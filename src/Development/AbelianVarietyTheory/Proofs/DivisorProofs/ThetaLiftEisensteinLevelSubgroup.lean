module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceVacuumIsLocalVacuumChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForUnipotentMatrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalGridNodeType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfPow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.CentreWeilComm

variable {D : D7} {θ : InfFam D} {V : HSp D} {n : ℕ} {τ : D.what₂.Tau}

theorem continuous_of_mem (hθ : IsInfFam θ) {m : ℕ} (Φ : schwartzA θ m n) : Continuous Φ.1 :=
  (GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ m n Φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n Φ.1 Φ.2)).1

theorem integrable_of_mem (hθ : IsInfFam θ) {m : ℕ} (μ : Measure (Mx D m n)) [μ.IsAddHaarMeasure] (Φ : schwartzA θ m n) :
    Integrable Φ.1 μ := by
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  obtain ⟨hc, K, hK, hC⟩ := GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ m n Φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n Φ.1 Φ.2)
  obtain ⟨N, hN⟩ := GlobalTheory.Unf.MajInt.maj_integrable D θ hθ m n (fun _ _ => True) 0 μ inferInstance
    (.of_forall fun _ _ _ h => (h trivial).elim) (fun t _ => map_add_right_eq_self μ t)
  obtain ⟨C, hC⟩ := hC N
  exact ((hN K hK).const_mul C).mono' hc.aestronglyMeasurable (.of_forall hC)


variable {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
  {μ : Measure (Mx D V.rank n)} {𝓕 : Set (Mx D V.rank n)} {ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n)}


section

variable (hψ : IsCharAF D.host.F ψ) (hθ : IsInfFam θ) (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
  (hω : StdUnn.IsWeilSch ψ χ θ V μ ω)
include hψ hθ hμ hω

end

end GlobalTheory.RegSch.CentreWeilComm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiag
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiag
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger.PresImpl

variable {D : D7}

theorem schr_schr_apply {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (x x₁ x₀ y₁ y₀ : κ → R) (f : (κ → R) → ℂ) :
    ψ (x ⬝ᵥ y₁ + ⅟2 * x₁ ⬝ᵥ y₁) * (ψ ((x + x₁) ⬝ᵥ y₀ + ⅟2 * x₀ ⬝ᵥ y₀) * f (x + x₁ + x₀)) =
      ψ (⅟2 * (x₁ ⬝ᵥ y₀ - x₀ ⬝ᵥ y₁)) * (ψ (x ⬝ᵥ (y₁ + y₀) + ⅟2 * (x₁ + x₀) ⬝ᵥ (y₁ + y₀)) * f (x + (x₁ + x₀))) := by
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
  refine congrArg (· * f (x + (x₁ + x₀))) (congrArg ψ ?_)
  have h2 : (2 : R) * ⅟2 = 1 := mul_invOf_self 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (-(x₁ ⬝ᵥ y₀)) * h2

theorem actO_eq (S T : HSp D) {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
    (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
    (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) (g : GA D S) (h : GA D T)
    (hh : mt T h = a.1.1) (hg : mt S g = (b⁻¹).1.1ᵀ) (w : Formalism.IndefR.Datum.WO S T) :
    Formalism.IndefR.Datum.actO S T g h w = GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (a, b) w := by
  have h1 : mt S g⁻¹ * mt S g = 1 := by
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : mt S g * (b.1.1)ᵀ = 1 := by
    rw [hg, ← Matrix.transpose_mul, ← Units.val_mul]
    simp
  have h3 : mt S g⁻¹ = (b.1.1)ᵀ := by
    calc mt S g⁻¹ = mt S g⁻¹ * (mt S g * (b.1.1)ᵀ) := by rw [h2, Matrix.mul_one]
      _ = (b.1.1)ᵀ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  simp only [Formalism.IndefR.Datum.actO, GlobalTheory.WeilM.actAB, hh, h3]

theorem thetaTr_rho (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {ξ : AF D.host.F ⊗[D.host.F] D.host.E}
    (hs : ∀ x y : Formalism.IndefR.Datum.WO S T,
      GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y =
        Formalism.IndefR.Datum.symplO S T x y) {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (w : Formalism.IndefR.Datum.WO S T) (φ : (κ → AF D.host.F) → ℂ) :
    thetaTr D.host.F co ψ (co.rho ψ w φ) = Formalism.IndefR.Datum.heisO ψ S T w (thetaTr D.host.F co ψ φ) := by
  funext v
  have hhalf : algebraMap D.host.F (AF D.host.F) (1 / 2) = ⅟(2 : AF D.host.F) := by
    refine (invOf_eq_right_inv ?_).symm
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  have hf := co.form v w
  simp only [thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, Formalism.IndefR.Datum.heisO, GlobalTheory.WeilM.schr,
    Formalism.IndefR.Datum.symplOH, ← hs, hf, hhalf, map_add, Prod.fst_add, Prod.snd_add]
  rw [← tsum_mul_left]
  exact tsum_congr fun x => schr_schr_apply ψ _ _ _ _ _ φ


set_option maxHeartbeats 400000 in
theorem pres_impl : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
                       (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, om p φ ∈ GlobalTheory.WeilM.schA D.host.F κ) ∧
                       ∀ p w, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                         om p (co.rho ψ w φ) = co.rho ψ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) p w) (om p φ) := by
  intro D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hB κ _ co hco ω hω om htr
  have key : ∀ p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB), ∃ (g : GA D S) (h : GA D T),
      mt T h = p.1.1.1 ∧ mt S g = (p.2⁻¹).1.1ᵀ := fun p => GlobalTheory.T.unitaryPair_of_transposedGram_inverseGram D S T JA JB ξ hA hB p.1 p.2
  have pres : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, om p φ ∈ GlobalTheory.WeilM.schA D.host.F κ := by
    intro p φ hφ
    obtain ⟨g, h, hh, hg⟩ := key p
    exact (htr p.1 p.2 g h hh hg φ hφ).1
  refine ⟨pres, fun p w φ hφ => ?_⟩
  obtain ⟨a, b⟩ := p
  obtain ⟨g, h, hh, hg⟩ := key (a, b)
  have hs := GlobalTheory.T.traceSymplecticForm_eq_orientedHomSymplecticForm D S T JA JB ξ hA hB
  have hrho : ∀ w', ∀ φ' ∈ GlobalTheory.WeilM.schA D.host.F κ, co.rho ψ w' φ' ∈ GlobalTheory.WeilM.schA D.host.F κ :=
    fun w' φ' h' => GlobalTheory.T.schrodingerOperator_mem_adelicSchwartz_stdChar D ψ hψ κ _ φ' h'
  have h1 := htr a b g h hh hg _ (hrho w φ hφ)
  have h2 := htr a b g h hh hg _ hφ
  have hF := GlobalTheory.T.isThetaFunction_thetaTransform_rationalDarboux D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ
  have E1 := hω.om_heis g h w _ hF
  have E2 := thetaTr_rho ψ S T hs co w φ
  have E3 := thetaTr_rho ψ S T hs co (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (a, b) w) (om (a, b) φ)
  have E4 := actO_eq S T a b g h hh hg w
  have E : thetaTr D.host.F co ψ (om (a, b) (co.rho ψ w φ)) =
      thetaTr D.host.F co ψ (co.rho ψ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (a, b) w) (om (a, b) φ)) := by
    refine h1.2.trans ?_
    refine (congrArg (ω (g, h)) E2).trans ?_
    refine E1.trans ?_
    refine Eq.trans ?_ E3.symm
    exact congrArg₂ (Formalism.IndefR.Datum.heisO ψ S T) E4 h2.2.symm
  unfold thetaTr GlobalTheory.WeilM.Darboux.rho at E
  refine GlobalTheory.T.adelicSchwartz_determined_by_schrodingerThetaValues D ψ hψ κ _ h1.1 _ (hrho _ _ h2.1) fun v => ?_
  obtain ⟨v', rfl⟩ := co.e.surjective v
  exact congrFun E v'

end GlobalTheory.WeilSchrodinger.PresImpl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
                       (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, om p φ ∈ GlobalTheory.WeilM.schA D.host.F κ) ∧
                       ∀ p w, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                         om p (co.rho ψ w φ) = co.rho ψ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) p w) (om p φ) := by
  first | exact @GlobalTheory.WeilSchrodinger.PresImpl.pres_impl | exact GlobalTheory.WeilSchrodinger.PresImpl.pres_impl | (intros; apply GlobalTheory.WeilSchrodinger.PresImpl.pres_impl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqLastAddGaps
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CompHS
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}


open Classical in
def headWt (τ : Psi H) (k : ℕ) : AllWt.Weight Dw := fun τ' i => if τ' = τ ∧ (i : ℕ) ≤ k then 1 else 0


open Classical in
def tailWt (τ : Psi H) (k : ℕ) : AllWt.Weight Dw := fun τ' i => if τ' = τ ∧ k < (i : ℕ) then -1 else 0


open Classical in
def unitWt (τ : Psi H) (a : ℤ) : AllWt.Weight Dw := fun τ' _ => if τ' = τ then a else 0

theorem eq_last_add_gaps {N : ℕ} (v : Fin N → ℤ) (hN : 0 < N) (i : Fin N) :
    v i = v ⟨N - 1, by omega⟩ + ∑ k ∈ Finset.range (N - 1), if (i : ℕ) ≤ k then gap v k else 0 := by
  have h := ofGaps_gap v ⟨N - 1, by omega⟩ i
  simp only [ofGaps] at h
  have hi : (i : ℕ) ≤ N - 1 := by omega
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have e : (Finset.range (N - 1)).filter (fun k => (i : ℕ) ≤ k) = Finset.Ico (i : ℕ) (N - 1) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [e, Finset.sum_Ico_eq_sub _ hi]
  linarith


open Classical in
def piece (Dw : Datum H) (τ : Psi H) (k : ℕ) : AllWt.Weight Dw :=
  if k + 1 < Dw.p + Dw.q then (if k < Dw.p then headWt τ k else tailWt τ k) else 0

open Classical in
theorem piece_apply (τ τ' : Psi H) (k : ℕ) (i : Fin (Dw.p + Dw.q)) : piece Dw τ k τ' i =
    if τ' = τ then (if k + 1 < Dw.p + Dw.q then (if k < Dw.p then (if (i : ℕ) ≤ k then 1 else 0)
      else (if k < (i : ℕ) then -1 else 0)) else 0) else 0 := by
  unfold piece headWt tailWt
  by_cases h : τ' = τ <;> split_ifs <;> simp_all

open Classical in
theorem unitWt_apply (τ τ' : Psi H) (a : ℤ) (i : Fin (Dw.p + Dw.q)) :
    unitWt τ a τ' i = if τ' = τ then a else 0 := rfl

open Classical in
theorem decomp (la : AllWt.Weight Dw) (hla : GapGe 0 la) (hN : 0 < Dw.p + Dw.q) :
    let cτ : Psi H → ℤ := fun τ => la τ ⟨Dw.p + Dw.q - 1, by omega⟩ +
      ∑ k ∈ Finset.range (Dw.p + Dw.q - 1), if Dw.p ≤ k then gap (la τ) k else 0
    la = ∑ x ∈ (Finset.univ ×ˢ Finset.range (Dw.p + Dw.q - 1)).disjSum (Finset.univ : Finset (Psi H × Bool)),
      (Sum.elim (fun y : Psi H × ℕ => (gap (la y.1) y.2).toNat)
        (fun y : Psi H × Bool => if y.2 then (cτ y.1).toNat else (-cτ y.1).toNat) x) •
      (Sum.elim (fun y : Psi H × ℕ => piece Dw y.1 y.2)
        (fun y : Psi H × Bool => unitWt y.1 (if y.2 then 1 else -1)) x) := by
  intro cτ
  classical
  funext τ' i
  rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_disjSum, Finset.sum_product, Finset.univ_product_univ.symm,
    Finset.sum_product]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, piece_apply, unitWt_apply, Fintype.sum_bool,
    mul_ite, mul_zero, if_true, if_false]
  rw [Finset.sum_eq_single (s := Finset.univ) τ' (fun x _ hx => by simp [Ne.symm hx]) (by simp),
    Finset.sum_eq_single (s := Finset.univ) τ' (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp only [if_true, nsmul_eq_mul, Bool.false_eq_true, if_false, mul_one]
  have hv := eq_last_add_gaps (la τ') hN i
  have hterm : ∀ y ∈ Finset.range (Dw.p + Dw.q - 1), (if (i : ℕ) ≤ y then gap (la τ') y else 0) =
      ((gap (la τ') y).toNat : ℤ) * (if y + 1 < Dw.p + Dw.q then (if y < Dw.p then (if (i : ℕ) ≤ y then 1 else 0)
        else (if y < (i : ℕ) then -1 else 0)) else 0) + (if Dw.p ≤ y then gap (la τ') y else 0) := by
    intro y hy
    have hy' : y + 1 < Dw.p + Dw.q := by simp only [Finset.mem_range] at hy; omega
    have hg : 0 ≤ gap (la τ') y := hla τ' y hy'
    rw [Int.toNat_of_nonneg hg, if_pos hy']
    split_ifs <;> first | omega | simp <;> omega
  have hc := Int.toNat_sub_toNat_neg (cτ τ')
  have hcdef : cτ τ' = la τ' ⟨Dw.p + Dw.q - 1, by omega⟩ +
      ∑ k ∈ Finset.range (Dw.p + Dw.q - 1), if Dw.p ≤ k then gap (la τ') k else 0 := rfl
  rw [hv, Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  linarith

end GlobalTheory.NefWt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ModifSections

open Opposite

theorem isIntegral_of_iso_comp {A B C E : CommRingCat.{0}} (i : A ⟶ B) (f : B ⟶ C) (m : C ⟶ E) [IsIso i]
    [IsIso m] (h : (i ≫ f ≫ m).hom.IsIntegral) : f.hom.IsIntegral := by
  have e : f = inv i ≫ (i ≫ f ≫ m) ≫ inv m := by simp
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp]
  refine RingHom.IsIntegral.trans _ _ ?_ (RingHom.IsIntegral.trans _ _ h ?_)
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv i)).2
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv m)).2

theorem isIntegral_app {Z₁ Z₂ : Scheme.{0}} (ρ : Z₁ ⟶ Z₂) [UniversallyClosed ρ]
    (V : Z₂.Opens) (hV : IsAffineOpen V) : (ρ.app V).hom.IsIntegral := by
  have : IsAffine V.toScheme := hV
  have h := isIntegral_appTop_of_universallyClosed (ρ ∣_ V)
  rw [morphismRestrict_appTop] at h
  have e : V.ι ''ᵁ ⊤ = V := by simp
  rw [ρ.app_eq e, Category.assoc, Category.assoc, ← Functor.map_comp] at h
  simp only [eqToHom_op, eqToHom_map, eqToHom_trans] at h
  have hi : ∀ {A B : CommRingCat.{0}} (q : A = B), IsIso (eqToHom q) := fun q => by
    subst q; rw [eqToHom_refl]; infer_instance
  exact @isIntegral_of_iso_comp _ _ _ _ _ _ _ (hi _) (hi _) h

theorem isNormalScheme_of_smooth {k : Type} [Field k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) [Smooth p] :
    GlobalTheory.IsNormalScheme Y :=
  (GlobalTheory.isNormalScheme_iff Y).2 (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p
    ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))

theorem exists_germ_eq {Y : Scheme.{0}} [IsIntegral Y] [GlobalTheory.IsNormalScheme Y] (y : Y) (hy : y = genericPoint Y)
    (V : Y.Opens) (hyV : y ∈ V) (t : Y.presheaf.stalk y)
    (h : ∀ x ∈ V, ∃ (W : Y.Opens) (hW : y ∈ W), x ∈ W ∧ W ≤ V ∧
      (Y.presheaf.germ W y hW).hom.IsIntegralElem t) :
    ∃ a : Γ(Y, V), Y.presheaf.germ V y hyV a = t := by
  subst hy
  have : Nonempty V := ⟨⟨_, hyV⟩⟩
  refine GlobalTheory.IsNormalScheme.exists_germToFunctionField_eq_of_locally V t fun x hx => ?_
  obtain ⟨W, hW, hxW, hWV, hi⟩ := h x hx
  have hne : Nonempty W := ⟨⟨_, hW⟩⟩
  have := GlobalTheory.IsNormalScheme.isIntegrallyClosedIn_functionField (X := Y) W
  obtain ⟨s, hs⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := Γ(Y, W)) (A := Y.functionField)).1 hi
  exact ⟨W, hne, s, hxW, hWV, hs⟩

theorem isoOver_top {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [GlobalTheory.IsNormalScheme Y]
    (σ : X ⟶ Y) [UniversallyClosed σ] (U : Y.Opens) [IsIso (σ ∣_ U)]
    (hU : ((σ ⁻¹ᵁ U : X.Opens) : Set X).Nonempty) : IsoOver σ ⊤ := by
  intro V _
  have hηU : genericPoint X ∈ σ ⁻¹ᵁ U :=
    ((genericPoint_spec X).mem_open_set_iff (σ ⁻¹ᵁ U).isOpen).2 (by simpa using hU)
  have hmem : ∀ V : Y.Opens, (V : Set Y).Nonempty → σ (genericPoint X) ∈ V := by
    intro V hV
    obtain ⟨y, hyV, hyU⟩ := nonempty_preirreducible_inter V.isOpen U.isOpen hV ⟨_, hηU⟩
    obtain ⟨x, hx⟩ := (σ ∣_ U).surjective ⟨y, hyU⟩
    have hx' : σ x.1 = y := (morphismRestrict_base_coe σ U x).symm.trans (congrArg Subtype.val hx)
    have hne : ((σ ⁻¹ᵁ V : X.Opens) : Set X).Nonempty := ⟨x.1, show σ x.1 ∈ V from hx' ▸ hyV⟩
    exact ((genericPoint_spec X).mem_open_set_iff (σ ⁻¹ᵁ V).isOpen).2 (by simpa using hne)
  have hgen : σ (genericPoint X) = genericPoint Y := by
    have h1 : σ (genericPoint X) ⤳ genericPoint Y :=
      specializes_iff_forall_open.2 fun s hs hg => hmem ⟨s, hs⟩ ⟨_, hg⟩
    exact (h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq
  have hS : IsIso (σ.stalkMap (genericPoint X)) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap σ U ⟨_, hηU⟩)).1
      (((isIso_iff_isIso_stalkMap (σ ∣_ U)).1 inferInstance).2 ⟨_, hηU⟩)
  have hSb := ConcreteCategory.bijective_of_isIso (σ.stalkMap (genericPoint X))
  by_cases hV : (V : Set Y).Nonempty
  swap
  · exact isoOver_of_isIso σ (O := U) V fun y hy => (hV ⟨y, hy⟩).elim
  have hyV := hmem V hV
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a a' e => ?_, fun b => ?_⟩
  · apply germ_injective_of_isIntegral Y (σ (genericPoint X)) hyV
    apply hSb.1
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, e]
  obtain ⟨t, ht⟩ := hSb.2 (X.presheaf.germ (σ ⁻¹ᵁ V) (genericPoint X) hyV b)
  obtain ⟨a, ha⟩ := exists_germ_eq (σ (genericPoint X)) hgen V hyV t fun y hy => by
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
    have hWV' : W ≤ V := hWV
    have hηW : σ (genericPoint X) ∈ W := hmem W ⟨y, hyW⟩
    refine ⟨W, hηW, hyW, hWV', ?_⟩
    have hi := isIntegral_app σ W hW (X.presheaf.map (homOfLE (σ.preimage_mono hWV')).op b)
    have h2 := RingHom.IsIntegralElem.map hi (X.presheaf.germ (σ ⁻¹ᵁ W) (genericPoint X) hηW).hom
    have e1 : (X.presheaf.germ (σ ⁻¹ᵁ W) (genericPoint X) hηW).hom.comp (σ.app W).hom =
        (σ.stalkMap (genericPoint X)).hom.comp (Y.presheaf.germ W (σ (genericPoint X)) hηW).hom :=
      RingHom.ext fun a => (Scheme.Hom.germ_stalkMap_apply σ W _ hηW a).symm
    have e2 : X.presheaf.germ (σ ⁻¹ᵁ W) (genericPoint X) hηW
        (X.presheaf.map (homOfLE (σ.preimage_mono hWV')).op b) = σ.stalkMap (genericPoint X) t := by
      exact (X.presheaf.germ_res_apply (homOfLE (σ.preimage_mono hWV')) _ hηW b).trans ht.symm
    rw [e1, e2] at h2
    have h3 := RingHom.IsIntegralElem.map h2 (inv (σ.stalkMap (genericPoint X))).hom
    have e3 : (inv (σ.stalkMap (genericPoint X))).hom.comp (σ.stalkMap (genericPoint X)).hom =
        RingHom.id _ := by
      rw [← CommRingCat.hom_comp, IsIso.hom_inv_id]; rfl
    rwa [← RingHom.comp_assoc, e3, RingHom.id_comp, ← RingHom.comp_apply, e3, RingHom.id_apply] at h3
  refine ⟨a, germ_injective_of_isIntegral X (genericPoint X) hyV ?_⟩
  rw [← Scheme.Hom.germ_stalkMap_apply, ha, ht]

theorem modification_lineBundleGlobalSectionsDim_pull_eq : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp k) (U : Y.Opens) (D : ℕ),
    SmoothOfRelativeDimension D p → IsProjOver p → ∀ (M : Modif p U D) [IsIntegral M.X] (B : LB Y), B.IsLB →
    letI := algebraΓOfHom p; letI := algebraΓOfHom M.str; lbH0 k (B.pull M.σ) = lbH0 k B := by
  intro k _ Y _ p U D hs hp M _ B hB
  haveI := hs
  haveI : Smooth p := SmoothOfRelativeDimension.smooth D p
  haveI : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth p
  haveI : IsProper (M.σ ≫ p) := GlobalTheory.CommonModel.isProper_of_isProjOver M.proj
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hp
  haveI : IsProper M.σ := IsProper.of_comp M.σ p
  haveI := M.iso
  have hb := (isoOver_top M.σ U M.dense.nonempty).bijective_pull (p := p) hB (W := ⊤) le_top le_top
  letI := algebraΓOfHom p
  letI := algebraΓOfHom M.str
  rw [← H0.finrank_top M.str (B.pull M.σ), ← H0.finrank_top p B]
  exact (LinearEquiv.ofBijective _ hb).finrank_eq.symm

end GlobalTheory.ModifSections
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEqStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modification_globalSectionsDim_pull_eq : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp k) (U : Y.Opens) (D : ℕ), SmoothOfRelativeDimension D p → IsProjOver p → ∀ (M : Modif p U D) [IsIntegral M.X] (B : LB Y), B.IsLB → letI := algebraΓOfHom p; letI := algebraΓOfHom M.str; lbH0 k (B.pull M.σ) = lbH0 k B := by
  first | exact @GlobalTheory.ModifSections.modification_lineBundleGlobalSectionsDim_pull_eq | exact GlobalTheory.ModifSections.modification_lineBundleGlobalSectionsDim_pull_eq | (intros; apply GlobalTheory.ModifSections.modification_lineBundleGlobalSectionsDim_pull_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIoExtensionOfWeakCharacterisationFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IoExtCore
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorProductFockVectorExtremalTorusWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorProductFockVectorExtremalTorusWeight
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.MinorWeightCore

open GlobalTheory.JointHarm GlobalTheory.AdTh.MinorWeight

theorem delta_extremal_weight_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (τ : D.what₂.Tau) (a : Fin (Wc D i).rank → ℝ) (t : T0), R.ωP i t (1, atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * diagonal (fun j => cexp ((a j : ℂ) * I)) * (R.MW i (sg0 D A)).fr τ)) (R.ptP i t (RealDat.Delta i)) = cexp (((∑ j, extWt (R.MW i (sg0 D A)) τ j * a j : ℝ) : ℂ) * I) • R.ptP i t (RealDat.Delta i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i hV τ a t
  have hA := GlobalTheory.PairWeightArith.arithAt D i
  have hI := GlobalTheory.PairInfTypes.infTypesAt D T0 R.toLevCh A.μ0 h.lev i t
  have hε := h.models.order i
  have hθ := h.models.inf
  obtain ⟨x₁, x₂, x₃, hx⟩ := GlobalTheory.JointHarm.weights_of_minors D i (sg0 D A) (sgAt_mk _ R.hv0) (R.MW i (sg0 D A)) hε
  have hpq : ∀ ρ, ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = (Wc D i).rank := fun ρ =>
    (hA ρ).rank.1.trans (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).symm
  have hmn : (Wc D i).rank ≤ (Vc D i).rank := (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).le.trans (r_le_V i)
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := pure_one _ (R.vP i t) ▸ h.thP.pt_theta i t 1
  have hv := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h.thP.vP i t) hth
  have hB : ∀ ρ, (R.BV i ρ)ᴴ * gramAt D (Vc D i) ρ * R.BV i ρ = 1 := fun ρ => by
    obtain ⟨e, he, h1, -⟩ := h.models.BV i ρ
    rw [h1, ← diagonal_one]
    congr 1
    funext j
    rcases he j with hj | hj
    · rw [hj.1]; rfl
    · exact absurd j.2 (not_lt.2 hj.2)
  have hBi : ∀ ρ, (R.BV i ρ)⁻¹ * R.BV i ρ = 1 := fun ρ =>
    Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_left_inverse (hB ρ))
  unfold RealDat.ptP
  generalize R.MW i (sg0 D A) = M at hε hx hv ⊢
  have h1 : ∀ ρ, M.fr ρ * (M.fr ρ)⁻¹ = 1 := fun ρ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ))
  have hK := diag_mem (ε := M.ε τ) a
  obtain ⟨a1, a2, a3⟩ := GlobalTheory.PointAtPlaceHom.atTau_spec hθ (Wc D i) τ (conj_mem M τ hK)
  generalize atTau R.θ (Wc D i) τ _ = g at a1 a2 a3 ⊢
  let θs : D.what₂.Tau → Fin (Wc D i).rank → ℝ := fun ρ => if ρ = τ then a else 0
  have hg : ∀ ρ, M.fr ρ * compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i) g) * (M.fr ρ)⁻¹ =
      diagonal fun j => cexp ((θs ρ j : ℂ) * I) := fun ρ => by
    by_cases e : ρ = τ
    · subst e
      rw [show compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i) g) = _ from a2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1,
        Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
      simp only [θs, if_true]
    · rw [show compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i) g) = _ from a3 ρ e, Matrix.mul_one, h1]
      simp [θs, e]
  have e1 : ∀ ρ, (R.BV i ρ)⁻¹ * compAt R.θ ρ (Formalism.L2.Theta.mt (Vc D i) 1) * R.BV i ρ = 1 := fun ρ => by
    rw [show compAt R.θ ρ (Formalism.L2.Theta.mt (Vc D i) 1) = 1 from GlobalTheory.PointAtPlaceHom.infMat_one _ _, Matrix.mul_one, hBi]
  have key := (GlobalTheory.T.weil_maximalCompact_fock_substitution_character D R.ψ R.θ _ _ _ _ _ _ M (R.BV i) (h.thP.ωP i t) hθ (D.sp.V_sig _) (D.sp.W_sig _) hB _ _ hpq hε
    _ _ (fun ρ => (hI ρ).chiV) (fun ρ => (hI ρ).chiW) x₁ x₂ x₃ (fun ρ => (hx ρ).1) (fun ρ => (hx ρ).2.1)
    (fun ρ => (hx ρ).2.2.1) _ hth hv 1 (one_mem _) g a1 (fun ρ => hg ρ ▸ diag_mem _)).2 (RealDat.Delta i)
  simp only [hg, e1] at key
  rw [key, RealDat.Delta, fact_diagonal M.ε _ _ _ _ x₁ x₂ x₃ hmn hpq hε (fun ρ => (hA ρ).aPlus_antitone) (fun ρ => (hA ρ).aM_anti)
    _ (fun _ _ => Complex.exp_ne_zero _), map_smul]
  congr 1
  rw [Finset.prod_eq_single τ (fun ρ _ e => by simp [θs, e]) (fun e => (e (Finset.mem_univ _)).elim), Complex.ofReal_sum,
    Finset.sum_mul, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hr := revNeg_shape (Nat.le.intro (hpq τ)) (hε τ) j
  have hj := j.2
  rw [extWt, (hx τ).2.2.2.1, ← Complex.exp_int_mul, wtK, hr]
  congr 1
  by_cases hp : (j : ℕ) < ((Wc D i).sig (tauE D τ)).1
  · simp [θs, hp, mul_assoc]
  · rw [if_neg hp, if_neg hp, if_neg (by have := hpq τ; omega),
      show (Wc D i).rank - 1 - ((Wc D i).rank - 1 - (j - ((Wc D i).sig (tauE D τ)).1)) =
        j - ((Wc D i).sig (tauE D τ)).1 by omega]
    simp [θs, mul_assoc]

end GlobalTheory.AdTh.MinorWeightCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorProductFockVectorExtremalTorusWeightStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minorProduct_fockVector_extremalTorusWeight : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (τ : D.what₂.Tau) (a : Fin (Wc D i).rank → ℝ) (t : T0), R.ωP i t (1, atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * diagonal (fun j => cexp ((a j : ℂ) * I)) * (R.MW i (sg0 D A)).fr τ)) (R.ptP i t (RealDat.Delta i)) = cexp (((∑ j, extWt (R.MW i (sg0 D A)) τ j * a j : ℝ) : ℂ) * I) • R.ptP i t (RealDat.Delta i) := by
  first | exact @GlobalTheory.AdTh.MinorWeightCore.delta_extremal_weight_core | exact GlobalTheory.AdTh.MinorWeightCore.delta_extremal_weight_core | (intros; apply GlobalTheory.AdTh.MinorWeightCore.delta_extremal_weight_core <;> assumption)
end
end

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.IoExtCore
open GlobalTheory.AdTh.IoExtPf

theorem ioExt_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ i, VStd D i) → (∀ i, LowSm (R.MW i (sg0 D A)) ∧ ExtLine (R.MW i (sg0 D A))) → IoExt R := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR hV hM i
  obtain ⟨hs, hl⟩ := hM i
  obtain ⟨-, hK, v, w, hv1, hw1, hio⟩ := hR.thP.ioP i A.μ0
  obtain ⟨hth, hvac, hcW, hcV, hbW⟩ := GlobalTheory.AdTh.VecFockCore.vec_fock_core D G Pl0 T0 A Ks R F hR i A.μ0 (hV i)
  have hP := (GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A Ks R F hR i A.μ0 (hV i)).1
  have hinj := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hP.weil.std hP.inf (fun _ => 1) (R.BV i)
    (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) (fun τ => ((Wc D i).sig (tauE D τ)).1)
    hcV hcW (hR.models.BV i) hbW hP.sigV hP.sigW _ hth hvac
    (GlobalTheory.AdTh.VecNeCore.thetaVector_ne_zero_core D G Pl0 T0 A Ks R F hR i (hV i))
  let pt := pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
    (R.vP i A.μ0)
  let f : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) := pt ∘ₗ (R.ioP i).flip w
  have hf : ∀ x, f x = R.ptP i A.μ0 (R.ioP i x w) := fun x => rfl
  have hv0 : f (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    rw [hf, hio]
    exact fun h => Delta_ne i (hinj (h.trans (map_zero pt).symm))
  refine ⟨fun ρ => v ρ, fun τ => ⟨hv1 τ, (v τ).2, fun a ha => ?_⟩, v, w, fun _ => rfl, hw1, hio⟩
  have hm := GlobalTheory.LowKProj.lowKSub_stable _ _ _ _ ha _ (v τ).2
  let u : lowT (R.MW i (sg0 D A)) τ := ⟨⟨_, hs τ hm⟩, hm⟩
  have h1 := hK τ _ ha v u rfl w
  rw [hio, GlobalTheory.T.minorProduct_fockVector_extremalTorusWeight D G Pl0 T0 A Ks R F hR i (hV i) τ a A.μ0, ← hio, ← hf, ← hf] at h1
  have h2 := inj_factor (R.MW i (sg0 D A)) hs hl τ f
    (fun k => R.ωP i A.μ0 (1, atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)))
    (fun k hk v u hu => hK τ k hk v u hu w) v hv0
    (u - cexp (((∑ j, extWt (R.MW i (sg0 D A)) τ j * a j : ℝ) : ℂ) * I) • v τ) (by
      rw [MultilinearMap.map_update_sub, MultilinearMap.map_update_smul, Function.update_eq_self, map_sub, map_smul, ← h1]
      simp)
  exact congrArg (fun y : lowT (R.MW i (sg0 D A)) τ => ((y : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ))
    (sub_eq_zero.1 h2)

end GlobalTheory.AdTh.IoExtCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIoExtensionOfWeakCharacterisationFrames
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IoExtStd

theorem thetaIoExtension_of_weakCharacterisation_frames : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ i, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧ (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)) → IoExt R.toRealDat := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hC hE hF
  have hB := GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face D G Pl0 I0 T0 A3 Ks R F hC hE
  have hcore := hB.1
  have hsh := GlobalTheory.DefLift.holShape_fixed D G Pl0 T0 A3.A Ks R.toRealDat hcore.models.order
  exact GlobalTheory.AdTh.IoExtCore.ioExt_core D G Pl0 T0 A3.A Ks R.toRealDat F.lv2 hcore
    (fun i => GlobalTheory.StdFrame.vStd_of_orthonormal_span D i (hF i))
    (fun i => ⟨GlobalTheory.LowSmooth.lowSm_MW D G Pl0 T0 A3.A Ks R.toRealDat i _,
      GlobalTheory.HolLowOnce.extLine_of_holShape D _ _ _ (hsh i).1⟩)

end GlobalTheory.IoExtStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIoExtensionOfWeakCharacterisationFramesStatement
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ioExt_of_weakCharacterisation_of_orthonormal_frames : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ i, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧ (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)) → IoExt R.toRealDat := by
  first | exact @GlobalTheory.IoExtStd.thetaIoExtension_of_weakCharacterisation_frames | exact GlobalTheory.IoExtStd.thetaIoExtension_of_weakCharacterisation_frames | (intros; apply GlobalTheory.IoExtStd.thetaIoExtension_of_weakCharacterisation_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedFactorEqProductAbove
noncomputable section

namespace GlobalTheory.UnrEuler.ConjFac

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors TensorProduct
open Formalism.L2.Host (aboveF)
open GlobalTheory.CuspRep (conjSrc conjPl_conjSrc)

theorem absNorm_conjSrc {E : Type} [Field E] [NumberField E] (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm (conjSrc c w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc c w)]
  rw [Ideal.absNorm_eq_natCard, Ideal.absNorm_eq_natCard]
  exact Nat.card_congr (Ideal.quotientEquiv (w.asIdeal.comap (RingOfIntegers.mapRingEquiv c)) w.asIdeal
    (RingOfIntegers.mapRingEquiv c)
    (Ideal.map_comap_of_surjective _ (RingEquiv.surjective (RingOfIntegers.mapRingEquiv c)) _).symm).toEquiv

end GlobalTheory.UnrEuler.ConjFac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.StdPairCone

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def blk₁ {m a a' : ℕ} (X : Matrix (Fin m) (Fin (a + a')) k) : Matrix (Fin m) (Fin a) k :=
  Matrix.of fun i j => X i (Fin.castAdd a' j)

def blk₂ {m a a' : ℕ} (X : Matrix (Fin m) (Fin (a + a')) k) : Matrix (Fin m) (Fin a') k :=
  Matrix.of fun i j => X i (Fin.natAdd a j)

def IsGLO {n : ℕ} (g : Matrix (Fin n) (Fin n) k) : Prop := (∀ i j, g i j ∈ 𝒪[k]) ∧ valuation k g.det = 1


open Classical in
def stdA (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (X : Matrix (Fin a) (Fin (a + a')) k) : ℂ :=
  if h : (blk₁ X).det ≠ 0 ∧ IsGLO (blk₁ X) ∧ ∀ i j, blk₂ X i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
    (((ν (Units.mk0 _ h.1))⁻¹ : ℂˣ) : ℂ) else 0


open Classical in
def stdB (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (Y : Matrix (Fin a') (Fin (a + a')) k) : ℂ :=
  if h : (blk₂ Y).det ≠ 0 ∧ IsGLO (blk₂ Y) ∧ ∀ i j, blk₁ Y i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
    (((ν (Units.mk0 _ h.1))⁻¹ : ℂˣ) : ℂ) else 0


open Classical in
def unitInd (ν : kˣ →* ℂˣ) (y : k) : ℂ :=
  if h : y ≠ 0 ∧ valuation k y = 1 then (((ν (Units.mk0 y h.1))⁻¹ : ℂˣ) : ℂ) else 0

def sgn (s : ℤˣ) : kˣ := Units.map (Int.castRingHom k).toMonoidHom s

end Local

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end Glob

end GlobalTheory.StdPairCone
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotSmallDict

def IsRootOne (ζ : ℂ) : Prop := ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1

def IsAlgUnit (ζ : ℂ) : Prop :=
  ζ ≠ 0 ∧ ζ ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam ζ‖ = 1

variable {D : D7}

def IsStdLat {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Prop :=
  ∀ y, y ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i

def unitPt (S T : HSp D) (a : Formalism.L2.Theta.AE D) (o : ℕ) : WO S T := fun i j => if i.1 = o + j.1 then a else 0

def cosetFn {S T : HSp D} (a : Formalism.L2.Theta.AE D) (I : Ideal (𝓞 D.host.E)) (x : WO S T) : WO S T → ℂ := fun y =>
  if IsHalf a y ∧ ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (y i j - x i j)) then 1 else 0

def modul (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) : Ideal (𝓞 D.host.E) :=
  ∏ w ∈ P, w.asIdeal ^ c w

def GoodIdem (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  IsIdemSum e P ∧ ∀ w ∈ P, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal

theorem IsRootOne.one : IsRootOne 1 := ⟨1, one_pos, one_pow 1⟩

theorem IsRootOne.mul {a b : ℂ} (ha : IsRootOne a) (hb : IsRootOne b) : IsRootOne (a * b) := by
  obtain ⟨m, hm, h⟩ := ha
  obtain ⟨n, hn, h'⟩ := hb
  exact ⟨m * n, Nat.mul_pos hm hn, by rw [mul_pow, pow_mul, h, mul_comm m n, pow_mul, h', one_pow, one_pow, one_mul]⟩

theorem IsRootOne.ne_zero {a : ℂ} (ha : IsRootOne a) : a ≠ 0 := by
  obtain ⟨m, hm, h⟩ := ha
  rintro rfl
  rw [zero_pow hm.ne'] at h
  exact zero_ne_one h

theorem IsRootOne.isAlgUnit {a : ℂ} (ha : IsRootOne a) : IsAlgUnit a := by
  have h0 := ha.ne_zero
  obtain ⟨m, hm, h⟩ := ha
  have hq : a ∈ Qbar := mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow hm (by rw [h]; exact isAlgebraic_one))
  refine ⟨h0, hq, fun p _ lam => ?_⟩
  have h1 : (⟨a, hq⟩ : Qbar) ^ m = 1 := Subtype.ext h
  have h2 : ‖lam ⟨a, hq⟩‖ ^ m = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  unfold lamC
  rw [dite_eq_left hq]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h2

theorem IsAlgUnit.mul {a b : ℂ} (ha : IsAlgUnit a) (hb : IsAlgUnit b) : IsAlgUnit (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, Qbar.mul_mem ha.2.1 hb.2.1, fun p _ lam => by
    rw [GlobalTheory.BotFormula.lamC_mul lam ha.2.1 hb.2.1, norm_mul, ha.2.2 p lam, hb.2.2 p lam, one_mul]⟩

end GlobalTheory.BotSmallDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCuspFormsFullLattice
section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SupremumLattice
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SupremumLattice

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

section Ambient

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
  [IsScalarTower (𝓞 K) K R] (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
  (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)

def supIn : Submodule (𝓞 K) R := (latOf C Vs hV).map (C.subtype.restrictScalars (𝓞 K))

theorem supIn_full_iff :
    ((supIn C Vs hV).FG ∧ Submodule.span K (supIn C Vs hV : Set R) = C) ↔
      Submodule.IsFullLattice K (latOf C Vs hV) := by
  have h1 : (supIn C Vs hV).FG ↔ (latOf C Vs hV).FG :=
    ⟨Submodule.fg_of_fg_map_injective (C.subtype.restrictScalars (𝓞 K)) C.injective_subtype, fun h => h.map _⟩
  have h2 : Submodule.span K (supIn C Vs hV : Set R) =
      (Submodule.span K (latOf C Vs hV : Set C)).map C.subtype := by
    rw [← Submodule.span_image]; rfl
  rw [h1, h2]
  constructor
  · rintro ⟨a, b⟩
    exact { toIsLattice := Submodule.IsLattice.of_fg K a
            span_eq_top := Submodule.map_injective_of_injective C.injective_subtype (by
              rw [b, Submodule.map_subtype_top]) }
  · intro h
    exact ⟨h.fg, by rw [Submodule.IsFullLattice.span_eq_top (self := h), Submodule.map_subtype_top]⟩

end Ambient

variable {D : D7}

end GlobalTheory.IndefiniteRowSideFullHecke.SupremumLattice
end
end

noncomputable section

namespace GlobalTheory.GoodLat.Obj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Arith Formalism.IndefR.FWT

theorem nV_pos (D : D7) : 0 < D.R.nV := by
  have := D.R.three_m_lt_t
  rw [Ranks.nV]
  omega

theorem fullLat {D : D7} (T : Core D) (hT : LawsM T) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) (hn : 0 < w.n) :
    FullLat (T.cuspA j (wtA w) w.n) (valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)) fun la => isVal_valSet la :=
  (GlobalTheory.IndefiniteRowSideFullHecke.SupremumLattice.supIn_full_iff _ _ _).1
    (GlobalTheory.SupFull.fullAt_of_pins D T hT.pins j hj (hT.unf j hj _ T.good_σ₀) w hn)

section Real

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem latFull (T : CoreJ D) (hT : LawsJ T) {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} (hκ : KapIs κ) :
    LatFull T κ := fun i =>
  fullLat T.toCore hT.toLawsM (inR i) (κ i) (by rw [(hκ i (D.eTau.symm 1)).2.2]; exact nV_pos D)

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem mkFull_of_tie (t : FWTie T R κ v₀) (i : Fin D.R.m) : (R.FW i).MKFull :=
  GlobalTheory.GoodLat.mkFull_of_tie t (latFull T t.laws t.kap) i

theorem mLat_of_tie (t : FWTie T R κ v₀) (F : Face D A) (b : Bool) : (R.toCx F).MLat b :=
  GlobalTheory.GoodLat.mLat_of_tie t (latFull T t.laws t.kap) F b

end Real

end GlobalTheory.GoodLat.Obj
end
end
