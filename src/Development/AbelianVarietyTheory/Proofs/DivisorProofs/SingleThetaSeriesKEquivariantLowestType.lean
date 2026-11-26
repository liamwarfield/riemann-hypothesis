module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModerateGrowthHeight
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.KerLe
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ExpLoss
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LogSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumCMPreservesSchwartzHeisenber

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SingleThetaSeriesKEquivariantLowestType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SingleThetaSeriesKEquivariantLowestType
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open Classical

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.SeriesKEquiv

theorem singleSeries_kEquiv : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (Q' : Finset (Pl D.host.E)) (Ω : DatFn D i) (φ' : WO (Vc D i) (Wc D i) → ℂ), VecOf R i Q' Ω φ' → ∀ (h : GA D (Vc D i)) (y : (R.cV i).W) (g0 : G) (τ : D.what₂.Tau) (k : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε τ) → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (u : lowT (R.MW i (sg0 D A)) τ), ((u : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) = (R.MW i (sg0 D A)).σ τ k ((v τ : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) → Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g0) (singleSeries R i ω φ' h y (Function.update v τ u)) = Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)) (Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g0) (singleSeries R i ω φ' h y v)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK Q' Ω φ' hφ' h y g0 τ k hk v u hu
  have hθ : IsInfFam R.θ := hR.models.inf
  have hω := hR.thP.ωP

  have hthφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ' := by
    obtain ⟨⟨hψ, h0⟩, e, -, hth⟩ := hφ'
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ hth h0.theta
  have hvφ : ∀ ρ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ ρ
      (cplxO 1 (cart (R.MW i (sg0 D A)) ρ)) φ' := by
    intro ρ
    obtain ⟨⟨hψ, hv⟩, e, he, hth⟩ := hφ'
    have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
    exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hv.inf ho.conj.infPart_eq ho.conj.conj.infPart_eq hth hv.theta
      hthφ (hv.fock ρ)

  have hthv : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i A.μ0) := by
    obtain ⟨⟨hψ, h0⟩, e, -, hth⟩ := hR.thP.vP i A.μ0
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ hth h0.theta
  have hvv := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hR.thP.vP i A.μ0) hthv
  have hBS : ∀ ρ, (R.BV i ρ)ᴴ * gramAt D (Vc D i) ρ * R.BV i ρ = 1 := fun ρ =>
    GlobalTheory.JointHarm.onb_eq_one (hR.models.BV i ρ)
  have hBu : ∀ ρ, IsUnit (R.BV i ρ) := fun ρ => IsUnit.of_mul_eq_one_right _ (hBS ρ)
  obtain ⟨x₁, x₂, x₃, hx⟩ := GlobalTheory.T.lowestKType_coefficientWeight_eq_minorWeights D i (sg0 D A) (sgAt_mk _ R.hv0) (R.MW i (sg0 D A)) (hR.models.order i)
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hpq : ∀ ρ, ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = (Wc D i).rank := fun ρ =>
    (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i ρ).rank.1.trans hrk.symm
  have hfr : ∀ ρ, (R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹ = 1 := fun ρ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit ρ))

  have hIT := GlobalTheory.T.thetaLiftInfinityTypes_atRealPlace D T0 R.toLevCh A.μ0 hR.lev i A.μ0
  obtain ⟨n, hn, ho⟩ := hK.fin
  have hχ0 : ∀ ρ, HasInfExp D χ ρ 0 := fun ρ => GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ hK.chr hn ho ρ
  have h1 : ∀ ρ, HasInfExp D (R.mu0 ((i : ℕ) + 1)) ρ (-GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.eS D i ρ) := fun ρ => by
    have h := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hR.lev.mu0 i)
      (GlobalTheory.PairInfTypes.hasInfQ_tauE D (R.toLevCh.C.isMu0 i).inf) ρ
    simpa only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] using h
  have hcV : ∀ ρ, HasInfExp D (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1 ρ (-GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.eS D i ρ) :=
    fun ρ => by
      have := GlobalTheory.Mem.HeckeExp.hasInfExp_mul (h1 ρ) (hχ0 ρ)
      rw [add_zero] at this
      exact this
  have hcW : ∀ ρ, HasInfExp D (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ρ
      (-GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.eS D i ρ - 1 / 2) := fun ρ => by
    rw [sub_eq_add_neg]
    exact GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hcV ρ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hIT ρ).eta)

  have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ (Wc D i) τ (GlobalTheory.JointHarm.conj_mem_UH (R.MW i (sg0 D A)) τ hk)
  have e : (fun ρ => (R.MW i (sg0 D A)).fr ρ * compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i)
      (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))) *
        ((R.MW i (sg0 D A)).fr ρ)⁻¹) = Pi.mulSingle τ k := by
    funext ρ
    rw [GlobalTheory.WeilDeriv.compAt_mt_eq_infMat]
    by_cases hρ : ρ = τ
    · subst hρ
      rw [hs.2.1, Pi.mulSingle_eq_same]
      calc _ = ((R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹) * k *
            ((R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹) := by simp only [Matrix.mul_assoc]
        _ = k := by rw [hfr, Matrix.one_mul, Matrix.mul_one]
    · rw [hs.2.2 ρ hρ, Pi.mulSingle_eq_of_ne hρ, Matrix.mul_one, hfr]
  have e' : (fun ρ => (R.BV i ρ)⁻¹ * compAt R.θ ρ (Formalism.L2.Theta.mt (Vc D i) 1) * R.BV i ρ) = 1 := by
    funext ρ
    rw [GlobalTheory.JointHarm.compAt_mt_one', Matrix.mul_one,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hBu ρ))]
    rfl
  have hKk : ∀ ρ, (R.MW i (sg0 D A)).fr ρ * compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i)
      (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))) *
        ((R.MW i (sg0 D A)).fr ρ)⁻¹ ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε ρ) := fun ρ => by
    rw [congrFun e ρ]
    by_cases hρ : ρ = τ
    · subst hρ; rwa [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hρ]; exact GlobalTheory.JointHarm.one_mem_K

  have aω := (GlobalTheory.T.weil_maximalCompact_fock_substitution_character D R.ψ R.θ (Vc D i) (Wc D i) _ _ ω _ (R.MW i (sg0 D A)) (R.BV i) hK.weil hθ
    (D.sp.V_sig _) (D.sp.W_sig _) hBS _ _ hpq (hR.models.order i) _ _ hcV hcW x₁ x₂ x₃
    (fun ρ => (hx ρ).1) (fun ρ => (hx ρ).2.1) (fun ρ => (hx ρ).2.2.1) φ' hthφ hvφ 1 (one_mem _) _ hs.1 hKk).2
  have av := (GlobalTheory.T.weil_maximalCompact_fock_substitution_character D R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i A.μ0) _ (R.MW i (sg0 D A)) (R.BV i) (hω i A.μ0) hθ
    (D.sp.V_sig _) (D.sp.W_sig _) hBS _ _ hpq (hR.models.order i) _ _ (fun ρ => (hIT ρ).chiV) (fun ρ => (hIT ρ).chiW)
    x₁ x₂ x₃ (fun ρ => (hx ρ).1) (fun ρ => (hx ρ).2.1) (fun ρ => (hx ρ).2.2.1) _ hthv hvv 1 (one_mem _) _ hs.1 hKk).2
  rw [e, e'] at aω av

  have hcVI : ∀ ρ, IsCartanInv (gramAt D (Vc D i) ρ)
      ((fun _ => (1 : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ)) ρ) := fun ρ => by
    have hu' := (Matrix.isUnit_iff_isUnit_det _).1 (hBu ρ)
    have h1' := Matrix.mul_nonsing_inv _ hu'
    have hG : gramAt D (Vc D i) ρ = ((R.BV i ρ)⁻¹)ᴴ * (R.BV i ρ)⁻¹ := by
      calc gramAt D (Vc D i) ρ
          = ((R.BV i ρ)⁻¹)ᴴ * ((R.BV i ρ)ᴴ * gramAt D (Vc D i) ρ * R.BV i ρ) * (R.BV i ρ)⁻¹ := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1', Matrix.conjTranspose_one,
              Matrix.one_mul, Matrix.mul_assoc, h1', Matrix.mul_one]
        _ = _ := by rw [hBS ρ, Matrix.mul_one]
    refine ⟨Matrix.one_mul _, by simp, ?_⟩
    rw [Matrix.mul_one, hG]
    exact Matrix.PosDef.conjTranspose_mul_self _
      (Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 (hBu ρ)))
  have hne : R.vP i A.μ0 ≠ 0 :=
    GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hR.lev.βV i))
      (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hR.lev.βW i))
      (hrk.trans_le (r_le_V i)) (hR.thP.vP i A.μ0)
  have hinj := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) (hω i A.μ0).std hθ
    (fun _ => 1) (R.BV i) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) _ hcVI
    (fun ρ => GlobalTheory.AdTh.VecFock.isCartanInv_cart _ ρ) (hR.models.BV i)
    (fun ρ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ ρ _ (hR.models.order i ρ))
    (D.sp.V_sig _) (D.sp.W_sig _) (R.vP i A.μ0) hthv hvv hne

  have key := (hR.thP.ioP i A.μ0).2.1 τ k hk v u hu y
  unfold RealDat.ptP at key
  rw [av] at key
  have hfa := hinj key

  have hA := aω (R.ioP i (PiTensorProduct.tprod ℂ v) y)
  rw [hfa] at hA
  have hser : singleSeries R i ω φ' h y (Function.update v τ u) =
      Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))
        (singleSeries R i ω φ' h y v) := by
    funext g
    simp only [singleSeries, Datum.thetaKO, Formalism.L2.Theta.rTr]
    rw [← hA, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  rw [hser]
  funext g
  simp only [Formalism.IndefR.Links.actL, LinearMap.coe_mk, AddHom.coe_mk, Formalism.L2.Theta.rTr]
  by_cases hl : ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g0) κ
  · have hc := GlobalTheory.FinTranslate.comm_fin_real (Wc D i) hl.choose_spec.1
      (GlobalTheory.FinTranslate.atTau_mem R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))
    simp only [actG0, dif_pos hl, Formalism.L2.Theta.rTr]
    rw [mul_assoc g, hc, ← mul_assoc]
  · simp only [actG0, dif_neg hl, Pi.zero_apply]

end GlobalTheory.SeriesKEquiv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SingleThetaSeriesKEquivariantLowestTypeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.singleThetaSeries_K_equivariant_lowest_type : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (Q' : Finset (Pl D.host.E)) (Ω : DatFn D i) (φ' : WO (Vc D i) (Wc D i) → ℂ), VecOf R i Q' Ω φ' → ∀ (h : GA D (Vc D i)) (y : (R.cV i).W) (g0 : G) (τ : D.what₂.Tau) (k : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε τ) → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (u : lowT (R.MW i (sg0 D A)) τ), ((u : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) = (R.MW i (sg0 D A)).σ τ k ((v τ : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) → Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g0) (singleSeries R i ω φ' h y (Function.update v τ u)) = Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)) (Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g0) (singleSeries R i ω φ' h y v)) := by
  first | exact @GlobalTheory.SeriesKEquiv.singleSeries_kEquiv | exact GlobalTheory.SeriesKEquiv.singleSeries_kEquiv | (intros; apply GlobalTheory.SeriesKEquiv.singleSeries_kEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumEqualSignKernelLossesBounded
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem GlobalTheory.SumSize.TopSize.depSum {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    ∃ S : Finset ℕ, GlobalTheory.NormSum.Exponents S (fun l => if l.Prime then (depL G l : ℝ) else 0) (sig G) := by
  classical
  let c : HeightOneSpectrum (𝓞 D.host.F) → ℕ := fun v => ringChar (𝓞 D.host.F ⧸ v.asIdeal)
  have key : ∀ l : ℕ, l.Prime → depL G l = 0 ∨ ∃ v ∈ G.pl.S0, c v = l ∧ l ≤ Ideal.absNorm v.asIdeal ∧
      depL G l = G.pl.depth sc v := by
    intro l hl
    rcases (G.pl.W0.filter fun PP => (l : 𝓞 D.host.E) ∈ PP.asIdeal).eq_empty_or_nonempty with h | h
    · left; unfold depL; rw [h]; rfl
    · right
      obtain ⟨PP, hPP, e⟩ := Finset.exists_mem_eq_sup _ h (depthAt G)
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hPP
      have h1' : ∃ v ∈ G.pl.S0, G.pl.w v = PP := by
        unfold Places.W0 at h1; simpa only [Finset.mem_image] using h1
      obtain ⟨v, hv, rfl⟩ := h1'
      have hlv : (l : 𝓞 D.host.F) ∈ v.asIdeal := by
        rw [← G.pl.under_w hv]
        change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) l ∈ (G.pl.w v).asIdeal
        rwa [map_natCast]
      haveI := v.isPrime
      haveI : Finite (𝓞 D.host.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
      have h0 : ((l : ℕ) : 𝓞 D.host.F ⧸ v.asIdeal) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hlv
      have hc : c v = l := CharP.ringChar_of_prime_eq_zero hl h0
      refine ⟨v, hv, hc, ?_, ?_⟩
      · have h3 : ((Nat.card (𝓞 D.host.F ⧸ v.asIdeal) : ℕ) : 𝓞 D.host.F ⧸ v.asIdeal) = 0 := by
          haveI := Fintype.ofFinite (𝓞 D.host.F ⧸ v.asIdeal)
          rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hc]
        exact Nat.le_of_dvd Nat.card_pos (ringChar.dvd h3)
      · rw [← (depthAt_w G hv).2, ← e]; unfold depL; congr
  refine ⟨(G.pl.S0.image c).filter Nat.Prime, fun l hl => (Finset.mem_filter.1 hl).2,
    fun l => by dsimp only; split_ifs <;> positivity, fun l hl => ?_, ?_⟩
  · dsimp only
    split_ifs with hp
    · rcases key l hp with h | ⟨v, hv, h, -⟩
      · rw [h, Nat.cast_zero]
      · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨v, hv, h⟩, hp⟩) hl
    · rfl
  have hnn : ∀ v, 0 ≤ (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal) :=
    fun v => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  unfold sig
  rw [← Finset.sum_fiberwise_of_maps_to (g := c) (t := G.pl.S0.image c) (fun w hw => Finset.mem_image_of_mem _ hw)]
  refine le_trans (Finset.sum_le_sum fun l hl => ?_) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset Nat.Prime _)
    fun l _ _ => Finset.sum_nonneg fun v _ => hnn v)
  have hp := (Finset.mem_filter.1 hl).2
  dsimp only
  rw [if_pos hp]
  rcases key l hp with h | ⟨v, hv, h, h1, h2⟩
  · rw [h, Nat.cast_zero, zero_mul]; exact Finset.sum_nonneg fun v _ => hnn v
  · refine le_trans ?_ (Finset.single_le_sum (f := fun v => (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal))
      (fun v _ => hnn v) (Finset.mem_filter.2 ⟨hv, h⟩))
    rw [h2]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast h1)) (Nat.cast_nonneg _)

private theorem GlobalTheory.SumSize.TopSize.sum_le_of_exponents {S : Finset ℕ} {h : ℕ → ℝ} {B : ℝ} (hE : GlobalTheory.NormSum.Exponents S h B)
    (P : Finset ℕ) : ∑ p ∈ P, h p * Real.log p ≤ B := by
  obtain ⟨-, h0, hS, hB⟩ := hE
  calc ∑ p ∈ P, h p * Real.log p ≤ ∑ p ∈ P ∪ S, h p * Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun p _ _ => mul_nonneg (h0 p) (Real.log_natCast_nonneg p))
    _ = ∑ p ∈ S, h p * Real.log p :=
        (Finset.sum_subset Finset.subset_union_right (fun x _ hxS => by rw [hS x hxS, zero_mul])).symm
    _ ≤ _ := hB

private theorem GlobalTheory.SumSize.TopSize.sum_nab_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {X : ℝ} (hX : 0 ≤ X) :
    ∑ p ∈ P, (if (p : ℝ) ≤ X then Real.logb p X else 0) * Real.log p ≤ X * max (Real.log X) 0 := by
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  rcases lt_or_ge X 1 with h1 | h1
  · rw [Finset.filter_false_of_mem, Finset.sum_empty]
    · positivity
    · intro p hp hle
      have : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
      linarith
  · rw [max_eq_left (Real.log_nonneg h1)]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p hp _ => ?_) (UpperTheory.WildA.logSum X h1)
    · obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hp2)), hP p hp1⟩
    · have hp' := (Finset.mem_filter.1 hp).2
      exact mul_nonneg (Real.logb_nonneg (by exact_mod_cast hp'.one_lt) h1) (Real.log_natCast_nonneg p)

private theorem GlobalTheory.SumSize.TopSize.d_le {D : D7} (large₂ : SizeData₂ D) (h : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) :
    (D.host.d : ℝ) ≤ large₂.sc.b := by
  obtain ⟨-, -, -, hf, hm, -⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ h
  obtain ⟨-, -, -, -, -, hb, -⟩ := h
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hN1 : 1 ≤ D.R.N D.R.m := by simp only [Formalism.BasicNotions.Ranks.N]; omega
  have h1 : 1 ≤ D.R.m * D.R.f * D.R.N D.R.m ^ 2 := Nat.mul_pos (Nat.mul_pos (by omega) hf) (by positivity)
  have h2 : (1 : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 := by exact_mod_cast h1
  exact (le_mul_of_one_le_left (Nat.cast_nonneg _) h2).trans hb

private theorem GlobalTheory.SumSize.TopSize.arith {C1 C f m N b lb sg s1 s2 s3 s4 : ℝ} (hC1 : 0 < C1)
    (hC : C1 * 26 + C1 ^ 2 * (|Real.log C1| + 1) ≤ C) (hf : 0 ≤ f) (hm : 0 ≤ m) (hN : 1 ≤ N) (hb : 0 ≤ b) (hlb : 1 ≤ lb)
    (hsg : 0 ≤ sg) (h1 : s1 ≤ lb / 100) (h2 : s2 ≤ lb) (h3 : s3 ≤ sg) (h4 : s4 ≤ C1 * b * (|Real.log C1| + lb)) :
    C1 * m * (13 * f * N * b) * s1 + C1 * m * (13 * f * N * b) * s2 + C1 * m * (13 * f * N * b) * s3 +
      C1 * m * (f * N ^ 2) * s4 ≤ C * f * m * N ^ 2 * (lb + sg) * b := by
  have hM0 : 0 ≤ f * m * N ^ 2 * b * (lb + sg) := by positivity
  have hNN : N ≤ N ^ 2 := by nlinarith
  have hT1 : C1 * m * (13 * f * N * b) * (s1 + s2 + s3) ≤ C1 * 26 * (f * m * N ^ 2 * b * (lb + sg)) := by
    calc C1 * m * (13 * f * N * b) * (s1 + s2 + s3) ≤ C1 * m * (13 * f * N * b) * (2 * (lb + sg)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ C1 * m * (13 * f * N ^ 2 * b) * (2 * (lb + sg)) := by gcongr
      _ = _ := by ring
  have h5 : |Real.log C1| + lb ≤ (|Real.log C1| + 1) * (lb + sg) := by nlinarith [abs_nonneg (Real.log C1)]
  have hT2 : C1 * m * (f * N ^ 2) * s4 ≤ C1 ^ 2 * (|Real.log C1| + 1) * (f * m * N ^ 2 * b * (lb + sg)) := by
    calc C1 * m * (f * N ^ 2) * s4 ≤ C1 * m * (f * N ^ 2) * (C1 * b * (|Real.log C1| + lb)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ C1 * m * (f * N ^ 2) * (C1 * b * ((|Real.log C1| + 1) * (lb + sg))) := by gcongr
      _ = _ := by ring
  have hC0 := mul_le_mul_of_nonneg_right hC hM0
  calc _ = C1 * m * (13 * f * N * b) * (s1 + s2 + s3) + C1 * m * (f * N ^ 2) * s4 := by ring
    _ ≤ (C1 * 26 + C1 ^ 2 * (|Real.log C1| + 1)) * (f * m * N ^ 2 * b * (lb + sg)) := by linarith
    _ ≤ C * (f * m * N ^ 2 * b * (lb + sg)) := hC0
    _ = _ := by ring

open GlobalTheory.SumSize.TopInt GlobalTheory.SumSize.TopSize in
private theorem GlobalTheory.SumSize.TopSize.core {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T)
    (large₂ : SizeData₂ D) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (hH : HostHyp D) (hc : sc.cGap = 1) {C1 C : ℝ} (hC1 : 0 < C1)
    (hC : C1 * 26 + C1 ^ 2 * (|Real.log C1| + 1) ≤ C) {S : Finset ℕ} {δ : ℕ → ℝ}
    (hδ : GlobalTheory.NormSum.Exponents S δ (Real.log D.host.rdE)) :
    Loss (topDl G δ C1 large₂.sc.b) (bOne G C large₂.sc.b) := by
  classical
  obtain ⟨Sd, hSd⟩ := depSum G
  obtain ⟨-, -, hN, -, -, -, hrd, hb12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hs
  have hd := d_le large₂ hs
  have hker : ∀ j, j < D.R.m → ((∑ τ, ∑ a, (wt G (.top (j + 1)) τ).natW a : ℕ) : ℝ) +
      (D.R.f : ℝ) * (G.V (.top j)).rank * (G.V (.top (j + 1))).rank ≤ 13 * D.R.f * bigN D * large₂.sc.b :=
    fun j hj => UpperTheory.WildA.kerLe (G := G) large₂ hs hH hc (.top t j) hj
  generalize large₂.sc.b = b at *
  have hδ0 := hδ.2.1
  have hlb : 1 ≤ Real.log b := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hsig : 0 ≤ sig G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  set h : ℕ → ℝ := fun l => if l.Prime then
    C1 * ∑ j ∈ Finset.range D.R.m, kerLoss G δ C1 b (.top j) (.top (j + 1)) l (depL G l) else 0 with hh
  set P : Finset ℕ := (S ∪ {D.host.d} ∪ Sd ∪ Finset.range (⌊C1 * b⌋₊ + 1)).filter Nat.Prime with hP
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.1 hp).2
  have e : topDl G δ C1 b = fun w : PlL D => (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) * h (primeUnder w) := by
    funext w
    simp only [hh, if_pos (primeUnder_prime w), topDl, mul_assoc]
  rw [e]
  refine UpperTheory.WildA.expLoss D P h _ ⟨hPp, fun l => ?_, fun l hl => ?_, ?_⟩
  · simp only [hh]
    split_ifs with hl
    · exact mul_nonneg hC1.le (Finset.sum_nonneg fun j _ => kerLoss_nonneg G hδ0 C1 b _ _ hl _)
    · exact le_rfl
  · simp only [hh]
    split_ifs with hp
    · simp only [hP, Finset.mem_filter, hp, and_true, Finset.mem_union, Finset.mem_singleton, Finset.mem_range, not_or] at hl
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hl
      have e1 := hδ.2.2.1 l h1
      have e3 : (depL G l : ℝ) = 0 := by simpa only [if_pos hp] using hSd.2.2.1 l h3
      have e4 : ¬ (l : ℝ) ≤ C1 * b := fun h5 => h4 (Nat.lt_succ_of_le (Nat.le_floor h5))
      simp only [kerLoss, e1, e3, if_neg h2, if_neg e4, add_zero, mul_zero, Finset.sum_const_zero]
    · rfl
  have hKp : ∀ p ∈ P, h p * Real.log p ≤
      C1 * D.R.m * (13 * D.R.f * bigN D * b) * (δ p * Real.log p) +
        C1 * D.R.m * (13 * D.R.f * bigN D * b) * ((if p = D.host.d then (1 : ℝ) else 0) * Real.log p) +
        C1 * D.R.m * (13 * D.R.f * bigN D * b) * ((if p.Prime then (depL G p : ℝ) else 0) * Real.log p) +
        C1 * D.R.m * (D.R.f * (bigN D : ℝ) ^ 2) * ((if (p : ℝ) ≤ C1 * b then Real.logb p (C1 * b) else 0) * Real.log p) := by
    intro p hp
    have hM : 0 ≤ δ p + (if p = D.host.d then (1 : ℝ) else 0) + (depL G p : ℝ) := by
      have := hδ0 p
      have : 0 ≤ (if p = D.host.d then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      positivity
    have hK := Finset.sum_le_card_nsmul (Finset.range D.R.m)
      (fun j => kerLoss G δ C1 b (.top j) (.top (j + 1)) p (depL G p))
      ((13 * D.R.f * bigN D * b) * (δ p + (if p = D.host.d then 1 else 0) + (depL G p : ℝ)) +
        D.R.f * (bigN D : ℝ) ^ 2 * (if (p : ℝ) ≤ C1 * b then Real.logb p (C1 * b) else 0)) (fun j hj => by
        unfold kerLoss
        exact add_le_add (mul_le_mul_of_nonneg_right (hker j (Finset.mem_range.1 hj)) hM) le_rfl)
    rw [Finset.card_range, nsmul_eq_mul] at hK
    have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    simp only [hh, if_pos (hPp p hp)]
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hC1.le) hlp).trans (le_of_eq ?_)
    ring
  have hs2 : ∑ p ∈ P, (if p = D.host.d then (1 : ℝ) else 0) * Real.log p ≤ Real.log b := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    split_ifs with hdP
    · exact Real.log_le_log (by exact_mod_cast (hPp _ hdP).pos) hd
    · linarith
  have hs4 : ∑ p ∈ P, (if (p : ℝ) ≤ C1 * b then Real.logb p (C1 * b) else 0) * Real.log p ≤
      C1 * b * (|Real.log C1| + Real.log b) := by
    have h0 : 0 ≤ C1 * b := mul_nonneg hC1.le (by linarith)
    refine (sum_nab_le P hPp h0).trans (mul_le_mul_of_nonneg_left ?_ h0)
    rw [Real.log_mul hC1.ne' (by linarith)]
    exact max_le (by linarith [le_abs_self (Real.log C1)]) (by linarith [abs_nonneg (Real.log C1)])
  refine (Finset.sum_le_sum hKp).trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact arith hC1 hC (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hN) (by linarith) hlb hsig
    ((sum_le_of_exponents hδ P).trans hrd) hs2 (sum_le_of_exponents hSd P) hs4

theorem _root_.GlobalTheory.T.sum_equalSign_kernel_losses_bounded : ∀ C1 : ℝ, 0 < C1 → ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ C0 : ℝ, ∀ ε C : ℝ, C0 ≤ C → ∃ x₀ : ℝ,
      ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
      ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → GlobalTheory.NormSum.Inp D →
      ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ →
        Loss (GlobalTheory.SumSize.TopInt.topDl ch.G δ C1 large₂.sc.b) (bOne ch.G C large₂.sc.b) := by
  intro C1 hC1
  refine ⟨0, fun CF _ => ⟨C1 * 26 + C1 ^ 2 * (|Real.log C1| + 1), fun ε C hC => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch _ hAt _ _ S δ hLet
  have hc : ch.sc.cGap = 1 := by rw [hAt]
  exact GlobalTheory.SumSize.TopSize.core ch.G A.μ0 large₂ hSet.size hSet.host hc hC1 hC ⟨hLet.1, hLet.2.1, hLet.2.2.1, hLet.2.2.2.1⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsTransportedActionFinitePointPreimage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsTransportedActionFinitePointPreimage
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

open Topology Filter

namespace GlobalTheory.WeilTransNbhd

variable (F : Type) [Field F] [NumberField F]

theorem exists_compact_open_subgroup (κ : Type) [Fintype κ] {S : Set (κ → FiniteAdeleRing (𝓞 F) F)}
    (hS : S ∈ 𝓝 0) : ∃ U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ S := by
  classical
  have hS' : S ∈ 𝓝 (fun _ : κ => (0 : FiniteAdeleRing (𝓞 F) F)) := hS
  rw [nhds_pi, Filter.mem_pi] at hS'
  obtain ⟨I, -, t, ht, hsub⟩ := hS'
  have hO : (⋂ i, t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.2 ht
  have hbox : ∀ u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i, u i ∈ ⋂ i, t i) → u ∈ S :=
    fun u hu => hsub fun i _ => Set.mem_iInter.1 (hu i) i
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hO
  let c : FiniteAdeleRing (𝓞 F) F := algebraMap F _ ((N : F)⁻¹)
  have hcN : (N : FiniteAdeleRing (𝓞 F) F) * c = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
  have hNc : c * (N : FiniteAdeleRing (𝓞 F) F) = 1 := by rw [mul_comm]; exact hcN
  let h : (κ → FiniteAdeleRing (𝓞 F) F) ≃ₜ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun u i => c * u i
      invFun := fun u i => (N : FiniteAdeleRing (𝓞 F) F) * u i
      left_inv := fun u => funext fun i => by
        show (N : FiniteAdeleRing (𝓞 F) F) * (c * u i) = u i
        rw [← mul_assoc, hcN, one_mul]
      right_inv := fun u => funext fun i => by
        show c * ((N : FiniteAdeleRing (𝓞 F) F) * u i) = u i
        rw [← mul_assoc, hNc, one_mul]
      continuous_toFun := continuous_pi fun i => continuous_const.mul (continuous_apply i)
      continuous_invFun := continuous_pi fun i => continuous_const.mul (continuous_apply i) }
  let φ : (κ → FiniteAdeleRing (𝓞 F) F) →+ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun u i => c * u i
      map_zero' := by funext i; exact mul_zero c
      map_add' := fun u w => by funext i; exact mul_add c (u i) (w i) }
  let U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) :=
    (AddSubgroup.pi Set.univ fun _ => (Formalism.UG.intAd F).toAddSubgroup).comap φ
  have hUset : (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      h ⁻¹' Set.univ.pi fun _ => (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := rfl
  have hint_c : IsCompact (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.Col.rlt_isCompact_intAd
  have hint_o : IsOpen (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.SG.Pf.top_isOpen_intAd F
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [hUset]; exact (isOpen_set_pi Set.finite_univ fun _ _ => hint_o).preimage h.continuous
  · rw [hUset]; exact h.isCompact_preimage.2 (isCompact_univ_pi fun _ => hint_c)
  · intro u hu
    refine hbox u fun i => ?_
    have hi : c * u i ∈ Formalism.UG.intAd F := hu i (Set.mem_univ i)
    have := hNO (c * u i) hi
    rwa [nsmul_eq_mul, ← mul_assoc, hcN, one_mul] at this

def finIdem : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))

variable {F}

theorem finIdem_smul_eq {κ : Type} (w : κ → AF F) :
    finIdem F • w = GlobalTheory.WeilCont.adeleJoin F 0 (fun i => (w i).2) := by
  funext i
  refine Prod.ext ?_ ?_
  · show (0 : InfiniteAdeleRing F) * (w i).1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ((0 : κ → mixedEmbedding.mixedSpace F) i)
    rw [zero_mul, Pi.zero_apply, map_zero]
  · show (1 : FiniteAdeleRing (𝓞 F) F) * (w i).2 = (w i).2
    exact one_mul _

theorem finIdem_smul_adeleJoin {κ : Type} (x : κ → FiniteAdeleRing (𝓞 F) F) :
    finIdem F • GlobalTheory.WeilCont.adeleJoin F 0 x = GlobalTheory.WeilCont.adeleJoin F 0 x :=
  finIdem_smul_eq _

theorem adeleJoin_zero_zero {κ : Type} :
    GlobalTheory.WeilCont.adeleJoin F (0 : κ → mixedEmbedding.mixedSpace F) 0 = 0 := by
  funext i
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ((0 : κ → mixedEmbedding.mixedSpace F) i) = 0
  rw [Pi.zero_apply, map_zero]

theorem continuous_adeleJoin_zero {κ : Type} :
    Continuous fun x : κ → FiniteAdeleRing (𝓞 F) F => GlobalTheory.WeilCont.adeleJoin F 0 x :=
  continuous_pi fun i => (continuous_const.prodMk (continuous_apply i) :
    Continuous fun x : κ → FiniteAdeleRing (𝓞 F) F =>
      (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ((0 : κ → mixedEmbedding.mixedSpace F) i), x i) :
        InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end GlobalTheory.WeilTransNbhd

end

noncomputable section

open Topology Filter

namespace GlobalTheory.WeilTransNbhd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem actAB_smul (σ : E →ₐ[F] E) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {JA : Matrix α α (AF F ⊗[F] E)} {JB : Matrix β β (AF F ⊗[F] E)} (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JA × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JB) (r : AF F)
    (X : Matrix α β (AF F ⊗[F] E)) : actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p (r • X) = r • actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p X := by
  unfold actAB
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem actAB_mul_inv (σ : E →ₐ[F] E) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {JA : Matrix α α (AF F ⊗[F] E)} {JB : Matrix β β (AF F ⊗[F] E)} (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JA × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JB)
    (X : Matrix α β (AF F ⊗[F] E)) : actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p (actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p⁻¹ X) = X := by
  unfold actAB
  have h1 : ((p.1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) * (((p⁻¹).1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) = 1 := by
    show ((p.1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) * (((p.1)⁻¹ : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) = 1
    exact Units.mul_inv _
  have h2 : (((p⁻¹).2 : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ * ((p.2 : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    show ((p.2 : GL β (AF F ⊗[F] E)) * ((p.2)⁻¹ : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ = 1
    rw [Units.mul_inv, Matrix.transpose_one]
  calc _ = ((p.1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) * (((p⁻¹).1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) * X *
        ((((p⁻¹).2 : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ * ((p.2 : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem exists_nhds_finite_preimage : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (ξ : AF F ⊗[F] E) (κ : Type) [Fintype κ]
    (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ) (L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)),
    IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    ∀ p0 : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB),
    ∃ N ∈ nhds p0, ∃ L₁' L₂' : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsCompact (L₁' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsOpen (L₂' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ p ∈ N, ∀ x ∈ L₁', ∀ y ∈ L₂', ∃ x' ∈ L₁, ∃ y' ∈ L₂,
        co.e (actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 x', GlobalTheory.WeilCont.adeleJoin F 0 y'))) =
          (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) := by
  intro F E _ _ _ _ _ σ a b JA JB ξ κ _ co L₁ L₂ hL₁ hL₂ p0
  haveI hmt : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin a) (Fin b) (AF F ⊗[F] E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin a → Fin b → AF F ⊗[F] E))
  haveI : ContinuousSMul (AF F) (Matrix (Fin a) (Fin b) (AF F ⊗[F] E)) :=
    inferInstanceAs (ContinuousSMul (AF F) (Fin a → Fin b → AF F ⊗[F] E))
  have hce : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  have hcs : Continuous co.e.symm := IsModuleTopology.continuous_of_linearMap co.e.symm.toLinearMap
  let Ψ : (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) → (κ → AF F) × (κ → AF F) :=
    fun q => co.e (actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) q.1⁻¹ (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 q.2.1, GlobalTheory.WeilCont.adeleJoin F 0 q.2.2)))
  let Φ : (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) →
      (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) :=
    fun q => (fun i => ((Ψ q).1 i).2, fun i => ((Ψ q).2 i).2)
  have hinv : Continuous fun q : (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) => q.1⁻¹ := continuous_fst.inv
  have hm1 : Continuous fun q : (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) =>
      (((q.1⁻¹).1 : GL (Fin a) (AF F ⊗[F] E)) : Matrix (Fin a) (Fin a) (AF F ⊗[F] E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (continuous_fst.comp hinv))
  have hm2 : Continuous fun q : (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) =>
      (((q.1⁻¹).2 : GL (Fin b) (AF F ⊗[F] E)) : Matrix (Fin b) (Fin b) (AF F ⊗[F] E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (continuous_snd.comp hinv))
  have hv : Continuous fun q : (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) =>
      co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 q.2.1, GlobalTheory.WeilCont.adeleJoin F 0 q.2.2) :=
    hcs.comp ((continuous_adeleJoin_zero.comp (continuous_fst.comp continuous_snd)).prodMk
      (continuous_adeleJoin_zero.comp (continuous_snd.comp continuous_snd)))
  have hΨ : Continuous Ψ := hce.comp ((hm1.matrix_mul hv).matrix_mul hm2.matrix_transpose)
  have hΦ : Continuous Φ :=
    (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_fst.comp hΨ))).prodMk
      (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_snd.comp hΨ)))
  have hΦ0 : Φ (p0, (0, 0)) = (0, 0) := by
    have : Ψ (p0, (0, 0)) = 0 := by
      simp only [Ψ, adeleJoin_zero_zero]
      rw [show ((0 : κ → AF F), (0 : κ → AF F)) = 0 from rfl, map_zero]
      rw [show actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p0⁻¹ (0 : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)) = 0 by
        unfold actAB; rw [Matrix.mul_zero, Matrix.zero_mul], map_zero]
    simp only [Φ, this]
    rfl
  have hopen : IsOpen (Φ ⁻¹' ((L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ×ˢ (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)))) :=
    (hL₁.prod hL₂).preimage hΦ
  have hmem : (p0, ((0 : κ → FiniteAdeleRing (𝓞 F) F), (0 : κ → FiniteAdeleRing (𝓞 F) F))) ∈
      Φ ⁻¹' ((L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ×ˢ (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F))) := by
    rw [Set.mem_preimage, hΦ0]
    exact ⟨L₁.zero_mem, L₂.zero_mem⟩
  obtain ⟨N, hN, V, hV, hNV⟩ := mem_nhds_prod_iff.1 (hopen.mem_nhds hmem)
  rw [← Prod.zero_eq_mk, nhds_prod_eq] at hV
  obtain ⟨V₁, hV₁, V₂, hV₂, hV12⟩ := mem_prod_iff.1 hV
  obtain ⟨L₁', hL₁'o, hL₁'c, hL₁'s⟩ := exists_compact_open_subgroup F κ hV₁
  obtain ⟨L₂', hL₂'o, -, hL₂'s⟩ := exists_compact_open_subgroup F κ hV₂
  refine ⟨N, hN, L₁', L₂', hL₁'o, hL₁'c, hL₂'o, fun p hp x hx y hy => ?_⟩
  have hin := hNV (Set.mk_mem_prod hp (hV12 (Set.mk_mem_prod (hL₁'s hx) (hL₂'s hy))))
  refine ⟨(Φ (p, (x, y))).1, hin.1, (Φ (p, (x, y))).2, hin.2, ?_⟩

  have hfin : (GlobalTheory.WeilCont.adeleJoin F 0 (Φ (p, (x, y))).1, GlobalTheory.WeilCont.adeleJoin F 0 (Φ (p, (x, y))).2) =
      Ψ (p, (x, y)) := by
    have e1 : Ψ (p, (x, y)) = finIdem F • Ψ (p, (x, y)) := by
      simp only [Ψ]
      conv_lhs => rw [← finIdem_smul_adeleJoin x, ← finIdem_smul_adeleJoin y, ← Prod.smul_mk, map_smul,
        actAB_smul, map_smul]
    rw [e1]
    refine Prod.ext ?_ ?_
    · rw [Prod.smul_fst, finIdem_smul_eq]
    · rw [Prod.smul_snd, finIdem_smul_eq]
  rw [hfin]
  simp only [Ψ, LinearEquiv.symm_apply_apply, actAB_mul_inv, LinearEquiv.apply_symm_apply]

end GlobalTheory.WeilTransNbhd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsTransportedActionFinitePointPreimageStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_transportedAction_finitePoint_preimage : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (ξ : AF F ⊗[F] E) (κ : Type) [Fintype κ]
    (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ) (L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)),
    IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    ∀ p0 : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB),
    ∃ N ∈ nhds p0, ∃ L₁' L₂' : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsCompact (L₁' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsOpen (L₂' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ p ∈ N, ∀ x ∈ L₁', ∀ y ∈ L₂', ∃ x' ∈ L₁, ∃ y' ∈ L₂,
        co.e (actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 x', GlobalTheory.WeilCont.adeleJoin F 0 y'))) =
          (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) := by
  first | exact @GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage | exact GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage | (intros; apply GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage <;> assumption)
end
end
