module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBExtFunEqHalfInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftsAllChartsEqClassSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MvZOneEqMapUnivSubst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInvertibleFamilyEvalSpan
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHermIsUnitGeneric
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTranslateOrthogonalOfSupportMovedOff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingBasicIdentityUnfolding

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LatIndHalf

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_one (p : SplitPt D k) : p.sec 1 = p.e := by
  rw [← map_one p.pr, p.sec_pr, mul_one]

theorem e_mul_sec (p : SplitPt D k) (a : k) : p.e * p.sec a = p.sec a := by
  rw [← p.sec_pr, p.pr_sec]

theorem sec_mul (p : SplitPt D k) (a b : k) : p.sec (a * b) = p.sec a * p.sec b :=
  calc p.sec (a * b) = p.sec (p.pr (p.sec a * p.sec b)) := by rw [map_mul p.pr, p.pr_sec, p.pr_sec]
    _ = p.e * (p.sec a * p.sec b) := p.sec_pr _
    _ = p.sec a * p.sec b := by rw [← mul_assoc, e_mul_sec]

theorem e_mem_idAt (p : SplitPt D k) : p.e ∈ idAt D (· = p.v) := by
  obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem p
  obtain ⟨α, rfl, -, h0⟩ := hε
  have hmem : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) ∈ idAt D (· = p.v) := by
    rw [show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) from rfl]
    unfold idAt
    rw [Submodule.mem_inf, RingHom.mem_ker, Submodule.mem_iInf]
    refine ⟨?_, fun w => RingHom.mem_ker.2 ?_⟩
    · change fstA D.host.F (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    · change evalV D.host.F w.1 α ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [h0 w.1 w.2, TensorProduct.zero_tmul]
  rw [← heε]
  exact Ideal.mul_mem_right _ _ hmem

theorem mul_mem_latV {S : HSp D} {L : Lat S} {P : Pl D → Prop} {w : AE D} (hw : finPart D w ∈ intAE D)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : (fun i => w * y i) ∈ latV S L P := by
  let Ψ : (Fin S.rank → AE D) →+ (Fin S.rank → AE D) :=
    AddMonoidHom.mk' (fun y i => w * y i) fun a b => funext fun i => mul_add w (a i) (b i)
  have main : latV S L P ≤ (latV S L P).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ (Fin S.rank → AE D) :=
      AddMonoidHom.mk' (fun c i => GlobalTheory.LatticeStable.liftFin D (c * (β ⊗ₜ[D.host.F] (1 * x i))))
        fun c c' => funext fun i => by rw [add_mul, LinearMap.map_add (f := _)]; rfl
    have hle : intAE D ≤ (latV S L P).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨γ, hγ, o, rfl⟩
      refine AddSubgroup.subset_closure ⟨γ * β, fun v => by rw [map_mul]; exact mul_mem (hγ v) (hβi v),
        fun v hv => by rw [map_mul, hβ v hv, mul_zero], 1, rfl, o • x, L.smul_mem o hx, ?_⟩
      funext i
      change GlobalTheory.LatticeStable.liftFin D ((γ ⊗ₜ[D.host.F] (o : D.host.E)) * (β ⊗ₜ[D.host.F] (1 * x i))) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.LatticeStable.liftFin_tmul, Pi.smul_apply, Algebra.smul_def,
        show algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) from rfl]
      congr 1
      ring
    have e : Ψ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) = Φ (finPart D w) :=
      funext fun i => GlobalTheory.LatticeStable.mul_pair_tmul D w β _
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, e]
    exact hle hw
  exact main hy

variable {p : SplitPt D k} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem mulVec_sec (α : Frame p S n') (β : Frame p T n) {t : WO S T} (ht : IsHalf p.e t) (x : n' → k) :
    t *ᵥ (fun j => p.sec ((α.b *ᵥ x) j)) = fun i => p.sec ((β.b *ᵥ (rd α β t *ᵥ x)) i) := by
  have hM : (β.b * rd α β t * α.b') *ᵥ (α.b *ᵥ x) = β.b *ᵥ (rd α β t *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (β.b * rd α β t), α.b'b, Matrix.mul_one, Matrix.mulVec_mulVec]
  rw [← hM]
  funext i
  conv_lhs => rw [← GlobalTheory.FinPl.HalfInd.wr_rd α β ht]
  simp only [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.HalfInd.wr_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => (sec_mul p _ _).symm

theorem mem_latO_iff_rd (α : Frame p S n') (β : Frame p T n) {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) (hU : p.UnitAA) {ΛS : Submodule 𝒪[k] (n' → k)} {ΛT : Submodule 𝒪[k] (n → k)}
    (hα : α.IsLat LS ΛS) (hβ : β.IsLat LT ΛT) {t : WO S T} (ht : IsHalf p.e t) :
    t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ↔ ∀ x ∈ ΛS, rd α β t *ᵥ x ∈ ΛT := by
  have hmem := GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT (· = p.v) t
  rw [hU.2 T LT] at hmem
  constructor
  · intro h x hx
    have h1 : t *ᵥ (fun j => p.sec ((α.b *ᵥ x) j)) ∈ latV T LT (· = p.v) := (hmem.1 h).2 _ ((hα x).1 hx)
    rw [mulVec_sec α β ht] at h1
    exact (hβ _).2 h1
  · intro h
    refine hmem.2 ⟨fun i j => ?_, fun y hy => ?_⟩
    · rw [← ht i j]
      exact Ideal.mul_mem_right _ _ (e_mem_idAt p)
    · have hy' : t *ᵥ y = t *ᵥ (fun j => p.e * y j) := by
        funext i
        simp only [Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_assoc, mul_comm (t i j) p.e, ht i j]
      have hey : (fun j => p.e * y j) = fun j => p.sec ((α.b *ᵥ (α.b' *ᵥ fun j => p.pr (y j))) j) := by
        funext j
        rw [Matrix.mulVec_mulVec, α.bb', Matrix.one_mulVec, p.sec_pr]
      have hint : finPart D p.e ∈ intAE D := by
        rw [← sec_one p]
        exact (p.int_iff 1).1 (one_mem _)
      have hx : α.b' *ᵥ (fun j => p.pr (y j)) ∈ ΛS := (hα _).2 (hey ▸ mul_mem_latV hint hy)
      show t *ᵥ y ∈ latV T LT (· = p.v)
      rw [hy', hey, mulVec_sec α β ht]
      exact (hβ _).1 (h _ hx)

end GlobalTheory.FinPl.LatIndHalf

theorem GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → p.UnitAA → ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT → extFun α β (latInd ΛS ΛT) = halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT hU ΛS ΛT hα hβ
  funext t
  unfold extFun halfInd
  by_cases ht : IsHalf p.e t
  · rw [if_pos ht]
    unfold latInd
    have key := GlobalTheory.FinPl.LatIndHalf.mem_latO_iff_rd α β hS hT hU hα hβ ht
    by_cases h : t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v)
    · rw [if_pos (key.1 h), if_pos ⟨h, ht⟩]
    · rw [if_neg fun h' => h (key.2 h'), if_neg fun h' => h h'.1]
  · rw [if_neg ht, if_neg fun h => ht h.2]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → p.UnitAA → ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT → extFun α β (latInd ΛS ΛT) = halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) := by
  first | exact @GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd | exact GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd | (intros; apply GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepWeilDatumNonzeroFockVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepWeilDatumNonzeroFockVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.StepExp

variable {D : D7}

theorem chrStep_exp' {c : Com D} (hc : c.Is) (k : Fin D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (c.chS ((k : ℕ) + 1)) τ (expS D k τ) ∧ HasInfExp D (c.chT ((k : ℕ) + 1)) τ (expT D k τ) := by
  have h1 : HasInfExp D (c.μ ((k : ℕ) + 1)) τ (-(D.hc τ).e k) := hc.exp k τ
  have h2 : HasInfExp D c.η τ (1 / 2) := hc.chars.2.2.2.1 τ
  have h3 := GlobalTheory.Chain.StepVac.hasInfExp_mul h1 (GlobalTheory.Chain.StepVac.hasInfExp_inv h2)
  unfold Com.chS Com.chT Lift.chrStep expS expT
  by_cases hk : Even (k : ℕ)
  · rw [if_pos hk.add_one, if_pos hk, if_pos hk, sub_zero, sub_eq_add_neg]
    exact ⟨h3, h1⟩
  · rw [if_neg (by rwa [Nat.odd_add_one, Nat.not_odd_iff_even]), if_neg hk, if_neg hk, sub_zero, sub_eq_add_neg]
    exact ⟨h1, h3⟩

theorem stepExpVac : ∀ D : D7, GlobalTheory.ChainOnto.ForStep D fun c k s s' p => ∀ hk : k < D.R.m,
    IsWeilExp c.ψ s.V s'.V (expS D ⟨k, hk⟩) (expT D ⟨k, hk⟩) p.ω ∧ IsVacVec c.ψ c.θ s.M s'.M p.f := by
  intro D _ c hc k _ s s' hs hs' p hp hk
  refine ⟨⟨c.chS (k + 1), c.chT (k + 1), hp.weil, fun τ => chrStep_exp' hc ⟨k, hk⟩ τ⟩, ?_⟩
  obtain ⟨ξ, f₀, hv⟩ := hp.vec
  have hr : s.V.rank ≤ s'.V.rank := by
    rw [hs.rank, hs'.rank]
    show D.R.r + k * D.R.t ≤ D.R.r + (k + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ k)) _
  obtain ⟨a, b, d⟩ := GlobalTheory.Chain.StepVac.stepVec_vac hs.selfDual hs'.selfDual hr hv
  exact ⟨a, b, d⟩

end GlobalTheory.ChainOnto.StepExp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepWeilDatumNonzeroFockVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStep_weilDatum_nonzero_fockVacuum : ∀ D : D7, GlobalTheory.ChainOnto.ForStep D fun c k s s' p => ∀ hk : k < D.R.m, IsWeilExp c.ψ s.V s'.V (expS D ⟨k, hk⟩) (expT D ⟨k, hk⟩) p.ω ∧ IsVacVec c.ψ c.θ s.M s'.M p.f := by
  first | exact @GlobalTheory.ChainOnto.StepExp.stepExpVac | exact GlobalTheory.ChainOnto.StepExp.stepExpVac | (intros; apply GlobalTheory.ChainOnto.StepExp.stepExpVac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodMajorantLevelConjUnitaryAdelicMaximalCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodMajorantLevelConjUnitaryAdelicMaximalCompact
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch

theorem good_level_conj_stab : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D)), IsMaj T b → HasIw d (Kmax T b) → ∀ l : Lvl T, l.Good → HasIw d l.K ∧ IsCompact (l.K : Set (GA D T)) ∧ ∃ q : stab d, ConjBy (q : GA D T) l.K (Kmax T b) := by
  intro D T T₀ r d b hb hIw l hl
  have hL0 : GlobalTheory.EisCont.IsLevel T (AdelicU.frameLat T) b :=
    ⟨(AdelicU.SelfDual.isLattice_frameLat T).toIsLattice, AdelicU.SelfDual.isSelfDualAt_frameLat D T, hb⟩
  have hL : GlobalTheory.EisCont.IsLevel T l.L l.c := ⟨hl.1.toIsLattice, hl.2.1, hl.2.2⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_adelic_unitary_conj_selfDual_majorant_levels D T (AdelicU.frameLat T) l.L b l.c hL0 hL
  obtain ⟨q, k₀, hk₀, hgq⟩ := hIw g
  have hconj : ConjBy (q : GA D T) l.K (Kmax T b) := by
    intro k
    have h1 : k ∈ l.K ↔ g⁻¹ * k * g ∈ Kmax T b := hg k
    rw [h1, hgq]
    constructor
    · intro h
      have := (Kmax T b).mul_mem (hk₀) ((Kmax T b).mul_mem h ((Kmax T b).inv_mem hk₀))
      simpa [mul_assoc] using this
    · intro h
      have := (Kmax T b).mul_mem ((Kmax T b).inv_mem hk₀) ((Kmax T b).mul_mem h hk₀)
      simpa [mul_assoc] using this
  haveI : Submodule.IsFullLattice D.host.E l.L := hl.1
  refine ⟨?_, isCompact_levelAll (AdelicU.isCMExt_host D) _ _ _, q, hconj⟩
  intro h
  obtain ⟨q₁, k₁, hk₁, e⟩ := hIw (h * q)
  refine ⟨q₁ * q⁻¹, (q : GA D T) * k₁ * (q : GA D T)⁻¹, ?_, ?_⟩
  · rw [hconj]
    simpa [mul_assoc] using hk₁
  · have : h = (q₁ : GA D T) * k₁ * (q : GA D T)⁻¹ := by rw [← e]; group
    rw [this]; simp [mul_assoc]

end GlobalTheory.RegSch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodMajorantLevelConjUnitaryAdelicMaximalCompactStatement
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodMajorantLevel_conj_unitaryAdelicMaximalCompact : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D)), IsMaj T b → HasIw d (Kmax T b) → ∀ l : Lvl T, l.Good → HasIw d l.K ∧ IsCompact (l.K : Set (GA D T)) ∧ ∃ q : stab d, ConjBy (q : GA D T) l.K (Kmax T b) := by
  first | exact @GlobalTheory.RegSch.good_level_conj_stab | exact GlobalTheory.RegSch.good_level_conj_stab | (intros; apply GlobalTheory.RegSch.good_level_conj_stab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawKernelLiftCombinationOfDefiniteClassData
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawKernelLiftCombinationOfDefiniteClassData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem kerX_of_clsPinD : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → KerX t := by
  intro D c 𝒯 t hc ht hP
  obtain ⟨ρ, hρ, hA⟩ := hP
  intro j hj y P
  have hj1 : j + 1 ≤ D.R.m := hj
  obtain ⟨hpos, hab⟩ := hρ.rk j hj
  obtain ⟨hB, ν, hν1, hνL, hmain⟩ := GlobalTheory.T.thetaLifts_all_charts_eq_classSum D c ρ hc hρ j hj1 hab
  obtain ⟨m', y', s, hinv, havg⟩ := @GlobalTheory.KJAvg.avg_span D.what₂.Tau _ (ρ.N j) (ρ.N (j + 1)) hab hpos (ρ.lam j) (ρ.n j)
    (GinfC (c.X j)) _ _ _ _ hB ν hν1 hνL (fun k τ => ρ.r j (Nat.le_of_succ_le hj1) k.1 τ) (hρ.uni j _) (ρ.fr j y).1
    (castP (ρ.hN j (Nat.le_of_succ_le hj1)) (ρ.hN (j + 1) hj1) P)
  have hz : ∀ i, ∀ τ, IsUnit ((fun τ => ρ.sc j τ • y' i τ) τ).det := by
    intro i τ
    simp only [Matrix.det_smul]
    exact (IsUnit.pow _ (Ne.isUnit (hρ.sc j τ))).mul (hinv i τ)
  let z : Fin m' → FrN D (ρ.N (j + 1)) := fun i => ⟨fun τ => ρ.sc j τ • y' i τ, hz i⟩
  let y'' : Fin m' → c.Fr (j + 1) := fun i => (ρ.fr (j + 1)).symm (z i)
  let cst : ℂ := ∏ τ, ((ρ.fr j y).1 τ).det ^ (-ρ.sS j τ)
  have key := hmain 1 (fun _ => y) (fun _ => P) m' y' y'' (fun i => cst * s i)
    (by intro i τ; simp only [y'', Equiv.apply_symm_apply]; rfl)
    (by
      intro F hF Λ
      rw [Fin.sum_univ_one, havg F hF Λ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)
  refine ⟨∑ i, Finsupp.single (y'' i) (cst * s i * ∏ τ, ((ρ.fr (j + 1) (y'' i)).1 τ).det ^ ρ.sD j τ), ?_⟩
  intro s' ψ hψ γ
  obtain ⟨⟨A, hA'⟩, _⟩ := hA s'
  have h1 := key (t s') A (ht s') hA' ψ hψ γ
  rw [Fin.sum_univ_one] at h1
  rw [h1]
  congr 1
  change _ = Finsupp.sum _ (fun y' b => b • (t s').rd (j + 1) γ ((t s').K j ψ) y')
  rw [Finsupp.sum_finsetSum _ _ (fun y' b => b • (t s').rd (j + 1) γ ((t s').K j ψ) y')
    (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sum_single_index (h := fun y' b => b • (t s').rd (j + 1) γ ((t s').K j ψ) y') (zero_smul ℂ _)]

end GlobalTheory.SeeSaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawKernelLiftCombinationOfDefiniteClassDataStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawKernelLiftCombination_of_definiteClassData : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → KerX t := by
  first | exact @GlobalTheory.SeeSaw.kerX_of_clsPinD | exact GlobalTheory.SeeSaw.kerX_of_clsPinD | (intros; apply GlobalTheory.SeeSaw.kerX_of_clsPinD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTupleKernelBackOfClassKernelData
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactEntriesLeOne
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.KJInf
variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem continuous_lin_mvZ {T : Type} [TopologicalSpace T] (g : T → ι → Matrix (Fin a) (Fin a) ℂ)
    (hg : Continuous g) (h : ι → Matrix (Fin b) (Fin b) ℂ) (P : FP ι a b) :
    ∀ Λ : FP ι a b →ₗ[ℂ] ℂ, Continuous fun x => Λ (mvZ (g x) h P) := by
  induction P using MvPolynomial.induction_on with
  | C c => intro Λ; simp only [mvZ, aeval_C, algebraMap_eq]; exact continuous_const
  | add p q hp hq => intro Λ; simp only [map_add (f := _)]; exact (hp Λ).add (hq Λ)
  | mul_X p v hp =>
    intro Λ
    have key : ∀ x, Λ (mvZ (g x) h (p * X v)) = ∑ i, ∑ j, (h v.1 i v.2.1 * g x v.1 v.2.2 j) *
        (Λ ∘ₗ LinearMap.mulRight ℂ (X (v.1, i, j))) (mvZ (g x) h p) := by
      intro x
      rw [map_mul]
      conv_lhs => rw [show mvZ (g x) h (X v) = ∑ i, ∑ j, C (h v.1 i v.2.1 * g x v.1 v.2.2 j) * X (v.1, i, j) by simp [mvZ, aeval_X]]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.mul_sum, map_sum, LinearMap.comp_apply, LinearMap.mulRight_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [C_mul', mul_smul_comm, map_smul, smul_eq_mul]
    simp_rw [key]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    refine Continuous.mul (continuous_const.mul ?_) (hp _)
    exact ((continuous_apply j).comp ((continuous_apply v.2.2).comp ((continuous_apply v.1).comp hg)))

theorem continuous_evalAt_mul (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    Continuous fun u : ι → Matrix (Fin a) (Fin a) ℂ => evalAt (fun τ => u τ * y τ) F := by
  unfold evalAt
  refine (MvPolynomial.continuous_eval F).comp (continuous_pi fun x => ?_)
  exact (((continuous_apply x.1).matrix_mul continuous_const).matrix_elem x.2.1 x.2.2)

theorem isCompact_entries_le_one :
    IsCompact {u : ι → Matrix (Fin a) (Fin a) ℂ | ∀ τ i j, ‖u τ i j‖ ≤ 1} := by
  have : {u : ι → Matrix (Fin a) (Fin a) ℂ | ∀ τ i j, ‖u τ i j‖ ≤ 1} =
      Set.univ.pi fun _ : ι => (Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : Fin a => Metric.closedBall (0:ℂ) 1 : Set (Matrix (Fin a) (Fin a) ℂ)) := by
    ext u
    constructor
    · intro hu τ _ i _ j _
      have := hu τ i j
      show dist (u τ i j) 0 ≤ 1
      simpa using this
    · intro hu τ i j
      have : dist (u τ i j) 0 ≤ 1 := hu τ trivial i trivial j trivial
      simpa using this
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _

theorem subY_eq_sum_averages : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a ≤ b) (lam : ι → DomWeight a) (n : ι → ℕ) (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] (r : K → ι → Matrix (Fin a) (Fin a) ℂ), OntoUni r → ∀ y' : ι → Matrix (Fin b) (Fin b) ℂ, ∃ (m : ℕ) (y : Fin m → ι → Matrix (Fin a) (Fin a) ℂ) (P : Fin m → FP ι a b), (∀ j, IsInv (y j)) ∧ ∀ F ∈ Vn lam n, ∀ Λ : FP ι a b →ₗ[ℂ] ℂ, ∑ j, ∫ k, Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) * evalAt (fun τ => r k τ * y j τ) F ∂ν = Λ (subY hab y' F) := by
  intro ι _ a b hab lam n K _ _ _ _ _ ν _ r hr y'
  obtain ⟨m, y, P, hy, hT⟩ := GlobalTheory.T.exists_invertibleFamily_eval_span ι a lam n (FP ι a b) (subY hab y').toLinearMap
  refine ⟨m, y, P, hy, ?_⟩
  intro F hF Λ
  obtain ⟨h1, -, -, h4, h5, h6, -, -⟩ := GlobalTheory.T.fockSubstitution_identities ι a b hab
  have vn := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable ι a lam n).2
  have hstar : ∀ k τ, star (r k τ) * r k τ = 1 := fun k τ => (Matrix.mem_unitaryGroup_iff').1 (hr.uni k τ)
  have hstar' : ∀ k τ, r k τ * star (r k τ) = 1 := fun k τ => (Matrix.mem_unitaryGroup_iff).1 (hr.uni k τ)
  have hinv : ∀ k τ, (r k τ)⁻¹ = star (r k τ) := fun k τ => Matrix.inv_eq_left_inv (hstar k τ)
  have hpt : ∀ k, ∑ j, Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) * evalAt (fun τ => r k τ * y j τ) F
      = Λ (subY hab y' F) := by
    intro k
    have hG : subY hab y' (lft (r k) F) = ∑ j, evalAt (y j) (lft (r k) F) • P j := hT _ (vn (r k) F hF)
    have e1 : mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (subY hab y' (lft (r k) F)) = subY hab y' F := by
      rw [h1, h4]
      have ha : (fun τ => r k τ * (r k τ)⁻¹) = fun _ => (1 : Matrix (Fin a) (Fin a) ℂ) := by
        funext τ; rw [hinv, hstar']
      have hb : (fun τ => (1 : Matrix (Fin b) (Fin b) ℂ) * y' τ) = y' := by funext τ; simp
      rw [ha, hb, h5]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e1, hG, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smul, smul_eq_mul, h6, mul_comm]
  have hst : Continuous fun u : ι → Matrix (Fin a) (Fin a) ℂ => fun τ => star (u τ) := continuous_pi fun τ => (continuous_apply τ).star
  have hcont : ∀ j, Continuous fun u : ι → Matrix (Fin a) (Fin a) ℂ =>
      Λ (mvZ (fun τ => star (u τ)) (fun _ => 1) (P j)) * evalAt (fun τ => u τ * y j τ) F := fun j => by
    have e1 := continuous_lin_mvZ (fun u : ι → Matrix (Fin a) (Fin a) ℂ => fun τ => star (u τ)) hst (fun _ => (1 : Matrix (Fin b) (Fin b) ℂ)) (P j) Λ
    exact e1.mul (continuous_evalAt_mul (y j) F)
  have hint : ∀ j ∈ Finset.univ, Integrable (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) *
      evalAt (fun τ => r k τ * y j τ) F) ν := by
    intro j _
    have hfun : (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) * evalAt (fun τ => r k τ * y j τ) F)
        = (fun u : ι → Matrix (Fin a) (Fin a) ℂ =>
          Λ (mvZ (fun τ => star (u τ)) (fun _ => 1) (P j)) * evalAt (fun τ => u τ * y j τ) F) ∘ r := by
      funext k; simp only [Function.comp_apply, hinv]
    rw [hfun]
    obtain ⟨C, hC⟩ := (isCompact_entries_le_one (ι := ι) (a := a)).exists_bound_of_continuousOn (hcont j).continuousOn
    refine Integrable.of_bound ((hcont j).comp hr.cont).aestronglyMeasurable C (Filter.Eventually.of_forall fun k => ?_)
    exact hC _ fun τ i i' => entry_norm_bound_of_unitary (hr.uni k τ) i i'
  rw [← integral_finsetSum _ hint]
  simp_rw [hpt]
  simp

end GlobalTheory.KJInf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTupleKernelBackOfClassKernelData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem castP_surjective {D : D7} {p q a b : ℕ} (hp : p = a) (hq : q = b) (Q : FP D.what₂.Tau a b) :
    ∃ P : PolF D q p, castP hp hq P = Q := by
  subst hp; subst hq
  refine ⟨Q, ?_⟩
  show MvPolynomial.rename _ Q = Q
  have : (fun v : D.what₂.Tau × Fin q × Fin p => (v.1, Fin.cast rfl v.2.1, Fin.cast rfl v.2.2)) = id := by
    funext v; simp
  rw [this, MvPolynomial.rename_id_apply]

theorem kBack_of_classData : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsK ρ t), c.Is → t.Is → ρ.Is → A.Is →
    (∀ j, j < D.R.m → t.cK j ≠ 0) → t.KBack := by
  intro D c t ρ A hc ht hρ hA hK j hj
  refine ⟨hK j hj, fun w => ?_⟩
  have hj1 : j + 1 ≤ D.R.m := hj
  have hab : ρ.N j ≤ ρ.N (j + 1) := (hρ.rk j hj).2
  obtain ⟨hB, ν, hν, -, hL⟩ := GlobalTheory.T.thetaLifts_all_charts_eq_classSum D c ρ hc hρ j hj1 hab
  haveI := hB
  haveI := hν
  set z : D.what₂.Tau → Matrix (Fin (ρ.N (j + 1))) (Fin (ρ.N (j + 1))) ℂ :=
    fun τ => (ρ.sc j τ)⁻¹ • (ρ.fr (j + 1) w).1 τ with hz
  obtain ⟨m, ys, Ps, hinv, havg⟩ := GlobalTheory.KJInf.subY_eq_sum_averages D.what₂.Tau (ρ.N j) (ρ.N (j + 1)) hab (ρ.lam j)
    (ρ.n j) (GinfC (c.X j)) ν (fun k => ρ.r j (Nat.le_of_succ_le hj1) k.1) (hρ.uni j _) z
  set s0 : ℂ := (∏ τ, ((ρ.fr (j + 1) w).1 τ).det ^ ρ.sD j τ)⁻¹ with hs0
  let y : Fin m → c.Fr j := fun i => (ρ.fr j).symm ⟨ys i, hinv i⟩
  have hy : ∀ i, (ρ.fr j (y i)).1 = ys i := fun i => congrArg Subtype.val ((ρ.fr j).apply_symm_apply ⟨ys i, hinv i⟩)
  have hP : ∀ i, ∃ P : PolF D (c.X (j + 1)).rank (c.X j).rank,
      castP (ρ.hN j (Nat.le_of_succ_le hj1)) (ρ.hN (j + 1) hj1) P = (s0 * ∏ τ, (ys i τ).det ^ ρ.sS j τ) • Ps i :=
    fun i => castP_surjective _ _ _
  choose P hP using hP
  refine ⟨m, y, P, fun ψ hψ γ => ?_⟩
  have hsc : ∀ (i : Fin 1) τ, (ρ.fr (j + 1) ((fun _ => w) i)).1 τ = ρ.sc j τ • (fun _ => z) i τ := by
    intro i τ
    simp only [hz]
    rw [smul_smul, mul_inv_cancel₀ (hρ.sc j τ), one_smul]
  have hav : ∀ F ∈ Vn (ρ.lam j) (ρ.n j), ∀ Λ : FP D.what₂.Tau (ρ.N j) (ρ.N (j + 1)) →ₗ[ℂ] ℂ,
      ∑ i, (∏ τ, ((ρ.fr j (y i)).1 τ).det ^ (-ρ.sS j τ)) *
        ∫ k, Λ (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj1) k.1 τ)⁻¹) (fun _ => 1)
          (castP (ρ.hN j (Nat.le_of_succ_le hj1)) (ρ.hN (j + 1) hj1) (P i))) *
          evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj1) k.1 τ * (ρ.fr j (y i)).1 τ) F ∂ν =
      ∑ i : Fin 1, (fun _ => s0) i * Λ (subY hab ((fun _ => z) i) F) := by
    intro F hF Λ
    clear hL
    have h0 := havg F hF Λ
    rw [Fin.sum_univ_one, ← h0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (∏ τ, (ys i τ).det ^ (-ρ.sS j τ)) * ∏ τ, (ys i τ).det ^ ρ.sS j τ = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun τ _ => ?_
      rw [_root_.zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hinv i τ).ne_zero)]
    beta_reduce
    simp only [hy, hP, map_smul, smul_eq_mul, mul_assoc, integral_const_mul]
    linear_combination (s0 * ∫ k, Λ (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj1) k.1 τ)⁻¹) (fun _ => 1) (Ps i)) *
          evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj1) k.1 τ * ys i τ) F ∂ν) * e
  have hmain := hL m y P 1 (fun _ => z) (fun _ => w) (fun _ => s0) hsc hav t A ht hA ψ hψ γ
  have hs1 : s0 * ∏ τ, ((ρ.fr (j + 1) w).1 τ).det ^ ρ.sD j τ = 1 := by
    rw [hs0]
    refine inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ ((ρ.fr (j + 1) w).2 τ).ne_zero)
  rw [hmain, Fin.sum_univ_one]
  simp only [hs1, one_smul]

end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTupleKernelBackOfClassKernelDataStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawTuple_kernelBack_of_classKernelData : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsK ρ t), c.Is → t.Is → ρ.Is → A.Is → (∀ j, j < D.R.m → t.cK j ≠ 0) → t.KBack := by
  first | exact @GlobalTheory.SeeSaw.kBack_of_classData | exact GlobalTheory.SeeSaw.kBack_of_classData | (intros; apply GlobalTheory.SeeSaw.kBack_of_classData <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryUnnSubgroupEqTopOfLeviUnipotentWeyl
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryUnnSubgroupEqTopOfLeviUnipotentWeyl
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Gen
open GlobalTheory.StdUnn.Model
variable {D : D7} {n : ℕ}

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem exists_blockMatrixTwoByTwoFin_eq {R : Type} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : ∃ a b c d, M = blk4 a b c d := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  rw [blk4, Matrix.fromBlocks_toBlocks]
  ext i j
  simp

theorem rel {g : G D n} {a b c d : Mx D n n} (hg : mat g = blk4 a b c d) :
    -(adj c * a) + adj a * c = 0 ∧ -(adj c * b) + adj a * d = 1 ∧ -(adj d * b) + adj b * d = 0 := by
  have h : adj (mat g) * JR (AF D.host.F) (Jst D n) * mat g = JR (AF D.host.F) (Jst D n) := g.2
  rw [JR_Jst, hg] at h
  simp only [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, mul_zero, mul_one, add_zero, zero_add, mul_neg, neg_mul] at h
  exact ⟨(blockMatrixTwoByTwoFin_injective h).1, (blockMatrixTwoByTwoFin_injective h).2.1, (blockMatrixTwoByTwoFin_injective h).2.2.2⟩

variable {S : Subgroup (G D n)}
  (hm : ∀ (g : G D n) (a : GL (Fin n) (AE D)), mat g = blk4 a.1 0 0 (adj (a⁻¹).1) → g ∈ S)
  (hn : ∀ (g : G D n) (b : Mx D n n), mat g = blk4 1 b 0 1 → g ∈ S)
  (hw : ∀ g : G D n, mat g = blk4 0 1 (-1) 0 → g ∈ S)

include hm hn in
theorem mem_of_upper {g : G D n} {a b d : Mx D n n} (hg : mat g = blk4 a b 0 d) (ha : IsUnit a) : g ∈ S := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨m, hmm⟩ := exists_levi (D := D) (n := n) u⁻¹
  have h1 : (adj u.1 : Mx D n n) * d = 1 := by simpa using (rel hg).2.1
  rw [← S.mul_mem_cancel_left (hm m _ hmm)]
  refine hn _ ((u⁻¹).1 * b) ?_
  rw [mat_mul, hmm, hg, submatrix_fromBlocks_mul]
  simp only [inv_inv, Units.inv_mul, mul_zero, zero_mul, add_zero, zero_add, h1]

include hm hn hw in
theorem mem_of_lower {g : G D n} {a c d : Mx D n n} (hg : mat g = blk4 a 0 c d) (hd : IsUnit d) : g ∈ S := by
  obtain ⟨w, hww⟩ := exists_weyl (D := D) (n := n)
  rw [← S.mul_mem_cancel_left (hw w hww), ← S.mul_mem_cancel_right (hw w hww)]
  refine mem_of_upper hm hn (a := -d) (b := c) (d := -a) ?_ hd.neg
  rw [mat_mul, mat_mul, hww, hg, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp

include hm hn hw in
theorem mem_of_isUnit {g : G D n} {a b c d : Mx D n n} (hg : mat g = blk4 a b c d) (hd : IsUnit d) : g ∈ S := by
  obtain ⟨u, rfl⟩ := hd
  have adj_mul_local {l m n : ℕ} (x : Mx D l m) (y : Mx D m n) :
      adj (x * y) = adj y * adj x := by
    unfold adj
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have h1 : (adj u.1 : Mx D n n) * b = adj b * u.1 := neg_add_eq_zero.1 (rel hg).2.2
  have h2 : (adj (u⁻¹).1 : Mx D n n) * adj u.1 = 1 := by rw [← adj_mul_local, Units.mul_inv, adj_one]
  have h3 : (adj (-(b * (u⁻¹).1)) : Mx D n n) = -(b * (u⁻¹).1) := by
    rw [adj_neg, adj_mul_local]
    congr 1
    calc (adj (u⁻¹).1 : Mx D n n) * adj b = adj (u⁻¹).1 * (adj b * u.1) * (u⁻¹).1 := by
          rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
      _ = b * (u⁻¹).1 := by rw [← h1, ← mul_assoc, h2, one_mul]
  obtain ⟨x, hx⟩ := (exists_unip _).2 h3
  rw [← S.mul_mem_cancel_left (hn x _ hx)]
  refine mem_of_lower hm hn hw (a := a + -(b * (u⁻¹).1) * c) (c := c) (d := u.1) ?_ u.isUnit
  rw [mat_mul, hx, hg, submatrix_fromBlocks_mul]
  simp only [one_mul, zero_mul, zero_add, neg_mul, mul_assoc, Units.inv_mul, mul_one, add_neg_cancel]

end GlobalTheory.StdUnn.Gen

namespace GlobalTheory.StdUnn

theorem eq_top_of_levi_unip_weyl : ∀ (D : D7) (n : ℕ) (S : Subgroup (GlobalTheory.StdUnn.G D n)), (∀ (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D)), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 a.1 0 0 (GlobalTheory.MixModel.adj (a⁻¹).1) → g ∈ S) → (∀ (g : GlobalTheory.StdUnn.G D n) (b : Mx D n n), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 1 b 0 1 → g ∈ S) → (∀ g : GlobalTheory.StdUnn.G D n, GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 → g ∈ S) → S = ⊤ := by
  intro D n S hm hn hw
  rw [eq_top_iff]
  intro g _
  obtain ⟨a, b, c, d, hg⟩ := Gen.exists_blockMatrixTwoByTwoFin_eq (mat g)
  obtain ⟨p', p, q', q, hi⟩ := Gen.exists_blockMatrixTwoByTwoFin_eq (mat g⁻¹)
  have h1 : mat g * mat g⁻¹ = 1 := by rw [← Gen.mat_mul, mul_inv_cancel]; rfl
  rw [hg, hi, Model.submatrix_fromBlocks_mul, ← Model.block_matrix_one] at h1
  obtain ⟨x, hx, hu⟩ := GlobalTheory.HermTransversal.exists_herm_isUnit D n c d p q (Model.blockMatrixTwoByTwoFin_injective h1).2.2.2
  obtain ⟨y, hy⟩ := (Model.exists_unip x).2 hx
  rw [← S.mul_mem_cancel_right (hn y _ hy)]
  refine Gen.mem_of_isUnit hm hn hw (a := a) (b := a * x + b) (c := c) (d := c * x + d) ?_ hu
  rw [Gen.mat_mul, hg, hy, Model.submatrix_fromBlocks_mul]
  simp only [mul_one, mul_zero, add_zero]

end GlobalTheory.StdUnn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryUnnSubgroupEqTopOfLeviUnipotentWeylStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryUnn_subgroup_eq_top_of_leviUnipotentWeyl : ∀ (D : D7) (n : ℕ) (S : Subgroup (GlobalTheory.StdUnn.G D n)), (∀ (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D)), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 a.1 0 0 (GlobalTheory.MixModel.adj (a⁻¹).1) → g ∈ S) → (∀ (g : GlobalTheory.StdUnn.G D n) (b : Mx D n n), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 1 b 0 1 → g ∈ S) → (∀ g : GlobalTheory.StdUnn.G D n, GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 → g ∈ S) → S = ⊤ := by
  first | exact @GlobalTheory.StdUnn.eq_top_of_levi_unip_weyl | exact GlobalTheory.StdUnn.eq_top_of_levi_unip_weyl | (intros; apply GlobalTheory.StdUnn.eq_top_of_levi_unip_weyl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixAndKillThetaOffSupportMove
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixAndKillThetaOffSupportMove
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfSep

theorem map_infPart_eq_zero {D : D7} {S T : HSp D} {b : AE D} (hb : infPart D b = 0) {y : WO S T}
    (hy : IsHalf b y) : y.map (infPart D) = 0 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  rw [← hy i j, map_mul, hb, zero_mul]

theorem sep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ f₀ Φ f : WO S T → ℂ, IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Φ f → ∀ g : GA D S, (∀ x, Φ x ≠ 0 → Φ (actO S T g 1 x) = 0) → ∃ (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), (∀ i, (y i).map (infPart D) = 0 ∧ (actO S T g⁻¹ 1 (-(y i))).map (infPart D) = 0) ∧ ∑ i, a i • heisO ψ S T (y i) f = f ∧ ∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) f = 0 := by
  classical
  intro D ψ S T hψ ΛS ΛT hS hT Z e he f₀ Φ f hΦ hth g hsupp
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  have hfT : f = Tm Φ := hall Tm hTm
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hinfc : infPart D (cA D e) = 0 := ho.conj.infPart_eq
  obtain ⟨k, hk, hinv, hsup⟩ := hΦ.2
  obtain ⟨M, hM, hMact⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).2 g 1
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  set N : ℕ := M * k with hN
  have hNpos : 0 < N := Nat.mul_pos hM hk
  let Ψ : WO S T → ℂ := fun u => if ∃ t, Φ t ≠ 0 ∧ N • t = u then 1 else 0
  have hNt : ∀ t, Φ t ≠ 0 → N • t ∈ Λ := fun t ht => by
    rw [hN, mul_smul]; exact Λ.nsmul_mem (hsup t ht) M
  have hΨ : IsSBHalf e Λ Ψ := by
    refine ⟨fun u hu => ?_, N * k, Nat.mul_pos hNpos hk, fun v hv hvh u => ?_, fun u hu => ?_⟩
    · have : ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        by_contra h; exact hu (if_neg h)
      obtain ⟨t, ht, rfl⟩ := this
      exact GlobalTheory.ThetaOrth.isHalf_nsmul (hΦ.1 t ht) N
    · have key : (∃ t, Φ t ≠ 0 ∧ N • t = u + (N * k) • v) ↔ ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        constructor
        · rintro ⟨t, ht, h⟩
          refine ⟨t + k • (-v), by rwa [hinv (-v) (Λ.neg_mem hv) (GlobalTheory.ThetaOrth.isHalf_neg hvh) t], ?_⟩
          exact GlobalTheory.ThetaOrth.nsmul_add_neg N k t u v h
        · rintro ⟨t, ht, rfl⟩
          refine ⟨t + k • v, by rwa [hinv v hv hvh t], ?_⟩
          exact GlobalTheory.ThetaOrth.nsmul_add_mul N k t v
      show (if _ then _ else _) = (if _ then _ else _)
      simp only [key]
    · have : ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        by_contra h; exact hu (if_neg h)
      obtain ⟨t, ht, rfl⟩ := this
      exact Λ.nsmul_mem (hNt t ht) _
  have hspan := (GlobalTheory.PlaceTensor.halfWaves_span D ψ S T ΛS ΛT hψ hS hT e ho.idem he.2 ho.infPart_eq).2 Ψ hΨ
  obtain ⟨q, hq, hqΨ⟩ := GlobalTheory.ThetaOrth.exists_char_of_wave N hspan
  have hq1 : ∀ t, Φ t ≠ 0 → q t = 1 := fun t ht => by
    rw [← hqΨ t (hΦ.1 t ht) (hNt t ht)]
    exact if_pos ⟨t, ht, rfl⟩
  have hq0 : ∀ t, Φ t ≠ 0 → q (actO S T g 1 t) = 0 := fun t ht => by
    have h1 : N • actO S T g 1 t ∈ Λ := by
      have := hMact (k • t) (hsup t ht)
      have e : actO S T g 1 (k • t) = k • actO S T g 1 t := map_nsmul (GlobalTheory.LatLevel.actHom S T g 1) k t
      rwa [e, ← mul_smul] at this
    rw [← hqΨ _ (GlobalTheory.SplitHecke.isHalf_actO _ _ (hΦ.1 t ht)) h1]
    refine if_neg ?_
    rintro ⟨t', ht', h⟩
    have : t' = actO S T g 1 t := GlobalTheory.ThetaOrth.nsmul_inj hNpos h
    exact ht' (this ▸ hsupp t ht)

  obtain ⟨n, a, yy, hqs⟩ := (Submodule.mem_span_set' (R := ℂ)).1 hq
  choose y hy hyq using fun i => (yy i).2
  have hqt : ∀ t, q t = ∑ i, a i * ψ (symplO S T t (y i)) := fun t => by
    rw [← hqs, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, hyq i, smul_eq_mul]
  set w : Fin n → WO S T := fun i => actO S T g⁻¹ 1 (-(y i)) with hw
  have hwh : ∀ i, IsHalf (cA D e) (w i) := fun i =>
    GlobalTheory.SplitHecke.isHalf_actO _ _ (GlobalTheory.ThetaOrth.isHalf_neg (hy i))
  have hact : ∀ i, actO S T g 1 (w i) = -(y i) := fun i => by
    have := GlobalTheory.AdelicLatMove.actO_actO_inv S T g 1 (-(y i))
    rwa [inv_one] at this
  refine ⟨n, a, y, fun i => ⟨map_infPart_eq_zero hinfc (hy i), map_infPart_eq_zero hinfc (hwh i)⟩, ?_, ?_⟩
  · have e1 : (fun t => q t * Φ t) = Φ := by
      funext t
      by_cases h : Φ t = 0
      · rw [h, mul_zero]
      · rw [hq1 t h, one_mul]
    have e2 : (fun t => q t * Φ t) = ∑ i, a i • fun t => ψ (symplO S T t (y i)) * Φ t := by
      funext t
      rw [hqt, Finset.sum_mul, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
    have e3 := congrArg Tm e2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum, ← hfT] at e3
    refine (Finset.sum_congr rfl fun i _ => ?_).trans e3.symm
    rw [map_smul, hTm.modul Φ hΦ (y i) (hy i), ← hfT]
  · have e1 : (fun t => conj (q (actO S T g 1 t)) * Φ t) = 0 := by
      funext t
      by_cases h : Φ t = 0
      · simp [h]
      · simp [hq0 t h]
    have e2 : (fun t => conj (q (actO S T g 1 t)) * Φ t) =
        ∑ i, conj (a i) • fun t => ψ (symplO S T t (w i)) * Φ t := by
      funext t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hqt, map_sum, Finset.sum_mul, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.ThetaOrth.conj_psi hψ,
        ← GlobalTheory.ThetaOrth.symplO_neg_right, ← hact i, GlobalTheory.SymplOInv.symplO_actO D S T g 1 t (w i), mul_assoc]
    have e3 := congrArg Tm e2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_zero, map_sum] at e3
    rw [e3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hfT, hTm.modul Φ hΦ (w i) (hwh i)]

end GlobalTheory.HalfSep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixAndKillThetaOffSupportMoveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_fix_and_kill_theta_off_support_move : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ f₀ Φ f : WO S T → ℂ, IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Φ f → ∀ g : GA D S, (∀ x, Φ x ≠ 0 → Φ (actO S T g 1 x) = 0) → ∃ (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), (∀ i, (y i).map (infPart D) = 0 ∧ (actO S T g⁻¹ 1 (-(y i))).map (infPart D) = 0) ∧ ∑ i, a i • heisO ψ S T (y i) f = f ∧ ∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) f = 0 := by
  first | exact @GlobalTheory.HalfSep.sep | exact GlobalTheory.HalfSep.sep | (intros; apply GlobalTheory.HalfSep.sep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinContinuationAndPoles
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open Filter Topology Set Metric GlobalTheory.Eis

namespace GlobalTheory.Eis

theorem zetaContinues_of_eisRegularAt {D : D7} {V : HSp D} {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ)
    {m : Measure (GA D V)} (hm : m.IsHaarMeasure) {Φ : ℂ → GA D (dblSp V) → ℂ} (hE : EisContinues V Φ)
    (ha : ∀ g, AnalyticOnNhd ℂ (eisSer V Φ g) (rightOf (V.rank / 2))) (hreg : ∀ s₀, ∃ k, EisRegularAt V Φ s₀ k)
    {f₁ f₂ : GA D V → ℂ} (h₁ : GlobalTheory.Grow.RapidDec V f₁) (h₂ : GlobalTheory.Grow.RapidDec V f₂)
    (hZ : IsZetaFamily V μ m Φ f₁ f₂) : ZetaContinues V μ m Φ f₁ f₂ := by
  obtain ⟨C', c, hio⟩ := GlobalTheory.T.exists_height_doublingEmbedding_le_pow_mul_heights D V
  have key : ∀ (H : ℂ → GA D (dblSp V) → ℂ) (z : ℂ) (r : ℝ), 0 < r →
      (∀ s ∈ ball z r, LeftInv (GQ (dblSp V)) (H s)) →
      (∀ g, DifferentiableOn ℂ (H · g) (ball z r)) →
      ContinuousOn (fun x : ℂ × GA D (dblSp V) => H x.1 x.2) (ball z r ×ˢ univ) →
      (∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball z r, ∀ g, ‖H s g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) →
      (∀ s ∈ ball z r, DblConv V μ m (H s) f₁ f₂) ∧
        DifferentiableOn ℂ (fun s => dblInt V μ m (H s) f₁ f₂) (ball z r) := by
    rintro H z r hr hinv hd hc ⟨C, N, hb⟩
    obtain ⟨bound, hbi, hbd⟩ := GlobalTheory.T.exists_integrable_bound_doubling_integrand_quotient D V μ m hm f₁ f₂ h₁ h₂ C' c hio C N
    have hcont : ∀ s ∈ ball z r, Continuous (H s) := fun s hs =>
      hc.comp_continuous (f := fun g => (s, g)) (by fun_prop) fun g => ⟨hs, trivial⟩
    have hli : ∀ s ∈ ball z r, LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ (H s) f₁ f₂) := fun s hs =>
      leftInv_dblIntegrand hμ (hinv s hs) h₁.1 h₂.1
    have hmeas : ∀ s ∈ ball z r, AEStronglyMeasurable (dblIntegrandQ V μ (H s) f₁ f₂)
        ((autMeasure V m).prod (autMeasure V m)) := by
      intro s hs
      have e' : dblIntegrandQ V μ (H s) f₁ f₂ =
          dblIntegrand V μ (H s) f₁ f₂ ∘ Prod.map (sec (GQ V)) (sec (GQ V)) :=
        funext fun q => (congrArg _ (Prod.ext (mk_sec q.1) (mk_sec q.2)).symm).trans (dblIntegrandQ_mk (hli s hs) _ _)
      rw [e']
      exact ((continuous_dblIntegrand hμ (hcont s hs) h₁.continuous h₂.continuous).measurable.comp
        (measurableEmbedding_sec.measurable.prodMap measurableEmbedding_sec.measurable)).aestronglyMeasurable
    refine ⟨fun s hs => ⟨hli s hs, hbi.mono' (hmeas s hs) (ae_of_all _ fun q => hbd (H s) (hinv s hs) (hb s hs) q)⟩, ?_⟩
    have := GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated
      (μ := (autMeasure V m).prod (autMeasure V m)) (F := fun q s => dblIntegrandQ V μ (H s) f₁ f₂ q)
      (isOpen_ball (x := z) (ε := r)) hmeas
      (ae_of_all _ fun q => by
        simp only [dblIntegrandQ, dblIntegrand]
        exact (((hd _).mul_const _).mul_const _).mul_const _)
      fun x hx => ⟨ball z r, isOpen_ball.mem_nhds hx, bound, hbi,
        ae_of_all _ fun q y hy => hbd (H y) (hinv y hy) (hb y hy) q⟩
    exact this.1
  have hinvE : ∀ s, LeftInv (GQ (dblSp V)) (eisCont V Φ s) := fun s => hE.1.leftInv_eisLaurent s 0
  set Z : ℂ → ℂ := fun s => dblInt V μ m (eisCont V Φ s) f₁ f₂ with hZdef
  have hmer : ∀ s₁, MeromorphicAt Z s₁ := by
    intro s₁
    obtain ⟨k, r, H, hr, e, hd, hc, C, N, hb⟩ := hreg s₁
    have hinvH : ∀ s ∈ ball s₁ r, LeftInv (GQ (dblSp V)) (H s) := by
      intro s hs γ hγ g
      rcases eq_or_ne s s₁ with rfl | h0
      · have t1 := ((hd (γ * g)).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := {s}ᶜ))
        have t2 := ((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := {s}ᶜ))
        refine tendsto_nhds_unique t1 (t2.congr' ?_)
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s hr)] with w h1 h2
        rw [e w h2 h1, e w h2 h1, hinvE w γ hγ g]
      · rw [e s hs h0, e s hs h0, hinvE s γ hγ g]
    have han : AnalyticAt ℂ (fun s => dblInt V μ m (H s) f₁ f₂) s₁ :=
      (key H s₁ r hr hinvH hd hc ⟨C, N, hb⟩).2.analyticAt (ball_mem_nhds _ hr)
    have hm1 : MeromorphicAt (fun s => ((s - s₁) ^ k)⁻¹ * dblInt V μ m (H s) f₁ f₂) s₁ := by
      have : MeromorphicAt (fun s : ℂ => s - s₁) s₁ := (MeromorphicAt.id s₁).sub (MeromorphicAt.const _ _)
      exact (this.pow k).inv.mul han.meromorphicAt
    refine hm1.congr ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₁ hr)] with w h1 h2
    have e1 : eisCont V Φ w = ((w - s₁) ^ k)⁻¹ • H w := by
      funext g
      rw [Pi.smul_apply, e w h2 h1 g, smul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ (sub_ne_zero.2 h1)), one_mul]
    have e2 := dblInt_smul (V := V) (μ := μ) (m := m) (E := H w) (f₁ := f₁) (f₂ := f₂) ((w - s₁) ^ k)⁻¹ 1 1
    simp only [one_smul, map_one, mul_one] at e2
    simp only [Z, e1, e2]
  have hext : IsMerExt (zeta V μ m Φ f₁ f₂) univ Z := by
    refine ⟨isRightDomain_univ, fun s _ => hmer s, (V.rank : ℝ) / 2, fun s hs => ?_⟩
    have : eisCont V Φ s = eis V (Φ s) := funext fun g => eqOn_cont (ha g) hs
    simp only [Z, zeta, this]
  exact ⟨hZ, Z, hext⟩

end GlobalTheory.Eis
end
