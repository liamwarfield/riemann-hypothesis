module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightSelfDualLatticesEqConj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstantTermLiftIsotropicSubspace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DictionaryColumnScalarFormEqTraceColumnForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateRowPairingPoincareSeriesBesselPeriods
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroTargetTensorRowProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsItWOfGlobIt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFockIntertwinerAdjointExchangedPair
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonCoefficientBoundedSphericalUnramified

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBExtFunEqHalfInd
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.HalfInd

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def wr (α : Frame p S n') (β : Frame p T n) : Matrix n n' k →+ WO S T where
  toFun x := (β.b * x * α.b').map p.sec
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul, Matrix.map_zero _ (map_zero _)]
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul, Matrix.map_add _ (map_add _)]

theorem wr_apply (α : Frame p S n') (β : Frame p T n) (x : Matrix n n' k) (i : Fin T.rank) (j : Fin S.rank) :
    wr α β x i j = p.sec ((β.b * x * α.b') i j) := rfl

theorem rd_eq (α : Frame p S n') (β : Frame p T n) (t : WO S T) :
    rd α β t = β.b' * (Matrix.map t p.pr : Matrix (Fin T.rank) (Fin S.rank) k) * α.b := rfl

theorem isHalf_wr (α : Frame p S n') (β : Frame p T n) (x : Matrix n n' k) : IsHalf p.e (wr α β x) := fun i j => by
  rw [wr_apply, ← p.sec_pr, p.pr_sec]

theorem wr_rd (α : Frame p S n') (β : Frame p T n) {t : WO S T} (ht : IsHalf p.e t) : wr α β (rd α β t) = t := by
  ext i j
  rw [wr_apply, rd_eq, Matrix.mul_assoc β.b', ← Matrix.mul_assoc β.b, β.bb', Matrix.one_mul, Matrix.mul_assoc, α.bb',
    Matrix.mul_one, Matrix.map_apply, p.sec_pr, ht i j]


set_option maxHeartbeats 800000 in
theorem open_compact_sec (p : SplitPt D k) {LS : Lat S} {LT : Lat T} (hS : Submodule.IsFullLattice D.host.E LS)
    (hT : Submodule.IsFullLattice D.host.E LT) :
    IsOpen {y : Matrix (Fin T.rank) (Fin S.rank) k | y.map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True} ∧
    IsCompact {y : Matrix (Fin T.rank) (Fin S.rank) k |
      y.map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True} := by
  have : CharZero k := charZero_of_injective_ringHom (f := p.pr.comp (incA D)) (RingHom.injective _)
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.toIsLattice.fg hT.toIsLattice.fg
  obtain ⟨N, hN, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS hT
  let A : AddSubgroup (Matrix (Fin T.rank) (Fin S.rank) k) :=
    (latO S T (LS : Set _) (LT : Set _) fun _ => True).comap p.sec.mapMatrix
  have hA : ∀ y, y ∈ A ↔ y.map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True := fun _ => Iff.rfl
  have hO : ∀ a : k, a ∈ (𝒪[k]).toAddSubgroup ↔ finPart D (p.sec a) ∈ intAE D := p.int_iff
  have key := GlobalTheory.PlaceCoord.isOpen_isCompact_of_comm (𝒪[k]).toAddSubgroup
    (Valuation.isOpen_integer (v := valuation k)) (IsNonarchimedeanLocalField.isCompact_closedBall k 1) A hN hM
    (fun y hy => by
      have ht : IsHalf p.e (y.map p.sec : WO S T) := fun i j => by
        rw [Matrix.map_apply, ← p.sec_pr, p.pr_sec]
      have h1 : (N • y).map p.sec = N • y.map p.sec := Matrix.ext fun i j => map_nsmul p.sec N (y i j)
      rw [hA, h1]
      exact hmul _ (GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceCoord.infPart_split p.split) ht) fun i j =>
        GlobalTheory.PlaceCoord.toEAf_mem ((hO _).1 (hy i j)))
    (fun y hy i j => by
      have h1 : p.sec ((M : k) * y i j) = (M : AE D) * p.sec (y i j) := by
        rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
      rw [hO, h1]
      refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
      rw [RingHom.map_mul, map_natCast]
      exact hden _ ((hA y).1 hy) i j)
  exact key

theorem exists_idem (p : SplitPt D k) : ∃ ε, IsPlaceIdem D p.v ε ∧ algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
  obtain ⟨ε, hε, h⟩ := p.above
  exact ⟨ε, hε, by rw [← h, add_mul, p.split.1, mul_comm, p.split.2.1, add_zero]⟩

theorem compact_open (α : Frame p S n') (β : Frame p T n) {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) :
    IsCompact {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧ IsHalf p.e (wr α β x)} ∧
      IsOpen {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧ IsHalf p.e (wr α β x)} := by
  obtain ⟨ε, hε, heε⟩ := exists_idem p
  have hh : ∀ x, wr α β x ∈ GlobalTheory.PlaceModel.half S T p.e := fun x => (GlobalTheory.PlaceModel.isHalf_iff S T).1 (isHalf_wr α β x)
  obtain ⟨ho, hc⟩ := open_compact_sec p (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S LS hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T LT hT)
  have h1 : {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧ IsHalf p.e (wr α β x)} =
      {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True} := by
    ext x
    refine ⟨fun h => GlobalTheory.PlaceModel.latO_le_top _ h.1, fun h => ⟨?_, isHalf_wr α β x⟩⟩
    have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε p.split.1 heε h).1
    rwa [(GlobalTheory.PlaceModel.mem_half S T).1 (hh x)] at h2
  rw [h1]
  refine ⟨?_, ho.preimage (f := fun x : Matrix n n' k => β.b * x * α.b')
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)⟩
  convert hc.image (f := fun y => β.b' * y * α.b)
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const) using 1
  ext x
  refine ⟨fun h => ⟨β.b * x * α.b', h, ?_⟩, ?_⟩
  · beta_reduce
    rw [Matrix.mul_assoc β.b, ← Matrix.mul_assoc β.b', β.b'b, Matrix.one_mul, Matrix.mul_assoc, α.b'b, Matrix.mul_one]
  · rintro ⟨y, hy, rfl⟩
    change (β.b * (β.b' * y * α.b) * α.b').map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True
    rwa [Matrix.mul_assoc β.b', ← Matrix.mul_assoc β.b, β.bb', Matrix.one_mul, Matrix.mul_assoc, α.bb', Matrix.mul_one]

theorem exists_SB_extFun_eq_halfInd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ Ψ : Matrix n n' k → ℂ, Ψ ∈ GlobalTheory.SplitWeil.SB (Matrix n n' k) ∧ extFun α β Ψ = halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) := by
  intro D k _ _ _ _ p S T n n' _ _ _ _ α β LS LT hS hT
  have := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  obtain ⟨hc, ho⟩ := compact_open α β hS hT
  refine ⟨fun x => halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) (wr α β x), ?_, ?_⟩
  · unfold halfInd
    convert GlobalTheory.FinPl.Comm.ite_mem_SB hc ho
  · funext t
    unfold extFun
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht]
      beta_reduce
      rw [wr_rd α β ht]
    · rw [if_neg ht, halfInd, if_neg fun h => ht h.2]

end GlobalTheory.FinPl.HalfInd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalDoublingZetaFormSelfDualLatticeTransfer
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalDoublingZetaFormSelfDualLatticeTransfer
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.GlobMove

variable {D : D7}

theorem rmul_one' {V : HSp D} (q : AutomorphicL2Unitary.Quot (GQ V)) : AutomorphicL2Unitary.rmul (GQ V) 1 q = q := by
  induction q using Quotient.inductionOn' with
  | h x => exact congrArg _ (mul_one x)

def rmulEquiv {V : HSp D} (y : GA D V) : AutomorphicL2Unitary.Quot (GQ V) ≃ᵐ AutomorphicL2Unitary.Quot (GQ V) where
  toFun := AutomorphicL2Unitary.rmul (GQ V) y
  invFun := AutomorphicL2Unitary.rmul (GQ V) y⁻¹
  left_inv q := by rw [← AutomorphicL2Unitary.rmul_mul, mul_inv_cancel, rmul_one']
  right_inv q := by rw [← AutomorphicL2Unitary.rmul_mul, inv_mul_cancel, rmul_one']
  measurable_toFun := AutomorphicL2Unitary.measurable_rmul y
  measurable_invFun := AutomorphicL2Unitary.measurable_rmul y⁻¹

theorem descend_mul_right {V : HSp D} {φ : GA D V → ℂ} (hφ : AutomorphicL2Unitary.LeftInv (GQ V) φ) (y : GA D V) :
    AutomorphicL2Unitary.descend (GQ V) (fun x => φ (x * y)) = AutomorphicL2Unitary.descend (GQ V) φ ∘ AutomorphicL2Unitary.rmul (GQ V) y := by
  funext q
  have e : AutomorphicL2Unitary.rmul (GQ V) y q = AutomorphicL2Unitary.mk (GQ V) (q.out * y) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  simp only [Function.comp, e, hφ.descend_mk]
  rfl

section Quot

variable {V : HSp D} (m : Measure (GA D V)) [m.IsHaarMeasure] [m.IsMulRightInvariant]

theorem integral_descend_mul_right {φ : GA D V → ℂ} (hφ : AutomorphicL2Unitary.LeftInv (GQ V) φ) (y : GA D V) :
    ∫ q, AutomorphicL2Unitary.descend (GQ V) (fun x => φ (x * y)) q ∂autMeasure V m =
      ∫ q, AutomorphicL2Unitary.descend (GQ V) φ q ∂autMeasure V m := by
  rw [descend_mul_right hφ y]
  exact (AutomorphicL2Unitary.measurePreserving_rmul (Γ := GQ V) (μ := m) y).integral_comp (rmulEquiv y).measurableEmbedding _

theorem integrable_descend_mul_right_iff {φ : GA D V → ℂ} (hφ : AutomorphicL2Unitary.LeftInv (GQ V) φ) (y : GA D V) :
    Integrable (AutomorphicL2Unitary.descend (GQ V) (fun x => φ (x * y))) (autMeasure V m) ↔
      Integrable (AutomorphicL2Unitary.descend (GQ V) φ) (autMeasure V m) := by
  rw [descend_mul_right hφ y]
  exact (AutomorphicL2Unitary.measurePreserving_rmul (Γ := GQ V) (μ := m) y).integrable_comp_emb (rmulEquiv y).measurableEmbedding

theorem petersson_rTr {φ ψ : GA D V → ℂ} (hφ : AutomorphicL2Unitary.LeftInv (GQ V) φ) (hψ : AutomorphicL2Unitary.LeftInv (GQ V) ψ) (y : GA D V) :
    petersson V m (rTr V y φ) (rTr V y ψ) = petersson V m φ ψ := by
  show ∫ q, AutomorphicL2Unitary.descend (GQ V) (fun x => φ (x * y)) q * conj (AutomorphicL2Unitary.descend (GQ V) (fun x => ψ (x * y)) q)
      ∂autMeasure V m = ∫ q, AutomorphicL2Unitary.descend (GQ V) φ q * conj (AutomorphicL2Unitary.descend (GQ V) ψ q) ∂autMeasure V m
  rw [descend_mul_right hφ y, descend_mul_right hψ y]
  exact (AutomorphicL2Unitary.measurePreserving_rmul (Γ := GQ V) (μ := m) y).integral_comp (rmulEquiv y).measurableEmbedding
    (fun q => AutomorphicL2Unitary.descend (GQ V) φ q * conj (AutomorphicL2Unitary.descend (GQ V) ψ q))

end Quot

section Conj

variable {V : HSp D} (m : Measure (GA D V)) [m.IsHaarMeasure] [m.IsMulRightInvariant]

theorem integral_conj (F : GA D V → ℂ) (k : GA D V) : ∫ y, F (k * y * k⁻¹) ∂m = ∫ y, F y ∂m := by
  rw [integral_mul_left_eq_self (fun z => F (z * k⁻¹)) k, integral_mul_right_eq_self F k⁻¹]

theorem integrable_of_conj {F : GA D V → ℂ} (k : GA D V) (h : Integrable (fun y => F (k * y * k⁻¹)) m) :
    Integrable F m := by
  have h2 := (h.comp_mul_left k⁻¹).comp_mul_right k
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

end Conj

end GlobalTheory.Core.Rk.GlobMove

namespace GlobalTheory.Core.Rk.GlobMove

variable {D : D7}

section Weil

variable {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χA χB : (AE D)ˣ →* Circle} {om : WRep A B}

theorem om_mul_one (g g' : GA D A) (f : WO A B → ℂ) : om (g, 1) (om (g', 1) f) = om (g * g', 1) f := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem thetaKO_om (g k : GA D A) (h : GA D B) (Φ : WO A B → ℂ) :
    thetaKO om g h (om (k, 1) Φ) = thetaKO om (g * k) h Φ := by
  unfold thetaKO
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem leftInv_thetaKO (hW : IsWeilDatumO ψ A B χA χB om) {Φ : WO A B → ℂ} (hΦ : IsThetaFunO ψ A B Φ) (h : GA D B) :
    AutomorphicL2Unitary.LeftInv (GQ A) fun g => thetaKO om g h Φ := by
  intro γ hγ g
  show om (γ * g, h) Φ 0 = om (g, h) Φ 0
  have e : ((γ * g, h) : GA D A × GA D B) = (γ, 1) * (g, h) := by rw [Prod.mk_mul_mk, one_mul]
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut γ hγ 1 (GQ B).one_mem _ (hW.om_pres _ _ hΦ)

theorem wcoef_om (hW : IsWeilDatumO ψ A B χA χB om) {ν : Measure (WO A B)} {𝓕 : Set (WO A B)}
    (hν : IsCovolOne (ratL B A) ν 𝓕) {Φ₁ Φ₂ : WO A B → ℂ} (h₁ : IsThetaFunO ψ A B Φ₁) (h₂ : IsThetaFunO ψ A B Φ₂)
    (k y : GA D A) :
    wcoef om ν 𝓕 (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) y = wcoef om ν 𝓕 Φ₁ Φ₂ (k * y * k⁻¹) := by
  have e : om (y, 1) (om (k⁻¹, 1) Φ₁) = om (k⁻¹, 1) (om (k * y * k⁻¹, 1) Φ₁) := by
    rw [om_mul_one, om_mul_one]; congr 2; group
  have key := GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hW.std A B ν 𝓕 hν.1 hν.2.1 (om (k⁻¹, 1))
    (fun f hf => hW.om_pres (k⁻¹, 1) f hf) (fun f hf => hW.om_unit ν 𝓕 hν.1 hν.2.1 (k⁻¹, 1) f hf)
    (om (k * y * k⁻¹, 1) Φ₁) Φ₂ (hW.om_pres _ _ h₁) h₂
  simp only [wcoef, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, e]
  exact key

end Weil

section Cusp

variable {V : HSp D} (m : Measure (GA D V)) [m.IsHaarMeasure] [m.IsMulRightInvariant]

theorem rcoef_rTr {u₁ u₂ : GA D V → ℂ} (h₁ : AutomorphicL2Unitary.LeftInv (GQ V) u₁) (h₂ : AutomorphicL2Unitary.LeftInv (GQ V) u₂) (k y : GA D V) :
    rcoef m (rTr V k⁻¹ u₁) (rTr V k⁻¹ u₂) y = rcoef m u₁ u₂ (k * y * k⁻¹) := by
  unfold rcoef
  have h₃ : AutomorphicL2Unitary.LeftInv (GQ V) (rTr V (k * y * k⁻¹) u₁) := h₁.mul_right _
  rw [← petersson_rTr m h₃ h₂ k⁻¹]
  congr 1
  funext x
  change u₁ ((x * y) * k⁻¹) = u₁ ((x * k⁻¹) * (k * y * k⁻¹))
  congr 1
  group

end Cusp

end GlobalTheory.Core.Rk.GlobMove

namespace GlobalTheory.Core.Rk.GlobMove

variable {D : D7}

theorem cuspFormsArchimedeanKFinite_left_invariant {θ : InfFam D} {A : HSp D} {cA : CptF A} {u : GA D A → ℂ} (hu : u ∈ A0 θ A cA) :
    AutomorphicL2Unitary.LeftInv (GQ A) u :=
  AutomorphicL2Unitary.leftInv_of_isAutFun (Submodule.mem_inf.1 hu).1.1.toIsAutFun

theorem globalFormAt_move : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' →
    GlobalFormAt A L → GlobalFormAt A L' := by
  intro D A L L' hL hL' hG
  obtain ⟨k, hk, hh⟩ := GlobalTheory.T.doubledLatticeHeight_selfDual_lattices_eq_conj D A L L' hL hL'
  intro ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hw m mH hm hmH Φ₁ Φ₂ hΦ₁ hΦ₂ u₁ hu₁ u₂ hu₂
  haveI := hm
  haveI := hmH
  haveI : m.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds A m hm
  have hW := hP.weil
  have hθ : IsInfFam θ := hP.setting.2.2.2.1
  have hki : k⁻¹ ∈ GfC A := inv_mem hk
  have fock : ∀ Φ, IsFockVec ψ θ A B sA sB Φ → IsFockVec ψ θ A B sA sB (om (k⁻¹, 1) Φ) := by
    rintro Φ ⟨hΦ, N, hN⟩
    refine ⟨hW.om_pres _ _ hΦ, N, fun l hl => ?_⟩
    refine GlobalTheory.T.weilRep_preserves_fockDegree_of_commute_cartan D ψ θ A B χA χB om sA sB hW hθ k⁻¹ (fun τ => ?_) N Φ hΦ hN l hl
    rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ A hki τ, Matrix.one_mul, Matrix.mul_one]
  have lu₁ := cuspFormsArchimedeanKFinite_left_invariant hu₁
  have lu₂ := cuspFormsArchimedeanKFinite_left_invariant hu₂

  have upEq : ∀ Φ, IsThetaFunO ψ A B Φ → ∀ u : GA D A → ℂ, AutomorphicL2Unitary.LeftInv (GQ A) u →
      (∀ h, AutomorphicL2Unitary.descend (GQ A) (fun g => thetaKO om g h (om (k⁻¹, 1) Φ) * rTr A k⁻¹ u g) =
        AutomorphicL2Unitary.descend (GQ A) (fun g => (fun x => thetaKO om x h Φ * u x) (g * k⁻¹))) ∧
      ∀ h, AutomorphicL2Unitary.LeftInv (GQ A) (fun x => thetaKO om x h Φ * u x) := by
    intro Φ hΦ u hu
    refine ⟨fun h => ?_, fun h γ hγ g => ?_⟩
    · congr 1
      funext g
      rw [thetaKO_om]
      rfl
    · simp only [leftInv_thetaKO hW hΦ h γ hγ g, hu γ hγ g]
  have upConvIff : ∀ Φ, IsThetaFunO ψ A B Φ → ∀ u : GA D A → ℂ, AutomorphicL2Unitary.LeftInv (GQ A) u →
      up om m (om (k⁻¹, 1) Φ) (rTr A k⁻¹ u) = up om m Φ u ∧
      (UpConv om m mH (om (k⁻¹, 1) Φ) (rTr A k⁻¹ u) → UpConv om m mH Φ u) := by
    intro Φ hΦ u hu
    obtain ⟨e1, e2⟩ := upEq Φ hΦ u hu
    have hup : up om m (om (k⁻¹, 1) Φ) (rTr A k⁻¹ u) = up om m Φ u := by
      funext h
      simp only [up]
      rw [e1 h, integral_descend_mul_right m (e2 h) k⁻¹]
    refine ⟨hup, fun ⟨c1, c2⟩ => ⟨fun h => ?_, hup ▸ c2⟩⟩
    have := c1 h
    rw [e1 h, integrable_descend_mul_right_iff m (e2 h) k⁻¹] at this
    exact this

  have hint : ∀ s y, integrand om m ν 𝓕 L a (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (rTr A k⁻¹ u₁) (rTr A k⁻¹ u₂) s y =
      integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s (k * y * k⁻¹) := by
    intro s y
    simp only [integrand]
    rw [wcoef_om hW hP.covol hΦ₁.1 hΦ₂.1, rcoef_rTr m lu₁ lu₂, hh a hP.maj]
    congr 3
    group
  obtain ⟨c1, c2, c3, z, hz, hpet⟩ := hG ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hw m mH hm hmH
    (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (fock Φ₁ hΦ₁) (fock Φ₂ hΦ₂)
    (rTr A k⁻¹ u₁) (GlobalTheory.T.rTr_mem_A0 D θ A cA hθ k⁻¹ hki u₁ hu₁)
    (rTr A k⁻¹ u₂) (GlobalTheory.T.rTr_mem_A0 D θ A cA hθ k⁻¹ hki u₂ hu₂)
  obtain ⟨up₁, cv₁⟩ := upConvIff Φ₁ hΦ₁.1 u₁ lu₁
  obtain ⟨up₂, cv₂⟩ := upConvIff Φ₂ hΦ₂.1 u₂ lu₂
  refine ⟨cv₁ c1, cv₂ c2, fun s hs => integrable_of_conj m k ?_, z, ?_, ?_⟩
  · have := c3 s hs
    rwa [show integrand om m ν 𝓕 L a (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (rTr A k⁻¹ u₁) (rTr A k⁻¹ u₂) s =
      fun y => integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s (k * y * k⁻¹) from funext (hint s)] at this
  · have e : (fun s => ∫ g, integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s g ∂m) =
        fun s => ∫ g, integrand om m ν 𝓕 L a (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (rTr A k⁻¹ u₁) (rTr A k⁻¹ u₂) s g ∂m := by
      funext s
      simp only [hint]
      rw [integral_conj m (integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s) k]
    rw [e]
    exact hz
  · rw [← up₁, ← up₂]
    exact hpet

end GlobalTheory.Core.Rk.GlobMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalDoublingZetaFormSelfDualLatticeTransferStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_doubling_zeta_form_selfDual_lattice_transfer : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' → GlobalFormAt A L → GlobalFormAt A L' := by
  first | exact @GlobalTheory.Core.Rk.GlobMove.globalFormAt_move | exact GlobalTheory.Core.Rk.GlobMove.globalFormAt_move | (intros; apply GlobalTheory.Core.Rk.GlobMove.globalFormAt_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionTransportChart
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RegSch.GChart

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate

variable {D : D7}

theorem trace_pow_conj {R : Type} [Ring R] [Algebra ℂ R] {n : ℕ} (E : Fin n → Fin n → R)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (m : ℕ) :
    ∑ c, (Matrix.of (fun a b => ∑ c, ∑ d, (P a c * Q d b) • E c d) ^ m) c c = ∑ c, (Matrix.of E ^ m) c c := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  let φ : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) R := (algebraMap ℂ R).mapMatrix
  have hc : ∀ (M : Matrix (Fin n) (Fin n) R) a b, (φ P * M * φ Q) a b = ∑ c, ∑ d, (P a c * Q d b) • M c d := by
    intro M a b
    simp only [Matrix.mul_apply, φ, RingHom.mapMatrix_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [← Algebra.smul_def, ← Algebra.commutes, ← Algebra.smul_def, smul_smul, mul_comm]
  have h1 : Matrix.of (fun a b => ∑ c, ∑ d, (P a c * Q d b) • E c d) = φ P * Matrix.of E * φ Q := by
    ext a b
    rw [hc]
    rfl
  have hqp : φ Q * φ P = 1 := by rw [← map_mul, hQP, map_one]
  have h2 : ∀ m : ℕ, (φ P * Matrix.of E * φ Q) ^ m = φ P * Matrix.of E ^ m * φ Q := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, mul_one, ← map_mul, hPQ, map_one]
    | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [mul_assoc]
      rw [← mul_assoc (φ Q), hqp, one_mul]
  rw [h1, h2]
  simp only [hc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  have : ∀ d, ∑ a, (P a c * Q d a) • (Matrix.of E ^ m) c d = (Q * P) d c • (Matrix.of E ^ m) c d := by
    intro d
    rw [← Finset.sum_smul, Matrix.mul_apply]
    simp only [mul_comm]
  simp [this, hQP, Matrix.one_apply]

section Chart

variable (A : HSp D) (μ : D.host.E) (hμ : GlobalTheory.StdUnn.IsSkew μ) (κ : GA D (dblSp A) ≃* GlobalTheory.StdUnn.G D A.rank)
  (hκ : GlobalTheory.StdUnn.IsChart A μ κ) {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau)

end Chart

end GlobalTheory.RegSch.GChart

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaPairAnalyticHypothesesOfDiscreteSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaPairAnalyticHypothesesOfDiscreteSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairLift

theorem inputs_of_chosenSeries :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
      GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (X : ProvA), ChosenSeries X → Inputs D X := by
  intro hDS hHC hDec hCW D X hX
  exact
    { chosen := hX
      hc := hHC
      decay := hDec
      bridge := GlobalTheory.CoverModel.modelsAreCoverSeries_all hDS hHC D
      vacChar := GlobalTheory.VacuumCharacter.vacChar D
      lie := GlobalTheory.LieScalar.lieFockAll D
      cpt := GlobalTheory.CompactFockAction.compactFockAll D
      dense := GlobalTheory.FockDensity.fockDense D
      laws := GlobalTheory.Chain.LiftReg.liftProps_of_rapidDecay hDec D (GlobalTheory.T.thetaKernel_moderateGrowth_with_seminorms D)
      const := GlobalTheory.T.constantTermLift_isotropicSubspace D
      ext := GlobalTheory.T.gkMapCuspForms_extends_to_smoothVectors hHC hCW D }

end GlobalTheory.PairLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaPairAnalyticHypothesesOfDiscreteSeriesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPairAnalyticHypotheses_of_discreteSeries : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (X : ProvA), ChosenSeries X → Inputs D X := by
  first | exact @GlobalTheory.PairLift.inputs_of_chosenSeries | exact GlobalTheory.PairLift.inputs_of_chosenSeries | (intros; apply GlobalTheory.PairLift.inputs_of_chosenSeries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsContAutRTrans
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.BotPin

variable {D : D7}

theorem isContAut_zero (V : HSp D) : IsContAut V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, continuous_const⟩

theorem isContAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem isContAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem isContAut_rTrans {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem isContAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact isContAut_smul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add (f := _)]; exact isContAut_add hx hy
  | zero => simpa using isContAut_zero V
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact isContAut_add (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact isContAut_smul (h x) c

end GlobalTheory.Core.Mi.BotPin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumFixedByLevelPairAtSelfDualPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumFixedByLevelPairAtSelfDualPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.VacFixP

theorem idAt_eq_bot {D : D7} {P : Pl D → Prop} (hP : ∀ v, ¬ P v) : idAt D P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  refine GlobalTheory.FinPlLoc.eq_zero_of_comp x hx.1 fun w => ?_
  exact (Submodule.mem_iInf _).1 hx.2 ⟨w, hP w⟩

theorem eq_one_of_grpAt {D : D7} {S : HSp D} {P : Pl D → Prop} (hP : ∀ v, ¬ P v) {κ : GA D S}
    (h : κ ∈ grpAt S P) : κ = 1 := by
  unfold grpAt congGrp at h
  rw [idAt_eq_bot hP, MonoidHom.mem_ker, MonoidHom.comp_apply] at h
  have h2 : matHom S κ = 1 := by
    apply Units.ext
    ext i j
    have := congrArg (fun g : GL (Fin S.rank) (AE D ⧸ (⊥ : Ideal (AE D))) => g.val i j) h
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at this
    rw [Units.val_one]
    rw [Matrix.one_apply] at this ⊢
    have h1 : ((if i = j then 1 else 0 : AE D ⧸ (⊥ : Ideal (AE D)))) = Ideal.Quotient.mk ⊥ (if i = j then 1 else 0) := by
      split_ifs <;> simp
    rw [h1, Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero] at this
    exact this
  unfold matHom at h2
  exact Subgroup.subtype_injective _ (h2.trans (map_one _).symm)

theorem vac_fix_on : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T) (P : Pl D → Prop), (∀ v, P v → IsSelfDualC S LS ∧ IsSelfDualC T LT ∧ Tame D v ∧ CharUnramAt D χS v ∧ CharUnramAt D χT v) → ∀ f, Vac ψ S T LS LT P f → ∀ κ κ', InK S LS P κ → InK T LT P κ' → om (κ, κ') f = f := by
  intro D ψ S T χS χT om hW LS LT P hP f hf κ κ' hκ hκ'
  by_cases hex : ∃ v, P v
  · obtain ⟨v, hv⟩ := hex
    obtain ⟨hS, hT, -⟩ := hP v hv
    exact GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ S T χS χT om hW LS LT hS hT P (fun w hw => (hP w hw).2.2) f hf κ κ' hκ hκ'
  · push_neg at hex
    rw [eq_one_of_grpAt hex hκ.1, eq_one_of_grpAt hex hκ'.1, Prod.mk_one_one, map_one]
    rfl

end GlobalTheory.VacFixP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumFixedByLevelPairAtSelfDualPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_fixed_by_levelPair_at_selfDualPlaces : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T) (P : Pl D → Prop), (∀ v, P v → IsSelfDualC S LS ∧ IsSelfDualC T LT ∧ Tame D v ∧ CharUnramAt D χS v ∧ CharUnramAt D χT v) → ∀ f, Vac ψ S T LS LT P f → ∀ κ κ', InK S LS P κ → InK T LT P κ' → om (κ, κ') f = f := by
  first | exact @GlobalTheory.VacFixP.vac_fix_on | exact GlobalTheory.VacFixP.vac_fix_on | (intros; apply GlobalTheory.VacFixP.vac_fix_on <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealThetaIntertwinerExchangedPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealThetaIntertwinerExchangedPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt

theorem itPairUp : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (k : Fin D.R.m) (V W : HSp D)
    (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ),
    S = parB (Ptw D) k → S' = parB (Ptw D) (k + 1) → IsInfFam θ → ChainPar D k →
    ∃ It : PolF D V.rank W.rank →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M', ∀ (ω : (GA D W × GA D V →* Module.End ℂ (WO W V → ℂ)))
      (f : WO W V → ℂ), IsWeilExp ψ W V (expT D k) (expS D k) ω → IsVacVec ψ θ M' M f →
        IsItW θ M' M ω (ptOf ψ θ M' M f) It := by
  intro hDS hHC D k V W S S' M M' θ ψ hS hS' hθ hP
  subst hS hS'
  obtain ⟨X, hX, h1, h2, -⟩ := GlobalTheory.T.exists_real_discreteSeries_data_theta_properties hDS hHC
  have hB := GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hDS hHC D
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (expS D k τ) (expT D k τ) A := fun τ => by
    obtain ⟨al, be, ga, de, hd, -, e1, e2⟩ := hP τ
    exact exists_locIt hX h1 h2 hB M M' τ hd (congrArg dualPar e1) (congrArg dualPar e2)
  choose hr A hA using key
  have hA' : ∀ τ, ∃ A', LocIt M' M τ (expT D k τ) (expS D k τ) A' := fun τ =>
    GlobalTheory.T.localFockIntertwiner_adjoint_exchangedPair D V W _ _ M M' τ _ _ (A τ) (hA τ)
  choose A' hA' using hA'
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D W V _ _ M' M (expT D k) (expS D k) A' GlobalTheory.ContrObj.contraction.2
    (GlobalTheory.T.gluing_law_holds D _ _) hA'
  refine ⟨It, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
  have hv := fun τ => GlobalTheory.T.thetaVacuumCharacters_realPlaces D W V _ _ M' M θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
  exact isItW_of_globIt hθ hI (fun τ => ⟨(hr τ).2, (hr τ).1⟩)
    (GlobalTheory.T.fockVectors_overVacuum_isometry D W V _ _ M' M ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1) fun τ => (hv τ).2.2

end GlobalTheory.Chain.RealIt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealThetaIntertwinerExchangedPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realThetaIntertwiner_exchangedPair : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (k : Fin D.R.m) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), S = parB (Ptw D) k → S' = parB (Ptw D) (k + 1) → IsInfFam θ → ChainPar D k → ∃ It : PolF D V.rank W.rank →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M', ∀ (ω : (GA D W × GA D V →* Module.End ℂ (WO W V → ℂ))) (f : WO W V → ℂ), IsWeilExp ψ W V (expT D k) (expS D k) ω → IsVacVec ψ θ M' M f → IsItW θ M' M ω (ptOf ψ θ M' M f) It := by
  first | exact @GlobalTheory.Chain.RealIt.itPairUp | exact GlobalTheory.Chain.RealIt.itPairUp | (intros; apply GlobalTheory.Chain.RealIt.itPairUp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalAdelicMatricesSelfAnnihilator
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalAdelicMatricesSelfAnnihilator
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GramAnnih

variable {D : D7} {m n : ℕ}

theorem pairing_rat (T : Matrix (Fin m) (Fin m) D.host.E) (ψ : AddChar (AF D.host.F) ℂ)
    (ξ : Matrix (Fin m) (Fin n) D.host.E) (x : Mx D m n) :
    GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ (GlobalTheory.MixModel.rat ξ) x =
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (GlobalTheory.MixModel.rat (ξᴴ * T) * x))) := by
  rw [rat_mul, rat_conjTranspose]
  rfl

theorem rat_single (j : Fin n) (i : Fin m) (e : D.host.E) :
    GlobalTheory.MixModel.rat (D := D) (Matrix.single j i e) = Matrix.single j i (incA D e) :=
  Matrix.map_single j i e (incA D)

theorem trace_tmul_half (t : AF D.host.F) :
    Algebra.trace (AF D.host.F) (AE D) (t ⊗ₜ[D.host.F] (2 : D.host.E)⁻¹) = t := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have e : (2 : D.host.E)⁻¹ = algebraMap D.host.F D.host.E 2⁻¹ := by rw [map_inv₀, map_ofNat]
  rw [e, GlobalTheory.LatVac.trace_tmul, Algebra.trace_algebraMap, D.sp.cm.deg2]
  simp

theorem ratMx_annihilator : ∀ (D : D7) (m n : ℕ) (T : Matrix (Fin m) (Fin m) D.host.E), IsHermND D.sp.cm.sig T → ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → (∀ x : Mx D m n, (∀ γ ∈ ratMx D m n, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ γ x = 1) ↔ x ∈ ratMx D m n) ∧ ∀ γ ∈ ratMx D m n, (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ γ x = 1) → γ = 0 := by
  intro D m n T hT ψ hψ
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have hU : IsUnit T.det := isUnit_iff_ne_zero.2 hT.2
  refine ⟨fun x => ⟨fun h => ?_, ?_⟩, ?_⟩
  · have key : ∀ i j (e : D.host.E), ψ (Algebra.trace (AF D.host.F) (AE D) (incA D e * x i j)) = 1 := by
      intro i j e
      have h1 := h _ (rat_mem (Matrix.single j i e * T⁻¹)ᴴ)
      rw [pairing_rat, Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_mul_cancel_right _ _ hU, rat_single,
        Matrix.trace_single_mul, smul_eq_mul] at h1
      exact h1
    have hent : ∀ i j, ∃ e : D.host.E, x i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := fun i j =>
      GlobalTheory.RatAnnih.tensor_rat (x i j) fun e =>
        (GlobalTheory.SWQ.Annihilator.self_annihilator D.host.F inferInstance ψ hψ).2 _ fun c =>
          (congrArg ψ (GlobalTheory.RatAnnih.trace_mul_algebraMap (x i j) e c)).trans (key i j (c • e))
    choose M hM using hent
    exact ⟨Matrix.of M, Matrix.ext fun i j => (hM i j).symm⟩
  · rintro ⟨η, rfl⟩ _ ⟨ξ, rfl⟩
    change GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ (GlobalTheory.MixModel.rat ξ) (GlobalTheory.MixModel.rat η) = 1
    have e : Matrix.trace (GlobalTheory.MixModel.rat (D := D) (ξᴴ * T * η)) =
        (1 : AF D.host.F) ⊗ₜ[D.host.F] Matrix.trace (ξᴴ * T * η) :=
      (AddMonoidHom.map_trace (incA D) _).symm
    rw [pairing_rat, ← rat_mul, e, GlobalTheory.LatVac.trace_tmul, one_mul]
    exact hψ.2.2.1 _
  · rintro _ ⟨ξ, rfl⟩ h
    change GlobalTheory.MixModel.rat ξ = 0
    have hM : ξᴴ * T = 0 := by
      refine Matrix.ext fun j i => ?_
      by_contra ha
      replace ha : (ξᴴ * T) j i ≠ 0 := ha
      obtain ⟨t, ht⟩ := hψ.2.2.2
      have h1 : GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ (GlobalTheory.MixModel.rat ξ) _ = 1 :=
        h (Matrix.single i j (t ⊗ₜ[D.host.F] ((2 : D.host.E)⁻¹ * ((ξᴴ * T) j i)⁻¹)))
      have e : (t ⊗ₜ[D.host.F] ((2 : D.host.E)⁻¹ * ((ξᴴ * T) j i)⁻¹)) * GlobalTheory.MixModel.rat (D := D) (ξᴴ * T) j i =
          t ⊗ₜ[D.host.F] (2 : D.host.E)⁻¹ := by
        change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (ξᴴ * T) j i) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, inv_mul_cancel_right₀ ha]
      rw [pairing_rat, Matrix.trace_mul_comm, Matrix.trace_single_mul, smul_eq_mul, e, trace_tmul_half] at h1
      exact ht h1
    have h0 : ξᴴ = 0 := by
      rw [← Matrix.mul_nonsing_inv_cancel_right T ξᴴ hU, hM, Matrix.zero_mul]
    rw [Matrix.conjTranspose_eq_zero.1 h0, rat_zero]

end GlobalTheory.GramAnnih
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalAdelicMatricesSelfAnnihilatorStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalAdelicMatrices_self_annihilator : ∀ (D : D7) (m n : ℕ) (T : Matrix (Fin m) (Fin m) D.host.E), IsHermND D.sp.cm.sig T → ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → (∀ x : Mx D m n, (∀ γ ∈ ratMx D m n, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ γ x = 1) ↔ x ∈ ratMx D m n) ∧ ∀ γ ∈ ratMx D m n, (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ γ x = 1) → γ = 0 := by
  first | exact @GlobalTheory.GramAnnih.ratMx_annihilator | exact GlobalTheory.GramAnnih.ratMx_annihilator | (intros; apply GlobalTheory.GramAnnih.ratMx_annihilator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomRelationOfPin
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
open Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting GlobalTheory.Core.Rk

noncomputable section

namespace GlobalTheory.MiTop.BotTwo

variable {D : D7}

theorem per_smul_f {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (φ : GA D B.A → ℂ) (b : ℂ) (f : GA D B.V → ℂ) :
    B.per ψ φ (b • f) = b * B.per ψ φ f := by
  simp only [BesLev.per, besPer, besFun, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x
  rw [← integral_const_mul]
  congr 1; funext n; ring

theorem contAut_zero (V : HSp D) : IsContAut V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, continuous_const⟩

theorem contAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem contAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem contAut_rTrans {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem contAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact contAut_smul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add (f := _)]; exact contAut_add hx hy
  | zero => simpa using contAut_zero V
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact contAut_add (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact contAut_smul (h x) c

theorem lev_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) {k : GA D V} (hk : k ∈ J)
    (g : GA D V) : G x (g * k) = χ k * G x g := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x g with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on generalizing g with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      simp only [Pi.smul_apply, smul_eq_mul, hT.lev v k hk g]; ring
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]; ring
  | zero => simp
  | add T₁ T₂ _ _ h₁ h₂ => simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply, h₁, h₂]; ring
  | smul c T _ h => simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, h]; ring

theorem shift_swap {G A B : Type} [Group G] [Group A] [Group B] (ι : G ≃* A × B) (g w : G) (y : A) (x : B)
    (hw : (ι w).1 = 1) : ι.symm (ι g * (y, x)) * w = g * (ι.symm (1, x) * w) * ι.symm (y, 1) := by
  apply ι.injective
  simp only [map_mul, MulEquiv.apply_symm_apply]
  ext
  · simp [hw]
  · simp [mul_assoc]

theorem comb_integral {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (c α α' : ℂ) (F F' : Y → ℂ)
    (h : ∀ y, α * F y + α' * F' y = 0) : α * (c * ∫ y, F y ∂ν) + α' * (c * ∫ y, F' y ∂ν) = 0 := by
  have hI : ∫ y, α * F y ∂ν = ∫ y, -(α' * F' y) ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => eq_neg_of_add_eq_zero_left (h y))
  rw [integral_neg, integral_const_mul, integral_const_mul] at hI
  linear_combination c * hI

end GlobalTheory.MiTop.BotTwo


end
end
