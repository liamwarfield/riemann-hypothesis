module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormula
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepRankZeroWittEmbeddingValueAtZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing MeasureTheory

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.VLast.Transport

section RankZero

variable {D : D7} {S S₀ : HSp D} (d : HypDec S S₀ 0)

theorem rz_gA : gA S = adj d.p0 ⬝ (gA S₀ ⬝ d.p0) := by
  rw [d.gA_eq, Subsingleton.elim d.pX 0, Subsingleton.elim d.pY 0]
  simp

theorem rz_j0p0 : d.j0 ⬝ d.p0 = 1 := by
  have := d.sum_eq_one
  rwa [Subsingleton.elim d.jX 0, Subsingleton.elim d.jY 0, Matrix.zero_mul, Matrix.zero_mul, zero_add, add_zero] at this

theorem unitaryMatrix_rankZeroWittEmbedding_eq (g : GA D S₀) : mt S (d.emb0 g) = d.j0 ⬝ mt S₀ g ⬝ d.p0 := by
  rw [d.unitaryMatrix_wittCoreEmbedding, Subsingleton.elim d.jX 0, Subsingleton.elim d.jY 0]
  simp

theorem rz_unit (g : GA D S) : adj (d.p0 ⬝ mt S g ⬝ d.j0) ⬝ (gA S₀ ⬝ (d.p0 ⬝ mt S g ⬝ d.j0)) = gA S₀ := by
  have key : ∀ X : Mx D S.rank S₀.rank, adj d.p0 ⬝ (gA S₀ ⬝ (d.p0 ⬝ X)) = gA S ⬝ X := fun X => by
    rw [rz_gA d, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [adj_mul, adj_mul]
  simp only [Matrix.mul_assoc]
  rw [key, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj (mt S g)), mt_unitary]
  exact d.gram_00

def rzInv (g : GA D S) : GA D S₀ := ofMat S₀ (d.p0 ⬝ mt S g ⬝ d.j0) (rz_unit d g)

theorem mt_rzInv (g : GA D S) : mt S₀ (rzInv d g) = d.p0 ⬝ mt S g ⬝ d.j0 := mt_ofMat _ _ _

def rzEquiv : GA D S₀ ≃* GA D S where
  toFun := d.emb0
  invFun := rzInv d
  left_inv g := mt_injective S₀ (by
    rw [mt_rzInv, unitaryMatrix_rankZeroWittEmbedding_eq]
    simp only [Matrix.mul_assoc, d.p0_j0, Matrix.mul_one]
    rw [← Matrix.mul_assoc, d.p0_j0, Matrix.one_mul])
  right_inv g := mt_injective S (by
    rw [unitaryMatrix_rankZeroWittEmbedding_eq, mt_rzInv]
    simp only [Matrix.mul_assoc, rz_j0p0 d, Matrix.mul_one]
    rw [← Matrix.mul_assoc, rz_j0p0 d, Matrix.one_mul])
  map_mul' := map_mul d.emb0

theorem rzInv_continuous : Continuous (rzInv d) :=
  continuous_of_mt S₀ (by
    simp only [mt_rzInv]
    exact (continuous_const.matrix_mul (continuous_mt S)).matrix_mul continuous_const)

theorem rzInv_mem_GQ {g : GA D S} (hg : g ∈ GQ S) : rzInv d g ∈ GQ S₀ := by
  rw [mem_GQ_iff, mt_rzInv]
  exact ratMx_mul (ratMx_mul (rat_mem _) ((mem_GQ_iff S g).1 hg)) (rat_mem _)

end RankZero

theorem weilRep_rankZeroWittEmbedding_valueAtZero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (d : HypDec S S₀ 0) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ f, IsThetaFunO ψ S T f → ∀ (g₀ : GA D S₀) (h : GA D T), om (d.emb0 g₀, h) f 0 = om₀ (g₀, h) (fun w => f (d.ext0 T w)) 0 := by
  intro D ψ S S₀ T d χS χT om om₀ hom hom₀ f hf g₀ h
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne (D := D) (m := T.rank) (n := 0)
  have hF := GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ S S₀ T 0 d χS χT om om₀ hom hom₀ μ 𝓕 hμ
  have H1 := (hF (om (1, h) f) (hom.om_pres _ _ hf)).core g₀ 0
  have H2 := (hF f hf).target h 0
  have hS : ∀ F x, _root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d T ψ μ 𝓕 F x =
      fun w => F (d.ext0 T w) := mixS_rankZero ψ S S₀ T d μ 𝓕 hμ
  simp only [hS] at H1 H2
  rw [H2] at H1
  have e1 : ((d.emb0 g₀, h) : GA D S × GA D T) = (d.emb0 g₀, 1) * (1, h) := by simp
  have e2 : ((g₀, h) : GA D S₀ × GA D T) = (g₀, 1) * (1, h) := by simp
  have := congrFun H1 0
  simp only [map_zero] at this
  rw [e1, e2, map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp]
  exact this

theorem om_flatBF_rankZero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (B : BesLev D 0) (J : JacLev D 0) (s : StepBF ψ B J) (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ (h₀ : GA D B.A) (g₀ : GA D J.W₀), s.om (embA B.d B.o h₀, J.d.emb0 g₀) Ψ 0 = s.om₀ (B.o.emb (h₀, 1), g₀) (flatBF s Ψ) 0 := by
  intro D ψ B J s Ψ hΨ h₀ g₀
  have hflat : ∀ X, flatBF s X = evalBF s X := by
    intro X; funext w
    obtain ⟨-, 𝓤, -, h1⟩ := s.vU.unit
    have : Subsingleton (UX D 0) := ⟨fun a b => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
    have hU : 𝓤 = Set.univ := by
      rcases Set.eq_empty_or_nonempty 𝓤 with he | ⟨x, hx⟩
      · rw [he, measure_empty] at h1; exact absurd h1 zero_ne_one
      · exact Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    have huniv : s.vU.ν Set.univ = 1 := hU ▸ h1
    have : IsProbabilityMeasure s.vU.ν := ⟨huniv⟩
    have hc : ∀ u : UX D 0, flatFun ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xZero J.d) (yZero B.V₀ 0 (vecB B.o B.ζ)) X w u = evalBF s X w := by
      intro u
      simp only [flatFun, evalBF, evalZero]
      rw [Subsingleton.elim (xZero J.d ⬝ u.1.1) (xZero J.d)]
      simp [psiUni, upSum, psiE]
    simp only [flatBF, flat, flatAt, hc, integral_const, probReal_univ, one_smul]
  have hd := GlobalTheory.T.weilDatum_descends_to_wittCore D
  have hm : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedModelFormulas D := ⟨GlobalTheory.T.mixedModelFormulasWittSource_proof D, GlobalTheory.T.mixedModelFormulas_wittTarget D⟩
  have hv := GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D
  rw [hflat, GlobalTheory.Unf.EvalCont.om_evalBF s hd hm hv hΨ h₀ g₀]
  unfold evalBF evalZero evalAt
  have hT : ∀ F y, _root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.target J.d B.V₀ ψ s.vT.μ s.vT.𝓕 F y =
      fun w => F (J.d.inc0 B.V₀ w) := mixT_rankZero ψ _ _ _ J.d s.vT.μ s.vT.𝓕 s.vT.covol
  have hS : ∀ F x, _root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source B.d J.W ψ s.vS.μ s.vS.𝓕 F x =
      fun w => F (B.d.ext0 J.W w) := mixS_rankZero ψ _ _ _ B.d s.vS.μ s.vS.𝓕 s.vS.covol
  rw [hT, hS]
  simp only [map_zero]

end GlobalTheory.FinPl.VLast.Transport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepLocalWeilActionLineCharactersCancel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepLocalWeilActionLineCharactersCancel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QPl.LineCancel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isComp_mul (p : Place D k) {χ χ' : (AE D)ˣ →* Circle} {μ μ' : kˣ →* ℂˣ} (h : p.IsComp χ μ)
    (h' : p.IsComp χ' μ') : p.IsComp (χ * χ') (μ * μ') := by
  intro x a ha
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, h x a ha, h' x a ha, Circle.coe_mul]

theorem isComp_inv (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ μ) :
    p.IsComp χ⁻¹ μ⁻¹ := by
  intro x a ha
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, h x a ha, Circle.coe_inv]

theorem om_mul {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ ν : kˣ →* ℂˣ) (g : GL a k)
    (h : GL b k) (Φ : Matrix b a k → ℂ) :
    om (μ * ν) g h Φ = (((ν (Matrix.GeneralLinearGroup.det g) * (ν (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ)) : ℂ) •
      om μ g h Φ := by
  funext t
  simp only [om, Pi.smul_apply, smul_eq_mul, MonoidHom.mul_apply, mul_inv, Units.val_mul]
  ring

theorem val_smul_inv {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} (S : Dbl2 ψ σ) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ)
    (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (A : WO S.B.V S.J.W → ℂ) (B : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ)
    (f : GA D S.B'.V → ℂ) (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) (z : ℂˣ) :
    S.val c₁ c₂ ((z : ℂ) • A) (((z⁻¹ : ℂˣ) : ℂ) • B) φ f g h₁ h₂ = S.val c₁ c₂ A B φ f g h₁ h₂ := by
  have e : S.con ((z : ℂ) • A) (((z⁻¹ : ℂˣ) : ℂ) • B) g h₁ h₂ = S.con A B g h₁ h₂ := by
    unfold Dbl2.con
    rw [map_smul, map_smul, GlobalTheory.HandHom.flatBF_smul, GlobalTheory.HandHom.flatFB_smul]
    funext u v
    unfold GlobalTheory.Unf.contr
    congr 1
    funext w
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_mul_mul_comm, Units.inv_mul, one_mul]
  unfold Dbl2.val
  rw [e]

end GlobalTheory.QPl.LineCancel

namespace GlobalTheory.QPl.LineCancel

theorem scal_one {G : Type} [Group G] (μ ζ : G →* ℂˣ) (a x : G) : ζ x = ((μ⁻¹ * ζ) * μ) a * (ζ⁻¹ a * (ζ⁻¹ x)⁻¹) := by
  rw [inv_mul_cancel_comm]
  simp only [MonoidHom.inv_apply, inv_inv, mul_inv_cancel_left]

theorem scal_two {G : Type} [Group G] (μ ζ : G →* ℂˣ) (x : G) : (ζ x)⁻¹ = (μ⁻¹ * (μ * ζ⁻¹)) x := by
  rw [inv_mul_cancel_left, MonoidHom.inv_apply]

end GlobalTheory.QPl.LineCancel

namespace GlobalTheory.QPl.LineCancel

theorem val_om_loc : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S)
    (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ))
    (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)),
    (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ →
  ∀ (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (φ : GA D S.B.A → ℂ) (F : GA D S.B'.V → ℂ)
    (a : GL (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) (x : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) (y : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k)
    (Φ₁ Φ₁' : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k))
    (Φ₂ Φ₂' : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k)),
    Φ₁'.1 = om Q.μ₁ a x Φ₁.1 → Φ₂'.1 = om Q.μ₂ x y Φ₂.1 →
    S.val c₁ c₂ (S.s₁.om (Q.gl₀ a, Q.gl₁ x) (T₁ Φ₁)) (S.s₂.om (Q.gl₁ x, Q.gl₂ y) (T₂ Φ₂)) φ F 1 1 1 =
      S.val c₁ c₂ (T₁ Φ₁') (T₂ Φ₂') φ F 1 1 1 := by
  intro D ψ hψ σ S Q T₁ T₂ h₁ h₂ c₁ c₂ φ F a x y Φ₁ Φ₁' Φ₂ Φ₂' e₁ e₂
  obtain ⟨ζ, hζ⟩ := GlobalTheory.LocMod.Witness.exists_isComp (ofSplit Q.q) S.χz
  have k₁' : (ofSplit Q.q).IsComp S.χ₁ Q.μ₁⁻¹ := by simpa using isComp_inv _ Q.comp₁
  have k₂' : (ofSplit Q.q).IsComp S.χ₂ Q.μ₂⁻¹ := by simpa using isComp_inv _ Q.comp₂
  have hV₁ : (ofSplit Q.q).IsComp S.s₁.χV (Q.μ₁⁻¹ * ζ) := by rw [S.V₁]; exact isComp_mul _ k₁' hζ
  have hW₁ : (ofSplit Q.q).IsComp S.s₁.χW Q.μ₁⁻¹ := by rw [S.W₁]; exact k₁'
  have hV₂ : (ofSplit Q.q).IsComp S.s₂.χV Q.μ₂⁻¹ := by rw [S.V₂]; exact k₂'
  have hW₂ : (ofSplit Q.q).IsComp S.s₂.χW (Q.μ₂⁻¹ * ζ) := by rw [S.W₂]; exact isComp_mul _ k₂' hζ
  have r₁ := GlobalTheory.T.weilDatum_localModel_formula D Q.k (ofSplit Q.q) ψ S.B.V S.J.W S.s₁.χV S.s₁.χW S.s₁.om S.s₁.weil (Q.μ₁⁻¹ * ζ) Q.μ₁⁻¹ hV₁ hW₁
    (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.F.G₀ Q.F.G₁ T₁ h₁ (Q.gl₀ a) a (Q.gl₁ x) x (Q.loc₀ a)
    (Q.loc₁ x) Φ₁ (((ζ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) • Φ₁') (by
      rw [Submodule.coe_smul, e₁, mul_inv, inv_inv, om_mul, smul_smul, ← Units.val_mul]
      congr 2
      exact scal_one Q.μ₁ ζ _ _)
  have r₂ := GlobalTheory.T.weilDatum_localModel_formula D Q.k (ofSplit Q.q) ψ S.J.W S.B'.V S.s₂.χV S.s₂.χW S.s₂.om S.s₂.weil Q.μ₂⁻¹ (Q.μ₂⁻¹ * ζ) hV₂ hW₂
    (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.F.G₁ Q.F.G₂ T₂ h₂ (Q.gl₁ x) x (Q.gl₂ y) y (Q.loc₁ x)
    (Q.loc₂ y) Φ₂ ((((ζ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) • Φ₂') (by
      rw [Submodule.coe_smul, e₂, inv_inv, mul_inv, inv_inv]
      congr 2
      exact scal_two Q.μ₂ ζ _)
  rw [r₁, r₂, map_smul, map_smul]
  exact val_smul_inv S c₁ c₂ _ _ φ F 1 1 1 _

end GlobalTheory.QPl.LineCancel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepLocalWeilActionLineCharactersCancelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStep_local_weil_action_line_characters_cancel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S)
    (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ))
    (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)),
    (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ →
  ∀ (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (φ : GA D S.B.A → ℂ) (F : GA D S.B'.V → ℂ)
    (a : GL (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) (x : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) (y : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k)
    (Φ₁ Φ₁' : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k))
    (Φ₂ Φ₂' : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k)),
    Φ₁'.1 = om Q.μ₁ a x Φ₁.1 → Φ₂'.1 = om Q.μ₂ x y Φ₂.1 →
    S.val c₁ c₂ (S.s₁.om (Q.gl₀ a, Q.gl₁ x) (T₁ Φ₁)) (S.s₂.om (Q.gl₁ x, Q.gl₂ y) (T₂ Φ₂)) φ F 1 1 1 =
      S.val c₁ c₂ (T₁ Φ₁') (T₂ Φ₂') φ F 1 1 1 := by
  first | exact @GlobalTheory.QPl.LineCancel.val_om_loc | exact GlobalTheory.QPl.LineCancel.val_om_loc | (intros; apply GlobalTheory.QPl.LineCancel.val_om_loc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelTensorIntegralIndicator
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelTensorIntegralIndicator
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.TOneModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem pi_e : p.π p.e = 1 := by
  have h : p.ι 1 = p.e := by simpa using p.ι_π 1
  rw [← h, p.π_ι]

theorem pi_of_mul {e : AE D} (he : e * p.e = 0) : p.π e = 0 := by
  have h := congrArg p.π he
  rwa [map_mul, pi_e, mul_one, map_zero] at h

theorem up_down_eq (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (t : WO S T) :
    p.up FS FT (p.down FS FT t) = t.map (fun a => p.e * a) := by
  unfold Place.up Place.down
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
  ext i j
  simp only [Matrix.map_apply]
  exact p.ι_π _

theorem down_half_zero (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D} (he : e * p.e = 0) {x : WO S T}
    (hx : IsHalf e x) : p.down FS FT x = 0 := by
  unfold Place.down
  have h : (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π = 0 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.zero_apply]
    rw [← hx i j, map_mul, pi_of_mul p he, zero_mul]
  rw [h, Matrix.mul_zero, Matrix.zero_mul]

theorem half_sum {e : AE D} (he : e * p.e = 0) {x : WO S T} (hx : IsHalf e x) : IsHalf (e + p.e) x := by
  intro i j
  have h : p.e * x i j = 0 := by rw [← hx i j, ← mul_assoc, mul_comm p.e e, he, zero_mul]
  rw [add_mul, hx i j, h, add_zero]

theorem half_sum_conj {e : AE D} (he : e * p.e = 0) {y : WO S T} (hy : IsHalf (cA D e) y) :
    IsHalf (cA D (e + p.e)) y := by
  intro i j
  have h : cA D p.e * y i j = 0 := by
    rw [← hy i j, ← mul_assoc, ← map_mul, mul_comm p.e e, he, map_zero, zero_mul]
  rw [map_add (f := _), add_mul, hy i j, h, add_zero]

theorem hO_zero {e : AE D} (he : e * p.e = 0) {w y : WO S T} (hw : IsHalf p.e w) (hy : IsHalf (cA D e) y) :
    hO S T w y = 0 := by
  unfold hO
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  have h1 : cA D (y c b) = e * cA D (y c b) := by
    conv_lhs => rw [← hy c b, map_mul, Formalism.L2.Theta.cA_cA]
  rw [h1, ← hw d a]
  linear_combination (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * w d a) * he

theorem symplO_sub_half {e : AE D} (he : e * p.e = 0) (t : WO S T) {w y : WO S T} (hw : IsHalf p.e w)
    (hy : IsHalf (cA D e) y) : symplO S T (t - w) y = symplO S T t y := by
  have h : hO S T (t - w) y = hO S T t y - hO S T w y := by
    simp only [hO, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  unfold symplO
  rw [h, hO_zero p he hw hy, sub_zero]

end GlobalTheory.LocMod.TOneModel

namespace GlobalTheory.LocMod.TOneModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem tensorOne_trans (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D} (he : e * p.e = 0)
    (Φ : WO S T → ℂ) {x : WO S T} (hx : IsHalf e x) :
    p.tensorOne FS FT (fun t => Φ (t + x)) = fun t => p.tensorOne FS FT Φ (t + x) := by
  funext t
  simp only [Place.tensorOne_apply, Place.tensorAt]
  rw [GlobalTheory.LocMod.Witness.down_add p FS FT t x, down_half_zero p FS FT he hx, add_zero, sub_add_eq_add_sub]

theorem tensorOne_modul (ψ : AddChar (AF D.host.F) ℂ) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D}
    (he : e * p.e = 0) (Φ : WO S T → ℂ) {y : WO S T} (hy : IsHalf (cA D e) y) :
    p.tensorOne FS FT (fun t => ψ (symplO S T t y) * Φ t) = fun t => ψ (symplO S T t y) * p.tensorOne FS FT Φ t := by
  funext t
  simp only [Place.tensorOne_apply, Place.tensorAt]
  rw [symplO_sub_half p he t (GlobalTheory.LocMod.Witness.up_half p FS FT _) hy, mul_assoc]

open Classical in
theorem intInd_eq (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    (hint : ∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) (x : Matrix Y Y' k) :
    Place.intInd Y Y' x = if p.up FS FT x ∈ stdHom S T then 1 else 0 := by
  classical
  unfold Place.intInd
  rw [Set.indicator_apply]
  exact if_congr (hint x) rfl rfl

theorem tensorOne_vac (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D} (he : e * p.e = 0)
    (hint : ∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T)
    (hstab : ∀ u ∈ stdHom S T, u.map (fun a => p.e * a) ∈ stdHom S T) :
    p.tensorOne FS FT ((1 : ℂ) • halfInd e (stdHom S T)) = (1 : ℂ) • halfInd (e + p.e) (stdHom S T) := by
  classical
  funext t
  simp only [one_smul]
  rw [Place.tensorOne_apply]
  simp only [Place.tensorAt]
  rw [intInd_eq p FS FT hint, up_down_eq p FS FT t]
  set M : WO S T := t.map (fun a => p.e * a) with hMdef
  have key : ((t - M ∈ stdHom S T ∧ IsHalf e (t - M)) ∧ M ∈ stdHom S T) ↔ (t ∈ stdHom S T ∧ IsHalf (e + p.e) t) := by
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨by simpa using add_mem h1 h3, fun i j => ?_⟩
      have h := h2 i j
      simp only [hMdef, Matrix.sub_apply, Matrix.map_apply] at h
      linear_combination h + t i j * he
    · rintro ⟨h1, h2⟩
      have h3 : M ∈ stdHom S T := hstab t h1
      refine ⟨⟨sub_mem h1 h3, fun i j => ?_⟩, h3⟩
      simp only [hMdef, Matrix.sub_apply, Matrix.map_apply]
      linear_combination h2 i j - t i j * he
  unfold halfInd
  by_cases hR : t ∈ stdHom S T ∧ IsHalf (e + p.e) t
  · obtain ⟨⟨h1, h2⟩, h3⟩ := key.2 hR
    rw [if_pos hR, if_pos ⟨h1, h2⟩, if_pos h3, mul_one]
  · rw [if_neg hR]
    by_cases h3 : M ∈ stdHom S T
    · rw [if_pos h3, mul_one, if_neg fun h => hR (key.1 ⟨h, h3⟩)]
    · rw [if_neg h3, mul_zero]

theorem isPlaceModel_tensorOne : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (e : AE D), e * p.e = 0 → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → (∀ u ∈ stdHom S T, u.map (fun a => p.e * a) ∈ stdHom S T) → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + p.e) (stdHom S T) 1 f₀ T' → (∀ Φ, IsSBHalf e (stdHom S T) Φ → IsSBHalf (e + p.e) (stdHom S T) (p.tensorAt FS FT Φ (Place.intInd Y Y'))) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 f₀ (T' ∘ₗ p.tensorOne FS FT) := by
  intro D k _ _ _ _ p ψ S T Y Y' _ _ _ _ FS FT e he hint hstab f₀ T' hT' hsb
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · rw [LinearMap.comp_apply, tensorOne_trans p FS FT he Φ hx]
    exact hT'.trans (p.tensorOne FS FT Φ) (hsb Φ hΦ) x (half_sum p he hx)
  · rw [LinearMap.comp_apply, tensorOne_modul p ψ FS FT he Φ hy]
    exact hT'.modul (p.tensorOne FS FT Φ) (hsb Φ hΦ) y (half_sum_conj p he hy)
  · rw [LinearMap.comp_apply, tensorOne_vac p FS FT he hint hstab]
    exact hT'.vac

end GlobalTheory.LocMod.TOneModel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelTensorIntegralIndicatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPlaceModel_tensorIntegralIndicator : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (e : AE D), e * p.e = 0 → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → (∀ u ∈ stdHom S T, u.map (fun a => p.e * a) ∈ stdHom S T) → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + p.e) (stdHom S T) 1 f₀ T' → (∀ Φ, IsSBHalf e (stdHom S T) Φ → IsSBHalf (e + p.e) (stdHom S T) (p.tensorAt FS FT Φ (Place.intInd Y Y'))) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 f₀ (T' ∘ₗ p.tensorOne FS FT) := by
  first | exact @GlobalTheory.LocMod.TOneModel.isPlaceModel_tensorOne | exact GlobalTheory.LocMod.TOneModel.isPlaceModel_tensorOne | (intros; apply GlobalTheory.LocMod.TOneModel.isPlaceModel_tensorOne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryPairMapsCompletedHomLatticeOntoTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryPairMapsCompletedHomLatticeOntoTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatMoveStd

variable {D : D7}

theorem mt_mul'' (V : HSp D) (g g' : GA D V) : mt V (g * g') = mt V g * mt V g' := by
  show (matHom V (g * g')).1 = (matHom V g).1 * (matHom V g').1
  rw [map_mul, Units.val_mul]

theorem mt_one'' (V : HSp D) : mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  rw [map_one, Units.val_one]

theorem cA_cA'' (x : AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a e =>
    show (a ⊗ₜ[D.host.F] D.sp.cm.sig (D.sp.cm.sig e)) = _
    rw [show D.sp.cm.sig (D.sp.cm.sig e) = e from star_star e]

theorem unitary (V : HSp D) (hg : V.gram = 1) (g : GA D V) :
    ((mt V g).map (cA D))ᵀ * mt V g = 1 := by
  have h : ((mt V g).map (cA D))ᵀ * V.gram.map (incA D) * mt V g = V.gram.map (incA D) :=
    (g : HR (AF D.host.F) D.sp.cm.sig V.gram).2
  rw [hg, Matrix.map_one (incA D) (map_zero _) (map_one _), Matrix.mul_one] at h
  exact h

theorem mt_inv_eq (V : HSp D) (hg : V.gram = 1) (g : GA D V) : mt V g⁻¹ = ((mt V g).map (cA D))ᵀ := by
  have h1 := unitary V hg g
  have h2 : mt V g * mt V g⁻¹ = 1 := by rw [← mt_mul'', mul_inv_cancel, mt_one'']
  calc mt V g⁻¹ = (((mt V g).map (cA D))ᵀ * mt V g) * mt V g⁻¹ := by rw [h1, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]


set_option synthInstance.maxHeartbeats 200000 in
theorem int_of_moves (V : HSp D) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hM : Moves V rfl g N) (x : Fin V.rank → D.host.E) (hx : x ∈ N) (i : Fin V.rank) :
    finPart D ((mt V g⁻¹ *ᵥ fun k => incA D (x k)) i) ∈ intAE D := by
  rw [GlobalTheory.SplitDec.int_iff]
  have := (hM x).1 hx i
  have e : toEAf D ((mt V g⁻¹ *ᵥ fun k => incA D (x k)) i) = (finM V rfl g⁻¹ *ᵥ fun j => eToEAf D (x j)) i := by
    simp only [Matrix.mulVec, dotProduct]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    rfl
  rw [e]; exact this

theorem gen_eq (α : Af D.host.F) (c x y : D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * x * y) = (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) * incA D x * incA D y := by
  simp [incA, inclR, Algebra.TensorProduct.tmul_mul_tmul]

end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd

variable {D : D7}


set_option synthInstance.maxHeartbeats 200000 in
theorem int_conj (V : HSp D) (hg : V.gram = 1) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hM : Moves V rfl g N) (s : Fin V.rank → D.host.E) (hs : s ∈ N) (j : Fin V.rank) :
    finPart D (∑ l, cA D (incA D (s l)) * mt V g l j) ∈ intAE D := by
  rw [← GlobalTheory.FinPl.FrameLat.cA_int_iff]
  have e : cA D (∑ l, cA D (incA D (s l)) * mt V g l j) = (mt V g⁻¹ *ᵥ fun k => incA D (s k)) j := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mt_inv_eq V hg g, map_sum]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, cA_cA'', mul_comm]
  rw [e]; exact int_of_moves V g N hM s hs j

theorem single_mem (S T : HSp D) (hgS : S.gram = 1) (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (c : D.host.E)
    (hc : c ∈ D.host.AA) (i0 : Fin T.rank) (j0 : Fin S.rank) :
    (Matrix.single i0 j0 (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) : WO S T) ∈
      latO S T (intVec D _) (intVec D _) (fun _ => True) := by
  have hint : ∀ {n : ℕ} (k : Fin n), Pi.single k (1 : D.host.E) ∈ intVec D n := by
    intro n k l
    by_cases h : l = k
    · subst h; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
  refine AddSubgroup.subset_closure ⟨α, hα, fun _ h => absurd trivial h, c, hc, Pi.single j0 1, hint j0,
    Pi.single i0 1, hint i0, ?_⟩
  ext i j
  rw [Matrix.of_apply, hgS]
  have hsum : ∑ k, star ((Pi.single j0 (1 : D.host.E) : Fin S.rank → D.host.E) k) *
      (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E) k j =
      star ((Pi.single j0 (1 : D.host.E) : Fin S.rank → D.host.E) j) := by
    rw [Finset.sum_eq_single j (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), Matrix.one_apply_eq, mul_one]
  rw [hsum]
  by_cases hi : i = i0
  · subst hi
    by_cases hj : j = j0
    · subst hj
      rw [Matrix.single_apply_same, Pi.single_eq_same, Pi.single_eq_same, star_one, mul_one, mul_one]
    · rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hj), Pi.single_eq_of_ne hj, star_zero, mul_zero,
        TensorProduct.tmul_zero]
  · rw [Matrix.single_apply_of_row_ne (Ne.symm hi), Pi.single_eq_of_ne hi, mul_zero, zero_mul,
      TensorProduct.tmul_zero]

end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd

variable {D : D7}

theorem row_one {n : ℕ} (s : Fin n → D.host.E) (l : Fin n) :
    ∑ m, star (s m) * (1 : Matrix (Fin n) (Fin n) D.host.E) m l = star (s l) := by
  rw [Finset.sum_eq_single l (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero])
    (fun h => absurd (Finset.mem_univ l) h), Matrix.one_apply_eq, mul_one]


set_option synthInstance.maxHeartbeats 200000 in
theorem gen_mem (S T : HSp D) (hgS : S.gram = 1) (hgT : T.gram = 1) (g : GA D S) (h : GA D T)
    (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hN : Moves S rfl g N) (hN' : Moves T rfl h N') (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (c : D.host.E)
    (hc : c ∈ D.host.AA) (s : Fin S.rank → D.host.E) (hs : s ∈ N) (t : Fin T.rank → D.host.E) (ht : t ∈ N') :
    actO S T g⁻¹ h⁻¹ (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j))
      ∈ latO S T (intVec D _) (intVec D _) (fun _ => True) := by
  have e1 : actO S T g⁻¹ h⁻¹
      (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j)) =
      Matrix.of fun i j => ((mt T h⁻¹ *ᵥ fun k => incA D (t k)) i * ∑ l, cA D (incA D (s l)) * mt S g l j) *
        (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) := by
    ext i j
    simp only [actO, inv_inv, Matrix.mul_apply, Matrix.of_apply, hgS, row_one, gen_eq,
      ← GlobalTheory.FinPl.FrameLat.cA_incA, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  rw [e1, Matrix.matrix_eq_sum_single ((Matrix.of fun i j =>
    ((mt T h⁻¹ *ᵥ fun k => incA D (t k)) i * ∑ l, cA D (incA D (s l)) * mt S g l j) *
        (pairA D.host.F 0 α ⊗ₜ[D.host.F] c)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))]
  refine sum_mem fun i0 _ => sum_mem fun j0 _ => ?_
  rw [Matrix.of_apply, ← smul_eq_mul, ← Matrix.smul_single]
  refine GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ?_ _ (single_mem S T hgS α hα c hc i0 j0)
  rw [map_mul]
  exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE (int_of_moves T h N' hN' t ht i0) (int_conj S hgS g N hN s hs j0)

end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd

theorem latO_moved_onto : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b), S.gram = 1 → T.gram = 1 → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), Moves S hS g N → Moves T hT h N' → ∀ u' ∈ latO S T (latFr S hS N) (latFr T hT N') (fun _ => True), ∃ u ∈ latO S T (intVec D _) (intVec D _) (fun _ => True), actO S T g h u = u' := by
  intro D S T a b hS hT hgS hgT g _ h _ N N' hN hN' u' hu'
  subst hS; subst hT
  refine ⟨actO S T g⁻¹ h⁻¹ u', ?_, ?_⟩
  · let Ψ : WO S T →+ WO S T :=
      { toFun := actO S T g⁻¹ h⁻¹
        map_zero' := by simp only [actO, Matrix.mul_zero, Matrix.zero_mul]
        map_add' := fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul] }
    have key : latO S T (latFr S rfl N) (latFr T rfl N') (fun _ => True) ≤
        (latO S T (intVec D _) (intVec D _) (fun _ => True)).comap Ψ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨α, hα, -, c, hc, s, hs, t, ht, rfl⟩
      exact gen_mem S T hgS hgT g h N N' hN hN' α hα c hc s hs t ht
    exact key hu'
  · simp only [actO]
    rw [inv_inv, Matrix.mul_assoc (mt T h), Matrix.mul_assoc (mt T h⁻¹ * u'), ← mt_mul'', mul_inv_cancel, mt_one'', Matrix.mul_one,
      ← Matrix.mul_assoc, ← mt_mul'', mul_inv_cancel, mt_one'', Matrix.one_mul]

end GlobalTheory.LatMoveStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryPairMapsCompletedHomLatticeOntoTranslateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryPair_maps_completedHomLattice_onto_translate : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b), S.gram = 1 → T.gram = 1 → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), Moves S hS g N → Moves T hT h N' → ∀ u' ∈ latO S T (latFr S hS N) (latFr T hT N') (fun _ => True), ∃ u ∈ latO S T (intVec D _) (intVec D _) (fun _ => True), actO S T g h u = u' := by
  first | exact @GlobalTheory.LatMoveStd.latO_moved_onto | exact GlobalTheory.LatMoveStd.latO_moved_onto | (intros; apply GlobalTheory.LatMoveStd.latO_moved_onto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfCocycleIsotropicIdempotentHalvesTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfCocycleIsotropicIdempotentHalvesTrivial
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfCocycle

theorem half_eq (D : D7) :
    incA D ((2 : D.host.E)⁻¹) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2)) := by
  have h2 : ((2 : D.host.E))⁻¹ = algebraMap D.host.F D.host.E (1 / 2) := by
    rw [map_div₀, map_one, map_ofNat, one_div]
  rw [h2, ← IsScalarTower.algebraMap_apply D.host.F (AF D.host.F) (AE D)]
  show (inclR (AF D.host.F)) (algebraMap D.host.F D.host.E (1/2)) = _
  simp [inclR, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]

theorem half_mul_symplO {D : D7} (S T : HSp D) (x y : WO S T) :
    algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T x y = symplO S T (incA D ((2 : D.host.E)⁻¹) • x) y := by
  unfold symplO
  rw [GlobalTheory.SplitScalar.hO_smul_left, half_eq, mul_left_comm (incA D D.host.xi0),
    ← Algebra.smul_def (algebraMap D.host.F (AF D.host.F) (1 / 2)) (incA D D.host.xi0 * hO S T x y),
    LinearMap.map_smul, smul_eq_mul]

theorem half_idem_int {D : D7} {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (hI : IsIdemSum e SS)
    (h2 : ∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) :
    finPart D (incA D ((2 : D.host.E)⁻¹) * e) ∈ intAE D := by
  obtain ⟨⟨es, hes, rfl⟩, _⟩ := hI
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, map_sum]
  refine AddSubgroup.sum_mem _ fun PP hPP => ?_
  have hn : (2 : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro hm
    apply h2 PP hPP
    have h2Q : 2 ∣ D.host.QS := (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd
    obtain ⟨k, hk⟩ := h2Q
    rw [hk]
    push_cast
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hm))
  have hiff := (hes PP hPP).2 (2 : 𝓞 D.host.E) two_ne_zero
  have hc : ((2 : 𝓞 D.host.E) : D.host.E) = 2 := by first | rfl | simp | exact map_ofNat _ 2 | norm_cast
  rw [hc] at hiff
  rw [mul_comm]
  by_contra hc'
  exact hn (hiff.mpr hc')

end GlobalTheory.HalfCocycle


open GlobalTheory.HalfCocycle in
theorem GlobalTheory.HalfCocycle.char_symplOH_idem_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ u ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True), ∀ v ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True), ψ (symplOH S T (e • u) (cA D e • v)) = 1 := by
  intro D ψ θ S T δ sc hP e SS hI h2 N N' hN hN' u hu v hv
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self hI
  have key : symplO S T (e • u) (cA D e • v) = symplO S T (e • u) v := by
    rw [← GlobalTheory.SplitScalar.symplO_smul, smul_smul, hee]
  rw [symplOH, key, half_mul_symplO, smul_smul]
  exact GlobalTheory.LatVac.char_sympl_eq_one hP.std hN hN'
    (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (half_idem_int hI h2) u hu) hv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfCocycleIsotropicIdempotentHalvesTrivialStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfCocycle_isotropic_idempotentHalves_trivial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ u ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True), ∀ v ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True), ψ (symplOH S T (e • u) (cA D e • v)) = 1 := by
  first | exact @GlobalTheory.HalfCocycle.char_symplOH_idem_conj | exact GlobalTheory.HalfCocycle.char_symplOH_idem_conj | (intros; apply GlobalTheory.HalfCocycle.char_symplOH_idem_conj <;> assumption)
end
end
