module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingEvaluation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterTransferAllFinitePlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalProductFormula
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormFiniteDimCompactStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedTensorFactorMemCoeffField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeSpanProjectionPreservesFiniteDimInvariantSub
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUpwardCuspSpanAndAdjoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGKSubmoduleISupGelfandJointEigenspaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupTransposeGramRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupTransposeGramRealPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.LineAtPlace

variable {D : D7}

theorem emb_eq_or_conj (e₁ e₂ : D.host.E →+* ℂ)
    (h : ∀ a : D.host.F, e₁ (algebraMap D.host.F D.host.E a) = e₂ (algebraMap D.host.F D.host.E a)) :
    (∀ x, e₂ x = e₁ x) ∨ ∀ x, e₂ x = starRingEnd ℂ (e₁ x) := by
  have hconj : ∀ a : D.host.E, e₁ (star a) = starRingEnd ℂ (e₁ a) := D.sp.cm.cmUnram.2.1 e₁
  have hb := Eqv.star_alphaE D
  have hdec : ∀ y : D.host.E, ∃ p q : D.host.F,
      y = algebraMap D.host.F D.host.E p + algebraMap D.host.F D.host.E q * Eqv.alphaE D := by
    intro y
    refine ⟨(Eqv.basE D).repr y 0, (Eqv.basE D).repr y 1, ?_⟩
    conv_lhs => rw [← (Eqv.basE D).sum_repr y]
    rw [Fin.sum_univ_two, Eqv.basE_zero, Eqv.basE_one, Algebra.smul_def, Algebra.smul_def, mul_one]
  have hb2 : e₂ (Eqv.alphaE D) ^ 2 = e₁ (Eqv.alphaE D) ^ 2 := by
    have h1 : star (Eqv.alphaE D ^ 2) = Eqv.alphaE D ^ 2 := by rw [star_pow, hb]; ring
    obtain ⟨t, ht⟩ := (D.sp.cm.fixed _).1 h1
    rw [← map_pow, ← map_pow, ← ht, h]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hb2 with hc | hc
  · left
    intro y
    obtain ⟨p, q, rfl⟩ := hdec y
    rw [map_add (f := _), map_add (f := _), map_mul, map_mul, hc, h, h]
  · right
    intro y
    obtain ⟨p, q, rfl⟩ := hdec y
    rw [← hconj, star_add, star_mul, Eqv.star_algebraMapF, Eqv.star_algebraMapF, hb, map_add (f := _), map_add (f := _), map_mul, map_mul,
      map_neg, hc, h, h]
    ring

theorem exists_piInf (τ : D.what₂.Tau) (p : GlobalTheory.AdelicU.EmbOver D.host.E (Eqv.plW D τ)) :
    ∃ c : ℂ →+* ℂ, Continuous c ∧ (∀ (t : ℝ) z, c (t • z) = t • c z) ∧
      ∀ y : AE D, Eqv.psiT D τ y = c (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf p y) := by
  have key : ∀ c : ℂ →+* ℂ, (∀ t : ℝ, c t = t) → (∀ x, tauE D τ x = c (p.1 x)) →
      ∀ y : AE D, Eqv.psiT D τ y = c (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf p y) := by
    intro c hc hx y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]
    | tmul a x =>
      have l1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf p (a ⊗ₜ[D.host.F] x) = Eqv.gW D (Eqv.plW D τ) (fstA D.host.F a) * p.1 x :=
        GlobalTheory.AdelicU.infEmb_tmul p _ x
      have l2 : Eqv.psiT D τ (a ⊗ₜ[D.host.F] x) = Eqv.gW D (Eqv.plW D τ) (fstA D.host.F a) * tauE D τ x :=
        Eqv.thetaC_tmul D τ _ x
      rw [l1, l2, map_mul, hx, Eqv.gW_real, hc]
  rcases emb_eq_or_conj p.1 (tauE D τ) (fun a => RingHom.congr_fun (p.2.trans (Eqv.plW_embedding D τ)) a) with h | h
  · exact ⟨RingHom.id ℂ, continuous_id, fun _ _ => rfl, key _ (fun _ => rfl) h⟩
  · exact ⟨starRingEnd ℂ, Complex.continuous_conj, fun t z => by simp, key _ Complex.conj_ofReal h⟩

theorem kapX_surj (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (k : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) : ∃ h, kapX X e hJ h = k := by
  subst hJ
  have h1 : (k.1.1)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • reindex e e X.gramᵀ) * (k.1.1).map (cA D) =
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • reindex e e X.gramᵀ) := k.2
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at h1
  have hx : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have h2 := congrArg (fun Y => ((incA D D.host.xi0⁻¹ • Y)ᵀ).submatrix e e) h1
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ hx, map_one, one_smul, transpose_mul,
    transpose_transpose, ← Matrix.mul_assoc] at h2
  rw [← submatrix_mul_equiv _ _ _ e, ← submatrix_mul_equiv _ _ _ e] at h2
  have e1 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ))ᵀ.submatrix e e = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram := by
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  rw [e1] at h2
  refine ⟨⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom k.1, h2⟩, Subtype.ext (Units.ext ?_)⟩
  show reindex e e (reindex e.symm e.symm k.1.1) = k.1.1
  simp


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem lie_of_exp {n : ℕ} (Y H : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Y))ᴴ * H * NormedSpace.exp (t • Y) = H) : Yᴴ * H + H * Y = 0 := by
  have h1 := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) Yᴴ (0 : ℝ)).mul_const H).fun_mul
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ))
  have h2 : (fun t : ℝ => NormedSpace.exp (t • Yᴴ) * H * NormedSpace.exp (t • Y)) = fun _ => H := by
    funext t
    have e : t • Yᴴ = (t • Y)ᴴ := by rw [Matrix.conjTranspose_smul, star_trivial]
    rw [e, Matrix.exp_conjTranspose]
    exact h t
  have h3 := (h1.congr_of_eventuallyEq (f₁ := fun _ => H)
    (Filter.Eventually.of_forall fun t => (congrFun h2 t).symm)).unique (hasDerivAt_const _ _)
  simpa using h3


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem exp_map {n d : ℕ} (e : Fin n ≃ Fin d) (c : ℂ →+* ℂ) (hc : Continuous c) (Z : Matrix (Fin d) (Fin d) ℂ) :
    ((NormedSpace.exp Z).map c).submatrix e e = NormedSpace.exp ((Z.map c).submatrix e e) :=
  NormedSpace.map_exp ((Matrix.reindexAlgEquiv ℂ ℂ e.symm).toRingHom.comp c.mapMatrix)
    ((continuous_id.matrix_map hc).matrix_submatrix e e) Z

end GlobalTheory.LineAtPlace

open GlobalTheory.LineAtPlace in
theorem GlobalTheory.LineAtPlace.exists_oneP : ∀ (D : D7) (θ : InfFam D) (X : HSp D), IsInfFam θ → ∀ {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ)
    (emb : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w) (w : InfinitePlace D.host.F)
    (Z : Matrix (Fin d) (Fin d) ℂ) (γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J),
    γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd →
    (∀ t : ℝ, (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w)) =
      NormedSpace.exp (t • Z)) →
    (∀ (t : ℝ) (w' : InfinitePlace D.host.F), w' ≠ w →
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w')) = 1) →
    ∃ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ), Y ∈ lieAt X τ ∧
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ (oneP θ X τ Y t) := by
  intro D θ X hθ d e Wd hJ emb w Z γ hγ hw ho
  obtain rfl := Eqv.eq_thetaC D hθ
  obtain ⟨τ, rfl⟩ : ∃ τ, Eqv.plW D τ = w := ⟨_, Eqv.plW_symm D w⟩
  choose h hh using fun t : ℝ => kapX_surj X e hJ (γ (Multiplicative.ofAdd t))
  have hm : ∀ t, Eqv.matA D X (h t) = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).submatrix e e := by
    intro t
    rw [← hh t]
    show _ = (reindex e e (Eqv.matA D X (h t))).submatrix e e
    simp
  obtain ⟨c, hc, hcs, hp⟩ := exists_piInf τ (emb _)
  have h1 : ∀ t : ℝ, infMat D.sp.cm.sig X.gram (Eqv.thetaC D τ) (h t) =
      NormedSpace.exp (t • (Z.map c).submatrix e e) := by
    intro t
    have e1 : t • (Z.map c).submatrix e e = ((t • Z).map c).submatrix e e := by
      ext i j
      exact (hcs t _).symm
    rw [Eqv.infMat_thetaC, hm, e1, ← exp_map e c hc, ← hw]
    ext i j
    exact hp _
  have hu : ∀ t : ℝ, (NormedSpace.exp (t • (Z.map c).submatrix e e))ᴴ * gramAt D X τ *
      NormedSpace.exp (t • (Z.map c).submatrix e e) = gramAt D X τ := by
    intro t
    rw [← h1]
    exact Eqv.infMat_unitary' D X (h t) τ
  refine ⟨τ, (Z.map c).submatrix e e, lie_of_exp _ _ hu, fun t => ?_⟩
  rw [← hh t, oneP, Eqv.atTau_eq D X τ _ (hu t)]
  congr 1
  apply Eqv.matA_inj D X
  rw [Eqv.matA_atH]
  refine Eqv.matA_of_isAtTau D X ⟨(Eqv.mem_GinfC D X _).2 ?_, h1 t, fun ρ hρ => ?_⟩
  · ext i j
    have k1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t)) (e i) (e j) - (1 : Matrix _ _ (AE D)) (e i) (e j)) :=
      fun u hu => congrFun (congrFun (hγ.2 _ u hu) (e i)) (e j)
    have k2 := GlobalTheory.ConjInfExp.finPart_eq_one
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t)) (e i) (e j) - (1 : Matrix _ _ (AE D)) (e i) (e j) + 1)
      (by rwa [add_sub_cancel_right])
    rw [RingHom.map_add (f := _), RingHom.map_one, add_eq_right, RingHom.map_sub, sub_eq_zero] at k2
    rw [Matrix.map_apply, hm, submatrix_apply, k2]
    by_cases k : i = j
    · subst k; simp
    · simp [Matrix.one_apply_ne k, Matrix.one_apply_ne (e.injective.ne k)]
  · obtain ⟨c', -, -, hp'⟩ := exists_piInf ρ (emb _)
    have k1 : Eqv.plW D ρ ≠ Eqv.plW D τ := fun k => hρ (by rw [← Eqv.symm_plW D ρ, k, Eqv.symm_plW])
    rw [Eqv.infMat_thetaC, hm]
    ext i j
    have k2 := congrFun (congrFun (ho t _ k1) (e i)) (e j)
    rw [Matrix.map_apply] at k2
    rw [Matrix.map_apply, submatrix_apply, hp', k2]
    by_cases k : i = j
    · subst k; simp
    · simp [Matrix.one_apply_ne k, Matrix.one_apply_ne (e.injective.ne k)]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupTransposeGramRealPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieGenerator_of_oneParameterSubgroup_realPlace : ∀ (D : D7) (θ : InfFam D) (X : HSp D), IsInfFam θ → ∀ {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ)
    (emb : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w) (w : InfinitePlace D.host.F)
    (Z : Matrix (Fin d) (Fin d) ℂ) (γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J),
    γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd →
    (∀ t : ℝ, (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w)) =
      NormedSpace.exp (t • Z)) →
    (∀ (t : ℝ) (w' : InfinitePlace D.host.F), w' ≠ w →
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w')) = 1) →
    ∃ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ), Y ∈ lieAt X τ ∧
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ (oneP θ X τ Y t) := by
  first | exact @GlobalTheory.LineAtPlace.exists_oneP | exact GlobalTheory.LineAtPlace.exists_oneP | (intros; apply GlobalTheory.LineAtPlace.exists_oneP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem cartan_eq_one {k : ℕ} {A s : Matrix (Fin k) (Fin k) ℂ} (hA : A.PosDef) (h : IsCartanInv A s) : s = 1 := by
  obtain ⟨h1, -, h3⟩ := h
  have hs : ∀ v : Fin k → ℂ, (s - 1) *ᵥ v = 0 := by
    intro v
    by_contra hw
    have hsw : s *ᵥ ((s - 1) *ᵥ v) = -((s - 1) *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_sub, h1, Matrix.mul_one, ← Matrix.neg_mulVec, neg_sub]
    have p1 := h3.dotProduct_mulVec_pos hw
    have p2 := hA.dotProduct_mulVec_pos hw
    rw [← Matrix.mulVec_mulVec, hsw, Matrix.mulVec_neg, dotProduct_neg] at p1
    have := add_pos p1 p2
    rw [neg_add_cancel] at this
    exact lt_irrefl _ this
  ext i j
  have := congrFun (hs (Pi.single j 1)) i
  simpa [Matrix.sub_mulVec, sub_eq_zero, Matrix.one_apply] using this

theorem negGA_mem_GinfC (V : HSp D) {g : GA D V} (hg : g ∈ GinfC V) : negGA V g ∈ GinfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GinfC, MonoidHom.mem_ker, finHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

def sgnP : Pair T → ℚ
  | .chi _ _ => -1
  | .core _ => -1
  | _ => 1

def realChar (W : G.Weil) (p : Pair T) (e₁ e₂ : D.what₂.Tau → ℤ) (k : GA D (G.V p.small)) (k' : GA D (G.V p.big)) : ℂ :=
  ∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) (G.toPair p k k').1)).det ^ e₂ τ *
    (compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (G.toPair p k k').2)).det ^ e₁ τ

def realSubst (W : G.Weil) (B : VertexFrames G) (p : Pair T) (k : GA D (G.V p.small)) (k' : GA D (G.V p.big)) :
    PolF D (G.pT p).rank (G.pS p).rank →ₐ[ℂ] PolF D (G.pT p).rank (G.pS p).rank :=
  GlobalTheory.CompactHowe.substF
    (fun τ => ((G.onT B p τ)⁻¹ * compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (G.toPair p k k').2) * G.onT B p τ).map (opp p))
    (fun τ => ((((G.onS B p τ)⁻¹ * compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) (G.toPair p k k').1) * G.onS B p τ)⁻¹)ᵀ).map (opp p))

theorem ker_mul (W : G.Weil) (p : Pair T) (F : WO (G.pS p) (G.pT p) → ℂ) (g k : GA D (G.V p.small))
    (h k' : GA D (G.V p.big)) : W.ker p F (g * k) (h * k') = W.ker p (W.om p (G.toPair p k k') F) g h := by
  have e : G.toPair p (g * k) (h * k') = G.toPair p g h * G.toPair p k k' := by
    cases p <;> simp [GridData.toPair, map_mul, Prod.ext_iff]
  unfold GridData.Weil.ker
  rw [e]
  simp only [thetaKO, Prod.mk.eta, map_mul, Module.End.mul_apply]

theorem cart_def {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) {X : Node} (hX : DefNode D.R.m X) (τ : D.what₂.Tau) :
    W.cart X τ = 1 := by
  rcases X with ⟨i, j⟩ | i | j
  · obtain ⟨hi, rfl⟩ := hX
    exact cartan_eq_one (posDef_grid hL hi (tauE D τ)) (W.cart_is (.grid i D.R.m) (show i ≤ D.R.m ∧ D.R.m ≤ D.R.m from ⟨hi, le_rfl⟩) τ)
  · exact hX.elim
  · exact cartan_eq_one (posDef_top G hX (tauE D τ)) (W.cart_is (.top j) (show j ≤ D.R.m from hX) τ)

theorem om_fockIn {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : VertexFrames G) {p : Pair T} (hp : DefPair D.R.m p)
    (hB : ∀ X, DefNode D.R.m X → ∀ τ, (B X τ)ᴴ * gramAt D (G.V X) τ * B X τ = 1)
    (a b : D.what₂.Tau → ℚ) (ha : ∀ τ, HasInfExp D (G.chrS p) τ (a τ)) (hb : ∀ τ, HasInfExp D (G.chrT p) τ (b τ))
    (e₁ e₂ : D.what₂.Tau → ℤ) (he₁ : ∀ τ, (e₁ τ : ℚ) = a τ + sgnP p * (G.pS p).rank / 2)
    (he₂ : ∀ τ, (e₂ τ : ℚ) = -(b τ + sgnP p * (G.pT p).rank / 2))
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f)
    (hv : ∀ τ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ τ (cplxO (G.cartS W.cart p τ) (G.onT W.cart p τ)) f)
    (k : GA D (G.V p.small)) (hk : k ∈ GinfC (G.V p.small)) (k' : GA D (G.V p.big)) (hk' : k' ∈ GinfC (G.V p.big))
    (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    W.om p (G.toPair p k k') (fockIn W B p f Q) = realChar W p e₁ e₂ k k' • fockIn W B p f (realSubst W B p k k' Q) := by
  have hn := DefPair.nodes hp
  have hom := W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  cases p with
  | top t j =>
    have c1 : W.cart (.top j) = fun _ => 1 := funext (cart_def hL W hn.1)
    have c2 : W.cart (.top (j + 1)) = fun _ => 1 := funext (cart_def hL W hn.2)
    simp only [fockIn, GridData.cartS, GridData.onT, GridData.onS, c1, c2] at hv ⊢
    have := GlobalTheory.T.weil_realPoint_fockVector_positiveDefinite_det D W.ψ W.θ _ _ _ _ (W.om (.top t j)) hom W.θ_is (B (.top j)) (B (.top (j + 1))) (hB _ hn.1)
      (hB _ hn.2) a b ha hb e₁ e₂ (fun τ => by rw [he₁]; simp [sgnP]) (fun τ => by rw [he₂]; simp [sgnP]) f hf hv k hk k' hk' Q
    simp only [GridData.toPair]
    rw [this]
    rfl
  | chi i j =>
    have c1 : W.cart (.grid (i + 1) j) = fun _ => 1 := funext (cart_def hL W hn.2)
    have c2 : W.cart (.grid i j) = fun _ => 1 := funext (cart_def hL W hn.1)
    simp only [fockIn, GridData.cartS, GridData.onT, GridData.onS, c1, c2] at hv ⊢
    have := GlobalTheory.T.weilAction_negPair_pureTensor_fock D W.ψ W.θ _ _ _ _ (W.om (.chi i j)) hom W.θ_is (B (.grid (i + 1) j)) (B (.grid i j)) (hB _ hn.2)
      (hB _ hn.1) a b ha hb e₁ e₂ (fun τ => by rw [he₁]; simp [sgnP]; ring) (fun τ => by rw [he₂]; simp [sgnP]; ring) f hf hv
      _ (negGA_mem_GinfC _ hk') k hk Q
    simp only [GridData.toPair]
    rw [this]
    rfl
  | mu t i j => exact hp.elim
  | core i => exact hp.elim

theorem negGA_mem_GfC (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem onb_def {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) {X : Node} (hX : DefNode D.R.m X) (τ : D.what₂.Tau) :
    (W.onb X τ)ᴴ * gramAt D (G.V X) τ * W.onb X τ = 1 := by
  have hR : X.InRange D.R.m := by
    rcases X with ⟨i, j⟩ | i | j
    · exact show i ≤ D.R.m ∧ j ≤ D.R.m from ⟨hX.1, hX.2.le⟩
    · exact hX.elim
    · exact hX
  obtain ⟨ε, h1, h2⟩ := W.onb_is X hR τ
  rw [cart_def hL W hX, Matrix.one_mul] at h2
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  calc (W.onb X τ)ᴴ * gramAt D (G.V X) τ * W.onb X τ
      = (W.onb X τ)ᴴ * gramAt D (G.V X) τ * (W.onb X τ * Formalism.REAL.Jm ε) := by rw [← h2]
    _ = Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [← Matrix.mul_assoc, h1]
    _ = 1 := hJ

theorem ker_fockIn_real {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : VertexFrames G) {p : Pair T} (hp : DefPair D.R.m p)
    (hB : ∀ X, DefNode D.R.m X → ∀ τ, (B X τ)ᴴ * gramAt D (G.V X) τ * B X τ = 1)
    (a b : D.what₂.Tau → ℚ) (ha : ∀ τ, HasInfExp D (G.chrS p) τ (a τ)) (hb : ∀ τ, HasInfExp D (G.chrT p) τ (b τ))
    (e₁ e₂ : D.what₂.Tau → ℤ) (he₁ : ∀ τ, (e₁ τ : ℚ) = a τ + sgnP p * (G.pS p).rank / 2)
    (he₂ : ∀ τ, (e₂ τ : ℚ) = -(b τ + sgnP p * (G.pT p).rank / 2))
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f)
    (hv : ∀ τ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ τ (cplxO (G.cartS W.cart p τ) (G.onT W.cart p τ)) f)
    (k : GA D (G.V p.small)) (hk : k ∈ GinfC (G.V p.small)) (k' : GA D (G.V p.big)) (hk' : k' ∈ GinfC (G.V p.big))
    (Q : PolF D (G.pT p).rank (G.pS p).rank) (g : GA D (G.V p.small)) (h : GA D (G.V p.big)) :
    W.ker p (fockIn W B p f Q) (g * k) (h * k') =
      realChar W p e₁ e₂ k k' * W.ker p (fockIn W B p f (realSubst W B p k k' Q)) g h := by
  rw [ker_mul, om_fockIn hL W B hp hB a b ha hb e₁ e₂ he₁ he₂ f hf hv k hk k' hk' Q]
  simp only [GridData.Weil.ker, thetaKO, map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]

theorem ker_fock_moved_real {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) {U : Set T} (S : GridChoice W U) (t : T) {p : Pair T}
    (hp : DefPair D.R.m p) (d : FinDatum G t p) (hd : S.Z.HasVec d)
    (a b : D.what₂.Tau → ℚ) (ha : ∀ τ, HasInfExp D (G.chrS p) τ (a τ)) (hb : ∀ τ, HasInfExp D (G.chrT p) τ (b τ))
    (e₁ e₂ : D.what₂.Tau → ℤ) (he₁ : ∀ τ, (e₁ τ : ℚ) = a τ + sgnP p * (G.pS p).rank / 2)
    (he₂ : ∀ τ, (e₂ τ : ℚ) = -(b τ + sgnP p * (G.pT p).rank / 2))
    (k : GA D (G.V p.small)) (hk : k ∈ GinfC (G.V p.small)) (k' : GA D (G.V p.big)) (hk' : k' ∈ GinfC (G.V p.big))
    (Q : PolF D (G.pT p).rank (G.pS p).rank) (g : GA D (G.V p.small)) (h : GA D (G.V p.big)) :
    W.ker p (W.fock p (GlobalTheory.RowClaim.movedVec t S d) Q) (g * k) (h * k') =
      realChar W p e₁ e₂ k k' * W.ker p (W.fock p (GlobalTheory.RowClaim.movedVec t S d) (realSubst W W.onb p k k' Q)) g h := by
  have hn := DefPair.nodes hp
  have hom := W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  obtain ⟨h1, h2⟩ := GlobalTheory.T.gridFiniteDatumVector_theta_fockVacuum W S.Z hp d hd
  have mem : (G.toPair p (S.N.u p.small).1 (S.N.u p.big).1).1 ∈ GfC (G.pS p) ∧
      (G.toPair p (S.N.u p.small).1 (S.N.u p.big).1).2 ∈ GfC (G.pT p) := by
    cases p with
    | chi i j => exact ⟨negGA_mem_GfC _ (S.N.u _).2, (S.N.u _).2⟩
    | mu t i j => exact ⟨(S.N.u _).2, (S.N.u _).2⟩
    | core i => exact ⟨negGA_mem_GfC _ (S.N.u _).2, (S.N.u _).2⟩
    | top t j => exact ⟨(S.N.u _).2, (S.N.u _).2⟩
  obtain ⟨h3, h4⟩ := GlobalTheory.T.weil_finitePoint_preserves_fockVacuum D W.ψ W.θ _ _ _ _ (W.om p) hom W.θ_is _ _ _ h1 h2 _ mem.1 _ mem.2
  exact ker_fockIn_real hL W W.onb hp (fun X hX τ => onb_def hL W hX τ) a b ha hb e₁ e₂ he₁ he₂ _ h3 h4 k hk k' hk' Q g h

end GlobalTheory.FockReal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenPtSSubset
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (At)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SmallDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}


variable (G i j) in
abbrev PtS : Type := Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)


variable (G i j) in
abbrev IxS : Type := Fin (spW₁ G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank)


variable (G) in
abbrev HomA (t : T) (i j : ℕ) : Type := WO (G.pS (.mu t i j)) (G.pT (.mu t i j))


variable (G i j) in
abbrev HomB : Type := WO (G.pS (.chi i j)) (G.pT (.chi i j))

abbrev mapA (t : T) (e : Num G i j) (u : PtS G i j) : HomA G t i j := mulG (spW₁ G i j) (colV e u)ᵀ

abbrev mapB (e : Num G i j) (u : PtS G i j) : HomB G i j := adjV₁ e u

def ofMaps (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) : PtS G i j :=
  (fromCols (GlobalTheory.BigDat.divG (spW₁ G i j) x.1)ᵀ ((GlobalTheory.BigDat.divG (spV₁ G i j) (-x.2)).map (cA D))).submatrix id e.symm

theorem mapA_ofMaps (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) : mapA t e (ofMaps t e x) = x.1 := by
  have h1 : (colV e (ofMaps t e x))ᵀ = GlobalTheory.BigDat.divG (spW₁ G i j) x.1 := Matrix.ext fun a b => by
    simp only [colV, ofMaps, transpose_apply, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl]
  exact (congrArg (mulG (spW₁ G i j)) h1).trans (GlobalTheory.BigDat.mulG_divG _ _)

theorem mapB_ofMaps (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) : mapB e (ofMaps t e x) = x.2 := by
  have h2 : ((ofMaps t e x).submatrix id fun k => e (.inr k)).map (cA D) = GlobalTheory.BigDat.divG (spV₁ G i j) (-x.2) :=
    Matrix.ext fun a b => by
      simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply,
        GlobalTheory.DualPairCheck.cA_cA]
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h2).trans ((congrArg Neg.neg (GlobalTheory.BigDat.mulG_divG _ _)).trans (neg_neg _))

theorem ofMaps_maps (t : T) (e : Num G i j) (u : PtS G i j) : ofMaps t e (mapA t e u, mapB e u) = u := by
  have h1 : GlobalTheory.BigDat.divG (spW₁ G i j) (mapA t e u) = (colV e u)ᵀ := GlobalTheory.BigDat.divG_mulG _ _
  have h2 : GlobalTheory.BigDat.divG (spV₁ G i j) (-mapB e u) = (u.submatrix id fun k => e (.inr k)).map (cA D) :=
    (congrArg (GlobalTheory.BigDat.divG (spV₁ G i j)) (neg_neg _)).trans (GlobalTheory.BigDat.divG_mulG _ _)
  ext a b
  obtain ⟨k | k, rfl⟩ := e.surjective b
  · simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, transpose_apply]
    exact congrFun (congrFun h1 k) a
  · simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply]
    exact (congrArg (cA D) (congrFun (congrFun h2 a) k)).trans (GlobalTheory.DualPairCheck.cA_cA _)

theorem mapA_add (t : T) (e : Num G i j) (u u' : PtS G i j) : mapA t e (u + u') = mapA t e u + mapA t e u' :=
  GlobalTheory.RouteCoords.mulG_colV_add e u u'

theorem mapB_add (e : Num G i j) (u u' : PtS G i j) : mapB e (u + u') = mapB e u + mapB e u' :=
  GlobalTheory.RouteCoords.adjV₁_add e u u'

theorem mapA_smul (t : T) (e : Num G i j) (c : AF D.host.F) (u : PtS G i j) : mapA t e (c • u) = c • mapA t e u :=
  GlobalTheory.BigDat.mulG_smul (spW₁ G i j) c (colV e u)ᵀ

theorem mapB_smul (e : Num G i j) (c : AF D.host.F) (u : PtS G i j) : mapB e (c • u) = c • mapB e u := by
  have h : ((c • u).submatrix id fun k => e (.inr k)).map (cA D) = c • (u.submatrix id fun k => e (.inr k)).map (cA D) :=
    Matrix.ext fun a b => map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) c _
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h).trans
    ((congrArg Neg.neg (GlobalTheory.BigDat.mulG_smul _ _ _)).trans (smul_neg _ _).symm)

def maps (t : T) (e : Num G i j) : PtS G i j ≃ₗ[AF D.host.F] HomA G t i j × HomB G i j where
  toFun u := (mapA t e u, mapB e u)
  invFun := ofMaps t e
  map_add' u u' := Prod.ext (mapA_add t e u u') (mapB_add e u u')
  map_smul' c u := Prod.ext (mapA_smul t e c u) (mapB_smul e c u)
  left_inv := ofMaps_maps t e
  right_inv x := Prod.ext (mapA_ofMaps t e x) (mapB_ofMaps t e x)

theorem maps_apply (t : T) (e : Num G i j) (u : PtS G i j) : maps t e u = (mapA t e u, mapB e u) := rfl

abbrev sympS (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (u u' : PtS G i j) : AF D.host.F :=
  symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u'

theorem sympS_eq (t : T) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (hW₁ : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram) (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e)
    (x x' : PtS G i j) :
    sympS Γ x x' = symplO _ _ (mapA t e x) (mapA t e x') + symplO _ _ (mapB e x) (mapB e x') :=
  GlobalTheory.RouteCoords.symp_eq t e Γ hW₁ hWW x x'

def boxS (t : T) (e : Num G i j) (f₁ : HomA G t i j → ℂ) (f₂ : HomB G i j → ℂ) (u : PtS G i j) : ℂ :=
  f₁ (mapA t e u) * f₂ (mapB e u)

def heisS (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (u₀ : PtS G i j) (f : PtS G i j → ℂ)
    (u : PtS G i j) : ℂ :=
  ψ (⅟(2 : AF D.host.F) * sympS Γ u u₀) * f (u + u₀)

theorem heisS_box (t : T) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (hW₁ : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram) (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e)
    (ψ : AddChar (AF D.host.F) ℂ) (u₀ : PtS G i j) (f₁ : HomA G t i j → ℂ) (f₂ : HomB G i j → ℂ) :
    heisS Γ ψ u₀ (boxS t e f₁ f₂) = boxS t e (heisO ψ _ _ (mapA t e u₀) f₁) (heisO ψ _ _ (mapB e u₀) f₂) := by
  funext u
  unfold heisS boxS heisO symplOH
  rw [sympS_eq t e Γ hW₁ hWW, mul_add, AddChar.map_add_eq_mul, mapA_add, mapB_add, GlobalTheory.BigDat.invOf_two]
  ring

abbrev thetaS (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (IxS G i j → AF D.host.F) → ℂ)
    (u : PtS G i j) : ℂ := thetaSum D.host.F (Γ.M'.co.rho ψ u Φ)

theorem thetaS_rho (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (IxS G i j → AF D.host.F) → ℂ)
    (u₀ : PtS G i j) : thetaS Γ ψ (Γ.M'.co.rho ψ u₀ Φ) = heisS Γ ψ u₀ (thetaS Γ ψ Φ) :=
  funext fun u => (congrArg (thetaSum D.host.F) (GlobalTheory.BigDat.rho_rho Γ.M'.co ψ u u₀ Φ)).trans tsum_mul_left

theorem thetaS_smul (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (c : ℂ)
    (Φ : (IxS G i j → AF D.host.F) → ℂ) (u : PtS G i j) : thetaS Γ ψ (c • Φ) u = c * thetaS Γ ψ Φ u :=
  (tsum_congr fun _ => mul_left_comm _ _ _).trans tsum_mul_left


variable (G) in
abbrev latA (t : T) (i j : ℕ) : AddSubgroup (HomA G t i j) :=
  latO (G.pS (.mu t i j)) (G.pT (.mu t i j)) (G.latS (.mu t i j) : Set _) (G.latT (.mu t i j) : Set _) fun _ => True


variable (G i j) in
abbrev latB : AddSubgroup (HomB G i j) :=
  latO (G.pS (.chi i j)) (G.pT (.chi i j)) (G.latS (.chi i j) : Set _) (G.latT (.chi i j) : Set _) fun _ => True

def latPtS (t : T) (e : Num G i j) (v : Pl D.host.F) : AddSubgroup (PtS G i j) where
  carrier := {u | At (evFin D.host.F v) u ∧ mapA t e u ∈ latA G t i j ∧ mapB e u ∈ latB G i j}
  zero_mem' := ⟨fun u _ => smul_zero u, by
    rw [show mapA t e 0 = 0 from congrArg Prod.fst (map_zero (maps t e))]; exact zero_mem _, by
    rw [show mapB e 0 = 0 from congrArg Prod.snd (map_zero (maps t e))]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨fun u hu => by rw [smul_add, ha.1 u hu, hb.1 u hu, add_zero],
    by rw [mapA_add]; exact add_mem ha.2.1 hb.2.1, by rw [mapB_add]; exact add_mem ha.2.2 hb.2.2⟩
  neg_mem' := fun {a} ha => ⟨fun u hu => by rw [smul_neg, ha.1 u hu, neg_zero], by
    rw [show mapA t e (-a) = -mapA t e a from congrArg Prod.fst (map_neg (maps t e) a)]; exact neg_mem ha.2.1, by
    rw [show mapB e (-a) = -mapB e a from congrArg Prod.snd (map_neg (maps t e) a)]; exact neg_mem ha.2.2⟩

def genPtS (t : T) (e : Num G i j) (v : Pl D.host.F) : Set (PtS G i j) :=
  {γ | (∃ γ' ∈ latPtS t e v, γ = 2 • γ') ∨ γ ∈ latPtS t e v ∧ ∃ ε, IsSplitIdem D ε ∧ γ ∈ GlobalTheory.FlipMatch.mixHalfS e ε}

theorem genPtS_subset (t : T) (e : Num G i j) (v : Pl D.host.F) : genPtS t e v ⊆ latPtS t e v := by
  rintro _ (⟨γ, h, rfl⟩ | h)
  exacts [nsmul_mem h 2, h.1]

end GlobalTheory.SmallDat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianCompactActionEigen
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped Matrix

namespace GlobalTheory.FockVacStab

theorem mat_mul_mat_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} (k : UA σ X.J) : mat k * mat k⁻¹ = 1 ∧ mat k⁻¹ * mat k = 1 := by
  constructor
  · show (k * k⁻¹).1.1 = 1
    simp
  · show (k⁻¹ * k).1.1 = 1
    simp

end GlobalTheory.FockVacStab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainUpwardLiftHeckeParamTransferred
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainUpwardLiftHeckeParamTransferred
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto

theorem PiLocalization₂.val_autCusp {D : D7} (c : Com D) (s : PiLocalization₂ D) (u : s.CC c) (x : SmT s.M) :
    IsAutFunSm c.θ s.V (PiLocalization₂.val u x) ∧ IsCuspFun s.V (PiLocalization₂.val u x) := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff D c.θ s.V _ s.M _ _ _).1 ((mem_multT _ _ _ _ _).1 u.2)
  have key : ∀ y : SmT s.M, PiLocalization₂.val u y =
      (PiTensorProduct.lift (PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))) y := by
    intro y; rw [LinearEquiv.apply_symm_apply]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [key, map_smul, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul r (hT.aut f), GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp f)⟩
  | add x y hx hy =>
    have e : PiLocalization₂.val u (x + y) = PiLocalization₂.val u x + PiLocalization₂.val u y := map_add _ _ _
    rw [e]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hx.1 hy.1,
      GlobalTheory.MultMem.isCuspFun_add hx.1.toIsAutFun hy.1.toIsAutFun hx.2 hy.2⟩

theorem upPar_of_transfer : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ D : D7, UpPar D := by
  intro hRD hHowe D c hc k hk s s' hs hs' p hp u B φ hu v _ hne
  set y := PiLocalization₂.val u v with hy
  have hy0 : y ≠ 0 := by
    intro h; apply hne; funext x; simp [Step.up, h]
  have hyB : GlobalTheory.LFun.IsParamFunV s.V c.S (fun g => conj (y g)) B := hu.2 v hy0
  have hconj : (fun x => conj (p.up φ y x)) =
      fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν := by
    funext x; simp only [Step.up]; rw [← integral_conj]; congr 1; funext g; simp [map_mul]
  have hne' : (fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν) ≠ 0 := by
    rw [← hconj]; intro h; apply hne; funext x; simpa using congrFun h x
  have hrank : s'.V.rank = s.V.rank + c.t := by rw [hs'.rank, hs.rank]; ring
  have hYA := PiLocalization₂.val_autCusp c s u v
  have hunr : ∀ w0 ∉ c.S, ∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w0 →
      GlobalTheory.LFun.UnrAt (c.χ k) w' ∧ GlobalTheory.LFun.UnrAt (c.χ k) w' := by
    intro w0 hw0 w' hw'
    have h1 := hc.unr k hk w' (by simpa [GlobalTheory.LFun.above, hw'] using hw0)
    exact ⟨h1, h1⟩
  unfold ParFun
  rw [hconj]
  intro w0 hw0 w h
  have hw0' : w0 ∉ c.S := by simpa using hw0
  exact GlobalTheory.T.thetaIntegral_conjCuspForm_parameterTransfer hRD D (GlobalTheory.T.sphericalParameterTransfer_all_finitePlaces hHowe D) c.ψ c.θ s.V s'.V _ _ p.ω hc.inf hp.pre.weil c.t hrank s.ν s.fd
    hs.haar hs.fund w0 (hunr w0 hw0') w h (p.pt φ)
    ((GlobalTheory.T.evenThetaChainStep_fockVectors_spherical_latticeVacua D c hc k hk s s' hs hs' p hp φ).2.2.2 w0 hw0') y (B w) hYA.1 hYA.2 (hyB w0 hw0 w h) hne'

end GlobalTheory.EvenOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainUpwardLiftHeckeParamTransferredStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenThetaChainUpwardLift_heckeParam_transferred : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ D : D7, UpPar D := by
  first | exact @GlobalTheory.EvenOnto.upPar_of_transfer | exact GlobalTheory.EvenOnto.upPar_of_transfer | (intros; apply GlobalTheory.EvenOnto.upPar_of_transfer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsArchimedeanIdentity
noncomputable section

namespace GlobalTheory.KStableLie

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_of_isExp {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (hU : IsExp L U)
    (N : Submodule ℂ V) (hL : ∀ y ∈ N, L y ∈ N) {v : V} (hv : v ∈ N) : U v ∈ N := by
  have hpow : ∀ m : ℕ, (L ^ m) v ∈ N := by
    intro m
    induction m with
    | zero => simpa using hv
    | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact hL _ ih
  by_contra hn
  obtain ⟨l, hl, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hz : ∀ y ∈ N, l y = 0 := fun y hy => by
    have h' := Submodule.mem_map_of_mem (f := l) hy
    rw [hmap, Submodule.mem_bot] at h'
    exact h'
  have h0 : (fun m : ℕ => ((m.factorial : ℂ))⁻¹ * l ((L ^ m) v)) = fun _ => 0 := by
    funext m; rw [hz _ (hpow m), mul_zero]
  have hs := hU v l
  rw [h0] at hs
  exact hl (hs.unique hasSum_zero)


end GlobalTheory.KStableLie

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchDer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.LieEq

theorem exists_op {S S' Pi : Type} [AddCommGroup S] [Module ℂ S] [AddCommGroup S'] [Module ℂ S'] [AddCommGroup Pi] [Module ℂ Pi]
    (N : Submodule ℂ S) (N' : Submodule ℂ S') (p : S →ₗ[ℂ] Pi) (p' : S' →ₗ[ℂ] Pi) (δ : S →ₗ[ℂ] S) (δ' : S' →ₗ[ℂ] S')
    (h : ∀ f ∈ N, ∀ f' ∈ N', p f = p' f' → p (δ f) = p' (δ' f')) :
    ∃ A : Pi →ₗ[ℂ] Pi, (∀ f ∈ N, A (p f) = p (δ f)) ∧ ∀ f' ∈ N', A (p' f') = p' (δ' f') := by
  let L : (N × N') →ₗ[ℂ] Pi := p ∘ₗ N.subtype ∘ₗ LinearMap.fst ℂ N N' + p' ∘ₗ N'.subtype ∘ₗ LinearMap.snd ℂ N N'
  let L₁ : (N × N') →ₗ[ℂ] Pi := p ∘ₗ δ ∘ₗ N.subtype ∘ₗ LinearMap.fst ℂ N N' + p' ∘ₗ δ' ∘ₗ N'.subtype ∘ₗ LinearMap.snd ℂ N N'
  have hk : LinearMap.ker L ≤ LinearMap.ker L₁ := by
    intro x hx
    simp only [LinearMap.mem_ker, L, L₁, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, Submodule.coe_subtype] at hx ⊢
    have e : p (x.1 : S) = p' (-(x.2 : S')) := by rw [map_neg]; exact eq_neg_of_add_eq_zero_left hx
    have := h _ x.1.2 _ (N'.neg_mem x.2.2) e
    rw [this, map_neg, map_neg, neg_add_cancel]
  let A₀ : LinearMap.range L →ₗ[ℂ] Pi := (LinearMap.ker L).liftQ L₁ hk ∘ₗ L.quotKerEquivRange.symm.toLinearMap
  have hA₀ : ∀ x, A₀ ⟨L x, LinearMap.mem_range_self L x⟩ = L₁ x := by
    intro x
    simp only [A₀, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  obtain ⟨A, hA⟩ := LinearMap.exists_extend A₀
  have hA' : ∀ x, A (L x) = L₁ x := fun x => by
    rw [← hA₀ x, ← hA]; rfl
  refine ⟨A, fun f hf => ?_, fun f' hf' => ?_⟩
  · have := hA' (⟨f, hf⟩, 0)
    simpa [L, L₁] using this
  · have := hA' (0, ⟨f', hf'⟩)
    simpa [L, L₁] using this

end GlobalTheory.SquareAgree.LieEq

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedKernelOfVectorAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedKernelOfVectorAdd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

open MvPolynomial

private theorem jetLin_add_tab {K : Type} [Field K] {ι : Type} {a b : ℕ} (J J' : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → K) :
    Formalism.L2.Ker.jetLin (J + J') = Formalism.L2.Ker.jetLin J + Formalism.L2.Ker.jetLin J' := by
  refine (basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) K).ext fun m => ?_
  simp only [Formalism.L2.Ker.jetLin, LinearMap.add_apply, Module.Basis.constr_basis, Pi.add_apply, map_add (f := _)]

theorem kkVec_add : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (p : Pair T) {f f' : WO (G.pS p) (G.pT p) → ℂ},
    IsThetaFunO W.ψ _ _ f → IsThetaFunO W.ψ _ _ f' → ∀ (x : FinPt G p.small) (y : FinPt G p.big),
    kkVec S p (f + f') x y = kkVec S p f x y + kkVec S p f' x y := by
  intro D T L sc G W U S p f f' hf hf' x y
  have hJ : ∀ x' y', GlobalTheory.FunObj.jetTab W S.N.frC p (f + f') x' y' =
      GlobalTheory.FunObj.jetTab W S.N.frC p f x' y' + GlobalTheory.FunObj.jetTab W S.N.frC p f' x' y' := by
    intro x' y'
    funext k
    simp only [GlobalTheory.FunObj.jetTab, GlobalTheory.FunObj.kerFin, GlobalTheory.FunObj.fockIn, Pi.add_apply]
    rw [GlobalTheory.SpecFac.pureTensorO_add W.ψ_std W.θ_is _ _ _ _ hf hf']
    simp only [GlobalTheory.ChiGrid.GridData.Weil.ker, thetaKO, map_add (f := _), Pi.add_apply]
  unfold kkVec GlobalTheory.FunObj.fockComp
  rw [hJ, ← smul_add]
  congr 1
  ext1 F
  simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, jetLin_add_tab, LinearMap.comp_apply, LinearMap.add_apply, map_add (f := _)]

end GlobalTheory.TopZeroInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedKernelOfVectorAddStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedKernelOfVector_add : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (p : Pair T) {f f' : WO (G.pS p) (G.pT p) → ℂ},
    IsThetaFunO W.ψ _ _ f → IsThetaFunO W.ψ _ _ f' → ∀ (x : FinPt G p.small) (y : FinPt G p.big),
    kkVec S p (f + f') x y = kkVec S p f x y + kkVec S p f' x y := by
  first | exact @GlobalTheory.TopZeroInv.kkVec_add | exact GlobalTheory.TopZeroInv.kkVec_add | (intros; apply GlobalTheory.TopZeroInv.kkVec_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKSubmoduleInfimumAndIrreducibleSupremum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.CuspGK

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

theorem isGKSub_sInf (s : Set (Submodule ℂ (GA D V → ℂ))) (h : ∀ A ∈ s, IsGKSub θ M A) : IsGKSub θ M (sInf s) := by
  constructor
  · intro τ g hg f hf
    exact Submodule.mem_sInf.2 fun A hA => (h A hA).k τ g hg f (Submodule.mem_sInf.1 hf A hA)
  · intro τ X hX f hf
    exact Submodule.mem_sInf.2 fun A hA => (h A hA).lie τ X hX f (Submodule.mem_sInf.1 hf A hA)


open scoped Matrix in
variable {M} in
theorem InK.inv {τ : D.what₂.Tau} {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (h : InK M τ g) : InK M τ g⁻¹ := by
  obtain ⟨hU, hk⟩ := h
  have hfd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  set k := M.fr τ * g * (M.fr τ)⁻¹ with hkdef
  have hku : k ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := hk.1
  have hsk : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hku
  have hks : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hku
  have hkdet : IsUnit k.det := (Matrix.isUnit_iff_isUnit_det _).1 ⟨⟨k, star k, hks, hsk⟩, rfl⟩
  have hdet : k.det = g.det := by
    rw [hkdef, Matrix.det_mul, Matrix.det_mul, mul_comm (M.fr τ).det, mul_assoc, ← Matrix.det_mul,
      Matrix.mul_nonsing_inv _ hfd, Matrix.det_one, mul_one]
  have hgd : IsUnit g.det := hdet ▸ hkdet
  have hg1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgd
  have hU' : gᴴ * gramAt D V τ * g = gramAt D V τ := hU
  refine ⟨?_, ?_⟩
  · show (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = gramAt D V τ
    calc (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * gramAt D V τ * g) * g⁻¹ := by rw [hU']
      _ = (g * g⁻¹)ᴴ * gramAt D V τ * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [hg1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · have e1 : M.fr τ * g⁻¹ * (M.fr τ)⁻¹ = k⁻¹ := by
      rw [hkdef, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hfd]
      simp only [Matrix.mul_assoc]
    have hinv : k⁻¹ = star k := Matrix.inv_eq_left_inv hsk
    rw [e1, hinv]
    refine ⟨Matrix.mem_unitaryGroup_iff.2 (by rw [star_star]; exact hsk), ?_⟩
    have hJ : star (Formalism.REAL.Jm (M.ε τ)) = Formalism.REAL.Jm (M.ε τ) := Formalism.REAL.Jm_conjTranspose _
    have hcomm : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ, m * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * m →
        star m * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * star m := fun m hm => by
      have h2 : star (m * Formalism.REAL.Jm (M.ε τ)) = star (Formalism.REAL.Jm (M.ε τ) * m) := congrArg star hm
      rw [star_mul, star_mul, hJ] at h2
      exact h2.symm
    exact hcomm k hk.2

end GlobalTheory.CuspGK

end
end
