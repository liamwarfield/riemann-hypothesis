module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisDualPointsOfTangentModuleBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalSumEmbeddingLeMul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalSumEmbeddingLeMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace CompanionTheory.Member.BlockMatrixNorms

theorem sq_le {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (x : n → ℂ) :
    ∑ i, ‖(M *ᵥ x) i‖ ^ 2 ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M‖ ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
  have h := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M).le_opNorm (WithLp.toLp 2 x)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  exact h2

theorem opNorm_blk {m n ι : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    (e : m ⊕ n ≃ ι) (x : Matrix m m ℂ) (y : Matrix n n ℂ) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (GlobalTheory.Doubling.blkMat e x y)‖₊ ≤
      max ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) x‖₊ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y‖₊ := by
  rw [← NNReal.coe_le_coe, NNReal.coe_max, coe_nnnorm, coe_nnnorm, coe_nnnorm]
  set a := ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) x‖ with ha
  set b := ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y‖ with hb
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hm : 0 ≤ max a b := le_max_of_le_left ha0
  refine ContinuousLinearMap.opNorm_le_bound _ hm fun w => ?_
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hm (norm_nonneg _)) two_ne_zero).1 ?_
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have h1 := sq_le x (fun i => w.ofLp (e (.inl i)))
  have h2 := sq_le y (fun i => w.ofLp (e (.inr i)))
  have e1 : ∀ i, (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (GlobalTheory.Doubling.blkMat e x y) w).ofLp (e (.inl i)) =
      (x *ᵥ fun i => w.ofLp (e (.inl i))) i := by
    intro i
    show (GlobalTheory.Doubling.blkMat e x y *ᵥ w.ofLp) (e (.inl i)) = _
    simp [Matrix.mulVec, dotProduct, ← e.sum_comp, GlobalTheory.Doubling.blkMat]
  have e2 : ∀ i, (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (GlobalTheory.Doubling.blkMat e x y) w).ofLp (e (.inr i)) =
      (y *ᵥ fun i => w.ofLp (e (.inr i))) i := by
    intro i
    show (GlobalTheory.Doubling.blkMat e x y *ᵥ w.ofLp) (e (.inr i)) = _
    simp [Matrix.mulVec, dotProduct, ← e.sum_comp, GlobalTheory.Doubling.blkMat]
  rw [← e.sum_comp, ← e.sum_comp (fun i => ‖w.ofLp i‖ ^ 2), Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [e1, e2]
  have s1 : 0 ≤ ∑ i, ‖w.ofLp (e (.inl i))‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have s2 : 0 ≤ ∑ i, ‖w.ofLp (e (.inr i))‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have p1 : a ^ 2 ≤ (max a b) ^ 2 := pow_le_pow_left₀ ha0 (le_max_left _ _) 2
  have p2 : b ^ 2 ≤ (max a b) ^ 2 := pow_le_pow_left₀ hb0 (le_max_right _ _) 2
  rw [mul_add]
  exact add_le_add (h1.trans (mul_le_mul_of_nonneg_right p1 s1)) (h2.trans (mul_le_mul_of_nonneg_right p2 s2))

theorem key {c c' a a' b b' : NNReal} (h : c ≤ max a b) (h' : c' ≤ max a' b') :
    max 1 (max c c') ≤ max 1 (max a a') * max 1 (max b b') := by
  have hA : 1 ≤ max 1 (max a a') := le_max_left _ _
  have hB : 1 ≤ max 1 (max b b') := le_max_left _ _
  have l1 : max 1 (max a a') ≤ max 1 (max a a') * max 1 (max b b') := le_mul_of_one_le_right' hB
  have l2 : max 1 (max b b') ≤ max 1 (max a a') * max 1 (max b b') := le_mul_of_one_le_left' hA
  refine max_le (hA.trans l1) (max_le (h.trans (max_le ?_ ?_)) (h'.trans (max_le ?_ ?_)))
  · exact (le_max_of_le_right (le_max_left _ _)).trans l1
  · exact (le_max_of_le_right (le_max_left _ _)).trans l2
  · exact (le_max_of_le_right (le_max_right _ _)).trans l1
  · exact (le_max_of_le_right (le_max_right _ _)).trans l2

theorem sup_blk {A m n ι κ : Type} [CommRing A] [Fintype m] [Fintype n] [Fintype ι] [Fintype κ]
    (e : m ⊕ n ≃ ι) (φ : A → κ → NNReal) (hφ : ∀ k, φ 0 k = 0) (x : Matrix m m A) (y : Matrix n n A) :
    (Finset.univ.sup fun p : ι × ι × κ => φ (GlobalTheory.Doubling.blkMat e x y p.1 p.2.1) p.2.2) ≤
      max (Finset.univ.sup fun p : m × m × κ => φ (x p.1 p.2.1) p.2.2)
        (Finset.univ.sup fun p : n × n × κ => φ (y p.1 p.2.1) p.2.2) := by
  refine Finset.sup_le ?_
  rintro ⟨i, j, k⟩ -
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  simp only [GlobalTheory.Doubling.blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · exact le_max_of_le_left (Finset.le_sup (f := fun p : m × m × κ => φ (x p.1 p.2.1) p.2.2) (Finset.mem_univ (i, j, k)))
  · simp [hφ]
  · simp [hφ]
  · exact le_max_of_le_right (Finset.le_sup (f := fun p : n × n × κ => φ (y p.1 p.2.1) p.2.2) (Finset.mem_univ (i, j, k)))

variable {D : D7}

theorem finMat_blk (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁) :
    finMat D.sp.cm.sig (hsum V V₁).gram (blk V V₁ (g, g₁)) =
      GlobalTheory.Doubling.blkMat finSumFinEquiv (finMat D.sp.cm.sig V.gram g) (finMat D.sp.cm.sig V₁.gram g₁) :=
  blkMat_map finSumFinEquiv _ (map_zero _) (Formalism.L2.Theta.mt V g) (Formalism.L2.Theta.mt V₁ g₁)

theorem infMat_blk (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁) :
    infMat D.sp.cm.sig (hsum V V₁).gram θ (blk V V₁ (g, g₁)) =
      GlobalTheory.Doubling.blkMat finSumFinEquiv (infMat D.sp.cm.sig V.gram θ g) (infMat D.sp.cm.sig V₁.gram θ g₁) := by
  have h := blkMat_map finSumFinEquiv
    (fun z => θ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z)) (by simp only [map_zero])
    (Formalism.L2.Theta.mt V g) (Formalism.L2.Theta.mt V₁ g₁)
  exact h

theorem infNorm_blk (θ : InfFam D) (V V₁ : HSp D) (τ : D.what₂.Tau) (g : GA D V) (g₁ : GA D V₁) :
    GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ (hsum V V₁) τ (blk V V₁ (g, g₁)) ≤
      max (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ V τ g) (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ V₁ τ g₁) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm
  rw [infMat_blk]
  exact opNorm_blk _ _ _

theorem finNorm_blk (V V₁ : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V) (g₁ : GA D V₁) :
    GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm (hsum V V₁) v (blk V V₁ (g, g₁)) ≤
      max (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm V v g) (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm V₁ v g₁) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm
  rw [finMat_blk]
  refine sup_blk finSumFinEquiv (fun z k => ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D z k)‖₊) (fun k => ?_) _ _
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D 0 k = 0 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord
    rw [map_zero]; rfl
  show ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D 0 k)‖₊ = 0
  rw [hz, map_zero, nnnorm_zero]

theorem blk_inv (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁) :
    (blk V V₁ (g, g₁))⁻¹ = blk V V₁ (g⁻¹, g₁⁻¹) := (map_inv (blk V V₁) (g, g₁)).symm

end CompanionTheory.Member.BlockMatrixNorms

theorem CompanionTheory.Member.unitaryAdelicHeight_blockDiagonal_le_mul : ∀ (D : D7) (θ : InfFam D) (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁), GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ (hsum V V₁) (blk V V₁ (g, g₁)) ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V₁ g₁ := by
  intro D θ V V₁ g g₁
  have f0 := GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite (hsum V V₁) (blk V V₁ (g, g₁))
  have f1 := GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite V g
  have f2 := GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite V₁ g₁
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← finprod_mul_distrib f1 f2]
  refine mul_le_mul' (Finset.prod_le_prod' fun τ _ => ?_) ?_
  · unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt
    rw [CompanionTheory.Member.BlockMatrixNorms.blk_inv]
    exact CompanionTheory.Member.BlockMatrixNorms.key (CompanionTheory.Member.BlockMatrixNorms.infNorm_blk _ _ _ _ _ _)
      (CompanionTheory.Member.BlockMatrixNorms.infNorm_blk _ _ _ _ _ _)
  · refine finprod_le_finprod' f0 ((f1.union f2).subset (Function.mulSupport_mul _ _)) fun v => ?_
    show GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt _ _ _ ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt _ _ _ * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt _ _ _
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt
    rw [CompanionTheory.Member.BlockMatrixNorms.blk_inv]
    exact CompanionTheory.Member.BlockMatrixNorms.key (CompanionTheory.Member.BlockMatrixNorms.finNorm_blk _ _ _ _ _)
      (CompanionTheory.Member.BlockMatrixNorms.finNorm_blk _ _ _ _ _)

end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.Adopt.unitaryAdelicHeight_orthogonalSum_embedding_le_mul : ∀ (D : D7) (θ : InfFam D) (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁), GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ (hsum V V₁) (blk V V₁ (g, g₁)) ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V₁ g₁ := by
  first | exact @CompanionTheory.Member.unitaryAdelicHeight_blockDiagonal_le_mul | exact CompanionTheory.Member.unitaryAdelicHeight_blockDiagonal_le_mul | (intros; apply CompanionTheory.Member.unitaryAdelicHeight_blockDiagonal_le_mul <;> assumption)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalSumEmbeddingLeMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicHeight_orthogonalSum_embedding_le_mul : ∀ (D : D7) (θ : InfFam D) (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁), GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ (hsum V V₁) (blk V V₁ (g, g₁)) ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V₁ g₁ := by
  first | exact @GlobalTheory.Adopt.unitaryAdelicHeight_orthogonalSum_embedding_le_mul | exact GlobalTheory.Adopt.unitaryAdelicHeight_orthogonalSum_embedding_le_mul | (intros; apply GlobalTheory.Adopt.unitaryAdelicHeight_orthogonalSum_embedding_le_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTranslatesConvergentLiftDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationCombIntegrableThetaKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationCombIntegrableThetaKernel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ZConv

theorem zconv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∃ z : GA D (G.V (.grid i j)) →₀ ℂ, zdeg z ≠ 0 ∧
    (∀ g, IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd (.grid i j)) (M.ν (.grid i j))) ∧
    Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) => F p.1 * translates z (kerSmall W Θ' p.1 g₁) p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid i j)).restrict (M.fd (.grid i j)))) := by
  intro D T L sc G hK hP μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hB g₁
  obtain ⟨e, Bs, Γ, X, om, om', h, hTr, hv⟩ := hT M hM
  obtain ⟨z, Φ, a, C₀, hz, hΦ, hid⟩ := GlobalTheory.T.translatedKernel_le_thetaFunction_routeBigVertex hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  have dec := (hK.1 D.host.F D.host.E D.sp.cm.sig Bs _ _ Γ X om om' hTr).1
  obtain ⟨C, k, hC⟩ := (dec.2 Φ hΦ).1 0
  have hbd : ∀ g u, ‖translates z (kerSmall W Θ' g g₁) u‖ ≤
      |C₀| * |C| * (2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁) ^ k := by
    intro g u
    obtain ⟨γ, hγ, hle⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight _ g
    have e1 : translates z (kerSmall W Θ' g g₁) u = translates z (kerSmall W Θ' (γ * g) g₁) u := by
      simp only [translates, GlobalTheory.T.smallRouteKernel_left_invariant_rationalUnitary hL W B ρ t i j Θ Θ' hΘ g₁ γ hγ]
    rw [e1]
    have h1 := hC (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))
    rw [pow_zero, mul_one] at h1
    have h2 := GlobalTheory.T.unitaryAdelicHeight_blockDiagonalEmbedding_le_mul _ _ e h.JWW (γ * g) g₁
    have h3 : (0 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) := NNReal.coe_nonneg _
    have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ≤
        2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁ :=
      h2.trans (mul_le_mul_of_nonneg_right hle (GlobalTheory.Grow.height_pos _ _).le)
    calc _ ≤ C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ := hid _ _
      _ ≤ |C₀| * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self C₀) (norm_nonneg _)
      _ ≤ |C₀| * (|C| * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h3 k)))
            (abs_nonneg C₀)
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h4 k) (mul_nonneg (abs_nonneg C₀) (abs_nonneg C))

  have hWl := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  have hVl := (hM.vtx (.grid i (j + 1)) ⟨i.2.le, j.2⟩).haar_fund
  haveI : IsFiniteMeasure ((M.ν (.grid i j)).restrict (M.fd (.grid i j))) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hWl.1 hWl.2).ne
  haveI : IsFiniteMeasure ((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hVl.1 hVl.2).ne
  have hcont := GlobalTheory.T.continuous_translates_kernel_route_small_vertex hL W B ρ t i j Θ Θ' hΘ g₁ z
  have hRD := GlobalTheory.Grow.rapidDec_of_cuspForm (GlobalTheory.Grow.cuspRapidDecay_of_bound hP) W.θ_is hF hFc
  obtain ⟨Bd, hBd⟩ := hRD.decay k
  refine ⟨z, hz, fun g => ?_, ?_⟩
  · exact Integrable.of_bound ((hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable) _
      (.of_forall fun u => hbd g u)
  · have h0 : (0 : ℝ) ≤ |C₀| * |C| * (2 * GlobalTheory.Grow.height _ g₁) ^ k :=
      mul_nonneg (mul_nonneg (abs_nonneg C₀) (abs_nonneg C)) (pow_nonneg (by have := GlobalTheory.Grow.height_pos _ g₁; positivity) k)
    refine Integrable.of_bound ((hRD.continuous.comp continuous_fst).mul hcont).aestronglyMeasurable
      (|C₀| * |C| * (2 * GlobalTheory.Grow.height _ g₁) ^ k * Bd) (.of_forall fun p => ?_)
    rw [norm_mul]
    calc ‖F p.1‖ * ‖translates z (kerSmall W Θ' p.1 g₁) p.2‖ ≤
          ‖F p.1‖ * (|C₀| * |C| * (2 * GlobalTheory.Grow.quotHeight _ p.1 * GlobalTheory.Grow.height _ g₁) ^ k) :=
          mul_le_mul_of_nonneg_left (hbd _ _) (norm_nonneg _)
      _ = |C₀| * |C| * (2 * GlobalTheory.Grow.height _ g₁) ^ k * (‖F p.1‖ * GlobalTheory.Grow.quotHeight _ p.1 ^ k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hBd _) h0
end GlobalTheory.ZConv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationCombIntegrableThetaKernelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translation_comb_integrable_thetaKernel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∃ z : GA D (G.V (.grid i j)) →₀ ℂ, zdeg z ≠ 0 ∧
    (∀ g, IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd (.grid i j)) (M.ν (.grid i j))) ∧
    Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) => F p.1 * translates z (kerSmall W Θ' p.1 g₁) p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid i j)).restrict (M.fd (.grid i j)))) := by
  first | exact @GlobalTheory.ZConv.zconv | exact GlobalTheory.ZConv.zconv | (intros; apply GlobalTheory.ZConv.zconv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteSumTranslatedOuterIntegralsEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteSumTranslatedOuterIntegralsEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallRoute

theorem sum_integral_translates_outer_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ' : TotT G (routeSmall t i j))
    (F : Fn G (.grid i (j + 1))) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j))) (z : GA D (G.V (.grid i j)) →₀ ℂ)
    (hI : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => GlobalTheory.SmallRoute.outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j)))
    (hJ : Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) => F p.1 * translates z (kerSmall W Θ' p.1 g₁) p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid i j)).restrict (M.fd (.grid i j))))),
    (Θ'.sum fun d c => c * ∫ u in M.fd (.grid i j), translates z (GlobalTheory.SmallRoute.outer W M d F g₁) u ∂M.ν (.grid i j)) =
      ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid i j),
        translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j) ∂M.ν (.grid i (j + 1)) := by
  intro D T L sc G μ₀ hL W t i j M hM Θ' F hB g₁ z hI hJ
  classical
  have hσ : ∀ X : Node, X.InRange D.R.m → SigmaFinite (M.ν X) := fun X hX => by
    obtain ⟨h1, h2, -⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D (G.V X)
    haveI := (hM.vtx X hX).haar_fund.1
    infer_instance
  haveI := hσ (.grid i (j + 1)) ⟨i.2.le, j.2⟩
  haveI := hσ (.grid i j) ⟨i.2.le, j.2.le⟩
  have hpt : ∀ u, ∫ g in M.fd (.grid i (j + 1)), F g * translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i (j + 1)) =
      Θ'.sum fun d c => c * translates z (outer W M d F g₁) u := by
    intro u
    have hint : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun g => W.kerA (.down t i j) d.1.2 g (u * k) * F g)
        (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1))) := fun d hd k => (hB d hd).1.2 (u * k)
    have e : ∀ g, F g * translates z (kerSmall W Θ' g g₁) u = ∑ k ∈ z.support, ∑ d ∈ Θ'.support,
        z k * (Θ' d * (W.kerA (.right i j) d.2 (u * k) g₁ * (W.kerA (.down t i j) d.1.2 g (u * k) * F g))) := by
      intro g
      simp only [translates, kerSmall, Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun d _ => by ring
    simp_rw [e]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun d hd =>
      (((hint d hd k).const_mul _).const_mul _).const_mul _]
    simp_rw [integral_finsetSum _ fun d hd => (((hint d hd _).const_mul _).const_mul _).const_mul _]
    simp only [integral_const_mul, translates, outer, Finsupp.sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun k _ => by ring
  have hint2 : ∀ d ∈ Θ'.support, Integrable (translates z (outer W M d F g₁))
      ((M.ν (.grid i j)).restrict (M.fd (.grid i j))) := fun d hd =>
    integrable_finsetSum _ fun k _ => (hI d hd k).const_mul _
  symm
  calc ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid i j), translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j)
        ∂M.ν (.grid i (j + 1))
      = ∫ g in M.fd (.grid i (j + 1)), ∫ u in M.fd (.grid i j), F g * translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j)
        ∂M.ν (.grid i (j + 1)) := by simp_rw [integral_const_mul]
    _ = ∫ u in M.fd (.grid i j), ∫ g in M.fd (.grid i (j + 1)), F g * translates z (kerSmall W Θ' g g₁) u
        ∂M.ν (.grid i (j + 1)) ∂M.ν (.grid i j) := integral_integral_swap hJ
    _ = ∫ u in M.fd (.grid i j), (Θ'.sum fun d c => c * translates z (outer W M d F g₁) u) ∂M.ν (.grid i j) := by
        simp_rw [hpt]
    _ = _ := by
        simp only [Finsupp.sum]
        rw [integral_finsetSum _ fun d hd => (hint2 d hd).const_mul _]
        simp_rw [integral_const_mul]

end GlobalTheory.SmallRoute

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteSumTranslatedOuterIntegralsEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallRoute_sum_translated_outerIntegrals_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ' : TotT G (routeSmall t i j))
    (F : Fn G (.grid i (j + 1))) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j))) (z : GA D (G.V (.grid i j)) →₀ ℂ)
    (hI : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => GlobalTheory.SmallRoute.outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j)))
    (hJ : Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) => F p.1 * translates z (kerSmall W Θ' p.1 g₁) p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid i j)).restrict (M.fd (.grid i j))))),
    (Θ'.sum fun d c => c * ∫ u in M.fd (.grid i j), translates z (GlobalTheory.SmallRoute.outer W M d F g₁) u ∂M.ν (.grid i j)) =
      ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid i j),
        translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j) ∂M.ν (.grid i (j + 1)) := by
  first | exact @GlobalTheory.SmallRoute.sum_integral_translates_outer_eq | exact GlobalTheory.SmallRoute.sum_integral_translates_outer_eq | (intros; apply GlobalTheory.SmallRoute.sum_integral_translates_outer_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTranslatesConvergentLiftDegree
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallRoute

theorem exists_translates_lift : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∃ z : GA D (G.V (.grid i j)) →₀ ℂ, zdeg z ≠ 0 ∧
    (∀ᵐ g ∂(M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1))),
      IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd (.grid i j)) (M.ν (.grid i j))) ∧
    zdeg z * liftT W M (routeSmall t i j) Θ' F g₁ = ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid i j),
      translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j) ∂M.ν (.grid i (j + 1)) := by
  intro D T L sc G hWC hK hP μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hB g₁
  obtain ⟨z, hz, h1, hJ⟩ := GlobalTheory.T.exists_translation_comb_integrable_thetaKernel hK hP hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hB g₁
  obtain ⟨hI, h2⟩ := GlobalTheory.T.smallRoute_combination_mul_lift_by_degree hL W B ρ t i j M hM Θ Θ' hΘ F hF hB g₁ z
  exact ⟨z, hz, Filter.Eventually.of_forall h1, h2.trans (GlobalTheory.T.smallRoute_sum_translated_outerIntegrals_eq hL W t i j M hM Θ' F hB g₁ z hI hJ)⟩

end GlobalTheory.SmallRoute

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTranslatesConvergentLiftDegreeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_translates_convergent_lift_degree : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∃ z : GA D (G.V (.grid i j)) →₀ ℂ, zdeg z ≠ 0 ∧
    (∀ᵐ g ∂(M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1))),
      IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd (.grid i j)) (M.ν (.grid i j))) ∧
    zdeg z * liftT W M (routeSmall t i j) Θ' F g₁ = ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid i j),
      translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j) ∂M.ν (.grid i (j + 1)) := by
  first | exact @GlobalTheory.SmallRoute.exists_translates_lift | exact GlobalTheory.SmallRoute.exists_translates_lift | (intros; apply GlobalTheory.SmallRoute.exists_translates_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEqIntegralRouteKernelFubini
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthIntegralNormKernelBigVertexRoute
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelNormLeConstMulThetaKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelNormLeConstMulThetaKernel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigRouteIdent

open GlobalTheory.RouteSeesaw

theorem kerBig_norm_le_thetaKO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∃ (ε : Bool) (ω : GlobalTheory.Grid.WRep (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))))
      (χ χ' : (AE D)ˣ →* Circle) (Φ : WO (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) → ℂ) (C₀ : ℝ),
      GlobalTheory.Grid.IsWeil W.ψ ε _ _ χ χ' ω ∧ IsThetaFunO W.ψ (GlobalTheory.Grid.sgn ε (G.V (.grid (i + 1) (j + 1)))) _ Φ ∧
      ∀ g u, ‖kerBig W Θ g g₁ u‖ ≤ C₀ * ‖thetaKO ω u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) Φ‖ := by
  intro D T L sc G μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  have hd := GlobalTheory.T.isThetaFunO_of_matchedSquare_bigRoute hL W B ρ t i j Θ Θ' hΘ
  have h1 := W.om_is (.chi i (j + 1)) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  have h2 := W.om_is (.mu t (i + 1) j) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  obtain ⟨ω₂, χa, χb, hω₂, hadj⟩ := GlobalTheory.T.weilDatum_adjoint_negSource_kernels_agree W.ψ W.ψ_std _ _ _ _ _ h2
  obtain ⟨ω', χ, χ', c, hω', hc, hbox⟩ := GlobalTheory.SeesawSumTarget.seesaw_sum W.ψ W.ψ_std _ _ _ _ _ _ _ _ ω₂ h1 hω₂
  let S := G.V (.grid (↑i + 1) (↑j + 1))
  let A := G.V (.grid (↑i) (↑j + 1))
  let Bs := G.V (.grid (↑i + 1) ↑j)
  let Φ : WO (negSp S) (GlobalTheory.Doubling.hsum A Bs) → ℂ :=
    Θ.sum fun d a => a • box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))
  have hth : ∀ d ∈ Θ.support, IsThetaFunO W.ψ (negSp S) (GlobalTheory.Doubling.hsum A Bs)
      (box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))) := fun d hdm =>
    (hbox _ _ (hd d hdm).1 ((hadj _ (hd d hdm).2).1)).1
  have e : ∀ u g, ∀ d ∈ Θ.support, thetaKO ω' (negGA S u) (GlobalTheory.SquareComm.blk A Bs (g, g₁))
      (box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))) =
      c (negGA S u) g g₁ * (W.kerA (.right i (j + 1)) d.1.2 g u * W.kerA (.down t (i + 1) j) d.2 u g₁) := fun u g d hdm => by
    rw [(hbox _ _ (hd d hdm).1 ((hadj _ (hd d hdm).2).1)).2, (hadj _ (hd d hdm).2).2]
    rfl
  refine ⟨true, ω'.comp ((negGA S).toMonoidHom.prodMap (MonoidHom.id _)), χ, χ', Φ, 1, hω', ?_, ?_⟩
  · let U : Submodule ℂ (WO (negSp S) (GlobalTheory.Doubling.hsum A Bs) → ℂ) :=
      { carrier := {g | IsThetaFunO W.ψ (negSp S) (GlobalTheory.Doubling.hsum A Bs) g}
        add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
        zero_mem' := GlobalTheory.OrientedHeis.theta_zero
        smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }
    show Φ ∈ U
    exact U.sum_mem fun d hdm => U.smul_mem _ (hth d hdm)
  · intro g u
    have key : ω' (negGA S u, GlobalTheory.SquareComm.blk A Bs (g, g₁)) Φ 0 = c (negGA S u) g g₁ * kerBig W Θ g g₁ u := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Φ, kerBig, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hdm => ?_
      have := e u g d hdm
      simp only [thetaKO] at this
      rw [this]; ring
    refine le_of_eq ?_
    show ‖kerBig W Θ g g₁ u‖ = 1 * ‖ω' (negGA S u, GlobalTheory.SquareComm.blk A Bs (g, g₁)) Φ 0‖
    rw [key, norm_mul, hc, one_mul, one_mul]

end GlobalTheory.BigRouteIdent

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelNormLeConstMulThetaKernelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigRoute_kernel_norm_le_const_mul_thetaKernel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∃ (ε : Bool) (ω : GlobalTheory.Grid.WRep (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))))
      (χ χ' : (AE D)ˣ →* Circle) (Φ : WO (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) → ℂ) (C₀ : ℝ),
      GlobalTheory.Grid.IsWeil W.ψ ε _ _ χ χ' ω ∧ IsThetaFunO W.ψ (GlobalTheory.Grid.sgn ε (G.V (.grid (i + 1) (j + 1)))) _ Φ ∧
      ∀ g u, ‖kerBig W Θ g g₁ u‖ ≤ C₀ * ‖thetaKO ω u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) Φ‖ := by
  first | exact @GlobalTheory.BigRouteIdent.kerBig_norm_le_thetaKO | exact GlobalTheory.BigRouteIdent.kerBig_norm_le_thetaKO | (intros; apply GlobalTheory.BigRouteIdent.kerBig_norm_le_thetaKO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthIntegralNormKernelBigVertexRoute
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigRoute

theorem modGrowth_integral_norm_kerBig {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))) :
    GlobalTheory.Grow.ModGrowth (G.V (.grid i (j + 1))) (fun g => ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1))) := by
  obtain ⟨ε, ω, χ, χ', Φ, C₀, hω, hΦ, hb⟩ := GlobalTheory.T.bigRoute_kernel_norm_le_const_mul_thetaKernel (G := G) hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  obtain ⟨p, hsig, hrk⟩ := GlobalTheory.T.squareThetaTriple_exists_signature_rank_sum_lt W t i j hT M hM
  have hHF : GlobalTheory.SquareComm.IsHaarFD _ (M.ν (.grid (i + 1) (j + 1))) (M.fd (.grid (i + 1) (j + 1))) :=
    (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund
  obtain ⟨N, Cw, hMI⟩ := hWC D W.ψ W.θ W.θ_is ε _ _ χ χ' ω hω p hsig hrk _ _ hHF Φ hΦ
  obtain ⟨Cc, hCc, hcmp⟩ := GlobalTheory.Grow.height_comparison (G.V (.grid i (j + 1))) W.θ_is
  set h₁ : ℝ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ g₁ : ℝ)
  refine ⟨max C₀ 0 * (max Cw 0 * (Cc * h₁) ^ N), N, fun g => ?_⟩
  have hI := (hMI (GlobalTheory.SquareComm.blk _ _ (g, g₁))).1
  have hle := (hMI (GlobalTheory.SquareComm.blk _ _ (g, g₁))).2
  have hpos : 0 ≤ ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1)) :=
    integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_of_nonneg hpos]
  have h1 : ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1)) ≤
      ∫ u in M.fd (.grid (i + 1) (j + 1)), max C₀ 0 * ‖thetaKO ω u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) Φ‖ ∂M.ν (.grid (i + 1) (j + 1)) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) (hI.norm.const_mul _)
      (Filter.Eventually.of_forall fun u => (hb g u).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
  rw [integral_const_mul] at h1
  have hX := GlobalTheory.T.unitaryAdelicHeight_orthogonalSum_embedding_le_mul D W.θ _ _ g g₁
  have hXg : ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) ≤
      Cc * GlobalTheory.Grow.height _ g * h₁ := by
    have := (hcmp g).1
    calc _ ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ g : ℝ) * h₁ := by exact_mod_cast hX
      _ ≤ _ := mul_le_mul_of_nonneg_right this (NNReal.coe_nonneg _)
  have h0 : (0 : ℝ) ≤ ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) := NNReal.coe_nonneg _
  have h2 : ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) ^ N ≤
      (Cc * h₁) ^ N * GlobalTheory.Grow.height _ g ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ h0 (hXg.trans_eq (by ring)) N
  have h3 : Cw * ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) ^ N ≤
      max Cw 0 * ((Cc * h₁) ^ N * GlobalTheory.Grow.height _ g ^ N) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg h0 _)).trans
      (mul_le_mul_of_nonneg_left h2 (le_max_right _ _))
  calc _ ≤ _ := h1
    _ ≤ max C₀ 0 * (max Cw 0 * ((Cc * h₁) ^ N * GlobalTheory.Grow.height _ g ^ N)) :=
      mul_le_mul_of_nonneg_left (hle.trans h3) (le_max_right _ _)
    _ = _ := by ring

end GlobalTheory.BigRoute
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthIntegralNormKernelBigVertexRouteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderateGrowth_integral_norm_kernel_bigVertexRoute : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    GlobalTheory.Grow.ModGrowth (G.V (.grid i (j + 1))) (fun g => ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1))) := by
  first | exact @GlobalTheory.BigRoute.modGrowth_integral_norm_kerBig | exact GlobalTheory.BigRoute.modGrowth_integral_norm_kerBig | (intros; apply GlobalTheory.BigRoute.modGrowth_integral_norm_kerBig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRouteBigVertexRationalLeftInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRouteBigVertexRationalLeftInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigRouteInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem theta_first_of_matched {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)} (hΘ : IsMatched B t ρ i j Θ Θ')
    {d : PureT G (routeBig t i j)} (hd : d ∈ Θ.support) :
    IsThetaFunO W.ψ (G.pS (.chi (i : ℕ) ((j : ℕ) + 1))) (G.pT (.chi (i : ℕ) ((j : ℕ) + 1))) d.1.2 := by
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, -, ⟨φ₁, φ₂, hloc, -⟩⟩, rfl, -⟩ := hΘ
  obtain ⟨d₀, hd₀, P, rfl⟩ := GlobalTheory.SmallRoute.mem_support_tensT W hd
  obtain ⟨h1, -⟩ := hloc d₀ hd₀
  have v1 := ρ.vX_is i (j + 1) i.2 j.2
  have t1 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h1.2 v1.2.theta
  exact GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _

theorem kerBig_rat_mul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g : GA D (G.V (.grid i (j + 1))), kerBig W Θ (γ * g) g₁ = kerBig W Θ g g₁ := by
  intro D T L sc G μ₀ hL W B ρ t i j Θ Θ' hΘ g₁ γ hγ g
  have hc := W.om_is (.chi (i : ℕ) ((j : ℕ) + 1)) ⟨i.2, j.2⟩
  funext u
  unfold kerBig
  refine Finsupp.sum_congr fun d hd => ?_
  have h1 := theta_first_of_matched hΘ hd
  congr 2
  show thetaKO (W.om (.chi (i : ℕ) ((j : ℕ) + 1))) (negGA _ u) (γ * g) d.1.2 =
    thetaKO (W.om (.chi (i : ℕ) ((j : ℕ) + 1))) (negGA _ u) g d.1.2
  unfold thetaKO
  have e : ((negGA _ u, γ * g) : GA D (G.pS (.chi (i : ℕ) ((j : ℕ) + 1))) × GA D (G.pT (.chi (i : ℕ) ((j : ℕ) + 1)))) =
      (1, γ) * (negGA _ u, g) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hc.om_aut 1 (one_mem _) γ hγ _ (hc.om_pres _ _ h1)

end GlobalTheory.BigRouteInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRouteBigVertexRationalLeftInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_route_big_vertex_rational_left_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g : GA D (G.V (.grid i (j + 1))), kerBig W Θ (γ * g) g₁ = kerBig W Θ g g₁ := by
  first | exact @GlobalTheory.BigRouteInv.kerBig_rat_mul | exact GlobalTheory.BigRouteInv.kerBig_rat_mul | (intros; apply GlobalTheory.BigRouteInv.kerBig_rat_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AestronglyMeasurableKernelRouteBigVertex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AestronglyMeasurableKernelRouteBigVertex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.BigRoute

theorem theta_of_matched_big : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)} (_ : IsMatched B t ρ i j Θ Θ')
    {d : PureT G (routeBig t i j)} (_ : d ∈ Θ.support),
    IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) d.2 := by
  intro D T L sc G W B ρ t i j Θ Θ' hΘ d hd
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, -, ⟨φ₁, φ₂, hloc, -⟩⟩, rfl, -⟩ := hΘ
  obtain ⟨d₀, hd₀, P, rfl⟩ := GlobalTheory.SmallRoute.mem_support_tensT W hd
  obtain ⟨h1, h2⟩ := hloc d₀ hd₀
  have v1 := ρ.vX_is i (j + 1) i.2 j.2
  have v2 := ρ.vT_is t (i + 1) j i.2 j.2
  have t1 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h1.2 v1.2.theta
  have t2 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h2.2 v2.2.theta
  exact ⟨GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _,
    GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _⟩

theorem continuous_kerBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (_ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    Continuous (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
      kerBig W Θ p.1 g₁ p.2) := by
  intro D T L sc G W B ρ t i j Θ Θ' hΘ g₁
  have hc := W.om_is (.chi (i : ℕ) (j + 1)) ⟨i.2, j.2⟩
  have hm := W.om_is (.mu t ((i : ℕ) + 1) j) ⟨i.2, j.2⟩
  have hK : ∀ d ∈ Θ.support, Continuous (fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
      W.kerA (.right i (j + 1)) d.1.2 q.1 q.2 * W.kerA (.down t (i + 1) j) d.2 q.2 g₁) := by
    intro d hd
    obtain ⟨h1, h2⟩ := theta_of_matched_big hΘ hd
    refine Continuous.mul ?_ ?_
    · show Continuous fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
        thetaKO (W.om (.chi (i : ℕ) (j + 1))) (negGA _ q.2) q.1 d.1.2
      exact (hc.om_cont _ h1 0).comp (((continuous_negGA _).comp continuous_snd).prodMk continuous_fst)
    · show Continuous fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
        thetaKO (W.om (.mu t ((i : ℕ) + 1) j)) g₁ q.2 d.2
      exact (hm.om_cont _ h2 0).comp (continuous_const.prodMk continuous_snd)
  unfold kerBig
  simp only [Finsupp.sum]
  exact continuous_finsetSum _ fun d hd => continuous_const.mul (hK d hd)

theorem aestronglyMeasurable_kerBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) => kerBig W Θ p.1 g₁ p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁
  exact (continuous_kerBig W B ρ t i j Θ Θ' hΘ g₁).aestronglyMeasurable

end GlobalTheory.BigRoute
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AestronglyMeasurableKernelRouteBigVertexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aestronglyMeasurable_kernel_route_big_vertex : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) => kerBig W Θ p.1 g₁ p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := by
  first | exact @GlobalTheory.BigRoute.aestronglyMeasurable_kerBig | exact GlobalTheory.BigRoute.aestronglyMeasurable_kerBig | (intros; apply GlobalTheory.BigRoute.aestronglyMeasurable_kerBig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEqIntegralRouteKernelFubini
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigRoute

theorem lift_eq_integral_kerBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hA : TotConv W M _ Θ F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    (∀ᵐ g ∂(M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1))),
      IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1)))) ∧
    liftT W M (routeBig t i j) Θ F g₁ = ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid (i + 1) (j + 1)),
      kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1)) ∂M.ν (.grid i (j + 1)) := by
  intro D T L sc G hWC hK hP μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hA g₁
  classical
  have hσ : ∀ X : Node, X.InRange D.R.m → SigmaFinite (M.ν X) := fun X hX => by
    obtain ⟨h1, h2, -⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D (G.V X)
    haveI := (hM.vtx X hX).haar_fund.1
    infer_instance
  haveI := hσ (.grid i (j + 1)) ⟨i.2.le, j.2⟩
  haveI := hσ (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩
  have hK1 : ∀ g, IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1))) := GlobalTheory.T.bigRoute_kernel_integrableOn_unitary_quotient hWC hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  have hmeas : AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
      kerBig W Θ p.1 g₁ p.2) (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
        ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := GlobalTheory.T.aestronglyMeasurable_kernel_route_big_vertex hL W B ρ t i j M hM Θ Θ' hΘ g₁
  have hinv : ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g, kerBig W Θ (γ * g) g₁ = kerBig W Θ g g₁ := GlobalTheory.T.kernel_route_big_vertex_rational_left_invariant hL W B ρ t i j Θ Θ' hΘ g₁
  have hgrow : GlobalTheory.Grow.ModGrowth (G.V (.grid i (j + 1))) (fun g => ∫ u in M.fd (.grid (i + 1) (j + 1)),
      ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1))) := GlobalTheory.T.moderateGrowth_integral_norm_kernel_bigVertexRoute hWC hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  have hRD : GlobalTheory.Grow.RapidDec _ F := GlobalTheory.Grow.rapidDec_of_cuspForm (GlobalTheory.Grow.cuspRapidDecay_of_bound hP) W.θ_is hF hFc
  obtain ⟨hH, hfd⟩ := (hM.vtx (.grid i (j + 1)) ⟨i.2.le, j.2⟩).haar_fund
  have hkm : AEStronglyMeasurable (fun g => ((∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖
      ∂M.ν (.grid (i + 1) (j + 1)) : ℝ) : ℂ)) ((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hmeas.norm.integral_prod_right'
  obtain ⟨C, A, hCA⟩ := hgrow
  have hkb : ∀ g, ‖((∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1)) : ℝ) : ℂ)‖ ≤
      C * 2 ^ A * GlobalTheory.Grow.quotHeight _ g ^ A := fun g => by
    rw [Complex.norm_real]
    exact GlobalTheory.Grow.norm_le_quotHeight_pow (fun γ hγ g => by simp only [hinv γ hγ g]) hCA g
  have hkF := hRD.integrableOn_mul_of_le hH hfd hkm hkb
  have hJ : Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) => F p.1 * kerBig W Θ p.1 g₁ p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
        ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := by
    have hFm : AEStronglyMeasurable F ((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))) :=
      hRD.continuous.aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
        F p.1 * kerBig W Θ p.1 g₁ p.2) (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
          ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) :=
      hFm.comp_fst.mul hmeas
    refine (integrable_prod_iff hm2).2
      ⟨.of_forall fun g => (hK1 g).const_mul (F g), ?_⟩
    refine hkF.norm.congr (.of_forall fun g => ?_)
    simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, integral_const_mul]
    rw [abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), mul_comm]
  refine ⟨Filter.Eventually.of_forall hK1, ?_⟩
  have hpt : ∀ u, ∫ g in M.fd (.grid i (j + 1)), F g * kerBig W Θ g g₁ u ∂M.ν (.grid i (j + 1)) =
      Θ.sum fun d c => c * (W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1))) := by
    intro u
    have hint : ∀ d ∈ Θ.support, IntegrableOn (fun g => W.kerA (.right i (j + 1)) d.1.2 g u * F g)
        (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1))) := fun d hd => (hA d hd).1.2 u
    have e : ∀ g, F g * kerBig W Θ g g₁ u = ∑ d ∈ Θ.support,
        Θ d * (W.kerA (.down t (i + 1) j) d.2 u g₁ * (W.kerA (.right i (j + 1)) d.1.2 g u * F g)) := by
      intro g
      simp only [kerBig, Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    simp_rw [e]
    rw [integral_finsetSum _ fun d hd => ((hint d hd).const_mul _).const_mul _]
    simp only [integral_const_mul, Finsupp.sum]
  have hint2 : ∀ d ∈ Θ.support, Integrable (fun u => W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1)))
      ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1)))) := fun d hd => (hA d hd).2 g₁
  symm
  calc ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid (i + 1) (j + 1)), kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1))
        ∂M.ν (.grid i (j + 1))
      = ∫ g in M.fd (.grid i (j + 1)), ∫ u in M.fd (.grid (i + 1) (j + 1)), F g * kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1))
        ∂M.ν (.grid i (j + 1)) := by simp_rw [integral_const_mul]
    _ = ∫ u in M.fd (.grid (i + 1) (j + 1)), ∫ g in M.fd (.grid i (j + 1)), F g * kerBig W Θ g g₁ u
        ∂M.ν (.grid i (j + 1)) ∂M.ν (.grid (i + 1) (j + 1)) := integral_integral_swap hJ
    _ = ∫ u in M.fd (.grid (i + 1) (j + 1)), (Θ.sum fun d c => c * (W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1))))
        ∂M.ν (.grid (i + 1) (j + 1)) := by
        simp_rw [hpt]
    _ = _ := by
        simp only [Finsupp.sum]
        rw [integral_finsetSum _ fun d hd => (hint2 d hd).const_mul _]
        simp_rw [integral_const_mul]
        simp only [liftT, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rfl

end GlobalTheory.BigRoute

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEqIntegralRouteKernelFubiniStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_eq_integral_routeKernel_fubini : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hA : TotConv W M _ Θ F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    (∀ᵐ g ∂(M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1))),
      IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1)))) ∧
    liftT W M (routeBig t i j) Θ F g₁ = ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid (i + 1) (j + 1)),
      kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1)) ∂M.ν (.grid i (j + 1)) := by
  first | exact @GlobalTheory.BigRoute.lift_eq_integral_kerBig | exact GlobalTheory.BigRoute.lift_eq_integral_kerBig | (intros; apply GlobalTheory.BigRoute.lift_eq_integral_kerBig <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames _root_.Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem commutesWith_of_isSquareConst_of_triple (hWC : GlobalTheory.SquareSt.WeilConvergence)
    (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound)
    {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    (hT : SquareTriple W t i j) {c : ℂ} (hc : IsSquareConst W B ρ t i j c) : CommutesWith W B ρ t i j c := by
  intro M hM Θ Θ' hΘ F hF hFc hFl hA hB
  funext g₁
  obtain ⟨hBa, hBe⟩ := GlobalTheory.T.thetaLift_eq_integral_routeKernel_fubini hWC hK hP hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hA g₁
  obtain ⟨z, hz, hSa, hSe⟩ := GlobalTheory.T.exists_theta_translates_convergent_lift_degree hWC hK hP hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hB g₁
  refine mul_left_cancel₀ hz ?_
  rw [Pi.smul_apply, smul_eq_mul, hBe, mul_left_comm, hSe, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hBa, hSa] with g hb hs
  have h := hc M hM Θ Θ' hΘ z g g₁ ⟨hb, hs⟩
  linear_combination F g * h

theorem commutesWith_of_isSquareConst (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T}
    {i j : Fin D.R.m} (hS : SquareStanding G t) {c : ℂ} (hc : IsSquareConst W B ρ t i j c) : CommutesWith W B ρ t i j c :=
  commutesWith_of_isSquareConst_of_triple hWC hK hP hL (squareTriple_of_standing hL W t i j hS) hc

end GlobalTheory.FunObj

end
