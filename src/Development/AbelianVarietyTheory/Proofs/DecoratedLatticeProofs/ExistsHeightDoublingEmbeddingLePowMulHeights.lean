module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridNuUnitTrivial
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHZeroRight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeightDoublingEmbeddingLePowMulHeights
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeightDoublingEmbeddingLePowMulHeights
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Cont.HeightIo

theorem height_io_le_mul {D : D7} (V : HSp D) (g₁ g₂ : GA D V) :
    GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂ := by
  have h := GlobalTheory.BlockHeight.heightGL_blk_le D.host.F finSumFinEquiv
    (Formalism.L2.Theta.matHom (dblSp V) (io V (g₁, g₂))) (Formalism.L2.Theta.matHom V g₁) (Formalism.L2.Theta.matHom V g₂) rfl rfl
  show ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ) ≤
    ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ) * ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ)
  exact_mod_cast h

theorem height_io_bound : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (c : ℕ), ∀ g₁ g₂ : GA D V,
    GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c := by
  intro D V
  refine ⟨1, 1, fun g₁ g₂ => ?_⟩
  rw [one_mul, pow_one]
  exact height_io_le_mul V g₁ g₂

end GlobalTheory.Cont.HeightIo

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeightDoublingEmbeddingLePowMulHeightsStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_height_doublingEmbedding_le_pow_mul_heights : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (c : ℕ), ∀ g₁ g₂ : GA D V,
    GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c := by
  first | exact @GlobalTheory.Cont.HeightIo.height_io_bound | exact GlobalTheory.Cont.HeightIo.height_io_bound | (intros; apply GlobalTheory.Cont.HeightIo.height_io_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroSourceTensorColumnProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroSourceTensorColumnProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

variable {D : D7}

theorem isHalf_mul_right {e : AE D} {l m n : ℕ} {u : Mx D l m} (hu : IsHalf e u) (M : Mx D m n) : IsHalf e (u * M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [← mul_assoc, hu]

theorem isHalf_add_of {e : AE D} {m n : ℕ} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u + v) := by
  intro i j
  simp only [Matrix.add_apply, mul_add, hu i j, hv i j]

theorem isHalf_resS_iff {S A L T : HSp D} (o : OrthDec S A L) (e : AE D) (t : WO S T) :
    IsHalf e t ↔ IsHalf e (t * o.jA) ∧ IsHalf e (t * o.jB) := by
  refine ⟨fun h => ⟨isHalf_mul_right h _, isHalf_mul_right h _⟩, fun h => ?_⟩
  have ht : t = (o.resS T).symm (o.resS T t) := ((o.resS T).symm_apply_apply t).symm
  rw [ht, OrthDec.resS_symm_apply, OrthDec.resS_apply]
  exact isHalf_add_of (isHalf_mul_right h.1 _) (isHalf_mul_right h.2 _)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rd_sum_inl {p : SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S A L T : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1))
    (β : Frame p T n) (hs : IsSumFrame o ζ α α₀) (t : WO S T) :
    (rd α₀ β t).submatrix id Sum.inl = rd α β (t * o.jA) := by
  have hs' : α₀.b = fromCols (o.jA.map p.pr * α.b) (replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) := hs
  simp only [rd, hs', Matrix.mul_fromCols]
  ext i j
  simp only [submatrix_apply, id, fromCols_apply_inl]
  rw [Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem rd_sum_inr {p : SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S A L T : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1))
    (β : Frame p T n) (hs : IsSumFrame o ζ α α₀) (t : WO S T) :
    (fun i => rd α₀ β t i (Sum.inr 0)) = zcol β ζ (t * o.jB) := by
  have h1 : (t * o.jB) *ᵥ (fun j => incA D (ζ j)) = t *ᵥ ratV (vecB o ζ) := by
    rw [← Matrix.mulVec_mulVec]
    congr 1
    funext i
    exact (RingHom.map_mulVec (incA D) o.iB ζ i).symm
  have hs' : α₀.b = fromCols (o.jA.map p.pr * α.b) (replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) := hs
  funext i
  simp only [rd, hs', Matrix.mul_fromCols, fromCols_apply_inr, zcol, h1]
  rw [show (fun i => p.pr ((t *ᵥ ratV (vecB o ζ)) i)) = t.map p.pr *ᵥ fun i => p.pr (ratV (vecB o ζ) i) from
    funext fun i => RingHom.map_mulVec p.pr t _ i]
  rw [Matrix.mulVec_mulVec]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, replicateCol]

theorem extFun_tensCol_sum (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S A L T : HSp D)
    (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n) :
    IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ),
      extFun α₀ β (tensCol Ψ a) = o.boxS T (extFun α β Ψ) (GlobalTheory.FinPl.ExtZero.colFun β ζ a) := by
  intro hs Ψ a
  funext t
  simp only [extFun, OrthDec.boxS, colFun]
  have key : IsHalf p.e t ↔ IsHalf p.e (o.resS T t).1 ∧ IsHalf p.e (o.resS T t).2 := isHalf_resS_iff o p.e t
  by_cases h : IsHalf p.e t
  · obtain ⟨hA, hL⟩ := key.1 h
    rw [if_pos h, if_pos hA, if_pos hL, tensCol, rd_sum_inl o ζ α α₀ β hs, rd_sum_inr o ζ α α₀ β hs]
    rfl
  · rw [if_neg h]
    by_cases hA : IsHalf p.e (o.resS T t).1
    · rw [if_neg fun hL => h (key.2 ⟨hA, hL⟩), mul_zero]
    · rw [if_neg hA, zero_mul]

end GlobalTheory.FinPl.ExtZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroSourceTensorColumnProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendByZero_source_tensor_column_product : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), extFun α₀ β (tensCol Ψ a) = o.boxS T (extFun α β Ψ) (GlobalTheory.FinPl.ExtZero.colFun β ζ a) := by
  exact @GlobalTheory.FinPl.ExtZero.extFun_tensCol_sum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroRightMemCoreLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroRightMemCoreLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.ContrComb.LatT

variable {D : D7}

theorem latV_entry_mem {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) (i : Fin S.rank) : y i ∈ idAt D P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, -, hβ, c, -, x, -, rfl⟩ := hz
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hβ _
  | zero => exact zero_mem _
  | add z z' _ _ hz hz' => exact add_mem hz hz'
  | neg z _ hz => exact neg_mem hz

theorem jA_latV {V₀ A L : HSp D} (o : OrthDec V₀ A L) {P : Pl D → Prop} {LA : Lat A} {M : Lat V₀}
    (hLA : IsSelfDualC A LA) (hM : IsSelfDualC V₀ M) (hloc : ∀ v, P v → ∃ LL, OrthAt o M LA LL v)
    {y : Fin A.rank → AE D} (hy : y ∈ latV A LA P) : o.jA *ᵥ y ∈ latV V₀ M P := by
  have hG := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P
  have hy' := ((hG.2 A).2.2.2 LA y hLA.1).1 hy
  refine ((hG.2 V₀).2.2.2 M _ hM.1).2 ⟨fun i => ?_, fun v hv e he => ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy'.1 j)
  · obtain ⟨LL, hLL⟩ := hloc v hv
    have hz := hy'.2 v hv e he
    rw [← Matrix.mulVec_smul]
    refine (hLL _).2 ⟨?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, o.pA_jA, Matrix.one_mulVec]; exact hz
    · rw [Matrix.mulVec_mulVec, o.pB_jA, Matrix.zero_mulVec]; exact zero_mem _

theorem smul_latV_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {w : Fin S.rank → AE D} (hw : w ∈ latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • w ∈ latA S L P := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

theorem jA_latA {V₀ A L : HSp D} (o : OrthDec V₀ A L) {P : Pl D → Prop} {LA : Lat A} {M : Lat V₀}
    (hLA : IsSelfDualC A LA) (hM : IsSelfDualC V₀ M) (hloc : ∀ v, P v → ∃ LL, OrthAt o M LA LL v)
    {z : Fin A.rank → AE D} (hz : z ∈ latA A LA P) : o.jA *ᵥ z ∈ latA V₀ M P := by
  induction hz using AddSubgroup.closure_induction with
  | mem g hg =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hg
    have hsplit : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i) : Fin A.rank → AE D) =
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    exact smul_latV_mem_latA ha
      (jA_latV o hLA hM hloc (AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, x, hx, rfl⟩))
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem latO_extR : ∀ (D : D7) (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (P : Pl D → Prop) (LA : Lat A) (LS : Lat S)
    (M : Lat V₀), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC V₀ M → (∀ v, P v → ∃ LL, OrthAt o M LA LL v) →
    ∀ u ∈ latO S A (LS : Set _) (LA : Set _) P, (o.resT S).symm (u, 0) ∈ latO S V₀ (LS : Set _) (M : Set _) P := by
  intro D V₀ A L S o P LA LS M hLA hLS hM hloc u hu
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
  have hu' := (GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D S A LS LA hLS hLA P u).1 hu
  refine (GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D S V₀ LS M hLS hM P _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hu'.1 k j)
  · show (o.jA * u) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec]
    exact jA_latA o hLA hM hloc (hu'.2 y hy)

end GlobalTheory.ContrComb.LatT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroRightMemCoreLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendByZero_right_mem_core_lattice : ∀ (D : D7) (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (P : Pl D → Prop) (LA : Lat A) (LS : Lat S) (M : Lat V₀), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC V₀ M → (∀ v, P v → ∃ LL, OrthAt o M LA LL v) → ∀ u ∈ latO S A (LS : Set _) (LA : Set _) P, (o.resT S).symm (u, 0) ∈ latO S V₀ (LS : Set _) (M : Set _) P := by
  first | exact @GlobalTheory.ContrComb.LatT.latO_extR | exact GlobalTheory.ContrComb.LatT.latO_extR | (intros; apply GlobalTheory.ContrComb.LatT.latO_extR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntertwinerValuesKFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntertwinerValuesKFinite
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ItKFin

theorem inclT_mapFactor {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (g : Module.End ℂ (M.sm τ)) (A : M.H τ →ₗ[ℂ] M.H τ) (hg : ∀ w, ((g w : M.sm τ) : M.H τ) = A w) (y : SmT M) :
    inclT M (GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one τ g y) =
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ A) (inclT M y) := by
  rw [inclT, GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp,
    ← PiTensorProduct.map_comp]
  congr 2
  funext ρ
  by_cases e : ρ = τ
  · subst e
    ext w
    simp [hg]
  · ext w
    simp [e]

theorem itKFin : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsInfFam θ → IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It → ∀ P v, It P v ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}) := by
  intro D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt P v
  obtain ⟨χS, χT, hWD, hexp⟩ := hW
  have hp : ptOf ψ θ M M' f = ⇑(pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f) := rfl
  have hA : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∃ P' : PolF D W.rank V.rank, P'.totalDegree ≤ P.totalDegree ∧
      inclT M (It P' v) = actT M τ ((M.fr τ)⁻¹ * h * M.fr τ) (inclT M (It P v)) := by
    intro τ h hh
    obtain ⟨a, b, -, -, hc⟩ := GlobalTheory.CompactFockAction.compactFockAll D V W (Fr.ofModel M) (Fr.ofModel M') θ ψ χS χT ω f τ
      (aS τ) (aT τ) hθ hWD (hexp τ).1 (hexp τ).2 ⟨hf.theta, hf.vac⟩ hf.ne
    have h1 : (1 : Matrix (Fin W.rank) (Fin W.rank) ℂ) ∈ Formalism.REAL.Kset (M'.ε τ) := ⟨one_mem _, by simp⟩
    have := hc h hh 1 h1 P
    have e1 : (Fr.ofModel M').elt θ τ 1 = 1 := by
      have hd' := (Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
      show atTau θ W τ ((M'.fr τ)⁻¹ * 1 * M'.fr τ) = 1
      rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hd']
      exact GlobalTheory.PointAtPlaceHom.atTau_one hθ W τ
    rw [e1, ptF_ofModel, hp, ← map_smul, ← hp] at this
    refine ⟨_, ?_, hIt.eqK τ _ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt_subset M τ (GlobalTheory.Chain.IoLift.frame_mem M τ hh)) P _ this.symm v⟩
    exact (MvPolynomial.totalDegree_smul_le _ _).trans (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _)
  have hJ := fun τ => (Formalism.REAL.maximal_compact_facts _ (M.ε τ)).1
  have hsm : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∀ w ∈ M.sm τ, (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ) w ∈ M.sm τ :=
    fun τ h hh w hw => (GlobalTheory.MultGelf.mem_sm M τ).2 (GlobalTheory.SmVec.sigma_mem (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
      ((GlobalTheory.MultGelf.mem_sm M τ).1 hw) (hJ τ h hh))
  let fK : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), Module.End ℂ (M.sm τ) := fun τ h hh =>
    (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ).restrict (hsm τ h hh)
  have hconj : ∀ τ (h : Matrix (Fin V.rank) (Fin V.rank) ℂ), M.fr τ * ((M.fr τ)⁻¹ * h * M.fr τ) * (M.fr τ)⁻¹ = h :=
    fun τ h => by
      have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  have hact : ∀ τ h (hh : h ∈ Formalism.REAL.Kset (M.ε τ)) (y : SmT M),
      inclT M (GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one τ (fK τ h hh) y) = actT M τ ((M.fr τ)⁻¹ * h * M.fr τ) (inclT M y) := by
    intro τ h hh y
    rw [inclT_mapFactor M τ _ (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ) (fun w => rfl)]
    simp only [actT, DSModel.rep, hconj]
  have hx := GlobalTheory.Chain.IoLift.mem_range_map_subtype_of_contr D.what₂.Tau (fun τ => M.sm τ)
    (fun τ => (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ).comap (M.sm τ).subtype) (It P v) fun τ L hL => by
      show IsKFin (M.ε τ) (M.σ τ) ((L (It P v) : M.sm τ) : M.H τ)
      let E : Submodule ℂ (SmT M) := (MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree).map (It.flip v)
      have hle : Submodule.span ℂ ((fun k => M.σ τ k ((L (It P v) : M.sm τ) : M.H τ)) '' Formalism.REAL.Kset (M.ε τ)) ≤
          (E.map L).map (M.sm τ).subtype := by
        rw [Submodule.span_le]
        rintro _ ⟨k, hk, rfl⟩
        obtain ⟨P', hP', e⟩ := hA τ k hk
        have e2 : It P' v = GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one τ (fK τ k hk) (It P v) :=
          (tensorLaw D V S M).inj (by rw [e, hact τ k hk])
        have e3 := LinearMap.congr_fun (hL (fK τ k hk)) (It P v)
        simp only [LinearMap.comp_apply] at e3
        refine ⟨L (It P' v), ⟨It P' v, ⟨P', (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP', rfl⟩, rfl⟩, ?_⟩
        rw [e2, e3]
        rfl
      have hσ := (M.ds τ).2.2.1
      refine ⟨_, Submodule.finiteDimensional_of_le hle, Submodule.subset_span ⟨1, ⟨one_mem _, by simp⟩, ?_⟩,
        fun g hg w hw => ?_⟩
      · simp only [hσ.1.1]; rfl
      · refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap (M.σ τ g : M.H τ →ₗ[ℂ] M.H τ) _)).2 ?_ hw)
        rintro _ ⟨k, hk', rfl⟩
        refine Submodule.subset_span ⟨g * k, Formalism.REAL.Kset_mul _ hg hk', ?_⟩
        simp only [hσ.1.2 g (hJ τ g hg) k (hJ τ k hk')]; rfl
  obtain ⟨z, hz⟩ := hx
  rw [← hz]
  clear hz
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r n =>
    rw [map_smul, PiTensorProduct.map_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun τ => (n τ : M.sm τ), fun τ => Submodule.subset_span (n τ).2, rfl⟩)
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

end GlobalTheory.ItKFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntertwinerValuesKFiniteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_intertwiner_values_kFinite : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsInfFam θ → IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It → ∀ P v, It P v ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}) := by
  first | exact @GlobalTheory.ItKFin.itKFin | exact GlobalTheory.ItKFin.itKFin | (intros; apply GlobalTheory.ItKFin.itKFin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactGinfCOfOntoUni
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem isCompact_ginfC_of_ontoUni (D : D7) (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hθ : IsInfFam θ) (hr : OntoUni (fun k : GinfC V => inB θ V B k.1)) : IsCompact (GinfC V : Set (GA D V)) := by
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hB : ∀ τ, IsUnit (B τ).det := by
    intro τ
    by_contra hn
    have h0 := hr.uni 1 τ
    have e : inB (Formalism.IndefR.Eqv.thetaC D) V B (1 : GinfC V).1 τ = 0 := by
      simp only [inB, Matrix.nonsing_inv_apply_not_isUnit _ hn, Matrix.zero_mul]
    rw [e] at h0
    have h1 : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) = 0 := by
      have := Matrix.mem_unitaryGroup_iff.mp h0
      simpa using this.symm
    have hB1 : B τ = 1 := by
      calc B τ = B τ * 1 := (Matrix.mul_one _).symm
        _ = 0 := by rw [h1, Matrix.mul_zero]
        _ = 1 := h1.symm
    exact hn (by rw [hB1, Matrix.det_one]; exact isUnit_one)
  have hconj : ∀ τ (M : Matrix (Fin V.rank) (Fin V.rank) ℂ), B τ * ((B τ)⁻¹ * M * B τ) * (B τ)⁻¹ = M := by
    intro τ M
    calc B τ * ((B τ)⁻¹ * M * B τ) * (B τ)⁻¹ = (B τ * (B τ)⁻¹) * M * (B τ * (B τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = M := by rw [Matrix.mul_nonsing_inv _ (hB τ), Matrix.one_mul, Matrix.mul_one]
  have hU : ∀ u : D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ,
      Formalism.IndefR.Eqv.IsUnitFam D V (fun τ => B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹) := by
    intro u
    obtain ⟨k, hk⟩ := hr.onto (fun τ => (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)) (fun τ => (u τ).2)
    have e : (fun τ => B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹) =
        fun τ => infMat D.sp.cm.sig V.gram (Formalism.IndefR.Eqv.thetaC D τ) (k : GA D V) := by
      funext τ
      have := congrFun hk τ
      rw [← this]
      exact hconj τ _
    rw [e]
    exact Formalism.IndefR.Eqv.infMat_unitary' D V _
  have : CompactSpace (unitaryGroup (Fin V.rank) ℂ) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.isCompact_unitaryGroup _ _)
  let Ψ : (D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ) → GA D V := fun u => Formalism.IndefR.Eqv.famH D V _ (hU u)
  have hg : Continuous fun u : (D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ) =>
      fun τ => B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹ :=
    continuous_pi fun τ => (continuous_const.matrix_mul (continuous_subtype_val.comp (continuous_apply τ))).matrix_mul
      continuous_const
  have hΨ : Continuous Ψ := by
    refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
    · exact GlobalTheory.HaarReal.continuous_famM.comp hg
    · have hi : Continuous fun u : (D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ) =>
          fun τ => Formalism.IndefR.Eqv.ginv D V τ (B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹) :=
        continuous_pi fun τ => (continuous_const.matrix_mul ((continuous_apply τ).comp hg).matrix_conjTranspose).matrix_mul
          continuous_const
      exact GlobalTheory.HaarReal.continuous_famM.comp hi
  have hsub : (GinfC V : Set (GA D V)) ⊆ Set.range Ψ := by
    intro g hg
    refine ⟨fun τ => ⟨inB (Formalism.IndefR.Eqv.thetaC D) V B g τ, hr.uni ⟨g, hg⟩ τ⟩, ?_⟩
    refine (Formalism.IndefR.Eqv.famH_unique D V _ (hU _) g hg fun τ => ?_).symm
    exact (hconj τ _).symm
  exact (isCompact_range hΨ).of_isClosed_subset (GlobalTheory.Ker.CongTop.isClosed_GinfC V) hsub

end GlobalTheory.SeeSaw

namespace GlobalTheory.SeeSaw

theorem integral_eq_classSum : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ → OntoUni (fun k : GinfC V => inB θ V B k.1) → BorelSpace (GinfC V) ∧ CompactSpace (GinfC V) ∧ (∀ g ∈ GfC V, ∀ k ∈ GinfC V, g * k = k * g) ∧ ∃ ν : Measure (GinfC V), IsProbabilityMeasure ν ∧ ν.IsMulLeftInvariant ∧ ∀ (v : Vol V) (U : Subgroup (GA D V)) (cl : Type) [Fintype cl] (h : cl → GA D V), IsReps V U h → 0 < volLev v U ∧ (∀ a, 0 < stabOrd U (h a)) ∧ ∀ Φ : GA D V → ℂ, Continuous Φ → (∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) → (∀ κ ∈ U, ∀ g, Φ (g * κ) = Φ g) → ∫ g in v.𝓕, Φ g ∂v.μ = (volLev v U : ℂ) * ∑ a, ((stabOrd U (h a) : ℕ) : ℂ)⁻¹ * ∫ k, Φ (h a * k.1) ∂ν := by
  intro D θ V B hθ hr
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.1
  haveI := hT.2.1
  haveI := hT.2.2.1
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := hT.2.2.2.2.2.1
  haveI := hT.2.2.2.2.2.2
  have hK : IsCompact (GinfC V : Set (GA D V)) := isCompact_ginfC_of_ontoUni D θ V B hθ hr
  haveI : CompactSpace (GinfC V) := isCompact_iff_compactSpace.mp hK
  haveI : BorelSpace (GinfC V) := Subtype.borelSpace _
  have hcf : ∀ {a b : GA D V}, a ∈ GinfC V → b ∈ GfC V → a * b = b * a := fun ha hb =>
    Formalism.IndefR.Eqv.Act.comm_inf_fin ha hb
  refine ⟨inferInstance, inferInstance, fun g hg k hk => (hcf hk hg).symm, ?_⟩
  let ν : Measure (GinfC V) := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure ν :=
    ⟨by simpa using (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC V))))⟩
  refine ⟨ν, inferInstance, inferInstance, ?_⟩
  intro v U cl _ h hU
  haveI := v.haar
  haveI : v.μ.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V v.μ v.haar
  haveI : (GinfC V).Normal := inferInstanceAs ((finHom V).ker.Normal)
  let K : Subgroup (GA D V) := GinfC V ⊔ U
  have hKset : (K : Set (GA D V)) = {g | ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ} := by
    show ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V)) = _
    rw [Subgroup.normal_mul]
    ext g
    simp only [Set.mem_mul, SetLike.mem_coe, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
  have hmemK : ∀ g, g ∈ K ↔ ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ := fun g => by
    rw [← SetLike.mem_coe, hKset]; rfl
  have hvol : volLev v U = (v.μ K).toReal := by
    simp only [volLev]
    rw [← hKset]
  have hKc : IsCompact (K : Set (GA D V)) := by
    show IsCompact ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V))
    rw [Subgroup.normal_mul]
    exact hK.mul hU.cpt
  have hKo : IsOpen (K : Set (GA D V)) := by
    have ho : IsOpen (((U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) : Subgroup (GA D V)) : Set (GA D V)) :=
      hU.opn.preimage (GlobalTheory.AutMult.continuous_toFin V)
    refine Subgroup.isOpen_mono (fun g hg => ?_) ho
    rw [hmemK]
    exact ⟨GlobalTheory.AutMult.toInf V g, (GlobalTheory.AutMult.toInf V g).2, GlobalTheory.AutMult.toFin V g,
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hg), (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩
  have hKfin : v.μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKpos : 0 < v.μ K := hKo.measure_pos v.μ ⟨1, K.one_mem⟩
  have huniq : ∀ x : GA D V, ∃! i, ∃ γ ∈ GQ V, ∃ k ∈ K, x = γ * h i * k := by
    intro x
    obtain ⟨γ, hγ, c, k, hk, κ, hκ, e⟩ := hU.dec x
    refine ⟨c, ⟨γ, hγ, k * κ, (hmemK _).2 ⟨k, hk, κ, hκ, rfl⟩, by rw [e]; group⟩, ?_⟩
    rintro c' ⟨γ', hγ', k', hk', e'⟩
    obtain ⟨k₁, hk₁, κ₁, hκ₁, rfl⟩ := (hmemK _).1 hk'
    refine (hU.uniq c c' (γ'⁻¹ * γ) (mul_mem (inv_mem hγ') hγ) (k * k₁⁻¹) (mul_mem hk (inv_mem hk₁)) (κ * κ₁⁻¹)
      (mul_mem hκ (inv_mem hκ₁)) ?_).symm
    have hc1 : k₁⁻¹ * (κ * κ₁⁻¹) = (κ * κ₁⁻¹) * k₁⁻¹ := hcf (inv_mem hk₁) (hU.le (mul_mem hκ (inv_mem hκ₁)))
    have e2 : h c' = γ'⁻¹ * x * (k₁ * κ₁)⁻¹ := by rw [e']; group
    rw [e2, e, _root_.mul_inv_rev]
    calc γ'⁻¹ * (γ * (h c * k) * κ) * (κ₁⁻¹ * k₁⁻¹) = γ'⁻¹ * γ * (h c * k) * ((κ * κ₁⁻¹) * k₁⁻¹) := by group
      _ = γ'⁻¹ * γ * (h c * k) * (k₁⁻¹ * (κ * κ₁⁻¹)) := by rw [hc1]
      _ = γ'⁻¹ * γ * (h c * (k * k₁⁻¹)) * (κ * κ₁⁻¹) := by group
  have hfin : ∀ i, {γ : GA D V | γ ∈ GQ V ∧ (h i)⁻¹ * γ * h i ∈ K}.Finite := by
    intro i
    have hC : IsCompact ((fun y => h i * y * (h i)⁻¹) '' (K : Set (GA D V))) :=
      hKc.image ((continuous_const.mul continuous_id).mul continuous_const)
    have hcl : IsClosed (GQ V : Set (GA D V)) := Subgroup.isClosed_of_discrete
    have hTc : IsCompact (((↑) : GQ V → GA D V) ⁻¹' ((fun y => h i * y * (h i)⁻¹) '' (K : Set (GA D V)))) :=
      hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hC
    refine (hTc.finite_of_discrete.image Subtype.val).subset ?_
    rintro γ ⟨hγ, hk⟩
    exact ⟨⟨γ, hγ⟩, ⟨_, hk, by group⟩, rfl⟩
  have hst : ∀ i, {γ : GA D V | γ ∈ GQ V ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard = stabOrd U (h i) := by
    intro i
    have hs : {γ : GA D V | γ ∈ GQ V ∧ (h i)⁻¹ * γ * h i ∈ K} =
        Subtype.val '' {γ : GQ V | ∃ k ∈ GinfC V, ∃ κ ∈ U, γ.1 * h i = h i * k * κ} := by
      ext γ
      constructor
      · rintro ⟨hγ, hk⟩
        obtain ⟨k, hk, κ, hκ, e⟩ := (hmemK _).1 hk
        refine ⟨⟨γ, hγ⟩, ⟨k, hk, κ, hκ, ?_⟩, rfl⟩
        calc γ * h i = h i * ((h i)⁻¹ * γ * h i) := by group
          _ = h i * k * κ := by rw [e, mul_assoc]
      · rintro ⟨γ, ⟨k, hk, κ, hκ, e⟩, rfl⟩
        refine ⟨γ.2, (hmemK _).2 ⟨k, hk, κ, hκ, ?_⟩⟩
        calc (h i)⁻¹ * γ.1 * h i = (h i)⁻¹ * (γ.1 * h i) := by group
          _ = k * κ := by rw [e]; group
    rw [hs, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
    rfl
  refine ⟨by rw [hvol]; exact ENNReal.toReal_pos hKpos.ne' hKfin, fun a => ?_, ?_⟩
  · rw [← hst]
    exact (Set.ncard_pos (hfin a)).mpr ⟨1, (GQ V).one_mem, by simpa using K.one_mem⟩
  intro Φ hΦc hΦl hΦr
  obtain ⟨-, he⟩ := GlobalTheory.integral_fundamentalDomain_eq_sum_doubleCoset_avg (GA D V) v.μ (GQ V) K U v.𝓕 v.fund hKo hKfin
    (GinfC V) ν (GinfC V).subtype continuous_subtype_val
    (fun k hk => by
      obtain ⟨a, ha, κ, hκ, rfl⟩ := (hmemK _).1 hk
      exact ⟨κ, hκ, ⟨a, ha⟩, hcf ha (hU.le hκ)⟩)
    (fun k hk w => (hcf w.2 (hU.le hk)).symm) cl h huniq hfin Φ hΦc hΦl hΦr
  rw [he, hvol]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hst i]
  rfl

end GlobalTheory.SeeSaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOSourceSlice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOSourceSlice
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixModel.OrthDec

theorem isThetaFunO_slice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L)
    (f : WO S T → ℂ) (y : WO L T), IsThetaFunO ψ S T f →
      IsThetaFunO ψ A T (fun w => f ((o.resS T).symm (w, y))) :=
  fun _ _ _ _ _ _ o _ y hf => GlobalTheory.BoxSlice.isThetaFunO_slice_left o hf y

end GlobalTheory.MixModel.OrthDec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOSourceSliceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunO_source_slice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (f : WO S T → ℂ) (y : WO L T), IsThetaFunO ψ S T f → IsThetaFunO ψ A T (fun w => f ((o.resS T).symm (w, y))) := by
  first | exact @GlobalTheory.MixModel.OrthDec.isThetaFunO_slice | exact GlobalTheory.MixModel.OrthDec.isThetaFunO_slice | (intros; apply GlobalTheory.MixModel.OrthDec.isThetaFunO_slice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroLeftMemCoreLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroLeftMemCoreLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ContrComb

theorem extL_mem_latO : ∀ (D : D7) (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (P : Pl D → Prop) (LA : Lat A) (LS : Lat S) (M : Lat V₀), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC V₀ M → (∀ v, P v → ∃ LL, OrthAt o M LA LL v) → ∀ u ∈ latO A S (LA : Set _) (LS : Set _) P, (o.resS S).symm (u, 0) ∈ latO V₀ S (M : Set _) (LS : Set _) P := by
  intro D V₀ A L S o P LA LS M hA hS hM hO u hu
  rw [GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D A S LA LS hA hS P u] at hu
  obtain ⟨huP, huL⟩ := hu
  rw [GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D V₀ S M LS hM hS P, OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
  have hloc := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (huP i k)
  · have hy' := ((hloc V₀).2.2.2 M y hM.1).1 hy
    have hp : o.pA *ᵥ y ∈ latV A LA P := by
      refine ((hloc A).2.2.2 LA (o.pA *ᵥ y) hA.1).2 ⟨fun i => ?_, fun v hv e he => ?_⟩
      · rw [Matrix.mulVec, dotProduct]
        exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hy'.1 k)
      · obtain ⟨LL, hLL⟩ := hO v hv
        have h1 := ((hLL (e • y)).1 (hy'.2 v hv e he)).1
        rwa [Matrix.mulVec_smul] at h1
    have h2 := huL _ hp
    change (u * o.pA) *ᵥ y ∈ latA S LS P
    rwa [← Matrix.mulVec_mulVec]

end GlobalTheory.ContrComb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroLeftMemCoreLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendByZero_left_mem_core_lattice : ∀ (D : D7) (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (P : Pl D → Prop) (LA : Lat A) (LS : Lat S) (M : Lat V₀), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC V₀ M → (∀ v, P v → ∃ LL, OrthAt o M LA LL v) → ∀ u ∈ latO A S (LA : Set _) (LS : Set _) P, (o.resS S).symm (u, 0) ∈ latO V₀ S (M : Set _) (LS : Set _) P := by
  first | exact @GlobalTheory.ContrComb.extL_mem_latO | exact GlobalTheory.ContrComb.extL_mem_latO | (intros; apply GlobalTheory.ContrComb.extL_mem_latO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceUniformiserIdeleValueUnramifiedChar
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceUniformiserIdeleValueUnramifiedChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)

noncomputable section

namespace GlobalTheory.SplitUnifIdele

theorem value_eq_val : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsSplit (E := D.host.E) v → ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → ∃ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e w ∧ ϖ ∈ w.asIdeal ∧ ϖ ∉ w.asIdeal ^ 2 ∧ (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) ∧ ∀ χ' : (AE D)ˣ →* Circle, UnrAt χ' w → ((χ' x : Circle) : ℂ) = ((val (F := D.host.F) χ' w : ℂˣ) : ℂ) := by
  intro D v w hw hs χ _
  obtain ⟨e, he⟩ := GlobalTheory.WeilAtPlace.exists_isIdemAt_of_split hs hw
  have hP : IsPrimeIdem w e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have hee : e * e = e := he.1.1
  have hlt : w.asIdeal ^ 2 < w.asIdeal ^ 1 :=
    Ideal.pow_right_strictAnti w.asIdeal w.ne_bot w.isPrime.ne_top (by norm_num : 1 < 2)
  rw [pow_one] at hlt
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt hlt
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := by
    intro h0
    exact h2 (by rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  have hab : incA D (ϖ : D.host.E) * incA D ((ϖ : D.host.E)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hϖ0, map_one]
  have hba : incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) = 1 := by
    rw [mul_comm]; exact hab
  let x : (AE D)ˣ := ⟨e * incA D (ϖ : D.host.E) + (1 - e), e * incA D ((ϖ : D.host.E)⁻¹) + (1 - e),
    by linear_combination (incA D (ϖ : D.host.E) * incA D ((ϖ : D.host.E)⁻¹) - incA D (ϖ : D.host.E)
      - incA D ((ϖ : D.host.E)⁻¹) + 1) * hee + e * hab,
    by linear_combination (incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) - incA D (ϖ : D.host.E)
      - incA D ((ϖ : D.host.E)⁻¹) + 1) * hee + e * hba⟩
  refine ⟨e, ϖ, x, he, h1, h2, rfl, fun χ' hχ' => ?_⟩
  obtain ⟨y, hy, hxy⟩ := GlobalTheory.WeilAtPlace.exists_eq_locIdele (GlobalTheory.WeilAtPlace.isPrimeIdem_infPart hP)
    (GlobalTheory.LFun.finPart_of_isPrimeIdem hP) x (by
      change e * (e * incA D (ϖ : D.host.E) + (1 - e) - 1) = e * incA D (ϖ : D.host.E) + (1 - e) - 1
      linear_combination (incA D (ϖ : D.host.E) - 1) * hee)
  have hy' : (y : w.adicCompletion D.host.E) = algebraMap D.host.E _ (ϖ : D.host.E) := by
    rw [hy, show (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) from rfl,
      GlobalTheory.WeilAtPlace.compAt_cut (GlobalTheory.LFun.finPart_of_isPrimeIdem hP), GlobalTheory.LFun.compAt_incA]
  have hu : Formalism.L2.Host.IsUnifAt w y := by
    unfold Formalism.L2.Host.IsUnifAt
    rw [hy']
    exact (Formalism.UG.P.levelaf_valued_algebraMap _ _).trans
      (GlobalTheory.LFun.EulerTie.valuation_of_mem_notMem_sq w h1 h2)
  have := hχ'.locChar_eq_val hu
  rw [← this, hxy]
  rfl

end GlobalTheory.SplitUnifIdele

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceUniformiserIdeleValueUnramifiedCharStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_uniformiserIdele_value_unramifiedChar : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsSplit (E := D.host.E) v → ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → ∃ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e w ∧ ϖ ∈ w.asIdeal ∧ ϖ ∉ w.asIdeal ^ 2 ∧ (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) ∧ ∀ χ' : (AE D)ˣ →* Circle, UnrAt χ' w → ((χ' x : Circle) : ℂ) = ((val (F := D.host.F) χ' w : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.SplitUnifIdele.value_eq_val | exact GlobalTheory.SplitUnifIdele.value_eq_val | (intros; apply GlobalTheory.SplitUnifIdele.value_eq_val <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIntegrandContinuousPeriodic
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIntegrandContinuousPeriodic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ContrComb

theorem gram_of_lineMap {D : D7} {n m : ℕ} (hm : ∀ i j : Fin m, i = j) (τ : Matrix (Fin n) (Fin m) D.host.E)
    (G : Matrix (Fin n) (Fin n) D.host.E) (G' : Matrix (Fin m) (Fin m) D.host.E) (ζ : Fin n → D.host.E)
    (ζ' : Fin m → D.host.E) (c : D.host.E) (hmap : τ *ᵥ ζ' = -ζ)
    (hnorm : star ζ ⬝ᵥ G *ᵥ ζ = c * (star ζ' ⬝ᵥ G' *ᵥ ζ')) (hne : star ζ' ⬝ᵥ G' *ᵥ ζ' ≠ 0) :
    τᴴ * (G * τ) = c • G' := by
  haveI : Subsingleton (Fin m) := ⟨hm⟩
  have key : ∀ (M : Matrix (Fin m) (Fin m) D.host.E) (i : Fin m), star ζ' ⬝ᵥ M *ᵥ ζ' = star (ζ' i) * (M i i * ζ' i) := by
    intro M i
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_subsingleton _ i, Pi.star_apply]
  have hζ : ζ = -(τ *ᵥ ζ') := by rw [hmap, neg_neg]
  have h1 : star ζ ⬝ᵥ G *ᵥ ζ = star ζ' ⬝ᵥ (τᴴ * (G * τ)) *ᵥ ζ' := by
    rw [hζ, star_neg, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg, Matrix.star_mulVec,
      Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]
  refine Matrix.ext fun i j => ?_
  obtain rfl := hm i j
  rw [h1, key _ i, key _ i] at hnorm
  rw [key _ i] at hne
  have hz : star (ζ' i) * ζ' i ≠ 0 := by
    intro h0; apply hne; rw [mul_left_comm, h0, mul_zero]
  have : star (ζ' i) * ζ' i * ((τᴴ * (G * τ)) i i - c * G' i i) = 0 := by
    rw [mul_sub]; rw [show star (ζ' i) * ζ' i * (τᴴ * (G * τ)) i i = star (ζ' i) * ((τᴴ * (G * τ)) i i * ζ' i) by ring, hnorm]; ring
  rw [Matrix.smul_apply, smul_eq_mul]
  have h3 := sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hz)
  exact h3

end GlobalTheory.ContrComb
end

noncomputable section
namespace GlobalTheory.ContrComb

theorem link_gram {D : D7} {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) :
    l.τᴴ ⬝ (B.L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • B'.L.gram := by
  rw [Int.cast_one, one_mul]
  refine gram_of_lineMap (fun i j => Fin.ext (by have := i.isLt; have := j.isLt; have := B'.line.1; omega))
    l.τ B.L.gram B'.L.gram B.ζ B'.ζ _ l.map l.norm B'.line.2

theorem integrand_cont_per : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S f₁ → IsThetaFunO ψ S B'.V₀ f₂ → Continuous (fun p : Mx D B'.L.rank S.rank × (WO B.A S × WO S B'.A) => f₂ ((B'.o.resT S).symm (p.2.2, p.1)) * f₁ ((B.o.resS S).symm (p.2.1, l.κ S p.1))) ∧ ∀ γ ∈ ratMx D B'.L.rank S.rank, ∀ (w : Mx D B'.L.rank S.rank) (u : WO B.A S) (v : WO S B'.A), f₂ ((B'.o.resT S).symm (v, γ + w)) * f₁ ((B.o.resS S).symm (u, l.κ S (γ + w))) = f₂ ((B'.o.resT S).symm (v, w)) * f₁ ((B.o.resS S).symm (u, l.κ S w)) := by
  intro D ρ σ B B' l S ψ f₁ f₂ h₁ h₂
  obtain ⟨hadd, hcont, hrat, -, hsym, -⟩ :=
    GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 (link_gram l) (l.κ S) (fun _ => rfl)
  refine ⟨?_, ?_⟩
  · exact (h₂.cont.comp ((B'.o.continuous_resT_symm S).comp
      ((continuous_snd.comp continuous_snd).prodMk continuous_fst))).mul
      (h₁.cont.comp ((B.o.continuous_resS_symm S).comp
        ((continuous_fst.comp continuous_snd).prodMk (hcont.comp continuous_fst))))
  · intro γ hγ w u v
    obtain ⟨c₀, hc₀⟩ := hrat γ hγ
    obtain ⟨γ₀, hγ₀⟩ := hγ
    have e₂ : (B'.o.resT S).symm (v, γ + w) = (B'.o.resT S).symm (0, γ) + (B'.o.resT S).symm (v, w) := by
      rw [← map_add (f := _)]; simp
    have q₂ : (B'.o.resT S).symm (0, γ) = ratW B'.V₀ S (B'.o.iB * γ₀) := by
      rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, ← hγ₀]
      show _ = rat _
      rw [rat_mul]; rfl
    have e₁ : (B.o.resS S).symm (u, l.κ S (γ + w)) = (B.o.resS S).symm (0, l.κ S γ) + (B.o.resS S).symm (u, l.κ S w) := by
      rw [hadd, ← map_add (f := _)]; simp
    have q₁ : (B.o.resS S).symm (0, l.κ S γ) = ratW S B.V₀ (c₀ * B.o.qB) := by
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add, ← hc₀]
      show _ = rat _
      rw [rat_mul]; rfl
    have hph : symplOH B.L S (l.κ S γ) (l.κ S w) = -(symplOH S B'.L γ w) := by
      simp only [symplOH, hsym]
      push_cast
      ring
    rw [e₂, e₁, q₂, q₁, h₂.quasi, h₁.quasi, ← q₂, ← q₁, B'.o.symplOH_resT, B.o.symplOH_resS,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      symplOH_zero_left, symplOH_zero_left, zero_add, zero_add, hph, neg_neg]
    have hψ : ψ (-(symplOH S B'.L γ w)) * ψ (symplOH S B'.L γ w) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    linear_combination (f₂ ((B'.o.resT S).symm (v, w)) * f₁ ((B.o.resS S).symm (u, l.κ S w))) * hψ

end GlobalTheory.ContrComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIntegrandContinuousPeriodicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_contraction_integrand_continuous_periodic : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S f₁ → IsThetaFunO ψ S B'.V₀ f₂ → Continuous (fun p : Mx D B'.L.rank S.rank × (WO B.A S × WO S B'.A) => f₂ ((B'.o.resT S).symm (p.2.2, p.1)) * f₁ ((B.o.resS S).symm (p.2.1, l.κ S p.1))) ∧ ∀ γ ∈ ratMx D B'.L.rank S.rank, ∀ (w : Mx D B'.L.rank S.rank) (u : WO B.A S) (v : WO S B'.A), f₂ ((B'.o.resT S).symm (v, γ + w)) * f₁ ((B.o.resS S).symm (u, l.κ S (γ + w))) = f₂ ((B'.o.resT S).symm (v, w)) * f₁ ((B.o.resS S).symm (u, l.κ S w)) := by
  first | exact @GlobalTheory.ContrComb.integrand_cont_per | exact GlobalTheory.ContrComb.integrand_cont_per | (intros; apply GlobalTheory.ContrComb.integrand_cont_per <;> assumption)
end
end
