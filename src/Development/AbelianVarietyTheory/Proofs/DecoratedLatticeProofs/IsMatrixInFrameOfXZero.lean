module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataLocalRelation
public import Formalism.LocalToGlobal.BaseRankEqOfRealisation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerFunctionFockVectorPolynomialGaussian
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialSchwartzKilledByLongAnnihilation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OnePlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace

variable {D : D7} {c : Comm D} {v : VCom c}

def IsMatrixInFrameOfXZero (G : GLoc v) (κ : GA D (c.X 0)) (g : GL (XIx (Fin D.R.k) (Fin D.R.t) 0) G.k) : Prop :=
  (mt (c.X 0) κ).map G.q.pr = (G.FX 0 (Nat.zero_le _)).β * g.val * (G.FX 0 (Nat.zero_le _)).γ

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word}

end GlobalTheory.FamTrace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeIdxUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTraceChiCol


open Classical in
def colLam {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.Forms0 D u) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))
    (g : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : ℂ :=
  if h : ∃ j : Fin 2, (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal then
    Formalism.L2.Forms.lamJ (T.gl.psi0 h.choose v h.choose_spec) (T.gl.chiB h.choose v h.choose_spec) D.R.k D.R.t 0 D.R.k
      (Formalism.L2.Forms.redM D.host.F v (T.gl.mat h.choose v h.choose_spec (T.glev0.fr h.choose v h.choose_spec)
        (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g)))
  else 1

theorem type_idx_unique {D : D7} {v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)} {j j' : Fin 2}
    (h : (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal) (h' : (D.host.g j' : 𝓞 D.host.F) ∈ v.asIdeal) : j' = j := by
  by_contra hne
  have hg : D.host.g j' ≠ D.host.g j := by
    intro e
    rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with hj | hj <;> rcases Fin.exists_fin_two.mp ⟨j', rfl⟩ with hj' | hj' <;>
      subst hj hj' <;> first | exact hne rfl | exact D.host.g_ne e | exact D.host.g_ne e.symm
  have hc : Nat.Coprime (D.host.g j') (D.host.g j) := (Nat.coprime_primes (D.host.g_prime j') (D.host.g_prime j)).2 hg
  obtain ⟨a, b, hab⟩ : IsCoprime (D.host.g j' : ℤ) (D.host.g j : ℤ) := Nat.isCoprime_iff_coprime.2 hc
  have h1 : (1 : 𝓞 D.host.F) ∈ v.asIdeal := by
    have e : ((a * (D.host.g j' : ℤ) + b * (D.host.g j : ℤ) : ℤ) : 𝓞 D.host.F) = 1 := by rw [hab]; simp
    rw [← e]
    push_cast
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ h') (v.asIdeal.mul_mem_left _ h)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem colLam_eq {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.Forms0 D u) {v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)}
    (j : Fin 2) (h : (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal)
    (g : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    colLam T v g = Formalism.L2.Forms.lamJ (T.gl.psi0 j v h) (T.gl.chiB j v h) D.R.k D.R.t 0 D.R.k
      (Formalism.L2.Forms.redM D.host.F v (T.gl.mat j v h (T.glev0.fr j v h) (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) := by
  have hex : ∃ j : Fin 2, (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal := ⟨j, h⟩
  unfold colLam
  rw [dite_eq_left hex]
  have key : ∀ (j' : Fin 2) (h' : (D.host.g j' : 𝓞 D.host.F) ∈ v.asIdeal), j' = j →
      Formalism.L2.Forms.lamJ (T.gl.psi0 j' v h') (T.gl.chiB j' v h') D.R.k D.R.t 0 D.R.k
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat j' v h' (T.glev0.fr j' v h') (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) =
      Formalism.L2.Forms.lamJ (T.gl.psi0 j v h) (T.gl.chiB j v h) D.R.k D.R.t 0 D.R.k
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat j v h (T.glev0.fr j v h) (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) := by
    rintro j' h' rfl; rfl
  exact key _ _ (type_idx_unique h hex.choose_spec)

end GlobalTheory.FamTraceChiCol

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCoordinateVectorsChainSpaceSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCoordinateVectorsChainSpaceSelfDual
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem intVec_isSelfDualC : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (j : ℕ), j ≤ B.R.m →
    ∀ L : Lat ((I.rec7 l Z).sp.X j), (∀ z, z ∈ L ↔ z ∈ intVec (I.rec7 l Z) _) → IsSelfDualC ((I.rec7 l Z).sp.X j) L := by
  intro B X I hI l Z j hj L hL
  have hG : ((I.rec7 l Z).sp.X j).gram = 1 := GlobalTheory.AdForm.PinInhab.gram_X hI j
  have hm : ∀ x : Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E,
      x ∈ Examples₂.stdLat _ ↔ ∀ i, IsIntegral ℤ (x i) := fun x => by
    rw [Examples₂.stdLat, Module.Basis.mem_span_iff_repr_mem]
    exact forall_congr' fun i => ⟨fun ⟨b, hb⟩ => by rw [← show _ = x i from hb]; exact b.2,
      fun h => ⟨⟨_, h⟩, rfl⟩⟩
  have hLe : L = Examples₂.stdLat _ := by
    ext z
    rw [hL z, hm]
    rfl
  subst hLe
  refine ⟨Examples₂.stdLat_isLattice _, fun y => GlobalTheory.Ker.Inhab.selfDual_diag (fun _ => false) _ (fun i k => ?_) y⟩
  rw [hG, Matrix.one_apply]
  simp [Examples₂.sgn]

end GlobalTheory.AdForm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCoordinateVectorsChainSpaceSelfDualStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_coordinate_vectors_chain_space_selfDual : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (j : ℕ), j ≤ B.R.m →
    ∀ L : Lat ((I.rec7 l Z).sp.X j), (∀ z, z ∈ L ↔ z ∈ intVec (I.rec7 l Z) _) → IsSelfDualC ((I.rec7 l Z).sp.X j) L := by
  first | exact @GlobalTheory.AdForm.intVec_isSelfDualC | exact GlobalTheory.AdForm.intVec_isSelfDualC | (intros; apply GlobalTheory.AdForm.intVec_isSelfDualC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopReadOfTrueQ
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.Inhab

open GlobalTheory.SymBridge

section Frames

variable {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]

def stdFr (k : Type) [Field k] (e : Y ≃ Fin N) : GlobalTheory.LocMod.Frame k N Y where
  β := (1 : Matrix (Fin N) (Fin N) k).submatrix id e
  γ := (1 : Matrix (Fin N) (Fin N) k).submatrix e id
  βγ := by rw [Matrix.submatrix_mul_equiv, Matrix.one_mul, Matrix.submatrix_id_id]
  γβ := by
    have h := Matrix.submatrix_mul_equiv (1 : Matrix (Fin N) (Fin N) k) (1 : Matrix (Fin N) (Fin N) k) e (Equiv.refl _) e
    rw [Matrix.one_mul, Matrix.submatrix_one_equiv] at h
    exact h

theorem isStdFr_stdFr {pos : Y → ℕ} {e : Y ≃ Fin N} (h : IsOrd pos e) : IsStdFr pos (stdFr k e) := ⟨e, h, rfl⟩

def blockOrd (κ τ l j : ℕ) : (Fin κ ⊕ Fin l) ⊕ Fin j × Fin τ ≃ Fin (κ + l + j * τ) :=
  (Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv

theorem isOrd_xPos (κ τ j : ℕ) : IsOrd (xPos (κ := κ) (τ := τ) (j := j)) (blockOrd κ τ j j) := by
  rintro ((i | i) | ⟨a, b⟩) <;> simp [blockOrd, xPos, finProdFinEquiv]
  ring

theorem isOrd_zPos (κ τ l j : ℕ) : IsOrd (zPos (κ := κ) (τ := τ) (l := l) (j := j)) (blockOrd κ τ l j) := by
  rintro ((i | i) | ⟨a, b⟩) <;> simp [blockOrd, zPos, finProdFinEquiv]
  ring

end Frames

section True

open GlobalTheory.Mem

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}

end True

section Built

open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) {Rc : Formalism.L2.RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} (y : RealIn a.x Rc S)

end Built

end GlobalTheory.Fam.Inhab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentPowCompletionTrivialAtSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentPowCompletionTrivialAtSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.DiUnit

variable {D : D7}

theorem eq_one_iff {𝔞 : FI D} {v : GlobalTheory.FinPl.Pl D} : idV 𝔞 v = idV 1 v ↔
    ∀ s, s ∈ idV 𝔞 v ↔ incA D (1 : D.host.E)⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v) := by
  simp only [inv_one, map_one, one_mul]
  constructor
  · intro h s
    rw [h, GlobalTheory.SeeSaw.idV_one_eq_intAt]
    exact ⟨fun h => ⟨h, h.1⟩, fun h => h.1⟩
  · intro h
    ext s
    rw [h, GlobalTheory.SeeSaw.idV_one_eq_intAt]
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩

theorem mul_eq_one {𝔞 𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D} (h1 : idV 𝔞 v = idV 1 v) (h2 : idV 𝔟 v = idV 1 v) :
    idV (𝔞 * 𝔟) v = idV 1 v := by
  have := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔞 𝔟 1 1 one_ne_zero one_ne_zero (eq_one_iff.1 h1) (eq_one_iff.1 h2)
  rw [mul_one] at this
  exact eq_one_iff.2 this

theorem pow_eq_one {𝔞 : FI D} {v : GlobalTheory.FinPl.Pl D} (h : idV 𝔞 v = idV 1 v) (n : ℕ) : idV (𝔞 ^ n) v = idV 1 v := by
  induction n with
  | zero => rw [pow_zero]
  | succ n ih => rw [pow_succ]; exact mul_eq_one ih h

theorem inv_eq_one {𝔞 : FI D} {v : GlobalTheory.FinPl.Pl D} (h : idV 𝔞 v = idV 1 v) : idV 𝔞⁻¹ v = idV 1 v := by
  have h0 : 𝔞 ≠ 0 := fun e =>
    GlobalTheory.SeeSaw.LiftModel.idV_ne_bot (one_ne_zero (α := FI D)) v (by rw [← h, e, GlobalTheory.SeeSaw.idV_zero])
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞⁻¹ (inv_ne_zero h0)
  have h1 := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔞 𝔞⁻¹ 1 y one_ne_zero hy0 (eq_one_iff.1 h) hy
  rw [mul_inv_cancel₀ h0, one_mul] at h1
  ext s
  rw [hy, ← h1]

theorem AAbar_eq_one {v : GlobalTheory.FinPl.Pl D} (hA : idV D.host.AA v = idV 1 v) : idV D.host.AAbar v = idV 1 v := by
  ext s
  have h1 := GlobalTheory.SeeSaw.idV_cA_iff D v D.host.AA (cA D s)
  rw [GlobalTheory.SeeSaw.cA_cA, GlobalTheory.SeeSaw.conjFI_AA] at h1
  have h2 := GlobalTheory.SeeSaw.idV_cA_iff D v 1 s
  rw [map_one] at h2
  rw [← h1, hA, h2]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fractionalIdealCompletion_xi0Span_eq_unit_at_splitPlace (p : SplitPt D k) (hp : p.UnitAA) :
    idV (FractionalIdeal.spanSingleton _ D.host.xi0) p.v = idV 1 p.v := by
  have hx : D.host.xi0 ≠ 0 := Formalism.L2.Pj.cmHost_imaginaryGenerator_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  ext s
  rw [GlobalTheory.SeeSaw.idV_one_eq_intAt]
  constructor
  · intro hs
    induction hs using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, hαv, a, ha, rfl⟩ := hy
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 ha
      have e : (pairA D.host.F 0 α ⊗ₜ[D.host.F] (r • D.host.xi0) : AE D) =
          incA D D.host.xi0 * (pairA D.host.F 0 α ⊗ₜ[D.host.F] algebraMap (𝓞 D.host.E) D.host.E r) := by
        rw [GlobalTheory.IdVGen.incA_mul_tmul, Algebra.smul_def, mul_comm (algebraMap (𝓞 D.host.E) D.host.E r)]
      rw [e]
      exact (hp.1 _ (GlobalTheory.IdVGen.gen_mem_intAt hα hαv r)).1
    | zero => exact GlobalTheory.IdVGen.intAt_zero' _
    | add a b _ _ ha hb => exact GlobalTheory.IdVGen.intAt_add' ha hb
    | neg a _ ha => exact GlobalTheory.IdVGen.intAt_neg' ha
  · intro hs
    have h3 := (GlobalTheory.SeeSaw.idV_one_eq_intAt D p.v _).2 (hp.1 s hs).2
    have key : ∀ y ∈ idV (1 : FI D) p.v,
        incA D D.host.xi0 * y ∈ idV (FractionalIdeal.spanSingleton _ D.host.xi0) p.v := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, hαv, a, ha, rfl⟩ := hy
        obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
        rw [GlobalTheory.IdVGen.incA_mul_tmul]
        refine AddSubgroup.subset_closure ⟨α, hα, hαv, _, ?_, rfl⟩
        exact (FractionalIdeal.mem_spanSingleton _).2 ⟨o, by rw [Algebra.smul_def]; exact mul_comm _ _⟩
      | zero => rw [mul_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
      | neg a _ ha => rw [mul_neg]; exact neg_mem ha
    have := key _ h3
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hx, map_one, one_mul] at this

theorem AA_eq_one (p : SplitPt D k) (hp : p.UnitAA) : idV D.host.AA p.v = idV 1 p.v := by
  let L : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1
  let ζ : Fin L.rank → D.host.E := fun _ => 1
  have hζ : ζ ≠ 0 := fun e => one_ne_zero (congrFun e ⟨0, by change 0 < 1; decide⟩)
  have e : GlobalTheory.FinPl.latA L (GlobalTheory.SeeSaw.LiftModel.lineLat L ζ 1) (· = p.v) =
      GlobalTheory.FinPl.latV L (GlobalTheory.SeeSaw.LiftModel.lineLat L ζ D.host.AA) (· = p.v) := by
    unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
    congr 1
    ext y
    constructor
    · rintro ⟨α, h1, h2, a, ha, _, ⟨c, hc, rfl⟩, rfl⟩
      refine ⟨α, h1, h2, 1, rfl, _, ⟨a * c, ?_, rfl⟩, ?_⟩
      · have := FractionalIdeal.mul_mem_mul (S := nonZeroDivisors (𝓞 D.host.E)) (I := D.host.AA) (J := 1) ha hc
        rwa [mul_one] at this
      · funext i; simp [mul_assoc]
    · rintro ⟨α, h1, h2, _, rfl, _, ⟨c, hc, rfl⟩, rfl⟩
      refine ⟨α, h1, h2, c, hc, _, ⟨1, FractionalIdeal.one_mem_one _, rfl⟩, ?_⟩
      funext i; simp
  have key : ∀ s ∈ idAt D (· = p.v), s ∈ idV D.host.AA p.v ↔ s ∈ idV 1 p.v := fun s hs => by
    rw [← GlobalTheory.SeeSaw.LiftModel.lineLatAt_lineLat L hζ D.host.AA p.v s hs,
      ← GlobalTheory.SeeSaw.LiftModel.lineLatAt_lineLat L hζ 1 p.v s hs, ← e, hp.2]
  ext s
  exact ⟨fun h => (key s (GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ s h)).1 h,
    fun h => (key s (GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ s h)).2 h⟩

end GlobalTheory.Core.Mi.LatMatch.DiUnit


open GlobalTheory.Core.Mi.LatMatch.DiUnit in
theorem GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k), p.UnitAA → ∀ (n : ℕ) (a : AE D), (a ∈ idV (dI D ^ n) p.v ↔ a ∈ intAt D (· = p.v)) ∧ (a ∈ idV (dI D ^ n)⁻¹ p.v ↔ a ∈ intAt D (· = p.v)) := by
  intro D k _ _ _ _ p hp n a
  have hd : idV (dI D) p.v = idV 1 p.v := by
    have hA := AA_eq_one p hp
    unfold GlobalTheory.SeeSaw.dI
    exact mul_eq_one (mul_eq_one (fractionalIdealCompletion_xi0Span_eq_unit_at_splitPlace p hp) hA) (AAbar_eq_one hA)
  have h1 := pow_eq_one hd n
  have h2 := inv_eq_one h1
  exact ⟨by rw [h1, GlobalTheory.SeeSaw.idV_one_eq_intAt], by rw [h2, GlobalTheory.SeeSaw.idV_one_eq_intAt]⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentPowCompletionTrivialAtSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseDifferentPow_completion_trivial_at_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k), p.UnitAA → ∀ (n : ℕ) (a : AE D), (a ∈ idV (dI D ^ n) p.v ↔ a ∈ intAt D (· = p.v)) ∧ (a ∈ idV (dI D ^ n)⁻¹ p.v ↔ a ∈ intAt D (· = p.v)) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit | exact GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit | (intros; apply GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulFractionalIdealCompletionSubsetIffMemQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulFractionalIdealCompletionSubsetIffMemQuotient
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdealQuot

theorem intAt_mul {D : D7} {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) := by
  refine ⟨Ideal.mul_mem_right _ _ ha.1, ?_⟩
  rw [map_mul]
  have hx := ha.2
  have hy := hb.2
  generalize finPart D a = x at hx
  generalize finPart D b = y at hy
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, c, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, d, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, c * d, ?_⟩
      · rw [map_mul]; exact mul_mem (ha w) (hb w)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]; push_cast; rfl
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem commRing_rearrange_idempotent_fixed_product {R : Type*} [CommRing R] (Y X P Q ε s : R) (e2 : P * Q = Y * X) (hse : ε * s = s) :
    Y * (s * (X * ε)) = P * (Q * s) := by
  linear_combination (Y * X) * hse - s * e2

theorem commGroup_mul_mul_eq_mul_mul_div {R : Type*} [CommRing R] (Y P Q C s a : R) (e2 : P * Q * C = Y) :
    Y * (s * a) = P * ((Q * s) * (C * a)) := by
  linear_combination (-(s * a)) * e2

theorem unit_of_gen {D : D7} {v : Pl D} {c : D.host.E} (hc : c ≠ 0)
    (h : ∀ s, s ∈ idV (1 : FI D) v ↔ incA D c⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) (t : AE D) :
    (t ∈ intAt D (· = v) → incA D c⁻¹ * t ∈ intAt D (· = v)) ∧
      (t ∈ intAt D (· = v) → incA D c * t ∈ intAt D (· = v)) := by
  refine ⟨fun ht => ((h t).1 ((GlobalTheory.SeeSaw.idV_one_eq_intAt D v t).2 ht)).1, fun ht => ?_⟩
  have h1 : incA D c * t ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ ht.1
  have h2 : incA D c⁻¹ * (incA D c * t) = t := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  exact (GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).1 ((h _).2 ⟨by rw [h2]; exact ht, h1⟩)

theorem mul_subset_iff : ∀ (D : D7) (v : Pl D) (𝔞 𝔟 : FI D), 𝔞 ≠ 0 → 𝔟 ≠ 0 → ∀ s ∈ idAt D (· = v),
    (∀ a ∈ idV 𝔞 v, s * a ∈ idV 𝔟 v) ↔ s ∈ idV (𝔟 * 𝔞⁻¹) v := by
  intro D v 𝔞 𝔟 h𝔞 h𝔟 s hs
  obtain ⟨x, hx, gx⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞 h𝔞
  obtain ⟨y, hy, gy⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔟 h𝔟
  obtain ⟨z, hz, gz⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞⁻¹ (inv_ne_zero h𝔞)
  have gyz := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔟 𝔞⁻¹ y z hy hz gy gz
  have gxz := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔞 𝔞⁻¹ x z hx hz gx gz
  rw [mul_inv_cancel₀ h𝔞] at gxz
  have hxz : x * z ≠ 0 := mul_ne_zero hx hz
  have u := unit_of_gen hxz gxz
  obtain ⟨ε, -, -, hε, hεa, -⟩ := (GlobalTheory.FinPl.localComponents D (· = v)).1
  rw [gyz]
  constructor
  · intro H
    have hxε : incA D x * ε ∈ idV 𝔞 v := by
      refine (gx _).2 ⟨?_, Ideal.mul_mem_left _ _ hε.1⟩
      rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]
    have h1 := ((gy _).1 (H _ hxε)).1
    have e1 : incA D y⁻¹ * (s * (incA D x * ε)) = incA D (x * z) * (incA D (y * z)⁻¹ * s) := by
      have hse : ε * s = s := (hεa s).1 hs
      have e2 : incA D (x * z) * incA D (y * z)⁻¹ = incA D y⁻¹ * incA D x := by
        rw [← map_mul, ← map_mul]; congr 1; field_simp
      exact commRing_rearrange_idempotent_fixed_product _ _ _ _ _ _ e2 hse
    rw [e1] at h1
    refine ⟨?_, hs⟩
    have := (u _).1 h1
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hxz, map_one, one_mul] at this
  · rintro ⟨H, -⟩ a ha
    obtain ⟨ha1, ha2⟩ := (gx a).1 ha
    refine (gy _).2 ⟨?_, Ideal.mul_mem_right _ _ hs⟩
    have e1 : incA D y⁻¹ * (s * a) = incA D (x * z) * ((incA D (y * z)⁻¹ * s) * (incA D x⁻¹ * a)) := by
      have e2 : incA D (x * z) * incA D (y * z)⁻¹ * incA D x⁻¹ = incA D y⁻¹ := by
        rw [← map_mul, ← map_mul]; congr 1; field_simp
      exact commGroup_mul_mul_eq_mul_mul_div _ _ _ _ _ _ e2
    rw [e1]
    exact (u _).2 (intAt_mul H ha1)

end GlobalTheory.IdealQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulFractionalIdealCompletionSubsetIffMemQuotientStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient : ∀ (D : D7) (v : Pl D) (𝔞 𝔟 : FI D), 𝔞 ≠ 0 → 𝔟 ≠ 0 → ∀ s ∈ idAt D (· = v), (∀ a ∈ idV 𝔞 v, s * a ∈ idV 𝔟 v) ↔ s ∈ idV (𝔟 * 𝔞⁻¹) v := by
  first | exact @GlobalTheory.IdealQuot.mul_subset_iff | exact GlobalTheory.IdealQuot.mul_subset_iff | (intros; apply GlobalTheory.IdealQuot.mul_subset_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HypsSatisfiable
noncomputable section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn.Inhab

theorem weil_exists : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ lam : D.host.F, lam ≠ 0 → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∃ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch (shift ψ lam) χ θ V μ ω := by
  intro D n V ψ hψ lam hlam χ hχ hr θ hθ μ 𝓕 hμ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  have hlamE : algebraMap D.host.F D.host.E lam ≠ 0 := (map_ne_zero _).2 hlam
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  set μ' : D.host.E := -D.host.xi0 / algebraMap D.host.F D.host.E lam with hμ'
  have hsk : IsSkew μ' := by
    refine ⟨div_ne_zero (neg_ne_zero.2 hxi) hlamE, ?_⟩
    rw [hμ', star_div₀, star_neg, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, Formalism.IndefR.Eqv.star_algebraMapF]
    ring
  have hl : algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ' := by
    rw [hμ']; field_simp
  obtain ⟨κ, hκ⟩ := GlobalTheory.StdUnn.chart_exists D A μ' hsk
  obtain ⟨hχi, hri⟩ := GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χ V.rank hχ hr
  have hr1 : ResEta D 1 (dblSp A).rank := by
    have := GlobalTheory.Eis.SimplePoleModel.resEta_one_two_mul D A.rank
    convert this using 2
    simp [GlobalTheory.Doubling.dblSp]
    omega
  obtain ⟨omh, homh⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ (dblSp A) V 1 χ⁻¹ hψ
    ⟨continuous_const, fun _ => rfl⟩ hχi hr1 hri
  obtain ⟨omS, hS⟩ := GlobalTheory.StdUnn.exists_transport_std D ψ A V χ⁻¹ omh homh μ 𝓕 hμ θ hθ κ
  refine ⟨omS, ⟨?_, ?_, ?_⟩⟩
  · intro g a hg Φ x
    have := GlobalTheory.StdUnn.transport_levi D ψ A V χ⁻¹ omh homh μ 𝓕 hμ θ hθ μ' hsk κ hκ omS hS lam hl g a hg Φ x
    rw [inv_inv] at this
    exact this
  · intro g b hg Φ x
    exact GlobalTheory.StdUnn.Unip.transport_unip D ψ A V χ⁻¹ omh homh μ 𝓕 hμ θ hθ μ' hsk κ hκ omS hS lam hl g b hg Φ x
  · intro g hg Φ x
    exact GlobalTheory.StdUnn.WeylStd.main D ψ A V χ⁻¹ omh homh μ 𝓕 hμ θ hθ μ' hsk κ hκ omS hS lam hl g hg Φ x

theorem fock_gauss (hg : ∀ (D : D7) (n : ℕ) (V : HSp D) (l : D.what₂.Tau → ℝ), (∀ τ, l τ ≠ 0) → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∃ f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ, ∀ z, f z = gauss V l s (fun τ => Matrix.of (z τ))) : ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ), (∀ τ, l τ ≠ 0) → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ U : Set (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsClopen U → IsCompact U → (0 : Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∈ U → ∃ Φ : schwartzA θ V.rank n, Φ.1 = (fun x => gauss V l s (fun τ => compAt θ τ x) * U.indicator 1 (fun i j => finPart D (x i j))) ∧ Φ.1 ∈ fockA θ V n l s ∧ Φ.1 0 ≠ 0 := by
  intro D n V θ l hl s hs U hUo hUc h0
  obtain ⟨f, hf⟩ := hg D n V l hl s hs
  set g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := U.indicator 1 with hgdef
  have hgSB : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
    refine ⟨?_, ?_⟩
    · exact (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hUo).isLocallyConstant
    · exact HasCompactSupport.intro' hUc hUo.isClosed (fun x hx => Set.indicator_of_notMem hx _)
  have hmem : (fun x : Mx D V.rank n => gauss V l s (fun τ => compAt θ τ x) * g (fun i j => finPart D (x i j))) ∈ schwartzA θ V.rank n := by
    refine Submodule.subset_span ⟨f, g, hgSB, ?_⟩
    funext x
    rw [hf]
    rfl
  refine ⟨⟨_, hmem⟩, rfl, ?_, ?_⟩
  · refine Submodule.subset_span ⟨1, g, hgSB, ?_⟩
    funext x
    simp [evalPoly]
  · show gauss V l s (fun τ => compAt θ τ 0) * g (fun i j => finPart D ((0 : Mx D V.rank n) i j)) ≠ 0
    have h1 : (fun τ => compAt θ τ (0 : Mx D V.rank n)) = fun _ => 0 := by
      funext τ; ext i j; simp [compAt]
    have h2 : (fun i j => finPart D ((0 : Mx D V.rank n) i j)) = 0 := by
      funext i j; simp
    rw [h1, h2, hgdef, Set.indicator_of_mem h0]
    simp [gauss]

end GlobalTheory.StdUnn.Inhab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilDoubledSpaceOfStandardUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilDoubledSpaceOfStandardUnitary
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem sw_doubled_of_std : GlobalTheory.Published.SiegelWeilUnitarySchrodinger → GlobalTheory.Published.SiegelWeilUnitaryConvergent := by
  intro hP D ψ A B hAB hB2 hW χB omh hWe a hMaj _ θ sS sB hθ hsS hsB hK mW 𝓨 hcov ν hν f hf
  obtain ⟨m0, hm0, hp0⟩ := GlobalTheory.T.exists_siegel_parabolic_conj_doubled_compact D
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_standardUnitaryChart_doubledSpace D A m0 hm0
  obtain ⟨p, hp⟩ := hp0 A a hMaj κ hκ
  obtain ⟨lam, hlam, hψ', l, hl, hlabs⟩ := GlobalTheory.T.shiftedAdditiveCharacter_archimedeanParameters D ψ hWe.std θ hθ m0 hm0
  obtain ⟨omS, hT⟩ := GlobalTheory.T.exists_weilDatum_transport_schwartzBruhat_standard D ψ A B χB omh hWe mW 𝓨 hcov θ hθ κ
  obtain ⟨s', hs'std, hs'⟩ := GlobalTheory.T.compactCommuting_cartanInvolution_moved_standard D A m0 hm0 κ hκ a p hp θ hθ sS hsS hK
  have hf' : IsFockVec ψ θ (dblSp A) B s' sB (omh ((p : GA D (dblSp A))⁻¹, 1) f) :=
    GlobalTheory.T.isPolynomialFockThetaVector_weilOperator_cartan D ψ (dblSp A) B 1 χB omh hWe θ hθ sS s' sB _ hs' f hf
  have hschw := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D
  let Φ : schwartzA θ B.rank A.rank :=
    ⟨sch ψ A B mW 𝓨 (omh ((p : GA D (dblSp A))⁻¹, 1) f),
      ((hschw ψ hWe.std θ hθ A B mW 𝓨 hcov).1 _ hf'.1)⟩
  have hΦ : Φ.1 ∈ fockA θ B A.rank l sB :=
    GlobalTheory.T.schroedingerFunction_fockVector_polynomial_gaussian D ψ hWe.std θ hθ A B mW 𝓨 hcov m0 hm0 s' sB hs'std hsB l hlabs _ hf'
  have hχ := GlobalTheory.T.isHeckeChar_restrictionEta_inv D χB B.rank hWe.hecT hWe.resT
  have hWS : IsWeilSch (shift ψ lam) χB⁻¹ θ B mW omS :=
    ⟨GlobalTheory.T.transportedSchrodinger_standardLeviAction D ψ A B χB omh hWe mW 𝓨 hcov θ hθ m0 hm0 κ hκ omS hT lam hlam,
     GlobalTheory.T.transportedSchrodinger_siegelUnipotentAction D ψ A B χB omh hWe mW 𝓨 hcov θ hθ m0 hm0 κ hκ omS hT lam hlam,
     GlobalTheory.T.weyl_formula_standardUnitaryGroup_weilDatum D ψ A B χB omh hWe mW 𝓨 hcov θ hθ m0 hm0 κ hκ omS hT lam hlam⟩
  have hH := GlobalTheory.T.standardUnitaryHeight_isSiegelHeightFunction D A m0 hm0 κ hκ a p hp
  obtain ⟨hInt, hEis, hHol⟩ := hP D A.rank B hAB hB2 hW (shift ψ lam) hψ' χB⁻¹ hχ.1 hχ.2 θ hθ mW 𝓨 hcov omS hWS
    (hgtStd A a κ p) hH l hl sB hsB ν hν Φ hΦ
  obtain ⟨h0, hflat, hact⟩ := GlobalTheory.T.doubledFlatSection_eq_translate_standardSection D ψ A B χB omh hWe mW 𝓨 hcov θ hθ m0 hm0 κ hκ omS hT lam hlam a p f hf.1 Φ rfl
  have hth : ∀ g : GA D (dblSp A), theta omS Φ (κ (g * p)) = fun h => thetaKO omh g h f := fun g => by
    funext h
    rw [GlobalTheory.T.thetaKernel_eq_tsum_schrodingerFunction D ψ A B χB omh hWe mW 𝓨 hcov f hf.1 g h, theta, hact g]
  have hmean : ∀ g : GA D (dblSp A), GlobalTheory.ThetaMean.thetaMean omh ν f g = thetaInt omS ν Φ (κ (g * p)) := fun g => by
    rw [thetaInt, hth g]; rfl
  have hP' := GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D A m0 hm0 κ hκ
  have hG' := GlobalTheory.T.standardUnitaryChart_mem_rational_iff D A m0 hm0 κ hκ
  have Heisenberg₂ := fun (z : ℂ) (hz : (A.rank : ℝ) / 2 < z.re) =>
    GlobalTheory.T.cosetSum_along_mulEquiv_subgroups _ _ κ (siegel A) (GQ (dblSp A)) (P D A.rank) (GF D A.rank) hP' hG'
      (sect omS (hgtStd A a κ p) Φ z) (p : GA D (dblSp A)) (npow (absA D (aP A p)) (sZero A B - z))
      (flat A a (swSec A B omh mW 𝓨 f) (sZero A B) z) (fun g => hflat z g) (hEis z hz).1
  refine ⟨fun g => ?_, ⟨fun z hz => ⟨(Heisenberg₂ z hz).1, fun g => ((Heisenberg₂ z hz).2 g).1 ((hEis z hz).2 _)⟩, fun g => ?_⟩⟩
  · rw [← hth g]; exact hInt _
  · have hr : 0 < absA D (aP A p) := hom_pos _ _
    have := GlobalTheory.T.holomorphicContinuationValue_nnrealPow_factor (fun z => GlobalTheory.Eis.cosetSum (P D A.rank) (GF D A.rank) (sect omS (hgtStd A a κ p) Φ z) (κ (g * p)))
      (GlobalTheory.Eis.eisSer A (flat A a (swSec A B omh mW 𝓨 f) (sZero A B)) g) (s0 B A.rank) _ (absA D (aP A p))
      ((A.rank : ℝ) / 2) hr (hHol (κ (g * p))) (fun z hz => by
        rw [h0]; exact ((Heisenberg₂ z hz).2 g).2)
    rw [h0] at this
    rw [hmean g]
    exact this

end GlobalTheory.StdUnn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilDoubledSpaceOfStandardUnitaryStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeil_doubledSpace_of_standardUnitary : GlobalTheory.Published.SiegelWeilUnitarySchrodinger → GlobalTheory.Published.SiegelWeilUnitaryConvergent := by
  first | exact @GlobalTheory.StdUnn.sw_doubled_of_std | exact GlobalTheory.StdUnn.sw_doubled_of_std | (intros; apply GlobalTheory.StdUnn.sw_doubled_of_std <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitFrameGLFiniteMatrixOffPlaceEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitFrameGLFiniteMatrixOffPlaceEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

namespace GlobalTheory.StabOff

set_option synthInstance.maxHeartbeats 200000

theorem prV_comm_tmul {D : D7} (v : Pl D) (a : Af ↥D.host.F) (e : D.host.E) :
    Formalism.UG.prV (E := D.host.E) v ((Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E) (a ⊗ₜ e)) =
      (Algebra.TensorProduct.comm _ _ _) (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (a ⊗ₜ e)) := by
  rw [Algebra.TensorProduct.comm_tmul]
  simp only [Formalism.UG.prV, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]
  rfl

theorem prV_comm {D : D7} (v : Pl D) (z : Af ↥D.host.F ⊗[↥D.host.F] D.host.E) :
    Formalism.UG.prV (E := D.host.E) v ((Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E) z) =
      (Algebra.TensorProduct.comm _ _ _) (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a e => exact prV_comm_tmul v a e
  | add a b ha hb =>
    simp only [map_add (f := _)]
    exact congrArg₂ (· + ·) ha hb

theorem prV_toEAf_eq_zero {D : D7} (v : Pl D) (y : AE D) (h : FinPl.compAt D v y = 0) :
    Formalism.UG.prV (E := D.host.E) v (toEAf D y) = 0 := by
  unfold FinPl.compAt at h
  unfold toEAf
  simp only [RingHom.comp_apply] at h ⊢
  generalize finPart D y = z at h ⊢
  refine (prV_comm v z).trans ?_
  rw [h, map_zero]

theorem compAt_mt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k) (v : Pl D)
    (hv : v ≠ p.v) (i j : Fin S.rank) :
    FinPl.compAt D v (Formalism.L2.Theta.mt S (β.gl g) i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) = 0 := by
  have hmem : β.gl g ∈ grpAt S (· = p.v) := ((GlobalTheory.T.splitPlaceHermitianFrame_properties D k p S n β).1 _).2 ⟨g, rfl⟩
  unfold grpAt congGrp at hmem
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hmem
  have h1 := congrArg (fun u => u.1 i j) hmem
  simp only [GeneralLinearGroup.map_apply, Units.val_one] at h1
  have h2 : Ideal.Quotient.mk (idAt D (· = p.v)) (Formalism.L2.Theta.mt S (β.gl g) i j) =
      Ideal.Quotient.mk (idAt D (· = p.v)) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) := by
    refine h1.trans ?_
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Ideal.Quotient.eq] at h2
  unfold idAt at h2
  rw [Ideal.mem_inf] at h2
  have h3 := h2.2
  rw [Submodule.mem_iInf] at h3
  exact (RingHom.mem_ker).1 (h3 ⟨v, hv⟩)

theorem bc_prV_finM_eq_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k) (m : ℕ) (hm : S.rank = m) (x : GL (Fin m) (EF D)), x.1 = finM S hm (β.gl g) → ∀ v : Pl D, v ≠ p.v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = 1 := by
  intro D k _ _ _ _ p S n _ _ β g m hm x hx v hv
  apply Units.ext
  ext i j
  change Formalism.UG.prV (E := D.host.E) v (x.1 i j) = (1 : Matrix (Fin m) (Fin m) _) i j
  rw [hx]
  simp only [GlobalTheory.AdForm.finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  have h := prV_toEAf_eq_zero v _ (compAt_mt β g v hv ((finCongr hm).symm i) ((finCongr hm).symm j))
  rw [map_sub, map_sub, sub_eq_zero] at h
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply]
  · have hij' : (finCongr hm).symm i ≠ (finCongr hm).symm j := fun e => hij ((finCongr hm).symm.injective e)
    simp [Matrix.one_apply, hij, hij']

end GlobalTheory.StabOff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitFrameGLFiniteMatrixOffPlaceEqOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitFrameGL_finiteMatrix_offPlace_eq_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k) (m : ℕ) (hm : S.rank = m) (x : GL (Fin m) (EF D)), x.1 = finM S hm (β.gl g) → ∀ v : Pl D, v ≠ p.v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = 1 := by
  first | exact @GlobalTheory.StabOff.bc_prV_finM_eq_one | exact GlobalTheory.StabOff.bc_prV_finM_eq_one | (intros; apply GlobalTheory.StabOff.bc_prV_finM_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFockVectorOfSchrodingerMemFockSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFockVectorOfSchrodingerMemFockSpace
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnnFockRev

theorem killed_of_subfamily {P Q V : Type} [AddCommGroup V] [Module ℂ V] (b : Q → V → V) (ι : P → Q) (T : V → Prop)
    (hb : ∀ q f, T f → T (b q f)) (hT : ∀ (c : ℂ) f, T f → T (c • f))
    (hadd : ∀ q f g, T f → T g → b q (f + g) = b q f + b q g)
    (hsmul : ∀ q (c : ℂ) f, b q (c • f) = c • b q f)
    (hdec : ∀ q, ∃ (p p' : P) (c : ℂ), ∀ f, T f → b q f = b (ι p) f + c • b (ι p') f) (N : ℕ) :
    ∀ f, T f → (∀ l : List P, l.length = N → (l.map ι).foldr b f = 0) →
      ∀ l : List Q, l.length = N → l.foldr b f = 0 := by
  have wT : ∀ (l : List Q) f, T f → T (l.foldr b f) := fun l f hf => by
    induction l with
    | nil => exact hf
    | cons q l ih => exact hb _ _ ih
  have wadd : ∀ (l : List Q) f g, T f → T g → l.foldr b (f + g) = l.foldr b f + l.foldr b g := fun l f g hf hg => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hadd _ _ _ (wT l f hf) (wT l g hg)]; rfl
  have wsmul : ∀ (l : List Q) (c : ℂ) f, l.foldr b (c • f) = c • l.foldr b f := fun l c f => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hsmul]; rfl
  have step : ∀ (M : ℕ) (f : V) (p : P), (∀ l : List P, l.length = M + 1 → (l.map ι).foldr b f = 0) →
      ∀ l : List P, l.length = M → (l.map ι).foldr b (b (ι p) f) = 0 := fun M f p h l hl => by
    have := h (l ++ [p]) (by simp [hl])
    rwa [List.map_append, List.foldr_append] at this
  induction N with
  | zero =>
    intro f _ k l hl
    obtain rfl := List.length_eq_zero_iff.1 hl
    exact k [] rfl
  | succ N ih =>
    intro f hf k l hl
    obtain rfl | ⟨l', q, rfl⟩ := l.eq_nil_or_concat'
    · simp at hl
    have hl' : l'.length = N := by simpa using hl
    obtain ⟨p, p', c, h⟩ := hdec q
    rw [List.foldr_append, List.foldr_cons, List.foldr_nil, h f hf,
      wadd _ _ _ (hb _ _ hf) (hT _ _ (hb _ _ hf)), wsmul,
      ih _ (hb _ _ hf) (step _ _ _ k) l' hl', ih _ (hb _ _ hf) (step _ _ _ k) l' hl', smul_zero, add_zero]

theorem dRho_smul_fun {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (c : ℂ) (f : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (c • f) = c • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f := by
  funext w
  simp only [Formalism.IndefR.Datum.dRho, Pi.smul_apply, smul_eq_mul]
  rw [← deriv_const_mul_field]
  congr 1
  funext t
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem isFockVec_of_sch_mem_fockA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ l : D.what₂.Tau → ℝ, (∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖) → ∀ f, IsThetaFunO ψ (dblSp A) B f → sch ψ A B ν 𝓨 f ∈ fockA θ B A.rank l sB → IsFockVec ψ θ (dblSp A) B s' sB f := by
  intro D ψ hψ θ hθ A B ν 𝓨 hν μ hμ s' sB hs' hsB l hl f hth hf
  obtain ⟨N, hN⟩ := GlobalTheory.T.fockPolynomialSchwartz_killed_by_longAnnihilation D θ hθ B A.rank l sB hsB _ hf
  have key : ∀ L : List (D.what₂.Tau × Matrix (Fin B.rank) (Fin A.rank) ℂ),
      IsThetaFunO ψ (dblSp A) B
        (List.foldr (fun (p : D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) g =>
          annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (s' p.1) (sB p.1)) p.2 g) f
          (L.map (fun q => (q.1, q.2 * (dblDec A).qX.map (tauE D q.1))))) ∧
      sch ψ A B ν 𝓨
        (List.foldr (fun (p : D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) g =>
          annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (s' p.1) (sB p.1)) p.2 g) f
          (L.map (fun q => (q.1, q.2 * (dblDec A).qX.map (tauE D q.1))))) =
        L.foldr (fun q g => annS B l sB θ q.1 q.2 g) (sch ψ A B ν 𝓨 f) := by
    intro L
    induction L with
    | nil => exact ⟨hth, rfl⟩
    | cons q L ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨isThetaFunO_annih_of_std hψ hθ hν _ _ _ ih1, ?_⟩
      rw [List.foldr_cons, ← ih2]
      exact GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair D ψ hψ θ hθ A B ν 𝓨 hν μ hμ s' sB hs' hsB l hl _ ih1 q.1 q.2
  refine ⟨hth, N, ?_⟩
  refine killed_of_subfamily (P := D.what₂.Tau × Matrix (Fin B.rank) (Fin A.rank) ℂ)
    (Q := D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ)
    (fun p g => annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (s' p.1) (sB p.1)) p.2 g)
    (fun q => (q.1, q.2 * (dblDec A).qX.map (tauE D q.1))) (IsThetaFunO ψ (dblSp A) B)
    (fun q g hg => isThetaFunO_annih_of_std hψ hθ hν _ _ _ hg)
    (fun c g hg => (GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hψ A B ν 𝓨 hν g g hg hg c).2.1)
    (fun q g g' hg hg' => ?_) (fun q c g => ?_) (fun q => ?_) N f hth (fun L hL => ?_)
  · simp only [annih]
    rw [GlobalTheory.Core.Rk.FockBox.dRho_add hθ hψ _ _ hg hg', GlobalTheory.Core.Rk.FockBox.dRho_add hθ hψ _ _ hg hg', smul_add]
    abel
  · simp only [annih]
    rw [dRho_smul_fun, dRho_smul_fun, smul_add, smul_comm]
  · obtain ⟨X, X', c, h⟩ := GlobalTheory.T.annihilationOperator_doubledHermitianSpace_decomp D ψ hψ θ hθ A B μ hμ s' sB hs' hsB q.1 q.2
    exact ⟨(q.1, X), (q.1, X'), c, h⟩
  · exact GlobalTheory.T.doubledPairThetaFunction_eq_zero_of_schrodinger_eq_zero D ψ hψ A B ν 𝓨 hν _ (key L).1 ((key L).2.trans (hN L hL))

end GlobalTheory.StdUnnFockRev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFockVectorOfSchrodingerMemFockSpaceStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFockVector_of_schrodinger_mem_fockSpace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ l : D.what₂.Tau → ℝ, (∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖) → ∀ f, IsThetaFunO ψ (dblSp A) B f → sch ψ A B ν 𝓨 f ∈ fockA θ B A.rank l sB → IsFockVec ψ θ (dblSp A) B s' sB f := by
  first | exact @GlobalTheory.StdUnnFockRev.isFockVec_of_sch_mem_fockA | exact GlobalTheory.StdUnnFockRev.isFockVec_of_sch_mem_fockA | (intros; apply GlobalTheory.StdUnnFockRev.isFockVec_of_sch_mem_fockA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupPropertyClosedMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZeroInd

theorem redFn_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) {x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ St β) (hy : y ∈ St β) : redFn β PP (x * y) = redFn β PP x * redFn β PP y := by
  unfold redFn ext1
  rw [dite_eq_left (mul_mem hx hy), dite_eq_left hx, dite_eq_left hy]
  rw [← map_mul]
  congr 1

theorem redFn_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ St β) : redFn β PP x⁻¹ = (redFn β PP x)⁻¹ := by
  unfold redFn ext1
  rw [dite_eq_left (inv_mem hx), dite_eq_left hx]
  rw [← map_inv]
  congr 1

theorem reductionBlock_injective_of_eq {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (hn : n = r) :
    Function.Injective (upperLeftBlock (κ := κ) hr) := by
  subst hn
  intro a b h
  rwa [GlobalTheory.SeeConjRead.restrictedBlock_self_apply, GlobalTheory.SeeConjRead.restrictedBlock_self_apply] at h

end GlobalTheory.LevZeroInd
end
