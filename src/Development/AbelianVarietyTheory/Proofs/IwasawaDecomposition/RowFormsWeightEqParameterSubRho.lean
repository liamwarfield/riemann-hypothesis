module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbFIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.RatStab

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsWeightEqParameterSubRho
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsWeightEqParameterSubRho
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem tup_sgHC_eq {R : Ranks} (P : HCParam R) (i : Fin (R.N R.m - 1)) :
    Formalism.L2.Forms.sgHC R P i = (RowPar.of P).sgHC i := by
  have hi := i.2
  have hN : R.N R.m = (R.k + R.m) + R.m * R.t := N_eq_blocks R R.m
  unfold Formalism.L2.Forms.sgHC RowPar.sgHC
  congr 1
  by_cases h1 : (i : ℕ) < R.k - 1
  · rw [dite_eq_left h1, dite_eq_left h1]
    rfl
  · rw [dite_eq_right h1, dite_eq_right h1]
    have h2 : ((i : ℕ) - (R.k - 1)) / (R.t + 1) < R.m := by
      rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos _)]
      have := R.two_le_m
      have e : R.m * (R.t + 1) = R.m + R.m * R.t := by ring
      have e' : R.m * R.t.succ = R.m * (R.t + 1) := rfl
      omega
    rw [dite_eq_left h2]
    split_ifs with h3
    · simp [RowPar.bAt, h2]
      rfl
    · simp [RowPar.eAt, h2]
      rfl

theorem tup_rowPar_eq (B : Base) (u : B.Word) (τ : Tau B.R) : RowPar.of (B.hcW u τ) = RowPar.of (B.hc τ) := by
  unfold RowPar.of
  rw [B.hcW_v, B.hcW_b, B.hcW_e]

theorem fm_sg_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ τ (i : Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)), (((I.fm l u a).sg τ).w i : ℚ) = Formalism.L2.Forms.sgHC (I.rec7 l Z).R ((I.rec7 l Z).hcW u τ) i - rhoVec ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) i := by
  intro B X I hI hP l Z u a τ i
  have h2 := (tup_sgHC_eq (B.hcW u τ) i).trans (congrArg (fun P => RowPar.sgHC P i) (tup_rowPar_eq B u τ))
  exact (RowPar.sg_eq (B.hc τ) i).trans (congrArg (· - _) h2.symm)

end GlobalTheory.Mem.Col2.TC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsWeightEqParameterSubRhoStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowForms_weight_eq_parameter_sub_rho : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ τ (i : Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)), (((I.fm l u a).sg τ).w i : ℚ) = Formalism.L2.Forms.sgHC (I.rec7 l Z).R ((I.rec7 l Z).hcW u τ) i - rhoVec ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) i := by
  first | exact @GlobalTheory.Mem.Col2.TC.fm_sg_eq | exact GlobalTheory.Mem.Col2.TC.fm_sg_eq | (intros; apply GlobalTheory.Mem.Col2.TC.fm_sg_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BranchingNormIdentityTrueColumnsMembers
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem cTw_eq_mul (B : Base) :
    ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) = (B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ) := by
  obtain ⟨b, hb⟩ := B.R.t_odd
  have h2 : B.R.t + 1 = 2 * (b + 1) := by omega
  rw [h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.mul_left_comm,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  push_cast
  ring

theorem trueWeight_lastStep_trueColumns {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (τ : (I.rec7 l Z).what₂.Tau) : Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ = B.wts.lamTrue u B.R.m τ := by
  have h := cTw_eq_mul B
  show Formalism.MainNotions.product_first_zeroth_parts.wSh (Examples₂.lamOf (B.hcW u τ) B.R.m) (Formalism.MainNotions.product_first_zeroth_parts.cTw B.R) =
    Formalism.L2.Col.shiftW (Examples₂.lamOf (B.hcW u τ) B.R.m) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
  unfold Formalism.MainNotions.product_first_zeroth_parts.wSh Formalism.L2.Col.shiftW Formalism.MainNotions.product_first_zeroth_parts.cTw
  congr 1
  funext i
  rw [h]
  ring

theorem trueRowWeight_trueColumns {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (τ : (I.rec7 l Z).what₂.Tau) : Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ = B.wts.sgTrue τ := by
  have h := cTw_eq_mul B
  show Formalism.MainNotions.product_first_zeroth_parts.wSh (B.wts.row τ).sg (Formalism.MainNotions.product_first_zeroth_parts.cTw B.R) =
    Formalism.L2.Col.shiftW (B.wts.row τ).sg (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
  unfold Formalism.MainNotions.product_first_zeroth_parts.wSh Formalism.L2.Col.shiftW Formalism.MainNotions.product_first_zeroth_parts.cTw
  congr 1
  funext i
  rw [h]
  ring

end GlobalTheory.Mem.Col2.TC

namespace GlobalTheory.Mem.Col2.TC

theorem branchingNorm_identity_trueColumns_members {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    BeOnTie (I.rec7 l Z) u := by
  intro τ
  have e1 := trueWeight_lastStep_trueColumns I l Z u τ
  have e2 := trueRowWeight_trueColumns I l Z u τ
  have n1 : (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ).natW = (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m τ).natW :=
    Formalism.MainNotions.product_first_zeroth_parts.natW_wSh _ _
  have n2 : (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ).natW = (((I.rec7 l Z).fm u).sg τ).natW := Formalism.MainNotions.product_first_zeroth_parts.natW_wSh _ _
  show fockOpNorm (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ)
      (GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ (N_m_succ B.R) (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ)) =
    fockOpNorm (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m τ) (((I.rec7 l Z).fm u).sg τ)
      (Formalism.L2.Ker.brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ)
        (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ))
  rw [e1, e2] at *
  exact fockOpNorm_congr _ n1 n2

theorem beOnTie_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)), ∀ u, BeOnTie (I.rec7 l Z) u :=
  fun I _ _ l Z u => branchingNorm_identity_trueColumns_members I l Z u

end GlobalTheory.Mem.Col2.TC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainComplexFormsEqAlgebraicModularForms
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainComplexFormsEqAlgebraicModularForms
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwP

open GlobalTheory.Mem.Col2.RowTie


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem ptC_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ z : (I.per l u a).Wrow, z ∈ (I.fm l u a).ptC ↔ GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z ∈ FiC K.lev (Formalism.L2.Forms.embT (I.rec7 l Z)) (sgTG (I.fm l u a)) K.y := by
  intro B X I hI hP l Z u a Q K hQ hQ' hR z
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  have hsg : (I.perIn u a).sgT = (sgTG (D := I.rec7 l Z) (I.fm l u a) : B.fields.Tau → DomWeight (B.R.N B.R.m - 1)) := by
    funext τ
    obtain ⟨a, ha⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (a + 1) := by
      rw [ha, show B.R.m * (2 * a + 1 + 1) = 2 * (B.R.m * (a + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = a + 1 := by omega
    show GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) =
      Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ)
    rw [e1, e2]
    unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
    congr 1
  have hc : ∀ c (s : (I.stX a).Stab c) (κ : K.lev.U), (K.y c).1 =
      bc (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (K.stabI c s).1 * (K.y c).1 * κ.1 →
      ((K.lev.chi κ : ℂˣ) : ℂ) = B.embLL (((I.stX a).chr c.1 s.1 : B.LLˣ) : B.LL) := by
    intro c s κ e
    let κ0 : (I.stX a).G c.1 := (1, s.1.2.1, s.1.2.2)
    have hgam : (I.stX a).gam c.1 κ0 = 1 := map_one (ufGL B.fields.E (B.R.N B.R.m - 1))
    have hp := GlobalTheory.Mem.Col2.TilX.isPtOf_rat (hR.pt c) (s.1.1)⁻¹
    have hact : ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
        GLG (E := B.fields.E) (n := B.R.N B.R.m - 1) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) •
        ((I.stX a).rep c).1.1 := by
      have e1 : FrmG.incl _ _ s.1 • ((I.stX a).rep c).1.1 = ((I.stX a).rep c).1.1 :=
        congrArg (fun d : (I.stX a).D c.1 => d.1.1) s.2
      conv_rhs => rw [← e1]
      refine Eq.trans ?_ (smul_smul _ _ _).symm
      have e2 : FrmG.incl _ _ κ0 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
          GLG (E := B.fields.E) (n := B.R.N B.R.m - 1) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) *
          FrmG.incl _ _ s.1 := by
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · exact (inv_mul_cancel _).symm
        · exact (one_mul _).symm
        · exact (one_mul _).symm
      exact congrArg (fun t => t • ((I.stX a).rep c).1.1) e2
    have hst := hR.stab c s
    let yc : GA B (B.R.N B.R.m - 1) := (K.y c).1
    let kk : GA B (B.R.N B.R.m - 1) := κ.1
    have e' : yc = bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1) * yc * kk := by
      have h0 := e
      rw [show (K.stabI c s).1 = (I.stX a).gam c.1 s.1 from hst] at h0
      exact h0
    have hyk : yc * kk = ratAd B.host.F (s.1.1)⁻¹ * yc := by
      have e3 : ratAd B.host.F (s.1.1)⁻¹ =
          (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1))⁻¹ := by
        unfold ratAd
        rw [map_inv, map_inv]
        rfl
      rw [e3]
      conv_rhs => rw [e']
      group
    have hq : PtOf (yc * kk) ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 := by
      rw [hyk, hact]
      exact hp
    exact hR.chr c κ κ0 hgam hq
  letI : Algebra (I.rec7 l Z).host.F B.fields.E := (inferInstance : Algebra (I.rec7 l Z).host.F (I.rec7 l Z).host.E)
  exact mem_Fi_iff (I.stX a) B.fields.emb B.embLL (I.perIn u a).sgT K.lev hemb hsg K.y K.y_bij K.stabI
    (fun c γ => K.stabI_range c γ) (fun c s => hR.stab c s) hc z

end GlobalTheory.Mem.Col2.TwP

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainComplexFormsEqAlgebraicModularFormsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleChain_complexForms_eq_algebraicModularForms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ z : (I.per l u a).Wrow, z ∈ (I.fm l u a).ptC ↔ GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z ∈ FiC K.lev (Formalism.L2.Forms.embT (I.rec7 l Z)) (sgTG (I.fm l u a)) K.y := by
  first | exact @GlobalTheory.Mem.Col2.TwP.ptC_tw | exact GlobalTheory.Mem.Col2.TwP.ptC_tw | (intros; apply GlobalTheory.Mem.Col2.TwP.ptC_tw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricallyIntegralAlgebraicConstantsMemRange
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricallyIntegralAlgebraicConstantsMemRange
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct

namespace GlobalTheory.GeomIntConst

theorem finrank_eq_one_of_isDomain_tensor {F L : Type} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsDomain (L ⊗[F] L)] : Module.finrank F L = 1 := by
  have hinj : Function.Injective (algebraMap L (L ⊗[F] L)) := (algebraMap L (L ⊗[F] L)).injective
  have hT : IsField (L ⊗[F] L) :=
    (Algebra.IsIntegral.isField_iff_isField hinj).1 (Field.toIsField L)
  let f : L ⊗[F] L →ₐ[L] L := Algebra.TensorProduct.lmul'' F
  have hf : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h
    obtain ⟨y, hy⟩ := hT.mul_inv_cancel h
    have := congrArg f hy
    rw [map_mul, hx, zero_mul, map_one] at this
    exact zero_ne_one this
  have hs : Function.Surjective f := fun x => ⟨x ⊗ₜ 1, by
    show Algebra.TensorProduct.lmul'' F (x ⊗ₜ[F] (1 : L)) = x
    first
      | simp [Algebra.TensorProduct.lmul''_apply_tmul]
      | exact (Algebra.TensorProduct.lmul'_apply_tmul (R := F) x (1 : L)).trans (mul_one x)⟩
  have e := (LinearEquiv.ofBijective f.toLinearMap ⟨hf, hs⟩).finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_self] at e
  exact e

theorem mem_range_constFn (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F)
    [GeometricallyIntegral p] (b : Y.functionField)
    (hb : ∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn p) b = 0) :
    b ∈ (GlobalTheory.Cartier.constFn p).range := by
  letI : Algebra F Y.functionField := (GlobalTheory.Cartier.constFn p).toAlgebra
  obtain ⟨P, hP, hPb⟩ := hb
  have hint : IsIntegral F b := (show IsAlgebraic F b from ⟨P, hP, hPb⟩).isIntegral
  obtain ⟨V, hV, s₀, hs₀⟩ := Y.presheaf.exists_germ_eq b
  obtain ⟨U, hU, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hV
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  let s : Γ(Y, U) := resG Y hUV s₀
  have hs : GlobalTheory.Cartier.fnOf U hxU s = b := by
    rw [GlobalTheory.Cartier.fnOf_resG]; exact hs₀
  letI : Algebra F Γ(Y, U) := (algX p U).toAlgebra
  have e : (GlobalTheory.Cartier.fnOf U hxU).comp (algebraMap F Γ(Y, U)) = algebraMap F Y.functionField :=
    GlobalTheory.Cartier.fnOf_comp_algX p U hxU
  have hm : Polynomial.aeval s (minpoly F b) = 0 := by
    apply GlobalTheory.Cartier.fnOf_injective U hxU
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂, e, hs, ← Polynomial.aeval_def,
      minpoly.aeval]
  haveI : Fact (Irreducible (minpoly F b)) := ⟨minpoly.irreducible hint⟩
  let φ : AdjoinRoot (minpoly F b) →ₐ[F] Γ(Y, U) := AdjoinRoot.liftAlgHom (minpoly F b) (Algebra.ofId F Γ(Y, U)) s
    (by rw [Polynomial.aeval_def] at hm; exact hm)
  have hφ : Function.Injective φ := φ.toRingHom.injective

  let g := Spec.map (CommRingCat.ofHom (algebraMap F (AdjoinRoot (minpoly F b))))
  have hg : hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F Γ(Y, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hYL : IsIntegral (pullback p g) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback p g)
  have : Surjective g := ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have : Nonempty ((pullback hU.fromSpec (pullback.fst p g) : Scheme.{0})) := by
    obtain ⟨z, -⟩ : genericPoint Y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
    have hz : z ∈ Set.range (pullback.fst hU.fromSpec (pullback.fst p g)) := by
      rw [Scheme.Pullback.range_fst]; exact (pullback.fst p g).surjective _
    exact ⟨hz.choose⟩
  haveI := hU.isOpenImmersion_fromSpec
  have : IsIntegral (pullback hU.fromSpec (pullback.fst p g)) :=
    isIntegral_of_isOpenImmersion (pullback.snd hU.fromSpec (pullback.fst p g))
  have : IsIntegral (pullback (hU.fromSpec ≫ p) g) :=
    IsIntegral.of_isIso (pullbackRightPullbackFstIso p g hU.fromSpec).hom
  rw [hg] at this
  have : IsIntegral (Spec (.of (Γ(Y, U) ⊗[F] AdjoinRoot (minpoly F b)))) :=
    IsIntegral.of_isIso (pullbackSpecIso F Γ(Y, U) (AdjoinRoot (minpoly F b))).hom
  have : IsDomain (Γ(Y, U) ⊗[F] AdjoinRoot (minpoly F b)) :=
    (affine_isIntegral_iff (.of (Γ(Y, U) ⊗[F] AdjoinRoot (minpoly F b)))).mp this

  have hinj : Function.Injective (Algebra.TensorProduct.map φ
      (AlgHom.id F (AdjoinRoot (minpoly F b)))) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := AdjoinRoot (minpoly F b))
      φ.toLinearMap hφ
  have : IsDomain (AdjoinRoot (minpoly F b) ⊗[F] AdjoinRoot (minpoly F b)) :=
    Function.Injective.isDomain (Algebra.TensorProduct.map φ
      (AlgHom.id F (AdjoinRoot (minpoly F b)))).toRingHom hinj
  have hm0 : minpoly F b ≠ 0 := minpoly.ne_zero hint
  have : FiniteDimensional F (AdjoinRoot (minpoly F b)) := (AdjoinRoot.powerBasis hm0).finite
  have h1 := finrank_eq_one_of_isDomain_tensor (F := F) (L := AdjoinRoot (minpoly F b))
  rw [(AdjoinRoot.powerBasis hm0).finrank, AdjoinRoot.powerBasis_dim] at h1
  exact minpoly.natDegree_eq_one_iff.1 h1

end GlobalTheory.GeomIntConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricallyIntegralAlgebraicConstantsMemRangeStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyIntegral_algebraicConstants_mem_range : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) [GeometricallyIntegral p] (b : Y.functionField), (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn p) b = 0) → b ∈ (GlobalTheory.Cartier.constFn p).range := by
  first | exact @GlobalTheory.GeomIntConst.mem_range_constFn | exact GlobalTheory.GeomIntConst.mem_range_constFn | (intros; apply GlobalTheory.GeomIntConst.mem_range_constFn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompanionCrd
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.MemLat

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem mem_N_iff (d : Deco E n ST SG) (hd : d.Ok) (π : 𝓞 E) (hmem : ∀ P : ST, π ∈ P.1.asIdeal)
    (hcop : IsCoprime π (cO E π)) (x : Sp E n) :
    x ∈ d.N ↔ ∃ a ∈ d.L, ∃ b ∈ d.Lsh, x = a + cO E π • b := by
  constructor
  · intro hx
    obtain ⟨s, t, hst⟩ := hcop
    refine ⟨s • (π • x), d.L.smul_mem s (hd.smul_N_mem_L hmem hx), t • x, d.Lsh.smul_mem t (hd.N_le_Lsh hx), ?_⟩
    rw [smul_smul, smul_smul, ← add_smul, mul_comm (cO E π) t, hst, one_smul]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact d.N.add_mem (hd.L_le_N ha) (hd.smul_Lsh_mem_N (fun P => by rw [cO_cO]; exact hmem P) hb)

theorem std_of_gram (S : HSpace E) {m : ℕ} (h : S.rank = m) (hg : S.gram.reindex (finCongr h) (finCongr h) = 1) (x y : S.V) :
    stdH E m (Crd.co S h x) (Crd.co S h y) = S.hT x y := by
  subst h
  have hg' : ∀ a b, S.hT (S.frame a) (S.frame b) = if a = b then 1 else 0 := fun a b => by
    have := congrFun (congrFun hg a) b
    simpa [HSpace.gram, Matrix.one_apply] using this
  conv_rhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, LinearMap.sum_apply, hg',
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp [stdH, Crd.co, starRingEnd_apply]

omit [NumberField E] in
theorem hStd_eq_stdH (x y : Fin n → E) : hStd E n x y = stdH E n x y := rfl

theorem mem_dual_crd (S : HSpace E) (co : S.V ≃ₗ[E] (Fin n → E)) (hco : ∀ x y, stdH E n (co x) (co y) = S.hT x y)
    (L : Submodule (𝓞 E) S.V) (b : S.V) :
    b ∈ Formalism.HermitianLatticesTheory.dual S.hT L ↔ co b ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) (L.map ((co : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))) := by
  rw [mem_dual]
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
  constructor
  · intro H z hz
    obtain ⟨a, ha, rfl⟩ := hz
    have := H a ha
    simpa [hStd_eq_stdH, hco] using this
  · intro H a ha
    have := H (co a) ⟨a, ha, rfl⟩
    simpa [hStd_eq_stdH, hco] using this

theorem companion_crd (S : HSpace E) (co : S.V ≃ₗ[E] (Fin n → E)) (hco : ∀ x y, stdH E n (co x) (co y) = S.hT x y)
    (L : Submodule (𝓞 E) S.V) (d : Deco E n ST SG) (hd : d.Ok)
    (hL : L.map ((co : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) = d.L)
    (π : 𝓞 E) (hmem : ∀ P : ST, π ∈ P.1.asIdeal) (hcop : IsCoprime π (cO E π)) (y : S.V) :
    co y ∈ d.N ↔ ∃ a ∈ L, ∃ b ∈ Formalism.HermitianLatticesTheory.dual S.hT L, y = a + star (algebraMap (𝓞 E) E π) • b := by
  have hA : ∀ a, a ∈ L ↔ co a ∈ d.L := fun a => by
    rw [← hL]
    exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨z, hz, e⟩ => co.injective e ▸ hz⟩
  have hB : ∀ b, b ∈ Formalism.HermitianLatticesTheory.dual S.hT L ↔ co b ∈ d.Lsh := fun b => by
    rw [mem_dual_crd S co hco, hL]
    exact Iff.rfl
  have hc : ∀ v : Fin n → E, cO E π • v = star (algebraMap (𝓞 E) E π) • v := fun v => by
    rw [← algebraMap_smul E (cO E π) v, algebraMap_cO]
  rw [mem_N_iff d hd π hmem hcop]
  constructor
  · rintro ⟨a', ha', b', hb', e⟩
    refine ⟨co.symm a', (hA _).2 (by simpa using ha'), co.symm b', (hB _).2 (by simpa using hb'), co.injective ?_⟩
    rw [map_add (f := _), map_smul, co.apply_symm_apply, co.apply_symm_apply, e, hc]
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨co a, (hA a).1 ha, co b, (hB b).1 hb, ?_⟩
    rw [map_add (f := _), map_smul, hc]

end Gen

end GlobalTheory.Mem.Col2.MemLat


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Mem.Col2.TC.memLatAt_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (O : GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).mem u).C), (∀ i c, (O.lat i c).1 = ((I.stp u I.mu0 i).rep c).1.1.deco.1.N) → MemLatAt O (X.piT u) := by
  intro B X I hI hP l Z u O hlat
  obtain ⟨-, -, -, hsp⟩ := spaces_in_coordinates I hI hP l Z
  intro i hi
  obtain ⟨hg, hl0, hL⟩ := hsp i hi
  have hL' := (hL u I.mu0).1
  set co := GlobalTheory.Mem.Col2.Crd.co ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) with hco
  have hiso := GlobalTheory.Mem.Col2.MemLat.std_of_gram _ _ hg
  refine ⟨co, hiso, ?_, ?_⟩
  · intro y
    rw [O.lattice_integral_coordinates]
    have h1 : co y ∈ selfDualLatticeCoords (I.rec7 l Z) i hi ↔ y ∈ ((I.rec7 l Z).sp.X i).L0 :=
      ⟨fun ⟨z, hz, e⟩ => co.injective e ▸ hz, fun h => ⟨y, h, rfl⟩⟩
    rw [← h1, hl0]
    refine forall_congr' fun k => ⟨fun h => ⟨⟨_, h⟩, rfl⟩, ?_⟩
    rintro ⟨r, hr⟩
    rw [← hr]
    exact RingOfIntegers.isIntegral_coe r
  · intro c y
    rw [hlat i c]
    have hsep := sepElt_of_ok l.pr u
    have hmem : ∀ P : (B.primes X).vT u, (B.primes X).piT u ∈ P.1.asIdeal := fun P => by
      have := hsep.conj P
      rwa [cO_cO] at this
    have hLm : ((I.rec7 l Z).clsLat u i c).map ((co : ((I.rec7 l Z).sp.X i).V →ₗ[(I.rec7 l Z).host.E] (Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E)).restrictScalars (𝓞 (I.rec7 l Z).host.E)) =
        (((I.stp u I.mu0 i).rep c).1.1.deco).1.L := hL' c
    refine (GlobalTheory.Mem.Col2.MemLat.companion_crd _ co hiso _ (((I.stp u I.mu0 i).rep c).1.1.deco).1 (((I.stp u I.mu0 i).rep c).1.1.deco).2
      hLm ((B.primes X).piT u) hmem (l.pr.piT_cop u) y).trans ?_
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHalfSelectionSplitPlacesBase
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemPvSet
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.PlaceOverPair

theorem exists_mem_pvSet {R : Ranks} (H : Formalism.BasicNotions.Host R) {p : ℕ} (hp : p.Prime) (𝔭 : HeightOneSpectrum (𝓞 H.K))
    (h𝔭 : (p : 𝓞 H.K) ∈ 𝔭.asIdeal) (v : HeightOneSpectrum (𝓞 H.F)) (hv : OverPF H p v) : ∃ w, w ∈ PvSet H 𝔭 v := by
  obtain ⟨w, h1, h2⟩ := exists_over_both H hp 𝔭 h𝔭 v hv
  refine ⟨w, ?_, h2⟩
  rw [aboveF, Set.Finite.mem_toFinset]
  exact h1

end GlobalTheory.PlaceOverPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHalfSelectionSplitPlacesBase
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.OnePrimeEach

theorem exists_ratPrime_mem {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ w.asIdeal := by
  haveI := w.isMaximal
  haveI : Finite (𝓞 L ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  letI := Ideal.Quotient.field w.asIdeal
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 L ⧸ w.asIdeal)
  refine ⟨p, CharP.char_is_prime (𝓞 L ⧸ w.asIdeal) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem exists_mem_of_prime (L : Type) [Field L] [NumberField L] {p : ℕ} (hp : p.Prime) :
    ∃ P : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ P.asIdeal := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) (Ideal.span {(p : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 L)).injective_int]; exact bot_le)
  have hmem : ((p : ℕ) : 𝓞 L) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 L)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hQ']
      exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hmem⟩
  rintro rfl
  exact (Nat.cast_ne_zero.2 hp.ne_zero) (Ideal.mem_bot.1 hmem)

theorem ratPrime_unique {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpw : (p : 𝓞 L) ∈ w.asIdeal) (hqw : (q : 𝓞 L) ∈ w.asIdeal) : p = q := by
  by_contra hne
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 L))
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpw) (Ideal.mul_mem_left _ _ hqw)

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def ratP (v : HeightOneSpectrum (𝓞 H.F)) : ℕ := (exists_ratPrime_mem v).choose

theorem ratP_prime (v : HeightOneSpectrum (𝓞 H.F)) : (ratP H v).Prime := (exists_ratPrime_mem v).choose_spec.1

theorem ratP_mem (v : HeightOneSpectrum (𝓞 H.F)) : ((ratP H v : ℕ) : 𝓞 H.F) ∈ v.asIdeal :=
  (exists_ratPrime_mem v).choose_spec.2

theorem ratP_eq (v : HeightOneSpectrum (𝓞 H.F)) {p : ℕ} (hp : p.Prime) (h : (p : 𝓞 H.F) ∈ v.asIdeal) :
    ratP H v = p := ratPrime_unique v (ratP_prime H v) hp (ratP_mem H v) h

def primeK (p : ℕ) : HeightOneSpectrum (𝓞 H.K) :=
  if hp : p.Prime then (exists_mem_of_prime H.K hp).choose else (exists_mem_of_prime H.K Nat.prime_two).choose

theorem primeK_mem {p : ℕ} (hp : p.Prime) : ((p : ℕ) : 𝓞 H.K) ∈ (primeK H p).asIdeal := by
  unfold primeK
  rw [dite_eq_left hp]
  exact (exists_mem_of_prime H.K hp).choose_spec

def sel (v : HeightOneSpectrum (𝓞 H.F)) : HeightOneSpectrum (𝓞 H.E) :=
  (GlobalTheory.PlaceOverPair.exists_mem_pvSet H (ratP_prime H v) (primeK H (ratP H v)) (primeK_mem H (ratP_prime H v)) v
    (ratP_mem H v)).choose

theorem sel_mem (v : HeightOneSpectrum (𝓞 H.F)) : sel H v ∈ PvSet H (primeK H (ratP H v)) v :=
  (GlobalTheory.PlaceOverPair.exists_mem_pvSet H (ratP_prime H v) (primeK H (ratP H v)) (primeK_mem H (ratP_prime H v)) v
    (ratP_mem H v)).choose_spec

theorem sel_above (v : HeightOneSpectrum (𝓞 H.F)) : sel H v ∈ aboveF (L := H.E) H.F v := (sel_mem H v).1

theorem sel_under (v : HeightOneSpectrum (𝓞 H.F)) : (sel H v).under (𝓞 H.F) = v := by
  have h := sel_above H v
  rw [aboveF, Set.Finite.mem_toFinset] at h
  exact h

theorem sel_underK (v : HeightOneSpectrum (𝓞 H.F)) : (sel H v).under (𝓞 H.K) = primeK H (ratP H v) := (sel_mem H v).2

theorem sel_mem_of {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 H.F)) (hv : (p : 𝓞 H.F) ∈ v.asIdeal) :
    sel H v ∈ PvSet H (primeK H p) v := by
  have h := sel_mem H v
  rwa [ratP_eq H v hp hv] at h

def splitPlacesTwoPrimes : PlacesOverCommonPrime H :=
  ⟨primeK H H.pde, primeK H H.pde', primeK_mem H H.pde_prime, primeK_mem H H.pde'_prime, fun v _ => sel H v,
    fun v _ => sel H v, fun v hv => sel_mem_of H H.pde_prime v hv, fun v hv => sel_mem_of H H.pde'_prime v hv⟩

end GlobalTheory.Mem.Top.Bl.OnePrimeEach


open GlobalTheory.Mem.Top.Bl.OnePrimeEach in
theorem GlobalTheory.Mem.Top.Bl.exists_half_selection_split_places : ∀ B : Base, ∃ (Pv : HeightOneSpectrum (𝓞 B.host.F) → HeightOneSpectrum (𝓞 B.host.E)) (d : PlacesOverCommonPrime B.host), Formalism.L2.Col.IsSel B.fields Pv ∧ (∀ v, Pv v ∈ aboveF (L := B.host.E) B.host.F v) ∧ Half B Pv ∧ (∀ v hv, Pv v = d.P v hv) ∧ ∀ v hv, Pv v = d.P' v hv := by
  intro B
  refine ⟨sel B.host, splitPlacesTwoPrimes B.host, ?_, sel_above B.host, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro v
    exact congrArg HeightOneSpectrum.asIdeal (sel_under B.host v)
  · intro v v' p hp hv hv'
    rw [sel_underK, sel_underK, ratP_eq B.host v hp hv, ratP_eq B.host v' hp hv']

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHalfSelectionSplitPlacesBaseStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_half_selection_split_places_base : ∀ B : Base, ∃ (Pv : HeightOneSpectrum (𝓞 B.host.F) → HeightOneSpectrum (𝓞 B.host.E)) (d : PlacesOverCommonPrime B.host), Formalism.L2.Col.IsSel B.fields Pv ∧ (∀ v, Pv v ∈ aboveF (L := B.host.E) B.host.F v) ∧ Half B Pv ∧ (∀ v hv, Pv v = d.P v hv) ∧ ∀ v hv, Pv v = d.P' v hv := by
  first | exact @GlobalTheory.Mem.Top.Bl.exists_half_selection_split_places | exact GlobalTheory.Mem.Top.Bl.exists_half_selection_split_places | (intros; apply GlobalTheory.Mem.Top.Bl.exists_half_selection_split_places <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepWeightArithmetic
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepWeightArithmetic
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

namespace GlobalTheory.IntegralityCompare

theorem weight_arith_step : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (μ : I.ι) (i : ℕ), i < B.R.m →
    ∃ k : (I.rec7 l Z).what₂.Tau → ℕ,
      (∀ τ, (k τ : ℤ) = shiftOf (lamTG (I.fm l u μ) i) τ + ((I.rec7 l Z).chTw u μ).sSharp i τ) ∧
      ∀ τ r, nuT (I.rec7 l Z) u i τ r = ((I.fm l u μ).lam i τ).natW r + k τ := by
  intro B X I hOk hPins l Z u μ i hi
  obtain ⟨n, h1, h2, -, -⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ (I.fm l u μ) i hi
  refine ⟨n, fun τ => ?_, fun τ r => ?_⟩
  · rw [← h2 τ]; rfl
  · rw [← h1 τ r]
    unfold lamTG
    rw [natW_shW]
    rfl

end GlobalTheory.IntegralityCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepWeightArithmeticStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainStep_weight_arithmetic : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (μ : I.ι) (i : ℕ), i < B.R.m →
    ∃ k : (I.rec7 l Z).what₂.Tau → ℕ,
      (∀ τ, (k τ : ℤ) = shiftOf (lamTG (I.fm l u μ) i) τ + ((I.rec7 l Z).chTw u μ).sSharp i τ) ∧
      ∀ τ r, nuT (I.rec7 l Z) u i τ r = ((I.fm l u μ).lam i τ).natW r + k τ := by
  exact @GlobalTheory.IntegralityCompare.weight_arith_step
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedEmbeddingMatrixSubstitutionMemRatSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedEmbeddingMatrixSubstitutionMemRatSpan
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

namespace GlobalTheory.IntegralityCompare

open MvPolynomial

theorem twSub_eq_subP (D : D7) {n : ℕ} (M : GL (Fin n) D.host.E) (s : D.what₂.Tau → ℤ)
    (P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :
    twSub (embT D) M s P = C (∏ τ, (embT D τ (M : Matrix (Fin n) (Fin n) D.host.E).det) ^ (s τ)) *
      Formalism.L2.Forms.subP (fun τ => (M : Matrix (Fin n) (Fin n) D.host.E).map (embT D τ)) P := by
  rfl

theorem twSub_mem_ratSpan : ∀ (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (M : GL (Fin n) D.host.E) (s : D.what₂.Tau → ℤ)
    (P0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ),
    P0 ∈ Formalism.L2.Forms.RatSpan D lam → twSub (embT D) M s P0 ∈ Formalism.L2.Forms.RatSpan D lam := by
  classical
  intro D n lam M s P0 hP
  let A : Matrix (Fin n) (Fin n) D.host.E := (M : Matrix (Fin n) (Fin n) D.host.E)
  let ML : D.what₂.Tau → Matrix (Fin n) (Fin n) D.what₂.LL := fun τ => A.map (Formalism.L2.G.Cmp.tEL D τ)
  have hoM : ∀ τ, A.map (embT D τ) = (ML τ).map D.what₂.embLL := fun τ => by
    ext a b
    exact (Formalism.L2.G.Cmp.tEL_emb D τ _).symm
  have hdetA : A.det ≠ 0 := (Matrix.isUnits_det_units M).ne_zero
  have hMdet : ∀ τ, (ML τ).det ≠ 0 := by
    intro τ h
    apply hdetA
    have : Formalism.L2.G.Cmp.tEL D τ A.det = 0 := by
      rw [RingHom.map_det]; exact h
    exact (map_eq_zero _).1 this
  have hc : (∏ τ, (embT D τ A.det) ^ (s τ)) =
      D.what₂.embLL (∏ τ, (ML τ).det ^ s τ) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply, hoM τ, RingHom.map_det D.what₂.embLL, RingHom.mapMatrix_apply]
  rw [twSub_eq_subP]
  show C (∏ τ, (embT D τ A.det) ^ (s τ)) * Formalism.L2.Forms.subP (fun τ => A.map (embT D τ)) P0 ∈ _
  rw [hc, MvPolynomial.C_mul']
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r, f, hf, rfl⟩ := hp
    rw [map_smul, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.substitution_tensor, smul_smul, ← map_mul]
    apply Formalism.L2.GlobalTheoryTheory.LemB.rat_ten D _ Finset.univ
    · intro τ _
      rw [hoM τ]
      exact Formalism.L2.GlobalTheoryTheory.LemB.rat_rowAct_mem D _ (Formalism.L2.DIV.natW_antitone _) (ML τ) (hMdet τ) _
        (Submodule.subset_span ⟨f τ, hf τ, rfl⟩)
    · intro τ hτ
      exact absurd (Finset.mem_univ τ) hτ
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx

end GlobalTheory.IntegralityCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedEmbeddingMatrixSubstitutionMemRatSpanStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedEmbeddingMatrixSubstitution_mem_ratSpan : ∀ (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (M : GL (Fin n) D.host.E) (s : D.what₂.Tau → ℤ)
    (P0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ),
    P0 ∈ Formalism.L2.Forms.RatSpan D lam → twSub (embT D) M s P0 ∈ Formalism.L2.Forms.RatSpan D lam := by
  first | exact @GlobalTheory.IntegralityCompare.twSub_mem_ratSpan | exact GlobalTheory.IntegralityCompare.twSub_mem_ratSpan | (intros; apply GlobalTheory.IntegralityCompare.twSub_mem_ratSpan <;> assumption)
end
end
