module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanOneParameterFamilyContinuous
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalGridNodeType
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOMemLatOOfHat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchOperatorUnitaryWSeesaw

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU

noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaLineDer

theorem schwartz_diffQuotient_eval_mul_eq_slope {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (s : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (y : κ → mixedEmbedding.mixedSpace F) (R : ℂ) (t : ℝ) :
    (t⁻¹ • (s t - s 0)) y * R = slope (fun t => s t y * R) 0 t := by
  simp only [slope_def_module, sub_zero, SchwartzMap.smul_apply, SchwartzMap.sub_apply, smul_mul_assoc, sub_mul]

theorem rho_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) {m : ℕ}
    (Φ : Fin m → (Fin n × Fin d → AF F) → ℂ) (hΦ : ∀ i, Φ i ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d)) :
    GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, Φ i)) = ∑ i, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (Φ i)) := by
  have hsum : M.co.rho ψ u (∑ i, Φ i) = ∑ i, M.co.rho ψ u (Φ i) := by
    funext x
    simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Finset.sum_apply, Finset.mul_sum]
  have hmem : ∀ i, M.co.rho ψ u (Φ i) ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun i => GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ u (Φ i) (hΦ i)
  rw [hsum]
  have key := map_sum (GlobalTheory.WeilM.thetaLin F (Fin n × Fin d))
    (fun i => (⟨M.co.rho ψ u (Φ i), hmem i⟩ : GlobalTheory.WeilM.schA F (Fin n × Fin d))) Finset.univ
  simpa only [GlobalTheory.WeilM.thetaLin_apply, Submodule.coe_sum] using key

end GlobalTheory.ThetaLineDer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.RatMoveJets

def RatCoord {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (g : GfC V)
    (U : Matrix.unitaryGroup (Fin V.rank) D.host.E) : Prop :=
  ∃ γ ∈ GQ V, finHom V γ = finHom V (g : GA D V) ∧
    Formalism.L2.Theta.mt V γ = (fr.1 * U.1 * (fr⁻¹ : GL (Fin V.rank) D.host.E).1).map (incA D)

section
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc}

def srcU : ∀ p : GlobalTheory.ChiGrid.Pair T, Matrix.unitaryGroup (Fin (G.V p.small).rank) D.host.E →
    Matrix.unitaryGroup (Fin (G.V p.big).rank) D.host.E → Matrix.unitaryGroup (Fin (G.pS p).rank) D.host.E
  | .chi _ _, _, U' => U'
  | .mu _ _ _, U, _ => U
  | .core _, _, U' => U'
  | .top _ _, U, _ => U

def tgtU : ∀ p : GlobalTheory.ChiGrid.Pair T, Matrix.unitaryGroup (Fin (G.V p.small).rank) D.host.E →
    Matrix.unitaryGroup (Fin (G.V p.big).rank) D.host.E → Matrix.unitaryGroup (Fin (G.pT p).rank) D.host.E
  | .chi _ _, U, _ => U
  | .mu _ _ _, _, U' => U'
  | .core _, U, _ => U
  | .top _ _, _, U' => U'

end

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def JetTh (ch : Choice R) (p : Pair T) (x : FinPt ch.G p.small) (y : FinPt ch.G p.big)
    (Θ : VC D (ch.G.pS p).rank (ch.G.pT p).rank → ℂ) : Prop :=
  ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ)

theorem jetKap_iff (ch : Choice R) (p : Pair T) (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ) :
    GlobalTheory.MovedKappaEx.JetKap ch p x y κ ↔ JetTh ch p x y (fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ)
      (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ)
        (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) :=
  Iff.rfl

end

end GlobalTheory.RatMoveJets
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeProj

section Gen

variable {M ι : Type} [AddCommGroup M] [Module ℂ M]

def typeSpan (ρ : ι → M →ₗ[ℂ] M) (Y₀ G : Submodule ℂ M) : Submodule ℂ M :=
  ⨆ (T : M →ₗ[ℂ] M) (_ : Y₀.map T ≤ G ∧ ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)), Y₀.map T

theorem typeSpan_le (ρ : ι → M →ₗ[ℂ] M) (Y₀ G : Submodule ℂ M) : typeSpan ρ Y₀ G ≤ G :=
  iSup₂_le fun _ h => h.1

theorem le_typeSpan (ρ : ι → M →ₗ[ℂ] M) {Y₀ G : Submodule ℂ M} (h : Y₀ ≤ G) : Y₀ ≤ typeSpan ρ Y₀ G := by
  have h1 : Y₀.map LinearMap.id ≤ typeSpan ρ Y₀ G :=
    le_iSup₂_of_le (f := fun (T : M →ₗ[ℂ] M) (_ : Y₀.map T ≤ G ∧ ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)) => Y₀.map T)
      LinearMap.id ⟨by rwa [Submodule.map_id], fun _ _ _ => rfl⟩ le_rfl
  rwa [Submodule.map_id] at h1

theorem map_le_typeSpan (ρ : ι → M →ₗ[ℂ] M) {Y₀ G : Submodule ℂ M} (T : M →ₗ[ℂ] M) (hT : Y₀.map T ≤ G)
    (hc : ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)) : Y₀.map T ≤ typeSpan ρ Y₀ G :=
  le_iSup₂_of_le (f := fun (T : M →ₗ[ℂ] M) (_ : Y₀.map T ≤ G ∧ ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)) => Y₀.map T)
    T ⟨hT, hc⟩ le_rfl

end Gen

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def rTrL (k : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := rTr V k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rTrL_apply (k : GA D V) (f : GA D V → ℂ) : rTrL k f = rTr V k f := rfl

def KIdx : Type := {p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ // GlobalTheory.CuspGK.InK M p.1 p.2}

def rhoK (i : KIdx M) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) := rTrL (atTau θ V i.1.1 i.1.2)

def KStable (Y : Submodule ℂ (GA D V → ℂ)) : Prop :=
  ∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ f ∈ Y, rTr V (atTau θ V τ g) f ∈ Y

theorem kStable_iff (Y : Submodule ℂ (GA D V → ℂ)) : KStable θ M Y ↔ ∀ i, ∀ y ∈ Y, rhoK θ M i y ∈ Y :=
  ⟨fun h i y hy => h i.1.1 i.1.2 i.2 y hy, fun h τ g hg y hy => h ⟨(τ, g), hg⟩ y hy⟩

theorem kStable_inf {Y Y' : Submodule ℂ (GA D V → ℂ)} (h : KStable θ M Y) (h' : KStable θ M Y') :
    KStable θ M (Y ⊓ Y') :=
  fun τ g hg f hf => ⟨h τ g hg f hf.1, h' τ g hg f hf.2⟩

theorem kStable_gkGen (ψ : GA D V → ℂ) : KStable θ M (GlobalTheory.CuspGK.gkGen θ M ψ) :=
  (GlobalTheory.CuspGK.isGKSub_gkGen θ M ψ).k

theorem kStable_of_isGKSub {A : Submodule ℂ (GA D V → ℂ)} (h : GlobalTheory.CuspGK.IsGKSub θ M A) : KStable θ M A := h.k

end GlobalTheory.KTypeProj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinCoefMultT
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColTypeLift

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

def FinCoef (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (φ : GA D V → ℂ) : Prop :=
  ∀ x, ∃ (n : ℕ) (L : Fin n → (M.H τ →L[ℂ] ℂ)) (v : Fin n → M.H τ),
    (∀ i, SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (v i)) ∧
    ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), φ (x * atTau θ V τ g) = ∑ i, L i (M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) (v i))

theorem FinCoef.zero (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    FinCoef θ M τ 0 := fun _ => ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun g _ => by simp⟩

theorem FinCoef.add {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau}
    {φ ψ : GA D V → ℂ} (h₁ : FinCoef θ M τ φ) (h₂ : FinCoef θ M τ ψ) : FinCoef θ M τ (φ + ψ) := fun x => by
  obtain ⟨n₁, L₁, v₁, hv₁, e₁⟩ := h₁ x
  obtain ⟨n₂, L₂, v₂, hv₂, e₂⟩ := h₂ x
  refine ⟨n₁ + n₂, Fin.append L₁ L₂, Fin.append v₁ v₂, fun i => ?_, fun g hg => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa using hv₁ i
    · simpa using hv₂ i
  · rw [Fin.sum_univ_add, Pi.add_apply, e₁ g hg, e₂ g hg]
    simp

theorem FinCoef.smul {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau}
    {φ : GA D V → ℂ} (c : ℂ) (h : FinCoef θ M τ φ) : FinCoef θ M τ (c • φ) := fun x => by
  obtain ⟨n, L, v, hv, e⟩ := h x
  refine ⟨n, fun i => c • L i, v, hv, fun g hg => ?_⟩
  rw [Pi.smul_apply, e g hg, Finset.smul_sum]
  simp

theorem FinCoef.sum {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau}
    {n : ℕ} {φ : Fin n → GA D V → ℂ} (h : ∀ i, FinCoef θ M τ (φ i)) : FinCoef θ M τ (∑ i, φ i) := by
  classical
  have : ∀ s : Finset (Fin n), FinCoef θ M τ (∑ i ∈ s, φ i) := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using FinCoef.zero θ M τ
    | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih
  exact this Finset.univ

theorem finCoef_lift {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T)
    (z : SmT M) : FinCoef θ M τ (PiTensorProduct.lift T z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    intro x
    obtain ⟨ℓ, -, hℓ⟩ := GlobalTheory.DefiniteEnd.exists_sobCont M τ T f x
    have hsv : SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (f τ : M.H τ) := by
      have hw : ∀ w ∈ M.sm τ, SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) w := by
        intro w hw
        rw [GlobalTheory.SmVec.sm_eq M τ] at hw
        exact hw
      exact hw _ (f τ).2
    refine ⟨1, fun _ => r • LinearMap.toContinuousLinearMap ℓ, fun _ => (f τ : M.H τ), fun _ => hsv, fun g hg => ?_⟩
    have e1 := congrFun (hT.equiv τ g hg f ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩ rfl) x
    have e3 : T f (x * atTau θ V τ g) = ℓ (M.rep τ g (f τ)) := by
      rw [hℓ ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩]
      exact e1.symm
    rw [Fin.sum_univ_one, map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul, e3, LinearMap.coe_toContinuousLinearMap']
    rfl
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact ha.add hb

end GlobalTheory.ColTypeLift

namespace GlobalTheory.ColTypeLift

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

theorem finCoef_multT {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] (F : MultT θ M ∅ 1) (z : SmT M) : FinCoef θ M τ (F.1 z) := by
  have hm : PiTensorProduct.lift.symm F.1 ∈ Mult θ M ∅ 1 := (mem_multT θ M ∅ 1 F.1).1 F.2
  have key : ∀ T ∈ Mult θ M ∅ 1, FinCoef θ M τ (PiTensorProduct.lift T z) := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem x hx => exact finCoef_lift M τ hx z
    | zero => simpa using FinCoef.zero θ M τ
    | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply]; exact hx.add hy
    | smul c x _ hx => rw [map_smul, LinearMap.smul_apply]; exact hx.smul c
  have := key _ hm
  rwa [LinearEquiv.apply_symm_apply] at this

theorem isTypeAt_sum (θ : InfFam D) (N : Node D) (hs : N.V.SigOK) (hd : N.V.IsDefinite) (τ : D.what₂.Tau) {n : ℕ}
    (F : Fin n → N.Cusp θ) (z : Fin n → SmT N.M) : IsTypeAt θ N.V τ (N.S τ) (∑ i, (F i).1 (z i)) := by
  haveI := GlobalTheory.DefiniteEnd.finiteDimensional_model hs hd N.M τ
  exact GlobalTheory.EndCusp.isTypeAt_of_finSum θ N.V τ (N.M.enum τ) (N.M.ds τ) (N.M.fr_unit τ) (N.M.fr_gram τ) _
    (FinCoef.sum fun i => finCoef_multT N.M τ (F i) (z i))

theorem xp_definite {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridPre R} (hG : G.Is)
    (k : ℕ) (hk : k ≤ D.R.m) : (G.Xp k).V.SigOK ∧ (G.Xp k).V.IsDefinite := by
  cases k with
  | zero =>
    have h := hG.spaces.P D.R.m le_rfl
    refine ⟨h.sigOK, fun τ => Or.inl ?_⟩
    rw [h.sig, h.rank]
    simp
  | succ k =>
    have h := hG.spaces.X k hk
    refine ⟨h.sigOK, fun τ => Or.inl ?_⟩
    rw [h.sig, h.rank]
    simp

end GlobalTheory.ColTypeLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasColOfChoice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColMeas

open Matrix
open scoped TensorProduct

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem frame_sub_eq (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E))
    (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    (β⁻¹).1 *ᵥ ((frGL β y).1 *ᵥ v - v) = ((intGL F E n y).1 - 1) *ᵥ ((β⁻¹).1 *ᵥ v) := by
  have e3 : (frGL β y).1 = β.1 * (intGL F E n y).1 * (β⁻¹).1 := rfl
  rw [e3, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]

theorem mem_princGL_iff {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hfr : IsFrame β Λ) (I : Ideal (𝓞 E)) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    x ∈ GlobalTheory.Grid.princGL β I ↔ x ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := F) Λ) ∧
      ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ v - v ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ) := by
  rw [GlobalTheory.Grid.mem_princGL, ← stabilizer_eq_stabilizer_lattice F E n Λ β hfr]
  constructor
  · rintro ⟨y, rfl, hy⟩
    refine ⟨⟨y, rfl⟩, fun v hv => ?_⟩
    rw [GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hfr I, frame_sub_eq]
    intro i
    have hw := (hfr v).1 hv
    simp only [Matrix.mulVec, dotProduct]
    refine GlobalTheory.FrameIdeal.inId_sum _ fun k => ?_
    rw [mul_comm]
    exact GlobalTheory.FrameIdeal.inId_mul (hw k) ⟨_, hy i k, GlobalTheory.LevRedTriv.coe_sub_one_apply y i k⟩
  · rintro ⟨⟨y, rfl⟩, h⟩
    refine ⟨y, rfl, fun i j => ?_⟩
    have h1 := (GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hfr I _).1 (h _ (GlobalTheory.ChainOnto.LStab.col_mem_hatL hfr j)) i
    have e : (β⁻¹).1 *ᵥ (β.1 *ᵥ Pi.single j 1) = Pi.single j (1 : E ⊗[F] Formalism.L2.Herm.Af F) := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [frame_sub_eq, e, Matrix.mulVec_single_one] at h1
    obtain ⟨s, hs, e⟩ := h1
    have : s = (y.1 - 1) i j := Subtype.ext (e.trans (GlobalTheory.LevRedTriv.coe_sub_one_apply y i j).symm)
    exact this ▸ hs

theorem princ_eq_congLev [StarRing E] (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ) (I : Ideal (𝓞 E)) :
    UA hc J ⊓ GlobalTheory.Grid.princGL β I = congLev hc J Λ I := by
  ext x
  rw [Subgroup.mem_inf, mem_princGL_iff hfr, mem_congLev]

end General

end GlobalTheory.ColMeas

end

noncomputable section

namespace GlobalTheory.ColMeas

open GlobalTheory.GridJoin

theorem exists_measDat {D : D7} (N : GlobalTheory.Grid.Node D) {V : HSp D} (hsp : SameSp V N.V)
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hlat : HEq N.Λ Λ) (hfr : IsFrame N.β N.Λ)
    (I : Ideal (𝓞 D.host.E)) {ν : Measure (GA D V)} {fd : Set (GA D V)}
    (hm : Lev.IsMeasFD V (congLev D.sp.cm V.gram Λ I) ν fd) :
    ∃ md : N.MeasDat, HEq md.ν ν ∧ HEq md.fd fd ∧ md.Is False (N.princ I) := by
  obtain ⟨L, h1, h2, e⟩ := hsp
  obtain ⟨V', S, M, Λ', β⟩ := N
  simp only at e hlat hfr ⊢
  subst e
  obtain rfl := eq_of_heq hlat
  refine ⟨⟨ν, fd⟩, HEq.rfl, HEq.rfl, fun h => h.elim, fun _ => ?_⟩
  unfold GlobalTheory.Grid.Node.princ
  rw [princ_eq_congLev _ _ hfr]
  exact hm

end GlobalTheory.ColMeas

end

noncomputable section

namespace GlobalTheory.ColMeas

theorem measCol_of_choice : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)
    (G : GlobalTheory.Grid.GridPre R), G.IsMeas → GlobalTheory.GridJoin.SpMatch G ch.W →
    (∀ i, i ≤ D.R.m → Formalism.L2.DIV.IsFrame (G.V i 0).β (G.V i 0).Λ) → ch.M.IsRow →
    ∃ (m00 : (G.V 0 0).MeasDat) (mV : ∀ i j, (G.nV i j).MeasDat),
      (GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX).IsMeas ∧
      (∀ i, i ≤ D.R.m → HEq ((GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX).measCol i).ν (ch.M.ν (.grid i 0))) ∧
      (∀ i, i ≤ D.R.m → HEq ((GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX).measCol i).fd (ch.M.fd (.grid i 0))) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch G hG hsp hfr hrow
  have H : ∀ i, ∃ md : (G.V i 0).MeasDat, i ≤ D.R.m → HEq md.ν (ch.M.ν (.grid i 0)) ∧
      HEq md.fd (ch.M.fd (.grid i 0)) ∧ md.Is False ((G.V i 0).princ (G.lvl R)) := by
    intro i
    by_cases hi : i ≤ D.R.m
    · have hN := hsp.vert i 0 hi (Nat.zero_le _)
      have hr := hrow.row i hi
      have hne : GlobalTheory.ChiGrid.Node.neg D.R.m (.grid i 0) ≠ 0 := by
        simp only [GlobalTheory.ChiGrid.Node.neg, Nat.sub_zero]
        have := D.R.two_le_m
        omega
      unfold Vol.IsAt at hr
      rw [if_neg hne] at hr
      obtain ⟨md, h1, h2, h3⟩ := exists_measDat (G.V i 0) hN.sp hN.lat (hfr i hi) _ hr
      exact ⟨md, fun _ => ⟨h1, h2, hsp.lvl ▸ h3⟩⟩
    · exact ⟨G.measCol i, fun h => absurd h hi⟩
  choose f hf using H
  refine ⟨f 0, fun i j => match j with | 0 => f (i + 1) | j + 1 => G.mV i (j + 1),
    ⟨fun i hi => ?_, fun i j hi hj => hG.vert i j hi hj, hG.P, hG.X⟩, fun i hi => ?_, fun i hi => ?_⟩
  · cases i <;> exact (hf _ hi).2.2
  · cases i <;> exact (hf _ hi).1
  · cases i <;> exact (hf _ hi).2.1

end GlobalTheory.ColMeas

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFinAtZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.CuspKFin

variable {D : D7}

def KFinAt (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (ψ : GA D N.V → ℂ) : Prop :=
  ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
    (ρ : Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) W),
    GlobalTheory.Published.AutFin.IsContRep ρ ∧ GlobalTheory.Published.AutFin.HasTypeAt θ N.V τ (N.M.ε τ) (N.M.fr τ) ρ ψ

end GlobalTheory.CuspKFin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.Tow

namespace GlobalTheory.Tow

theorem idemAt_orth {D : D7} {P Q : Formalism.L2.DIV.Pl D.host.E} {a b : AE D} (ha : Formalism.L2.NTheta.IsIdemAt a P)
    (hb : Formalism.L2.NTheta.IsIdemAt b Q) (h : P ≠ Q) : a * b = 0 := by

  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have ha0 := GlobalTheory.PlaceModelSum.infPart_split ha.1
  have hda := (GlobalTheory.IdemSupport.tie_iff hΦ ha.1.1 ha0 P).mp ha.2
  have hdb := (GlobalTheory.IdemSupport.tie_iff hΦ hb.1.1 (GlobalTheory.PlaceModelSum.infPart_split hb.1) Q).mp hb.2
  apply hΦ.ext'
  · rw [map_mul, ha0, zero_mul, map_zero]
  · intro R
    rw [GlobalTheory.IdemSupport.ev_mul, GlobalTheory.IdemSupport.ev_zero]
    by_cases hR : R = P
    · rw [hR, hdb.2.2 P h, mul_zero]
    · rw [hda.2.2 R hR, zero_mul]

theorem idemAt_unique {D : D7} {P : Formalism.L2.DIV.Pl D.host.E} {a b : AE D} (ha : Formalism.L2.NTheta.IsIdemAt a P)
    (hb : Formalism.L2.NTheta.IsIdemAt b P) : a = b := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  exact GlobalTheory.IdemSupport.delta_unique hΦ
    ((GlobalTheory.IdemSupport.tie_iff hΦ ha.1.1 (GlobalTheory.PlaceModelSum.infPart_split ha.1) P).mp ha.2)
    ((GlobalTheory.IdemSupport.tie_iff hΦ hb.1.1 (GlobalTheory.PlaceModelSum.infPart_split hb.1) P).mp hb.2)

theorem idemSum_mul_of_subset {D : D7} {e e₂ : AE D} {P P₂ : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : IsIdemSum e P) (h₂ : IsIdemSum e₂ P₂) (hP : P ⊆ P₂) : e₂ * e = e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  obtain ⟨⟨fs, hfs, rfl⟩, -⟩ := h₂
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun R hR => ?_

  rw [Finset.sum_mul, Finset.sum_eq_single_of_mem R (hP hR)]
  · rw [idemAt_unique (hfs R (hP hR)) (hes R hR)]
    exact (hes R hR).1.1
  · intro Q hQ hQR
    exact idemAt_orth (hfs Q hQ) (hes R hR) hQR

end GlobalTheory.Tow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftLowestKTypeCompatibility
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaProjEquiv

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem eq_zero_of_no_lift (R : RealDat D A Ks) (hW : R.models_HW) (hg : R.models_gW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (g : G) (hn : ¬ ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ) (x : (R.HW i σ).H) : x = 0 := by
  have hL : actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) = 0 := by
    ext F h
    show actG0 _ _ _ _ F h = 0
    rw [GlobalTheory.ProjComm.levelGroupAction_eq_zero_of_no_lift hn F]
    rfl
  have h1 : (R.HW i σ).e (R.gW i σ g x) = 0 := by
    rw [hg i σ g x, hL]
    ext v h
    rfl
  have h2 : R.gW i σ g x = 0 := (hW i σ).1 (by rw [h1, map_zero])
  have h3 := congrArg (R.gW i σ g⁻¹) h2
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at h3

theorem realDatum_coeffFlagLevelCharacter_eq_one (R : RealDat D A Ks) (i : Fin D.R.m) (κ : GA D (Wc D i)) :
    levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) κ = 1 := by
  classical
  unfold levChi Formalism.L2.DIV.levFn
  simp [flagL, withP, LevCh.datWp, datY, Formalism.L2.DIV.ext1, Formalism.L2.DIV.LevelP.full]
  exact dite_eq_right_iff.mpr fun _ => rfl

theorem left_abs {H Gf W : Type} [Group H] [Group Gf] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (Γ : Subgroup H)
    (p : H →* Gf) (ρ : H →* Module.End ℂ W) (f : Gf → W) (J : Subgroup Gf) (χ : J →* ℂˣ)
    (hy : f ∈ Bridge.AdForms (p.comp Γ.subtype) (ρ.comp Γ.subtype) J χ) (γ : H) (hγ : γ ∈ Γ) (h : H) :
    ρ (γ * h)⁻¹ (f (p (γ * h))) = ρ h⁻¹ (f (p h)) := by
  have h1 : f (p γ * p h) = ρ γ (f (p h)) := by
    have h0 : f (p γ * p h * 1) = ((χ 1 : ℂˣ) : ℂ) • ρ γ (f (p h)) := hy ⟨γ, hγ⟩ (p h) 1
    simpa using h0
  rw [map_mul p, h1, mul_inv_rev, map_mul ρ, Module.End.mul_apply, ← Module.End.mul_apply (ρ γ⁻¹), ← map_mul ρ,
    inv_mul_cancel, map_one, Module.End.one_apply]

theorem shift_abs {H Gf W : Type} [Group H] [Group Gf] [AddCommGroup W] [Module ℂ W]
    (p : H →* Gf) (ρ : H →* Module.End ℂ W) (κ : H) (hκ : ρ κ⁻¹ = 1) (a : ℂ) (ha : a ≠ 0) (f f' : Gf → W)
    (hy : ∀ h, f' h = a⁻¹ • f (h * p κ)) (h : H) :
    ρ h⁻¹ ((a • f') (p h)) = ρ (h * κ)⁻¹ (f (p (h * κ))) := by
  rw [Pi.smul_apply, hy, smul_smul, mul_inv_cancel₀ ha, one_smul, map_mul p, mul_inv_rev, map_mul ρ,
    Module.End.mul_apply, hκ, Module.End.one_apply]

theorem ext_left {V : HSp D} (c : CoefA V) (f : Bridge.Gf V → c.W) (J : Subgroup (Bridge.Gf V)) (χ : J →* ℂˣ)
    (hy : f ∈ Bridge.AdForms (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) J χ)
    (γ : GA D V) (hγ : γ ∈ GQ V) (h : GA D V) : c.ext f (γ * h) = c.ext f h := by
  show c.ρ (γ * h)⁻¹ (f ((finHom V).rangeRestrict (γ * h))) = c.ρ h⁻¹ (f ((finHom V).rangeRestrict h))
  exact left_abs (GQ V) (finHom V).rangeRestrict c.ρ f J χ hy γ hγ h

theorem ext_shift {V : HSp D} (c : CoefA V) (hc : c.Is) (κ : GA D V) (hκ : κ ∈ GfC V) (a : ℂ) (ha : a ≠ 0)
    (f f' : Bridge.Gf V → c.W) (hy : ∀ h, f' h = a⁻¹ • f (h * (finHom V).rangeRestrict κ)) (h : GA D V) :
    c.ext (a • f') h = c.ext f (h * κ) := by
  show c.ρ h⁻¹ ((a • f') ((finHom V).rangeRestrict h)) = c.ρ (h * κ)⁻¹ (f ((finHom V).rangeRestrict (h * κ)))
  exact shift_abs (finHom V).rangeRestrict c.ρ κ (hc.1 _ (inv_mem hκ)) a ha f f' hy h

theorem extV_left (R : RealDat D A Ks) (hV : R.models_HV) (i : Fin D.R.m) (t : T0) (y : (R.HV i t).H)
    (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) : R.extV i t y (γ * h) = R.extV i t y h := by
  have h3 := LinearMap.mem_range_self (R.HV i t).e y
  rw [(hV i t).2.1] at h3
  show (R.cV i).ext ((R.HV i t).e y) (γ * h) = (R.cV i).ext ((R.HV i t).e y) h
  exact ext_left (R.cV i) _ _ _ h3 γ hγ h

theorem extV_shift (R : RealDat D A Ks) (hc : R.models_cV) (i : Fin D.R.m) (t : T0) (κ : GA D (Vc D i))
    (hκ : κ ∈ GfC (Vc D i)) (c : ℂ) (hc0 : c ≠ 0) (y y' : (R.HV i t).H)
    (hy : ∀ h, (R.HV i t).e y' h = c⁻¹ • (R.HV i t).e y (h * (finHom (Vc D i)).rangeRestrict κ)) (h : GA D (Vc D i)) :
    R.extV i t (c • y') h = R.extV i t y (h * κ) := by
  show (R.cV i).ext ((R.HV i t).e (c • y')) h = (R.cV i).ext ((R.HV i t).e y) (h * κ)
  rw [map_smul]
  exact ext_shift (R.cV i) (hc i) κ hκ c hc0 _ _ hy h

theorem integral_shift (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (g0 : G0 L.Pg L.r)
    (κ : GA D V) (hκ : IsLevelLift V β L g0 κ) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) (𝓕 : Set (GA D V))
    (hfd : IsFundamentalDomain (GQ V) 𝓕 ν) (f : GA D V → ℂ) (hf : ∀ γ ∈ GQ V, ∀ h, f (γ * h) = f h)
    (hi : IntegrableOn f 𝓕 ν) : ∫ h in 𝓕, f (h * κ) ∂ν = ∫ h in 𝓕, f h ∂ν := by
  obtain ⟨htg, hlc, hsc, -, hbo, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  obtain ⟨-, -, -, hct⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  obtain ⟨hK, hlift⟩ := GlobalTheory.ParahoricCompact.isCompact_flag_and_lift V β L
  haveI := htg
  haveI := hlc
  haveI := hsc
  haveI := hbo
  haveI := hct
  haveI := hν
  have hmap := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup ν _ hK κ (hlift g0 κ hκ)
  exact (GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ V) ν 𝓕 hfd κ hmap f hf hi).2

theorem thetaLift_shift {G' H' S' Sinf TK Tau : Type} [Group G'] [Group H'] [MeasurableSpace H']
    [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]
    {ν : Measure H'} {𝓕 : Set H'} {th : G' → H' → S' → ℂ} {pt : Sinf → S'} {io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf}
    {B : Submodule ℂ (H' → Tau)} {thP : B →ₗ[ℂ] (TK →ₗ[ℂ] (G' → ℂ))} (hP : Lift.IsThetaP ν 𝓕 th pt io B thP)
    (Γ : Subgroup H') (k : H') (k' : G') (c : ℂ) (hc : c ≠ 0)
    (hsh : ∀ f : H' → ℂ, (∀ γ ∈ Γ, ∀ h, f (γ * h) = f h) → IntegrableOn f 𝓕 ν →
      ∫ h in 𝓕, f (h * k) ∂ν = ∫ h in 𝓕, f h ∂ν)
    (hl : ∀ P, ∀ γ ∈ Γ, ∀ g h, th g (γ * h) (pt P) = th g h (pt P))
    (hr : ∀ P g h, th (g * k') (h * k) (pt P) = c⁻¹ * th g h (pt P))
    (f f' : B) (hf : ∀ γ ∈ Γ, ∀ h, (f : H' → Tau) (γ * h) = (f : H' → Tau) h)
    (hf' : ∀ h, ((c • f' : B) : H' → Tau) h = (f : H' → Tau) (h * k)) (e : TK) (g : G') :
    thP f' e g = thP f e (g * k') := by
  have hA : thP f e (g * k') = ∫ h in 𝓕, th (g * k') h (pt (io e ((f : H' → Tau) h))) ∂ν :=
    hP.eq f e (g * k')
  have hB : thP (c • f') e g = ∫ h in 𝓕, th g h (pt (io e (((c • f' : B) : H' → Tau) h))) ∂ν :=
    hP.eq (c • f') e g
  have hF := hsh (fun h => th (g * k') h (pt (io e ((f : H' → Tau) h))))
    (fun γ hγ h => by
      rw [hf γ hγ h]
      exact hl _ γ hγ _ _)
    (hP.integ f e (g * k'))
  rw [hA, ← hF]
  simp only [hr]
  rw [integral_const_mul]
  have hfk : ∀ h, (f : H' → Tau) (h * k) = ((c • f' : B) : H' → Tau) h := fun h => (hf' h).symm
  simp only [hfk]
  rw [← hB, map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem thF_type (R : RealDat D A Ks) (hm : R.thP_thF_mem) (i : Fin D.R.m) (t : T0) (y : (R.HV i t).H)
    (v : (R.MW i (sg0 D A)).Vec) : HasType (Wc D i) (R.βW i) (R.datWp i R.triv) (R.thF i t y v) := by
  intro κ hκ h
  have hmem : R.thF i t y ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) := hm i t y
  exact (GlobalTheory.mult_value_left_cont_level R.θ _ _ _ _ hmem v).2.2 κ hκ h

theorem finiteGroup_acts_by_lift_translation_principalType (R : RealDat D A Ks) (i : Fin D.R.m) (g0 : G0 R.Pg D.R.r) (κ' : GA D (Wc D i))
    (hκ' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ') (f : GA D (Wc D i) → ℂ)
    (hT : HasType (Wc D i) (R.βW i) (R.datWp i R.triv) f) (x : GA D (Wc D i)) :
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 f x = f (x * κ') := by
  have hex : ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ := ⟨κ', hκ'⟩
  have hchi : ∀ k, levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1 := by
    intro k
    classical
    unfold levChi Formalism.L2.DIV.levFn
    simp [LevCh.datWp, datY, Formalism.L2.DIV.ext1, Formalism.L2.DIV.LevelP.triv]
    exact dite_eq_right_iff.mpr fun _ => rfl
  have hmem := lift_div_mem hκ' hex.choose_spec
  have hfl : flag1L (R.datWp i R.triv) = R.datWp i R.triv := rfl
  rw [hfl] at hmem
  have hx := hT _ hmem (x * κ')
  rw [hchi, one_mul, ← mul_assoc, mul_inv_cancel_right] at hx
  show actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) g0 f x = f (x * κ')
  unfold actG0
  rw [dite_eq_left hex, realDatum_coeffFlagLevelCharacter_eq_one, inv_one, one_mul]
  exact hx

end GlobalTheory.ThetaProjEquiv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfApprox
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ThLiftCusp

theorem isCuspFun_of_approx {D : D7} (V : HSp D) (f : GA D V → ℂ) (hf : Continuous f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) (N : ℕ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ ψ : GA D V → ℂ, Continuous ψ ∧ (∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) ∧ IsCuspFun V ψ ∧
      ∀ g, ‖ψ g - f g‖ ≤ ε * GlobalTheory.Grow.height V g ^ N) : IsCuspFun V f := by
  choose ψ hψ using fun n : ℕ => h (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  refine GlobalTheory.CuspLimit.isCuspFun_of_tendsto D V N ψ f (fun n => ⟨(hψ n).1, (hψ n).2.1, (hψ n).2.2.1⟩) hf hl ?_
  have hb : ∀ n : ℕ, GlobalTheory.Size.growthSize V N (ψ n - f) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    (GlobalTheory.Size.growthSize_le_iff Nat.one_div_pos_of_nat.le).2 fun g => by simpa using (hψ n).2.2.2 g
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le) hb
  simpa using (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat)

end GlobalTheory.ThLiftCusp

namespace GlobalTheory.ThLiftCusp

theorem norm_lift_sub_le {X H : Type} [MeasurableSpace X] (μ : Measure X) (K K' : H → X → ℂ) (φ φ' : X → ℂ)
    (u : H → ℝ) (w : X → ℝ) (C e δ : ℝ) (hC : 0 ≤ C) (he : 0 ≤ e) (hu : ∀ h, 0 ≤ u h)
    (hK : ∀ h x, ‖K h x‖ ≤ C * u h * w x) (hKK : ∀ h x, ‖K' h x - K h x‖ ≤ e * u h * w x)
    (h1 : Integrable (fun x => w x * ‖φ x‖) μ) (h2 : Integrable (fun x => w x * ‖φ' x - φ x‖) μ)
    (hδ : ∫ x, w x * ‖φ' x - φ x‖ ∂μ ≤ δ)
    (hA : ∀ h, Integrable (fun x => K' h x * φ' x) μ) (hB : ∀ h, Integrable (fun x => K h x * φ x) μ) (h : H) :
    ‖∫ x, K' h x * φ' x ∂μ - ∫ x, K h x * φ x ∂μ‖ ≤ u h * (e * ∫ x, w x * ‖φ x‖ ∂μ + (e + C) * δ) := by
  rw [← integral_sub (hA h) (hB h)]
  have hpt : ∀ x, ‖K' h x * φ' x - K h x * φ x‖ ≤
      u h * (e * (w x * ‖φ x‖) + (e + C) * (w x * ‖φ' x - φ x‖)) := fun x => by
    have e1 : K' h x * φ' x - K h x * φ x =
        (K' h x - K h x) * φ x + (K' h x - K h x) * (φ' x - φ x) + K h x * (φ' x - φ x) := by ring
    rw [e1]
    refine (norm_add₃_le).trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    have a1 := mul_le_mul_of_nonneg_right (hKK h x) (norm_nonneg (φ x))
    have a2 := mul_le_mul_of_nonneg_right (hKK h x) (norm_nonneg (φ' x - φ x))
    have a3 := mul_le_mul_of_nonneg_right (hK h x) (norm_nonneg (φ' x - φ x))
    nlinarith
  have hint : Integrable (fun x => u h * (e * (w x * ‖φ x‖) + (e + C) * (w x * ‖φ' x - φ x‖))) μ :=
    ((h1.const_mul e).add (h2.const_mul (e + C))).const_mul (u h)
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hint
    (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul, integral_add (h1.const_mul e) (h2.const_mul (e + C)), integral_const_mul,
    integral_const_mul]
  exact mul_le_mul_of_nonneg_left (by nlinarith) (hu h)

end GlobalTheory.ThLiftCusp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatHatStabOfHatL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.RowMovedLat

open Matrix

variable {D : D7}

theorem negGA_mem_GfC (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem latHat_stab_of_hatL (V : HSp D) (g : GA D V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (h : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔
      (Formalism.IndefR.Lev.finE V g).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt V g).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) := by
  have key : (fun i => Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E
      ((((Formalism.L2.Theta.mt V g).map (finPart D)).mulVec y) i)) =
      (Formalism.IndefR.Lev.finE V g).val *ᵥ (fun i => Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (y i)) := by
    have hf : (Formalism.IndefR.Lev.finE V g).val = ((Formalism.L2.Theta.mt V g).map (finPart D)).map (Formalism.IndefR.Lev.swapAE D) := by
      ext i j
      rfl
    rw [hf]
    ext i
    exact RingHom.map_mulVec (Formalism.IndefR.Lev.swapAE D) _ y i
  refine (GlobalTheory.SplitFrameColumn.latHat_iff_hatL Λ y).trans ((h _).trans ?_)
  refine Iff.symm ((GlobalTheory.SplitFrameColumn.latHat_iff_hatL Λ _).trans ?_)
  exact Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) key)

end GlobalTheory.RowMovedLat

namespace GlobalTheory.RowMovedLat

theorem moved_pair_stab : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le →
    (G.toPair (.chi j D.R.m) 1 (moved S j k)).1 ∈ GfC (G.pS (.chi j D.R.m)) ∧
    (∀ y, y ∈ latHat D.host.F D.host.E (S.N.latS (.chi j D.R.m) : Set (Fin (G.pS (.chi j D.R.m)).rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt _ (G.toPair (.chi j D.R.m) 1 (moved S j k)).1).map (finPart D)).mulVec y ∈
        latHat D.host.F D.host.E (S.N.latS (.chi j D.R.m) : Set (Fin (G.pS (.chi j D.R.m)).rank → D.host.E))) ∧
    (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2 ∈ GfC (G.pT (.chi (j + 1) D.R.m)) ∧
    (∀ y, y ∈ latHat D.host.F D.host.E (S.N.latT (.chi (j + 1) D.R.m) : Set (Fin (G.pT (.chi (j + 1) D.R.m)).rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2).map (finPart D)).mulVec y ∈
        latHat D.host.F D.host.E (S.N.latT (.chi (j + 1) D.R.m) : Set (Fin (G.pT (.chi (j + 1) D.R.m)).rank → D.host.E))) := by
  intro D T L sc G W U S t _ j hj k hk
  have hG : moved S j k ∈ GfC (G.V (.grid (j + 1) D.R.m)) :=
    (((S.N.u (.grid (j + 1) D.R.m))⁻¹ * k * S.N.u (.grid (j + 1) D.R.m) : FinPt G (.grid (j + 1) D.R.m))).2
  have hst := latHat_stab_of_hatL _ (moved S j k) _ (moved_keeps_std S j hj k hk)
  exact ⟨negGA_mem_GfC _ hG, hst, hG, hst⟩

end GlobalTheory.RowMovedLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairExistenceOfFunctoriality
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PairIt

open GlobalTheory.Chain GlobalTheory.Chain.RealIt

theorem exists_locIt_pair {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} {X : ProvA} (hX : ChosenSeries X)
    (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h2 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X) (hB : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D)
    (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) {aS aT : ℚ}
    (hP : GlobalTheory.PairLift.PairPar (S τ) (S' τ) aS aT) :
    (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ aS aT A := by
  obtain ⟨t, P, P', hS, hS', hc⟩ := hP
  rcases hc with ⟨⟨al, be, ga, de, e1, ⟨hd, e2⟩ | ⟨hd, e2⟩⟩, -⟩ | ⟨al, be, ga, de, e1, ⟨hd, e2⟩ | ⟨hd, e2⟩⟩
  · exact exists_locIt hX h1 h2 hB M M' τ hd (hS.trans (congrArg dualPar e1)) (hS'.trans (congrArg dualPar e2))
  · obtain ⟨hr, A, hA⟩ := GlobalTheory.Chain.RealItLarge.exists_locIt_large hX h1 h2 hB M' M τ hd
      (hS'.trans (congrArg dualPar e2)) (hS.trans (congrArg dualPar e1))
    obtain ⟨A', hA'⟩ := GlobalTheory.T.localFockIntertwiner_adjoint_exchangedPair D W V _ _ M' M τ _ _ A hA
    exact ⟨⟨hr.2, hr.1⟩, A', hA'⟩
  · obtain ⟨hr, A, hA⟩ := exists_locIt hX h1 h2 hB M' M τ hd
      (hS'.trans (congrArg dualPar e1)) (hS.trans (congrArg dualPar e2))
    obtain ⟨A', hA'⟩ := GlobalTheory.T.localFockIntertwiner_adjoint_exchangedPair D W V _ _ M' M τ _ _ A hA
    exact ⟨⟨hr.2, hr.1⟩, A', hA'⟩
  · exact GlobalTheory.Chain.RealItLarge.exists_locIt_large hX h1 h2 hB M M' τ hd
      (hS.trans (congrArg dualPar e2)) (hS'.trans (congrArg dualPar e1))

end GlobalTheory.PairIt

end
end
