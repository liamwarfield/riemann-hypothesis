module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameCoordsMemSelfDualLatticeCoordsIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorCorrespondencePullback
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

namespace GlobalTheory.QPl

variable {D : D7} {c : Comm D} {v : VCom c} {t : Tup c}

def QFam.pinTup (F : QFam v t) (sc cT : ℕ → ℂ) : VTup t where
  Q := Finset.univ.image fun i => (F.Q i).q.v
  sc := sc
  eQ := fun j => if j + 1 < D.R.m then aconv (List.ofFn fun i => (F.Q i).eL j) else 0
  eQT := fun j h => aconv (List.ofFn fun i => (F.Q i).eT j h)
  dQ := fun j α γ => if j < D.R.m then
    (∏ i, (F.Q i).wt j (F.eqv j α i)) • aconv (List.ofFn fun i => (F.Q i).dL j (F.eqv j α i) (F.eqv (j + 1) γ i)) else 0
  ε := fun j α => if (∃ ρ, j + 2 * ρ + 2 = D.R.m) ∨ j = 0 then
    (∏ i, (F.Q i).wt j (F.eqv j α i)) • conv (List.ofFn fun i => (F.Q i).εL j (F.eqv j α i)) else 0
  εT := fun n _ β => Finsupp.single 1 (∏ i, (F.Q i).wt n (F.eqv n β i))
  FX := fun _ _ => Set.univ
  FY := fun j => {f | ∀ i, (F.Q i).Typed j f}
  FT := Set.univ
  cQ := fun j => ∏ i, (((F.Q i).idx (j + 1) : ℂ) * ((F.Q i).idx (j + 1 + 1) : ℂ))⁻¹
  cT := cT

end GlobalTheory.QPl

namespace GlobalTheory.Fam

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}

variable (a : GeoAll W u) (J : ∀ t, QJ a t)

end GlobalTheory.Fam

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepIndexLeS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevProd

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} {a : GeoAll W u} {t : W.P.T}

theorem step_index_le_s (J : QJ a t) (i : Fin J.r) {j : ℕ} (hj : j + 2 ≤ B.R.m) : j ≤ (J.G i).s := by
  have h1 := (J.G i).hs
  change j + 2 ≤ (I.rec7 l Z).R.m at hj
  omega

def phi (J : QJ a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →* ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
  Pi.monoidHom fun i => GlobalTheory.LevIdx.locHom (J.G i).q _ ((J.G i).FX j (by have := step_index_le_s J i hj; omega))

def H (J : QJ a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) (i : Fin J.r) :
    Subgroup (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
  prX (Cgrp (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev j ((J.G i).s - j + 1) (by have := step_index_le_s J i hj; omega)).J
    ((J.E i).rep j ((J.G i).s - j) (Nat.add_sub_cancel' (step_index_le_s J i hj)) (α i)))

def twAt (J : QJ a t) : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop := fun v => ∃ i, (J.G i).q.v = v

def relax (J : QJ a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  (J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (twAt J)) ⊓ GfC _ ⊓
    (Subgroup.pi Set.univ fun i => KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)).comap (phi J j hj)

def Up (a : GeoAll W u) (j : ℕ) (hj : j + 2 ≤ B.R.m) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  if h : ∃ t, ∃ J : QJ a t, J.Reads ∧ Nonempty (J.Ch j) then
    relax h.choose_spec.choose j hj h.choose_spec.choose_spec.2.some
  else ⊥

end GlobalTheory.LevProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepBeforeLastEqSSucc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenBridge

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n]

def toSum0 (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] : GL n k ≃* GL (n ⊕ Fin 0) k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k (Equiv.sumEmpty n (Fin 0)).symm).toMulEquiv

theorem toSum0_val (g : GL n k) :
    ((toSum0 k n g : GL (n ⊕ Fin 0) k) : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) =
      (g : Matrix n n k).reindex (Equiv.sumEmpty n (Fin 0)).symm (Equiv.sumEmpty n (Fin 0)).symm := rfl

end Local

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)}
  {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

theorem step_before_last_eq_s_succ (J : QJ a t) {j : ℕ} (hj : j + 1 = B.R.m) (i : Fin J.r) : j = (J.G i).s + 1 := by
  have h1 := (J.G i).hs
  have h2 : (I.rec7 l Z).R.m = B.R.m := rfl
  have h3 : (GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.m = B.R.m := rfl
  omega

def frJ (J : QJ a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) :
    Frame (J.G i).k ((I.rec7 l Z).sp.X j).rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1)) := by
  subst e
  exact (J.G i).FX _ le_rfl

def rdAt (J : QJ a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →*
      GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k :=
  (toSum0 (J.G i).k _).toMonoidHom.comp (GlobalTheory.LevIdx.locHom (J.G i).q _ (frJ J j i e))

def rd (J : QJ a t) (j : ℕ) (hj : j + 1 = B.R.m) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →*
      ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k) :=
  MonoidHom.pi fun i => rdAt J j i (step_before_last_eq_s_succ J hj i)

def plF (J : QJ a t) (p : GlobalTheory.FinPl.Pl (I.rec7 l Z)) : Prop := ∃ i, (J.G i).q.v = p

end GlobalTheory.PenBridge
end

namespace GlobalTheory.PenBridge

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n]

theorem toSum0_mem_KO_iff (x : GL n k) : toSum0 k n x ∈ KO k (n ⊕ Fin 0) ↔ x ∈ KO k n := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Units.mapEquiv (Matrix.reindexAlgEquiv 𝒪[k] 𝒪[k] (Equiv.sumEmpty n (Fin 0))).toMulEquiv y, ?_⟩
    ext a b
    have := congrArg (fun g : GL (n ⊕ Fin 0) k => (g : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) (Sum.inl a) (Sum.inl b)) hy
    simpa [toSum0_val, Matrix.reindex_apply] using this
  · rintro ⟨y, rfl⟩
    refine ⟨Units.mapEquiv (Matrix.reindexAlgEquiv 𝒪[k] 𝒪[k] (Equiv.sumEmpty n (Fin 0)).symm).toMulEquiv y, ?_⟩
    ext a b
    simp [toSum0_val, Matrix.reindex_apply]

end Local

theorem relIndex_comap_conj {G : Type} [Group G] (H K : Subgroup G) {c : G} (hc : c ∈ K) :
    (H.comap (MulAut.conj c).toMonoidHom).relIndex K = H.relIndex K := by
  rw [Subgroup.relIndex_comap]
  congr 1
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact K.mul_mem (K.mul_mem hc hy) (K.inv_mem hc)
  · intro hx
    exact ⟨c⁻¹ * x * c, K.mul_mem (K.mul_mem (K.inv_mem hc) hx) hc, by group⟩

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)}
  {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

end GlobalTheory.PenBridge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevSph
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TopVol
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}

end GlobalTheory.TopVol

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteLiftCommLevelPrimeOperators
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteLiftCommLevelPrimeOperators
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LiftsAtLevel

variable {D : D7}

theorem combAt_mono {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) {S T : HSp D} {c : WO S T →₀ ℂ} (hc : CombAt P c) :
    CombAt P' c :=
  fun u hu a b => AllBij.idAt_mono h (hc u hu a b)

theorem comb_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hstd : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {c : WO S T →₀ ℂ} (hc : IsFinComb c) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (comb ψ S T c f) φ = comb ψ S T c (pureTensorO ψ θ S T sS sT BS BT f φ) := by
  classical
  have e : ∀ g : WO S T → ℂ, comb ψ S T c g =
      ∑ i, c (c.support.equivFin.symm i) • heisO ψ S T (c.support.equivFin.symm i) g := by
    intro g
    unfold comb
    rw [← Finset.sum_coe_sort c.support]
    exact Fintype.sum_equiv c.support.equivFin _ _ (fun x => by simp)
  have key := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hstd hθ sS sT BS BT f hf c.support.card
    (fun i => c (c.support.equivFin.symm i)) (fun i => (c.support.equivFin.symm i : WO S T))
    (fun i => hc _ (c.support.equivFin.symm i).2) φ).1
  rw [e, e, key]

theorem vac_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {x : DefSp S} {y : DefSp T}
    {f₀ : WO S T → ℂ} (hvac : IsVacO ψ θ S T x.s y.s x.L y.L f₀) (P : Pl D → Prop)
    (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    Vac ψ S T x.L y.L P (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := by
  have hth : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hvac.1 hvac.2.inf x.s x.B y.s y.B hvac.2.theta φ
  have hle : latO S T (x.L : Set _) (y.L : Set _) P ≤ latO S T (x.L : Set _) (y.L : Set _) fun _ => True :=
    GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
  refine ⟨hth φ, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have hu' := hle hu
    exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth (2 • u)
      (GlobalTheory.VacGood.infPart_latO (AddSubgroup.nsmul_mem _ hu' 2)) (hvac.2.lat.1 u hu') φ
  · have hu' := hle hu
    exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth u
      (GlobalTheory.VacGood.infPart_latO hu') (hvac.2.lat.2 e he u hu' hh) φ

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sOp_ram {ι : Type} {p : ι → SplitPt D k} (hinj : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k) (χ₀ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ₀ i) 1) (ε : 𝓀[k]ˣ) (i : ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', RamAt (β i') (Q i') φ) :
    IsContAut S (sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) ε φ) ∧
      ∀ i', RamAt (β i') (Q i') (sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) ε φ) := by
  obtain ⟨hbij, -, c, c', hc, -⟩ := GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k (p i) n q (χ₀ i) (hχ i) _ rfl ε S (β i) (Q i)
  have hT : ∀ φ, sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) ε φ = AllBij.act (Finsupp.mapDomain (β i).gl c) φ :=
    fun φ => (hc φ).trans (AllBij.sum_rep_eq _ _ _)
  have hC := AllBij.mapDomain_mem _ (AllBij.gl_mem (β i)) c
  refine ⟨by rw [hT]; exact AllBij.isContAut_act _ hφ.1, fun i' => ?_⟩
  rcases eq_or_ne i' i with rfl | hne
  · exact hbij.mapsTo (hφ.2 i')
  · rw [hT]
    exact AllBij.ramAt_act _ _ _ (fun x hx g => AllBij.grpAt_comm S (fun e => hne (hinj e)) (hC x hx)
      (AllBij.gl_mem _ g)) (hφ.2 i')

theorem foldr_ram {ι : Type} {p : ι → SplitPt D k} (hinj : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k) (χ₀ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ₀ i) 1) (ε : ι → 𝓀[k]ˣ) (l : List ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', RamAt (β i') (Q i') φ) :
    IsContAut S (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) (ε i) φ') φ) ∧
      ∀ i', RamAt (β i') (Q i') (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) (ε i) φ') φ) := by
  induction l with
  | nil => exact hφ
  | cons i l ih => exact sOp_ram hinj β Q q χ₀ hχ (ε i) i ih

theorem isIdele_idele (p : SplitPt D k) (x : kˣ) : p.IsIdele x (p.idele x) := by
  unfold SplitPt.IsIdele
  rw [SplitPt.idele_val]
  ring

end Local

theorem chrPow_mul_neg (μ : (AE D)ˣ →* Circle) (a : (AE D)ˣ) (e : ℤ) : chrPow μ a e * chrPow μ a (-e) = 1 := by
  simp only [chrPow, ← Circle.coe_mul, _root_.zpow_neg, mul_inv_cancel, Circle.coe_one]

end GlobalTheory.SeeSaw.LiftsAtLevel

namespace GlobalTheory.SeeSaw.LiftsAtLevel


open GlobalTheory.FinPl.ValDbl in
theorem pt_over {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} {v : VCom c} {o : TDat c k ι} {t : Tup c} {w : VTup t} (hc : c.Is) (ht : t.Is) (hv : v.Is) (hVF : VForm v w)
    (hSh : ShapeOff v o) (j : ℕ) (hj : j < D.R.m) (α : t.Ch j) (γ : t.Ch (j + 1))
    (P : PolF D (c.X (j + 1)).rank (c.X j).rank) (i : ι) :
    ∃ f₀, Over c.ψ (o.β j i) (o.β (j + 1) i) (c.x j).L (c.x (j + 1)).L f₀ (phiOne (o.Q j i) (o.Q (j + 1) i))
      ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) := by
  have hk := ht.ker j hj α γ
  have hvac : IsVacO c.ψ c.θ (c.X j) (c.X (j + 1)) (c.x j).s (c.x (j + 1)).s (c.x j).L (c.x (j + 1)).L (c.vac j) := hk.vac
  have hstd := hc.std
  have hxS := hc.x j hj.le
  have hxT := hc.x (j + 1) hj
  set f := pureTensorO c.ψ c.θ (c.X j) (c.X (j + 1)) (c.x j).s (c.x (j + 1)).s (c.x j).B (c.x (j + 1)).B (c.vac j) P
    with hfdef
  have hfV : ∀ Pp, Vac c.ψ _ _ (c.x j).L (c.x (j + 1)).L Pp f := fun Pp => vac_pureTensorO hvac Pp P
  have hpt : (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P =
      comb c.ψ _ _ (w.dQ j α γ) (comb c.ψ _ _ (v.dG j) (comb c.ψ _ _ (v.dT j) f)) := by
    show pureTensorO c.ψ c.θ (c.X j) (c.X (j + 1)) (c.x j).s (c.x (j + 1)).s (c.x j).B (c.x (j + 1)).B
      (comb c.ψ _ _ (t.dd j α γ) (c.vac j)) P = _
    rw [comb_pureTensorO hstd hc.inf _ _ _ _ hvac.2.theta (c := t.dd j α γ) hk.fin P]
    exact hVF.dd j hj α γ f (hfV fun _ => True).1
  have hrep := hSh.rep j hj f (hfV _)
  have hpl : Places o.p o.I (· ∈ v.tP) :=
    ⟨hSh.pre.nodup, hSh.pre.all, hSh.pre.inj, hSh.pre.tP, fun i => (hSh.pre.char i).2⟩
  have hAC := (GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι o.p o.I (· ∈ v.tP) hpl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) c.ψ hstd
    (c.X j) (c.X (j + 1)) (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L hxS.sd hxT.sd
    (fun i => phiOne (o.Q j i) (o.Q (j + 1) i))).2.2
  have hdG : CombAt (fun x => ¬ x ∈ v.tP) (v.dG j) :=
    combAt_mono (fun x hx ht' => Finset.disjoint_left.1 hv.disj hx ht') (hv.atG j).2.1
  have hdQ : CombAt (fun x => ¬ x ∈ v.tP) (w.dQ j α γ) :=
    combAt_mono (fun x hx ht' => Finset.disjoint_left.1 hVF.disjT hx ht') ((hVF.atQ j).2.2 α γ)
  obtain ⟨hV1, hO1⟩ := hAC (v.dG j) hdG f (hfV _)
  obtain ⟨hV2, hO2⟩ := hAC (w.dQ j α γ) hdQ _ hV1
  have hO := hO2 _ (hO1 _ hrep)
  obtain ⟨g, hg, -⟩ := overAll_last hstd (fun i => (hSh.pre.char i).2) hSh.pre.inj o.I hSh.pre.nodup _ _
    (fun j' => vac_at ((hSh.pre.tP _).2 ⟨j', rfl⟩) hV2) hO i (hSh.pre.all i)
  exact ⟨g, hpt ▸ hg⟩

end GlobalTheory.SeeSaw.LiftsAtLevel


open GlobalTheory.SeeSaw.LiftsAtLevel in
theorem GlobalTheory.SeeSaw.liftS_of_exact : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom c) (o : TDat c k ι) (t : Tup c) (w : VTup t), LiftExact D → c.Is → t.Is → v.Is → VForm v w → ShapeOff v o → (∀ j, j < D.R.m → ∃ μ, IsWeilDatumO c.ψ _ _ μ μ (t.kom j) ∧ ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D μ (o.p i).v) → LiftS o t := by
  intro D c k _ _ _ _ ι v o t w hLE hc ht hv hVF hSh hμ j hj α γ P φ hφ
  obtain ⟨μ, hW, hU⟩ := hμ j hj
  have hxS := hc.x j hj.le
  have hxT := hc.x (j + 1) hj
  have hk := ht.ker j hj α γ
  have hφ' : IsContAut (c.X j) φ ∧ ∀ i, RamAt (o.β j i) (o.Q j i) φ := hφ
  set F := (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P with hF
  have hOv := pt_over hc ht hv hVF hSh j hj α γ P
  have hlift : ∀ φ', (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) P φ' =
      liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕 φ' F := fun φ' => rfl

  have hram : ∀ φ', (IsContAut (c.X j) φ' ∧ ∀ i, RamAt (o.β j i) (o.Q j i) φ') →
      liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕 φ' F ∈ o.Ram (j + 1) := by
    intro φ' h'
    refine ⟨?_, fun i => ?_⟩
    · rw [← hlift]
      exact (GlobalTheory.SeeSaw.LiftSumProof.liftSum D c.ψ c.θ hc.inf _ _ (c.x j) (c.x (j + 1)) hxS hxT _ hk P).2.1 φ' h'.1
    · obtain ⟨f₀, hf₀⟩ := hOv i
      obtain ⟨c₀, -, H⟩ := GlobalTheory.T.ramifiedThetaLift_commutes_splitPlace_operators D k (o.p i) (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) o.q (o.χ i) (o.hχ i) c.ψ
        (c.X j) (c.X (j + 1)) hxS.cpt (c.x j).vol μ μ (t.kom j) hW (hU i) (hU i) (o.β j i) (o.β (j + 1) i) (o.Q j i)
        (o.Q (j + 1) i)
      exact (H _ _ f₀ F hf₀ φ' (h'.2 i)).1
  refine ⟨by rw [hlift]; exact hram φ hφ', fun η => ?_⟩

  have key : ∀ l : List ι, l.foldr (fun i φ' => sOp (o.β (j + 1) i) (o.Q (j + 1) i) o.q (resChar (o.χ i) (o.hχ i) o.q) (η i) φ')
        (liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕 φ F) =
      ((((resCard k : ℝ) ^ ((((c.X (j + 1)).rank : ℝ) - (c.X j).rank) / 2) : ℝ) : ℂ) ^ l.length) •
        liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕
          (l.foldr (fun i φ' => sOp (o.β j i) (o.Q j i) o.q (resChar (o.χ i) (o.hχ i) o.q) (η i) φ') φ) F := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.foldr_cons, List.length_cons]
      rw [ih, GlobalTheory.FinPl.ValDbl.sOp_smul]
      obtain ⟨e, -, hE⟩ := hLE k (o.p i) o.q (o.χ i) (o.hχ i)
      obtain ⟨f₀, hf₀⟩ := hOv i
      have hr := (foldr_ram hSh.pre.inj (o.β j) (o.Q j) o.q o.χ o.hχ η l hφ').2 i
      rw [hE (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) c.ψ (c.X j) (c.X (j + 1)) hxS.cpt (c.x j).vol μ μ (t.kom j) hW
        (hU i) (hU i) (o.β j i) (o.β (j + 1) i) (o.Q j i) (o.Q (j + 1) i) _ (isIdele_idele (o.p i) o.q.unit) _ _ f₀ F hf₀ _ hr
        (η i), mul_assoc, chrPow_mul_neg, mul_one, smul_smul, pow_succ]
      simp only [Fintype.card_fin]
  simp only [TDat.S, TDat.cL, hlift]
  exact key o.I
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteLiftCommLevelPrimeOperatorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteLift_comm_levelPrimeOperators : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom c) (o : TDat c k ι) (t : Tup c) (w : VTup t), LiftExact D → c.Is → t.Is → v.Is → VForm v w → ShapeOff v o → (∀ j, j < D.R.m → ∃ μ, IsWeilDatumO c.ψ _ _ μ μ (t.kom j) ∧ ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D μ (o.p i).v) → LiftS o t := by
  first | exact @GlobalTheory.SeeSaw.liftS_of_exact | exact GlobalTheory.SeeSaw.liftS_of_exact | (intros; apply GlobalTheory.SeeSaw.liftS_of_exact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtKStdOfTwist
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.MovedJoin
open GlobalTheory.AdForm


open _root_.Formalism.L2.Col in
theorem adAt_kb_eq_frsF {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀) (hA : A.Is) (P : BadPr I a) (hP : P.1 ∉ (B.primes X).vGs)
    (i : ℕ) (hi : i ≤ B.R.m) (β : Ch₀ i) (r s : Fin (B.R.N i)) :
    adAt B.host.F P.1 (((A.kb i β : TC.GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) _) r s) =
      algebraMap B.host.E _ (frsF I.sel (I.tup a) (A.p0 i β).1.1 P (Pi.single s 1) r) := by
  have hQ : P.1 ∈ I.Q a := by
    rcases Finset.mem_union.1 P.2 with h | h
    · exact absurd h hP
    · exact h
  have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
  have h1 := ((hA.base i hi β).1).fr ⟨P.1, hSQ⟩ r s
  rw [h1, extTo_fr, frsF_eq_ptFr]

theorem adAt_kStd_of_twist {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} (hI : I.Ok) (a : I.ι) (P : BadPr I a)
    (hP : P.1 ∉ (B.primes X).vGs) (u : B.Word) (n : ℕ) (r s : Fin n) :
    adAt B.host.F P.1 (((TC.kStd X u n : TC.GA B n) : Matrix (Fin n) (Fin n) _) r s) =
      algebraMap B.host.E _ (if r = s then 1 else 0) := by
  have hQ : P.1 ∈ I.Q a := by
    rcases Finset.mem_union.1 P.2 with h | h
    · exact absurd h hP
    · exact h
  have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
  have hT := GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P.1 (Finset.mem_union_right _ hSQ)
  have hb := (GlobalTheory.Mem.Col2.MemChart.kStd_spec (X := X) (GlobalTheory.BasePrimes.primes_ok B X).1 u n).2.1 _ hT
  have he := congrArg (fun g => (g.1 : Matrix (Fin n) (Fin n) _) r s) hb
  simp only [Units.val_one] at he
  have h2 : Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F)) (((TC.kStd X u n : TC.GA B n) : Matrix (Fin n) (Fin n) _) r s) =
      Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F)) ((1 : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) := by
    refine he.trans ?_
    by_cases h : r = s <;> simp [Matrix.one_apply, h]
  rw [GlobalTheory.Mem.Col2.AdT.LocSplice.adAt_eq_of_prV P.1 h2]
  by_cases h : r = s <;> simp [Matrix.one_apply, h]

theorem map_eq_one_of_pr {D : Formalism.BasicNotions.D7} {k : Type} [CommRing k] {n : ℕ} (φ : Formalism.L2.Theta.AE D →+* k)
    (M : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D))
    (h : ∀ c d, φ (M c d) = φ (Formalism.L2.Theta.incA D (if c = d then 1 else 0))) : M.map φ = 1 := by
  ext c d
  rw [Matrix.map_apply, h, Matrix.one_apply]
  split_ifs <;> simp

theorem mul_frameγ_std {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) (e' : Y ≃ Fin N)
    (hF : F.β = (1 : Matrix (Fin N) (Fin N) k).submatrix id e') (M : Matrix (Fin N) Y k) (r : Fin N) (b : Y) :
    (M * F.γ) r (e' b) = M r b := by
  have h1 : M * F.γ * F.β = M := by rw [Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  have h2 := congrFun (congrFun h1 r) b
  rw [hF, Matrix.mul_apply] at h2
  simp only [Matrix.submatrix_apply, id, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  exact h2

theorem frameβ_mul_std {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) (e' : Y ≃ Fin N)
    (hF : F.β = (1 : Matrix (Fin N) (Fin N) k).submatrix id e') (g : Matrix Y Y k) (r b : Y) :
    (F.β * g) (e' r) b = g r b := by
  rw [hF, Matrix.mul_apply]
  simp only [Matrix.submatrix_apply, id, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem map_eq_sum_frame {E k : Type} [Field E] [CommRing k] {n : ℕ} (φ : E →+* k) (f : (Fin n → E) ≃ₗ[E] (Fin n → E)) (y : Fin n → E)
    (x : Fin n) : φ (y x) = ∑ c, φ (f (Pi.single c 1) x) * φ (f.symm y c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← f.apply_symm_apply y, pi_eq_sum_univ' (f.symm y), map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_comm]

end GlobalTheory.Fam.MovedJoin

namespace GlobalTheory.Fam
open GlobalTheory.AdForm GlobalTheory.Fam.MovedJoin


end GlobalTheory.Fam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProof
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.FlatVacuum

variable {D : D7}

theorem mulVec_mem_ideal {m n : ℕ} (I : Ideal (AE D)) (M : Matrix (Fin m) (Fin n) (AE D)) {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ I) (i : Fin m) : (M *ᵥ y) i ∈ I := by
  show ∑ j, M i j * y j ∈ I
  exact I.sum_mem fun j _ => I.mul_mem_left _ (hy j)

theorem mulVec_latV_of_local {S S' : HSp D} {L : Lat S} {L' : Lat S'} (hL : Submodule.IsLattice D.host.E L)
    (hL' : Submodule.IsLattice D.host.E L') {P : Pl D → Prop} (M : Matrix (Fin S'.rank) (Fin S.rank) (AE D))
    (h : ∀ v, P v → ∀ y ∈ latV S L (· = v), M *ᵥ y ∈ latV S' L' (· = v)) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : M *ᵥ y ∈ latV S' L' P := by
  obtain ⟨h1, h2⟩ := (((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 S).2.2.2 L y hL).1 hy
  refine (((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 S').2.2.2 L' _ hL').2 ⟨mulVec_mem_ideal _ M h1, fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact h v hv _ (h2 v hv e he)

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • y ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
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

theorem mulVec_latA {S S' : HSp D} {L : Lat S} {L' : Lat S'} {P : Pl D → Prop}
    (M : Matrix (Fin S'.rank) (Fin S.rank) (AE D)) (h : ∀ y ∈ latV S L P, M *ᵥ y ∈ latV S' L' P)
    {y : Fin S.rank → AE D} (hy : y ∈ latA S L P) : M *ᵥ y ∈ latA S' L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    have e : (fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) : AE D)) =
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) : AE D) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [e, Matrix.mulVec_smul]
    exact smul_mem_latA ha (h _ (AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩))
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

section Mono

variable {S S₀ : HSp D} {ρ : ℕ} {d : HypDec S S₀ ρ} {L : Lat S} {L₀ : Lat S₀}

theorem p0_mem {v : Pl D} (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) :
    d.p0 *ᵥ y ∈ latV S₀ L₀ (· = v) := ((h y).1 hy).2.2

theorem wittCoreInclusion_mulVec_mem_latticeCompletionAtPlace {v : Pl D} (h : MonoAt d L L₀ v) {y : Fin S₀.rank → AE D} (hy : y ∈ latV S₀ L₀ (· = v)) :
    d.j0 *ᵥ y ∈ latV S L (· = v) := by
  have hX : d.pX *ᵥ (d.j0 *ᵥ y) = 0 := by
    rw [Matrix.mulVec_mulVec]; exact (congrArg (· *ᵥ y) d.pX_j0).trans (Matrix.zero_mulVec _)
  have hY : d.pY *ᵥ (d.j0 *ᵥ y) = 0 := by
    rw [Matrix.mulVec_mulVec]; exact (congrArg (· *ᵥ y) d.pY_j0).trans (Matrix.zero_mulVec _)
  have h0 : d.p0 *ᵥ (d.j0 *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec]; exact (congrArg (· *ᵥ y) d.p0_j0).trans (Matrix.one_mulVec _)
  have hc : ∀ (x : Mx D S.rank ρ) i, colMul x i 0 = 0 := fun x i => funext fun k => zero_mul _
  refine (h _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
  · rw [hX, Pi.zero_apply, hc]; exact zero_mem _
  · rw [hY, Pi.zero_apply, hc]; exact zero_mem _
  · rw [h0]; exact hy

theorem wittExtendByZero_mem_completedHomLattice {T : HSp D} {LT : Lat T} {P : Pl D → Prop} (hL : IsSelfDualC S L) (hL₀ : IsSelfDualC S₀ L₀)
    (hT : IsSelfDualC T LT) (h : ∀ v, P v → MonoAt d L L₀ v) {w : WO S₀ T}
    (hw : w ∈ latO S₀ T (L₀ : Set _) (LT : Set _) P) : d.ext0 T w ∈ latO S T (L : Set _) (LT : Set _) P := by
  obtain ⟨h1, h2⟩ := (LatMem.mem_latO_iff D S₀ T L₀ LT hL₀ hT P w).1 hw
  refine (LatMem.mem_latO_iff D S T L LT hL hT P _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · show ∑ k, w i k * d.p0 k j ∈ idAt D P
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (h1 i k)
  · have := h2 _ (mulVec_latV_of_local hL.1 hL₀.1 d.p0 (fun v hv z hz => p0_mem (h v hv) hz) hy)
    rw [Matrix.mulVec_mulVec] at this
    exact this

theorem wittCoreInclusion_mem_completedHomLattice {T : HSp D} {LT : Lat T} {P : Pl D → Prop} (hL : IsSelfDualC S L) (hL₀ : IsSelfDualC S₀ L₀)
    (hT : IsSelfDualC T LT) (h : ∀ v, P v → MonoAt d L L₀ v) {w : WO T S₀}
    (hw : w ∈ latO T S₀ (LT : Set _) (L₀ : Set _) P) : d.inc0 T w ∈ latO T S (LT : Set _) (L : Set _) P := by
  obtain ⟨h1, h2⟩ := (LatMem.mem_latO_iff D T S₀ LT L₀ hT hL₀ P w).1 hw
  refine (LatMem.mem_latO_iff D T S LT L hT hL P _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · show ∑ k, d.j0 i k * w k j ∈ idAt D P
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (h1 k j)
  · have := mulVec_latA d.j0
      (fun z hz => mulVec_latV_of_local hL₀.1 hL.1 d.j0 (fun v hv z hz => wittCoreInclusion_mulVec_mem_latticeCompletionAtPlace (h v hv) hz) hz) (h2 y hy)
    rw [Matrix.mulVec_mulVec] at this
    exact this

theorem isHalf_wittExtendByZero {T : HSp D} {e : AE D} {w : WO S₀ T} (hw : IsHalf e w) : IsHalf e (d.ext0 T w) :=
  fun i j => GlobalTheory.WeilSrc.entries_fix_right e hw d.p0 i j

theorem isHalf_wittCoreInclusion {T : HSp D} {e : AE D} {w : WO T S₀} (hw : IsHalf e w) : IsHalf e (d.inc0 T w) := by
  intro i j
  show e * (∑ k, d.j0 i k * w k j) = ∑ k, d.j0 i k * w k j
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, hw k j]

end Mono

theorem isLatVac_of_intertwine {m n m' n' : ℕ} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)}
    {hs' : Mx D m' n' → (Mx D m' n' → ℂ) → (Mx D m' n' → ℂ)} {Λ : AddSubgroup (Mx D m n)} {Λ' : AddSubgroup (Mx D m' n')}
    (ι : Mx D m' n' →+ Mx D m n) (hΛ : ∀ u ∈ Λ', ι u ∈ Λ) (hh : ∀ e u, IsHalf e u → IsHalf e (ι u))
    (𝔉 : (Mx D m n → ℂ) → (Mx D m' n' → ℂ)) {f : Mx D m n → ℂ} (hF : ∀ u ∈ Λ', 𝔉 (hs (ι u) f) = hs' u (𝔉 f))
    (hf : IsLatVac hs Λ f) : IsLatVac hs' Λ' (𝔉 f) := by
  refine ⟨fun u hu => ?_, fun e he u hu hue => ?_⟩
  · rw [← hF _ (Λ'.nsmul_mem hu 2), map_nsmul, hf.1 _ (hΛ u hu)]
  · rw [← hF _ hu, hf.2 e he _ (hΛ u hu) (hh e u hue)]

theorem latO_empty {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : Pl D → Prop} (hP : ∀ v, ¬ P v) {u : WO S T} (hu : u ∈ latO S T LS LT P) : u = 0 := by
  ext i j
  have h1 := LatMem.mul_indP (LatMem.latO_mxAt hu i j)
  have h2 : LatMem.indP D.host.F P = 0 := by
    classical
    refine Subtype.ext (funext fun v => ?_)
    exact if_neg (hP v)
  have h3 : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl
  rw [h2, h3, TensorProduct.zero_tmul, mul_zero] at h1
  exact h1.symm

theorem vac_of_heisLaws {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} {dV : HypDec V V₀ ρ}
    {dW : HypDec W W₀ σ} {x : Mx D W.rank ρ} {y : Mx D V₀.rank σ} {P : Pl D → Prop}
    {𝔉 : (WO V W → ℂ) → (WO V₀ W₀ → ℂ)} (H : HeisLaws ψ dV dW x y P 𝔉) {LV : Lat V} {LV₀ : Lat V₀} {LW : Lat W}
    {LW₀ : Lat W₀}
    (h : ∀ v, P v → IsSelfDualC V LV ∧ IsSelfDualC V₀ LV₀ ∧ IsSelfDualC W LW ∧ IsSelfDualC W₀ LW₀ ∧
      MonoAt dV LV LV₀ v ∧ MonoAt dW LW LW₀ v) {Φ : WO V W → ℂ} (hΦ : Vac ψ V W LV LW P Φ) :
    Vac ψ V₀ W₀ LV₀ LW₀ P (𝔉 Φ) := by
  refine ⟨H.theta Φ hΦ.1, isLatVac_of_intertwine ((dV.ext0 W).comp (dW.inc0 V₀)) (fun u hu => ?_)
    (fun e u hu => isHalf_wittExtendByZero (isHalf_wittCoreInclusion hu)) 𝔉 (fun u hu => H.core Φ hΦ.1 u (LatMem.latO_mxAt hu)) hΦ.2⟩
  by_cases hP : ∃ v, P v
  · obtain ⟨v, hv⟩ := hP
    obtain ⟨a, b, c, e, -⟩ := h v hv
    exact wittExtendByZero_mem_completedHomLattice a b c (fun v hv => (h v hv).2.2.2.2.1) (wittCoreInclusion_mem_completedHomLattice c e b (fun v hv => (h v hv).2.2.2.2.2) hu)
  · rw [latO_empty (not_exists.1 hP) hu, map_zero]
    exact zero_mem _

theorem flatVac : ∀ D : D7, GlobalTheory.FinPl.FlatVac D := by
  intro D ψ P
  refine ⟨fun ρ B J s LV LV₀ LW LW₀ h Φ hΦ => ?_, fun σ J B s LV LV₀ LW LW₀ h Φ hΦ => ?_,
    fun V V₀ T d L L₀ LT hL hL₀ hT h Φ hΦ => ?_⟩
  · exact vac_of_heisLaws ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ P).1 ρ B J s).Heisenberg₂
      (fun v hv => ⟨(h v hv).sdV, (h v hv).sdV₀, (h v hv).sdW, (h v hv).sdW₀, (h v hv).monoV, (h v hv).monoW⟩) hΦ
  · exact vac_of_heisLaws ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ P).2 σ J B s).Heisenberg₂
      (fun v hv => ⟨(h v hv).sdV, (h v hv).sdV₀, (h v hv).sdW, (h v hv).sdW₀, (h v hv).monoV, (h v hv).monoW⟩) hΦ
  · exact ⟨(GlobalTheory.WeilSrc.Zero.theta_iff d Φ).2 hΦ.1, isLatVac_of_intertwine (d.ext0 T)
      (fun u hu => wittExtendByZero_mem_completedHomLattice hL hL₀ hT h hu) (fun e u hu => isHalf_wittExtendByZero hu) (fun f w => f (d.ext0 T w))
      (fun u _ => GlobalTheory.WeilSrc.Zero.heisO_eqv d u Φ) hΦ.2⟩

end GlobalTheory.FinPl.FlatVacuum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProofStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMapPreservesVacuum_proof : ∀ D : D7, GlobalTheory.FinPl.FlatVac D := by
  first | exact @GlobalTheory.FinPl.FlatVacuum.flatVac | exact GlobalTheory.FinPl.FlatVacuum.flatVac | (intros; apply GlobalTheory.FinPl.FlatVacuum.flatVac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainDescent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.VacTheta

theorem isFinComb_of_combAt {D : D7} {P : GlobalTheory.FinPl.Pl D → Prop} {S T : HSp D} {c : WO S T →₀ ℂ}
    (h : GlobalTheory.FinPl.CombAt P c) : IsFinComb c := by
  intro u hu
  ext i j
  have := (Ideal.mem_inf.1 (h u hu i j)).1
  simpa using this

end GlobalTheory.Fam.VacTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelProdHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfProd

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.AdForm GlobalTheory.ExportSeries

variable {D : D7}

def prodHalf {m n : ℕ} (a b : AE D) (Ψ : Mx D m n → ℂ) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun Φ x := Φ (a • x) * Ψ (b • x) * (if IsHalf (a + b) x then 1 else 0)
  map_add' Φ Φ' := by funext x; simp only [Pi.add_apply]; ring
  map_smul' c Φ := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem prodHalf_apply {m n : ℕ} (a b : AE D) (Ψ Φ : Mx D m n → ℂ) (x : Mx D m n) :
    prodHalf a b Ψ Φ x = Φ (a • x) * Ψ (b • x) * (if IsHalf (a + b) x then 1 else 0) := rfl

def combL (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (d : WO S T →₀ ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
  ∑ u ∈ d.support, d u • GlobalTheory.PlaceModel.heisL S T ψ u

theorem combL_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (d : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    combL ψ S T d f = comb ψ S T d f := by
  simp only [combL, comb, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

end GlobalTheory.HalfProd

namespace GlobalTheory.HalfProd

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.AdForm GlobalTheory.ExportSeries GlobalTheory.ExportSeries.RestrictHalfModel

variable {D : D7}

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

theorem isSBHalf_prodHalf {m n : ℕ} {a b : AE D} (ha : a * a = a) (hb : b * b = b) {Λ : AddSubgroup (Mx D m n)}
    (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) {Ψ Φ : Mx D m n → ℂ} (hΨ : IsSBHalf b Λ Ψ)
    (hΦ : IsSBHalf a Λ Φ) : IsSBHalf (a + b) Λ (prodHalf a b Ψ Φ) := by
  obtain ⟨-, k, hk, hinv, hlat⟩ := hΦ
  obtain ⟨-, k', hk', hinv', hlat'⟩ := hΨ
  refine ⟨fun t ht => ?_, k * k', Nat.mul_pos hk hk', fun u hu hhu t => ?_, fun t ht => ?_⟩
  · rw [prodHalf_apply] at ht
    by_contra h
    exact ht (by rw [if_neg h, mul_zero])
  · rw [isHalf_iff'] at hhu
    simp only [prodHalf_apply]
    have e1 : a • (t + (k * k') • u) = a • t + k • (k' • (a • u)) := by
      rw [smul_add, mul_smul, smul_comm a k (k' • u), smul_comm a k' u]
    have e2 : b • (t + (k * k') • u) = b • t + k' • (k • (b • u)) := by
      rw [smul_add, mul_comm, mul_smul, smul_comm b k' (k • u), smul_comm b k u]
    have e3 : (a + b) • ((k * k') • u) = (k * k') • u := by rw [smul_comm, hhu]
    have ha' : IsHalf a (k' • (a • u)) := (isHalf_iff' _ _).2 (by rw [smul_comm, smul_smul, ha])
    have hb' : IsHalf b (k • (b • u)) := (isHalf_iff' _ _).2 (by rw [smul_comm, smul_smul, hb])
    rw [e1, e2, hinv _ (Λ.nsmul_mem (hΛ a ha u hu) k') ha', hinv' _ (Λ.nsmul_mem (hΛ b hb u hu) k) hb']
    simp only [isHalf_add_iff e3]
  · rw [prodHalf_apply] at ht
    have h1 : Φ (a • t) ≠ 0 := fun h => ht (by rw [h, zero_mul, zero_mul])
    have h2 : Ψ (b • t) ≠ 0 := fun h => ht (by rw [h, mul_zero, zero_mul])
    have h3 : IsHalf (a + b) t := by
      by_contra h
      exact ht (by rw [if_neg h, mul_zero])
    rw [isHalf_iff', add_smul] at h3
    rw [← h3, smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem (hlat _ h1) k'
    · rw [mul_smul]; exact Λ.nsmul_mem (hlat' _ h2) k

theorem isPlaceModel_prodHalf {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ}
    {a b : AE D} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} {Ψ : WO S T → ℂ} (ha : a * a = a) (hb : b * b = b)
    (hab : a * b = 0) (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) (hΨ : IsSBHalf b Λ Ψ)
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ T₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 (T₀ (prodHalf a b Ψ (halfInd a Λ))) (T₀ ∘ₗ prodHalf a b Ψ) := by
  have hsb : ∀ Φ, IsSBHalf a Λ Φ → IsSBHalf (a + b) Λ (prodHalf a b Ψ Φ) :=
    fun Φ hΦ => isSBHalf_prodHalf ha hb hΛ hΨ hΦ
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · obtain ⟨hbx, hax⟩ := smul_of_half hab hx
    have e : prodHalf a b Ψ (fun t => Φ (t + x)) = fun t => prodHalf a b Ψ Φ (t + x) := by
      funext z
      simp only [prodHalf_apply]
      rw [smul_add, (isHalf_iff' _ _).1 hx, smul_add b, hbx, add_zero, isHalf_add_iff hax]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.trans _ (hsb Φ hΦ) x ((isHalf_iff' _ _).2 hax)
  · have hy' : IsHalf (cA D (a + b)) y := by
      rw [isHalf_iff'] at hy ⊢
      rw [map_add (f := _), add_smul, hy, ← hy, smul_smul, ← map_mul, mul_comm, hab, map_zero, zero_smul, add_zero]
    have e : prodHalf a b Ψ (fun t => ψ (symplO S T t y) * Φ t) =
        fun t => ψ (symplO S T t y) * prodHalf a b Ψ Φ t := by
      funext z
      simp only [prodHalf_apply]
      rw [GlobalTheory.PlaceModel.symplO_smul, (isHalf_iff' _ _).1 hy]
      ring
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.modul _ (hsb Φ hΦ) y hy'
  · rw [LinearMap.comp_apply, one_smul]

theorem placeModel_eq {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {e : AE D} (he : e * e = e) (hinf : infPart D e = 0)
    {f₁ : WO S T → ℂ} {T₁ T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₁ T₁)
    (h₂ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₁ T₂)
    {Φ : WO S T → ℂ}
    (hΦ : IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ) :
    T₁ Φ = T₂ Φ := by
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hLL' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) →
      x ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e := fun x hx h => by
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin' : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, ∃ r ∈ R,
        ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u := fun k hk => by
    obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ (latO S T ΛS ΛT fun _ => True) := fun y hy =>
    exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))
  exact placeModel_unique_of_dual ψ _ hLL' hX hfin' hden h₁ h₂ hΦ

end GlobalTheory.HalfProd

end
end
