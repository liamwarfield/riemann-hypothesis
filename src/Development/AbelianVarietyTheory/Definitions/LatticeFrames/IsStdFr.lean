module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

def IsStdFr {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (pos : Y → ℕ) (F : Frame k N Y) : Prop :=
  ∃ e : Y ≃ Fin N, GlobalTheory.SymBridge.IsOrd pos e ∧ F.β = (1 : Matrix (Fin N) (Fin N) k).submatrix id e

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word)


set_option maxHeartbeats 1000000 in
structure GeoAll where
  g : Geo D
  j : SmT (pk W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP D → ℂ)
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  ι : Type
  v : VCom (commOf (pk W) u g)
  o : TDat (commOf (pk W) u g) k ι
  n : ℕ
  G : Fin n → GLoc v
  pl : Fin n ≃ (pk W).Pg
  Q : ∀ PP, QAll W PP → GlobalTheory.QTw.QGeo v (baseOf (pk W) (lvP W) u g) PP
  d : BotDat W u
  c₀ : ℕ → ℂ

attribute [instance] GeoAll.fld GeoAll.val GeoAll.top GeoAll.loc

variable {W u} (a : GeoAll W u)

abbrev GeoAll.fam (row : ∀ t, RowCh (pk W) (lvP W) u a.g t) (col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t))) : FamCh W u :=
  ⟨a.g, a.j, row, col⟩

structure GeoAll.Is : Prop where
  meas : GeoMeas (pk W) a.g
  last : (commOf (pk W) u a.g).VolLast
  x : ∀ j, j ≤ D.R.m → (a.g.x j).Is
  vis : a.v.Is
  shape : ShapeOff a.v a.o
  gpin : GPin a.G
  tie : ∀ row col, VTie (a.fam row col) a.v ∧ GRead (a.fam row col) a.G a.pl
  top : TopReadAt W u a.j a.g.bT

  norm : star a.o.ζ₀ ⬝ᵥ a.g.Lz.gram *ᵥ a.o.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) ∧
    ∀ j h, a.v.τ j h *ᵥ a.o.ζ₀ = (-D.host.xi0 ^ (D.R.m / 2)) • (a.g.bes j 0 h).ζ

  stdG : ∀ i, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((a.G i).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (a.G i).FT ∧
    (a.G i).z₀ = fun r => (ofSplit (a.G i).q).pr (a.o.ζ₀ r)
  stdQ : ∀ PP h, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((a.Q PP h).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (a.Q PP h).FT ∧
    (a.Q PP h).z₀ = fun r => (ofSplit (a.Q PP h).q).pr (a.o.ζ₀ r)
  bot : (∀ h0, a.d.B.lev = (commOf (pk W) u a.g).B 0 D.R.rS h0) ∧ a.d.b = a.g.b 0 ∧ a.d.B.Adapted (W.S.tr u).wt ∧
    ∀ r, (a.d.B.d.i₀ *ᵥ vecB a.d.B.o a.d.B.ζ) r = W.S.X.ιE (W.S.X.zR u (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) r))

end Gen

section True

open GlobalTheory.Mem GlobalTheory.Mem.Col2

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}

structure GeoAll.True (a : GeoAll W u) : Prop where
  pinX : GlobalTheory.AdForm.PinX I l Z (pk W).ψ (pk W).θ a.g.x a.g.vac a.c₀
  std : @GlobalTheory.AdForm.StdT B X I l Z u a.k a.fld a.val a.top a.loc a.ι (@TDat.p _ _ _ a.fld a.val a.top a.loc _ a.o)
    (@TDat.β _ _ _ a.fld a.val a.top a.loc _ a.o) (@TDat.Q _ _ _ a.fld a.val a.top a.loc _ a.o) fun j => (a.g.x j).L
  emb : GlobalTheory.AdForm.IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((a.g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _))
  z0 : ∀ r, vecB (a.g.oT B.R.m rfl) (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) r =
    (show Fin (B.R.N B.R.m) → (I.rec7 l Z).host.E from TC.z0 X u) (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl) r)

end True

end GlobalTheory.Fam

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QTw

section Sign
variable {D : D7} {c : Comm D} {t : Tup c}

def twist (w : VTup t) (s : ∀ j, t.Ch j → ℂ) : VTup t :=
  { w with
    dQ := fun j α γ => (s j α * s (j + 1) γ) • w.dQ j α γ
    ε := fun j α => s j α • w.ε j α
    εT := fun n h β => s n β • w.εT n h β }

variable {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E}

def QGeo.Res (G : QGeo v B PP) (δ : G.kˣ →* ℂˣ) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ (z : 𝓞 D.host.E) (x : G.kˣ) (r : (Formalism.L2.DIV.kP PP)ˣ), (x : G.k) = (ofSplit G.q).pr (z : D.host.E) →
    (r : Formalism.L2.DIV.kP PP) = Ideal.Quotient.mk PP.asIdeal z → δ x = (ξ r)⁻¹

def QExt.tw {G : QGeo v B PP} {χ : ℕ → (AE D)ˣ →* Circle} (E : QExt G χ) (hψ : Continuous G.ψk) (sg : ℂ) : GlobalTheory.TwBridge.TwData G.k :=
  ⟨G.ϖ, G.unif, G.ψk, hψ, G.cond, E.δ, E.tame, E.η, E.unr, sg⟩

theorem exists_xOrd (R : Ranks) (j : ℕ) :
    ∃ e : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e := by
  have h : R.k + j + j * R.t = R.N j := by
    show _ = R.k + j * (R.t + 1)
    ring
  refine ⟨((Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv).trans (finCongr h), ?_⟩
  rintro ((i | i) | ⟨p, q⟩) <;> simp [GlobalTheory.SymBridge.xPos, finProdFinEquiv]
  ring

theorem exists_topOrd (R : Ranks) (s : ℕ) (hs : s + 1 + 1 = R.m) :
    ∃ e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N (s + 1 + 1)),
      GlobalTheory.SymBridge.IsOrd (Sum.elim GlobalTheory.SymBridge.zPos fun _ => R.N R.m - 1) e := by
  have h : R.k + (s + 1) + (s + 2) * R.t + 1 = R.N (s + 1 + 1) := by
    show _ = R.k + (s + 1 + 1) * (R.t + 1)
    ring
  refine ⟨((Equiv.sumCongr ((Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv)
    finOneEquiv.symm).trans finSumFinEquiv).trans (finCongr h), ?_⟩
  rintro (((i | i) | ⟨p, q⟩) | i)
  · simp [GlobalTheory.SymBridge.zPos]
  · simp [GlobalTheory.SymBridge.zPos]
  · simp [GlobalTheory.SymBridge.zPos, finProdFinEquiv]
    ring
  · simp [← hs, ← h]

end Sign

section True
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀)

abbrev BadPr (I : TC B X) (a : I.ι) : Type := Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a)

def locLast (I : TC B X) (a : I.ι) (P : BadPr I a) : ∀ (i : ℕ), i + 1 = B.R.m →
    Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)) → Formalism.L2.Col.Sp B.fields.E (B.R.N i) → B.fields.K
  | 0, h => absurd B.R.two_le_m (by omega)
  | n + 1, h => fun y y' => TopStep.locTop I.Ch I.sel (I.tup a) (I.cst a) n P (castSp B.fields.E (congrArg B.R.N h) ∘ₗ y) y'

def locXi (i : ℕ) (α : Ch₀ i) (γ : Ch₀ (i + 1)) (P : BadPr I a)
    (x : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))) : B.fields.K :=
  let y := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 i α).1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (i + 1) γ).1.1 P) x
  if h : i + 2 < B.R.m then
    Formalism.L2.Col.XiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i ((A.b0 i α).get (by omega)) P)
      ((I.idx a).h (i + 1) ((A.b0 (i + 1) γ).get (by omega)) P) y
  else if h : i + 2 = B.R.m then
    Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i ((A.b0 i α).get (by omega)) P) y
      ((Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (i + 1) γ).1.1 P).symm (Formalism.L2.Col.repY (A.p0 (i + 1) γ).1.2))
  else if h : i + 1 = B.R.m then
    locLast I a P i h y ((Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 i α).1.1 P).symm (Formalism.L2.Col.repY (A.p0 i α).1.2))
  else 0

abbrev homOf (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) :=
  toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z

def xiOff (i : ℕ) (hi : i + 1 ≤ B.R.m) (α : Ch₀ i) (γ : Ch₀ (i + 1))
    (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) : ℂ :=
  B.embLL (Formalism.L2.Col.phiT B.fields.K (A.p0 i α).1.1.deco.1 (A.p0 (i + 1) γ).1.1.deco.1 (homOf I l Z i hi z) *
    ∏ P ∈ Finset.univ.filter (fun P : BadPr I a => P.1 ∈ (B.primes X).vGs), locXi A i α γ P (homOf I l Z i hi z))

theorem xi_eq_xiOff_mul (i : ℕ) (hi : i + 1 ≤ B.R.m) (α : Ch₀ i) (γ : Ch₀ (i + 1)) (z) :
    A.xi i hi α γ z = xiOff A i hi α γ z *
      B.embLL (∏ P ∈ Finset.univ.filter (fun P : BadPr I a => ¬ P.1 ∈ (B.primes X).vGs), locXi A i α γ P (homOf I l Z i hi z)) := by
  rw [xiOff, ← map_mul, mul_assoc, Finset.prod_filter_mul_prod_filter_not, TwDat.xi]
  congr 1
  unfold xiAt locXi
  split_ifs with h1 h2 h3
  · rfl
  · rfl
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by have := B.R.two_le_m; omega⟩
    rfl
  · omega

def BaseCommon : Prop := ∀ i, i ≤ B.R.m → ∀ β β', (A.p0 i β).1.1 = (A.p0 i β').1.1 ∧ A.kA i β = A.kA i β' ∧ A.xr i β = A.xr i β'

def baseFr (P : BadPr I a) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch₀ i) :
    Matrix (Fin ((I.rec7 l Z).sp.X i).rank) (Fin (B.R.N i)) (I.rec7 l Z).host.E := fun r b =>
  Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 i β).1.1 P (Pi.single b 1) (finCongr (rankN (I.rec7 l Z) i hi) r)

variable {c : Comm (I.rec7 l Z)} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E} {G : QGeo v Bs PP}
  {χ : ℕ → (AE (I.rec7 l Z))ˣ →* Circle}

structure ReadsAt (P : BadPr I a) (E : QExt G χ) (hψ : Continuous G.ψk) (sg : ℂ) (π : ∀ j, Ch₀ j → E.Ch j) : Prop where
  eq : P.1 = PP
  tw : GlobalTheory.TwBridge.AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL P (G.q.pr.comp (incA (I.rec7 l Z))) G.s (E.tw hψ sg)
  M : E.M = (I.cst a).M
  rep : ∀ j d (h : j + d = G.s) (hj : j < B.R.m) β, GlobalTheory.TwBridge.IsGL (X := B.fields) (R := B.R) (k := G.k) (G.q.pr.comp (incA (I.rec7 l Z)))
    ((I.idx a).h j ((A.b0 j β).get hj) P) (E.rep j d h (π j β))


variable (G) in
def ownVec (P : BadPr I a) (e : XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) ≃ Fin (B.R.N (G.s + 1))) (β : Ch₀ (G.s + 1)) :
    XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) → G.k := fun r => (ofSplit G.q).pr
  ((Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (G.s + 1) β).1.1 P).symm (Formalism.L2.Col.repY (A.p0 (G.s + 1) β).1.2) (e r))

structure MovedAt (P : BadPr I a) (E : QExt G χ) (hψ : Continuous G.ψk) (sg : ℂ) (π : ∀ j, Ch₀ j → E.Ch j) : Prop
    extends ReadsAt A P E hψ sg π where
  rk : ∀ i, (c.X i).rank = ((I.rec7 l Z).sp.X i).rank
  low : ∀ i (hi : i ≤ G.s) (hm : i ≤ B.R.m) β (e : XIx (Fin B.R.k) (Fin B.R.t) i ≃ Fin (B.R.N i)),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ r b,
      (ofSplit G.q).pr (baseFr A P i hm β (Fin.cast (rk i) r) (e b)) = (G.FX i (Nat.le_succ_of_le hi)).β r b
  pen : ∀ (hm : G.s + 1 ≤ B.R.m) β (e : XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) ≃ Fin (B.R.N (G.s + 1))),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∃ κ ∈ ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J,
      (∀ r b, (ofSplit G.q).pr (baseFr A P (G.s + 1) hm β (Fin.cast (rk _) r) (e b)) =
        ((G.FX (G.s + 1) le_rfl).β * κ.val.toBlocks₁₁) r b) ∧
      E.cos (π (G.s + 1) β) = Submodule.Quotient.mk (κ.val.toBlocks₁₁ *ᵥ ownVec A G P e β)

variable {A}

variable (A)

theorem ownVec_mem (P : BadPr I a) (hP : P.1 ∉ (B.primes X).vGs)
    (hc : GlobalTheory.SymBridge.IsCompl (E := B.fields.E) P.1 (Formalism.L2.Col.qOf P.1) (G.q.pr.comp (incA (I.rec7 l Z))) G.ϖ) (e) (β) :
    ownVec A G P e β ∈ box _ (G.ϖ ^ (I.cst a).M)⁻¹ := by
  have hs : G.s + 1 + 1 = B.R.m := G.hs
  have h0 := (A.p0 (G.s + 1) β).repY_mem hs
  obtain ⟨y, hy, hY⟩ := (A.p0 (G.s + 1) β).mem_ybSet hs
  set z := Formalism.L2.Col.repY (A.p0 (G.s + 1) β).1.2 with hz
  rw [hY] at h0
  have h1 := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy P
  have h2 := (Formalism.L2.Col.mem_locLat _ _ _ _).1 h0 P
  simp only [if_neg hP] at h1 h2
  have hq : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ≠ 0 := fun h => G.ϖ.ne_zero (by rw [hc.unif, h, map_zero])
  have h3 : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M • z ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (A.p0 (G.s + 1) β).1.1.deco.1.N := by
    have h4 := add_mem h1 (Submodule.smul_mem _ (((Formalism.L2.Col.qOf P.1 : ℕ) : 𝓞 B.fields.E) ^ (2 * (I.cst a).M)) h2)
    convert h4 using 1
    rw [← algebraMap_smul B.fields.E (((Formalism.L2.Col.qOf P.1 : ℕ) : 𝓞 B.fields.E) ^ (2 * (I.cst a).M)), smul_smul, map_pow, map_natCast,
      _root_.zpow_neg, inv_inv, zpow_natCast, two_mul, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), mul_one, ← smul_add, add_sub_cancel]
  rw [← (ptFr (A.p0 (G.s + 1) β).1.1 P.1).apply_symm_apply (_ • z)] at h3
  have h5 := (isFr_ptFr (A.p0 (G.s + 1) β).1.1 P.1 _).1 h3
  rw [← frsF_eq_ptFr I.sel (I.tup a), map_smul] at h5
  intro r
  have h6 := (hc.int _).2 (GlobalTheory.TopStep.mem_stdAt.1 h5 (e r))
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, ← hc.unif, Valuation.mem_integer_iff, map_mul] at h6
  have h7 : 0 < valuation G.k ((G.ϖ : G.k) ^ (I.cst a).M) := by
    rw [map_pow]
    exact pow_pos ((Valuation.pos_iff _).2 G.ϖ.ne_zero) _
  rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, ← mul_one (_⁻¹), le_inv_mul_iff₀ h7]
  exact h6

end True

end GlobalTheory.QTw
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.Framed
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MiTop

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D}

def Framed (B : SBes X h u ψ A) : Prop :=
  ∃ μ lam : D.host.E, μ ≠ 0 ∧ (lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)) ∧
    (∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) ∧
    (∀ k (a : Fin D.R.rS), B.d.e k a = μ * lam ^ (D.R.rS - (a : ℕ)) * X.ιE (X.eR a (Fin.cast (rank_eq X h) k))) ∧
    ∀ k (a : Fin D.R.rS), B.d.e' k a = (star (μ * lam ^ (D.R.rS - (a : ℕ))))⁻¹ * X.ιE (X.fR a (Fin.cast (rank_eq X h) k))

end GlobalTheory.MiTop

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsLatInd
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocMod ValuativeRel Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SeeSaw.LocPlModel
variable {D : D7}

section Rel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem exists_latInd (q : GlobalTheory.FinPl.SplitPt D k) (hU : q.UnitAA) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') :
    ∃ Φ₀ : SB (Matrix Y Y' k),
      Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) := by
  obtain ⟨gS, hS1, hS2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D k q S Y' FS.β FS.γ FS.βγ FS.γβ
  obtain ⟨gT, hT1, hT2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D k q T Y FT.β FT.γ FT.βγ FT.γβ
  let α : GlobalTheory.FinPl.Frame q S Y' := ⟨FS.β, FS.γ, FS.βγ, FS.γβ, gS, hS1, hS2⟩
  let β : GlobalTheory.FinPl.Frame q T Y := ⟨FT.β, FT.γ, FT.βγ, FT.γβ, gT, hT1, hT2⟩
  obtain ⟨ΛS, i1, hα, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D k q S Y' α M hM
  obtain ⟨ΛT, i2, hβ, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D k q T Y β M' hM'
  haveI : ΛS.IsFullLattice k := GlobalTheory.FinPl.isLattice_of_isLat_selfDual α M hM ΛS hα
  haveI : ΛT.IsFullLattice k := GlobalTheory.FinPl.isLattice_of_isLat_selfDual β M' hM' ΛT hβ
  refine ⟨⟨GlobalTheory.LatPair.latInd ΛS ΛT, GlobalTheory.LatPair.latInd_mem_SB ΛS ΛT⟩, funext fun x => ?_⟩
  have hh := GlobalTheory.FinPl.HalfInd.isHalf_wr α β x
  have mulvec (z : Y' → k) : (GlobalTheory.FinPl.HalfInd.wr α β x) *ᵥ (fun j => q.sec ((α.b *ᵥ z) j)) =
      fun i => q.sec ((β.b *ᵥ (x *ᵥ z)) i) := by
    have hM : (β.b * x * α.b') *ᵥ (α.b *ᵥ z) = β.b *ᵥ (x *ᵥ z) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (β.b * x), α.b'b, Matrix.mul_one, Matrix.mulVec_mulVec]
    rw [← hM]
    funext i
    simp only [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.HalfInd.wr_apply]
    set_option synthInstance.maxHeartbeats 100000 in rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => (GlobalTheory.FinPl.LatIndHalf.sec_mul q _ _).symm
  have key : GlobalTheory.FinPl.HalfInd.wr α β x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v) ↔
      ∀ z ∈ ΛS, x *ᵥ z ∈ ΛT := by
    have hmem := GlobalTheory.FinPl.LatMem.mem_latO_iff D S T M M' hM hM' (· = q.v) (GlobalTheory.FinPl.HalfInd.wr α β x)
    rw [hU.2 T M'] at hmem
    constructor
    · intro h z hz
      have h1 := (hmem.1 h).2 _ ((hα z).1 hz)
      rw [mulvec] at h1
      exact (hβ _).2 h1
    · intro h
      refine hmem.2 ⟨fun i j => ?_, fun y hy => ?_⟩
      · rw [← hh i j]
        exact Ideal.mul_mem_right _ _ (GlobalTheory.FinPl.LatIndHalf.e_mem_idAt q)
      · have hy' : (GlobalTheory.FinPl.HalfInd.wr α β x) *ᵥ y = (GlobalTheory.FinPl.HalfInd.wr α β x) *ᵥ (fun j => q.e * y j) := by
          funext i
          simp only [Matrix.mulVec, dotProduct]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← mul_assoc, mul_comm (GlobalTheory.FinPl.HalfInd.wr α β x i j) q.e, hh i j]
        have hey : (fun j => q.e * y j) = fun j => q.sec ((α.b *ᵥ (α.b' *ᵥ fun j => q.pr (y j))) j) := by
          funext j
          rw [Matrix.mulVec_mulVec, α.bb', Matrix.one_mulVec, q.sec_pr]
        have hint : finPart D q.e ∈ intAE D := by
          rw [← GlobalTheory.FinPl.LatIndHalf.sec_one q]
          exact (q.int_iff 1).1 (one_mem _)
        have hx : α.b' *ᵥ (fun j => q.pr (y j)) ∈ ΛS := (hα _).2 (hey ▸ GlobalTheory.FinPl.LatIndHalf.mul_mem_latV hint hy)
        rw [hy', hey, mulvec]
        exact (hβ _).1 (h _ hx)
  change GlobalTheory.LatPair.latInd ΛS ΛT x = _
  unfold GlobalTheory.LatPair.latInd
  by_cases h : ∀ y ∈ ΛS, x *ᵥ y ∈ ΛT
  · rw [ite_eq_left h, Set.indicator_of_mem (by exact key.2 h)]
  · rw [ite_eq_right h, Set.indicator_of_notMem (by exact fun h' => h (key.1 h'))]

end Rel

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}

theorem e_mul_e (L L' : LocPl ψ S T M M') (h : L.q.v ≠ L'.q.v) : L.q.e * L'.q.e = 0 := by
  have h1 : L.q.e * L'.q.e ∈ GlobalTheory.FinPl.idAt D (· = L.q.v) := Ideal.mul_mem_right _ _ (GlobalTheory.FinPl.LatIndHalf.e_mem_idAt L.q)
  have h2 : L.q.e * L'.q.e ∈ GlobalTheory.FinPl.idAt D (· = L'.q.v) := Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.LatIndHalf.e_mem_idAt L'.q)
  have h3 : GlobalTheory.FinPl.compAt D L.q.v (L.q.e * L'.q.e) = 0 := (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 h2).2 ⟨_, h⟩
  rw [GlobalTheory.FinPl.Model.eq_single h1, h3, map_zero]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.SeeSaw.LocPlModel
end
end
