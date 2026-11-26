module

public import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.DoubleCosetMeasures.StatementV
public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
noncomputable section

namespace Formalism.MainNotions.LocalQuadraticParts

open Formalism.BasicNotions Formalism.BasicNotions.DV NumberField IsDedekindDomain

structure Loc (D : D7) where

  Jx : ℕ → D.what₂.places.Pl → ℝ

abbrev qn {D : D7} (A : AmbForm D (RowSide.sharp D)) (v : InfinitePlace D.what₂.LL) (q : (A.MtH D.what₂.mu0).V) : ℝ :=
  DV.quotNorm A v q

def nTT (D : D7) : ℝ := (D.host.TT.card : ℝ)

def UsedT (D : D7) (μ : D.what₂.Tup) : Prop := μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w

def PeterssonBoundAtEmbedding (D : D7) (Z : DivX D) (A : AmbForm D (RowSide.sharp D)) (s : D.what₂.LL →+* ℂ) : Prop :=
  ∀ (x : D.div.RR.V) (q : (A.MtH D.what₂.mu0).V), A.jAmb D.what₂.mu0 q ∈ D.what₂.V0 D.what₂.mu0 →
    D.jEE x = D.what₂.iota D.what₂.mu0 (A.jAmb D.what₂.mu0 q) →
    Z.kapR s * Real.exp (⨅ σ : Fin D.what₂.Drows, ∑ j ∈ SizeData₂.lifts D, Z.logLam j (D.what₂.ft σ) s) *
        qn A (InfinitePlace.mk s) q ^ 2 ≤
      Formalism.HermitianLatticesTheory.normAt D.div.RR.b D.div.RR.X (InfinitePlace.mk s) x ^ 2 ∧
    Formalism.HermitianLatticesTheory.normAt D.div.RR.b D.div.RR.X (InfinitePlace.mk s) x ^ 2 ≤
      Z.kapR s * Real.exp (⨆ σ : Fin D.what₂.Drows, ∑ j ∈ SizeData₂.lifts D, Z.logLam j (D.what₂.ft σ) s) *
        qn A (InfinitePlace.mk s) q ^ 2

def PeterssonBoundAllEmbeddings (D : D7) (Z : DivX D) (A : AmbForm D (RowSide.sharp D)) : Prop := ∀ s, PeterssonBoundAtEmbedding D Z A s

def adm2 (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (φ : (D.div.Nu u).V), φ ∈ L.NuLat u →
    ∀ F ∈ (D.what₂.Mtilde (D.what₂.muAt w)).carrier, F ∈ D.what₂.V0 (D.what₂.muAt w) →
      ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u (D.what₂.muAt w) (D.jN u φ) F ∧
        (y = 0 ∨ ((⌊ur D w (L.sg u w)⌋ : ℤ) : ℝ) ≤ (vAdd (D.plEq w) y : ℝ))

def UnroundedValuationBound (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (φ : (D.div.Nu u).V), φ ∈ L.NuLat u →
    ∀ F ∈ (D.what₂.Mtilde (D.what₂.muAt w)).carrier, F ∈ D.what₂.V0 (D.what₂.muAt w) →
      ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u (D.what₂.muAt w) (D.jN u φ) F ∧
        (y = 0 ∨ ur D w (L.sg u w) ≤ (vAdd (D.plEq w) y : ℝ))

theorem valuation_bound_of_unrounded (D : D7) (L : SizeData₂ D) (h : UnroundedValuationBound D L) : adm2 D L := by
  intro u w φ hφ F hF hV
  obtain ⟨y, hy, h'⟩ := h u w φ hφ F hF hV
  exact ⟨y, hy, h'.imp_right fun h'' => (Int.floor_le _).trans h''⟩

def ArchimedeanSignatureMatching (D : D7) (L : SizeData₂ D) (X : Loc D) (C Cabs : ℝ) : Prop :=
  ∃ (err : ℕ → D.what₂.places.Pl → ℝ) (fl : ℕ → ℕ → ℝ) (r : ℕ → D.what₂.places.Pl → ℝ),
    (∀ j l, 0 ≤ fl j l) ∧ (∀ j w, 0 ≤ r j w) ∧ (∀ j w, 0 ≤ X.Jx j w) ∧
    (∀ j w, err j w = fl j (D.what₂.places.resChar w) +
      (r j w + r j (D.what₂.places.conj w)) / (D.what₂.D0 : ℝ)) ∧
    (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
      ∑ j ∈ SizeData₂.lifts D,
        (((D.what₂.Ij (D.what₂.muAt w) j w : ℝ) +
          (D.what₂.Ij (D.what₂.muAt w) j (D.what₂.places.conj w) : ℝ)) /
          (D.what₂.D0 : ℝ) - 2 * ur D w (L.F j w)) ≤
        ur D w ((∑ j ∈ SizeData₂.lifts D, err j w) + 2 / ((D.what₂.places.resChar w : ℝ) ^ 2))) ∧
    (∀ j ∈ SizeData₂.lifts D,
      Summable (fun w => SizeData₂.lwP w * ur D w (err j w + X.Jx j w)) ∧
      ∑' w, SizeData₂.lwP w * ur D w (err j w + X.Jx j w) ≤
        C * L.sc.x ^ (Cabs * L.sc.eps) * (L.B0 + L.Nc))


def adm11 (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u, ∀ j ∈ SizeData₂.lifts D,
    |(∑ w ∈ L.supp, SizeData₂.sz w (L.E u j w)) -
        (∑ t : D.host.TT, (L.aT t : ℝ)) * Real.log (∏ g ∈ L.gTypes, (g : ℝ))| ≤ C * L.B0 ∧
    ∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w ∉ L.gTypes), |SizeData₂.sz w (L.E u j w)| ≤
      C * L.B0

def adm12 (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    ∀ (φ : (D.div.Nu u).V), φ ∈ MramL D u →
    ∀ F ∈ (D.what₂.Mtilde (D.what₂.muAt w)).carrier, F ∈ D.what₂.V0 (D.what₂.muAt w) →
      ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u (D.what₂.muAt w) (D.jN u φ) F ∧
        (y = 0 ∨ ur D w (∑ j ∈ SizeData₂.lifts D, (L.F j w - L.E u j w)) ≤ (vAdd (D.plEq w) y : ℝ))

def adm13 (D : D7) : Prop :=
  ∃ V : D.what₂.EE ≃ₗᵢ[ℂ] D.what₂.EE, ∀ u, ∃ a : ℂ, a ≠ 0 ∧
    ∃ U : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u, ∀ φ F, D.what₂.Bu u φ F = a * D.besS u (U φ) (V F)

def TWAt (D : D7) (N : NChoice D) (T : ThData D) : Prop :=
  Formalism.MainNotions.TwConjAt D N ∧
    ∃ (N0 : D.ntw.Tw → ℕ) (S : ∀ (i' : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i' j b)),
      Formalism.MainNotions.TwGoodAt D N ⟨Formalism.MainNotions.twEOf T, N0, S⟩

def sExpl (D : D7) (L : SizeData₂ D) (Z : DivX D) (C : ℝ) : ℝ := sFrame D.div.Nu (hExpl6 D L Z C)

def FrameNumberBound (D : D7) (L : SizeData₂ D) (Z : DivX D) (Csz CH : ℝ) : Prop :=
  sExpl D L Z Csz + D.div.RR.muMax ≤ L.sc.x ^ CH * L.sc.b

section ThmF

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end ThmF

def ComplementTwoFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, adm11 (Fm.D x i) (Fm.L x i) C

def ComplementCountFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, adm13 (Fm.D x i)

def FrameNumberBoundFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Csz CH : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, FrameNumberBound (Fm.D x i) (Fm.L x i) (Fm.X x i) Csz CH

open Formalism.FrobeniusOrbits

def MuH (D : D7) (u : D.what₂.Word) : HLat D.what₂.LL := { D.div.Nu u with L := MramL D u }


open Classical in
def wAt (D : D7) (j : ℕ) (g : D.R.GG) : ℝ :=
  if h : g ∈ D.R.Psi then wSz D j (D.eTau.symm ⟨g, h⟩) else 0

section Derived

variable {D : D7} (L : SizeData₂ D)

def IOsum : ℝ := ∑ w ∈ L.supp, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (L.io w : ℝ)

def askPrimes (a : ℤ) : Finset ℕ := (Finset.range (a.toNat + 1)).filter Nat.Prime


open Classical in
def ASK : ℝ :=
  ∑ j ∈ SizeData₂.lifts D, ∑ t : D.host.TT,
    ((∑ p ∈ (askPrimes (L.aT t)).filter (fun p => InertK D p),
        2 * Real.log p * L.vonMangoldtClassSum j t p) +
      Real.log D.host.d * ZetaZeroFreeRegion.askD D (L.aT t : ℝ) (wAt D j) (D.R.tau1 (t : D.R.A)))

def LoU (C : ℝ) (u : D.what₂.Word) : ℝ :=
  C * IOsum L + C * nTT D * D.R.m * (L.sc.a / D.R.k + L.sc.b') * Real.log ((D.mem u).A.T : ℝ) +
    C * L.sc.X'' D.R.n + 1


end Derived

section admitted

variable {D : D7} {L : SizeData₂ D}

def DropDef (Gi : G.Inst D L) (K : G.Consts) (Cr : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → (p ∈ L.drop ↔ NoGain Gi K Cr p ∧ ∀ u, p ≠ (D.mem u).A.T)

def Defs (Gi : G.Inst D L) (K : G.Consts) (Cr : ℝ) : Prop :=
  NprimeDef D L ∧ NuDef D L ∧ DropDef Gi K Cr ∧ ∀ w, G.ParametersFill Gi K w

end admitted

section Adm2

variable {D : D7} (L : SizeData₂ D)

end Adm2

section Adm3

variable {D : D7} {L : SizeData₂ D}


end Adm3

section Adm4

variable {D : D7} (L : SizeData₂ D)

def FrobeniusExpansionCongruence (C : ℝ) : Prop :=
  ∀ u,
    (-(∑ t : D.host.TT, ((L.aT t : ℝ) / D.R.k) * Real.log ((D.mem u).A.T : ℝ)) -
        C * nTT D * L.sc.a * Real.log D.R.k -
        C * D.R.f * D.R.k * (L.sc.b' + L.Sc) * Real.log D.R.k -
        C * D.R.f * L.Sc * Real.log ((D.mem u).A.T : ℝ) -
        C * D.R.f * (D.R.k : ℝ) ^ 2 * L.sc.L ≤ ((D.fm u).lat 0).mu) ∧
    ((D.fm u).lat 0).muMax ≤ C * nTT D * L.sc.a * Real.log (D.R.k * D.host.v) +
      C * D.R.f * (L.sc.b' + L.Sc) * (D.R.k * Real.log (D.R.k * D.host.v) +
        Real.log ((D.mem u).A.T : ℝ)) + C * D.R.f * (D.R.k : ℝ) ^ 2 * L.sc.L


open Classical in
def adm26 (C : ℝ) : Prop :=
  ∀ u,
    ((D.mem u).A.du : ℝ) = (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f * (D.duS u : ℝ) ∧
    (MuH D u).mu = ((D.fm u).lat 0).mu -
      (D.R.f : ℝ) * Real.log (((D.mem u).A.T : ℝ) - 1) / (((D.mem u).A.T : ℝ) - 2) ∧
    (MuH D u).muMax ≤ ((D.fm u).lat 0).muMax ∧
    (∀ w, D.what₂.places.resChar w = (D.mem u).A.T → LocLe (D.plEq w) 0 (L.NuLat u) (MramL D u)) ∧
    ∀ S : Finset D.what₂.places.Pl, (∀ w ∈ S, D.what₂.places.resChar w = (D.mem u).A.T) →
      (∑ w ∈ S, SizeData₂.sz w (L.lenMN u w)) / ((D.mem u).A.du : ℝ) ≤
        C * nTT D * D.R.m * (L.sc.a / D.R.k + L.sc.b') * Real.log ((D.mem u).A.T : ℝ)

end Adm4

section Adm5

variable {D : D7} {L : SizeData₂ D}

end Adm5

def Conclusion4 {D : D7} {L : SizeData₂ D} (Gi : G.Inst D L) (K : G.Consts) (C Cr : ℝ) : Prop :=
  Defs Gi K Cr →
  ∀ u, (D.div.Nu u).muMax ≤ ((D.fm u).lat 0).muMax + L.Ga + L.Fo - L.Ee u + C * D.R.m * L.B0 ∧
    ((D.fm u).lat 0).mu + L.Ga + L.Fo - L.Ee u - LoU L C u ≤ (D.div.Nu u).mu

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

theorem defs_fam {x : ℝ} (hx : Fm.x1 < x) (i : Fm.Ix x) : Defs (Fm.Gx x i) Fm.GK Fm.Cr :=
  ⟨Fm.nprimeDef x hx i, Fm.nuDef x hx i, fun p hp => Fm.drop_iff x hx i p hp, fun w => Fm.fills x hx i w⟩

end Fam

section FamV

open Filter

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def SlopesFamily : Prop := ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i, FrobeniusExpansionCongruence (Fm.L x i) C

def LevelTFamily : Prop := ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i, adm26 (Fm.L x i) C

def SlopeLemmaFamily : Prop := ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i, Conclusion4 (Fm.Gx x i) Fm.GK C Fm.Cr

end FamV

end Formalism.MainNotions.LocalQuadraticParts

end
end

section -- merged from Formalism.SharpRestriction.Divisibility.LatticeTransfer
noncomputable section

open NumberField MvPolynomial Finset
open scoped BigOperators

namespace Formalism.MainNotions.LatticeTransfer

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

def wt (Tau : Type) [Fintype Tau] (N : ℕ) : Vm Tau N → ℕ
  | Sum.inl _ => 1
  | Sum.inr (_, k) => k

structure Loc (D : D7) (XD : DivX D) where

  rt : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev) (p : ℕ) [Fact p.Prime]
    (la : XD.PlP p) (z : XD.Mp S κ p la), Bool × Rt D.what₂.Tau (XD.shv S κ).N → (XD.md S κ p la z).Z.LB

  rt_lie : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
    ∀ (i : Fin (rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ)) (i' : Fin (XD.shv S κ).N),
      (i' : ℕ) = i →
      rt S κ p la z (false, (τ0, i')) = ((XD.md S κ p la z).lie τ).x i ∧
      rt S κ p la z (true, (τ0, i')) = ((XD.md S κ p la z).lie τ).x' i

  rt_om : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
    ∀ (i : Fin ((XD.shv S κ).N - rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ))
      (i' : Fin (XD.shv S κ).N), (i' : ℕ) = (XD.shv S κ).j + i →
      rt S κ p la z (false, (τ0, i')) = ((XD.md S κ p la z).om τ).x i ∧
      rt S κ p la z (true, (τ0, i')) = ((XD.md S κ p la z).om τ).x' i

  lieW_gen : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la), ∃ (e : Fin (D.R.f * (XD.shv S κ).N) ≃ Rt D.what₂.Tau (XD.shv S κ).N)
      (V : Fin (D.R.f * (XD.shv S κ).N) → (XD.md S κ p la z).Z.VDiv), ∀ l,
      (XD.md S κ p la z).Z.c1 ((XD.md S κ p la z).lieW.x l) =
        (if ((e l).2 : ℕ) < (XD.shv S κ).j then (1 : ℚ) else -1) •
            (XD.md S κ p la z).Z.c1 (rt S κ p la z (false, e l)) +
          (XD.md S κ p la z).Z.cD (V l)

section One
variable (D : D7) (XD : DivX D) (T : Loc D XD)
  (S : letI := D.host.cmStar; HSpace D.host.E) (κ : XD.Lev)

def adm1 : Prop :=
  ∀ p : ℕ, p.Prime → ∀ c : (XD.shv S κ).FibComp p, ¬ (XD.shv S κ).fibInBd p c

end One

def PointsLemma (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) : Prop :=
  ∀ S κ, HidaSetting D XD S κ → DIV.Align.LevB P κ → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ),
  p.Prime → p ≠ 2 → UnramE D p → p ∉ (XD.shv S κ).lev → ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
  ∀ Q : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℝ,
    Q.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) m →
    (XD.shv S κ).arMix Sx R p
        ((tagDR D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k) -
          tagHT D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k)) * Q) =
      Real.log p * ((∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          (XD.shv S κ).chern (chLie (XD.shv S κ).j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) *
            collapse D _ Q)) -
        (XD.shv S κ).chern (chLie (XD.shv S κ).j (k - 1) (Sum.inl τ) * collapse D _ Q) /
          ((p : ℝ) - 1))

section One1
variable (D : D7) (XD : DivX D) (T : Loc D XD)
  (S : letI := D.host.cmStar; HSpace D.host.E) (κ : XD.Lev)

end One1

end Formalism.MainNotions.LatticeTransfer

end
end

section -- merged from Formalism.SharpRestriction.Divisibility.ZetaProductPairs
noncomputable section

namespace Formalism.MainNotions.ZetaProductPairs

open Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Loc (D : D7) (T : ThetaX D) where

  gl1 : D.what₂.Word → T.Gf (D.sp.Y 0)

  glSym : D.what₂.Word → T.Gf (D.sp.Y 0)

  ArchDat : D.what₂.Word → Type
  ArchDat_ne : ∀ u, Nonempty (ArchDat u)

  ellT : ∀ u, ArchDat u → ℂ

  Au : ∀ u, ArchDat u → ℂ

  B0 : ∀ u, D.what₂.Mu u →ₗ[ℂ] D.what₂.EE →ₗ[ℂ] ℂ

  zeX : D.what₂.Word → D.what₂.Tup → ℂ

  zeta_at_base_tuple : ∀ u, zeX u D.what₂.mu0 = 1

  zeX_fin : ∀ u μ, ∃ n : ℕ, 0 < n ∧ zeX u μ ^ n = 1

variable {D : D7}

variable {T : ThetaX D}

section Local

open MeasureTheory Matrix ComplexConjugate Finset

def qE (q : ℝ) (a c : ℕ) : ℝ := ∏ i ∈ Icc a c, (1 - q ^ (-(i : ℤ)))

def zetaProd (q : ℝ) (n : ℕ) : ℝ := (qE q 1 n)⁻¹

def idxPar (q : ℝ) (r s : ℕ) : ℝ := TH.parIdx q r s

def Lpair (q : ℝ) (t : ℕ) (x : ℂ) : ℂ :=
  (∏ s ∈ Icc 1 t, ((1 - x * ((q : ℂ) ^ (-(s : ℤ)))) * (1 - x⁻¹ * ((q : ℂ) ^ (-(s : ℤ))))))⁻¹


end Local

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (A : TH.ProvA)
  (GF : ∀ x (i : Fm.Ix x), Formalism.MainNotions.product_first_zeroth_parts.Th22 (Fm.D x i))
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.ex x hx i).th)

end Family

end Formalism.MainNotions.ZetaProductPairs

end
end

section -- merged from Formalism.SharpRestriction.Divisibility.SmallFirstModulusBelowScale
noncomputable section

namespace Formalism.MainNotions.DIV.Align

open Formalism.BasicNotions Formalism.MainNotions

def SmallFirstModulusBelowScale {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), ((AbsolutelyIrreducibleSpan.q0 (Fm.D x i) : ℕ) : ℝ) < (Fm.L x i).sc.X'

end Formalism.MainNotions.DIV.Align

end
end
