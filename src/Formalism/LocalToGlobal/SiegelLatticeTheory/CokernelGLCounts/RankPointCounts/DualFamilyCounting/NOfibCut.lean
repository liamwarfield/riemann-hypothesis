module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFixPushIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlphaDiscriminantHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GluingProductHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBR

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibCut
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} (X : HidaSetting D)

abbrev BV : Type := ∀ q : CBlk D.R.rS, CSpc (InfinitePlace X.B.I.F) D.R.k q

def iQ (D : D7) (b a : Fin D.R.rS) : Set D.host.E :=
  ((aaD D b * (aaD D a)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)

def iP (D : D7) (b a : Fin D.R.rS) : Set D.host.E :=
  ((aaD D b * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)

def pW (y : (VS D).V) : (VS D).V :=
  y - ∑ c, (VS D).hT (X.fY c) y • X.eX c - ∑ c, (VS D).hT (X.eX c) y • X.fY c

def InW (y : (VS D).V) : Prop := ∀ c, (VS D).hT (X.eX c) y = 0 ∧ (VS D).hT (X.fY c) y = 0

def Xq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  fun b a => (VS D).hT (X.fY b) (n (X.eX a))

def Aq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  fun b a => (VS D).hT (X.fY b) (n (X.fY a))

def Mq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  (Xq X n)⁻¹ * Aq X n

def xq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (b : Fin D.R.rS) : (VS D).V := pW X (n.symm (X.fY b))

def Gq (D : D7) (xs : Fin D.R.rS → (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  fun b c => (VS D).hT (xs b) (xs c)

def Gp (D : D7) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V) :
    Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  X0⁻¹ * Gq D xs * (X0⁻¹)ᴴ

def DataOK (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) : Prop :=
  (∀ b a : Fin D.R.rS, a < b → X0 b a = 0) ∧ (∀ a, X0 a a = 1) ∧ (∀ b, InW X (xs b)) ∧ M + Mᴴ = -Gp D X0 xs

def LatQ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) : Prop :=
  (∀ b a : Fin D.R.rS, b < a → X0 b a ∈ iQ D b a) ∧ (∀ b, xs b ∈ aaLb X b) ∧ ∀ b a, M b a ∈ iP D b a

variable (u : D.what₂.Word)

def NFl (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
    (∀ j, ∀ x ∈ Xflag (lf D (X.Fu u)) (j + 1), n x - x ∈ Xflag (lf D (X.Fu u)) j) ∧
    ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u))), n x - x ∈ Xsp (lf D (X.Fu u))

def blkQ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) :
    ∀ p : CBlk D.R.rS, CSpc (InfinitePlace X.B.I.F) D.R.k p
  | Sum.inl (Sum.inl p) => embV X (X0 p.1.1 p.1.2)
  | Sum.inl (Sum.inr b) => rowV X u (xs b)
  | Sum.inr (Sum.inl p) => fun v =>
      (embS D (X.pl v) (M p.1.1 p.1.2) - star (embS D (X.pl v) (M p.1.2 p.1.1))) / 2
  | Sum.inr (Sum.inr a) => fun v => (embS D (X.pl v) (M a a)).im


open scoped Classical in
def theta (D : D7) : D.host.E :=
  if h : ∃ t : D.host.E, IsIntegral ℤ t ∧ t + D.host.conj t = 1 then h.choose else 0

def Xc (x : BV X) (v : InfinitePlace X.B.I.F) :
    Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  fun b a => if h : b < a then x (Sum.inl (Sum.inl ⟨(b, a), h⟩)) v else if b = a then 1 else 0

def Gc (x : BV X) (v : InfinitePlace X.B.I.F) :
    Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  fun b c => (∑ j : Fin D.R.k, x (Sum.inl (Sum.inr b)) v (Fin.castSucc j) *
      star (x (Sum.inl (Sum.inr c)) v (Fin.castSucc j))) -
    x (Sum.inl (Sum.inr b)) v (Fin.last D.R.k) * star (x (Sum.inl (Sum.inr c)) v (Fin.last D.R.k)) /
      (((D.mem u).A.T : ℕ) : ℂ)

def Hc (x : BV X) (v : InfinitePlace X.B.I.F) :
    Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  (Xc X x v)⁻¹ * Gc X u x v * ((Xc X x v)⁻¹)ᴴ

def tauQ : ∀ p : CBlk D.R.rS, BV X → CSpc (InfinitePlace X.B.I.F) D.R.k p
  | Sum.inl (Sum.inl _) => fun _ => 0
  | Sum.inl (Sum.inr _) => fun _ => 0
  | Sum.inr (Sum.inl p) => fun x v => Hc X u x v p.1.1 p.1.2 / 2
  | Sum.inr (Sum.inr a) => fun x v => -((Hc X u x v a a).re * (embS D (X.pl v) (theta D)).im)

end Defs

def NOratC : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf),
    s ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ↔
      ∃ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x n ∧ x.1 = s ∧
        n ∈ NLam (VS D).L0 (lf D (X.Fu u))

def DictGram : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    NFl X u n → DataOK X (Xq X n) (xq X n) (Mq X n)

def DictLat : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    NFl X u n → (Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0 ↔ LatQ X (Xq X n) (xq X n) (Mq X n))

def DictEx : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (xs : Fin D.R.rS → (VS D).V) (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E), DataOK X X0 xs M →
    ∃ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, NFl X u n ∧ Xq X n = X0 ∧ xq X n = xs ∧ Mq X n = M

def DictPlace : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    RatLink X x n → NFl X u n → blk X u x.1 = blkQ X u (Xq X n) (xq X n) (Mq X n)

def FibQ : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (xs : Fin D.R.rS → (VS D).V) (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E), DataOK X X0 xs M →
    ((∀ p, blkQ X u X0 xs M p - tauQ X u p (blkQ X u X0 xs M) ∈ cLat X u p) ↔ LatQ X X0 xs M)

def FibOnto : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (x : BV X),
    (∀ p, x p - tauQ X u p x ∈ cLat X u p) →
      ∃ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
        (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E), DataOK X X0 xs M ∧ blkQ X u X0 xs M = x

def ThetaEx : Prop :=
  ∀ D : D7, ∃ t : D.host.E, IsIntegral ℤ t ∧ t + D.host.conj t = 1

theorem tauQ_lower {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (p : CBlk D.R.rS)
    (x x' : BV X) (h : ∀ q, cHgt q < cHgt p → x q = x' q) :
    tauQ X u p x = tauQ X u p x' := by
  rcases p with (p | b) | (p | a)
  · rfl
  · rfl
  all_goals
    have hX : ∀ q, x (Sum.inl q) = x' (Sum.inl q) := by
      intro q
      apply h
      rcases q with q | c
      · have := q.1.2.isLt
        simp only [cHgt]
        omega
      · have := c.isLt
        simp only [cHgt]
        omega
    have hH : Hc X u x = Hc X u x' := by
      funext v
      have hXc : Xc X x v = Xc X x' v := by
        funext i j
        simp only [Xc, hX]
      have hGc : Gc X u x v = Gc X u x' v := by
        funext i j
        simp only [Gc, hX]
      simp only [Hc, hXc, hGc]
    simp only [tauQ]
    rw [hH]

theorem nofibLat_of (hR : NOratC) (hG : DictGram) (hL : DictLat) (hE : DictEx) (hP : DictPlace) (hF : FibQ)
    (hO : FibOnto) : NOfibLat := by
  intro D X u
  refine ⟨tauQ X u, fun p x x' h => tauQ_lower X u p x x' h, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨xA, n, hlink, hx1, hn⟩ := (hR X u s).1 hs
    have hNF : NFl X u n := ⟨hn.1.1, hn.2.1, hn.2.2⟩
    have hD := hG X u n hNF
    have hLat := (hL X u n hNF).1 hn.1.2
    rw [← hx1, hP X u xA n hlink hNF]
    exact (hF X u _ _ _ hD).2 hLat
  · intro hx
    obtain ⟨X0, xs, M, hD, rfl⟩ := hO X u x hx
    have hLat := (hF X u X0 xs M hD).1 hx
    obtain ⟨n, hNF, h1, h2, h3⟩ := hE X u X0 xs M hD
    subst h1 h2 h3
    have hgm := (hL X u n hNF).2 hLat
    have hn : n ∈ NLam (VS D).L0 (lf D (X.Fu u)) := ⟨⟨hNF.1, hgm⟩, hNF.2.1, hNF.2.2⟩
    obtain ⟨xA, hlink⟩ := ratPt_holds D X n hNF.1
    exact ⟨xA.1, (hR X u xA.1).2 ⟨xA, n, hlink, rfl, hn⟩, hP X u xA n hlink hNF⟩

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GluingMassHolds
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PushforwardOrthComplement
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G9

theorem cJof_cast {F : Type} [Field F] {n n' : ℕ} (e : n' = n) (𝔭 : Ideal (𝓞 F)) (a : Fin n → 𝓞 F) :
    cJof 𝔭 (fun i : Fin n' => a (Fin.cast e i)) = cJof 𝔭 a := by
  subst e
  rfl

theorem vJof_cast {F : Type} [Field F] {n n' : ℕ} (e : n' = n) (𝔭 : Ideal (𝓞 F)) (a : Fin n → 𝓞 F) :
    vJof 𝔭 (fun i : Fin n' => a (Fin.cast e i)) = vJof 𝔭 a := by
  subst e
  rfl

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}

theorem isTotPosDef_formOn (hpos : PosDefOn h (orthK h U)) :
    IsTotPosDef (formOn h (orthK h U)) :=
  fun x hx φ => hpos x x.2 (fun e => hx (Subtype.ext e)) φ

theorem jordan_data (h1 : JordanExists) (h5 : AlphaDisc) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hnd : Nondeg h) (hc : IsCompl U (orthK h U)) (hpos : PosDefOn h (orthK h U))
    (T : Submodule (𝓞 K) ↥(orthK h U)) (hT : Submodule.IsFullLattice K T)
    (hTi : Formalism.HermitianLatticesTheory.IsIntegralLat (formOn h (orthK h U)) T) (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsMaximal) :
    vJ h (orthK h U) (push _ T) 𝔭 = vd (formOn h (orthK h U)) T 𝔭 ∧
    alphaL (formOn h (orthK h U)) T 𝔭 = (discAut h (orthK h U) (push _ T) 𝔭 : ℝ) *
      alphaStd K 𝔭 (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T) 𝔭) ∧
    (vd (formOn h (orthK h U)) T 𝔭 = 0 → cJ h (orthK h U) (push _ T) 𝔭 = 0) := by
  have hWs := formOn_isSymm hs (orthK h U)
  have hWd := isTotPosDef_formOn hpos
  have hex : ∀ b a, IsJordanIn h (orthK h U) (push _ T) 𝔭 b a →
      vJof 𝔭 a = vd (formOn h (orthK h U)) T 𝔭 ∧
      alphaL (formOn h (orthK h U)) T 𝔭 = (discAut h (orthK h U) (push _ T) 𝔭 : ℝ) *
        alphaStd K 𝔭 (finrank K ↥(orthK h U) - cJof 𝔭 a) := by
    intro b a hb
    have hb' := isJordanIn_top h𝔭.isPrime hb
    have e1 := (h1 K F ↥(orthK h U) hK hF (formOn h (orthK h U)) hWs).2 T hT.toIsLattice 𝔭 h𝔭 _ _ hb'
    have e2 := h5 K F ↥(orthK h U) hK hF (formOn h (orthK h U)) hWs hWd T hT.toIsLattice hTi 𝔭 h𝔭 _ _ hb'
    rw [vJof_cast] at e1
    rw [cJof_cast, ← discAut_push h𝔭.isPrime] at e2
    exact ⟨e1.symm, e2⟩
  obtain ⟨b, a, hb⟩ := (h1 K F V hK hF h hs).1 (orthK h U) (push _ T) (nondegenerate_on_orth_compl hs hnd hc)
    ((isLatIn_push_iff_isLattice T).2 hT) ((isIntegralLat_push T).2 hTi) 𝔭 h𝔭
  have hvJ : vJ h (orthK h U) (push _ T) 𝔭 = vd (formOn h (orthK h U)) T 𝔭 := by
    unfold vJ
    obtain ⟨b', a', hb', e⟩ := Nat.sInf_mem (⟨_, b, a, hb, rfl⟩ :
      Set.Nonempty {v | ∃ b a, IsJordanIn h (orthK h U) (push _ T) 𝔭 b a ∧ v = vJof 𝔭 a})
    rw [e]
    exact (hex b' a' hb').1
  obtain ⟨b₀, a₀, hb₀, e₀⟩ := Nat.sInf_mem (⟨_, b, a, hb, rfl⟩ :
    Set.Nonempty {c | ∃ b a, IsJordanIn h (orthK h U) (push _ T) 𝔭 b a ∧ c = cJof 𝔭 a})
  have hcJ : cJ h (orthK h U) (push _ T) 𝔭 = cJof 𝔭 a₀ := e₀
  refine ⟨hvJ, by rw [hcJ]; exact (hex b₀ a₀ hb₀).2, fun hv => ?_⟩
  rw [hcJ]
  have h0 := (hex b₀ a₀ hb₀).1
  rw [hv] at h0
  unfold vJof at h0
  unfold cJof
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _ hi
  exact hi ((Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ _))

theorem mem_of_isLatIn {X : Submodule K V} {T : Submodule (𝓞 K) V} (hT : IsLatIn X T) :
    ∀ v ∈ T, v ∈ X := fun _ hv => hT.2 ▸ Submodule.subset_span hv

theorem full_of_sameGenusFix {A B : Submodule (𝓞 K) ↥(orthK h U)}
    (hA : Submodule.IsFullLattice K A) (hB : Submodule.IsLattice K B)
    (hg : SameGenusFix (F := F) h U (push _ A) (push _ B))
    (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hc : IsCompl U (orthK h U)) : Submodule.IsFullLattice K B := by
  obtain ⟨𝔭, h𝔭⟩ := Ideal.exists_maximal (α := 𝓞 F)
  have hg' := (sameGenusFix_push_iff hK hF hs hc A B).1 hg
  rw [GoodGenusOrbits.sameGenus_iff (F := F) hK hF A B] at hg'
  obtain ⟨g, hg, he⟩ := hg' ⟨𝔭, h𝔭⟩
  have hspan : ∀ x ∈ A, g x ∈ Submodule.span K (B : Set ↥(orthK h U)) := by
    intro x hx
    apply Formalism.L2.SG.Pf.GluingBases.locF_subset_span h𝔭.isPrime B
    rw [← he]
    exact ⟨x, LocF.le_locF 𝔭 A hx, rfl⟩
  refine { toIsLattice := hB, span_eq_top := ?_ }
  apply top_unique
  intro x _
  have hx : g.symm x ∈ Submodule.span K (A : Set ↥(orthK h U)) := by rw [hA.span_eq_top]; trivial
  have hk : ∀ y ∈ Submodule.span K (A : Set ↥(orthK h U)), g y ∈ Submodule.span K (B : Set ↥(orthK h U)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hspan y hy
    | zero => simp
    | add y z hy hz ihy ihz => simpa using (Submodule.add_mem _ ihy ihz)
    | smul a y hy ih => simpa using (Submodule.smul_mem _ a ih)
  simpa using hk (g.symm x) hx

theorem genusMassW_of (h1 : JordanExists) (h5 : AlphaDisc) : GenusMassW := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hc hpos T₀ hT₀ hT₀i c hmc
  obtain ⟨T', rfl⟩ : ∃ T', push (orthK h U) T' = T₀ := ⟨_, push_pull (mem_of_isLatIn hT₀)⟩
  have hT' : Submodule.IsFullLattice K T' := (isLatIn_push_iff_isLattice T').1 hT₀
  have hT'i := (isIntegralLat_push T').1 hT₀i
  have hWs := formOn_isSymm hs (orthK h U)
  have hWd := isTotPosDef_formOn hpos
  have hMB := Formalism.HermitianLatticesTheory.massBasic K ↥(orthK h U) (formOn h (orthK h U)) hWs
    (StabilizerLattices.trace_pos hWd) T' hT'
  obtain ⟨s', hs'⟩ := hMB.1
  have hmass := hMB.2.1 s' hs'
  have hMpos := hMB.2.2
  have hMC := hmc ↥(orthK h U) (formOn h (orthK h U)) T' hWs hWd rfl hT' hT'i
  refine ⟨s'.image (push (orthK h U)), ?_, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hT
    have hg := hs'.1 N hN
    exact ⟨(isLatIn_push_iff_isLattice N).2 hg.1, (sameGenusFix_push_iff hK hF hs hc T' N).2 hg.2⟩
  · intro T hT hgen
    obtain ⟨N, rfl⟩ : ∃ N, push (orthK h U) N = T := ⟨_, push_pull (mem_of_isLatIn hT)⟩
    have hN : N ∈ Formalism.HermitianLatticesTheory.genus (formOn h (orthK h U)) T' :=
      ⟨(isLatIn_push_iff_isLattice N).1 hT, (sameGenusFix_push_iff hK hF hs hc T' N).1 hgen⟩
    obtain ⟨N₁, ⟨hN₁, g, hg, hgN⟩, huniq⟩ := hs'.2 N hN
    refine ⟨push _ N₁, ⟨Finset.mem_image_of_mem _ hN₁, extId hc g, extId_mem hs hc hg, ?_⟩, ?_⟩
    · rw [gmap_extId_push hs hc hg, hgN]
    · rintro T₂ ⟨hT₂, g₂, hg₂, e₂⟩
      obtain ⟨N₂, hN₂, rfl⟩ := Finset.mem_image.mp hT₂
      have e : N₂ = N₁ := huniq N₂ ⟨hN₂, restr hg₂, restr_mem hg₂,
        push_injective _ (by rw [← gmap_push hg₂, e₂])⟩
      rw [e]
  · intro T hT _
    obtain ⟨N, rfl⟩ : ∃ N, push (orthK h U) N = T := ⟨_, push_pull (mem_of_isLatIn hT)⟩
    have hfin := Formalism.HermitianLatticesTheory.autFinite K ↥(orthK h U) (formOn h (orthK h U)) hWs (StabilizerLattices.trace_pos hWd) N
      ((isLatIn_push_iff_isLattice N).1 hT)
    have : Finite ↥(Formalism.ThetaLiftIndependence.autL (formOn h (orthK h U)) N) := hfin.to_subtype
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (stabEquivW hs hc N).symm)
  · rw [Finset.sum_image (fun x _ y _ e => push_injective _ e)]
    simp_rw [card_stab_push hs hc]
    rw [← hmass, hMC]
    have hZ := finite_vd_ne_zero hK hF hWs hWd hT' hT'i
    set Z := hZ.toFinset with hZdef
    have hout : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ Z →
        vd (formOn h (orthK h U)) T' 𝔭.1 = 0 := fun 𝔭 h𝔭 => by
      rw [hZdef, Set.Finite.mem_toFinset] at h𝔭
      exact not_not.mp h𝔭
    have hlam₀ : ∀ 𝔭 ∉ Z, lamP (formOn h (orthK h U)) T' 𝔭.1 = 1 :=
      fun 𝔭 h𝔭 => localMassFactor_of_valuation_eq_zero hK hF hWs hWd hT' hT'i 𝔭.2 (hout 𝔭 h𝔭)
    have hjd := fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} =>
      jordan_data h1 h5 hK hF hs hnd hc hpos T' hT' hT'i 𝔭.1 𝔭.2
    have hlam : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
        lamP (formOn h (orthK h U)) T' 𝔭.1 =
          alphaStd K 𝔭.1 (finrank K ↥(orthK h U)) *
            (Ideal.absNorm 𝔭.1 : ℝ) ^ (finrank K ↥(orthK h U) * vd (formOn h (orthK h U)) T' 𝔭.1) /
          ((discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) *
            alphaStd K 𝔭.1 (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T') 𝔭.1)) := by
      intro 𝔭
      unfold lamP
      rw [(hjd 𝔭).2.1]
    have hD1 : ∀ 𝔭 ∉ Z, discAut h (orthK h U) (push _ T') 𝔭.1 = 1 := by
      intro 𝔭 h𝔭
      have hv := hout 𝔭 h𝔭
      have hl := hlam₀ 𝔭 h𝔭
      rw [hlam 𝔭, hv, (hjd 𝔭).2.2 hv, Nat.sub_zero, mul_zero, pow_zero, mul_one] at hl
      have hA := (alphaStd_pos hK hF 𝔭.2 (finrank K ↥(orthK h U))).ne'
      have hDA : (discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) *
          alphaStd K 𝔭.1 (finrank K ↥(orthK h U)) ≠ 0 := fun e => by
        rw [e, div_zero] at hl
        exact zero_ne_one hl
      have e := (div_eq_one_iff_eq hDA).mp hl
      have e' : (discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) = 1 :=
        mul_right_cancel₀ hA (by rw [one_mul]; exact e.symm)
      exact_mod_cast e'
    have e1 : ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, discAut h (orthK h U) (push _ T') 𝔭.1 =
        ∏ 𝔭 ∈ Z, discAut h (orthK h U) (push _ T') 𝔭.1 := tprod_eq_prod hD1
    have e2 : lamG F (formOn h (orthK h U)) T' = ∏ 𝔭 ∈ Z, lamP (formOn h (orthK h U)) T' 𝔭.1 := by
      unfold lamG
      exact tprod_eq_prod hlam₀
    have e3 : nM F h (orthK h U) (push _ T') =
        ∏ 𝔭 ∈ Z, (Ideal.absNorm 𝔭.1 : ℝ) ^ vd (formOn h (orthK h U)) T' 𝔭.1 := by
      unfold nM
      simp_rw [fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => (hjd 𝔭).1]
      exact tprod_eq_prod fun 𝔭 h𝔭 => by rw [hout 𝔭 h𝔭, pow_zero]
    have e4 : ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, alphaStd K 𝔭.1 (finrank K ↥(orthK h U)) /
          alphaStd K 𝔭.1 (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T') 𝔭.1) =
        ∏ 𝔭 ∈ Z, alphaStd K 𝔭.1 (finrank K ↥(orthK h U)) /
          alphaStd K 𝔭.1 (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T') 𝔭.1) :=
      tprod_eq_prod fun 𝔭 h𝔭 => by
        rw [(hjd 𝔭).2.2 (hout 𝔭 h𝔭), Nat.sub_zero,
          div_self (alphaStd_pos hK hF 𝔭.2 (finrank K ↥(orthK h U))).ne']
    have hDne : ∀ 𝔭 ∈ Z, (discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) ≠ 0 := by
      intro 𝔭 h𝔭 e
      have h0 : lamP (formOn h (orthK h U)) T' 𝔭.1 = 0 := by rw [hlam 𝔭, e, zero_mul, div_zero]
      have : Formalism.HermitianLatticesTheory.mass (formOn h (orthK h U)) T' = 0 := by
        rw [hMC, e2, Finset.prod_eq_zero h𝔭 h0, mul_zero]
      linarith
    have key : ∀ 𝔭 ∈ Z, (discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) * lamP (formOn h (orthK h U)) T' 𝔭.1 =
        ((Ideal.absNorm 𝔭.1 : ℝ) ^ vd (formOn h (orthK h U)) T' 𝔭.1) ^ finrank K ↥(orthK h U) *
          (alphaStd K 𝔭.1 (finrank K ↥(orthK h U)) /
            alphaStd K 𝔭.1 (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T') 𝔭.1)) := by
      intro 𝔭 h𝔭
      have hB := (alphaStd_pos hK hF 𝔭.2
        (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T') 𝔭.1)).ne'
      rw [hlam 𝔭, ← pow_mul, mul_comm (vd _ _ _) (finrank K _)]
      field_simp [hDne 𝔭 h𝔭, hB]
    rw [e1, e2, e3, e4, Nat.cast_prod, ← Finset.prod_pow]
    calc (∏ 𝔭 ∈ Z, (discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ)) *
          (c * ∏ 𝔭 ∈ Z, lamP (formOn h (orthK h U)) T' 𝔭.1)
        = c * ∏ 𝔭 ∈ Z, ((discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) *
            lamP (formOn h (orthK h U)) T' 𝔭.1) := by
          rw [Finset.prod_mul_distrib]
          ring
      _ = _ := by
          rw [Finset.prod_congr rfl key, Finset.prod_mul_distrib]
          ring

end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

namespace Formalism.L2.SG.Pf.Cnt

theorem genusMassW_of (h1 : JordanExists) (h5 : AlphaDisc) : GenusMassW :=
  OrthogonalComplementGenusMass.genusMassW_of h1 h5

theorem glueMass_of' (h1 : JordanExists) (h2 : JordanInv) (h5 : AlphaDisc) (h6 : GlueLoc)
    (h8 : GlueProd) : GlueMass :=
  glueMass_of h1 h2 h6 h8 (OrthogonalComplementGenusMass.genusMassW_of h1 h5)

end Formalism.L2.SG.Pf.Cnt
end
end

namespace Formalism.L2.SG.Pf.Cnt

theorem gluing_mass_holds : GlueMass :=
  glueMass_of' jordan_splitting_exists jordan_invariants_holds alpha_discriminant_holds local_gluing_holds gluing_product_holds

end Formalism.L2.SG.Pf.Cnt
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBRa
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def aaLbS (b : Fin D.R.rS) : Submodule (𝓞 D.host.E) (VS D).V :=
  Submodule.span (𝓞 D.host.E) {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l}

def TrDetUnimod : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (b : Fin D.R.rS) {N : ℕ}
    (m : Module.Basis (Fin N) ℤ ((aaLbS X b).restrictScalars ℤ)),
    N = Module.finrank ℚ D.host.E * (D.R.k + 1) →
    |(Matrix.of fun i j => Algebra.trace ℚ D.host.E ((VS D).hT (m i : (VS D).V) (m j : (VS D).V))).det| =
      |(discr D.host.E : ℚ)| ^ (D.R.k + 1) * (FractionalIdeal.absNorm (aaD D b) : ℚ) ^ (2 * (D.R.k + 1))

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNBoxOf
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem refNBox_of (hF : FrameRow) : RefNBox := by
  intro D X u w
  choose L hL hdet using fun v => hF X u w v
  have hTu := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) u
  have hTw := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) w
  have hdet0 : ∀ v, LinearMap.det (L v) ≠ 0 := fun v h0 => by
    have h1 := hdet v
    rw [h0, abs_zero] at h1
    exact (pow_pos (div_pos hTw hTu) _).ne' h1.symm
  have key : ∀ (s : X.B.I.Ginf) v i, LsNc5.kapV X w v s i =
      L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) (s v)) i := fun s v i => by
    have h1 := congrFun (hL v s) i
    rw [kapV_eq (X := X) u v s] at h1
    exact h1
  have hbox : LsNc5.boxN X w = X.NinfU w ∩ Set.univ.pi (fun v =>
      (fun g => L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) g)) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) := by
    rw [LsNc5.boxN_eq]
    congr 1
    ext s
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h v i
      rw [← key s v i]
      exact h (v, i)
    · rintro h ⟨v, i⟩
      show LsNc5.kapV X w v s i ∈ _
      rw [key s v i]
      exact h v i
  have hv : ∀ v, refNX X u v ((fun g => L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) g)) ⁻¹'
      Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) =
      ENNReal.ofReal ((2 : ℝ) ^ (D.R.rS ^ 2 + D.R.rS * D.R.k) * (Tw w ^ D.R.rS)⁻¹) := fun v => by
    obtain ⟨hae, hmap⟩ := refN_map_kapL (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v)
      (ProductExactness.zV X u v) hTu (fX_ee (X := X) (v := v)) (fX_ff (X := X) (v := v))
      (fX_ef (X := X) (v := v)) (fX_ww (X := X) (u := u) (v := v)) (fX_ew (X := X) (u := u) (v := v))
      (fX_fw (X := X) (u := u) (v := v)) (fX_ez (X := X) (u := u) (v := v))
      (fX_fz (X := X) (u := u) (v := v)) (frame_real_z_z_eq_neg (X := X) (u := u) (v := v))
      (fX_zw (X := X) (u := u) (v := v))
    have hmeas : MeasurableSet ((L v) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) :=
      (L v).continuous_of_finiteDimensional.measurable (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
    have hpre : (fun g => L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) g)) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1) =
        kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) ⁻¹' ((L v) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) := rfl
    rw [hpre, show refNX X u v = refNg (nX X) _ _ _ _ _ from rfl, ← Measure.map_apply_of_aemeasurable hae hmeas, hmap,
      Measure.smul_apply, smul_eq_mul, Measure.addHaar_preimage_linearMap _ (hdet0 v), Real.volume_pi_Ico]
    simp only [sub_zero, ENNReal.ofReal_one, Finset.prod_const_one, mul_one]
    rw [abs_inv, hdet v, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_pow]
    field_simp
  haveI : ∀ v, SigmaFinite (refNX X u v) := fun v =>
    (refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
      (ProductExactness.zV X u v) hTu (fX_ee (X := X) (v := v)) (fX_ff (X := X) (v := v))
      (fX_ef (X := X) (v := v)) (fX_ww (X := X) (u := u) (v := v)) (fX_ew (X := X) (u := u) (v := v))
      (fX_fw (X := X) (u := u) (v := v)) (fX_ez (X := X) (u := u) (v := v))
      (fX_fz (X := X) (u := u) (v := v)) (frame_real_z_z_eq_neg (X := X) (u := u) (v := v))
      (fX_zw (X := X) (u := u) (v := v)) (fX_ez (X := X) (u := u) (v := v))).1
  rw [hbox, Set.inter_comm, measure_inter_conull (refNX_haar X u w).2.2.1, Measure.pi_pi]
  simp only [hv, Finset.prod_const, Finset.card_univ]
  rw [← ENNReal.ofReal_pow (by positivity)]
  congr 1
  rw [inv_pow, ← inv_pow]
  ring

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXKS
noncomputable section

open MeasureTheory Matrix NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Inv

variable {r k : ℕ}

def RcInv (y : LsNc5.CIdx r k → ℝ) : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) :=
  (fun c => (⟨y (eIdx (Sum.inl (c, false))), y (eIdx (Sum.inl (c, true)))⟩ : ℂ), fun a => y (eIdx (Sum.inr a)))

theorem Rc_RcInv (y : LsNc5.CIdx r k → ℝ) : Rc (RcInv y) = y := by
  funext i
  obtain ⟨j, rfl⟩ := eIdx.surjective i
  rcases j with ⟨c, b⟩ | a
  · cases b <;> simp [Rc, RcInv, LsNc5.reim]
  · simp [Rc, RcInv]

theorem measurable_RcInv : Measurable (RcInv (r := r) (k := k)) := by
  apply Continuous.measurable
  unfold RcInv
  have h : Continuous fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ) := Complex.equivRealProdCLM.symm.continuous
  exact Continuous.prodMk (continuous_pi fun c => h.comp'
      (f := fun a : LsNc5.CIdx r k → ℝ => (a (eIdx (Sum.inl (c, false))), a (eIdx (Sum.inl (c, true)))))
      ((continuous_apply _).prodMk (continuous_apply _)))
    (continuous_pi fun a => continuous_apply _)

def dYInv (T : ℝ) (y : LsNc5.CIdx r k → ℝ) : LsNc5.CIdx r k → ℝ := fun i => y i / dY T i

theorem dY_pos {T : ℝ} (hT : 0 < T) (i : LsNc5.CIdx r k) : 0 < dY T i := by
  rcases i with (a | a) | a <;> simp [dY, hT]

theorem LyM_dYInv {T : ℝ} (hT : 0 < T) (y : LsNc5.CIdx r k → ℝ) : LyM T (dYInv T y) = y := by
  funext i
  simp only [LyM, Matrix.toLin'_apply, Matrix.mulVec_diagonal, dYInv]
  field_simp [(dY_pos hT i).ne']

theorem measurable_dYInv (T : ℝ) : Measurable (dYInv (r := r) (k := k) T) := by
  unfold dYInv
  exact Measurable.of_eval fun i => (measurable_pi_apply i).div_const _

end Inv

theorem surjLoc {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (w : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (w a) = 0) (hfw : ∀ c a, hJ ε (f c) (w a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (w a) = 0) :
    ∃ σL : (LsNc5.CIdx r k → ℝ) → Formalism.REAL.UJ ε, Measurable σL ∧
      ∀ y, σL y ∈ NLoc ε e z ∧ kapL ε e f w z (σL y) = y := by
  subst hn
  have hFJ := isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have emb := embQ hFJ
  have hQz : Qm e f w (z0v T z) *ᵥ zBv k r T = z := Qm_zB hT z
  set Ψ := cM (ε := ε) (Qi ε e f w (z0v T z)) (Qm e f w (z0v T z)) with hΨ
  let ψ0 : (LsNc5.CIdx r k → ℝ) → (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) := fun y => RcInv (dYInv T y)
  have hψ0 : Measurable ψ0 := measurable_RcInv.comp (measurable_dYInv T)
  let Φ : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) → Mt k r := fun t => WlocSk.NB.phi0 t.1 t.2
  have hΦc : Continuous Φ := WlocSk.NB.continuous_nilpotent_chart
  have hΦN : ∀ t : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ), WlocSk.NB.phi0 t.1 t.2 ∈ Nset k r := fun t =>
    WlocSk.NB.test_vector_mem_schwartz_bruhat t.1 t.2
  have hrange : ∀ t, Φ t ∈ Set.range Ψ := fun t => by
    refine ⟨toUJ _ (conjQ_UJ hFJ (hΦN t).1), ?_⟩
    show (Qi ε e f w (z0v T z) * uMat (toUJ _ (conjQ_UJ hFJ (hΦN t).1)) * Qm e f w (z0v T z) :
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 t.1 t.2
    rw [uMat_toUJ, Qi_Qm_conj hFJ]
  let σL : (LsNc5.CIdx r k → ℝ) → Formalism.REAL.UJ ε := fun y => emb.equivRange.symm ⟨Φ (ψ0 y), hrange (ψ0 y)⟩
  have hσΨ : ∀ y, Ψ (σL y) = Φ (ψ0 y) := fun y => by
    have h1 := emb.equivRange.apply_symm_apply ⟨Φ (ψ0 y), hrange (ψ0 y)⟩
    rw [MeasurableEmbedding.equivRange_apply] at h1
    exact congrArg Subtype.val h1
  have hz0 : ∃ t : ℂ, z0v T z = t • (Qm e f w (z0v T z) *ᵥ zBv k r T) :=
    ⟨(((Real.sqrt T)⁻¹ : ℝ) : ℂ), by rw [hQz]; rfl⟩
  refine ⟨σL, ?_, fun y => ⟨?_, ?_⟩⟩
  · exact emb.equivRange.symm.measurable.comp
      ((hΦc.measurable.comp hψ0).subtype_mk)
  · have hN : Qi ε e f w (z0v T z) * uMat (σL y) * Qm e f w (z0v T z) ∈ Nset k r := by
      have : (Qi ε e f w (z0v T z) * uMat (σL y) * Qm e f w (z0v T z) :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 (ψ0 y).1 (ψ0 y).2 := hσΨ y
      rw [this]; exact hΦN _
    have h1 := inN_of_conj hFJ (inWb_zB T) hN
    rw [hQz] at h1
    exact h1
  · have hN : Qi ε e f w (z0v T z) * uMat (σL y) * Qm e f w (z0v T z) ∈ Nset k r := by
      have : (Qi ε e f w (z0v T z) * uMat (σL y) * Qm e f w (z0v T z) :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 (ψ0 y).1 (ψ0 y).2 := hσΨ y
      rw [this]; exact hΦN _
    rw [kapL_eq hFJ hT (σL y) hN]
    show Kc T (Ψ (σL y)) = y
    rw [hσΨ y]
    funext i
    rw [chart_kappa_coordinates T (ψ0 y) i, ← LyM_apply]
    show LyM T (Rc (RcInv (dYInv T y))) i = y i
    rw [Rc_RcInv, LyM_dYInv hT]

theorem kapSurj_holds : KapSurj := by
  intro D X u
  have hloc := fun v : InfinitePlace X.B.I.F => surjLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v)
    (ProductExactness.zV X u v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
    (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v)
  choose σL hσm hσ using hloc
  refine ⟨fun t v => σL v (fun i => Φc t (v, i)), ?_, fun t => ⟨fun v => (hσ v _).1, ?_⟩⟩
  · exact Measurable.of_eval fun v => (hσm v).comp
      (Measurable.of_eval fun i => (measurable_pi_apply (v, i)).comp measurable_Φc)
  · have hk : Φc (blk X u (fun v => σL v (fun i => Φc t (v, i)))) = Φc t := by
      rw [← kap_eq_Φc]
      funext p
      have := (hσ p.1 (fun i => Φc t (p.1, i))).2
      have h2 := congrFun (kapV_eq X u p.1 (fun v => σL v (fun i => Φc t (v, i)))) p.2
      exact h2.trans (congrFun this p.2)
    have := congrArg Ψc hk
    rwa [Ψc_Φc, Ψc_Φc] at this

end Formalism.L2.SG.Pf.NcReal.JX
end
end
