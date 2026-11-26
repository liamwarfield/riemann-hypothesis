module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXCap
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isHCParam_cast {m n : ℕ} (h : m = n) (f : Fin n → ℝ) (hf : Formalism.QuantumDeterminants.IsHCParam f) :
    Formalism.QuantumDeterminants.IsHCParam (fun i : Fin m => f (Fin.cast h i)) := by
  subst h
  exact hf

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem isHCParam_lamX (w : InfinitePlace X.B.I.F) : Formalism.QuantumDeterminants.IsHCParam (X.B.lam w) := by
  have hf := Formalism.MainNotions.S.Inh.amp_isHCParam_lamSH D.R (D.hc (X.pl w))
  have e : X.B.lam w = fun i => lamSH D.R (D.hc (X.pl w)) (Fin.cast (X.n_eq.trans (dimS_eq D.R).symm) i) := by
    funext i
    rw [X.lam_eq]
    rfl
  rw [e]
  exact isHCParam_cast _ _ hf

theorem gap_X {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hS0 : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCl : 1000 ≤ Cl)
    (hk : 1801 ≤ D.R.k) (w : InfinitePlace X.B.I.F) :
    ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast (X.B.I.ε w) (X.B.lam w) h ∧ Formalism.MainNotions.GapDS.thrX (X.B.I.ε w) < h := by
  refine ⟨Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L, ?_, ?_⟩
  · have hg := Formalism.MainNotions.BridgeLemma.szh_gap hS0 (X.pl w)
    set c : Fin X.B.I.n → Fin (2 * D.R.rS + D.R.k + 1) := Fin.cast (X.n_eq.trans (dimS_eq D.R).symm) with hc
    have ea : ∀ a, X.B.I.ε w a = epsSH D.R (c a) := fun a => by rw [X.eps_eq]; rfl
    have la : ∀ a, X.B.lam w a = lamSH D.R (D.hc (X.pl w)) (c a) := fun a => by rw [X.lam_eq]; rfl
    intro a b hab
    rw [la a, la b]
    exact hg (c a) (c b) (by rwa [ea a, ea b] at hab)
  · have hn : (D.R.r : ℝ) = (X.B.I.n : ℝ) := by rw [X.n_eq]
    have hrS : 2 * D.R.rS + 2 = D.R.m := Ranks.rS_two D.R
    have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
    have hn900 : (900 : ℝ) ≤ (X.B.I.n : ℝ) := by
      rw [← hn, hr]; push_cast
      have : (1801 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk
      have : (0 : ℝ) ≤ (D.R.rS : ℝ) := Nat.cast_nonneg _
      linarith
    have hthr := Formalism.MainNotions.GapDS.thrX_le (X.B.I.ε w) hn900
    rw [← hn] at hthr
    have hkL := Formalism.MainNotions.BridgeLemma.szh_k_le hS0 (by linarith) (X.pl w)
    have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
    have hL : (1 / 2 : ℝ) ≤ large₂.sc.L := by
      by_contra hcn
      push Not at hcn
      have h1 : Real.exp (2 * large₂.sc.L) < Real.exp 1 := Real.exp_lt_exp.mpr (by linarith)
      have h2 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
      linarith
    have hf : (2 : ℝ) ≤ (D.R.f : ℝ) := by
      have : 2 ≤ D.R.f := by
        unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
      exact_mod_cast this
    have hf5 : (32 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := by
      have : (2 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hf 5
      norm_num at this; linarith
    have hn1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by
      rw [hr]; push_cast; have : (0 : ℝ) ≤ (D.R.rS : ℝ) := Nat.cast_nonneg _; linarith
    have hn19 : 0 ≤ (D.R.r : ℝ) ^ 19 := by positivity
    have h3 : (D.R.r : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
    have e1 : Cl * (D.R.r : ℝ) ^ 19 * 32 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 :=
      mul_le_mul_of_nonneg_left hf5 (by positivity)
    have e2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * (1 / 2) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    have e3 : 1000 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_le_mul_of_nonneg_right hCl hn19
    have hr0 : (0 : ℝ) < (D.R.r : ℝ) ^ 19 := by positivity
    linarith

theorem smooth_tr {n m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (J : Matrix (Fin n) (Fin n) ℂ) (K : Matrix (Fin m) (Fin m) ℂ)
    (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ) (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (h3 : Qᴴ * J * Q = K) (b : H) (hs : Formalism.QuantumDeterminants.SmoothOnH K (fun x => σ (Q * x * Qi) b)) :
    Formalism.QuantumDeterminants.SmoothOnH J (fun g => σ g b) := by
  have h2' : Qiᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
  have hU : ∀ g : Matrix (Fin n) (Fin n) ℂ, Formalism.QuantumDeterminants.inUH J g → Formalism.QuantumDeterminants.inUH K (Qi * g * Q) := by
    intro g hg
    have hg' : gᴴ * J * g = J := hg
    show (Qi * g * Q)ᴴ * K * (Qi * g * Q) = K
    rw [← h3]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qiᴴ Qᴴ, h2', Matrix.one_mul, ← Matrix.mul_assoc Q Qi, h2, Matrix.one_mul]
    rw [← Matrix.mul_assoc gᴴ J, ← Matrix.mul_assoc (gᴴ * J) g, hg']
  have hback : ∀ g : Matrix (Fin n) (Fin n) ℂ, Q * (Qi * g * Q) * Qi = g := by
    intro g
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  let Lφ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    { toFun := fun g => Qi * g * Q
      map_add' := fun x y => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }
  have hφ : ContDiff ℝ ⊤ (fun g : Matrix (Fin n) (Fin n) ℂ => Qi * g * Q) :=
    (LinearMap.toContinuousLinearMap Lφ).contDiff
  intro g₀ hg₀
  obtain ⟨U, F, hUo, h0, hF, hE⟩ := hs (Qi * g₀ * Q) (hU g₀ hg₀)
  refine ⟨(fun g => Qi * g * Q) ⁻¹' U, fun g => F (Qi * g * Q), hUo.preimage hφ.continuous, h0,
    hF.comp (hφ.of_le le_top).contDiffOn (fun g hg => hg), ?_⟩
  intro g hgU hgJ
  have := hE _ hgU (hU g hgJ)
  simp only [hback] at this
  exact this

variable {θ : ℝ} (C : Choice X θ)


variable [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] in
theorem coefCap_ITc {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hS0 : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCl : 1000 ≤ Cl)
    (hk : 1801 ≤ D.R.k) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (hkb : ∀ j, PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS)
      (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (b j)) :
    CoefCap (ITc X C u u' e he hv CA de de' l grid grid1 (fcT X C e u u' a b ξ ξ' cc) c i0' Θ TP A₀) := by
  have hb : ∀ j, b j ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm (X.B.I.ε (tauE X e j))) (X.B.σ (tauE X e j)) := by
    intro j
    have hsmv : Formalism.MainNotions.S.IsSmoothVec (k := D.R.k) (r := D.R.rS)
        (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (b j) :=
      Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.k_finite_smooth D.R.k D.R.rS (epsSH D.R) (lamD D (e (plE D j))) _
        (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D _)
        (Formalism.L2.SG.Pf.dsTr C (e (plE D j))) (b j) (hkb j)
    obtain ⟨h1, h2, h3, -⟩ := C.isT (e (plE D j))
    exact smooth_tr (X.B.σ (vOf X (e (plE D j)))) _ _ (C.Q (e (plE D j))) (C.Qi (e (plE D j))) h1 h2 h3 (b j) hsmv
  exact coefCap_carrierInT X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c (nuE X C u' e i0') (m0E X C u u' e) Θ TP A₀
    hb (isHCParam_lamX X) (gap_X X hS0 hCl hk)

end Formalism.L2.SG.Pf.CarrierXAll
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopRowSOf
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopsFinalS
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsCut
  Formalism.L2.SG.LoopsFinal Formalism.L2.SG.LoopsEv Formalism.FourierDecayAlt

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ThrS

end ThrS

section Point

variable {D : D7} (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (Formalism.L2.SG.PackageTie2.sOf hF)) (hCT : ConcTie X Y)

def wOf : WittDat X := Classical.choice (Formalism.L2.SG.Pf.WittFlags.WittExists_holds D X)

theorem hOf : TieHyp (wOf X) hI :=
  { lat := Formalism.L2.SG.Pf.WittFlags.LatIso_holds D
    idG := fun u u' => identityCell_vanishes u u'
    atSome := fun u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds _ _ Y u u'
    autFin := fun u => Formalism.L2.SG.Pf.autFin_of (automorphism_lattice_finite D) (D.sp.Y_sig 0)
      (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u)
      (Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D ((wOf X).δ u) ((wOf X).isom u) (X.Fu u) (Y.what₂ u) (Y.rowsOK u))
    dim := fun u => Formalism.L2.SG.Pf.dimTie X u
    pairs := Formalism.L2.SG.Pf.pairTiesAll_holds _ _ Y hF (wOf X) hI }

def aOf : AmpDat X := Classical.choose (Formalism.L2.SG.Pf.KernelOfEmbedding.pvalForm_holds (wOf X) hI hCT.2.2.2.2.1)

end Point

section PointW

variable {D : D7} (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (Formalism.L2.SG.PackageTie2.sOf hF))
  (hWD : Formalism.L2.SG.WuDecay.WuDecay X)

def aOfW : AmpDat X := Classical.choose (Formalism.L2.SG.Pf.KernelOfEmbedding.pvalForm_holds (wOf X) hI hWD)

theorem hvOfW : PvalForm (wOf X) hI (aOfW X Y hF hI hWD) :=
  Classical.choose_spec (Formalism.L2.SG.Pf.KernelOfEmbedding.pvalForm_holds (wOf X) hI hWD)

def atOfW : TermTie D := termTieOf (wOf X) hI (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD)

def ccOfW : ConcAt0 D (atOfW X Y hF hI hWD) :=
  ⟨X, Y, hF, hI,
    jtPin_of (wOf X) hI (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD)
      (Formalism.L2.SG.Pf.FibreCounting.AmpFibreConst_holds Y),
    Formalism.L2.SG.Pf.WittFlags.WRowPin_holds hF hI (wOf X) (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD),
    Formalism.L2.SG.Pf.FibreCounting.FibreCount_holds Y⟩

end PointW

end Formalism.L2.SG.LoopsTies
end
end

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsFinal Formalism.FourierDecayAlt
  Formalism.L2.SG.ThmSOwn

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SelQ

variable {𝒞 : FamClass} (sel : SSel 𝒞)

variable {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm)

end SelQ

section Closed

variable (C0 : ℝ) {𝒞 : FamClass} (sel : SSel 𝒞)

theorem cOut_take {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).take 16 = Fm.cOut := by
  unfold FamP.cOut; simp

theorem constant_list_cylinder {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).getD 6 0 = Fm.CYL := by
  unfold FamP.cOut; simp

theorem constant_list_trace {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).getD 13 0 = Fm.CTu := by
  unfold FamP.cOut; simp

end Closed

section Raised

variable (C0 : ℝ) {𝒞 : FamClass} (sel : SSel 𝒞)
  (yF : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → ℝ)

def YFOK : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x), yF Fm hc ≤ x →
    ∀ i : Fm.Ix x, FinX ((sel Fm hc).2 x hx h0 i).Y ∧ Formalism.L2.SG.WuDecay.WuDecay ((sel Fm hc).2 x hx h0 i).X

def yR {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) : ℝ := max (sel Fm hc).1 (yF Fm hc)

theorem h0R {eps : ℝ} {Fm : FamP eps} {hc : 𝒞 Fm} {x : ℝ} (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) :
    (sel Fm hc).1 ≤ x :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans hx.le

theorem hyR {eps : ℝ} {Fm : FamP eps} {hc : 𝒞 Fm} {x : ℝ} (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) :
    yF Fm hc ≤ x :=
  ((le_max_right _ _).trans (le_max_right _ _)).trans hx.le

def AtR (hyF : YFOK sel yF) {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) (x : ℝ) (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x)
    (i : Fm.Ix x) : TermTie (Fm.D x i) :=
  atOfW ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1
    (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1)
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2

def CcR (hyF : YFOK sel yF) {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) (x : ℝ) (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x)
    (i : Fm.Ix x) : ConcAt0 (Fm.D x i) (AtR sel yF hyF Fm hc x hx i) :=
  ccOfW ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1
    (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1)
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem loopRowS_of_raised (hyF : YFOK sel yF) (C1f : List ℝ → ℝ) (C₀f : (List ℝ → ℝ) → List ℝ → ℝ)
    (Yt : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopTie (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut))
    (hRowsF : ∀ aF : List ℝ → ℝ, Closed 𝒞 fun Fm CH => ∀ hc : 𝒞 Fm, ∀ C : ℝ, C₀f aF (Fm.cOut ++ Fm.cMid CH) ≤ C →
      OwnEv Fm fun C' Cl x i => ∀ (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (u u' : (Fm.D x i).what₂.Word),
        Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 (aF Fm.cOut) →
          Formalism.MainNotions.BridgeLemma.RowsND (AtR sel yF hyF Fm hc x hx i) (Yt Fm hc x hx i u u') C ∧
            Formalism.MainNotions.BridgeLemma.RowsDeg (AtR sel yF hyF Fm hc x hx i) (Yt Fm hc x hx i u u') C ∧
            Formalism.MainNotions.BridgeLemma.RowsOne (AtR sel yF hyF Fm hc x hx i) (Yt Fm hc x hx i u u') C)
    (hForm : Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      Hyp0 (Fm.D x i) (Fm.L x i) C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) :
    LoopRowS C0 𝒞 sel := by
  intro aF
  choose f g hfg using fun p : ℝ × ℝ × ℝ × ℝ =>
    loop_evaluation_threshold_zero Formalism.FourierDecayAlt.P.loop_kernels Formalism.FourierDecayAlt.P.subfamilyAlt Formalism.HermitianLattices.Ext.L3.siegelMassRatio
      (p.1 + 1) (1 / 4) 3 (1 / 2) p.2.1 C0 p.2.2.1 p.2.2.2
  let par : List ℝ → ℝ × ℝ × ℝ × ℝ := fun l => (l.getD 6 0, l.getD 13 0, aF (l.take 16), C₀f aF l)
  obtain ⟨e1, he1, H1⟩ := hRowsF aF
  obtain ⟨e2, he2, H2⟩ := hForm
  refine ⟨min e1 e2, lt_min he1 he2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := H1 eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := H2 eps he (hle.trans (min_le_right _ _))
  let K4 : TransportedAlt := ⟨0, fun _ => 0, fun _ => 0, fun l => max (f (par l)) (g (par l))⟩
  refine ⟨(K1.sup K2).sup K4, fun Fm CH hc hL => ?_⟩
  obtain ⟨hL12, hL4⟩ := (Fm.large_sup _ _ CH).1 hL
  obtain ⟨hL1, hL2⟩ := (Fm.large_sup _ _ CH).1 hL12
  intro hc'
  have epar : par (Fm.cOut ++ Fm.cMid CH) = (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) := by
    simp only [par, constant_list_cylinder, constant_list_trace, cOut_take]
  have hthr : ∀ c ∈ Fm.cLast, max (f (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)))
      (g (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH))) ≤ c := by
    intro c hc0
    have := hL4.2.2.2 c hc0
    simpa only [K4, epar] using this
  have hC' : f (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) ≤ sC' Fm :=
    (le_max_left _ _).trans (hthr _ (by unfold FamP.cLast sC'; simp))
  have hCl : g (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) ≤ sCl Fm := by
    have h := fun c hc => (le_max_right _ _).trans (hthr c hc)
    unfold sCl
    refine le_min (h _ (by unfold FamP.cLast; simp)) (le_min (h _ (by unfold FamP.cLast; simp))
      (le_min (h _ (by unfold FamP.cLast; simp)) (le_min (h _ (by unfold FamP.cLast; simp))
        (le_min (h _ (by unfold FamP.cLast; simp)) (h _ (by unfold FamP.cLast; simp))))))
  have hE := hfg (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) (Fm.raise (yR sel yF Fm hc')) (C1f Fm.cOut)
    (AtR sel yF hyF Fm hc') (Yt Fm hc') (CcR sel yF hyF Fm hc') (hK1 Fm CH hc hL1 hc') (hK2 Fm CH hc hL2)
  obtain ⟨x0, H⟩ := hE
  refine ⟨max x0 (yR sel yF Fm hc' + 1), fun x hx0 i => ?_⟩
  intro hx h0 u u' hH hCT hA
  have hx' : (Fm.raise (yR sel yF Fm hc')).x1 < x := by
    show max Fm.x1 (yR sel yF Fm hc') < x
    refine max_lt hx ?_
    have := (le_max_right _ _).trans hx0
    linarith
  exact H x ((le_max_left _ _).trans hx0) i hC' hCl hx' u u' hH hCT hA

theorem constant_list_gamma {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).getD 17 0 = Fm.CGam := by
  unfold FamP.cOut FamP.cMid; simp


end Raised

end Formalism.L2.SG.LoopsTies
end
end
