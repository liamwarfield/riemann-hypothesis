module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfChoices
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutER

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftDegreeLemmas
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

section nice

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def NV {S : Type} (Bs : B.RealPlaceData k ρ Wp Wq) (ε : ℝ) (x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ e, JC.NiceCoef Bs ε (x e)

variable {S : Type} {Bs : B.RealPlaceData k ρ Wp Wq} {ε : ℝ}

theorem nv_zero : NV (S := S) Bs ε 0 := fun _ => JCx2.mn_nice_zero

theorem nv_add {x y : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : NV Bs ε x) (hy : NV Bs ε y) : NV Bs ε (x + y) :=
  fun e => JCx2.mn_nice_add (hx e) (hy e)

theorem nv_smul (c : ℂ) {x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : NV Bs ε x) : NV Bs ε (c • x) :=
  fun e => JCx2.mn_nice_smul c (hx e)

theorem nice_mono {F : B.Mat k ρ → (Wq →L[ℂ] Wp)} {ε ε' : ℝ} (h : JC.NiceCoef Bs ε F) (h' : ε' ≤ ε) :
    JC.NiceCoef Bs ε' F :=
  ⟨h.1, h.2.1, fun g hg hne => h'.trans (h.2.2 g hg hne)⟩

theorem nv_mono {x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} {ε ε' : ℝ} (h : NV Bs ε x) (h' : ε' ≤ ε) : NV Bs ε' x :=
  fun e => nice_mono (h e) h'

theorem nice_of_cpt {F : B.Mat k ρ → (Wq →L[ℂ] Wp)} (h : KB.CptCoef Bs F) : ∃ ε, 0 < ε ∧ JC.NiceCoef Bs ε F := by
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hG⟩⟩ := h
  refine ⟨ε, hε, hs, fun A m => JFxG.cptInCC_G hs (PBE.isCompact_gN_le k ρ R) (fun g hg hgC => ?_) A m, hG⟩
  by_contra h0
  exact hgC (hR g hg h0)

end nice

section forms

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem nv_common {α S : Type} {k ρ : ℕ} {Bs : B.RealPlaceData k ρ Wp Wq} (Y : Finset α)
    (u : α → Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) (h : ∀ a ∈ Y, ∃ ε, 0 < ε ∧ NV Bs ε (u a)) :
    ∃ ε, 0 < ε ∧ ∀ a ∈ Y, NV Bs ε (u a) := by
  obtain ⟨ε, hε, hall⟩ := common_eps (ι := Y) (fun a ε => NV Bs ε (u a)) (fun a ε ε' h h0 h' => nv_mono h h')
    (fun a => h a a.2)
  exact ⟨ε, hε, fun a ha => hall ⟨a, ha⟩⟩

theorem slv_nv (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F) (j : ℕ)
    (hj : j ≤ P.r) (w : List C.Letter) (a : C.LPt) (ha : D.IsLocPt a j) :
    ∃ ε, 0 < ε ∧ NV (p.T.bs j) ε (KB.slv p.T F j hj w a ha.2) := by
  have h := fun e => nice_of_cpt (Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w a ha hF e)
  obtain ⟨ε, hε, hall⟩ := common_eps (fun e ε => JC.NiceCoef (p.T.bs j) ε (KB.slv p.T F j hj w a ha.2 e))
    (fun e ε ε' h h0 h' => nice_mono h h') h
  exact ⟨ε, hε, hall⟩

theorem form_eq' (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) :
    p.form j hj w = D.formLev p.T (M.sgn P p.l0) ⟨j, by omega⟩ w := rfl

theorem form_sl (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) {ε : ℝ}
    (x₁ x₂ y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (h₁ : NV (p.T.bs j) ε x₁) (h₂ : NV (p.T.bs j) ε x₂) (hy : NV (p.T.bs j) ε y) :
    p.form j hj w (x₁ + c • x₂) y = p.form j hj w x₁ y + c * p.form j hj w x₂ y :=
  PBG.form_sesq_left P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w x₁ x₂ y c (PBG.decV_of_nice h₁) (PBG.decV_of_nice h₂)
    (PBG.decV_of_nice hy)

theorem form_sr (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) {ε : ℝ}
    (x y₁ y₂ : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : NV (p.T.bs j) ε x) (h₁ : NV (p.T.bs j) ε y₁) (h₂ : NV (p.T.bs j) ε y₂) :
    p.form j hj w x (y₁ + c • y₂) = p.form j hj w x y₁ + conj c * p.form j hj w x y₂ :=
  PBG.form_sesq_right P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w x y₁ y₂ c (PBG.decV_of_nice hx) (PBG.decV_of_nice h₁)
    (PBG.decV_of_nice h₂)

end forms

end

end Formalism.FourierDecayAlt.P.PBL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLQOf
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

variable {k r : ℕ}

def qOf (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : (Fin r → ℂ) × ℂ :=
  (fun a => Formalism.QuantumDeterminants.cmin k r z z' g a, Formalism.QuantumDeterminants.zeta k r z z' g)

theorem qOf_contOn (z z' : Fin (2 * r + k + 1) → ℂ) : ContinuousOn (qOf z z') (Q.OmPlus k r z z') := by
  refine ContinuousOn.prodMk ?_ ?_
  · refine continuousOn_pi.2 fun a => ?_
    show ContinuousOn (fun g : B.Mat k r => Dmin k r z z' g ⟨a.val + 1, by omega⟩ / Dmin k r z z' g ⟨a.val, by omega⟩) _
    exact (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn.div (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn
      fun g hg => hg.1 ⟨a.val, by omega⟩ (by simp)
  · show ContinuousOn (fun g : B.Mat k r => Dmin k r z z' g (Fin.last (r + 1)) / Dmin k r z z' g ⟨r, by omega⟩) _
    exact (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn.div (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn
      fun g hg => hg.1 ⟨r, by omega⟩ le_rfl

theorem isOpen_qOf (z z' : Fin (2 * r + k + 1) → ℂ) {U : Set ((Fin r → ℂ) × ℂ)} (hU : IsOpen U) :
    IsOpen (Q.OmPlus k r z z' ∩ qOf z z' ⁻¹' U) :=
  (qOf_contOn z z').isOpen_inter_preimage (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open z z') hU

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem qOf_sgs (Bs : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : Bs.inSS p) (g : B.Mat k r) :
    qOf Bs.z Bs.z' (B.sgs p g) = qOf Bs.z Bs.z' g := by
  unfold qOf Formalism.QuantumDeterminants.cmin Formalism.QuantumDeterminants.zeta
  simp only [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp]

theorem qOf_gq (Bs : B.RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ JF.QDom k r Bs.z Bs.z') :
    qOf Bs.z Bs.z' (B.gq Bs q) = q :=
  Prod.ext (funext fun a => Formalism.FourierDecayAlt.P.BigCellZetaMinors.cmin_gq Bs hq a) (Formalism.FourierDecayAlt.P.BigCellZetaMinors.zeta_gq Bs hq)

theorem om_eq_sgs (Bs : B.RealPlaceData k r Wp Wq) {g : B.Mat k r} (hg : g ∈ JF.Om k r Bs.z Bs.z') :
    ∃ p, Bs.inSS p ∧ qOf Bs.z Bs.z' g ∈ JF.QDom k r Bs.z Bs.z' ∧ g = B.sgs p (B.gq Bs (qOf Bs.z Bs.z' g)) := by
  obtain ⟨p, hp, q, hq, rfl⟩ := Formalism.FourierDecayAlt.P.psiOnto_true k r Wp Wq Bs g hg
  rw [qOf_sgs Bs hp, qOf_gq Bs hq]
  exact ⟨p, hp, hq, rfl⟩

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem agree_qOf (Bs : B.RealPlaceData k r Wp Wq) (J F : B.Mat k r → (Wq →L[ℂ] Wp)) (U : Set ((Fin r → ℂ) × ℂ))
    (hJ : J ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 {g | 0 < Gf k r Bs.z Bs.z' g ∧
      ∀ a : Fin r, Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0})
    (hag : ∀ q ∈ JF.QDom k r Bs.z Bs.z', q ∈ U → J (B.gq Bs q) = B.JF Bs F (B.gq Bs q)) :
    ∀ g ∈ JF.Om k r Bs.z Bs.z', qOf Bs.z Bs.z' g ∈ U → J g = B.JF Bs F g := by
  intro g hg hgU
  obtain ⟨p, hp, hq, hge⟩ := om_eq_sgs Bs hg
  set q := qOf Bs.z Bs.z' g with hqdef
  rw [hge]
  have hgq := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom Bs hq
  have hD : ∀ y ∈ JF.Om k r Bs.z Bs.z', y ∈ Q.Glev k r 0 ∩ {g | 0 < Gf k r Bs.z Bs.z' g ∧
      ∀ a : Fin r, Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := fun y hy =>
    ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hy.1, Formalism.FourierDecayAlt.P.CutMP.jdc_of_om _ _ hy⟩
  have hNl : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, n ∈ Q.Nlev k r 0 := fun n hn => ⟨hn, Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hn.1⟩
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq k r Bs.z Bs.z' cStd Bs.π Bs.π' Bs.μW Bs.μN Bs.μW' F Bs.z_mem Bs.z'_mem
    Bs.haarN.conc (fun n₀ h => Bs.haarN.left n₀ h)
  refine LT.agree_sgs Bs J (B.JF Bs F)
    (fun y hy n hn => hJ.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy n hn => hJ.2.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy h hh h' hh' => hJ.2.2.2 y (hD y hy) h hh h' hh')
    (fun y _ n hn => ?_) (fun y _ n hn => ?_)
    (fun y _ h hh h' hh' => Formalism.FourierDecayAlt.P5.jf_uEquiv Bs F y hh hh')
    hp hgq (hag q hq hgU)
  · have e := hN y n hn 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z'_mem, mul_one] at e
    exact e
  · have e := hN y 1 WeylGroupFacts.mem_n_one n hn
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z_mem, one_mul] at e
    exact e

end Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO

end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftZeroOrder
namespace Formalism.FourierDecayAlt.P

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.TLB
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lift_zero_order : TL.LiftZero := by
  intro Wp Wq _ _ _ _ _ _ P Bs κ i j c Pol E a
  intro cf hPol hE hcomm ha
  obtain ⟨q, hqdeg, hq⟩ := id hPol
  let fib : Fin 1 → B.Mat P.k P.r → C6.EndH Wp Wq := fun _ => E
  let t : MinorPolynomials.CT P.k P.r 1 :=
    ⟨q, fun l => if l = Fin.last (P.r + 1) then i else 0,
      fun l => if l = Fin.last (P.r + 1) then j else 0, c, [((0 : Fin 1), [])]⟩
  let T0 : B.DTerm P.k P.r Wp Wq :=
    { coef := MinorPolynomials.cv Bs fib t
      coefAdj := fun g => HilbertSchmidtVectorization.adjH (MinorPolynomials.cv Bs fib t g)
      word := []
      word_lie := fun X hX => by simp at hX
      adj_id := fun g A J => HilbertSchmidtVectorization.adjH_spec (MinorPolynomials.cv Bs fib t g) A J }
  have hcoef : ∀ g, T0.coef g = cf g := by
    intro g
    simp only [T0, MinorPolynomials.cv, MinorPolynomials.cvs, C6.Epart, C6.monoM, t, fib, cf]
    rw [Finset.prod_eq_single (Fin.last (P.r + 1)) (fun l _ hl => by simp [hl])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [↓reduceIte, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, B.Rw, List.foldr_nil]
    rw [hq g]
    simp only [PI.UnitaryGroupMassFormula.UsCompose.vars]
    congr 1
    ring

  have hfib : ∀ j : Fin 1, C6.FibBound Bs (fib j) := fun _ => hE
  have hgood : MinorPolynomials.Good (∅ : Finset (Fin (P.r + 2))) (t, ([] : List (B.Mat P.k P.r))) := by
    refine ⟨fun l hl => ?_, by simp [t], by simp⟩
    right
    by_contra h
    simp [t, h] at hl
  have hadj : ∀ {S : Set (B.Mat P.k P.r)} {f : B.Mat P.k P.r → C6.EndH Wp Wq},
      B.CkOn ⊤ S f → B.CkOn ⊤ S (fun x => HilbertSchmidtVectorization.adjH (f x)) := by
    intro S f hf g0 hg0
    obtain ⟨U, f', hU, hgU, hf', heq⟩ := hf g0 hg0
    refine ⟨U, fun x => HilbertSchmidtVectorization.adjR (f' x), hU, hgU, (HilbertSchmidtVectorization.adjR (Wp := Wp) (Wq := Wq)).contDiff.comp_contDiffOn hf', ?_⟩
    intro g hg hgv
    show HilbertSchmidtVectorization.adjH (f g) = HilbertSchmidtVectorization.adjH (f' g)
    rw [heq g hg hgv]
  have hsmooth : B.SmoothCoef (C6.domL Bs ∅) [T0] := by
    intro T hT
    rw [List.mem_singleton] at hT
    subst hT
    exact ⟨MinorPolynomials.ckOn_cv Bs fib (fun j => (hfib j).1) hgood,
      hadj (MinorPolynomials.ckOn_cv Bs fib (fun j => (hfib j).1) hgood)⟩
  have hop : ∀ (F : B.Mat P.k P.r → Wq →L[ℂ] Wp) g, B.opApply [T0] F g = cf g (F g) := by
    intro F g
    simp only [B.opApply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hcoef]
    rfl
  have hord : B.opOrder [T0] = 0 := by
    rfl
  have hcomD : B.Commutes Bs (C6.domL Bs ∅) [T0] := by
    intro p hp f _ g hg
    rw [hop]
    simp only [B.rho]
    rw [hop]
    exact hcomm p hp g hg (f (B.sgs p g))
  have hDD : C6.InDDPlus Bs fib ∅ 0 κ [T0] := by
    refine ⟨hsmooth, hcomD, fun T hT => ?_⟩
    rw [List.mem_singleton] at hT
    subst hT
    refine ⟨Pol, t.a, t.b, c, [((0 : Fin 1), [])], hPol, fun l _ hl => by simp [t, hl], ?_, by simp, ?_⟩
    · exact le_rfl
    · intro g _
      simp only [T0, MinorPolynomials.cv, MinorPolynomials.cvs, t]
      rw [hq g]
      rfl
  refine ⟨1, fib, [T0], hfib, hDD, ?_⟩
  intro F hF Φ hΦ x hx
  rw [ha Φ x hx, hΦ x hx]
  obtain ⟨ε, _, hnice⟩ := TLB.nice_of_cpt hF
  have hcomO : B.Commutes Bs (JF.Om P.k P.r Bs.z Bs.z') [T0] := by
    intro p hp f hf g hg
    exact hcomD p hp f hf g ⟨hg.1, hg.2.2, by simp⟩
  have hJ := orbital_commutes_on_open_set P.k P.r Wp Wq Bs
    (12 * ((P.r : ℝ) + 1) ^ 2 * (((0 : ℕ) : ℝ) + (P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1)) 0 F [T0]
    (JF.Om P.k P.r Bs.z Bs.z') subset_rfl hord.le (OrbitalIntegralIdentities.thrW_of P.k P.r 0 _ le_rfl) (hnice.2.1 _ 0) hcomO
    _ (TLB.wCell_om Bs hx)
  rw [hop] at hJ
  simp only [Q.resG, map_smul]
  rw [hJ]

end

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportInClassGeneral
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CompactSupportClassLemmas

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem compact_support_in_class_general (D : RealPlaceData k r Wp Wq) (Θ : DiffOp k r Wp Wq) (hS : SmoothCoef (GPos D) Θ)
    (hC : Commutes D (GPos D) Θ) (F F' : Mat k r → (Wq →L[ℂ] Wp))
    (hF : CkOn ⊤ (GV k r) F) (hFc : HasCompactSupport F) (hFO : ∀ g ∈ tsupport F, g ∈ GV k r → g ∈ GPos D)
    (hF' : CkOn ⊤ (GV k r) F') (hF'c : HasCompactSupport F') (hF'O : ∀ g ∈ tsupport F', g ∈ GV k r → g ∈ GPos D) :
    InCC (AB k r) 5 F ∧ InCC (AB k r) 5 F' ∧ InCC (AB k r) 5 (opApply Θ F) ∧ InCC (AB k r) 5 (opAdj Θ F') ∧
      beta D (opApply Θ F) F' = beta D F (opAdj Θ F') := by
  set C : Set (Mat k r) := tsupport F with hCdef
  set C' : Set (Mat k r) := tsupport F' with hC'def
  have hCc : IsCompact C := hFc
  have hC'c : IsCompact C' := hF'c
  obtain ⟨_, _, _, _, _, hL3, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi k r Wp Wq D (AB k r) le_rfl
  have supp : ∀ {φ : Mat k r → (Wq →L[ℂ] Wp)} {K : Set (Mat k r)}, IsCompact K →
      (∀ g ∈ K, g ∈ GV k r → g ∈ GPos D) →
      (∀ g ∈ GV k r, g ∉ K → φ g = 0) → closure {g | g ∈ GV k r ∧ φ g ≠ 0} ⊆ GPos D :=
    by
    intro φ K hK hKO hz
    exact (closure_minimal (s := {g | g ∈ GV k r ∧ φ g ≠ 0}) (t := K ∩ GV k r) (fun g hg => by
      refine ⟨?_, hg.1⟩
      by_contra hgK
      exact hg.2 (hz g hg.1 hgK)) (hK.isClosed.inter Formalism.FourierDecayAlt.P.B5.GV_closed)).trans (fun g hg => hKO g hg.1 hg.2)
  have rwz : ∀ {φ : Mat k r → (Wq →L[ℂ] Wp)} {K : Set (Mat k r)}, IsCompact K →
      (∀ g ∈ GV k r, g ∉ K → φ g = 0) → ∀ w : List (Mat k r), (∀ X ∈ w, inLie k r X) →
        ∀ g ∈ GV k r, g ∉ K → Rw w φ g = 0 :=
    fun hK hz w hw g hg hgK => Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hK.isClosed.isOpen_compl hw (fun x hx hxK => hz x hx hxK) g hg hgK
  have hFz : ∀ g ∈ GV k r, g ∉ C → F g = 0 := fun g _ h => image_eq_zero_of_notMem_tsupport h
  have hF'z : ∀ g ∈ GV k r, g ∉ C' → F' g = 0 := fun g _ h => image_eq_zero_of_notMem_tsupport h
  have hap : ∀ T ∈ Θ, CkOn ⊤ (GV k r) (fun x => T.coefAdj x (F' x)) ∧
      ∀ g ∈ GV k r, g ∉ C' → T.coefAdj g (F' g) = 0 := fun T hT =>
    ⟨Formalism.FourierDecayAlt.P.B5.ckOn_coef (hS T hT).2 hF' (supp hC'c hF'O hF'z), fun g hg hgK => by rw [hF'z g hg hgK, map_zero]⟩
  have hrev : ∀ T ∈ Θ, ∀ X ∈ T.word.reverse, inLie k r X := fun T _ X hX => T.word_lie X (List.mem_reverse.1 hX)
  have hΘF : InCC (AB k r) 5 (opApply Θ F) := by
    show InCC _ 5 (fun g => (Θ.map fun T => T.coef g (Rw T.word F g)).sum)
    refine Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_opsum Θ (fun T g => T.coef g (Rw T.word F g)) fun T hT => ?_
    exact cptInCC_G (Formalism.FourierDecayAlt.P.B5.ckOn_coef (hS T hT).1 (ckOn_Rw_top hF T.word T.word_lie)
        (supp hCc hFO (rwz hCc hFz T.word T.word_lie))) hCc
      (fun g hg hgK => by
        show T.coef g (Rw T.word F g) = 0
        rw [rwz hCc hFz T.word T.word_lie g hg hgK, map_zero]) _ 5
  have hΘF' : InCC (AB k r) 5 (opAdj Θ F') := by
    show InCC _ 5 (fun g => (Θ.map fun T =>
      ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g).sum)
    refine Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_opsum Θ
      (fun T g => ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g) fun T hT => ?_
    exact cptInCC_G (ckOn_smul ((-1 : ℂ) ^ T.word.length) (ckOn_Rw_top (hap T hT).1 _ (hrev T hT))) hC'c
      (fun g hg hgK => by
        show ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g = 0
        rw [rwz hC'c (hap T hT).2 _ (hrev T hT) g hg hgK, smul_zero]) _ 5
  have hIC : IntClause D Θ F F' := by
    intro p hp T hT i j hij hj
    have hlie1 : ∀ X ∈ (T.word.take i).reverse, inLie k r X := fun X hX =>
      T.word_lie X (List.mem_of_mem_take (List.mem_reverse.mp hX))
    have hlie2 : ∀ X ∈ T.word.drop j, inLie k r X := fun X hX => T.word_lie X (List.mem_of_mem_drop hX)
    set f₁ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.take i).reverse (fun x => T.coefAdj x (F' x)) with hf₁
    set f₂ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.drop j) (rho D p F) with hf₂
    have hf₁c : CkOn ⊤ (GV k r) f₁ := ckOn_Rw_top (hap T hT).1 _ hlie1
    have hf₁z : ∀ g ∈ GV k r, g ∉ C' → f₁ g = 0 := rwz hC'c (hap T hT).2 _ hlie1
    obtain ⟨K₁, hK₁⟩ := cptInCC_G hf₁c hC'c hf₁z 0 0
    have hb₁ : ∀ g ∈ GV k r, ‖f₁ g‖ ≤ K₁ := by
      intro g hg
      have := hK₁.2 [] [] (by simp) (by simp) (by simp) g hg
      simpa [Real.rpow_zero, dLR, Rw] using this
    have hf₂c : ContinuousOn f₂ (GV k r) :=
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_cont subset_rfl (Formalism.FourierDecayAlt.P.B5.ckOn_mono bot_le
        (ckOn_Rw_top (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hF) _ hlie2))
    have hf₁cont : ContinuousOn f₁ (GV k r) :=
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_cont subset_rfl (Formalism.FourierDecayAlt.P.B5.ckOn_mono bot_le hf₁c)
    obtain ⟨K₂, hK₂⟩ := (hC'c.inter_right Formalism.FourierDecayAlt.P.B5.GV_closed).exists_bound_of_continuousOn
      (hf₂c.mono Set.inter_subset_right)
    set G : Mat k r → (Wq →L[ℂ] Wp) := fun g => ((‖f₂ g‖ : ℝ) : ℂ) • f₁ g with hG
    have hGn : ∀ g, ‖G g‖ = ‖f₁ g‖ * ‖f₂ g‖ := by
      intro g
      simp only [hG, norm_smul, Complex.norm_real, norm_norm]
      ring
    have hGc : ContinuousOn G (GV k r) := (Complex.continuous_ofReal.comp_continuousOn hf₂c.norm).smul hf₁cont
    have hGm := Formalism.FourierDecayAlt.P.BetaSesquilinearity.aesm_of_continuousOn D hGc
    have hfin : D.μG (C' : Set (Mt k r)) ≠ ⊤ := (D.haarG.finite_compact C' hC'c).ne
    have hind : Integrable ((C' : Set (Mt k r)).indicator fun _ => K₁ * K₂) D.μG :=
      (integrableOn_const hfin).integrable_indicator (IsClosed.measurableSet (α := Mt k r) hC'c.isClosed)
    have hint : Integrable (fun g : Mt k r => G (Matrix.of g)) D.μG := by
      refine hind.mono' hGm ?_
      filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae D.haarG] with x hx
      by_cases hxC : x ∈ (C' : Set (Mt k r))
      · rw [Set.indicator_of_mem hxC, hGn]
        have h1 := hb₁ (Matrix.of x) hx
        have h2 := hK₂ (Matrix.of x) ⟨hxC, hx⟩
        exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      · rw [Set.indicator_of_notMem hxC, hGn, hf₁z (Matrix.of x) hx hxC, norm_zero, zero_mul]
    exact hint.norm.congr (Filter.Eventually.of_forall fun g => hGn _)
  have hIF := cptInCC_G hF hCc hFz (AB k r) 5
  have hIF' := cptInCC_G hF' hC'c hF'z (AB k r) 5
  exact ⟨hIF, hIF', hΘF, hΘF', hL3 (GPos D) Θ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gPos_stable D) hS hC F F'
    (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF) (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF')
    (supp hCc hFO hFz) (supp hC'c hF'O hF'z) hIF hIF' hΘF hΘF' hIC⟩

end Formalism.FourierDecayAlt.P.CompactSupportClassLemmas

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

theorem compact_support_lemma_three : CompactSupportClassMembership := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ _hB v Θ hΘ F F' hF hFc hFO hF' hF'c hF'O
  exact Formalism.FourierDecayAlt.P.CompactSupportClassLemmas.compact_support_in_class_general (T v).base Θ hΘ.1 hΘ.2 F F' hF hFc
    (fun g hg hgG => ⟨hgG, (hFO hg).1⟩) hF' hF'c (fun g hg hgG => ⟨hgG, (hF'O hg).1⟩)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA

end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCV
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.ER

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem coefficient_vector_in_class : CVCC := by
  intro k r Wp Wq _ _ _ _ _ _ s Y A m F _ hF
  exact Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_in_L2_class k r _ A m F Y s hF

theorem coefficient_vector_congr : CVCongr := by
  intro k r Wp Wq _ _ _ _ _ _ s Y F F₁ hF hF₁ heq g hg
  have hmono : ∀ G : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) G →
      B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (Set.univ ∩ B.GV k r) G := by
    intro G hG g₀ hg₀
    obtain ⟨U, f', hU, hgU, hcd, hfe⟩ := hG g₀ hg₀.2
    exact ⟨U, f', hU, hgU, hcd.of_le (WithTop.coe_le_coe.mpr le_top), hfe⟩
  have h := Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_locality k r (Wq →L[ℂ] Wp) Set.univ F F₁ Y isOpen_univ
    (hmono F hF) (hmono F₁ hF₁) (fun x hx => heq x hx.2) g ⟨trivial, hg⟩
  simp only [Pi.smul_apply]
  rw [h]

theorem cV_zero {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) :
    Q.CV k r Y (0 : B.Mat k r → E) = 0 := by
  have hop : ∀ (u : ℂ) (a b : Fin (2 * r + k + 1)),
      Formalism.QuantumDeterminants.Top (Q.EH k r) u a b (0 : B.Mat k r → E) = 0 := by
    intro u a b
    funext g
    simp [Formalism.QuantumDeterminants.Top, Q.EH, Formalism.QuantumDeterminants.EabH, Formalism.REAL.RdV]
  have hfold : ∀ l : List ((B.Mat k r → E) → (B.Mat k r → E)), (∀ T ∈ l, T 0 = 0) →
      l.foldr (fun T h => T h) 0 = 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons T l ih =>
      simp only [List.foldr_cons]
      rw [ih (fun T' hT' => hl T' (List.mem_cons_of_mem _ hT'))]
      exact hl T List.mem_cons_self
  unfold Q.CV Q.capL Formalism.QuantumDeterminants.qminorOp
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [hfold _ ?_, smul_zero]
  intro T hT
  rw [List.mem_ofFn] at hT
  obtain ⟨i, rfl⟩ := hT
  exact hop _ _ _

theorem coefficient_vector_support : CVSupp := by
  intro k r Wp Wq _ _ _ _ _ _ z z' c s Y F hF hsupp g hg hne
  by_contra hlt
  push_neg at hlt
  have hU : IsOpen {x | Gf k r z z' x < c} :=
    isOpen_lt (Formalism.FourierDecayAlt.P.Ux8.cont_Gf k r z z') continuous_const
  have hF0 : ∀ x ∈ {x | Gf k r z z' x < c} ∩ B.GV k r,
      F x = (0 : B.Mat k r → (Wq →L[ℂ] Wp)) x := by
    intro x hx
    by_contra hne'
    exact absurd (hsupp x hx.2 hne') (not_le.mpr hx.1)
  have hCk0 : B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) ({x | Gf k r z z' x < c} ∩ B.GV k r)
      (0 : B.Mat k r → (Wq →L[ℂ] Wp)) :=
    fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hCkF : B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) ({x | Gf k r z z' x < c} ∩ B.GV k r) F := by
    intro g₀ hg₀
    obtain ⟨U, f', hU', hgU, hcd, hfe⟩ := hF g₀ hg₀.2
    exact ⟨U, f', hU', hgU, hcd.of_le (WithTop.coe_le_coe.mpr le_top), hfe⟩
  have h := Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_locality k r (Wq →L[ℂ] Wp) {x | Gf k r z z' x < c} F 0 Y hU
    hCkF hCk0 hF0 g ⟨hlt, hg⟩
  apply hne
  simp only [Pi.smul_apply]
  rw [h, cV_zero, Pi.zero_apply, smul_zero]

theorem coefficient_vector_smoothness : CVSmooth := by
  intro k r Wp Wq _ _ _ _ _ _ s Y F hF
  have hadd : ∀ {f g : B.Mat k r → (Wq →L[ℂ] Wp)}, B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) g →
      B.CkOn ⊤ (B.GV k r) (f + g) := by
    intro f g hf hg g₀ hg₀
    obtain ⟨U1, f1, hU1, h1, hc1, he1⟩ := hf g₀ hg₀
    obtain ⟨U2, f2, hU2, h2, hc2, he2⟩ := hg g₀ hg₀
    refine ⟨U1 ∩ U2, f1 + f2, hU1.inter hU2, ⟨h1, h2⟩,
      (hc1.mono Set.inter_subset_left).add (hc2.mono Set.inter_subset_right), ?_⟩
    intro x hx hxG
    simp [he1 x hx.1 hxG, he2 x hx.2 hxG]
  have hsmul : ∀ (c : ℂ) {f : B.Mat k r → (Wq →L[ℂ] Wp)}, B.CkOn ⊤ (B.GV k r) f →
      B.CkOn ⊤ (B.GV k r) (c • f) := by
    intro c f hf g₀ hg₀
    obtain ⟨U1, f1, hU1, h1, hc1, he1⟩ := hf g₀ hg₀
    refine ⟨U1, c • f1, hU1, h1, hc1.const_smul c, ?_⟩
    intro x hx hxG
    simp [he1 x hx hxG]
  have hzero : B.CkOn ⊤ (B.GV k r) (0 : B.Mat k r → (Wq →L[ℂ] Wp)) :=
    fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hrd : ∀ X : B.Mat k r, B.inLie k r X → ∀ {f : B.Mat k r → (Wq →L[ℂ] Wp)},
      B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) (Formalism.REAL.RdV X f) := by
    intro X hX f hf
    have h1 : B.CkOn ((⊤ : ℕ∞) + 1) (B.GV k r) f := by
      rw [top_add]
      exact hf
    exact Formalism.FourierDecayAlt.P.B5.ckOn_RdV hX h1
  have hTop : ∀ (u : ℂ) (a b : Fin (2 * r + k + 1)) {f : B.Mat k r → (Wq →L[ℂ] Wp)},
      B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) (Formalism.QuantumDeterminants.Top (Q.EH k r) u a b f) := by
    intro u a b f hf
    have e : Formalism.QuantumDeterminants.Top (Q.EH k r) u a b f = (if a = b then u • f else 0) +
        (Formalism.REAL.RdV (hpart1 (Hpk k r) (Matrix.single a b 1)) f +
          Complex.I • Formalism.REAL.RdV (hpart2 (Hpk k r) (Matrix.single a b 1)) f) := by
      funext g
      simp only [Formalism.QuantumDeterminants.Top, Q.EH, Formalism.QuantumDeterminants.EabH, Pi.add_apply, Pi.smul_apply]
      split_ifs <;> simp
    rw [e]
    refine hadd ?_ (hadd (hrd _ (Formalism.FourierDecayAlt.P.Qb1.lie1 _) hf) (hsmul _ (hrd _ (Formalism.FourierDecayAlt.P.Qb1.lie2 _) hf)))
    split_ifs
    · exact hsmul u hf
    · exact hzero
  have hfold : ∀ l : List ((B.Mat k r → (Wq →L[ℂ] Wp)) → (B.Mat k r → (Wq →L[ℂ] Wp))),
      (∀ T ∈ l, ∀ f, B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) (T f)) →
      ∀ f, B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) (l.foldr (fun T h => T h) f) := by
    intro l hl f hf
    induction l with
    | nil => exact hf
    | cons T l ih =>
      simp only [List.foldr_cons]
      exact hl T List.mem_cons_self _ (ih (fun T' hT' => hl T' (List.mem_cons_of_mem _ hT')))
  apply hsmul s
  unfold Q.CV Q.capL Formalism.QuantumDeterminants.qminorOp
  refine Finset.sum_induction _ (fun f => B.CkOn ⊤ (B.GV k r) f) (fun a b ha hb => hadd ha hb) hzero ?_
  intro σ _
  apply hsmul
  refine hfold _ ?_ F hF
  intro T hT f hf
  rw [List.mem_ofFn] at hT
  obtain ⟨i, rfl⟩ := hT
  exact hTop _ _ _ hf

end Formalism.FourierDecayAlt.P.CutMP.ER
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentRankOne
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem asm_contOn_of_ckOn {r : ℕ} {m : ℕ∞} {F : B.Mat k r → E} (hF : B.CkOn m (B.GV k r) F) :
    ContinuousOn F (B.GV k r) := by
  intro g₀ hg₀
  obtain ⟨W0, F', hU, hgU, hF', hag⟩ := hF g₀ hg₀
  have hc : ContinuousAt F' g₀ := (hF'.continuousOn).continuousAt (hU.mem_nhds hgU)
  refine (hc.continuousWithinAt (s := B.GV k r)).congr_of_eventuallyEq ?_ (hag g₀ hgU hg₀)
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g hgU' hgG
  exact hag g hgU' hgG

theorem asm_star_cpt (j ρ : ℕ) (F : B.Mat k (j + ρ) → E) (hFc : B.CkOn ⊤ (B.GV k (j + ρ)) F)
    (R : ℝ) (hR : ∀ g ∈ B.GV k (j + ρ), F g ≠ 0 → B.gN g ≤ R) (χD : ℂ → ℂ) (hχ : U.IsCutC χD) (A₁ : ℝ)
    (hA₁ : 0 ≤ A₁) :
    ∃ B₁, U.Star k j ρ (fun g => χD (U.DjU k j ρ g) • F g) A₁ 0 B₁ ((fun w : ℂ => ‖w‖) '' tsupport χD) := by
  have hχc : Continuous χD := hχ.1.continuous
  have hDc := Formalism.FourierDecayAlt.P.JCTx6.Pos.cont_DjU k j ρ
  obtain ⟨Cχ, hCχ⟩ := hχc.bounded_above_of_compact_support hχ.2.1
  have hKc : IsCompact (B.GV k (j + ρ) ∩ {g : B.Mat k (j + ρ) | B.gN g ≤ R}) :=
    (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k (j + ρ) R).inter_left (Formalism.FourierDecayAlt.P.unitary_group_closed k (j + ρ)).closed
  obtain ⟨CF, hCF⟩ := hKc.exists_bound_of_continuousOn ((asm_contOn_of_ckOn hFc).mono Set.inter_subset_left)
  refine ⟨(max R 0) ^ A₁ * (max Cχ 0 * max CF 0), ⟨?_, ?_, ?_⟩⟩
  · intro g₀ hg₀
    obtain ⟨W0, F', hU, hgU, hF', hag⟩ := hFc g₀ hg₀
    refine ⟨W0, fun g => χD (U.DjU k j ρ g) • F' g, hU, hgU, ?_, fun g hg hgG => by simp only [hag g hg hgG]⟩
    exact contDiffOn_zero.2 ((hχc.comp hDc).continuousOn.smul (hF'.continuousOn))
  · intro g _ hne
    refine ⟨U.DjU k j ρ g, subset_tsupport _ (fun h0 => hne ?_), rfl⟩
    simp only [h0, zero_smul]
  · intro u v hu hv hl g hg
    have hu0 : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hv0 : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu0 hv0
    show B.gN g ^ A₁ * ‖χD (U.DjU k j ρ g) • F g‖ ≤ _
    by_cases h0 : F g = 0
    · rw [h0, smul_zero, norm_zero, mul_zero]
      exact mul_nonneg (Real.rpow_nonneg (le_max_right _ _) _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
    · have hgR := hR g hg h0
      have hg0 : 0 ≤ B.gN g := Real.sqrt_nonneg _
      refine mul_le_mul (Real.rpow_le_rpow hg0 (hgR.trans (le_max_left _ _)) hA₁) ?_ (norm_nonneg _)
        (Real.rpow_nonneg (le_max_right _ _) _)
      rw [norm_smul]
      exact mul_le_mul ((hCχ _).trans (le_max_left _ _)) ((hCF g ⟨hg, hgR⟩).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)

theorem asm_gInt_int (ph ρ : ℕ) (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t : ℂ) (hd : ∀ i, d i ≠ 0) (ht : t ≠ 0)
    (z z' : Fin (2 * (ph + (0 + 1) + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + (0 + 1) + ρ) → E)
    (hFc : B.CkOn ⊤ (B.GV k (ph + (0 + 1) + ρ)) F) (R : ℝ)
    (hR : ∀ g ∈ B.GV k (ph + (0 + 1) + ρ), F g ≠ 0 → B.gN g ≤ R) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ) :
    Integrable (Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' F γ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ) := by
  have hw : (G.wMat (0 + 1)).det ≠ 0 := Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero (0 + 1)
  set c₀ : ℂ := (U.hMat σ d).det * (t ^ (0 + 1) * (G.wMat (0 + 1)).det) with hc₀def
  have hc₀ : c₀ ≠ 0 := mul_ne_zero (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd) (mul_ne_zero (pow_ne_zero _ ht) hw)
  obtain ⟨χD, hχD, hχD1, hχDs⟩ := Formalism.FourierDecayAlt.P.JCTx6.Pos.bump_exists hc₀
  have hR0 : (0 : ℝ) ≤ ((ph + (0 + 1) + ρ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA₁ : (0 : ℝ) ≤ 8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1) *
      (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) + 1) := by positivity
  obtain ⟨B₁, hStar⟩ := asm_star_cpt (ph + (0 + 1)) ρ F hFc R hR χD hχD _ hA₁
  have hK : IsCompact ((fun w : ℂ => ‖w‖) '' tsupport χD) := hχD.2.1.isCompact.image continuous_norm
  have hK0 : (fun w : ℂ => ‖w‖) '' tsupport χD ⊆ Set.Ioi 0 := by
    rintro _ ⟨w, hw', rfl⟩
    have := norm_pos_iff.mpr hc₀
    exact lt_of_lt_of_le (by positivity) (hχDs w hw').1
  have hthr : 2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) <
      8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1) *
        (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) + 1) /
        (8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1)) := by
    rw [mul_div_cancel_left₀ _ (by positivity)]
    linarith
  have h1 := Formalism.FourierDecayAlt.P.JCTx6.Int.intG k ph 0 ρ σ d t hd ht _ hK hK0 0 _ hthr z z' E _ B₁ hStar γ hγ
  have e : Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' F γ =
      Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' (fun g => χD (U.DjU k (ph + (0 + 1)) ρ g) • F g) γ := by
    funext y
    have hdet : G.detM (Matrix.of.symm (t • G.wMat (0 + 1) * G.upper y.2.2)) = t ^ (0 + 1) * (G.wMat (0 + 1)).det :=
      Formalism.FourierDecayAlt.P.JCTx6.Pos.detM_Zv 0 t y.2.2
    have hD : U.DjU k (ph + (0 + 1)) ρ (U.gaXi (p := ph) (s := 0 + 1) k ρ σ d (y.1, y.2.1)
        (Matrix.of.symm (t • G.wMat (0 + 1) * G.upper y.2.2)) γ) = c₀ := by
      rw [Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice, hdet]
    simp only [Formalism.FourierDecayAlt.P.JCTx6.gInt]
    rw [hD, hχD1 c₀ (by rw [dist_self]; positivity), one_smul]
  rw [e]; exact h1

theorem integrable_unipotent_rank_one (ph ρ : ℕ) (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (c : ℂ)
    (z z' : Fin (2 * (ph + 1 + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + 1 + ρ) → E) (γ : B.Mat k ρ)
    (h : Integrable (Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d c z z' F γ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ)) :
    Integrable (fun ξ : U.Xi k ph 1 ρ σ => U.psiStar k ρ σ z z' ξ • F (U.gaXi k ρ σ d ξ (fun _ _ => c) γ))
      (U.muXi k ph 1 ρ σ) := by
  have hE : IsEmpty (G.UT (0 + 1)) := ⟨fun q => by have h := q.2; rw [Fin.lt_def] at h; omega⟩
  let v₀ : G.UT (0 + 1) → ℂ := fun q => isEmptyElim q
  have hvol : (volume : Measure (G.UT (0 + 1) → ℂ)) = Measure.dirac v₀ := by
    rw [volume_pi]; exact Measure.pi_of_empty _ _
  have a1 : SigmaFinite (volume : Measure (Fin (0 + 1) → Fin ph → ℂ)) := inferInstance
  have a2 : SigmaFinite (volume : Measure (Fin ph → Fin (0 + 1) → ℂ)) := inferInstance
  have a3 : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
  have a4 : SigmaFinite (volume : Measure (G.UT ph → ℂ)) := inferInstance
  have b1 : SigmaFinite (volume : Measure ((Fin (0 + 1) → Fin ph → ℂ) × (Fin ph → Fin (0 + 1) → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have b2 : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT ph → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have b3 : SigmaFinite (volume : Measure (U.XiH ph (0 + 1) σ)) := by
    haveI := b1; haveI := b2
    rw [Measure.volume_eq_prod]; infer_instance
  have b4 : SigmaFinite (U.muXiH ph (0 + 1) σ) := by unfold U.muXiH; exact b3
  have hg : MeasurePreserving (fun b : U.XiH ph (0 + 1) σ => (b, v₀)) volume
      ((volume : Measure (U.XiH ph (0 + 1) σ)).prod (volume : Measure (G.UT (0 + 1) → ℂ))) := by
    rw [hvol]
    exact ⟨measurable_id.prodMk measurable_const, (Measure.prod_dirac _).symm⟩
  have := Formalism.FourierDecayAlt.P.Dx2.SL.sigma_RC k (ph + (0 + 1)) ρ
  have hφ : MeasurePreserving (Prod.map (id : U.RC k (ph + (0 + 1)) ρ × U.RC k (ph + (0 + 1)) ρ → _)
      (fun b : U.XiH ph (0 + 1) σ => (b, v₀))) (U.muXi k ph 1 ρ σ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ) :=
    (MeasurePreserving.id _).prod hg
  have h2 := (hφ.integrable_comp h.aestronglyMeasurable).2 h
  refine h2.congr (ae_of_all _ fun ξ => ?_)
  have hs : G.superSum (G.upper v₀) = 0 := by simp [G.superSum]
  have hZ : (Matrix.of.symm (c • G.wMat (0 + 1) * G.upper v₀) : G.Mat (0 + 1)) = fun _ _ => c := by
    funext i j
    have hi : i = 0 := Fin.ext (by have := i.isLt; simp)
    have hj : j = 0 := Fin.ext (by have := j.isLt; simp)
    subst hi hj
    simp [G.wMat, G.upper, G.strictUpper, Matrix.mul_apply]
  simp only [Function.comp_apply, Prod.map, id, Formalism.FourierDecayAlt.P.JCTx6.gInt, hs, hZ]
  simp [G.psi]

end Formalism.FourierDecayAlt.P.PBH
end
end
