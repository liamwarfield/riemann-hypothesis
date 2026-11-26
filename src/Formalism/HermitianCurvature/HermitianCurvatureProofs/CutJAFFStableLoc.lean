module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPRealInv

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableLoc
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section loc

variable {k r : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem mem_level_zero_of_mem_group {g : B.Mat k r} (hg : g ∈ B.GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun a ha => by simp at ha⟩

def LocSm (g₀ : B.Mat k r) (h : B.Mat k r → E') : Prop :=
  ∃ (U : Set (B.Mat k r)) (F : B.Mat k r → E'), IsOpen U ∧ g₀ ∈ U ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U ∧ ∀ x ∈ U, x ∈ B.GV k r → h x = F x

theorem locSm_of_ckOn {UU : Set (B.Mat k r)} {h : B.Mat k r → E'} (hh : B.CkOn ⊤ UU h) {g₀ : B.Mat k r}
    (hg : g₀ ∈ UU) : LocSm g₀ h := hh g₀ hg

theorem locSm_zero (g₀ : B.Mat k r) : LocSm g₀ (fun _ => (0 : E')) :=
  ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem locSm_add {g₀ : B.Mat k r} {h₁ h₂ : B.Mat k r → E'} (h1 : LocSm g₀ h₁) (h2 : LocSm g₀ h₂) :
    LocSm g₀ (fun x => h₁ x + h₂ x) := by
  obtain ⟨U₁, F₁, o₁, m₁, c₁, e₁⟩ := h1
  obtain ⟨U₂, F₂, o₂, m₂, c₂, e₂⟩ := h2
  exact ⟨U₁ ∩ U₂, fun x => F₁ x + F₂ x, o₁.inter o₂, ⟨m₁, m₂⟩,
    (c₁.mono Set.inter_subset_left).add (c₂.mono Set.inter_subset_right),
    fun x hx hxG => by simp only [e₁ x hx.1 hxG, e₂ x hx.2 hxG]⟩

theorem locSm_smul {g₀ : B.Mat k r} {h : B.Mat k r → E'} (c : ℂ) (h1 : LocSm g₀ h) :
    LocSm g₀ (fun x => c • h x) := by
  obtain ⟨U, F, o, m, cd, e⟩ := h1
  exact ⟨U, fun x => c • F x, o, m, cd.const_smul c, fun x hx hxG => by simp only [e x hx hxG]⟩

theorem locSm_clm {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] {g₀ : B.Mat k r}
    {a : B.Mat k r → (E' →L[ℂ] E₂)} {φ : B.Mat k r → E'} (ha : LocSm g₀ a) (hφ : LocSm g₀ φ) :
    LocSm g₀ (fun x => a x (φ x)) := by
  obtain ⟨U₁, F₁, o₁, m₁, c₁, e₁⟩ := ha
  obtain ⟨U₂, F₂, o₂, m₂, c₂, e₂⟩ := hφ
  refine ⟨U₁ ∩ U₂, fun x => F₁ x (F₂ x), o₁.inter o₂, ⟨m₁, m₂⟩, ?_,
    fun x hx hxG => by simp only [e₁ x hx.1 hxG, e₂ x hx.2 hxG]⟩
  have c₁' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (F₁ x).restrictScalars ℝ) (U₁ ∩ U₂) :=
    ((ContinuousLinearMap.restrictScalarsL ℂ E' E₂ ℝ ℝ).contDiff.comp_contDiffOn
      (c₁.mono Set.inter_subset_left))
  exact c₁'.clm_apply (c₂.mono Set.inter_subset_right)

theorem locSm_listSum {ι : Type*} {g₀ : B.Mat k r} (l : List ι) (φ : ι → B.Mat k r → E')
    (h : ∀ i ∈ l, LocSm g₀ (φ i)) : LocSm g₀ (fun x => (l.map fun i => φ i x).sum) := by
  induction l with
  | nil => simpa using locSm_zero (E' := E') g₀
  | cons a l ih =>
    simpa using locSm_add (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem ckOn_Rw_top {f : B.Mat k r → E'} (hf : B.CkOn ⊤ (B.GV k r) f) (w : List (B.Mat k r))
    (hw : ∀ X ∈ w, B.inLie k r X) : B.CkOn ⊤ (B.GV k r) (B.Rw w f) := by
  induction w with
  | nil => exact hf
  | cons X w ih =>
    have ih' := ih (fun Y hY => hw Y (by simp [hY]))
    show B.CkOn ⊤ (B.GV k r) (RdV X (B.Rw w f))
    exact Formalism.FourierDecayAlt.P.B5.ckOn_RdV (m := ⊤) (hw X (by simp)) (by rw [top_add]; exact ih')

theorem locSm_smoothLev {O : Set (B.Mat k r)} {h : B.Mat k r → E'}
    (hh : ∀ g₀ ∈ B.GV k r, g₀ ∈ O → LocSm g₀ h) : Q.SmoothLev k r 0 O h := by
  intro g₀ hg₀
  obtain ⟨U, F, o, m, c, e⟩ := hh g₀ hg₀.1.1 hg₀.2
  exact ⟨U, F, o, m, c, fun x hx hxG => e x hx hxG.1⟩

end loc

theorem extension_locality_holds : ExtLoc := by
  intro k r E' _ _ O J hO hJ g₀ hg₀ hg₀O
  obtain ⟨U₀, F, hU₀, hgU₀, hF, hFJ⟩ := hJ g₀ ⟨mem_level_zero_of_mem_group hg₀, hg₀O⟩
  have hV : U₀ ∩ O ∈ nhds g₀ := (hU₀.inter hO).mem_nhds ⟨hgU₀, hg₀O⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  let b : ContDiffBump g₀ := ⟨ε / 3, 2 * ε / 3, by positivity, by linarith⟩
  have hts : tsupport (fun x => b x • F x) ⊆ Metric.closedBall g₀ (2 * ε / 3) :=
    (tsupport_smul_subset_left _ _).trans b.tsupport_eq.subset
  have hcb : Metric.closedBall g₀ (2 * ε / 3) ⊆ U₀ ∩ O := fun x hx =>
    hball (Metric.closedBall_subset_ball (by linarith) hx)
  refine ⟨fun x => b x • F x, Metric.ball g₀ (ε / 3), ?_, ?_, fun x hx => (hcb (hts hx)).2,
    Metric.isOpen_ball, Metric.mem_ball_self (by positivity), ?_⟩
  · intro g _
    refine ⟨Set.univ, fun x => b x • F x, isOpen_univ, trivial, ?_, fun _ _ _ => rfl⟩
    apply ContDiff.contDiffOn
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U₀
    · exact ((b.contDiff.contDiffOn).smul hF).contDiffAt (hU₀.mem_nhds hx)
    · have hx' : x ∉ tsupport (fun x => b x • F x) := fun h => hx (hcb (hts h)).1
      exact (contDiffAt_const (c := (0 : E'))).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 hx')
  · exact IsCompact.of_isClosed_subset (isCompact_closedBall g₀ (2 * ε / 3)) (isClosed_tsupport _) hts
  · intro x hx hxG
    have hb : b x = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    have hxU : x ∈ U₀ := (hball (Metric.ball_subset_ball (by linarith) hx)).1
    simp only [hb, one_smul]
    exact (hFJ x hxU (mem_level_zero_of_mem_group hxG)).symm

theorem smooth_operators_holds : SmoothOps := by
  intro k r Wp Wq _ _ _ _ _ D Θ O hO hOP hΘ f hf hs
  have hsupp : closure {g | g ∈ B.GV k r ∧ f g ≠ 0} ⊆ B.GPos D := by
    intro x hx
    have hxG : x ∈ B.GV k r :=
      (Formalism.FourierDecayAlt.P.B5.GV_closed (k := k) (r := r)).closure_subset_iff.2 (by exact fun y hy => hy.1) hx
    have hxT : x ∈ tsupport f := closure_mono (by exact fun y hy => hy.2) hx
    exact hOP x (hs hxT) hxG
  constructor
  · apply locSm_smoothLev
    intro g₀ hg₀ hg₀O
    apply locSm_listSum
    intro T hT
    exact locSm_clm (locSm_of_ckOn (hΘ T hT).1 (hOP g₀ hg₀O hg₀))
      (locSm_of_ckOn (ckOn_Rw_top hf T.word T.word_lie) hg₀)
  · apply locSm_smoothLev
    intro g₀ hg₀ hg₀O
    apply locSm_listSum
    intro T hT
    apply locSm_smul
    have hc : B.CkOn ⊤ (B.GV k r) (fun x => T.coefAdj x (f x)) :=
      Formalism.FourierDecayAlt.P.B5.ckOn_coef (hΘ T hT).2 hf hsupp
    exact locSm_of_ckOn (ckOn_Rw_top hc T.word.reverse
      (fun X hX => T.word_lie X (List.mem_reverse.1 hX))) hg₀

theorem omP_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f) :
    OmP S T v = Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' := by
  ext g
  constructor
  · rintro ⟨hG, hD⟩
    refine ⟨fun l hl => ?_, hG⟩
    rcases Nat.eq_zero_or_pos l.val with h0 | hpos
    · have : l = ⟨0, by omega⟩ := Fin.ext h0
      rw [this]
      rw [show Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g ⟨0, by omega⟩ = 1 by
        unfold Dmin; exact Matrix.det_isEmpty]
      exact one_ne_zero
    · have := hD ⟨l.val - 1, by omega⟩
      have e : (⟨(l.val - 1) + 1, by omega⟩ : Fin (S.G.r + 2)) = l := Fin.ext (by simp; omega)
      simpa [e] using this
  · rintro ⟨hD, hG⟩
    exact ⟨hG, fun a => hD ⟨a.val + 1, by omega⟩ (by have := a.isLt; simp only [Fin.val_mk]; omega)⟩

theorem positive_domain_condition_holds : OmPDom := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v
  refine ⟨?_, fun g hg hgG => ⟨hgG, hg.1⟩⟩
  rw [omP_eq]
  exact Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (T v).base.z_mem (T v).base.z'_mem

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportFacts
namespace Formalism.FourierDecayAlt.P

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt

noncomputable section

theorem compact_support_facts : TL.CptFacts := by
  intro k r Wp Wq _ _ _ _ _ Bs F hF
  obtain ⟨hFs, ⟨R, hR⟩, ε, hε, hεF⟩ := hF
  refine ⟨⟨ε, hε, ?_⟩, fun Dop hDop => ?_⟩
  · set R' : ℝ := |R| + 1 with hR'
    have hR0 : 0 < R' := by positivity
    obtain ⟨h1, h2⟩ := JCx2.pd_cut_nice (E := Wq →L[ℂ] Wp) hR0 hFs
    have hN : JC.NiceCoef Bs ε (fun g => JCx2.pdPhi (R'⁻¹ • g) • F g) :=
      ⟨h1, fun A m => h2 A m, fun g hg hne => by
        refine hεF g hg ?_
        intro h0; apply hne; simp [h0]⟩
    refine JCx2.mn_nice_congr (fun g hg => ?_) hN
    by_cases h0 : F g = 0
    · simp [h0]
    · have hgR : gN g ≤ R := hR g hg h0
      have hg0 : 0 ≤ gN g := Real.sqrt_nonneg _
      have hsq : JCx2.pdSq (R'⁻¹ • g) ≤ 1 := by
        rw [JCx2.pd_sq_smul, JCx2.pd_sq_eq, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
        have : gN g ≤ R' := by rw [hR']; linarith [le_abs_self R]
        nlinarith
      simp [JCx2.pdPhi, JCx2.pd_chi_one hsq]
  · have hGc : Continuous (Gf k r Bs.z Bs.z') := Formalism.FourierDecayAlt.P.Ux8.cont_Gf _ _ _ _
    have hv1 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat k r | Gf k r Bs.z Bs.z' g < ε}, g ∈ GV k r →
        Rw T.word F g = 0 := fun T _ =>
      PBJ.rw_vanish_GV (isOpen_lt hGc continuous_const)
        (fun g hg hgG => by by_contra hne; exact absurd (hεF g hgG hne) (not_le.2 hg)) T.word T.word_lie
    have hv2 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat k r | R < gN g}, g ∈ GV k r → Rw T.word F g = 0 := fun T _ =>
      PBJ.rw_vanish_GV (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous)
        (fun g hg hgG => by by_contra hne; exact absurd (hR g hgG hne) (not_le.2 hg)) T.word T.word_lie
    have hcl : IsClosed {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gf k r Bs.z Bs.z' g} :=
      Formalism.FourierDecayAlt.P.B5.GV_closed.inter (isClosed_le continuous_const hGc)
    have hsub : {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gf k r Bs.z Bs.z' g} ⊆ C6.domL Bs ∅ :=
      fun g hg => ⟨hg.1, lt_of_lt_of_le hε hg.2, by simp⟩
    have hsF : closure {g | g ∈ GV k r ∧ F g ≠ 0} ⊆ C6.domL Bs ∅ := by
      refine subset_trans (closure_minimal ?_ hcl) hsub
      intro g hg; exact ⟨hg.1, hεF g hg.1 hg.2⟩
    have hsT : ∀ T ∈ Dop, closure {g | g ∈ GV k r ∧ Rw T.word F g ≠ 0} ⊆ C6.domL Bs ∅ := by
      intro T hT
      refine subset_trans (closure_minimal ?_ hcl) hsub
      intro g hg
      refine ⟨hg.1, ?_⟩
      by_contra hlt
      exact hg.2 (hv1 T hT g (not_le.1 hlt) hg.1)
    refine ⟨⟨?_, ⟨R, ?_⟩, ε, hε, ?_⟩, fun g hg hgn => ?_⟩
    · exact PBJ.ckOn_opApply_list _ F hFs hsF Dop (fun T hT => (hDop T hT).1) hsT
    · intro g hgG hne
      by_contra hlt
      exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv2 T hT g (not_le.1 hlt) hgG)
    · intro g hgG hne
      by_contra hlt
      exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv1 T hT g (not_le.1 hlt) hgG)
    · refine PBJ.opApply_eq_zero Dop F g fun T hT => hv1 T hT g ?_ hg
      show Gf k r Bs.z Bs.z' g < ε
      by_contra hge
      exact hgn ⟨hg, lt_of_lt_of_le hε (not_lt.1 hge), by simp⟩

end

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnAsm
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem foldCV_nil (k r : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) (H : B.Mat k r → E) :
    foldCV k r s [] H = H := rfl

theorem foldCV_cons (k r : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) (x : C.Letter)
    (a : List C.Letter) (H : B.Mat k r → E) :
    foldCV k r s (x :: a) H = s • Q.CV k r (x.2 : ℂ) (foldCV k r s a H) := rfl

theorem foldCV_mem {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Q.Mx k r)}
    (hcl : ∀ J ∈ Q.FFl k r z z' π π' 0 Dm, ∀ (Y : ℝ) (s : ℂ), s • Q.CV k r (Y : ℂ) J ∈ Q.FFl k r z z' π π' 0 Dm)
    {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r z z' π π' 0 Dm) (s : ℂ) :
    ∀ a : List C.Letter, foldCV k r s a J ∈ Q.FFl k r z z' π π' 0 Dm
  | [] => hJ
  | x :: a => hcl _ (foldCV_mem hcl hJ s a) x.2 s

theorem om_sub {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    g ∈ Q.Glev k r 0 ∩ {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
  obtain ⟨hU, hD, hG⟩ := hg
  refine ⟨⟨hU, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hG, fun a => hD _ ?_⟩
  show (a : ℕ) + 1 ≤ r
  omega

theorem energyTr_of_parts (hR : FoldRev) (hL : AdmLen) (hBF : BesselFoldBuilt) (hL2 : L2BoundAtTowerPlace) (hBe : BetaFrame) :
    EnergyTr := by
  refine ⟨100, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hcl ε hε hJF a hadm
  have hB' := hB
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, _, _, _, _⟩, _, _, _⟩ := hB'
  obtain ⟨_, hv⟩ := hbuilt
  obtain ⟨_, _, _, hplace, _, _⟩ := hv v
  have hlen : a.length ≤ S.Ntop := hL E Wp Wq S v a hadm
  set Db := (T v).base with hDb
  set s : ℂ := M.sgn (D.parOf S v) (S.l + 1) with hs
  set F := D.cutF Db χ (f v) ε with hF
  set J₁ := foldCV S.G.k S.G.r s a.reverse (B.JF Db F) with hJ₁
  have hJ₁m : J₁ ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v) := foldCV_mem hcl hJF s _
  have hOpen : IsOpen (OmP S T v) := (isDom_omP Db.z_mem Db.z'_mem).1

  have hae : ∀ᵐ p ∂(volume : Measure ((Fin S.G.r → ℂ) × ℂ)),
      bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p = 0 ∨
        B.JF Db (foldCV S.G.k S.G.r s a F) (B.gq Db p) = J₁ (B.gq Db p) := by
    have h0 := ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_restrict Db)
    filter_upwards [h0] with p hp
    by_cases hq : p ∈ B.Qset Db
    · right
      have hg := Formalism.FourierDecayAlt.P.big_cell_domain S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db p (hp hq)
      rw [hBF E Wp Wq S T f χ ν' m₀ top A₀ hB v hcl ε hε hJF a hlen _ hg]
      exact (hR _ _ _ _ _ _ _ _ _ hOpen hcl _ hJF s a _ (om_sub hg)).symm
    · left
      exact le_antisymm (not_lt.1 hq) (Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ p)
  have hN1 : jNormSq S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z')
      (fun q => B.hsVec (J₁ (B.gq Db q))) ≠ ⊤ := by
    have h := hL2 E Wp Wq S T f χ ν' m₀ top A₀ hB v ε hε a hlen
    unfold B.normSq at h
    unfold jNormSq at h ⊢
    rwa [lintegral_congr_ae (hae.mono fun p hp => ?_)] at h
    rcases hp with hp | hp
    · rw [show bcWeight S.G.k S.G.r (Tz S.G.k S.G.r (T v).base.z) (Tz S.G.k S.G.r (T v).base.z') p = 0 from hp]
      simp
    · show ENNReal.ofReal (_ * ‖B.hsVec (B.JF Db (foldCV S.G.k S.G.r s a F) (B.gq Db p))‖ ^ 2) = _
      rw [hp]
  have hN2 : jNormSq S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z')
      (fun q => B.hsVec (B.JF Db F (B.gq Db q))) ≠ ⊤ :=
    hL2 E Wp Wq S T f χ ν' m₀ top A₀ hB v ε hε [] (Nat.zero_le _)
  have hBeq := hBe E Wp Wq S T v hplace e hFr J₁ hJ₁m (B.JF Db F) hJF hN1 hN2
  unfold C7.principalHermitianLattice B.beta
  show _ = MA.ipA (D.parOf S v) (trJ S T v e J₁) (trJ S T v e (B.JF Db F))
  rw [← hBeq]
  unfold betaBig
  refine integral_congr_ae (hae.mono fun p hp => ?_)
  rcases hp with hp | hp
  · show ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) * _ =
      ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) * _
    rw [hp]; simp
  · show ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) *
        inner ℂ (B.hsVec (B.JF Db F (B.gq Db p))) (B.hsVec (B.JF Db (foldCV S.G.k S.G.r s a F) (B.gq Db p))) =
      ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) *
        inner ℂ (B.hsVec (B.JF Db F (B.gq Db p))) (B.hsVec (J₁ (B.gq Db p)))
    rw [hp]

end Formalism.FourierDecayAlt.P.CutMP.En
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCutTr
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section helpers

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem cutTr_Gf_gq (D : B.RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hc : ∀ a, q.1 a ≠ 0)
    (hζ : Tz k r D.z * Tz k r D.z' < Complex.normSq q.2) :
    Formalism.QuantumDeterminants.Gf k r D.z D.z' (B.gq D q) =
      (∏ l, Complex.normSq (q.1 l)) * (Complex.normSq q.2 - Tz k r D.z * Tz k r D.z') := by
  have hsec := D.sec.2 q.2 hζ
  have hmin := big_cell_minors_holds k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem
  have hz := hmin.2.2 hc
  rw [Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem, hsec.2] at hz
  have hr := hmin.1 (Fin.last r)
  set P := Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) ⟨r, by omega⟩ with hP
  have hPe : P = ∏ a : Fin r, q.1 a := by
    have : P = ∏ a : Fin r with a.val < (Fin.last r).val, q.1 a := hr
    rw [this]
    congr 1
    ext a
    simp
  have hP0 : P ≠ 0 := by
    rw [hPe]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  have hlast : Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1)) = q.2 * P := by
    unfold zeta at hz
    rw [← hP] at hz
    have h2 := div_mul_cancel₀ (Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1))) hP0
    rw [hz] at h2
    exact h2.symm
  show Formalism.QuantumDeterminants.Gf k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) = _
  unfold Formalism.QuantumDeterminants.Gf
  rw [hlast, ← hP, Complex.normSq_mul, hPe, map_prod]
  ring

theorem cutTr_hsVec_contDiff [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] :
    ContDiff ℝ ∞ (B.hsVec : (Wq →L[ℂ] Wp) → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) := by
  have h : (B.hsVec : (Wq →L[ℂ] Wp) → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) =
      ⇑((LinearMap.toContinuousLinearMap (Formalism.FourierDecayAlt.P.JFxI.hsVecL (Wp := Wp) (Wq := Wq))).restrictScalars ℝ) := rfl
  rw [h]
  exact ContinuousLinearMap.contDiff _

theorem cutTr_jgq_smooth (D : B.RealPlaceData k r Wp Wq) (J : B.Mat k r → (Wq →L[ℂ] Wp)) (Om : Set (B.Mat k r))
    (hJ : Q.SmoothLev k r 0 Om J) (hOm : ∀ q ∈ JF.QDom k r D.z D.z', B.gq D q ∈ Om) :
    ContDiffOn ℝ ∞ (fun q => J (B.gq D q)) (JF.QDom k r D.z D.z') := by
  have hg : ContDiffOn ℝ ∞ (fun q => B.gq D q) (JF.QDom k r D.z D.z') :=
    contDiffOn_infty.2 fun n => Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn D n
  refine contDiffOn_of_locally_contDiffOn fun q hq => ?_
  have hG := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hq
  obtain ⟨U, F', hU, hgU, hc, he⟩ := hJ (B.gq D q) ⟨Formalism.FourierDecayAlt.P.WordKeyIdentity.glev0 hG.1, hOm q hq⟩
  refine ⟨JF.QDom k r D.z D.z' ∩ (fun q => B.gq D q) ⁻¹' U,
    hg.continuousOn.isOpen_inter_preimage (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open D.z D.z') hU, ⟨hq, hgU⟩, ?_⟩
  have hcomp : ContDiffOn ℝ ∞ (F' ∘ fun q => B.gq D q)
      (JF.QDom k r D.z D.z' ∩ (JF.QDom k r D.z D.z' ∩ (fun q => B.gq D q) ⁻¹' U)) :=
    hc.comp (hg.mono Set.inter_subset_left) fun x hx => hx.2.2
  refine hcomp.congr fun x hx => ?_
  exact he _ hx.2.2 (Formalism.FourierDecayAlt.P.WordKeyIdentity.glev0 (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hx.1).1)

end helpers

theorem cutTr_normSq_contDiff : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
  have : (fun z : ℂ => Complex.normSq z) = fun z => ‖z‖ ^ 2 := by
    funext z; exact Complex.normSq_eq_norm_sq z
  rw [this]
  exact contDiff_norm_sq ℝ

theorem cutoff_transport_to_model : CutTr := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he hJ c hc ε hε
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hQ : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' :=
    fun x hx => ⟨hx.1, hTT ▸ hx.2⟩
  have hOm : ∀ q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z', B.gq (T v).base q ∈ OmP S T v := by
    intro q hq
    have h := (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq).2
    exact ⟨h.2, fun a => h.1 _ (by simp)⟩
  funext ρ
  set u : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ := fun q =>
    ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
      inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (B.JF (T v).base (f v) (B.gq (T v).base q.1))) with hu_def
  have hu : u ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT := by
    show ContDiffOn ℝ MA.sm (MA.ext u) (MA.Qset _ _)
    have hg : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => B.JF (T v).base (f v) (B.gq (T v).base x))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      (cutTr_jgq_smooth (T v).base _ _ hJ.1 hOm).mono hQ
    have he' : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => e ρ x.2) (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
    have hwc : ContDiff ℝ ∞ (fun x : MA.E (D.parOf S v).r => MA.wq S.G.k x (D.parOf S v).TT) := by
      have hn := cutTr_normSq_contDiff
      unfold MA.wq
      fun_prop
    have hwp : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.wq S.G.k x (D.parOf S v).TT ≠ 0 := by
      intro x hx
      unfold MA.wq
      exact (mul_pos (Finset.prod_pos fun l _ => pow_pos (Complex.normSq_pos.2 (hx.1 l)) _)
        (pow_pos (sub_pos.2 hx.2) _)).ne'
    have hw : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hwc.contDiffOn.sqrt hwp)
    refine (hw.mul ((cutTr_hsVec_contDiff.comp_contDiffOn he').inner ℂ
      (cutTr_hsVec_contDiff.comp_contDiffOn hg))).congr ?_
    intro x hx
    simp [MA.ext, hx, hu_def]
  have hL : trJ S T v e (B.JF (T v).base (D.cutF (T v).base χ (f v) ε)) ρ =
      MA.toSm (D.parOf S v) (fun q => ((c.sc ε 1 (MA.Gq (D.parOf S v) q) : ℝ) : ℂ) * u q) := by
    unfold trJ
    congr 1
    funext q
    rw [Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_right,
      cutTr_Gf_gq (T v).base q.2.1 (hTT ▸ q.2.2)]
    simp only [hu_def, LE.Cut.sc, hc, pow_one, MA.Gq, hTT]
    ring
  have hR : (trJ S T v e (B.JF (T v).base (f v)) ρ) = ⟨u, hu⟩ := by
    unfold trJ MA.toSm
    rw [dite_eq_left hu]
  rw [hL]
  show _ = MA.toSm (D.parOf S v) (fun q => ((c.sc ε 1 (MA.Gq (D.parOf S v) q) : ℝ) : ℂ) *
    (trJ S T v e (B.JF (T v).base (f v)) ρ).1 q)
  rw [hR]

end Formalism.FourierDecayAlt.P.CutMP
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gcut

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem gcut_ckOn_smul {m : ℕ∞} {a : B.Mat k r → ℂ} (ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn m (B.GV k r) F) :
    B.CkOn m (B.GV k r) (fun g => a g • F g) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hF g₀ hg₀
  refine ⟨U, fun g => a g • f' g, hU, hgU,
    ((ha.of_le (by exact_mod_cast le_top)).contDiffOn).smul hc, fun g hg hG => ?_⟩
  simp only [hff g hg hG]

theorem gcut_sum_const {X : Type*} (c : ℕ) (l : List X) :
    (((l.map (fun _ => c)).sum : ℕ) : ℝ) = (c : ℝ) * l.length := by
  have h : ∀ l : List X, (l.map (fun _ => c)).sum = c * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
  rw [h]; push_cast; ring

theorem gcut_leib {a : B.Mat k r → ℂ} (ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a) (c n : ℕ) (Ca : ℝ)
    (hWB : PI.UnitaryCorollaryDerivatives.WB (fun _ => c) a n Ca 0)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV k r) F) {A Bg : ℝ} (hc : (c : ℝ) ≤ Bg)
    (hFg : ∀ m : ℕ, B.InCC (A - Bg * m) m F) :
    B.InCC (A - Bg * n) n (fun g => a g • F g) := by
  choose cF hcF using hFg
  set K : ℝ := ∑ j ∈ Finset.range (n + 1), |cF j| with hK
  have hKj : ∀ j ≤ n, |cF j| ≤ K := fun j hj =>
    Finset.single_le_sum (f := fun j => |cF j|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hBg : 0 ≤ Bg := le_trans (Nat.cast_nonneg c) hc
  refine ⟨2 ^ n * (|Ca| * K), gcut_ckOn_smul ha (sCkOn_mono le_top hF), fun u v hu hv hl g hg => ?_⟩
  set L : ℂ →L[ℂ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) with hL
  set a' : B.Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) := fun h => L (a h) with ha'
  have hfun : (fun g => a g • F g) = ap a' F := by funext h; simp [ap, ha', hL]
  have hlie := lie_LR (unit_lie hu) (unit_lie hv)
  have hca : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a' := (L.restrictScalars ℝ).contDiff.comp ha
  have hP : Pr (∅ : Set (B.Mat k r)) (B.GV k r) ((wL u ++ wR v).length : ℕ) a' F :=
    ⟨PI.UnitaryCorollaryDerivatives.ckOn_of_contDiff hca, sCkOn_mono le_top hF, fun _ _ h => absurd h (Set.notMem_empty _)⟩
  have hp := gN_pos hg
  have hg1 := gN_ge_one hg
  have hLn : ∀ x : ℂ, ‖L x‖ ≤ ‖x‖ := by
    intro x
    have : L x = x • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := by simp [hL]
    rw [this, norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_id_le)
  have hw : (wL u ++ wR v).length = u.length + v.length := len_LR u v
  have hb := leib_bound isOpen_empty (fun g hg => Or.inr hg) g hg
    (|Ca| * K * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A)) (wL u ++ wR v) a' F hlie hP (by
      intro w₁ w₂ hs₁ hs₂ hl₁₂
      obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR hs₁
      obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR hs₂
      rw [len_LR, len_LR] at hl₁₂
      have hl₁ : u₁.length + v₁.length ≤ n := by
        have := hu₁.length_le; have := hv₁.length_le; omega
      have hl₂ : u₂.length + v₂.length ≤ n := by
        have := hu₂.length_le; have := hv₂.length_le; omega
      have hu₁' : ∀ X ∈ u₁, B.unitLie k r X := fun X hX => hu X (hu₁.subset hX)
      have hv₁' : ∀ X ∈ v₁, B.unitLie k r X := fun X hX => hv X (hv₁.subset hX)
      have hu₂' : ∀ X ∈ u₂, B.unitLie k r X := fun X hX => hu X (hu₂.subset hX)
      have hv₂' : ∀ X ∈ v₂, B.unitLie k r X := fun X hX => hv X (hv₂.subset hX)
      have ea : Dw (wL u₁ ++ wR v₁) a' g = L (Dw (wL u₁ ++ wR v₁) a g) :=
        PI.UnitaryCorollaryDerivatives.Dw_clm L _ (lie_LR (unit_lie hu₁') (unit_lie hv₁'))
          (PI.UnitaryCorollaryDerivatives.ckOn_of_contDiff ha) g hg
      set L₁ : ℝ := ((u₁.length + v₁.length : ℕ) : ℝ) with hL₁
      set L₂ : ℝ := ((u₂.length + v₂.length : ℕ) : ℝ) with hL₂
      have b1 : ‖Dw (wL u₁ ++ wR v₁) a' g‖ ≤ |Ca| * B.gN g ^ (Bg * L₁) := by
        rw [ea]
        refine (hLn _).trans ?_
        rw [← dLR_eq]
        have h1 := hWB u₁ v₁ hu₁' hv₁' hl₁ g hg
        rw [gcut_sum_const, List.length_append, zero_add] at h1
        have h1' : ‖B.dLR u₁ v₁ a g‖ ≤ Ca * B.gN g ^ ((c : ℝ) * L₁) := by
          rw [hL₁]; exact h1
        have h2 : B.gN g ^ ((c : ℝ) * L₁) ≤ B.gN g ^ (Bg * L₁) :=
          Real.rpow_le_rpow_of_exponent_le hg1 (mul_le_mul_of_nonneg_right hc (by rw [hL₁]; positivity))
        calc _ ≤ Ca * B.gN g ^ ((c : ℝ) * L₁) := h1'
          _ ≤ |Ca| * B.gN g ^ ((c : ℝ) * L₁) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hp.le _)
          _ ≤ |Ca| * B.gN g ^ (Bg * L₁) :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      have b2 : ‖Dw (wL u₂ ++ wR v₂) F g‖ ≤ K * B.gN g ^ (Bg * L₂ - A) := by
        rw [← dLR_eq]
        have h1 := (hcF (u₂.length + v₂.length)).2 u₂ v₂ hu₂' hv₂' le_rfl g hg
        have e : B.gN g ^ (Bg * L₂ - A) * B.gN g ^ (A - Bg * L₂) = 1 := by
          rw [← Real.rpow_add hp]; simp
        have h4 : ‖B.dLR u₂ v₂ F g‖ = B.gN g ^ (Bg * L₂ - A) * (B.gN g ^ (A - Bg * L₂) * ‖B.dLR u₂ v₂ F g‖) := by
          rw [← mul_assoc, e, one_mul]
        rw [h4]
        have h5 : B.gN g ^ (A - Bg * L₂) * ‖B.dLR u₂ v₂ F g‖ ≤ K := by
          refine le_trans ?_ (hKj _ hl₂)
          refine le_trans ?_ (le_abs_self _)
          simpa [hL₂] using h1
        calc _ ≤ B.gN g ^ (Bg * L₂ - A) * K := mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hp.le _)
          _ = K * B.gN g ^ (Bg * L₂ - A) := mul_comm _ _
      have hsum : Bg * L₁ + (Bg * L₂ - A) = Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A := by
        rw [← hl₁₂, hL₁, hL₂]; push_cast; ring
      calc ‖Dw (wL u₁ ++ wR v₁) a' g‖ * ‖Dw (wL u₂ ++ wR v₂) F g‖
          ≤ (|Ca| * B.gN g ^ (Bg * L₁)) * (K * B.gN g ^ (Bg * L₂ - A)) :=
            mul_le_mul b1 b2 (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hp.le _))
        _ = |Ca| * K * (B.gN g ^ (Bg * L₁) * B.gN g ^ (Bg * L₂ - A)) := by ring
        _ = |Ca| * K * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A) := by
            rw [← Real.rpow_add hp, hsum])
  rw [hfun, dLR_eq]
  have hlen : ((wL u ++ wR v).length : ℕ) ≤ n := by rw [hw]; exact hl
  have e2 : B.gN g ^ (A - Bg * n) * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A) ≤ 1 := by
    rw [← Real.rpow_add hp]
    refine Real.rpow_le_one_of_one_le_of_nonpos hg1 ?_
    have : (((wL u ++ wR v).length : ℕ) : ℝ) ≤ n := by exact_mod_cast hlen
    nlinarith
  have e3 : (2 : ℝ) ^ (wL u ++ wR v).length ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hlen
  have hCK : 0 ≤ |Ca| * K := mul_nonneg (abs_nonneg _) hK0
  calc B.gN g ^ (A - Bg * n) * ‖Dw (wL u ++ wR v) (ap a' F) g‖
      ≤ B.gN g ^ (A - Bg * n) * (2 ^ (wL u ++ wR v).length *
          (|Ca| * K * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A))) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hp.le _)
    _ = 2 ^ (wL u ++ wR v).length * (|Ca| * K) *
          (B.gN g ^ (A - Bg * n) * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A)) := by ring
    _ ≤ 2 ^ (wL u ++ wR v).length * (|Ca| * K) * 1 :=
        mul_le_mul_of_nonneg_left e2 (mul_nonneg (by positivity) hCK)
    _ ≤ 2 ^ n * (|Ca| * K) := by rw [mul_one]; exact mul_le_mul_of_nonneg_right e3 hCK

theorem gcut_graded (z z' : Fin (2 * r + k + 1) → ℂ) (h : ℝ → ℝ) (ε : ℝ) (hh : U.IsCutG ε h) {A Bg : ℝ}
    (hBg : 2 * ((r : ℝ) + 1) ≤ Bg) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV k r) F)
    (hFg : ∀ m : ℕ, B.InCC (A - Bg * m) m F) :
    B.CkOn ⊤ (B.GV k r) (fun g => ((h (Gf k r z z' g) : ℝ) : ℂ) • F g) ∧
      ∀ m : ℕ, B.InCC (A - Bg * m) m (fun g => ((h (Gf k r z z' g) : ℝ) : ℂ) • F g) := by
  have hW := PI.UnitaryCorollaryDerivatives.gfWB_of PI.UnitaryCorollaryDerivatives.generating_function_polynomial PI.UnitaryCorollaryDerivatives.polynomial_bound PI.UnitaryCorollaryDerivatives.compact_region_estimate
  have hcd := (hW k r z z' h ε 0 hh).1
  refine ⟨gcut_ckOn_smul hcd hF, fun m => ?_⟩
  obtain ⟨C, hC⟩ := (hW k r z z' h ε m hh).2
  exact gcut_leib hcd (2 * (r + 1)) m C hC hF (by push_cast; linarith) hFg

end gcut

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMRealInv
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def JDRInvFnM : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Y : ℂ) (p : B.SS k r), D.inSS p →
    ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ((r + k : ℕ) : ℕ∞) (B.GV k r) F →
      ∀ g ∈ B.GPos D, rvhatOp k r D.z D.z' Y (B.rho D p F) g = B.rho D p (rvhatOp k r D.z D.z' Y F) g

section poly

open Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {k r : ℕ}

theorem rim_herm (v w : Fin (2 * r + k + 1) → ℂ) :
    U.IsPolyDeg 1 (fun g : Q.Mx k r => herm (Hpk k r) (g *ᵥ v) w) := by
  have e : (fun g : Q.Mx k r => herm (Hpk k r) (g *ᵥ v) w) =
      fun g => ∑ a, star (w a) * ∑ b, Hpk k r a b * ∑ c, g b c * v c := by
    funext g
    simp only [herm, Matrix.mulVec, dotProduct, Pi.star_apply]
  rw [e]
  exact pd_sum _ fun a _ => ri_mul_left _ (pd_sum _ fun b _ => ri_mul_left _
    (pd_sum _ fun c _ => ri_mul_right (pd_entry b c) _))

theorem rim_rowV (z : Fin (2 * r + k + 1) → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (p q : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g => rowV k r z g J p q) := by
  unfold rowV
  by_cases h : p.val < r
  · simp only [dif_pos h]
    exact rim_herm _ _
  · by_cases h2 : p.val = r
    · simp only [dif_neg h, dif_pos h2]
      exact rim_herm _ _
    · simp only [dif_neg h, dif_neg h2]
      exact pd_const _ 1

theorem rim_alJ (z : Fin (2 * r + k + 1) → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) :
    U.IsPolyDeg (2 * r + k + 1) (fun g => alJ k r z g J) :=
  pd_det (fun g => Matrix.of fun p q => rowV k r z g J p q) fun a b => by
    simpa only [Matrix.of_apply] using rim_rowV z J a b

end poly

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def rimCat {ι : Type} (Θs : ι → B.DiffOp k r Wp Wq) : List ι → B.DiffOp k r Wp Wq
  | [] => []
  | i :: l => Θs i ++ rimCat Θs l

theorem rimCat_poly {ι : Type} {Θs : ι → B.DiffOp k r Wp Wq} {t κ : ℕ} (h : ∀ i, PolyOp t κ (Θs i)) :
    ∀ l, PolyOp t κ (rimCat Θs l)
  | [] => fun T hT => absurd hT List.not_mem_nil
  | i :: l => QMinOp.polyOp_append (h i) (rimCat_poly h l)

theorem rimCat_apply {ι : Type} (Θs : ι → B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    ∀ l, B.opApply (rimCat Θs l) F g = (l.map fun i => B.opApply (Θs i) F g).sum
  | [] => by simp [rimCat, B.opApply]
  | i :: l => by rw [rimCat, QMinOp.opApply_append, rimCat_apply Θs F g l, List.map_cons, List.sum_cons]

theorem rimCat_order {ι : Type} {Θs : ι → B.DiffOp k r Wp Wq} {t κ : ℕ} (h : ∀ i, PolyOp t κ (Θs i))
    (ho : ∀ i, B.opOrder (Θs i) = t) (i : ι) (l : List ι) :
    B.opOrder (rimCat Θs (i :: l)) = t := by
  rw [rimCat, QMinOp.opOrder_append, ho i]
  exact max_eq_left (ri_order_le _ (rimCat_poly h l))

theorem residue_rows_strict_mono : StrictMono (rowsR k r 0) := by
  intro a b h
  have h' : a.val < b.val := h
  show (rowsR k r 0 a).val < (rowsR k r 0 b).val
  simp only [rowsR]
  split_ifs <;> omega

theorem rim_mem : rowsR k r 0 ∈ jSetR k r := by
  classical
  simp only [jSetR, Finset.mem_filter, Finset.mem_univ, true_and]
  convert (residue_rows_strict_mono (k := k) (r := r))

theorem rim_real (z z' : Fin (2 * r + k + 1) → ℂ) (Y ε : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp (r + k) (2 * r + k + 1) Θ ∧ B.opOrder Θ = r + k ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F →
        ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ε • rvhatOp k r z z' Y F g := by
  have h : ∀ x : Fin (k + 1) × (Fin (r + k) → Fin (2 * r + k + 1)),
      ∃ Θ : B.DiffOp k r Wp Wq, PolyOp (r + k) (2 * r + k + 1) Θ ∧ B.opOrder Θ = r + k ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F →
        ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ∑ j ∈ ({()} : Finset Unit),
          (fun (_ : Unit) (g : B.Mat k r) =>
            ε * (((-1 : ℂ) ^ (x.1 : ℕ)) * z' (wI k r x.1) * alJ k r z g x.2)) j g •
            qminorOp (Q.EH k r) x.2 ((fun (_ : Unit) => colsV k r x.1) j) (Q.uC k r (Fin.last r) Y - 1) F g := fun x =>
    QMinOp.qminOpRep {()} x.2 (fun _ => colsV k r x.1) _
      (fun _ _ => ri_mul_left _ (ri_mul_left _ (rim_alJ z x.2))) _
  choose Θs hP hO hR using h
  let idx : List (Fin (k + 1) × (Fin (r + k) → Fin (2 * r + k + 1))) :=
    ((Finset.univ : Finset (Fin (k + 1))) ×ˢ jSetR k r).toList
  have hmem : ((0 : Fin (k + 1)), rowsR k r 0) ∈ idx := by
    simp only [idx, Finset.mem_toList, Finset.mem_product, Finset.mem_univ, true_and]
    exact rim_mem
  refine ⟨rimCat Θs idx, rimCat_poly hP _, ?_, ?_⟩
  · obtain ⟨i, l, hl⟩ : ∃ i l, idx = i :: l := by
      cases h' : idx with
      | nil => rw [h'] at hmem; exact absurd hmem List.not_mem_nil
      | cons i l => exact ⟨i, l, rfl⟩
    rw [hl]
    exact rimCat_order hP hO _ _
  · intro UU F hF g hgU hg
    rw [rimCat_apply]
    simp only [idx]
    rw [Finset.sum_map_toList, Finset.sum_product]
    simp only [rvhatOp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [hR (t, J) UU F hF g hgU hg, Finset.sum_singleton, smul_smul]

end ops

theorem jDRRealInvM_of_inv (hI : JDRInvFnM) : JDRRealInvM := by
  intro ε Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨Θ, hP, hO, hR⟩ := rim_real (Wp := Wp (S.pl v)) (Wq := Wq (S.pl v)) (T v).base.z (T v).base.z' (y : ℂ) ε
  have hn : 0 < 2 * S.G.r + S.G.k + 1 := by omega
  refine ⟨Θ, QMinOp.polyOp_mono hP (by omega) (Nat.le_mul_of_pos_left _ (by omega)), ?_, ?_⟩
  · intro p hp F hF g hg
    rw [hO] at hF
    have hgG : g ∈ B.GV S.G.k S.G.r := hg.1
    have hsg : B.sgs p g ∈ B.GV S.G.k S.G.r := Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group (T v).base hp hgG
    rw [hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho (T v).base hp hF) g hgG hgG]
    have e2 : B.rho (T v).base p (B.opApply Θ F) g =
        B.rho (T v).base p (fun x => ε • rvhatOp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) F x) g := by
      simp only [B.rho]
      rw [hR _ _ hF _ hsg hsg]
    rw [e2, hI S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base (y : ℂ) p hp F hF g hg]
    simp only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  · intro U F hU hF g hg
    have hgG : g ∈ B.GV S.G.k S.G.r := by simpa [Q.Glev] using hg.1
    refine hR (Q.Glev S.G.k S.G.r 0 ∩ U) F ?_ g hg hgG
    intro g₀ hg₀
    obtain ⟨U', F', hU', hg₀U, hc, he⟩ := hF g₀ hg₀
    refine ⟨U', F', hU', hg₀U, hc.of_le (by exact_mod_cast le_top), fun x hx hxG => he x hx ?_⟩
    simpa [Q.Glev] using hxG

end

end Formalism.FourierDecayAlt.P.CutMP
end
