module

public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.IntFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HolSubMul

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
  (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop)

def algCls (T : CDVR) (ι : c.F →+* T.Fr) (y : IntFr Xo c T ι) : Prop := y.IsAlg

def valSet (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) :=
  Set.range (vAtV : PtV Xo c cls Unit (fun _ _ _ _ => True) la → Rul Xo c → EReal)

variable {Xo c cls}

theorem isVal_vAt {PY : Type} {lies : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY → Prop}
    {la : HeightOneSpectrum (𝓞 c.F)} (y : PtV Xo c cls PY lies la) : IsVal la (vAtV y) :=
  ⟨vAtV_zero y, vAtV_ne_bot y, vAtV_add y, fun a f ha => vAtV_smul y a f ha, vAtV_mul y⟩

theorem isVal_valSet (la : HeightOneSpectrum (𝓞 c.F)) : ∀ v ∈ valSet Xo c cls la, IsVal la v := by
  rintro _ ⟨y, rfl⟩
  exact isVal_vAt y

variable (Xo c cls)

def LiesTotal (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ la (T : CDVR) (ι : c.F →+* T.Fr) (e : ℕ), OverLa la T.V ι e → ∀ y : IntFr Xo c T ι, cls T ι y →
    ∃ η, lies la T ι y η

variable {Xo c cls}

theorem nonneg_iff_of_liesTotal {PY : HeightOneSpectrum (𝓞 c.F) → Type}
    {lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop}
    (h : LiesTotal Xo c cls PY lies) (f : Rul Xo c) :
    (∀ la, ∀ v ∈ valSet Xo c cls la, 0 ≤ v f) ↔
      ∀ la (y : PtV Xo c cls (PY la) (lies la) la), 0 ≤ vAtV y f := by
  constructor
  · rintro h0 la ⟨q, T, ι, e, ho, y, hy, η, hη, rfl⟩
    exact h0 la _ ⟨PtV.mk la ho y hy () trivial, rfl⟩
  · rintro h0 la _ ⟨⟨q, T, ι, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
    obtain ⟨η', hη'⟩ := h la T ι e ho y hy
    exact h0 la (PtV.mk la ho y hy η' hη')

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

section Sup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  (X : Comp → Data E r) (la : ∀ c, ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r)

theorem supE_add_le (P Q : FDSec X) : supE X la (P + Q) ≤ supE X la P + supE X la Q := by
  unfold supE
  refine iSup_le fun p => ?_
  have h1 : (X p.1).pnorm (la p.1) ((P + Q) p.1) p.2 ≤
      (X p.1).pnorm (la p.1) (P p.1) p.2 + (X p.1).pnorm (la p.1) (Q p.1) p.2 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
  calc ENNReal.ofReal ((X p.1).pnorm (la p.1) ((P + Q) p.1) p.2)
      ≤ ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2) +
          ENNReal.ofReal ((X p.1).pnorm (la p.1) (Q p.1) p.2) :=
        (ENNReal.ofReal_le_ofReal h1).trans ENNReal.ofReal_add_le
    _ ≤ (⨆ p : FPt X, ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) +
          ⨆ p : FPt X, ENNReal.ofReal ((X p.1).pnorm (la p.1) (Q p.1) p.2) :=
        add_le_add (le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) p)
          (le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (Q p.1) p.2)) p)

theorem supE_smul (a : ℂ) (P : FDSec X) : supE X la (a • P) = ENNReal.ofReal ‖a‖ * supE X la P := by
  unfold supE
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun p => ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  show ‖a * P p.1 p.2‖ * _ = ‖a‖ * (‖P p.1 p.2‖ * _)
  rw [norm_mul]
  ring

theorem supE_ne_top [Fintype Comp] {P : FDSec X} (h : P ∈ holSub X la) : supE X la P ≠ ⊤ := by
  unfold holSub at h
  induction h using Submodule.span_induction with
  | mem P hP =>
    have hb : ∀ c, ∃ C : ℝ, ∀ x ∈ (X c).dom, (X c).pnorm (la c) (P c) x ≤ C := fun c => (hP c).1.2
    choose C hC using hb
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑ c, |C c|))
      (iSup_le fun p => ENNReal.ofReal_le_ofReal ?_)
    calc (X p.1).pnorm (la p.1) (P p.1) p.2 ≤ C p.1 := hC p.1 p.2 p.2.2
      _ ≤ |C p.1| := le_abs_self _
      _ ≤ ∑ c, |C c| := Finset.single_le_sum (fun c _ => abs_nonneg (C c)) (Finset.mem_univ _)
  | zero =>
    refine ne_top_of_le_ne_top ENNReal.zero_ne_top (iSup_le fun p => ?_)
    simp [ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm]
  | add P Q _ _ hP hQ =>
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hP, hQ⟩) (supE_add_le X la P Q)
  | smul a P _ hP =>
    rw [supE_smul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP

end Sup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)


open Classical in
def goodOf (σ : c.F →+* ℂ) : c.F →+* ℂ := if GoodEmb c σ then σ else (starRingEnd ℂ).comp σ

theorem norm_goodOf (σ : c.F →+* ℂ) (x : c.F) : ‖goodOf c σ x‖ = ‖σ x‖ := by
  unfold goodOf
  split_ifs <;> simp

theorem goodEmb_goodOf (σ : c.F →+* ℂ) : GoodEmb c (goodOf c σ) := by
  unfold goodOf
  split_ifs with h
  · exact h
  · unfold GoodEmb at h ⊢
    set β := (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ with hβ
    have hβsq : β ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq, hβ, ← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
    have hneg : β = -H.rt0 := by
      have hm : (β - H.rt0) * (β + H.rt0) = 0 := by
        rw [show (β - H.rt0) * (β + H.rt0) = β ^ 2 - H.rt0 ^ 2 by ring, hβsq, sub_self]
      rcases mul_eq_zero.mp hm with h1 | h1
      · exact absurd (sub_eq_zero.mp h1) h
      · exact eq_neg_of_add_eq_zero_left h1
    have hd : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
    have h3 := congrArg Complex.im H.sqrt_neg_disc_sq
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero] at h2 h3
    have hre : H.rt0.re = 0 := by
      rcases mul_eq_zero.mp (show H.rt0.re * H.rt0.im = 0 by nlinarith) with h4 | h4
      · exact h4
      · rw [h4] at h2
        exfalso
        nlinarith [mul_self_nonneg H.rt0.re]
    show starRingEnd ℂ β = H.rt0
    rw [hneg, map_neg]
    apply Complex.ext <;> simp [hre]

theorem IsNormOn.of_goodOf {C : Submodule c.F (Rul Xo c)} {σ : c.F →+* ℂ} {N : Rul Xo c → ℝ}
    (h : IsNormOn C (goodOf c σ) N) : IsNormOn C σ N := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by simpa only [norm_goodOf] using h1, by simpa only [norm_goodOf] using h2,
    by simpa only [norm_goodOf] using h3, by simpa only [norm_goodOf] using h4⟩

def lieFac (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

theorem lieFac_pos (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : 0 < lieFac Dw x a := Real.exp_pos _

def supC (x : ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ℝ :=
  lieFac Dw x a * supN (U σ).X (laU (U σ) a n) (rdU (U σ) f)

def SupDef : Prop :=
  ∀ a n, Dom a n → ∀ σ, GoodEmb c σ → ∀ f ∈ cusp Xo c U a n, supN (U σ).X (laU (U σ) a n) (rdU (U σ) f) = 0 → f = 0

variable {Xo c U}

theorem supE_cusp_ne_top {a n} {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n) :
    supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) ≠ ⊤ := by
  have h1 := (Submodule.mem_inf.mp hf).2
  have h2 := Submodule.mem_iInf _ |>.mp h1 σ
  have h3 := Submodule.mem_iInf _ |>.mp h2 hσ
  exact supE_ne_top (U σ).X (laU (U σ) a n) (Submodule.mem_comap.mp h3)

theorem isNormOn_supC (x : ℝ) (h : SupDef Xo c U) {a n} (hd : Dom a n) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) :
    IsNormOn (cusp Xo c U a n) σ (supC Xo c U x σ a n) := by
  constructor
  · intro f _
    exact mul_nonneg (lieFac_pos _ _ _).le (supN_nonneg _ _ _)
  · intro f hf h0
    exact h a n hd σ hσ f hf ((mul_eq_zero.mp h0).resolve_left (lieFac_pos _ _ _).ne')
  · intro y f _
    unfold supC supN
    rw [map_smulₛₗ, supE_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
    ring
  · intro f hf g hg
    unfold supC supN
    rw [← mul_add, map_add (f := _), ← ENNReal.toReal_add (supE_cusp_ne_top hσ hf) (supE_cusp_ne_top hσ hg)]
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono ?_ (supE_add_le _ _ _ _)) (lieFac_pos _ _ _).le
    exact ENNReal.add_ne_top.mpr ⟨supE_cusp_ne_top hσ hf, supE_cusp_ne_top hσ hg⟩

variable (U)

-- Prefer the same-scalar submodule instance when elaborating the L² constructions.
attribute [local instance 2000] Submodule.module

def rdC (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : cusp Xo c U a n →ₛₗ[σ] FDSec (U σ).X :=
  (rdU (U σ)).comp (cusp Xo c U a n).subtype

variable {D : D7} (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ)

def CuspL2 : Prop := ∀ a n, Dom a n → JMemL2 V σ (rdC U σ a n) dict mu


open Classical in
def l2C (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : JMemL2 V σ (rdC U σ a n) dict mu) (f : Rul Xo c) : ℝ :=
  if hf : f ∈ cusp Xo c U a n then
    lieFac Dw x a * l2NormAlt V σ (rdC U σ a n) dict mu h ⟨f, hf⟩ else 0

def L2DefiniteCuspForms (h : CuspL2 U σ V dict mu) : Prop :=
  ∀ a n (hd : Dom a n), L2Definite V σ (rdC U σ a n) dict mu (h a n hd)

variable {U σ V dict mu}

theorem isNormOn_l2C (x₀ : ℝ) {h : CuspL2 U σ V dict mu} (h1 : L2DefiniteCuspForms U σ V dict mu h) {a n} (hd : Dom a n) :
    IsNormOn (cusp Xo c U a n) σ (l2C U σ V dict mu x₀ a n (h a n hd)) := by
  constructor
  · intro f hf
    rw [l2C, dite_eq_left hf]; exact mul_nonneg (lieFac_pos _ _ _).le (l2Norm_nonneg_bis _ _ _ _ _ _ _)
  · intro f hf h0
    rw [l2C, dite_eq_left hf] at h0
    exact congrArg Subtype.val (h1 a n hd ⟨f, hf⟩ ((mul_eq_zero.mp h0).resolve_left (lieFac_pos _ _ _).ne'))
  · intro x f hf
    rw [l2C, l2C, dite_eq_left hf, dite_eq_left (Submodule.smul_mem _ x hf)]
    have := l2Norm_smul_alt V σ (rdC U σ a n) dict mu (h a n hd) x ⟨f, hf⟩
    exact (congrArg (lieFac Dw x₀ a * ·) this).trans (by ring)
  · intro f hf g hg
    rw [l2C, l2C, l2C, dite_eq_left hf, dite_eq_left hg, dite_eq_left (Submodule.add_mem _ hf hg), ← mul_add]
    exact mul_le_mul_of_nonneg_left (L2Norm_add_le V σ (rdC U σ a n) dict mu (h a n hd) ⟨f, hf⟩ ⟨g, hg⟩)
      (lieFac_pos _ _ _).le

theorem l2C_le_supC (x : ℝ) (hσ : GoodEmb c σ) {a n} (h : JMemL2 V σ (rdC U σ a n) dict mu)
    (hd : ∀ g, (dict g).2 ∈ ((U σ).X (dict g).1).dom) (hm : MuUnit V dict mu) :
    ∀ f ∈ cusp Xo c U a n, l2C U σ V dict mu x a n h f ≤ supC Xo c U x σ a n f := by
  intro f hf
  unfold l2C supC
  rw [dite_eq_left hf]
  refine mul_le_mul_of_nonneg_left ?_ (lieFac_pos Dw x a).le
  exact L2Norm_le_sup_norm (V := V) (la := laU (U σ) a n) (rd := rdC U σ a n) (dict := dict) (mu := mu) (h := h)
    (hd := hd) (hm := hm) (f := ⟨f, hf⟩) (hfin := supE_cusp_ne_top hσ hf)

theorem rdC_continuousOn (hU : IsUnf (U σ)) {a n} (hd : Dom a n) (f : cusp Xo c U a n) (k : (U σ).Comp) :
    ContinuousOn (rdC U σ a n f k) ((U σ).X k).dom := by
  obtain ⟨-, -, -, -, hsec, -⟩ := hU
  have hf : (f : Rul Xo c) ∈ sec Xo c a n := (Submodule.mem_inf.mp f.2).1
  exact (hsec a n hd f hf k).1.continuousOn

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Calc

variable {X X' Y : Scheme.{0}}

def thfPull (L : LB X) (F : X' ⟶ X) (s : LB.Sec L) : LB.Sec (L.pull F) where
  f := fun (J : PUnit → L.ι) =>
    (F.appLE (L.U (J PUnit.unit)) ((L.pull F).U J) (LB.wchart_le L _ J PUnit.unit)).hom (s.f (J PUnit.unit))
  compat := fun (J J' : PUnit → L.ι) => fn_ext fun y hy => by
    have h₁ : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy.1
    have h₂ : F y ∈ L.U (J' PUnit.unit) := mem_pull.1 hy.2
    exact (gs_res _ y _ hy _).trans ((gs_appLE F _ _ _ (𝟙 _) y hy.1 _).trans ((gs_compat s (𝟙 X' ≫ F) y h₁ h₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
        ((gs_unit _ y _ hy _).trans (congrArg Units.val (gm_pull_g L F (𝟙 _) y J J' hy.1 hy.2)))
        ((gs_res _ y _ hy _).trans (gs_appLE F _ _ _ (𝟙 _) y hy.2 _)))))))

theorem chart_le_pullback_open (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (h : Y ⟶ X') (e : h ≫ F = φ) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => φ) j ≤ h ⁻¹ᵁ (L.pull F).U (fun _ => j 0) := by
  intro y hy
  have h0 := LB.wchart_le L (fun _ : Fin 1 => φ) j 0 hy
  show h y ∈ (L.pull F).U (fun _ => j 0)
  rw [mem_pull]
  subst e
  simpa using h0

def thfPull1 (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (h : Y ⟶ X') (e : h ≫ F = φ) (s : LB.Sec (L.pull F)) :
    LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)) where
  f := fun (j : Fin 1 → L.ι) => (h.appLE _ _ (chart_le_pullback_open L h e j)).hom (s.f (fun _ => j 0))
  compat := fun (j j' : Fin 1 → L.ι) => fn_ext fun y hy => by
    have h₁ : h y ∈ (L.pull F).U (fun _ => j 0) := chart_le_pullback_open L h e j hy.1
    have h₂ : h y ∈ (L.pull F).U (fun _ => j' 0) := chart_le_pullback_open L h e j' hy.2
    have g : gm (𝟙 Y) y _ ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)).g j j') =
        gm (𝟙 Y ≫ φ) y (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) :=
      (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2).trans (by rw [Fin.prod_univ_one, zpow_one])
    have eφ : (𝟙 Y ≫ h) ≫ F = 𝟙 Y ≫ φ := by rw [Category.assoc, e]
    exact (gs_res _ y _ hy _).trans ((gs_appLE h _ _ _ (𝟙 _) y hy.1 _).trans ((gs_compat s (𝟙 Y ≫ h) y h₁ h₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
        ((gs_unit _ y _ hy _).trans (congrArg Units.val (g.trans ((congrArg (fun q => gm q y (L.U (j 0) ⊓ L.U (j' 0))
          (L.g (j 0) (j' 0))) eφ).symm.trans (gm_pull_g L F (𝟙 Y ≫ h) y _ _ h₁ h₂).symm))))
        ((gs_res _ y _ hy _).trans (gs_appLE h _ _ _ (𝟙 _) y hy.2 _)))))))

theorem thf_secUp {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB)
    (hL' : L'.IsLB) (σ : LB.Sec L') : ∃ s : LB.Sec (L.pull F), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z)
      (J : PUnit → L.ι) (k : L'.ι), r z ∈ (L.pull F).U J → r z ∈ L'.U k →
      gs r z _ (s.f J) = (gw w r z (J PUnit.unit) k).val * gs r z _ (σ.f k) := by
  have hP : ∀ K : PUnit → L'.ι, (L'.pull (𝟙 X')).U K ≤ L'.U (K PUnit.unit) := fun K x hx => by
    have hx' := (mem_pull (L := L') (F := 𝟙 X')).1 hx
    simpa using hx'
  obtain ⟨w', hw'⟩ : ∃ w' : LB.Iso (L.pull F) (L'.pull (𝟙 X')), ∀ (Y : Scheme.{0}) (f : Y ⟶ X') (y : Y) (j : L'.ι)
      (K : PUnit → L.ι), f y ∈ L'.U j → f y ∈ (L.pull F).U K → gw w' f y j K = (gw w f y (K PUnit.unit) j)⁻¹ := by
    refine ⟨⟨fun p => (res (le_inf inf_le_right (inf_le_left.trans (hP p.1))) (w.s (p.2, p.1 PUnit.unit)))⁻¹⟩, ?_⟩
    intro Y f y j K hj hK
    have hm : f y ∈ (L'.pull (𝟙 X')).U (fun _ => j) ⊓ (L.pull F).U K :=
      ⟨(mem_pull (L := L') (F := 𝟙 X')).2 (by simpa using hj), hK⟩
    unfold gw
    dsimp only
    exact (map_inv (gm f y _) _).trans (congrArg (·⁻¹) (gm_res f y _ hm _))
  have hPG : PGen w' := by
    intro Y f y j j' k k' hj hj' hk hk'
    have hj0 : f y ∈ L'.U j := by simpa using hj
    have hj0' : f y ∈ L'.U j' := by simpa using hj'
    rw [hw' Y f y j k hj0 hk, hw' Y f y j' k' hj0' hk', gm_pull_g L F f y k k' hk hk', Category.comp_id,
      hw Y f y (k PUnit.unit) (k' PUnit.unit) j j' (mem_pull.1 hk) (mem_pull.1 hk') hj0 hj0']
    simp only [mul_inv, inv_inv]
    ac_rfl
  obtain ⟨s, hs⟩ := sec_down (L := L') (F := 𝟙 X') (L' := L.pull F) (w := w') hPG hL' (pull_isLB hL F)
    (fun j => (Scheme.Hom.appLE (𝟙 X') (L'.U j) ((𝟙 X') ⁻¹ᵁ L'.U j) le_rfl).hom (σ.f j)) (by
      intro y j j' hj hj'
      rw [gs_appLE (𝟙 X') (L'.U j) ((𝟙 X') ⁻¹ᵁ L'.U j) le_rfl (𝟙 X') y hj,
        gs_appLE (𝟙 X') (L'.U j') ((𝟙 X') ⁻¹ᵁ L'.U j') le_rfl (𝟙 X') y hj', Category.comp_id]
      exact gs_compat σ (𝟙 X') y hj hj')
  refine ⟨s, fun Z r z J k hJ hk => ?_⟩
  have hk1 : (𝟙 X') (r z) ∈ L'.U k := by simpa using hk
  have e := hs Z r z k J hk1 hJ
  rw [gs_appLE (𝟙 X') (L'.U k) ((𝟙 X') ⁻¹ᵁ L'.U k) le_rfl r z hk, Category.comp_id, hw' Z r z k J hk hJ] at e
  rw [e, ← _root_.mul_assoc, ← Units.val_mul, _root_.mul_inv_cancel, Units.val_one, _root_.one_mul]

end Calc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)


set_option maxHeartbeats 400000 in
theorem thetaFrame_of (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) : ThetaFrameSt Xo c := by
  intro T io O _ β Y hPI yt z hz hzs G m t' m1 m2
  obtain ⟨θ, hθ, -, w2, σ', ⟨g2, r2⟩, hcl, hgen⟩ := thetaCore_of hT E H Dw l Xo c O β Y hPI T.V yt z hz G m t' m2
  generalize (z ≫ pullback.fst _ _ : Sp T.Fr ⟶ Xo.X) = x at m1 ⊢
  intro s₀ hs₀
  obtain ⟨w1, g1, r1, -⟩ := m1.lin
  have hw1 := (isGen_iff w1).1 g1
  have hL := Xo.univ.t.PP.isLB
  have hL' := t'.PP.isLB
  obtain ⟨s1, hs1⟩ := thf_secUp hw1 hL hL' σ'
  let A := Xo.univ.t.G
  have cond : (snd (Over.mk x) A).left ≫ A.hom = (fst (Over.mk x) A).left ≫ x :=
    (Over.w (snd (Over.mk x) A)).trans (Over.w (fst (Over.mk x) A)).symm
  let h : Gx x ⟶ t'.G.left := m1.cart.1.lift _ _ cond
  have hφ : h ≫ m1.φ = (snd (Over.mk x) A).left := m1.cart.1.lift_fst _ _ cond
  have hh : h ≫ t'.G.hom = (fst (Over.mk x) A).left := m1.cart.1.lift_snd _ _ cond
  let a0 : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk t'.G.hom rfl
  let b0 : Over.mk (t'.G.hom ≫ x) ⟶ A := Over.homMk m1.φ m1.cart.1.w
  let g0 : t'.G.left ⟶ Gx x := (lift a0 b0).left
  have g0f : g0 ≫ (fst (Over.mk x) A).left = t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
  have g0s : g0 ≫ (snd (Over.mk x) A).left = m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
  have uniq : ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) A).left = m1.φ → g ≫ (fst (Over.mk x) A).left = t'.G.hom →
      g ≫ h = 𝟙 _ := fun g e₁ e₂ => m1.cart.1.hom_ext (by rw [Category.assoc, hφ, e₁, Category.id_comp])
        (by rw [Category.assoc, hh, e₂, Category.id_comp])
  have hg0 : g0 ≫ h = 𝟙 _ := uniq g0 g0s g0f
  have h0g : h ≫ g0 = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      show h ≫ g0 ≫ (fst (Over.mk x) A).left = 𝟙 _ ≫ (fst (Over.mk x) A).left
      rw [g0f, hh, Category.id_comp]
    · rw [Category.assoc]
      show h ≫ g0 ≫ (snd (Over.mk x) A).left = 𝟙 _ ≫ (snd (Over.mk x) A).left
      rw [g0s, hφ, Category.id_comp]
  let s : LB.Sec (PPx x) := thfPull1 Xo.univ.t.PP.L h hφ s1
  have hsf : ∀ j : Fin 1 → Xo.univ.t.PP.L.ι, s.f j = (h.appLE _ _ (chart_le_pullback_open _ h hφ j)).hom (s1.f (fun _ => j 0)) :=
    fun j => rfl
  let θ2 := thfPull G.PP.L m2.φ θ
  have hI2 : IsoMaps w2 σ' θ2 := fun (i : PUnit → G.PP.L.ι) k => fn_ext fun y hy => by
    have h₁ : (G.PP.L.pull m2.φ).U i ⊓ t'.PP.L.U k ≤ m2.φ ⁻¹ᵁ G.PP.L.U (i PUnit.unit) :=
      inf_le_left.trans (LB.wchart_le G.PP.L _ i PUnit.unit)
    have h₂ : (G.PP.L.pull m2.φ).U i ⊓ t'.PP.L.U k ≤ (G.PP.L.pull m2.φ).U (fun _ => i PUnit.unit) ⊓ t'.PP.L.U k :=
      le_rfl
    have e := congrArg (gs (𝟙 _) y _) (hcl (i PUnit.unit) k _ h₁ h₂)
    refine (gs_res _ y _ hy _).trans ((gs_appLE m2.φ _ _ _ (𝟙 _) y hy.1 _).trans
      (((gs_appLE m2.φ _ _ h₁ (𝟙 _) y hy _).symm.trans e).trans ((gs_mul _ y _ hy _ _).trans ?_)))
    refine Eq.symm ((gs_mul _ y _ hy _ _).trans ?_)
    exact congrArg₂ (· * ·) (gs_res _ y h₂ hy _).symm ((gs_res _ y _ hy _).trans (gs_res _ y _ hy _).symm)
  have hI1 : IsoMaps w1 σ' s1 := fun (i : PUnit → Xo.univ.t.PP.L.ι) k => fn_ext fun y hy => by
    exact (gs_res _ y _ hy _).trans ((hs1 _ (𝟙 _) y i k hy.1 hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _)))))
  have hgc : ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) A).left = m1.φ → g ≫ (fst (Over.mk x) A).left = t'.G.hom →
      ∀ (j : PUnit → Xo.univ.t.PP.L.ι) (hj : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
        s1.f j = (g.appLE _ _ hj).hom (s.f (fun _ => j PUnit.unit)) := fun g e₁ e₂ j hj => fn_ext fun y hy =>
    Eq.symm ((gs_appLE g _ _ hj (𝟙 _) y hy _).trans
      ((gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _ ≫ g) y (hj hy) _).trans
        (congrArg (fun q => gs q y _ (s1.f j)) (by rw [Category.id_comp, uniq g e₁ e₂]))))
  have hgenS : ∀ s'' : LB.Sec (PPx x), ∃! a : T.Fr, ∀ i, s''.f i = scal x a i * s.f i := by
    intro s''
    have le : ∀ j, m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j ≤ g0 ⁻¹ᵁ (PPx x).U (fun _ => j) := fun j y hy =>
      Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) g0s).mpr hy
    let σ : ∀ j, Γ(t'.G.left, m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j) := fun j => (g0.appLE _ _ (le j)).hom (s''.f (fun _ => j))
    have gP : ∀ (Z : Scheme.{0}) (r : Z ⟶ t'.G.left) (z : Z) j, m1.φ (r z) ∈ Xo.univ.t.PP.L.U j →
        gs r z _ (σ j) = gs (r ≫ g0) z _ (s''.f (fun _ => j)) := fun Z r z j hz => gs_appLE g0 _ _ (le j) r z hz _
    obtain ⟨τ, hτ⟩ := sec_down hw1 hL hL' σ fun y j j' h₁ h₂ => by
      have m : (𝟙 _ ≫ g0) y ∈ (PPx x).U (fun _ => j) := le j h₁
      have m' : (𝟙 _ ≫ g0) y ∈ (PPx x).U (fun _ => j') := le j' h₂
      have gg : gm (𝟙 _ ≫ g0) y _ ((PPx x).g (fun _ => j) (fun _ => j')) =
          gm m1.φ y (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j') :=
        (gm_linComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (snd (Over.mk x) A).left) (fun _ => 1) (𝟙 _ ≫ g0) y _ _ m m').trans
          (by rw [Fin.prod_univ_one, zpow_one, Category.assoc, g0s, Category.id_comp])
      exact (gP _ (𝟙 _) y j h₁).trans ((gs_compat s'' (𝟙 _ ≫ g0) y m m').trans
        (congrArg₂ (· * ·) (congrArg Units.val gg) (gP _ (𝟙 _) y j' h₂).symm))
    obtain ⟨a, ha, hu⟩ := hgen τ
    refine ⟨a, fun (i : Fin 1 → Xo.univ.t.PP.L.ι) => ?_, fun a' ha' => hu a' ?_⟩
    · obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun k => congrArg i (Subsingleton.elim k 0)⟩
      refine fn_ext fun y hy => ?_
      have mφ : m1.φ ((𝟙 _ ≫ h) y) ∈ Xo.univ.t.PP.L.U j :=
        (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j)
          (by rw [Category.id_comp, hφ] : (𝟙 _ ≫ h) ≫ m1.φ = (snd (Over.mk x) A).left)).mpr (Set.mem_iInter.1 hy 0)
      obtain ⟨k, hk⟩ := exists_chart hL' ((𝟙 _ ≫ h) y)
      have e1 : gs (𝟙 _) y _ (s''.f (fun _ => j)) =
          (gw w1 (𝟙 _ ≫ h) y j k).val * (cst ((𝟙 _ ≫ h) ≫ t'.G.hom) y a * gs (𝟙 _ ≫ h) y _ (σ'.f k)) := by
        have c1 : (𝟙 _ ≫ h) ≫ g0 = 𝟙 _ := by rw [Category.id_comp, h0g]
        refine (congrArg (fun q => gs q y _ (s''.f (fun _ => j))) c1).symm.trans ?_
        refine (gP _ (𝟙 _ ≫ h) y j mφ).symm.trans ((hτ _ (𝟙 _ ≫ h) y j k mφ hk).trans (congrArg _ ?_))
        rw [ha k, gs_mul _ y _ hk, gs_constFn _ _ _ y hk]
      have e2 : gs (𝟙 _) y _ (s.f (fun _ => j)) = (gw w1 (𝟙 _ ≫ h) y j k).val * gs (𝟙 _ ≫ h) y _ (σ'.f k) :=
        (gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _) y hy _).trans
          (hs1 _ (𝟙 _ ≫ h) y (fun _ => j) k (chart_le_pullback_open _ h hφ _ hy) hk)
      have e3 : gs (𝟙 _) y _ (scal x a (fun _ => j)) = cst ((𝟙 _ ≫ h) ≫ t'.G.hom) y a := by
        rw [show (𝟙 _ ≫ h) ≫ t'.G.hom = 𝟙 _ ≫ (fst (Over.mk x) A).left by rw [Category.assoc, hh]]
        exact gs_constFn (fst (Over.mk x) A).left _ (𝟙 _) y hy a
      exact e1.trans ((mul_left_comm _ _ _).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) e3 e2))))
    · intro k
      refine fn_ext fun y hy => ?_
      obtain ⟨j, hj⟩ := exists_chart hL (m1.φ y)
      have c2 : (𝟙 _ ≫ g0) ≫ h = 𝟙 _ := by rw [Category.id_comp, hg0]
      have mg : (𝟙 _ ≫ g0) y ∈ (PPx x).U (fun _ => j) := le j hj
      have e1 := hτ _ (𝟙 _) y j k hj hy
      have e2 : gs (𝟙 _) y _ (σ j) =
          cst (𝟙 _ ≫ t'.G.hom) y a' * ((gw w1 (𝟙 _) y j k).val * gs (𝟙 _) y _ (σ'.f k)) := by
        refine (gP _ (𝟙 _) y j hj).trans ?_
        rw [ha' (fun _ => j), gs_mul _ y _ mg]
        refine congrArg₂ (· * ·) ?_ ?_
        · exact (gs_constFn (fst (Over.mk x) A).left _ _ y mg a').trans (by rw [Category.assoc, g0f])
        · refine (gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _ ≫ g0) y mg _).trans ?_
          rw [c2]
          exact hs1 _ (𝟙 _) y (fun _ => j) k (mem_pull.2 hj) hy
      rw [gs_mul _ y _ hy, gs_constFn _ _ _ y hy]
      rw [e1, mul_left_comm] at e2
      exact (Units.mul_right_inj _).1 e2
  obtain ⟨a, ha, -⟩ := hs₀ s
  have a0 : a ≠ 0 := by
    rintro rfl
    have z0 : ∀ i, s.f i = 0 := fun i => by
      rw [ha i]
      simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, toΓ, map_zero, zero_mul]
    obtain ⟨b, -, hb⟩ := hgenS s
    exact zero_ne_one ((hb 0 fun i => by rw [z0 i, mul_zero]).trans (hb 1 fun i => by rw [z0 i, mul_zero]).symm)
  exact ⟨θ, s, hθ, ⟨w1, w2, σ', s1, θ2, ⟨g1, r1⟩, ⟨g2, r2⟩, hI1, hI2, fun j hj => rfl, hgc⟩, hgenS,
    Units.mk0 a a0, ha⟩

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}


open Classical in
theorem rdU_mul {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (f g : Rul Xo c) : rdU U (f * g) = rdU U f * rdU U g := by
  funext k x
  show (if h : x ∈ (U.X k).dom then toC (evR Xo c (f * g) (U.un k ⟨x, h⟩)) else 0) =
    (if h : x ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0) *
      (if h : x ∈ (U.X k).dom then toC (evR Xo c g (U.un k ⟨x, h⟩)) else 0)
  split_ifs with h
  · exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (U.un k ⟨x, h⟩)
  · simp

theorem laU_add {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (hn : Even n)
    (hn' : Even n') (k : U.Comp) : laU U (a + a') (n + n') k = laU U a n k + laU U a' n' k := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨m', rfl⟩ := hn'
  have h1 : (m + m) / 2 = m := by omega
  have h2 : (m' + m') / 2 = m' := by omega
  have h3 : (m + m + (m' + m')) / 2 = m + m' := by omega
  funext τ j
  simp only [laU, Pi.add_apply, h1, h2, h3]
  split_ifs <;> push_cast <;> ring

theorem holSub_mul (hM : SiegelSpaceAlgebra (E := E)) {Comp : Type} {X : Comp → Data E r} {la la' : ∀ k, Wt (X k).Ψ r}
    {P Q : FDSec X} (hP : P ∈ holSub X la) (hQ : Q ∈ holSub X la') : P * Q ∈ holSub X (la + la') := by
  first | exact UpperTheory.Reformulated.B.Qe28.holSub_mul .. | (apply UpperTheory.Reformulated.B.Qe28.holSub_mul <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe28.holSub_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe28.holSub_mul <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe28.holSub_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe28.holSub_mul <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' P Q hP hQ | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' P Q hP | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' P Q | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' P | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E

theorem cusp_mul_of_M5 (hM : SiegelSpaceAlgebra (E := E)) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : CuspMul Xo c U := by
  intro a a' n n' f g hd hd' hf hg
  rw [mem_cusp] at hf hg ⊢
  refine ⟨mulC_mem_sec Xo c a a' n n' hf.1 hg.1, fun σ hσ => ?_⟩
  have hla : laU (U σ) (a + a') (n + n') = laU (U σ) a n + laU (U σ) a' n' :=
    funext fun k => laU_add (U σ) a a' n n' hd.2 hd'.2 k
  show rdU (U σ) (f * g) ∈ holSub (U σ).X (laU (U σ) (a + a') (n + n'))
  rw [rdU_mul, hla]
  exact holSub_mul hM (hf.2 σ hσ) (hg.2 σ hσ)

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def lamOf (la : HeightOneSpectrum (𝓞 c.F)) : PointsOfFlagModel.abelian₂ (Formalism.MainNotions.WeightAlgebra.resCh la) c :=
  ⟨la, by
    have h : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : 𝓞 c.F ⧸ la.asIdeal) = 0 := by
      unfold Formalism.MainNotions.WeightAlgebra.resCh
      exact CharP.cast_eq_zero _ _
    exact (Ideal.Quotient.eq_zero_iff_mem).1 (by simpa using h)⟩

def LiesOverBaseChange (la : HeightOneSpectrum (𝓞 c.F)) (Tw : PointsOfFlagModel.Tower (Formalism.MainNotions.WeightAlgebra.resCh la) Xo c) (T : CDVR)
    (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (η : PointsOfFlagModel.Pt Tw .yy) : Prop :=
  letI := io.toAlgebra
  η.1 = lamOf la ∧ ∃ eF : T.Fr →+* ↥η.2.1.S,
    eF.comp io = η.2.2.1.fK ∧
    (∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1) ∧
    (∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1) ∧
    η.2.2.1.y ≫ pullback.fst _ _ = spMap eF ≫ y.1.x ∧
    ∀ τ i, ∃ u' : Sp (DualNumber ↥η.2.1.S) ⟶ (Tw.Y η.1).oF.t.G.left,
      u' ≫ (Tw.Y η.1).m.φ = (η.2.2.2.u τ i).left ∧
      u' ≫ (Tw.Y η.1).m0.toSABMap.φ = spMap (dualMap eF) ≫ y.1.u τ i

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CuspFDOf
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def RdIndep (σ : c.F →+* ℂ) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (k : ℕ), Dom a k → ∀ (n : ℕ) (b : Fin n → Rul Xo c), (∀ i, b i ∈ sec Xo c a k) →
    LinearIndependent c.F b → LinearIndependent ℂ (fun i => rdU (U σ) (b i))

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.HeckeJ
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

namespace HeckeJ

open scoped TensorProduct

section Gen

variable {L : Type*} [Field L] (σ₀ : L →+* ℂ) {WL : Type*} [AddCommGroup WL] [Module L WL]
  {H F : Type*} [AddCommGroup H] [Module ℂ H] [AddCommGroup F] [Module ℂ F]
  (j : WL →ₛₗ[σ₀] H) (em : H →ₗ[ℂ] F) (TF : F →ₗ[ℂ] F) (c : ℂ)

def IsHkJ (T : WL →ₗ[L] WL) : Prop := ∀ x, em (j (T x)) = c • TF (em (j x))


variable {σ₀ j em TF c}

variable (σ₀ j em TF c)

variable {σ₀ j em TF c}

end Gen

section Inj

variable {K L : Type} [Field K] [Field L] [Algebra K L] {M : Type} [AddCommGroup M] [Module K M]
  {W : Type} [AddCommGroup W] [Module ℂ W]

end Inj

end HeckeJ

end Formalism.L2.Pj
end
end
