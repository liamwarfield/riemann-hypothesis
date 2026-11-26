module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitOfGPl
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SingleDatum

variable {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H}

def IsHalfIdem (l : Geo.Tor.Level H) (e : AE D) : Prop :=
  ∃ P : Finset (Formalism.L2.DIV.Pl D.host.E), IsIdemSum e P ∧ ∀ PP, PP ∈ P ↔ l.Mb ≤ PP.asIdeal

def levPoint (V W : HSp D) (l : Geo.Tor.Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (e : AE D)
    (q : Fin V.rank → LevQ Dw l) : WO V W :=
  Matrix.of fun a b => e * incA D (ι (cSep l • levRep (q b)) a / (l.M : D.host.E))

def transSum (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (l : Geo.Tor.Level H)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (e : AE D) (f₀ : WO V W → ℂ) (w : (Fin V.rank → LevQ Dw l) → ℂ) :
    WO V W → ℂ :=
  ((Nat.card (Fin V.rank → LevQ Dw l) : ℂ))⁻¹ • ∑ᶠ q : Fin V.rank → LevQ Dw l, w q • heisO ψ V W (levPoint V W l ι e q) f₀

def VacPair (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ) : Prop :=
  IsPair ψ θ V W χV χW om ∧ V.rank ≠ 0 ∧ (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V ∧
    (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W ∧ IsSelfDualC V ΛV ∧ IsSelfDualC W ΛW ∧
    (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) ∧
    (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) ∧
    IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f₀

def clsScal (χ : (AE D)ˣ →* Circle) (y : (AE D)ˣ) {n : ℕ} (Λ : GenLat D.host.E n) (r : ℕ) : ℂ :=
  ((χ y : Circle) : ℂ)⁻¹ * ((Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E n).toAddSubgroup.addSubgroupOf
    Λ.La.toAddSubgroup).index : ℝ) ^ r) : ℝ) : ℂ)⁻¹


variable (Dw) in
def IsLetters {m n : ℕ} (lt : LtN Dw n ≃ FVar D m n) : Prop :=
  ∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨
    (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = Dw.p + ℓ.2.1))



variable (Dw) in
def degA (a : (D.host.E →+* ℂ) × ℕ → ℕ) : ℕ := ∑ τ : D.host.E →+* ℂ, ∑ j : Fin (Dw.mult τ), a (τ, j)

variable {l : Geo.Tor.Level H} {Xo : Moduli Dw l}

def IsDict {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (W : HSp D) (hr : W.rank = r)
    (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  IsUnf U ∧ GlobalTheory.Member.IotaOK Dw W ι ∧ (∀ k, IsMod W hr (U.X k)) ∧ (∀ k, IsOrthogonalFrame (U.X k) x₀) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
      (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
      (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictLat U W hr dict ι e F ik φ th x₀

def FrameTie {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (W : HSp D) (hr : W.rank = r)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (s BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) : Prop :=
  ∀ k, IsInvOf W hr (U.X k) (fun τ => x₀ τ.1) s ∧
    ∀ hq : (U.X k).p0 + Dw.p = r, IsBasOf W hr (U.X k) hq (fun τ => x₀ τ.1) BW

def MarkedVal {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (θ : InfFam D) (W : HSp D) {r : ℕ} (hr : W.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (f : Rul d.Xo₂ d.c₂) (ν : GA D W → ℂ) : Prop :=
  ∀ (X : Data D.host.E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (k : GA D W) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), IsMod W hr X → X.p0 = Dw.q → IsSympl X bas →
    IdxIs c (inC c) X idx e → latR hr (latG W k) = X.Λ → IsMark d.l₂ X.Λ mk → MarkAd d.l₂ W hr ι k mk →
    letI : Algebra d.c₂.F ℂ := ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
    ∀ (y₂ : FrPt d.Xo₂ d.c₂ ℂ) (A₂ : AnFib X bas idx e (frMove θ W hr X k (fun τ => x₀ τ.1)) X.Λ y₂), A₂.Marked mk →
      evR d.Xo₂ d.c₂ f y₂ = ν k

def IsThetaSum {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) {T : Type} [Fintype T] (cs : T → Rul d.Xo₂ d.c₂)
    (w : T → (Fin n → LevQ Dw d.l₂) → c.F) (La : GenLat D.host.E n) (N : ℕ) (P : T → MvPolynomial (LtN Dw n) c.F)
    (f : Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ x : c.F, algebraMap d.c₂.F k (d.eF x) = algebraMap c.F k x) →
    ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → ∃ v : T → k,
      (∀ t, thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w t q)) La N
        (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (P t)) y₂ (v t)) ∧
      evR Xo c f y = ∑ t, evR d.Xo₂ d.c₂ (cs t) y₂ * v t


end GlobalTheory.SingleDatum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteral
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeterminantRecCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeterminantRecCompatible
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem LawsLit.nu_eq_lpTw (H : LawsLit a ha e rc) (x : IrrGL (k := w.adicCompletion E)) (s : ℝ) :
    rc (x.nu s) = (rc x).lpTw s := by
  rw [IrrGL.nu, H.twist, H.one, lpChar_lpOfChar, WD.lpTw]
  congr 1
  exact ha.absPow_comp s

end GlobalTheory.LocLanglands

namespace GlobalTheory

theorem lawsLit_det : StandardCosocleGL → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (t : ℕ) χ hχ, rc (cls (IrrRep.det (Fin t) χ hχ)) = sumList ((List.range t).map fun j : ℕ => (rc (.ofChar χ hχ)).lpTw (((t : ℝ) - 1) / 2 - j)) := by
  intro hSC E Ω _ _ _ _ _ A w h a ha e rc H t χ hχ
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  have hL := GlobalTheory.T.isLanglandsClassification_detCharacter hSC (w.adicCompletion E) t χ hχ
  obtain ⟨φ⟩ := (IrrRep.det (Fin t) χ hχ).nonempty_equiv_rep
  have hL' := hL.of_equiv φ.symm
  rw [H.langlands _ (cls (IrrRep.det (Fin t) χ hχ)) hL', segSum, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply]
  show ((rc ((IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ))).lpTw ((((1 : ℕ) : ℝ) - 1) / 2)).lpChar
      (WD.lpSp (h := h) 1) = _
  have h0 : ((((1 : ℕ) : ℝ) - 1) / 2) = 0 := by norm_num
  rw [h0, (GlobalTheory.T.weilDeligne_charpoly_twist_special E Ω A w h _).1, H.nu_eq_lpTw]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeterminantRecCompatibleStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_rec_compatible : StandardCosocleGL → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (t : ℕ) χ hχ, rc (cls (IrrRep.det (Fin t) χ hχ)) = sumList ((List.range t).map fun j : ℕ => (rc (.ofChar χ hχ)).lpTw (((t : ℝ) - 1) / 2 - j)) := by
  first | exact @GlobalTheory.lawsLit_det | exact GlobalTheory.lawsLit_det | (intros; apply GlobalTheory.lawsLit_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteral
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem isRec_of_isRecLit : DepthZeroCuspidalLL → DepthZeroInduction → LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecLit h rc → IsRec h rc := by
  intro hDZ hDI hEx hLM hSC hZP hGL hBZ E Ω _ _ _ _ _ A w h rc H
  obtain ⟨a, ha, ε, hε, L⟩ := H
  refine ⟨a, ha, ε, hε, ?_⟩
  exact
    { bij := L.bij, dim := L.dim, one := L.one, eps := L.eps, cusp := L.cusp, langlands := L.langlands,
      twist := L.twist, central := L.central, dual := L.dual,
      det := GlobalTheory.T.determinant_rec_compatible hSC E Ω A w h a ha _ rc L
      prod := GlobalTheory.T.twist_rec_compatible hEx hLM hSC E Ω A w h a ha _ rc L
      supp := GlobalTheory.T.central_character_rec_compatible hEx hZP hGL hBZ E Ω A w h a ha _ rc L
      sph := GlobalTheory.T.l_factor_rec_compatible hEx hLM hSC hZP hGL hBZ E Ω A w h a ha _ rc L
      sat := GlobalTheory.T.epsilon_factor_rec_compatible hEx hLM hSC hZP hGL hBZ E Ω A w h a ha _ rc L
      depth := GlobalTheory.T.conductor_rec_compatible hDZ hDI hEx hZP hGL hBZ E Ω A w h rc ⟨a, ha, ε, hε, L⟩ }

end GlobalTheory.LocLanglands
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteralStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rec_of_rec_literal : DepthZeroCuspidalLL → DepthZeroInduction → LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecLit h rc → IsRec h rc := by
  first | exact @GlobalTheory.LocLanglands.isRec_of_isRecLit | exact GlobalTheory.LocLanglands.isRec_of_isRecLit | (intros; apply GlobalTheory.LocLanglands.isRec_of_isRecLit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open GlobalTheory.VacuumCharacter
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealFockAction

variable {D : D7}

theorem eq_one_of_isOpen_ker {θ : InfFam D} (hθ : IsInfFam θ) {χ : (AE D)ˣ →* Circle}
    (hχ : IsOpen (χ.ker : Set (AE D)ˣ)) (x : (AE D)ˣ) (hx : finPart D (x : AE D) = 1) : χ x = 1 := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  let a : (D.what₂.Tau → ℂ) → AE D := fun z => 1 + σ fun τ => Complex.exp (z τ) - 1
  have a1 : ∀ z, finPart D (a z) = 1 := fun z => by
    simp only [a]; rw [RingHom.map_add (f := _), hσ.fin, RingHom.map_one, add_zero]
  have a2 : ∀ z τ, θ τ (infPart D (a z)) = Complex.exp (z τ) := fun z τ => by
    simp only [a]; rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hσ.comp, RingHom.map_one, RingHom.map_one]; ring
  have a3 : ∀ z, a z * a (-z) = 1 := fun z => adele_ext hθ
    (by rw [RingHom.map_mul, a1, a1, RingHom.map_one, one_mul]) fun τ => by
      rw [RingHom.map_mul, RingHom.map_mul, a2, a2, RingHom.map_one, RingHom.map_one, ← Complex.exp_add]
      simp
  have ac : Continuous a := continuous_const.add (hσ.cont.comp (by fun_prop))
  let e : (D.what₂.Tau → ℂ) → (AE D)ˣ := fun z => ⟨a z, a (-z), a3 z, (mul_comm _ _).trans (a3 z)⟩
  have ec : Continuous e := Units.continuous_iff.2 ⟨ac, ac.comp continuous_neg⟩
  have hcl : IsClopen (e ⁻¹' (χ.ker : Set (AE D)ˣ)) :=
    IsClopen.preimage ⟨Subgroup.isClosed_of_isOpen _ hχ, hχ⟩ ec
  have e0 : e 0 = 1 := Units.ext (adele_ext hθ ((a1 0).trans (RingHom.map_one _).symm) fun τ => by
    refine (a2 0 τ).trans ?_
    rw [Units.val_one, RingHom.map_one, RingHom.map_one]
    simp)
  have hall := hcl.eq_univ ⟨0, by rw [Set.mem_preimage, e0]; exact one_mem χ.ker⟩
  have ex : e (fun τ => Complex.log (θ τ (infPart D (x : AE D)))) = x :=
    Units.ext (adele_ext hθ ((a1 _).trans hx.symm) fun τ => (a2 _ τ).trans
      (Complex.exp_log ((x.isUnit.map (infPart D)).map (θ τ)).ne_zero))
  rw [← ex]
  exact MonoidHom.mem_ker.1 (hall ▸ Set.mem_univ _ : _ ∈ e ⁻¹' (χ.ker : Set (AE D)ˣ))

theorem hasInfExp_mul_of_isOpen_ker {χ ν : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (hχ : HasInfExp D χ τ a)
    (hν : IsOpen (ν.ker : Set (AE D)ˣ)) : HasInfExp D (χ * ν) τ a := by
  obtain ⟨n, hn, h1, h2⟩ := hχ
  refine ⟨n, hn, h1, fun θ hθ x hx hτ => ?_⟩
  rw [MonoidHom.mul_apply, eq_one_of_isOpen_ker hθ hν x hx, mul_one, h2 θ hθ x hx hτ]

theorem onb_laws {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) (hp : p ≤ k) :
    (s * B = B * diagonal fun a : Fin k => if decide (a.val < p) then (1 : ℂ) else -1) ∧
      s.trace = 2 * p - k := by
  obtain ⟨ε, hε, h1, h2⟩ := h
  have e : (fun a => (ε a : ℂ)) = fun a : Fin k => if decide (a.val < p) then (1 : ℂ) else -1 := funext fun a => by
    rcases hε a with h | h
    · simp [h.1, h.2]
    · simp [h.1, not_lt.2 h.2]
  have hd : B.det ≠ 0 := fun h0 => by
    have h3 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at h3
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h3.symm
    rcases hε a with h | h <;> simp [h.1] at ha
  rw [e] at h2
  refine ⟨h2, ?_⟩
  have h4 : s = B * (diagonal fun a : Fin k => if decide (a.val < p) then (1 : ℂ) else -1) * B⁻¹ := by
    rw [← h2, Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.2 hd)]
  rw [h4, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hd), Matrix.one_mul,
    Matrix.trace_diagonal]
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [Fin.sum_univ_add]
  simp
  ring

theorem onb_posDef {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : Bᴴ * G * B = 1 := by
  obtain ⟨ε, hε, h1, -⟩ := h
  rw [h1, ← Matrix.diagonal_one]
  congr 1
  funext a
  rcases hε a with h | h
  · simp [h.1]
  · exact absurd a.2 (not_lt.2 h.2)

theorem conj_unitary {n : ℕ} {G B g : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) (hg : gᴴ * G * g = G) :
    B⁻¹ * g * B ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hB : B * (Bᴴ * G) = 1 := mul_eq_one_comm.1 h
  have hi : B⁻¹ = Bᴴ * G := Matrix.inv_eq_right_inv hB
  have h0 : B * B⁻¹ = 1 := by rw [hi, hB]
  have h1 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h0, Matrix.conjTranspose_one]
  have hG : (B⁻¹)ᴴ * B⁻¹ = G := by
    calc _ = (B⁻¹)ᴴ * (Bᴴ * G) := by rw [← hi]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc _ = Bᴴ * (gᴴ * ((B⁻¹)ᴴ * B⁻¹) * g) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hG, hg, h]

variable {S T : HSp D}

theorem pureTensorO_subst {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {p : D.what₂.Tau → ℕ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) 1) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (ht : ∀ τ, sT τ * BT τ = BT τ * diagonal fun a : Fin T.rank => if decide (a.val < p τ) then (1 : ℂ) else -1)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (u : GLR D S.rank)
    (hu : ∀ τ, (u τ).val ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (P : PolF D T.rank S.rank) :
    pureTensorO ψ θ S T (fun _ => 1) sT (fun τ => BS τ * (u τ).val) BT f P =
      pureTensorO ψ θ S T (fun _ => 1) sT BS BT f (fockSubst p u P) := by
  classical
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ B B' v g, IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (sT τ)) B B' v g) :=
    fun _ _ _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ B B' v Q,
      pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (sT τ)) B B') f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (sT τ)) B B' v
        (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (sT τ)) B B') f Q) := fun B B' v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) hadd hsm (hth B B') ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hA : ∀ v g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (sT τ)) (fun τ => BS τ * (u τ).val) BT v g =
      ∑ a, ∑ b, (if decide (v.2.1.val < p v.1) = true then
          (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) a v.2.1 * (u v.1).val⁻¹ v.2.2 b
        else (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)⁻¹ v.2.1 a * (u v.1).val b v.2.2) •
        aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (sT τ)) BS BT (v.1, a, b) g := fun v g hg => by
    unfold aPlusAll
    have := GlobalTheory.FockBasis.aPlus_unitMap_mul hψ hθ v.1 _ hg (ht v.1) (k := 1)
      ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩ (BS v.1) (hu v.1) v.2.1 v.2.2
    rw [Matrix.mul_one] at this
    exact this
  have key := GlobalTheory.FockBasis.pure_subst (P := IsThetaFunO ψ S T) _ _
    (GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ S T) hadd hsm (hth _ _) hf) (hX _ _) (hX _ _) hA P
  unfold pureTensorO
  rw [key]
  congr 2
  unfold fockSubst
  congr 1
  funext ⟨τ, i, j⟩
  rw [Finset.sum_eq_single i]
  · by_cases h : i.val < p τ <;> simp [h]
  · intro a _ ha
    simp [Matrix.one_apply_ne ha, Matrix.one_apply_ne ha.symm]
  · simp

theorem om_vac {B : Base S T} {ψ : Twist D Circle} {ω : PairRep S T} (hB : B.Good) (hψ : ψ.Good)
    (hω : B.IsWeil ψ.chi ω) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO B.F.ψ S T) B.F.θ τ (cplxO 1 (B.F.sT τ)) f) {u : GA D S} (hu : u ∈ GinfC S) :
    ω (u, 1) f = (((detFam B.w.c (realGL B.F.θ S u))⁻¹ : ℂˣ) : ℂ) • f := by
  have hθ := hB.frame.vac.2.inf
  have hS := fun τ => GlobalTheory.FockBasis.isCartanInv_one (onb_posDef (hB.frame.onbS τ))
  have hT := hB.frame.cartT
  have one : ∀ τ, compAt B.F.θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have hpq : ∀ τ, B.w.p τ + B.w.q τ = T.rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    simpa using (Fintype.card_congr e).symm
  obtain ⟨x, hx, hxv⟩ := exists_root hθ S (fun τ => by
    have := (hS τ).2.2.det_pos.ne'
    rwa [Matrix.mul_one] at this) u hu
  have hy : IsDetRoot T 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  choose p hp hd using fun τ => detPlus_one (n := S.rank) (B.F.sT τ) (hT τ).1
  have ep : ∀ τ, p τ = B.w.p τ := fun τ => by
    have h1 := hB.frame.onbT τ
    rw [← hB.sig τ] at h1
    have h2 := (onb_laws h1 (hpq τ ▸ Nat.le_add_right _ _)).2
    rw [hp] at h2
    have h3 : (p τ : ℂ) = B.w.p τ := by linear_combination h2 / 2
    exact_mod_cast h3
  rw [GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D B.F.ψ hω.std S T B.F.θ hθ _ _ ω B.eta hB.eta hω (fun _ => 1) B.F.sT hS hT u hu 1 (one_mem _)
    (fun τ => by rw [one_mul, mul_one]) (fun τ => by rw [one, one_mul, mul_one]) x 1 hx hy f hf hv]
  congr 1
  have hexp : ∀ τ, HasInfExp D (B.mu * ψ.chi * B.eta⁻¹ * (B.eta ^ T.rank)⁻¹) τ ((B.w.c τ - p τ : ℤ) : ℚ) := fun τ => by
    have h1 := hasInfExp_twist (hasInfExp_twist (hasInfExp_mul_of_isOpen_ker
      (hasInfExp_mul_of_isOpen_ker (hB.inf τ) hB.de.isOpen) hψ.isOpen) (hB.eta.2.2.2 τ) 1) (hB.eta.2.2.2 τ) T.rank
    rw [pow_one] at h1
    convert h1 using 1
    · rfl
    rw [← hpq τ, ep]
    push_cast
    ring
  rw [MonoidHom.map_one, mul_one, Circle.coe_inv, hxv _ _ hexp, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    Units.val_inv_eq_inv_val]
  simp only [detFam, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    GeneralLinearGroup.val_det_apply]
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have inv := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := B.F.θ) τ u)
  rw [Matrix.det_mul, Matrix.det_one] at inv
  have g0 := left_ne_zero_of_mul_eq_one inv
  rw [one, (hd τ _ 1 (by rw [one_mul, mul_one])).1, eq_inv_of_mul_eq_one_right inv, mul_one, ← smul_add,
    add_add_sub_cancel, ← two_smul ℂ, smul_smul, show (1 / 2 * 2 : ℂ) = 1 by norm_num, one_smul, Matrix.det_one, one_pow,
    one_mul, show (realGL B.F.θ S u τ).val = compAt B.F.θ τ (Formalism.L2.Theta.mt S u) from rfl, zpow_sub₀ g0, zpow_natCast,
    inv_pow]
  have := pow_ne_zero (p τ) g0
  have := zpow_ne_zero (B.w.c τ) g0
  field_simp

theorem om_fock_vecAt : ∀ (D : D7) (S T : HSp D) (B : Base S T) (ψ : Twist D Circle) (ω : PairRep S T) (Q : Finset (Pl D.host.E)) (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ), B.Good → ψ.Good → B.admitted Q → B.IsWeil ψ.chi ω → ∀ u ∈ GinfC S, ∀ P, ω (u, 1) (B.F.fock (B.vecAt Q φ) P) = B.F.fock (B.vecAt Q φ) (B.act u P) := by
  intro D S T B ψ ω Q φ hB hψ hQ hω u hu P
  have hθ := hB.frame.vac.2.inf
  have hBS := fun τ => onb_posDef (hB.frame.onbS τ)
  have hth := Base.isThetaAt_vecAt hB hQ φ
  have hf := GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hθ hth hB.frame.vac.2.theta
  have ho := hQ.1.isOrthSum.1
  have hv := fun τ => GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hB.frame.vac.1.1.1 hθ ho.infPart_eq ho.conj.infPart_eq hth
    hB.frame.vac.2.theta hf (hB.frame.vac.2.fock τ)
  have one : ∀ τ, compAt B.F.θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have eu : ∀ τ, (inBasis B.F.BS (realGL B.F.θ S u) τ).val =
      (B.F.BS τ).val⁻¹ * compAt B.F.θ τ (Formalism.L2.Theta.mt S u) * (B.F.BS τ).val := fun τ => by
    rw [← Matrix.coe_units_inv]
    rfl
  have hle : ∀ τ, B.w.p τ ≤ T.rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  unfold Frame.fock
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hθ (fun _ => 1) (fun _ => 1) (fun τ => (B.F.BS τ).val)
    (fun τ => (B.F.BS τ).val * (inBasis B.F.BS (realGL B.F.θ S u) τ).val) B.F.sT B.F.sT B.F.BT B.F.BT u 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, one_mul, mul_one])
    (fun τ => by rw [eu, ← Matrix.coe_units_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul])
    (fun τ => by rw [one, one_mul]) _ hf P).2, om_vac hB hψ hω hf hv hu, GlobalTheory.FiniteFock.pureTensorO_smul,
    pureTensorO_subst (p := B.w.p) hB.frame.vac.1 hθ (fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBS τ)) hB.frame.cartT
      (fun τ => (onb_laws (by have := hB.frame.onbT τ; rwa [← hB.sig τ] at this) (hle τ)).1) _ _
      (fun τ => by rw [eu]; exact conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S u τ)) hf,
    Base.act, MonoidHom.comp_apply, fockGL_apply, LinearMap.map_smul]

end GlobalTheory.RealFockAction

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictHalfApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries

variable {D : D7}


open Classical in
def restrictHalf {m n : ℕ} (a' b : AE D) (Λ : AddSubgroup (Mx D m n)) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun Φ x := Φ (a' • x) * halfInd b Λ (b • x) * (if IsHalf (a' + b) x then 1 else 0)
  map_add' Φ Φ' := by funext x; simp only [Pi.add_apply]; ring
  map_smul' c Φ := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

open Classical in
theorem restrictHalf_apply {m n : ℕ} (a' b : AE D) (Λ : AddSubgroup (Mx D m n)) (Φ : Mx D m n → ℂ) (x : Mx D m n) :
    restrictHalf a' b Λ Φ x = Φ (a' • x) * halfInd b Λ (b • x) * (if IsHalf (a' + b) x then 1 else 0) := rfl

end GlobalTheory.ExportSeries

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralOfIsSubquotientProdIrr
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT

namespace GlobalTheory.RecT

theorem geometricLemma_holds : GlobalTheory.Published.GeometricLemma :=
  GlobalTheory.geometricLemma_of_filtration GlobalTheory.bernsteinZelevinskyFiniteness_holds GlobalTheory.geometricLemmaFiltration_holds

theorem good_toral_of_isSubquotient_prodIrr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : ℕ) (y : Fin t → IrrGL (k := k)) (x : IrrGL (k := k)) (hd : ∑ i, (y i).1 = x.1),
    IsSubquotient x.rep (prodIrr y hd) → (Good x → ∀ i, Good (y i)) ∧ (Toral x → ∀ i, Toral (y i)) ∧
      ((∀ i, Good (y i)) → Good x) ∧ ((∀ i, Toral (y i)) → Toral x) := by
  intro k _ _ _ _ t y x hd hsq
  have hG := geometricLemma_holds
  have hBZ := GlobalTheory.bernsteinZelevinskyFiniteness_holds
  choose s hs using fun i => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG (y i)
  have hx : HasSupport x.rep (∑ i, s i) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr hs x.2.rep.irr hsq

  have down : ∀ P : IrrGL (k := k) → Prop, (∃ u, HasSupport x.rep u ∧ ∀ z ∈ u, P z) →
      ∀ i, ∃ u, HasSupport (y i).rep u ∧ ∀ z ∈ u, P z := by
    rintro P ⟨u, hu, hP⟩ i
    have := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ hu hx
    exact ⟨s i, hs i, fun z hz => hP z (this ▸ Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, hz⟩)⟩

  have up : ∀ P : IrrGL (k := k) → Prop, (∀ i, ∃ u, HasSupport (y i).rep u ∧ ∀ z ∈ u, P z) →
      ∃ u, HasSupport x.rep u ∧ ∀ z ∈ u, P z := by
    intro P h
    choose u hu hP using h
    refine ⟨∑ i, u i, GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr hu x.2.rep.irr hsq, fun z hz => ?_⟩
    obtain ⟨i, -, hz⟩ := Multiset.mem_sum.1 hz
    exact hP i z hz
  exact ⟨down _, down _, up _, up _⟩

end GlobalTheory.RecT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatAtIffHat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatAtHLat

theorem mem_latAt_iff_hat {D : D7} {S T : HSp D} (B : Base S T) (h : Bridge.Gf S) (x : Fin S.rank → D.host.E) :
    x ∈ B.latAt h ↔ (h.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
      GlobalTheory.AdLat.hat D.host.F (B.F.ΛS : Set (Fin S.rank → D.host.E)) := by
  have e : ((Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) =
      fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E (((h.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) i) := by
    rw [← map_inv]
    funext i
    change _ = Lev.swapAE D _
    rw [RingHom.map_mulVec (Lev.swapAE D)]
    rfl
  change ((Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) B.F.ΛS ↔ _
  rw [e]
  constructor
  · intro hz
    have := GlobalTheory.PrincInLevel.swap_symm_mem_hat B.F.ΛS _ hz
    simpa only [AlgEquiv.symm_apply_apply] using this
  · intro hz
    exact GlobalTheory.PrincInLevel.swap_mem_hatL B.F.ΛS _ hz

theorem latAt_eq_hLat : ∀ (D : D7) (S T : HSp D) (B : Base S T), (B.F.ΛS : Set (Fin S.rank → D.host.E)) = L0c D S → ∀ h, B.latAt h = Bridge.hLat S h := by
  intro D S T B hΛ h
  have e : Bridge.hLat S h = Submodule.span (𝓞 D.host.E) {x : Fin S.rank → D.host.E |
      (h.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
        GlobalTheory.AdLat.hat D.host.F (B.F.ΛS : Set (Fin S.rank → D.host.E))} := by
    unfold Bridge.hLat
    rw [hΛ]
    rfl
  rw [e, ← Submodule.span_eq (B.latAt h)]
  congr 1
  ext x
  exact mem_latAt_iff_hat B h x

end GlobalTheory.LatAtHLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGood
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceIdempotentFiniteAdeleZeroElsewhere
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceIdempotentFiniteAdeleZeroElsewhere
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries

theorem idem_apply_eq_zero_of_ne : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ k : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] k) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) k) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → ∀ (P : Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ P' : Pl D.host.E, P' ≠ P → ι (finPart D e) P' = 0 := by
  intro D ι h1 h2 P e he P' hP
  have hee : e * e = e := he.1.1
  have hm : ∀ a b : AE D, ι (finPart D (a * b)) P' = ι (finPart D a) P' * ι (finPart D b) P' := fun a b => by
    rw [RingHom.map_mul, map_mul]; rfl
  by_contra h0
  have hone : ι (finPart D e) P' = 1 := mul_left_cancel₀ h0 (by rw [← hm, hee, mul_one])
  refine hP (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top fun x hx => ?_))
  by_cases hx0 : x = 0
  · rw [hx0]; exact zero_mem _
  refine (he.2 x hx0).2 fun hint => ?_
  have hv := (h2 _).1 hint P'
  have hi : ι (finPart D (incA D ((x : D.host.E)⁻¹))) P' =
      algebraMap D.host.E (P'.adicCompletion D.host.E) ((x : D.host.E)⁻¹) :=
    congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P') (h1 ((x : D.host.E)⁻¹))
  rw [hm, hone, one_mul, hi, map_inv₀, map_inv₀, GlobalTheory.GeoLevel.valued_coe_int] at hv
  have hlt : P'.intValuation x < 1 := (P'.intValuation_lt_one_iff_mem x).2 hx
  have hpos : 0 < P'.intValuation x := zero_lt_iff.2 (P'.intValuation_ne_zero x hx0)
  exact absurd ((inv_le_one₀ hpos).1 hv) (not_le.2 hlt)

end GlobalTheory.ExportSeries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceIdempotentFiniteAdeleZeroElsewhereStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_idempotent_finite_adele_zero_elsewhere : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ k : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] k) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) k) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → ∀ (P : Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ P' : Pl D.host.E, P' ≠ P → ι (finPart D e) P' = 0 := by
  first | exact @GlobalTheory.ExportSeries.idem_apply_eq_zero_of_ne | exact GlobalTheory.ExportSeries.idem_apply_eq_zero_of_ne | (intros; apply GlobalTheory.ExportSeries.idem_apply_eq_zero_of_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePartIntegralUnitOfUnitResidue
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePartIntegralUnitOfUnitResidue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries

theorem finPart_mem_intAE_of_unit_residue : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ k : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] k) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) k) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → ∀ (P : Pl D.host.E) (e : AE D), (∀ P' : Pl D.host.E, P' ≠ P → ι (finPart D e) P' = 0) → ∀ (x : (AE D)ˣ), (1 - e) * (x : AE D) = 1 - e → ∀ (hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (v : (kP P)ˣ), resS D.host.F P ⟨_, hx⟩ = v → finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := by
  intro D ι h1 h2 P e he x hxe hx v hv
  have hun : GlobalTheory.GeoLevel.unswap D (toEAf D (x : AE D)) = finPart D (x : AE D) :=
    GlobalTheory.GeoLevel.unswap_swap (finPart D (x : AE D))
  have hy : ∀ P' : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P') = 1 := by
    intro P'
    by_cases hP : P' = P
    · subst hP
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (v : kP P')
      have hna : a ∉ P'.asIdeal := fun h => v.ne_zero (by rw [← ha]; exact Ideal.Quotient.eq_zero_iff_mem.2 h)
      have h4 := GlobalTheory.GeoLevel.valued_sub_le ι h1 h2 P' ⟨_, hx⟩ a (hv.trans ha.symm)
      have h5 : Valued.v (algebraMap D.host.E (P'.adicCompletion D.host.E) (a : D.host.E)) = 1 := by
        rw [GlobalTheory.GeoLevel.valued_coe_int]
        exact HeightOneSpectrum.intValuation_eq_one_iff.2 hna
      have h6 : Valued.v (ι (finPart D (x : AE D)) P' -
          algebraMap D.host.E (P'.adicCompletion D.host.E) (a : D.host.E)) ≤ WithZero.exp (-1 : ℤ) := by
        rw [← hun]; exact h4
      rw [← h5]
      refine Valuation.map_eq_of_sub_lt _ (h6.trans_lt ?_)
      rw [h5, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.2 (by norm_num)
    · let ev : FiniteAdeleRing (𝓞 D.host.E) D.host.E →+* P'.adicCompletion D.host.E :=
        RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.adicCompletion D.host.E) P'
      have h0 : ev (ι (finPart D e)) = 0 := he P' hP
      have h3 := congrArg (fun z => ev (ι (finPart D z))) hxe
      simp only [map_mul, map_sub, map_one, h0, sub_zero, one_mul] at h3
      have h4 : ι (finPart D (x : AE D)) P' = 1 := h3
      rw [h4, map_one]
  refine ⟨(h2 _).2 fun P' => (hy P').le, (h2 _).2 fun P' => ?_⟩
  have e1 : ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have e2 : ι (finPart D (x : AE D)) P' * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P' = 1 :=
    congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P') e1
  have e3 := congrArg (Valued.v : P'.adicCompletion D.host.E → _) e2
  rw [map_mul, map_one, hy P', one_mul] at e3
  exact e3.le

end GlobalTheory.ExportSeries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePartIntegralUnitOfUnitResidueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_part_integral_unit_of_unit_residue : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ k : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] k) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) k) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → ∀ (P : Pl D.host.E) (e : AE D), (∀ P' : Pl D.host.E, P' ≠ P → ι (finPart D e) P' = 0) → ∀ (x : (AE D)ˣ), (1 - e) * (x : AE D) = 1 - e → ∀ (hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (v : (kP P)ˣ), resS D.host.F P ⟨_, hx⟩ = v → finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := by
  first | exact @GlobalTheory.ExportSeries.finPart_mem_intAE_of_unit_residue | exact GlobalTheory.ExportSeries.finPart_mem_intAE_of_unit_residue | (intros; apply GlobalTheory.ExportSeries.finPart_mem_intAE_of_unit_residue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGood
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ExportSeries.SpecGood

variable {D : D7}

theorem infPart_eq_zero_of_isIdemAt : ∀ (D : D7) (P : Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 := by
  intro D P e h
  obtain ⟨⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h3⟩, -⟩ := h
  have k1 := congrArg (infPart D) h1
  have k2 := congrArg (infPart D) h2
  have k3 := congrArg (infPart D) h3
  simp only [RingHom.map_mul, RingHom.map_add (f := _), RingHom.map_zero] at k1 k2 k3
  have k4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    simp [infPart, Algebra.TensorProduct.algebraMap_apply]
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  rw [k4] at k3
  linear_combination -k1 + infPart D e * k3 - k2

theorem finUnit_of_res (P : Pl D.host.E) (hP : Formalism.L2.NTheta.IsIdemAt (idemAt P) P) (x : (AE D)ˣ)
    (h1 : (1 - idemAt P) * (x : AE D) = 1 - idemAt P)
    (hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (v : (kP P)ˣ)
    (hv : resS D.host.F P ⟨_, hx⟩ = v) :
    infPart D (x : AE D) = 1 ∧ finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := by
  obtain ⟨ι, i1, i2, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  refine ⟨?_, GlobalTheory.T.finite_part_integral_unit_of_unit_residue D ι i1 i2 P (idemAt P) (GlobalTheory.T.place_idempotent_finite_adele_zero_elsewhere D ι i1 i2 P _ hP) x h1 hx v hv⟩
  have := congrArg (infPart D) h1
  rwa [RingHom.map_mul, RingHom.map_sub, RingHom.map_one, infPart_eq_zero_of_isIdemAt D P _ hP, sub_zero, one_mul] at this

variable {C A : Type} [AddCommGroup C] [CommGroup A]

theorem idemAt_mul_idem {Q : Finset (Pl D.host.E)} (h : SplitSet Q) {P : Pl D.host.E} (hP : P ∈ Q) :
    idemAt P * idem Q = idemAt P :=
  GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (h.isIdemAt ha).1) (fun a ha b hb hab => h.mul_eq_zero ha hb hab) hP

theorem idemAt_mul_conj_idem {Q : Finset (Pl D.host.E)} (h : SplitSet Q) {P : Pl D.host.E} (hP : P ∈ Q) :
    idemAt P * cA D (idem Q) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [idem, map_sum, Finset.mul_sum]
  exact Finset.sum_eq_zero fun j hj => h.mul_conj hP hj

theorem delQ_eq_one {u : UnivTwist D C} {Q : Finset (Pl D.host.E)} {x : (AE D)ˣ} (hx : ∀ P ∈ Q, u.del P x = 1) :
    u.delQ Q x = 1 := by
  ext PP
  exact congrArg Multiplicative.toAdd (hx PP.1 PP.2)


open Classical in
theorem spec_good (D : D7) (C A : Type) [AddCommGroup C] [CommGroup A] (u : UnivTwist D C) (Q : Finset (Pl D.host.E))
    (χ : Multiplicative (↥Q → C) →* A) (h : u.Good Q) : (u.spec Q χ).Good := by
  have cc := GlobalTheory.DualPairCheck.cA_cA (D := D)
  refine ⟨?_, ?_, ?_, h.1, ?_, ?_⟩
  · haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
    let H : Subgroup (AE D)ˣ := ⨅ P : ↥Q, (u.del P.1).ker
    have hH : IsOpen (H : Set (AE D)ˣ) := by
      rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun P => (h.2 P.1 P.2).isOpen
    refine Subgroup.isOpen_mono (fun x hx => ?_) hH
    rw [Subgroup.mem_iInf] at hx
    show χ (u.delQ Q x) = 1
    rw [delQ_eq_one fun P hP => hx ⟨P, hP⟩, map_one]
  · intro x
    show χ (u.delQ Q _) = 1
    rw [delQ_eq_one fun P hP => (h.2 P hP).rat x, map_one]
  · intro a
    show χ (u.delQ Q _) = 1
    rw [h.delQ_real a, map_one]
  · intro x h1 h2 h3 h4
    show χ (u.delQ Q x) = 1
    replace h4 : (idem Q + cA D (idem Q)) * (x : AE D) = idem Q + cA D (idem Q) := h4
    refine (congrArg χ (delQ_eq_one fun P hP => ?_)).trans (map_one χ)
    refine (h.2 P hP).unram x h1 h2 h3 ?_
    show (idem {P} + cA D (idem {P})) * (x : AE D) = idem {P} + cA D (idem {P})
    have e1 : idem ({P} : Finset (Pl D.host.E)) = idemAt P := Finset.sum_singleton _ _
    rw [e1]
    have k1 := idemAt_mul_idem h.1 hP
    have k2 := idemAt_mul_conj_idem h.1 hP
    have k3 : cA D (idemAt P) * idem Q = 0 := by
      have := congrArg (cA D) k2
      rwa [RingHom.map_mul, cc, RingHom.map_zero] at this
    have k4 : cA D (idemAt P) * cA D (idem Q) = cA D (idemAt P) := by
      rw [← RingHom.map_mul, k1]
    linear_combination (idemAt P + cA D (idemAt P)) * h4 + (1 - (x : AE D)) * (k1 + k2 + k3 + k4)
  · intro PP hPP x h1 hx v hv
    show χ (u.delQ Q x) = (u.spec Q χ).res PP v
    rw [show (u.spec Q χ).res PP = χ.comp ((AddMonoidHom.toMultiplicative (AddMonoidHom.single (fun _ : ↥Q => C) ⟨PP, hPP⟩)).comp
      (u.kap PP)) from dif_pos hPP, MonoidHom.comp_apply]
    have hfu := finUnit_of_res PP (h.1.isIdemAt hPP) x h1 hx v hv
    refine congrArg χ ?_
    ext ⟨P', hP'⟩
    by_cases hne : P' = PP
    · subst hne
      have := (h.2 P' hP').res P' (Finset.mem_singleton_self _) x h1 hx v hv
      simp [UnivTwist.delQ, this]
    · have hd : u.del P' x = 1 := by
        refine (h.2 P' hP').unram x hfu.1 hfu.2.1 hfu.2.2 ?_
        show (idem {P'} + cA D (idem {P'})) * (x : AE D) = idem {P'} + cA D (idem {P'})
        have e1 : idem ({P'} : Finset (Pl D.host.E)) = idemAt P' := Finset.sum_singleton _ _
        rw [e1]
        have z1 : idemAt P' * idemAt PP = 0 := h.1.mul_eq_zero hP' hPP (Ne.symm hne)
        have z2 : idemAt PP * cA D (idemAt P') = 0 := h.1.mul_conj hPP hP'
        linear_combination (idemAt P' + cA D (idemAt P')) * h1 + ((x : AE D) - 1) * (z1 + z2)
      simp [UnivTwist.delQ, hd, Pi.single_apply, hne]
      intro e
      exact absurd (congrArg Subtype.val e) hne

end GlobalTheory.ExportSeries.SpecGood
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGoodStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameTwistFamily_specialization_good : ∀ (D : D7) (C A : Type) [AddCommGroup C] [CommGroup A] (u : UnivTwist D C) (Q : Finset (Pl D.host.E)) (χ : Multiplicative (↥Q → C) →* A), u.Good Q → (u.spec Q χ).Good := by
  first | exact @GlobalTheory.ExportSeries.SpecGood.spec_good | exact GlobalTheory.ExportSeries.SpecGood.spec_good | (intros; apply GlobalTheory.ExportSeries.SpecGood.spec_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunctionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_polynomial_eq_zero_of_function : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → ∀ P ∈ harm m w B, harmFn m w B P = 0 → P = 0 := by
  first | exact @GlobalTheory.ExportSeries.HarmInj.harm_inj | exact GlobalTheory.ExportSeries.HarmInj.harm_inj | (intros; apply GlobalTheory.ExportSeries.HarmInj.harm_inj <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjLMemWeil
open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.FunExt

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FunExt.ConjLift

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω]

theorem mem_Dec_of_iff {F : Type} [Field F] [NumberField F] [Algebra F Ω] {A : ValuationSubring Ω} {σ : G F Ω}
    (hσ : ∀ x, σ x ∈ A ↔ x ∈ A) : σ ∈ Dec (F := F) A := by
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hσ]
  show (σ * σ⁻¹) x ∈ A ↔ x ∈ A
  rw [mul_inv_cancel]; rfl

variable (s : L ≃ₐ[K] L) (g : G K Ω) (hgs : ∀ x : L, g (algebraMap L Ω x) = algebraMap L Ω (s x))
include hgs


variable {A : ValuationSubring Ω}

omit hgs

end GlobalTheory.FunExt.ConjLift
end
end
