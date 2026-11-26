module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AmbientH1fOfLocalFiniteness
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiAtPsiAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryGroupPositiveCharacterTrivialAndUnimodula
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentRepresentation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisationStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarBoundOfMultiplicity
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLinkTyp

theorem typePrime_size_terms_le_elementary (n t r nV f η eta vdel constantSecondHub C1 x : ℝ) (hf : f = 2 * n) (hnV0 : 0 ≤ nV) (hnV : nV ≤ 2 * t)
    (hr0 : 0 ≤ r) (hr : r ≤ t) (he0 : 0 ≤ eta) (he : eta ≤ η) (ht1 : 1 ≤ t) (hte : t ≤ η) (hn1 : 1 ≤ n)
    (hnx : n ≤ x ^ C1) (htx : t ≤ x ^ C1) (hv0 : 0 ≤ vdel) (hv : vdel ≤ 2 * t) (hC68 : 0 ≤ constantSecondHub) (hC1 : 1 ≤ C1)
    (hx : 1 ≤ x) :
    4 * f * nV * (constantSecondHub * nV ^ 2 * (nV + eta + t)) + 2 * f * r ^ 2 + 4 * nV * vdel ≤
      (2000 * (constantSecondHub + 1) + 5 * C1) * x ^ (2000 * (constantSecondHub + 1) + 5 * C1) * η := by
  have hη1 : 1 ≤ η := ht1.trans hte
  have ht0 : 0 ≤ t := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hη0 : 0 ≤ η := by linarith
  have e1 : nV ^ 2 ≤ 4 * t ^ 2 := by nlinarith
  have e2 : nV + eta + t ≤ 4 * η := by linarith
  have eT : constantSecondHub * nV ^ 2 * (nV + eta + t) ≤ constantSecondHub * (4 * t ^ 2) * (4 * η) := by
    have h0 : 0 ≤ nV + eta + t := by linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left e1 hC68) e2 h0 (by positivity)
  have A : 4 * f * nV * (constantSecondHub * nV ^ 2 * (nV + eta + t)) ≤ 256 * constantSecondHub * (n * t ^ 3) * η := by
    rw [hf]
    have h1 : 4 * (2 * n) * nV ≤ 4 * (2 * n) * (2 * t) := mul_le_mul_of_nonneg_left hnV (by positivity)
    have h2 : 0 ≤ constantSecondHub * nV ^ 2 * (nV + eta + t) := by
      have : 0 ≤ nV + eta + t := by linarith
      positivity
    calc 4 * (2 * n) * nV * (constantSecondHub * nV ^ 2 * (nV + eta + t))
        ≤ 4 * (2 * n) * (2 * t) * (constantSecondHub * (4 * t ^ 2) * (4 * η)) :=
          mul_le_mul h1 eT h2 (by positivity)
      _ = 256 * constantSecondHub * (n * t ^ 3) * η := by ring
  have ht3 : t ^ 2 ≤ t ^ 3 := by nlinarith
  have B : 2 * f * r ^ 2 ≤ 4 * (n * t ^ 3) * η := by
    rw [hf]
    have h1 : r ^ 2 ≤ t ^ 2 := by nlinarith
    have h2 : n * t ^ 3 ≤ n * t ^ 3 * η := le_mul_of_one_le_right (by positivity) hη1
    nlinarith [mul_le_mul_of_nonneg_left h1 hn0, mul_le_mul_of_nonneg_left ht3 hn0]
  have Cc : 4 * nV * vdel ≤ 16 * (n * t ^ 3) * η := by
    have h1 : 4 * nV * vdel ≤ 4 * (2 * t) * (2 * t) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hnV (by norm_num)) hv hv0 (by positivity)
    have h2 : t ^ 2 ≤ n * t ^ 3 := by nlinarith
    have h3 : n * t ^ 3 ≤ n * t ^ 3 * η := le_mul_of_one_le_right (by positivity) hη1
    nlinarith
  have hX0 : 0 ≤ x ^ C1 := Real.rpow_nonneg (by linarith) _
  have hnt : n * t ^ 3 ≤ x ^ (4 * C1) := by
    have : x ^ (4 * C1) = x ^ C1 * (x ^ C1) ^ 3 := by
      rw [show (4 : ℝ) * C1 = C1 + C1 * (3 : ℕ) by push_cast; ring, Real.rpow_add (by linarith),
        Real.rpow_mul_natCast (by linarith : (0 : ℝ) ≤ x)]
    rw [this]
    exact mul_le_mul hnx (pow_le_pow_left₀ ht0 htx 3) (by positivity) hX0
  have hexp : x ^ (4 * C1) ≤ x ^ (2000 * (constantSecondHub + 1) + 5 * C1) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hK : 256 * constantSecondHub + 20 ≤ 2000 * (constantSecondHub + 1) + 5 * C1 := by linarith
  have hxC0 : 0 ≤ x ^ (2000 * (constantSecondHub + 1) + 5 * C1) := Real.rpow_nonneg (by linarith) _
  have hsum : 4 * f * nV * (constantSecondHub * nV ^ 2 * (nV + eta + t)) + 2 * f * r ^ 2 + 4 * nV * vdel ≤
      (256 * constantSecondHub + 20) * (n * t ^ 3) * η := by nlinarith
  calc _ ≤ (256 * constantSecondHub + 20) * (n * t ^ 3) * η := hsum
    _ ≤ (2000 * (constantSecondHub + 1) + 5 * C1) * x ^ (2000 * (constantSecondHub + 1) + 5 * C1) * η := by
        apply mul_le_mul_of_nonneg_right _ hη0
        exact mul_le_mul hK (hnt.trans hexp) (by positivity) (by linarith)

end GlobalTheory.NLinkTyp

namespace GlobalTheory.NLinkTyp


open Classical in
theorem starH_of_local {D : D7} (L : SizeData₂ D) (C : ℝ)
    (hloc : ∀ i : D.nd.Loc, TwistedPlaces.TwLoc D i → D.nd.l i ∈ TwistedPlaces.gset D →
      (D.nd.etaLoc i : ℝ) ≤ ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ) *
        (C * L.sc.x ^ C * L.etaSz + TwistedPlaces.epsL (D.nd.l i) + TwistedPlaces.VVr D (D.nd.l i) + TwistedPlaces.vhE D (D.nd.l i) +
          TwistedPlaces.epsL (D.nd.l i)))
    (hM : ∀ l ∈ TwistedPlaces.gset D,
      0 ≤ C * L.sc.x ^ C * L.etaSz + TwistedPlaces.epsL l + TwistedPlaces.VVr D l + TwistedPlaces.vhE D l + TwistedPlaces.epsL l)
    (hmult : MultLe L) (h3 : TwistedPlaces.adm3 L) : StarH L C := by
  intro j hj l hl
  set M := C * L.sc.x ^ C * L.etaSz + TwistedPlaces.epsL l + TwistedPlaces.VVr D l + TwistedPlaces.vhE D l + TwistedPlaces.epsL l with hMdef
  have hM0 : 0 ≤ M := hM l hl
  have hlp : l.Prime := by
    unfold TwistedPlaces.gset at hl
    rcases Finset.mem_insert.1 hl with h | h
    · rw [h]; exact D.host.g_prime 0
    · rw [Finset.mem_singleton.1 h]; exact D.host.g_prime 1
  have hj' : 1 ≤ j ∧ j ≤ D.R.m := Finset.mem_Icc.1 hj
  have hw : ∀ w ∈ TwistedPlaces.twAt L l, (D.what₂.etaJ j w : ℝ) ≤ (L.dZ0 j : ℝ) * M := by
    intro w hw
    obtain ⟨_, htw, hres⟩ := TwistedPlaces.mem_twAt.1 hw
    rw [D.etaJ_tie j w hj'.1 hj'.2]
    push_cast
    calc ∑ i ∈ D.nd.locs j w, (D.nd.etaLoc i : ℝ)
        ≤ ∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ) * M := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hli : D.nd.l i = l := by
            rw [← D.nd.w_l i, ((D.nd.locs_mem j w i).1 hi).2, hres]
          have := hloc i (htw.twLoc hi) (hli ▸ hl)
          rw [hli] at this
          exact this
      _ = (∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) * M := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
      _ ≤ (L.zeroSpaceRankAtPlace j w : ℝ) * M := mul_le_mul_of_nonneg_right (hmult j hj w htw) hM0
      _ = (L.dZ0 j : ℝ) * M := by rw [h3 j hj w htw]
  unfold TwistedPlaces.etaAt
  have hnn : ∀ w, 0 ≤ SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) := fun w =>
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  calc ∑ w ∈ TwistedPlaces.twAt L l, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (D.what₂.etaJ j w : ℝ)
      ≤ ∑ w ∈ TwistedPlaces.twAt L l, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * ((L.dZ0 j : ℝ) * M) :=
        Finset.sum_le_sum fun w h => mul_le_mul_of_nonneg_left (hw w h) (hnn w)
    _ = (∑ w ∈ TwistedPlaces.twAt L l, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) * ((L.dZ0 j : ℝ) * M) := by
        rw [Finset.sum_mul]
    _ ≤ Real.log l * ((L.dZ0 j : ℝ) * M) :=
        mul_le_mul_of_nonneg_right (TwistedPlaces.admissibleMeanCondition_holds L l hlp) (mul_nonneg (Nat.cast_nonneg _) hM0)
    _ = Real.log l * (L.dZ0 j : ℝ) * M := by ring

end GlobalTheory.NLinkTyp

namespace GlobalTheory.NLinkTyp

theorem rhs_le {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (constantSecondHub C1 : ℝ) (hC68 : 0 ≤ constantSecondHub)
    (hC1 : 1 ≤ C1) (hpar : TwistedPlaces.ParametersPolynomiallyBounded L C1 P) (heta : (X.eta : ℝ) ≤ L.etaSz) (hK : KillingConditions.KillAt X.ρ)
    (i : D.nd.Loc) (hi : TwistedPlaces.TwLoc D i) (hl2 : D.nd.l i ∉ D.host.small) (hν : TwistedPlaces.nuL D (D.nd.l i) = 0) (π : D.nd.X i) (hπ : π ∈ D.nd.Zgood i) :
    PairedCharacterCondition.rhs constantSecondHub X.eta i (X.ρ i) π ≤
      (2000 * (constantSecondHub + 1) + 5 * C1) * L.sc.x ^ (2000 * (constantSecondHub + 1) + 5 * C1) * L.etaSz + TwistedPlaces.epsL (D.nd.l i) +
        TwistedPlaces.VVr D (D.nd.l i) + TwistedPlaces.vhE D (D.nd.l i) + TwistedPlaces.epsL (D.nd.l i) := by
  have hK1 := ((hK i hi).1 π hπ).2
  rw [hν, zero_add] at hK1
  have hK2 := (hK i hi).2
  have hVV : TwistedPlaces.VVr D (D.nd.l i) = ∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℝ) := by
    have : TwistedPlaces.VVr D (D.nd.l i) = ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) := by
      show ((∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) = _
      congr 2
    rw [this]
    push_cast
    rfl
  have hvh : TwistedPlaces.vhE D (D.nd.l i) = (padicValNat (D.nd.l i) (hE D.host) : ℝ) := rfl
  have hZ : (∑ q ∈ D.nd.Q i, (PairedCharacterCondition.vZeta i q : ℝ)) = ((∑ v ∈ D.nd.Q i,
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}) : ℚ) : ℝ) := by
    push_cast
    rfl

  have htr := TwistedPlaces.t_ge D
  have hnV : (D.R.nV : ℝ) = D.R.r + D.R.t := by unfold Ranks.nV; push_cast; ring
  have hv0 : (0 : ℝ) ≤ (D.nd.vdel i : ℝ) := by
    have : (0 : ℚ) ≤ D.nd.vdel i := by unfold NData.vdel; positivity
    exact_mod_cast this
  have hv : (D.nd.vdel i : ℝ) ≤ 2 * D.R.t := by
    have h1 := LargeLevelLemmas.vdel_le (D := D) i
    rw [UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i hl2] at h1
    have h2 : (padicValNat (D.nd.l i) D.R.t.factorial : ℚ) ≤ D.R.t := by
      rw [Nat.padicValNat_def]
      exact_mod_cast multiplicity_factorial_le (D.nd.l i) D.R.t
    have h3 : D.nd.vdel i ≤ 2 * (D.R.t : ℚ) := by push_cast at h1; linarith
    exact_mod_cast h3
  have hS := typePrime_size_terms_le_elementary (D.R.n : ℝ) D.R.t D.R.r D.R.nV D.R.f L.etaSz (X.eta : ℝ) (D.nd.vdel i : ℝ) constantSecondHub C1 L.sc.x
    (TwistedPlaces.f_eq D) (Nat.cast_nonneg _) (by linarith) (Nat.cast_nonneg _) (by linarith) (Nat.cast_nonneg _) heta
    (TwistedPlaces.t_ge_one D) (TwistedPlaces.t_le_eta L P) (TwistedPlaces.n_ge_one D) hpar.2.2.2.1 hpar.2.2.2.2.1 hv0 hv hC68 hC1
    L.sc.one_lt_alt.le
  unfold PairedCharacterCondition.rhs PairedCharacterCondition.eT
  rw [hVV, hvh, hZ]
  linarith

end GlobalTheory.NLinkTyp

namespace GlobalTheory.NLinkTyp

theorem g_two_lt {D : D7} (L : SizeData₂ D) (hG : SizeG L) (k : Fin 2) : 2 < D.host.g k := by
  have h := (hG k k).1
  have hk : (5 : ℝ) ≤ D.R.k := TwistedPlaces.k_ge_five D
  have hb : 1 ≤ L.sc.b := by
    rw [TwistedPlaces.b_eq]
    exact Real.one_le_exp (by linarith [TwistedPlaces.L_ge_one L])
  have h5 : (5 : ℝ) ≤ D.R.k * L.sc.b := by nlinarith
  have h8 : (5 : ℝ) ^ 8 ≤ (D.R.k * L.sc.b) ^ 8 := pow_le_pow_left₀ (by norm_num) h5 8
  have : (2 : ℝ) < D.host.g k := by nlinarith
  exact_mod_cast this

end GlobalTheory.NLinkTyp

namespace GlobalTheory.NLinkTyp

end GlobalTheory.NLinkTyp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalIffUnrOfLawsT
section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRecTOfIsRec
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GLq

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecT.Model

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

section Classes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem good_of_toral {x : IrrGL (k := k)} (hx : Toral x) : Good x := by
  obtain ⟨s, hs, hy⟩ := hx
  exact ⟨s, hs, fun y hys => Or.inl (hy y hys)⟩

end Classes

end GlobalTheory.RecT.Model

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardCosocleGLHolds
namespace GlobalTheory

theorem standardCosocleGL_holds : GlobalTheory.Published.StandardCosocleGL :=
  CompanionTheory.Exh.standardCosocleGL_of_seg CompanionTheory.RgGu.segmentRepresentation

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsMultisegmentsOutright
namespace GlobalTheory

theorem langlandsMultisegments_outright : GlobalTheory.Published.LanglandsMultisegments :=
  CompanionTheory.Exh.langlandsMultisegments_of_seg CompanionTheory.RgGu.segmentRepresentation

end GlobalTheory
end

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.RecT
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RecT.SphLaw

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def consEquiv (n : ℕ) : ((Fin 1 → ℂ) × (Fin n → ℂ)) ≃ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun v := Fin.cons (v.1 0) v.2
  invFun f := (fun _ => f 0, Fin.tail f)
  map_add' x y := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  left_inv v := Prod.ext (funext fun i => by rw [Subsingleton.elim i 0]; simp) (funext fun j => by simp [Fin.tail])
  right_inv f := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]

theorem diag_sum_iso {n : ℕ} (c : Fin (n + 1) → ℂˣ) :
    ((WDRep.diag h fun _ : Fin 1 => c 0).sum (WDRep.diag h fun i : Fin n => c i.succ)).Iso (WDRep.diag h c) := by
  refine ⟨consEquiv n, fun σ v => ?_, fun v => ?_⟩
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [consEquiv]
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [consEquiv]

theorem sumList_cons (x : WD h) (l : List (WD h)) : sumList (x :: l) = x.lpSum (sumList l) := rfl

theorem sumList_ofFn_diag : ∀ (n : ℕ) (c : Fin n → ℂˣ),
    sumList (List.ofFn fun i => WD.mk (WDRep.diag h fun _ : Fin 1 => c i)) = WD.mk (WDRep.diag h c)
  | 0, c => by
      rw [List.ofFn_zero]
      show WD.lpZero (h := h) = _
      unfold WD.lpZero
      congr 2
      funext i
      exact i.elim0
  | n + 1, c => by
      rw [List.ofFn_succ]
      rw [sumList_cons]
      rw [sumList_ofFn_diag n (fun i => c i.succ), WD.lpSum_mk]
      exact WD.sound (diag_sum_iso c)

theorem zelevinskyPolynomialRing : GlobalTheory.Published.ZelevinskyPolynomialRing :=
  GlobalTheory.zelevinskyPolynomialRing_of_parts GlobalTheory.bernsteinZelevinskyFiniteness_holds GlobalTheory.segmentRepresentation'
    GlobalTheory.grothendieckRingPolynomial_outright

theorem geometricLemma : GlobalTheory.Published.GeometricLemma :=
  GlobalTheory.geometricLemma_of_filtration GlobalTheory.bernsteinZelevinskyFiniteness_holds GlobalTheory.geometricLemmaFiltration_holds

variable {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem sat (H : LawsT a ha rc) (x : IrrGL (k := w.adicCompletion E)) (α : Fin x.1 → ℂˣ) (hα : HasSatake x.rep α) :
    rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hL := GlobalTheory.LocLanglands.SatakeL.isL_single_unrChar GlobalTheory.langlandsExhaustionGL_holds
    GlobalTheory.langlandsMultisegments_outright GlobalTheory.standardCosocleGL_holds zelevinskyPolynomialRing geometricLemma
    GlobalTheory.bernsteinZelevinskyFiniteness_holds (w.adicCompletion E) x α hα
  rw [Fin.univ_val_map] at hL
  rw [H.langlands _ x hL, segSum, List.map_ofFn, ← sumList_ofFn_diag]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
    zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, H.one]
  exact Test.lpOfChar_unrChar ha (α i) _

end GlobalTheory.RecT.SphLaw

namespace GlobalTheory.RecT

theorem isSpherical_iff_unr_of_lawsT : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsT a ha rc → ∀ x : IrrGL (k := w.adicCompletion E), IsSpherical x.rep ↔ (rc x).unr := by
  intro E Ω _ _ _ _ _ A w h a ha rc H x
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  constructor
  · intro hs
    obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.main GlobalTheory.bernsteinZelevinskyFiniteness_holds (w.adicCompletion E) x.1
      ⟨x.2.rep.V, x.2.rep.ρ, x.2.rep.smooth, x.2.rep.irr⟩ hs
    rw [SphLaw.sat H x α hα]
    exact (WD.unr_mk _).2 (WDRep.unr_diag _)
  · intro hu
    obtain ⟨α, hα⟩ := GlobalTheory.LocLanglands.unr_eq_diag_inv E Ω A w h (rc x) hu
    obtain ⟨π, hπ⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := w.adicCompletion E) α
    have φ := equivRep π
    have hπ' : HasSatake (cls π).rep α := ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hπ.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hπ.2.2⟩
    have e1 := SphLaw.sat H (cls π) α hπ'
    have hsupp := GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries (w.adicCompletion E) _
      (fun i => unrChar (w.adicCompletion E) (α i)) (fun i => isSmoothChar_of_isUnram (isUnram_unrChar _ _))
      (cls π).2.rep hπ'.2.2
    have hg : Good (cls π) := Model.good_of_toral ⟨_, hsupp, fun y hy => by
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
      rfl⟩
    have e2 : x = cls π := H.inj x (cls π) hg (hα.trans e1.symm)
    rw [e2]
    exact hπ'.2.1

end GlobalTheory.RecT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverLevelOneOverSmallField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverLevelOneOverSmallField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverSmall

abbrev smallF (D : D7) : IntermediateField ℚ ℂ := (embLL0 D).toRatAlgHom.fieldRange

theorem smallF_toSubfield (D : D7) : (smallF D).toSubfield = (embLL0 D).fieldRange := by
  ext x; rfl

def smallEquiv (D : D7) : D.LL0 ≃ₐ[ℚ] smallF D := AlgEquiv.ofInjectiveField (embLL0 D).toRatAlgHom

instance smallF_fin (D : D7) : FiniteDimensional ℚ (smallF D) :=
  (smallEquiv D).toLinearEquiv.finiteDimensional

theorem smallF_normal (D : D7) (hgal : IsGalois ℚ D.LL0) : Normal ℚ (smallF D) :=
  (IsGalois.of_algEquiv (smallEquiv D)).to_normal

theorem rayIn_of_dvd (hRF : GlobalTheory.NT.RayField) (D : D7) {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hd : M ∣ N)
    {k : Subfield ℂ} (h : RayIn D N k) : RayIn D M k := by
  obtain ⟨L, i1, i2, i3, i4, hL, j, hj, hk⟩ := h
  have hMb : Ideal.span {((M : ℕ) : 𝓞 D.host.K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hM
  have hNb : Ideal.span {((N : ℕ) : 𝓞 D.host.K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hN
  obtain ⟨L', f1, f2, f3, f4, hL'⟩ := hRF D.host.K _ hMb
  have hdv : Ideal.span {((M : ℕ) : 𝓞 D.host.K)} ∣ Ideal.span {((N : ℕ) : 𝓞 D.host.K)} :=
    Ideal.dvd_iff_le.2 (Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hd))
  obtain ⟨f⟩ := GlobalTheory.Published.nonempty_algHom_of_isRay_of_dvd (L := L) (L' := L') hNb hdv hL hL'
  refine ⟨L', f1, f2, f3, f4, hL', j.comp f.toRingHom, ?_, fun x => hk (f x)⟩
  rw [← hj]; ext x; simp

theorem core_le_small {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL]
    (Rl : RealDat3 D A3 ↥T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S)
    (hLaws : LawsJ T) (ha : AlgTie T) (j : Fin D.R.m) : T.Q.c.F ≤ smallF D := by
  intro a ha'
  refine ⟨S.kKs ((YS.fi j).eK.symm ⟨a, ha'⟩), ?_⟩
  have h1 : res T D.what₂.embLL = T.σ₀ := res_embLL T ha hLaws.pins.2.2.1
  change D.what₂.embLL ((S.kKs ((YS.fi j).eK.symm ⟨a, ha'⟩) : ↥D.LL0) : D.what₂.LL) = a
  rw [S.kKs_spec, ← (YS.fi j).eK_LL, RingEquiv.apply_symm_apply]
  exact RingHom.congr_fun h1 ⟨a, ha'⟩

theorem exists_goodCover_small : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → ∀ n : ℕ, ∃ C : GlobalTheory.CoverRead.Cover T ((j : ℕ) + 1) T.σ₀, C.d.pd = 1 ∧ C.σ₂.fieldRange = (embLL0 D).fieldRange ∧ GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.GoodCover T Rl.toRealDat j C n := by
  intro D Γ _ _ Pl0 I0 T0 A3 hRF T _ Rl cG S YS F κ v₀ O hLaws hCore hFW hTie hIo hQG hgal hVal hRay hroots j hV hOM hFP n
  haveI : Normal ℚ (smallF D) := smallF_normal D hgal
  have hle : T.Q.c.F ≤ smallF D := core_le_small T Rl cG S YS hLaws hTie.alg j
  have hnum := GlobalTheory.T.numerical_consequences_of_pins D T.Q hLaws.toLawsM.pins
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := hLaws.toLawsM.pins.2.1.1
  have hz : ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (T.Q.l.M * 1) ∈ smallF D := by
    rw [mul_one, ← hnum.2.2.1]; exact hle T.Q.c.zeta_mem
  have hsm : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SmallIn Rl.toRealDat j ((smallF D).val : smallF D →+* ℂ) := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨y, hy⟩ := hVal.mu0 j v hv
      exact ⟨⟨embLL0 D y, y, rfl⟩, hy⟩
    · obtain ⟨y, hy⟩ := hVal.eta v hv
      exact ⟨⟨embLL0 D y, y, rfl⟩, hy⟩
  have hM0 : T.Q.l.M ≠ 0 := by have := T.Q.l.three_le; omega
  have hN0 : D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' ≠ 0 := by
    have h0 := (D.host.g_prime 0).ne_zero
    have h1 := (D.host.g_prime 1).ne_zero
    have h2 := D.host.pde_prime.ne_zero
    have h3 := D.host.pde'_prime.ne_zero
    positivity
  have hray : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (T.Q.l.M * 1) (smallF D).toSubfield := by
    rw [mul_one, smallF_toSubfield]
    refine rayIn_of_dvd hRF D hM0 hN0 ?_ hRay
    rw [hMg, mul_assoc _ D.host.pde]; exact dvd_mul_right _ _
  have hj : InR D ((j : ℕ) + 1) := ⟨by omega, j.2⟩
  have hK : (⊤ : Ideal (𝓞 D.host.E)) = Ideal.span {x | x ∈ (⊤ : Ideal (𝓞 D.host.E)) ∧ x ∈ Algebra.adjoin ℤ {T.Q.H.w0}} := by
    symm; rw [Ideal.eq_top_iff_one]; exact Ideal.subset_span ⟨Submodule.mem_top, Subalgebra.one_mem _⟩
  have hprod : (⊤ : Ideal (𝓞 D.host.E)) * (⊤ : Ideal (𝓞 D.host.E)).map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) =
      Ideal.span {((1 : ℕ) : 𝓞 D.host.E)} := by
    rw [Ideal.map_top, Ideal.top_mul, Nat.cast_one, Ideal.span_singleton_one]
  have hsup : (⊤ : Ideal (𝓞 D.host.E)) ⊔ (⊤ : Ideal (𝓞 D.host.E)).map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ :=
    top_sup_eq _
  obtain ⟨C, hpd, -, hfr, hG⟩ := GlobalTheory.CoverGalois.exists_goodCover_galois D T Rl.toRealDat hLaws j hj n 1 ⊤
    (GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.auxiliarySplitSquarefreeLevel_one _) hK hprod hsup (smallF D) hle hz hsm hray
  exact ⟨C, hpd, hfr.trans (smallF_toSubfield D), hG⟩

end GlobalTheory.CoverSmall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverLevelOneOverSmallFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodCover_levelOne_over_smallField : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → ∀ n : ℕ, ∃ C : GlobalTheory.CoverRead.Cover T ((j : ℕ) + 1) T.σ₀, C.d.pd = 1 ∧ C.σ₂.fieldRange = (embLL0 D).fieldRange ∧ GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.GoodCover T Rl.toRealDat j C n := by
  first | exact @GlobalTheory.CoverSmall.exists_goodCover_small | exact GlobalTheory.CoverSmall.exists_goodCover_small | (intros; apply GlobalTheory.CoverSmall.exists_goodCover_small <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegralsInvariantLocallyCon
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegralsInvariantLocallyCon
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.OrbLC

theorem eventually_eq_fun {A G β : Type} [TopologicalSpace A] [TopologicalSpace G] (Φ : A → G → β) (a₀ : A)
    (K : Set G) (hK : IsCompact K) (hloc : ∀ g ∈ K, ∀ᶠ z in 𝓝 (a₀, g), Φ z.1 z.2 = Φ a₀ g)
    (hout : ∀ᶠ a in 𝓝 a₀, ∀ g ∉ K, Φ a g = Φ a₀ g) : ∀ᶠ a in 𝓝 a₀, Φ a = Φ a₀ := by
  have h := hK.eventually_forall_of_forall_eventually (x₀ := a₀) (P := fun a g => Φ a g = Φ a₀ g) (by
    intro g hg
    have h1 := hloc g hg
    have hT : Tendsto (fun z : A × G => (a₀, z.2)) (𝓝 (a₀, g)) (𝓝 (a₀, g)) := by
      have : Continuous (fun z : A × G => (a₀, z.2)) := by fun_prop
      simpa using this.tendsto (a₀, g)
    have h2 := hT.eventually h1
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2])
  filter_upwards [h, hout] with a h1 h2
  funext g
  by_cases hg : g ∈ K
  · exact h1 g hg
  · exact h2 g hg

theorem act_mul {r : ℕ} {k : Type} [CommRing k] (g h : GL (Fin r) k) (Y : Gl r k) :
    act (g * h) Y = act g (act h Y) := by
  simp only [act, Units.val_mul, _root_.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem actU_mul {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    (g h : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : actU (g * h) X = actU g (actU h X) := by
  simp only [actU]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · apply Subtype.ext
    simp only [Submonoid.coe_mul, star_mul, Matrix.mul_assoc]
  · simp only [Submonoid.coe_mul, Matrix.mulVec_mulVec]

theorem part1 (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (r : ℕ) (M : Meas r F E) (f' : Gl r F → ℂ) (g : GL (Fin r) F) (Y : Gl r F) :
    orbG M f' (act g Y) = orbG M f' Y := by
  letI := M.mG
  haveI := M.bG
  haveI := GlobalTheory.T.generalLinear_haar_isMulRightInvariant_unramified F E r M
  unfold orbG
  simp only [← act_mul]
  exact integral_mul_right_eq_self (fun h => f' (act h Y) * omega (act h Y)) g

theorem part2 (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (r : ℕ) (M : Meas r F E) (f : Hn r F E → ℂ) (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) :
    orbU M f (actU g X) = orbU M f X := by
  letI := M.mU
  haveI := M.bU
  haveI := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E r).2 M
  unfold orbU
  simp only [← actU_mul]
  exact integral_mul_right_eq_self (fun h => f (actU h X)) g

end GlobalTheory.JR.OrbLC

namespace GlobalTheory.JR.OrbLC

theorem companion_pow_mulVec {r : ℕ} {k : Type} [CommRing k] (p : Fin r → k) :
    ∀ (j : ℕ) (hj : j < r), (companion p) ^ j *ᵥ (fun i : Fin r => if (i : ℕ) = 0 then (1 : k) else 0) =
      Pi.single (⟨j, hj⟩ : Fin r) 1 := by
  intro j
  induction j with
  | zero =>
    intro hj
    funext i
    simp only [pow_zero, Matrix.one_mulVec, Pi.single_apply, Fin.ext_iff]
  | succ j ih =>
    intro hj
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih (by omega)]
    funext i
    rw [Matrix.mulVec_single]
    simp only [companion, Matrix.of_apply, mul_one, Pi.single_apply, Fin.ext_iff]
    have : j + 1 ≠ r := by omega
    simp [this]

theorem Cm_sec {r : ℕ} {k : Type} [CommRing k] (a : Inv r k) : Cm (sec a) = hankel a := by
  ext i j
  simp only [Cm, hankel, mom, Matrix.of_apply]
  rw [pow_add, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have h := companion_pow_mulVec a.1 j j.2
  simp only [sec] at h ⊢
  rw [h, Fin.eta, dotProduct_single, mul_one]

theorem lastDet_act_sec {r : ℕ} {k : Type} [CommRing k] (g : GL (Fin r) k) (a : Inv r k) :
    lastDet (act g (sec a)) = (-1) ^ r * (Delta a * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).det) := by
  rw [(GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det k r).1, (GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det k r).2, Matrix.det_mul, Cm_sec]
  rfl

theorem eta_eventually {F : Type} [NormedField F] [IsUltrametricDist F] (x : F) (hx : x ≠ 0) :
    ∀ᶠ y in 𝓝 x, eta y = eta x := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  filter_upwards [Metric.ball_mem_nhds x hpos] with y hy
  have hn : ‖y‖ = ‖x‖ := by
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := y - x) (y := x) hy.ne
    rw [sub_add_cancel] at this
    rw [this, max_eq_right hy.le]
  unfold eta
  rw [hn]

end GlobalTheory.JR.OrbLC

namespace GlobalTheory.JR.OrbLC

theorem part3 (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (r : ℕ) (M : Meas r F E) (f' : Gl r F → ℂ) (hf : IsTest f') (a₀ : Inv r F) (hΔ : Delta a₀ ≠ 0) :
    ∀ᶠ a in 𝓝 a₀, orbG M f' (sec a) = orbG M f' (sec a₀) := by
  haveI : LocallyCompactSpace F := Unram.lcF (E := E)
  haveI : IsUltrametricDist F := Unram.ultraF (E := E)
  obtain ⟨hcont, -, hDc, hprop⟩ := GlobalTheory.T.jacquetRallis_orbit_invariant_map_proper F E r
  have hopen : IsOpen {a : Inv r F | Delta a ≠ 0} := isOpen_ne_fun hDc continuous_const
  obtain ⟨Ω, hΩn, hΩsub, hΩc⟩ := local_compact_nhds (hopen.mem_nhds hΔ)
  set K : Set (GL (Fin r) F) :=
    Prod.fst '' {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ tsupport f'} with hKdef
  have hK : IsCompact K := (hprop (tsupport f') Ω hf.2 hΩc (fun a ha => hΩsub ha)).image continuous_fst
  have hzero : ∀ a ∈ Ω, ∀ g ∉ K, f' (act g (sec a)) = 0 := by
    intro a ha g hg
    by_contra h
    exact hg ⟨(g, a), ⟨ha, subset_tsupport _ h⟩, rfl⟩
  set Φ : Inv r F → GL (Fin r) F → ℂ := fun a g => f' (act g (sec a)) * omega (act g (sec a)) with hΦ
  have ha₀ : a₀ ∈ Ω := mem_of_mem_nhds hΩn
  have hc2 : Continuous (fun z : Inv r F × GL (Fin r) F => act z.2 (sec z.1)) :=
    hcont.comp continuous_swap
  have hdet : Continuous (fun z : Inv r F × GL (Fin r) F =>
      (-1 : F) ^ r * (Delta z.1 * ((z.2⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det)) := by
    have h1 : Continuous (fun z : Inv r F × GL (Fin r) F => ((z.2⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) :=
      Units.continuous_val.comp (continuous_inv.comp continuous_snd)
    exact continuous_const.mul ((hDc.comp continuous_fst).mul h1.matrix_det)
  have hloc : ∀ g ∈ K, ∀ᶠ z in 𝓝 (a₀, g), Φ z.1 z.2 = Φ a₀ g := by
    intro g _
    have h1 : ∀ᶠ z in 𝓝 (a₀, g), f' (act z.2 (sec z.1)) = f' (act g (sec a₀)) :=
      (hc2.tendsto (a₀, g)).eventually ((IsLocallyConstant.iff_eventually_eq f').1 hf.1 _)
    have hne : (-1 : F) ^ r * (Delta a₀ * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (mul_ne_zero hΔ ?_)
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (g⁻¹ : GL (Fin r) F))).ne_zero
    have h2 := (hdet.tendsto (a₀, g)).eventually (eta_eventually _ hne)
    filter_upwards [h1, h2] with z hz1 hz2
    simp only [hΦ, omega, lastDet_act_sec]
    rw [hz1]
    rw [hz2]
  have hout : ∀ᶠ a in 𝓝 a₀, ∀ g ∉ K, Φ a g = Φ a₀ g := by
    filter_upwards [hΩn] with a ha g hg
    simp only [hΦ, hzero a ha g hg, hzero a₀ ha₀ g hg, zero_mul]
  filter_upwards [eventually_eq_fun Φ a₀ K hK hloc hout] with a h
  have h' : ∀ g, f' (act g (sec a)) * omega (act g (sec a)) = f' (act g (sec a₀)) * omega (act g (sec a₀)) :=
    fun g => congrFun h g
  simp only [orbG, h']

end GlobalTheory.JR.OrbLC

namespace GlobalTheory.JR.OrbLC

theorem continuous_star_of_unram (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] : Continuous (star : E → E) :=
  (AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := E)) (fun x => Unram.norm_star (F := F) x)).continuous

theorem continuous_actU (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) :
    Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => actU p.1 p.2) := by
  haveI : ContinuousStar E := ⟨continuous_star_of_unram F E⟩
  have hg : Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => (p.1 : Matrix (Fin r) (Fin r) E)) :=
    continuous_subtype_val.comp continuous_fst
  have hA : Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => (p.2.1 : Matrix (Fin r) (Fin r) E)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hb : Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => p.2.2.1) :=
    continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hl : Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => p.2.2.2) :=
    continuous_snd.comp (continuous_snd.comp continuous_snd)
  refine Continuous.prodMk ?_ (Continuous.prodMk (hg.matrix_mulVec hb) hl)
  exact Continuous.subtype_mk ((hg.mul hA).mul hg.star) _

theorem part4 (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (r : ℕ) (M : Meas r F E) (f : Hn r F E → ℂ) (hf : IsTest f) (a₀ : Inv r F) (X₀ : Hn r F E)
    (hΔ : Delta a₀ ≠ 0) (hX₀ : HasInv X₀ a₀) :
    ∀ᶠ a in 𝓝 a₀, (∃ X : Hn r F E, HasInv X a) ∧ ∀ X : Hn r F E, HasInv X a → orbU M f X = orbU M f X₀ := by
  obtain ⟨Ω, s, hΩc, hΩo, ha₀, hs, hsinv, hprop⟩ := (GlobalTheory.T.invariant_image_openClosed_local_sections F E r a₀ hΔ).2 ⟨X₀, hX₀⟩
  have huniq := (GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E r).2.2.1
  set K : Set (Matrix.unitaryGroup (Fin r) E) :=
    Prod.fst '' {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ tsupport f} with hKdef
  have hK : IsCompact K := (hprop (tsupport f) hf.2).image continuous_fst
  have hzero : ∀ a ∈ Ω, ∀ g ∉ K, f (actU g (s a)) = 0 := by
    intro a ha g hg
    by_contra h
    exact hg ⟨(g, a), ⟨ha, subset_tsupport _ h⟩, rfl⟩
  set Φ : Inv r F → Matrix.unitaryGroup (Fin r) E → ℂ := fun a g => f (actU g (s a)) with hΦ
  have hloc : ∀ g ∈ K, ∀ᶠ z in 𝓝 (a₀, g), Φ z.1 z.2 = Φ a₀ g := by
    intro g _
    have hsa : ContinuousAt s a₀ := hs.continuousAt (hΩo.mem_nhds ha₀)
    have h1 : ContinuousAt (fun z : Inv r F × Matrix.unitaryGroup (Fin r) E => (z.2, s z.1)) (a₀, g) :=
      continuousAt_snd.prodMk (hsa.comp continuousAt_fst)
    have hT : ContinuousAt (fun z : Inv r F × Matrix.unitaryGroup (Fin r) E => actU z.2 (s z.1)) (a₀, g) :=
      ContinuousAt.comp (g := fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => actU p.1 p.2)
        (f := fun z : Inv r F × Matrix.unitaryGroup (Fin r) E => (z.2, s z.1))
        ((continuous_actU F E r).continuousAt) h1
    exact hT.tendsto.eventually ((IsLocallyConstant.iff_eventually_eq f).1 hf.1 _)
  have hout : ∀ᶠ a in 𝓝 a₀, ∀ g ∉ K, Φ a g = Φ a₀ g := by
    filter_upwards [hΩo.mem_nhds ha₀] with a ha g hg
    simp only [hΦ, hzero a ha g hg, hzero a₀ ha₀ g hg]
  have horb : ∀ a ∈ Ω, ∀ X : Hn r F E, HasInv X a → orbU M f X = orbU M f (s a) := by
    intro a ha X hX
    obtain ⟨g, hg, -⟩ := huniq (s a) X a (hsinv a ha).1 (hsinv a ha).2 hX
    rw [← hg, part2]
  filter_upwards [eventually_eq_fun Φ a₀ K hK hloc hout, hΩo.mem_nhds ha₀] with a h ha
  refine ⟨⟨s a, (hsinv a ha).2⟩, fun X hX => ?_⟩
  have h' : ∀ g, f (actU g (s a)) = f (actU g (s a₀)) := fun g => congrFun h g
  rw [horb a ha X hX, horb a₀ ha₀ X₀ hX₀]
  simp only [orbU, h']

theorem orbital_integrals_invariant_locally_constant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (∀ (f' : Gl r F → ℂ) (g : GL (Fin r) F) (Y : Gl r F), orbG M f' (act g Y) = orbG M f' Y) ∧ (∀ (f : Hn r F E → ℂ) (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E), orbU M f (actU g X) = orbU M f X) ∧ (∀ (f' : Gl r F → ℂ), IsTest f' → ∀ a₀ : Inv r F, Delta a₀ ≠ 0 → ∀ᶠ a in 𝓝 a₀, orbG M f' (sec a) = orbG M f' (sec a₀)) ∧ ∀ (f : Hn r F E → ℂ), IsTest f → ∀ (a₀ : Inv r F) (X₀ : Hn r F E), Delta a₀ ≠ 0 → HasInv X₀ a₀ → ∀ᶠ a in 𝓝 a₀, (∃ X : Hn r F E, HasInv X a) ∧ ∀ X : Hn r F E, HasInv X a → orbU M f X = orbU M f X₀ := by
  intro F E _ _ _ _ _ r M
  exact ⟨part1 F E r M, part2 F E r M, fun f' hf a₀ hΔ => part3 F E r M f' hf a₀ hΔ,
    fun f hf a₀ X₀ hΔ hX₀ => part4 F E r M f hf a₀ X₀ hΔ hX₀⟩

end GlobalTheory.JR.OrbLC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegralsInvariantLocallyConStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisOrbitalIntegrals_invariant_locallyConstant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (∀ (f' : Gl r F → ℂ) (g : GL (Fin r) F) (Y : Gl r F), orbG M f' (act g Y) = orbG M f' Y) ∧ (∀ (f : Hn r F E → ℂ) (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E), orbU M f (actU g X) = orbU M f X) ∧ (∀ (f' : Gl r F → ℂ), IsTest f' → ∀ a₀ : Inv r F, Delta a₀ ≠ 0 → ∀ᶠ a in 𝓝 a₀, orbG M f' (sec a) = orbG M f' (sec a₀)) ∧ ∀ (f : Hn r F E → ℂ), IsTest f → ∀ (a₀ : Inv r F) (X₀ : Hn r F E), Delta a₀ ≠ 0 → HasInv X₀ a₀ → ∀ᶠ a in 𝓝 a₀, (∃ X : Hn r F E, HasInv X a) ∧ ∀ X : Hn r F E, HasInv X a → orbU M f X = orbU M f X₀ := by
  first | exact @GlobalTheory.JR.OrbLC.orbital_integrals_invariant_locally_constant | exact GlobalTheory.JR.OrbLC.orbital_integrals_invariant_locally_constant | (intros; apply GlobalTheory.JR.OrbLC.orbital_integrals_invariant_locally_constant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundAtPlaceOfLatticeColengthBound
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundAtPlaceOfLatticeColengthBound
noncomputable section

namespace GlobalTheory.RowAtOfColLen

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : ℝ) (y : ℚ), RowL i r ρ π w hw Cx x → x ≤ (y : ℝ) → RowAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL Cx.LL)) (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x))) ⇑(TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π)) y := by
  intro D i r ρ π w hw Cx x y hx hxy
  intro V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 T2 hc2 hm2 V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 T1 hc1 hs1 F hF
  obtain ⟨mm, k, h1, h2, h3⟩ :=
    hx { V := V1, ρ := ρ1, cont := hc1, L := T1 } { V := V2, ρ := ρ2, cont := hc2, L := T2 } F hm2 hs1 hF
  refine ⟨mm, k, h1, h2, ?_⟩
  have h4 : (mm : ℝ) ≤ (y : ℝ) * k := h3.trans (mul_le_mul_of_nonneg_right hxy (Nat.cast_nonneg _))
  exact_mod_cast h4

end GlobalTheory.RowAtOfColLen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundAtPlaceOfLatticeColengthBoundStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowBound_at_place_of_latticeColengthBound : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : ℝ) (y : ℚ), RowL i r ρ π w hw Cx x → x ≤ (y : ℝ) → RowAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL Cx.LL)) (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x))) ⇑(TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π)) y := by
  first | exact @GlobalTheory.RowAtOfColLen.main | exact GlobalTheory.RowAtOfColLen.main | (intros; apply GlobalTheory.RowAtOfColLen.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlaceResidueCharactersValuesMemSmallField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlaceResidueCharactersValuesMemSmallField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeChar

theorem chi_mem_smallField : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 ↥T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m), ∀ PP ∈ Rl.Pg, ∀ x : (kP PP)ˣ, ((Rl.chi ((j : ℕ) + 1) PP x : ℂˣ) : ℂ) ∈ (embLL0 D).fieldRange := by
  classical
  intro D Γ _ _ Pl0 I0 T0 A3 T _ Rl cG S YS F _ hCore _ _ hroot j PP hPP x
  obtain ⟨k, hk⟩ := (hCore.lev.Pg PP).1 hPP
  have hov := Rl.C.P.overP hk
  obtain ⟨hn, -, -⟩ := GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) PP hov
  have hcard : Nat.card (kP PP) = D.host.g k := by
    rw [← hn, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (kP PP) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (D.host.g_prime k).ne_zero)
  have : Fintype (kP PP) := Fintype.ofFinite _
  have hu : Nat.card (kP PP)ˣ = D.host.g k - 1 := by
    rw [← hcard, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have : NeZero (Nat.card (kP PP)ˣ) := ⟨Nat.card_pos.ne'⟩
  have h1 : ((Rl.chi ((j : ℕ) + 1) PP x : ℂˣ) : ℂ) ^ Nat.card (kP PP)ˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  rw [hu] at h1
  refine hroot k _ ?_
  rw [mul_comm, pow_mul, h1, one_pow]

end GlobalTheory.TypeChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlaceResidueCharactersValuesMemSmallFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePlace_residueCharacters_values_mem_smallField : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 ↥T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m), ∀ PP ∈ Rl.Pg, ∀ x : (kP PP)ˣ, ((Rl.chi ((j : ℕ) + 1) PP x : ℂˣ) : ℂ) ∈ (embLL0 D).fieldRange := by
  first | exact @GlobalTheory.TypeChar.chi_mem_smallField | exact GlobalTheory.TypeChar.chi_mem_smallField | (intros; apply GlobalTheory.TypeChar.chi_mem_smallField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsOfReadingBoundedCuspidalHolomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsOfReadingBoundedCuspidalHolomorphic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspOfReading


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem mem_cuspA_of_rdU_mem_holSub0 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ w : WeightFamilies.Wt D j, w.LastPos → 8 * D.R.f * D.R.r + 4 ≤ w.n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n, rdU (T.U j T.σ₀) f ∈ Formalism.L2.Pj.holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) → f ∈ T.cuspA j (wtA w) w.n := by
  intro D T h j hj w hw hn f hf hfh
  classical
  set S := T.cuspA j (wtA w) w.n with hS
  haveI : FiniteDimensional T.Q.c.F S := h.toLawsM.cuspFD j hj (wtA w) w.n (dom_wtA w)
  haveI : Module.Free T.Q.c.F S := Module.Free.of_divisionRing _ _
  let b := Module.finBasis T.Q.c.F S
  let b' : Fin (Module.finrank T.Q.c.F S) → T.R j := fun i => (b i : T.R j)
  have hb'S : Submodule.span T.Q.c.F (Set.range b') ≤ S := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact (b i).2
  have hSb' : S ≤ Submodule.span T.Q.c.F (Set.range b') := by
    intro x hx
    have h1 : (⟨x, hx⟩ : S) ∈ Submodule.span T.Q.c.F (Set.range b) := by rw [b.span_eq]; trivial
    have h2 := Submodule.mem_map_of_mem (f := S.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  by_contra hfS
  have hli : LinearIndependent T.Q.c.F (Fin.cons f b' : Fin (Module.finrank T.Q.c.F S + 1) → T.R j) := by
    rw [linearIndependent_finCons]
    exact ⟨b.linearIndependent.map' S.subtype (Submodule.ker_subtype _), fun hm => hfS (hb'S hm)⟩
  have hsec : ∀ i, (Fin.cons f b' : Fin (Module.finrank T.Q.c.F S + 1) → T.R j) i ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n := by
    intro i
    refine Fin.cases hf (fun i => ?_) i
    exact cusp_le_sec _ _ _ _ _ (b i).2
  have hC := GlobalTheory.rdIndep_of_lawsM D T.toCore h.toLawsM j hj T.σ₀ T.toCore.good_σ₀ (wtA w) w.n (dom_wtA w) _ _ hsec hli
  have hC' : LinearIndependent ℂ (Fin.cons (rdU (T.U j T.σ₀) f) (fun i => rdU (T.U j T.σ₀) (b' i)) :
      Fin (Module.finrank T.Q.c.F S + 1) → _) := by
    convert hC using 1
    funext i
    refine Fin.cases rfl (fun i => rfl) i
  rw [linearIndependent_finCons] at hC'
  apply hC'.2
  have hspan := GlobalTheory.OntoCore.holSub0_le_span_cuspA D T h j hj w hw hn T.σ₀ T.toCore.good_σ₀ hfh
  refine (Submodule.span_le.2 ?_) hspan
  rintro _ ⟨x, hx, rfl⟩
  have hx' := hSb' hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

end GlobalTheory.CuspOfReading
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsOfReadingBoundedCuspidalHolomorphicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_cuspForms_of_reading_bounded_cuspidal_holomorphic : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ w : WeightFamilies.Wt D j, w.LastPos → 8 * D.R.f * D.R.r + 4 ≤ w.n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n, rdU (T.U j T.σ₀) f ∈ Formalism.L2.Pj.holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) → f ∈ T.cuspA j (wtA w) w.n := by
  first | exact @GlobalTheory.CuspOfReading.mem_cuspA_of_rdU_mem_holSub0 | exact GlobalTheory.CuspOfReading.mem_cuspA_of_rdU_mem_holSub0 | (intros; apply GlobalTheory.CuspOfReading.mem_cuspA_of_rdU_mem_holSub0 <;> assumption)
end
end
