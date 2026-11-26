module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumsTwistedDefiniteFormsRational
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumsTwistedDefiniteFormsRational
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.ClassSumRat

variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ D.nexp i j b)

theorem add_mem_range {k : ℕ} {x y : GA D (Wc D j) → ℂ} (hx : x ∈ Set.range (rdK rd hρ k)) (hy : y ∈ Set.range (rdK rd hρ k)) :
    x + y ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  exact ⟨x + y, map_add _ _ _⟩

theorem zero_mem_range {k : ℕ} : (0 : GA D (Wc D j) → ℂ) ∈ Set.range (rdK rd hρ k) := ⟨0, map_zero _⟩

theorem e_smul_mem_range {k : ℕ} (c : FractionRing (D.ntw.O i)) {y : GA D (Wc D j) → ℂ} (hy : y ∈ Set.range (rdK rd hρ k)) :
    ρ.e i b c • y ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨x, rfl⟩ := hy
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add (f := _), smul_add]; exact add_mem_range hρ rd hx hy
  | tmul a f => exact ⟨a ⊗ₜ (c • f), by rw [rdK_tmul, rdK_tmul, LinearMap.map_smulₛₗ, smul_comm]⟩

theorem ek_smul_mem_range {k : ℕ} (a : FractionRing (D.ntw.Ok i k)) {y : GA D (Wc D j) → ℂ} (hy : y ∈ Set.range (rdK rd hρ k)) :
    ρ.ek i b k a • y ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨p, d, hd, e⟩ := D.ntw.Ok_gen i k a
  generalize Polynomial.aeval (D.ntw.zk i k : D.ntw.Ok i k) p = u at e
  have h1 : ρ.ek i b k a * ρ.eO i b d = ρ.eOk i b k u := by
    rw [← hρ.ek_e i b k d]
    exact (map_mul (ρ.ek i b k) _ _).symm.trans (congrArg (ρ.ek i b k) e)
  have hd0 : ρ.eO i b d ≠ 0 := fun h => hd (ρ.eO_injective i b (h.trans (map_zero _).symm))
  have h2 : ρ.ek i b k a = ρ.e i b (algebraMap (D.ntw.O i) _ d)⁻¹ * ρ.eOk i b k u := by
    rw [map_inv₀, ← h1, mul_comm (ρ.ek i b k a)]
    exact (inv_mul_cancel_left₀ hd0 _).symm
  obtain ⟨x, rfl⟩ := hy
  rw [h2, mul_smul]
  exact e_smul_mem_range hρ rd _ ⟨u • x, LinearMap.map_smulₛₗ _ _ _⟩


include hρ in
theorem exists_rep (t : Twist D Circle) (h : GA D (Vc D j)) : ∃ (γ : GQ (Vc D j)) (s : Finset (Pl D.host.E)) (h' : GA D (Vc D j))
    (κ : (ρ.B i j b).levJ t), SplitSet s ∧ (∀ v ∈ s, ((ρ.bad i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) ∧ h' ∈ GfC (Vc D j) ∧
      SuppAt (idem s) (Vc D j) h' ∧
      finPt (Vc D j) h = Bridge.ratF (Vc D j) γ * finPt (Vc D j) h' * (κ : Bridge.Gf (Vc D j)) := by
  obtain ⟨N₀, hN₀, hK⟩ := GlobalTheory.LevFinCong.exists_finCong_lev D (Vc D j) (ρ.B i j b).F.βS ((ρ.B i j b).levS t)
  have hbad : 0 < ρ.bad i := Nat.pos_of_ne_zero (hρ.bad_ne i)
  have hK' : ∀ k ∈ GfC (Vc D j), GlobalTheory.Member.FinCong (Vc D j) N₀ k → FWT.fin (Vc D j) k ∈ (ρ.B i j b).levJ t :=
    fun k hk hc => ((ρ.B i j b).finPt_mem_levJ _ hk).2 (hK k hk hc).1
  obtain ⟨h', ⟨hh', hs⟩, γ, k, e⟩ := GlobalTheory.SplitReps.exists_split_rep (Vc D j) hN₀ hK' hbad (finPt (Vc D j) h)
  obtain ⟨-, e', P, hP, hoff, hsupp⟩ := GlobalTheory.SplitReps.splitOffBad_of_suppSplit (Vc D j) (ρ.bad i) h' hh' hs
  refine ⟨γ, P, h', k, ⟨e', hP⟩, hoff, hh', ?_, e⟩
  rw [idem_eq hP]
  exact hsupp

theorem series_datum (hR : RatTwist hρ rd) {k Q ψ} (hψ : TwOK i k Q ψ) (hQ : ClsQ (D := D) Q) {s h P}
    (hd : ρ.IsDatum i j b s h P) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b k Q ψ).chi) ((ρ.B i j b).vecFlat (ρ.tw i b k Q ψ)) h P ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨ht, hadm, hval⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ
  have h1 := hR k Q ψ hψ hQ s h P hd ⟨1, GlobalTheory.SplitLinear.suppAt_one _ _, rfl⟩
  rw [mul_one, GlobalTheory.TwTraceCx.gen_eq_smul (hρ.base i j b) ht hadm (hρ.weil_base i j b) (hρ.weil i j b _ ht)] at h1
  obtain ⟨u, hu⟩ := hval (detRoot (Vc D j) h)
  have hc : ((detChar (Vc D j) (ρ.tw i b k Q ψ).chi h : Circle) : ℂ) = ρ.ek i b k (algebraMap (D.ntw.Ok i k) _ u) := hu
  have h2 := ek_smul_mem_range hρ rd (algebraMap (D.ntw.Ok i k) _ u)⁻¹ h1
  rwa [map_inv₀, ← hc, inv_smul_smul₀ (Circle.coe_ne_zero _)] at h2

theorem term_mem (hR : RatTwist hρ rd) {k Q ψ} (hψ : TwOK i k Q ψ) (hQ : ClsQ (D := D) Q) {F} (hF : F ∈ ρ.mt i j b k Q ψ)
    {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b k Q ψ).chi) ((ρ.B i j b).vecFlat (ρ.tw i b k Q ψ)) h (F (finPt _ h)) ∈
      Set.range (rdK rd hρ k) := by
  obtain ⟨ht, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ
  have hB := hρ.base i j b
  obtain ⟨hF1, hF2⟩ := ((ρ.B i j b).mem_mtLat _ _ _).1 hF
  obtain ⟨γ, s, h', κ, hs, hoff, hh', hsupp, e⟩ := exists_rep hρ (i := i) (b := b) (ρ.tw i b k Q ψ) h
  have hlaw := ((ρ.B i j b).mem_formsC.1 hF1).2 γ (finPt _ h') κ
  have hinv : ((ρ.B i j b).act ((γ⁻¹ : GQ (Vc D j)) : GA D (Vc D j))) ((ρ.B i j b).act (γ : GA D (Vc D j)) (F (finPt _ h'))) =
      F (finPt _ h') := by
    rw [← mul_apply_eq_comp, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, one_apply_eq_self]
  rw [e, hlaw, LinearMap.map_smul, GlobalTheory.BaseClassSum.series_move hB (D.sp.V_sig _) ht hadm (hρ.weil i j b _ ht) hh hh' γ κ e, hinv,
    smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  have hspan : F (finPt _ h') ∈ Submodule.span (ρ.eOk i b k).range
      (ρ.lat i j b (ρ.eO i b).range h' : Set (PolF D (Wc D j).rank (Vc D j).rank)) :=
    GlobalTheory.SmallSpan.harmLat_le_span (RingHom.id _) (embLL0 D) (labLL0 D) (ρ.eO i b).range (ρ.eOk i b k).range
      (hρ.isCoefRing_k i b k).int _ _ hB.wt (GlobalTheory.CoefLatConj.pq_le hB) (GlobalTheory.SmallSpan.isLattice_latAt hB.frame _) (hF2 _)
  generalize F (finPt _ h') = P at hspan
  induction hspan using Submodule.span_induction with
  | mem P hP => exact series_datum hρ rd hR hψ hQ ⟨hs, hoff, hh', hsupp, hP⟩
  | zero => rw [map_zero]; exact zero_mem_range hρ rd
  | add x y _ _ hx hy => rw [map_add]; exact add_mem_range hρ rd hx hy
  | smul a x _ hx =>
    obtain ⟨_, u, rfl⟩ := a
    have h2 := ek_smul_mem_range hρ rd (algebraMap (D.ntw.Ok i k) _ u) hx
    rw [← map_smul] at h2
    exact h2

theorem sum_mem_range : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (rd : Rd ρ D.nexp i j b) (T : CellTie hρ D.nexp rd), RatTwist hρ rd → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) →
  ∀ k Q ψ, TwOK i k Q ψ → ClsQ (D := D) Q → ∀ f, ρ.sum i j b k Q ψ (T.rdV k Q ψ f) ∈ Set.range (rdK rd hρ k) := by
  intro D ρ hρ i j b rd T hR _ k Q ψ hψ hQ f
  obtain ⟨ht, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ
  have hc := hρ.classes i j b _ ht hadm
  have hf : f ∈ Submodule.span (FractionRing (D.ntw.Ok i k)) (D.nexp.MtLat i ((j : ℕ) + 1) b k Q ψ : Set (D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ)) := by
    rw [D.nexp.MtLat_span]; trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    have hF := (T.mtLat_iff k Q ψ hψ _).2 ⟨f, hf, rfl⟩
    rw [Setup.sum, Base.classSum_apply]
    refine Finset.sum_induction _ (· ∈ Set.range (rdK rd hρ k)) (fun _ _ => add_mem_range hρ rd) (zero_mem_range hρ rd) fun c _ => ?_
    rw [← map_natCast (ρ.ek i b k), ← map_inv₀]
    exact ek_smul_mem_range hρ rd _ (term_mem hρ rd hR hψ hQ hF (hc.fin c))
  | zero => rw [map_zero, map_zero]; exact zero_mem_range hρ rd
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact add_mem_range hρ rd hx hy
  | smul a x _ hx => rw [LinearMap.map_smulₛₗ, map_smul]; exact ek_smul_mem_range hρ rd a hx

end GlobalTheory.ClassSumRat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumsTwistedDefiniteFormsRationalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_sums_twisted_definite_forms_rational : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (rd : Rd ρ D.nexp i j b) (T : CellTie hρ D.nexp rd), RatTwist hρ rd → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) →
  ∀ k Q ψ, TwOK i k Q ψ → ClsQ (D := D) Q → ∀ f, ρ.sum i j b k Q ψ (T.rdV k Q ψ f) ∈ Set.range (rdK rd hρ k) := by
  first | exact @GlobalTheory.ClassSumRat.sum_mem_range | exact GlobalTheory.ClassSumRat.sum_mem_range | (intros; apply GlobalTheory.ClassSumRat.sum_mem_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFormsCentralTranslateIff
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFormsCentralTranslateIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.CentralTranslate

open GlobalTheory.FreeBlockTwist Matrix
open GlobalTheory.StdFrames (cpt)

variable {D : D7} {S T : HSp D}

theorem exists_pow_latAt {B : Base S T} (hF : B.F.Good) {a : AE D} {k : GA D S} (hk : SuppAt a S k) {N : ℕ}
    (ha : ∀ PP : Pl D.host.E, (N : 𝓞 D.host.E) ∉ PP.asIdeal → cpt PP (toEAf D (a + cA D a)) = 0) :
    ∃ m : ℕ, ∀ l, m ≤ l → ∀ h : Bridge.Gf S, ∀ x ∈ B.latAt h,
      ((N ^ l : ℕ) : 𝓞 D.host.E) • x ∈ B.latAt (h * (finPt S k)⁻¹) := by
  classical
  have hβ := hF.frS
  choose m hm using fun ij : Fin S.rank × Fin S.rank =>
    GlobalTheory.StdFrames.exists_pow_mul_mem (N := N)
      (((B.F.βS⁻¹).1 * (Formalism.L2.Theta.mt S k).map (toEAf D) * B.F.βS.1) ij.1 ij.2) fun PP hPP =>
      conj_entry (toEAf D) B.F.βS hk (cpt PP) (ha PP hPP) (PP.adicCompletionIntegers D.host.E) (zero_mem _) (one_mem _) ij.1 ij.2
  refine ⟨Finset.univ.sup m, fun l hl h x hx => ?_⟩
  have hx' : ((Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹).1 *ᵥ (fun i => eToEAf D (x i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) B.F.ΛS := hx
  have h3 := (hβ _).1 hx'
  have h4 := (hβ _).2 (conj_mulVec _ B.F.βS _ (fun i j => hm (i, j) l ((Finset.le_sup (Finset.mem_univ _)).trans hl)) h3)
  change ((Formalism.UG.bc (Lev.swapAE D) (h * (finPt S k)⁻¹).1)⁻¹).1 *ᵥ (fun i => eToEAf D ((((N ^ l : ℕ) : 𝓞 D.host.E) • x) i)) ∈
    Formalism.L2.Herm.hatL (F := D.host.F) B.F.ΛS
  have e1 : (Formalism.UG.bc (Lev.swapAE D) (h * (finPt S k)⁻¹).1)⁻¹ =
      Formalism.UG.bc (Lev.swapAE D) (finPt S k).1 * (Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.map_mul, MonoidHom.map_inv, _root_.mul_inv_rev, inv_inv]
  have e2 : (fun i => eToEAf D ((((N ^ l : ℕ) : 𝓞 D.host.E) • x) i)) = (N ^ l) • fun i => eToEAf D (x i) := by
    funext i
    rw [Nat.cast_smul_eq_nsmul, Pi.smul_apply, Pi.smul_apply, map_nsmul]
  rw [e1, e2, Units.val_mul, mulVec_nsmul]
  convert h4 using 1
  funext i
  rw [Pi.smul_apply, nsmul_eq_mul]
  rfl

theorem coefLatFn_le {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    {n : ℕ} (lam : D.what₂.Tau → DomWeight n) {M M' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {N : ℕ} (hN : N ≠ 0)
    (hO : (N : ℂ)⁻¹ ∈ O) (hM : Submodule.IsFullLattice D.host.E M) (h1 : ∀ x ∈ M, (N : 𝓞 D.host.E) • x ∈ M')
    (h2 : ∀ x ∈ M', (N : 𝓞 D.host.E) • x ∈ M) : coefLatFn σ emb O lam M ≤ coefLatFn σ emb O lam M' := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨F, hF, rfl⟩
  have h3 : coefFn σ lam (((N : K) ^ GlobalTheory.NabScale.scaleExp lam • F : VV K lam) : Pol K D.what₂.Tau n) ∈ coefLatFn σ emb O lam M' :=
    Submodule.subset_span ⟨_, nabAtr_scale emb lam N (by first | exact hM.toIsLattice | exact hM) h1 h2 F hF, rfl⟩
  have h4 := Submodule.smul_mem _ ((⟨_, hO⟩ : O) ^ GlobalTheory.NabScale.scaleExp lam) h3
  have h0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  rw [SetLike.mem_coe]
  convert h4 using 1
  funext x
  change _ = ((N : ℂ)⁻¹) ^ GlobalTheory.NabScale.scaleExp lam * coefFn σ lam ((N : K) ^ GlobalTheory.NabScale.scaleExp lam • F.1) x
  rw [coefFn, coefFn, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, map_pow, map_natCast, inv_pow]
  field_simp

theorem coefLat_mul {B : Base S T} (hF : B.F.Good) {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ) {a : AE D} {k : GA D S} (hk : SuppAt a S k) {N : ℕ} (hN : N ≠ 0)
    (hO : (N : ℂ)⁻¹ ∈ O)
    (ha : ∀ PP : Pl D.host.E, (N : 𝓞 D.host.E) ∉ PP.asIdeal → cpt PP (toEAf D (a + cA D a)) = 0) (h : Bridge.Gf S) :
    B.coefLat σ emb O (h * finPt S k) = B.coefLat σ emb O h := by
  obtain ⟨m₁, h₁⟩ := exists_pow_latAt hF hk ha
  obtain ⟨m₂, h₂⟩ := exists_pow_latAt hF (GlobalTheory.SplitLinear.suppAt_inv hk) ha
  have e1 := h₁ (m₁ + m₂) (Nat.le_add_right _ _) (h * finPt S k)
  have e2 := h₂ (m₁ + m₂) (Nat.le_add_left _ _) h
  rw [mul_inv_cancel_right] at e1
  rw [show finPt S k⁻¹ = (finPt S k)⁻¹ from MonoidHom.map_inv _ k, inv_inv] at e2
  have hL : ∀ y : Bridge.Gf S, Submodule.IsFullLattice D.host.E (B.latAt y) := by
    intro y
    classical
    have hspan : Submodule.span D.host.E (B.F.ΛS : Set (Fin S.rank → D.host.E)) = ⊤ := by
      let W := Submodule.span D.host.E (B.F.ΛS : Set (Fin S.rank → D.host.E))
      change W = ⊤
      by_contra hW
      let g : (Fin S.rank → D.host.E) →ₗ[D.host.E] Module.Dual D.host.E W :=
        { toFun := fun x => { toFun := fun y => ∑ i, ∑ j, x i * S.gram i j * y.1 j
                              map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
                              map_smul' := by intros; simp [mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum] }
          map_add' := by intros; ext y; simp [add_mul, Finset.sum_add_distrib]
          map_smul' := by intros; ext y; simp [mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum] }
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E (Fin S.rank → D.host.E) := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt hW
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      let v : Fin S.rank → D.host.E := fun i => star (x i)
      have hv0 : v ≠ 0 := by
        intro hv
        apply hx0
        funext i
        have hi := congrFun hv i
        simpa [v] using congrArg star hi
      have hline (r : D.host.E) : r • v ∈ B.F.ΛS := by
        apply (hF.sdS.2 _).2
        intro y hy
        have hz : (∑ i, ∑ j, x i * S.gram i j * y j) = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hzy : (∑ i, ∑ j, star (y i) * S.gram i j * v j) = 0 := by
          have hg (i j : Fin S.rank) : star (S.gram i j) = S.gram j i := by
            exact S.herm.eq _ _
          have hs : (starRingEnd D.host.E) (∑ i, ∑ j, x i * S.gram i j * y j) = 0 := by rw [hz, map_zero]
          simp only [map_sum, map_mul] at hs
          change (∑ i, ∑ j, star (x i) * star (S.gram i j) * star (y j)) = 0 at hs
          simp only [hg] at hs
          rw [Finset.sum_comm] at hs
          simpa [mul_comm, mul_left_comm, mul_assoc] using hs
        refine ⟨0, ?_⟩
        simp only [map_zero, Pi.smul_apply, smul_eq_mul]
        calc
          0 = r * (∑ i, ∑ j, star (y i) * S.gram i j * v j) := by rw [hzy, mul_zero]
          _ = ∑ i, ∑ j, star (y i) * S.gram i j * (r * v j) := by simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra hn
        apply hv0
        funext i
        simpa using not_exists.mp hn i
      let coord := (LinearMap.proj i : (Fin S.rank → D.host.E) →ₗ[D.host.E] D.host.E).restrictScalars (𝓞 D.host.E)
      have htop : B.F.ΛS.map coord = ⊤ := by
        rw [eq_top_iff]
        intro a _
        exact ⟨(a / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 D.host.E) D.host.E := Module.finite_def.mpr (htop ▸ hF.sdS.1.fg.map coord)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    exact Formalism.UG.P.csGlob_lattice _ (Module.Finite.iff_fg.2 hF.sdS.1.fg) hspan _
  have hO' : ((N ^ (m₁ + m₂) : ℕ) : ℂ)⁻¹ ∈ O := by
    rw [Nat.cast_pow, ← inv_pow]
    exact pow_mem hO _
  have e := le_antisymm (coefLatFn_le σ emb O B.w.lam (pow_ne_zero _ hN) hO' (hL _) e1 e2)
    (coefLatFn_le σ emb O B.w.lam (pow_ne_zero _ hN) hO' (hL _) e2 e1)
  unfold Base.coefLat harmLat
  rw [e]

theorem translate_mem_formsC {B : Base S T} {ψ : Twist D Circle} {c : Bridge.Gf S} (hc : ∀ g, g * c = c * g)
    {f : Bridge.Gf S → PolF D T.rank S.rank} (hf : f ∈ B.formsC ψ) : (fun h => f (h * c)) ∈ B.formsC ψ := by
  rw [Base.mem_formsC] at hf ⊢
  refine ⟨fun h => hf.1 _, fun γ h k => ?_⟩
  have := hf.2 γ (h * c) k
  rw [← mul_assoc, mul_assoc _ c, ← hc, ← mul_assoc] at this
  exact this

theorem mem_mtLat_iff_translate : ∀ (D : D7) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → ∀ (ψ : Twist D Circle) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ), IsCoefRing σ emb O →
  ∀ (Q : Finset (Pl D.host.E)) (z : GA D (Vc D j)), IsCentAt j Q z → ∀ N : ℕ, N ≠ 0 → (∀ P ∈ Q, (N : 𝓞 D.host.E) ∈ P.asIdeal) → (N : ℂ)⁻¹ ∈ O →
  ∀ F : Amb D j, F ∈ B.mtLat σ emb O ψ ↔ (fun h => F (h * finPt (Vc D j) z)) ∈ B.mtLat σ emb O ψ := by
  intro D j B hB ψ K _ _ σ emb O _ Q z hz N hN hQ hO F
  obtain ⟨hzc, -, e, he, hsupp⟩ := hz
  have ha : ∀ PP : Pl D.host.E, (N : 𝓞 D.host.E) ∉ PP.asIdeal → cpt PP (toEAf D (e + cA D e)) = 0 := fun PP hPP => by
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), (cpt_sum he PP).2 fun h => hPP (hQ PP h), zero_add, GlobalTheory.StdFrames.toEAf_cA]
    exact GlobalTheory.StdFrames.cpt_sg_eq_zero ((cpt_sum he _).2 fun h => hPP ((GlobalTheory.StdFrames.natCast_mem_cP PP N).1 (hQ _ h)))
  have hc : ∀ g : Bridge.Gf (Vc D j), g * finPt (Vc D j) z = finPt (Vc D j) z * g := fun g => by
    obtain ⟨y, rfl⟩ := (finHom (Vc D j)).rangeRestrict_surjective g
    rw [← MonoidHom.map_mul, ← MonoidHom.map_mul, Subgroup.mem_center_iff.1 hzc y]
  have hc' : ∀ g : Bridge.Gf (Vc D j), g * (finPt (Vc D j) z)⁻¹ = (finPt (Vc D j) z)⁻¹ * g := fun g =>
    (Commute.inv_right (hc g)).eq
  have hl := coefLat_mul hB.frame σ emb O hsupp hN hO ha
  rw [Base.mem_mtLat, Base.mem_mtLat]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨translate_mem_formsC hc h1, fun h => hl h ▸ h2 _⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun h => ?_⟩
    · have := translate_mem_formsC hc' h1
      simp only [inv_mul_cancel_right] at this
      exact this
    · have := h2 (h * (finPt (Vc D j) z)⁻¹)
      rw [← hl] at this
      simp only [inv_mul_cancel_right] at this
      exact this

end GlobalTheory.CentralTranslate

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFormsCentralTranslateIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_forms_central_translate_iff : ∀ (D : D7) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → ∀ (ψ : Twist D Circle) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ), IsCoefRing σ emb O →
  ∀ (Q : Finset (Pl D.host.E)) (z : GA D (Vc D j)), IsCentAt j Q z → ∀ N : ℕ, N ≠ 0 → (∀ P ∈ Q, (N : 𝓞 D.host.E) ∈ P.asIdeal) → (N : ℂ)⁻¹ ∈ O →
  ∀ F : Amb D j, F ∈ B.mtLat σ emb O ψ ↔ (fun h => F (h * finPt (Vc D j) z)) ∈ B.mtLat σ emb O ψ := by
  first | exact @GlobalTheory.CentralTranslate.mem_mtLat_iff_translate | exact GlobalTheory.CentralTranslate.mem_mtLat_iff_translate | (intros; apply GlobalTheory.CentralTranslate.mem_mtLat_iff_translate <;> assumption)
end
end
