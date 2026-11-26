module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PartialDerivativeExponent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofComm

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.L2.Pj.SaturatedCharts (toT prodPts_of_combAt combAt_of_prodPts chartTan_of tanAt_of isTan_iff' fst_comp_jetTan)

attribute [local instance] Over.cartesianMonoidalCategory

section Lemmas

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem isChartG_reindex (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) {κ κ' : Type}
    [Fintype κ] [Fintype κ'] (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (tg : κ → (Sp (DualNumber S) ⟶ t.G.left))
    (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (h : IsChartG t x0 d F act tg uvec x) (e : κ' ≃ κ) :
    IsChartG t x0 d F act (fun ℓ => tg (e ℓ)) (fun ℓ => uvec (e ℓ)) x := by
  refine ⟨h.zero, h.trunc, h.law, h.act, fun ℓ => h.tan (e ℓ), ?_⟩
  intro v
  obtain ⟨b, hb, hbu⟩ := h.basis v
  refine ⟨fun ℓ => b (e ℓ), fun j => ?_, fun a ha => ?_⟩
  · rw [← hb j]
    exact Equiv.sum_comp e (fun ℓ => b ℓ * uvec ℓ j)
  · have h1 : (fun ℓ => a (e.symm ℓ)) = b := hbu _ fun j => by
      rw [← ha j, ← Equiv.sum_comp e (fun ℓ => a (e.symm ℓ) * uvec ℓ j)]
      simp only [Equiv.symm_apply_apply]
    funext ℓ
    rw [← h1]
    simp only [Equiv.symm_apply_apply]

variable {V : Type} [CommRing V] (t : SAB H (Sp V))

theorem combAt_iff {n : ℕ} {x} (hx : ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart t.G n x) {m : ℕ}
    (f : Fin m → (Sp (DualNumber V) ⟶ t.G.left)) (hf : ∀ i, f i ≫ t.G.hom = spMap (algebraMap V (DualNumber V)))
    (hft : ∀ i, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t (f i) (hf i))) (a : Fin m → V)
    (w : Sp (DualNumber V) ⟶ t.G.left) (hw : w ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) :
    IsCombAtG t (𝟙 (Sp V)) f a w ↔ ∃ h : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t w hw),
      ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx _ h = ∑ i, a i • ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx _ (hft i) := by
  constructor
  · intro hc
    have e := prodPts_of_combAt (t := t) f hf a w hw hc
    obtain ⟨h, hh⟩ := ReciprocityTheory.ChartRestriction.G.Chart.prodPts_tan hx a (fun i => toT t (f i) (hf i)) hft
    have hT : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t w hw) := by rw [e]; exact h
    exact ⟨hT, (ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx e hT h).trans hh⟩
  · rintro ⟨h, hh⟩
    apply combAt_of_prodPts (t := t) f hf a w hw
    obtain ⟨h', hh'⟩ := ReciprocityTheory.ChartRestriction.G.Chart.prodPts_tan hx a (fun i => toT t (f i) (hf i)) hft
    exact ReciprocityTheory.ChartRestriction.G.Chart.tan_ext hx h h' (hh.trans hh'.symm)

theorem dir_tan {d : ℕ} (xc : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
    (hz : ∀ m, homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) m →ₐ[V] V) ≫ xc m = 1) (j : Fin d)
    (ho : (homAt (𝟙 (Sp V)) (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) ≫
      xc 1).left ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) :
    ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t _ ho) := by
  apply chartTan_of
  refine ⟨ho.trans (Category.comp_id _).symm, ?_⟩
  have h1 := congrArg CommaMorphism.left (hz 1)
  simp only [Over.comp_left] at h1 ⊢
  have h2 : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫
      (homAt (𝟙 (Sp V)) (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V)).left =
      (homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V)).left := by
    show spMap _ ≫ spMap _ = spMap _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact congrArg (fun φ : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V => φ.toRingHom) (fst_comp_jetTan ((0 : Fin 1), j))
  rw [← Category.assoc, h2, h1]
  have hobj : spMap (algebraMap V V) ≫ 𝟙 (Sp V) = 𝟙 (Sp V) := by
    rw [Category.comp_id]
    first
      | (rw [Algebra.algebraMap_self]; exact Spec.map_id _)
      | simp [spMap]
  have h3 : ∀ (f g : Sp V ⟶ Sp V), f = g →
      (1 : Over.mk f ⟶ t.G).left = (1 : Over.mk g ⟶ t.G).left := by
    rintro f g rfl; rfl
  exact h3 _ _ hobj

end Lemmas

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdSy
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)

section Alg

variable {S : Type} [CommRing S] (d : ℕ)

abbrev swJ (m : ℕ) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S)
      p.1 p.2

private theorem jetSubstP_apply_mk {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S)
    (p : MvPolynomial κ S) :
    jetSubstP m φ (Ideal.Quotient.mk (orig S κ ^ (m + 1)) p) =
      Ideal.Quotient.mk _ (aeval (fun i => φ i - C (MvPolynomial.constantCoeff (φ i))) p) := by
  rfl

private theorem degree_eq_sum_lemma_2 {τ : Type} (e : τ →₀ ℕ) : e.degree = ∑ i ∈ e.support, e i := by
  first
  | rfl
  | simp [Finsupp.degree, Finsupp.sum]

private theorem le_degree_lemma_4 {τ : Type} (e : τ →₀ ℕ) (i : τ) : e i ≤ e.degree := by
  by_cases h : e i = 0
  · rw [h]; exact Nat.zero_le _
  · rw [degree_eq_sum_lemma_2]
    exact Finset.single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _)
      (Finsupp.mem_support_iff.2 h)

private theorem mem_degLE_lemma_6 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) (e : τ →₀ ℕ) :
    e ∈ degLE m ↔ e.degree ≤ m := by
  unfold degLE
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨_, h⟩
    rw [degree_eq_sum_lemma_2]
    exact h
  · intro h
    refine ⟨⟨fun i => ⟨e i, by have := le_degree_lemma_4 e i; omega⟩, Finset.mem_univ _, ?_⟩, ?_⟩
    · ext i
      simp
    · rw [degree_eq_sum_lemma_2] at h
      exact h

private theorem coeff_psTrunc_lemma_7 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ)
    (f : MvPowerSeries τ S) (e : τ →₀ ℕ) :
    AddMonoidAlgebra.coeff (psTrunc m f) e = if e.degree ≤ m then MvPowerSeries.coeff e f else 0 := by
  rw [psTrunc, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq', mem_degLE_lemma_6]

theorem mk_psTrunc_X {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) (q : τ) :
    (Ideal.Quotient.mk (orig S τ ^ (m + 1)) (psTrunc m (MvPowerSeries.X q))) = Ideal.Quotient.mk _ (X q) := by
  have hdeg : (Finsupp.single q 1).degree = 1 := by
    rw [degree_eq_sum_lemma_2, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same]
  have hs : psTrunc m (MvPowerSeries.X q : MvPowerSeries τ S) = if 1 ≤ m then X q else 0 := by
    ext e
    rw [coeff_psTrunc_lemma_7, MvPowerSeries.coeff_X]
    by_cases h2 : e = Finsupp.single q 1
    · subst h2
      rw [hdeg]
      by_cases h3 : 1 ≤ m
      · simp [h3, MvPolynomial.coeff_X]
      · simp [h3]
    · have h4 : AddMonoidAlgebra.coeff (X q : MvPolynomial τ S) e = 0 := by
        rw [MvPolynomial.coeff_X']
        exact if_neg (Ne.symm h2)
      split_ifs <;> simp [h4, h2]
  rw [Ideal.Quotient.eq, hs]
  split_ifs with h
  · rw [sub_self]
    exact Ideal.zero_mem _
  · have hm : m = 0 := by omega
    subst hm
    rw [zero_sub, zero_add, pow_one]
    exact Ideal.neg_mem_iff _ |>.2 (Ideal.subset_span ⟨q, rfl⟩)

private theorem jetMap_mk_lemma_13 {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (hφ : ∀ i, φ i ∈ orig S κ')
    (p : MvPolynomial κ S) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk (orig S κ ^ (m + 1)) p) = Ideal.Quotient.mk _ (aeval φ p) := by
  rfl

end Alg

section Axes

variable {S : Type} [CommRing S] (d : ℕ)

abbrev axJ (m : ℕ) (b : Bool) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (if b then ![fun _ => 0, fun j => X ((0 : Fin 1), j)] else ![fun j => X ((0 : Fin 1), j), fun _ => 0] :
      Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2

def axV (b : Bool) (k : Fin 2) (j : Fin d) : MvPolynomial (Fin 1 × Fin d) S :=
  if (k = 1) = b then X ((0 : Fin 1), j) else 0

theorem axJ_X (m : ℕ) (b : Bool) (k : Fin 2) (j : Fin d) :
    axJ (S := S) d m b (Ideal.Quotient.mk _ (X (k, j))) = Ideal.Quotient.mk _ (axV d b k j) := by
  rw [jetSubstP_apply_mk, aeval_X]
  cases b <;> fin_cases k <;> simp [axV]

theorem psTrunc_zero {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) :
    psTrunc m (0 : MvPowerSeries τ S) = 0 := by
  simp [psTrunc]

theorem psJet_ev_ax (m : ℕ) (f : PS S 2 d) (b : Bool) :
    psJet m (ev (n := 1) (if b then ![0, pt S d 0] else ![pt S d 0, 0]) f) = axJ d m b (psJet m f) := by
  have ha : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff
      ((fun p : Fin 2 × Fin d => ((if b then ![0, pt S d 0] else ![pt S d 0, 0]) : Fin 2 → Pt S 1 d) p.1 p.2) p) = 0 := by
    rintro ⟨i, j⟩
    cases b <;> fin_cases i <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  rw [psJet_subst m _ ha f]
  refine DFunLike.congr_fun ?_ (psJet m f)
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨k, j⟩
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [axJ_X, jetMap_mk_lemma_13, aeval_X]
  cases b <;> fin_cases k <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, mk_psTrunc_X, axV, psTrunc_zero]

end Axes

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

theorem scaleGenG_scaleGenG {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (v w : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    scaleGenG t φ ε v (scaleGenG t φ ε w g) = scaleGenG t φ ε (v * w) g := by
  simp only [scaleGenG, Units.val_mul, map_mul, mul_assoc]

theorem unitΓ_mul {A : Type} [CommRing A] (a b : Aˣ) : unitΓ (a * b) = unitΓ a * unitΓ b := by
  exact map_mul (Units.map (toΓ A).toMonoidHom) a b

theorem unitΓ_one {A : Type} [CommRing A] : unitΓ (1 : Aˣ) = 1 := by
  exact map_one (Units.map (toΓ A).toMonoidHom)

end Frame

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqB
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPolynomial Formalism.L2.Pj

namespace GaugeR

variable {R ι : Type} [CommRing R]

theorem monomial_mem_orig_pow (e : ι →₀ ℕ) (a : R) : monomial e a ∈ orig R ι ^ e.degree := by
  rw [monomial_eq]
  apply Ideal.mul_mem_left
  unfold Finsupp.prod
  have hpow : orig R ι ^ e.degree = ∏ i ∈ e.support, orig R ι ^ e i := by
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hpow]
  exact Ideal.prod_mem_prod (fun i _ => Ideal.pow_mem_pow (show (X i : MvPolynomial ι R) ∈ orig R ι from Ideal.subset_span (Set.mem_range_self i)) _)

theorem mem_orig_pow_of_coeff (n : ℕ) (p : MvPolynomial ι R) (h : ∀ e, e.degree < n → AddMonoidAlgebra.coeff p e = 0) :
    p ∈ orig R ι ^ n := by
  rw [p.as_sum]
  refine Ideal.sum_mem _ (fun e he => ?_)
  have hn : n ≤ e.degree := by
    by_contra hlt
    push_neg at hlt
    exact (mem_support_iff.mp he) (h e hlt)
  exact Ideal.pow_le_pow_right hn (monomial_mem_orig_pow e _)

variable [Fintype ι] [DecidableEq ι]

theorem psJet_eq_mk (m : ℕ) (f : MvPowerSeries ι R) (p : MvPolynomial ι R)
    (h : ∀ e, e.degree ≤ m → AddMonoidAlgebra.coeff p e = MvPowerSeries.coeff e f) :
    psJet m f = Ideal.Quotient.mk _ p := by
  unfold psJet
  rw [Ideal.Quotient.eq]
  apply mem_orig_pow_of_coeff
  intro e he
  rw [coeff_sub, GermFun.coeff_psTrunc m f e (by omega), h e (by omega), sub_self]

theorem psJet_mul (m : ℕ) (f g : MvPowerSeries ι R) : psJet m (f * g) = psJet m f * psJet m g := by
  have key : psJet m (f * g) = Ideal.Quotient.mk _ (psTrunc m f * psTrunc m g) := by
    refine psJet_eq_mk m _ _ (fun e he => ?_)
    rw [MvPolynomial.coeff_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hd : x.1.degree + x.2.degree ≤ m := by
      rw [← map_add Finsupp.degree, hx']
      exact he
    rw [GermFun.coeff_psTrunc m f x.1 (by omega), GermFun.coeff_psTrunc m g x.2 (by omega)]
  rw [key, map_mul]
  rfl

theorem psJet_one (m : ℕ) : psJet m (1 : MvPowerSeries ι R) = 1 := by
  rw [psJet_eq_mk m 1 1 (fun e _ => by rw [MvPolynomial.coeff_one, MvPowerSeries.coeff_one]; exact if_congr eq_comm rfl rfl), map_one]

theorem psJet_pow (m : ℕ) (f : MvPowerSeries ι R) (k : ℕ) : psJet m (f ^ k) = psJet m f ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, psJet_one]
  | succ k ih => rw [pow_succ, pow_succ, psJet_mul, ih]

theorem aeval_scale_monomial (s : ι → R) (e : ι →₀ ℕ) (a : R) :
    aeval (fun i => C (s i) * X i) (monomial e a : MvPolynomial ι R) =
      monomial e (a * e.prod fun i k => s i ^ k) := by
  rw [aeval_monomial, monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, ← map_pow]
  rw [map_mul, map_finsuppProd, MvPolynomial.algebraMap_eq]
  ring

theorem coeff_aeval_scale (s : ι → R) (p : MvPolynomial ι R) (e : ι →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun i => C (s i) * X i) p) e = (e.prod fun i k => s i ^ k) * AddMonoidAlgebra.coeff p e := by
  induction p using MvPolynomial.induction_on' with
  | monomial e' a =>
    rw [aeval_scale_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      ring
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem jetMap_mk {ι' : Type} (m : ℕ) (φ : ι → MvPolynomial ι' R) (hφ : ∀ i, φ i ∈ orig R ι')
    (p : MvPolynomial ι R) :
    jetMap φ hφ (Ideal.Quotient.mk (orig R ι ^ (m + 1)) p) = Ideal.Quotient.mk _ (aeval φ p) := rfl

theorem jetSubstP_scale (m : ℕ) (s : ι → R) (f : MvPowerSeries ι R) :
    Formalism.L2.Pj.jetSubstP m (fun i => C (s i) * X i) (psJet m f) =
      psJet m (MvPowerSeries.rescale s f) := by
  unfold jetSubstP psJet
  rw [jetMap_mk]
  simp only [map_mul, constantCoeff_C, constantCoeff_X, mul_zero, map_zero, sub_zero]
  symm
  refine psJet_eq_mk m _ _ (fun e he => ?_)
  rw [coeff_aeval_scale, GermFun.coeff_psTrunc m f e he, MvPowerSeries.coeff_rescale]

theorem jetAug_psJet (m : ℕ) (f : MvPowerSeries ι R) :
    jetAug (psJet m f) = MvPowerSeries.constantCoeff f := by
  show (MvPolynomial.aeval fun _ => (0 : R)) (psTrunc m f) = _
  rw [MvPolynomial.aeval_zero', Algebra.algebraMap_self_apply]
  show AddMonoidAlgebra.coeff (psTrunc m f) 0 = _
  rw [GermFun.coeff_psTrunc m f 0 (by simp)]
  rfl

theorem exists_ps_of_compat (ρ : ∀ m, Jet R ι m) (h : ∀ m, jetTrunc (ρ (m + 1)) = ρ m) :
    ∃ r : MvPowerSeries ι R, ∀ m, psJet m r = ρ m := by
  classical
  choose P hP using fun m => Ideal.Quotient.mk_surjective (ρ m)
  have hstep : ∀ m, P (m + 1) - P m ∈ orig R ι ^ (m + 1) := by
    intro m
    rw [← Ideal.Quotient.eq]
    have h1 := h m
    rw [← hP (m + 1), ← hP m] at h1
    exact h1
  have hcoef : ∀ n k (e : ι →₀ ℕ), e.degree ≤ n → AddMonoidAlgebra.coeff (P (n + k)) e = AddMonoidAlgebra.coeff (P n) e := by
    intro n k e he
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [← ih, ← sub_eq_zero, ← coeff_sub]
      exact GermFun.coeff_eq_zero_of_mem (hstep (n + k)) (by omega)
  refine ⟨fun e => AddMonoidAlgebra.coeff (P e.degree) e, fun m => ?_⟩
  rw [← hP m]
  refine psJet_eq_mk m _ _ (fun e he => ?_)
  have h2 := hcoef e.degree (m - e.degree) e le_rfl
  rw [show e.degree + (m - e.degree) = m by omega] at h2
  rw [h2]
  rfl

end GaugeR

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvA
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA

open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

variable {R : Type} [CommRing R]

theorem coeff_eq_of_psJet {ι : Type} [Fintype ι] [DecidableEq ι] {D : ℕ} {a b : MvPowerSeries ι R}
    (h : psJet D a = psJet D b) {e : ι →₀ ℕ} (he : e.degree ≤ D) :
    MvPowerSeries.coeff e a = MvPowerSeries.coeff e b := by
  have h' : Ideal.Quotient.mk (orig R ι ^ (D + 1)) (psTrunc D a) =
      Ideal.Quotient.mk (orig R ι ^ (D + 1)) (psTrunc D b) := h
  have hm := Ideal.Quotient.eq.mp h'
  have h0 := coeff_eq_zero_of_mem hm (show e.degree < D + 1 by omega)
  rw [MvPolynomial.coeff_sub, coeff_psTrunc D a e he, coeff_psTrunc D b e he] at h0
  exact sub_eq_zero.mp h0

theorem psJet_subst_congr {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] (D : ℕ)
    (a : σ → MvPowerSeries τ R) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) {f g : MvPowerSeries σ R}
    (h : psJet D f = psJet D g) : psJet D (MvPowerSeries.subst a f) = psJet D (MvPowerSeries.subst a g) := by
  rw [psJet_subst D a ha f, psJet_subst D a ha g, h]

def psJetM {ι : Type} [Fintype ι] [DecidableEq ι] (D : ℕ) : MvPowerSeries ι R →* Jet R ι D where
  toFun := psJet D
  map_one' := psJet_one D
  map_mul' := psJet_mul D

theorem psJet_prod_congr {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (D : ℕ)
    {f g : κ → MvPowerSeries ι R} (h : ∀ b, psJet D (f b) = psJet D (g b)) :
    psJet D (∏ b, f b) = psJet D (∏ b, g b) := by
  change psJetM D (∏ b, f b) = psJetM D (∏ b, g b)
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun b _ => h b

theorem subst_exp {σ τ : Type} [Finite σ] [Algebra ℚ R] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (g : MvPowerSeries σ R)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.subst a (PowerSeries.subst g (PowerSeries.exp R)) =
      PowerSeries.subst (MvPowerSeries.subst a g) (PowerSeries.exp R) := by
  exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp a ha hg

end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.DescentPf
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Gen

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

section Jet

variable {k : Type} [CommRing k] {n : ℕ}

end Jet

section Lin

variable {k : Type} [CommRing k] {n : ℕ}

theorem DpolyN_sub {ι : Type} [Fintype ι] (F : Fin d → PS k 2 d) (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (g : PS k n d) (S : Finset (ι →₀ ℕ)) (hS : P.support ⊆ S) :
    DpolyN F cp u P g = ∑ e ∈ S, MvPowerSeries.C (P.coeff e) * DmonN F cp u e g := by
  unfold DpolyN
  refine Finset.sum_subset hS (fun e _ he => ?_)
  have h0 : P.coeff e = 0 := by simpa using he
  rw [h0, map_zero, zero_mul]

theorem DpolyN_addP {ι : Type} [Fintype ι] (F : Fin d → PS k 2 d) (cp : ι → Fin n) (u : ι → Fin d → k)
    (P Q : MvPolynomial ι k) (g : PS k n d) :
    DpolyN F cp u (P + Q) g = DpolyN F cp u P g + DpolyN F cp u Q g := by
  classical
  rw [DpolyN_sub F cp u (P + Q) g (P.support ∪ Q.support) MvPolynomial.support_add,
    DpolyN_sub F cp u P g (P.support ∪ Q.support) Finset.subset_union_left,
    DpolyN_sub F cp u Q g (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.coeff_add, map_add (f := _), add_mul]

theorem DpolyN_smulP {ι : Type} [Fintype ι] (F : Fin d → PS k 2 d) (cp : ι → Fin n) (u : ι → Fin d → k)
    (c : k) (P : MvPolynomial ι k) (g : PS k n d) :
    DpolyN F cp u (c • P) g = c • DpolyN F cp u P g := by
  rw [DpolyN_sub F cp u (c • P) g P.support MvPolynomial.support_smul,
    DpolyN_sub F cp u P g P.support subset_rfl, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul, mul_assoc, ← MvPowerSeries.smul_eq_C_mul]

end Lin

theorem nabValN_addP (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O)
    (m : ℕ) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k) (P Q : MvPolynomial ι k)
    (f : PS k n d) :
    nabValN B k h w0 m f cp u (P + Q) = nabValN B k h w0 m f cp u P + nabValN B k h w0 m f cp u Q := by
  unfold nabValN
  rw [DpolyN_addP, map_add (f := _)]

theorem nabValN_smulP (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O)
    (m : ℕ) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k) (c : k) (P : MvPolynomial ι k)
    (f : PS k n d) :
    nabValN B k h w0 m f cp u (c • P) = c * nabValN B k h w0 m f cp u P := by
  unfold nabValN
  rw [DpolyN_smulP, MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_C]

end Gen

section Asm

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

end Asm

section Main

open ReciprocityTheory.ChartRestriction.G.TB Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.FoldPermutation
section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.FormalGroupCopies
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent

variable {R : Type} [CommRing R] {d n : ℕ}

theorem dofN_mul_left (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (A B : PS R n d)
    (hA : ∀ j, pderiv (R := R) (b, j) A = 0) : DofN F b u (A * B) = A * DofN F b u B := by
  unfold DofN
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Derivation.leibniz, hA j, smul_zero, add_zero, smul_eq_mul]
  ring

section Fold

variable {ι : Type} [Fintype ι] (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)

theorem dmon_zero (g : PS R n d) : DmonN F cp u 0 g = g := by
  simp [DmonN]

theorem dpoly_sup (P : MvPolynomial ι R) (T : Finset (ι →₀ ℕ)) (hT : P.support ⊆ T)
    (g : PS R n d) : DpolyN F cp u P g = ∑ mm ∈ T, C (P.coeff mm) * DmonN F cp u mm g := by
  unfold DpolyN
  apply Finset.sum_subset hT
  intro mm _ hmm
  have h0 : P.coeff mm = 0 := by simpa [MvPolynomial.mem_support_iff] using hmm
  rw [h0, map_zero, zero_mul]

theorem dpoly_add (P Q : MvPolynomial ι R) (g : PS R n d) :
    DpolyN F cp u (P + Q) g = DpolyN F cp u P g + DpolyN F cp u Q g := by
  classical
  rw [dpoly_sup F cp u (P + Q) (P.support ∪ Q.support) MvPolynomial.support_add,
    dpoly_sup F cp u P (P.support ∪ Q.support) Finset.subset_union_left,
    dpoly_sup F cp u Q (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun mm _ => ?_)
  rw [MvPolynomial.coeff_add, map_add (f := _), add_mul]

theorem dpoly_monomial (mm : ι →₀ ℕ) (a : R) (g : PS R n d) :
    DpolyN F cp u (MvPolynomial.monomial mm a) g = C a * DmonN F cp u mm g := by
  classical
  rw [dpoly_sup F cp u _ {mm} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

def dpolyHom (g : PS R n d) : MvPolynomial ι R →+ PS R n d where
  toFun P := DpolyN F cp u P g
  map_zero' := by simp [DpolyN]
  map_add' P Q := dpoly_add F cp u P Q g

end Fold

end Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

variable {k : Type} [CommRing k] {d : ℕ}

def embP {n' n : ℕ} (e : Fin n' → Fin n) : Fin n' → Pt k n d := fun b => pt k d (e b)

theorem cz_embP {n' n : ℕ} (e : Fin n' → Fin n) : LogPf.CZ (embP (k := k) (d := d) e) := by
  intro j i
  simp [embP, pt]

theorem cz_ptz {n : ℕ} (b : Fin n) : LogPf.CZ (![pt k d b, 0] : Fin 2 → Pt k n d) := by
  intro j i
  fin_cases j <;> simp [pt]

theorem pderiv_embP {n' n : ℕ} (e : Fin n' → Fin n) (he : Function.Injective e) (g : PS k n' d) (b : Fin n')
    (j : Fin d) : pderiv (R := k) (e b, j) (ev (embP e) g) =
      ev (embP e) (pderiv (R := k) (b, j) g) := by
  classical
  rw [LogPf.pderiv_ev (cz_embP e), Finset.sum_eq_single (b, j)]
  · simp [embP, LogPf.pderiv_pt]
  · intro p _ hp
    rw [show embP (k := k) (d := d) e p.1 p.2 = pt k d (e p.1) p.2 from rfl, LogPf.pderiv_pt, if_neg, mul_zero]
    intro hc
    apply hp
    have h1 : e p.1 = e b := congrArg Prod.fst hc
    have h2 : p.2 = j := congrArg Prod.snd hc
    exact Prod.ext (he h1) h2
  · simp

theorem pderiv_ev_embP_of_notMem_range {n' n : ℕ} (e : Fin n' → Fin n) (g : PS k n' d) (c : Fin n) (hc : ∀ b, e b ≠ c)
    (j : Fin d) : pderiv (R := k) (c, j) (ev (embP e) g) = 0 := by
  classical
  refine LogPf.pderiv_ev_zero (cz_embP e) g (c, j) fun b i => ?_
  rw [show embP (k := k) (d := d) e b i = pt k d (e b) i from rfl, LogPf.pderiv_pt, if_neg]
  intro h
  exact hc b (congrArg Prod.fst h)

theorem ev_ptz {n' n : ℕ} (e : Fin n' → Fin n) (b : Fin n') (X : PS k 2 d) :
    ev ![pt k d (e b), 0] X = ev (embP e) (ev ![pt k d b, 0] X) := by
  rw [LogPf.ev_ev (cz_embP e) (cz_ptz b)]
  congr 1
  funext q i
  fin_cases q
  · simp [LogPf.ev_X (cz_embP e), embP, pt]
  · simp [LogPf.ev_zero' (cz_embP e)]

theorem dofN_embP (F : Fin d → PS k 2 d) {n' n : ℕ} (e : Fin n' → Fin n) (he : Function.Injective e) (b : Fin n')
    (u : Fin d → k) (g : PS k n' d) : DofN F (e b) u (ev (embP e) g) = ev (embP e) (DofN F b u g) := by
  unfold DofN
  rw [LogPf.ev_sum (cz_embP e)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LogPf.ev_mul (cz_embP e), LogPf.ev_sum (cz_embP e), pderiv_embP e he]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LogPf.ev_mul (cz_embP e), LogPf.ev_C (cz_embP e), ev_ptz]

section Comm

def cB (G : FGLaw k d) {n : ℕ} (b : Fin n) (u : Fin d → k) : Fin n × Fin d → PS k n d := fun t =>
  if t.1 = b then ev (embP (fun _ : Fin 1 => b)) (WickVanishing.Nab.co G u ((0 : Fin 1), t.2)) else 0

theorem inj1 {n : ℕ} (b : Fin n) : Function.Injective (fun _ : Fin 1 => b) := by
  intro x y _
  exact Subsingleton.elim x y

theorem dofN_vf (G : FGLaw k d) {n : ℕ} (b : Fin n) (u : Fin d → k) (g : PS k n d) :
    DofN G.F b u g = WickVanishing.Nab.vf (cB G b u) g := by
  classical
  unfold DofN WickVanishing.Nab.vf cB
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos rfl]
    congr 1
    unfold WickVanishing.Nab.co
    rw [LogPf.ev_sum (cz_embP _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LogPf.ev_mul (cz_embP _), LogPf.ev_C (cz_embP _)]
    congr 1
    exact ev_ptz (fun _ : Fin 1 => b) 0 _
  · intro c _ hc
    exact Finset.sum_eq_zero fun j _ => by rw [if_neg hc, zero_mul]
  · simp

theorem cB_one (G : FGLaw k d) (u : Fin d → k) : cB G (0 : Fin 1) u = WickVanishing.Nab.co G u := by
  funext t
  have h1 : t.1 = 0 := Subsingleton.elim _ _
  have hp : (embP (k := k) (d := d) (fun _ : Fin 1 => (0 : Fin 1))) = fun j => pt k (n := 1) d j := by
    funext j
    rw [Subsingleton.elim j 0]
    rfl
  simp only [cB, if_pos h1, hp, LogPf.ev_pt]
  rw [show t = ((0 : Fin 1), t.2) from Prod.ext h1 rfl]

theorem dofN_cB_ne (G : FGLaw k d) {n : ℕ} (b c : Fin n) (hbc : b ≠ c) (u v : Fin d → k) (t : Fin n × Fin d) :
    DofN G.F b u (cB G c v t) = 0 := by
  unfold cB
  split_ifs
  · unfold DofN
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [pderiv_ev_embP_of_notMem_range _ _ b (fun _ => Ne.symm hbc) j, mul_zero]
  · unfold DofN
    simp

theorem dofN_comm (G : FGLaw k d) {n : ℕ} (b b' : Fin n) (u v : Fin d → k) (g : PS k n d) :
    DofN G.F b u (DofN G.F b' v g) = DofN G.F b' v (DofN G.F b u g) := by
  classical
  rw [dofN_vf G b, dofN_vf G b', dofN_vf G b', dofN_vf G b, ← sub_eq_zero, WickVanishing.Nab.vf_comm]
  have hz : (fun t => WickVanishing.Nab.vf (cB G b u) (cB G b' v t) - WickVanishing.Nab.vf (cB G b' v) (cB G b u t)) =
      fun _ => (0 : PS k n d) := by
    funext t
    rw [← dofN_vf G b, ← dofN_vf G b']
    by_cases hb : b = b'
    · rw [← hb]
      have hE : ∀ (w : Fin d → k) (X : PS k 1 d),
          DofN G.F b w (ev (embP (fun _ : Fin 1 => b)) X) = ev (embP (fun _ : Fin 1 => b)) (DofN G.F 0 w X) :=
        fun w X => dofN_embP G.F (fun _ : Fin 1 => b) (inj1 b) 0 w X
      unfold cB
      by_cases ht : t.1 = b
      · rw [if_pos ht, if_pos ht, hE, hE, ← LogPf.ev_sub (cz_embP _), dofN_vf G (0 : Fin 1),
          dofN_vf G (0 : Fin 1), cB_one, cB_one, WickVanishing.Nab.co_bracket G u v, LogPf.ev_zero' (cz_embP _)]
      · rw [if_neg ht, if_neg ht]
        unfold DofN
        simp
    · rw [dofN_cB_ne G b b' hb, dofN_cB_ne G b' b (Ne.symm hb), sub_zero]
  rw [hz, WickVanishing.Nab.vf_zeroc]

end Comm

section Fold

variable {n' n : ℕ} (F : Fin d → PS k 2 d)
  (hF : ∀ (b b' : Fin n) (v v' : Fin d → k) (G : PS k n d), DofN F b v (DofN F b' v' G) = DofN F b' v' (DofN F b v G))
  (e : Fin n' → Fin n) (he : Function.Injective e) {ι ι' : Type} [Fintype ι] [Fintype ι']
  (cp : ι → Fin n) (u : ι → Fin d → k) (cp' : ι' → Fin n') (u' : ι' → Fin d → k) (φ : ι' → ι)
  (hφ : Function.Injective φ) (hcp : ∀ l, cp (φ l) = e (cp' l)) (hu : ∀ l, u (φ l) = u' l)
include hF he hφ hcp hu

end Fold

section Val

variable {R : Type} [CommRing R] {O : Type} [CommRing O] [StarRing O] (B : FB R d O) (K : Type) [CommRing K]
  [Algebra ℚ K] [Algebra R K]

end Val

end Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation
end
end
