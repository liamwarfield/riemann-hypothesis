module

public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.KTFiniteDimensional
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def TestRd (σ : c.F →+* ℂ) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ),
    ∃ (k : (U σ).Comp) (x : ((U σ).X k).dom) (u : ℂ), ∀ f ∈ sec Xo c a n,
      cvalR σ (ψ (f p y)) = u * rdU (U σ) f k x.1

def BCEx (σ : c.F →+* ℂ) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ), ∃ z : FrPt Xo c (CAt σ), FrMap ψ y z

def WtC (σ : c.F →+* ℂ) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, ∀ (t : Ix Dw → (CAt σ)ˣ) (y y' : FrPt Xo c (CAt σ)),
    FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def frInv {Ψ : Finset (E →+* ℂ)} (b : Frame Ψ r) : Frame Ψ r := fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

theorem mat_frInv {Ψ : Finset (E →+* ℂ)} (b : Frame Ψ r) (τ : Ψ) : mat (frInv b) τ = (mat b τ)⁻¹ := rfl

theorem mat_rmul {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) (τ : Ψ) : mat (rmul x b) τ = mat x τ * mat b τ := rfl

theorem eq_zero_of_orbit (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x)
    (hΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, P (lact γ x) = X.χ la γ * P x)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (hz : rmul (lact γ x) b ∈ X.dom) (h0 : P (rmul (lact γ x) b) = 0) : P x = 0 := by
  have hbinv : frInv b ∈ Bor X.Ψ r := by
    intro τ
    obtain ⟨hdet, htri⟩ := hb τ
    have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.2 hdet
    refine ⟨?_, ?_⟩
    · rw [mat_frInv]
      exact (Matrix.isUnit_nonsing_inv_det_iff.2 hu).ne_zero
    · intro i j hij
      haveI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ hu
      have hBT : (mat b τ).BlockTriangular id := fun i' j' h' => htri i' j' h'
      exact Matrix.blockTriangular_inv_of_blockTriangular hBT hij
  have hrm : rmul (rmul (lact γ x) b) (frInv b) = lact γ x := by
    funext τ
    show mat (rmul (lact γ x) b) τ * mat (frInv b) τ = mat (lact γ x) τ
    rw [mat_rmul, mat_frInv, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hb τ).1), Matrix.mul_one]
  have h1 : P (lact γ x) = 0 := by
    have h2 := hB _ hz (frInv b) hbinv
    rw [hrm, h0, mul_zero] at h2
    exact h2
  rw [hΓ γ hγ x hx] at h1
  obtain ⟨n, hn, hχ⟩ := X.χ_fin la
  have hne : X.χ la γ ≠ 0 := by
    intro h
    have h3 := hχ γ hγ
    rw [h, zero_pow hn.ne'] at h3
    exact zero_ne_one h3
  exact (mul_eq_zero.1 h1).resolve_left hne

theorem eqv_holSub {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X}
    (hP : P ∈ holSub X la) :
    (∀ k, ∀ x ∈ (X k).dom, ∀ b ∈ Bor (X k).Ψ r, P k (rmul x b) = bchar (la k) b * P k x) ∧
      (∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = (X k).χ (la k) γ * P k x) := by
  replace hP : P ∈ Submodule.span ℂ {Q | IsHolCusp X la Q} := hP
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
    have hQ' : IsHolCusp X la Q := hQ
    exact ⟨fun k x hx b hb => (hQ' k).1.1.2.1 x hx b hb, fun k γ hγ x hx => (hQ' k).1.1.2.2 γ hγ x hx⟩
  | zero => exact ⟨fun k x _ b _ => by simp, fun k γ _ x _ => by simp⟩
  | add Q R _ _ hQ hR =>
    refine ⟨fun k x hx b hb => ?_, fun k γ hγ x hx => ?_⟩
    · simp only [Pi.add_apply]
      rw [hQ.1 k x hx b hb, hR.1 k x hx b hb]
      ring
    · simp only [Pi.add_apply]
      rw [hQ.2 k γ hγ x hx, hR.2 k γ hγ x hx]
      ring
  | smul a Q _ hQ =>
    refine ⟨fun k x hx b hb => ?_, fun k γ hγ x hx => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hQ.1 k x hx b hb]
      ring
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hQ.2 k γ hγ x hx]
      ring

variable {D : D7} {Comp : Type} {X : Comp → Data E r} (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r)
  (mu : GA D V → ℂ)

def AdelAut : Prop :=
  ∀ (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X), IsHolCusp X la P →
    (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P)

def QuotSupp : Prop :=
  ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → onQ V φ =ᵐ[muQ1 V] 0 → ∀ g, φ g = 0

variable {V dict mu}

theorem adelAut_holSub (h : AdelAut V dict mu) (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X} (hP : P ∈ holSub X la) :
    (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P) := by
  replace hP : P ∈ Submodule.span ℂ {Q | IsHolCusp X la Q} := hP
  induction hP using Submodule.span_induction with
  | mem Q hQ => exact h la Q hQ
  | zero =>
    refine ⟨fun γ _ g => ?_, ?_⟩
    · simp only [map_zero, Pi.zero_apply]
    · rw [map_zero]
      exact continuous_const
  | add Q R _ _ hQ hR =>
    refine ⟨fun γ hγ g => ?_, ?_⟩
    · simp only [map_add (f := _), Pi.add_apply, hQ.1 γ hγ g, hR.1 γ hγ g]
    · rw [map_add (f := _)]
      exact hQ.2.add hR.2
  | smul a Q _ hQ =>
    refine ⟨fun γ hγ g => ?_, ?_⟩
    · simp only [map_smul, Pi.smul_apply, hQ.1 γ hγ g]
    · rw [map_smul]
      exact hQ.2.const_smul a

theorem onQ_eq_lift (φ : GA D V → ℂ) (hL : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) :
    onQ V φ = Quotient.lift φ (fun a b hab => by
      have h' : b * a⁻¹ ∈ GQ V := QuotientGroup.rightRel_apply.1 hab
      have := hL _ h' a
      rw [inv_mul_cancel_right] at this
      exact this.symm) := by
  funext q
  exact congrArg (Quotient.lift φ _) (Quotient.out_eq q)

theorem adelMeas_of_aut {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {V : HSp D}
    {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ}
    (h : AdelAut V dict mu) : AdelMeas U σ V dict mu := by
  intro la P hP
  obtain ⟨hL, hc⟩ := h la P hP
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [onQ_eq_lift _ hL]
  refine Measurable.aestronglyMeasurable ?_
  exact measurable_from_quotient.2 hc.measurable

theorem aeDom_of_aut {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {V : HSp D}
    {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)}
    {th : ∀ k, ((U σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hA : AdelAut V dict mu) (hQ : QuotSupp V) (hmu : MuUnit V dict mu) (hd : DictIsUnif V dict Kf th hr) :
    AeDom U σ V dict mu := by
  intro la P hP h0 k x hx
  have hA' := adelAut_holSub hA la hP
  have hz : ∀ g, adel V dict mu P g = 0 := hQ _ hA'.2 hA'.1 h0
  obtain ⟨-, -, -, hdom, hsurj, -⟩ := hd
  obtain ⟨g, γ, hγ, b, hb, hg⟩ := hsurj k x hx
  have hm : mu g ≠ 0 := by
    intro h
    have h1 := hmu.2.1 g
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have h1 : mu g * P (dict g).1 (dict g).2 = 0 := hz g
  have h2 : P (dict g).1 (dict g).2 = 0 := (mul_eq_zero.1 h1).resolve_left hm
  have h3 := hdom g
  rw [hg] at h2 h3
  have hE := eqv_holSub (U σ).X la hP
  exact eq_zero_of_orbit ((U σ).X k) (la k) (P k) (hE.1 k) (hE.2 k) hx hγ hb h3 h2

end Adelic

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def PartIAt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → l.GoodAt p →
    ∃ Y : Model Xo c (c.V W).subtype, Y.N3 ∧ PushInvertible Y.t.G Y.t.PP.L

theorem exists_lieElement_middleBlockPart (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) :
    ∃ W : ValuationSubring ℂ, (∀ x : 𝓞 c.F, x ∈ la.asIdeal → (((algebraMap (𝓞 c.F) c.F x : c.F) : ℂ)) ∈ W.nonunits) ∧
      ∀ x : c.F, (x : ℂ) ∈ W → la.valuation c.F x ≤ 1 := by
  set V := (la.valuation c.F).valuationSubring with hVdef
  let g : V →+* ℂ := c.F.val.toRingHom.comp V.subtype
  have hg : Function.Injective g := fun a b h => Subtype.ext (c.F.val.injective h)
  let e : V ≃+* g.range := RingEquiv.ofBijective g.rangeRestrict ⟨fun a b h => hg (congrArg (fun z : g.range => (z : ℂ)) h),
    g.rangeRestrict_surjective⟩
  have hmax : ((IsLocalRing.maximalIdeal V).map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
  obtain ⟨W, hAW, hIW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hmax.ne_top
  have hnon : ∀ y : V, y ∈ IsLocalRing.maximalIdeal V → g y ∈ W.nonunits := fun y hy =>
    hIW ⟨e y, Ideal.mem_map_of_mem _ hy, rfl⟩
  refine ⟨W, fun x hx => ?_, fun x hx => ?_⟩
  · have hxV : algebraMap (𝓞 c.F) c.F x ∈ V := by
      rw [hVdef, Valuation.mem_valuationSubring_iff, HeightOneSpectrum.valuation_of_algebraMap]
      exact la.intValuation_le_one x
    have hxm : (⟨_, hxV⟩ : V) ∈ IsLocalRing.maximalIdeal V := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
      have h1 : la.valuation c.F (algebraMap (𝓞 c.F) c.F x) < 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap]; exact (la.intValuation_lt_one_iff_mem x).2 hx
      have h2 : la.valuation c.F ((w : V) : c.F) ≤ 1 := w.2
      have h3 := congrArg (fun z : V => la.valuation c.F (z : c.F)) hw
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one, map_mul, map_one] at h3
      have h4 : la.valuation c.F (algebraMap (𝓞 c.F) c.F x) * la.valuation c.F ((w : V) : c.F) < 1 :=
        lt_of_lt_of_le (mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 h2) le_rfl
      rw [h3] at h4
      exact lt_irrefl _ h4
    exact hnon _ hxm
  · by_contra hv
    push_neg at hv
    have hx0 : x ≠ 0 := by rintro rfl; simp at hv
    have hiV : x⁻¹ ∈ V := by
      rw [hVdef, Valuation.mem_valuationSubring_iff, map_inv₀]
      exact (inv_lt_one_of_one_lt₀ hv).le
    have him : (⟨x⁻¹, hiV⟩ : V) ∈ IsLocalRing.maximalIdeal V := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
      have h1 : (w : c.F) = x := by
        have := congrArg (fun z : V => (z : c.F)) hw
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
        field_simp at this
        exact this
      have h2 : la.valuation c.F ((w : V) : c.F) ≤ 1 := w.2
      rw [h1] at h2
      exact absurd h2 (not_le.2 hv)
    have h5 := hnon _ him
    rw [ValuationSubring.mem_nonunits_iff] at h5
    have h6 := (ValuationSubring.valuation_le_one_iff W _).2 hx
    have h7 : g ⟨x⁻¹, hiV⟩ = ((x : ℂ))⁻¹ := by
      show ((x⁻¹ : c.F) : ℂ) = _
      exact map_inv₀ c.F.val x
    rw [h7, map_inv₀] at h5
    have hW0 : W.valuation (x : ℂ) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact_mod_cast hx0
    exact absurd ((inv_lt_one₀ (zero_lt_iff.2 hW0)).1 h5) (not_lt.2 h6)

theorem modelAtSt_of {Xo : Moduli Dw l} {c : Coeff l} (hI : PartIAt Xo c) (hgood : ∀ p : ℕ, p.Prime → l.GoodAt p)
    (la : HeightOneSpectrum (𝓞 c.F)) : ModelAtSt Xo c la := by
  obtain ⟨W, hWnon, hWkey⟩ := exists_lieElement_middleBlockPart c la
  have hp : (Formalism.MainNotions.WeightAlgebra.resCh la).Prime := resCh_prime la
  have hmem : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : 𝓞 c.F) ∈ la.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  have hpW : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : ℂ) ∈ W.nonunits := by
    have := hWnon _ hmem
    simpa using this
  obtain ⟨Y, hN3, hPI⟩ := hI _ W hp hpW (hgood _ hp)
  refine ⟨c.V W, inferInstance, (c.V W).subtype, Y, hN3, hPI, fun Tc io e ho => ?_⟩
  have hint : ∀ x : c.V W, io (x : c.F) ∈ (algebraMap Tc.V Tc.Fr).range := by
    intro x
    have hx : la.valuation c.F (x : c.F) ≤ 1 := hWkey _ x.2
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have hv : v = IsDiscreteValuationRing.maximalIdeal Tc.V :=
      HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal v.isMaximal)
    subst hv
    by_cases hx0 : (x : c.F) = 0
    · rw [hx0, map_zero, map_zero]; exact zero_le
    have hvx0 : la.valuation c.F (x : c.F) ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
    have hla : 0 ≤ vLa la (x : c.F) := by
      unfold vLa
      rw [← WithZero.exp_log hvx0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hx
      linarith
    have hvV : 0 ≤ vV Tc.V (io (x : c.F)) := by
      rw [ho.2 (x : c.F)]
      positivity
    have hio0 : io (x : c.F) ≠ 0 := (map_ne_zero io).2 hx0
    have hval0 : valV Tc.V (io (x : c.F)) ≠ 0 := valV_ne_zero hio0
    show valV Tc.V (io (x : c.F)) ≤ 1
    unfold vV at hvV
    rw [← WithZero.exp_log hval0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    linarith
  let f : c.V W →+* (algebraMap Tc.V Tc.Fr).range := (io.comp (c.V W).subtype).codRestrict _ hint
  let eq : Tc.V ≃+* (algebraMap Tc.V Tc.Fr).range := RingEquiv.ofBijective (algebraMap Tc.V Tc.Fr).rangeRestrict
    ⟨fun a b h => IsFractionRing.injective Tc.V Tc.Fr (congrArg (fun z : (algebraMap Tc.V Tc.Fr).range => (z : Tc.Fr)) h),
      (algebraMap Tc.V Tc.Fr).rangeRestrict_surjective⟩
  refine ⟨eq.symm.toRingHom.comp f, ?_⟩
  ext x
  have := congrArg (fun z : (algebraMap Tc.V Tc.Fr).range => (z : Tc.Fr)) (eq.apply_symm_apply (f x))
  exact this

theorem goodAt_of_two_primes {g0 g1 : ℕ} (hM : l.M = g0 * g1) (h0 : g0.Prime) (h1 : g1.Prime)
    (hne : g0 ≠ g1) (p : ℕ) (hp : p.Prime) : l.GoodAt p := by
  unfold Level.GoodAt
  have hodd : Odd (g0 * g1) := hM ▸ l.odd
  have h3 : 3 ≤ g0 * g1 := hM ▸ l.three_le
  have o0 : Odd g0 := (Nat.odd_mul.1 hodd).1
  have o1 : Odd g1 := (Nat.odd_mul.1 hodd).2
  have t0 : 3 ≤ g0 := by
    have := h0.two_le
    have := Nat.odd_iff.1 o0
    omega
  have t1 : 3 ≤ g1 := by
    have := h1.two_le
    have := Nat.odd_iff.1 o1
    omega
  rw [hM, Nat.factorization_mul h0.ne_zero h1.ne_zero, Finsupp.add_apply, h0.factorization, h1.factorization]
  by_cases e0 : p = g0
  · have e : (Finsupp.single g0 1 : ℕ →₀ ℕ) p + (Finsupp.single g1 1 : ℕ →₀ ℕ) p = 1 := by
      simp [Finsupp.single_apply, e0, hne, hne.symm]
    rw [e, pow_one, e0, Nat.mul_div_cancel_left g1 h0.pos]
    exact t1
  · by_cases e1 : p = g1
    · have e : (Finsupp.single g0 1 : ℕ →₀ ℕ) p + (Finsupp.single g1 1 : ℕ →₀ ℕ) p = 1 := by
        simp [Finsupp.single_apply, e1, hne, hne.symm]
      rw [e, pow_one, e1, Nat.mul_div_cancel g0 h1.pos]
      exact t0
    · have e : (Finsupp.single g0 1 : ℕ →₀ ℕ) p + (Finsupp.single g1 1 : ℕ →₀ ℕ) p = 0 := by
        simp [Finsupp.single_apply, e0, e1, Ne.symm e0, Ne.symm e1]
      rw [e, pow_zero, Nat.div_one]
      exact h3

theorem partIAt_of (hP : PartI) (hN : N1ab) (Xo : Moduli Dw l) (c : Coeff l) (hpq : 1 ≤ Dw.p + Dw.q) : PartIAt Xo c := by
  classical
  obtain ⟨-, hI⟩ := hP
  let Xf : ∀ l' : Level H, Moduli Dw l' := fun l' =>
    if h : l' = l then h ▸ Xo else Classical.choice (hN E H Dw l' hpq)
  obtain ⟨Y, hY, -⟩ := hI E H Dw hpq Xf
  intro p W hp hW hg
  obtain ⟨hN2, hrest⟩ := hY p W hp hW
  let i : Idx H p := ⟨l, c, hg⟩
  have hPIi := (hN2.1 i).2.2.1
  have hN3 := (hrest i).2.1
  have hX : Xf l = Xo := by simp [Xf]
  have key : ∀ (X' : Moduli Dw l), X' = Xo → ∀ Y' : Model X' c (c.V W).subtype, Y'.N3 →
      PushInvertible Y'.t.G Y'.t.PP.L → ∃ Y : Model Xo c (c.V W).subtype, Y.N3 ∧ PushInvertible Y.t.G Y.t.PP.L := by
    rintro X' rfl Y' h1 h2
    exact ⟨Y', h1, h2⟩
  exact key (Xf l) hX (Y p W hp hW i) hN3 hPIi

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.HtXfer
section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.HeightsOfHtConcl
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace Formalism.MainNotions.Gaps.HeightData

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def toHtData (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ) : HtData where
  K := B.KO
  D := WeightFamilies.dimY D j
  δ := G.del
  i := G.iet
  g0 := (g0 D : ℝ)
  L := wL.size
  G := Gc
  PH := PH
  Prw := Prw
  Pet := Pet
  S k := WeightFamilies.meanLogSup B (G.th' k)
  etaPart := j < D.R.m
  Op la := Op X la G.N
  SectionSheafQuotient la := SectionSheafQuotient X la G.w wF
  A0 la := (Qf la).A0
  t la := tL G la
  Pts la := PtsG G la
  ep la ζ := ep (unifO X la G.N) ζ
  f _ ζ := fdeg ζ
  vEt la ζ := (X.vAt la ((Qf la).y ζ) (X.inc _ G.et)).toReal

theorem heights_of_htConcl (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ)
    (h : HtConcl (toHtData G Qf Gc PH Prw Pet)) : Heights Qf Gc PH Prw Pet := by
  exact h

end Formalism.MainNotions.Gaps.HeightData
end
end

noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.HeightData NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
  {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra B.KO (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra B.KO (A c)]
  [∀ c, Algebra (𝓞 B.KO) (A c)] {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

theorem lN_nonneg' (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    0 ≤ Formalism.MainNotions.Gaps.HeightData.lN K la := by
  unfold Formalism.MainNotions.Gaps.HeightData.lN
  refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
  have h0 : Ideal.absNorm la.asIdeal ≠ 0 := fun h => la.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast Nat.one_le_iff_ne_zero.2 h0

theorem htConcl_toHtData_of (d : Data B.KO ι Ω WT A) (hd : d.AxH 𝒜) (hs : d.S1)
    (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ)
    (hD : (d.htOf hd hs).D = WeightFamilies.dimY D j) (hδ : (d.htOf hd hs).δ = G.del) (hi : (d.htOf hd hs).i = G.iet)
    (hg0 : (d.htOf hd hs).g0 = (g0 D : ℝ)) (hL : (d.htOf hd hs).L = wL.size) (hG : (d.htOf hd hs).G = Gc)
    (hPH : (d.htOf hd hs).PH = PH) (hPrw : (d.htOf hd hs).Prw = Prw) (hPet : (d.htOf hd hs).Pet = Pet)
    (hS : ∑ k, (d.htOf hd hs).S k ≤ ∑ k, WeightFamilies.meanLogSup B (G.th' k))
    (hI : ∀ la : HeightOneSpectrum (𝓞 B.KO), (toHtData G Qf Gc PH Prw Pet).Ila la ≤ (d.htOf hd hs).Ila la)
    (hN : ∀ la : HeightOneSpectrum (𝓞 B.KO), (toHtData G Qf Gc PH Prw Pet).Net la = (d.htOf hd hs).Net la)
    (h : Formalism.MainNotions.Gaps.HeightData.HtConcl (d.htOf hd hs)) :
    Formalism.MainNotions.Gaps.HeightData.HtConcl (toHtData G Qf Gc PH Prw Pet) := by
  obtain ⟨hfin, hsum, hineq, heta⟩ := h
  have hle : ∀ la : HeightOneSpectrum (𝓞 B.KO),
      (((toHtData G Qf Gc PH Prw Pet).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la ≤
        (((d.htOf hd hs).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la := fun la =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast ENat.toNat_le_toNat (hI la) (hfin la)) (lN_nonneg' _ la)
  have hsum' : Summable fun la : HeightOneSpectrum (𝓞 B.KO) =>
      (((toHtData G Qf Gc PH Prw Pet).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la :=
    Summable.of_nonneg_of_le (fun la => mul_nonneg (Nat.cast_nonneg _) (lN_nonneg' _ la)) hle hsum
  have hDr : ((d.htOf hd hs).D : ℝ) = (WeightFamilies.dimY D j : ℝ) := by exact_mod_cast hD
  have hδr : ((d.htOf hd hs).δ : ℝ) = (G.del : ℝ) := by exact_mod_cast hδ
  have hir : ((d.htOf hd hs).i : ℝ) = (G.iet : ℝ) := by exact_mod_cast hi
  refine ⟨fun la => ne_top_of_le_ne_top (hfin la) (hI la), hsum', ?_, fun he => ?_⟩
  · have ht := Summable.tsum_le_tsum hle hsum' hsum
    have hineq' : 2 * ∑' la : HeightOneSpectrum (𝓞 B.KO),
          (((d.htOf hd hs).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la ≤
        (G.del : ℝ) * Real.log G.del + 2 * ∑ k, (d.htOf hd hs).S k +
        8 / 3 * (WeightFamilies.dimY D j : ℝ) * ((WeightFamilies.dimY D j : ℝ) + 4) * G.del * Prw * wL.size +
        2 * ((WeightFamilies.dimY D j : ℝ) + 4) * ((WeightFamilies.dimY D j : ℝ) + 1) * G.del * (2 * Gc + 6 * PH) * wL.size := by
      rw [hDr, hδr, hL, hG, hPH, hPrw] at hineq
      exact hineq
    show 2 * ∑' la : HeightOneSpectrum (𝓞 B.KO),
          (((toHtData G Qf Gc PH Prw Pet).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la ≤
        (G.del : ℝ) * Real.log G.del + 2 * ∑ k, WeightFamilies.meanLogSup B (G.th' k) +
        8 / 3 * (WeightFamilies.dimY D j : ℝ) * ((WeightFamilies.dimY D j : ℝ) + 4) * G.del * Prw * wL.size +
        2 * ((WeightFamilies.dimY D j : ℝ) + 4) * ((WeightFamilies.dimY D j : ℝ) + 1) * G.del * (2 * Gc + 6 * PH) * wL.size
    linarith
  · obtain ⟨hsN, hbN⟩ := heta trivial
    rw [hir, hg0, hDr, hδr, hG, hPH, hL, hPrw, hPet] at hbN
    have e : (fun la : HeightOneSpectrum (𝓞 B.KO) =>
          (toHtData G Qf Gc PH Prw Pet).Net la * Formalism.MainNotions.Gaps.HeightData.lN B.KO la) =
        fun la : HeightOneSpectrum (𝓞 B.KO) => (d.htOf hd hs).Net la * Formalism.MainNotions.Gaps.HeightData.lN B.KO la :=
      funext fun la => by rw [hN la]
    refine ⟨?_, ?_⟩
    · show Summable fun la : HeightOneSpectrum (𝓞 B.KO) =>
        (toHtData G Qf Gc PH Prw Pet).Net la * Formalism.MainNotions.Gaps.HeightData.lN B.KO la
      rw [e]; exact hsN
    · show (∑' la : HeightOneSpectrum (𝓞 B.KO),
          (toHtData G Qf Gc PH Prw Pet).Net la * Formalism.MainNotions.Gaps.HeightData.lN B.KO la) / (G.iet : ℝ) ≤
        (g0 D : ℝ) * (((WeightFamilies.dimY D j : ℝ) + 1) * G.del * (2 * Gc + 6 * PH) * wL.size +
          4 / 3 * (WeightFamilies.dimY D j : ℝ) * G.del * Prw * wL.size) + G.del * Pet
      rw [e]; exact hbN

section Ties

variable (d : Data B.KO ι Ω WT A) (hd : d.AxH 𝒜) (hs : d.S1)
    (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ)

def IlaTie : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 B.KO), (toHtData G Qf Gc PH Prw Pet).Ila la ≤ (d.htOf hd hs).Ila la

def NetTie : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 B.KO), (toHtData G Qf Gc PH Prw Pet).Net la = (d.htOf hd hs).Net la

end Ties

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CoreExists
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def parameterOfRecord (D : D7) (hF : OFull D) (hz : OZeta D)
    (hDat : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI) (hN : N1ab) : Par D where
  H := hostOf D (unramBridge D.host.E (cmUnram_conj D))
  l := levelG D (hU := unramBridge D.host.E (cmUnram_conj D))
  c := coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz
  Dw := datumAtLift D (unramBridge D.host.E (cmUnram_conj D)) hDat
  Xo := fun j => Classical.choice (hN D.host.E (hostOf D (unramBridge D.host.E (cmUnram_conj D)))
    (datumAtLift D (unramBridge D.host.E (cmUnram_conj D)) hDat j) (levelG D (hU := unramBridge D.host.E (cmUnram_conj D)))
    (datumAtLift_pq_pos D (unramBridge D.host.E (cmUnram_conj D)) hDat j))
  eO := eOf D hF

variable {D : D7}

def levSet (V : HSp D) (N : ℕ) : Set (GA D V) :=
  {k | k ∈ GfC V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y}

def kfW (V : HSp D) (N : ℕ) : Subgroup (GA D V) := Subgroup.closure (levSet V N)

def LevGrp (V : HSp D) (N : ℕ) : Prop := ∀ k ∈ kfW V N, k ∈ levSet V N

section One

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def RdIndep1 (U : Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (k : ℕ), Dom a k → ∀ (n : ℕ) (b : Fin n → Rul Xo c), (∀ i, b i ∈ sec Xo c a k) →
    LinearIndependent c.F b → LinearIndependent ℂ (fun i => rdU U (b i))

def HolFD1 (U : Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional ℂ (holSub U.X (laU U a n))

def RdDomInj1 (U : Unf Xo c σ r) : Prop :=
  ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, rdU U f ∈ holSub U.X (laU U a n) →
    (∀ k, ∀ x ∈ (U.X k).dom, rdU U f k x = 0) → f = 0

def AdelMeas1 (U : Unf Xo c σ r) (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ) : Prop :=
  ∀ (la : ∀ k, Wt (U.X k).Ψ r) (P : FDSec U.X), IsHolCusp U.X la P →
    AEStronglyMeasurable (onQ V (adel V dict mu P)) (muQ1 V)

def AeDom1 (U : Unf Xo c σ r) (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ) : Prop :=
  ∀ (la : ∀ k, Wt (U.X k).Ψ r) (P : FDSec U.X), P ∈ holSub U.X la →
    onQ V (adel V dict mu P) =ᵐ[muQ1 V] 0 → ∀ k, ∀ x ∈ (U.X k).dom, P k x = 0

end One

abbrev PkgT (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) : Type 1 :=
  Σ U : Unf (Q.Xo j) Q.c σ D.R.r, (GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r) × (GA D (D.sp.W j) → ℂ)

structure PkgOK (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) (U : Unf (Q.Xo j) Q.c σ D.R.r)
    (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r) (mu : GA D (D.sp.W j) → ℂ) : Prop where

  unf : IsUnf U

  unTest : ∀ k x, FromTest (K := Q.c.F) (fun S _ _ => FrPt (Q.Xo j) Q.c S) (fun φ y z => FrMap φ y z) (U.un k x)

  chiTriv : ∀ a n, Dom a n → ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1

  dictU : ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif (D.sp.W j) dict (kfW (D.sp.W j) (D.host.g 0 * D.host.g 1)) th hr

  xiAbs : ∀ k (τ : D.host.E →+* ℂ), ‖τ (U.X k).ξ0‖ = xiR D

  muUnit : MuUnit (D.sp.W j) dict mu
  muCont : Continuous mu

  rdIndep : RdIndep1 U
  holFD : HolFD1 U

  rdDomInj : RdDomInj1 U

  adelMeas : AdelMeas1 U (D.sp.W j) dict mu

  aeDom : AeDom1 U (D.sp.W j) dict mu

  latZ : FJ.LatZ U.X (WeightFamilies.rho D j)
  cuNe : FJ.CuNeF U.X (WeightFamilies.rho D j)
  expo : FJ.ExpoMatch U.X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1)

def FamOK (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) : Prop :=
  ∀ (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)), IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty →
    Nonempty (FamilyUnif (Q.Xo j) (σ.comp (IntermediateField.inclusion Q.c.le).toRingHom) ty)

def HalfPb (Q : Par D) : Prop :=
  ∃ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) ∧
    Q.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

structure LawsRest (Q : Par D) : Prop where

  evalWD : ∀ j, InR D j → EvalWD (K := Q.c.F) (fun S _ _ => FrPt (Q.Xo j) Q.c S) (fun φ y z => FrMap φ y z)

  wtField : ∀ j, InR D j → WtField (Q.Xo j) Q.c
  intDiagUnit : ∀ j, InR D j → IntDiagUnit (Q.Xo j) Q.c

  algPtLa : ∀ j, InR D j → AlgPtLa (Q.Xo j) Q.c
  intFrExt : ∀ j, InR D j → IntFrExt (Q.Xo j) Q.c

  m5 : SiegelSpaceAlgebra (E := D.host.E)

  volTie : VolTieG D

  levGrp : ∀ j, InR D j → LevGrp (D.sp.W j) (D.host.g 0 * D.host.g 1)

  half : HalfPb Q

  pkg : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → FamOK Q j σ → ∃ U dict mu, PkgOK Q j σ U dict mu

  dataAll : ∀ j σ, Nonempty (PkgT Q j σ)

section Build

variable {Q : Par D}

theorem pkgEx (hRs : LawsRest Q) (hfam : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → FamOK Q j σ) (j : ℕ)
    (σ : Q.c.F →+* ℂ) : ∃ p : PkgT Q j σ, InR D j → GoodEmb Q.c σ → PkgOK Q j σ p.1 p.2.1 p.2.2 := by
  by_cases hj : InR D j
  · by_cases hσ : GoodEmb Q.c σ
    · obtain ⟨U, dict, mu, h⟩ := hRs.pkg j hj σ hσ (hfam j hj σ hσ)
      exact ⟨⟨U, dict, mu⟩, fun _ _ => h⟩
    · exact ⟨Classical.choice (hRs.dataAll j σ), fun _ h => absurd h hσ⟩
  · exact ⟨Classical.choice (hRs.dataAll j σ), fun h => absurd h hj⟩

def pkgOf (hRs : LawsRest Q) (hfam : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → FamOK Q j σ) (j : ℕ)
    (σ : Q.c.F →+* ℂ) : PkgT Q j σ := (pkgEx hRs hfam j σ).choose

end Build

theorem datHolds (D : D7) : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI :=
  fun j hj => ⟨datInt_holds D j,
    { unimod := efW_unimod_holds D j _, rank := latW_rank D j hj, dom := datDom_holds D j hj _ }⟩

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.NormalizedValuationMul
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

structure SecPt (ζ : PtsG G la) (y : E.Pt' la) where

  T : CDVR

  ep_pos : 0 < ep (unifO (xplus X E hM) la G.N) ζ

  ev : Rp (xplus X E hM) la G.N →+* T.Fr

  hv : ∀ (w : WeightFamilies.Wt D j) (F : B.Cusp j w), E.vAt' la y (X.inc w F) =
    nval T.V (ep (unifO (xplus X E hM) la G.N) ζ) (ev (emb (xplus X E hM) la G.N (X.inc w F)))

  onS : ∀ i : Fin (WeightFamilies.dimY D j), ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w i.succ) = 0

  s0 : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0))

  ord : ∀ x : ↥(Frac0 (xplus X E hM) la G.w),
    toE (ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w x)) =
      nval T.V 1 (IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) s0 (x : Lw (xplus X E hM) la G.w))

structure FromW (ζ : PtsG G la) (y : E.Pt' la) extends SecPt ζ y where

  ι : Loc ζ →+* T.V

  loc : IsLocalHom ι
  unr : ∃ ϖ : Loc ζ, Irreducible ϖ ∧ Irreducible (ι ϖ)

  evW : ∀ (x : ↥(Frac0 (xplus X E hM) la G.w)) (a : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))),
    toOsK (xplus X E hM) la G.w x = (a : OsK (xplus X E hM) la G.w) →
    IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) toSecPt.s0 (x : Lw (xplus X E hM) la G.w) =
      algebraMap T.V T.Fr (ι (algebraMap _ (Loc ζ) a))

def secQ (y : PtsG G la → E.Pt' la) (hs : ∀ ζ, SecPt ζ (y ζ)) (g0 : B.Cusp j wF) : LocalPointData G la where
  y ζ := .inr (y ζ)
  g0 := g0
  c ζ := vV (hs ζ).T.V ((hs ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)))

def InTieSecSt : Prop :=
  ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E)
    (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B)
    (y : PtsG G la → E.Pt' la) (hs : ∀ ζ, SecPt ζ (y ζ)) (g0 : B.Cusp j wF),
    (∀ ζ, (xplus X E hM).depth S.sW wL la (.inr (y ζ)) =
      nval (hs ζ).T.V (ep (unifO (xplus X E hM) la G.N) ζ) ((hs ζ).ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0))) →
    (j < D.R.m → ∀ ζ, (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc _ G.et)) ≠ 0) →
    (∀ ζ, (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    IsGen (OsK (xplus X E hM) la G.w) (resF G la g0) →
    (secQ y hs g0).InTie S

section Nval

variable {T : CDVR}

lemma vV_one' : vV T.V (1 : T.Fr) = 0 := by simp [vV]

lemma vV_inv' {b : T.Fr} (hb : b ≠ 0) : vV T.V b⁻¹ = - vV T.V b := by
  have h := vV_mul (V := T.V) hb (inv_ne_zero hb)
  rw [mul_inv_cancel₀ hb, vV_one'] at h
  omega

lemma vV_pow' {b : T.Fr} (hb : b ≠ 0) (k : ℕ) : vV T.V (b ^ k) = k * vV T.V b := by
  induction k with
  | zero => simp [vV_one']
  | succ n ih => rw [pow_succ, vV_mul (pow_ne_zero n hb) hb, ih]; push_cast; ring

lemma nval_frac {e : ℕ} (he : 0 < e) (a b : T.Fr) (hb : b ≠ 0) (k : ℕ) :
    nval T.V 1 (a * (b⁻¹) ^ k) = (e : EReal) * (nval T.V e a - (k : EReal) * nval T.V e b) := by
  rw [nval_of_ne hb]
  by_cases ha : a = 0
  · subst ha
    rw [zero_mul, nval_zero, nval_zero]
    have hk : (k : EReal) * (((vV T.V b : ℝ) / e : ℝ) : EReal) = ((k * ((vV T.V b : ℝ) / e) : ℝ) : EReal) := by
      norm_cast
    rw [hk, EReal.top_sub_coe, EReal.mul_top_of_pos (by exact_mod_cast he)]
  · have hab : a * (b⁻¹) ^ k ≠ 0 := mul_ne_zero ha (pow_ne_zero k (inv_ne_zero hb))
    rw [nval_of_ne hab, nval_of_ne ha, vV_mul ha (pow_ne_zero k (inv_ne_zero hb)), vV_pow' (inv_ne_zero hb),
      vV_inv' hb]
    have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    have : (((vV T.V a : ℤ) + (k : ℤ) * -vV T.V b : ℤ) : ℝ) / ((1 : ℕ) : ℝ) =
        (e : ℝ) * ((vV T.V a : ℝ) / e - k * ((vV T.V b : ℝ) / e)) := by
      push_cast; field_simp; ring
    rw [this]
    norm_cast

lemma e_mul_nval {e : ℕ} (he : 0 < e) (x : T.Fr) : (e : EReal) * nval T.V e x = nval T.V 1 x := by
  by_cases hx : x = 0
  · subst hx; rw [nval_zero, nval_zero, EReal.mul_top_of_pos (by exact_mod_cast he)]
  · rw [nval_of_ne hx, nval_of_ne hx]
    have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    have : (e : ℝ) * ((vV T.V x : ℝ) / e) = (vV T.V x : ℝ) / ((1 : ℕ) : ℝ) := by
      rw [Nat.cast_one, div_one]; field_simp
    rw [← this]; norm_cast

end Nval

lemma normalized_valuation_mul {T : CDVR} {e : ℕ} (he : 0 < e) (b : T.Fr) (hb : b ≠ 0) :
    (e : ℝ) * (nval T.V e b).toReal = (vV T.V b : ℝ) := by
  rw [nval_of_ne hb, EReal.toReal_coe]
  have : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  field_simp

lemma toE_add_coe (a : WithTop ℤ) (n : ℤ) : toE (a + (n : WithTop ℤ)) = toE a + ((n : ℝ) : EReal) := by
  cases a with
  | top => simp [toE]
  | coe m =>
    show toE ((m + n : ℤ) : WithTop ℤ) = toE (m : WithTop ℤ) + ((n : ℝ) : EReal)
    simp only [toE]; push_cast; rfl

section Lift

variable {ζ : PtsG G la} {y₀ : E.Pt' la} (h : SecPt ζ y₀)

abbrev SecPt.lift : Lw (xplus X E hM) la G.w →+* h.T.Fr :=
  IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) h.s0

lemma SecPt.lift_alg (r : Rp (xplus X E hM) la G.N) : h.lift (algebraMap _ _ r) = h.ev r :=
  IsLocalization.lift_eq _ r

lemma SecPt.lift_w0inv : h.lift (w0inv (xplus X E hM) la G.w) = (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0))⁻¹ := by
  have := congrArg h.lift (section_mul_inverse_eq_one (xplus X E hM) la G.w)
  rw [map_mul, h.lift_alg, map_one] at this
  exact eq_inv_of_mul_eq_one_right this

lemma SecPt.lift_frac (k : ℕ) (g : Rp (xplus X E hM) la G.N) :
    h.lift (frac (xplus X E hM) la G.w k g) = h.ev g * (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0))⁻¹ ^ k := by
  rw [frac_apply, map_mul, map_pow, h.lift_alg, h.lift_w0inv]

lemma SecPt.lift_Jid {r : ↥(Frac0 (xplus X E hM) la G.w)} (hr : r ∈ Jid (xplus X E hM) la G.w) :
    h.lift (r : Lw (xplus X E hM) la G.w) = 0 := by
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [coe_sfr, h.lift_frac, h.onS i, zero_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [Subalgebra.coe_add, map_add (f := _), hx, hy, add_zero]
  | smul a x _ hx => rw [smul_eq_mul, Subalgebra.coe_mul, map_mul, hx, mul_zero]

lemma SecPt.lift_JHK {u : WeightFamilies.Wt D j} {z : ↥(HK (xplus X E hM) la G.w u)}
    (hz : z ∈ Jid (xplus X E hM) la G.w • (⊤ : Submodule ↥(Frac0 (xplus X E hM) la G.w) ↥(HK (xplus X E hM) la G.w u))) :
    h.lift (z : Lw (xplus X E hM) la G.w) = 0 := by
  refine Submodule.smul_induction_on
    (p := fun z : ↥(HK (xplus X E hM) la G.w u) => h.lift (z : Lw (xplus X E hM) la G.w) = 0) hz ?_ ?_
  · intro r hr m _
    rw [Submodule.coe_smul, Algebra.smul_def, map_mul]
    have : h.lift (algebraMap ↥(Frac0 (xplus X E hM) la G.w) (Lw (xplus X E hM) la G.w) r) = 0 := h.lift_Jid hr
    rw [this, zero_mul]
  · intro x y hx hy
    rw [Submodule.coe_add, map_add (f := _), hx, hy, add_zero]

end Lift

theorem inTieSec : InTieSecSt := by
  intro D B P j X E hM ka wL wF G la S y hs g0 hdep het hg0 hgen ζ
  have hd := hdep ζ
  have hg0' := hg0 ζ
  have het' : j < D.R.m → (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc _ G.et)) ≠ 0 := fun hj => het hj ζ
  set h := hs ζ with hh
  have hb : h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) ≠ 0 := h.s0.ne_zero
  have he := h.ep_pos
  have hvat : ∀ (w : WeightFamilies.Wt D j) (F : B.Cusp j w), (xplus X E hM).vAt la (.inr (y ζ)) ((xplus X E hM).inc w F) =
      nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.ev (emb (xplus X E hM) la G.N (X.inc w F))) :=
    fun w F => h.hv w F
  have hQy : (secQ y hs g0).y ζ = .inr (y ζ) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hQy, hd, nval_of_ne hb]; exact EReal.coe_ne_top _
  · rw [hQy, hd, nval_of_ne hb]; exact EReal.coe_ne_bot _
  · intro hj
    rw [hQy, hvat, nval_of_ne (het' hj)]; exact EReal.coe_ne_top _
  · refine ⟨vV h.T.V (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0)), ?_⟩
    simp only [LocalPointData.nu, hQy, hd]
    exact normalized_valuation_mul he _ (hs ζ).s0.ne_zero
  · change (((vV h.T.V (h.ev (emb (xplus X E hM) la G.N (X.inc wF g0))) : ℤ) : ℝ) : EReal) =
      (ep (unifO (xplus X E hM) la G.N) ζ : EReal) * (xplus X E hM).vAt la (.inr (y ζ)) ((xplus X E hM).inc wF g0)
    rw [hvat, e_mul_nval he, nval_of_ne hg0']
    simp
  · intro k g
    rw [h.ord, coe_weightZeroFraction, h.lift_frac, nval_frac he _ _ hb, hQy, hvat, hd]
    rfl
  · intro k g
    have hgen' : IsGen (OsK (xplus X E hM) la G.w) ((secQ y hs g0).e) := hgen
    set a := toA0K (xplus X E hM) la G.w wF (toHK (xplus X E hM) la G.w wF k
      ⟨emb (xplus X E hM) la G.N ((xplus X E hM).inc _ g), emb_mem_Vw (xplus X E hM) la G.N _ g⟩) with ha
    obtain ⟨x, hx⟩ := toOsK_surjective (xplus X E hM) la G.w (coord ((secQ y hs g0).e) a)
    have hca : coord ((secQ y hs g0).e) a • (secQ y hs g0).e = a := coord_smul_self hgen' a
    have h1 : toA0K (xplus X E hM) la G.w wF (x • toHK0 (xplus X E hM) la G.w wF
        ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩) = a := by
      rw [map_smul, ← restriction_apply_eq_reduction, ← hca, ← hx]
      exact (algebraMap_smul (OsK (xplus X E hM) la G.w) x _).symm
    have h2 := (Submodule.Quotient.eq _).1 h1
    have h3 := h.lift_JHK h2
    rw [Submodule.coe_sub, map_sub, sub_eq_zero, Submodule.coe_smul, Algebra.smul_def, map_mul, coe_toHK0,
      coe_toHK, h.lift_alg] at h3
    have h3' : h.lift (x : Lw (xplus X E hM) la G.w) * h.ev (emb (xplus X E hM) la G.N (X.inc wF g0)) =
        h.lift (frac (xplus X E hM) la G.w k (emb (xplus X E hM) la G.N ((xplus X E hM).inc _ g))) := h3
    have hord := h.ord x
    rw [hx] at hord
    simp only [LocalPointData.ordA, ordV]
    rw [toE_add_coe, hord]
    change nval h.T.V 1 (h.lift (x : Lw (xplus X E hM) la G.w)) +
      (((vV h.T.V (h.ev (emb (xplus X E hM) la G.N (X.inc wF g0))) : ℤ) : ℝ) : EReal) = _
    have hm := nval_mul (V := h.T.V) 1 (h.lift (x : Lw (xplus X E hM) la G.w))
      (h.ev (emb (xplus X E hM) la G.N (X.inc wF g0)))
    rw [h3', nval_of_ne hg0'] at hm
    have hc : (((vV h.T.V (h.ev (emb (xplus X E hM) la G.N (X.inc wF g0))) : ℤ) : ℝ) : EReal) =
        (((vV h.T.V (h.ev (emb (xplus X E hM) la G.N (X.inc wF g0))) : ℝ) / ((1 : ℕ) : ℝ) : ℝ) : EReal) := by simp
    rw [hc, ← hm, h.lift_frac, nval_frac he _ _ hb, hQy, hvat, hd]
    rfl

end Formalism.L2.Pj
end
end
