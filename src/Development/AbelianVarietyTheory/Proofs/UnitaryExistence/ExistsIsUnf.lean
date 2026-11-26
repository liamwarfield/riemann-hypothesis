module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CkOnInCCCongrOnGroup
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralChartTransportToFramedPoint
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralChartsCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsConjSplitPointLatticeLinearMap
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryRealEquivariantOntoTriangular
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemLevelKOfSameMarkAndFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsWeightZeroSectionOfPeriodSpaceFunction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsUnf
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb lieFac toC relab rdU laU IsUnf ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.IsUnfEx

theorem exists_xi {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ∃ ξ₀ : E, cc ξ₀ = -ξ₀ ∧ ξ₀ ≠ 0 ∧ ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have key : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.re = 0 ∧ z.im ≠ 0 := by
    intro z hz
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
    have him : z.im ≠ 0 := by
      intro h
      rw [h] at h1
      nlinarith [mul_self_nonneg z.re]
    refine ⟨?_, him⟩
    have : z.re * z.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right him
  have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτ₀ := key (τ₀ (H.rt : E)) (by rw [← map_pow, hsq]; simp)
  have hcc : cc (H.rt : E) = -(H.rt : E) := by
    apply τ₀.injective
    unfold cc
    rw [IsCMField.complexEmbedding_complexConj, map_neg]
    apply Complex.ext <;> simp [hτ₀.1]
  have hne : (H.rt : E) ≠ 0 := by
    intro h
    apply hτ₀.2
    rw [h]; simp
  rcases lt_or_gt_of_ne (key _ H.sqrt_neg_disc_sq).2 with h | h
  · exact ⟨H.rt, hcc, hne, fun τ hτ => by rw [hτ]; exact h⟩
  · refine ⟨-(H.rt : E), ?_, neg_ne_zero.2 hne, fun τ hτ => ?_⟩
    · unfold cc at hcc ⊢
      rw [map_neg, hcc]
    · rw [map_neg, hτ, Complex.neg_im]; linarith

theorem exists_isUnf : N1c → GlobalTheory.Published.HasseNormSt → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), 1 ≤ Dw.p + Dw.q → GoodEmb c σ → ∃ U : Unf Xo c σ (Dw.p + Dw.q), IsUnf U := by
  intro h1 h2 h3 h4 E _ _ _ H Dw l Xo c σ hpq hσ
  obtain ⟨ξ₀, hcc, hne, him⟩ := exists_xi H
  have hcc' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hcc ⊢
    rw [map_neg, hcc]
  obtain ⟨Gm, φ, hφ⟩ :=
    GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne) (Dw.p + Dw.q) rfl
  obtain ⟨U, hU, -⟩ :=
    GlobalTheory.T.exists_frameUniformisation_prescribedSpace h1 h2 h3 h4 E H Dw l Xo c σ (Dw.p + Dw.q) ξ₀ Gm φ hpq hσ hcc him hφ
  exact ⟨U, hU⟩

end GlobalTheory.IsUnfEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntChartFrTruncExists
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

theorem GlobalTheory.IntChartTrunc.intChart_frTrunc_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∃ C : IntegralChartA3 Xo c T io y, FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT :=
  fun E _ _ _ H Dw l Xo c _ hstar T io y =>
    GlobalTheory.IntChartTrunc.exists_intChart_frTrunc GlobalTheory.T.integral_charts_complete_dvr E H Dw l Xo c hstar (GlobalTheory.T.integralChart_transport_to_framedPoint E H Dw l Xo c) T io y
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitLatticeDatumEverySignature
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConjDatum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CM.ConjDatum

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem emb_bar (H : Host E) (τ : E →+* ℂ) (a : 𝓞 E) :
    τ ((H.bar a : 𝓞 E) : E) = starRingEnd ℂ (τ (a : E)) := by
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]

def ConjLat {H : Host E} (D : Datum H) : Type := D.La

instance {H : Host E} (D : Datum H) : AddCommGroup (ConjLat D) := D.acg

instance {H : Host E} (D : Datum H) : Module (𝓞 E) (ConjLat D) :=
  Module.compHom D.La (H.bar : 𝓞 E →+* 𝓞 E)

def toLat {H : Host E} (D : Datum H) : ConjLat D ≃+ D.La := AddEquiv.refl _

theorem toLat_smul {H : Host E} (D : Datum H) (s : 𝓞 E) (a : ConjLat D) :
    toLat D (s • a) = H.bar s • toLat D a := rfl

theorem finite {H : Host E} (D : Datum H) : Module.Finite (𝓞 E) (ConjLat D) := by
  have := D.fin
  let f : D.La →ₛₗ[(H.bar : 𝓞 E →+* 𝓞 E)] ConjLat D :=
    { toFun := (toLat D).symm
      map_add' := map_add _
      map_smul' := fun s a => by
        apply (toLat D).injective
        rw [toLat_smul]
        simp [bar_bar] }
  exact Module.Finite.of_surjective f (toLat D).symm.surjective

theorem projective {H : Host E} (D : Datum H) : Module.Projective (𝓞 E) (ConjLat D) := by
  have := D.proj
  have i1 : RingHomInvPair (H.bar : 𝓞 E →+* 𝓞 E) (H.bar : 𝓞 E →+* 𝓞 E) :=
    ⟨RingHom.ext (bar_bar H), RingHom.ext (bar_bar H)⟩
  let f : D.La ≃ₛₗ[(H.bar : 𝓞 E →+* 𝓞 E)] ConjLat D :=
    { (toLat D).symm with
      map_smul' := fun s a => by
        apply (toLat D).injective
        rw [toLat_smul]
        simp [bar_bar] }
  exact Module.Projective.of_equiv f

theorem finrank_eq {H : Host E} (D : Datum H) :
    Module.finrank (𝓞 E) (ConjLat D) = Module.finrank (𝓞 E) D.La := by
  unfold Module.finrank
  rw [rank_eq_of_equiv_equiv H.bar (toLat D) H.bar.bijective (toLat_smul D)]

def conj {H : Host E} (D : Datum H) : Datum H where
  La := ConjLat D
  fin := finite D
  proj := projective D
  EF := D.EF
  alt := D.alt
  unimod := D.unimod
  adj := fun a x y => D.adj (H.bar a) x y
  p := D.q
  q := D.p
  rank := by rw [finrank_eq, D.rank]; push_cast; ring
  dom := by
    obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
    refine ⟨J, h1, h2, h3, fun a A t hA ht => h4 (H.bar a) A t hA ?_⟩
    rw [ht]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [emb_bar, Complex.conj_conj, add_comm]

end GlobalTheory.CM.ConjDatum

namespace GlobalTheory.CM

end GlobalTheory.CM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitLatticeDatumEverySignature
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CompRat.SplitSum

theorem finrank_prod_int {E : Type} [Field E] [NumberField E] (M N : Type) [AddCommGroup M] [Module (𝓞 E) M]
    [AddCommGroup N] [Module (𝓞 E) N] [Module.Finite (𝓞 E) M] [Module.Finite (𝓞 E) N] :
    Module.finrank (𝓞 E) (M × N) = Module.finrank (𝓞 E) M + Module.finrank (𝓞 E) N := by
  have h1 := (TensorProduct.isBaseChange (𝓞 E) (M × N) E).finrank_eq
  have h2 := (TensorProduct.isBaseChange (𝓞 E) M E).finrank_eq
  have h2' := (TensorProduct.isBaseChange (𝓞 E) N E).finrank_eq
  have h3 := (TensorProduct.prodRight (𝓞 E) E E M N).finrank_eq
  rw [← h1, h3, Module.finrank_prod, h2, h2']

def prodSubEquiv {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (A : Submodule R M) (B : Submodule R N) : (A.prod B) ≃ₗ[R] A × B where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem finrank_prod_sub {E : Type} [Field E] [NumberField E] {M N : Type} [AddCommGroup M] [Module (𝓞 E) M]
    [AddCommGroup N] [Module (𝓞 E) N] [Module.Finite (𝓞 E) M] [Module.Finite (𝓞 E) N]
    (A : Submodule (𝓞 E) M) (B : Submodule (𝓞 E) N) :
    Module.finrank (𝓞 E) (A.prod B) = Module.finrank (𝓞 E) A + Module.finrank (𝓞 E) B := by
  rw [(prodSubEquiv A B).finrank_eq, finrank_prod_int]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem splitLat_sum {D D' : Datum H} (h : SplitLat D) (h' : SplitLat D') : SplitLat (DatumSum.sumDatum D D') := by
  obtain ⟨Lp, Lm, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨Lp', Lm', h1', h2', h3', h4', h5', h6'⟩ := h'
  have := D.fin
  have := D'.fin
  have hE : ∀ x y : D.La × D'.La, (DatumSum.sumDatum D D').EF x y = D.EF x.1 y.1 + D'.EF x.2 y.2 :=
    fun x y => DatumSum.sumForm_apply D.EF D'.EF x y
  have hR : ∀ x : D.La × D'.La, (DatumSum.sumDatum D D').EF (H.rt • x) x =
      D.EF (H.rt • x.1) x.1 + D'.EF (H.rt • x.2) x.2 := fun x => hE _ _
  refine ⟨Lp.prod Lp', Lm.prod Lm', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : Lp.prod Lp' ⊔ Lm.prod Lm' = ⊤ := by
      rw [Submodule.prod_sup_prod, h1, h1', Submodule.prod_top]
    exact this
  · intro a ha b hb
    refine (hE a b).trans ?_
    rw [h2 _ ha.1 _ hb.1, h2' _ ha.2 _ hb.2, add_zero]
  · exact (finrank_prod_sub Lp Lp').trans (by rw [h3, h3']; rfl)
  · exact (finrank_prod_sub Lm Lm').trans (by rw [h4, h4']; rfl)
  · intro a ha hne
    have := hR a
    erw [this]
    push_cast
    rw [mul_add]
    by_cases h0 : a.1 = 0
    · have h0' : a.2 ≠ 0 := fun h0' => hne (Prod.ext h0 h0')
      simpa [h0] using h5' _ ha.2 h0'
    · by_cases h0' : a.2 = 0
      · simpa [h0'] using h5 _ ha.1 h0
      · exact add_pos (h5 _ ha.1 h0) (h5' _ ha.2 h0')
  · intro a ha hne
    have := hR a
    erw [this]
    push_cast
    rw [mul_add]
    by_cases h0 : a.1 = 0
    · have h0' : a.2 ≠ 0 := fun h0' => hne (Prod.ext h0 h0')
      simpa [h0] using h6' _ ha.2 h0'
    · by_cases h0' : a.2 = 0
      · simpa [h0'] using h6 _ ha.1 h0
      · exact add_neg (h6 _ ha.1 h0) (h6' _ ha.2 h0')

end GlobalTheory.CompRat.SplitSum

namespace GlobalTheory.CompRat

theorem exists_splitLat_of_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ), (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) → ∃ D₀ : Datum H, D₀.p = p ∧ D₀.q = q ∧ SplitLat D₀ := by
  intro E _ _ _ H p q ⟨D, hp, hq⟩
  refine ⟨DatumSum.sumDatum (powDatum D p) (powDatum (CM.ConjDatum.conj D) q), ?_, ?_, ?_⟩
  · change p * D.p + q * D.q = p
    simp [hp, hq]
  · change p * D.q + q * D.p = q
    simp [hp, hq]
  · refine SplitSum.splitLat_sum (GlobalTheory.T.hermitianLatticeSignatureSplit_of_definite E H _ (Or.inr ?_)) (GlobalTheory.T.hermitianLatticeSignatureSplit_of_definite E H _ (Or.inl ?_))
    · change p * D.q = 0
      simp [hq]
    · change q * D.q = 0
      simp [hq]

end GlobalTheory.CompRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitLatticeDatumEverySignatureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitLattice_datum_every_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ), (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) → ∃ D₀ : Datum H, D₀.p = p ∧ D₀.q = q ∧ SplitLat D₀ := by
  first | exact @GlobalTheory.CompRat.exists_splitLat_of_signature | exact GlobalTheory.CompRat.exists_splitLat_of_signature | (intros; apply GlobalTheory.CompRat.exists_splitLat_of_signature <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsometryOfConjugateSplitPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsometryOfConjugateSplitPoint
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.ConjIsometry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply Subtype.ext
  show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem conj_of_sq {ρ : ℂ} (hρ : ρ ^ 2 = -(H.d : ℂ)) : starRingEnd ℂ ρ = -ρ := by
  have h1 : (starRingEnd ℂ ρ) ^ 2 = ρ ^ 2 := by rw [← map_pow, hρ]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h
    rw [hx] at hρ
    have h5 : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast hρ
    have h6 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [sq_nonneg x]
  · exact h

theorem bar_rt : H.bar H.rt = -H.rt := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h4 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun a : 𝓞 E => φ (a : E)) H.rt_sq
    simpa using this
  apply Subtype.ext
  show ((H.bar H.rt : 𝓞 E) : E) = ((-H.rt : 𝓞 E) : E)
  apply φ.injective
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, conj_of_sq h4]
  simp

theorem cmHost_bar_halfIntegerGenerator : H.bar H.w0 = 1 - H.w0 := by
  have h := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add (f := _), map_one, bar_rt, map_ofNat] at h
  apply mul_left_cancel₀ (two_ne_zero (α := 𝓞 E))
  linear_combination h + H.two_weight_eq_one_add_root

theorem bar_mul_wE (s : ℤ × ℤ) :
    H.bar (wE H s) * wE H s = ((s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) : ℤ) : 𝓞 E) := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (H.d : ℤ) + 1 = 4 * m := ⟨((H.d : ℤ) + 1) / 4, by have := H.d_mod; omega⟩
  have e : ((H.d : ℤ) + 1) / 4 = m := by omega
  have hm' : (H.d : 𝓞 E) + 1 = 4 * m := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hm
  have hw : H.w0 * (1 - H.w0) = (m : 𝓞 E) := by
    have h4 : (4 : 𝓞 E) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h4
    linear_combination (-(2 * H.w0 + H.rt - 1)) * H.two_weight_eq_one_add_root - H.rt_sq + hm'
  rw [e, wE, map_add (f := _), map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator]
  push_cast
  linear_combination (s.2 : 𝓞 E) ^ 2 * hw

theorem form_smul_smul (D : Datum H) (c : 𝓞 E) (N : ℤ) (h : H.bar c * c = N) (x y : D.La) :
    D.EF (c • x) (c • y) = N * D.EF x y := by
  rw [D.adj, smul_smul, h, Int.cast_smul_eq_zsmul, map_zsmul, smul_eq_mul]

theorem form_skew (D : Datum H) (x y : D.La) : D.EF x y = -D.EF y x := by
  have h := D.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, D.alt] at h
  linarith

variable {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem form_lat_eq_zero {D : Datum H} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) {a b : D.La}
    (ha : a ∈ lat hP H.rt0) (hb : b ∈ lat hP (-H.rt0)) : D.EF a b = 0 := by
  obtain ⟨Hm, -, -, hE⟩ := hP.2.2.2.2
  have h1 := hE (H.rt • a) (H.rt • b)
  rw [form_smul_smul D H.rt H.d (by rw [bar_rt]; push_cast; linear_combination -H.rt_sq),
    period_rt_smul hP ha, period_rt_smul hP hb] at h1
  have h2 : hermForm Hm (H.rt0 • P a) ((-H.rt0) • P b) = -(H.d : ℂ) * hermForm Hm (P a) (P b) := by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [star_neg, ← starRingEnd_apply, conj_of_sq H.sqrt_neg_disc_sq, ← H.sqrt_neg_disc_sq]
    ring
  rw [h2] at h1
  simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
    hE] at h1
  push_cast at h1
  have h6 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have : (D.EF a b : ℝ) = 0 := by nlinarith
  exact_mod_cast this

theorem surjective_of_isometry {D D' : Datum H} (hr : D.p + D.q = D'.p + D'.q) (Φ : D.La →ₗ[𝓞 E] D'.La)
    (hi : Function.Injective Φ) (hΦ : ∀ a b, D'.EF (Φ a) (Φ b) = D.EF a b) : Function.Surjective Φ := by
  have := D.fin
  have := D'.fin
  have := D'.proj
  have h0 : Module.finrank (𝓞 E) (D'.La ⧸ LinearMap.range Φ) = 0 := by
    have h1 := (LinearMap.range Φ).finrank_quotient_add_finrank
    rw [LinearMap.finrank_range_of_inj hi, D.rank, D'.rank] at h1
    omega
  intro y
  obtain ⟨x, hx⟩ := D.unimod.2 ((D'.EF y).comp (Φ.restrictScalars ℤ))
  have hx' : ∀ z, D'.EF (y - Φ x) (Φ z) = 0 := fun z => by
    rw [map_sub, LinearMap.sub_apply, hΦ, hx]; simp
  obtain ⟨c, hc, hcw⟩ := Module.finrank_eq_zero_iff.1 h0 (Submodule.Quotient.mk (y - Φ x))
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hcw
  obtain ⟨v, hv⟩ := hcw
  have hv0 : v = 0 := D.unimod.1 (by
    ext z
    rw [← hΦ, hv, D'.adj, ← map_smul, hx']; simp)
  rw [hv0, map_zero] at hv
  exact ⟨x, (sub_eq_zero.1 ((smul_eq_zero.1 hv.symm).resolve_left hc)).symm⟩

theorem exp_eq_zeta (n : ℕ) (m : ℤ) :
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / n) = zeta n ^ (-m) := by
  rw [zeta, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ}

theorem conj_pairing (F : FamilyUnif Xo σ ty) (τ : ℂ ≃+* ℂ) {i i' : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)}
    {P' : (F.Di i').La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di i') ty P')
    (hu : spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P') {n : ℕ} (hn : 0 < n) {x y : (F.Di i).La} {x' y' : (F.Di i').La}
    (hx : spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P x)).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' x')).left)
    (hy : spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P y)).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' y')).left) :
    τ (zeta n) ^ (-(F.Di i).EF x y) = zeta n ^ (-(F.Di i').EF x' y') := by
  let c : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * ((F.Di i).EF x y : ℂ) / n))
  let c' : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * ((F.Di i').EF x' y' : ℂ) / n))
  have W := F.ex_weil i P hP n x y c hn rfl
  have W' := F.ex_weil i' P' hP' n x' y' c' hn rfl
  let h : Over.mk (F.u i' P') ⟶ Over.mk (F.u i P) := Over.homMk (spMap (τ : ℂ →+* ℂ)) hu
  have W₁ := CommPairing.weilIs_pull globalFns_holds
    ⟨Xo.univ.t.semi.comm, Xo.univ.t.semi.smooth, Xo.univ.proper, Xo.univ.t.semi.geomConnected⟩ Xo.univ.t.PP.isLB h W
  have e' : Units.map h.left.appTop.hom.toMonoidHom (unitOn c) =
      unitOn (Units.map (τ : ℂ →+* ℂ).toMonoidHom c) :=
    Units.ext (congrArg (fun q => q.hom c.val)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (τ : ℂ →+* ℂ)))).symm
  have ex : h ≫ F.ex i P ((n : ℂ)⁻¹ • P x) = F.ex i' P' ((n : ℂ)⁻¹ • P' x') := Over.OverMorphism.ext hx
  have ey : h ≫ F.ex i P ((n : ℂ)⁻¹ • P y) = F.ex i' P' ((n : ℂ)⁻¹ • P' y') := Over.OverMorphism.ext hy
  rw [e', ex, ey] at W₁
  have k := congrArg Units.val (weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ _ _ _ _ _ _ W₁ W')
  rw [← map_zpow₀, ← exp_eq_zeta, ← exp_eq_zeta]
  exact k

end GlobalTheory.CompRat.ConjIsometry

namespace GlobalTheory.CompRat


open ConjIsometry in
theorem exists_isometry_of_conj_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P (a + b))).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ (wE H s • a + H.bar (wE H s) • b)))).left := by
  intro E _ _ _ H D l Xo σ g ty F h1 hσ hty hA τ hτ C io hio i P hP i' P' hP' hs hu
  obtain ⟨Φ, hinj, hp, hm, hact⟩ :=
    GlobalTheory.T.exists_conj_split_point_lattice_linear_map E H D l Xo σ g ty F h1 hσ hty hA τ hτ C io hio i P hP i' P' hP' hs hu
  have hiso : ∀ x y, (F.Di i').EF (Φ x) (Φ y) = (F.Di i).EF x y := by
    intro x y
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := x)))
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := y)))
    have key : ∀ n : ℕ, 0 < n →
        (n : ℤ) ∣ (F.Di i').EF (Φ (a + b)) (Φ (a' + b')) - (F.Di i).EF (a + b) (a' + b') := by
      intro n hn
      obtain ⟨⟨s, hs⟩, -⟩ := GlobalTheory.T.conjugation_acts_on_cm_torsion_by_multiplication E H C τ hτ io hio n hn
      have k := conj_pairing F τ hP hP' hu hn (hact n s hn hs a ha b hb) (hact n s hn hs a' ha' b' hb')
      have hN := GlobalTheory.T.cyclotomicCharacter_eq_cmMultiplier_norm E H C τ hτ io n s hn hs
      have hb1 := bar_mul_wE (H := H) s
      generalize s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) = N at hN hb1
      have hb2 : H.bar (H.bar (wE H s)) * H.bar (wE H s) = N := by rw [bar_bar, mul_comm, hb1]
      have o : ∀ u ∈ lat hP H.rt0, ∀ v ∈ lat hP (-H.rt0),
          (F.Di i').EF (Φ u) (Φ v) = 0 ∧ (F.Di i').EF (Φ v) (Φ u) = 0 := fun u hu v hv => by
        have := form_lat_eq_zero hP' ((hp u).2 hu) ((hm v).2 hv)
        exact ⟨this, by rw [form_skew, this, neg_zero]⟩
      have e : (F.Di i').EF (Φ (wE H s • a + H.bar (wE H s) • b)) (Φ (wE H s • a' + H.bar (wE H s) • b')) =
          N * (F.Di i').EF (Φ (a + b)) (Φ (a' + b')) := by
        simp only [map_add (f := _), LinearMap.add_apply]
        rw [(o _ (Submodule.smul_mem _ _ ha) _ (Submodule.smul_mem _ _ hb')).1,
          (o _ (Submodule.smul_mem _ _ ha') _ (Submodule.smul_mem _ _ hb)).2, (o _ ha _ hb').1, (o _ ha' _ hb).2]
        simp only [map_smul Φ]
        rw [form_smul_smul _ _ _ hb1, form_smul_smul _ _ _ hb2]
        ring
      rw [e, ← mul_neg, zpow_mul, ← hN] at k
      have prim : IsPrimitiveRoot (τ (zeta n)) n :=
        (Complex.isPrimitiveRoot_exp n hn.ne').map_of_injective τ.injective
      have ne : τ (zeta n) ≠ 0 := prim.ne_zero hn.ne'
      rw [← prim.zpow_eq_one_iff_dvd, sub_eq_add_neg, zpow_add₀ ne, k, ← zpow_add₀ ne, add_neg_cancel, zpow_zero]
    have := key (((F.Di i').EF (Φ (a + b)) (Φ (a' + b')) - (F.Di i).EF (a + b) (a' + b')).natAbs + 1) (by omega)
    exact sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _))
  have hsurj := surjective_of_isometry
    (by rw [(F.sig i).1, (F.sig i).2, (F.sig i').1, (F.sig i').2]) Φ hinj hiso
  exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, hiso, hp, hm, hact⟩

end GlobalTheory.CompRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsometryOfConjugateSplitPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_of_conjugate_split_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P (a + b))).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ (wE H s • a + H.bar (wE H s) • b)))).left := by
  first | exact @GlobalTheory.CompRat.exists_isometry_of_conj_split | exact GlobalTheory.CompRat.exists_isometry_of_conj_split | (intros; apply GlobalTheory.CompRat.exists_isometry_of_conj_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DictIsUnifOfMarkingRuleDictionary
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DictIsUnifOfMarkingRuleDictionary
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem dictIsUnif_of_isDict : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → DictIsUnif V dict Kf C.th C.hr := by
  intro D H Dw l Xo c σ V r C hC dict hd Kf hK
  obtain ⟨h1, h2, h3, -, -⟩ := GlobalTheory.T.memberDictionary_invariant_rational_level D H Dw l Xo c σ V r C hC dict hd Kf hK
  obtain ⟨h4, h5⟩ := GlobalTheory.T.memberDictionary_real_equivariant_onto_triangular D H Dw l Xo c σ V r C hC dict hd
  refine ⟨h1, h2, ⟨fun k => C.fr 1 k, fun k => ⟨(GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC 1 k).2.1, hd.2 k⟩, h4⟩,
    h3, h5, ?_⟩
  rintro g g' ⟨δ, hδ, he⟩
  obtain ⟨γ, hγ, hf⟩ := hd.1 g
  obtain ⟨γ', hγ', hf'⟩ := hd.1 g'
  rw [he] at hγ' hf'
  dsimp only at hγ' hf'
  obtain ⟨γ₁, hγ₁, hm, hfr⟩ := (GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC g _ γ hγ).2.2.2 δ hδ
  have hk := GlobalTheory.T.mem_levelK_of_same_mark_and_frame D H Dw l Xo c σ V r C hC Kf hK g g' _ _ _ hm hγ' (by rw [hfr, ← hf, hf'])
  refine ⟨γ'⁻¹ * (γ₁ * γ), mul_mem (inv_mem hγ'.1) hm.1, _, hk, ?_⟩
  group

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DictIsUnifOfMarkingRuleDictionaryStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictIsUnif_of_markingRule_dictionary : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → DictIsUnif V dict Kf C.th C.hr := by
  first | exact @GlobalTheory.Member.dictIsUnif_of_isDict | exact GlobalTheory.Member.dictIsUnif_of_isDict | (intros; apply GlobalTheory.Member.dictIsUnif_of_isDict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOrthogonalIdempotentSectionsPeriodSpaces
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOrthogonalIdempotentSectionsPeriodSpaces
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

noncomputable section

namespace GlobalTheory.CompSystem

open GlobalTheory.CompIdem GlobalTheory.CompFun

theorem orthogonal_of_fibres {R ι : Type} [CommRing R] [Fintype ι] (e : ι → R) (he : ∀ i, IsIdempotentElem (e i))
    (k : PrimeSpectrum R → ι) (h : ∀ i z, e i ∉ z.asIdeal ↔ k z = i) :
    (∀ i j, i ≠ j → e i * e j = 0) ∧ ∑ i, e i = 1 := by
  classical
  have ho : ∀ i j, i ≠ j → e i * e j = 0 := by
    intro i j hij
    refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem ((he i).mul (he j)) IsIdempotentElem.zero ?_
    ext z
    refine iff_of_false (fun hz => ?_) (fun hz => hz (zero_mem _))
    have hz' : e i * e j ∉ z.asIdeal := hz
    exact hij (((h i z).1 fun h1 => hz' (z.asIdeal.mul_mem_right _ h1)).symm.trans
      ((h j z).1 fun h1 => hz' (z.asIdeal.mul_mem_left _ h1)))
  refine ⟨ho, ?_⟩
  have hs : IsIdempotentElem (∑ i, e i) :=
    (OrthogonalIdempotents.mk he fun i j hij => ho i j hij).isIdempotentElem_sum
  refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem hs IsIdempotentElem.one ?_
  ext z
  refine iff_of_true (fun hz => ?_) (fun hz => z.2.ne_top ((Ideal.eq_top_iff_one _).2 hz))
  refine (h (k z) z).2 rfl ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (k z))] at hz
  refine (Ideal.add_mem_iff_left _ (sum_mem fun j hj => ?_)).1 hz
  by_contra hc
  exact (Finset.mem_erase.1 hj).1 ((h j z).1 hc).symm

theorem exists_complex_point {K : Type} [Field K] (σ : K →+* ℂ) {Y : Scheme.{0}} (s : Y ⟶ Sp K)
    [LocallyOfFiniteType s] {V : Set Y} (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ p : Sp ℂ ⟶ Y, p ≫ s = spMap σ ∧ p (IsLocalRing.closedPoint ℂ) ∈ V := by
  let g := pullback.snd s (spMap σ)
  let π := pullback.fst s (spMap σ)
  have hy : Surjective (spMap σ) :=
    ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have := LocallyOfFiniteType.jacobsonSpace g
  obtain ⟨z, hz⟩ := hne
  obtain ⟨w, rfl⟩ := π.surjective z
  obtain ⟨x, hx, hc'⟩ := nonempty_inter_closedPoints (Z := π ⁻¹' V) ⟨w, hz⟩
    (hV.preimage π.continuous).isLocallyClosed
  have hc : IsClosed ({x} : Set _) := hc'
  refine ⟨pointOfClosedPoint g x hc ≫ π, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · exact (congrArg (π · ∈ V) (pointOfClosedPoint_apply g x hc _)).mpr hx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l : Level H} {Xo : Moduli D l} {c : Coeff l}

theorem exists_indicator_test (hA : AllTest Xo c) (U : Set (Xo.XF c)) (hU : IsClopen U) :
    ∃ χ ∈ sec Xo c 0 0, (∀ (p : TRing c.F) (y : FrPt Xo c p.R), IsIdempotentElem (χ p y) ∧
      ∀ z : PrimeSpectrum p.R, χ p y ∉ z.asIdeal ↔ basePt y z ∈ U) ∧
      ∀ (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S),
      IsIdempotentElem (evR Xo c χ y) ∧
        ∀ z : PrimeSpectrum S, evR Xo c χ y ∉ z.asIdeal ↔ basePt y z ∈ U := by
  have hex : ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ∃ e : p.R, IsIdempotentElem e ∧
      ∀ z : PrimeSpectrum p.R, e ∉ z.asIdeal ↔ basePt y z ∈ U := by
    intro p y
    obtain ⟨e, he, h⟩ := PrimeSpectrum.isClopen_iff.1 (hU.preimage (basePt y).continuous)
    exact ⟨e, he, fun z => (Set.ext_iff.1 h z).symm⟩
  choose χ hi hχ using hex
  have hmap : ∀ (p : TRing c.F) (S : Type) [CommRing S] [Algebra c.F S] (φ : p.R →ₐ[c.F] S) (y : FrPt Xo c p.R)
      (w : FrPt Xo c S), w.x = spMap φ.toRingHom ≫ y.x →
      ∀ z : PrimeSpectrum S, φ (χ p y) ∉ z.asIdeal ↔ basePt w z ∈ U := by
    intro p S _ _ φ y w h z
    rw [basePt_map φ y w h]
    exact hχ p y (PrimeSpectrum.comap φ.toRingHom z)
  have hw : ∀ (p : TRing c.F) (t : Ix D → (p.R)ˣ), wchar (ex D 0 0) t = 1 := by
    intro p t
    refine Finset.prod_eq_one fun i _ => ?_
    have : ex D 0 0 i = 0 := by rcases i with _ | ⟨τ, i⟩ <;> simp [ex]
    rw [this, pow_zero]
  refine ⟨χ, ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩, fun p y => ⟨hi p y, hχ p y⟩, fun S _ _ _ y => ?_⟩
  · refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem (hi q z) ((hi p y).map φ) ?_
    ext w
    exact (hχ q z w).trans (hmap p q.R φ y z h.1 w).symm
  · rw [hw, _root_.one_mul]
    refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem (hi p y') (hi p y) ?_
    ext w
    have := hχ p y' w
    rw [basePt_congr y y' h.1] at this
    exact this.trans (hχ p y w).symm
  · have h := hA S y
    have e : evR Xo c χ y = h.choose_spec.choose (χ h.choose h.choose_spec.choose_spec.choose) := dif_pos h
    rw [e]
    exact ⟨(hi _ _).map _, hmap _ S _ _ y h.choose_spec.choose_spec.choose_spec.1⟩

theorem exists_index_map (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (hcl : FnAlgClosed (Xo := Xo) (c := c)) :
    ∃ k : Xo.XF c → Fin F.n, (∀ i, IsClopen (k ⁻¹' {i})) ∧ ∀ (y : FrPt Xo c (CAt σ)) (i : Fin F.n) P,
      IsPeriod (F.Di i) ty P → y.x = F.u i P → k (basePt (S := CAt σ) y (IsLocalRing.closedPoint ℂ)) = i := by
  classical
  have := CompFin.quasiCompact_alt Xo
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have := c.fin
  obtain ⟨t, ht, hcont⟩ := exists_index F
  have := CompFin.isNoetherian_XF Xo c
  let s : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  let pr : Xo.XF c ⟶ Xo.X := pullback.fst _ _
  have hover : ∀ p : Sp ℂ ⟶ Xo.XF c, p ≫ s = spMap σ →
      (p ≫ pr) ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    intro p hp
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp, CompIdem.spMap_comp]
  have hconst : ∀ p q : Sp ℂ ⟶ Xo.XF c, p ≫ s = spMap σ → q ≫ s = spMap σ →
      p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (q (IsLocalRing.closedPoint ℂ)) →
      t (p ≫ pr) = t (q ≫ pr) := by
    refine const_on_component_of_closed σ s (fun Z x hx => ?_) (fun x => t (x ≫ pr))
      (fun m B y hB hy hh => hcont m B _ hB (fun b hb => hover _ (hy b hb)) (GlobalTheory.LocLift.isHolTo_comp_hom hh _))
    have hx' : IsIntegral c.F (A := kap Z) x := hx
    obtain ⟨k, hk⟩ := hcl Z (algebraMap (kap Z) (Om Z) x) hx'.algebraMap.isAlgebraic
    rw [IsScalarTower.algebraMap_apply c.F (kap Z) (Om Z)] at hk
    exact ⟨k, (algebraMap (kap Z) (Om Z)).injective hk⟩
  have hex : ∀ z : Xo.XF c, ∃ i : Fin F.n, ∃ p : Sp ℂ ⟶ Xo.XF c, p ≫ s = spMap σ ∧
      p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z ∧ t (p ≫ pr) = i := by
    intro z
    obtain ⟨p, hp, hz⟩ := exists_complex_point σ s (isOpen_connectedComponent_of_noetherianSpace z)
      ⟨z, mem_connectedComponent⟩
    obtain ⟨i, P, hP, e⟩ := F.onto _ (hover p hp)
    exact ⟨i, p, hp, hz, e ▸ ht i P hP⟩
  choose k hk using hex
  have hk' : ∀ (z : Xo.XF c) (q : Sp ℂ ⟶ Xo.XF c), q ≫ s = spMap σ →
      q (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z → t (q ≫ pr) = k z := by
    intro z q hq hz
    obtain ⟨p, hp, h1, h2⟩ := hk z
    rw [← h2]
    exact hconst q p hq hp (connectedComponent_eq h1 ▸ hz)
  have hkc : ∀ z w, w ∈ connectedComponent z → k w = k z := by
    intro z w h
    obtain ⟨p, hp, h1, h2⟩ := hk w
    exact Fin.ext (h2.symm.trans (hk' z p hp (connectedComponent_eq h ▸ h1)))
  refine ⟨k, fun i => ?_, fun y i P hP hy => ?_⟩
  · refine ⟨⟨isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩, isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩
    · exact ⟨connectedComponent z, fun w hw h => hz ((hkc z w hw).symm.trans h),
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
    · exact ⟨connectedComponent z, fun w hw => (hkc z w hw).trans hz,
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
  · let p : Sp ℂ ⟶ Xo.XF c := basePt (S := CAt σ) y
    have hp : p ≫ s = spMap σ := pullback.lift_snd _ _ _
    have hp' : t (p ≫ pr) = i := by
      have : p ≫ pr = F.u i P := (pullback.lift_fst _ _ _).trans hy
      rw [this]
      exact ht i P hP
    exact Fin.ext ((hk' _ p hp mem_connectedComponent).symm.trans hp')

theorem exists_orthogonal_idempotents : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), FnAlgClosed (Xo := Xo) (c := c) → ∃ χ : Fin F.n → Rul Xo c, (∀ i, χ i ∈ sec Xo c 0 0) ∧ (∀ i, χ i * χ i = χ i) ∧ (∀ i i', i ≠ i' → χ i * χ i' = 0) ∧ ∑ i, χ i = 1 ∧ ∀ (y : FrPt Xo c (CAt σ)) (i i' : Fin F.n) P, IsPeriod (F.Di i') ty P → y.x = F.u i' P → toC (evR Xo c (χ i) y) = if i' = i then 1 else 0 := by
  intro E _ _ _ H D l Xo c σ g ty F hcl
  classical
  have hA := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.allSixLaws.1.secBaseChange E H D l Xo c
  obtain ⟨k, hk, hv⟩ := exists_index_map σ F hcl
  choose χ h1 h2 h3 using fun i => exists_indicator_test hA _ (hk i)
  have ho := fun (p : TRing c.F) (y : FrPt Xo c p.R) => orthogonal_of_fibres (fun i => χ i p y)
    (fun i => (h2 i p y).1) (fun z => k (basePt y z)) fun i z => (h2 i p y).2 z
  refine ⟨χ, h1, fun i => ?_, fun i j hij => ?_, ?_, fun y i i' P hP hy => ?_⟩
  · funext p y
    exact (h2 i p y).1.eq
  · funext p y
    exact (ho p y).1 i j hij
  · funext p y
    rw [Finset.sum_apply, Finset.sum_apply]
    exact (ho p y).2
  · have : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
    obtain ⟨h4, h5⟩ := h3 i (CAt σ) y
    let v : ℂ := evR Xo c (χ i) (S := CAt σ) y
    have h6 : v ∉ (IsLocalRing.closedPoint ℂ).asIdeal ↔
        k (basePt (S := CAt σ) y (IsLocalRing.closedPoint ℂ)) = i := h5 (IsLocalRing.closedPoint ℂ)
    have h8 : v ∉ (IsLocalRing.closedPoint ℂ).asIdeal ↔ v ≠ 0 := by
      show v ∉ IsLocalRing.maximalIdeal ℂ ↔ _
      rw [IsLocalRing.notMem_maximalIdeal, isUnit_iff_ne_zero]
    rw [h8, hv y i' P hP hy] at h6
    have h9 : IsIdempotentElem v := h4
    show v = _
    split_ifs with h
    · exact (IsIdempotentElem.iff_eq_zero_or_one.1 h9).resolve_left (h6.2 h)
    · exact not_not.1 (mt h6.1 h)

end GlobalTheory.CompSystem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOrthogonalIdempotentSectionsPeriodSpacesStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_idempotentSections_periodSpaces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), FnAlgClosed (Xo := Xo) (c := c) → ∃ χ : Fin F.n → Rul Xo c, (∀ i, χ i ∈ sec Xo c 0 0) ∧ (∀ i, χ i * χ i = χ i) ∧ (∀ i i', i ≠ i' → χ i * χ i' = 0) ∧ ∑ i, χ i = 1 ∧ ∀ (y : FrPt Xo c (CAt σ)) (i i' : Fin F.n) P, IsPeriod (F.Di i') ty P → y.x = F.u i' P → toC (evR Xo c (χ i) y) = if i' = i then 1 else 0 := by
  first | exact @GlobalTheory.CompSystem.exists_orthogonal_idempotents | exact GlobalTheory.CompSystem.exists_orthogonal_idempotents | (intros; apply GlobalTheory.CompSystem.exists_orthogonal_idempotents <;> assumption)
end
end
