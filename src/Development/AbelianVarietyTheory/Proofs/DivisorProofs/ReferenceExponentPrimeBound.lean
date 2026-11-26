module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasUnramifiedIntegralFramedPointsOfGoodPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGenerat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentTwistingSectionMulLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistingSectionMulLatticeValueLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistingSectionMulLatticeValueLe
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.TwMulOne

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem val_eq_of_agree {Z : Comp Xo c} {w : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal} (hv : v ∈ valOn Z w)
    {f g : Rul Xo c}
    (h : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → evR Xo c g y = evR Xo c f y) :
    v g = v f := by
  obtain ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  show nval T.V e (evR Xo c g y.1) = nval T.V e (evR Xo c f y.1)
  rw [h _ y.1 hy.2]

theorem exists_latW_val_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (Z : Comp Xo c)
    (t : TwSec U x Z G₀) (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valOn Z w, ∀ f ∈ latW U G,
    ∃ g ∈ latW U (G + G₀), v g ≤ v f + ((t.hi w - (⌊t.lo w⌋ : ℝ) : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c r U hU x G G₀ hG Z t w v hv f hf
  obtain ⟨f', hres, hlat⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hU Z G f
  have hf'lat := hlat hf
  obtain ⟨a, ha0, hva, hpos⟩ := GlobalTheory.RefSum.ScalApprox.exists_scal c.F t.lo t.finite_lo w
  obtain ⟨φ, hφ, -, hint, -⟩ := GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ t G hG
  have hg := hint a ha0 hpos f' hf'lat (a • φ f') (by rw [Submodule.coe_smul])
  refine ⟨⟨(a • φ f' : cuspOn U Z (G + G₀)), cuspOn_le U Z (G + G₀) (a • φ f').2⟩, (mem_latOn U).1 hg, ?_⟩
  have hV := isVal_valOn hv
  obtain ⟨b, hb, -, -, hbhi⟩ := t.exists_val hv
  have e1 : v (f' : Rul Xo c) = v (f : Rul Xo c) := val_eq_of_agree hv (hres)
  show v ((a • φ f' : cuspOn U Z (G + G₀)) : Rul Xo c) ≤ _
  rw [Submodule.coe_smul, hV.smul _ _ ha0, hφ, hV.mul, e1, hb, hva]
  rw [← add_assoc, add_comm (((-(⌊t.lo w⌋ : ℝ) : ℝ)) : EReal) (v (f : Rul Xo c)), add_assoc, ← EReal.coe_add]
  exact add_le_add le_rfl (EReal.coe_le_coe_iff.2 (by linarith))

end GlobalTheory.TwMulOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistingSectionMulLatticeValueLeStatement
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistingSection_mul_lattice_value_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (Z : Comp Xo c) (t : TwSec U x Z G₀) (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valOn Z w, ∀ f ∈ latW U G, ∃ g ∈ latW U (G + G₀), v g ≤ v f + ((t.hi w - (⌊t.lo w⌋ : ℝ) : ℝ) : EReal) := by
  first | exact @GlobalTheory.TwMulOne.exists_latW_val_le | exact GlobalTheory.TwMulOne.exists_latW_val_le | (intros; apply GlobalTheory.TwMulOne.exists_latW_val_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentIntegralFramedPointLiesOn
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentIntegralFramedPointLiesOn
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.IntFrComp

open AlgebraicGeometry

theorem exists_liesOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∃ Z : Comp Xo c, (letI := io.toAlgebra; LiesOn Z y.1) := by
  intro E _ _ _ H Dw l Xo c T io y
  letI := io.toAlgebra
  let s₀ : Sp T.Fr := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr)
  refine ⟨⟨irreducibleComponent (GlobalTheory.AllWt.ptF y.1 s₀), irreducibleComponent_mem_irreducibleComponents _⟩,
    fun s => ?_⟩
  obtain rfl : s = s₀ := Subsingleton.elim (α := PrimeSpectrum T.Fr) s s₀
  exact mem_irreducibleComponent

end GlobalTheory.IntFrComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentIntegralFramedPointLiesOnStatement
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_component_integral_framedPoint_liesOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∃ Z : Comp Xo c, (letI := io.toAlgebra; LiesOn Z y.1) := by
  first | exact @GlobalTheory.IntFrComp.exists_liesOn | exact GlobalTheory.IntFrComp.exists_liesOn | (intros; apply GlobalTheory.IntFrComp.exists_liesOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentTwistingSectionMulLe
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefTwist

theorem vAdd_natCast_pos {K : Type} [Field K] [NumberField K] {q : ℕ} (hq : q ≠ 0) {w : HeightOneSpectrum (𝓞 K)}
    (hw : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : 0 < vAdd w (q : K) := by
  have h1 : w.valuation K (algebraMap (𝓞 K) K q) < 1 := (w.valuation_lt_one_iff_mem _).2 hw
  rw [map_natCast] at h1
  have h0 : w.valuation K (q : K) ≠ 0 := (w.valuation K).ne_zero_iff.2 (Nat.cast_ne_zero.2 hq)
  have h2 := (WithZero.log_lt_log h0 one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  unfold vAdd
  omega

theorem nval_le_add_of_mul {T : CDVR} {e n : ℕ} {m s k : ℝ} (he : 0 < e) (hm : 0 < m) (hn : (n : ℝ) = e * m)
    (hs : s ≤ k * m) {a b : T.Fr} (h : nval T.V e b ≤ nval T.V e a + (s : EReal)) :
    nval T.V n b ≤ nval T.V n a + (k : EReal) := by
  by_cases ha : a = 0
  · rw [ha, nval_zero, EReal.top_add_coe]; exact le_top
  rw [nval_of_ne ha, ← EReal.coe_add] at h ⊢
  by_cases hb : b = 0
  · rw [hb, nval_zero] at h; exact absurd h (not_le.2 (EReal.coe_lt_top _))
  rw [nval_of_ne hb, EReal.coe_le_coe_iff] at h ⊢
  have he' : (0 : ℝ) < e := Nat.cast_pos.2 he
  rw [hn, ← div_div, ← div_div, div_le_iff₀ hm, add_mul, div_mul_cancel₀ _ hm.ne']
  linarith

theorem refExp_vp_add_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (cst k : ℝ) (q : ℕ), q.Prime → ∀ t : ∀ Z : Comp Xo c, TwSec U x Z G₀, (∀ Z (w : HeightOneSpectrum (𝓞 c.F)), ((q : ℕ) : 𝓞 c.F) ∈ w.asIdeal → (t Z).hi w - (⌊(t Z).lo w⌋ : ℝ) ≤ k * (vAdd w (q : c.F) : ℝ)) → refExp_vp U cst (G + G₀) q ≤ refExp_vp U cst G q + (k : EReal) := by
  intro E _ _ _ H Dw l Xo c r U hU x G G₀ hG cst k q hq t ht
  refine (refExp_vp_le_iff U).2 fun la T io e ho y hy φ hφ => ?_
  have h0 := (refExp_vp_le_iff U).1 (le_refl (refExp_vp U cst G q)) la T io e ho y hy φ hφ
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.exists_component_integral_framedPoint_liesOn E H Dw l Xo c T io y
  have hv : (fun f => nval T.V e (evI y f)) ∈ valOn Z la.1 := ⟨PtV.mk la.1 ho y ⟨hy, hZ⟩ () trivial, rfl⟩
  have hm : 0 < vAdd la.1 (q : c.F) := vAdd_natCast_pos hq.ne_zero la.2
  have hq' : vV T.V (q : T.Fr) = (e : ℤ) * vAdd la.1 (q : c.F) := by
    rw [← map_natCast io q]; exact ho.2 _
  have hn : (((vV T.V (q : T.Fr)).toNat : ℕ) : ℝ) = e * (vAdd la.1 (q : c.F) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (hq' ▸ mul_nonneg (Int.natCast_nonneg e) hm.le), hq']
    push_cast; rfl
  have hd : depthAt_vp U (G + G₀) q y ≤ depthAt_vp U G q y + (k : EReal) := by
    rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    refine le_iInf₂ fun f hf => ?_
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    obtain ⟨g, hg, hle⟩ := GlobalTheory.T.exists_twistingSection_mul_lattice_value_le E H Dw l Xo c r U hU x G G₀ hG Z (t Z) la.1 _ hv f hf
    exact (iInf₂_le g hg).trans (nval_le_add_of_mul ho.1 (Int.cast_pos.2 hm) hn (ht Z la.1 la.2) hle)
  rw [add_right_comm]
  exact hd.trans (add_le_add h0 le_rfl)

end GlobalTheory.RefTwist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentTwistingSectionMulLeStatement
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLocusExponent_twistingSection_mul_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (cst k : ℝ) (q : ℕ), q.Prime → ∀ t : ∀ Z : Comp Xo c, TwSec U x Z G₀, (∀ Z (w : HeightOneSpectrum (𝓞 c.F)), ((q : ℕ) : 𝓞 c.F) ∈ w.asIdeal → (t Z).hi w - (⌊(t Z).lo w⌋ : ℝ) ≤ k * (vAdd w (q : c.F) : ℝ)) → refExp_vp U cst (G + G₀) q ≤ refExp_vp U cst G q + (k : EReal) := by
  first | exact @GlobalTheory.RefTwist.refExp_vp_add_le | exact GlobalTheory.RefTwist.refExp_vp_add_le | (intros; apply GlobalTheory.RefTwist.refExp_vp_add_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentAndSum
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.DifferentGalois

theorem ord_conjDifferent_and_sum : ∀ (E K : Type) [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K] (i : E →+* K) (q : ℕ) (w : HeightOneSpectrum (𝓞 K)), q.Prime → ((q : ℕ) : 𝓞 K) ∈ w.asIdeal → (ord_vw w (conjDifferent i) : ℝ) = (different_vp E q : ℝ) * (vAdd w (q : K) : ℝ) ∧ ∑ p ∈ (discr E).natAbs.primeFactors, (different_vp E p : ℝ) * Real.log p = lrd E := by
  intro E K _ _ _ _ _ i q w hq hm
  refine ⟨?_, ?_⟩
  · have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
    have h1 := DefectSumCompare.vla_discAt i w
    have h2 := GlobalTheory.FlatLine.vla_span (K := K) (x := ((discr E).natAbs : ℕ)) (Nat.cast_ne_zero.2 hd) w
    have h3 := GlobalTheory.FlatLine.vAdd_natCast (K := K) hq hd hm
    have h5 : ((Module.finrank ℚ E * ord_vw w (conjDifferent i) : ℕ) : ℤ) =
        padicValNat q (discr E).natAbs * vAdd w (q : K) := by
      rw [← h1, ← h3]; exact h2
    have h7 := congrArg (Int.cast : ℤ → ℝ) h5
    simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at h7
    have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    rw [different_vp]
    push_cast
    field_simp
    linarith
  · have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
    have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    have h1 := DefectSumCompare.log_discr_eq E
    have h2 : Real.log |((discr E : ℤ) : ℝ)| = Real.log ((discr E).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization] at h1
    have h3 : ∀ p ∈ (discr E).natAbs.primeFactors, ((different_vp E p : ℚ) : ℝ) * Real.log p =
        ((discr E).natAbs.factorization p * Real.log p) / (Module.finrank ℚ E : ℝ) := by
      intro p hp
      rw [different_vp, Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]
      push_cast
      rw [Nat.padicValNat_def]
      ring
    rw [Finset.sum_congr rfl h3, ← Finset.sum_div, h1]
    field_simp

end GlobalTheory.DifferentGalois
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraSide
namespace GlobalTheory.ClosingLemmaFourth

theorem main : ∀ {z : ℂ} {d : ℕ}, (0 : ℕ) < d → z ^ (2 : ℕ) = -(↑d : ℂ) →
    (starRingEnd ℂ : ℂ → ℂ) z = -z ∧ z ≠ (0 : ℂ) := by
  intro z d hd h
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have hr : z.re = 0 := by
    have h2 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · rw [h3] at hre
      nlinarith [sq_nonneg z.re]
  refine ⟨?_, ?_⟩
  · apply Complex.ext <;> simp [hr]
  · rintro rfl
    simp at hre
    linarith

end GlobalTheory.ClosingLemmaFourth
end

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.RefSum.WFree

theorem conj_eq_neg {z : ℂ} {d : ℕ} (hd : 0 < d) (h : z ^ 2 = -(d : ℂ)) : (starRingEnd ℂ) z = -z ∧ z ≠ 0 :=
  _root_.GlobalTheory.ClosingLemmaFourth.main hd h

theorem two_mul_sum_mult {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) : 2 * ∑ τ : E →+* ℂ, Dw.mult τ = Module.finrank ℚ E * (Dw.p + Dw.q) := by
  have key : ∀ τ : E →+* ℂ, Dw.mult τ + Dw.mult (ComplexEmbedding.conjugate τ) = Dw.p + Dw.q := fun τ => by
    have hs : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
      simpa using this
    obtain ⟨h1, h2⟩ := conj_eq_neg H.d_prime.pos hs
    have h3 : ComplexEmbedding.conjugate τ (H.rt : E) = -τ (H.rt : E) := h1
    unfold Datum.mult
    rw [h3]
    by_cases h : τ (H.rt : E) = H.rt0
    · rw [if_pos h, if_neg fun e => h2 (by linear_combination (h - e) / 2)]
    · have : -τ (H.rt : E) = H.rt0 := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hs.trans H.sqrt_neg_disc_sq.symm) with e | e
        · exact absurd e h
        · rw [e, neg_neg]
      rw [if_neg h, if_pos this, add_comm]
  have hinv : Function.Involutive (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) := fun τ => star_star τ
  have e := Equiv.sum_comp hinv.toPerm Dw.mult
  rw [two_mul]
  nth_rewrite 2 [← e]
  rw [← Finset.sum_add_distrib]
  refine (Finset.sum_congr rfl fun τ _ => key τ).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Embeddings.card, smul_eq_mul]

theorem one_le_vAdd {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : q ≠ 0)
    (h : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : 1 ≤ vAdd w (q : K) := by
  have h1 : w.valuation K (algebraMap (𝓞 K) K (q : 𝓞 K)) < 1 := (w.valuation_lt_one_iff_mem (K := K) _).2 h
  rw [map_natCast] at h1
  have h0 : w.valuation K (q : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hq)
  have := WithZero.log_lt_log h0 one_ne_zero |>.2 h1
  rw [WithZero.log_one] at this
  unfold vAdd
  omega

theorem notMem_of_ne {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hne : p ≠ q) (h : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((p : ℕ) : 𝓞 K) ∉ w.asIdeal := fun h' => by
  have hc : IsCoprime ((p : ℕ) : 𝓞 K) ((q : ℕ) : 𝓞 K) := ((Nat.coprime_primes hp hq).2 hne).cast
  obtain ⟨a, b, e⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (Ideal.mul_mem_left _ _ h') (Ideal.mul_mem_left _ _ h)))

theorem different_vp_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l : Level H) {q : ℕ} (hq : q.Prime) (h : q ∉ badPrimes H l) : different_vp E q = 0 := by
  have : ¬ q ∣ (discr E).natAbs := fun hd => h (Nat.mem_primeFactors.2 ⟨hq, (hd.mul_left _).mul_right _,
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero H.d_prime.ne_zero) (Int.natAbs_ne_zero.2 (discr_ne_zero E)))
      (Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne')⟩)
  rw [different_vp, Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd this]
  simp

theorem refExp_vp_le_of_laws {E : Type} [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : GlobalTheory.FlatCore.Laws U x) (hN : UnramPts Xo c (badPrimes H l))
    (hF : FlatExists U x) (u : GlobalTheory.AllWt.Weight Dw) (w₀ : Psi H → ℤ) (m : ℕ) (cst : ℝ) {q : ℕ} (hq : q.Prime) {N : ℝ}
    (hs : ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) = N) :
    refExp_vp U cst (wtOf Dw u 0) q ≤ refExp_vp U cst (wtOf Dw (u + parWt Dw w₀) m) q +
      (((if q ∈ badPrimes H l then (m * N * (different_vp E q : ℝ) + 1) else 0 : ℝ)) : EReal) := by
  obtain ⟨hK, ht⟩ := GlobalTheory.T.exists_keySection_inverseRoot_twistingSection_spread E H Dw l Xo c r U hL.unf x hL.xi hL.geo hL.pos hL.good hN
  have hz : ∀ Z : Comp Xo c, ∃ z : TwSec U x Z (wtOf Dw u 0 - wtOf Dw (u + parWt Dw w₀) m),
      IntOff (badPrimes H l) z.lo ∧ ∀ w, z.hi w - z.lo w ≤
        m * ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) := fun Z => by
    obtain ⟨t, ht1, ht2⟩ := ht Z
    obtain ⟨s, -, -, -, hs1, hs2⟩ := (GlobalTheory.FlatTwisting.twSec_of_flat E H Dw l Xo c r U x _ hK hL.unf hL.pos hN).1 Z (-w₀) _
      (FlatSec.shift (hasPts U hL.pos hL.good hL.unf Z) (fun τ => (hF.nonempty Z τ).some) (-w₀))
      ((Set.finite_iUnion fun τ => finite_flDefect_vw (Dw := Dw) (c := c) τ).subset fun w hw => by
        by_contra hn
        simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
        exact hw (by simp [Finset.sum_apply, hn]))
    exact GlobalTheory.CombTw.exists_twSec_comb E H Dw l Xo c r U hL.unf x _ Z u w₀ m _ s t hs1 hs2 ht1 ht2
  choose z hz1 hz2 using hz
  have key := GlobalTheory.T.baseLocusExponent_twistingSection_mul_le E H Dw l Xo c r U hL.unf x (wtOf Dw (u + parWt Dw w₀) m) _ (even_two_mul (m : ℤ)) cst
    (if q ∈ badPrimes H l then (m * N * (different_vp E q : ℝ) + 1) else 0) q hq z fun Z w hw => by
      have h1 := hz2 Z w
      simp only [fun τ => (GlobalTheory.DifferentGalois.ord_conjDifferent_and_sum E c.F (embF c τ) q w hq hw).1, ← Finset.sum_mul, hs] at h1
      split_ifs with hb
      · have h2 : (1 : ℝ) ≤ (vAdd w (q : c.F) : ℝ) := by exact_mod_cast one_le_vAdd w hq.ne_zero hw
        have h3 := Int.lt_floor_add_one ((z Z).lo w)
        linarith
      · obtain ⟨n, hn⟩ := hz1 Z w fun p hp =>
          notMem_of_ne w (Nat.prime_of_mem_primeFactors hp) hq (fun e => hb (e ▸ hp)) hw
        rw [different_vp_eq_zero l hq hb, hn] at h1
        rw [hn, Int.floor_intCast]
        simpa using h1
  rwa [add_sub_cancel] at key

end GlobalTheory.RefSum.WFree
