module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaOperatorFrameSeriesOfSteps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationEqPartialLogCoordsProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCellFiniteUnionLocalDoubleCosets
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.BilLActRight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigDirInt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndAll
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralTypesAndDirections
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TypicalBasisCoordinates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.FlatGenInjective
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IntChartCheck

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem const_zero (C : IntegralChartA3 Xo c T io y) :
    (∀ j, MvPowerSeries.constantCoeff (C.FT j) = 0) ∧ ∀ a j, MvPowerSeries.constantCoeff (C.actT a j) = 0 := by
  letI := io.toAlgebra
  obtain ⟨⟨h1, h2, -⟩, -⟩ := C.gen
  refine ⟨fun j => ?_, fun a j => ?_⟩
  · have := C.ch.B.G.const j
    rw [h1 j, MvPowerSeries.constantCoeff_map] at this
    exact (map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)).1 this
  · have := C.ch.B.A.const a j
    rw [h2 a j, MvPowerSeries.constantCoeff_map] at this
    exact (map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)).1 this

theorem dim_eq (C : IntegralChartA3 Xo c T io y) : chD C.ch = Fintype.card (Lt1 Dw) := by
  letI := io.toAlgebra
  let f : (Lt1 Dw → T.Fr) →ₗ[T.Fr] (Fin C.ch.d → T.Fr) :=
    { toFun := fun a j => ∑ ℓ, a ℓ * C.ch.uvec ℓ j
      map_add' := fun a b => by funext j; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r a => by funext j; simp [Finset.mul_sum, _root_.mul_assoc] }
  have hb : Function.Bijective f := (Function.bijective_iff_existsUnique f).2 fun v => by
    obtain ⟨a, ha, hu⟩ := C.ch.chart.basis v
    exact ⟨a, funext ha, fun b hb => hu b (congrFun hb)⟩
  have := (LinearEquiv.ofBijective f hb).finrank_eq
  simpa using this.symm

end GlobalTheory.IntChartCheck
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelDirectionsIntegralBasisUnramifiedPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelDirectionsIntegralBasisUnramifiedPrime
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.PrimePart

theorem exists_integral_inverse_lieVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), UnramIn E p → ∀ [DecidableEq (Lt1 Dw)], ∃ L : Matrix (Lt1 Dw) (Fin (chD Ch.ch)) X.C, (∀ a b, IsIntV (vX_vp X) (L a b)) ∧ L * (Matrix.of fun e ℓ => lieVec Ch X ℓ e) = 1 ∧ (Matrix.of fun e ℓ => lieVec Ch X ℓ e) * L = 1 := by
  intro E _ _ _ H Dw l Xo c _ p _ T io X y Ch hp inst
  have hbij := GlobalTheory.T.embeddingReducedResidueField_bijective_unramified E H l c p T io X hp
  choose σV hσV using fun τ : E →+* ℂ =>
    GlobalTheory.PowGerm.exists_lift_ringOfIntegers (V := T.V) (io.comp (embK c τ))
  have hσV' : ∀ τ a, algebraMap T.V T.Fr (σV τ a) = io (embK c τ a) := hσV
  have hι : ∀ τ a, X.ι (σV τ a) = embO io X τ a := fun τ a => X.ints.hom_inj (by
    rw [algebraMap_embO, ← X.comp, hσV']; rfl)
  have hsep : ∀ τ τ' : E →+* ℂ, τ ≠ τ' → ∃ a, IsUnit (σV τ a - σV τ' a) := by
    intro τ τ' hne
    have h1 : red io X τ ≠ red io X τ' := fun h => hne (hbij.1 h)
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 h1
    refine ⟨a, ?_⟩
    have := X.ι_local
    refine (isUnit_map_iff X.ι _).1 ?_
    rw [map_sub, hι, hι]
    by_contra hu
    apply ha
    rw [← sub_eq_zero]
    show residue X.O _ - residue X.O _ = 0
    rw [← map_sub, residue_eq_zero_iff]
    exact (mem_maximalIdeal _).2 hu
  have hex : ∃ lam : Lt1 Dw → Fin (chD Ch.ch) → T.V, ∀ l l', ∑ s, lam l s * Ch.uvecT l' s = if l = l' then 1 else 0 := by
    classical
    obtain ⟨lam, hlam⟩ := GlobalTheory.exists_dual_forms_of_separated_types T.V (𝓞 E) (chD Ch.ch)
      (fun a => Matrix.of fun m j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Ch.actT a m))
      (E →+* ℂ) Dw.mult (fun τ a => σV τ a) Ch.uvecT hsep
      (fun a ℓ => ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.eigDir_int Xo c T io y Ch ℓ a _ (hσV' _ _)) (fun τ => by
        obtain ⟨⟨w, emb, hw, hb⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y Ch τ
        exact GlobalTheory.PowGerm.exists_dual_of_extends (fun i => Ch.uvecT ⟨τ, i⟩) w emb hw hb)
    exact ⟨lam, fun l l' => by convert hlam l l'⟩
  obtain ⟨lam, hlam⟩ := hex
  have h1 : (Matrix.of fun ℓ e => jX X (lam ℓ e)) * (Matrix.of fun e ℓ => lieVec Ch X ℓ e) = 1 := by
    ext ℓ ℓ'
    have h := congrArg (jX X) (hlam ℓ ℓ')
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    simp only [map_mul] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply, lieVec]
    rw [h]
    split_ifs
    · exact map_one _
    · exact map_zero _
  refine ⟨Matrix.of fun ℓ e => jX X (lam ℓ e), fun a b => isIntV_jX X _, h1, ?_⟩
  have e : Lt1 Dw ≃ Fin (chD Ch.ch) := Fintype.equivFinOfCardEq (GlobalTheory.IntChartCheck.dim_eq Ch).symm
  exact (Matrix.mul_eq_one_comm_of_equiv e).1 h1

end GlobalTheory.PrimePart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelDirectionsIntegralBasisUnramifiedPrimeStatement
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.label_directions_integral_basis_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), UnramIn E p → ∀ [DecidableEq (Lt1 Dw)], ∃ L : Matrix (Lt1 Dw) (Fin (chD Ch.ch)) X.C, (∀ a b, IsIntV (vX_vp X) (L a b)) ∧ L * (Matrix.of fun e ℓ => lieVec Ch X ℓ e) = 1 ∧ (Matrix.of fun e ℓ => lieVec Ch X ℓ e) * L = 1 := by
  first | exact @GlobalTheory.PrimePart.exists_integral_inverse_lieVec | exact GlobalTheory.PrimePart.exists_integral_inverse_lieVec | (intros; apply GlobalTheory.PrimePart.exists_integral_inverse_lieVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusActsOnTypeAtValuation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusActsOnTypeAtValuation
set_option autoImplicit false

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth
  GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

section ResidueField

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {d : ℕ}

theorem sqrtNeg_ne_neg (h2 : p ≠ 2) (hd : (d : ZMod p) ≠ 0) {r : k} (hr : r ^ 2 = -(d : k)) : r ≠ -r := by
  intro h
  have h2k : (2 : k) ≠ 0 := by
    intro h0
    have : p ∣ 2 := (CharP.cast_eq_zero_iff k p 2).1 (by exact_mod_cast h0)
    exact h2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  have hr0 : r = 0 := by
    have : 2 * r = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left h2k
  have hdk : (d : k) = 0 := by
    rw [hr0] at hr
    linear_combination hr
  exact hd ((ZMod.natCast_eq_zero_iff d p).2 ((CharP.cast_eq_zero_iff k p d).1 hdk))

theorem sqrtNeg_pow_of_isSquare (hs : IsSquare (-(d : ZMod p))) {r : k} (hr : r ^ 2 = -(d : k)) : r ^ p = r := by
  obtain ⟨m, hm⟩ := hs
  have h1 : r ^ 2 = (ZMod.castHom (dvd_refl p) k m) ^ 2 := by
    rw [hr, ← map_pow, sq, ← hm, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · rw [h, ← map_pow, ZMod.pow_card]
  · rw [h, ← map_neg, ← map_pow, ZMod.pow_card]

theorem sqrtNeg_pow_ne_of_not_isSquare (hs : ¬ IsSquare (-(d : ZMod p))) {r : k} (hr : r ^ 2 = -(d : k)) :
    r ^ p ≠ r := by
  have hd : (d : ZMod p) ≠ 0 := fun h => hs (by rw [h, neg_zero]; exact IsSquare.zero)
  have hd' : -(d : ZMod p) ≠ 0 := neg_ne_zero.2 hd
  have h2 : p ≠ 2 := by
    rintro rfl
    apply hs
    generalize (-(d : ZMod 2)) = x
    exact ⟨x, by rw [← sq, ZMod.pow_card]⟩
  have he : (-(d : ZMod p)) ^ (p / 2) = -1 :=
    (ZMod.pow_div_two_eq_neg_one_or_one p hd').resolve_left fun h => hs ((ZMod.euler_criterion p hd').2 h)
  have hk : (-(d : k)) ^ (p / 2) = -1 := by
    have := congrArg (ZMod.castHom (dvd_refl p) k) he
    rwa [map_pow, map_neg, map_neg, map_natCast, map_one] at this
  have hp : p = 2 * (p / 2) + 1 := by
    have := (Fact.out : p.Prime).eq_two_or_odd.resolve_left h2
    omega
  have h3 : r ^ p = -r := by
    conv_lhs => rw [hp]
    rw [pow_succ, pow_mul, hr, hk, neg_one_mul]
  rw [h3]
  exact (sqrtNeg_ne_neg h2 hd hr).symm

end ResidueField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

theorem label_rt_sq (H : Host E) (σ : E →+* ℂ) : σ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
  have := congrArg (σ.comp (algebraMap (𝓞 E) E)) H.rt_sq
  rwa [map_pow, map_neg, map_natCast] at this

theorem conj_label_rt (H : Host E) (σ : E →+* ℂ) :
    ComplexEmbedding.conjugate σ (H.rt : E) = -σ (H.rt : E) := by
  rw [ComplexEmbedding.conjugate_coe_eq]
  have h := label_rt_sq H σ
  generalize σ (H.rt : E) = z at h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [sq] at h1 h2
  have h3 : z.re = 0 := by
    by_contra h0
    have h4 : z.im = 0 := by
      have : z.re * z.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left h0
    rw [h4] at h1
    nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [h3]

theorem exists_w0_sq_even_constant (H : Host E) : ∃ n : ℕ, H.w0 ^ 2 = H.w0 - 2 * n := by
  refine ⟨(H.d + 1) / 8, ?_⟩
  have h8 : ((H.d : ℕ) : 𝓞 E) + 1 = 8 * (((H.d + 1) / 8 : ℕ) : 𝓞 E) := by
    have : H.d + 1 = 8 * ((H.d + 1) / 8) := by have := H.d_mod; omega
    exact_mod_cast this
  have h4 : (4 : 𝓞 E) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  have h1 := H.two_weight_eq_one_add_root
  have h2 := H.rt_sq
  linear_combination (2 * H.w0 - 1 + H.rt) * h1 + h2 - h8

variable {c : Coeff l} {T : CDVR} (io : c.F →+* T.Fr) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

theorem red_eq_of_label_eq {σ σ' : E →+* ℂ} {a b : 𝓞 E} (h : σ' (a : E) = σ (b : E)) :
    red io X σ' a = red io X σ b := by
  have h1 : embK c σ' a = embK c σ b := Subtype.ext h
  have h2 : embO io X σ' a = embO io X σ b := X.ints.hom_inj (by
    rw [algebraMap_embO, algebraMap_embO, embX, embX, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      RingHom.comp_apply, h1])
  rw [red, red, RingHom.comp_apply, RingHom.comp_apply, h2]

theorem frobOnType : FrobOnType io X := by
  intro σ σ' hF
  haveI := charP_residueField_of_irreducible X
  have hred : ∀ a, red io X σ' a = red io X σ a ^ p := fun a => (red_eq_pow_iff io X σ σ' a p).2 (hF a)
  have hr : red io X σ H.rt ^ 2 = -(H.d : ResidueField X.O) := by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have hpm : σ' (H.rt : E) = σ (H.rt : E) ∨ σ' (H.rt : E) = -σ (H.rt : E) :=
    sq_eq_sq_iff_eq_or_eq_neg.1 (by rw [label_rt_sq, label_rt_sq])
  refine ⟨fun hs => ?_, fun hi => ?_⟩
  · have key : σ' (H.rt : E) = σ (H.rt : E) := by
      refine hpm.resolve_right fun h => ?_
      by_cases h2 : p = 2
      · subst h2
        obtain ⟨n, hn⟩ := exists_w0_sq_even_constant H
        have hw : ∀ τ : E →+* ℂ, 2 * τ (H.w0 : E) = 1 + τ (H.rt : E) := fun τ => by
          have := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.two_weight_eq_one_add_root
          rwa [map_mul, map_add, map_one, map_ofNat] at this
        have h1 : σ' (H.w0 : E) = σ ((1 - H.w0 : 𝓞 E) : E) := by
          have e : σ ((1 - H.w0 : 𝓞 E) : E) = 1 - σ (H.w0 : E) := by
            have := map_sub (σ.comp (algebraMap (𝓞 E) E)) 1 H.w0
            rwa [map_one] at this
          rw [e]
          linear_combination (1 / 2) * hw σ' + (1 / 2) * hw σ + (1 / 2) * h
        have h3 := red_eq_of_label_eq io X h1
        rw [hred, ← map_pow, hn, map_sub, map_sub, map_mul, map_one, map_ofNat] at h3
        have h4 : (2 : ResidueField X.O) = 0 := by
          exact_mod_cast CharP.cast_eq_zero (ResidueField X.O) 2
        apply one_ne_zero (α := ResidueField X.O)
        linear_combination -h3 + (red io X σ H.w0 - red io X σ n) * h4
      · have h1 : σ' (H.rt : E) = σ ((-H.rt : 𝓞 E) : E) := by
          rw [h]; exact (map_neg (σ.comp (algebraMap (𝓞 E) E)) H.rt).symm
        have h3 := red_eq_of_label_eq io X h1
        rw [hred, sqrtNeg_pow_of_isSquare hs.2 hr, map_neg] at h3
        exact sqrtNeg_ne_neg h2 hs.1 hr h3
    rw [InPsi, InPsi, key]
  · have key : σ' (H.rt : E) = -σ (H.rt : E) := by
      refine hpm.resolve_left fun h => ?_
      have h3 := red_eq_of_label_eq io X h
      rw [hred] at h3
      exact sqrtNeg_pow_ne_of_not_isSquare hi hr h3
    rw [InPsi, InPsi, key, conj_label_rt]

theorem frobOnType_all (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l)
    (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) : FrobOnType io X :=
  frobOnType io X

end GlobalTheory.PrimePart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusActsOnTypeAtValuationStatement
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_acts_on_type_at_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), FrobOnType io X := by
  first | exact @GlobalTheory.PrimePart.frobOnType_all | exact GlobalTheory.PrimePart.frobOnType_all | (intros; apply GlobalTheory.PrimePart.frobOnType_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDetPowDepthLeOfIntegralLogHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDetPowDepthLeOfIntegralLogHom
set_option autoImplicit false

noncomputable section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory.DepthMono

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

def linSub {d d' : ℕ} (M : Matrix (Fin d') (Fin d) C) : Fin d' → MvPowerSeries (Fin d) C :=
  fun b => ∑ a, M b a • (X a : MvPowerSeries (Fin d) C)

theorem constantCoeff_linSub {d d' : ℕ} (M : Matrix (Fin d') (Fin d) C) (b : Fin d') :
    constantCoeff (linSub M b) = 0 := by
  simp [linSub]

theorem subst_expOf_hom {d d' : ℕ} {G : LogFGL v d} {G' : LogFGL v d'}
    {φ : Fin d' → MvPowerSeries (Fin d) C} {M : Matrix (Fin d') (Fin d) C} (hφ : IsIntHom G G' φ M)
    (c : Fin d') : subst (expOf G) (φ c) = subst (linSub M) (expOf G' c) := by
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero (isExp_expOf G).1
  have hE' : HasSubst (expOf G') := hasSubst_of_constantCoeff_zero (isExp_expOf G').1
  have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ.1
  have hL : HasSubst (linSub M) := hasSubst_of_constantCoeff_zero (constantCoeff_linSub M)
  have hlg' : HasSubst G'.lg := hasSubst_of_constantCoeff_zero G'.lg_const
  set ψ : Fin d' → MvPowerSeries (Fin d) C := fun c => subst (expOf G) (φ c) with hψ
  set ρ : Fin d' → MvPowerSeries (Fin d) C := fun c => subst (linSub M) (expOf G' c) with hρ
  have hψ0 : ∀ c, constantCoeff (ψ c) = 0 := fun c =>
    constantCoeff_subst_eq_zero hE (isExp_expOf G).1 (hφ.1 c)
  have hρ0 : ∀ c, constantCoeff (ρ c) = 0 := fun c =>
    constantCoeff_subst_eq_zero hL (constantCoeff_linSub M) ((isExp_expOf G').1 c)
  have hψs : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  have hρs : HasSubst ρ := hasSubst_of_constantCoeff_zero hρ0
  have key : ∀ b, subst ψ (G'.lg b) = subst ρ (G'.lg b) := by
    intro b
    have h1 : subst ψ (G'.lg b) = subst (expOf G) (subst φ (G'.lg b)) :=
      (subst_comp_subst_apply hφs hE (G'.lg b)).symm
    have h2 : subst ρ (G'.lg b) = subst (linSub M) (subst (expOf G') (G'.lg b)) :=
      (subst_comp_subst_apply hE' hL (G'.lg b)).symm
    rw [h1, h2, hφ.2.2, (isExp_expOf G').2, subst_sum_smul hE, subst_X hL]
    simp only [(isExp_expOf G).2, linSub]
  have inj : ∀ c, ψ c = subst (fun b => subst ψ (G'.lg b)) (expOf G' c) ∧
      ρ c = subst (fun b => subst ρ (G'.lg b)) (expOf G' c) := by
    intro c
    constructor
    · rw [← subst_comp_subst_apply hlg' hψs, subst_lg_expOf, subst_X hψs]
    · rw [← subst_comp_subst_apply hlg' hρs, subst_lg_expOf, subst_X hρs]
  show ψ c = ρ c
  rw [(inj c).1, (inj c).2, funext key]

theorem subst_exp_hom {τ : Type} {d d' : ℕ} {G : LogFGL v d} {G' : LogFGL v d'}
    {φ : Fin d' → MvPowerSeries (Fin d) C} {M : Matrix (Fin d') (Fin d) C} (hφ : IsIntHom G G' φ M)
    {L : Fin d → MvPowerSeries τ C} (hL0 : ∀ e, constantCoeff (L e) = 0) (c : Fin d') :
    subst (fun e => (subst L (expOf G e) : MvPowerSeries τ C)) (φ c) =
      (subst (fun b => ∑ a, M b a • L a) (expOf G' c) : MvPowerSeries τ C) := by
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero (isExp_expOf G).1
  have hM : HasSubst (linSub M) := hasSubst_of_constantCoeff_zero (constantCoeff_linSub M)
  have hL : HasSubst L := hasSubst_of_constantCoeff_zero hL0
  rw [← subst_comp_subst_apply hE hL, subst_expOf_hom hφ, subst_comp_subst_apply hM hL]
  congr 1
  funext b
  rw [linSub, subst_sum_smul hL]
  simp only [subst_X hL]

theorem detDepth_le_of_isIntHom : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)),
    ∀ (i d d' k : ℕ) (G : LogFGL v d) (G' : LogFGL v d') (φ : Fin d' → MvPowerSeries (Fin d) C)
      (M : Matrix (Fin d') (Fin d) C), IsIntHom G G' φ M → ∀ u : Fin i → Fin d → C,
      detDepth G u k ≤ detDepth G' (fun a => M.mulVec (u a)) k := by
  intro C _ _ v i d d' k G G' φ M hφ u
  have hX : ∀ b : Fin i, HasSubst
      (fun e : Fin d => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) := fun b =>
    hasSubst_of_constantCoeff_zero fun e => by simp
  let Φ : (Σ _ : Fin i, Fin d') → MvPowerSeries (Σ _ : Fin i, Fin d) C := fun x =>
    subst (fun e : Fin d => (X ⟨x.1, e⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (φ x.2)
  have hΦ : HasSubst Φ := hasSubst_of_constantCoeff_zero fun x =>
    constantCoeff_subst_eq_zero (hX x.1) (fun e => by simp) (hφ.1 x.2)
  have hΦi : ∀ x, MvIsInt v (Φ x) := fun x =>
    ptIntSer_subst (v := v) (hX x.1) (fun e => ptIntSer_X _) (hφ.2.1 x.2)
  have hL0 : ∀ (b : Fin i) (e : Fin d), constantCoeff
      (∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) = 0 := fun b e => by simp
  have hA : HasSubst (expAlong (fun _ : Fin i => G) (fun _ => u)) :=
    hasSubst_of_constantCoeff_zero fun x =>
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (hL0 x.1)) (hL0 x.1)
        ((isExp_expOf G).1 x.2)
  have hcol : (fun x => subst (expAlong (fun _ : Fin i => G) (fun _ => u)) (Φ x)) =
      expAlong (fun _ : Fin i => G') (fun _ a => M.mulVec (u a)) := by
    funext x
    simp only [Φ]
    rw [subst_comp_subst_apply (hX x.1) hA]
    simp only [subst_X hA, expAlong]
    rw [subst_exp_hom hφ (hL0 x.1)]
    congr 1
    funext b
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
  refine le_iInf fun f => iInf_le_of_le ⟨subst Φ f.1, ptIntSer_subst (v := v) hΦ hΦi f.2⟩ (le_of_eq ?_)
  simp only
  rw [subst_comp_subst_apply hΦ hA, hcol]

end GlobalTheory.DepthMono
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDetPowDepthLeOfIntegralLogHomStatement
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupDetPowDepth_le_of_integralLogHom : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (i d d' k : ℕ) (G : LogFGL v d) (G' : LogFGL v d') (φ : Fin d' → MvPowerSeries (Fin d) C) (M : Matrix (Fin d') (Fin d) C), IsIntHom G G' φ M → ∀ u : Fin i → Fin d → C, detDepth G u k ≤ detDepth G' (fun a => M.mulVec (u a)) k := by
  first | exact @GlobalTheory.DepthMono.detDepth_le_of_isIntHom | exact GlobalTheory.DepthMono.detDepth_le_of_isIntHom | (intros; apply GlobalTheory.DepthMono.detDepth_le_of_isIntHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersActIntegralChartEigenDirections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersActIntegralChartEigenDirections
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartAct

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth
  GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart GlobalTheory.LawLog

theorem logOf_eq {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ} (G : Germ.FGLaw k d) (i : Fin d) :
    GlobalTheory.FormalLog.logOf G i = ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i := rfl

theorem subst_act_log {k O : Type} [CommRing k] [Algebra ℚ k] [CommRing O] {d : ℕ} (G : Germ.FGLaw k d)
    (A : Germ.OAct O G) (a : O) (b : Fin d) :
    subst (fun i => subst (oneVar k d) (A.act a i)) (subst (oneVar k d) (GlobalTheory.FormalLog.logOf G b)) =
      ∑ j, coeff (Finsupp.single ((0 : Fin 1), j) 1) (A.act a b) •
        (subst (oneVar k d) (GlobalTheory.FormalLog.logOf G j) : MvPowerSeries (Fin d) k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [subst_oneVar _ cc_oneVar _ (A.const a), logOf_eq, GlobalTheory.TwistCheck.log_act, ← coe_substAlgHom hs_oneVar, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_eq_C_mul, map_smul]
  rfl

theorem isIntHom_actX_and_eigen (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR)
    (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (a : 𝓞 E) :
    IsIntHom (fgl Ch X) (fgl Ch X) (actX Ch X a) (tanX Ch X a) ∧
      ∀ ℓ : Lt1 Dw, (tanX Ch X a).mulVec (lieVec Ch X ℓ) = embX io X ℓ.1 a • lieVec Ch X ℓ := by
  refine ⟨⟨fun b => ?_, fun b α => ?_, fun b => ?_⟩, fun ℓ => ?_⟩
  · refine constantCoeff_subst_eq_zero hs_oneVar cc_oneVar ?_
    rw [constantCoeff_map, (GlobalTheory.IntChartCheck.const_zero Ch).2 a b, map_zero]
  · have e : actX Ch X a b = map (jX X) (subst (oneVar T.V _) (Ch.actT a b)) := by
      rw [actX, map_subst hs_oneVar]
      congr 1
      funext q
      simp [oneVar]
    rw [e, coeff_map]
    exact isIntV_jX X _
  · let _ := io.toAlgebra
    let A : Germ.OAct (𝓞 E) (lawX Ch X) := GlobalTheory.FBMap.mapAct X.ιF Ch.ch.B.A
    have hA : ∀ i, A.act a i = map (jX X) (Ch.actT a i) := fun i => by
      show map X.ιF (Ch.ch.B.A.act a i) = _
      rw [Ch.gen.1.2.1 a i, jX, map_comp]; rfl
    have h := subst_act_log (lawX Ch X) A a b
    simp only [hA, coeff_map] at h
    exact h
  · obtain ⟨χ, hχ⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDir.exists_char c T io ℓ.1
    have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.eigDir_int Xo c T io y Ch ℓ a (χ a) (hχ a)
    have hz : embX io X ℓ.1 a = jX X (χ a) := by
      rw [jX, RingHom.comp_apply, hχ]; rfl
    funext i
    have h2 := congrArg (jX X) (congrFun h i)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, map_sum, map_mul, Pi.smul_apply, smul_eq_mul] at h2
    rw [hz]
    simpa only [Matrix.mulVec, dotProduct, tanX, lieVec, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] using h2

end GlobalTheory.ChartAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersActIntegralChartEigenDirectionsStatement
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integers_act_integralChart_eigenDirections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), ∀ a : 𝓞 E, IsIntHom (fgl Ch X) (fgl Ch X) (actX Ch X a) (tanX Ch X a) ∧ ∀ ℓ : Lt1 Dw, (tanX Ch X a).mulVec (lieVec Ch X ℓ) = embX io X ℓ.1 a • lieVec Ch X ℓ := by
  first | exact @GlobalTheory.ChartAct.isIntHom_actX_and_eigen | exact GlobalTheory.ChartAct.isIntHom_actX_and_eigen | (intros; apply GlobalTheory.ChartAct.isIntHom_actX_and_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralLogHomDiagonalOfLimit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralLogHomDiagonalOfLimit
set_option autoImplicit false

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.DiagLimit

theorem isIntHom_diagonal_of_limit :
    ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (d : ℕ) (G : LogFGL v d) (κ : Type) [Fintype κ] [DecidableEq κ] (U : Matrix (Fin d) κ C) (L : Matrix κ (Fin d) C), (∀ a b, IsIntV v (U a b)) → (∀ a b, IsIntV v (L a b)) → U * L = 1 → ∀ t : κ → C, (∀ r : ℝ, ∃ (t' : κ → C) (A : Matrix (Fin d) (Fin d) C) (φ : Fin d → MvPowerSeries (Fin d) C), IsIntHom G G φ A ∧ (∀ ℓ, A.mulVec (fun e => U e ℓ) = t' ℓ • fun e => U e ℓ) ∧ ∀ ℓ, (r : WithTop ℝ) ≤ v (t' ℓ - t ℓ)) → ∃ φ, IsIntHom G G φ (U * Matrix.diagonal t * L) := by
  intro C _ _ v d G κ _ _ U L hU hL hUL t h
  obtain ⟨φ, h1, h2, h3⟩ := GlobalTheory.IntegralEndLimit.integral_of_limit C v d G
    (U * Matrix.diagonal t * L) (fun r => by
      obtain ⟨t', A, φ, hφ, hA, ht⟩ := h r
      refine ⟨A, fun a b => ?_, φ, hφ.2.1, hφ.1, hφ.2.2⟩
      have e1 : A * U = U * Matrix.diagonal t' := by
        ext e ℓ
        have := congrFun (hA ℓ) e
        rw [Matrix.mul_diagonal, mul_comm]
        exact this
      have e2 : A = U * Matrix.diagonal t' * L := by
        rw [← e1, Matrix.mul_assoc, hUL, Matrix.mul_one]
      have e3 : (U * Matrix.diagonal t * L) a b - A a b =
          ∑ ℓ, U a ℓ * -(t' ℓ - t ℓ) * L ℓ b := by
        rw [e2, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
        ring
      rw [e3]
      refine v.map_le_sum fun ℓ _ => ?_
      rw [v.map_mul, v.map_mul, v.map_neg]
      have := add_le_add (add_le_add (show (0 : WithTop ℝ) ≤ v (U a ℓ) from hU a ℓ) (ht ℓ))
        (show (0 : WithTop ℝ) ≤ v (L ℓ b) from hL ℓ b)
      rwa [zero_add, add_zero] at this)
  exact ⟨φ, h2, h1, h3⟩

end GlobalTheory.DiagLimit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralLogHomDiagonalOfLimitStatement
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralLogHom_diagonal_of_limit : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (d : ℕ) (G : LogFGL v d) (κ : Type) [Fintype κ] [DecidableEq κ] (U : Matrix (Fin d) κ C) (L : Matrix κ (Fin d) C), (∀ a b, IsIntV v (U a b)) → (∀ a b, IsIntV v (L a b)) → U * L = 1 → ∀ t : κ → C, (∀ r : ℝ, ∃ (t' : κ → C) (A : Matrix (Fin d) (Fin d) C) (φ : Fin d → MvPowerSeries (Fin d) C), IsIntHom G G φ A ∧ (∀ ℓ, A.mulVec (fun e => U e ℓ) = t' ℓ • fun e => U e ℓ) ∧ ∀ ℓ, (r : WithTop ℝ) ≤ v (t' ℓ - t ℓ)) → ∃ φ, IsIntHom G G φ (U * Matrix.diagonal t * L) := by
  first | exact @GlobalTheory.DiagLimit.isIntHom_diagonal_of_limit | exact GlobalTheory.DiagLimit.isIntHom_diagonal_of_limit | (intros; apply GlobalTheory.DiagLimit.isIntHom_diagonal_of_limit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomKerEqIffFrobeniusTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomKerEqIffFrobeniusTwist
open Polynomial

namespace GlobalTheory.FrobOrbit

theorem card_le_of_pow_eq_self {k : Type} [Field k] {n : ℕ} (hn : 1 < n) (Z : Finset k)
    (hZ : ∀ x ∈ Z, x ^ n = x) : Z.card ≤ n := by
  have hd := Polynomial.natDegree_X_pow_sub_X (R := k) hn
  have hne : (X ^ n - X : k[X]) ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hd
    omega
  have := card_le_degree_of_subset_roots (p := (X ^ n - X : k[X])) (Z := Z) (by
    intro x hx
    rw [mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, hZ x hx, sub_self])
  rwa [hd] at this

theorem field_case (K k : Type) [Field K] [Fintype K] [Field k] (p : ℕ) [hp : Fact p.Prime]
    [CharP k p] (f : K →+* k) (h : ℕ) (hh : 0 < h) (hc : Fintype.card K = p ^ h) :
    (∀ a, f a ^ p ^ h = f a) ∧ (∀ x : k, x ^ p ^ h = x → ∃ a, f a = x) ∧
    (∀ s t : ℕ, s < h → t < h → (∀ a, f a ^ p ^ s = f a ^ p ^ t) → s = t) ∧
    ∀ g : K →+* k, ∃ s : ℕ, s < h ∧ ∀ a, g a = f a ^ p ^ s := by
  classical
  have h1 : 1 < p := hp.out.one_lt
  have hfix : ∀ a, f a ^ p ^ h = f a := fun a => by
    rw [← map_pow, ← hc, FiniteField.pow_card]
  have himg : (Finset.univ.image f).card = p ^ h := by
    rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ, hc]
  have hlt : ∀ s t : ℕ, s < t → t < h → ¬ ∀ a, f a ^ p ^ s = f a ^ p ^ t := by
    intro s t hst hth H
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hst
    have hle := card_le_of_pow_eq_self (k := k) (n := p ^ (d + 1))
      (Nat.one_lt_pow (Nat.succ_ne_zero d) h1) (Finset.univ.image f) (by
        intro x hx
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
        apply (iterateFrobenius k p s).injective
        rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add, H a]
        congr 2
        omega)
    rw [himg] at hle
    have := (Nat.pow_le_pow_iff_right h1).1 hle
    omega
  have hinj : ∀ s t : ℕ, s < h → t < h → (∀ a, f a ^ p ^ s = f a ^ p ^ t) → s = t := by
    intro s t hs ht H
    rcases lt_trichotomy s t with hst | hst | hst
    · exact absurd H (hlt s t hst ht)
    · exact hst
    · exact absurd (fun a => (H a).symm) (hlt t s hst hs)
  refine ⟨hfix, ?_, hinj, ?_⟩
  · intro x hx
    by_contra hne
    have hx' : x ∉ Finset.univ.image f := by
      intro hm
      obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hm
      exact hne ⟨a, ha⟩
    have hle := card_le_of_pow_eq_self (k := k) (n := p ^ h)
      (Nat.one_lt_pow hh.ne' h1) (insert x (Finset.univ.image f)) (by
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact hx
        · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
          exact hfix a)
    rw [Finset.card_insert_of_notMem hx', himg] at hle
    omega
  · intro g
    haveI : CharP K p := RingHom.charP f f.injective p
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    let toAlg : (K →+* k) → (K →ₐ[ZMod p] k) := fun φ =>
      { φ with
        commutes' := fun r =>
          congrArg (fun ψ : ZMod p →+* k => ψ r)
            (Subsingleton.elim (φ.comp (algebraMap (ZMod p) K)) (algebraMap (ZMod p) k)) }
    have toAlg_apply : ∀ φ a, toAlg φ a = φ a := fun _ _ => rfl
    have hrank : Module.finrank (ZMod p) K = h := by
      have := Module.card_eq_pow_finrank (K := ZMod p) (V := K)
      rw [ZMod.card, hc] at this
      exact (Nat.pow_right_injective h1 this).symm
    let F : Fin h → (K →ₐ[ZMod p] k) := fun s => toAlg ((iterateFrobenius k p s.val).comp f)
    have hF : ∀ s a, F s a = f a ^ p ^ s.val := fun s a => rfl
    have hFinj : Function.Injective F := by
      intro s t hst
      apply Fin.ext
      apply hinj _ _ s.2 t.2
      intro a
      rw [← hF, ← hF, hst]
    have hbij := hFinj.bijective_of_nat_card_le (by
      have := card_algHom_le_finrank (ZMod p) K k
      rw [hrank] at this
      simpa using this)
    obtain ⟨s, hs⟩ := hbij.2 (toAlg g)
    exact ⟨s.val, s.2, fun a => by rw [← hF, hs, toAlg_apply]⟩

theorem ringHom_ker_eq_iff_frobenius_twist :
    ∀ (R k : Type) [CommRing R] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (f : R →+* k) (h : ℕ),
      0 < h → Nat.card (R ⧸ RingHom.ker f) = p ^ h →
      (∀ x : k, x ^ p ^ h = x → ∃ a, f a = x) ∧
      ∃ F : ZMod h → (R →+* k), (∀ s a, F s a = f a ^ p ^ s.val) ∧
        (∀ s a, F (s + 1) a = F s a ^ p) ∧ Function.Injective F ∧
        ∀ g : R →+* k, RingHom.ker g = RingHom.ker f ↔ ∃ s, F s = g := by
  intro R k _ _ p hp _ f h hh hc
  haveI : NeZero h := ⟨hh.ne'⟩
  haveI : Finite (R ⧸ RingHom.ker f) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp.out.ne_zero)
  haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  haveI : (RingHom.ker f).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isDomain_to_isField _)
  letI : Field (R ⧸ RingHom.ker f) := Ideal.Quotient.field _
  letI : Fintype (R ⧸ RingHom.ker f) := Fintype.ofFinite _
  obtain ⟨hfix, hsurj, hinj, hall⟩ := field_case (R ⧸ RingHom.ker f) k p (RingHom.kerLift f) h hh
    (by rw [← Nat.card_eq_fintype_card, hc])
  have hmk : ∀ a, RingHom.kerLift f (Ideal.Quotient.mk _ a) = f a := RingHom.kerLift_mk f
  have hfix' : ∀ a, f a ^ p ^ h = f a := fun a => by
    have := hfix (Ideal.Quotient.mk _ a)
    exact this
  have hmod : ∀ (a : R) (n : ℕ), f a ^ p ^ (n % h) = f a ^ p ^ n := by
    intro a n
    have hm : ∀ m : ℕ, f a ^ p ^ (h * m) = f a := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hfix']
    conv_rhs => rw [← Nat.div_add_mod n h, pow_add, pow_mul, hm]
  refine ⟨fun x hx => ?_, fun s => (iterateFrobenius k p s.val).comp f, fun s a => rfl,
    fun s a => ?_, fun s t hst => ?_, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · obtain ⟨a, ha⟩ := hsurj x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨b, ha⟩
  · change f a ^ p ^ (s + 1).val = (f a ^ p ^ s.val) ^ p
    have hv : (s + 1).val = (s.val + 1) % h := by
      rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    rw [hv, hmod, pow_succ, pow_mul]
  · apply ZMod.val_injective h
    apply hinj _ _ (ZMod.val_lt s) (ZMod.val_lt t)
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact congrArg (fun φ : R →+* k => φ b) hst
  · obtain ⟨s, hs, hgs⟩ := hall (Ideal.Quotient.lift (RingHom.ker f) g
      (fun a ha => by rw [← hg] at ha; exact ha))
    refine ⟨(s : ZMod h), RingHom.ext fun a => ?_⟩
    change f a ^ p ^ ((s : ZMod h)).val = g a
    rw [ZMod.val_cast_of_lt hs]
    exact (hgs (Ideal.Quotient.mk _ a)).symm
  · rintro ⟨s, rfl⟩
    ext a
    rw [RingHom.mem_ker, RingHom.mem_ker]
    change f a ^ p ^ s.val = 0 ↔ f a = 0
    exact pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero)

end GlobalTheory.FrobOrbit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomKerEqIffFrobeniusTwistStatement
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_ker_eq_iff_frobeniusTwist : ∀ (R k : Type) [CommRing R] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (f : R →+* k) (h : ℕ), 0 < h → Nat.card (R ⧸ RingHom.ker f) = p ^ h → (∀ x : k, x ^ p ^ h = x → ∃ a, f a = x) ∧ ∃ F : ZMod h → (R →+* k), (∀ s a, F s a = f a ^ p ^ s.val) ∧ (∀ s a, F (s + 1) a = F s a ^ p) ∧ Function.Injective F ∧ ∀ g : R →+* k, RingHom.ker g = RingHom.ker f ↔ ∃ s, F s = g := by
  first | exact @GlobalTheory.FrobOrbit.ringHom_ker_eq_iff_frobenius_twist | exact GlobalTheory.FrobOrbit.ringHom_ker_eq_iff_frobenius_twist | (intros; apply GlobalTheory.FrobOrbit.ringHom_ker_eq_iff_frobenius_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupRootsOfUnityTypedLieRanks
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

section Abstract

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d d' : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
  {U : Matrix (Fin d) κ C} {L : Matrix κ (Fin d) C}

theorem cut_diagonal (hLU : L * U = 1) {j : Fin d' → κ} (hj : Function.Injective j) (t : κ → C) :
    L.submatrix j id * (U * Matrix.diagonal t * L) * U.submatrix id j = Matrix.diagonal fun b => t (j b) := by
  have h : L * (U * Matrix.diagonal t * L) * U = Matrix.diagonal t := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hLU, Matrix.one_mul, Matrix.mul_assoc, hLU, Matrix.mul_one]
  have h2 : L.submatrix j id * (U * Matrix.diagonal t * L) * U.submatrix id j =
      (L * (U * Matrix.diagonal t * L) * U).submatrix j j := by
    ext a b; simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  rw [h2, h, Matrix.submatrix_diagonal _ _ hj]; rfl

theorem proj_eq {j : Fin d' → κ} (hj : Function.Injective j) (t : κ → C) (h1 : ∀ b, t (j b) = 1)
    (h0 : ∀ ℓ, (¬ ∃ b, j b = ℓ) → t ℓ = 0) :
    U.submatrix id j * L.submatrix j id = U * Matrix.diagonal t * L := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_of_injOn j hj.injOn (fun _ _ => by simp) (fun ℓ _ hℓ => ?_) fun b' _ => by rw [h1, mul_one]
  rw [h0 ℓ (by simpa using hℓ), mul_zero, zero_mul]

theorem diagonal_mulVec (hLU : L * U = 1) (t : κ → C) (ℓ : κ) :
    (U * Matrix.diagonal t * L).mulVec (fun e => U e ℓ) = t ℓ • fun e => U e ℓ := by
  have h : U * Matrix.diagonal t * L * U = U * Matrix.diagonal t := by rw [Matrix.mul_assoc, hLU, Matrix.mul_one]
  funext e
  have := congrFun (congrFun h e) ℓ
  rw [Matrix.mul_diagonal, Matrix.mul_apply] at this
  simpa [Matrix.mulVec, dotProduct, mul_comm] using this

theorem coord_mulVec (hLU : L * U = 1) (j : Fin d' → κ) (ℓ : κ) (b : Fin d') :
    (L.submatrix j id).mulVec (fun e => U e ℓ) b = if j b = ℓ then 1 else 0 := by
  have := congrFun (congrFun hLU (j b)) ℓ
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

theorem intSpan_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (u : β → Fin d → C) :
    intSpan v (fun a => u (e a)) = intSpan v u := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨fun k => a (e.symm k), fun k => ha _, by rw [← e.sum_comp]; simp⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨fun k => a (e k), fun k => ha _, by rw [← e.sum_comp]⟩

theorem nonempty_muAction (G : LogFGL v d) (p h : ℕ) (ty : Fin d → ZMod h)
    (hz : ∀ z : C, z ^ (p ^ h - 1) = 1 → ∃ φ, IsIntHom G G φ (Matrix.diagonal fun b => z ^ p ^ (ty b).val)) :
    Nonempty (MuAction G p h ty) := by
  classical
  choose φ hφ using hz
  refine ⟨⟨fun z => if hz : z ^ (p ^ h - 1) = 1 then φ z hz else 0, fun z hz a => ?_, fun z a => ?_, fun z hz a => ?_⟩⟩
  · rw [dite_eq_left hz]; exact (hφ z hz).2.1 a
  · split_ifs with hz
    · exact (hφ z hz).1 a
    · simp
  · rw [dite_eq_left hz, (hφ z hz).2.2 a]
    simp [Matrix.diagonal_apply, ite_smul]

end Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {p : ℕ} [Fact p.Prime]

theorem exists_orbit (X : ValExt T p) (hp : UnramIn E p) (τ : E →+* ℂ) :
    ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ primeBelow io X τ) = p ^ h ∧ ∃ lab : ZMod h → (E →+* ℂ), IsOrbit io X τ lab ∧
      (∀ s a, X.v (embX io X (lab s) a - embX io X τ a ^ p ^ s.val) < 1) ∧
      ∀ z : X.C, z ^ (p ^ h - 1) = 1 → ∃ a₀ : 𝓞 E, X.v (embX io X τ a₀ - z) < 1 := by
  obtain ⟨-, h, h0, hc⟩ := GlobalTheory.T.primeBelowComplexEmbeddingLabel_isMaximal_card E H l c p T io X τ
  haveI := charP_residueField_of_irreducible X
  obtain ⟨hon, F, Fp, Fs, Fi, Fk⟩ := GlobalTheory.T.ringHom_ker_eq_iff_frobeniusTwist (𝓞 E) _ p (red io X τ) h h0 (by rw [← primeBelow_eq_ker]; exact hc)
  obtain ⟨hi, hs⟩ := GlobalTheory.T.embeddingReducedResidueField_bijective_unramified E H l c p T io X hp
  choose lab hlab using fun s => hs (F s)
  refine ⟨h, h0, hc, lab, ⟨hi ?_, fun s a => ?_, fun s s' e => Fi ?_, fun σ => ?_⟩, fun s a => ?_, fun z hz => ?_⟩
  · rw [hlab]; ext a; rw [Fp]; simp
  · rw [← red_eq_pow_iff, hlab, hlab, Fs]
  · rw [← hlab, ← hlab, e]
  · rw [primeBelow_eq_ker, primeBelow_eq_ker, Fk]
    exact exists_congr fun s => by rw [← hlab, hi.eq_iff]
  · rw [← red_eq_pow_iff, hlab, Fp]
  · have hq : p ^ h - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow h0.ne' (Fact.out : p.Prime).one_lt)
    obtain ⟨z', hz'⟩ := X.ints.exists_of_le_one
      ((isIntV_iff X z).1 (le_of_eq (v_eq_zero_of_pow_eq_one hq hz).symm))
    have h1 : z' ^ p ^ h = z' := X.ints.hom_inj (by
      rw [map_pow, hz', ← Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.lt_of_sub_ne_zero hq)), pow_succ, hz, one_mul])
    obtain ⟨a, ha⟩ := hon (residue X.O z') (by rw [← map_pow, h1])
    refine ⟨a, ?_⟩
    rw [← hz', ← algebraMap_embO, ← residue_eq_iff_v]
    exact ha

variable [StarRing (𝓞 E)] {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p)

theorem exists_hom_of_approx [DecidableEq (Lt1 Dw)] {L : Matrix (Lt1 Dw) (Fin (chD Ch.ch)) X.C}
    (hL : ∀ a b, IsIntV (vX_vp X) (L a b)) (hUL : (Matrix.of fun e ℓ => lieVec Ch X ℓ e) * L = 1)
    (t : (E →+* ℂ) → X.C) (ht : ∀ r : ℝ, ∃ a : 𝓞 E, ∀ σ, (r : WithTop ℝ) ≤ vX_vp X (embX io X σ a - t σ)) :
    ∃ φ, IsIntHom (fgl Ch X) (fgl Ch X) φ
      ((Matrix.of fun e ℓ => lieVec Ch X ℓ e) * Matrix.diagonal (fun ℓ : Lt1 Dw => t ℓ.1) * L) := by
  refine GlobalTheory.T.isIntegralLogHom_diagonal_of_limit X.C (vX_vp X) _ (fgl Ch X) (Lt1 Dw) _ L (fun e ℓ => isIntV_jX X _) hL hUL _ fun r => ?_
  obtain ⟨a, ha⟩ := ht r
  obtain ⟨h1, h2⟩ := GlobalTheory.T.integers_act_integralChart_eigenDirections E H Dw l Xo c p T io X y Ch a
  exact ⟨fun ℓ => embX io X ℓ.1 a, _, _, h1, h2, fun ℓ => ha ℓ.1⟩

theorem typedPartAt (hp : UnramIn E p) (τ : E →+* ℂ) : TypedPartAt Ch X τ := by
  classical
  obtain ⟨h, h0, hc, lab, horb, hpow, hroot⟩ := exists_orbit (io := io) X hp τ
  haveI : NeZero h := ⟨h0.ne'⟩
  obtain ⟨L, hL, hLU, hUL⟩ := GlobalTheory.T.label_directions_integral_basis_unramified_prime E H Dw l Xo c p T io X y Ch hp
  set U : Matrix (Fin (chD Ch.ch)) (Lt1 Dw) X.C := Matrix.of fun e ℓ => lieVec Ch X ℓ e with hU
  obtain ⟨-, -, hinj, hker⟩ := id horb

  let t : X.C → (E →+* ℂ) → X.C := fun z => Function.extend lab (fun s => z ^ p ^ s.val) 0
  have ht1 : ∀ z s, t z (lab s) = z ^ p ^ s.val := fun z s => hinj.extend_apply _ _ s
  have ht0 : ∀ z σ, (¬ ∃ s, lab s = σ) → t z σ = 0 := fun z σ hσ => Function.extend_apply' _ _ σ hσ
  have happ : ∀ z : X.C, z ^ (p ^ h - 1) = 1 → ∀ r : ℝ, ∃ a : 𝓞 E, ∀ σ,
      (r : WithTop ℝ) ≤ vX_vp X (embX io X σ a - t z σ) := by
    intro z hz r
    obtain ⟨a, h1, h2⟩ := GlobalTheory.T.exists_integers_approximating_root_of_unity_twists E H l c p T io X τ h h0 lab hpow z hz (hroot z hz) r
    refine ⟨a, fun σ => ?_⟩
    by_cases hσ : ∃ s, lab s = σ
    · obtain ⟨s, rfl⟩ := hσ
      rw [ht1]; exact h1 s
    · rw [ht0 z σ hσ, sub_zero]; exact h2 σ fun e => hσ ((hker σ).1 e)

  let K := Σ s : ZMod h, Fin (Dw.mult (lab s))
  let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let j₀ : K → Lt1 Dw := fun k => ⟨lab k.1, k.2⟩
  have hj₀ : Function.Injective j₀ := by
    rintro ⟨s, k⟩ ⟨s', k'⟩ hk
    obtain rfl : s = s' := hinj (congrArg Sigma.fst hk)
    obtain rfl : k = k' := eq_of_heq (Sigma.mk.inj hk).2
    rfl
  let j : Fin (Fintype.card K) → Lt1 Dw := fun b => j₀ (e b)
  have hj : Function.Injective j := hj₀.comp e.injective
  have hjr : ∀ ℓ : Lt1 Dw, (∃ s, lab s = ℓ.1) → ∃ b, j b = ℓ := by
    rintro ⟨σ, k⟩ ⟨s, rfl⟩
    exact ⟨e.symm ⟨s, k⟩, congrArg j₀ (e.apply_symm_apply _)⟩
  have hIP : U.submatrix id j * L.submatrix j id = U * Matrix.diagonal (fun ℓ : Lt1 Dw => t 1 ℓ.1) * L :=
    proj_eq hj _ (fun b => by rw [show (j b).1 = lab (e b).1 from rfl, ht1, one_pow])
      fun ℓ hℓ => ht0 1 _ fun hs => hℓ (hjr ℓ hs)
  have hPI : L.submatrix j id * U.submatrix id j = 1 := by
    have := cut_diagonal hLU hj (fun _ => 1)
    rwa [Matrix.diagonal_one, Matrix.mul_one, hUL, Matrix.mul_one, Matrix.diagonal_one] at this
  have hco : (1 : Matrix _ _ X.C) - U.submatrix id j * L.submatrix j id =
      U * Matrix.diagonal (fun ℓ : Lt1 Dw => 1 - t 1 ℓ.1) * L := by
    rw [hIP, ← Matrix.diagonal_sub, Matrix.diagonal_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUL]
  obtain ⟨G', ⟨ι', hι⟩, ⟨π', hπ⟩⟩ := GlobalTheory.T.logarithmic_group_law_split_by_idempotent X.C (vX_vp X) _ _ (fgl Ch X) (U.submatrix id j) (L.submatrix j id)
    (fun a b => isIntV_jX X _) (fun a b => hL _ _) hPI
    (by rw [hIP]; exact exists_hom_of_approx Ch X hL hUL (t 1) (happ 1 (one_pow _)))
    (by
      rw [hco]
      refine exists_hom_of_approx Ch X hL hUL (fun σ => 1 - t 1 σ) fun r => ?_
      obtain ⟨a, ha⟩ := happ 1 (one_pow _) r
      refine ⟨1 - a, fun σ => ?_⟩
      rw [map_sub (embX io X σ), map_one, sub_sub_sub_cancel_left, AddValuation.map_sub_swap]
      exact ha σ)
  have hfix : ∀ ℓ : Lt1 Dw, (U.submatrix id j * L.submatrix j id).mulVec (lieVec Ch X ℓ) =
      t 1 ℓ.1 • lieVec Ch X ℓ := fun ℓ => by
    rw [hIP]; exact diagonal_mulVec hLU _ ℓ
  have hco' : ∀ (ℓ : Lt1 Dw) b, (L.submatrix j id).mulVec (lieVec Ch X ℓ) b = if j b = ℓ then 1 else 0 :=
    fun ℓ b => coord_mulVec hLU j ℓ b
  let q : ∀ s, {b : Fin (Fintype.card K) // (e b).1 = s} ≃ Fin (Dw.mult (lab s)) := fun s =>
    (e.subtypeEquiv (q := fun k : K => k.1 = s) fun _ => Iff.rfl).trans (Equiv.sigmaSubtype s)
  have hq : ∀ s b, j b.1 = ⟨lab s, q s b⟩ := by
    rintro s ⟨b, rfl⟩; rfl
  refine ⟨h, h0, hc, lab, horb, _, G', fun b => (e b).1, U.submatrix id j, L.submatrix j id,
    ⟨⟨ι', hι⟩, ⟨π', hπ⟩, hPI, fun ℓ => ⟨fun hℓ => ?_, fun hℓ => ?_⟩⟩, nonempty_muAction _ _ _ _ fun z hz => ?_,
    fun s => ?_, fun s => ?_, fun s f hf => ⟨⟨fun a b => ?_, ?_⟩, fun a b hb => ?_, fun k => le_antisymm ?_ ?_⟩⟩
  · obtain ⟨s, hs⟩ := (hker _).1 hℓ
    rw [hfix, ← hs, ht1, one_pow, one_smul]
  · rw [hfix, ht0 1 _ fun hs => hℓ ((hker _).2 hs), zero_smul]
  · obtain ⟨φ, hφ⟩ := exists_hom_of_approx Ch X hL hUL (t z) (happ z hz)
    have := isIntHom_comp hι (isIntHom_comp hφ hπ)
    rw [cut_diagonal hLU hj] at this
    exact ⟨_, by simpa only [show ∀ b, (j b).1 = lab (e b).1 from fun _ => rfl, ht1] using this⟩
  · rw [← intSpan_equiv (q s)]
    congr 1
    funext b
    rw [← hq]; rfl
  · rw [Fintype.card_congr (q s), Fintype.card_fin, Dw.rank, Nat.add_sub_cancel]
    unfold Datum.mult InPsi
    congr
  · beta_reduce; rw [frame, hco']; unfold IsIntV; split_ifs <;> simp
  · choose r hr using fun a : Fin (rk f) => hjr ⟨f.1, Fin.castLE (rk_le f) a⟩ ⟨s, hf.symm⟩
    refine ⟨r, ?_⟩
    have : (Matrix.of fun a b => (L.submatrix j id).mulVec (frame Ch X f a) (r b)) = 1 := by
      ext a b
      rw [Matrix.of_apply, frame, hco', hr, Matrix.one_apply]
      simp [eq_comm]
    rw [this]; simp
  · rw [frame, hco', if_neg]
    intro hb'
    exact hb (hinj ((congrArg Sigma.fst hb').trans hf))
  · exact GlobalTheory.T.formalGroupDetPowDepth_le_of_integralLogHom X.C _ _ _ _ k _ _ _ _ hπ _
  · have := GlobalTheory.T.formalGroupDetPowDepth_le_of_integralLogHom X.C _ _ _ _ k _ _ _ _ hι fun a => (L.submatrix j id).mulVec (frame Ch X f a)
    simp only [Matrix.mulVec_mulVec, frame, hfix, hf, ht1, one_pow, one_smul] at this
    exact this

theorem formalGroupTypes : FormalGroupTypes := fun E _ _ _ H _ l _ c _ _ p _ hp T io X =>
  ⟨GlobalTheory.T.frobenius_acts_on_type_at_valuation E H l c p T io X, fun _ Ch τ => typedPartAt Ch X hp τ⟩

end GlobalTheory.PrimePart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupRootsOfUnityTypedLieRanksStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroup_rootsOfUnity_typed_lieRanks : GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes.FormalGroupTypes := by
  first | exact @GlobalTheory.PrimePart.formalGroupTypes | exact GlobalTheory.PrimePart.formalGroupTypes | (intros; apply GlobalTheory.PrimePart.formalGroupTypes <;> assumption)
end
