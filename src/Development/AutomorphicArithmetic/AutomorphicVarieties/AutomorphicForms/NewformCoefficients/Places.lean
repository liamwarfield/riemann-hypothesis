module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasSatOfFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwMemMul

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.Sd

theorem UpperTheory.V.Af.Nf.places :
    UpperTheory.V.Af.Nf.Places := by
  intro w
  have hq := Rat.HeightOneSpectrum.prime_natGenerator w
  have hspan := Rat.HeightOneSpectrum.span_natGenerator w
  have hN : normV w = Rat.HeightOneSpectrum.natGenerator w := by
    unfold normV
    rw [Nat.card_congr (Ideal.quotientEquiv w.asIdeal _
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hspan).toEquiv,
      Nat.card_congr (Int.quotientSpanNatEquivZMod _).toEquiv, Nat.card_zmod]
  have hP : w.asIdeal =
      Ideal.span {((Rat.HeightOneSpectrum.natGenerator w : ℕ) : 𝓞 ℚ)} := by
    ext x
    rw [Ideal.mem_span_singleton,
      ← Ideal.apply_mem_of_equiv_iff (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), ← hspan,
      Ideal.mem_span_singleton,
      ← map_dvd_iff (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_natCast]
  refine ⟨by rw [hN]; exact hq, by rw [hN]; exact hP, ?_, ?_⟩
  · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  · intro M hM hndvd
    unfold UpperTheory.V.Af.Nf.lev ordI
    have hne : Ideal.span {(M : 𝓞 ℚ)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (by omega : M ≠ 0)
    by_contra hc
    rw [← Ne, Associates.count_ne_zero_iff_dvd hne w.irreducible, Ideal.dvd_iff_le,
      Ideal.span_singleton_le_iff_mem] at hc
    apply hndvd
    rw [hN, Rat.HeightOneSpectrum.natGenerator_dvd_iff,
      ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) M, Ideal.apply_mem_of_equiv_iff]
    exact hc
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.IntOfIntegers
open NumberField IsDedekindDomain GlobalTheory.CuspRep

namespace UpperTheory.V.Af.Nf

private theorem memO {x : Af ℚ} :
    x ∈ Ohat ℚ ↔ ∀ v : HeightOneSpectrum (𝓞 ℚ), x v ∈ v.adicCompletionIntegers ℚ := by
  rw [Ohat, Subring.mem_iInf]
  rfl

private theorem int_of_integers (x : 𝓞 ℚ) : ∃ n : ℤ, (x : ℚ) = n :=
  ⟨Rat.ringOfIntegersEquiv x, (Rat.ringOfIntegersEquiv_apply_coe x).symm⟩

private theorem dense_int (M : ℕ) (hM : 1 ≤ M) (x : Af ℚ) (hx : x ∈ Ohat ℚ) :
    ∃ d : ℤ, ∃ y ∈ Ohat ℚ, x - d = M * y := by
  obtain ⟨r, a, ha, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat ℚ M hM).2 x (memO.1 hx)
  obtain ⟨n, hn⟩ := int_of_integers r
  refine ⟨n, a, memO.2 ha, ?_⟩
  rw [e, hn, map_intCast, nsmul_eq_mul]
  ring

private theorem exists_den (y : Af ℚ) : ∃ N : ℕ, 1 ≤ N ∧ (N : Af ℚ) * y ∈ Ohat ℚ := by
  obtain ⟨r, a, ha, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat ℚ 1 one_pos).1 y
  refine ⟨r.den, r.den_pos, ?_⟩
  have h : (r.den : Af ℚ) * algebraMap ℚ (Af ℚ) r = (r.num : Af ℚ) := by
    rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, Rat.den_mul_eq_num, map_intCast]
  rw [e, mul_add, h, one_smul]
  exact add_mem (intCast_mem _ _) (mul_mem (natCast_mem _ _) (memO.2 ha))

private theorem class_one (y : (Af ℚ)ˣ) : ∃ (r : ℚˣ) (u : (Af ℚ)ˣ), 0 < (r : ℚ) ∧ IsZU u ∧
    y = Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r * u := by
  classical
  obtain ⟨N, hN, ha⟩ := exists_den (y : Af ℚ)
  obtain ⟨M, hM, hb⟩ := exists_den ((y⁻¹ : (Af ℚ)ˣ) : Af ℚ)
  set a : Af ℚ := N * y with ha'
  set b : Af ℚ := M * ((y⁻¹ : (Af ℚ)ˣ) : Af ℚ) with hb'
  have hab : a * b = ((N * M : ℕ) : Af ℚ) := by
    rw [ha', hb', mul_mul_mul_comm, Units.mul_inv, mul_one, Nat.cast_mul]
  let I : Ideal ℤ :=
    { carrier := {n | ∃ w ∈ Ohat ℚ, (n : Af ℚ) = a * w}
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      add_mem' := by
        rintro m n ⟨w, hw, e⟩ ⟨w', hw', e'⟩
        exact ⟨w + w', add_mem hw hw', by rw [Int.cast_add, e, e', mul_add]⟩
      smul_mem' := by
        rintro c n ⟨w, hw, e⟩
        exact ⟨c * w, mul_mem (intCast_mem _ _) hw, by rw [smul_eq_mul, Int.cast_mul, e]; ring⟩ }
  obtain ⟨d₀, hd₀⟩ := (IsPrincipalIdealRing.principal I).principal
  have hI : I = Ideal.span {|d₀|} := by
    rw [hd₀, Ideal.submodule_span_eq, Ideal.span_singleton_abs]
  set d : ℤ := |d₀| with hd
  have hL : ((N * M : ℕ) : ℤ) ∈ I := ⟨b, hb, by rw [hab, Int.cast_natCast]⟩
  obtain ⟨w, hw, hdw⟩ : d ∈ I := hI ▸ Ideal.mem_span_singleton_self d
  obtain ⟨n, z, hz, hn⟩ := dense_int (N * M) (Nat.mul_pos hN hM) a ha
  have hnI : n ∈ I := ⟨1 - b * z, sub_mem (one_mem _) (mul_mem hb hz), by
    rw [← hab] at hn; linear_combination -hn⟩
  rw [hI, Ideal.mem_span_singleton] at hL hnI
  obtain ⟨l, hl⟩ := hL
  obtain ⟨k, hk⟩ := hnI
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, zero_mul, Nat.cast_eq_zero] at hl
    exact (Nat.mul_pos hN hM).ne' hl
  have hdpos : (0 : ℚ) < d := by exact_mod_cast lt_of_le_of_ne (abs_nonneg d₀) hd0.symm
  have hNpos : (0 : ℚ) < N := by exact_mod_cast hN
  have hl' : ((N * M : ℕ) : Af ℚ) = d * l := by
    rw [← Int.cast_natCast, hl, Int.cast_mul]
  have hau : a = d * ((k : Af ℚ) + l * z) := by
    rw [hk, hl', Int.cast_mul] at hn
    linear_combination hn
  have hdi : algebraMap ℚ (Af ℚ) (d : ℚ)⁻¹ * d = 1 := by
    rw [← map_intCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hdpos.ne', map_one]
  have hNi : algebraMap ℚ (Af ℚ) (N : ℚ)⁻¹ * N = 1 := by
    rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hNpos.ne', map_one]
  have huw : ((k : Af ℚ) + l * z) * w = 1 := by
    rw [hau] at hdw
    linear_combination (-algebraMap ℚ (Af ℚ) (d : ℚ)⁻¹) * hdw + (1 - ((k : Af ℚ) + l * z) * w) * hdi
  refine ⟨Units.mk0 (d / N) (div_pos hdpos hNpos).ne', ⟨(k : Af ℚ) + l * z, w, huw, by rw [mul_comm, huw]⟩,
    div_pos hdpos hNpos, ⟨add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _) hz), hw⟩, Units.ext ?_⟩
  change (y : Af ℚ) = algebraMap ℚ (Af ℚ) ((d : ℚ) / N) * ((k : Af ℚ) + l * z)
  rw [div_eq_mul_inv, map_mul, map_intCast]
  rw [ha'] at hau
  linear_combination (algebraMap ℚ (Af ℚ) (N : ℚ)⁻¹) * hau - (y : Af ℚ) * hNi

private theorem val_le (K : Type) [Field K] [NumberField K] (r : K) (v : HeightOneSpectrum (𝓞 K))
    (h : algebraMap K (Af K) r v ∈ v.adicCompletionIntegers K) : v.valuation K r ≤ 1 :=
  (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v r).symm.trans_le h

private theorem rat_int (r : ℚ) (hr : algebraMap ℚ (Af ℚ) r ∈ Ohat ℚ) : ∃ n : ℤ, r = n := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ r fun v =>
    val_le ℚ r v (memO.1 hr v)
  obtain ⟨n, hn⟩ := int_of_integers x
  exact ⟨n, hx.symm.trans hn⟩

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.ratAd :
    UpperTheory.V.Af.Nf.RatAd :=
  ⟨UpperTheory.V.Af.Nf.class_one, UpperTheory.V.Af.Nf.dense_int, UpperTheory.V.Af.Nf.rat_int⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMul
open UpperHalfPlane

namespace UpperTheory.V.Af.Nf

end UpperTheory.V.Af.Nf

private theorem lower_row_mul_add_ne_zero_of_det_ne_zero (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) (w : ℍ) :
    (x 1 0 : ℂ) * (w : ℂ) + (x 1 1 : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  rcases him with h1 | h1
  · apply hx
    rw [Matrix.det_fin_two]
    simp [h1] at hre
    simp [h1, hre]
  · exact absurd h1 w.im_pos.ne'

private theorem im_mobius_pos_of_det_pos (y : Matrix (Fin 2) (Fin 2) ℝ) (hy : 0 < y.det) (z : ℍ) :
    0 < (((y 0 0 : ℂ) * z + y 0 1) / ((y 1 0 : ℂ) * z + y 1 1)).im := by
  have hj := lower_row_mul_add_ne_zero_of_det_ne_zero y hy.ne' z
  rw [Complex.div_im]
  have hn : 0 < Complex.normSq ((y 1 0 : ℂ) * z + y 1 1) := Complex.normSq_pos.mpr hj
  rw [← sub_div]
  apply div_pos _ hn
  have hd := hy
  rw [Matrix.det_fin_two] at hd
  simp
  nlinarith [z.im_pos]

open UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.nslMul :
    UpperTheory.V.Af.Nf.NslMul := by
  intro k f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    funext z
    have hjy := lower_row_mul_add_ne_zero_of_det_ne_zero y hy.ne' z
    have hm := im_mobius_pos_of_det_pos y hy z
    set m := ((y 0 0 : ℂ) * z + y 0 1) / ((y 1 0 : ℂ) * z + y 1 1) with hmdef
    simp only [nsl]
    rw [sign_pos hy, Matrix.det_mul, sign_mul, sign_pos hy, mul_one, abs_mul,
      Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    simp only [SignType.coe_one, Int.cast_one, Complex.ofReal_one, one_mul]
    rw [← hmdef, UpperHalfPlane.ofComplex_apply_of_im_pos hm]
    simp only [UpperHalfPlane.coe_mk, Matrix.mul_apply, Fin.sum_univ_two]
    have hJ : ((↑(x 1 0 * y 0 0 + x 1 1 * y 1 0) : ℂ) * z + ↑(x 1 0 * y 0 1 + x 1 1 * y 1 1)) =
        ((x 1 0 : ℂ) * m + x 1 1) * ((y 1 0 : ℂ) * z + y 1 1) := by
      rw [hmdef, add_mul, mul_assoc, div_mul_cancel₀ _ hjy]
      push_cast
      ring
    have hN : ((↑(x 0 0 * y 0 0 + x 0 1 * y 1 0) : ℂ) * z + ↑(x 0 0 * y 0 1 + x 0 1 * y 1 1)) =
        ((x 0 0 : ℂ) * m + x 0 1) * ((y 1 0 : ℂ) * z + y 1 1) := by
      rw [hmdef, add_mul, mul_assoc, div_mul_cancel₀ _ hjy]
      push_cast
      ring
    rw [hJ, hN, mul_div_mul_right _ _ hjy, mul_zpow]
    push_cast
    ring
  · intro x
    funext z
    simp only [nsl, eps, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp
    have h1 : -(x 0 0 * x 1 1) + x 0 1 * x 1 0 = -(x 0 0 * x 1 1 - x 0 1 * x 1 0) := by ring
    rw [h1, abs_neg, Left.sign_neg]
    congr 3
    push_cast
    ring
  · intro t x ht
    funext z
    simp only [nsl, Matrix.det_fin_two, Matrix.smul_apply, smul_eq_mul]
    have h1 : t * x 0 0 * (t * x 1 1) - t * x 0 1 * (t * x 1 0) =
        t ^ 2 * (x 0 0 * x 1 1 - x 0 1 * x 1 0) := by ring
    rw [h1]
    set d := x 0 0 * x 1 1 - x 0 1 * x 1 0
    have h2 : SignType.sign (t ^ 2 * d) = SignType.sign d := by
      rw [sign_mul, sign_pos (by positivity), one_mul]
    have h3 : |t ^ 2 * d| ^ ((k : ℝ) / 2) = t ^ k * |d| ^ ((k : ℝ) / 2) := by
      rw [abs_mul, Real.mul_rpow (by positivity) (abs_nonneg _),
        abs_of_pos (by positivity : (0:ℝ) < t ^ 2)]
      congr 1
      rw [show (t ^ 2 : ℝ) = t ^ (2:ℝ) by norm_cast, ← Real.rpow_mul ht.le,
        show (2:ℝ) * (k / 2) = k by ring, Real.rpow_natCast]
    have hj : ((↑(t * x 1 0) : ℂ) * ↑z + ↑(t * x 1 1)) = (t : ℂ) * ((x 1 0 : ℂ) * z + x 1 1) := by
      push_cast
      ring
    have hn : ((↑(t * x 0 0) : ℂ) * ↑z + ↑(t * x 0 1)) = (t : ℂ) * ((x 0 0 : ℂ) * z + x 0 1) := by
      push_cast
      ring
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [h2, h3, hj, hn, mul_div_mul_left _ _ ht']
    congr 1
    push_cast
    rw [mul_zpow, zpow_neg, zpow_neg, zpow_natCast]
    field_simp
  · intro c x
    funext z
    simp only [nsl, Pi.smul_apply, smul_eq_mul]
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AbsExpo
open NumberField Formalism.L2.Host UpperTheory.V UpperTheory.V.Af GlobalTheory.HeckeGal.Model GlobalTheory.Mem.Chr.CharModel
open GlobalTheory.CuspRep (Af)

theorem UpperTheory.V.Af.Nf.absExpo :
    UpperTheory.V.Af.Nf.AbsExpo := by
  intro F _ _ _ s v
  classical
  refine TR.expo_eq_of_exp _ v s fun t => ?_
  change Complex.exp (s * logNorm F (TR.infId F (TR.expU (Pi.single v t)))) = _
  have h1 : finPart F (TR.infId F (TR.expU (Pi.single v t))) = 1 := Units.ext (by
    change (1 : Af F) - 0 + 0 = 1
    simp)
  have h2 : ∀ u, ‖(infPart F (TR.infId F (TR.expU (Pi.single v t)))).val u‖ = Real.exp ((Pi.single v t : TR.Rinf F) u) := fun u => by
    have e : (infPart F (TR.infId F (TR.expU (Pi.single v t)))).val = TR.infEq F (TR.expU (Pi.single v t)).val := by
      change 1 - TR.infEq F 1 + TR.infEq F _ = _
      simp
    rw [e]
    exact (((InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal u)).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).symm)) _).trans
      (Real.norm_of_nonneg (Real.exp_pos _).le)
  rw [logNorm, h1, logFin_one, logInf]
  simp [h2, Pi.single_apply, InfinitePlace.mult, IsTotallyReal.isReal]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.MemMirabIff
open UpperTheory.V.Sd in
private theorem mem_mirab_iff {R : Type} [CommRing R] (g : GL (Fin 2) R) : g ∈ mirab R ↔ g 1 0 = 0 ∧ g 1 1 = 1 := by
  change Matrix.vecMul ![0, 1] (g : Matrix (Fin 2) (Fin 2) R) = ![0, 1] ↔ _
  simp [funext_iff, Fin.forall_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

open NumberField GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.V.Sd in
theorem UpperTheory.V.Af.Nf.memK :
    UpperTheory.V.Af.Nf.MemK := by
  intro M g
  constructor
  · rintro ⟨k, hk, rfl⟩
    have e0 : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat ℚ))}) (k 1 0) = 0 := ((mem_mirab_iff _).1 hk).1
    have e1 : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat ℚ))}) (k 1 1) = Ideal.Quotient.mk _ 1 := ((mem_mirab_iff _).1 hk).2
    refine ⟨fun a b => (k a b).2, fun a b => ?_, ?_, ?_⟩
    · rw [← map_inv]; exact ((k⁻¹ : GL (Fin 2) ↥(Ohat ℚ)) a b).2
    · obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 e0)
      exact ⟨y, y.2, congrArg Subtype.val hy⟩
    · obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 e1)
      exact ⟨y, y.2, congrArg Subtype.val hy⟩
  · rintro ⟨ha, hb, ⟨y, hy, e⟩, ⟨z, hz, e'⟩⟩
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin 2) (Ohat ℚ).subtype) := fun x y h =>
      Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
    let k : GL (Fin 2) ↥(Ohat ℚ) :=
      ⟨Matrix.of fun a b => ⟨g a b, ha a b⟩, Matrix.of fun a b => ⟨(g⁻¹ : GL (Fin 2) (Af ℚ)) a b, hb a b⟩,
        inj (by rw [map_mul, map_one]; exact g.mul_inv), inj (by rw [map_mul, map_one]; exact g.inv_mul)⟩
    have e0 : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat ℚ))}) (k 1 0) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ⟨⟨y, hy⟩, Subtype.ext e⟩)
    have e1 : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat ℚ))}) (k 1 1) = Ideal.Quotient.mk _ 1 :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨⟨z, hz⟩, Subtype.ext e'⟩)
    exact ⟨k, (mem_mirab_iff _).2 ⟨e0, e1⟩, Units.ext rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ArchBd
open UpperHalfPlane hiding I
open CongruenceSubgroup

theorem UpperTheory.V.Af.Nf.archBd :
    UpperTheory.V.Af.Nf.ArchBd := by
  intro k M hM f
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  refine ⟨C, fun x hx => ?_⟩
  unfold UpperTheory.V.Af.Nf.nsl
  set J : ℂ := (x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ) with hJdef
  set w : ℂ := (((SignType.sign x.det : ℝ)) : ℂ) *
    (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) / J) with hwdef
  have hJ0 : J ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [J] at h1 h2
    apply hx
    rw [Matrix.det_fin_two, h1, h2]
    ring
  have hn : Complex.normSq J = ‖J‖ ^ 2 := Complex.normSq_eq_norm_sq J
  have hJpos : 0 < ‖J‖ := norm_pos_iff.mpr hJ0
  have hDpos : 0 < |x.det| := abs_pos.mpr hx
  have hq : (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) / J).im =
      x.det / Complex.normSq J := by
    rw [Complex.div_im, Matrix.det_fin_two]
    simp [J]
    ring
  have himw : w.im = |x.det| / ‖J‖ ^ 2 := by
    rw [hwdef, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hq, hn]
    rcases lt_or_gt_of_ne hx with h | h
    · rw [sign_neg h, abs_of_neg h]
      simp
      ring
    · rw [sign_pos h, abs_of_pos h]
      simp
  have hw : 0 < w.im := by
    rw [himw]
    positivity
  have hτ : (ofComplex w).im = |x.det| / ‖J‖ ^ 2 := by
    rw [← himw, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    all_goals rfl
  have hb := hC (ofComplex w)
  rw [hτ] at hb
  have hpow : (|x.det| / ‖J‖ ^ 2) ^ (((k : ℤ) : ℝ) / 2) = |x.det| ^ ((k : ℝ) / 2) / ‖J‖ ^ k := by
    rw [Real.div_rpow hDpos.le (by positivity), ← Real.rpow_natCast ‖J‖ 2,
      ← Real.rpow_mul hJpos.le]
    push_cast
    congr 1
    rw [show (2 : ℝ) * ((k : ℝ) / 2) = ((k : ℕ) : ℝ) by ring, Real.rpow_natCast]
  rw [hpow] at hb
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_zpow]
  calc _ ≤ |x.det| ^ ((k : ℝ) / 2) * ‖J‖ ^ (-(k : ℤ)) *
        (C / (|x.det| ^ ((k : ℝ) / 2) / ‖J‖ ^ k)) := by gcongr
    _ = C := by
      have h1 : 0 < |x.det| ^ ((k : ℝ) / 2) := by positivity
      have h2 : 0 < ‖J‖ ^ k := by positivity
      rw [zpow_neg, zpow_natCast]
      field_simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMdiffPos
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Af.Nf

private theorem nsl_pos (k : ℕ) (f : ℍ → ℂ) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (z : ℍ) :
    nsl k f g z = ((g.val.det ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (denom g z ^ (-(k : ℤ)) * f (g • z)) := by
  have h : (((g.val 0 0 : ℝ) : ℂ) * z + g.val 0 1) / (((g.val 1 0 : ℝ) : ℂ) * z + g.val 1 1) = ((g • z : ℍ) : ℂ) := by
    rw [coe_smul_of_det_pos (by simpa using hg)]
    rfl
  unfold nsl
  rw [h, sign_pos hg, abs_of_pos hg]
  simp only [SignType.coe_one, Complex.ofReal_one, one_mul, ofComplex_apply, mul_assoc]
  rfl

private theorem nsl_slash (k : ℕ) (f : ℍ → ℂ) (x : GL (Fin 2) ℝ) (hx : 0 < x.val.det) :
    nsl k f x = (((x.val.det ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ)) • f ∣[(k : ℤ)] x := by
  funext z
  have hσ : σ x (f (x • z)) = f (x • z) := by simp [σ, hx]
  have hr : x.val.det ^ ((k : ℝ) / 2) = x.val.det ^ (1 - (k : ℝ) / 2) * x.val.det ^ ((k : ℤ) - 1) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add hx]
    congr 1
    push_cast
    ring
  rw [nsl_pos k f x hx, Pi.smul_apply, ModularForm.slash_apply, hσ, Matrix.GeneralLinearGroup.val_det_apply,
    abs_of_pos hx, hr, smul_eq_mul]
  push_cast
  ring

private theorem nsl_eps (k : ℕ) (f : ℍ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) : nsl k f (eps * x) = nsl k f x := by
  funext z
  have hd : (eps * x).det = -x.det := by rw [Matrix.det_mul]; simp [eps]
  have h0 : ∀ j, (eps * x) 0 j = -x 0 j := fun j => by simp [eps, Matrix.mul_apply]
  have h1 : ∀ j, (eps * x) 1 j = x 1 j := fun j => by simp [eps, Matrix.mul_apply]
  unfold nsl
  rw [hd, h0, h0, h1, h1, abs_neg, Left.sign_neg]
  congr 3
  push_cast
  ring

private theorem nsl_mdiff_pos (k : ℕ) (f : ℍ → ℂ) (hf : MDiff f) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : 0 < x.det) :
    MDiff (nsl k f x) := by
  let g : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero x hx.ne'
  have hg : 0 < g.val.det := hx
  have : nsl k f x = fun z : ℍ => ((g.val.det ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (denom g z ^ (-(k : ℤ)) * f (g • z)) :=
    funext (nsl_pos k f g hg)
  rw [this]
  exact mdifferentiable_const.mul ((mdifferentiable_denom_zpow g _).mul
    (hf.comp (mdifferentiable_smul (by simpa using hg))))

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.nslSl :
    UpperTheory.V.Af.Nf.NslSl := by
  intro k f
  refine ⟨fun δ => ?_, nsl_slash k f, fun hf x hx => ?_⟩
  · have hv : (δ : GL (Fin 2) ℝ).val = δ.1.map (Int.cast : ℤ → ℝ) := rfl
    have hd : (δ : GL (Fin 2) ℝ).val.det = 1 :=
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) δ).det_coe
    rw [← hv, nsl_slash k f _ (by rw [hd]; exact one_pos), hd, ModularForm.SL_slash]
    simp
  · rcases hx.lt_or_gt with h | h
    · rw [← nsl_eps]
      refine nsl_mdiff_pos k f hf _ ?_
      have hd : (eps * x).det = -x.det := by rw [Matrix.det_mul]; simp [eps]
      rw [hd]; linarith
    · exact nsl_mdiff_pos k f hf x h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatOfVec
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Matrix GlobalTheory.PRep GlobalTheory.CuspRep.LocEx
open GlobalTheory.CuspRep (SmIrr Af locGL pLoc finGL)

namespace UpperTheory.V.Af.Nf.LocalComponentIsotypic

section Gen

variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]

private def orb (κ : Representation ℂ K V) (x : V) : (K →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ fun k => κ k x

private theorem orb_comm (κ : Representation ℂ K V) (T : Module.End ℂ V) (hT : ∀ k x, T (κ k x) = κ k (T x)) (x : V)
    (c : K →₀ ℂ) : orb κ (T x) c = T (orb κ x c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hT]

private theorem orb_act (κ : Representation ℂ K V) (x : V) (k : K) (c : K →₀ ℂ) :
    orb κ x (c.mapDomain (k * ·)) = κ k (orb κ x c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' h h' => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), map_add (f := _), h, h']
  | single a b => simp [orb]

private def annPart (κ : Representation ℂ K V) (φ : V) : Submodule ℂ V where
  carrier := {x | ∀ c, orb κ φ c = 0 → orb κ x c = 0}
  add_mem' := fun {x y} hx hy c hc => by
    have : orb κ (x + y) c = orb κ x c + orb κ y c := by
      simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_add (f := _), smul_add, Finset.sum_add_distrib]
    rw [this, hx c hc, hy c hc, add_zero]
  zero_mem' := fun c _ => by simp [orb, Finsupp.linearCombination_apply, Finsupp.sum]
  smul_mem' := fun a x hx c hc => by
    have := orb_comm κ (a • (1 : Module.End ℂ V)) (fun k x => by simp) x c
    simpa [hx c hc] using this

private theorem exists_type (κ : Representation ℂ K V) (φ : V)
    (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => κ k φ))) :
    ∃ (d : ℕ) (ξ : K →* Matrix (Fin d) (Fin d) ℂ), ∀ x ∈ annPart κ φ, ∃ f : (Fin d → ℂ) →ₗ[ℂ] V,
      (∀ k v, f (ξ k *ᵥ v) = κ k (f v)) ∧ x ∈ LinearMap.range f ∧ ∀ v, ∃ c, f v = orb κ x c := by
  have hO : ∀ k, ∀ y ∈ LinearMap.range (orb κ φ), κ k y ∈ LinearMap.range (orb κ φ) := by
    rintro k _ ⟨c, rfl⟩
    exact ⟨_, orb_act κ φ k c⟩
  haveI : FiniteDimensional ℂ (LinearMap.range (orb κ φ)) := by
    rw [orb, Finsupp.range_linearCombination]; exact hφ
  let b := Module.finBasis ℂ (LinearMap.range (orb κ φ))
  obtain ⟨s, hs⟩ := (orb κ φ).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
  refine ⟨_, (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO), fun x hx => ?_⟩
  have key : ∀ c, orb κ x (s ((orb κ φ).rangeRestrict c)) = orb κ x c := fun c => by
    rw [← sub_eq_zero, ← map_sub]
    refine hx _ ?_
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val (LinearMap.congr_fun hs ((orb κ φ).rangeRestrict c))
  refine ⟨orb κ x ∘ₗ s ∘ₗ b.equivFun.symm.toLinearMap, fun k v => ?_,
    ⟨b.equivFun ((orb κ φ).rangeRestrict (Finsupp.single 1 1)), ?_⟩, fun v => ⟨_, rfl⟩⟩
  · obtain ⟨y, rfl⟩ := b.equivFun.surjective v
    obtain ⟨c, rfl⟩ := (orb κ φ).surjective_rangeRestrict y
    have h1 : (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO) k *ᵥ b.equivFun ((orb κ φ).rangeRestrict c) =
        b.equivFun ((orb κ φ).rangeRestrict (c.mapDomain (k * ·))) := by
      have h2 : (orb κ φ).rangeRestrict (c.mapDomain (k * ·)) = sub κ _ hO k ((orb κ φ).rangeRestrict c) :=
        Subtype.ext (orb_act κ φ k c)
      rw [h2]
      exact LinearMap.toMatrix_mulVec_repr b b _ _
    rw [h1]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key, orb_act]
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key]
    simp [orb]

end Gen

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

private theorem smooth_fin (π : TR.CuspSub F n) : IsSmooth π.finPart := fun v => by
  convert (π.cusp v.1 v.2).1.level using 1
  ext k
  exact Subtype.ext_iff

private theorem smooth_loc (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) : IsSmooth (π.locRep w) := fun v =>
  (smooth_fin π v).preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)

private theorem cpt_fin (π : TR.CuspSub F n) (k : TR.Kinf F n) (g : GL (Fin n) (Af F)) (y : π.V) :
    π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
  refine Subtype.ext ?_
  change (TR.rt F n (TR.infGL F n (Unitary.toUnits k)) * TR.rt F n (finGL F n g)) y.1 =
    (TR.rt F n (finGL F n g) * TR.rt F n (TR.infGL F n (Unitary.toUnits k))) y.1
  rw [← map_mul, ← map_mul, TR.infGL_comm]

private theorem fin_loc (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) {k : GL (Fin n) (Af F)}
    (hk : GeneralLinearGroup.map (pLoc F w) k = 1) (g : GL (Fin n) (w.adicCompletion F)) (y : π.V) :
    π.finPart k (π.locRep w g y) = π.locRep w g (π.finPart k y) := by
  simp only [TR.CuspSub.locRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL w hk]

private theorem bot_or_top (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) (W : Submodule ℂ π.V)
    (h1 : ∀ g, ∀ x ∈ W, π.locRep w g x ∈ W)
    (h2 : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.locRep w g x) = π.locRep w g (T x)) → ∀ x ∈ W, T x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ o, ∀ x ∈ W, π.op o x ∈ W := fun o x hx => by
    cases o with
    | fin k =>
      have h3 := h1 (GeneralLinearGroup.map (pLoc F w) k) _ (h2
        (π.finPart ((locGL F n w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ * k))
        (fin_loc π w (map_pLoc_inv_mul w k)) x hx)
      rwa [TR.CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h3
    | cpt k => exact h2 _ (fun g y => cpt_fin π k _ y) x hx
    | lie X => exact h2 _ (fun g y => Subtype.ext (LinearMap.congr_fun (TR.lie_rt_fin X (locGL F n w g)) y.1)) x hx
  rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h | h
  · exact Or.inl (hi (h.trans (Submodule.map_bot _).symm))
  · exact Or.inr (hi (h.trans (Submodule.map_subtype_top _).symm))

private theorem isotypic (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin n) (w.adicCompletion F)))
    (h : π.IsLocComp w σ) : LocIsotypic π.finPart w σ := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩
  refine (bot_or_top π w _ (fun g x hx => ?_) (fun T hT x hx => ?_)).resolve_left fun e => ?_
  · refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap (π.locRep w g) _) fun f => ?_) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem f ⟨σ.ρ g v, f.2 g v⟩
  · refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap T _) fun f => ?_) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by
      rw [LinearMap.comp_apply, f.2]; exact hT g _⟩ ⟨v, rfl⟩
  · obtain ⟨f, h0, hf⟩ := h
    exact h0 (LinearMap.range_eq_bot.1 ((iSup_eq_bot.1 e) ⟨f, hf⟩))

private def cptPart (π : TR.CuspSub F n) : Representation ℂ (TR.Kinf F n) π.V :=
  sub (TR.cptRep F n) π.V fun k => π.stable (.cpt k)

private theorem exists_comp (h : UpperTheory.V.Published.AdmissibleReal) (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) :
    ∃ σ, π.IsLocComp w σ := by
  obtain ⟨φ₀, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set φ : π.V := ⟨φ₀, hφ⟩
  have h0' : φ ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  set L := stab π.finPart φ
  have hL : IsOpen (L : Set (GL (Fin n) (Af F))) := smooth_fin π _
  obtain ⟨K, ho, hc, hK⟩ := exists_compact_open w _ hL
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptPart π k φ)) := by
    have := (π.cusp φ₀ hφ).1.kfin
    refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ Submodule.subtype _).codRestrict
      (Submodule.span ℂ (Set.range fun k => TR.cptRep F n k φ₀)) fun v => ?_)
      fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
    refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap π.V.subtype _)).2 ?_ v.2)
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨d, ξ, hξ⟩ := exists_type (cptPart π) φ hfd
  have hcomm : ∀ g k x, π.finPart g (cptPart π k x) = cptPart π k (π.finPart g x) := fun g k x => (cpt_fin π k g x).symm
  let U : Submodule ℂ π.V := annPart (cptPart π) φ ⊓
    fixed π.finPart (L ⊓ (GeneralLinearGroup.map (n := Fin n) (pLoc F w)).ker)
  obtain ⟨σ, hσ, -⟩ := exists_irred (smooth_loc π w) ho (fun W hW e => by
      rcases bot_or_top π w (nullPart (π.locRep w) K) (fun g x hx => nullPart_act _ K g hx)
        (fun T hT x hx => nullPart_comm _ K T hT hx) with h2 | h2
      · exact le_bot_iff.1 (h2 ▸ le_nullPart (smooth_loc π w) hc W hW e)
      · exact absurd (eq_zero_of_mem_nullPart (smooth_loc π w) hc (mem_fix.2 hK) (h2 ▸ Submodule.mem_top)) h0')
    U (fun g x hx => ⟨fun c hc => by
        rw [TR.CuspSub.locRep, MonoidHom.comp_apply, orb_comm _ _ (hcomm _), hx.1 c hc, map_zero],
      mem_fix.2 fun k hk => by rw [fin_loc π w hk.2, mem_fix.1 hx.2 k hk]⟩)
    ((Submodule.ne_bot_iff _).2 ⟨φ, ⟨fun _ hc => hc, mem_fix.2 fun k hk => hk.1⟩, h0'⟩) (fun K' hK' => by
      obtain ⟨W, hW, hWf⟩ := h F n π (L ⊓ (K' ⊓ L.comap (locGL F n w)).comap (GeneralLinearGroup.map (pLoc F w)))
        (hL.inter ((hK'.inter (hL.preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w))).preimage
          (continuous_map_pLoc w))) d ξ
      refine Submodule.finiteDimensional_of_le (S₂ := W) fun x hx => ?_
      obtain ⟨f, hf, hx1, hf2⟩ := hξ x hx.1.1
      refine hWf f hf (fun k hk v => ?_) hx1
      have h1 := mem_fix.1 hx.1.2 _ ⟨L.mul_mem (L.inv_mem hk.2.2) hk.1, map_pLoc_inv_mul w k⟩
      have h2 := mem_fix.1 hx.2 _ hk.2.1
      have h3 : π.finPart k x = x := by
        rw [← mul_inv_cancel_left (locGL F n w (GeneralLinearGroup.map (pLoc F w) k)) k, map_mul,
          Module.End.mul_apply, h1]
        exact h2
      obtain ⟨c, hc⟩ := hf2 v
      rw [hc, ← orb_comm _ _ (hcomm k), h3])
  exact ⟨σ, hσ⟩

end UpperTheory.V.Af.Nf.LocalComponentIsotypic

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun GlobalTheory.PRep in
private theorem UpperTheory.V.Af.Nf.satLoc' : UpperTheory.V.Af.SatLoc := by
  intro F _ _ n w σ
  have hex : GlobalTheory.LGrp.IsSpherical σ.ρ (KGL w n) → ∃ B, HasSatGL w σ.ρ B :=
    GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred
  refine ⟨fun ⟨v, h0, hv⟩ => hex ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, h0⟩), ?_⟩
  intro V _ _ ρ ⟨hV, htop⟩ B
  have up : ∀ B, HasSatGL w σ.ρ B → HasSatGL w (ρ.comp (locGL F n w)) B := by
    intro B h
    constructor
    · obtain ⟨f, h0⟩ : ∃ f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F n w g) (f v)}, f.1 ≠ 0 := by
        by_contra hc
        push Not at hc
        refine top_ne_bot (htop.symm.trans (eq_bot_iff.2 (iSup_le fun f => ?_)))
        rw [hc f, LinearMap.range_zero]
      obtain ⟨x, hx⟩ := h.exists_vec
      have hi : LinearMap.ker f.1 = ⊥ := ((isIrreducible_iff σ.ρ).1 σ.irred).2 _ (fun g v hv => by
        rw [LinearMap.mem_ker] at hv ⊢
        rw [f.2, hv, map_zero]) |>.resolve_right fun e => h0 (LinearMap.ker_eq_top.1 e)
      have h1 := hx.map (ρ' := ρ.comp (locGL F n w)) f.1 f.2
        ((map_ne_zero_iff f.1 (LinearMap.ker_eq_bot.1 hi)).2 hx.1)
      exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
    · intro x hx h0
      exact GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup (ρ := ρ.comp (locGL F n w)) σ.irred h
        (fun f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F n w g) (f v)} => f.1) (fun f => f.2)
        (htop ▸ Submodule.mem_top) hx h0
  refine ⟨fun h => ?_, up B⟩
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 h.1
  obtain ⟨y, hy0, hy⟩ := LocSph.exists_fixed_of_mem_iSup (ρ.comp (locGL F n w)) σ.ρ σ.irred
    (fun f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F n w g) (f v)} => f.1) (fun f => f.2)
    (KGL w n : Set _) x hx0 (fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx k hk) (htop ▸ Submodule.mem_top)
  obtain ⟨B', hB'⟩ := hex ((Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩)
  exact (up B' hB').unique h ▸ hB'

open UpperTheory.V.Af GlobalTheory.LFun in
theorem UpperTheory.V.Af.Nf.satOfVec :
    UpperTheory.V.Published.AdmissibleReal → UpperTheory.V.Af.Nf.SatOfVec := by
  intro hA F _ _ _ a π w ψ B h
  obtain ⟨σ, hσ⟩ := Nf.LocalComponentIsotypic.exists_comp hA π w
  have hi := Nf.LocalComponentIsotypic.isotypic π w σ hσ
  obtain ⟨B', hB'⟩ := (satLoc' F a w σ).1 (hi.hasFixed (SatCompare.isOpen_isCompact_KGL w a).2
    ⟨ψ, h.1, fun k hk => GlobalTheory.LGrp.mem_fixed.1 h.2.1 k hk⟩)
  have h2 : π.HasSat w B' := ((satLoc' F a w σ).2 _ _ hi B').2 hB'
  rwa [h.unique (h2.2 ψ h.2.1 h.1)]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatComp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.CuspRep in
theorem UpperTheory.V.Af.Nf.satComp :
    UpperTheory.V.Af.Nf.SatComp := by
  intro F _ _ _ φ π ψ W h0 hW hd hφ w B h
  have hle : ∀ g, W ≤ W.comap (locSm F w g) := fun g x hx => hW (.fin (locGL F 2 w g)) x hx
  have hi : Function.Injective (W.mkQ ∘ₗ π.V.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, Submodule.ker_mkQ]
    exact Submodule.disjoint_iff_comap_eq_bot.1 hd
  have he : W.mkQ φ = (W.mkQ ∘ₗ π.V.subtype) ψ := (Submodule.Quotient.eq W).2 hφ
  have h1 := h.map (ρ' := (locSm F w).quotient W hle) W.mkQ (fun _ _ => rfl)
    (by rw [he]; exact fun e => h0 (hi (e.trans (map_zero _).symm)))
  rw [he] at h1
  exact GlobalTheory.LFun.IsSatVecGL.of_map _ (fun _ _ => rfl) hi h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Imports
open UpperTheory.V in
theorem UpperTheory.V.Af.Nf.split :
    UpperTheory.V.Af.Nf.Split := by
  intro F _ _ _ a φ hφ hmem
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hmem
  have hst : ∀ t : Finset (TR.CuspSub F a), TR.IsStable (⨆ π ∈ t, π.V) := by
    intro t o x hx
    have : (⨆ π ∈ t, π.V) ≤ (⨆ π ∈ t, π.V).comap (TR.act o) :=
      iSup₂_le fun π hπ y hy =>
        (le_iSup₂ (f := fun (π : TR.CuspSub F a) (_ : π ∈ t) => π.V) π hπ) (π.stable o y hy)
    exact this hx
  induction s using Finset.induction_on with
  | empty => exact absurd (by simpa using hs) hφ
  | insert π t _ ih =>
    by_cases ht : φ ∈ ⨆ π ∈ t, π.V
    · exact ih ht
    rw [Finset.iSup_insert] at hs
    obtain ⟨ψ, hψ, w, hw, e⟩ := Submodule.mem_sup.1 hs
    rcases π.irred (π.V ⊓ ⨆ π ∈ t, π.V) inf_le_left
      (fun o x hx => ⟨π.stable o x hx.1, hst t o x hx.2⟩) with h | h
    · refine ⟨π, ⟨ψ, hψ⟩, _, ?_, hst t, disjoint_iff.2 h, ?_⟩
      · intro h0
        have h1 : ψ = 0 := congrArg Subtype.val h0
        rw [h1, zero_add] at e
        exact ht (e ▸ hw)
      · rw [← e]
        simpa using hw
    · exact absurd (e ▸ Submodule.add_mem _ (inf_eq_left.1 h hψ) hw) ht
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatHol
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatOfU
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Sd Matrix GlobalTheory.LFun Formalism.UG

private theorem hecke_eq_dc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (a : G) (h : G → ℂ) (h1 : ∀ g : G, (g : G ⧸ K) ∈ MulAction.orbit K (a : G ⧸ K) → h g = 1)
    (h2 : ∀ g : G, (g : G ⧸ K) ∉ MulAction.orbit K (a : G ⧸ K) → h g = 0) (hf : {c : G ⧸ K | h c.out ≠ 0}.Finite) (x : V) :
    heckeVec ρ K h x = Hi.dc ρ K K a x := by
  classical
  have hfin : (MulAction.orbit K (a : G ⧸ K)).Finite := hf.subset fun c hc => by
    rw [Set.mem_setOf_eq, h1 _ (by rwa [QuotientGroup.out_eq'])]; exact one_ne_zero
  letI := hfin.fintype
  rw [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, ← finsum_eq_sum_of_fintype,
    finsum_set_coe_eq_finsum_mem (f := fun c : G ⧸ K => ρ c.out x), heckeVec]
  refine finsum_congr fun c => ?_
  by_cases hc : c ∈ MulAction.orbit K (a : G ⧸ K)
  · rw [h1 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]
  · rw [h2 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]

variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

private theorem iwahori_level_zero_eq : K1 w 0 = KGL w (n := 2) := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _

private theorem hecke_Tj {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V)
    (j : ℕ) (a : GL (Fin 2) (w.adicCompletion F)) (ha : a.val = diagJ 2 (atFin w (unif w) : w.adicCompletion F) j) (x : V) :
    heckeVec ρ (KGL w (n := 2)) (Tj ℂ 2 (Ov F w) (atFin w (unif w) : w.adicCompletion F) j) x = Hi.dc ρ (KGL w (n := 2)) (KGL w (n := 2)) a x := by
  refine hecke_eq_dc ρ _ a _ (fun g hg => ?_) (fun g hg => ?_)
    (Formalism.UG.P.finite_support_cosets (Final.GLintComm F w 2) (Tj_mem_hecke (unif_spec w) j).2) x
  · obtain ⟨k, hk⟩ := hg
    have h : ((k : GL (Fin 2) (w.adicCompletion F)) * a)⁻¹ * g ∈ KGL w (n := 2) := QuotientGroup.eq.1 hk
    rw [Tj, Set.indicator_of_mem, Pi.one_apply]
    refine ⟨k, k.2, _, h, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel_left]
  · rw [Tj, Set.indicator_of_notMem]
    rintro ⟨k, hk, k', hk', e⟩
    refine hg ⟨⟨k, hk⟩, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul] at e
    rw [Units.ext e]
    exact (QuotientGroup.mk_mul_of_mem (k * a) hk').symm

theorem UpperTheory.V.Af.Nf.satOfU :
    UpperTheory.V.Af.Nf.SatOfU := by
  intro F _ _ w V _ _ ρ x α β h0 hx hU hz
  rw [iwahori_level_zero_eq] at hx
  have hx' : x ∈ GlobalTheory.PRep.fixed ρ (KGL w (n := 2)) := GlobalTheory.LGrp.mem_fixed.2 hx
  refine ⟨h0, hx', rfl, fun ϖ hϖ j hj => ?_⟩
  rw [ExSatGL.Tj_indep j (ϖ := (atFin w (unif w) : w.adicCompletion F)) (unif_spec w) hϖ]
  interval_cases j
  · rw [ExSatGL.heckeVec_Tj_zero ρ _ hx']
    simp [satEig, Multiset.esymm]
  · rw [Uop, iwahori_level_zero_eq, ← hecke_Tj w ρ 1 _ (by ext i j; fin_cases i <;> fin_cases j <;> simp [aff, diagJ])] at hU
    rw [hU]
    congr 1
    rw [Complex.ofReal_cpow (by positivity)]
    have : qV F w = normV w := by
      simp [normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    simp [satEig, Multiset.esymm, Multiset.powersetCard_one, this]
    norm_num [add_comm]
  · set z := GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))
    rw [hecke_Tj w ρ 2 z (by ext i j; fin_cases i <;> fin_cases j <;> simp [z, diagJ])]
    have ho : ∀ q ∈ MulAction.orbit (KGL w (n := 2)) (z : _ ⧸ KGL w (n := 2)), q = z := by
      rintro _ ⟨k, rfl⟩
      change (((k : GL (Fin 2) (w.adicCompletion F)) * z : GL (Fin 2) (w.adicCompletion F)) : _ ⧸ KGL w (n := 2)) = _
      rw [← GlobalTheory.CuspRep.scalar_comm]
      exact QuotientGroup.mk_mul_of_mem _ k.2
    rw [(Hi.dcSum ℂ _ V ρ _ _ z ((Set.finite_singleton _).subset ho)).1 {z}
      (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact MulAction.mem_orbit_self _)
      (fun q hq => ⟨z, ⟨Finset.mem_singleton_self _, (ho q hq).symm⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩) x
      hx, Finset.sum_singleton, hz]
    simp [satEig, Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one]
end
end

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd Matrix
open GlobalTheory.CuspRep (finId locGL finGL)

private theorem fin_scalar {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) x)) = GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) := by
  have h := GlobalTheory.CuspRep.finId_det_locGL w (GeneralLinearGroup.scalar (Fin 1) x)
  rw [locGL, GlobalTheory.CuspRep.cornerGL_scalar] at h ⊢
  rw [finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  congr 1
  exact (congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans
    (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))

private theorem roots (s : ℂ) (p : ℂˣ) : ∃ α β : ℂˣ, (α : ℂ) + β = s ∧ α * β = p := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (s ^ 2 - 4 * (p : ℂ)) (n := 2) two_pos
  have h : (s + d) / 2 * ((s - d) / 2) = p := by linear_combination (-1 / 4 : ℂ) * hd
  have h0 := h ▸ p.ne_zero
  refine ⟨Units.mk0 _ (left_ne_zero_of_mul h0), Units.mk0 _ (right_ne_zero_of_mul h0), ?_, Units.ext h⟩
  simp only [Units.val_mk0]
  ring

theorem UpperTheory.V.Af.Nf.satHol :
    UpperTheory.V.Af.Nf.SatHol := by
  intro F _ _ _ k c ω φ hφ h0 w lam hw hU
  have hq : (0 : ℝ) < normV w :=
    Nat.cast_pos.2 (zero_lt_one.trans (by
      simpa [normV, Ideal.absNorm_eq_natCard] using NumberField.HeightOneSpectrum.one_lt_absNorm w))
  have hne : ∀ t : ℝ, (((normV w : ℝ) ^ t : ℝ) : ℂ) ≠ 0 := fun t =>
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq t).ne'
  obtain ⟨α, β, h1, h2⟩ := roots (lam / (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ)) (ω.val w)
  have h3 : (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) = lam := by
    rw [h1, mul_div_cancel₀ _ (hne _)]
  refine ⟨α, β, UpperTheory.V.Af.Nf.satOfU F w _ _ φ α β h0 (hw ▸ hφ.level w) ?_ ?_, h3, h2⟩
  · refine smul_right_injective _ (hne ((k : ℝ) / 2 - 1)) (hU.trans ?_)
    dsimp only
    rw [smul_smul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hq, ← h3]
    congr 4
    ring
  · rw [h2]
    refine Subtype.ext (funext fun g => ?_)
    change φ.1 (g * finGL F 2 (locGL F 2 w _)) = _
    rw [fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent]
    rfl
end
