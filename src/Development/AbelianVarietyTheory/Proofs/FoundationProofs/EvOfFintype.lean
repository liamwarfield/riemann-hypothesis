module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormMulTransposeMulFormInvMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosure
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvOfFintype
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue.EvRing

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

variable (p Ω) in
def zpH : ℤ_[p] →+* Ω := (algebraMap (O0 p) Ω).comp ((algebraMap (Lau p) (O0 p)).comp HahnSeries.C)

theorem zp_eq (z : ℤ_[p]) : zp Ω z = zpH (p := p) (Ω := Ω) z := rfl

theorem thL_coeff (a : Lau p) (r : ℤ) : (thL a).coeff r = (r : ℤ_[p]) * a.coeff r := rfl

theorem thL_mul (a b : Lau p) : thL (a * b) = thL a * b + a * thL b := by
  apply HahnSeries.ext
  funext r
  have hs : (thL a).support ⊆ a.support := fun i hi h => hi (by simp [thL_coeff, h])
  have ht : (thL b).support ⊆ b.support := fun i hi h => hi (by simp [thL_coeff, h])
  rw [HahnSeries.coeff_add, HahnSeries.coeff_mul_left' a.isPWO_support hs,
    HahnSeries.coeff_mul_right' b.isPWO_support ht, thL_coeff,
    HahnSeries.coeff_mul (x := a) (y := b), Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  rw [thL_coeff, thL_coeff, ← hij.2.2]
  push_cast
  ring

theorem thL_neg (a : Lau p) : thL (-a) = -thL a := by
  ext r
  simp [thL_coeff]

theorem ev_of_fintype {ι : Type} [Fintype ι] (ψ : O0 p →+* Ω) (c : ℤ → Ω) (x x' : Ω) (e : ι → Ω)
    (a : ι → Lau p) (he : ∀ t, IsInt (p := p) (e t) ∧ IsAlgZp (p := p) (e t))
    (hc : ∀ r, c r = ∑ t, e t * zp Ω ((a t).coeff r))
    (hx : x = ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)))
    (hx' : x' = ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (thL (a t)))) : GlobalTheory.Glue.Ev ψ c x x' := by
  let σ := Fintype.equivFin ι
  refine ⟨Fintype.card ι, e ∘ σ.symm, a ∘ σ.symm, fun t => he _, fun r => ?_, ?_, ?_⟩
  · rw [hc r]; exact (Equiv.sum_comp σ.symm (fun t => e t * zp Ω ((a t).coeff r))).symm
  · rw [hx]; exact (Equiv.sum_comp σ.symm (fun t => e t * ψ (algebraMap (Lau p) (O0 p) (a t)))).symm
  · rw [hx']; exact (Equiv.sum_comp σ.symm (fun t => e t * ψ (algebraMap (Lau p) (O0 p) (thL (a t))))).symm

theorem repr {d : ℕ} (e : Fin d → Ω) (a : Fin d → Lau p) (C : HahnSeries ℤ Ω)
    (h : ∀ r, C.coeff r = ∑ t, e t * zp Ω ((a t).coeff r)) :
    C = ∑ t, HahnSeries.C (e t) * (a t).map (zpH (p := p) (Ω := Ω)).toNonUnitalRingHom := by
  ext r
  rw [h r, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.map_coeff]
  rfl

theorem isAlgZp_mul {x y : Ω} (hx : IsAlgZp (p := p) x) (hy : IsAlgZp (p := p) y) :
    IsAlgZp (p := p) (x * y) := by
  let : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra
  have : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have key : ∀ z : Ω, IsAlgZp (p := p) z ↔ IsAlgebraic ℤ_[p] z := by
    intro z; simp only [IsAlgZp, IsAlgebraic, Polynomial.aeval_map_algebraMap]
  rw [key] at hx hy ⊢
  exact hx.mul hy

theorem isAlgZp_gal (g : Gal p Ω) {x : Ω} (hx : IsAlgZp (p := p) x) : IsAlgZp (p := p) (g x) := by
  obtain ⟨P, hP, h⟩ := hx
  exact ⟨P, hP, by rw [Polynomial.aeval_algHom_apply, h, map_zero]⟩

end GlobalTheory.Glue.EvRing

namespace GlobalTheory.Glue.EvRing

open GlobalTheory.K5.Basic in
theorem ev_ring : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ →
    (∀ (C D : HahnSeries ℤ Ω) (x x' y y' : Ω),
      GlobalTheory.Glue.Ev ψ C.coeff x x' → GlobalTheory.Glue.Ev ψ D.coeff y y' →
      GlobalTheory.Glue.Ev ψ (C * D).coeff (x * y) (x' * y + x * y') ∧
      GlobalTheory.Glue.Ev ψ (C + D).coeff (x + y) (x' + y') ∧
      GlobalTheory.Glue.Ev ψ (C - D).coeff (x - y) (x' - y')) ∧
    (∀ (c : ℤ → Ω) (x x' : Ω), GlobalTheory.Glue.Ev ψ c x x' →
      IsInt (p := p) x ∧ IsInt (p := p) x' ∧ (∃ C : HahnSeries ℤ Ω, C.coeff = c) ∧
      (∃ x'', GlobalTheory.Glue.Ev ψ (fun r => (r : Ω) * c r) x' x'') ∧
      (∀ e : Ω, IsInt (p := p) e → IsAlgZp (p := p) e →
        GlobalTheory.Glue.Ev ψ (fun r => e * c r) (e * x) (e * x')) ∧
      ∀ g : Gal p Ω, g (T.qq n) = T.qq n → GlobalTheory.Glue.Ev ψ (fun r => g (c r)) (g x) (g x')) := by
  intro p hp Ω _ _ _ T n ψ hreb
  refine ⟨?_, ?_⟩
  · rintro C D x x' y y' ⟨d, e, a, he, hc, hx, hx'⟩ ⟨d', f, b, hf, hd, hy, hy'⟩
    refine ⟨?_, ?_, ?_⟩
    · refine ev_of_fintype (ι := Fin d × Fin d') ψ _ _ _ (fun ts => e ts.1 * f ts.2)
        (fun ts => a ts.1 * b ts.2) (fun ts => ⟨IsIntegral.mul (he _).1 (hf _).1, isAlgZp_mul (he _).2 (hf _).2⟩)
        (fun r => ?_) ?_ ?_
      · rw [repr e a C hc, repr f b D hd, Finset.sum_mul_sum, HahnSeries.coeff_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [HahnSeries.coeff_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [show HahnSeries.C (e t) * (a t).map (zpH (p := p) (Ω := Ω)).toNonUnitalRingHom *
            (HahnSeries.C (f s) * (b s).map (zpH (p := p) (Ω := Ω)).toNonUnitalRingHom) =
            HahnSeries.C (e t * f s) * (a t * b s).map (zpH (p := p) (Ω := Ω)).toNonUnitalRingHom by
          rw [HahnSeries.map_mul, map_mul]; ring]
        rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.map_coeff]
        rfl
      · rw [hx, hy, Finset.sum_mul_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
        simp only [map_mul]
        ring
      · rw [hx, hx', hy, hy', Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib,
          Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [thL_mul, map_add (f := _), map_mul]
        ring
    · refine ev_of_fintype (ι := Fin d ⊕ Fin d') ψ _ _ _ (Sum.elim e f) (Sum.elim a b)
        (by rintro (t | t) <;> simp [he, hf]) (fun r => ?_) ?_ ?_
      · simp [Fintype.sum_sum_type, hc, hd]
      · simp [Fintype.sum_sum_type, hx, hy]
      · simp [Fintype.sum_sum_type, hx', hy']
    · refine ev_of_fintype (ι := Fin d ⊕ Fin d') ψ _ _ _ (Sum.elim e f) (Sum.elim a fun s => -b s)
        (by rintro (t | t) <;> simp [he, hf]) (fun r => ?_) ?_ ?_
      · simp [Fintype.sum_sum_type, hc, hd, zp_eq, sub_eq_add_neg]
      · simp [Fintype.sum_sum_type, hx, hy, sub_eq_add_neg]
      · simp [Fintype.sum_sum_type, hx', hy', thL_neg, sub_eq_add_neg]
  · rintro c x x' ⟨d, e, a, he, hc, hx, hx'⟩
    have hpow : T.qq n ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) := by
      clear hreb
      induction n with
      | zero => simp [T.q0]
      | succ n ih => rw [pow_succ', pow_mul, T.qpow, ih]
    have hq : IsIntegral (O0 p) (T.qq n) :=
      IsIntegral.of_pow (pow_pos hp.out.pos n) (hpow ▸ isIntegral_algebraMap)
    have hmem : ∀ y, ψ y ∈ Algebra.adjoin (O0 p) {T.qq n} := fun y => by
      have : ψ y ∈ ψ.range := ⟨y, rfl⟩
      rw [hreb.rng] at this
      exact this
    have hint : ∀ y, IsInt (p := p) (ψ y) := fun y => adjoin_le_integralClosure hq (hmem y)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx]; exact IsIntegral.sum _ fun t _ => IsIntegral.mul (he t).1 (hint _)
    · rw [hx']; exact IsIntegral.sum _ fun t _ => IsIntegral.mul (he t).1 (hint _)
    · refine ⟨∑ t, HahnSeries.C (e t) * (a t).map (zpH (p := p) (Ω := Ω)).toNonUnitalRingHom, funext fun r => ?_⟩
      rw [hc r, HahnSeries.coeff_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.map_coeff]
      rfl
    · refine ⟨_, ev_of_fintype ψ _ x' _ e (fun t => thL (a t)) he (fun r => ?_) hx' rfl⟩
      rw [hc r, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [thL_coeff, zp_eq, zp_eq, map_mul, map_intCast]
      ring
    · intro e0 hi ha
      refine ev_of_fintype ψ _ _ _ (fun t => e0 * e t) a
        (fun t => ⟨IsIntegral.mul hi (he t).1, isAlgZp_mul ha (he t).2⟩) (fun r => ?_) ?_ ?_
      · rw [hc r, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
      · rw [hx, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
      · rw [hx', Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
    · intro g hg
      have hfix : ∀ y, g (ψ y) = ψ y := fun y =>
        (AlgHom.eqOn_adjoin_iff (φ := (g : Ω →ₐ[O0 p] Ω)) (ψ := AlgHom.id (O0 p) Ω) (s := {T.qq n})).2
          (by intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact hg) (hmem y)
      have hint_gal : ∀ t, IsInt (p := p) (g (e t)) := fun t =>
        IsIntegral.map g.toAlgHom (he t).1
      refine ev_of_fintype ψ _ _ _ (fun t => g (e t)) a
        (fun t => ⟨hint_gal t, isAlgZp_gal g (he t).2⟩) (fun r => ?_) ?_ ?_
      set_option synthInstance.maxHeartbeats 100000 in
        · rw [hc r, map_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [map_mul]
          congr 1
          exact g.commutes _
      set_option synthInstance.maxHeartbeats 100000 in
        · rw [hx, map_sum]
          exact Finset.sum_congr rfl fun t _ => by rw [map_mul, hfix]
      set_option synthInstance.maxHeartbeats 100000 in
        · rw [hx', map_sum]
          exact Finset.sum_congr rfl fun t _ => by rw [map_mul, hfix]

end GlobalTheory.Glue.EvRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionOfPeriodicBoundedHolomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionOfPeriodicBoundedHolomorphic
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Function

namespace GlobalTheory.FN

theorem periodic_comp_ofComplex_of_vadd_real {f : ℍ → ℂ} {h : ℝ}
    (hf : ∀ τ : ℍ, f (h +ᵥ τ) = f τ) :
    Periodic (f ∘ UpperHalfPlane.ofComplex) (h : ℂ) := by
  intro w
  by_cases! hw : 0 < Complex.im w
  · have : 0 < Complex.im (w + h) := by simp [hw]
    simp only [comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos this,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    convert! hf ⟨w, hw⟩ using 2
    ext
    simp [add_comm]
  · have : Complex.im (w + h) ≤ 0 := by simpa using hw
    simp [UpperHalfPlane.ofComplex_apply_of_im_nonpos this,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hw]

theorem hasQ_of_periodic_bounded : ∀ (N : ℕ) (f : ℍ → ℂ), 0 < N → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → (∀ τ : ℍ, f ((N : ℝ) +ᵥ τ) = f τ) → UpperHalfPlane.IsBoundedAtImInfty f → ∃ a, HasQ N f a := by
  intro N f hN hf hper hbdd
  refine ⟨fun n => PowerSeries.coeff n (UpperHalfPlane.qExpansion (N : ℝ) f), ?_⟩
  rw [GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion]
  exact GlobalTheory.HasQExpansion.of_periodic (by exact_mod_cast hN)
    (periodic_comp_ofComplex_of_vadd_real hper) hf hbdd

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionOfPeriodicBoundedHolomorphicStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansion_of_periodic_bounded_holomorphic : ∀ (N : ℕ) (f : ℍ → ℂ), 0 < N → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → (∀ τ : ℍ, f ((N : ℝ) +ᵥ τ) = f τ) → UpperHalfPlane.IsBoundedAtImInfty f → ∃ a, HasQ N f a := by
  first | exact @GlobalTheory.FN.hasQ_of_periodic_bounded | exact GlobalTheory.FN.hasQ_of_periodic_bounded | (intros; apply GlobalTheory.FN.hasQ_of_periodic_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesAsRatHahnSeriesFractionalQ
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesAsRatHahnSeriesFractionalQ
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem powerSeries_to_hahnSeries_rat :
    ∀ (Ω : Type) [Field Ω] (N : ℕ), 0 < N → ∃ Φ : PowerSeries Ω →+* HahnSeries ℚ Ω, (∀ (p : PowerSeries Ω) (k : ℕ), (Φ p).coeff ((k : ℚ) / N) = PowerSeries.coeff k p) ∧ ∀ (p : PowerSeries Ω) (r : ℚ), (∀ k : ℕ, r ≠ (k : ℚ) / N) → (Φ p).coeff r = 0 := by
  intro Ω _ N hN
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  let f : ℕ →+ ℚ := (AddMonoidHom.mulRight ((N : ℚ)⁻¹)).comp (Nat.castAddMonoidHom ℚ)
  have hf : ∀ k : ℕ, f k = (k : ℚ) / N := fun k => by
    simp [f, div_eq_mul_inv]
  have hfle : ∀ g g' : ℕ, f g ≤ f g' ↔ g ≤ g' := fun g g' => by
    rw [hf, hf, div_le_div_iff_of_pos_right hN', Nat.cast_le]
  have hfi : Function.Injective f := fun g g' h =>
    le_antisymm ((hfle g g').1 h.le) ((hfle g' g).1 h.ge)
  refine ⟨(HahnSeries.embDomainRingHom f hfi hfle).comp
    (HahnSeries.toPowerSeries (R := Ω)).symm.toRingHom, ?_, ?_⟩
  · intro p k
    rw [← hf]
    simp only [RingHom.comp_apply, HahnSeries.embDomainRingHom_apply]
    rw [HahnSeries.embDomain_mk_coeff]
    rfl
  · intro p r hr
    simp only [RingHom.comp_apply, HahnSeries.embDomainRingHom_apply]
    apply HahnSeries.embDomain_notin_image_support
    rintro ⟨k, -, hk⟩
    exact hr k (by rw [← hf]; exact hk.symm)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesAsRatHahnSeriesFractionalQStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeries_as_rat_hahnSeries_fractional_q : ∀ (Ω : Type) [Field Ω] (N : ℕ), 0 < N → ∃ Φ : PowerSeries Ω →+* HahnSeries ℚ Ω, (∀ (p : PowerSeries Ω) (k : ℕ), (Φ p).coeff ((k : ℚ) / N) = PowerSeries.coeff k p) ∧ ∀ (p : PowerSeries Ω) (r : ℚ), (∀ k : ℕ, r ≠ (k : ℚ) / N) → (Φ p).coeff r = 0 := by
  first | exact @GlobalTheory.powerSeries_to_hahnSeries_rat | exact GlobalTheory.powerSeries_to_hahnSeries_rat | (intros; apply GlobalTheory.powerSeries_to_hahnSeries_rat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagOneUnitConjLiftsSl2IntReductionMod
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagOneUnitConjLiftsSl2IntReductionMod
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_redGL_eq {N : ℕ} (g : GL (Fin 2) (ZMod N))
    (hg : Matrix.det (g : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1) : ∃ γ : SL(2, ℤ), redGL N γ = g := by
  obtain ⟨γ, hγ⟩ := GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) N ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod N)), hg⟩
  refine ⟨γ, Units.ext ?_⟩
  show ((Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ) : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = g
  rw [hγ]; rfl

theorem dg_conj_lift : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ), (∀ γ : SL(2, ℤ), ∃ γ' : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u) ∧ ∀ γ' : SL(2, ℤ), ∃ γ : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u := by
  intro N _ u
  have hdet : ∀ γ : SL(2, ℤ), Matrix.det ((redGL N γ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
    intro γ
    exact (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ).2
  have hconj : ∀ (a g : GL (Fin 2) (ZMod N)), Matrix.det ((g : Matrix (Fin 2) (Fin 2) (ZMod N))) = 1 →
      Matrix.det (((a⁻¹ * g * a : GL (Fin 2) (ZMod N))) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
    intro a g hg
    simp only [Units.val_mul, Matrix.det_mul]
    rw [hg, mul_one, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  refine ⟨fun γ => ?_, fun γ' => ?_⟩
  · obtain ⟨γ', h⟩ := exists_redGL_eq _ (hconj (dg u) (redGL N γ) (hdet γ))
    refine ⟨γ', ?_⟩
    rw [h]; group
  · obtain ⟨γ, h⟩ := exists_redGL_eq _ (hconj (dg u)⁻¹ (redGL N γ') (hdet γ'))
    refine ⟨γ, ?_⟩
    rw [h]; group

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagOneUnitConjLiftsSl2IntReductionModStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagOneUnit_conj_lifts_sl2IntReductionMod : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ), (∀ γ : SL(2, ℤ), ∃ γ' : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u) ∧ ∀ γ' : SL(2, ℤ), ∃ γ : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u := by
  first | exact @GlobalTheory.FN.dg_conj_lift | exact GlobalTheory.FN.dg_conj_lift | (intros; apply GlobalTheory.FN.dg_conj_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonicRootNormLeOneAddSum
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonicRootNormLeOneAddSum
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem monic_root_norm_le_one_add_sum :
    ∀ (n : ℕ) (s : Fin n → ℂ) (y : ℂ), y ^ n + ∑ j, s j * y ^ (j : ℕ) = 0 →
      ‖y‖ ≤ 1 + ∑ j, ‖s j‖ := by
  intro n s y h
  have hS : 0 ≤ ∑ j, ‖s j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  by_cases hy : ‖y‖ ≤ 1
  · linarith
  push_neg at hy
  cases n with
  | zero => simp at h
  | succ m =>
    have hyn : y ^ (m + 1) = -∑ j, s j * y ^ (j : ℕ) := eq_neg_of_add_eq_zero_left h
    have h1 : ‖y‖ ^ (m + 1) ≤ ∑ j, ‖s j‖ * ‖y‖ ^ (j : ℕ) := by
      rw [← norm_pow, hyn, norm_neg]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [norm_mul, norm_pow]
    have h2 : ∑ j : Fin (m + 1), ‖s j‖ * ‖y‖ ^ (j : ℕ) ≤ (∑ j, ‖s j‖) * ‖y‖ ^ m := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact pow_le_pow_right₀ hy.le (Nat.lt_succ_iff.mp j.isLt)
    have h3 : ‖y‖ ^ (m + 1) = ‖y‖ * ‖y‖ ^ m := pow_succ' _ _
    have hpos : 0 < ‖y‖ ^ m := pow_pos (by linarith) m
    have h4 : ‖y‖ ≤ ∑ j, ‖s j‖ := by
      have h5 := h1.trans h2
      rw [h3] at h5
      exact le_of_mul_le_mul_right h5 hpos
    linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonicRootNormLeOneAddSumStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_root_le_one_add_sum_norm_coeff : ∀ (n : ℕ) (s : Fin n → ℂ) (y : ℂ), y ^ n + ∑ j, s j * y ^ (j : ℕ) = 0 → ‖y‖ ≤ 1 + ∑ j, ‖s j‖ := by
  first | exact @GlobalTheory.monic_root_norm_le_one_add_sum | exact GlobalTheory.monic_root_norm_le_one_add_sum | (intros; apply GlobalTheory.monic_root_norm_le_one_add_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolynomialRelationPassesToQExpansions
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolynomialRelationPassesToQExpansions
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam

theorem HasQ.mul_powerSeries {N : ℕ} {f g : ℍ → ℂ} {φ ψ : PowerSeries ℂ}
    (hf : HasQ N f (fun n => PowerSeries.coeff n φ)) (hg : HasQ N g (fun n => PowerSeries.coeff n ψ)) :
    HasQ N (fun τ => f τ * g τ) (fun n => PowerSeries.coeff n (φ * ψ)) := by
  have h := hf.mul_conv hg
  have e : conv (fun n => PowerSeries.coeff n φ) (fun n => PowerSeries.coeff n ψ) =
      fun n => PowerSeries.coeff n (φ * ψ) := by
    funext n; rw [conv, PowerSeries.coeff_mul]
  rwa [e] at h

theorem HasQ.pow_powerSeries {N : ℕ} {f : ℍ → ℂ} {b : ℕ → ℂ} (hf : HasQ N f b) (i : ℕ) :
    HasQ N (fun τ => f τ ^ i) (fun n => PowerSeries.coeff n (PowerSeries.mk b ^ i)) := by
  induction i with
  | zero =>
    have h := HasQ.const N (1 : ℂ)
    convert h using 2 <;> simp [PowerSeries.coeff_one]
  | succ i ih =>
    have hb : HasQ N f (fun n => PowerSeries.coeff n (PowerSeries.mk b)) := by
      simpa only [PowerSeries.coeff_mk] using hf
    have h := ih.mul_powerSeries hb
    simpa only [pow_succ] using h

theorem polyRel_qSeries : ∀ (N n : ℕ) (f : ℍ → ℂ) (b : ℕ → ℂ) (p : ℕ → ℍ → ℂ) (c : ℕ → ℕ → ℂ), 0 < N → HasQ N f b → (∀ i, HasQ N (p i) (c i)) → (∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * f τ ^ i = 0) → (∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (c i))).eval (PowerSeries.mk b) = 0 := by
  intro N n f b p c hN hf hp hrel
  have hterm : ∀ i ∈ Finset.range (n + 1), HasQ N (fun τ => p i τ * f τ ^ i)
      (fun m => PowerSeries.coeff m (PowerSeries.mk (c i) * PowerSeries.mk b ^ i)) := by
    intro i _
    have hpi : HasQ N (p i) (fun m => PowerSeries.coeff m (PowerSeries.mk (c i))) := by
      simpa only [PowerSeries.coeff_mk] using hp i
    exact hpi.mul_powerSeries (hf.pow_powerSeries i)
  have hsum := HasQ.sum (Finset.range (n + 1)) hterm
  have hzero : HasQ N (fun τ => ∑ i ∈ Finset.range (n + 1), p i τ * f τ ^ i) (fun _ => 0) := by
    have h0 := HasQ.const N (0 : ℂ)
    have e : (fun τ => ∑ i ∈ Finset.range (n + 1), p i τ * f τ ^ i) = fun _ => (0 : ℂ) :=
      funext hrel
    rw [e]
    simpa using h0
  have hc := HasQ.coeff_unique hN hsum hzero
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  ext m
  have := congrFun hc m
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum] using this

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolynomialRelationPassesToQExpansionsStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_relation_passes_to_qExpansions : ∀ (N n : ℕ) (f : ℍ → ℂ) (b : ℕ → ℂ) (p : ℕ → ℍ → ℂ) (c : ℕ → ℕ → ℂ), 0 < N → HasQ N f b → (∀ i, HasQ N (p i) (c i)) → (∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * f τ ^ i = 0) → (∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (c i))).eval (PowerSeries.mk b) = 0 := by
  first | exact @GlobalTheory.QFam.polyRel_qSeries | exact GlobalTheory.QFam.polyRel_qSeries | (intros; apply GlobalTheory.QFam.polyRel_qSeries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PermutedModularFamilyMonicPolyCoeffInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PermutedModularFamilyMonicPolyCoeffInvariant
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Polynomial

namespace GlobalTheory.QFam

theorem vieta_root {ι : Type} [Fintype ι] (y : ι → ℂ) (i : ι) :
    y i ^ Fintype.card ι + ∑ j : Fin (Fintype.card ι),
      ((-1) ^ (Fintype.card ι - (j : ℕ)) *
        ∑ t ∈ Finset.powersetCard (Fintype.card ι - (j : ℕ)) Finset.univ, ∏ l ∈ t, y l) *
        y i ^ (j : ℕ) = 0 := by
  classical
  set n := Fintype.card ι with hn
  set P : ℂ[X] := ∏ l, (X + C (-y l)) with hP
  have hmon : P.Monic := monic_prod_of_monic _ _ fun l _ => monic_X_add_C _
  have hdeg : P.natDegree = n := by
    rw [hP, natDegree_prod_of_monic _ _ fun l _ => monic_X_add_C _]
    simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hn]
  have hroot : P.eval (y i) = 0 := by
    rw [hP, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hcoeff : ∀ j ≤ n, P.coeff j =
      (-1) ^ (n - j) * ∑ t ∈ Finset.powersetCard (n - j) Finset.univ, ∏ l ∈ t, y l := by
    intro j hj
    rw [hP, Finset.prod_X_add_C_coeff _ _ (by simpa [hn] using hj), Finset.card_univ, ← hn,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.prod_neg, (Finset.mem_powersetCard.mp ht).2]
  have h1 : P.coeff n = 1 := hdeg ▸ hmon.coeff_natDegree
  rw [eval_eq_sum_range, hdeg, Finset.sum_range_succ, h1, one_mul] at hroot
  rw [← hroot, add_comm]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun m => P.coeff m * y i ^ m)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcoeff j j.2.le]

end GlobalTheory.QFam

theorem GlobalTheory.QFam.minpoly_coeff_invariant : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (k N : ℕ) (F : ι → ℍ → ℂ) (R : Subring ℂ), 0 < N → ActBij act → IsFam act k F → (∀ i, QAll (· ∈ R) N (F i)) → ∃ s : Fin (Fintype.card ι) → ℍ → ℂ, (∀ j : Fin (Fintype.card ι), (∀ γ : SL(2, ℤ), s j ∣[((k * (Fintype.card ι - j) : ℕ) : ℤ)] γ = s j) ∧ QAll (· ∈ R) N (s j)) ∧ ∀ i τ, F i τ ^ Fintype.card ι + ∑ j, s j τ * F i τ ^ (j : ℕ) = 0 := by
  intro ι _ act k N F R _ hb hF hQ
  refine ⟨fun j τ => (-1) ^ (Fintype.card ι - (j : ℕ)) *
      ∑ t ∈ Finset.powersetCard (Fintype.card ι - (j : ℕ)) Finset.univ, ∏ l ∈ t, F l τ,
    fun j => ⟨fun γ => ?_, ?_⟩, fun i τ => vieta_root (fun l => F l τ) i⟩
  · have hE := IsFam.esymm_slash hb hF γ (Fintype.card ι - (j : ℕ))
    have hw : (((k * (Fintype.card ι - (j : ℕ)) : ℕ) : ℤ)) =
        (((Fintype.card ι - (j : ℕ) : ℕ) : ℤ) * (k : ℤ)) := by
      rw [Nat.cast_mul, mul_comm]
    funext τ
    have hEτ := congrFun hE τ
    rw [ModularForm.SL_slash_apply] at hEτ
    rw [hw, ModularForm.SL_slash_apply, mul_assoc, hEτ]
  · exact QAllSubring.mul (QAllSubring.const (R.pow_mem (R.neg_mem R.one_mem) _))
      (QAllSubring.sum _ fun t _ => QAllSubring.prod _ fun l _ => hQ l)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PermutedModularFamilyMonicPolyCoeffInvariantStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.permutedModularFamily_monic_poly_coeff_invariant : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (k N : ℕ) (F : ι → ℍ → ℂ) (R : Subring ℂ), 0 < N → ActBij act → IsFam act k F → (∀ i, QAll (· ∈ R) N (F i)) → ∃ s : Fin (Fintype.card ι) → ℍ → ℂ, (∀ j : Fin (Fintype.card ι), (∀ γ : SL(2, ℤ), s j ∣[((k * (Fintype.card ι - j) : ℕ) : ℤ)] γ = s j) ∧ QAll (· ∈ R) N (s j)) ∧ ∀ i τ, F i τ ^ Fintype.card ι + ∑ j, s j τ * F i τ ^ (j : ℕ) = 0 := by
  first | exact @GlobalTheory.QFam.minpoly_coeff_invariant | exact GlobalTheory.QFam.minpoly_coeff_invariant | (intros; apply GlobalTheory.QFam.minpoly_coeff_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommonLevelSpanMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommonLevelSpanMultiple
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ

theorem _root_.GlobalTheory.KZ.gamma_le_of_dvd {M M' : ℕ} (h : M ∣ M') :
    CongruenceSubgroup.Gamma M' ≤ CongruenceSubgroup.Gamma M := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have e : ∀ z : ℤ, (z : ZMod M) = ZMod.castHom h (ZMod M) (z : ZMod M') := fun z =>
    (map_intCast _ z).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e, h1, map_one]
  · rw [e, h2, map_zero]
  · rw [e, h3, map_zero]
  · rw [e, h4, map_one]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.lev_mono (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {M M' : ℕ} (h : M ∣ M') :
    X.Lev l M ≤ X.Lev l M' := by
  apply Submodule.span_mono
  rintro x ⟨f, hf, rfl⟩
  exact ⟨f, fun γ hγ => hf γ (gamma_le_of_dvd h hγ), rfl⟩

theorem Tower.exists_lev (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (y : X.Kl l) :
    ∃ M : ℕ, 0 < M ∧ y ∈ X.Lev l M := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, Submodule.zero_mem _⟩
  | tmul a f =>
    obtain ⟨M, hM, hf⟩ := X.level (Additive.toMul f : X.Kˣ)
    refine ⟨M, hM, ?_⟩
    have hmem : (1 : ℤ_[l]) ⊗ₜ[ℤ] f ∈ X.Lev l M :=
      Submodule.subset_span ⟨Additive.toMul f, fun γ hγ => hf γ hγ, rfl⟩
    have e : a ⊗ₜ[ℤ] f = a • ((1 : ℤ_[l]) ⊗ₜ[ℤ] f) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e]
    exact Submodule.smul_mem _ a hmem
  | add y z hy hz =>
    obtain ⟨M, hM, hy⟩ := hy
    obtain ⟨M', hM', hz⟩ := hz
    refine ⟨M * M', Nat.mul_pos hM hM', Submodule.add_mem _ ?_ ?_⟩
    · exact X.lev_mono l (dvd_mul_right M M') hy
    · exact X.lev_mono l (dvd_mul_left M' M) hz

theorem Tower.exists_lev_family : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime] (K : ℕ) {ι : Type} [Fintype ι] (y : ι → X.Kl l), 0 < K →
    ∃ M : ℕ, 0 < M ∧ K ∣ M ∧ ∀ i, y i ∈ X.Lev l M := by
  intro Ω _ _ ε X l _ K ι _ y hK
  choose L hL hy using fun i => X.exists_lev l (y i)
  refine ⟨K * ∏ i, L i, Nat.mul_pos hK (Finset.prod_pos fun i _ => hL i), dvd_mul_right _ _, fun i => ?_⟩
  refine X.lev_mono l ?_ (hy i)
  exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem L (Finset.mem_univ i)) K

end GlobalTheory.KZ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommonLevelSpanMultipleStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_level_span_multiple : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (K : ℕ) {ι : Type} [Fintype ι] (y : ι → X.Kl l), 0 < K → ∃ M : ℕ, 0 < M ∧ K ∣ M ∧ ∀ i, y i ∈ X.Lev l M := by
  first | exact @GlobalTheory.KZ.Tower.exists_lev_family | exact GlobalTheory.KZ.Tower.exists_lev_family | (intros; apply GlobalTheory.KZ.Tower.exists_lev_family <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSlTwoPermutedModularFamilyOfLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSlTwoPermutedModularFamilyOfLevel
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FamOfLevel

theorem redGL_mul (N : ℕ) (γ δ : SL(2, ℤ)) : redGL N (γ * δ) = redGL N γ * redGL N δ := by
  simp [redGL]

theorem redGL_eq_one_iff (N : ℕ) (γ : SL(2, ℤ)) : redGL N γ = 1 ↔ γ ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem', redGL]
  constructor
  · intro h
    apply Matrix.SpecialLinearGroup.toGL_injective
    simpa using h
  · intro h
    rw [h]; simp

theorem slash_eq_of_redGL_eq (N : ℕ) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[k] γ = f) {γ δ : SL(2, ℤ)}
    (h : redGL N γ = redGL N δ) : f ∣[k] γ = f ∣[k] δ := by
  have hη : γ * δ⁻¹ ∈ CongruenceSubgroup.Gamma N := by
    rw [← redGL_eq_one_iff, redGL_mul, h, ← redGL_mul, mul_inv_cancel]
    simp [redGL]
  have : γ = (γ * δ⁻¹) * δ := by group
  rw [this, SlashAction.slash_mul, hf _ hη]

theorem exists_family (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[k] γ = f) :
    ∃ F : GL (Fin 2) (ZMod N) → ℍ → ℂ, IsFam (gact N 1) k F ∧
      (∀ γ : SL(2, ℤ), F (redGL N γ) = f ∣[k] γ) ∧
      ∀ α, (∃ γ : SL(2, ℤ), α = redGL N γ) ∨ F α = 0 := by
  classical
  let F : GL (Fin 2) (ZMod N) → ℍ → ℂ := fun α =>
    if h : ∃ γ : SL(2, ℤ), α = redGL N γ then f ∣[k] h.choose else 0
  have hF : ∀ γ : SL(2, ℤ), F (redGL N γ) = f ∣[k] γ := by
    intro γ
    have h : ∃ δ : SL(2, ℤ), redGL N γ = redGL N δ := ⟨γ, rfl⟩
    simp only [F, dif_pos h]
    exact slash_eq_of_redGL_eq N k f hf h.choose_spec.symm
  refine ⟨F, ?_, hF, ?_⟩
  · intro α γ
    rw [gact_one]
    by_cases h : ∃ δ : SL(2, ℤ), α = redGL N δ
    · obtain ⟨δ, rfl⟩ := h
      rw [hF, ← redGL_mul, hF, SlashAction.slash_mul]
    · have h' : ¬ ∃ δ : SL(2, ℤ), α * redGL N γ = redGL N δ := by
        rintro ⟨δ, hδ⟩
        apply h
        refine ⟨δ * γ⁻¹, ?_⟩
        rw [redGL_mul, ← hδ, mul_assoc, ← redGL_mul, mul_inv_cancel]
        simp [redGL]
      simp only [F, dif_neg h, dif_neg h']
      exact SlashAction.zero_slash _ _
  · intro α
    by_cases h : ∃ γ : SL(2, ℤ), α = redGL N γ
    · exact Or.inl h
    · right; simp only [F, dif_neg h]

end GlobalTheory.FamOfLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSlTwoPermutedModularFamilyOfLevelStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_slTwoPermutedModularFamily_of_level : ∀ (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ), (∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[k] γ = f) → ∃ F : GL (Fin 2) (ZMod N) → ℍ → ℂ, IsFam (gact N 1) k F ∧ (∀ γ : SL(2, ℤ), F (redGL N γ) = f ∣[k] γ) ∧ ∀ α, (∃ γ : SL(2, ℤ), α = redGL N γ) ∨ F α = 0 := by
  first | exact @GlobalTheory.FamOfLevel.exists_family | exact GlobalTheory.FamOfLevel.exists_family | (intros; apply GlobalTheory.FamOfLevel.exists_family <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterEqOneNearOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterEqOneNearOne
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ev_one' (χ : kˣ →* ℂˣ) : ev χ (1 : k) = 1 := by
  unfold ev
  simp

theorem minor_one' {n : ℕ} (m : Fin n) : minor (1 : GL (Fin n) k) m = 1 := by
  unfold minor
  simp [Matrix.toSquareBlockProp]

theorem continuous_minor' {n : ℕ} (m : Fin n) : Continuous fun g : GL (Fin n) k => minor g m := by
  unfold minor
  exact (Units.continuous_val.matrix_submatrix _ _).matrix_det

theorem ev_eventually_one (χ : kˣ →* ℂˣ) (S : Set k) (hS : S ∈ nhds (0 : k)) (hT : ∀ x ∈ S, Triv χ x) :
    ∀ᶠ x in nhds (1 : k), ev χ x = 1 := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := triv_ev_props k
  have hball : {x : k | valuation k (x - 1) < 1} ∈ nhds (1 : k) :=
    (IsValuativeTopology.hasBasis_nhds' (1 : k)).mem_of_mem one_ne_zero
  have hpre : (fun x : k => x - 1) ⁻¹' S ∈ nhds (1 : k) :=
    (continuous_sub_right (1 : k)).continuousAt.preimage_mem_nhds (by simpa using hS)
  filter_upwards [hball, hpre] with x hx hxS
  have hv : valuation k x = 1 := by
    have : x = 1 + (x - 1) := by ring
    rw [this]
    exact Valuation.map_one_add_of_lt _ hx
  rw [h8 χ x 1 hv (by simp) (hT _ hxS), ev_one']

theorem theta_one_and_near : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) →
    theta ψ 1 = 1 ∧ ∃ U ∈ nhds (1 : GL (Fin n) k), ∀ g ∈ U, theta ψ g = 1 := by
  intro k _ _ _ _ n ψ hψ
  obtain ⟨-, -, h3, h4, h5, h6, -, -, -⟩ := triv_ev_props k
  have hset : ∀ χ : kˣ →* ℂˣ, IsSmoothChar χ → {x : k | Triv χ x} ∈ nhds (0 : k) := fun χ hχ =>
    (h6 χ hχ).1.mem_nhds (h3 χ)
  have hnxt : ∀ m, {x : k | Triv (nxt ψ m) x} ∈ nhds (0 : k) := by
    intro m
    unfold nxt
    split_ifs with h
    · exact hset _ (hψ _)
    · refine Filter.univ_mem' fun x => ?_
      intro u _ _
      rfl
  have hev : ∀ m, ∀ᶠ x in nhds (1 : k), ev (ψ m / nxt ψ m) x = 1 := fun m =>
    ev_eventually_one _ _ (Filter.inter_mem (hset _ (hψ m)) (hnxt m)) fun x hx => by
      rw [div_eq_mul_inv]
      exact h4 _ _ x hx.1 (h5 _ x hx.2)
  refine ⟨?_, ?_⟩
  · unfold theta
    exact Finset.prod_eq_one fun m _ => by rw [minor_one', ev_one']
  · have hall : ∀ᶠ g in nhds (1 : GL (Fin n) k), ∀ m, ev (ψ m / nxt ψ m) (minor g m) = 1 := by
      rw [Filter.eventually_all]
      intro m
      have hc := (continuous_minor' (k := k) m).continuousAt (x := 1)
      rw [ContinuousAt, minor_one'] at hc
      exact hc.eventually (hev m)
    exact ⟨_, hall, fun g hg => Finset.prod_eq_one fun m _ => hg m⟩

end

end GlobalTheory.PsType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterEqOneNearOneStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → theta ψ 1 = 1 ∧ ∃ U ∈ nhds (1 : GL (Fin n) k), ∀ g ∈ U, theta ψ g = 1 := by
  first | exact @GlobalTheory.PsType.theta_one_and_near | exact GlobalTheory.PsType.theta_one_and_near | (intros; apply GlobalTheory.PsType.theta_one_and_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicCharacterFrobV
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem rootOfUnity_eq_one_of_val {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    {m : ℕ} (hm : ¬ v (m : K) < 1) {η : K} (hη : η ^ m = 1) (h1 : v (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hm
  have hv : v η = 1 := by
    have := v.map_one_add_of_lt h1
    simpa using this
  have hi : ∀ i : ℕ, v (1 - η ^ i) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : 1 - η ^ (i + 1) = (1 - η ^ i) + -(η ^ i * (η - 1)) := by ring
      rw [e]
      refine v.map_add_lt ih ?_
      rw [v.map_neg, map_mul, map_pow, hv, one_pow, one_mul]
      exact h1
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  have e : (m : K) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  exact v.map_sum_lt one_ne_zero fun i _ => hi i

theorem not_val_lt_one_of_coprime {K : Type*} [Field K] (V : ValuationSubring K) {m q : ℕ} (h : Nat.Coprime m q)
    (hq : V.valuation (q : K) < 1) : ¬ V.valuation (m : K) < 1 := by
  intro hm
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  have e : (1 : K) = (a : K) * m + (b : K) * q := by
    have := congrArg (Int.cast : ℤ → K) hab
    push_cast at this
    exact this.symm
  have hz : ∀ (c : ℤ) (x : K), V.valuation x < 1 → V.valuation ((c : K) * x) < 1 := by
    intro c x hx
    rw [map_mul]
    have hc : V.valuation (c : K) ≤ 1 := (V.valuation_le_one_iff _).mpr (intCast_mem V c)
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hx
  have := V.valuation.map_add_lt (hz a _ hm) (hz b _ hq)
  rw [← e, map_one] at this
  exact lt_irrefl _ this

theorem FrobV.apply_rootOfUnity {Ω : Type} [Field Ω] [Algebra ℚ Ω] {V : ValuationSubring Ω} {q : ℕ}
    {s : Ω ≃ₐ[ℚ] Ω} (hs : FrobV V q s) {m : ℕ} (hm0 : m ≠ 0) (hm : Nat.Coprime m q) {ζ : Ω} (hζ : ζ ^ m = 1) :
    s ζ = ζ ^ q := by
  have hq : V.valuation (q : Ω) < 1 := V.mem_nonunits_iff.mp hs.1
  have hv : V.valuation ζ = 1 := by
    have := congrArg V.valuation hζ
    rw [map_pow, map_one] at this
    exact (pow_eq_one_iff_left hm0).mp this
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hv
  have hV : ζ ∈ V := (V.valuation_le_one_iff _).mp hv.le
  have h := (hs.2 ζ hV).2.2
  have hq0 : ζ ^ q ≠ 0 := pow_ne_zero _ hζ0
  have key : s ζ / ζ ^ q = 1 := by
    refine rootOfUnity_eq_one_of_val V.valuation (not_val_lt_one_of_coprime V hm hq) ?_ ?_
    · rw [div_pow, ← map_pow, hζ, map_one, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, div_one]
    · rw [div_sub_one hq0, map_div₀, map_pow, hv, one_pow, div_one]
      exact h
  exact (div_eq_one_iff_eq hq0).mp key

theorem cyclotomicCharacter_frobV : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l q : ℕ) [Fact l.Prime],
    q.Prime → q ≠ l → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s →
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) = q := by
  intro Ω _ _ _ l q hl hq hql V s hs
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, NeZero ((l ^ i : ℕ) : Ω) := fun i => ⟨by exact_mod_cast pow_ne_zero i hl.out.ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [cyclotomicCharacter.toZModPow, map_natCast]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have ht' : (t : Ω) ^ (l ^ n) = 1 := (mem_rootsOfUnity' _ _).mp ht
  have hc : Nat.Coprime (l ^ n) q := ((Nat.coprime_primes hl.out hq).mpr hql.symm).pow_left n
  have := hs.apply_rootOfUnity (pow_ne_zero n hl.out.ne_zero) hc ht'
  rw [ZMod.val_natCast, ← pow_eq_pow_mod q ht']
  exact this

end GlobalTheory.KZ.ES
end
