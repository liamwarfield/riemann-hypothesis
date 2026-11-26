module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionSectionsOfRoot
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueExistsUniqueOfChartIndependence
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueWeightTriangularFrame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsIdempotentElemRangeSpMapSubset
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem eq_one_iff_isUnit_of_isIdempotentElem {R : Type} [CommRing R] {u : R} (hu : IsIdempotentElem u) :
    u = 1 ↔ IsUnit u := by
  constructor
  · rintro rfl
    exact isUnit_one
  · intro h
    exact h.mul_left_cancel (by rw [hu.eq, _root_.mul_one])

private theorem isUnit_iff_forall_primeSpectrum_notMem {R : Type} [CommRing R] (x : R) :
    IsUnit x ↔ ∀ q : PrimeSpectrum R, x ∉ q.asIdeal := by
  constructor
  · intro h q hq
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hq h)
  · intro h
    by_contra hx
    obtain ⟨I, hI, hxI⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hx)
    exact h ⟨I, hI.isPrime⟩ hxI

theorem exists_isIdempotentElem_range_spMap_subset {B : Type} [CommRing B] {U : Set (Sp B)} (hU : IsClopen U) :
    ∃ e : B, IsIdempotentElem e ∧ ∀ (T : Type) [CommRing T] (χ : B →+* T), χ e = 1 ↔ Set.range (spMap χ) ⊆ U := by
  let s : TopologicalSpace.Clopens (PrimeSpectrum B) := ⟨U, hU⟩
  have he : IsIdempotentElem (PrimeSpectrum.isIdempotentElemEquivClopens.symm s).1 :=
    (PrimeSpectrum.isIdempotentElemEquivClopens.symm s).2

  have hmem : ∀ p : PrimeSpectrum B,
      p ∈ U ↔ (PrimeSpectrum.isIdempotentElemEquivClopens.symm s).1 ∉ p.asIdeal := by
    intro p
    have h := congrArg (fun o : TopologicalSpace.Opens (PrimeSpectrum B) => p ∈ o)
      (PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm s)
    simp only [eq_iff_iff] at h
    rw [PrimeSpectrum.mem_basicOpen] at h
    exact h.symm
  refine ⟨_, he, fun T _ χ => ?_⟩
  rw [eq_one_iff_isUnit_of_isIdempotentElem (he.map χ), isUnit_iff_forall_primeSpectrum_notMem]
  constructor
  · rintro h _ ⟨q, rfl⟩
    exact (hmem _).2 (h q)
  · intro h q
    exact (hmem _).1 (h ⟨q, rfl⟩)

theorem exists_isIdempotentElem_torsion_eq :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (B : Type) [CommRing B] (x0 : Sp B ⟶ Xo.X) (k : ℕ), 0 < k → ∀ (a b : ptO Xo x0 ⟶ Xo.univ.t.G), a ^ k = 1 → b ^ k = 1 → ∃ e : B, IsIdempotentElem e ∧ ∀ (T : Type) [CommRing T] (χ : B →+* T), χ e = 1 ↔ spMap χ ≫ a.left = spMap χ ≫ b.left := by
  intro _ E _ _ _ H Dw l Xo B _ x0 k hk a b ha hb
  obtain ⟨-, -, hunit, hab, -⟩ := moduli_univ_polAV E H Dw l Xo
  obtain ⟨Z, et, hZf, hZe, hadd, hpow, huniv⟩ :=
    exists_finiteEtale_latticeTorsionHom Xo.X Xo.univ.t.G k ℤ hab (hunit k hk)
  have R : LevCover.RepTors Xo.univ.t.G k ℤ Z et := ⟨hZf, hZe, hadd, hpow, huniv⟩

  have hz : ∀ c : ptO Xo x0 ⟶ Xo.univ.t.G, c ^ k = 1 → ∀ m : ℤ, (c ^ m) ^ k = 1 := by
    intro c hc m
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow]
  obtain ⟨U, hUc, hU⟩ := R.clopenCond (T := ptO Xo x0) (fun m => a ^ m) (fun m => b ^ m)
    (fun m c => zpow_add a m c) (hz a ha) (fun m c => zpow_add b m c) (hz b hb)
  let V : Set (Sp B) := (U : Set (ptO Xo x0).left)
  obtain ⟨e, he, hE⟩ := exists_isIdempotentElem_range_spMap_subset (B := B) (U := V) ⟨hUc, U.isOpen⟩
  refine ⟨e, he, fun T _ χ => ?_⟩
  rw [hE T χ]
  let h : Over.mk (spMap χ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap χ) rfl
  have hh : Set.range (spMap χ) ⊆ V ↔ Set.range h.left ⊆ U := Iff.rfl
  rw [hh, ← hU _ h]
  simp only [GrpObj.comp_zpow]
  constructor
  · intro hm
    have h1 : h ≫ a = h ≫ b := by simpa using hm 1
    simpa [h] using congrArg CommaMorphism.left h1
  · intro hl m
    have h1 : h ≫ a = h ≫ b := Over.OverMorphism.ext (by simpa [h] using hl)
    rw [h1]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleMemSec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem thetaRule_mem_sec : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ thGen Xo c nab a n, f ∈ sec Xo c a n := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab a n f hf
  obtain ⟨x, P, hP, hR⟩ := hf
  unfold sec secW
  refine ⟨?_, ?_⟩
  · intro p q φ y z hyz
    exact (GlobalTheory.T.thetaValue_natural_algebraMap hL hC E H Dw l Xo c nab hnab p.R q.R φ y z hyz a n x P hP _ _ (hR p y) (hR q z)).symm
  · intro p t y y' hB
    have hid : FrMap (AlgHom.id c.F p.R) y' y' := by
      have hs : spMap (AlgHom.id c.F p.R).toRingHom = 𝟙 _ := by
        simp [spMap]
      have hd : spMap (dualMap (AlgHom.id c.F p.R).toRingHom) = 𝟙 _ := by
        have : dualMap (AlgHom.id c.F p.R).toRingHom = RingHom.id _ := by
          ext z <;> simp [dualMap]
        rw [this]
        simp [spMap]
      refine ⟨?_, ?_, 𝟙 _, ?_, ?_, ?_⟩
      · rw [hs, Category.id_comp]
      · intro τ i
        rw [hd, Category.id_comp]
      · simp
      · rw [hs]
        simp
      · intro i h
        have e : (Gx y'.x).presheaf.map (homOfLE h).op = 𝟙 _ := by
          erw [CategoryTheory.Functor.map_id]
        erw [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp, e]
        rfl
    have h1 := (GlobalTheory.T.thetaValue_weight_triangular_frame hL hC E H Dw l Xo c nab hnab p.R y y' t hB n a P).1 hP x (f p y) (hR p y)
    exact GlobalTheory.T.thetaValue_natural_algebraMap hL hC E H Dw l Xo c nab hnab p.R p.R (AlgHom.id c.F p.R) y' y' hid a n x P hP _ _ (hR p y') h1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HalfIntegralGeneratorTraceEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

private theorem complexConj_rt_eq_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hsq : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have h := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
    simpa using h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  set u := φ (H.rt : E) with hu
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp [pow_two] at hre him
  have him' : u.re * u.im = 0 := by linarith
  have hu0 : u.re = 0 := by
    rcases mul_eq_zero.1 him' with h | h
    · exact h
    · rw [h] at hre; nlinarith [sq_nonneg u.re]
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  apply Complex.ext
  all_goals simp
  all_goals (rw [← hu]; linarith)

theorem halfIntegralGenerator_trace_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  apply RingOfIntegers.coe_injective
  have h1 := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  rw [map_mul, map_add (f := _), map_one, map_ofNat] at h1
  have h2 := congrArg (IsCMField.complexConj E) h1
  rw [map_mul, map_add (f := _), map_one, map_ofNat] at h2
  have hr : IsCMField.complexConj E (algebraMap (𝓞 E) E H.rt) = -(algebraMap (𝓞 E) E H.rt) :=
    complexConj_rt_eq_neg H
  have hb : algebraMap (𝓞 E) E (H.bar H.w0) = IsCMField.complexConj E (algebraMap (𝓞 E) E H.w0) :=
    H.bar_eq _
  rw [map_add (f := _), map_one]
  linear_combination (h1 + h2) / 2 + hb + hr / 2

theorem univ_finset_fin_two : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide

theorem chi_sum_two {M : Type} [AddCommMonoid M] (f : ULift.{0} (Finset (Fin 2)) → M) :
    ∑ I, f I = f ⟨∅⟩ + f ⟨{0}⟩ + f ⟨{1}⟩ + f ⟨{0, 1}⟩ := by
  rw [← (Equiv.ulift (α := Finset (Fin 2))).symm.sum_comp, univ_finset_fin_two,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [Equiv.ulift_symm_apply, add_assoc]

theorem chi_prod_two {M : Type} [CommMonoid M] (f : ULift.{0} (Finset (Fin 2)) → M) :
    ∏ I, f I = f ⟨∅⟩ * f ⟨{0}⟩ * f ⟨{1}⟩ * f ⟨{0, 1}⟩ := by
  rw [← (Equiv.ulift (α := Finset (Fin 2))).symm.prod_comp, univ_finset_fin_two,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp only [Equiv.ulift_symm_apply, _root_.mul_assoc]

theorem chi_eq_sign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1 ∧ Φ.χ a = Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a (tyAct ty H.w0 a)).im : ℂ)) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ a ha
  obtain ⟨⟨wP, hP⟩, hrd⟩ := GlobalTheory.T.exists_normalisedIso_reading_one_analyticFrame E H Dw l Xo c y g ty el Φ
  have hlat : ∀ b ∈ Φ.lat, tyAct ty H.w0 b ∈ Φ.lat := by
    intro b hb
    have := Xo.univ.t.act.hom H.w0
    rw [← Φ.e_ker, Φ.lin, (Φ.e_ker b).2 hb, MonObj.one_comp]
  have hw := hlat a ha
  have htr : ∀ w : Fin g → ℂ, tyAct ty H.w0 w + tyAct ty (H.bar H.w0) w = w := by
    intro w
    have h1 : (H.w0 : E) + ((H.bar H.w0 : 𝓞 E) : E) = 1 := by
      exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) (halfIntegralGenerator_trace_eq_one H)
    funext k
    simp only [tyAct, Pi.add_apply, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
    rw [← add_mul, ← map_add (f := _), h1, map_one, _root_.one_mul]
  let Λ : (Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    Sum.elim (fun _ => LinearMap.id) (fun I => (psumL 2 g I).comp (LinearMap.pi ![LinearMap.id, tyAct ty H.w0]))
  have hΛ : ∀ k z, Λ k z = Sum.elim (fun _ => z) (fun I => psumL 2 g I ![z, tyAct ty H.w0 z]) k := by
    intro k z
    rcases k with k | I
    · rfl
    · simp only [Λ, Sum.elim_inr, LinearMap.comp_apply]
      congr 1
      funext i
      fin_cases i <;> rfl
  have hT := GlobalTheory.T.abelianHolomorphicFrame_reading_const_of_forms_cancel _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr _ _ _ _ wP hP.1 g
    (fun z => (Φ.e z).left) Λ Φ.lat Φ.hol
    (fun z k => by rw [hΛ]; exact (hrd wP hP z).1 k) Φ.span
    (fun gm hgm => ⟨fun z => by simp only [Φ.e_add, (Φ.e_ker gm).2 hgm, _root_.mul_one], fun k => by
      rw [hΛ]
      rcases k with k | I
      · exact hgm
      · show psumL 2 g I ![gm, tyAct ty H.w0 gm] ∈ Φ.lat
        simp only [psumL, LinearMap.sum_apply, LinearMap.proj_apply]
        refine AddSubgroup.sum_mem _ fun i _ => ?_
        fin_cases i
        · exact hgm
        · exact hlat gm hgm⟩)
    (fun z w => by
      rw [Fintype.sum_sum_type, Fin.sum_univ_one, chi_sum_two]
      simp [Λ, psumL, cε]
      have hz := semichar_herm_add_left Φ.Hm z (tyAct ty H.w0 z) (w + tyAct ty H.w0 w)
      have hz1 := semichar_herm_add_right Φ.Hm z w (tyAct ty H.w0 w)
      have hz2 := semichar_herm_add_right Φ.Hm (tyAct ty H.w0 z) w (tyAct ty H.w0 w)
      have h0 := semichar_herm_zero_left Φ.Hm (0 : Fin g → ℂ)
      have hadj := Φ.adj H.w0 z w
      have hs := semichar_herm_add_right Φ.Hm z (tyAct ty H.w0 w) (tyAct ty (H.bar H.w0) w)
      rw [htr] at hs
      linear_combination (-1 : ℂ) * hz - hz1 - hz2 - h0 - hadj + hs)
  have hprod := hT.2 a ha
  rw [Fintype.prod_sum_type, Fin.prod_univ_one, chi_prod_two] at hprod
  simp [Λ, psumL, cε] at hprod
  rw [Φ.toAnFr.χ_zero, Φ.toAnFr.χ_add ha hw] at hprod
  have ha0 := Φ.toAnFr.χ_ne_zero ha
  have hw0 := Φ.toAnFr.χ_ne_zero hw
  have hX := Complex.exp_ne_zero (Real.pi * Complex.I * ((hermForm Φ.Hm a (tyAct ty H.w0 a)).im : ℂ))
  have key : Φ.χ a * (Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a (tyAct ty H.w0 a)).im : ℂ)))⁻¹ = 1 := by
    rw [← hprod]
    field_simp
    try ring
  have hχ := (mul_inv_eq_one₀ hX).1 key
  obtain ⟨k, hk⟩ := Φ.toAnFr.herm_im_int ha hw
  refine ⟨?_, hχ⟩
  rw [hχ, hk, ← Complex.exp_nat_mul]
  convert Complex.exp_int_mul_two_pi_mul_I k using 2
  push_cast
  ring

end GlobalTheory.AnVal
end
