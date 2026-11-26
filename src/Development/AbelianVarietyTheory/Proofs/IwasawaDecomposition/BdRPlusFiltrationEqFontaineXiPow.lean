module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElement
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMatExp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPow
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.FilPrincipal

section General
variable {R : Type} [CommRing R] {I : Ideal R} {a : R}

theorem evalₐ_eq_zero_iff (h : I = Ideal.span {a}) (n : ℕ) (y : AdicCompletion I R) :
    AdicCompletion.evalₐ I n y = 0 ↔ algebraMap R (AdicCompletion I R) a ^ n ∣ y := by
  have hfg : I.FG := ⟨{a}, by simp [h]⟩
  have e : (I ^ n).map (algebraMap R (AdicCompletion I R)) =
      Ideal.span {algebraMap R (AdicCompletion I R) a ^ n} := by
    have : I ^ n = Ideal.span {a ^ n} := by rw [h, Ideal.span_singleton_pow]
    rw [this, Ideal.map_span, Set.image_singleton, map_pow]
  rw [← Ideal.mem_span_singleton, ← e, ← Submodule.restrictScalars_mem R,
    ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]
  have h' : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  exact map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R h').injective

theorem evalₐ_algebraMap (n : ℕ) (r : R) :
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r) = Ideal.Quotient.mk _ r := by
  rw [AlgHom.commutes]; rfl

theorem regular_of_isDomain [IsDomain R] (h : I = Ideal.span {a}) (ha : a ≠ 0) (y : AdicCompletion I R)
    (hy : algebraMap R (AdicCompletion I R) a * y = 0) : y = 0 := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [map_zero, evalₐ_eq_zero_iff h]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
  have h1 : algebraMap R (AdicCompletion I R) a ^ (n + 1) ∣ y - algebraMap R _ r := by
    rw [← evalₐ_eq_zero_iff h, map_sub, evalₐ_algebraMap, hr, sub_self]
  have h2 := congrArg (AdicCompletion.evalₐ I (n + 1)) hy
  rw [map_mul, map_zero, evalₐ_algebraMap, ← hr, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h2
  have h3 : I ^ (n + 1) = Ideal.span {a ^ (n + 1)} := by rw [h, Ideal.span_singleton_pow]
  rw [h3, Ideal.mem_span_singleton, pow_succ', mul_dvd_mul_iff_left ha] at h2
  have h4 : algebraMap R (AdicCompletion I R) a ^ n ∣ algebraMap R _ r := by
    rw [← map_pow]; exact map_dvd _ h2
  have h5 := dvd_add ((pow_dvd_pow _ (Nat.le_succ n)).trans h1) h4
  rwa [sub_add_cancel] at h5

theorem isAdicComplete_span (h : I = Ideal.span {a}) :
    IsAdicComplete (Ideal.span {algebraMap R (AdicCompletion I R) a}) (AdicCompletion I R) := by
  have hfg : I.FG := ⟨{a}, by simp [h]⟩
  have e : I.map (algebraMap R (AdicCompletion I R)) =
      Ideal.span {algebraMap R (AdicCompletion I R) a} := by
    have : ∀ J : Ideal R, J = Ideal.span {a} → J.map (algebraMap R (AdicCompletion I R)) =
        Ideal.span {algebraMap R (AdicCompletion I R) a} := by
      rintro J rfl
      rw [Ideal.map_span, Set.image_singleton]
    exact this I h
  rw [← e, IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete hfg

end General

theorem xi_ne_zero {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (he : IsEps e) : xi e ≠ 0 := by
  intro h0
  set a := (frobeniusEquiv (Per.Fl l) l).symm e with ha
  have h1 : xi e * (Per.tm a - 1) = Per.tm a ^ l - 1 := geom_sum_mul _ _
  rw [h0, zero_mul, eq_comm, sub_eq_zero, ← map_pow] at h1
  have h2 := congrArg (fun w : Per.Ainf l => w.coeff 0) h1
  simp only [WittVector.teichmuller_coeff_zero, WittVector.one_coeff_zero] at h2
  have h3 : a = 1 := by
    apply (frobeniusEquiv (Per.Fl l) l).injective
    rw [frobeniusEquiv_apply, frobenius_def, h2, map_one]
  apply he.2
  rw [← ha, h3, map_one]

end GlobalTheory.MemLoc.FilPrincipal


open GlobalTheory.MemLoc.FilPrincipal in
theorem GlobalTheory.MemLoc.filtration_eq_xi_pow : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e →
    (∀ (n : ℕ) (y : Per.BdRp l), y ∈ Per.FilP l n ↔ aDp l (xi e) ^ n ∣ y) ∧
    (∀ y : Per.BdRp l, aDp l (xi e) * y = 0 → y = 0) ∧
    IsAdicComplete (Ideal.span {aDp l (xi e)}) (Per.BdRp l) ∧
    (∀ n : ℕ, Function.Surjective (Per.ev l n)) := by
  intro l _ e he
  have hk := GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he
  obtain ⟨-, hd, hinj⟩ := GlobalTheory.T.usage l
  have hne : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ≠ 0 := fun h =>
    xi_ne_zero e he (hinj (h.trans (map_zero _).symm))
  obtain ⟨E, hE, hev⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  have ha : E (aDp l (xi e)) = algebraMap (Per.AinfP l) (AdicCompletion (Per.kerP l) (Per.AinfP l))
      (algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)) := by
    rw [aDp, RingHom.comp_apply, hE]
  refine ⟨fun n y => ?_, fun y hy => ?_, ?_, fun n => GlobalTheory.RingIface.ev_surj l n⟩
  · rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, ← hev, evalₐ_eq_zero_iff hk n (E y), ← ha, ← map_pow]
    exact map_dvd_iff E
  · have h1 := congrArg E hy
    rw [map_mul, map_zero, ha] at h1
    exact E.injective ((regular_of_isDomain hk hne (E y) h1).trans (map_zero E).symm)
  · rw [← IsAdicComplete.congr_ringEquiv _ E, Ideal.map_span, Set.image_singleton, ha]
    exact isAdicComplete_span hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → (∀ (n : ℕ) (y : Per.BdRp l), y ∈ Per.FilP l n ↔ aDp l (xi e) ^ n ∣ y) ∧ (∀ y : Per.BdRp l, aDp l (xi e) * y = 0 → y = 0) ∧ IsAdicComplete (Ideal.span {aDp l (xi e)}) (Per.BdRp l) ∧ (∀ n : ℕ, Function.Surjective (Per.ev l n)) := by
  first | exact @GlobalTheory.MemLoc.filtration_eq_xi_pow | exact GlobalTheory.MemLoc.filtration_eq_xi_pow | (intros; apply GlobalTheory.MemLoc.filtration_eq_xi_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApprox
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApprox
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.CrisUnique

variable {l : ℕ} [Fact l.Prime]

theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, e, h0, -, h1, h⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  refine ⟨e, ?_, fun h' => h1 ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · have := h 1
    have h2 : rootT e 1 = 1 := h'
    rw [h2] at this
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_one, ← this]
    rfl

theorem dvd_of_pow_mul {R : Type} [CommRing R] (x p : R) (h : ∀ a, x ∣ p * a → x ∣ a) (k : ℕ) (a : R)
    (ha : x ∣ p ^ k * a) : x ∣ a := by
  induction k with
  | zero => simpa using ha
  | succ k ih => exact ih (h _ (by rwa [pow_succ', mul_assoc] at ha))

theorem localization_quotient_separated_dvd {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (x p : R) [IsLocalization.Away p S]
    (h : ∀ a, x ∣ p * a → x ∣ a)
    (hc : IsHausdorff (Ideal.span {Ideal.Quotient.mk (Ideal.span {x}) p}) (R ⧸ Ideal.span {x}))
    (q : S) (hq : ∀ r : ℕ, ∃ a : R, algebraMap R S x ∣ q - algebraMap R S (p ^ r * a)) :
    algebraMap R S x ∣ q := by
  have sat : ∀ b : R, algebraMap R S x ∣ algebraMap R S b → x ∣ b := by
    rintro b ⟨c, hc⟩
    obtain ⟨⟨c', ⟨_, m, rfl⟩⟩, hm⟩ := IsLocalization.surj (Submonoid.powers p) c
    have e : algebraMap R S (p ^ m * b) = algebraMap R S (x * c') := by
      rw [map_mul, map_mul, hc, ← hm]; ring
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers p) S).1 e
    refine dvd_of_pow_mul x p h m _ (dvd_of_pow_mul x p h k _ ⟨p ^ k * c', ?_⟩)
    simp only at hk
    rw [hk]; ring
  obtain ⟨a0, h0⟩ := hq 0
  rw [pow_zero, one_mul] at h0
  have h1 : Ideal.Quotient.mk (Ideal.span {x}) a0 = 0 := by
    refine hc.haus _ fun r => ?_
    obtain ⟨a, ha⟩ := hq r
    have h2 : x ∣ a0 - p ^ r * a := sat _ (by
      have := dvd_sub ha h0
      rw [map_sub]
      convert this using 1
      ring)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact h2
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h1
  have := dvd_add h0 (map_dvd (algebraMap R S) h1)
  simpa using this

theorem sep (n : ℕ) (q : Per.AinfP l ⧸ Per.kerP l ^ n)
    (hq : ∀ r : ℕ, ∃ a : Per.Ainf l, q = (l : Per.AinfP l ⧸ Per.kerP l ^ n) ^ r *
      Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a)) : q = 0 := by
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨h1, h2⟩ := GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete l e he n
  have hk : ∀ y : Per.AinfP l, y ∈ Per.kerP l ^ n ↔ algebraMap (Per.Ainf l) (Per.AinfP l) (xi e ^ n) ∣ y := by
    intro y
    rw [GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he, Ideal.span_singleton_pow, Ideal.mem_span_singleton, map_pow]
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Ideal.Quotient.eq_zero_iff_mem, hk]
  refine localization_quotient_separated_dvd (xi e ^ n) (l : Per.Ainf l) h1 ?_ y fun r => ?_
  · rw [map_natCast]
    exact h2.toIsHausdorff
  · obtain ⟨a, ha⟩ := hq r
    refine ⟨a, ?_⟩
    rw [← hk, ← Ideal.Quotient.eq, ha, map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast]

theorem ev_alg (n : ℕ) (y : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) y) = Ideal.Quotient.mk _ y :=
  GlobalTheory.RingIface.ev_alg l n y

theorem ev_aDp (n : ℕ) (a : Per.Ainf l) :
    Per.ev l n (aDp l a) = Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a) :=
  ev_alg n _

theorem ev_ext {x y : Per.BdRp l} (h : ∀ n, Per.ev l n x = Per.ev l n y) : x = y :=
  GlobalTheory.RingIface.ev_ext l x y h

theorem σDp_alg (g : Per.Gq l) (y : Per.AinfP l) :
    Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) y) =
      algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) y) :=
  GlobalTheory.RingIface.sigDp_alg l g y

private theorem ker_evalₐ_fg {A : Type} [CommRing A] (J : Ideal A) (fg : J.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ J n) = (J ^ n).map (algebraMap A (AdicCompletion J A)) := by
  ext a
  rw [RingHom.mem_ker, ← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval fg, LinearMap.mem_ker]
  have hle : (J ^ n • ⊤ : Ideal A) ≤ J ^ n := by intro x hx; simpa using hx
  rw [← AdicCompletion.factor_eval_eq_evalₐ J a hle]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval J A n a)
    rw [← hb] at h ⊢
    have : b ∈ J ^ n := Ideal.Quotient.eq_zero_iff_mem.mp h
    exact (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using this)
  · intro h; rw [h, map_zero]

private theorem mem_map_of_ev (n : ℕ) (w : Per.BdRp l) (h : Per.ev l n w = 0) :
    w ∈ (Per.kerP l ^ n).map (algebraMap (Per.AinfP l) (Per.BdRp l)) := by
  obtain ⟨ε, hε⟩ := exists_isEps l
  have fg : (Per.kerP l).FG := by
    rw [GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l ε hε]
    exact Submodule.fg_span_singleton _
  obtain ⟨e, he, hev⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  have h1 : e w ∈ RingHom.ker (AdicCompletion.evalₐ (Per.kerP l) n) := by
    rw [RingHom.mem_ker, hev, h]
  rw [ker_evalₐ_fg _ fg] at h1
  have h2 : (Per.kerP l ^ n).map (algebraMap (Per.AinfP l) (AdicCompletion (Per.kerP l) (Per.AinfP l))) ≤
      ((Per.kerP l ^ n).map (algebraMap (Per.AinfP l) (Per.BdRp l))).comap e.symm.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, ← he a]
    have := Ideal.mem_map_of_mem (algebraMap (Per.AinfP l) (Per.BdRp l)) ha
    simpa using this
  have h3 := h2 h1
  rw [Ideal.mem_comap] at h3
  simpa using h3

theorem ev_σDp (g : Per.Gq l) (n : ℕ) (w : Per.BdRp l) (y : Per.AinfP l)
    (h : Per.ev l n w = Ideal.Quotient.mk _ y) :
    Per.ev l n (Per.σDp g w) = Ideal.Quotient.mk _ (Per.extP (Per.σA g) y) := by
  have h0 : Per.ev l n (w - algebraMap (Per.AinfP l) (Per.BdRp l) y) = 0 := by
    rw [map_sub, h, ev_alg, sub_self]
  have h1 := mem_map_of_ev n _ h0
  have h2 : (Per.kerP l ^ n).map (algebraMap (Per.AinfP l) (Per.BdRp l)) ≤
      (RingHom.ker (Per.ev l n)).comap (Per.σDp g) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, σDp_alg, ev_alg, Ideal.Quotient.eq_zero_iff_mem]
    exact ((Ideal.pow_right_mono (GlobalTheory.RingBasics.ker_σ g) n).trans (Ideal.le_comap_pow _ n)) ha
  have h3 := h2 h1
  rw [Ideal.mem_comap, RingHom.mem_ker, map_sub, map_sub, σDp_alg, ev_alg, sub_eq_zero] at h3
  exact h3

theorem sigA_alg (g : Per.Gq l) (s : Per.Acris0 l) :
    sigA g (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
      algebraMap (Per.Acris0 l) (Per.Acris l) ⟨Per.extP (Per.σA g) s, (GlobalTheory.CrisMaps.sigA_extends g).mem _ s.2⟩ :=
  (GlobalTheory.CrisMaps.sigA_extends g).env s

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem ev_eq {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (n : ℕ) (x : Per.Acris l) (y : Per.BdRp l)
    (h : ∀ r : ℕ, ∃ (s : Per.Acris0 l) (z : Per.Acris l) (a : Per.Ainf l),
      x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ r * z ∧
      Per.ev l n (y - algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) =
        Per.ev l n ((l : Per.BdRp l) ^ r * aDp l a)) : Per.ev l n (j x) = Per.ev l n y := by
  obtain ⟨N, hN⟩ := hj.bdd n
  have hu : IsUnit ((l : Per.AinfP l ⧸ Per.kerP l ^ n) ^ N) := by
    have := (GlobalTheory.RingBasics.isUnit_l l).map (Ideal.Quotient.mk (Per.kerP l ^ n))
    rw [map_natCast] at this
    exact this.pow N
  rw [← sub_eq_zero, ← hu.mul_right_eq_zero]
  refine sep n _ fun r => ?_
  obtain ⟨s, z, a, hx, hy⟩ := h r
  obtain ⟨b, hb⟩ := hN z
  refine ⟨b - (l : Per.Ainf l) ^ N * a, ?_⟩
  rw [map_sub, map_mul, map_pow, map_natCast, ev_aDp] at hy
  rw [map_mul, map_pow, map_natCast] at hb
  simp only [hx, map_add (f := _), map_sub, map_mul, map_pow, map_natCast, hj.on0]
  linear_combination (l : Per.AinfP l ⧸ Per.kerP l ^ n) ^ r * hb -
    (l : Per.AinfP l ⧸ Per.kerP l ^ n) ^ N * hy

theorem unique {j j' : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (hj' : IsCrisP j') : j' = j := by
  refine RingHom.ext fun x => ev_ext fun n => (ev_eq hj n x _ fun r => ?_).symm
  obtain ⟨N, hN⟩ := hj'.bdd n
  obtain ⟨s, z, hx⟩ := (acris_basic l).2.2.1 x (r + N)
  obtain ⟨a, ha⟩ := hN z
  refine ⟨s, (l : Per.Acris l) ^ N * z, a, by rw [hx, pow_add, mul_assoc], ?_⟩
  rw [map_mul (Per.ev l n), ev_aDp, ← ha, ← map_mul, hx, map_add (f := _), map_mul j', map_pow j', map_natCast, hj'.on0,
    add_sub_cancel_left, pow_add, mul_assoc]

theorem equivariant {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (g : Per.Gq l) (x : Per.Acris l) :
    j (sigA g x) = Per.σDp g (j x) := by
  refine ev_ext fun n => ev_eq hj n _ _ fun r => ?_
  obtain ⟨N, hN⟩ := hj.bdd n
  obtain ⟨s, z, hx⟩ := (acris_basic l).2.2.1 x (r + N)
  obtain ⟨a, ha⟩ := hN z
  refine ⟨⟨Per.extP (Per.σA g) s, (GlobalTheory.CrisMaps.sigA_extends g).mem _ s.2⟩, (l : Per.Acris l) ^ N * sigA g z, Per.σA g a, ?_, ?_⟩
  · rw [hx, map_add (f := _), sigA_alg, map_mul, map_pow, map_natCast, pow_add, mul_assoc]
  · have hb := ev_σDp g n _ _ ha
    rw [GlobalTheory.RingBasics.awayMap_algebraMap₂, map_mul (Per.σDp g), map_pow (Per.σDp g), map_natCast] at hb
    rw [map_mul (Per.ev l n), ev_aDp, ← hb, ← map_mul, hx, map_add j, map_mul j, map_pow j, map_natCast j, hj.on0,
      map_add (Per.σDp g), σDp_alg, add_sub_cancel_left, map_mul (Per.σDp g), map_pow (Per.σDp g),
      map_natCast (Per.σDp g), pow_add, mul_assoc]

end GlobalTheory.MemLoc.CrisUnique

namespace GlobalTheory.MemLoc

theorem crisP_unique_equivariant : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → (∀ j' : Per.Acris l →+* Per.BdRp l, IsCrisP j' → j' = j) ∧ (∀ (g : Per.Gq l) (x : Per.Acris l), j (sigA g x) = Per.σDp g (j x)) ∧ ∀ (n : ℕ) (x : Per.Acris l) (y : Per.BdRp l), (∀ r : ℕ, ∃ (s : Per.Acris0 l) (z : Per.Acris l) (a : Per.Ainf l), x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ r * z ∧ Per.ev l n (y - algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) = Per.ev l n ((l : Per.BdRp l) ^ r * aDp l a)) → Per.ev l n (j x) = Per.ev l n y :=
  fun _ _ _ hj => ⟨fun _ hj' => CrisUnique.unique hj hj', CrisUnique.equivariant hj, CrisUnique.ev_eq hj⟩

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApproxStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → (∀ j' : Per.Acris l →+* Per.BdRp l, IsCrisP j' → j' = j) ∧ (∀ (g : Per.Gq l) (x : Per.Acris l), j (sigA g x) = Per.σDp g (j x)) ∧ ∀ (n : ℕ) (x : Per.Acris l) (y : Per.BdRp l), (∀ r : ℕ, ∃ (s : Per.Acris0 l) (z : Per.Acris l) (a : Per.Ainf l), x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ r * z ∧ Per.ev l n (y - algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) = Per.ev l n ((l : Per.BdRp l) ^ r * aDp l a)) → Per.ev l n (j x) = Per.ev l n y := by
  first | exact @GlobalTheory.MemLoc.crisP_unique_equivariant | exact GlobalTheory.MemLoc.crisP_unique_equivariant | (intros; apply GlobalTheory.MemLoc.crisP_unique_equivariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCanonicalAcrisToBdRPlus
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCanonicalAcrisToBdRPlus
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.CrisMap

theorem smodEq_iff {R : Type} [CommRing R] (a : R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule R R)] ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem complete_of_sandwich (p N : ℕ) {B R : Type} [CommRing B] [CommRing R]
    (hB : IsAdicComplete (Ideal.span {(p : B)}) B) (g : B →+* R) (hg : Function.Injective g)
    (h : ∀ r : R, ∃ b : B, (p : R) ^ N * r = g b) : IsAdicComplete (Ideal.span {(p : R)}) R := by
  have key : ∀ (b : B) (k : ℕ), (p : R) ^ (k + N) ∣ g b → (p : B) ^ k ∣ b := by
    rintro b k ⟨y, hy⟩
    obtain ⟨c, hc⟩ := h y
    refine ⟨c, hg ?_⟩
    rw [hy, map_mul, map_pow, map_natCast, ← hc]
    ring
  refine { haus' := fun x hx => ?_, prec' := fun x hx => ?_ }
  · simp only [smodEq_iff, sub_zero] at hx
    obtain ⟨y, hy⟩ := hx N
    obtain ⟨b, hb⟩ := h y
    have : b = 0 := by
      refine IsHausdorff.haus hB.toIsHausdorff b fun k => ?_
      rw [smodEq_iff, sub_zero]
      exact key b k (by rw [← hb, ← hy]; exact hx _)
    rw [hy, hb, this, map_zero]
  · simp only [smodEq_iff] at hx ⊢
    have h1 : ∀ k, ∃ b : B, x (k + N) - x N = g b := fun k => by
      obtain ⟨y, hy⟩ := hx (Nat.le_add_left N k)
      obtain ⟨b, hb⟩ := h y
      exact ⟨-b, by rw [map_neg, ← hb, ← hy]; ring⟩
    choose b hb using h1
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hB.toIsPrecomplete (f := b) (fun {m n} hmn => by
      rw [smodEq_iff]
      refine key _ _ ?_
      rw [map_sub, ← hb, ← hb, sub_sub_sub_cancel_right]
      exact hx (Nat.add_le_add_right hmn N))
    refine ⟨x N + g L, fun n => ?_⟩
    have h2 := map_dvd g ((smodEq_iff _ _ _ _).1 (hL n))
    rw [map_pow, map_natCast, map_sub, ← hb] at h2
    have h3 := dvd_add (hx (Nat.le_add_right n N)) h2
    convert h3 using 1
    ring

theorem exists_extend (p : ℕ) {D R : Type} [CommRing D] [CommRing R]
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) (f : D →+* R) :
    ∃ F : AdicCompletion (Ideal.span {(p : D)}) D →+* R, ∀ d, F (algebraMap D _ d) = f d := by
  have hf : (Ideal.span {(p : D)}).map f ≤ Ideal.span {(p : R)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  refine ⟨((AdicCompletion.ofAlgEquiv (Ideal.span {(p : R)})).symm : _ →+* R).comp
    (GlobalTheory.AdicMaps.adicMap (Ideal.span {(p : D)}) (Ideal.span {(p : R)}) f
      (Ideal.map_le_iff_le_comap.1 hf)), fun d => ?_⟩
  rw [RingHom.comp_apply, GlobalTheory.AdicMaps.adicMap_alg]
  exact (AdicCompletion.ofAlgEquiv (Ideal.span {(p : R)})).symm_apply_apply (f d)

theorem extend_unique (p : ℕ) {D R : Type} [CommRing D] [CommRing R]
    (hR : IsHausdorff (Ideal.span {(p : R)}) R) (F G : AdicCompletion (Ideal.span {(p : D)}) D →+* R)
    (h : ∀ d, F (algebraMap D _ d) = G (algebraMap D _ d)) : F = G := by
  ext1 x
  rw [← sub_eq_zero]
  refine IsHausdorff.haus hR _ fun k => ?_
  rw [smodEq_iff, sub_zero]
  obtain ⟨s, z, rfl⟩ := GlobalTheory.PrincipalCompletion.dense (p : D) x k
  refine ⟨F z - G z, ?_⟩
  simp only [map_add (f := _), map_mul, map_pow, map_natCast, h]
  ring

theorem exists_lift (p : ℕ) {D P : Type} [CommRing D] [CommRing P] (I : Ideal P) (f : D →+* P)
    (h : ∀ n : ℕ, IsAdicComplete
      (Ideal.span {(p : ((Ideal.Quotient.mk (I ^ n)).comp f).range)})
      ((Ideal.Quotient.mk (I ^ n)).comp f).range) :
    ∃ j : AdicCompletion (Ideal.span {(p : D)}) D →+* AdicCompletion I P,
      (∀ d, j (algebraMap D _ d) = algebraMap P _ (f d)) ∧
      ∀ n x, ∃ d, AdicCompletion.evalₐ I n (j x) = Ideal.Quotient.mk _ (f d) := by
  choose F hF using fun n => exists_extend p (h n) ((Ideal.Quotient.mk (I ^ n)).comp f).rangeRestrict
  have hc : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp
      ((Subring.subtype _).comp (F n)) = (Subring.subtype _).comp (F m) := by
    intro m n hle
    have hm : ∀ x, (Ideal.Quotient.factorPow I hle).comp ((Subring.subtype _).comp (F n)) x ∈
        ((Ideal.Quotient.mk (I ^ m)).comp f).range := fun x => by
      obtain ⟨d, hd⟩ := (F n x).2
      refine ⟨d, ?_⟩
      simp only [RingHom.comp_apply, Subring.subtype_apply, ← hd]
      rfl
    have := extend_unique p (h m).toIsHausdorff (RingHom.codRestrict _ _ hm) (F m) fun d => by
      refine Subtype.ext ?_
      simp only [RingHom.codRestrict_apply, RingHom.comp_apply, hF]
      rfl
    rw [← this]
    rfl
  refine ⟨AdicCompletion.liftRingHom I (fun n => (Subring.subtype _).comp (F n)) hc, fun d => ?_,
    fun n x => ?_⟩
  · refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [AdicCompletion.evalₐ_liftRingHom, RingHom.comp_apply, hF]
    simp [AdicCompletion.algebraMap_apply]
  · obtain ⟨d, hd⟩ := (F n x).2
    exact ⟨d, by rw [AdicCompletion.evalₐ_liftRingHom]; exact hd.symm⟩

variable (l : ℕ) [Fact l.Prime]

theorem exists_isEps : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, h⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  refine ⟨ε, Subtype.ext ?_, fun h2 => h1 ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact this
  · have h3 := h 1
    have h4 : rootT ε 1 = 1 := h2
    rw [h4] at h3
    exact (algebraMap (Om l) ℂ_[l]).injective (by rw [← h3, map_one]; rfl)

theorem bound (n : ℕ) (s : Per.AinfP l) (hs : s ∈ Per.Acris0 l) : ∃ a : Per.Ainf l,
    (l : Per.AinfP l) ^ n * s - algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ n := by
  obtain ⟨e, he⟩ := exists_isEps l
  rw [mem_Acris0_iff_span l e he] at hs
  induction hs using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, hk⟩ := hy
    rcases le_total k n with hkn | hkn
    · obtain ⟨c, hc⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l k
      have hc' : ((k.factorial : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l c) =
          (l : Per.AinfP l) ^ k := by
        have h := congrArg ((algebraMap (Per.Ainf l) (Per.AinfP l)).comp (Per.zA l)) hc
        rwa [map_mul, map_natCast, map_pow, map_natCast, RingHom.comp_apply] at h
      refine ⟨(l : Per.Ainf l) ^ (n - k) * Per.zA l c * xi e ^ k, ?_⟩
      have : (l : Per.AinfP l) ^ n * y = algebraMap (Per.Ainf l) (Per.AinfP l)
          ((l : Per.Ainf l) ^ (n - k) * Per.zA l c * xi e ^ k) := by
        rw [map_mul, map_mul, map_pow, map_pow, map_natCast, ← hk]
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
        rw [Nat.add_sub_cancel_left, pow_add, ← hc']
        ring
      rw [this, sub_self]
      exact zero_mem _
    · refine ⟨0, ?_⟩
      obtain ⟨u, hu⟩ := (GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero).exists_left_inv
      have hy : y = u * algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ k := by
        rw [← hk, ← mul_assoc, hu, one_mul]
      rw [map_zero, sub_zero, hy, GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
        (Ideal.pow_le_pow_right hkn (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k)))
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    convert add_mem ha hb using 1
    rw [map_add (f := _)]
    ring
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨c * a, ?_⟩
    convert Ideal.mul_mem_left _ (algebraMap (Per.Ainf l) (Per.AinfP l) c) ha using 1
    rw [map_mul, Algebra.smul_def]
    ring

theorem algebraMap_mem_kerTheta_pow_iff₂ (e : Per.Fl l) (he : IsEps e) (n : ℕ) (a : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ n ↔ a ∈ Ideal.span {xi e ^ n} := by
  have h1 : Per.kerP l ^ n = (Ideal.span {xi e ^ n}).map (algebraMap (Per.Ainf l) (Per.AinfP l)) := by
    rw [GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow]
  rw [h1]
  refine ⟨fun h => ?_, Ideal.mem_map_of_mem _⟩
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers (l : Per.Ainf l))] at h
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := h
  rw [Ideal.mem_span_singleton] at hk ⊢
  induction k with
  | zero => simpa using hk
  | succ k ih =>
    refine ih ((GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete l e he n).1 _ ?_)
    convert hk using 1
    ring

theorem range_complete (n : ℕ) : IsAdicComplete
    (Ideal.span {(l : ((Ideal.Quotient.mk (Per.kerP l ^ n)).comp (Per.Acris0 l).val.toRingHom).range)})
    ((Ideal.Quotient.mk (Per.kerP l ^ n)).comp (Per.Acris0 l).val.toRingHom).range := by
  obtain ⟨e, he⟩ := exists_isEps l
  let g0 : Per.Ainf l →+* ((Ideal.Quotient.mk (Per.kerP l ^ n)).comp (Per.Acris0 l).val.toRingHom).range :=
    ((Ideal.Quotient.mk (Per.kerP l ^ n)).comp (Per.Acris0 l).val.toRingHom).rangeRestrict.comp
      (algebraMap (Per.Ainf l) (Per.Acris0 l))
  have hg0 : ∀ a, (g0 a).1 = Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a) := fun _ => rfl
  have hk : ∀ a, g0 a = 0 ↔ a ∈ Ideal.span {xi e ^ n} := fun a => by
    rw [← algebraMap_mem_kerTheta_pow_iff₂ l e he, ← Ideal.Quotient.eq_zero_iff_mem, ← hg0]
    exact Subtype.ext_iff
  refine complete_of_sandwich l n (GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete l e he n).2
    (Ideal.Quotient.lift _ g0 fun a ha => (hk a).2 ha) ?_ ?_
  · refine RingHom.lift_injective_of_ker_le_ideal _ _ fun a ha => (hk a).1 ha
  · rintro ⟨_, s, rfl⟩
    obtain ⟨a, ha⟩ := bound l n s s.2
    refine ⟨Ideal.Quotient.mk _ a, Subtype.ext ?_⟩
    rw [Ideal.Quotient.lift_mk, hg0, ← (Ideal.Quotient.eq).2 ha, map_mul, map_pow, map_natCast,
      Subring.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
    rfl

end GlobalTheory.MemLoc.CrisMap

namespace GlobalTheory.MemLoc

theorem exists_isCrisP : ∀ (l : ℕ) [Fact l.Prime], ∃ j : Per.Acris l →+* Per.BdRp l, IsCrisP j := by
  intro l _
  obtain ⟨j, h0, h1⟩ := CrisMap.exists_lift l (Per.kerP l) (Per.Acris0 l).val.toRingHom
    (CrisMap.range_complete l)
  obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  obtain ⟨e', he0, he1⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  refine ⟨e'.symm.toRingHom.comp (j.comp e.toRingHom), fun a => ?_, fun n => ⟨n, fun x => ?_⟩⟩
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [he, h0, RingEquiv.symm_apply_eq, he0]
    rfl
  · obtain ⟨d, hd⟩ := h1 n (e x)
    obtain ⟨a, ha⟩ := CrisMap.bound l n d d.2
    refine ⟨a, ?_⟩
    have h2 : Per.ev l n (e'.symm (j (e x))) = Ideal.Quotient.mk _ (d : Per.AinfP l) := by
      rw [← he1, RingEquiv.apply_symm_apply]
      exact hd
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [map_mul, map_pow, map_natCast, ← (Ideal.Quotient.eq).2 ha, map_mul, map_pow, map_natCast, h2]

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCanonicalAcrisToBdRPlusStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_canonical_acris_to_bdRPlus : ∀ (l : ℕ) [Fact l.Prime], ∃ j : Per.Acris l →+* Per.BdRp l, IsCrisP j := by
  first | exact @GlobalTheory.MemLoc.exists_isCrisP | exact GlobalTheory.MemLoc.exists_isCrisP | (intros; apply GlobalTheory.MemLoc.exists_isCrisP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapAinfInvPrimeBdRPlusInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapAinfInvPrimeBdRPlusInjective
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_isEps_for_inj (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, h⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  refine ⟨ε, ?_, ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro hh
    have := h 1
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    exact congrArg Subtype.val hh

theorem eq_zero_of_mem_span_pow_away {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (r ξ : A)
    [IsLocalization.Away r B] (hs : ∀ n : ℕ, ∀ a : A, ξ ^ n ∣ r * a → ξ ^ n ∣ a)
    (hh : ∀ a : A, (∀ n : ℕ, ξ ^ n ∣ a) → a = 0) (x : B)
    (hx : ∀ n : ℕ, x ∈ Ideal.span {algebraMap A B ξ} ^ n) : x = 0 := by
  have hs' : ∀ n m : ℕ, ∀ a : A, ξ ^ n ∣ r ^ m * a → ξ ^ n ∣ a := by
    intro n m
    induction m with
    | zero => intro a ha; simpa using ha
    | succ m ih =>
      intro a ha
      apply ih
      apply hs
      rwa [← mul_assoc, ← pow_succ']
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers r) x
  have ha : a = 0 := by
    apply hh
    intro n
    have h1 : algebraMap A B a ∈ Ideal.map (algebraMap A B) (Ideal.span {ξ ^ n}) := by
      rw [Ideal.map_span, Set.image_singleton, map_pow, ← Ideal.span_singleton_pow,
        ← IsLocalization.mk'_spec B a s]
      exact Ideal.mul_mem_right _ _ (hx n)
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers r)] at h1
    obtain ⟨_, ⟨m, rfl⟩, hm⟩ := h1
    exact hs' n m a (Ideal.mem_span_singleton.1 hm)
  simp [ha]

theorem algebraMap_AinfP_BdRp_injective (l : ℕ) [Fact l.Prime] :
    Function.Injective (algebraMap (Per.AinfP l) (Per.BdRp l)) := by
  obtain ⟨e, he⟩ := exists_isEps_for_inj l
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  refine eq_zero_of_mem_span_pow_away (l : Per.Ainf l) (xi e)
    (fun n a h => XiHaus.xi_sat he n a h) (GlobalTheory.MemLoc.eq_zero_of_forall_xi_pow_dvd l e he) x fun n => ?_
  rw [← GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he, ← Ideal.Quotient.eq_zero_iff_mem]
  have h1 : Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) x) = Ideal.Quotient.mk _ x :=
    GlobalTheory.RingIface.ev_alg l n x
  rw [← h1, hx, map_zero]

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapAinfInvPrimeBdRPlusInjectiveStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraMap_ainfInvPrime_bdRPlus_injective : ∀ (l : ℕ) [Fact l.Prime], Function.Injective (algebraMap (Per.AinfP l) (Per.BdRp l)) := by
  first | exact @GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective | exact GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective | (intros; apply GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusAcrisDecompositionMuPower
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLimitSeries
namespace GlobalTheory.LimitSeriesPowSmul

theorem mem_pow_smul_top_iff {R : Type} [CommRing R] (p : R) (n : ℕ) (x : R) :
    x ∈ ((Ideal.span {p}) ^ n • (⊤ : Submodule R R)) ↔ p ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem exists_limit_series {R : Type} [CommRing R] (p : R) [IsPrecomplete (Ideal.span {p}) R]
    (f : ℕ → R) : ∃ (L : R), ∀ (k : ℕ), p ^ k ∣ ∑ i ∈ Finset.range k, p ^ i * f i - L := by
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p})
    (fun k => ∑ i ∈ Finset.range k, p ^ i * f i) (by
      intro m n hmn
      rw [SModEq.sub_mem, mem_pow_smul_top_iff, ← Finset.sum_range_add_sum_Ico _ hmn,
        sub_add_cancel_left, dvd_neg]
      refine Finset.dvd_sum fun i hi => ?_
      exact Dvd.dvd.mul_right (pow_dvd_pow p (Finset.mem_Ico.mp hi).1) _)
  exact ⟨L, fun k => (mem_pow_smul_top_iff p k _).mp ((SModEq.sub_mem).mp (hL k))⟩

theorem target : ∀ {R : Type} [inst : CommRing R] (p : R) [IsPrecomplete (Ideal.span {p}) R]
    (f : ℕ → R), ∃ (L : R), ∀ (k : ℕ), p ^ k ∣ ∑ i ∈ Finset.range k, p ^ i * f i - L :=
  by
  intro R _ p _ f
  exact exists_limit_series p f

end GlobalTheory.LimitSeriesPowSmul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusAcrisDecompositionMuPower
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.PhiImage

theorem exists_lim_series {R : Type} [CommRing R] (p : R) [IsPrecomplete (Ideal.span {p}) R] (f : ℕ → R) :
    ∃ L : R, ∀ k, p ^ k ∣ (∑ i ∈ Finset.range k, p ^ i * f i) - L := by
  first
  | exact @_root_.GlobalTheory.LimitSeriesPowSmul.target
  | exact _root_.GlobalTheory.LimitSeriesPowSmul.target
  | (apply _root_.GlobalTheory.LimitSeriesPowSmul.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.LimitSeriesPowSmul.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LimitSeriesPowSmul.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LimitSeriesPowSmul.target ..)

theorem approx {R A : Type} [CommRing R] [CommRing A] (ι : R →+* A) (p : ℕ)
    [IsPrecomplete (Ideal.span {(p : R)}) R] [IsAdicComplete (Ideal.span {(p : A)}) A]
    (φ : A → A) (w : A) (h : ∀ y, ∃ (a : R) (z y' : A), φ y = ι a + w * z + p * φ y') (y : A) :
    ∃ (a : R) (z : A), φ y = ι a + w * z := by
  choose a z nx h using h
  obtain ⟨α, hα⟩ := exists_lim_series (p : R) (fun i => a (nx^[i] y))
  obtain ⟨ζ, hζ⟩ := exists_lim_series (p : A) (fun i => z (nx^[i] y))
  have key : ∀ k, φ y = ι (∑ i ∈ Finset.range k, (p : R) ^ i * a (nx^[i] y)) +
      w * (∑ i ∈ Finset.range k, (p : A) ^ i * z (nx^[i] y)) + (p : A) ^ k * φ (nx^[k] y) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Function.iterate_succ_apply', map_add (f := _), map_mul,
        map_pow, map_natCast]
      linear_combination ih + (p : A) ^ k * h (nx^[k] y)
  refine ⟨α, ζ, sub_eq_zero.1 (IsHausdorff.haus (I := Ideal.span {(p : A)}) inferInstance _ fun k => ?_)⟩
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨u, hu⟩ := hα k
  obtain ⟨v, hv⟩ := hζ k
  have hu' := congrArg ι hu
  rw [map_sub, map_mul, map_pow, map_natCast] at hu'
  exact ⟨ι u + w * v + φ (nx^[k] y), by linear_combination key k + hu' + w * hv⟩

theorem geom_sum_one_add {R : Type} [CommRing R] {p : ℕ} (hp : p.Prime) (x : R) :
    ∃ c : R, ∑ i ∈ Finset.range p, (x + 1) ^ i = p * c + x ^ (p - 1) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (Polynomial.X : Polynomial ℤ) 1
  have h1 := geom_sum_mul (Polynomial.X + 1 : Polynomial ℤ) p
  have h2 : (Polynomial.X : Polynomial ℤ) ^ p = Polynomial.X ^ (p - 1) * Polynomial.X := by
    rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
  have h3 : ∑ i ∈ Finset.range p, (Polynomial.X + 1 : Polynomial ℤ) ^ i = (p : Polynomial ℤ) * r + Polynomial.X ^ (p - 1) := by
    refine mul_right_cancel₀ Polynomial.X_ne_zero ?_
    rw [one_pow] at hr
    linear_combination h1 + hr + h2
  refine ⟨Polynomial.aeval x r, ?_⟩
  simpa using congrArg (Polynomial.aeval x) h3

variable {l : ℕ} [Fact l.Prime]

theorem phi_xi (e : Per.Fl l) : ∃ c : Per.Ainf l, Per.φA l (xi e) = l * c + mu e ^ (l - 1) := by
  obtain ⟨c, hc⟩ := geom_sum_one_add (Fact.out : l.Prime) (mu e)
  refine ⟨c, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hc, xi, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, mu, sub_add_cancel]
  congr 1
  refine (GlobalTheory.RingIface.phiA_teich l _).trans ?_
  rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]

theorem nat_cancel {A : Type} [CommRing A] (f : ℤ_[l] →+* A) (ht : ∀ x : A, (l : A) * x = 0 → x = 0)
    (m : ℕ) (hm : m ≠ 0) (x y : A) (h : (m : A) * x = m * y) : x = y := by
  have h0 : ((m : ℕ) : ℤ_[l]) ≠ 0 := by exact_mod_cast hm
  have h1 := congrArg f (PadicInt.unitCoeff_spec h0)
  rw [map_natCast, map_mul, map_pow, map_natCast] at h1
  have hp : ∀ (k : ℕ) (x : A), (l : A) ^ k * x = 0 → x = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => exact fun x hx => ht x (ih _ (by linear_combination hx))
  refine sub_eq_zero.1 (hp ((m : ℕ) : ℤ_[l]).valuation _ ?_)
  refine ((PadicInt.unitCoeff h0).isUnit.map f).mul_left_cancel ?_
  rw [mul_zero, ← mul_assoc, ← h1]
  linear_combination h

theorem alg_tower (a : Per.Ainf l) :
    algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) =
      algebraMap (Per.Ainf l) (Per.Acris l) a := (GlobalTheory.RingIface.tower l a).symm

theorem phiA_alg (a : Per.Ainf l) :
    phiA l (algebraMap (Per.Ainf l) (Per.Acris l) a) = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l a) :=
  (GlobalTheory.CrisMaps.phiA_extends l).alg a

theorem on_span {R P A : Type} [CommRing R] [CommRing P] [Algebra R P] [CommRing A] (B : Subalgebra R P)
    (j : B →+* A) (zR : ℤ_[l] →+* R) (ht : ∀ x : A, (l : A) * x = 0 → x = 0)
    (φ : A →+* A) (φR : R → R) (hφ : ∀ a, φ (j (algebraMap R B a)) = j (algebraMap R B (φR a)))
    (ξ c : R) (w : A) (hξ : j (algebraMap R B (φR ξ)) = l * (j (algebraMap R B c) + w))
    (hB : ∀ s : P, s ∈ B ↔ s ∈ Submodule.span R {y : P | ∃ n : ℕ,
      ((n.factorial : ℕ) : P) * y = algebraMap R P ξ ^ n}) (s : B) :
    ∃ (a : R) (z : A), φ (j s) = j (algebraMap R B a) + w * z := by
  obtain ⟨s, hs⟩ := s
  have hs' := (hB s).1 hs
  induction hs' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, hn⟩ := hy
    have h1 : ((n.factorial : ℕ) : B) * ⟨y, hs⟩ = algebraMap R B ξ ^ n := Subtype.ext (by simpa using hn)
    have h2 := congrArg (fun t => φ (j t)) h1
    simp only [map_mul, map_natCast, map_pow, hφ, hξ] at h2
    obtain ⟨d, hd⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l n
    have h3 := congrArg ((j.comp (algebraMap R B)).comp zR) hd
    rw [map_mul, map_natCast, map_pow, map_natCast] at h3
    have h4 : φ (j ⟨y, hs⟩) = j (algebraMap R B (zR d)) * (j (algebraMap R B c) + w) ^ n := by
      refine nat_cancel ((j.comp (algebraMap R B)).comp zR) ht _ n.factorial_ne_zero _ _ ?_
      rw [h2, mul_pow, ← h3, mul_assoc]
      rfl
    obtain ⟨u, hu⟩ := sub_dvd_pow_sub_pow (j (algebraMap R B c) + w) (j (algebraMap R B c)) n
    refine ⟨zR d * c ^ n, j (algebraMap R B (zR d)) * u, ?_⟩
    rw [h4, map_mul, map_mul, map_pow, map_pow]
    linear_combination j (algebraMap R B (zR d)) * hu
  | zero => exact ⟨0, 0, by
      have : (⟨0, hs⟩ : B) = 0 := rfl
      simp [this]⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a, z, h⟩ := ihx ((hB x).2 hx)
    obtain ⟨a', z', h'⟩ := ihy ((hB y).2 hy)
    have : (⟨x + y, hs⟩ : B) = ⟨x, (hB x).2 hx⟩ + ⟨y, (hB y).2 hy⟩ := rfl
    refine ⟨a + a', z + z', ?_⟩
    rw [this, map_add (f := _), map_add (f := _), h, h', map_add (f := _), map_add (f := _)]
    ring
  | smul r x hx ihx =>
    obtain ⟨a, z, h⟩ := ihx ((hB x).2 hx)
    have : (⟨r • x, hs⟩ : B) = algebraMap R B r * ⟨x, (hB x).2 hx⟩ := Subtype.ext (Algebra.smul_def r x)
    refine ⟨φR r * a, j (algebraMap R B (φR r)) * z, ?_⟩
    rw [this, map_mul, map_mul, h, hφ, map_mul, map_mul]
    ring

end GlobalTheory.MemLoc.PhiImage

namespace GlobalTheory.MemLoc
open PhiImage

theorem phiA_mem_ainf_add : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ w : Per.Acris l, (l : Per.Acris l) * w = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ^ (l - 1) → ∀ y : Per.Acris l, ∃ (a : Per.Ainf l) (z : Per.Acris l), phiA l y = algebraMap (Per.Ainf l) (Per.Acris l) a + w * z := by
  intro l _ e he w hw
  obtain ⟨hc, ht, hd, -⟩ := acris_basic l
  obtain ⟨c, hc'⟩ := phi_xi e
  haveI : IsAdicComplete (Ideal.span {(l : Per.Ainf l)}) (Per.Ainf l) := WittVector.isAdicCompleteIdealSpanP
  refine approx (algebraMap (Per.Ainf l) (Per.Acris l)) l (phiA l) w fun y => ?_
  obtain ⟨s, y', hy⟩ := hd y 1
  obtain ⟨a, z, h⟩ := on_span (l := l) (Per.Acris0 l) (algebraMap (Per.Acris0 l) (Per.Acris l)) (Per.zA l) ht
    (phiA l) (Per.φA l) (fun a => by rw [alg_tower, alg_tower, phiA_alg]) (xi e) c w
    (by rw [alg_tower, alg_tower, hc', map_add (f := _), map_mul, map_natCast, map_pow, mul_add, hw])
    (mem_Acris0_iff_span l e he) s
  refine ⟨a, z, y', ?_⟩
  rw [hy, map_add (f := _), h, alg_tower, pow_one, map_mul, map_natCast]

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusAcrisDecompositionMuPowerStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_acris_decomposition_mu_power : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ w : Per.Acris l, (l : Per.Acris l) * w = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ^ (l - 1) → ∀ y : Per.Acris l, ∃ (a : Per.Ainf l) (z : Per.Acris l), phiA l y = algebraMap (Per.Ainf l) (Per.Acris l) a + w * z := by
  first | exact @GlobalTheory.MemLoc.phiA_mem_ainf_add | exact GlobalTheory.MemLoc.phiA_mem_ainf_add | (intros; apply GlobalTheory.MemLoc.phiA_mem_ainf_add <;> assumption)
end
end
