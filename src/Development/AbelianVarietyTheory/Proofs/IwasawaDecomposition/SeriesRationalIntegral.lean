module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SerIntAtOfSeriesRat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicCompletionIntegersLeIntAE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsTowerCover

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormsDetTwistMulRational
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalApprox
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldElementRelativeApproxCompletions
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldElementRelativeApproxCompletions
open NumberField IsDedekindDomain

namespace GlobalTheory.WeakApprox

variable {L : Type} [Field L] [NumberField L]

theorem exists_int_approx (S : Finset (HeightOneSpectrum (𝓞 L))) (t : HeightOneSpectrum (𝓞 L) → 𝓞 L)
    (ht : ∀ v ∈ S, t v ≠ 0) : ∃ y : 𝓞 L, ∀ v ∈ S,
      v.valuation L ((y : L) - (t v : L)) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (t v : L) := by
  classical
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    (fun v : HeightOneSpectrum (𝓞 L) => v.asIdeal)
    (fun v => multiplicity v.asIdeal (Ideal.span {t v}) + 1)
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => t v)
  refine ⟨y, fun v hv => ?_⟩
  have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hy v hv)
  have h2 := v.intValuation_eq_exp_neg_multiplicity (ht v hv)
  have e1 : ((y : L) - (t v : L)) = algebraMap (𝓞 L) L (y - t v) := by simp
  have e2 : ((t v : L)) = algebraMap (𝓞 L) L (t v) := rfl
  rw [e1, e2, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    h2, ← WithZero.exp_add]
  refine h1.trans (le_of_eq ?_)
  congr 1
  push_cast
  ring

private lemma valued_algebraMap_adicCompletion_eq_valuation (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (a : K) :
    Valued.v (algebraMap K (P.adicCompletion K) a) = P.valuation K a := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  simp

private lemma exp_neg_one_mul_lt_of_ne_zero {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) : WithZero.exp (-1 : ℤ) * x < x := by
  have h : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  simpa using mul_lt_mul_of_pos_right h (zero_lt_iff.2 hx)

theorem exists_units_approx :
    ∀ (L : Type) [Field L] [NumberField L] (R : Finset (HeightOneSpectrum (𝓞 L)))
      (z : ∀ P : HeightOneSpectrum (𝓞 L), P.adicCompletion L), (∀ P ∈ R, z P ≠ 0) →
      ∃ k : Lˣ, ∀ P ∈ R, Valued.v (z P - algebraMap L (P.adicCompletion L) (k : L)) ≤
        WithZero.exp (-1 : ℤ) * Valued.v (z P) := by
  intro L _ _ R z hz
  classical

  have happ : ∀ P, ∃ a : L, P ∈ R →
      Valued.v (z P - algebraMap L (P.adicCompletion L) a) < WithZero.exp (-1 : ℤ) * Valued.v (z P) := by
    intro P
    by_cases hP : P ∈ R
    · obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer L
      have hπ0 : π ≠ 0 := by
        intro h
        rw [h, map_zero] at hπ
        exact WithZero.exp_ne_zero hπ.symm
      have hc : algebraMap L (P.adicCompletion L) π * z P ≠ 0 :=
        mul_ne_zero ((map_ne_zero _).2 hπ0) (hz P hP)
      obtain ⟨a, ha⟩ := GlobalTheory.adicCompletion_exists_approx_lt L P (z P) _ hc
      refine ⟨a, fun _ => ?_⟩
      rwa [map_mul, valued_algebraMap_adicCompletion_eq_valuation, hπ] at ha
    · exact ⟨0, fun h => absurd h hP⟩
  choose a ha using happ

  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 L)) R a
  have hint : ∀ P, ∃ r : 𝓞 L, P ∈ R → algebraMap (𝓞 L) L r = (d : 𝓞 L) • a P := by
    intro P
    by_cases hP : P ∈ R
    · obtain ⟨r, hr⟩ := hd P hP
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose t ht using hint
  set D : L := algebraMap (𝓞 L) L d with hDdef
  have hD : D ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 L) L) (IsFractionRing.injective (𝓞 L) L)).2
      (nonZeroDivisors.coe_ne_zero d)
  have htP : ∀ P ∈ R, algebraMap (𝓞 L) L (t P) = D * a P := fun P hP => by
    rw [ht P hP, Algebra.smul_def]
  have ha0 : ∀ P ∈ R, a P ≠ 0 := by
    intro P hP h
    have h' := ha P hP
    rw [h, map_zero, sub_zero] at h'
    exact lt_irrefl _ (h'.trans (exp_neg_one_mul_lt_of_ne_zero ((Valuation.ne_zero_iff _).2 (hz P hP))))
  have ht0 : ∀ P ∈ R, t P ≠ 0 := by
    intro P hP h
    have h' := htP P hP
    rw [h, map_zero] at h'
    exact mul_ne_zero hD (ha0 P hP) h'.symm

  obtain ⟨y, hy⟩ := exists_int_approx (L := L) R t ht0
  have hy' : ∀ P ∈ R, P.valuation L (algebraMap (𝓞 L) L y - algebraMap (𝓞 L) L (t P)) ≤
      WithZero.exp (-1 : ℤ) * P.valuation L (algebraMap (𝓞 L) L (t P)) := hy
  rcases R.eq_empty_or_nonempty with hR | ⟨P0, hP0⟩
  · exact ⟨1, by simp [hR]⟩
  have hy0 : algebraMap (𝓞 L) L y ≠ 0 := by
    intro h
    have h' := hy' P0 hP0
    rw [h, zero_sub, Valuation.map_neg] at h'
    have hv : P0.valuation L (algebraMap (𝓞 L) L (t P0)) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 (ht0 P0 hP0))
    exact lt_irrefl _ (h'.trans_lt (exp_neg_one_mul_lt_of_ne_zero hv))
  refine ⟨Units.mk0 (algebraMap (𝓞 L) L y / D) (div_ne_zero hy0 hD), fun P hP => ?_⟩
  simp only [Units.val_mk0]
  have hA := ha P hP
  have hza : Valued.v (algebraMap L (P.adicCompletion L) (a P)) = Valued.v (z P) := by
    apply Valuation.map_eq_of_sub_lt
    rw [Valuation.map_sub_swap]
    exact hA.trans (exp_neg_one_mul_lt_of_ne_zero ((Valuation.ne_zero_iff _).2 (hz P hP)))
  have hsplit : z P - algebraMap L (P.adicCompletion L) (algebraMap (𝓞 L) L y / D) =
      (z P - algebraMap L _ (a P)) + algebraMap L _ (a P - algebraMap (𝓞 L) L y / D) := by
    rw [map_sub]; ring
  rw [hsplit]
  refine Valuation.map_add_le _ hA.le ?_
  rw [valued_algebraMap_adicCompletion_eq_valuation, ← hza, valued_algebraMap_adicCompletion_eq_valuation]
  have e : a P - algebraMap (𝓞 L) L y / D =
      (algebraMap (𝓞 L) L (t P) - algebraMap (𝓞 L) L y) / D := by
    rw [htP P hP]; field_simp
  have hDv : P.valuation L D ≠ 0 := (Valuation.ne_zero_iff _).2 hD
  rw [e, map_div₀, Valuation.map_sub_swap, div_le_iff₀ (zero_lt_iff.2 hDv)]
  calc _ ≤ WithZero.exp (-1 : ℤ) * P.valuation L (algebraMap (𝓞 L) L (t P)) := hy' P hP
    _ = _ := by rw [htP P hP, map_mul]; ac_rfl

end GlobalTheory.WeakApprox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldElementRelativeApproxCompletionsStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_element_relative_approx_completions : ∀ (L : Type) [Field L] [NumberField L] (R : Finset (HeightOneSpectrum (𝓞 L))) (z : ∀ P : HeightOneSpectrum (𝓞 L), P.adicCompletion L), (∀ P ∈ R, z P ≠ 0) → ∃ k : Lˣ, ∀ P ∈ R, Valued.v (z P - algebraMap L (P.adicCompletion L) (k : L)) ≤ WithZero.exp (-1 : ℤ) * Valued.v (z P) := by
  first | exact @GlobalTheory.WeakApprox.exists_units_approx | exact GlobalTheory.WeakApprox.exists_units_approx | (intros; apply GlobalTheory.WeakApprox.exists_units_approx <;> assumption)
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistValues
variable {D : D7}

theorem pow_eq_one (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle) (hc : ChrEq δc δ) (n : ℕ)
    (hn : δ.OrderDvd n) (x : (AE D)ˣ) : δc x ^ n = 1 := by
  have hH : IsHeckeChar D (δc ^ n) := by
    refine ⟨?_, fun k => ?_⟩
    · exact (continuous_pow n).comp hc.1.1
    · rw [MonoidHom.pow_apply, hc.1.2 k, one_pow]
  have := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (δc ^ n) hH (fun y hy => by
    rw [MonoidHom.pow_apply]
    exact GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D δc δ hc n hn y hy) x
  rwa [MonoidHom.pow_apply] at this

theorem exists_pow_of_snd {R A B I : Type} [CommRing R] [CommRing A] [CommRing B] (e : R ≃+* A × B)
    (s : A ≃+* (I → ℂ)) (n : ℕ) (hn : 0 < n) (x : Rˣ) (hx : (e x).2 = 1) : ∃ V : Rˣ, x = V ^ n := by
  have hz : ∀ τ, s (e x).1 τ ≠ 0 := by
    intro τ h0
    have h1 : s (e x).1 * s (e ((x⁻¹ : Rˣ) : R)).1 = 1 := by
      rw [← map_mul, ← Prod.fst_mul, ← map_mul, Units.mul_inv, map_one, Prod.fst_one, map_one]
    have := congrFun h1 τ
    rw [Pi.mul_apply, h0, zero_mul, Pi.one_apply] at this
    exact zero_ne_one this
  choose w hw using fun τ => IsAlgClosed.exists_pow_nat_eq (s (e x).1 τ) hn
  have hw0 : ∀ τ, w τ ≠ 0 := fun τ h0 => hz τ (by rw [← hw τ, h0, zero_pow hn.ne'])
  let wi : I → ℂ := fun τ => (w τ)⁻¹
  have hwi : w * wi = 1 := funext fun τ => mul_inv_cancel₀ (hw0 τ)
  have hiw : wi * w = 1 := funext fun τ => inv_mul_cancel₀ (hw0 τ)
  let U : (A × B)ˣ := ⟨(s.symm w, 1), (s.symm wi, 1), by
      rw [Prod.mk_mul_mk, ← map_mul, hwi, map_one, mul_one]; rfl, by
      rw [Prod.mk_mul_mk, ← map_mul, hiw, map_one, mul_one]; rfl⟩
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom U, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.coe_map]
  change (x : R) = (e.symm (s.symm w, 1)) ^ n
  rw [← map_pow, Prod.pow_mk, one_pow, ← map_pow,
    show w ^ n = s (e x).1 from funext fun τ => by rw [Pi.pow_apply, hw τ], RingEquiv.symm_apply_apply, ← hx,
    Prod.mk.eta, RingEquiv.symm_apply_apply]

theorem eq_one_of_finPart (c : (AE D)ˣ →* Circle) (n : ℕ) (hn : 0 < n) (hpow : ∀ x, c x ^ n = 1) (x : (AE D)ˣ)
    (hx : finPart D (x : AE D) = 1) : c x = 1 := by
  obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  obtain ⟨V, hV⟩ := exists_pow_of_snd e (Formalism.IndefR.Eqv.splitEquiv D) n hn x ((he _).2.trans hx)
  rw [hV, map_pow, hpow]

theorem exists_global_approx : ∀ (L : Type) [Field L] [NumberField L] (R : Finset (HeightOneSpectrum (𝓞 L))) (z : ∀ P : HeightOneSpectrum (𝓞 L), P.adicCompletion L), (∀ P ∈ R, z P ≠ 0) → ∃ k : Lˣ, ∀ P ∈ R, Valued.v (z P - algebraMap L (P.adicCompletion L) (k : L)) ≤ WithZero.exp (-1 : ℤ) * Valued.v (z P) :=
  GlobalTheory.T.exists_field_element_relative_approx_completions


set_option maxHeartbeats 1000000 in
open _root_.Formalism.L2.Host in
theorem mem_of_infPart {k : Type} [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle)
    (hc : ChrEq δc δ) (n : ℕ) (hn : 0 < n) (hord : δ.OrderDvd n) (htame : ∀ v, δ.TameAt v) (hval : δ.ValuesIn 0 σ)
    (x : (AE D)ˣ) (hx : infPart D (x : AE D) = 1) : ((δc x : Circle) : ℂ) ∈ σ.fieldRange := by
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h4 δc δ hc
  have hev := GlobalTheory.HeckeSplit.eventually_unrAt δ.1 δ.2.1
  set Rm := (Filter.eventually_cofinite.1 hev).toFinset with hRmdef
  have hRm : ∀ P, P ∉ Rm → δ.UnrAt P := fun P hP => by
    by_contra h
    exact hP ((Set.Finite.mem_toFinset _).2 h)
  let zz : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ := Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x
  have hz0 : ∀ P, (zz : FiniteAdeleRing (𝓞 D.host.E) D.host.E) P ≠ 0 := (FiniteAdeleRing.isUnit_iff.1 zz.isUnit).1
  obtain ⟨k, hk⟩ := exists_global_approx D.host.E Rm (fun P => (zz : FiniteAdeleRing (𝓞 D.host.E) D.host.E) P)
    (fun P _ => hz0 P)
  let K : (AE D)ˣ := Units.map (incA D).toMonoidHom k
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  have e1 : δc x = δc (b (x * K⁻¹)) := by
    have : δc (x * K⁻¹) = δc x := by rw [map_mul, map_inv, hc.1.2 k, inv_one, mul_one]
    rw [← this]
    conv_lhs => rw [hab (x * K⁻¹)]
    rw [map_mul, eq_one_of_finPart δc n hn (pow_eq_one δ δc hc n hord) _ (ha _).2, one_mul]
  set y := b (x * K⁻¹) with hydef
  have hy : infPart D (y : AE D) = 1 := (hb _).1
  have hyP : ∀ P, ι (finPart D (y : AE D)) P =
      (zz : FiniteAdeleRing (𝓞 D.host.E) D.host.E) P * algebraMap D.host.E _ ((k⁻¹ : D.host.Eˣ) : D.host.E) := by
    intro P
    rw [(hb _).2, Units.val_mul, map_mul, map_mul]
    have : ((K⁻¹ : (AE D)ˣ) : AE D) = incA D ((k⁻¹ : D.host.Eˣ) : D.host.E) := rfl
    rw [this]
    show _ * ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((k⁻¹ : D.host.Eˣ) : D.host.E)) P = _
    rw [h1]
    rfl

  let yy : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ := Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom y
  have hy0 : ∀ P, ι (finPart D (y : AE D)) P ≠ 0 := (FiniteAdeleRing.isUnit_iff.1 yy.isUnit).1
  obtain ⟨S0, -, -, hS0⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN yy
  choose kk hkk using fun P => GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P _ (hy0 P)
  have key := hprod y hy (S0 ∪ Rm) kk (fun P _ => ⟨(hkk P).1, (hkk P).2.1⟩)
    (fun P hP => hS0 P fun h => hP (Finset.mem_union_left _ h))
  rw [e1, key]
  refine prod_mem fun P _ => ?_
  have hva : ∀ t : D.host.E, Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) t) = P.valuation D.host.E t :=
    fun t => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P t
  by_cases hR : P ∈ Rm
  ·
    set zP := (zz : FiniteAdeleRing (𝓞 D.host.E) D.host.E) P with hzP
    have hk0 : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) ≠ 0 := by
      rw [hva]; exact (Valuation.ne_zero_iff _).2 k.ne_zero
    have hlt : WithZero.exp (-1 : ℤ) < 1 := by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    have hzv : Valued.v zP = Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) := by
      refine (Valuation.map_eq_of_sub_lt _ ?_).symm
      rw [Valuation.map_sub_swap]
      exact (hk P hR).trans_lt (mul_lt_of_lt_one_left (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (hz0 P))) hlt)
    have hkinv : algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E) *
        algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hkv' : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E)) *
        Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) = 1 := by
      rw [← map_mul, hkinv, map_one]
    have hyv : Valued.v (ι (finPart D (y : AE D)) P) = 1 := by
      rw [hyP, map_mul, mul_comm, hzv]; exact hkv'
    have hy1 : Valued.v (ι (finPart D (y : AE D)) P - 1) ≤ WithZero.exp (-1 : ℤ) := by
      have : ι (finPart D (y : AE D)) P - 1 = (zP - algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) *
          algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E) := by
        rw [hyP, sub_mul, mul_comm (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)), hkinv]
      rw [this, map_mul]
      calc Valued.v (zP - _) * Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E))
          ≤ WithZero.exp (-1 : ℤ) * Valued.v zP *
            Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E)) :=
            mul_le_mul' (hk P hR) le_rfl
        _ = WithZero.exp (-1 : ℤ) := by rw [mul_assoc, hzv, mul_comm (Valued.v (algebraMap _ _ (k : D.host.E))), hkv', mul_one]
    obtain ⟨q1, q2, q3⟩ := hkk P
    have hq : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (kk P : D.host.E)) = 1 := by
      rw [hva, ← q1, hyv]
    have hq1 : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (kk P : D.host.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
      have e2 : algebraMap D.host.E (P.adicCompletion D.host.E) (kk P : D.host.E) - 1 =
          (ι (finPart D (y : AE D)) P - 1) - (ι (finPart D (y : AE D)) P - algebraMap D.host.E _ (kk P : D.host.E)) := by ring
      rw [e2]
      refine (Valuation.map_sub _ _ _).trans (max_le hy1 ?_)
      rw [← hva, hq, mul_one] at q3
      simpa using q3
    have ht := htame P (Formalism.L2.Host.atFin P (kk P)) hq hq1
    have : δ.locK P (kk P) = 1 := ht
    rw [this, Units.val_one]
    exact one_mem _
  ·
    have hu := hRm P hR
    have hkv0 : P.valuation D.host.E (kk P : D.host.E) ≠ 0 := (Valuation.ne_zero_iff _).2 (kk P).ne_zero
    have hm : P.valuation D.host.E (kk P : D.host.E) = WithZero.exp (-(-WithZero.log (P.valuation D.host.E (kk P : D.host.E)))) := by
      rw [neg_neg, WithZero.exp_log hkv0]
    rw [GlobalTheory.CharUnramVal.locK_eq_val_zpow δ P hu (kk P) _ hm, Units.val_zpow_eq_zpow_val]
    refine zpow_mem ?_ _
    obtain ⟨t, ht⟩ := hval P hu
    refine ⟨t, ht.trans ?_⟩
    simp [Formalism.L2.Host.HChar.valTw]

theorem mem_fieldRange : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ g, dd g ∈ σ.fieldRange := by
  intro D V pd k _ σ δ δc hT dd hdd g
  obtain ⟨hc, ⟨n, hn, hord⟩, -, htame, -, hval⟩ := hT
  have key : ∀ x : (AE D)ˣ, ((δc x : Circle) : ℂ) ∈ σ.fieldRange := by
    intro x
    obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
    rw [hab x, map_mul, eq_one_of_finPart δc n hn (pow_eq_one δ δc hc n hord) _ (ha x).2, one_mul]
    exact mem_of_infPart σ δ δc hc n hn hord htame hval _ (hb x).1
  rcases hdd with ⟨hex, hv⟩ | ⟨hex, hv⟩
  · obtain ⟨x, hx⟩ := hex g
    rw [hv g x hx]
    exact key x
  · obtain ⟨x, hx⟩ := hex g
    rw [hv g x hx, MonoidHom.inv_apply, Circle.coe_inv]
    exact inv_mem (key x)

end GlobalTheory.TwistValues
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrincipalRoot
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistLeft

theorem exists_principal_root {D : D7} (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) :
    ∃ e : D.host.Eˣ, IsDetRoot V γ (Units.map (incA D).toMonoidHom e) := by
  obtain ⟨γ₀, -, h0⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  have hdet : ((matHom V γ).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det =
      incA D γ₀.1.det := by
    rw [← GlobalTheory.DetRootRows.det_bc, h0]; rfl
  generalize γ₀.1.det = d at hdet
  have hc : ∀ e : D.host.E, cA D (incA D e) = incA D (star e) := fun e => rfl
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  have hn : star d * d = 1 := by
    have := det_conj_mul V γ
    apply GlobalTheory.DetRootRows.inclR_injective (F := D.host.F) (AF D.host.F)
    rw [map_mul, map_one, ← hc, ← hdet]
    exact this
  obtain ⟨e, he0, he⟩ : ∃ e : D.host.E, e ≠ 0 ∧ e = d * star e := by
    by_cases hd : d = -1
    · obtain ⟨a, ha⟩ := GlobalTheory.RecDict.cmData_sig_ne_id D.sp.cm
      refine ⟨a - star a, sub_ne_zero.2 (Ne.symm ha), ?_⟩
      rw [hd, star_sub, star_star]; ring
    · refine ⟨1 + d, fun h => hd (by linear_combination h), ?_⟩
      rw [star_add, star_one]; linear_combination -hn
  refine ⟨Units.mk0 e he0, ?_⟩
  unfold IsDetRoot
  rw [hdet]
  show incA D e = incA D d * cA D (incA D e)
  rw [hc, ← map_mul, ← he]

theorem muVal_left {D : D7} (V : HSp D) (χ : (AE D)ˣ →* Circle)
    (hE : ∀ x : D.host.Eˣ, χ (Units.map (incA D).toMonoidHom x) = 1) (mu : GA D V → ℂ) (hmu : MuVal V χ mu)
    (γ : GA D V) (hγ : γ ∈ GQ V) (h : GA D V) : mu (γ * h) = mu h := by
  obtain ⟨x, hx⟩ := hmu.1 h
  obtain ⟨e, he⟩ := exists_principal_root V γ hγ
  rw [hmu.2 _ _ (detRootMul_holds V γ h _ x he hx), hmu.2 h x hx, map_mul, hE e, one_mul]

theorem twist_left : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E)
    (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) →
    ∀ γ ∈ GQ V, ∀ h : GA D V, dd (γ * h) = dd h := by
  intro D V pd k _ σ δ δc ht dd hdd γ hγ h
  have hE : ∀ x : D.host.Eˣ, δc (Units.map (incA D).toMonoidHom x) = 1 := ht.1.1.2
  rcases hdd with hm | hm
  · exact muVal_left V δc hE dd hm γ hγ h
  · exact muVal_left V δc⁻¹ (fun x => by rw [MonoidHom.inv_apply, hE x, inv_one]) dd hm γ hγ h

end GlobalTheory.TwistLeft
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormsDetTwistMulRational
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistRat

theorem curveOver_of_rayIn : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ (N : ℕ), 3 ≤ N → ∀ (Fc : IntermediateField ℚ ℂ) (σ : Fc →+* ℂ), RayIn D N σ.fieldRange → GlobalTheory.CompRat.CurveOver Q.H Fc N := GlobalTheory.TwistRat.Field.curveOver_of_rayIn

theorem twist_mem_fieldRange : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ g, dd g ∈ σ.fieldRange := GlobalTheory.TwistValues.mem_fieldRange

theorem twist_eq_of_finHom : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ h h' : GA D V, finHom V h = finHom V h' → dd h = dd h' := GlobalTheory.TwistFinPart.twist_eq_of_finHom

theorem twist_mul_left : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ γ ∈ GQ V, ∀ h : GA D V, dd (γ * h) = dd h := GlobalTheory.TwistLeft.twist_left

theorem twist_mul_right : ∀ (D : D7) (V : HSp D) (M pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsAuxiliarySplitSquarefreeLevel D M pd → IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ u : GA D V, Formalism.L2.Pj.gLat V u = ↑(Formalism.L2.Pj.latHat V) → GlobalTheory.Member.FinCong V (M * pd) u → ∀ h : GA D V, dd (h * u) = dd h := GlobalTheory.TwistRat.Right.dd_mul_right

theorem muVal_cast {D : D7} {V W : HSp D} (h : V = W) (χ : (AE D)ˣ →* Circle) (dd : GA D W → ℂ) (hd : MuVal W χ dd) :
    MuVal V χ (castDict h.symm dd) := by
  subst h; exact hd

theorem castDict_mul {D : D7} {V W : HSp D} (h : V = W) (dd : GA D W → ℂ) (φ : GA D V → ℂ) :
    castDict h (fun g => castDict h.symm dd g * φ g) = fun g => dd g * castDict h φ g := by
  subst h; rfl

theorem isRat_twist : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
      ∀ (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist C.d.pd C.σ₂ δ δc →
      ∀ dd : GA D (Wc D i) → ℂ, MuVal (Wc D i) δc dd ∨ MuVal (Wc D i) δc⁻¹ dd →
      ∀ φ : GA D (Wc D i) → ℂ, IsRat T i hV C (κ i) φ → IsRat T i hV C (κ i) (fun g => dd g * φ g) := by
  intro hRF D G _ _ Pl0 T0 A T _ R F κ v₀ hL hLev hGrp hFam hMod hThP hTie i hV hFP gramR c0R c0L hFT u hu C hGC δ δc hTw dd hdd φ hφ
  obtain ⟨hU, -, hAux, -, hRay⟩ := hGC
  obtain ⟨φ', hφ', rfl⟩ := hφ
  have hlev : C.d.l₂.M = T.Q.l.M * C.d.pd := hU.1.2.1
  have hpd : 0 < C.d.pd := hAux.1.pos
  have hN3 : 3 ≤ T.Q.l.M * C.d.pd := le_trans T.Q.l.three_le (Nat.le_mul_of_pos_right _ hpd)
  have hcurve : GlobalTheory.CompRat.CurveOver T.Q.H C.d.c₂.F (T.Q.l.M * C.d.pd) :=
    curveOver_of_rayIn hRF D T.Q hL.pins.1 _ hN3 C.d.c₂.F C.σ₂ hRay
  set dd' : GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ := castDict hV.symm dd with hdd'
  have hdd2 : MuVal _ δc dd' ∨ MuVal _ δc⁻¹ dd' :=
    hdd.imp (muVal_cast hV δc dd) (muVal_cast hV δc⁻¹ dd)
  have hval := twist_mem_fieldRange D _ C.d.pd _ C.σ₂ δ δc hTw dd' hdd2
  choose w hw using fun g => RingHom.mem_fieldRange.1 (hval g)
  have hinj : ∀ g g', dd' g = dd' g' → w g = w g' := fun g g' h => C.σ₂.injective (by rw [hw, hw, h])
  have key := (GlobalTheory.CoverComp.forms_mul_comp D T hL ((i : ℕ) + 1) ⟨Nat.succ_pos _, i.2⟩ T.σ₀ rfl C hU
    (T.Q.l.M * C.d.pd) (Nat.mul_pos (by have := T.Q.l.three_le; omega) hpd) (by rw [hlev]) (Or.inr hcurve) w
    (fun h h' hh => hinj _ _ (twist_eq_of_finHom D _ C.d.pd _ C.σ₂ δ δc hTw dd' hdd2 h h' hh))
    (fun γ hγ h => hinj _ _ (twist_mul_left D _ C.d.pd _ C.σ₂ δ δc hTw dd' hdd2 γ hγ h))
    (fun u hu1 hu2 h => hinj _ _ (twist_mul_right D _ T.Q.l.M C.d.pd _ C.σ₂ δ δc hAux hTw dd' hdd2 u hu1 (hlev ▸ hu2) h))
    (wtA (κ i)) (κ i).n).1 φ' hφ'
  refine ⟨_, key, ?_⟩
  simp only [hw]
  exact castDict_mul hV dd φ'

end GlobalTheory.TwistRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormsDetTwistMulRationalStatement
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalForms_detTwist_mul_rational : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
      ∀ (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist C.d.pd C.σ₂ δ δc →
      ∀ dd : GA D (Wc D i) → ℂ, MuVal (Wc D i) δc dd ∨ MuVal (Wc D i) δc⁻¹ dd →
      ∀ φ : GA D (Wc D i) → ℂ, IsRat T i hV C (κ i) φ → IsRat T i hV C (κ i) (fun g => dd g * φ g) := by
  first | exact @GlobalTheory.TwistRat.isRat_twist | exact GlobalTheory.TwistRat.isRat_twist | (intros; apply GlobalTheory.TwistRat.isRat_twist <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UntwistedThetaRationalOnGoodCovers
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjIdempotentSumOverLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjIdempotentSumOverLevel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.HalfLevelConj

theorem exists_conj_idemSum : ∀ (D : D7) (N : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P →
    (∀ PP ∈ P, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ (e' : AE D) (P' : Finset (Formalism.L2.DIV.Pl D.host.E)),
    IsIdemSum e' P' ∧ (∀ PP ∈ P', ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ cA D e' = e := by
  intro D N e P hE hN
  classical
  refine ⟨cA D e, P.image Formalism.L2.DIV.conjPl, Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj hE, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hQ
    have hmem : ((N : ℕ) : 𝓞 D.host.E) ∈ (Formalism.L2.DIV.conjPl PP).asIdeal ↔
        Formalism.L2.DIV.starO ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := Iff.rfl
    have hs : Formalism.L2.DIV.starO ((N : ℕ) : 𝓞 D.host.E) = ((N : ℕ) : 𝓞 D.host.E) := by
      apply RingOfIntegers.ext
      rw [Formalism.L2.DIV.starO_coe]
      simp
    rw [hmem, hs]
    exact hN PP hPP
  · rw [Formalism.L2.Theta.cA_cA]

end GlobalTheory.HalfLevelConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjIdempotentSumOverLevelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_idempotentSum_over_level : ∀ (D : D7) (N : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ (e' : AE D) (P' : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e' P' ∧ (∀ PP ∈ P', ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ cA D e' = e := by
  first | exact @GlobalTheory.HalfLevelConj.exists_conj_idemSum | exact GlobalTheory.HalfLevelConj.exists_conj_idemSum | (intros; apply GlobalTheory.HalfLevelConj.exists_conj_idemSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UntwistedThetaRationalOnGoodCovers
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.SerStd

theorem exists_of_mem_ratVec {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (i : Fin D.R.m) {c0L : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W}
    {c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W} (hc : CoefficientBaseChange R i D.what₂.embLL (RingHom.id ℂ) c0L c0) (k : Subfield ℂ)
    {w : (R.cV i).W} (hw : w ∈ ratVec R i c0L k) :
    ∃ v : VsV D i ℂ, (∀ m, AddMonoidAlgebra.coeff (v : Formalism.L2.DIV.Pol ℂ D.what₂.Tau (Vc D i).rank) m ∈ k) ∧ w = c0 v := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨v', hv', e⟩ := hc v
    exact ⟨v', fun m => by rw [hv', MvPolynomial.coeff_map]; exact hv m, e.symm⟩
  | zero => exact ⟨0, fun m => by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, fun m => by simpa using k.add_mem (ha m) (hb m), by simp⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨(c : ℂ) • a, fun m => ?_, ?_⟩
    · simpa using k.mul_mem c.2 (ha m)
    · rw [map_smul]; rfl

theorem sum_mem_ratForms {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {m : ℕ} (β : Fin m → ℂ) (fs : Fin m → Rul C.d.Xo₂ C.d.c₂)
    (hβ : ∀ k, β k ∈ C.σ₂.range) (hf : ∀ k, fs k ∈ C.cuspSec a n) :
    ∑ k, β k • C.rd a (fs k) ∈ C.ratForms a n := by
  choose b hb using fun k => RingHom.mem_range.1 (hβ k)
  refine ⟨∑ k, b k • fs k, ⟨sum_mem fun k _ => (sec _ _ _ _).smul_mem _ (hf k).1, ?_⟩, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
      exact sum_mem fun k _ => by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (hf k).2
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [Cover.rd, map_sum, map_smulₛₗ, hb, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [RingHom.id_apply, smul_comm]


set_option maxHeartbeats 2000000 in
theorem untwRatS : UntwRatS := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hLev hG hFam hMod hTh hTie i hV hFP hstd gramR c0R c0L hFT u hu
  obtain ⟨c0, hc0, -⟩ := GlobalTheory.RationalValuesObj.existsUnique_c0BC R i D.what₂.embLL (RingHom.id ℂ) rfl (c0L i)
  have hcm : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap R i c0 := ⟨gramR, c0R, c0L, hFT, hc0⟩
  have hj : Formalism.L2.Pj.InR D ((i : ℕ) + 1) := inR i
  have h5 : GlobalTheory.Core5 R F := ⟨hLev, hG, hFam, hMod, hTh⟩
  obtain ⟨hPr, q1, q2, q3, q4, q5, q6⟩ := GlobalTheory.AdTh.RecPair.isPair_record_ofFive D G Pl0 T0 A _ R F h5 i A.μ0 hstd
  obtain ⟨-, -, f3, -, f5⟩ := GlobalTheory.AdTh.PhaseMapFree.vec_fock_of_clauses D G Pl0 T0 A _ R hMod hTh i A.μ0 hstd
  have hvac := (hTh.vP i A.μ0).1
  have hP : VacPair R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i A.μ0) (R.ΛV i) (R.ΛW i) (cart (R.MW i (sg0 D A))) (R.vacP i) :=
    ⟨hPr, q1, q2, q3, q4, q5, q6, f3, hvac⟩
  obtain ⟨-, -, -, -, hrpq, -, -, -, -, -, hDom, hn, hLast⟩ := GlobalTheory.AdTh.models_at_record_ofFive D G Pl0 T0 A T R F κ v₀ h5 hTie i
    T.σ₀ rfl (T.dict _ T.σ₀ 1).1
  obtain ⟨-, -, hΨ, -, -⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hL.pins _ hj (κ i)
  have hodd : Odd D.R.r := by
    have := D.R.m_add_three_le_k
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have hpq := (rank_Wc i).trans hrpq
  have hB : ∀ τ, IsONBasis (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) (onb (R.MW i (sg0 D A)) τ)
      (T.Q.Dw ((i : ℕ) + 1)).p := fun τ => by
    rw [(hL.pins.2.2.2 _ hj).1, ← show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
    exact f5 τ
  have hlt := GlobalTheory.FockLetters.isLetters_letterEquiv (n := (Vc D i).rank) (T.Q.Dw ((i : ℕ) + 1)) hΨ hpq
  generalize GlobalTheory.FockLetters.letterEquiv (n := (Vc D i).rank) (T.Q.Dw ((i : ℕ) + 1)) hΨ hpq = lt at hlt
  have hχ := GlobalTheory.T.referenceTuple_secondSplittingCharacter D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := hL.pins.2.1.1
  rw [← hMg] at hχ
  have hM₀ : T.Q.l.M ≠ 0 := by have := T.Q.l.three_le; omega
  have hMb : Nat.Coprime T.Q.l.M (GlobalTheory.Tow.badN D) := by
    have : ∀ k, Nat.Coprime (D.host.g k) (GlobalTheory.Tow.badN D) := fun k =>
      ((D.host.level_coprimeS _ (D.host.g_level k)).mul_right (Nat.Coprime.of_dvd_right
        (Dvd.intro _ rfl |>.trans (show D.host.q * (D.host.QS * D.host.d) ∣ D.host.QS * D.host.q * D.host.d from ⟨1, by ring⟩))
        (Nat.Coprime.symm (by rw [Nat.Coprime, Nat.gcd_rec, D.ntypes.g_cond k, Nat.gcd_one_left])))).mul_right
        (D.host.ccK_coprime _ (by simp [D.host.g_level k])).symm
    rw [hMg]
    exact (this 0).mul_left (this 1)
  obtain ⟨ph, hph, hbase⟩ := GlobalTheory.T.coreConstants_eq_vacuumIdentity_up_to_phase D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd hV hFP
  obtain ⟨ka, hka, J, hJH, hJk, hJ⟩ := GlobalTheory.T.harmonicMap_extremalVector_eq_phase_smul_letters D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd u hu c0 hcm lt hlt
  have hph0 : ph ≠ 0 := fun h => by simp [h] at hph
  have hka0 : ka ≠ 0 := fun h => by simp [h] at hka
  refine ⟨(ka * ph)⁻¹, by rw [norm_inv, norm_mul, hka, hph]; norm_num, fun C hC s hs f hf w hw => ?_⟩
  obtain ⟨hU, hpin, hAux, hSmall, -⟩ := hC
  obtain ⟨v, hvk, rfl⟩ := exists_of_mem_ratVec R i hc0 _ hw
  have hM₂ : C.d.l₂.M = T.Q.l.M * C.d.pd := hU.1.2.1
  have hpd0 : 0 < C.d.pd := hAux.1.pos
  obtain ⟨l, hlge, hl⟩ := Nat.exists_infinite_primes (C.d.pd + 1)
  have hcl : Nat.Coprime C.d.pd l :=
    ((Nat.Prime.coprime_iff_not_dvd hl).2 fun h => by have := Nat.le_of_dvd hpd0 h; omega).symm
  obtain ⟨c₂, hc₂⟩ := series_bound hP (rank_Wc i) hodd hχ hM₀ hpq hΨ hB hlt hDom hLast hl hs
  obtain ⟨hD, hF, hrel, hσ⟩ := GlobalTheory.T.uniformisedCover_isDictionary_frameCompatible D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd hV C hU
  have hcc := GlobalTheory.T.vacuumIdentityConstants_cover_of_dominantPins D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd hV ph hph hbase C hU hpin
  have hgood : C.d.l₂.GoodAt l := goodAt_of_dvd hl hM₂ hcl
    (Formalism.L2.Pj.goodAt_of_two_primes hMg (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne l hl)
  have hval := GlobalTheory.T.character_quotient_values_in_embedding_field D G Pl0 T0 A T.Q.c.F R i C.d.c₂.F C.σ₂ hSmall
  obtain ⟨P, e, Φ, he, hPM, hsupp, hper, hΦk, hth⟩ := hf
  obtain ⟨e', P', he', hPM', hce⟩ := GlobalTheory.T.exists_conj_idempotentSum_over_level D _ e P he hPM
  obtain ⟨la, hla⟩ := exists_place_over C.d.c₂.F hl
  have hθf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f :=
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hPr.weil.std hPr.inf hth hvac.2.theta
  have hfld : ∀ x ∈ T.Q.c.F, x ∈ C.σ₂.fieldRange := fun x hx => ⟨C.inc ⟨x, hx⟩, RingHom.congr_fun hU.2.2.1 ⟨x, hx⟩⟩
  have hQO : ∀ mo, (J v).coeff mo ∈ C.σ₂.range := fun mo =>
    RingHom.mem_range.2 (RingHom.mem_fieldRange.1 (hJk C.σ₂.fieldRange hfld v hvk mo))
  have hΦO : ∀ x, Φ x ∈ C.σ₂.range := fun x => RingHom.mem_range.2 (RingHom.mem_fieldRange.1 (hΦk x))
  have hPM₂ : ∀ PP ∈ P', ((C.d.l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by rw [hM₂]; exact hPM'
  have hfn : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsLevelFn (cA D e') (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) C.d.l₂.M Φ := by
    rw [hce, hM₂]; exact ⟨hsupp, hper⟩
  have hth' : IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D e')
      (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) Φ f := by rw [hce]; exact hth
  obtain ⟨m, β, fs, hfs, hsum⟩ := hc₂ C.d.l₂ C.d.pd C.d.Xo₂ C.d.c₂ C.σ₂ C.U₂ _ _ _ _ _ hM₂ hU.1.2.2.1 hcl
    (hM₂ ▸ hMb.mul_left hAux.2.2.2.2) hU.2.1 hgood hrel hσ hD hF hcc hval la C.σ₂.range hla (valRing_range _ _) e' P' Φ f he'
    hPM₂ hfn hΦO hth' (J v) (hJH v) hQO
  let Fn : GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ := castDict hV.symm fun g =>
    (l : ℂ) ^ c₂ * ((ka * ph)⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.series R i u s f (c0 v) g)
  have e1 : Fn = ∑ k, β k • C.rd (wtA (κ i)) (fs k) := by
    refine eq_of_castDict hV fun g => ?_
    rw [castDict_symm]
    have e2 := hsum g
    have e3 : castDict hV (∑ k, β k • C.rd (wtA (κ i)) (fs k)) g = ∑ k, β k * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
        (C.cc₂ (castDict hV C.dict₂ g).1 * castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) g *
          rdU C.U₂ (fs k) (castDict hV C.dict₂ g).1 (castDict hV C.dict₂ g).2)) := by
      unfold castDict
      rw [Finset.sum_apply]
      rfl
    rw [e3, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.series, hJ f hθf v]
    simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul] at e2 ⊢
    have e4 : ∑ k, β k * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
        (ph * C.cc₂ (castDict hV C.dict₂ g).1 * castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) g *
          rdU C.U₂ (fs k) (castDict hV C.dict₂ g).1 (castDict hV C.dict₂ g).2)) = ph *
        ∑ k, β k * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
        (C.cc₂ (castDict hV C.dict₂ g).1 * castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) g *
          rdU C.U₂ (fs k) (castDict hV C.dict₂ g).1 (castDict hV C.dict₂ g).2)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e4] at e2
    refine mul_left_cancel₀ hph0 ?_
    rw [← e2]
    field_simp
  have hR : IsRat T i hV C (κ i) (castDict hV Fn) := by
    refine ⟨Fn, ?_, rfl⟩
    rw [e1]
    refine sum_mem_ratForms C _ _ β fs (fun k => (hfs k).1) fun k => ?_
    rw [hn]; exact ⟨(hfs k).2.1, (hfs k).2.2.1⟩
  have hl0 : ((l : ℂ) ^ c₂) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.ne_zero)
  have h2 := GlobalTheory.SerRatRay.isRat_const_mul T i hV C (κ i) _ ((l : ℂ) ^ c₂)⁻¹ hR
    ⟨((l : C.d.c₂.F) ^ c₂)⁻¹, by simp⟩
  convert h2 using 1
  funext g
  show _ = ((l : ℂ) ^ c₂)⁻¹ * castDict hV (castDict hV.symm _) g
  rw [castDict_symm, inv_mul_cancel_left₀ hl0]
  rfl

end GlobalTheory.SerStd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UntwistedThetaRationalOnGoodCoversStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untwisted_theta_rational_on_good_covers : GlobalTheory.SerStd.UntwRatS := by
  first | exact @GlobalTheory.SerStd.untwRatS | exact GlobalTheory.SerStd.untwRatS | (intros; apply GlobalTheory.SerStd.untwRatS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaSeriesRationalOnGoodCoversOfUntwisted
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaSeriesRationalOnGoodCoversOfUntwisted
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.SerRatRay
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SerStdTwist

theorem seriesRatS_of_untwRatS (hRF : GlobalTheory.Published.RayClassFieldSt) (hU : GlobalTheory.SerStd.UntwRatS) : GlobalTheory.SerStd.SeriesRatS := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hIs hG hFam hMod hThP hTie i hV hFP hstd gramR c0R c0L hFT u hu
  obtain ⟨ph, hph, hU'⟩ := hU D G Pl0 T0 A T R F κ v₀ hL hIs hG hFam hMod hThP hTie i hV hFP hstd gramR c0R c0L hFT u hu
  refine ⟨ph, hph, fun C hC s hs f hf w hw => ⟨hU' C hC s hs f hf w hw, fun δ δc hδ => ⟨fun dd hdd => ?_, fun om hom => ?_⟩⟩⟩
  · have := GlobalTheory.T.rationalForms_detTwist_mul_rational hRF D G Pl0 T0 A T R F κ v₀ hL hIs hG hFam hMod hThP hTie i hV hFP gramR c0R c0L hFT u hu C hC δ δc hδ dd
      (Or.inl hdd) _ (hU' C hC s hs f hf w hw)
    simpa [mul_assoc] using this
  · obtain ⟨c, hc, dd, hdd, heq⟩ :=
      GlobalTheory.WeilTwistSeries.theta_weil_twist D G Pl0 T0 A T R F κ v₀ hL hIs hG hFam hMod hThP hTie i hV hFP gramR c0R c0L hFT u hu C hC δ δc hδ om hom s hs
        f hf w hw
    have h1 := GlobalTheory.T.rationalForms_detTwist_mul_rational hRF D G Pl0 T0 A T R F κ v₀ hL hIs hG hFam hMod hThP hTie i hV hFP gramR c0R c0L hFT u hu C hC δ δc
      hδ dd hdd _ (hU' C hC s hs f hf w hw)
    have h2 := isRat_const_mul T i hV C (κ i) _ c h1 hc
    convert h2 using 2 with g
    rw [heq g]; ring

end GlobalTheory.SerStdTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaSeriesRationalOnGoodCoversOfUntwistedStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeriesRationalOnGoodCovers_of_untwisted : GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.UntwRatS → GlobalTheory.SerStd.SeriesRatS := by
  first | exact @GlobalTheory.SerStdTwist.seriesRatS_of_untwRatS | exact GlobalTheory.SerStdTwist.seriesRatS_of_untwRatS | (intros; apply GlobalTheory.SerStdTwist.seriesRatS_of_untwRatS <;> assumption)
end
end

namespace GlobalTheory

theorem serInt_outright : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP
  exact ⟨fun u hu c0 hc0 => GlobalTheory.LevelSeries.serIntAt_record D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP u hu c0 hc0,
    GlobalTheory.T.unramified_descent_integral_forms_tower_cover D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP⟩

theorem _root_.GlobalTheory.T.thetaSeries_integral_uniform_prime_power : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt :=
  serInt_outright

theorem seriesRatS_and_serInt_of_globalArtin :
    GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.SerStd.SeriesRatS ∧ GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt :=
  fun hA => ⟨GlobalTheory.T.thetaSeriesRationalOnGoodCovers_of_untwisted (GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt hA) GlobalTheory.T.untwisted_theta_rational_on_good_covers,
    GlobalTheory.T.thetaSeries_integral_uniform_prime_power⟩

end GlobalTheory
