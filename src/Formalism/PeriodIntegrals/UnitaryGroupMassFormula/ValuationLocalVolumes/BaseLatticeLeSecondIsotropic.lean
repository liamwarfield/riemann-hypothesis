module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FrameVectorMemBaseLattice

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVZPrimHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVSDBwdHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OneMemOev
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem incl_mem (o : 𝓞 E) : inclR (F := F) (Fv F v) (o : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨o, trivial, rfl⟩

theorem one_mem_oev : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  have h := incl_mem (F := F) (E := E) v 1
  simpa using h

theorem denseF (c ε : Fv F v) (hε : ε ≠ 0) :
    ∃ b : F, ∃ o ∈ v.adicCompletionIntegers F, algebraMap F (Fv F v) b - c = ε * o := by
  have hO : IsOpen ((v.adicCompletionIntegers F : Set (Fv F v))) := Valued.isOpen_integer _
  have hU : IsOpen {k : Fv F v | (k - c) * ε⁻¹ ∈ v.adicCompletionIntegers F} :=
    hO.preimage ((continuous_id.sub continuous_const).mul continuous_const)
  obtain ⟨b, hb⟩ := (HeightOneSpectrum.denseRange_algebraMap (v := v) (K := F)).exists_mem_open hU
    ⟨c, by simp [zero_mem]⟩
  refine ⟨b, _, hb, ?_⟩
  field_simp

theorem tmul_eq (c : Fv F v) (x : E) :
    c ⊗ₜ[F] x = algebraMap (Fv F v) (Fv F v ⊗[F] E) c * inclR (F := F) (Fv F v) x := by
  simp [inclR, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]

theorem alg_alg (b : F) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) b) = inclR (F := F) (Fv F v) (algebraMap F E b) := by
  rw [← IsScalarTower.algebraMap_apply]
  simp [inclR]

theorem approx (M : ℤ) (hM : M ≠ 0) (t : Fv F v ⊗[F] E) :
    ∃ e : E, ∃ w ∈ OEv (E := E) v, t - inclR (F := F) (Fv F v) e = (M : Fv F v ⊗[F] E) * w := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩
  | tmul c x =>
    obtain ⟨m, hm, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) {x}
    have hi : IsIntegral ℤ (m • x) := hint x (Finset.mem_singleton_self x)
    set o : 𝓞 E := ⟨m • x, hi⟩ with ho
    set mF : Fv F v := algebraMap F (Fv F v) (m : F) with hmF
    have hmF0 : mF ≠ 0 := (map_ne_zero _).2 (Int.cast_ne_zero.2 hm)
    have hMF0 : algebraMap F (Fv F v) (M : F) ≠ 0 := (map_ne_zero _).2 (Int.cast_ne_zero.2 hM)
    obtain ⟨b, u, hu, hb⟩ := denseF v (c / mF) (algebraMap F (Fv F v) (M : F)) hMF0
    refine ⟨algebraMap F E b * (m • x), (⟨-u, neg_mem hu⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) (o : E),
      Submodule.smul_mem _ _ (incl_mem v o), ?_⟩
    have hb' : mF * algebraMap F (Fv F v) b - c = mF * (algebraMap F (Fv F v) (M : F) * u) := by
      rw [← hb]; field_simp
    have hb'' := congrArg (algebraMap (Fv F v) (Fv F v ⊗[F] E)) hb'
    simp only [map_sub, map_mul, hmF, alg_alg, map_intCast] at hb''
    have ho' : inclR (F := F) (Fv F v) (o : E) = (m : Fv F v ⊗[F] E) * inclR (F := F) (Fv F v) x := by
      rw [ho]; show inclR (F := F) (Fv F v) (m • x) = _; rw [zsmul_eq_mul, map_mul, map_intCast]
    have hs : (⟨-u, neg_mem hu⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) (o : E) =
        -(algebraMap (Fv F v) (Fv F v ⊗[F] E) u * inclR (F := F) (Fv F v) (o : E)) := by
      rw [← neg_mul, ← map_neg, ← Algebra.smul_def]; rfl
    rw [hs, ho', tmul_eq, zsmul_eq_mul, map_mul, map_mul, map_intCast]
    linear_combination (-(inclR (F := F) (Fv F v) x)) * hb''
  | add t t' h1 h2 =>
    obtain ⟨e1, w1, hw1, he1⟩ := h1
    obtain ⟨e2, w2, hw2, he2⟩ := h2
    refine ⟨e1 + e2, w1 + w2, Submodule.add_mem _ hw1 hw2, ?_⟩
    rw [map_add (f := _)]; linear_combination he1 + he2

def trV : Fv F v ⊗[F] E →ₗ[Fv F v] Fv F v :=
  (Algebra.TensorProduct.rid F (Fv F v) (Fv F v)).toLinearMap ∘ₗ LinearMap.baseChange (Fv F v) (Algebra.trace F E)

theorem trV_tmul (c : Fv F v) (x : E) : trV v (c ⊗ₜ[F] x) = Algebra.trace F E x • c := rfl

theorem trV_mem {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : trV v x ∈ v.adicCompletionIntegers F := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨o, _, rfl⟩ := hx
    change trV v ((1 : Fv F v) ⊗ₜ[F] (o : E)) ∈ _
    rw [trV_tmul, Algebra.smul_def, mul_one]
    have hI : IsIntegral ℤ (Algebra.trace F E (o : E)) := Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)
    set r : 𝓞 F := ⟨_, (mem_integralClosure_iff ℤ F).2 hI⟩ with hr
    have h1 : Algebra.trace F E (o : E) = (r : F) := rfl
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (r : F)
    rw [h1, HeightOneSpectrum.mem_adicCompletionIntegers,
      show algebraMap F (Fv F v) (r : F) = ((r : F) : Fv F v) from rfl, this, HeightOneSpectrum.valuation_of_algebraMap]
    exact v.intValuation_le_one r
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | smul c x _ h =>
    change trV v ((c : Fv F v) • x) ∈ _
    rw [map_smul, smul_eq_mul]; exact mul_mem c.2 h

theorem trV_alg (c : Fv F v) :
    trV v (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = algebraMap F (Fv F v) (Module.finrank F E : F) * c := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, trV_tmul,
    ← map_one (algebraMap F E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one, Algebra.smul_def]

theorem pow_unbdd {a b : WithZero (Multiplicative ℤ)} (ha : 1 < a) (hb : b ≠ 0) :
    ∃ k : ℕ, 1 < b * a ^ k := by
  obtain ⟨β, rfl⟩ := WithZero.ne_zero_iff_exists.1 hb
  have ha0 : a ≠ 0 := ne_of_gt (lt_trans zero_lt_one ha)
  obtain ⟨α, rfl⟩ := WithZero.ne_zero_iff_exists.1 ha0
  have hα : 0 < Multiplicative.toAdd α := by
    have h := WithZero.coe_lt_coe.1 (show ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < α from ha)
    exact Multiplicative.ofAdd_lt.1 h
  refine ⟨(Multiplicative.toAdd β).natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_lt_coe,
    ← Multiplicative.toAdd_lt, toAdd_mul, toAdd_pow, toAdd_one]
  rw [nsmul_eq_mul]; push_cast
  have h3 : (|Multiplicative.toAdd β| + 1) * 1 ≤ (|Multiplicative.toAdd β| + 1) * Multiplicative.toAdd α :=
    mul_le_mul_of_nonneg_left (by omega) (by positivity)
  linarith [neg_abs_le (Multiplicative.toAdd β)]

theorem int_of_alg (c : Fv F v) (hc : algebraMap (Fv F v) (Fv F v ⊗[F] E) c ∈ OEv (E := E) v) :
    c ∈ v.adicCompletionIntegers F := by
  by_contra hn
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hn
  have hpow : ∀ k : ℕ, algebraMap (Fv F v) (Fv F v ⊗[F] E) (c ^ k) ∈ OEv (E := E) v := by
    intro k
    induction k with
    | zero => rw [pow_zero, map_one]; exact one_mem_oev v
    | succ k ih => rw [pow_succ, map_mul]; exact oev_mul v ih hc
  have hd0 : algebraMap F (Fv F v) (Module.finrank F E : F) ≠ 0 :=
    (map_ne_zero _).2 (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  obtain ⟨k, hk⟩ := pow_unbdd hn ((Valuation.ne_zero_iff _).2 hd0)
  have := trV_mem v (hpow k)
  rw [trV_alg, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_pow] at this
  exact absurd this (not_le.2 hk)

end Gen

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

theorem sigR_oev {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : sigR (Fv F v) σ x ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨o, _, rfl⟩ := hx
    rw [sigR_inclR]
    exact incl_mem (F := F) v (⟨σ (o : E), (RingOfIntegers.isIntegral_coe o).map (σ : E →+* E).toIntAlgHom⟩ : 𝓞 E)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ h1 h2 => rw [map_add (f := _)]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    change sigR (Fv F v) σ ((c : Fv F v) • x) ∈ _
    rw [Algebra.smul_def, map_mul, sigR_alg, ← Algebra.smul_def]
    exact Submodule.smul_mem _ c h

theorem unit_of_notMem (t : 𝓞 F) (ht : t ∉ v.asIdeal) :
    (algebraMap F (Fv F v) (t : F))⁻¹ ∈ v.adicCompletionIntegers F ∧ algebraMap F (Fv F v) (t : F) ≠ 0 := by
  have hv : Valued.v (algebraMap F (Fv F v) (t : F)) = (1 : WithZero (Multiplicative ℤ)) := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (t : F)
    rw [show algebraMap F (Fv F v) (t : F) = ((t : F) : Fv F v) from rfl, this,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v t).2 ht
  refine ⟨?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
  · intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv

theorem hR_sub_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (y - y') = hR (Fv F v) σ J x y - hR (Fv F v) σ J x y' := by
  rw [eq_sub_iff_add_eq, ← hR_add_right, sub_add_cancel]

theorem exists_int_smul_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨N1, h1, m1⟩ := hy
    obtain ⟨N2, h2, m2⟩ := hz
    refine ⟨N1 * N2, mul_ne_zero h1 h2, ?_⟩
    have e1 : (N1 * N2) • y = N2 • (N1 • y) := by rw [mul_comm, mul_smul]
    have e2 : (N1 * N2) • z = N1 • (N2 • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact L.add_mem (zsmul_mem m1 N2) (zsmul_mem m2 N1)
  | smul e y _ hy =>
    obtain ⟨N, hN, m⟩ := hy
    obtain ⟨c, hc, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
    have hi : IsIntegral ℤ (c • e) := hint e (Finset.mem_singleton_self e)
    refine ⟨c * N, mul_ne_zero hc hN, ?_⟩
    have e3 : (c * N) • (e • y) = (c • e) • (N • y) := by
      rw [mul_smul, smul_comm N e y, smul_assoc]
    rw [e3]
    have e4 : (c • e) • (N • y) = (⟨c • e, hi⟩ : 𝓞 E) • (N • y) := by
      rw [← algebraMap_smul E (⟨c • e, hi⟩ : 𝓞 E) (N • y)]; rfl
    rw [e4]
    exact L.smul_mem _ m

end Gen

variable {D : D7} (X : HidaSetting D)

theorem fixed_ex (a : X.B.I.E) (ha : star a = a) : ∃ f : X.B.I.F, algebraMap X.B.I.F X.B.I.E f = a := by
  obtain ⟨f, hf⟩ := (X.B.I.cm.fixed a).1 ha
  exact ⟨f, hf⟩

theorem val_le (v : PlX X) (f : X.B.I.F)
    (hf : inclR (F := X.B.I.F) (Fv X.B.I.F v) (algebraMap X.B.I.F X.B.I.E f) ∈ OEv (E := X.B.I.E) v) :
    v.valuation X.B.I.F f ≤ 1 := by
  rw [← alg_alg] at hf
  have := int_of_alg v _ hf
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, show algebraMap X.B.I.F (Fv X.B.I.F v) f = (f : Fv X.B.I.F v) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  exact this


open Polynomial in
theorem denom (v : PlX X) (e : X.B.I.E) (he : inclR (F := X.B.I.F) (Fv X.B.I.F v) e ∈ OEv (E := X.B.I.E) v) :
    ∃ s : 𝓞 X.B.I.F, s ∉ v.asIdeal ∧ ∃ c : 𝓞 X.B.I.E, (c : X.B.I.E) = algebraMap X.B.I.F X.B.I.E s * e := by
  have hse : inclR (F := X.B.I.F) (Fv X.B.I.F v) (star e) ∈ OEv (E := X.B.I.E) v := by
    have := sigR_oev X.B.I.cm.sig v he
    rwa [sigR_inclR] at this
  obtain ⟨fT, hfT⟩ := fixed_ex X (e + star e) (by rw [star_add, star_star, add_comm])
  obtain ⟨fN, hfN⟩ := fixed_ex X (e * star e) (by rw [star_mul, star_star])
  have vT : v.valuation X.B.I.F fT ≤ 1 := val_le X v fT (by rw [hfT, map_add (f := _)]; exact Submodule.add_mem _ he hse)
  have vN : v.valuation X.B.I.F fN ≤ 1 := val_le X v fN (by rw [hfN, map_mul]; exact oev_mul v he hse)
  obtain ⟨nT, ⟨dT, hdT⟩, hT⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v fT vT
  obtain ⟨nN, ⟨dN, hdN⟩, hN⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v fN vN
  refine ⟨dT * dN, ?_, ?_⟩
  · exact (Ideal.primeCompl v.asIdeal).mul_mem hdT hdN
  · let φ := algebraMap X.B.I.F X.B.I.E
    let ψ := algebraMap (𝓞 X.B.I.F) X.B.I.F
    have hy_eq : (φ (ψ (dT * dN)) * e) ^ 2 - φ (ψ (dN * nT)) * (φ (ψ (dT * dN)) * e) +
        φ (ψ (dT * dT * dN * nN)) = 0 := by
      simp only [map_mul ψ]
      rw [← hT, ← hN]
      simp only [map_mul φ]
      rw [hfT, hfN]
      ring
    have h𝓞 : IsIntegral (𝓞 X.B.I.F) (φ (ψ (dT * dN)) * e) := by
      refine ⟨Polynomial.X ^ 2 - C (dN * nT) * Polynomial.X + C (dT * dT * dN * nN), ?_, ?_⟩
      · monicity!
      · simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X]
        rw [IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) X.B.I.F X.B.I.E (dN * nT),
          IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) X.B.I.F X.B.I.E (dT * dT * dN * nN)]
        exact hy_eq
    exact ⟨⟨_, isIntegral_trans _ h𝓞⟩, rfl⟩

def liftE (r : 𝓞 X.B.I.F) : 𝓞 X.B.I.E :=
  ⟨algebraMap X.B.I.F X.B.I.E (r : X.B.I.F),
    (RingOfIntegers.isIntegral_coe r).map (IsScalarTower.toAlgHom ℤ X.B.I.F X.B.I.E)⟩

theorem liftE_coe (r : 𝓞 X.B.I.F) : ((liftE X r : 𝓞 X.B.I.E) : X.B.I.E) = algebraMap X.B.I.F X.B.I.E (r : X.B.I.F) :=
  rfl

def starE (a : 𝓞 X.B.I.E) : 𝓞 X.B.I.E :=
  ⟨star (a : X.B.I.E), (RingOfIntegers.isIntegral_coe a).map (starRingEnd X.B.I.E).toIntAlgHom⟩

theorem hform_zero_left (x : Fin X.B.I.n → X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J 0 x = 0 := by
  simp [Formalism.UG.hform]

theorem hform_add_left (y y' x : Fin X.B.I.n → X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (y + y') x =
      Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y x + Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y' x := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_smul_left (a : 𝓞 X.B.I.E) (y x : Fin X.B.I.n → X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (a • y) x =
      star (a : X.B.I.E) * Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y x := by
  simp only [Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, map_mul, starRingEnd_apply (algebraMap (𝓞 X.B.I.E) X.B.I.E a)]
  ring

theorem hform_smul_right (y x : Fin X.B.I.n → X.B.I.E) (c : X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y (c • x) = c * Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y x := by
  simp only [Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem locGlob (v : PlX X) (x : Fin X.B.I.n → X.B.I.E)
    (hx : ∀ l ∈ X.B.I.L, inclR (F := X.B.I.F) (Fv X.B.I.F v) (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l x) ∈
      OEv (E := X.B.I.E) v) :
    ∃ t : 𝓞 X.B.I.F, t ∉ v.asIdeal ∧ algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) • x ∈ X.B.I.L := by
  classical
  obtain ⟨S, hS⟩ := X.B.I.L_fg
  have hSL : ∀ g ∈ S, g ∈ X.B.I.L := fun g hg => hS ▸ Submodule.subset_span hg
  have hg : ∀ g ∈ S, ∃ s : 𝓞 X.B.I.F, s ∉ v.asIdeal ∧ ∃ c : 𝓞 X.B.I.E,
      (c : X.B.I.E) = algebraMap X.B.I.F X.B.I.E s * Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J g x :=
    fun g hgS => denom X v _ (hx g (hSL g hgS))
  choose! s hs c hc using hg
  set t : 𝓞 X.B.I.F := ∏ g ∈ S, s g with ht_def
  have ht : t ∉ v.asIdeal := by
    intro h
    have := v.isPrime
    obtain ⟨g, hgS, hg⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hs g hgS hg
  set T : X.B.I.E := algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) with hT
  have hkey : ∀ g ∈ S, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J g (T • x) ∈
      (algebraMap (𝓞 X.B.I.E) X.B.I.E).range := by
    intro g hgS
    rw [hform_smul_right]
    refine ⟨liftE X (∏ h ∈ S.erase g, s h) * c g, ?_⟩
    rw [map_mul]
    show ((liftE X (∏ h ∈ S.erase g, s h) : 𝓞 X.B.I.E) : X.B.I.E) * ((c g : 𝓞 X.B.I.E) : X.B.I.E) = _
    rw [hc g hgS, liftE_coe, hT, ht_def, ← Finset.mul_prod_erase S s hgS]
    have hm : ((s g * ∏ x ∈ S.erase g, s x : 𝓞 X.B.I.F) : X.B.I.F) =
        (s g : X.B.I.F) * ((∏ x ∈ S.erase g, s x : 𝓞 X.B.I.F) : X.B.I.F) := map_mul (algebraMap _ _) _ _
    rw [hm, map_mul]
    ring
  refine ⟨t, ht, ?_⟩
  refine (X.B.I.L_dual _).2 fun y hy => ?_
  rw [← hS] at hy
  induction hy using Submodule.span_induction with
  | mem g hg => exact hkey g hg
  | zero => rw [hform_zero_left]; exact ⟨0, map_zero _⟩
  | add y y' _ _ h1 h2 =>
      obtain ⟨c1, e1⟩ := h1
      obtain ⟨c2, e2⟩ := h2
      exact ⟨c1 + c2, by rw [map_add (f := _), e1, e2, hform_add_left]⟩
  | smul a y _ h1 =>
      obtain ⟨c1, e1⟩ := h1
      exact ⟨starE X a * c1, by rw [map_mul, e1, hform_smul_left]; rfl⟩

theorem cube (v : PlX X) : ∃ M : ℤ, M ≠ 0 ∧ ∀ u : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E,
    (∀ i, u i ∈ OEv (E := X.B.I.E) v) → (M : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) • u ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
  classical
  have h : ∀ j : Fin X.B.I.n, ∃ N : ℤ, N ≠ 0 ∧ N • (Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) ∈ X.B.I.L :=
    fun j => exists_int_smul_mem X.B.I.L X.B.I.L_span _
  choose N hN0 hNL using h
  set M : ℤ := ∏ j, N j with hM
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hN0 j
  have hML : ∀ j, M • (Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) ∈ X.B.I.L := by
    intro j
    rw [hM, ← Finset.mul_prod_erase Finset.univ N (Finset.mem_univ j), mul_comm, mul_smul]
    exact zsmul_mem (hNL j) _
  refine ⟨M, hM0, fun u hu => ?_⟩
  have hsingle : ∀ j, ∀ t ∈ OEv (E := X.B.I.E) v,
      (Pi.single j ((M : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) * t) : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ∈
        latLoc (E := X.B.I.E) v (abelian₂ X) := by
    intro j t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨o, _, rfl⟩ := ht
      refine Submodule.subset_span ⟨o • (M • Pi.single j (1 : X.B.I.E)), X.B.I.L.smul_mem o (hML j), ?_⟩
      funext i
      simp only [ratV, Pi.smul_apply, Pi.single_apply]
      split_ifs with hij
      · simp [Algebra.smul_def, map_mul, mul_comm]
      · simp
    | zero => rw [mul_zero, Pi.single_zero]; exact Submodule.zero_mem _
    | add t t' _ _ h1 h2 => rw [mul_add, Pi.single_add]; exact Submodule.add_mem _ h1 h2
    | smul c t _ h1 =>
      have e : (Pi.single j ((M : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) * (c • t)) : Fin X.B.I.n → _) =
          c • (Pi.single j ((M : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) * t) : Fin X.B.I.n → _) := by
        funext i
        simp only [Pi.single_apply, Pi.smul_apply]
        split_ifs <;> simp
      rw [e]; exact Submodule.smul_mem _ c h1
  have hs : (M : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) • u =
      ∑ j, (Pi.single j ((M : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) * u j) : Fin X.B.I.n → _) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hs]
  exact Submodule.sum_mem _ fun j _ => hsingle j (u j) (hu j)

theorem omVSDBwd_holds : OmVSDBwd X := by
  intro v y hy
  obtain ⟨M, hM, hcube⟩ := cube X v
  choose e w hw he using fun j => approx v M hM (y j)
  have hd : y - ratV (F := X.B.I.F) (Fv X.B.I.F v) e ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
    have : y - ratV (F := X.B.I.F) (Fv X.B.I.F v) e = (M : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) • w :=
      funext fun j => he j
    rw [this]; exact hcube w hw
  have hpair : ∀ l ∈ X.B.I.L, inclR (F := X.B.I.F) (Fv X.B.I.F v)
      (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l e) ∈ OEv (E := X.B.I.E) v := by
    intro l hl
    have h1 : inclR (F := X.B.I.F) (Fv X.B.I.F v) (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l e) =
        hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) l)
          (ratV (F := X.B.I.F) (Fv X.B.I.F v) e) :=
      (hR_ratTup (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J ![l, e] 0 1).symm
    rw [h1]
    have hl' : ratV (F := X.B.I.F) (Fv X.B.I.F v) l ∈ latLoc (E := X.B.I.E) v (abelian₂ X) :=
      Submodule.subset_span ⟨l, hl, rfl⟩
    have e2 : ratV (F := X.B.I.F) (Fv X.B.I.F v) e = y - (y - ratV (F := X.B.I.F) (Fv X.B.I.F v) e) := by abel
    rw [e2, hR_sub_right]
    exact Submodule.sub_mem _ (hy _ hl') (omVSD_fwd X v hl' hd)
  obtain ⟨s, hs, hsL⟩ := locGlob X v e hpair
  have hre : ratV (F := X.B.I.F) (Fv X.B.I.F v) e ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
    obtain ⟨hinv, hne⟩ := unit_of_notMem v s hs
    have hm : ratV (F := X.B.I.F) (Fv X.B.I.F v) (algebraMap X.B.I.F X.B.I.E (s : X.B.I.F) • e) ∈
        latLoc (E := X.B.I.E) v (abelian₂ X) := Submodule.subset_span ⟨_, hsL, rfl⟩
    have heq : ratV (F := X.B.I.F) (Fv X.B.I.F v) e =
        (⟨(algebraMap X.B.I.F (Fv X.B.I.F v) (s : X.B.I.F))⁻¹, hinv⟩ : v.adicCompletionIntegers X.B.I.F) •
          ratV (F := X.B.I.F) (Fv X.B.I.F v) (algebraMap X.B.I.F X.B.I.E (s : X.B.I.F) • e) := by
      funext j
      show inclR (F := X.B.I.F) (Fv X.B.I.F v) (e j) = (algebraMap X.B.I.F (Fv X.B.I.F v) (s : X.B.I.F))⁻¹ •
        inclR (F := X.B.I.F) (Fv X.B.I.F v) (algebraMap X.B.I.F X.B.I.E (s : X.B.I.F) * e j)
      rw [map_mul, ← alg_alg, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [heq]; exact Submodule.smul_mem _ _ hm
  have e3 : y = (y - ratV (F := X.B.I.F) (Fv X.B.I.F v) e) + ratV (F := X.B.I.F) (Fv X.B.I.F v) e := by abel
  rw [e3]; exact Submodule.add_mem _ hd hre

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem zu_orth_X (y : (VS D).V) (hy : y ∈ (X.Fu u').X) : (VS D).hT y (X.zu u') = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [← X.flagZVector u']
    exact (X.Fu u').z_orth a
  | zero => simp
  | add x y _ _ h1 h2 => simp [h1, h2]
  | smul c x _ h => simp [h]

theorem glob_prim (g : X.B.I.E) (hg : g • crdOf X.B.I X.ιE X.bas (X.zu u') ∈ X.B.I.L) : IsIntegral ℤ g := by
  have hL0 : X.ιE g • X.zu u' ∈ (VS D).L0 := by
    have h := (X.L_eq _).1 hg
    have e : (∑ i, X.ιE ((g • crdOf X.B.I X.ιE X.bas (X.zu u')) i) • X.bas i) = X.ιE g • X.zu u' := by
      simp only [Pi.smul_apply, smul_eq_mul, crdOf, map_mul, RingEquiv.apply_symm_apply, mul_smul]
      rw [← Finset.smul_sum, X.bas.sum_repr]
    rwa [e] at h
  have horth : X.ιE g • X.zu u' ∈ Formalism.MainNotions.S.Lat.orth (VS D) (X.Fu u').X := by
    simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker, map_smul, smul_eq_mul]
    intro x hx
    rw [zu_orth_X X u' x hx, mul_zero]
  obtain ⟨o, ho⟩ := (X.Fu_fixed u').2.2.2.2 (X.ιE g) (by
    change X.ιE g • (X.Fu u').z ∈ _
    rw [X.flagZVector u']
    unfold Formalism.MainNotions.S.Lat.Lsub Formalism.MainNotions.S.Lat.Lrep
    exact Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hL0, horth⟩), horth⟩)
  have e : g = X.ιE.symm (o : D.host.E) := by rw [ho, RingEquiv.symm_apply_apply]
  rw [e]
  exact (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom

theorem yTup_zi (v : PlX X) :
    yTup X u' v (zi (D := D)) = ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas (X.zu u')) := by
  have hs : scl X v (zi (D := D)) = 1 := by
    simp only [scl, zi, Fin.append_left]; exact alp_last v D.R.rS
  have h1 : yTup X u' v (zi (D := D)) = ratV (F := X.B.I.F) (Fv X.B.I.F v) (tupH (frameOf X u') (zi (D := D))) := by
    funext i
    change sc (E := X.B.I.E) v (scl X v (zi (D := D))) * _ = _
    rw [hs]
    simp only [sc, ← Algebra.TensorProduct.one_def, one_mul]
    rfl
  have h2 : hv X u' (zi (D := D)) = X.zu u' := by simp only [hv, zi, Fin.append_left, Fin.snoc_last]
  rw [h1, tupH_eq, h2]

theorem omVZPrim_holds : OmVZPrim X u' := by
  intro v _ c hc
  set z := crdOf X.B.I X.ιE X.bas (X.zu u') with hz_def
  have hz : z ∈ abelian₂ X := crdOf_mem X (frame_vector_mem_base_lattice X u')
  rw [yTup_zi] at hc
  obtain ⟨c', w, hw, hcw⟩ := approx v 1 one_ne_zero c
  have hw' : c - inclR (F := X.B.I.F) (Fv X.B.I.F v) c' = w := by rw [hcw]; simp
  have h1 : ratV (F := X.B.I.F) (Fv X.B.I.F v) (c' • z) ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
    have e : ratV (F := X.B.I.F) (Fv X.B.I.F v) (c' • z) =
        c • ratV (F := X.B.I.F) (Fv X.B.I.F v) z - w • ratV (F := X.B.I.F) (Fv X.B.I.F v) z := by
      funext i
      simp only [ratV, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul]
      rw [← hw']; ring
    rw [e]
    exact Submodule.sub_mem _ hc (lat_oev_smul X v hw (Submodule.subset_span ⟨z, hz, rfl⟩))
  have hpair : ∀ l ∈ X.B.I.L, inclR (F := X.B.I.F) (Fv X.B.I.F v)
      (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l (c' • z)) ∈ OEv (E := X.B.I.E) v := by
    intro l hl
    have h2 : inclR (F := X.B.I.F) (Fv X.B.I.F v) (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l (c' • z)) =
        hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) l)
          (ratV (F := X.B.I.F) (Fv X.B.I.F v) (c' • z)) :=
      (hR_ratTup (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J ![l, c' • z] 0 1).symm
    rw [h2]
    exact omVSD_fwd X v (Submodule.subset_span ⟨l, hl, rfl⟩) h1
  obtain ⟨t, ht, htL⟩ := locGlob X v _ hpair
  have hg : IsIntegral ℤ (algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) * c') :=
    glob_prim X u' _ (by rw [mul_smul]; exact htL)
  obtain ⟨hinv, hne⟩ := unit_of_notMem v t ht
  have hc' : inclR (F := X.B.I.F) (Fv X.B.I.F v) c' ∈ OEv (E := X.B.I.E) v := by
    have e : inclR (F := X.B.I.F) (Fv X.B.I.F v) c' =
        (⟨(algebraMap X.B.I.F (Fv X.B.I.F v) (t : X.B.I.F))⁻¹, hinv⟩ : v.adicCompletionIntegers X.B.I.F) •
          inclR (F := X.B.I.F) (Fv X.B.I.F v) (algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) * c') := by
      show inclR (F := X.B.I.F) (Fv X.B.I.F v) c' = (algebraMap X.B.I.F (Fv X.B.I.F v) (t : X.B.I.F))⁻¹ •
        inclR (F := X.B.I.F) (Fv X.B.I.F v) (algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) * c')
      rw [map_mul, ← alg_alg, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (incl_mem v (⟨_, (mem_integralClosure_iff ℤ _).2 hg⟩ : 𝓞 X.B.I.E))
  have e2 : c = w + inclR (F := X.B.I.F) (Fv X.B.I.F v) c' := by rw [← hw']; ring
  rw [e2]
  exact Submodule.add_mem _ hw hc'

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

def OmVDdLoc : Prop :=
  ∀ (v : PlX X) (a : Fin D.R.rS),
    (∀ x ∈ (aaD D a)⁻¹, sc (E := X.B.I.E) v (alp v D.R.rS a.castSucc) *
      inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) ∈ OEv (E := X.B.I.E) v) ∧
    (∀ x ∈ aaD D a, sc (E := X.B.I.E) v (alp v D.R.rS a.castSucc)⁻¹ *
      inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) ∈ OEv (E := X.B.I.E) v)

def Pm (v : PlX X) (c : Fv X.B.I.F v) (w : (VS D).V) : Submodule (𝓞 D.host.E) (VS D).V where
  carrier := {y | sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((VS D).hT w y)) ∈
    OEv (E := X.B.I.E) v}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero, mul_zero]; exact Submodule.zero_mem _
  add_mem' := by
    intro y y' hy hy'
    simp only [Set.mem_ofPred_eq, map_add (f := _), mul_add] at *
    exact Submodule.add_mem _ hy hy'
  smul_mem' := by
    intro o y hy
    simp only [Set.mem_ofPred_eq] at *
    rw [← algebraMap_smul D.host.E o y, map_smul, smul_eq_mul, map_mul, map_mul, mul_left_comm]
    exact oev_mul v (incl_mem v (⟨X.ιE.symm (o : D.host.E),
      (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom⟩ : 𝓞 X.B.I.E)) hy

theorem pm_iff (v : PlX X) (c : Fv X.B.I.F v) (w y : (VS D).V) : y ∈ Pm X v c w ↔
    sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((VS D).hT w y)) ∈ OEv (E := X.B.I.E) v :=
  Iff.rfl

theorem pm_zero (v : PlX X) (c : Fv X.B.I.F v) (w y : (VS D).V) (h : (VS D).hT w y = 0) : y ∈ Pm X v c w := by
  rw [pm_iff, h, map_zero, map_zero, mul_zero]; exact Submodule.zero_mem _

theorem hT_smul_right (w y : (VS D).V) (x : D.host.E) : (VS D).hT w (x • y) = x * (VS D).hT w y := by
  rw [map_smul, smul_eq_mul]

theorem base_lattice_le_first_isotropic (hD : OmVDdLoc X) (v : PlX X) (a : Fin D.R.rS) :
    (VS D).L0 ≤ Pm X v (alp v D.R.rS a.castSucc) (X.eX a) := by
  rw [X.Lam_split]
  refine sup_le (sup_le ?_ ?_) ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, x, _, rfl⟩
    exact pm_zero X v _ _ _ (by rw [hT_smul_right, X.ee, mul_zero])
  · intro y hy
    exact pm_zero X v _ _ _ (X.Lb_perp y hy a).1
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, x, hx, rfl⟩
    refine (pm_iff X v _ _ _).2 ?_
    rw [hT_smul_right, X.ef]
    by_cases hab : a = b
    · subst hab; rw [if_pos rfl, mul_one]; exact (hD v a).1 x hx
    · rw [if_neg hab, mul_zero, map_zero, map_zero, mul_zero]; exact Submodule.zero_mem _

theorem base_lattice_le_second_isotropic (hD : OmVDdLoc X) (v : PlX X) (a : Fin D.R.rS) :
    (VS D).L0 ≤ Pm X v (alp v D.R.rS a.castSucc)⁻¹ (X.fY a) := by
  rw [X.Lam_split]
  refine sup_le (sup_le ?_ ?_) ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, x, hx, rfl⟩
    refine (pm_iff X v _ _ _).2 ?_
    rw [hT_smul_right, ← (VS D).herm.eq (X.eX b) (X.fY a), X.ef]
    by_cases hab : b = a
    · subst hab; rw [if_pos rfl, map_one, mul_one]; exact (hD v b).2 x hx
    · rw [if_neg hab, map_zero, mul_zero, map_zero, map_zero, mul_zero]; exact Submodule.zero_mem _
  · intro y hy
    exact pm_zero X v _ _ _ (X.Lb_perp y hy a).2
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, x, _, rfl⟩
    exact pm_zero X v _ _ _ (by rw [hT_smul_right, X.ff, mul_zero])

theorem crd_of_L (l : Fin X.B.I.n → X.B.I.E) (hl : l ∈ X.B.I.L) :
    ∃ y ∈ (VS D).L0, crdOf X.B.I X.ιE X.bas y = l := by
  refine ⟨∑ i, X.ιE (l i) • X.bas i, (X.L_eq l).1 hl, ?_⟩
  funext j
  have h : X.bas.repr (∑ i, X.ιE (l i) • X.bas i) j = X.ιE (l j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [crdOf]
  rw [h, RingEquiv.symm_apply_apply]

theorem hform_star (l x : Fin X.B.I.n → X.B.I.E) :
    star (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l x) = Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J x l := by
  have herm_entry : ∀ i j, star (X.B.I.J i j) = X.B.I.J j i := fun i j => by
    have := congrFun (congrFun X.B.I.J_herm j) i
    simpa [Formalism.UG.IsHerm, Formalism.UG.cT, starRingEnd_apply] using this
  unfold Formalism.UG.hform
  rw [Finset.sum_comm, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [starRingEnd_apply, star_mul, star_star]
  rw [herm_entry]
  ring

theorem pair_mem (v : PlX X) (s : Fv X.B.I.F v) (w : (VS D).V) (l : Fin X.B.I.n → X.B.I.E) (hl : l ∈ X.B.I.L)
    (hP : (VS D).L0 ≤ Pm X v s w) :
    hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) l)
      (sc (E := X.B.I.E) v s • ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas w)) ∈ OEv (E := X.B.I.E) v := by
  obtain ⟨y, hy, rfl⟩ := crd_of_L X l hl
  rw [hR_smulE_right]
  have h1 : hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas y))
      (ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas w)) =
      inclR (F := X.B.I.F) (Fv X.B.I.F v) (hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas y) (crdOf X.B.I X.ιE X.bas w)) :=
    hR_ratTup (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J ![crdOf X.B.I X.ιE X.bas y, crdOf X.B.I X.ιE X.bas w] 0 1
  have h2 : hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas y) (crdOf X.B.I X.ιE X.bas w) =
      X.B.I.cm.sig (X.ιE.symm ((VS D).hT w y)) := by
    rw [← hE_crdOf]
    exact (hform_star X _ _).symm
  rw [h1, h2, ← sigR_inclR]
  have hsc : sc (E := X.B.I.E) v s = sigR (Fv X.B.I.F v) X.B.I.cm.sig (sc (E := X.B.I.E) v s) :=
    (sigR_tmul_one (Fv X.B.I.F v) X.B.I.cm.sig s).symm
  rw [hsc, ← map_mul]
  exact sigR_oev X.B.I.cm.sig v ((pm_iff X v s w y).1 (hP hy))

theorem yTup_eq (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) :
    yTup X u' v i = sc (E := X.B.I.E) v (scl X v i) •
      ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas (hv X u' i)) := by
  rw [← tupH_eq]; rfl

theorem omVMemEF_of (hD : OmVDdLoc X) : OmVMemEF X u' := by
  intro v i hi
  have hpair : ∀ l ∈ X.B.I.L, hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) l)
      (yTup X u' v i) ∈ OEv (E := X.B.I.E) v := by
    intro l hl
    rw [yTup_eq]
    refine Fin.addCases (fun j hj => ?_) (fun b _ => ?_) i hi
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨a, rfl⟩ | rfl
      · have hs : scl X v (Fin.castAdd D.R.rS a.castSucc) = alp v D.R.rS a.castSucc := by
          simp only [scl, Fin.append_left]
        have hw : hv X u' (Fin.castAdd D.R.rS a.castSucc) = X.eX a := by
          simp only [hv, Fin.append_left, Fin.snoc_castSucc]
        rw [hs, hw]
        exact pair_mem X v _ _ l hl (base_lattice_le_first_isotropic X hD v a)
      · exact absurd rfl hj
    · have hs : scl X v (Fin.natAdd (D.R.rS + 1) b) = (alp v D.R.rS b.castSucc)⁻¹ := by
        simp only [scl, Fin.append_right]
      have hw : hv X u' (Fin.natAdd (D.R.rS + 1) b) = X.fY b := by
        simp only [hv, Fin.append_right]
      rw [hs, hw]
      exact pair_mem X v _ _ l hl (base_lattice_le_second_isotropic X hD v b)
  refine ((omVSD_of X (omVSDBwd_holds X)) v _).2 fun x hx => ?_
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact hpair l hl
  | zero => rw [OmW.hR_zero_left]; exact Submodule.zero_mem _
  | add x x' _ _ h1 h2 => rw [OmW.hR_add_left]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    change hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J ((c : Fv X.B.I.F v) • x) _ ∈ _
    rw [OmW.hR_smul_left]; exact oev_smul v h

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
