module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ArchimedeanSignatureMatchingOfTrivialBranchingSymm

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.BlockActions.FixOrthogonalVector
section -- merged from Formalism.LocalToGlobal.GlobalTheory.BlockActions.LengthInverseBound
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open NumberField Formalism.UG

section Sesq

variable {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)

theorem hform_add_left (x x' y : Fin n → E) : hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_add_right (x y y' : Fin n → E) : hform σ J x (y + y') = hform σ J x y + hform σ J x y' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_left (r : E) (x y : Fin n → E) : hform σ J (r • x) y = σ r * hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_smul_right (r : E) (x y : Fin n → E) : hform σ J x (r • y) = r * hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Sesq

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem length_inverse_bound (σ : E →+* E) (hσ : ∀ (φ : E →+* ℂ) (x : E), φ (σ x) = (starRingEnd ℂ) (φ x))
    (J : Matrix (Fin n) (Fin n) E)
    (hdef : ∀ (φ : E →+* ℂ) (x : Fin n → E), ∃ r : ℝ, 0 ≤ r ∧ φ (hform σ J x x) = r ∧ (r = 0 → x = 0))
    (L : Submodule (𝓞 E) (Fin n → E)) (hint : ∀ x ∈ L, ∃ a : 𝓞 E, (a : E) = hform σ J x x)
    (z : Fin n → E) (hzL : ∀ x ∈ L, hform σ J x z = 0 ∧ hform σ J z x = 0)
    (T : ℕ) (hT : 1 < T) (hz : (T : E) * hform σ J z z = 1)
    (y : Fin n → E) (hy : y ∈ L ⊔ Submodule.span (𝓞 E) {z}) (hyy : (T : E) * hform σ J y y = 1) :
    ∃ b : 𝓞 E, (∃ k : ℕ, 0 < k ∧ b ^ k = 1) ∧ y = (b : E) • z := by
  obtain ⟨x, hxL, w, hw, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
  have haz : (a • z : Fin n → E) = algebraMap (𝓞 E) E a • z := (algebraMap_smul E a z).symm
  rw [haz] at hyy ⊢
  have hxz := hzL x hxL
  have hexp : hform σ J (x + algebraMap (𝓞 E) E a • z) (x + algebraMap (𝓞 E) E a • z) =
      hform σ J x x + σ (algebraMap (𝓞 E) E a) * algebraMap (𝓞 E) E a * hform σ J z z := by
    simp only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right, hxz.1, hxz.2]
    ring
  have key : (T : E) * hform σ J x x + σ (algebraMap (𝓞 E) E a) * algebraMap (𝓞 E) E a = 1 := by
    rw [hexp] at hyy
    linear_combination hyy - σ (algebraMap (𝓞 E) E a) * algebraMap (𝓞 E) E a * hz
  obtain ⟨c0, hc0⟩ := hint x hxL
  have hT1 : (1 : ℝ) < T := by exact_mod_cast hT
  have hemb : ∀ φ : E →+* ℂ, ‖φ (c0 : E)‖ < 1 ∧ ‖φ (algebraMap (𝓞 E) E a)‖ ≤ 1 ∧
      (‖φ (c0 : E)‖ = 0 → ‖φ (algebraMap (𝓞 E) E a)‖ = 1) := by
    intro φ
    obtain ⟨r, hr0, hr, -⟩ := hdef φ x
    have hk := congrArg φ key
    rw [map_add (f := _), map_mul, map_mul, hσ, map_natCast, map_one, hr, Complex.conj_mul'] at hk
    have hk' : (T : ℝ) * r + ‖φ (algebraMap (𝓞 E) E a)‖ ^ 2 = 1 := by exact_mod_cast hk
    have hc : ‖φ (c0 : E)‖ = r := by
      rw [hc0, hr, Complex.norm_real, Real.norm_of_nonneg hr0]
    have hn0 := norm_nonneg (φ (algebraMap (𝓞 E) E a))
    have hTr : 0 ≤ (T : ℝ) * r := mul_nonneg (by linarith) hr0
    refine ⟨?_, ?_, ?_⟩
    · rw [hc]
      nlinarith [sq_nonneg ‖φ (algebraMap (𝓞 E) E a)‖]
    · nlinarith
    · intro h0
      rw [hc] at h0
      rw [h0, mul_zero, zero_add] at hk'
      exact (pow_eq_one_iff_of_nonneg hn0 two_ne_zero).1 hk'
  have hne : Nonempty (E →+* ℂ) := by
    rw [← Fintype.card_pos_iff, NumberField.Embeddings.card E ℂ]
    exact Module.finrank_pos
  obtain ⟨φ0⟩ := hne
  have hc0z : (c0 : E) = 0 := by
    by_contra hc
    obtain ⟨m, hm, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one E ℂ hc
      c0.isIntegral_coe (fun φ => (hemb φ).1.le)
    have h1 := congrArg (fun t => ‖φ0 t‖) hpow
    simp only [map_pow, norm_pow, map_one, norm_one] at h1
    have h2 : ‖φ0 (c0 : E)‖ ^ m < 1 := pow_lt_one₀ (norm_nonneg _) (hemb φ0).1 hm.ne'
    linarith
  have hx0 : x = 0 := by
    obtain ⟨r, hr0, hr, hr0'⟩ := hdef φ0 x
    apply hr0'
    rw [← hc0, hc0z, map_zero] at hr
    exact_mod_cast hr.symm
  obtain ⟨m, hm, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ
    (x := algebraMap (𝓞 E) E a) (by exact a.isIntegral_coe)
    (fun φ => (hemb φ).2.2 (by rw [hc0z, map_zero, norm_zero]))
  refine ⟨a, ⟨m, hm, ?_⟩, ?_⟩
  · apply IsFractionRing.injective (𝓞 E) E
    rw [map_pow, hpow, map_one]
  · rw [hx0, zero_add]

theorem root_eq_one (P : Ideal (𝓞 E)) (T k : ℕ) (b : 𝓞 E) (hT : T.Prime) (hP : P.IsPrime)
    (hTP : (T : 𝓞 E) ∈ P) (hk : 0 < k) (hb : b ^ k = 1) (hb1 : b - 1 ∈ P) (hdeg : Module.finrank ℚ E < T - 1) : b = 1 := by
  by_contra hne
  have hfin : IsOfFinOrder b := isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, hb⟩
  have hd1 : orderOf b ≠ 1 := fun h1 => hne (orderOf_eq_one_iff.1 h1)
  obtain ⟨q, hq, e, he⟩ := Nat.exists_prime_and_dvd hd1
  have hη : IsPrimitiveRoot (b ^ e) q :=
    (IsPrimitiveRoot.orderOf b).pow hfin.orderOf_pos (by rw [he, mul_comm])
  have hbP : Ideal.Quotient.mk P b = 1 := by
    rw [← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq]
    exact hb1
  have hqP : (q : 𝓞 E) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h0 := congrArg (Ideal.Quotient.mk P) (hη.geom_sum_eq_zero hq.one_lt)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, map_pow, hbP] using h0
  have hTq : T = q := by
    by_contra hne'
    have hcop : Nat.Coprime T q := (Nat.coprime_primes hT hq).2 hne'
    have key : ((Nat.gcd T q : ℤ) : 𝓞 E) =
        (T : 𝓞 E) * (Nat.gcdA T q : 𝓞 E) + (q : 𝓞 E) * (Nat.gcdB T q : 𝓞 E) := by
      rw [Nat.gcd_eq_gcd_ab]
      push_cast
      ring
    rw [hcop.gcd_eq_one] at key
    have h1 : (1 : 𝓞 E) ∈ P := by
      have h := P.add_mem (P.mul_mem_right (Nat.gcdA T q : 𝓞 E) hTP)
        (P.mul_mem_right (Nat.gcdB T q : 𝓞 E) hqP)
      rw [← key] at h
      simpa using h
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 h1)
  have hηE : IsPrimitiveRoot (algebraMap (𝓞 E) E (b ^ e)) T := by
    rw [hTq]
    exact hη.map_of_injective (IsFractionRing.injective (𝓞 E) E)
  have hdg := minpoly.natDegree_le (A := ℚ) (algebraMap (𝓞 E) E (b ^ e))
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hηE hT.pos, Polynomial.natDegree_cyclotomic,
    Nat.totient_prime hT] at hdg
  omega

end Formalism.L2.GlobalTheoryTheory.Br
end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open NumberField Formalism.UG Matrix

variable {E : Type} [Field E] [NumberField E]

theorem sig_natInv (σ : E →+* E) (T : ℕ) : σ ((T : E)⁻¹) = (T : E)⁻¹ := by
  simp [map_inv₀, map_natCast]

theorem galois_image_integers (σ : E →+* E) (r : 𝓞 E) : σ (r : E) ∈ (algebraMap (𝓞 E) E).range :=
  ⟨⟨σ (r : E), (r.2).map σ.toIntAlgHom⟩, rfl⟩

theorem fix_orthogonal_vector {N N' : ℕ} (σ : E →+* E) (hσ : ∀ (φ : E →+* ℂ) (x : E), φ (σ x) = (starRingEnd ℂ) (φ x))
    (J : Matrix (Fin N) (Fin N) E) (J' : Matrix (Fin N') (Fin N') E)
    (hdef : ∀ (φ : E →+* ℂ) (x : Fin N → E), ∃ r : ℝ, 0 ≤ r ∧ φ (hform σ J x x) = r ∧ (r = 0 → x = 0))
    (ι : (Fin N' → E) →ₗ[E] (Fin N → E)) (z0 : Fin N → E)
    (hiso : ∀ x x', hform σ J (ι x) (ι x') = hform σ J' x x')
    (horth : ∀ x, hform σ J (ι x) z0 = 0 ∧ hform σ J z0 (ι x) = 0)
    (hspan : ∀ y, ∃ (x : Fin N' → E) (s : E), y = ι x + s • z0)
    (T : ℕ) (hTp : T.Prime) (hdeg : Module.finrank ℚ E < T - 1) (hzz : hform σ J z0 z0 = T)
    (L1 L2 : Submodule (𝓞 E) (Fin N' → E))
    (hsd2 : (∀ y, (∀ x ∈ L2, hform σ J' x y ∈ (algebraMap (𝓞 E) E).range) → y ∈ L2) ∧
      ∀ x ∈ L2, ∀ y ∈ L2, hform σ J' x y ∈ (algebraMap (𝓞 E) E).range)
    (γ : Matrix (Fin N) (Fin N) E) (hγ : ∀ x y, hform σ J (γ *ᵥ x) (γ *ᵥ y) = hform σ J x y)
    (hlat : Formalism.L2.Forms.mulLat γ (L1.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0}) =
      L2.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0})
    (P : Ideal (𝓞 E)) (hP : P.IsPrime) (hTP : (T : 𝓞 E) ∈ P)
    (hres : ∀ y : Fin N → E, (∀ w ∈ L1.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0},
        hform σ J w y ∈ (algebraMap (𝓞 E) E).range) →
      ∀ r r' : 𝓞 E, (r : E) = hform σ J z0 y → (r' : E) = hform σ J z0 (γ *ᵥ y) → r - r' ∈ P) :
    γ *ᵥ z0 = z0 := by
  have hT1 : 1 < T := hTp.one_lt
  have hT0 : (T : E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  set z' : Fin N → E := (T : E)⁻¹ • z0 with hz'
  have hz0 : z0 = (T : E) • z' := by rw [hz', smul_smul, mul_inv_cancel₀ hT0, one_smul]

  have hzz' : (T : E) * hform σ J z' z' = 1 := by
    rw [hz', hform_smul_left, hform_smul_right, hzz, sig_natInv]; field_simp
  have hz0z' : hform σ J z0 z' = 1 := by
    rw [hz', hform_smul_right, hzz]; field_simp

  have memL : ∀ (L : Submodule (𝓞 E) (Fin N' → E)) w, w ∈ L.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0} →
      ∃ l ∈ L, ∃ r : 𝓞 E, w = ι l + (r : E) • z0 := by
    intro L w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
    obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.1 ha
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hb
    exact ⟨l, hl, r, by rw [← algebraMap_smul E r z0]; rfl⟩

  have hd1 : ∀ w ∈ L1.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0},
      hform σ J w z' ∈ (algebraMap (𝓞 E) E).range := by
    intro w hw
    obtain ⟨l, _, r, rfl⟩ := memL L1 w hw
    rw [hform_add_left, hform_smul_left, hz', hform_smul_right, hform_smul_right, (horth l).1, hzz]
    have : (T : E)⁻¹ * 0 + σ (r : E) * ((T : E)⁻¹ * (T : E)) = σ (r : E) := by
      rw [mul_zero, zero_add, inv_mul_cancel₀ hT0, mul_one]
    rw [this]; exact galois_image_integers σ r

  have hd2 : ∀ w ∈ L2.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0},
      hform σ J w (γ *ᵥ z') ∈ (algebraMap (𝓞 E) E).range := by
    intro w hw
    rw [← hlat] at hw
    obtain ⟨w1, hw1, rfl⟩ := Submodule.mem_map.1 hw
    show hform σ J (γ *ᵥ w1) (γ *ᵥ z') ∈ _
    rw [hγ]; exact hd1 w1 hw1

  obtain ⟨y1, s, hys⟩ := hspan (γ *ᵥ z')
  have hy1 : y1 ∈ L2 := by
    apply hsd2.1
    intro x hx
    have hmem : ι x ∈ L2.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0} :=
      Submodule.mem_sup_left (Submodule.mem_map.2 ⟨x, hx, rfl⟩)
    have := hd2 _ hmem
    rwa [hys, hform_add_right, hform_smul_right, (horth x).1, mul_zero, add_zero, hiso] at this
  obtain ⟨t, ht⟩ : ∃ t : 𝓞 E, (t : E) = s * T := by
    have hmem : z0 ∈ L2.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self z0)
    have := hd2 _ hmem
    rw [hys, hform_add_right, hform_smul_right, (horth y1).2, hzz, zero_add] at this
    obtain ⟨t, ht⟩ := this
    exact ⟨t, ht⟩
  have hyt : γ *ᵥ z' = ι y1 + (t : E) • z' := by
    rw [hys, ht, hz0, smul_smul]

  have hγzz : (T : E) * hform σ J (γ *ᵥ z') (γ *ᵥ z') = 1 := by rw [hγ]; exact hzz'
  have hmemy : γ *ᵥ z' ∈ L2.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z'} := by
    rw [hyt]
    refine Submodule.add_mem_sup (Submodule.mem_map.2 ⟨y1, hy1, rfl⟩) ?_
    have h := Submodule.smul_mem (Submodule.span (𝓞 E) {z'}) t (Submodule.mem_span_singleton_self z')
    rw [← algebraMap_smul E t z'] at h
    exact h
  have hint : ∀ x ∈ L2.map (ι.restrictScalars (𝓞 E)), ∃ a : 𝓞 E, (a : E) = hform σ J x x := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨a, ha⟩ := hsd2.2 l hl l hl
    refine ⟨a, ?_⟩
    show (a : E) = hform σ J (ι l) (ι l)
    rw [hiso]; exact ha
  have hzL : ∀ x ∈ L2.map (ι.restrictScalars (𝓞 E)), hform σ J x z' = 0 ∧ hform σ J z' x = 0 := by
    intro x hx
    obtain ⟨l, _, rfl⟩ := Submodule.mem_map.1 hx
    refine ⟨?_, ?_⟩
    · show hform σ J (ι l) z' = 0
      rw [hz', hform_smul_right, (horth l).1, mul_zero]
    · show hform σ J z' (ι l) = 0
      rw [hz', hform_smul_left, (horth l).2, mul_zero]
  obtain ⟨b, ⟨k, hk, hbk⟩, hb⟩ :=
    length_inverse_bound σ hσ J hdef (L2.map (ι.restrictScalars (𝓞 E))) hint z' hzL T hT1 hzz' (γ *ᵥ z') hmemy hγzz

  have hbP : b - 1 ∈ P := by
    have h1 := hres z' hd1 1 b (by rw [hz0z']; simp) (by rw [hb, hform_smul_right, hz0z', mul_one])
    have : b - 1 = -(1 - b) := by ring
    rw [this]; exact P.neg_mem h1
  have hb1 : b = 1 := root_eq_one P T k b hTp hP hTP hk hbk hbP hdeg
  rw [hb1] at hb
  have : γ *ᵥ z' = z' := by rw [hb]; simp
  rw [hz0, Matrix.mulVec_smul, this]

theorem fix_restrict {N N' : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (J' : Matrix (Fin N') (Fin N') E)
    (ι : (Fin N' → E) →ₗ[E] (Fin N → E)) (hinj : Function.Injective ι) (z0 : Fin N → E)
    (hiso : ∀ x x', hform σ J (ι x) (ι x') = hform σ J' x x')
    (horth : ∀ x, hform σ J (ι x) z0 = 0 ∧ hform σ J z0 (ι x) = 0)
    (hspan : ∀ y, ∃ (x : Fin N' → E) (s : E), y = ι x + s • z0)
    (hzz : hform σ J z0 z0 ≠ 0)
    (γ : Matrix (Fin N) (Fin N) E) (hγ : ∀ x y, hform σ J (γ *ᵥ x) (γ *ᵥ y) = hform σ J x y) (hfix : γ *ᵥ z0 = z0) :
    ∃ δ : Matrix (Fin N') (Fin N') E, (∀ x, γ *ᵥ ι x = ι (δ *ᵥ x)) ∧
      ∀ x y, hform σ J' (δ *ᵥ x) (δ *ᵥ y) = hform σ J' x y := by
  have hrange : ∀ x, γ *ᵥ ι x ∈ LinearMap.range ι := by
    intro x
    obtain ⟨x', s, hs⟩ := hspan (γ *ᵥ ι x)
    have h0 : hform σ J (γ *ᵥ ι x) z0 = 0 := by
      conv_lhs => rw [← hfix]
      rw [hγ]; exact (horth x).1
    rw [hs, hform_add_left, hform_smul_left, (horth x').1, zero_add] at h0
    have hs0 : σ s = 0 := (mul_eq_zero.1 h0).resolve_right hzz
    have : s = 0 := (map_eq_zero σ).1 hs0
    rw [hs, this, zero_smul, add_zero]; exact ⟨x', rfl⟩
  let e := LinearEquiv.ofInjective ι hinj
  let g : (Fin N' → E) →ₗ[E] LinearMap.range ι :=
    LinearMap.codRestrict (LinearMap.range ι) ((Matrix.mulVecLin γ).comp ι) hrange
  let f : (Fin N' → E) →ₗ[E] (Fin N' → E) := e.symm.toLinearMap.comp g
  have hf : ∀ x, ι (f x) = γ *ᵥ ι x := by
    intro x
    have h1 : (e (f x) : Fin N → E) = ι (f x) := rfl
    rw [← h1]
    show ((e (e.symm (g x)) : LinearMap.range ι) : Fin N → E) = _
    rw [LinearEquiv.apply_symm_apply]; rfl
  refine ⟨LinearMap.toMatrix' f, fun x => ?_, fun x y => ?_⟩
  · rw [LinearMap.toMatrix'_mulVec, hf]
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, ← hiso, hf, hf, hγ, hiso]

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.BlockActions.ExtendOneMulVecSingleLast
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Matrix
attribute [default_instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {R : Type} [CommRing R] {n : ℕ}

def blk1 (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  (fromBlocks g 0 0 (1 : Matrix (Fin 1) (Fin 1) R)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def inclusionAlt : Matrix (Fin (n + 1)) (Fin n) R := of fun a b => if a = Fin.castSucc b then 1 else 0

theorem extendOne_mul_inclusion (g : Matrix (Fin n) (Fin n) R) : blk1 g * inclusionAlt = inclusionAlt * g := by
  ext i j
  simp only [Matrix.mul_apply, inclusionAlt, of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  induction i using Fin.lastCases with
  | last =>
    have hne : ∀ x : Fin n, ¬ (Fin.last n = Fin.castSucc x) := fun x hx => (Fin.castSucc_lt_last x).ne' hx
    simp [blk1, hne, finSumFinEquiv_symm_last]
  | cast i =>
    simp [blk1, Fin.castSucc_inj]

theorem extendOne_mulVec_single_last (g : Matrix (Fin n) (Fin n) R) : blk1 g *ᵥ Pi.single (Fin.last n) 1 = Pi.single (Fin.last n) 1 := by
  ext i
  rw [Matrix.mulVec_single_one]
  induction i using Fin.lastCases with
  | last => simp [blk1]
  | cast i => simp [blk1, Fin.castSucc_ne_last]

theorem det_extendOne (g : Matrix (Fin n) (Fin n) R) : (blk1 g).det = g.det := by
  simp [blk1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

def extM {E : Type} [Field E] (φ : E →+* R) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (g : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  B.map φ * blk1 g * (B.map φ)⁻¹

theorem eN_map {E : Type} [Field E] (φ : E →+* R) : (inclusionAlt : Matrix (Fin (n + 1)) (Fin n) E).map φ = inclusionAlt := by
  ext a b
  simp only [inclusionAlt, map_apply, of_apply]
  split_ifs <;> simp

theorem extM_spec {E : Type} [Field E] (φ : E →+* R) (A : Matrix (Fin (n + 1)) (Fin n) E) (z : Fin (n + 1) → E)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hBA : B * inclusionAlt = A) (hBz : B *ᵥ Pi.single (Fin.last n) 1 = z) (hB : IsUnit B.det)
    (g : Matrix (Fin n) (Fin n) R) :
    extM φ B g * A.map φ = A.map φ * g ∧ extM φ B g *ᵥ (fun a => φ (z a)) = (fun a => φ (z a)) ∧
      (IsUnit g.det → IsUnit (extM φ B g).det) := by
  have hBu : IsUnit (B.map φ).det := by
    have e1 : (B.map φ).det = φ B.det := (RingHom.map_det φ B).symm
    rw [e1]
    exact hB.map φ
  have hinv : (B.map φ)⁻¹ * B.map φ = 1 := Matrix.nonsing_inv_mul _ hBu
  have hA : A.map φ = B.map φ * inclusionAlt := by
    rw [← hBA, Matrix.map_mul, eN_map]
  have hz : (fun a => φ (z a)) = B.map φ *ᵥ Pi.single (Fin.last n) 1 := by
    rw [← hBz]
    ext a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    by_cases hk : k = Fin.last n
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  refine ⟨?_, ?_, ?_⟩
  · rw [hA, extM, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (B.map φ)⁻¹, hinv,
      Matrix.one_mul, extendOne_mul_inclusion, ← Matrix.mul_assoc]
  · rw [hz, extM, Matrix.mulVec_mulVec, Matrix.mul_assoc _ _ (B.map φ), hinv, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, extendOne_mulVec_single_last]
  · intro hg
    rw [extM, Matrix.det_mul, Matrix.det_mul]
    refine (hBu.mul ?_).mul ?_
    · rw [det_extendOne]; exact hg
    · exact Matrix.isUnit_nonsing_inv_det _ hBu

theorem ext_general {E : Type} [Field E] (φ : E →+* R) {N : ℕ} (hN : n + 1 = N) (A : Matrix (Fin N) (Fin n) E) (z : Fin N → E)
    (hB : IsUnit (Matrix.of (fun a (b : Fin N) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a)).det)
    (g : Matrix (Fin n) (Fin n) R) :
    ∃ G : Matrix (Fin N) (Fin N) R, G * A.map φ = A.map φ * g ∧ G *ᵥ (fun a => φ (z a)) = (fun a => φ (z a)) ∧
      (IsUnit g.det → IsUnit G.det) := by
  subst hN
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
    Matrix.of (fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) with hBdef
  have hBA : B * inclusionAlt = A := by
    ext a b
    change (∑ k : Fin (n + 1), B a k * inclusionAlt k b) = A a b
    simp only [hBdef, inclusionAlt, of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Fin.coe_castSucc, b.isLt, dif_pos]
  have hBz : B *ᵥ Pi.single (Fin.last n) 1 = z := by
    ext a
    rw [Matrix.mulVec_single_one]
    simp [hBdef]
  exact ⟨extM φ B g, extM_spec φ A z B hBA hBz hB g⟩

end Formalism.L2.GlobalTheoryTheory.Br
end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

structure CrdFacts (D : D7) : Prop where
  conj : ∀ (φ : D.host.E →+* ℂ) (x : D.host.E), φ ((sigD D : D.host.E →+* D.host.E) x) = (starRingEnd ℂ) (φ x)
  defN : ∀ (φ : D.host.E →+* ℂ) (x : Fin (D.R.N D.R.m) → D.host.E), ∃ r : ℝ, 0 ≤ r ∧
    φ (hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) x x) = r ∧ (r = 0 → x = 0)
  iso : ∀ x x', hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (iXc D x) (iXc D x') =
    hform (sigD D : D.host.E →+* D.host.E) (gramP D) x x'
  orth : ∀ x, hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (iXc D x) (zc D) = 0 ∧
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (zc D) (iXc D x) = 0
  span : ∀ y, ∃ (x : Fin (D.R.N D.R.m - 1) → D.host.E) (s : D.host.E), y = iXc D x + s • zc D

section Unit

variable {E : Type} [Field E] {n : ℕ}

theorem hform_eq_dot (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hform σ J x y = dotProduct (fun i => σ (x i)) (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem hform_UJ (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) E) (hg : cT σ g * J * g = J)
    (x y : Fin n → E) : hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ J x y := by
  have h1 : (fun i => σ ((g *ᵥ x) i)) = (g.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i; simp [mulVec, dotProduct, map_sum]
  have key : ∀ (A : Matrix (Fin n) (Fin n) E) (v w : Fin n → E), (A *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (Aᵀ *ᵥ w) := by
    intro A v w; rw [dotProduct_mulVec, vecMul_transpose]
  rw [hform_eq_dot, hform_eq_dot, h1, key, mulVec_mulVec, mulVec_mulVec]
  congr 2

end Unit

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem ga_herm (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (x y : Fin (D.R.N D.R.m) → D.host.E) :
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) ((Tf.til.ga c).1.1 *ᵥ x) ((Tf.til.ga c).1.1 *ᵥ y) =
      hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) x y :=
  hform_UJ _ _ _ (Tf.til.ga c).2 x y

section Glue

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem mulLat_mulLat {E : Type} [Field E] [NumberField E] {n : ℕ} (A B : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) : mulLat A (mulLat B L) = mulLat (A * B) L := by
  unfold mulLat
  rw [← Submodule.map_comp]
  congr 1
  ext x i
  simp

theorem fv_pr_congr (Tf : FormsTiedSym D u Ch chOf) (v : (D.mem u).A.vT) (a b : (D.mem u).C.cls D.R.m) (hab : a = b)
    (x : Fin (D.R.N D.R.m) → D.host.E) (hxa : x ∈ Ld D u D.R.m le_rfl a) (hxb : x ∈ Ld D u D.R.m le_rfl b) :
    (D.fm u).fv D.R.m v a ((Tf.lv D.R.m le_rfl).pr v a ⟨x, hxa⟩) =
      (D.fm u).fv D.R.m v b ((Tf.lv D.R.m le_rfl).pr v b ⟨x, hxb⟩) := by
  subst hab; rfl

theorem T_mem_Pv (Tf : FormsTiedSym D u Ch chOf) (v : (D.mem u).A.vT) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ Tf.atT.Pv v := by
  let pb : 𝓞 D.host.E := ⟨D.host.conj (Tf.atT.piU : D.host.E), (Tf.atT.piU.2).map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom⟩
  have hT : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) = Tf.atT.piU * pb := by
    apply RingOfIntegers.ext
    have e1 : ((Tf.atT.piU * pb : 𝓞 D.host.E) : D.host.E) = (Tf.atT.piU : D.host.E) * (pb : D.host.E) := rfl
    have e2 : ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) : D.host.E) = (((D.mem u).A.T : ℕ) : D.host.E) := by simp
    rw [e1, e2, ← Tf.atT.piU_norm]; rfl
  rw [hT]
  show Tf.atT.res v (Tf.atT.piU * pb) = 0
  rw [map_mul, Tf.atT.res_pi, zero_mul]

theorem til_eq_fix (Tf : FormsTiedSym D u Ch chOf) (hC : CrdFacts D)
    (hSD : ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : Module.finrank ℚ D.host.E < (D.mem u).A.T - 1) (v : (D.mem u).A.vT)
    (c c' : (D.fm u).clsP) (h : (D.fm u).til c = (D.fm u).til c') :
    ((Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1) *ᵥ Tf.til.z0 = Tf.til.z0 := by
  have hTp : ((D.mem u).A.T : ℕ).Prime := (D.mem u).A.T_prime
  set σ : D.host.E →+* D.host.E := (sigD D : D.host.E →+* D.host.E) with hσdef
  set J := gramN D D.R.m le_rfl with hJ
  set z0 := Tf.til.z0 with hz0
  set g1 := (Tf.til.ga c).1.1 with hg1
  set g2 := (Tf.til.ga c').1.1 with hg2
  set gi := ((Tf.til.ga c)⁻¹).1.1 with hgi
  have hgi1 : gi * g1 = 1 := by simp [hgi, hg1]
  have hg1i : g1 * gi = 1 := by simp [hgi, hg1]
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  rw [← hz0] at ha
  have hzz : hform σ J z0 z0 = (((D.mem u).A.T : ℕ) : D.host.E) := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
  have ha0 : a ≠ 0 := by
    intro h0
    have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
    rw [ha, h0, zero_smul] at hzz
    apply hT0; rw [← hzz]; simp [hform]
  have horth : ∀ x, hform σ J (iXc D x) z0 = 0 ∧ hform σ J z0 (iXc D x) = 0 := fun x => by
    rw [ha, hform_smul_right, hform_smul_left, (hC.orth x).1, (hC.orth x).2]; simp
  have hspan : ∀ y, ∃ (x : Fin (D.R.N D.R.m - 1) → D.host.E) (s : D.host.E), y = iXc D x + s • z0 := fun y => by
    obtain ⟨x, s, hy⟩ := hC.span y
    exact ⟨x, s / a, by rw [hy, ha, smul_smul, div_mul_cancel₀ s ha0]⟩
  have hUgi : cT σ gi * J * gi = J := ((Tf.til.ga c)⁻¹).2
  have hγ : ∀ x y, hform σ J ((g2 * gi) *ᵥ x) ((g2 * gi) *ᵥ y) = hform σ J x y := fun x y => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, ga_herm Tf c', hform_UJ σ J gi hUgi]
  have hlat : mulLat (g2 * gi) ((Tf.clsP.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0}) =
      (Tf.clsP.lat c').map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0} := by
    rw [← Tf.til.til_lat c, ← Tf.til.til_lat c', mulLat_mulLat, Matrix.mul_assoc, hgi1, Matrix.mul_one, h]
  have hres : ∀ y : Fin (D.R.N D.R.m) → D.host.E,
      (∀ w ∈ (Tf.clsP.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0},
        hform σ J w y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) →
      ∀ r r' : 𝓞 D.host.E, (r : D.host.E) = hform σ J z0 y → (r' : D.host.E) = hform σ J z0 ((g2 * gi) *ᵥ y) →
        r - r' ∈ Tf.atT.Pv v := by
    intro y hy r r' hr hr'
    have hxy : g1 *ᵥ (gi *ᵥ y) = y := by rw [mulVec_mulVec, hg1i, one_mulVec]
    have hxa : gi *ᵥ y ∈ Ld D u D.R.m le_rfl ((D.fm u).til c) := by
      apply Submodule.subset_span
      intro l hl
      have hl' : g1 *ᵥ l ∈ (Tf.clsP.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0} := by
        rw [← Tf.til.til_lat c]; exact Submodule.mem_map.2 ⟨l, hl, rfl⟩
      have := hy _ hl'
      rw [← hxy, ga_herm Tf c] at this
      exact this
    have hxb : gi *ᵥ y ∈ Ld D u D.R.m le_rfl ((D.fm u).til c') := h ▸ hxa
    have e1 := Tf.til.til_fv v c ⟨gi *ᵥ y, hxa⟩ r (by rw [hr]; show _ = hform σ J z0 (g1 *ᵥ (gi *ᵥ y)); rw [hxy])
    have e2 := Tf.til.til_fv v c' ⟨gi *ᵥ y, hxb⟩ r' (by rw [hr', ← mulVec_mulVec])
    rw [fv_pr_congr Tf v _ _ h _ hxa hxb, e2] at e1
    show Tf.atT.res v (r - r') = 0
    rw [map_sub, e1, sub_self]
  exact fix_orthogonal_vector σ hC.conj J (gramP D) hC.defN (iXc D) z0 hC.iso horth hspan _ hTp hdeg hzz
    (Tf.clsP.lat c) (Tf.clsP.lat c')
    ⟨fun y hy => by
      have : y ∈ dualSet σ (gramP D) (Tf.clsP.lat c') := fun x hx => hy x hx
      rw [hSD c'] at this; exact this,
     fun x hx y hy => by
      have : y ∈ dualSet σ (gramP D) (Tf.clsP.lat c') := by rw [hSD c']; exact hy
      exact this x hx⟩
    (g2 * gi) hγ hlat (Tf.atT.Pv v) inferInstance (T_mem_Pv Tf v) hres

theorem til_eq_ext (Tf : FormsTiedSym D u Ch chOf) (hC : CrdFacts D)
    (hSD : ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : Module.finrank ℚ D.host.E < (D.mem u).A.T - 1) (v : (D.mem u).A.vT)
    (c c' : (D.fm u).clsP) (h : (D.fm u).til c = (D.fm u).til c') :
    ∃ δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E,
      IsExt D Tf.til.z0 (RingHom.id D.host.E) δ ((Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1) ∧
      ∀ x y, hform (sigD D : D.host.E →+* D.host.E) (gramP D) (δ *ᵥ x) (δ *ᵥ y) =
        hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y := by
  have hTp : ((D.mem u).A.T : ℕ).Prime := (D.mem u).A.T_prime
  have hfix := til_eq_fix Tf hC hSD hdeg v c c' h
  set σ : D.host.E →+* D.host.E := (sigD D : D.host.E →+* D.host.E) with hσdef
  set J := gramN D D.R.m le_rfl with hJ
  set z0 := Tf.til.z0 with hz0
  set γ := (Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1 with hγdef
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  rw [← hz0] at ha
  have hzz : hform σ J z0 z0 = (((D.mem u).A.T : ℕ) : D.host.E) := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  have ha0 : a ≠ 0 := by
    intro h0
    have hzz' := hzz
    rw [ha, h0, zero_smul] at hzz'
    apply hT0; rw [← hzz']; simp [hform]
  have horth : ∀ x, hform σ J (iXc D x) z0 = 0 ∧ hform σ J z0 (iXc D x) = 0 := fun x => by
    rw [ha, hform_smul_right, hform_smul_left, (hC.orth x).1, (hC.orth x).2]; simp
  have hspan : ∀ y, ∃ (x : Fin (D.R.N D.R.m - 1) → D.host.E) (s : D.host.E), y = iXc D x + s • z0 := fun y => by
    obtain ⟨x, s, hy⟩ := hC.span y
    exact ⟨x, s / a, by rw [hy, ha, smul_smul, div_mul_cancel₀ s ha0]⟩
  have hUgi : cT σ ((Tf.til.ga c)⁻¹).1.1 * J * ((Tf.til.ga c)⁻¹).1.1 = J := ((Tf.til.ga c)⁻¹).2
  have hγ : ∀ x y, hform σ J (γ *ᵥ x) (γ *ᵥ y) = hform σ J x y := fun x y => by
    rw [hγdef, ← mulVec_mulVec, ← mulVec_mulVec, ga_herm Tf c', hform_UJ σ J _ hUgi]
  obtain ⟨δ, hδ, hδi⟩ := fix_restrict σ J (gramP D) (iXc D) (iXc_injective D) z0 hC.iso horth hspan
    (by rw [hzz]; exact hT0) γ hγ hfix
  refine ⟨δ, ⟨?_, ?_⟩, hδi⟩
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLin'_apply, ← mulVec_mulVec]
    show γ *ᵥ ((iXm D).map (RingHom.id D.host.E) *ᵥ x) = (iXm D).map (RingHom.id D.host.E) *ᵥ (δ *ᵥ x)
    have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
    rw [hm, iXm, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hδ]
  · have : (fun a => (RingHom.id D.host.E) (z0 a)) = z0 := rfl
    rw [this]; exact hfix

theorem til_ext (Tf : FormsTiedSym D u Ch chOf) {R : Type} [CommRing R] (φ : D.host.E →+* R)
    (g' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) R) :
    ∃ g : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) R, IsExt D Tf.til.z0 φ g' g ∧ (IsUnit g'.det → IsUnit g.det) := by
  obtain ⟨G, h1, h2, h3⟩ := ext_general φ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (iXm D)
    (fun a => Tf.til.z0 a / ((D.mem u).A.T : D.host.E)) (by exact bZ_isUnitS Tf) g'
  refine ⟨G, ⟨h1, ?_⟩, h3⟩
  have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have hz : (fun a => φ (Tf.til.z0 a)) = φ ((D.mem u).A.T : D.host.E) • (fun a => φ (Tf.til.z0 a / ((D.mem u).A.T : D.host.E))) := by
    funext a
    rw [Pi.smul_apply, smul_eq_mul, ← map_mul, mul_div_cancel₀ _ hT]
  rw [hz, mulVec_smul, h2]

end Glue

end Formalism.L2.GlobalTheoryTheory.Br
