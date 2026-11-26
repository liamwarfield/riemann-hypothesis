module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQuotBijective
open Polynomial

namespace GlobalTheory
namespace DedekindCodimG

variable {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

end DedekindCodimG
end GlobalTheory

namespace GlobalTheory
namespace DedekindCodimG

variable {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

private theorem isArtinianRing_quotient_of_ne_bot_of_isDedekindDomain (A : Type) [CommRing A] [IsDedekindDomain A]
    (I : Ideal A) (hI : I ≠ ⊥) : IsArtinianRing (A ⧸ I) := by
  have : Ring.KrullDimLE 0 (A ⧸ I) := by
    refine Ring.KrullDimLE.mk₀ fun Q hQ => ?_
    have hle : I ≤ Q.comap (Ideal.Quotient.mk I) := fun a ha => by
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha, Q.zero_mem]
    have hne : Q.comap (Ideal.Quotient.mk I) ≠ ⊥ := fun h => hI (le_bot_iff.mp (h ▸ hle))
    have hmax := (Ideal.IsPrime.comap (Ideal.Quotient.mk I) (hK := hQ)).isMaximal hne
    have := hmax.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using hle)
    rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at this
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

private theorem module_finite_quotient_of_ne_bot_of_isDedekindDomain (k A : Type) [Field k] [CommRing A] [IsDedekindDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (I : Ideal A) (hI : I ≠ ⊥) :
    Module.Finite k (A ⧸ I) := by
  haveI := isArtinianRing_quotient_of_ne_bot_of_isDedekindDomain A I hI
  exact Module.finite_of_isArtinianRing k (A ⧸ I)

private theorem algebraMap_quotient_bijective_of_isMaximal_of_isAlgClosed (k A : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (P : Ideal A) [P.IsMaximal] :
    Function.Bijective (algebraMap k (A ⧸ P)) := by
  letI := Ideal.Quotient.field P
  haveI : Module.Finite k (A ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ P)
  exact ⟨(algebraMap k (A ⧸ P)).injective, IsSepClosed.algebraMap_surjective k (A ⧸ P)⟩

private theorem mul_sup_span_singleton_eq_of_mem_of_not_mem_mul (A : Type) [CommRing A] [IsDedekindDomain A]
    (I P : Ideal A) (hI : I ≠ ⊥) (hP : P.IsMaximal) (hP0 : P ≠ ⊥) {x : A} (hxI : x ∈ I)
    (hxIP : x ∉ I * P) : I * P ⊔ Ideal.span {x} = I := by
  have hle : I * P ⊔ Ideal.span {x} ≤ I :=
    sup_le (Ideal.mul_le_inf.trans inf_le_left) ((Ideal.span_singleton_le_iff_mem I).mpr hxI)
  obtain ⟨M, hM⟩ := Ideal.dvd_iff_le.mpr hle
  have hMP : M ∣ P := by
    have : I * M ∣ I * P := Ideal.dvd_iff_le.mpr (hM ▸ le_sup_left)
    exact (mul_dvd_mul_iff_left hI).mp this
  obtain ⟨N, hN⟩ := hMP
  rcases (Ideal.prime_of_isPrime hP0 hP.isPrime).irreducible.isUnit_or_isUnit hN with hu | hu
  · rw [hM, Ideal.isUnit_iff.mp hu, Ideal.mul_top]
  · rw [Ideal.isUnit_iff.mp hu, Ideal.mul_top] at hN
    subst hN
    refine absurd ?_ hxIP
    rw [← hM]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)

private theorem exists_sub_algebraMap_mem_of_isMaximal_of_isAlgClosed (k A : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (P : Ideal A) [P.IsMaximal] (r : A) :
    ∃ c : k, r - algebraMap k A c ∈ P := by
  obtain ⟨c, hc⟩ := (algebraMap_quotient_bijective_of_isMaximal_of_isAlgClosed k A P).2 (Ideal.Quotient.mk P r)
  refine ⟨c, Ideal.Quotient.eq.mp ?_⟩
  rw [Ideal.Quotient.mk_algebraMap, hc]

private theorem finrank_quotient_mul_maximal_eq_finrank_add_one (k A : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (I P : Ideal A)
    (hI : I ≠ ⊥) (hP : P.IsMaximal) (hP0 : P ≠ ⊥) :
    Module.finrank k (A ⧸ I * P) = Module.finrank k (A ⧸ I) + 1 := by
  haveI := hP
  haveI := module_finite_quotient_of_ne_bot_of_isDedekindDomain k A (I * P) (mul_ne_zero hI hP0)
  haveI := module_finite_quotient_of_ne_bot_of_isDedekindDomain k A I hI
  obtain ⟨x, hxI, hxIP⟩ : ∃ x ∈ I, x ∉ I * P := by
    by_contra! h
    have hIP : I * P = I * ⊤ := by
      rw [Ideal.mul_top]
      exact le_antisymm (Ideal.mul_le_inf.trans inf_le_left) fun y hy => h y hy
    exact hP.ne_top (mul_left_cancel₀ hI hIP)
  let f : (A ⧸ I * P) →ₗ[k] (A ⧸ I) :=
    (Ideal.Quotient.factorₐ k (Ideal.mul_le_inf.trans inf_le_left : I * P ≤ I)).toLinearMap
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have hker : LinearMap.ker f = k ∙ Ideal.Quotient.mk (I * P) x := by
    apply le_antisymm
    · intro z hz
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      have haI : a ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp hz)
      rw [← mul_sup_span_singleton_eq_of_mem_of_not_mem_mul A I P hI hP hP0 hxI hxIP] at haI
      obtain ⟨b, hb, y, hy, rfl⟩ := Submodule.mem_sup.mp haI
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_of_isMaximal_of_isAlgClosed k A P r
      refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
      rw [← Ideal.Quotient.mkₐ_eq_mk k, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq,
        Algebra.smul_def]
      have h1 : x * (r - algebraMap k A c) ∈ I * P := Ideal.mul_mem_mul hxI hc
      have h2 : algebraMap k A c * x - (b + r * x) = -(b + x * (r - algebraMap k A c)) := by ring
      rw [h2]
      exact (I * P).neg_mem ((I * P).add_mem hb h1)
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hxI
  have hx0 : Ideal.Quotient.mk (I * P) x ≠ 0 := fun h => hxIP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker, finrank_span_singleton hx0] at h
  exact h.symm

theorem _root_.GlobalTheory.DedekindCodimG.dedekind_finiteType_codim (k A : Type) [Field k]
    [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    (∀ (I : Ideal A), I ≠ ⊥ → Module.Finite k (A ⧸ I)) ∧
    (∀ (P : Ideal A), P.IsMaximal →
      Module.finrank k (A ⧸ P) = (1 : ℕ) ∧ ∃ (φ : A →ₐ[k] k), ∀ (u : A), u ∈ P ↔ (φ : A → k) u = (0 : k)) ∧
    (∀ (I J : Ideal A), I ≠ ⊥ → J ≠ ⊥ →
      Module.finrank k (A ⧸ I * J) = Module.finrank k (A ⧸ I) + Module.finrank k (A ⧸ J)) ∧
    ∀ (I J : Ideal A), I ≠ ⊥ → I ≤ J → Module.finrank k (A ⧸ I) ≤ Module.finrank k (A ⧸ J) →
      I = J := by
  refine ⟨fun I hI => module_finite_quotient_of_ne_bot_of_isDedekindDomain k A I hI, ?_, ?_, ?_⟩
  · intro P hP
    haveI := hP
    let e : k ≃ₐ[k] A ⧸ P :=
      AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ P)) (algebraMap_quotient_bijective_of_isMaximal_of_isAlgClosed k A P)
    refine ⟨by rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self],
      e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k P), fun u => ?_⟩
    change u ∈ P ↔ e.symm (Ideal.Quotient.mk P u) = 0
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  · intro I J hI hJ
    induction J using UniqueFactorizationMonoid.induction_on_prime generalizing I with
    | h₁ => exact absurd rfl hJ
    | h₂ u hu =>
      rw [Ideal.isUnit_iff.mp hu, Ideal.mul_top]
      haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      rw [Module.finrank_zero_of_subsingleton (M := A ⧸ (⊤ : Ideal A)), add_zero]
    | h₃ a p ha hp ih =>
      have hp0 : p ≠ ⊥ := hp.ne_zero
      have hpmax : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp0
      have ha' : a ≠ ⊥ := ha
      rw [show I * (p * a) = I * a * p by ring, mul_comm p a,
        finrank_quotient_mul_maximal_eq_finrank_add_one k A (I * a) p (mul_ne_zero hI ha') hpmax hp0,
        finrank_quotient_mul_maximal_eq_finrank_add_one k A a p ha' hpmax hp0, ih I hI ha']
      ring
  · intro I J hI hIJ hle
    have hJ : J ≠ ⊥ := fun h => hI (le_bot_iff.mp (h ▸ hIJ))
    haveI := module_finite_quotient_of_ne_bot_of_isDedekindDomain k A I hI
    haveI := module_finite_quotient_of_ne_bot_of_isDedekindDomain k A J hJ
    let f : (A ⧸ I) →ₗ[k] (A ⧸ J) := (Ideal.Quotient.factorₐ k hIJ).toLinearMap
    have hsurj : Function.Surjective f := by
      intro y
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨Ideal.Quotient.mk _ a, rfl⟩
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h
    have hker : LinearMap.ker f = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    refine le_antisymm hIJ fun a ha => ?_
    have hmem : Ideal.Quotient.mk I a ∈ LinearMap.ker f :=
      LinearMap.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
    rw [hker, Submodule.mem_bot] at hmem
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmem

end DedekindCodimG
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeIntegerInIdeal
open NumberField IsDedekindDomain

namespace GlobalTheory.NormCoprime

theorem coprime_absNorm_of_sup {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (h : I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} = ⊤) : Nat.Coprime (Ideal.absNorm I) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let _ : Fintype (𝓞 K ⧸ I) := Fintype.ofFinite _
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] at hdvd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hdvd
  have h1 : (1 : 𝓞 K) ∈ I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} := by rw [h]; trivial
  obtain ⟨i, hi, r, hr, hir⟩ := Submodule.mem_sup.mp h1
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have hpx : (p : ℕ) • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  have hq : (Ideal.Quotient.mk I i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hi
  have hx0 : x = 0 := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have e0 : y = i * y + t * (((p : ℕ) : 𝓞 K) * y) := by linear_combination (-(y)) * hir
    have e : Ideal.Quotient.mk I y = Ideal.Quotient.mk I i * Ideal.Quotient.mk I y +
        Ideal.Quotient.mk I t * ((p : ℕ) • Ideal.Quotient.mk I y) := by
      rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk I) p, ← map_mul, ← map_mul, ← map_mul, ← map_add (f := _), ← e0]
    rw [e, hpx, mul_zero, add_zero, hq, zero_mul]
  rw [hx0, addOrderOf_zero] at hx
  exact hp.one_lt.ne hx

end GlobalTheory.NormCoprime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramSub
namespace GlobalTheory

def UnramSub {V F : Type} [CommRing V] [Field F] (i : V →+* F) (T : Subring F) : Prop :=
  ∃ (_ : IsDiscreteValuationRing T) (f : V →+* T), (∀ v, (f v : F) = i v) ∧ ∀ π : V, Irreducible π → Irreducible (f π)

namespace UnramSub

variable {V F : Type} [CommRing V] [Field F] {i : V →+* F}

theorem mem {T : Subring F} (h : UnramSub i T) (v : V) : i v ∈ T := by
  obtain ⟨_, f, hf, -⟩ := h
  exact hf v ▸ (f v).2

theorem isDVR {T : Subring F} (h : UnramSub i T) : IsDiscreteValuationRing T := h.1

theorem trans {T₁ T₂ : Subring F} (h₁ : UnramSub i T₁) (h₂ : UnramSub T₁.subtype T₂) : UnramSub i T₂ := by
  obtain ⟨_, f₁, hf₁, hi₁⟩ := h₁
  obtain ⟨_, f₂, hf₂, hi₂⟩ := h₂
  refine ⟨‹_›, f₂.comp f₁, fun v => ?_, fun π hπ => hi₂ _ (hi₁ π hπ)⟩
  rw [RingHom.comp_apply, hf₂, Subring.coe_subtype, hf₁]

theorem le {T₁ T₂ : Subring F} (h₂ : UnramSub T₁.subtype T₂) : T₁ ≤ T₂ := fun z hz => h₂.mem ⟨z, hz⟩

theorem range [IsDomain V] [IsDiscreteValuationRing V] (hi : Function.Injective i) : UnramSub i i.range := by
  let e : V ≃+* i.range := RingEquiv.ofLeftInverse (Function.leftInverse_invFun hi)
  exact ⟨IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, e.toRingHom, fun v => rfl,
    fun π hπ => hπ.map e⟩

end UnramSub

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdHomeoSymmApplySnd
noncomputable section

namespace GlobalTheory.Cusp.Shear

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {N N' : Subgroup G}
  {V : Type} [AddCommGroup V] [TopologicalSpace V] {s : V → G} {π : N → V}

def prodMap (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (z : N' × V) : N :=
  ⟨z.1 * s z.2, N.mul_mem (hle z.1.2) (hs z.2)⟩

theorem coe_prodMap (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (z : N' × V) :
    (prodMap hle hs z : G) = z.1 * s z.2 := rfl

theorem map_inv_of_mul (hπmul : ∀ a b : N, π (a * b) = π a + π b) (a : N) : π a⁻¹ = -π a := by
  have h1 : π 1 = 0 := by simpa using hπmul 1 1
  have := hπmul a a⁻¹
  rw [mul_inv_cancel, h1] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

theorem mul_inv_mem (hs : ∀ v, s v ∈ N) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
    (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N') (n : N) :
    (n : G) * (s (π n))⁻¹ ∈ N' := by
  have h := (hker (n * (⟨s (π n), hs _⟩ : N)⁻¹)).1 (by
    rw [hπmul, map_inv_of_mul hπmul, hπs ⟨s (π n), hs _⟩ _ rfl, add_neg_cancel])
  simpa using h

def prodHomeo (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π)
    (hπmul : ∀ a b : N, π (a * b) = π a + π b) (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v)
    (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N') : N' × V ≃ₜ N where
  toFun := prodMap hle hs
  invFun n := (⟨(n : G) * (s (π n))⁻¹, mul_inv_mem hs hπmul hπs hker n⟩, π n)
  left_inv z := by
    have hv : π (prodMap hle hs z) = z.2 := by
      have e : prodMap hle hs z = ⟨z.1, hle z.1.2⟩ * ⟨s z.2, hs _⟩ := rfl
      rw [e, hπmul, hπs ⟨s z.2, hs _⟩ z.2 rfl, (hker _).2 z.1.2, zero_add]
    refine Prod.ext (Subtype.ext ?_) hv
    simp [hv, coe_prodMap]
  right_inv n := by
    apply Subtype.ext
    simp [coe_prodMap]
  continuous_toFun := by
    unfold prodMap
    fun_prop
  continuous_invFun := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) hπc
    fun_prop

@[simp] theorem prodHomeo_apply (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π)
    (hπmul : ∀ a b : N, π (a * b) = π a + π b) (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v)
    (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N') (z : N' × V) :
    (prodHomeo hle hs hsc hπc hπmul hπs hker z : G) = z.1 * s z.2 := rfl

end GlobalTheory.Cusp.Shear

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelALogALe
namespace GlobalTheory

theorem hilbertSamuel_ALogA_le (T D : ℕ) (PP b z : ℝ) (hD1 : 1 ≤ D) (hDT : D ≤ T) (hPP : 1 ≤ PP)
    (hb : 1 ≤ b) (hlogb : Real.log b ≤ PP) (hTP : (T : ℝ) * PP ≤ Real.sqrt b) (hz0 : 0 ≤ z)
    (hz : z ≤ 1 / 2) :
    26 * (26 * (D : ℝ) ^ 2 + 2 * z * T) * Real.log (max (26 * (26 * (D : ℝ) ^ 2 + 2 * z * T)) 1)
      ≤ 6000 * b := by
  have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hDT' : (D : ℝ) ≤ T := by exact_mod_cast hDT
  have hT1 : (1 : ℝ) ≤ T := le_trans hD1' hDT'
  set A : ℝ := 26 * (26 * (D : ℝ) ^ 2 + 2 * z * T) with hAdef
  have hA1 : 1 ≤ A := by
    have : (0 : ℝ) ≤ 2 * z * T := by positivity
    nlinarith
  have hmax : max A 1 = A := max_eq_left hA1
  rw [hmax]
  have hApos : 0 < A := by linarith
  have hAle : A ≤ 702 * (T : ℝ) ^ 2 := by
    have h1 : (D : ℝ) ^ 2 ≤ (T : ℝ) ^ 2 := by nlinarith
    have h2 : 2 * z * (T : ℝ) ≤ T := by nlinarith
    have h3 : (T : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hTsq : (T : ℝ) ≤ Real.sqrt b := by nlinarith
  have hlogT : 2 * Real.log T ≤ PP := by
    have h1 : Real.log T ≤ Real.log (Real.sqrt b) := Real.log_le_log hT0 hTsq
    rw [Real.log_sqrt (by linarith)] at h1
    linarith
  have hlog702 : Real.log 702 < 7 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have : Real.exp 7 = Real.exp 1 ^ 7 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h27 : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := by
      apply pow_le_pow_left₀ (by norm_num); linarith
    nlinarith
  have hlogA : Real.log A ≤ 8 * PP := by
    have h1 : Real.log A ≤ Real.log (702 * (T : ℝ) ^ 2) := Real.log_le_log hApos hAle
    have h2 : Real.log (702 * (T : ℝ) ^ 2) = Real.log 702 + 2 * Real.log T := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    linarith
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hmain : A * Real.log A ≤ 702 * (T : ℝ) ^ 2 * (8 * PP) :=
    mul_le_mul hAle hlogA hlogA0 (by positivity)
  have hsq : ((T : ℝ) * PP) ^ 2 ≤ b := by
    have h0 : 0 ≤ (T : ℝ) * PP := by positivity
    calc ((T : ℝ) * PP) ^ 2 ≤ Real.sqrt b ^ 2 := pow_le_pow_left₀ h0 hTP 2
      _ = b := Real.sq_sqrt (by linarith)
  have hTPP : (T : ℝ) ^ 2 * PP ≤ (T : ℝ) ^ 2 * PP ^ 2 := by
    have : PP ≤ PP ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  nlinarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
noncomputable section

namespace GlobalTheory.LatOrb

open Polynomial Matrix

variable (O : Type) {K : Type} [CommRing O] [Field K] [Algebra O K]

def stdLat (n : ℕ) : Submodule O (Fin n → K) where
  carrier := {v | ∀ i, v i ∈ (algebraMap O K).range}
  add_mem' := by
    intro a b ha hb i
    exact Subring.add_mem _ (ha i) (hb i)
  zero_mem' := fun i => Subring.zero_mem _
  smul_mem' := by
    intro c v hv i
    obtain ⟨a, ha⟩ := hv i
    exact ⟨c * a, by simp [Algebra.smul_def, ha]⟩

def matLat {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K)) :
    Submodule O (Fin n → K) :=
  M.map ((Matrix.mulVecLin g).restrictScalars O)

def IsLatV {n : ℕ} (M : Submodule O (Fin n → K)) : Prop :=
  M.FG ∧ Submodule.span K (M : Set (Fin n → K)) = ⊤

def herm {n : ℕ} (σ : K →+* K) (x y : Fin n → K) : K := ∑ k, x k * σ (y k)

def SelfDual {n : ℕ} (σ : K →+* K) (M : Submodule O (Fin n → K)) : Prop :=
  ∀ y, y ∈ M ↔ ∀ x ∈ M, herm σ y x ∈ (algebraMap O K).range

variable {O}

theorem mem_stdLat {n : ℕ} (v : Fin n → K) : v ∈ stdLat O n ↔ ∀ i, v i ∈ (algebraMap O K).range :=
  Iff.rfl

theorem mem_matLat {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K))
    (v : Fin n → K) : v ∈ matLat O g M ↔ ∃ u ∈ M, g *ᵥ u = v := by
  simp [matLat]

theorem matLat_mul {n : ℕ} (a b : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K)) :
    matLat O (a * b) M = matLat O a (matLat O b M) := by
  ext v
  simp only [mem_matLat]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨b *ᵥ u, ⟨u, hu, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by rw [Matrix.mulVec_mulVec]⟩

theorem matLat_one {n : ℕ} (M : Submodule O (Fin n → K)) : matLat O 1 M = M := by
  ext v
  simp [mem_matLat]

end GlobalTheory.LatOrb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootSubMemOfEvalMem
open IsLocalRing Polynomial

namespace GlobalTheory.AbsIntClosedLocal

theorem exists_root_sub_mem_of_eval_mem (T : Type) [CommRing T] [IsLocalRing T] [IsDomain T]
    (hroot : ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) :
    ∀ (n : ℕ) (f : T[X]), f.Monic → f.natDegree = n → ∀ a₀ : T, f.eval a₀ ∈ maximalIdeal T →
      ∃ a : T, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal T := by
  intro n
  induction n with
  | zero =>
    intro f hf hdeg a₀ hmem
    have : f = 1 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
      have := hf.coeff_natDegree
      rw [hdeg] at this
      rw [this, map_one]
    rw [this, eval_one] at hmem
    exact absurd ((Ideal.eq_top_iff_one _).2 hmem) (maximalIdeal.isMaximal T).ne_top
  | succ n ih =>
    intro f hf hdeg a₀ hmem
    obtain ⟨r, hr⟩ := hroot f hf (by omega)
    have hrr : f.IsRoot r := hr
    have hdiv := (mul_divByMonic_eq_iff_isRoot (p := f) (a := r)).2 hrr
    set g := f /ₘ (X - C r) with hg
    have hgm : g.Monic := (monic_X_sub_C r).of_mul_monic_left (by rw [hdiv]; exact hf)
    have hgdeg : g.natDegree = n := by
      have := natDegree_divByMonic f (monic_X_sub_C r)
      rw [natDegree_X_sub_C] at this
      rw [hg, this, hdeg]; omega
    have hev : f.eval a₀ = (a₀ - r) * g.eval a₀ := by
      conv_lhs => rw [← hdiv]
      simp [eval_mul]
    rw [hev] at hmem
    rcases (maximalIdeal.isMaximal T).isPrime.mem_or_mem hmem with h | h
    · refine ⟨r, hrr, ?_⟩
      have := (maximalIdeal T).neg_mem h
      simpa using this
    · obtain ⟨a, ha, ha'⟩ := ih g hgm hgdeg a₀ h
      refine ⟨a, ?_, ha'⟩
      rw [← hdiv]
      simp [IsRoot, eval_mul, ha.eq_zero]

theorem henselian_isAlgClosed_pow_surj :
    ∀ (T : Type) [CommRing T] [IsLocalRing T], (IsDomain T ∧ ∀ f : Polynomial T, f.Monic →
      0 < f.natDegree → ∃ x : T, f.eval x = 0) →
      HenselianLocalRing T ∧ IsAlgClosed (ResidueField T) ∧
        ∀ (n : ℕ) (u : Tˣ), 0 < n → ∃ v : Tˣ, v ^ n = u := by
  intro T _ _ ⟨hdom, hroot⟩
  refine ⟨⟨fun f hf a₀ h₁ _ => exists_root_sub_mem_of_eval_mem T hroot _ f hf rfl a₀ h₁⟩, ?_, ?_⟩
  · refine IsAlgClosed.of_exists_root _ (fun p hpm hpirr => ?_)
    have hl : p ∈ lifts (residue T) := (mem_lifts p).2 (map_surjective _ residue_surjective p)
    obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hpm
    obtain ⟨x, hx⟩ := hroot q hqm (by rw [hqd]; exact hpirr.natDegree_pos)
    refine ⟨residue T x, ?_⟩
    rw [← hq, eval_map, eval₂_hom, hx, map_zero]
  · intro n u hn
    obtain ⟨x, hx⟩ := hroot (X ^ n - C (u : T)) (monic_X_pow_sub_C _ hn.ne')
      (by rw [natDegree_X_pow_sub_C _]; exact hn)
    have hxn : x ^ n = (u : T) := by
      simp only [eval_sub, eval_pow, eval_X, eval_C] at hx
      exact sub_eq_zero.1 hx
    have hxu : IsUnit x := (isUnit_pow_iff hn.ne').1 (hxn ▸ u.isUnit)
    refine ⟨hxu.unit, Units.ext ?_⟩
    simp [hxn]

end GlobalTheory.AbsIntClosedLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetOperatorsCommOfAntiInvolution
open scoped BigOperators
open Classical

namespace GlobalTheory

namespace GelfandTrick

variable {G : Type} [Group G]

def InDoubleCoset (J : Subgroup G) (a y : G) : Prop := ∃ k₁ ∈ J, ∃ k₂ ∈ J, y = k₁ * a * k₂

theorem InDoubleCoset.mul {J : Subgroup G} {a y z j₁ j₂ : G} (h : InDoubleCoset J a y)
    (h₁ : j₁ ∈ J) (h₂ : j₂ ∈ J) (hz : z = j₁ * y * j₂) : InDoubleCoset J a z := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := h
  exact ⟨j₁ * k₁, J.mul_mem h₁ hk₁, k₂ * j₂, J.mul_mem hk₂ h₂, by rw [hz]; group⟩


open Classical in
theorem card_pairs_le (J : Subgroup G) (τ : G → G) (hmul : ∀ a b, τ (a * b) = τ b * τ a)
    (hinv : ∀ a, τ (τ a) = a) (hdc : ∀ g : G, ∃ k₁ ∈ J, ∃ k₂ ∈ J, τ g = k₁ * g * k₂)
    (hJ : ∀ k ∈ J, τ k ∈ J) (α β : G) (R S : Finset G)
    (hR : ∀ γ ∈ R, InDoubleCoset J α γ)
    (hR' : ∀ x : G, InDoubleCoset J α x → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ J)
    (hS : ∀ γ ∈ S, InDoubleCoset J β γ)
    (hS' : ∀ x : G, InDoubleCoset J β x → ∃! γ, γ ∈ S ∧ γ⁻¹ * x ∈ J) (c : G ⧸ J) :
    ((R ×ˢ S).filter (fun (p : G × G) => ((p.1 * p.2 : G) : G ⧸ J) = c)).card ≤
      ((S ×ˢ R).filter (fun (p : G × G) => ((p.1 * p.2 : G) : G ⧸ J) = c)).card := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  have hone : τ 1 = 1 := by
    have := hmul 1 1
    rw [mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hτinv : ∀ a, τ a⁻¹ = (τ a)⁻¹ := fun a => by
    have := hmul a a⁻¹
    rw [mul_inv_cancel, hone] at this
    exact eq_inv_of_mul_eq_one_left this.symm
  have hτdc : ∀ a y, InDoubleCoset J a y → InDoubleCoset J a (τ y) := fun a y h => by
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := hdc y
    exact h.mul hk₁ hk₂ e
  obtain ⟨k₁, hk₁, k₂, hk₂, hx⟩ := hdc x
  refine Finset.card_le_card_of_forall_subsingleton
    (fun (p q : G × G) => q.1⁻¹ * (x * k₂ * (τ p.1)⁻¹) ∈ J) ?_ ?_
  · rintro ⟨γ, δ⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq] at hp
    obtain ⟨⟨hγ, hδ⟩, hj⟩ := hp
    have h1 : τ x = τ ((γ * δ)⁻¹ * x) * τ δ * τ γ := by
      rw [← hmul, ← hmul]; congr 1; group
    have h2 : InDoubleCoset J β (x * k₂ * (τ γ)⁻¹) := by
      refine (hτdc _ _ (hS δ hδ)).mul (J.mul_mem (J.inv_mem hk₁) (hJ _ hj)) J.one_mem ?_
      have : x * k₂ = k₁⁻¹ * τ x := by rw [hx]; group
      rw [this, h1]; group
    obtain ⟨δ', ⟨hδ', hj'⟩, -⟩ := hS' _ h2
    have h3 : InDoubleCoset J α (δ'⁻¹ * x) :=
      (hτdc _ _ (hR γ hγ)).mul hj' (J.inv_mem hk₂) (by group)
    obtain ⟨γ', ⟨hγ', hj''⟩, -⟩ := hR' _ h3
    refine ⟨(δ', γ'), ?_, hj'⟩
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq]
    refine ⟨⟨hδ', hγ'⟩, ?_⟩
    rwa [mul_inv_rev, mul_assoc]
  · rintro ⟨δ', γ'⟩ - ⟨γ₁, δ₁⟩ h₁ ⟨γ₂, δ₂⟩ h₂
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_product,
      QuotientGroup.eq, Finset.mem_coe] at h₁ h₂
    obtain ⟨⟨⟨hγ₁, hδ₁⟩, hj₁⟩, hr₁⟩ := h₁
    obtain ⟨⟨⟨hγ₂, hδ₂⟩, hj₂⟩, hr₂⟩ := h₂
    have h4 : γ₂⁻¹ * γ₁ ∈ J := by
      have := hJ _ (J.mul_mem (J.inv_mem hr₁) hr₂)
      have e : (δ'⁻¹ * (x * k₂ * (τ γ₁)⁻¹))⁻¹ * (δ'⁻¹ * (x * k₂ * (τ γ₂)⁻¹))
          = τ (γ₂⁻¹ * γ₁) := by rw [hmul, hτinv]; group
      rwa [e, hinv] at this
    have hγ : γ₁ = γ₂ :=
      (hR' γ₁ (hR γ₁ hγ₁)).unique ⟨hγ₁, by simpa using J.one_mem⟩ ⟨hγ₂, h4⟩
    subst hγ
    have h5 : InDoubleCoset J β (γ₁⁻¹ * x) := (hS δ₁ hδ₁).mul J.one_mem hj₁ (by group)
    have hδ : δ₁ = δ₂ :=
      (hS' _ h5).unique ⟨hδ₁, by rwa [mul_inv_rev, mul_assoc] at hj₁⟩
        ⟨hδ₂, by rwa [mul_inv_rev, mul_assoc] at hj₂⟩
    rw [hδ]

end GelfandTrick

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricFunctionInverseInvariant
namespace GlobalTheory

theorem exists_perm_of_univ_map_eq {ι β : Type} [Fintype ι] (g g' : ι → β)
    (h : Finset.univ.val.map g = Finset.univ.val.map g') :
    ∃ π : Equiv.Perm ι, ∀ i, g (π i) = g' i := by
  classical
  have hc : ∀ c, Fintype.card {i // g' i = c} = Fintype.card {i // g i = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [Finset.card, Finset.filter_val]
    simpa only [eq_comm] using this.symm
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩

theorem eq_of_perm_inv_invariant_of_multiset_eq :
    ∀ (m : ℕ) (f : (Fin m → ℂ) → ℂ), (∀ α : Fin m → ℂ, (∀ i, α i ≠ 0) → (∀ π : Equiv.Perm (Fin m), f (α ∘ π) = f α) ∧ ∀ i, f (Function.update α i (α i)⁻¹) = f α) → ∀ α α' : Fin m → ℂ, (∀ i, α i ≠ 0) → Finset.univ.val.map α + Finset.univ.val.map (fun i => (α i)⁻¹) = Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹) → f α = f α' := by
  classical
  intro m f hf α α' hα h
  have hα' : ∀ i, α' i ≠ 0 := by
    intro i hi
    have hmem : (0 : ℂ) ∈ Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹) :=
      Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, hi⟩))
    rw [← h] at hmem
    rcases Multiset.mem_add.1 hmem with h1 | h1
    · obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 h1
      exact hα j hj
    · obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 h1
      exact hα j (inv_eq_zero.1 hj)
  have h2 := congrArg (Multiset.map (fun x : ℂ => x + x⁻¹)) h
  simp only [Multiset.map_add (f := _), Multiset.map_map, Function.comp_def, inv_inv] at h2
  have e1 : ∀ γ : Fin m → ℂ, (fun i => (γ i)⁻¹ + γ i) = fun i => γ i + (γ i)⁻¹ :=
    fun γ => funext fun i => add_comm _ _
  rw [e1 α, e1 α'] at h2
  have h3 : Finset.univ.val.map (fun i => α i + (α i)⁻¹)
      = Finset.univ.val.map (fun i => α' i + (α' i)⁻¹) := by
    ext c
    have := congrArg (Multiset.count c) h2
    simp only [Multiset.count_add] at this
    omega
  obtain ⟨π, hπ⟩ := exists_perm_of_univ_map_eq _ _ h3
  have hor : ∀ i, α' i = α (π i) ∨ α' i = (α (π i))⁻¹ := by
    intro i
    have h4 := hπ i
    have ha := hα (π i)
    have hb := hα' i
    have h5 : (α' i - α (π i)) * (α' i * α (π i) - 1) = 0 := by
      field_simp at h4
      linear_combination -h4
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact Or.inl (sub_eq_zero.1 h6)
    · exact Or.inr (eq_inv_of_mul_eq_one_left (sub_eq_zero.1 h6))
  have hβ : ∀ i, (α ∘ π) i ≠ 0 := fun i => hα _
  have key : ∀ s : Finset (Fin m),
      f (fun i => if i ∈ s then α' i else (α ∘ π) i) = f (α ∘ π) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Function.comp_def]
    | insert j s hj ih =>
      rw [← ih]
      have hne : ∀ i, (fun i => if i ∈ s then α' i else (α ∘ π) i) i ≠ 0 := by
        intro i
        by_cases hi : i ∈ s
        · simpa [hi] using hα' i
        · simpa [hi] using hα (π i)
      rcases hor j with h6 | h6
      · congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
      · rw [← (hf _ hne).2 j]
        congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
  have := key Finset.univ
  simp only [Finset.mem_univ, if_true] at this
  rw [← (hf α hα).1 π, ← this]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimFiberStalkEqQuotient
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FibreStalk

theorem fromSpecResidueField_eq {B : Scheme.{0}} {x b : B} (h : x = b) :
    B.fromSpecResidueField b =
      Spec.map (B.residue x ≫ (B.residueFieldCongr h).hom) ≫ B.fromSpecStalk x := by
  rw [← B.residueFieldCongr_fromSpecResidueField h, Spec.map_comp, Category.assoc]
  rfl

theorem image_eq (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b) : π (π.fiberι b z) = b := by
  have := (π.range_fiberι b).le ⟨z, rfl⟩
  simpa using this

theorem ker_stalkMap_fiberι (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b) :
    RingHom.ker ((π.fiberι b).stalkMap z).hom =
      (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map
        (π.stalkMap (π.fiberι b z)).hom := by
  have h' := image_eq B Y π b z
  have hA := fromSpecResidueField_eq h'
  apply le_antisymm
  · intro a ha
    let y := π.fiberι b z
    let S := Y.presheaf.stalk y
    let I := (IsLocalRing.maximalIdeal (B.presheaf.stalk (π y))).map (π.stalkMap y).hom
    have hIm : I ≤ IsLocalRing.maximalIdeal S :=
      Ideal.map_le_iff_le_comap.2 fun r hr => map_nonunit (π.stalkMap y).hom r hr
    have : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.2
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top hIm)
    have : IsLocalRing (S ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hl : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    let L : B.residueField (π y) ⟶ CommRingCat.of (S ⧸ I) := CommRingCat.ofHom
      (Ideal.Quotient.lift (IsLocalRing.maximalIdeal (B.presheaf.stalk (π y)))
        ((Ideal.Quotient.mk I).comp (π.stalkMap y).hom)
        (fun r hr => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hr)))
    have hres : B.residue (π y) ≫ L = π.stalkMap y ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      ext r; rfl
    let g : Spec (CommRingCat.of (S ⧸ I)) ⟶ Y := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ Y.fromSpecStalk y
    let t : Spec (CommRingCat.of (S ⧸ I)) ⟶ Spec (B.residueField b) := Spec.map ((B.residueFieldCongr h').inv ≫ L)
    have w : g ≫ π = t ≫ B.fromSpecResidueField b := by
      rw [hA, ← Category.assoc, ← Spec.map_comp]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, g]
      rw [hres]
      first
        | (rw [Spec.map_comp (π.stalkMap y) (CommRingCat.ofHom (Ideal.Quotient.mk I)), Category.assoc,
            Scheme.SpecMap_stalkMap_fromSpecStalk])
        | (erw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk])
      all_goals rfl
    let ℓ : Spec (CommRingCat.of (S ⧸ I)) ⟶ π.fiber b := Limits.pullback.lift g t w
    have hℓ : ℓ ≫ π.fiberι b = g := Limits.pullback.lift_fst _ _ _
    have e : ℓ (IsLocalRing.closedPoint _) = z := by
      apply (π.fiberι b).isEmbedding.injective
      refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hℓ).trans ?_
      exact (congrArg (Y.fromSpecStalk y) (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I))).trans
        Scheme.fromSpecStalk_closedPoint
    let ψ := (π.fiber b).presheaf.stalkSpecializes (specializes_of_eq e) ≫ Scheme.stalkClosedPointTo ℓ
    have hψ : (π.fiberι b).stalkMap z ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      apply Spec.map_injective
      rw [← cancel_mono (Y.fromSpecStalk y)]
      change _ = g
      rw [← hℓ, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
    have hψ' := congrArg (fun q => q.hom a) hψ
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hψ'
    rw [RingHom.mem_ker.1 ha, map_zero] at hψ'
    exact Ideal.Quotient.eq_zero_iff_mem.1 hψ'.symm
  · obtain ⟨c, hc⟩ := Spec.map_surjective ((π.fiber b).fromSpecStalk z ≫ π.fiberToSpecResidueField b)
    have key : π.stalkMap (π.fiberι b z) ≫ (π.fiberι b).stalkMap z =
        B.residue _ ≫ (B.residueFieldCongr h').hom ≫ c := by
      apply Spec.map_injective
      rw [← cancel_mono (B.fromSpecStalk (π (π.fiberι b z)))]
      rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
        Scheme.SpecMap_stalkMap_fromSpecStalk_assoc, Scheme.Hom.fiber_fac, ← Category.assoc, ← hc, hA]
      simp only [Spec.map_comp, Category.assoc]
    refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have := congrArg (fun q => q.hom r) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    have : (B.residue (π (π.fiberι b z))).hom r = 0 := (IsLocalRing.residue_eq_zero_iff r).2 hr
    rw [this, map_zero, map_zero]

theorem nonempty_ringEquiv_stalk_fiber (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b) :
    Nonempty ((Y.presheaf.stalk (π.fiberι b z) ⧸
        (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map
          (π.stalkMap (π.fiberι b z)).hom) ≃+* (π.fiber b).presheaf.stalk z) := by
  rw [← ker_stalkMap_fiberι]
  exact ⟨RingHom.quotientKerEquivOfSurjective ((π.fiberι b).stalkMap_surjective z)⟩

end GlobalTheory.FibreStalk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsCompactClosureZpowers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsCompactClosureZpowers
open NumberField IsDedekindDomain

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.isIntegral_matrix_of_pow_bounded {O K : Type} [CommRing O] [IsNoetherianRing O]
    [Field K] [Algebra O K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (a : K) (ha : a ≠ 0)
    (h : ∀ (k : ℕ) (i j : Fin n), ∃ b : O, algebraMap O K b = a * (g ^ k) i j) :
    IsIntegral O g := by
  classical
  let ψ : (Fin n → Fin n → O) →ₗ[O] Matrix (Fin n) (Fin n) K :=
    { toFun := fun b => Matrix.of fun i j => algebraMap O K (b i j)
      map_add' := fun b c => by ext i j; simp
      map_smul' := fun c b => by ext i j; simp [Algebra.smul_def] }
  let φ : Matrix (Fin n) (Fin n) K →ₗ[O] Matrix (Fin n) (Fin n) K :=
    { toFun := fun A => a • A
      map_add' := fun A B => smul_add a A B
      map_smul' := fun c A => smul_comm a c A }
  have hφ : Function.Injective φ := fun A B hAB => smul_right_injective _ ha hAB
  have hP : (LinearMap.range ψ).FG := by
    rw [LinearMap.range_eq_map]; exact Submodule.FG.map _ Module.Finite.fg_top
  haveI := isNoetherian_of_fg_of_noetherian _ hP
  have hle : Submodule.map φ (Subalgebra.toSubmodule (Algebra.adjoin O {g})) ≤
      LinearMap.range ψ := by
    rw [Algebra.adjoin_eq_span, ← Submonoid.powers_eq_closure, Submodule.map_span_le]
    rintro _ ⟨k, rfl⟩
    choose b hb using h k
    exact ⟨b, by ext i j; simp [ψ, φ, hb]⟩
  exact IsIntegral.of_mem_of_fg _ (Submodule.fg_of_fg_map_injective φ hφ
    (Submodule.FG.of_le_of_isNoetherian hle)) g (Algebra.self_mem_adjoin_singleton O g)

open NumberField IsDedekindDomain in
private theorem exists_smul_pow_entry_mem_adicCompletionIntegers (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E))
    (hg : IsCompact (closure (Subgroup.zpowers g : Set (GL (Fin n) (w.adicCompletion E))))) :
    ∃ a : w.adicCompletion E, a ≠ 0 ∧ ∀ (k : ℕ) (i j : Fin n),
      a * ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ^ k) i j ∈
        w.adicCompletionIntegers E := by
  set O := w.adicCompletionIntegers E
  set C := closure (Subgroup.zpowers g : Set (GL (Fin n) (w.adicCompletion E)))
  set S : Set (w.adicCompletion E) :=
    ⋃ i, ⋃ j, (fun h : GL (Fin n) (w.adicCompletion E) => (h : Matrix (Fin n) (Fin n) _) i j) '' C
  have hS : IsCompact S := isCompact_iUnion fun i => isCompact_iUnion fun j =>
    hg.image (Units.continuous_val.matrix_elem i j)
  let U : {a : w.adicCompletion E // a ∈ O ∧ a ≠ 0} → Set (w.adicCompletion E) :=
    fun a => (fun x => a.1 * x) ⁻¹' (O : Set _)
  have hUo : ∀ a, IsOpen (U a) := fun a =>
    (Valued.isOpen_integer _).preimage (continuous_const.mul continuous_id)
  have hcov : S ⊆ ⋃ a, U a := by
    intro x _
    by_cases hx : x ∈ O
    · exact Set.mem_iUnion.2 ⟨⟨1, O.one_mem, one_ne_zero⟩, by simpa [U] using hx⟩
    · have hx0 : x ≠ 0 := by
        rintro rfl
        exact hx O.zero_mem
      have hxi : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hx
      exact Set.mem_iUnion.2 ⟨⟨x⁻¹, hxi, inv_ne_zero hx0⟩, by simp [U, hx0, O.one_mem]⟩
  have hdir : Directed (· ⊆ ·) U := by
    rintro ⟨a, ha, ha0⟩ ⟨b, hb, hb0⟩
    refine ⟨⟨a * b, mul_mem ha hb, mul_ne_zero ha0 hb0⟩, ?_, ?_⟩
    · intro x hx
      have := mul_mem hb (show a * x ∈ O from hx)
      simpa [U, mul_assoc, mul_comm, mul_left_comm] using this
    · intro x hx
      have := mul_mem ha (show b * x ∈ O from hx)
      simpa [U, mul_assoc] using this
  haveI : Nonempty {a : w.adicCompletion E // a ∈ O ∧ a ≠ 0} := ⟨⟨1, O.one_mem, one_ne_zero⟩⟩
  obtain ⟨a, hSa⟩ := hS.elim_directed_cover U hUo hcov hdir
  refine ⟨a.1, a.2.2, fun k i j => hSa ?_⟩
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨g ^ k, subset_closure ?_, by simp⟩⟩⟩
  exact Subgroup.npow_mem_zpowers g k


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.isIntegral_of_isCompact_closure_zpowers (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E))
    (hg : IsCompact (closure (Subgroup.zpowers g : Set (GL (Fin n) (w.adicCompletion E))))) :
    IsIntegral (w.adicCompletionIntegers E)
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
  obtain ⟨a, ha0, ha⟩ := exists_smul_pow_entry_mem_adicCompletionIntegers E w n g hg
  exact _root_.GlobalTheory.isIntegral_matrix_of_pow_bounded _ a ha0 fun k i j => ⟨⟨_, ha k i j⟩, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsCompactClosureZpowersStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E)), IsCompact (closure (Subgroup.zpowers g : Set (GL (Fin n) (w.adicCompletion E)))) → IsIntegral (w.adicCompletionIntegers E) (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
  first | exact @GlobalTheory.isIntegral_of_isCompact_closure_zpowers | exact GlobalTheory.isIntegral_of_isCompact_closure_zpowers | (intros; apply GlobalTheory.isIntegral_of_isCompact_closure_zpowers <;> assumption)
end
end
