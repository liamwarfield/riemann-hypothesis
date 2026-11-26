module

public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Transport
public import Formalism.SatakeDualWeyl.StatementC
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero

@[expose] public section

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeAssoc
noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G] (K : Subgroup G)

theorem out_smul_out (h : G) (z : G ⧸ K) : ∃ c : K, (h • z : G ⧸ K).out = h * z.out * c := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K (h * z.out)
  refine ⟨c, ?_⟩
  have e : (h • z : G ⧸ K) = ((h * z.out : G) : G ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' z]
    rfl
  rw [e, hc]

theorem conv_assoc (hK : IsCommensurated K) {k : Type} [CommRing k] (f₁ f₂ f₃ : G → k)
    (h₁ : FinDosetSupp K f₁) (h₂ : IsBiInv K f₂) (h₃ : IsBiInv K f₃) (h₃' : FinDosetSupp K f₃) :
    conv K (conv K f₁ f₂) f₃ = conv K f₁ (conv K f₂ f₃) := by
  classical
  funext g
  have hA := finite_supp_translate (K := K) hK f₁ h₁ 1
  have hB := finite_supp_inv (K := K) hK f₃ h₃' g
  have sA : ∀ x : G ⧸ K, x ∉ hA.toFinset → f₁ x.out = 0 := by
    intro x hx
    simpa using hx
  have sB : ∀ y : G ⧸ K, y ∉ hB.toFinset → f₃ (y.out⁻¹ * g) = 0 := by
    intro y hy
    simpa using hy
  generalize hA.toFinset = A at sA
  generalize hB.toFinset = B at sB

  have key : ∀ x z : G ⧸ K, f₂ z.out * f₃ (z.out⁻¹ * (x.out⁻¹ * g)) =
      f₂ (x.out⁻¹ * (x.out • z).out) * f₃ ((x.out • z).out⁻¹ * g) := by
    intro x z
    obtain ⟨c, hc⟩ := out_smul_out K x.out z
    rw [hc]
    have e2 : x.out⁻¹ * (x.out * z.out * c) = ((1 : K) : G) * z.out * c := by
      simp [mul_assoc]
    have e3 : (x.out * z.out * c)⁻¹ * g =
        ((c⁻¹ : K) : G) * (z.out⁻¹ * (x.out⁻¹ * g)) * ((1 : K) : G) := by
      simp [mul_assoc]
    rw [e2, e3, h₂, h₃]
  have inner : ∀ x : G ⧸ K, conv K f₂ f₃ (x.out⁻¹ * g) =
      ∑ y ∈ B, f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) := by
    intro x
    calc conv K f₂ f₃ (x.out⁻¹ * g)
        = ∑ᶠ z : G ⧸ K, f₂ z.out * f₃ (z.out⁻¹ * (x.out⁻¹ * g)) := rfl
      _ = ∑ᶠ z : G ⧸ K, (fun y : G ⧸ K => f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g))
            (MulAction.toPerm x.out z) := finsum_congr (fun z => key x z)
      _ = ∑ᶠ y : G ⧸ K, f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) :=
            finsum_comp_equiv (MulAction.toPerm x.out : G ⧸ K ≃ G ⧸ K)
              (f := fun y : G ⧸ K => f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g))
      _ = ∑ y ∈ B, f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) := by
        apply finsum_eq_sum_of_support_subset
        intro y hy
        by_contra h
        exact (Function.mem_support.mp hy) (by rw [sB y (by simpa using h), mul_zero])
  have L : conv K (conv K f₁ f₂) f₃ g =
      ∑ y ∈ B, ∑ x ∈ A, f₁ x.out * f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) := by
    rw [show conv K (conv K f₁ f₂) f₃ g =
      ∑ᶠ y : G ⧸ K, (∑ᶠ x : G ⧸ K, f₁ x.out * f₂ (x.out⁻¹ * y.out)) * f₃ (y.out⁻¹ * g) from rfl]
    rw [finsum_eq_sum_of_support_subset _ (s := B) ?_]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [finsum_eq_sum_of_support_subset _ (s := A) ?_, Finset.sum_mul]
      intro x hx
      by_contra h
      exact (Function.mem_support.mp hx) (by rw [sA x (by simpa using h), zero_mul])
    · intro y hy
      by_contra h
      exact (Function.mem_support.mp hy) (by rw [sB y (by simpa using h), mul_zero])
  have R : conv K f₁ (conv K f₂ f₃) g =
      ∑ x ∈ A, ∑ y ∈ B, f₁ x.out * f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) := by
    rw [show conv K f₁ (conv K f₂ f₃) g = ∑ᶠ x : G ⧸ K, f₁ x.out * conv K f₂ f₃ (x.out⁻¹ * g) from rfl]
    rw [finsum_eq_sum_of_support_subset _ (s := A) ?_]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [inner x, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    · intro x hx
      by_contra h
      exact (Function.mem_support.mp hx) (by rw [sA x (by simpa using h), zero_mul])
  rw [L, R, Finset.sum_comm]

theorem hecke_assoc : Formalism.UG.HeckeAssoc := by
  intro G _ K k _ hK f₁ hf₁ f₂ hf₂ f₃ hf₃
  exact conv_assoc K hK f₁ f₂ f₃ hf₁.2 hf₂.1 hf₃.1 hf₃.2

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeRes
noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Formalism.UG.P

open Formalism.UG

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem satake_unif_ne_zero {ϖ : v.adicCompletion F} (h : IsUnifV F v ϖ) : ϖ ≠ 0 := by
  intro h0
  subst h0
  unfold IsUnifV at h
  first | simp at h | done

theorem satake_lt_one_le {x : WithZero (Multiplicative ℤ)} (hx : x < 1) :
    x ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  cases x using WithZero.recZeroCoe with
  | zero => exact WithZero.zero_le _
  | coe a =>
    have h1 : a < 1 := by exact_mod_cast hx
    have h2 : a ≤ Multiplicative.ofAdd (-1 : ℤ) := by
      change Multiplicative.toAdd a ≤ -1
      have h3 : Multiplicative.toAdd a < 0 := h1
      omega
    exact WithZero.coe_le_coe.mpr h2

private theorem mem_Ov_iff' (x : v.adicCompletion F) : x ∈ Ov F v ↔ Valued.v x ≤ 1 := by
  unfold Ov
  first
    | exact Iff.rfl
    | exact mem_adicCompletionIntegers
    | simp [mem_adicCompletionIntegers]

theorem satake_unif_inv_not_mem {ϖ : v.adicCompletion F} (h : IsUnifV F v ϖ) : ϖ⁻¹ ∉ Ov F v := by
  unfold IsUnifV at h
  intro hm
  have hm' : Valued.v ϖ⁻¹ ≤ 1 := (mem_Ov_iff' v _).mp hm
  rw [map_inv₀, h] at hm'
  have h4 : ((Multiplicative.ofAdd (-1 : ℤ))⁻¹ : Multiplicative ℤ) ≤ 1 := by
    rw [← WithZero.coe_le_coe, WithZero.coe_inv]
    first | exact_mod_cast hm' | simpa using hm'
  have h5 : Multiplicative.toAdd ((Multiplicative.ofAdd (-1 : ℤ))⁻¹) ≤ Multiplicative.toAdd (1 : Multiplicative ℤ) := h4
  simp at h5

theorem satake_mem_span_iff {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (h : IsUnifV F v ϖ)
    (y : Ov F v) : y ∈ Ideal.span {(⟨ϖ, hϖ⟩ : Ov F v)} ↔ Valued.v (y : v.adicCompletion F) < 1 := by
  have h0 := satake_unif_ne_zero v h
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, rfl⟩
    have hz : Valued.v ((z : Ov F v) : v.adicCompletion F) ≤ 1 := z.2
    show Valued.v ((z : v.adicCompletion F) * ϖ) < 1
    rw [Valuation.map_mul, h]
    calc Valued.v (z : v.adicCompletion F) * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
        ≤ 1 * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
          by gcongr
      _ < 1 := by
          rw [one_mul, ← WithZero.coe_one, WithZero.coe_lt_coe]
          show (-1 : ℤ) < 0
          omega
  · intro hy
    have hle := satake_lt_one_le hy
    have hm : (y : v.adicCompletion F) * ϖ⁻¹ ∈ Ov F v := by
      show Valued.v ((y : v.adicCompletion F) * ϖ⁻¹) ≤ 1
      rw [Valuation.map_mul, Valuation.map_inv, h]
      calc Valued.v (y : v.adicCompletion F) * (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))⁻¹
          ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) *
              (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))⁻¹ :=
            by gcongr
        _ = 1 := mul_inv_cancel₀ WithZero.coe_ne_zero
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    show (y : v.adicCompletion F) * ϖ⁻¹ * ϖ = y
    field_simp

def satakeIota : 𝓞 F →+* Ov F v := algebraMap (𝓞 F) (v.adicCompletionIntegers F)

theorem satakeIota_coe (r : 𝓞 F) :
    ((satakeIota v r : Ov F v) : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) r := by first | rfl | simp [satakeIota] | (unfold satakeIota Ov; done)

theorem satake_card_res {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (h : IsUnifV F v ϖ) :
    Nat.card (Ov F v ⧸ Ideal.span {(⟨ϖ, hϖ⟩ : Ov F v)}) = qV F v := by
  set I := Ideal.span {(⟨ϖ, hϖ⟩ : Ov F v)}
  let φ : 𝓞 F →+* Ov F v ⧸ I := (Ideal.Quotient.mk I).comp (satakeIota v)
  have hker : ∀ r ∈ v.asIdeal, φ r = 0 := by
    intro r hr
    simp only [φ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    rw [satake_mem_span_iff v hϖ h]
    unfold satakeIota
    rw [algebraMap_adicCompletionIntegers_apply, adicCompletion.valued_coe (K := F) (v := v),
      valuation_of_algebraMap]
    exact (intValuation_lt_one_iff_mem v r).2 hr
  have := v.isMaximal
  let _ := Ideal.Quotient.field v.asIdeal
  let ψ := Ideal.Quotient.lift v.asIdeal φ hker
  have hne : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : Ov F v) ∈ I := htop ▸ Submodule.mem_top
    rw [satake_mem_span_iff v hϖ h] at h1
    simp at h1
  have : Nontrivial (Ov F v ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hne
  have hinj : Function.Injective ψ := RingHom.injective ψ
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := glint_exists_approx v x
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    show φ r = _
    simp only [φ, RingHom.comp_apply]
    rw [Ideal.Quotient.eq, satake_mem_span_iff v hϖ h]
    have e : ((satakeIota v r - x : Ov F v) : v.adicCompletion F) =
        -((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) := by
      rw [AddSubgroupClass.coe_sub, satakeIota_coe, neg_sub]
    rw [e, Valuation.map_neg]
    exact hr
  rw [← Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩)]
  unfold qV
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem satake_ordV_unif {ϖ : v.adicCompletion F} (h : IsUnifV F v ϖ) : ordV F v ϖ = 1 := by
  unfold ordV IsUnifV at *
  have h0 : Valued.v ϖ ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
  rw [dite_eq_right h0]
  have e : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [WithZero.coe_unzero, h]
  rw [WithZero.coe_injective e]
  simp

theorem satake_ordV_one : ordV F v 1 = 0 := by
  unfold ordV
  have h0 : Valued.v (1 : v.adicCompletion F) ≠ 0 := by simp
  rw [dite_eq_right h0]
  have e : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [WithZero.coe_unzero, map_one, WithZero.coe_one]
  rw [WithZero.coe_injective e]
  simp

theorem satake_two_le_qV : 2 ≤ qV F v := by
  unfold qV
  have h1 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h2 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

end Formalism.UG.P
end
end
