module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTorsionQuotientConjInvariantDecomposition

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameCochainCocycleExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicCharCongruentOneOnDecompositionGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicCharCongruentOneOnDecompositionGroup
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.EpsDec

theorem natCast_eq_of_pow_eq {M : Type} [CommMonoid M] {ζ : M} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0)
    {a b : ℕ} (h : ζ ^ a = ζ ^ b) : (a : ZMod N) = b := by
  rw [ZMod.natCast_eq_natCast_iff' a b N]
  rw [pow_eq_pow_mod a hζ.pow_eq_one, pow_eq_pow_mod b hζ.pow_eq_one] at h
  exact hζ.pow_inj (Nat.mod_lt _ (Nat.pos_of_ne_zero hN)) (Nat.mod_lt _ (Nat.pos_of_ne_zero hN)) h

theorem eps_dec_cong : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl)
    (B : ValuationSubring Ω), IsPlaceOver B w → l ^ n ∣ normV w - 1 → 1 ≤ n →
    ∀ σ ∈ Dec (F := ℚ) B, Cg n (eps l σ) 1 := by
  intro l _ Ω _ _ _ n w B hB hdiv hn σ hσ
  have hl : l.Prime := Fact.out
  have hl2 := hl.two_le
  set p := normV w with hpdef
  have hp : p.Prime := GlobalTheory.Ord2.PrimeChar.normV_prime w
  haveI : Fact p.Prime := ⟨hp⟩
  have hA : B.valuation (p : Ω) < 1 := GlobalTheory.Ord2.PrimeChar.val_normV_lt_one hB
  have hpl : p ≠ l := by
    intro e
    have h1 : l ∣ p - 1 := (dvd_pow_self l (by omega)).trans hdiv
    rw [e] at h1
    have h2 := Nat.le_of_dvd (by omega) h1
    omega
  have hcop : (l ^ n).Coprime p :=
    Nat.Coprime.pow_left n ((Nat.coprime_primes hl hp).2 hpl.symm)
  obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω p B hA (l ^ n) hcop σ hσ
  have hp1 : (p : ZMod (l ^ n)) = 1 := by
    have h1 : 1 ≤ p := hp.one_lt.le
    have : ((p - 1 : ℕ) : ZMod (l ^ n)) = 0 := (CharP.cast_eq_zero_iff (ZMod (l ^ n)) (l ^ n) _).2 hdiv
    rw [Nat.cast_sub h1, Nat.cast_one, sub_eq_zero] at this
    exact this
  have hIAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ hl.ne_zero
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hspec := cyclotomicCharacter.spec (L := Ω) l
    (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) ζ hζ.pow_eq_one
  set c : ℤ_[l] := ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) with hc
  have hσζ : σ ζ = ζ ^ (PadicInt.toZModPow n c).val := hspec
  have hζp : ζ ^ (p ^ k) = ζ ^ 1 := by
    rw [pow_eq_pow_mod (p ^ k) hζ.pow_eq_one, pow_eq_pow_mod 1 hζ.pow_eq_one]
    congr 1
    rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_pow, hp1, one_pow, Nat.cast_one]
  have hm : PadicInt.toZModPow n c = 1 := by
    have h1 : ζ ^ (PadicInt.toZModPow n c).val = ζ ^ 1 := by rw [← hσζ, hk ζ hζ.pow_eq_one, hζp]
    have h2 := natCast_eq_of_pow_eq hζ hN0 h1
    rwa [ZMod.natCast_zmod_val, Nat.cast_one] at h2
  have hker : c - 1 ∈ Ideal.span {((l : ℤ_[l])) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hm, map_one, sub_self]
  have hnorm := (PadicInt.norm_le_pow_iff_mem_span_pow (c - 1) n).2 hker
  have e1 : eps l σ - 1 = algebraMap ℚ_[l] (Qbar l) ((c : ℚ_[l]) - 1) := by
    rw [map_sub, map_one]; rfl
  unfold Cg
  rw [e1, norm_algebraMap', norm_pow]
  have e2 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [e2, norm_algebraMap', Padic.norm_p]
  have e3 : ‖(c : ℚ_[l]) - 1‖ = ‖c - 1‖ := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]
  rw [e3]
  refine hnorm.trans (le_of_eq ?_)
  rw [zpow_neg, zpow_natCast, inv_pow]

end GlobalTheory.Ord2.EpsDec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicCharCongruentOneOnDecompositionGroupStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicChar_congruent_one_on_decompositionGroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl) (B : ValuationSubring Ω), IsPlaceOver B w → l ^ n ∣ normV w - 1 → 1 ≤ n → ∀ σ ∈ Dec (F := ℚ) B, Cg n (eps l σ) 1 := by
  first | exact @GlobalTheory.Ord2.EpsDec.eps_dec_cong | exact GlobalTheory.Ord2.EpsDec.eps_dec_cong | (intros; apply GlobalTheory.Ord2.EpsDec.eps_dec_cong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsAlt
namespace GlobalTheory.IntegralNormLeOne

open Polynomial

theorem norm_le_one_of_isIntegral {l : ℕ} [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  have hc : ∀ a : ℤ_[l], ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
    intro a
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
    exact a.2
  obtain ⟨p, hm, hp⟩ := hx
  by_contra h
  push_neg at h
  have h0 : (0 : ℝ) < ‖x‖ := lt_trans one_pos h
  rw [hm.as_sum, eval₂_add, eval₂_pow, eval₂_X, eval₂_finsetSum] at hp
  have he : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree,
      eval₂ (algebraMap ℤ_[l] (PadicAlgCl l)) x (C (p.coeff i) * X ^ i) :=
    eq_neg_of_add_eq_zero_left hp
  rcases Nat.eq_zero_or_pos p.natDegree with hn | hn
  · rw [hn] at he
    simp at he
  · have hle : ‖∑ i ∈ Finset.range p.natDegree,
        eval₂ (algebraMap ℤ_[l] (PadicAlgCl l)) x (C (p.coeff i) * X ^ i)‖
        ≤ ‖x‖ ^ (p.natDegree - 1) := by
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
      intro i hi
      have hi' : i ≤ p.natDegree - 1 := by
        have := Finset.mem_range.mp hi
        omega
      rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, norm_mul, norm_pow]
      calc _ ≤ 1 * ‖x‖ ^ i := by gcongr; exact hc _
        _ = ‖x‖ ^ i := one_mul _
        _ ≤ _ := pow_le_pow_right₀ h.le hi'
    have h1 : ‖x‖ ^ p.natDegree ≤ ‖x‖ ^ (p.natDegree - 1) := by
      rw [← norm_pow, he, norm_neg]; exact hle
    have h2 : ‖x‖ ^ (p.natDegree - 1) < ‖x‖ ^ p.natDegree :=
      pow_lt_pow_right₀ h (by omega)
    exact absurd h1 (not_le.mpr h2)

end GlobalTheory.IntegralNormLeOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameCochainCocycleExtension
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.BrTame

variable {l : ℕ} [Fact l.Prime]

def ballSub (r : ℝ) (hr : 0 ≤ r) : AddSubgroup (PadicAlgCl l) where
  carrier := {x | ‖x‖ ≤ r}
  zero_mem' := by simpa using hr
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  neg_mem' := fun {a} ha => by simpa [Set.mem_setOf_eq, norm_neg] using ha

theorem mem_ballSub {r : ℝ} {hr : 0 ≤ r} {x : PadicAlgCl l} : x ∈ ballSub r hr ↔ ‖x‖ ≤ r := Iff.rfl

theorem cg_iff {n : ℕ} {a b : Qbar l} : Cg n a b ↔ a - b ∈ ballSub (l := l) ‖((l : ℕ) : Qbar l) ^ n‖ (norm_nonneg _) := Iff.rfl

theorem mul_mem_ballSub {r : ℝ} {hr : 0 ≤ r} {k x : PadicAlgCl l} (hk : ‖k‖ ≤ 1) (hx : x ∈ ballSub r hr) :
    k * x ∈ ballSub r hr := by
  rw [mem_ballSub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hk).trans hx

theorem norm_le_one_of_int (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral ..)

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  norm_le_one_of_int x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

end GlobalTheory.BrTame


open GlobalTheory.BrTame in
theorem GlobalTheory.br_tame : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (w : Pl) (B : ValuationSubring Ω) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (h : G ℚ Ω → Qbar l) (σ : G ℚ Ω), 1 ≤ n → IsPlaceOver B w → l ^ n ∣ normV w - 1 → (∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) → (∀ s, h s ∈ c.O) → (∀ s ∈ Dec (F := ℚ) B, ∀ t ∈ Dec (F := ℚ) B, Cg n (h (s * t)) (h s + h t)) → (∀ s ∈ Ine (F := ℚ) B, Cg n (h s) 0) → Cob2 c n (Dec (F := ℚ) B) (fun s t => (((ψ s).toAdd.val : ℕ) : Qbar l) * h t) → σ ∈ Dec (F := ℚ) B → Cg n (h σ) 0 := by
  intro l _ Ω _ _ _ c n w B ψ h σ hn hB hdiv ⟨τ, hτ, hψτ⟩ hO _ hIne ⟨u, hucont, huO, hu⟩ hσ
  set S := ballSub (l := l) ‖((l : ℕ) : Qbar l) ^ n‖ (norm_nonneg _) with hS
  have hu1 : ∀ s, ‖u s‖ ≤ 1 := fun s => norm_le_one_of_mem c (huO s)
  have heps : ∀ s ∈ Dec (F := ℚ) B, eps l s - 1 ∈ S := fun s hs => GlobalTheory.T.cyclotomicChar_congruent_one_on_decompositionGroup l Ω n w B hB hdiv hn s hs
  have hnat : ∀ k : ℕ, ‖((k : ℕ) : Qbar l)‖ ≤ 1 := fun k => IsUltrametricDist.norm_natCast_le_one _ k
  have hmul : ∀ k x : Qbar l, ‖k‖ ≤ 1 → x ∈ S → k * x ∈ S := fun k x hk hx => mul_mem_ballSub hk hx
  have hIne' : ∀ s ∈ Ine (F := ℚ) B, h s ∈ S := fun s hs => by
    have := cg_iff.1 (hIne s hs)
    rwa [sub_zero] at this
  have hIneDec : ∀ s ∈ Ine (F := ℚ) B, s ∈ Dec (F := ℚ) B := fun s hs => Ine_le_Dec B hs

  set T := ballSub (l := l) 1 zero_le_one with hT
  let M := T ⧸ S.comap T.subtype
  let f : G ℚ Ω → M := fun s => QuotientAddGroup.mk ⟨u s, hu1 s⟩
  have hf : ∀ s t, f s = f t ↔ u s - u t ∈ S := fun s t => by
    show (QuotientAddGroup.mk _ : M) = QuotientAddGroup.mk _ ↔ _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_comap]
    change -u s + u t ∈ S ↔ _
    have e : -u s + u t = -(u s - u t) := by ring
    rw [e, S.neg_mem_iff]
  have hlpos : 0 < ‖((l : ℕ) : Qbar l) ^ n‖ := norm_pos_iff.2 (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  have htors : ∀ x : M, l ^ n • x = 0 := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H y =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap, AddSubgroup.coe_subtype,
        AddSubgroup.coe_nsmul, nsmul_eq_mul, mem_ballSub, norm_mul, Nat.cast_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) y.2
  have hloc : IsLocallyConstant (fun s : Ine (F := ℚ) B => f s) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    have hc : Continuous (fun s : Ine (F := ℚ) B => u s) :=
      (hucont.mono (fun s hs => hIneDec s hs)).comp_continuous continuous_subtype_val (fun s => s.2)
    refine ⟨(fun s : Ine (F := ℚ) B => u s) ⁻¹' Metric.ball (u x) ‖((l : ℕ) : Qbar l) ^ n‖,
      Metric.isOpen_ball.preimage hc, Metric.mem_ball_self hlpos, fun y hy => ?_⟩
    rw [hf, mem_ballSub]
    have := Metric.mem_ball.1 hy
    rw [dist_eq_norm] at this
    exact this.le
  have hadd : ∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, f (s * t) = f s + f t := by
    intro s hs t ht
    have e : f s + f t = QuotientAddGroup.mk (⟨u s, hu1 s⟩ + ⟨u t, hu1 t⟩ : T) := rfl
    rw [e]
    show (QuotientAddGroup.mk _ : M) = QuotientAddGroup.mk _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_comap]
    change -u (s * t) + (u s + u t) ∈ S
    have h1 := hu s (hIneDec s hs) t (hIneDec t ht)
    have h2 := hmul _ _ (hnat ((ψ s).toAdd.val)) (hIne' t ht)
    have h3 := hmul _ _ (hu1 t) (heps s (hIneDec s hs))
    rw [cg_iff] at h1
    have e2 : -u (s * t) + (u s + u t) =
        -((((ψ s).toAdd.val : ℕ) : Qbar l) * h t - (eps l s * u t - u (s * t) + u s))
          + (((ψ s).toAdd.val : ℕ) : Qbar l) * h t - u t * (eps l s - 1) := by ring
    rw [e2]
    exact S.sub_mem (S.add_mem (S.neg_mem h1) h2) h3
  have hconj := GlobalTheory.T.inertiaTorsionQuotient_conj_invariant_decomposition l Ω n w B M f hB hdiv hn htors hloc hadd σ hσ τ hτ
  rw [hf] at hconj
  set τ' := σ * τ * σ⁻¹ with hτ'
  have hτ'I : τ' ∈ Ine (F := ℚ) B := conj_mem_Ine hσ hτ
  have hprod : τ' * σ = σ * τ := by rw [hτ']; group
  have hψ' : ((ψ τ').toAdd.val : Qbar l) = 1 := by
    have e : ψ τ' = ψ τ := by rw [hτ', map_mul, map_mul, mul_comm (ψ σ), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    have hl1 : 1 < l ^ n := Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt
    rw [e, hψτ, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hl1, Nat.cast_one]
  have hA := hu τ' (hIneDec τ' hτ'I) σ hσ
  have hB' := hu σ hσ τ (hIneDec τ hτ)
  dsimp only at hA hB'
  rw [cg_iff, hprod, hψ', one_mul] at hA
  rw [cg_iff] at hB'
  have hC := hmul _ _ (hnat ((ψ σ).toAdd.val)) (hIne' τ hτ)
  have hD := hmul _ _ (hu1 σ) (heps τ' (hIneDec τ' hτ'I))
  have hF := hmul _ _ (hu1 τ) (heps σ hσ)
  rw [cg_iff, sub_zero]
  have e : h σ = (h σ - (eps l τ' * u σ - u (σ * τ) + u τ')) + u σ * (eps l τ' - 1) + (u τ' - u τ)
      - ((((ψ σ).toAdd.val : ℕ) : Qbar l) * h τ - (eps l σ * u τ - u (σ * τ) + u σ))
      + (((ψ σ).toAdd.val : ℕ) : Qbar l) * h τ - u τ * (eps l σ - 1) := by ring
  rw [e]
  exact S.sub_mem (S.add_mem (S.sub_mem (S.add_mem (S.add_mem hA hD) hconj) hB') hC) hF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameCochainCocycleExtensionStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_cochain_cocycle_extension : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (w : Pl) (B : ValuationSubring Ω) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (h : G ℚ Ω → Qbar l) (σ : G ℚ Ω), 1 ≤ n → IsPlaceOver B w → l ^ n ∣ normV w - 1 → (∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) → (∀ s, h s ∈ c.O) → (∀ s ∈ Dec (F := ℚ) B, ∀ t ∈ Dec (F := ℚ) B, Cg n (h (s * t)) (h s + h t)) → (∀ s ∈ Ine (F := ℚ) B, Cg n (h s) 0) → Cob2 c n (Dec (F := ℚ) B) (fun s t => (((ψ s).toAdd.val : ℕ) : Qbar l) * h t) → σ ∈ Dec (F := ℚ) B → Cg n (h σ) 0 := by
  first | exact @GlobalTheory.br_tame | exact GlobalTheory.br_tame | (intros; apply GlobalTheory.br_tame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalHeightFrobeniusPlace
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.LocW

open GlobalTheory.Ord2.CupCob

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem sm_add {L : ℝ} {x y : Qbar l} (hx : ‖x‖ ≤ L) (hy : ‖y‖ ≤ L) : ‖x + y‖ ≤ L :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

theorem sm_neg {L : ℝ} {x : Qbar l} (hx : ‖x‖ ≤ L) : ‖-x‖ ≤ L := by rwa [norm_neg]

theorem sm_sub {L : ℝ} {x y : Qbar l} (hx : ‖x‖ ≤ L) (hy : ‖y‖ ≤ L) : ‖x - y‖ ≤ L := by
  rw [sub_eq_add_neg]; exact sm_add hx (sm_neg hy)

theorem sm_mul {L : ℝ} {k x : Qbar l} (hk : ‖k‖ ≤ 1) (hx : ‖x‖ ≤ L) : ‖k * x‖ ≤ L := by
  rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hk).trans hx

theorem nat_norm (k : ℕ) : ‖(k : Qbar l)‖ ≤ 1 := by
  have : (k : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((k : ℤ_[l]) : ℚ_[l]) := by simp
  rw [this, norm_algebraMap']
  exact PadicInt.norm_le_one _

theorem eps_val (s : G ℚ Ω) : eps l s = algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := rfl

theorem eps_norm (s : G ℚ Ω) : ‖eps l s‖ = 1 := by
  rw [eps_val, norm_algebraMap']
  exact PadicInt.norm_units _

theorem eps_mul (s t : G ℚ Ω) : eps l (s * t) = eps l s * eps l t := by simp [eps, map_mul]

theorem eps_one : eps l (1 : G ℚ Ω) = 1 := by simp [eps]

theorem eps_inv_mul (s : G ℚ Ω) : eps l s⁻¹ * eps l s = 1 := by rw [← eps_mul, inv_mul_cancel, eps_one]

theorem normV_eq (v : Pl) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem dvd_of_mem {I : Ideal (𝓞 ℚ)} {n : ℕ} (h : (n : 𝓞 ℚ) ∈ I) : Ideal.absNorm I ∣ n := by
  have h1 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem I).2 h)
  rwa [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one] at h1

theorem mem_iff (v : Pl) (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ normV v ∣ n := by
  rw [normV_eq]
  refine ⟨dvd_of_mem, ?_⟩
  rintro ⟨c, rfl⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem normV_prime (v : Pl) : (normV v).Prime := by
  have h1 : 1 < normV v := by
    rw [normV_eq]
    exact NumberField.HeightOneSpectrum.one_lt_absNorm v
  refine Nat.prime_def.2 ⟨h1, fun m hm => ?_⟩
  obtain ⟨c, hc⟩ := hm
  have h2 := (mem_iff v _).2 dvd_rfl
  rw [hc, Nat.cast_mul] at h2
  rcases v.isPrime.mem_or_mem h2 with h | h
  · exact Or.inr (Nat.dvd_antisymm ⟨c, hc⟩ ((mem_iff v _).1 h))
  · have h3 := Nat.dvd_antisymm (Dvd.intro_left m hc.symm) ((mem_iff v _).1 h)
    rw [h3] at hc
    exact Or.inl (Nat.eq_of_mul_eq_mul_right (by omega) (hc.symm.trans (one_mul _).symm))

theorem not_mem_l {w : Pl} {n : ℕ} (hn : 1 ≤ n) (hw : l ^ n ∣ normV w - 1) : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  intro h
  have h1 := (mem_iff w l).1 h
  have h2 : normV w = l := (Nat.prime_dvd_prime_iff_eq (normV_prime w) (Fact.out : l.Prime)).1 h1
  rw [h2] at hw
  have hl := (Fact.out : l.Prime).two_le
  have h3 : l ^ n ≤ l - 1 := Nat.le_of_dvd (by omega) hw
  have h4 : l ≤ l ^ n := Nat.le_self_pow (by omega) l
  omega

theorem eps_ine [IsAlgClosure ℚ Ω] {B : ValuationSubring Ω} {w : Pl} (hl : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal)
    (hB : IsPlaceOver B w) {a : G ℚ Ω} (ha : a ∈ Ine (F := ℚ) B) : eps l a = 1 := by
  have h1 : cycZ ℚ Ω l a = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun k => ?_)
    rw [cycZ_toZModPow_eq hl hB (q := 1) (fun x hx => by simpa using ha.2 x hx) k]
    simp
  rw [eps_val, h1]; simp

theorem eps_frob [IsAlgClosure ℚ Ω] {B : ValuationSubring Ω} {w : Pl} (hl : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal)
    (hB : IsPlaceOver B w) {τ : G ℚ Ω} (hτ : IsFrob B (normV w) τ) : eps l τ = ((normV w : ℕ) : Qbar l) := by
  rw [eps_val, cycZ_of_isFrob hl hB hτ]; simp

theorem cg_norm {w : Pl} {n : ℕ} (hw : l ^ n ∣ normV w - 1) : Cg n ((normV w : ℕ) : Qbar l) 1 := by
  obtain ⟨k, hk⟩ := hw
  have h0 : 1 ≤ normV w := (normV_prime w).one_lt.le
  have e : ((normV w : ℕ) : Qbar l) - 1 = ((l : ℕ) : Qbar l) ^ n * (k : Qbar l) := by
    have : normV w = l ^ n * k + 1 := by omega
    rw [this]; push_cast; ring
  show ‖_‖ ≤ _
  rw [e, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (nat_norm k)

theorem gen [IsAlgClosure ℚ Ω] {B : ValuationSubring Ω} {w : Pl} {τ : G ℚ Ω}
    (hB : IsPlaceOver B w) (hτ : IsFrob B (normV w) τ) (Q : G ℚ Ω → Prop) (hQ : IsClosed {s | Q s})
    (hI : ∀ a ∈ Ine (F := ℚ) B, Q a) (hτQ : Q τ)
    (hmul : ∀ s ∈ Dec (F := ℚ) B, ∀ t ∈ Dec (F := ℚ) B, Q s → Q t → Q (s * t))
    (hinv : ∀ s ∈ Dec (F := ℚ) B, Q s → Q s⁻¹) : ∀ s ∈ Dec (F := ℚ) B, Q s := by
  haveI : IsGalois ℚ Ω := {}
  set S : Subgroup (G ℚ Ω) := Subgroup.closure (insert τ (Ine (F := ℚ) B : Set (G ℚ Ω))) with hS
  have hSQ : ∀ s ∈ S, s ∈ Dec (F := ℚ) B ∧ Q s := by
    intro s hs
    induction hs using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨hτ.1, hτQ⟩
      · exact ⟨Ine_le_Dec B hx, hI x hx⟩
    | one => exact ⟨(Dec (F := ℚ) B).one_mem, hI 1 (Ine (F := ℚ) B).one_mem⟩
    | mul x y _ _ hx hy => exact ⟨(Dec (F := ℚ) B).mul_mem hx.1 hy.1, hmul x hx.1 y hy.1 hx.2 hy.2⟩
    | inv x _ hx => exact ⟨(Dec (F := ℚ) B).inv_mem hx.1, hinv x hx.1 hx.2⟩
  have hD : Dec (F := ℚ) B ≤ S.topologicalClosure := by
    have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G ℚ Ω)
      ⟨S.topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
    refine le_trans (le_sInf ?_) key.ge
    rintro N ⟨hNo, hN⟩
    have h := (Subgroup.le_topologicalClosure _).trans hN
    exact Kum.decGen ℚ Ω B w τ N hB hτ hNo
      (fun a ha => h (Subgroup.subset_closure (Set.mem_insert_of_mem _ ha)))
      (h (Subgroup.subset_closure (Set.mem_insert _ _)))
  intro s hs
  have h1 : (S.topologicalClosure : Set (G ℚ Ω)) ⊆ {s | Q s} := by
    rw [Subgroup.topologicalClosure_coe]
    exact closure_minimal (fun x hx => (hSQ x hx).2) hQ
  exact h1 (hD hs)

theorem eps_dec [IsAlgClosure ℚ Ω] {B : ValuationSubring Ω} {w : Pl} {τ : G ℚ Ω} {n : ℕ} (hn : 1 ≤ n)
    (hB : IsPlaceOver B w) (hw : l ^ n ∣ normV w - 1) (hτ : IsFrob B (normV w) τ) :
    ∀ s ∈ Dec (F := ℚ) B, Cg n (eps l s) 1 := by
  have hl := not_mem_l hn hw
  refine gen hB hτ (fun s => Cg n (eps l s) 1) ?_ ?_ ?_ ?_ ?_
  · exact isClosed_le ((eps_cont.sub continuous_const).norm) continuous_const
  · intro a ha
    show ‖_‖ ≤ _
    rw [eps_ine hl hB ha, sub_self, norm_zero]; exact norm_nonneg _
  · show Cg n (eps l τ) 1
    rw [eps_frob hl hB hτ]; exact cg_norm hw
  · intro s _ t _ hs ht
    show ‖_‖ ≤ _
    have e : eps l (s * t) - 1 = eps l s * (eps l t - 1) + (eps l s - 1) := by rw [eps_mul]; ring
    rw [e]; exact sm_add (sm_mul (eps_norm s).le ht) hs
  · intro s _ hs
    show ‖_‖ ≤ _
    have e : eps l s⁻¹ - 1 = -(eps l s⁻¹ * (eps l s - 1)) := by linear_combination eps_inv_mul (l := l) s
    rw [e]; exact sm_neg (sm_mul (eps_norm _).le hs)

theorem det_dec [IsAlgClosure ℚ Ω] {B : ValuationSubring Ω} {w : Pl} {τ : G ℚ Ω}
    (hB : IsPlaceOver B w) (hτ : IsFrob B (normV w) τ) (W : R2 Ω l) (hW : Continuous W)
    (hI : Ine (F := ℚ) B ≤ W.ker) (hdt : dt W τ = 1) : ∀ s ∈ Dec (F := ℚ) B, (mat W s).det = 1 := by
  have hm : ∀ s t, mat W (s * t) = mat W s * mat W t := fun s t => by simp [mat]
  refine gen hB hτ (fun s => (mat W s).det = 1) ?_ (fun a ha => ?_) ?_ ?_ ?_
  · exact isClosed_eq (Units.continuous_val.comp hW).matrix_det continuous_const
  · show (mat W a).det = 1
    rw [mat, MonoidHom.mem_ker.1 (hI ha)]; simp
  · have := congrArg (fun u : (Qbar l)ˣ => (u : Qbar l)) hdt
    simpa [dt, mat] using this
  · intro s _ t _ hs ht
    show (mat W (s * t)).det = 1
    rw [hm, Matrix.det_mul, hs, ht, one_mul]
  · intro s _ hs
    show (mat W s⁻¹).det = 1
    have h1 : (mat W s⁻¹).det * (mat W s).det = 1 := by
      rw [← Matrix.det_mul, ← hm, inv_mul_cancel]; simp [mat]
    rwa [hs, mul_one] at h1

theorem coc_dec [IsAlgClosure ℚ Ω] {B : ValuationSubring Ω} {w : Pl} {τ : G ℚ Ω}
    (hB : IsPlaceOver B w) (hτ : IsFrob B (normV w) τ) {L : ℝ}
    (A : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (hA : ∀ s i j, ‖A s i j‖ ≤ 1)
    (c : G ℚ Ω → Fin 2 → Qbar l) (hc : Continuous c) (hmul : ∀ s t, c (s * t) = c s + A s *ᵥ c t)
    (hI : ∀ a ∈ Ine (F := ℚ) B, c a = 0) (hτc : ∀ i, ‖c τ i‖ ≤ L) :
    ∀ s ∈ Dec (F := ℚ) B, ∀ i, ‖c s i‖ ≤ L := by
  have hL : 0 ≤ L := (norm_nonneg _).trans (hτc 0)
  refine gen hB hτ (fun s => ∀ i, ‖c s i‖ ≤ L) ?_ (fun a ha i => ?_) hτc ?_ ?_
  · have : {s | ∀ i, ‖c s i‖ ≤ L} = ⋂ i, {s | ‖c s i‖ ≤ L} := by ext; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_le ((continuous_apply i).comp hc).norm continuous_const
  · rw [hI a ha]; simpa using hL
  · intro s _ t _ hs ht i
    rw [hmul, Pi.add_apply]
    exact sm_add (hs i) (mulVec_le _ _ (hA s) ht i)
  · intro s _ hs i
    have h1 : c 1 = 0 := hI 1 (Ine (F := ℚ) B).one_mem
    have h2 := hmul s⁻¹ s
    rw [inv_mul_cancel, h1] at h2
    have h3 : c s⁻¹ = -(A s⁻¹ *ᵥ c s) := by
      rw [eq_neg_iff_add_eq_zero]; exact h2.symm
    rw [h3, Pi.neg_apply]
    exact sm_neg (mulVec_le _ _ (hA s⁻¹) hs i)

end GlobalTheory.Ord2.LocW

namespace GlobalTheory.Ord2.LocW

variable {l : ℕ} [Fact l.Prime]

theorem sm_mul' {L : ℝ} {k x : Qbar l} (hx : ‖x‖ ≤ L) (hk : ‖k‖ ≤ 1) : ‖x * k‖ ≤ L := by
  rw [mul_comm]; exact sm_mul hk hx

theorem ident_add (ys yt zt Vt b : Fin 2 → Qbar l) (Ws Ds : Matrix (Fin 2) (Fin 2) (Qbar l)) (de es ust us ut : Qbar l)
    (key : om (Ws *ᵥ yt) (Ds *ᵥ Vt) = es * om yt Vt) :
    (de * ust + om (ys + Ws *ᵥ yt) (Ds *ᵥ Vt)) - ((de * us + om ys (Ds *ᵥ b)) + (de * ut + om yt Vt)) =
      de * ((es - 1) * ut) + de * (om ys (Ds *ᵥ zt) - (es * ut - ust + us)) + om ys (Ds *ᵥ (Vt - b - de • zt)) +
        (es - 1) * om yt Vt := by
  simp only [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at *
  linear_combination key

theorem ident_cob (ds dt dst yt zt Vt b : Fin 2 → Qbar l) (Ws Ds : Matrix (Fin 2) (Fin 2) (Qbar l))
    (ps P de es ut u't u'st u's : Qbar l)
    (key1 : om (Ws *ᵥ dt) (Ds *ᵥ Vt) = es * om dt Vt) (key2 : om (Ws *ᵥ yt) (Ds *ᵥ Vt) = es * om yt Vt) :
    ps * (P * (de * ut + om yt Vt)) -
        (es * -(de * u't + om dt Vt) - -(de * u'st + om dst (Ds *ᵥ Vt)) + -(de * u's + om ds (Ds *ᵥ b))) =
      ps * P * de * ut * (1 - es) + ps * P * om yt Vt * (1 - es) -
        de * ((om ds (Ds *ᵥ zt) - ps * P * es * ut) - (es * u't - u'st + u's)) -
        om ds (Ds *ᵥ (Vt - b - de • zt)) - om (dst - (ds + Ws *ᵥ dt + (ps * P) • (Ws *ᵥ yt))) (Ds *ᵥ Vt) := by
  simp only [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at *
  linear_combination -key1 - (ps * P) * key2

theorem ident_fin (A : Matrix (Fin 2) (Fin 2) (Qbar l)) (y z : Fin 2 → Qbar l) (e u : Qbar l) (hA : A.det = 1) :
    ((A - 1).det * u - om ((A - 1).adjugate *ᵥ y) z) - ((A - 1).det * u + om y ((e • A) *ᵥ ((A - 1).adjugate *ᵥ z))) =
      (e - 1) * om ((A - 1).adjugate *ᵥ y) z := by
  rw [Matrix.eta_fin_two A] at hA ⊢
  rw [Matrix.one_fin_two]
  simp only [Matrix.det_fin_two_of] at hA
  simp [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.adjugate_fin_two_of, Matrix.det_fin_two_of]
  linear_combination (-e * (y 0 * z 1 - y 1 * z 0)) * hA

theorem mul_adj_mulVec (A : Matrix (Fin 2) (Fin 2) (Qbar l)) (z : Fin 2 → Qbar l) :
    A *ᵥ ((A - 1).adjugate *ᵥ z) = (A - 1).adjugate *ᵥ z + (A - 1).det • z := by
  have h : ∀ v, A *ᵥ v = (A - 1) *ᵥ v + v := fun v => by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  rw [h, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec, add_comm]

end GlobalTheory.Ord2.LocW


open GlobalTheory.Ord2.CupCob GlobalTheory.Ord2.LocW in
theorem GlobalTheory.Ord2.LocW.local_height_at_frobenius : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (y z d : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l) (P : Qbar l) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (w : Pl) (B : ValuationSubring Ω) (τ : G ℚ Ω), 1 ≤ n → Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → IsPlaceOver B w → l ^ n ∣ normV w - 1 → IsFrob B (normV w) τ → τ ∈ Dec (F := ℚ) B → dt W τ = 1 → Ine (F := ℚ) B ≤ W.ker → IsLocallyConstant ψ → (∃ t ∈ Ine (F := ℚ) B, (ψ t).toAdd = 1) → P ∈ c.O → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, y s i ∈ c.O) → (∀ s i, z s i ∈ c.O) → (∀ a ∈ Ine (F := ℚ) B, y a = 0 ∧ z a = 0) → Continuous u → (∀ s, u s ∈ c.O) → (∀ s, ∀ a ∈ Ine (F := ℚ) B, Cg n (u (s * a)) (u s)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → Continuous d → (∀ s i, d s i ∈ c.O) → (∀ s t, Cv n (d (s * t)) (d s + mat W s *ᵥ d t + ((((ψ s).toAdd.val : ℕ) : Qbar l) * P) • (mat W s *ᵥ y t))) → Cob2 c n (Dec (F := ℚ) B) (fun s t => cup W d z s t - (((ψ s).toAdd.val : ℕ) : Qbar l) * P * eps l s * u t) → Cg n (P * ht W y z u τ) 0 := by
  intro l _ Ω _ _ _ c n W y z d u P ψ w B τ hn hW hint hdet hB hw hτ hτD hdtτ hIW hψlc hψram hP hy hz hyO hzO hyzI hu huO
    huI hcup hd hdO hdc hcob
  have hWn : ∀ s i j, ‖mat W s i j‖ ≤ 1 := fun s i j => norm_le_one_of_mem c (hint s i j)
  have hDm : ∀ s i j, mat (dual1 W) s i j ∈ c.O := dual_representation_integral c W hdet hint
  have hDn : ∀ s i j, ‖mat (dual1 W) s i j‖ ≤ 1 := fun s i j => norm_le_one_of_mem c (hDm s i j)
  have hyn : ∀ s i, ‖y s i‖ ≤ 1 := fun s i => norm_le_one_of_mem c (hyO s i)
  have hzn : ∀ s i, ‖z s i‖ ≤ 1 := fun s i => norm_le_one_of_mem c (hzO s i)
  have hdn : ∀ s i, ‖d s i‖ ≤ 1 := fun s i => norm_le_one_of_mem c (hdO s i)
  have hun : ∀ s, ‖u s‖ ≤ 1 := fun s => norm_le_one_of_mem c (huO s)
  have hPn : ‖P‖ ≤ 1 := norm_le_one_of_mem c hP
  have hl := not_mem_l hn hw
  have hM : Continuous fun s => mat W s := Units.continuous_val.comp hW
  have hDc : Continuous fun s => mat (dual1 W) s := by
    have : (fun s => mat (dual1 W) s) = fun s => (eps l s * (mat W s).det) • mat W s := funext (mat_dual1 W hdet)
    rw [this]
    exact (eps_cont.mul hM.matrix_det).smul hM
  have hyc : ∀ s t, y (s * t) = y s + mat W s *ᵥ y t := fun s t => hy.2 s t
  have hzc : ∀ s t, z (s * t) = z s + mat (dual1 W) s *ᵥ z t := fun s t => hz.2 s t
  obtain ⟨de, hde⟩ : ∃ de, de = (mat W τ - 1).det := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = (mat W τ - 1).adjugate *ᵥ z τ := ⟨_, rfl⟩
  have hMO : ∀ i j, (mat W τ - 1) i j ∈ c.O := fun i j => by
    rw [Matrix.sub_apply, Matrix.one_apply]
    split_ifs
    · exact sub_mem (hint τ i j) (one_mem _)
    · exact sub_mem (hint τ i j) (zero_mem _)
  have hdeO : de ∈ c.O := by
    rw [hde, Matrix.det_fin_two]
    exact sub_mem (mul_mem (hMO 0 0) (hMO 1 1)) (mul_mem (hMO 0 1) (hMO 1 0))
  have hadjO : ∀ i j, (mat W τ - 1).adjugate i j ∈ c.O := by
    generalize mat W τ - 1 = M at hMO ⊢
    intro i j
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp <;> first | exact hMO _ _ | exact neg_mem (hMO _ _)
  have hbO : ∀ i, b i ∈ c.O := fun i => by rw [hb]; exact mulVec_mem c _ _ hadjO (hzO τ) i
  have hbn : ∀ i, ‖b i‖ ≤ 1 := fun i => norm_le_one_of_mem c (hbO i)
  have hden : ‖de‖ ≤ 1 := norm_le_one_of_mem c hdeO
  have hεD := eps_dec hn hB hw hτ
  have hdetD := det_dec hB hτ W hW hIW hdtτ
  have hWdD : ∀ s ∈ Dec (F := ℚ) B, mat (dual1 W) s = eps l s • mat W s := fun s hs => by
    rw [mat_dual1 W hdet, hdetD s hs, mul_one]
  have hWI : ∀ a ∈ Ine (F := ℚ) B, mat W a = 1 := fun a ha => by
    rw [mat, MonoidHom.mem_ker.1 (hIW ha)]; rfl
  have hWdI : ∀ a ∈ Ine (F := ℚ) B, mat (dual1 W) a = 1 := fun a ha => by
    rw [hWdD a (Ine_le_Dec B ha), hWI a ha, eps_ine hl hB ha, one_smul]
  have hX : ∀ s ∈ Dec (F := ℚ) B, ∀ i, ‖(de • z s - (mat (dual1 W) s *ᵥ b - b)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
    refine coc_dec hB hτ (fun s => mat (dual1 W) s) hDn (fun s => de • z s - (mat (dual1 W) s *ᵥ b - b)) ?_ ?_ ?_ ?_
    · exact ((continuous_const : Continuous fun _ : G ℚ Ω => de).smul hz.1).sub ((hDc.matrix_mulVec continuous_const).sub continuous_const)
    · intro s t
      simp only [hzc, mat_dual1_mul]
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    · intro a ha
      simp only [(hyzI a ha).2, hWdI a ha, Matrix.one_mulVec, smul_zero, sub_self]
    · intro i
      have h1 : mat W τ *ᵥ b = b + de • z τ := by rw [hb, hde]; exact mul_adj_mulVec _ _
      have h2 : (de • z τ - (mat (dual1 W) τ *ᵥ b - b)) i = (1 - eps l τ) * (mat W τ *ᵥ b) i := by
        rw [hWdD τ hτD, Matrix.smul_mulVec, h1]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [h2]
      exact sm_mul' (by rw [norm_sub_rev]; exact hεD τ hτD) (mulVec_le _ _ (hWn τ) hbn i)
  have hX' : ∀ s ∈ Dec (F := ℚ) B, ∀ i, ‖(mat (dual1 W) s *ᵥ b - b - de • z s) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
    intro s hs i
    have e : mat (dual1 W) s *ᵥ b - b - de • z s = -(de • z s - (mat (dual1 W) s *ᵥ b - b)) := by abel
    rw [e, Pi.neg_apply, norm_neg]
    exact hX s hs i
  have hu1 : ‖u 1‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
    have h := hcup 1 1
    have hy1 : y 1 = 0 := (hyzI 1 (Ine (F := ℚ) B).one_mem).1
    unfold Cg cup at h
    rw [hy1, eps_one, one_mul, mul_one] at h
    have e : om 0 (mat (dual1 W) 1 *ᵥ z 1) = 0 := by simp [om]
    rw [e] at h
    simpa using h
  have huI' : ∀ a ∈ Ine (F := ℚ) B, ‖u a‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := fun a ha => by
    have h := huI 1 a ha
    rw [one_mul] at h
    have e : u a = (u a - u 1) + u 1 := by ring
    rw [e]
    exact sm_add h hu1
  have hint' : ∀ s, P * (de * u s + om (y s) (mat (dual1 W) s *ᵥ b)) ∈ c.O := fun s =>
    mul_mem hP (add_mem (mul_mem hdeO (huO s)) (om_mem c _ _ (hyO s) (mulVec_mem c _ _ (hDm s) hbO)))
  have hadd : ∀ s ∈ Dec (F := ℚ) B, ∀ t ∈ Dec (F := ℚ) B,
      Cg n (P * (de * u (s * t) + om (y (s * t)) (mat (dual1 W) (s * t) *ᵥ b)))
        (P * (de * u s + om (y s) (mat (dual1 W) s *ᵥ b)) + P * (de * u t + om (y t) (mat (dual1 W) t *ᵥ b))) := by
    intro s hs t ht
    show ‖_ - _‖ ≤ _
    rw [← mul_add, ← mul_sub]
    refine sm_mul hPn ?_
    rw [hyc, mat_dual1_mul, ident_add (y s) (y t) (z t) (mat (dual1 W) t *ᵥ b) b (mat W s) (mat (dual1 W) s) de (eps l s)
      (u (s * t)) (u s) (u t) (om_key W hdet s _ _)]
    refine sm_add (sm_add (sm_add ?_ ?_) ?_) ?_
    · exact sm_mul hden (sm_mul' (hεD s hs) (hun t))
    · exact sm_mul hden (hcup s t)
    · exact om_le_right _ _ (hyn s) (mulVec_le _ _ (hDn s) (hX' t ht))
    · exact sm_mul' (hεD s hs) (om_le_left _ _ (hyn t) (mulVec_le _ _ (hDn t) hbn))
  have hine : ∀ a ∈ Ine (F := ℚ) B, Cg n (P * (de * u a + om (y a) (mat (dual1 W) a *ᵥ b))) 0 := by
    intro a ha
    show ‖_ - _‖ ≤ _
    have e : om (y a) (mat (dual1 W) a *ᵥ b) = 0 := by rw [(hyzI a ha).1]; simp [om]
    rw [e, add_zero, sub_zero]
    exact sm_mul hPn (sm_mul hden (huI' a ha))
  have hvc : Continuous fun s => om (d s) (mat (dual1 W) s *ᵥ b) := by
    have hv : Continuous fun s => mat (dual1 W) s *ᵥ b := hDc.matrix_mulVec continuous_const
    show Continuous fun s => d s 0 * (mat (dual1 W) s *ᵥ b) 1 - d s 1 * (mat (dual1 W) s *ᵥ b) 0
    exact (((continuous_apply 0).comp hd).mul ((continuous_apply 1).comp hv)).sub
      (((continuous_apply 1).comp hd).mul ((continuous_apply 0).comp hv))
  have hcob' : Cob2 c n (Dec (F := ℚ) B) (fun s t => (((ψ s).toAdd.val : ℕ) : Qbar l) *
      (P * (de * u t + om (y t) (mat (dual1 W) t *ᵥ b)))) := by
    obtain ⟨u', hu'c, hu'O, hu'⟩ := hcob
    refine ⟨fun s => -(de * u' s + om (d s) (mat (dual1 W) s *ᵥ b)), ((continuousOn_const.mul hu'c).add hvc.continuousOn).neg,
      fun s => neg_mem (add_mem (mul_mem hdeO (hu'O s)) (om_mem c _ _ (hdO s) (mulVec_mem c _ _ (hDm s) hbO))), ?_⟩
    intro s hs t ht
    show ‖(((ψ s).toAdd.val : ℕ) : Qbar l) * (P * (de * u t + om (y t) (mat (dual1 W) t *ᵥ b))) -
      (eps l s * -(de * u' t + om (d t) (mat (dual1 W) t *ᵥ b)) - -(de * u' (s * t) + om (d (s * t)) (mat (dual1 W) (s * t) *ᵥ b)) +
        -(de * u' s + om (d s) (mat (dual1 W) s *ᵥ b)))‖ ≤ _
    rw [mat_dual1_mul, ident_cob (d s) (d t) (d (s * t)) (y t) (z t) (mat (dual1 W) t *ᵥ b) b (mat W s) (mat (dual1 W) s) _ P de
      (eps l s) (u t) (u' t) (u' (s * t)) (u' s) (om_key W hdet s _ _) (om_key W hdet s _ _)]
    have h1e : ‖1 - eps l s‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by rw [norm_sub_rev]; exact hεD s hs
    refine sm_sub (sm_sub (sm_sub (sm_add ?_ ?_) ?_) ?_) ?_
    · exact sm_mul (sm_mul' (sm_mul' (sm_mul' (nat_norm _) hPn) hden) (hun t)) h1e
    · exact sm_mul (sm_mul' (sm_mul' (nat_norm _) hPn) (om_le_left _ _ (hyn t) (mulVec_le _ _ (hDn t) hbn))) h1e
    · exact sm_mul hden (hu' s hs t ht)
    · exact om_le_right _ _ (hdn s) (mulVec_le _ _ (hDn s) (hX' t ht))
    · exact om_le_left _ _ (fun i => hdc s t i) (mulVec_le _ _ (hDn s) (fun i => mulVec_le _ _ (hDn t) hbn i))
  have hT : Cg n (P * (de * u τ + om (y τ) (mat (dual1 W) τ *ᵥ b))) 0 :=
    GlobalTheory.T.tame_cochain_cocycle_extension l Ω c n w B ψ (fun t => P * (de * u t + om (y t) (mat (dual1 W) t *ᵥ b))) τ hn hB hw hψram hint' hadd
      hine hcob' hτD
  show ‖_ - _‖ ≤ _
  have hT' : ‖P * (de * u τ + om (y τ) (mat (dual1 W) τ *ᵥ b))‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
    have := hT; unfold Cg at this; rwa [sub_zero] at this
  rw [sub_zero]
  have e : P * ht W y z u τ = P * (ht W y z u τ - (de * u τ + om (y τ) (mat (dual1 W) τ *ᵥ b))) +
      P * (de * u τ + om (y τ) (mat (dual1 W) τ *ᵥ b)) := by ring
  rw [e]
  refine sm_add (sm_mul hPn ?_) hT'
  rw [hWdD τ hτD, hde, hb]
  unfold ht
  rw [ident_fin (mat W τ) (y τ) (z τ) (eps l τ) (u τ) (hdetD τ hτD)]
  exact sm_mul' (hεD τ hτD) (om_le_left _ _ (mulVec_le _ _ (fun i j => norm_le_one_of_mem c (hadjO i j)) (hyn τ)) (hzn τ))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalHeightFrobeniusPlaceStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_height_frobenius_place : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (y z d : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l) (P : Qbar l) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (w : Pl) (B : ValuationSubring Ω) (τ : G ℚ Ω), 1 ≤ n → Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → IsPlaceOver B w → l ^ n ∣ normV w - 1 → IsFrob B (normV w) τ → τ ∈ Dec (F := ℚ) B → dt W τ = 1 → Ine (F := ℚ) B ≤ W.ker → IsLocallyConstant ψ → (∃ t ∈ Ine (F := ℚ) B, (ψ t).toAdd = 1) → P ∈ c.O → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, y s i ∈ c.O) → (∀ s i, z s i ∈ c.O) → (∀ a ∈ Ine (F := ℚ) B, y a = 0 ∧ z a = 0) → Continuous u → (∀ s, u s ∈ c.O) → (∀ s, ∀ a ∈ Ine (F := ℚ) B, Cg n (u (s * a)) (u s)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → Continuous d → (∀ s i, d s i ∈ c.O) → (∀ s t, Cv n (d (s * t)) (d s + mat W s *ᵥ d t + ((((ψ s).toAdd.val : ℕ) : Qbar l) * P) • (mat W s *ᵥ y t))) → Cob2 c n (Dec (F := ℚ) B) (fun s t => cup W d z s t - (((ψ s).toAdd.val : ℕ) : Qbar l) * P * eps l s * u t) → Cg n (P * ht W y z u τ) 0 := by
  first | exact @GlobalTheory.Ord2.LocW.local_height_at_frobenius | exact GlobalTheory.Ord2.LocW.local_height_at_frobenius | (intros; apply GlobalTheory.Ord2.LocW.local_height_at_frobenius <;> assumption)
end
