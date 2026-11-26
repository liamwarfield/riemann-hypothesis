module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.MemOfMulMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonvanishingTransferCharacterSumsPowerSeries

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientCharTrivialInertiaCyclotomicTower
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientCharTrivialInertiaCyclotomicTower
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

noncomputable section

namespace GlobalTheory.QuotInertia

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem fix_mu [IsAlgClosure ℚ Ω] (s : G ℚ Ω) (hs : cycBar ℚ Ω l s = 1) (ζ : Ω) (hζ : ζ ^ l = 1) :
    s ζ = ζ := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
    (algebraMap ℚ_[l] (Qbar l)).injective.comp (fun a b h => Subtype.ext h)
  have hz : cycZ ℚ Ω l s = 1 := by
    apply Units.map_injective (f := ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) hinj
    rw [map_one]
    exact hs
  have hz' : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) = 1 := hz
  have h := cyclotomicCharacter.spec l (n := 1) (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ (by rw [pow_one]; exact hζ)
  change s ζ = _ at h
  rw [h, hz', Units.val_one, map_one, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by rw [pow_one]; exact (Fact.out : l.Prime).one_lt), pow_one]

theorem fix_sqrt_unit (hl : l ≠ 2) {A : ValuationSubring Ω} (hA : OverL l A) {s : G ℚ Ω}
    (hs : s ∈ Ine (F := ℚ) A) (N : ℤ) (hN : ¬ (l : ℤ) ∣ N) (β : Ω) (hβ : β ^ 2 = N) : s β = β := by
  have hsq : (s β) ^ 2 = β ^ 2 := by rw [← map_pow, hβ, map_intCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  exfalso
  obtain ⟨-, hI⟩ := hs
  have hβ1 : A.valuation β ≤ 1 := by
    by_contra hc
    push_neg at hc
    have h1 : 1 < A.valuation β ^ 2 := one_lt_pow₀ hc two_ne_zero
    rw [← map_pow, hβ] at h1
    have : A.valuation (N : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A N)
    exact absurd h1 (not_lt.2 this)
  have h2 := hI β hβ1
  rw [h] at h2
  have h3 : A.valuation (((4 * N : ℤ) : Ω)) < 1 := by
    have e : ((4 * N : ℤ) : Ω) = (-β - β) ^ 2 := by push_cast; rw [← hβ]; ring
    rw [e, map_pow]
    exact pow_lt_one₀ zero_le' h2 two_ne_zero
  obtain ⟨v, hv, hlv⟩ := hA
  have h4 : ((4 * N : ℤ) : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [← hv]
    convert h3 using 2
    simp only [map_intCast, Int.cast_mul, Int.cast_ofNat, map_mul, map_ofNat, algebraMap.coe_mul, map_ratCast]
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hcop : IsCoprime (l : ℤ) (4 * N) := by
    rw [hp.irreducible.coprime_iff_not_dvd]
    intro hd
    rcases hp.dvd_or_dvd hd with h5 | h5
    · have h6 : l ∣ 4 := by exact_mod_cast h5
      have h7 : l ∣ 2 := (Fact.out : l.Prime).dvd_of_dvd_pow (n := 2) (by norm_num; exact h6)
      exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h7)
    · exact hN h5
  obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom (𝓞 ℚ))
  have hl' : (Int.castRingHom (𝓞 ℚ)) (l : ℤ) ∈ v.asIdeal := by simpa using hlv
  have h1 : (1 : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [← hab]
    exact add_mem (Ideal.mul_mem_left _ _ hl') (Ideal.mul_mem_left _ _ (by simpa using h4))
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem gauss_fix [IsAlgClosure ℚ Ω] (hl : l ≠ 2) (s : G ℚ Ω) (hs : ∀ ζ : Ω, ζ ^ l = 1 → s ζ = ζ) :
    ∃ (Gs : Ω) (c : ℤ), c ^ 2 = 1 ∧ Gs ^ 2 = ((c * l : ℤ) : Ω) ∧ s Gs = Gs := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  have hF : ringChar (ZMod l) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hl
  set ψ : AddChar (ZMod l) Ω := AddChar.zmodChar l hζ.pow_eq_one with hψdef
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root l hζ
  set χ : MulChar (ZMod l) Ω := (quadraticChar (ZMod l)).ringHomComp (Int.castRingHom Ω) with hχdef
  have hχ1 : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := Ω))).2 (quadraticChar_ne_one hF)
  have hχ2 : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod l)).comp _
  have hχa : ∀ x, χ x = ((quadraticChar (ZMod l) x : ℤ) : Ω) := fun x => rfl
  refine ⟨gaussSum χ ψ, quadraticChar (ZMod l) (-1), quadraticChar_sq_one (neg_ne_zero.2 one_ne_zero), ?_, ?_⟩
  · rw [gaussSum_sq hχ1 hχ2 hψ, hχa, ZMod.card]
    push_cast
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [gaussSum, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_mul, hχa, map_intCast, hψdef, AddChar.zmodChar_apply, map_pow, hs ζ hζ.pow_eq_one]

theorem fix_sqrt_int [IsAlgClosure ℚ Ω] (hl : l ≠ 2) {A : ValuationSubring Ω} (hA : OverL l A) {s : G ℚ Ω}
    (hs : s ∈ Ine (F := ℚ) A) (hmu : ∀ ζ : Ω, ζ ^ l = 1 → s ζ = ζ) :
    ∀ (N : ℤ) (α : Ω), α ^ 2 = N → s α = α := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  intro N
  induction hn : N.natAbs using Nat.strong_induction_on generalizing N with
  | _ n ih =>
  intro α hα
  by_cases h0 : N = 0
  · subst h0
    have : α = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by simpa using hα)
    rw [this, map_zero]
  by_cases hd : (l : ℤ) ∣ N
  · obtain ⟨N1, rfl⟩ := hd
    obtain ⟨Gs, c, hc, hG, hsG⟩ := gauss_fix hl s hmu
    have hc0 : (c : Ω) ≠ 0 := by
      rintro h
      have : c = 0 := by exact_mod_cast h
      rw [this] at hc
      norm_num at hc
    have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    have hG0 : Gs ≠ 0 := by
      rintro h
      rw [h] at hG
      push_cast at hG
      exact mul_ne_zero hc0 hl0 (by rw [← hG]; ring)
    have hc' : (c : Ω) ^ 2 = 1 := by exact_mod_cast hc
    have hβ : (α / Gs) ^ 2 = ((c * N1 : ℤ) : Ω) := by
      rw [div_pow, hα, hG]
      push_cast
      rw [div_eq_iff (mul_ne_zero hc0 hl0)]
      linear_combination (-(l : Ω) * N1) * hc'
    have hcabs : c.natAbs = 1 := by
      have h1 : (c ^ 2).natAbs = 1 := by rw [hc]; rfl
      rw [Int.natAbs_pow] at h1
      exact (pow_eq_one_iff.1 h1).resolve_right two_ne_zero
    have hN1 : N1 ≠ 0 := by rintro rfl; exact h0 (mul_zero _)
    have hlt : (c * N1).natAbs < n := by
      rw [← hn, Int.natAbs_mul, Int.natAbs_mul, hcabs, one_mul, Int.natAbs_natCast]
      have := Int.natAbs_pos.2 hN1
      have := (Fact.out : l.Prime).one_lt
      nlinarith
    have h1 := ih _ hlt (c * N1) rfl (α / Gs) hβ
    have e : α = α / Gs * Gs := (div_mul_cancel₀ α hG0).symm
    rw [e, map_mul, h1, hsG]
  · exact fix_sqrt_unit hl hA hs N hd α hα

theorem fix_sqrt_rat [IsAlgClosure ℚ Ω] (hl : l ≠ 2) {A : ValuationSubring Ω} (hA : OverL l A) {s : G ℚ Ω}
    (hs : s ∈ Ine (F := ℚ) A) (hmu : ∀ ζ : Ω, ζ ^ l = 1 → s ζ = ζ) (α : Ω) (q : ℚ)
    (hα : α ^ 2 = algebraMap ℚ Ω q) : s α = α := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hden : (q.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
  have hq : algebraMap ℚ Ω q * (q.den : Ω) = (q.num : Ω) := by
    rw [← map_natCast (algebraMap ℚ Ω), ← map_mul, Rat.mul_den_eq_num, map_intCast]
  have h := fix_sqrt_int hl hA hs hmu (q.num * q.den) (α * q.den) (by
    rw [mul_pow, hα]
    push_cast
    rw [← hq]
    ring)
  rw [map_mul, map_natCast] at h
  exact mul_right_cancel₀ hden h

theorem dt_eq_one [IsAlgClosure ℚ Ω] {W : R2 Ω l} (hcont : Continuous W) (hdet2 : dt W ^ 2 = 1) (s : G ℚ Ω)
    (hfix : ∀ (α : Ω) (q : ℚ), α ^ 2 = algebraMap ℚ Ω q → s α = α) : dt W s = 1 := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hval : ∀ g, ((dt W g : (Qbar l)ˣ) : Qbar l) = ((W g : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)).det :=
    fun g => Matrix.GeneralLinearGroup.val_det_apply _
  have hc : Continuous fun g : G ℚ Ω => ((dt W g : (Qbar l)ˣ) : Qbar l) := by
    simp only [hval]
    exact (Units.continuous_val.comp hcont).matrix_det
  have hcl : IsClosed ((dt W).ker : Set (G ℚ Ω)) := by
    have : ((dt W).ker : Set (G ℚ Ω)) = (fun g : G ℚ Ω => ((dt W g : (Qbar l)ˣ) : Qbar l)) ⁻¹' {1} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => by rw [h, Units.val_one], fun h => Units.ext (by rw [h, Units.val_one])⟩
    rw [this]
    exact isClosed_singleton.preimage hc
  let Hc : ClosedSubgroup (G ℚ Ω) := ⟨(dt W).ker, hcl⟩
  have hpm : ∀ g, dt W g = 1 ∨ dt W g = -1 := by
    intro g
    have h2 : (dt W g) ^ 2 = 1 := by
      have := congrArg (fun f => f g) hdet2
      simpa using this
    have hv : ((dt W g : (Qbar l)ˣ) : Qbar l) * ((dt W g : (Qbar l)ˣ) : Qbar l) = 1 := by
      rw [← Units.val_mul, ← pow_two, h2, Units.val_one]
    rcases mul_self_eq_one_iff.1 hv with h | h
    · exact Or.inl (Units.ext (by rw [h, Units.val_one]))
    · exact Or.inr (Units.ext (by rw [h, Units.val_neg, Units.val_one]))
  have hsub : s ∈ (IntermediateField.fixedField (Hc : Subgroup (G ℚ Ω))).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hsame : ∀ g1 g2 : G ℚ Ω, dt W g1 = dt W g2 → g1 x = g2 x := by
      intro g1 g2 h
      have hm : g2⁻¹ * g1 ∈ (Hc : Subgroup (G ℚ Ω)) := by
        show g2⁻¹ * g1 ∈ (dt W).ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
      have h1 := hx _ hm
      calc g1 x = g2 ((g2⁻¹ * g1) x) := by
            rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
        _ = g2 x := by rw [h1]
    rcases hpm s with h1 | h1
    · exact hx s (show s ∈ (dt W).ker from h1)
    have hs2 : (s * s) x = x := by
      rw [hsame (s * s) 1 (by rw [map_mul, h1, map_one]; simp)]
      rfl
    have hsα : s (x - s x) = -(x - s x) := by
      rw [map_sub, ← AlgEquiv.mul_apply, hs2]
      ring
    have hgα : ∀ g : G ℚ Ω, (g (x - s x)) ^ 2 = (x - s x) ^ 2 := by
      intro g
      rw [map_sub, ← AlgEquiv.mul_apply]
      rcases hpm g with h2 | h2
      · rw [hsame g 1 (by rw [h2, map_one]), hsame (g * s) s (by rw [map_mul, h2, one_mul])]
        rfl
      · rw [hsame g s (by rw [h2, h1]), hsame (g * s) 1 (by rw [map_mul, h2, h1, map_one]; simp)]
        show (s x - x) ^ 2 = (x - s x) ^ 2
        ring
    obtain ⟨q, hq⟩ : ∃ q : ℚ, (x - s x) ^ 2 = algebraMap ℚ Ω q := by
      have hmem : (x - s x) ^ 2 ∈ IntermediateField.fixedField (⊥ : IntermediateField ℚ Ω).fixingSubgroup := by
        rw [IntermediateField.mem_fixedField_iff]
        intro f _
        rw [map_pow]
        exact hgα f
      rw [InfiniteGalois.fixedField_fixingSubgroup, IntermediateField.mem_bot] at hmem
      obtain ⟨q, hq⟩ := hmem
      exact ⟨q, hq.symm⟩
    have h3 := hfix _ q hq
    rw [hsα] at h3
    have h4 : (2 : Ω) * (x - s x) = 0 := by linear_combination -h3
    have h5 := (mul_eq_zero.1 h4).resolve_left two_ne_zero
    exact (sub_eq_zero.1 h5).symm
  rw [InfiniteGalois.fixingSubgroup_fixedField Hc] at hsub
  exact hsub

end GlobalTheory.QuotInertia


open GlobalTheory.QuotInertia in
theorem GlobalTheory.quot_eq_one_of_cycBar_eq_one : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)),
    Nf e S A W → SrcUr ι e A W g → ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 → mat W s 1 1 = 1 := by
  intro l _ Ω _ _ _ ι e S A W g hNf hSrc s hs hc
  obtain ⟨-, -, χ, hχ, -, hI⟩ := hSrc
  have hmu := fix_mu s hc
  have hχs : χ s = 1 := hχ s hmu
  have hdt := dt_eq_one hNf.cont hNf.det2 s (fun α q hq => fix_sqrt_rat hNf.l_odd hNf.atL hs hmu α q hq)
  have h := hI s hs
  rw [hc, hχs, hdt] at h
  simpa using h

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientCharTrivialInertiaCyclotomicTowerStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_char_trivial_inertia_cyclotomic_tower : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g → ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 → mat W s 1 1 = 1 := by
  first | exact @GlobalTheory.quot_eq_one_of_cycBar_eq_one | exact GlobalTheory.quot_eq_one_of_cycBar_eq_one | (intros; apply GlobalTheory.quot_eq_one_of_cycBar_eq_one <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7.LocalUnitsRoots

variable {l : ℕ} [Fact l.Prime]

private theorem cg_symm {n : ℕ} {x y : Qbar l} (h : Cg n x y) : Cg n y x := by
  unfold Cg at *; rwa [norm_sub_rev]

private theorem cg_trans {n : ℕ} {x y w : Qbar l} (h₁ : Cg n x y) (h₂ : Cg n y w) : Cg n x w := by
  unfold Cg at *
  calc ‖x - w‖ = ‖(x - y) + (y - w)‖ := by ring_nf
    _ ≤ max ‖x - y‖ ‖y - w‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le h₁ h₂

private theorem cg_mono {n n' : ℕ} (hn : n ≤ n') {x y : Qbar l} (h : Cg n' x y) : Cg n x y := by
  unfold Cg at *
  refine h.trans ?_
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ l) hn

private theorem cg_mul {n : ℕ} {t x y : Qbar l} (ht : ‖t‖ ≤ 1) (h : Cg n x y) : Cg n (t * x) (t * y) := by
  unfold Cg at *
  rw [← mul_sub, norm_mul]
  calc ‖t‖ * ‖x - y‖ ≤ 1 * ‖x - y‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h

private theorem norm_char_le_one {N : ℕ} [NeZero N] (ψ : DirichletCharacter (Qbar l) N) (x : ZMod N) : ‖ψ x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    have h1 : (ψ (u : ZMod N)) ^ (Fintype.card (ZMod N)ˣ) = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    have h2 : ‖ψ (u : ZMod N)‖ ^ (Fintype.card (ZMod N)ˣ) = 1 := by rw [← norm_pow, h1, norm_one]
    have hc : Fintype.card (ZMod N)ˣ ≠ 0 := Fintype.card_ne_zero
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hc).mp h2)
  · rw [MulChar.map_nonunit ψ hx, norm_zero]; exact zero_le_one

private theorem norm_factor_le_one {N : ℕ} [NeZero N] (ψ : DirichletCharacter (Qbar l) N) (d : ℕ) :
    ‖(1 - (d : Qbar l) * ψ (d : ZMod N))‖ ≤ 1 := by
  have h1 := norm_char_le_one ψ (d : ZMod N)
  have h2 := IsUltrametricDist.norm_natCast_le_one (Qbar l) d
  calc _ ≤ max ‖(1 : Qbar l)‖ ‖(d : Qbar l) * ψ (d : ZMod N)‖ := by
        rw [sub_eq_add_neg, ← norm_neg ((d : Qbar l) * _)]; exact IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := by
      refine max_le (by rw [norm_one]) ?_
      rw [norm_mul]
      calc _ ≤ 1 * 1 := mul_le_mul h2 h1 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem cycMod_eq_one {s : G ℚ Ω} (h : cycBar ℚ Ω l s = 1) (m : ℕ) : cycMod ℚ Ω l m s = 1 := by
  have h1 : cycZ ℚ Ω l s = 1 := by
    have h2 := congrArg (fun u : (Qbar l)ˣ => (u : Qbar l)) h
    simp only [cycBar, MonoidHom.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      RingHom.comp_apply, Units.val_one] at h2
    have h3 : PadicInt.Coe.ringHom ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = (1 : ℚ_[l]) :=
      (algebraMap ℚ_[l] (Qbar l)).injective (by rw [h2, map_one])
    exact Units.ext (Subtype.ext h3)
  simp only [cycMod, MonoidHom.comp_apply, h1, map_one]

private theorem roots_pow {ζ : ℕ → Ω} (h : Roots l ζ) (c m : ℕ) (hc : c ≤ m) : ζ m ^ l ^ c = ζ (m - c) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hc
  rw [Nat.add_sub_cancel]
  clear hc
  induction c with
  | zero => simp
  | succ c ih => rw [pow_succ', pow_mul, ← add_assoc, (h (k + c)).2, ih]

private theorem conj_law {c : Coef l} {A : ValuationSubring Ω} {ν : G ℚ Ω → (Qbar l)ˣ} {Z : Sy Ω l}
    (hIw : IwSys2 c A ν Z) (hν : ∀ s ∈ Ine (F := ℚ) A, ν s = 1) {σ : G ℚ Ω} (hσ : σ ∈ Dec (F := ℚ) A)
    (hcy : cycBar ℚ Ω l σ = 1) (m : ℕ) {s : G ℚ Ω} (hs : s ∈ Hm l A m) :
    Z m (σ * s * σ⁻¹) 1 = (ν σ : Qbar l) * Z m s 1 := by
  obtain ⟨hsI, hsc⟩ := Subgroup.mem_inf.1 hs
  rw [MonoidHom.mem_ker] at hsc
  have hsD := Ine_le_Dec A hsI
  have hc := cycMod_eq_one hcy m
  have coc := (hIw.2.1 m).2
  have h0 : Z m 1 1 = 0 := by
    have := coc 1 (one_mem _) 1 (one_mem _) 1
    rw [hν 1 (one_mem _)] at this
    simpa using this
  have h1 := coc σ hσ σ⁻¹ (inv_mem hσ) 1
  have h2 := coc σ hσ s hsD 1
  have h3 := coc (σ * s) (mul_mem hσ hsD) σ⁻¹ (inv_mem hσ) 1
  rw [hIw.1 σ hσ s hsD, hν s hsI, map_mul, hc, hsc] at h3
  rw [mul_inv_cancel, h0, hc] at h1
  rw [hc] at h2
  simp only [inv_one, mul_one] at h1 h2 h3
  rw [h3, h2]
  linear_combination -h1

private theorem main
    (h48 : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Gs L : PowerSeries (Qbar l)) (a a' κ : Qbar l) (v v' : ℕ → Qbar l) (c₀ m₀ c₁ n₀ : ℕ) (φ : DirichletCharacter (Qbar l) l) (e : ℕ), l ≠ 2 → 1 ≤ e → 2 ≤ m₀ → (∀ n, Gs.coeff n ∈ c.O) → (∀ n, L.coeff n ∈ c.O) → ‖a‖ = 1 → ‖a'‖ = 1 → κ ≠ 0 → (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) → (∀ m, ‖v' m‖ = 1 ∧ Cg m (v' (m + 1)) (v' m)) → 2 ≤ c₀ → ¬ l ∣ c₀ → (∀ m, m₀ ≤ m → ∃ z : Qbar l, IsPrimitiveRoot z (l ^ m) ∧ ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive → Cg (m - c₁) ((1 - (c₀ : Qbar l) * ψ⁻¹ (c₀ : ZMod (l ^ m))) * (v' m * κ * a' ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval L (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) (v m * a ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval Gs (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) → (∃ r₁ : ℕ, ∀ r, r₁ ≤ r → 1 ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) → ¬ Cg (n₀ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass L r ξ x) 0) → ∃ n₁ r₁ : ℕ, ∀ r, r₁ ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) → ¬ Cg (n₁ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass Gs r ξ x) 0)
    (h50 : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g → ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 → mat W s 1 1 = 1) :
    GlobalTheory.KZ.ZetaEulerSystemNonvanishing GlobalTheory.KZ.Pin7 := by
  intro l _ Ω _ _ _ ι e S A W g hN hS c y S' ν χ Z hSys hIw hSp hPin
  obtain ⟨a, a', κ, v', j, Rhs, L, φ, m₀, c₀, n₀, hInu, ⟨σ₀, hσ₀, hF₀, hν₀⟩, ha, ha', hv', hκ, hj, hL, ⟨ζ, hζ, hHT⟩,
    hRhs, hχ, hNZ⟩ := hPin
  have hl2 : l ≠ 2 := hN.l_odd
  have he : 1 ≤ e := hN.e_pos
  have hA : OverL l A := hN.atL
  have hl2' : ¬ l ∣ 2 := fun h => hl2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h)
  have hR : Roots l ζ := hζ
  by_contra hnz
  have hy : ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 → y s 1 = 0 := by
    intro s hs hc
    by_contra h0
    exact hnz ⟨s, hs, hc, h50 l Ω ι e S A W g hN hS s hs hc, h0⟩
  have hSZ : SpZero A φ e Z := by
    intro n
    obtain ⟨r₀, hr₀⟩ := hSp n
    refine ⟨max r₀ 1, fun r hr s hs hc => ?_⟩
    have h1 := hr₀ r (le_trans (le_max_left _ _) hr) s hs hc
    have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
    have heq : (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) = eta φ e r := by
      funext x
      rw [hχ r hr1 x, mul_comm]
    rw [heq, hy s hs hc] at h1
    exact cg_symm h1
  have hI : IwI c A Z := by
    refine ⟨fun r s _ x => (hIw.2.1 r).1 s x, fun r s hs t ht x => ?_, fun r s _ x => hIw.2.2 r s x⟩
    rw [(hIw.2.1 r).2 s (Ine_le_Dec A hs) t (Ine_le_Dec A ht) x, hInu s hs, Units.val_one, one_mul]
  have hFr : ∀ σ ∈ Dec (F := ℚ) A, IsFrob A l σ → cycBar ℚ Ω l σ = 1 → ∀ m, ∀ s ∈ Hm l A m,
      Z m (σ * s * σ⁻¹) 1 = a * Z m s 1 := by
    intro σ hσ hF hc m s hs
    have h1 := (pFrobEx l hl2 Ω A hA).2.1 σ₀ hσ₀ σ hσ hF₀ hF
    have h2 := hIw.1 σ₀ hσ₀ _ (Ine_le_Dec A h1)
    rw [mul_inv_cancel_left, hInu _ h1, mul_one] at h2
    rw [conj_law hIw hInu hσ hc m hs, h2, hν₀]
  obtain ⟨Gs, v, c₁, m₁, hGs, hv, hrel, hint⟩ := pCore l hl2 Ω A hA c Z a j 2 c₀ (max m₀ c₀) ζ hI ha hFr hj hl2' hR (by
    intro m hm
    obtain ⟨κι, hfin, P, o, hP, -⟩ := hHT m (le_trans (le_max_left _ _) hm)
    refine ⟨κι, hfin, P, o, hP.2.1, hP.2.2.1, ?_⟩
    rw [← roots_pow hR c₀ m (le_trans (le_max_right _ _) hm)]
    exact hP.2.2.2.2)
  have hprim : ∀ m, IsPrimitiveRoot (j (ζ m)) (l ^ m) := fun m => (hζ m).1.map_of_injective j.injective
  obtain ⟨n₁, r₂, hG⟩ := h48 l c Gs L a a' κ v v' 2 (max (max m₀ c₀) (max m₁ 2)) (max c₀ c₁) n₀ φ e hl2 he
    (by omega) hGs hL ha ha' hκ hv hv' le_rfl hl2' (by
      intro m hm
      have hm0 : m₀ ≤ m := by omega
      obtain ⟨κι, hfin, P, o, hP, hlaw⟩ := hHT m hm0
      refine ⟨j (ζ m), hprim m, fun ψ hψ => ?_⟩
      have ht := norm_factor_le_one ψ⁻¹ 2
      have e1 := cg_mul ht (cg_symm (hRhs m hm0 ψ hψ _ (hprim m)))
      have e2 := cg_mul ht (cg_symm (hlaw ψ hψ))
      have e3 := hrel m (by omega) κι hfin P o hP.2.1 hP.2.2.1 (by
        rw [← roots_pow hR c₀ m (by omega)]
        exact hP.2.2.2.2) ψ
      exact cg_trans (cg_mono (by omega) (cg_trans e1 e2)) (cg_mono (by omega) e3)) hNZ
  obtain ⟨r₃, hr₃⟩ := hint φ e he hSZ n₁
  exact hG (max r₂ r₃) (le_max_left _ _) _ (hprim _) (hr₃ _ (le_max_right _ _) _ (hprim _))

end UpperTheory.Kd.C7.LocalUnitsRoots

theorem UpperTheory.Kd.C7.pLocu :
    GlobalTheory.KZ.ZetaEulerSystemNonvanishing GlobalTheory.KZ.Pin7 :=
  UpperTheory.Kd.C7.LocalUnitsRoots.main GlobalTheory.T.nonvanishing_transfer_characterSums_powerSeries GlobalTheory.T.quotient_char_trivial_inertia_cyclotomic_tower
