module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGaloisExtendingAlgHom
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ContentStep

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGLLatBasisOfIsSplitEquiv
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.LTA

open PowerSeries

variable {O : Type*} [CommRing O]

theorem alg_C (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (a : O) : h (C a) = C a := by
  have e : (C a : O⟦X⟧) = algebraMap O O⟦X⟧ a := by
    first
    | rfl
    | simp
    | (rw [PowerSeries.algebraMap_apply']; rfl)
  rw [e, AlgHom.commutes]

private theorem exists_pow_sub_pow_eq_mul_sub_of_constantCoeff_eq_one (l : ℕ) (x y : O⟦X⟧)
    (hx : constantCoeff x = 1) (hy : constantCoeff y = 1) :
    ∃ S : O⟦X⟧, constantCoeff S = l ∧ x ^ l - y ^ l = S * (x - y) := by
  refine ⟨∑ i ∈ Finset.range l, x ^ i * y ^ (l - 1 - i), ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [map_sum, hx, hy]
  · first
    | exact (geom_sum₂_mul x y l).symm
    | exact ((Commute.all x y).geom_sum₂_mul l).symm

theorem exists_GL_latBasis_of_isSplitEquiv (l : ℕ) :
    ∃ Q0 : O⟦X⟧, constantCoeff Q0 = l ∧ (1 + X : O⟦X⟧) ^ l - 1 = X * Q0 := by
  obtain ⟨S, hS, e⟩ := exists_pow_sub_pow_eq_mul_sub_of_constantCoeff_eq_one l (1 + X : O⟦X⟧) 1 (by simp) (by simp)
  exact ⟨S, hS, by linear_combination e⟩

variable [IsDomain O] [CharZero O]

end Formalism.MainNotions.N.FrobeniusPowerSeries.LTA
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaOnLevels
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ThetaAtRoot
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ThetaAtRootAlt
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.LTB

open PowerSeries

section Roots

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]

theorem root_eq (l : ℕ) [hp : Fact l.Prime] {x₀ y w : O} (hx : x₀ ≠ 0)
    (hrx : (1 + x₀) ^ l = 1) (hry : (1 + y) ^ l = 1)
    (hw : w ∈ IsLocalRing.maximalIdeal O) (hyw : y - x₀ = x₀ * w) : y = x₀ := by
  have hl0 : 0 < l := hp.out.pos
  have hζ1 : (1 + x₀) ≠ 1 := fun h => hx (by linear_combination h)
  have hprim : IsPrimitiveRoot (1 + x₀) l := by
    have h := IsPrimitiveRoot.orderOf (1 + x₀)
    rwa [orderOf_eq_prime hrx hζ1] at h
  have hζu : IsUnit (1 + x₀) := by
    first
    | exact hprim.isUnit hl0
    | exact hprim.isUnit hl0.ne'
  have hwu : ¬ IsUnit w := (IsLocalRing.mem_maximalIdeal w).1 hw
  obtain ⟨i, hil, hi⟩ : ∃ i < l, (1 + x₀) ^ i = 1 + y := by
    first
    | exact hprim.eq_pow_of_pow_eq_one hry
    | exact hprim.eq_pow_of_pow_eq_one hry hl0
  rcases i with _ | j
  · exfalso
    have hy0 : y = 0 := by linear_combination -hi
    have hxw : x₀ * (1 + w) = 0 := by linear_combination -hyw + hy0
    rcases mul_eq_zero.1 hxw with h | h
    · exact hx h
    · apply hwu
      have hw1 : w = -1 := by linear_combination h
      rw [hw1]
      exact isUnit_one.neg
  · rcases j with _ | j
    · linear_combination -hi
    · exfalso
      have hk0 : 0 < j + 1 := Nat.succ_pos j
      have hkl : j + 1 < l := by omega
      have hcop : (j + 1).Coprime l :=
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 (Nat.not_dvd_of_pos_of_lt hk0 hkl))
      have hprim' := hprim.pow_of_coprime (j + 1) hcop
      obtain ⟨m, -, hm⟩ : ∃ m < l, ((1 + x₀) ^ (j + 1)) ^ m = 1 + x₀ := by
        first
        | exact hprim'.eq_pow_of_pow_eq_one hrx
        | exact hprim'.eq_pow_of_pow_eq_one hrx hl0
      have e1 := geom_sum_mul ((1 + x₀) ^ (j + 1)) m
      have e2 := geom_sum_mul (1 + x₀) (j + 1)
      rw [hm] at e1
      set S := ∑ i ∈ Finset.range m, ((1 + x₀) ^ (j + 1)) ^ i with hS
      set v := ∑ i ∈ Finset.range (j + 1), (1 + x₀) ^ i with hv
      have hSv0 : x₀ * (S * v - 1) = 0 := by linear_combination S * e2 + e1
      have hSv : S * v = 1 := by
        have := (mul_eq_zero.1 hSv0).resolve_left hx
        linear_combination this
      have hvu : IsUnit v := ⟨⟨v, S, by rw [mul_comm]; exact hSv, hSv⟩, rfl⟩
      have hwz : x₀ * (w - (1 + x₀) * v) = 0 := by
        linear_combination -hyw - hi - (1 + x₀) * e2
      have hw' : w = (1 + x₀) * v := by
        have := (mul_eq_zero.1 hwz).resolve_left hx
        linear_combination this
      exact hwu (hw' ▸ hζu.mul hvu)

end Roots

section Main

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem mem_max (l : ℕ) [hp : Fact l.Prime] (hl : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    {x₀ : O} (hroot : (1 + x₀) ^ l = 1) : x₀ ∈ IsLocalRing.maximalIdeal O := by
  have hk : ((l : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O)]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hl
  haveI : CharP (IsLocalRing.ResidueField O) l := by
    first
    | exact (CharP.charP_iff_prime_eq_zero hp.out).2 hk
    | exact ringChar.of_eq ((hp.out.eq_one_or_self_of_dvd _ (ringChar.dvd hk)).resolve_left
        CharP.ringChar_ne_one)
  have h := congrArg (IsLocalRing.residue O) hroot
  simp only [map_pow, map_add (f := _), map_one] at h
  rw [add_pow_char, one_pow] at h
  have h2 : (IsLocalRing.residue O x₀) ^ l = 0 := by linear_combination h
  exact (IsLocalRing.residue_eq_zero_iff _).1 (pow_eq_zero_iff hp.out.ne_zero |>.1 h2)

theorem map_res {x₀ : O} (hx : x₀ ∈ IsLocalRing.maximalIdeal O) :
    PowerSeries.map (IsLocalRing.residue O) (X - C x₀) = X := by
  have h : IsLocalRing.residue O x₀ = 0 := (IsLocalRing.residue_eq_zero_iff x₀).2 hx
  rw [map_sub, PowerSeries.map_X, PowerSeries.map_C, h, map_zero, sub_zero]

theorem map_mk {x₀ : O} (hx : x₀ ∈ IsLocalRing.maximalIdeal O) :
    PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) (X - C x₀) = X := by
  have h : Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) x₀ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 hx
  rw [map_sub, PowerSeries.map_X, PowerSeries.map_C, h, map_zero, sub_zero]

theorem decomp {x₀ : O} (hx : x₀ ∈ IsLocalRing.maximalIdeal O) (p : O⟦X⟧) :
    ∃ c : O, ∃ q : O⟦X⟧, p = (X - C x₀) * q + C c := by
  have hord : PowerSeries.map (IsLocalRing.residue O) (X - C x₀) ≠ 0 := by
    rw [map_res hx]; exact PowerSeries.X_ne_zero
  obtain ⟨q, r, hqr⟩ := PowerSeries.exists_isWeierstrassDivision (f := p) (g := X - C x₀) hord
  have hdeg := hqr.1
  first
  | rw [map_mk hx, PowerSeries.order_X] at hdeg
  | rw [map_res hx, PowerSeries.order_X] at hdeg
  simp at hdeg
  have hrc : (r : O⟦X⟧) = C (r.coeff 0) := by
    first
    | (have hr0 : r.degree ≤ 0 := by
          first
          | exact Nat.WithBot.lt_one_iff_le_zero.1 hdeg
          | exact Order.le_of_lt_succ hdeg
       conv_lhs => rw [Polynomial.eq_C_of_degree_le_zero hr0]
       exact Polynomial.coe_C _)
    | (ext n
       rcases n with _ | n
       · simp
       · rw [Polynomial.coeff_coe, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n)]
         exact Polynomial.coeff_eq_zero_of_degree_lt
           (lt_of_lt_of_le hdeg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))))
  refine ⟨r.coeff 0, q, ?_⟩
  rw [← hrc]
  exact hqr.2

theorem uniq {x₀ : O} (hx : x₀ ∈ IsLocalRing.maximalIdeal O) {c : O}
    (hc : C c ∈ Ideal.span {X - C x₀}) : c = 0 := by
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton'.1 hc
  have hrec : ∀ n, coeff n f = x₀ * coeff (n + 1) f := by
    intro n
    have h := congrArg (fun g => coeff (n + 1) g) hf
    simp only [mul_sub, map_sub, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_C, Nat.succ_ne_zero, if_false] at h
    linear_combination h
  have hpow : ∀ n, coeff 0 f = x₀ ^ n * coeff n f := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [ih, hrec n]; ring
  have hall : ∀ n : ℕ, coeff 0 f ≡ 0 [SMOD ((IsLocalRing.maximalIdeal O) ^ n • ⊤ : Submodule O O)] := by
    intro n
    rw [SModEq.zero]
    have hmem := Submodule.smul_mem_smul
      (Ideal.mul_mem_right (coeff n f) _ (Ideal.pow_mem_pow hx n)) (Submodule.mem_top : (1 : O) ∈ ⊤)
    rw [hpow n]
    simpa using hmem
  have hcoef0 : coeff 0 f = 0 := by
    first
    | exact IsHausdorff.haus inferInstance _ hall
    | exact IsHausdorff.haus' _ hall
  have h0 := congrArg (fun g => coeff 0 g) hf
  simp only [mul_sub, map_sub, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mul_C, hcoef0,
    PowerSeries.coeff_zero_C] at h0
  linear_combination -h0

def Fs (l : ℕ) (x₀ : O) (a : O⟦X⟧) : O⟦X⟧ :=
  ∑ i ∈ Finset.range l, (1 + a) ^ i * (1 + C x₀) ^ (l - 1 - i)

theorem Fs_mul (l : ℕ) {x₀ : O} (hroot : (1 + x₀) ^ l = 1) (a : O⟦X⟧) :
    (1 + a) ^ l - 1 = Fs l x₀ a * (a - C x₀) := by
  have hy : (1 + C x₀ : O⟦X⟧) ^ l = 1 := by
    simpa [map_pow, map_add (f := _), map_one] using congrArg (C : O →+* O⟦X⟧) hroot
  have h := geom_sum₂_mul (1 + a) (1 + C x₀) l
  rw [hy] at h
  unfold Fs
  rw [← h]
  congr 1
  ring

end Main

end Formalism.MainNotions.N.FrobeniusPowerSeries.LTB
end
end

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

private theorem exists_eq_C_constantCoeff_add_X_mul {A : Type*} [CommRing A] (f : A⟦X⟧) :
    ∃ f' : A⟦X⟧, f = C (constantCoeff f) + X * f' := by
  obtain ⟨f', hf'⟩ :=
    (PowerSeries.X_dvd_iff).mpr (show constantCoeff (f - C (constantCoeff f)) = 0 by simp)
  exact ⟨f', by linear_combination hf'⟩

private theorem ringHom_eq_of_eq_on_C_X_of_pow_dvd_eq_zero {A B : Type*} [CommRing A] [CommRing B]
    (ψ₁ ψ₂ : A⟦X⟧ →+* B) (hC : ∀ a, ψ₁ (C a) = ψ₂ (C a)) (hX : ψ₁ X = ψ₂ X)
    (hsep : ∀ d : B, (∀ n : ℕ, ψ₁ X ^ n ∣ d) → d = 0) (f : A⟦X⟧) : ψ₁ f = ψ₂ f := by
  have key : ∀ n : ℕ, ∀ g : A⟦X⟧, ψ₁ X ^ n ∣ ψ₁ g - ψ₂ g := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      obtain ⟨g', hg'⟩ := exists_eq_C_constantCoeff_add_X_mul g
      obtain ⟨r, hr⟩ := ih g'
      have e1 : ψ₁ g = ψ₁ (C (constantCoeff g)) + ψ₁ X * ψ₁ g' := by
        calc ψ₁ g = ψ₁ (C (constantCoeff g) + X * g') := by rw [← hg']
          _ = _ := by rw [map_add (f := _), map_mul]
      have e2 : ψ₂ g = ψ₂ (C (constantCoeff g)) + ψ₂ X * ψ₂ g' := by
        calc ψ₂ g = ψ₂ (C (constantCoeff g) + X * g') := by rw [← hg']
          _ = _ := by rw [map_add (f := _), map_mul]
      exact ⟨r, by linear_combination e1 - e2 + hC (constantCoeff g) + ψ₂ g' * hX + ψ₁ X * hr⟩
  exact sub_eq_zero.mp (hsep _ (fun n => key n f))

theorem theta_at_root (l : ℕ) [Fact l.Prime] (hl : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (φ₀ γ : O⟦X⟧ →ₐ[O] O⟦X⟧) (hφ₀ : φ₀ X = (1 + X) ^ l - 1) (hc : ∀ f, φ₀ (γ f) = γ (φ₀ f))
    (χ : O) (h0 : constantCoeff (γ X) = 0) (h1 : coeff 1 (γ X) = χ)
    (hχ : χ - 1 ∈ Ideal.span {((l : ℕ) : O)})
    (x₀ : O) (hx₀ : x₀ ≠ 0) (hroot : (1 + x₀) ^ l = 1)
    (Q : O⟦X⟧) (hQ : X * Q = (1 + X) ^ l - 1) (u : O⟦X⟧) (hu : IsUnit u) (θ : O⟦X⟧)
    (hθ : γ (u * Q) = u * Q * θ) :
    θ - C χ ∈ Ideal.span {X - C x₀} := by
  have hxm : x₀ ∈ IsLocalRing.maximalIdeal O :=
    Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.mem_max l hl hroot
  obtain ⟨I, hI⟩ : ∃ I : Ideal O⟦X⟧, I = Ideal.span {X - C x₀} := ⟨_, rfl⟩
  rw [← hI]
  have hXI : X - C x₀ ∈ I := by rw [hI]; exact Ideal.mem_span_singleton_self _
  have hπX : Ideal.Quotient.mk I X = Ideal.Quotient.mk I (C x₀) := Ideal.Quotient.eq.mpr hXI
  have hinj : ∀ a b : O, Ideal.Quotient.mk I (C a) = Ideal.Quotient.mk I (C b) → a = b := by
    intro a b hab
    have h' : C (a - b) ∈ Ideal.span {X - C x₀} := by
      rw [map_sub, ← hI]; exact Ideal.Quotient.eq.mp hab
    exact sub_eq_zero.mp (Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.uniq hxm h')
  have hsurj : ∀ p : O⟦X⟧, ∃ c : O, Ideal.Quotient.mk I p = Ideal.Quotient.mk I (C c) := by
    intro p
    obtain ⟨c, q, hpq⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.decomp hxm p
    refine ⟨c, Ideal.Quotient.eq.mpr ?_⟩
    rw [hpq, add_sub_cancel_right]
    exact I.mul_mem_right q hXI
  have hsep : ∀ d : O⟦X⟧ ⧸ I, (∀ n : ℕ, Ideal.Quotient.mk I X ^ n ∣ d) → d = 0 := by
    intro d hd
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective d
    obtain ⟨c, hc'⟩ := hsurj p
    rw [hc'] at hd ⊢
    have hmem : ∀ n : ℕ, c ∈ Ideal.span {x₀} ^ n := by
      intro n
      obtain ⟨r, hr⟩ := hd n
      obtain ⟨p', rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨e, he⟩ := hsurj p'
      have h2 : Ideal.Quotient.mk I (C c) = Ideal.Quotient.mk I (C (x₀ ^ n * e)) := by
        rw [hr, hπX, he]; simp only [map_mul, map_pow]
      rw [hinj _ _ h2, Ideal.span_singleton_pow]
      exact (Ideal.span {x₀ ^ n}).mul_mem_right e (Ideal.mem_span_singleton_self _)
    have hne : Ideal.span {x₀} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x₀).mp hxm)
    have hc0 : c ∈ ⨅ n : ℕ, Ideal.span {x₀} ^ n := Ideal.mem_iInf.mpr hmem
    rw [Ideal.iInf_pow_eq_bot_of_isDomain (Ideal.span {x₀}) hne, Ideal.mem_bot] at hc0
    rw [hc0, map_zero, map_zero]
  have hπφX : Ideal.Quotient.mk I (φ₀ X) = 0 := by
    have h3 : Ideal.Quotient.mk I (φ₀ X) = Ideal.Quotient.mk I (C ((1 + x₀) ^ l - 1)) := by
      rw [hφ₀]; simp only [map_sub, map_pow, map_add (f := _), map_one, hπX]
    rw [h3, hroot, sub_self, map_zero, map_zero]
  have hφπ : ∀ f, Ideal.Quotient.mk I (φ₀ f) = Ideal.Quotient.mk I (C (constantCoeff f)) := by
    intro f
    obtain ⟨f', hf'⟩ := exists_eq_C_constantCoeff_add_X_mul f
    calc Ideal.Quotient.mk I (φ₀ f)
        = Ideal.Quotient.mk I (φ₀ (C (constantCoeff f) + X * f')) := by rw [← hf']
      _ = _ := by
        simp only [map_add (f := _), map_mul, Formalism.MainNotions.N.FrobeniusPowerSeries.LTA.alg_C, hπφX, zero_mul, add_zero]
  obtain ⟨g1, hg1⟩ := (PowerSeries.X_dvd_iff).mpr h0
  have hg1χ : constantCoeff g1 = χ := by
    rw [← h1, hg1]
    show constantCoeff g1 = coeff (0 + 1) (X * g1)
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  obtain ⟨t, ht⟩ := exists_eq_C_constantCoeff_add_X_mul g1
  obtain ⟨e, he⟩ := hsurj t
  have hπg1 : Ideal.Quotient.mk I g1 = Ideal.Quotient.mk I (C (χ + x₀ * e)) := by
    rw [ht, hg1χ]; simp only [map_add (f := _), map_mul, hπX, he]
  have hπg : Ideal.Quotient.mk I (γ X) = Ideal.Quotient.mk I (C (x₀ * (χ + x₀ * e))) := by
    rw [hg1, map_mul, hπg1, hπX]; simp only [map_mul]
  have hry : (1 + x₀ * (χ + x₀ * e)) ^ l = 1 := by
    have h4 : Ideal.Quotient.mk I (γ (φ₀ X)) = 0 := by
      rw [← hc X, hφπ, h0, map_zero, map_zero]
    have h5 : Ideal.Quotient.mk I (γ (φ₀ X))
        = Ideal.Quotient.mk I (C ((1 + x₀ * (χ + x₀ * e)) ^ l - 1)) := by
      rw [hφ₀]; simp only [map_sub, map_pow, map_add (f := _), map_one, hπg]
    have h6 := hinj ((1 + x₀ * (χ + x₀ * e)) ^ l - 1) 0 (by rw [← h5, h4, map_zero, map_zero])
    exact sub_eq_zero.mp h6
  have hχm : χ - 1 ∈ IsLocalRing.maximalIdeal O :=
    (Ideal.span_singleton_le_iff_mem _).mpr hl hχ
  have hw : χ - 1 + x₀ * e ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.maximalIdeal O).add_mem hχm ((IsLocalRing.maximalIdeal O).mul_mem_right e hxm)
  have hyx : x₀ * (χ + x₀ * e) = x₀ :=
    Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.root_eq l hx₀ hroot hry hw (by ring)
  have hχe : χ + x₀ * e = 1 := mul_left_cancel₀ hx₀ (by rw [hyx, mul_one])
  have hπg1' : Ideal.Quotient.mk I g1 = 1 := by rw [hπg1, hχe, map_one, map_one]
  have hπgX : Ideal.Quotient.mk I (γ X) = Ideal.Quotient.mk I X := by
    rw [hπg, hyx, hπX]
  have hγπ : ∀ f, Ideal.Quotient.mk I (γ f) = Ideal.Quotient.mk I f := by
    intro f
    exact (ringHom_eq_of_eq_on_C_X_of_pow_dvd_eq_zero (Ideal.Quotient.mk I) ((Ideal.Quotient.mk I).comp γ.toRingHom)
      (fun a => by
        show _ = Ideal.Quotient.mk I (γ (C a))
        rw [Formalism.MainNotions.N.FrobeniusPowerSeries.LTA.alg_C])
      hπgX.symm hsep f).symm
  obtain ⟨Q0, hQ0c, hQ0⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.LTA.exists_GL_latBasis_of_isSplitEquiv (O := O) l
  have hQQ0 : Q = Q0 := mul_left_cancel₀ PowerSeries.X_ne_zero (hQ.trans hQ0)
  have hQne : Q ≠ 0 := by
    intro hQz
    have hl0 : ((l : ℕ) : O) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    apply hl0
    rw [← hQ0c, ← hQQ0, hQz, map_zero]
  have hγQ : γ (X * Q) = X * g1 * γ Q := by rw [map_mul, hg1]
  have hγQ' : γ (X * Q) = X * Q * φ₀ g1 := by
    rw [hQ, ← hφ₀, ← hc X, hg1, map_mul]
  have hg1Q : g1 * γ Q = Q * φ₀ g1 :=
    mul_left_cancel₀ PowerSeries.X_ne_zero (by linear_combination hγQ' - hγQ)
  have hkey : Q * (g1 * u * θ) = Q * (γ u * φ₀ g1) := by
    have e3 : γ (u * Q) = γ u * γ Q := map_mul _ _ _
    linear_combination (-g1) * hθ + g1 * e3 + γ u * hg1Q
  have hkey' : g1 * u * θ = γ u * φ₀ g1 := mul_left_cancel₀ hQne hkey
  have hk : Ideal.Quotient.mk I (g1 * u * θ) = Ideal.Quotient.mk I (γ u * φ₀ g1) := by
    rw [hkey']
  simp only [map_mul] at hk
  rw [hγπ, hφπ, hg1χ, hπg1', one_mul] at hk
  exact Ideal.Quotient.eq.mp ((hu.map (Ideal.Quotient.mk I)).mul_left_cancel hk)

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module

namespace GammaOnLevels

open PowerSeries

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem cancel_C {x a : O} (hx : x ∈ IsLocalRing.maximalIdeal O) (ha : a ≠ 0) {g : O⟦X⟧}
    (h : C a * g ∈ Ideal.span {X - C x}) : g ∈ Ideal.span {X - C x} := by
  obtain ⟨c, t, rfl⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.decomp hx g
  have h2 : C (a * c) ∈ Ideal.span {X - C x} := by
    have e : C (a * c) = C a * ((X - C x) * t + C c) - (X - C x) * (C a * t) := by
      rw [map_mul]; ring
    rw [e]
    exact Ideal.sub_mem _ h (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have h3 := Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.uniq hx h2
  have hc : c = 0 := (mul_eq_zero.1 h3).resolve_left ha
  rw [hc, map_zero, add_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

theorem eval_eq_zero {x : O} (hx : x ∈ IsLocalRing.maximalIdeal O) (r : Polynomial O)
    (h : (r : O⟦X⟧) ∈ Ideal.span {X - C x}) : r.eval x = 0 := by
  apply Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.uniq hx
  have e := Polynomial.modByMonic_add_div r (Polynomial.X - Polynomial.C x)
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at e
  generalize r /ₘ (Polynomial.X - Polynomial.C x) = d at e
  generalize r.eval x = c at e ⊢
  subst e
  rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C,
    Polynomial.coe_C] at h
  have e2 : (C c : O⟦X⟧) = (C c + (X - C x) * (d : O⟦X⟧)) - (X - C x) * (d : O⟦X⟧) := by ring
  rw [e2]
  exact Ideal.sub_mem _ h (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

end GammaOnLevels

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]


end Core

end Formalism.MainNotions.N.Ln17
end
end

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem charZero_of_prime_ne_zero [IsDomain O] [IsLocalRing O] (W : LocWach PD LL O v n)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hl0 : ((PD.p : ℕ) : O) ≠ 0) : CharZero O := by
  obtain ⟨m, hm⟩ := CharP.exists O
  rcases CharP.char_is_prime_or_zero O m with hmp | hm0
  · exfalso
    by_cases hml : m = PD.p
    · subst hml
      exact hl0 (CharP.cast_eq_zero O _)
    · have hcop : Nat.Coprime PD.p m := (Nat.coprime_primes PD.hp hmp).2 (fun h => hml h.symm)
      have hu : IsUnit ((PD.p : ℕ) : ZMod m) := (ZMod.isUnit_iff_coprime PD.p m).2 hcop
      have hu' := hu.map (ZMod.castHom (dvd_refl m) O)
      rw [map_natCast] at hu'
      exact (IsLocalRing.mem_maximalIdeal _).1 (ArcLengthOneTwo.l_mem_max W hO) hu'
  · subst hm0
    exact CharP.charP_to_charZero O

theorem gamma_sub_self_mem_pi0_lattice (W : LocWach PD LL O v n) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (i : ZMod n) (T : LocLat G Qp LL O) (hc : IsCrys PD T.ρ) :
    ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T i y ∧ W.γ T x - x = W.π₀ • y := by
  intro x hx
  obtain ⟨y, hy, he⟩ := Formalism.MainNotions.LiftingTheory.coreHgr_of W hP9 hcase T hc i 0 x hx
  refine ⟨y, hy, ?_⟩
  simpa using he

theorem exists_gamma_sub_one_div_pi0 (W : LocWach PD LL O v n) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (T : LocLat G Qp LL O) :
    ∃ dop : W.DD T →ₗ[O] W.DD T, ∀ y, W.π₀ • dop y = W.γ T y - y := by
  have hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀) :=
    (Formalism.MainNotions.LiftingTheory.lifta_ring_of W
      (Formalism.MainNotions.LiftingTheory.uniformizer_ring_and_module_clauses W hP9 hcase W.one (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1).πU
  obtain ⟨c, hc⟩ := hπ.exists_right_inv
  exact ⟨Formalism.MainNotions.LiftingTheory.lifta_δ W T c, Formalism.MainNotions.LiftingTheory.lifta_δ_spec W T c hc⟩

theorem units_sub_one_dvd_zpow_sub_one {R : Type} [CommRing R] (u : Rˣ) (k : ℤ) :
    (u : R) - 1 ∣ ((u ^ k : Rˣ) : R) - 1 := by
  have hN : ∀ j : ℕ, (u : R) - 1 ∣ ((u ^ j : Rˣ) : R) - 1 := fun j => by
    rw [Units.val_pow_eq_pow_val]
    simpa using sub_dvd_pow_sub_pow (u : R) 1 j
  rcases Int.eq_nat_or_neg k with ⟨j, rfl | rfl⟩
  · exact_mod_cast hN j
  · rw [zpow_neg, zpow_natCast]
    obtain ⟨w, hw⟩ := hN j
    refine ⟨-(((u ^ j)⁻¹ : Rˣ) : R) * w, ?_⟩
    have h1 : (((u ^ j)⁻¹ : Rˣ) : R) * ((u ^ j : Rˣ) : R) = 1 := Units.inv_mul _
    linear_combination (-(((u ^ j)⁻¹ : Rˣ) : R)) * hw + h1

theorem exists_cyclotomic_char_quotient (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x) (hinj : Function.Injective (algebraMap O LL)) :
    ∃ cc : ℤ → O, ∀ m : ℤ, (-((PD.p : ℕ) : O)) * cc m = (((W.χΓ W.gam) ^ (-m) : Oˣ) : O) - 1 := by
  have hl : ∃ c₀ : O, ((W.χΓ W.gam : Oˣ) : O) - 1 = ((PD.p : ℕ) : O) * c₀ := by
    set a : LL := algebraMap O LL (((W.χΓ W.gam : Oˣ) : O) - 1) with ha
    have hva : v a = 1 := by
      have := W.gam_gen
      rw [hcase.2.1] at this
      rw [ha, map_sub, map_one]
      simpa using this
    have hvp : v (PD.p : LL) = 1 := W.v_l
    have hp0 : (PD.p : LL) ≠ 0 := by
      intro h
      rw [h, AddValuation.map_zero] at hvp
      exact WithTop.top_ne_coe hvp
    have hx : 0 ≤ v (a * (PD.p : LL)⁻¹) := by
      have h := v.map_mul (a * (PD.p : LL)⁻¹) (PD.p : LL)
      rw [inv_mul_cancel_right₀ hp0, hva, hvp] at h
      cases hq : v (a * (PD.p : LL)⁻¹) using WithTop.recTopCoe with
      | top => exact le_top
      | coe q =>
        rw [hq] at h
        have h2 : (1 : ℚ) = q + 1 := by exact_mod_cast h
        exact_mod_cast (show (0 : ℚ) ≤ q by linarith)
    obtain ⟨c₀, hc₀⟩ := hOv _ hx
    refine ⟨c₀, hinj ?_⟩
    rw [map_mul, hc₀, map_natCast, ← ha, mul_left_comm, mul_inv_cancel₀ hp0, mul_one]
  obtain ⟨c₀, hc₀⟩ := hl
  choose w hw using fun m : ℤ => units_sub_one_dvd_zpow_sub_one (W.χΓ W.gam) (-m)
  refine ⟨fun m => -(c₀ * w m), fun m => ?_⟩
  rw [hw m, hc₀]
  ring

open PowerSeries in
theorem gamma_q_expansion_of_points [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x))
    (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x) (hinj : Function.Injective (algebraMap O LL))
    (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i → ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ) :
    ∃ g ∈ W.AΔ, W.γA W.gam (qA W) = ((W.χΓ W.gam : Oˣ) : O) • qA W + qA W ^ 2 * g := by
  have hpF : Fact PD.p.Prime := ⟨PD.hp⟩
  set χ : O := ((W.χΓ W.gam : Oˣ) : O) with hχdef

  have hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h2 : algebraMap O LL ((u⁻¹ : Oˣ) : O) * ((PD.p : ℕ) : LL) = 1 := by
      rw [← map_natCast (algebraMap O LL), ← hu, ← map_mul, Units.inv_mul, map_one]
    have h3 := congrArg v h2
    rw [AddValuation.map_mul, AddValuation.map_one, W.v_l] at h3
    have h1 := hO ((u⁻¹ : Oˣ) : O)
    generalize v (algebraMap O LL ((u⁻¹ : Oˣ) : O)) = t at h1 h3
    induction t using WithTop.recTopCoe with
    | top => simp at h3
    | coe q =>
      have e3 : q + 1 = 0 := by exact_mod_cast h3
      have e1 : (0 : ℚ) ≤ q := by exact_mod_cast h1
      linarith

  have hχ : χ - 1 ∈ Ideal.span {((PD.p : ℕ) : O)} := by
    have hg := W.gam_gen
    rw [hcase.2.1, Nat.cast_one] at hg
    have hL0 : ((PD.p : ℕ) : LL) ≠ 0 := by
      intro h0
      have h1 := W.v_l
      rw [h0, AddValuation.map_zero] at h1
      exact WithTop.top_ne_coe h1
    set a : LL := algebraMap O LL χ - 1 with ha
    have hx : v (a * ((PD.p : ℕ) : LL)⁻¹) = 0 := by
      have e : a * ((PD.p : ℕ) : LL)⁻¹ * ((PD.p : ℕ) : LL) = a := by field_simp
      have h1 := congrArg v e
      rw [AddValuation.map_mul, W.v_l, hg] at h1
      generalize v (a * ((PD.p : ℕ) : LL)⁻¹) = t at h1 ⊢
      induction t using WithTop.recTopCoe with
      | top => simp at h1
      | coe q =>
        have e3 : q + 1 = 1 := by exact_mod_cast h1
        have : q = 0 := by linarith
        rw [this]; rfl
    obtain ⟨y, hy⟩ := hOv _ (le_of_eq hx.symm)
    have hyy : ((PD.p : ℕ) : O) * y = χ - 1 := by
      apply hinj
      rw [map_mul, hy, map_natCast, map_sub, map_one, ← ha]
      field_simp
    exact Ideal.mem_span_singleton'.mpr ⟨y, by rw [mul_comm]; exact hyy⟩

  let e : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hcase.1
  let τ : K →ₐ[Qp] LL := (W.emb 0).comp e.symm.toAlgHom
  have hover : Formalism.MainNotions.LiftingTheory.Over W τ 0 := by
    apply AlgHom.ext
    intro x
    show W.emb 0 (e.symm (IsScalarTower.toAlgHom Qp K₀ K x)) = W.emb 0 x
    rw [show IsScalarTower.toAlgHom Qp K₀ K x = e x from rfl, AlgEquiv.symm_apply_apply]
  obtain ⟨ζ, hζp, hζ1, -⟩ := hPtEx 0 τ hover
  have hvζ : 0 ≤ v ζ := by
    have h1 : v (ζ ^ PD.p) = 0 := by rw [hζp, AddValuation.map_one]
    rw [AddValuation.map_pow] at h1
    have hne : v ζ ≠ ⊤ := by
      rw [Ne, AddValuation.top_iff]
      rintro rfl
      rw [zero_pow PD.hp.ne_zero] at hζp
      exact zero_ne_one hζp
    generalize v ζ = t at h1 hne ⊢
    induction t using WithTop.recTopCoe with
    | top => exact absurd rfl hne
    | coe q =>
      have h2 : ((PD.p • q : ℚ) : WithTop ℚ) = ((0 : ℚ) : WithTop ℚ) := by
        rw [WithTop.coe_nsmul]; exact h1
      have h3 : (PD.p : ℚ) * q = 0 := by
        rw [← nsmul_eq_mul]; exact_mod_cast h2
      have hp0 : (PD.p : ℚ) ≠ 0 := by exact_mod_cast PD.hp.ne_zero
      have hq : q = 0 := (mul_eq_zero.1 h3).resolve_left hp0
      rw [hq]; rfl
  obtain ⟨z, hz⟩ := hOv ζ hvζ
  have hzp : z ^ PD.p = 1 := hinj (by rw [map_pow, hz, hζp, map_one])
  have hz1 : z ≠ 1 := fun h => hζ1 (by rw [← hz, h, map_one])
  have hprim : IsPrimitiveRoot z PD.p := by
    have h := orderOf_eq_prime hzp hz1
    rw [← h]
    exact IsPrimitiveRoot.orderOf z

  let xr : Fin (PD.p - 1) → O := fun j => z ^ (j.1 + 1) - 1
  have hxr0 : ∀ j, xr j ≠ 0 := by
    intro j h
    apply hprim.pow_ne_one_of_pos_of_lt (Nat.succ_ne_zero j.1) (by have := j.2; omega)
    exact sub_eq_zero.1 h
  have hxrr : ∀ j, (1 + xr j) ^ PD.p = 1 := by
    intro j
    show (1 + (z ^ (j.1 + 1) - 1)) ^ PD.p = 1
    rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul, hzp, one_pow]
  have hxinj : Function.Injective xr := by
    intro j k h
    have h' : z ^ (j.1 + 1) = z ^ (k.1 + 1) := by
      have := h; simp only [xr] at this; exact sub_left_injective this
    have := hprim.pow_inj (by have := j.2; omega) (by have := k.2; omega) h'
    exact Fin.ext (by omega)

  have hfr : Module.finrank K₀ K = 1 := by
    have e' : K₀ ≃ₗ[K₀] K := LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hcase.1
    rw [← e'.finrank_eq, Module.finrank_self]
  have hring := ((hP9 W.one (Formalism.MainNotions.LiftingTheory.gen_one_crys W) hcase.2.1 hcase.2.2).2.2 hfr).1
  obtain ⟨-, -, -, -, ⟨w, hw⟩, -⟩ := hring
  have hE : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
      qA W := by
    funext i
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qA, lA]
  rw [hE] at hw
  have hwi : ∀ i, W.q₀ = (w : LetA O n) i * qA W i := fun i => congrFun hw i

  obtain ⟨κ, hκ, -, hγπ⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.gamma_pi0_eq_pi0_mul_one_add_unit_mul_q W hcase hP9
  set θ : LetA O n := 1 + W.π₀ * κ with hθdef
  have hγq : W.γA W.gam (qA W) = qA W * θ := by
    have e1 : W.γA W.gam (qA W) = W.γA W.gam W.π₀ + ((PD.p : ℕ) : LetA O n) := by
      simp only [qA, lA, map_add (f := _), map_natCast]
    rw [e1, hγπ, hθdef]
    simp only [qA, lA]
    ring

  have hchar : CharP (IsLocalRing.ResidueField O) PD.p :=
    (CharP.charP_iff_prime_eq_zero PD.hp).mpr (by
      rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]; exact hlm)
  have hmapQ : W.q₀.map (IsLocalRing.residue O) = X ^ (PD.p - 1) := by
    have h1 := congrArg (PowerSeries.map (IsLocalRing.residue O)) W.q₀_def
    have : CharP (PowerSeries (IsLocalRing.ResidueField O)) PD.p :=
      charP_of_injective_algebraMap
        (algebraMap (IsLocalRing.ResidueField O) (PowerSeries (IsLocalRing.ResidueField O))).injective PD.p
    simp only [map_mul, map_X, map_sub, map_pow, map_add (f := _), map_one] at h1
    rw [add_pow_char, one_pow, add_sub_cancel_left] at h1
    have h2 : (X : PowerSeries (IsLocalRing.ResidueField O)) ^ PD.p = X * X ^ (PD.p - 1) := by
      rw [← pow_succ']; congr 1; have := PD.hp.two_le; omega
    rw [h2] at h1
    exact mul_left_cancel₀ X_ne_zero h1
  have hQne : W.q₀.map (IsLocalRing.residue O) ≠ 0 := by
    rw [hmapQ]; exact pow_ne_zero _ X_ne_zero
  have hQ0 : W.q₀ ≠ 0 := by
    intro h; apply hQne; rw [h, map_zero]
  have hq0 : ∀ i, qA W i ≠ 0 := by
    intro i h; apply hQ0; rw [hwi i, h, mul_zero]

  have hlet : ∀ i : ZMod n, ∃ h : O⟦X⟧, θ i - C χ = qA W i * h := by
    intro i
    set f : O⟦X⟧ := θ i - C χ with hf
    let u : O⟦X⟧ := ((w⁻¹ : (LetA O n)ˣ) : LetA O n) i
    have hu : IsUnit u := (w⁻¹).isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) i)
    have huQ : u * W.q₀ = qA W i := by
      rw [hwi i, ← mul_assoc]
      show ((w⁻¹ : (LetA O n)ˣ) : LetA O n) i * (w : LetA O n) i * qA W i = qA W i
      rw [← Pi.mul_apply, Units.inv_mul, Pi.one_apply, one_mul]
    have hθi : W.γ₀ W.gam (u * W.q₀) = u * W.q₀ * θ i := by
      rw [huQ]
      have := congrFun hγq i
      exact this
    have hφ₀ : W.φ₀ X = (1 + X) ^ PD.p - 1 := by rw [W.φ₀_X, W.q₀_def]
    have hroot : ∀ j, f ∈ Ideal.span {X - C (xr j)} := fun j =>
      Formalism.MainNotions.N.FrobeniusPowerSeries.theta_at_root PD.p hlm W.φ₀ (W.γ₀ W.gam) hφ₀ (W.γ₀_comm W.gam) χ
        (W.γ₀_X W.gam).1 (W.γ₀_X W.gam).2 hχ (xr j) (hxr0 j) (hxrr j) W.q₀ W.q₀_def u hu (θ i) hθi
    have hQroot : ∀ j, W.q₀ ∈ Ideal.span {X - C (xr j)} := by
      intro j
      have hx : xr j ∈ IsLocalRing.maximalIdeal O := Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.mem_max PD.p hlm (hxrr j)
      apply Formalism.MainNotions.N.Ln17.GammaOnLevels.cancel_C hx (hxr0 j)
      have e1 := Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.Fs_mul PD.p (hxrr j) X
      have e2 : C (xr j) * W.q₀ = (X - C (xr j)) * (Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.Fs PD.p (xr j) X - W.q₀) := by
        rw [mul_sub, mul_comm (X - C (xr j)), ← e1, ← W.q₀_def]; ring
      rw [e2]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    have hdiv := eq_mul_weierstrassDiv_add_weierstrassMod f hQne
    set r := f %ʷ W.q₀ with hr
    have hdeg : r.degree < ((PD.p - 1 : ℕ) : WithBot ℕ) := by
      have := degree_weierstrassMod_lt f W.q₀
      rw [hmapQ, order_X_pow, ENat.toNat_natCast] at this
      exact this
    have hev : ∀ j, r.eval (xr j) = 0 := by
      intro j
      have hx : xr j ∈ IsLocalRing.maximalIdeal O := Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.mem_max PD.p hlm (hxrr j)
      apply Formalism.MainNotions.N.Ln17.GammaOnLevels.eval_eq_zero hx
      have e : (r : O⟦X⟧) = f - W.q₀ * (f /ʷ W.q₀) := by
        rw [eq_sub_iff_add_eq, add_comm]; exact hdiv.symm
      rw [e]
      exact Ideal.sub_mem _ (hroot j) (Ideal.mul_mem_right _ _ (hQroot j))
    have hr0 : r = 0 := by
      by_contra hne
      exact hne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero r hxinj hev
        (by rw [Fintype.card_fin]; exact (Polynomial.natDegree_lt_iff_degree_lt hne).2 hdeg))
    refine ⟨(w : LetA O n) i * (f /ʷ W.q₀), ?_⟩
    have e : f = W.q₀ * (f /ʷ W.q₀) := by
      rw [hr0, Polynomial.coe_zero, add_zero] at hdiv; exact hdiv
    show f = _
    generalize f /ʷ W.q₀ = d at e ⊢
    rw [e, hwi i]
    ring
  choose H hH using hlet
  have hθH : θ - algebraMap O (LetA O n) χ = qA W * H := by
    funext i
    rw [Pi.sub_apply, Pi.mul_apply, ← hH i]
    rfl

  have hθmem : θ ∈ W.AΔ :=
    W.AΔ.add_mem W.AΔ.one_mem (W.AΔ.mul_mem (Formalism.MainNotions.N.FrobeniusPowerSeries.GS.π₀_mem W) hκ)
  have hqmem : qA W ∈ W.AΔ := Formalism.MainNotions.N.FrobeniusPowerSeries.GS.qA_mem W
  have hHmem : H ∈ W.AΔ := by
    intro δ hδ
    have h1 : W.γA δ (qA W * H) = qA W * H := by
      rw [← hθH]
      exact (W.AΔ.sub_mem hθmem (W.AΔ.algebraMap_mem χ)) δ hδ
    rw [map_mul, hqmem δ hδ] at h1
    funext i
    exact mul_left_cancel₀ (hq0 i) (congrFun h1 i)
  refine ⟨H, hHmem, ?_⟩
  rw [hγq, Algebra.smul_def]
  linear_combination qA W * hθH

end Formalism.MainNotions.N.FrobeniusPowerSeries
