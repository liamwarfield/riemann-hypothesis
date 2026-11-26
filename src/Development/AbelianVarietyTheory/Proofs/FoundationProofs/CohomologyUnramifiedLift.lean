module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductUnramifiedClassesVanishes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedCocycleKillsRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalHeightFrobeniusPlace

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOfNatCastMem
@[reducible] noncomputable def UpperTheory.Reformulated.B.Yza3.Pl :
    Type :=
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)

noncomputable def UpperTheory.Reformulated.B.Yza3.normV.{u_1} :
    {F : Type u_1} → [inst : Field F] → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → ℕ :=
    fun {F : Type u_1} [Field F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
      Nat.card (NumberField.RingOfIntegers F ⧸ v.asIdeal)

namespace UpperTheory.Reformulated.B.Yza3

open NumberField in
private lemma exists_prime_gen (v : Pl) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  classical
  let e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hprime : v.asIdeal.IsPrime := v.isPrime
  obtain ⟨g, hg⟩ : ∃ g : 𝓞 ℚ, v.asIdeal = Ideal.span {g} :=
    haveI : IsPrincipalIdealRing (𝓞 ℚ) :=
      IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective
    (IsPrincipalIdealRing.principal v.asIdeal).principal
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact v.ne_bot (by simpa using hg)
  have hgp : Prime g := by
    rw [← Ideal.span_singleton_prime hg0, ← hg]
    exact hprime
  have hep : Prime (e g) := (MulEquiv.prime_iff e.toMulEquiv).2 hgp
  refine ⟨(e g).natAbs, Int.prime_iff_natAbs_prime.1 hep, ?_⟩
  rw [hg]
  have hassoc : Associated (e g) (((e g).natAbs : ℕ) : ℤ) := (Int.associated_natAbs _)
  have : Associated g (((e g).natAbs : ℕ) : 𝓞 ℚ) := by
    have h2 := hassoc.map e.symm.toMonoidHom
    generalize (e g).natAbs = n at h2 ⊢
    have h3 : e.symm.toMonoidHom (e g) = g := e.symm_apply_apply g
    have h4 : e.symm.toMonoidHom ((n : ℕ) : ℤ) = (n : 𝓞 ℚ) := map_natCast e.symm n
    rwa [h3, h4] at h2
  exact Ideal.span_singleton_eq_span_singleton.2 this

open NumberField in
private lemma eq_of_natCast_mem {p : ℕ} (hp : p.Prime) (v v' : Pl)
    (h : (p : 𝓞 ℚ) ∈ v.asIdeal) (h' : (p : 𝓞 ℚ) ∈ v'.asIdeal) : v = v' := by
  have key : ∀ u : Pl, (p : 𝓞 ℚ) ∈ u.asIdeal → u.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
    intro u hu
    obtain ⟨q, hq, huq⟩ := exists_prime_gen u
    rw [huq] at hu ⊢
    have hd : (q : 𝓞 ℚ) ∣ (p : 𝓞 ℚ) := Ideal.mem_span_singleton.1 hu
    have hd' : (q : ℤ) ∣ (p : ℤ) := by
      have := map_dvd (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) hd
      simpa using this
    have : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).1 (Int.natCast_dvd_natCast.1 hd')
    rw [this]
  exact IsDedekindDomain.HeightOneSpectrum.ext ((key v h).trans (key v' h').symm)

open NumberField in
theorem htc_places :
    ∀ (w : UpperTheory.Reformulated.B.Yza3.Pl),
      UpperTheory.Reformulated.B.Yza3.normV w ≠ (0 : ℕ) ∧
        (∀ (v : UpperTheory.Reformulated.B.Yza3.Pl), v ≠ w → (↑(UpperTheory.Reformulated.B.Yza3.normV w) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal) ∧
          ∀ (p : ℕ),
            Nat.Prime p →
              ∀ (v v' : UpperTheory.Reformulated.B.Yza3.Pl),
                (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal → (↑p : NumberField.RingOfIntegers ℚ) ∈ v'.asIdeal → v = v' := by
  intro w
  obtain ⟨p, hp, hw⟩ := exists_prime_gen w
  have hnorm : normV w = p := by
    have h1 : normV w = Ideal.absNorm w.asIdeal := by
      simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [h1, hw, Ideal.absNorm_span_singleton]
    have : ((p : 𝓞 ℚ)) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp
  refine ⟨by rw [hnorm]; exact hp.ne_zero, ?_, fun q hq v v' => eq_of_natCast_mem hq v v'⟩
  intro v hvw hmem
  rw [hnorm] at hmem
  refine hvw (eq_of_natCast_mem hp v w hmem ?_)
  rw [hw]
  exact Ideal.mem_span_singleton_self _

end UpperTheory.Reformulated.B.Yza3
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CongruenceMulOfUnitFactor
@[reducible] noncomputable def UpperTheory.Reformulated.B.Yza4.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.Yza4.Cg :
    {l : ℕ} → [inst : Fact (Nat.Prime l)] → ℕ → UpperTheory.Reformulated.B.Yza4.Qbar l → UpperTheory.Reformulated.B.Yza4.Qbar l → Prop :=
    fun {l : ℕ} [Fact (Nat.Prime l)] (n : ℕ) (a b : UpperTheory.Reformulated.B.Yza4.Qbar l) ↦
      ‖a - b‖ ≤ ‖(↑l : UpperTheory.Reformulated.B.Yza4.Qbar l) ^ n‖

theorem UpperTheory.Reformulated.B.Yza4.congruence_mul_of_unit_factor :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {n : ℕ} {P h un D : UpperTheory.Reformulated.B.Yza4.Qbar l},
      UpperTheory.Reformulated.B.Yza4.Cg n (P * h) (0 : UpperTheory.Reformulated.B.Yza4.Qbar l) →
        UpperTheory.Reformulated.B.Yza4.Cg n P (un * D) →
          ‖un‖ = (1 : ℝ) → ‖h‖ ≤ (1 : ℝ) → UpperTheory.Reformulated.B.Yza4.Cg n (D * h) (0 : UpperTheory.Reformulated.B.Yza4.Qbar l) := by
  intro l _ n P h un D h1 h2 hu hh
  unfold UpperTheory.Reformulated.B.Yza4.Cg at *
  rw [sub_zero] at h1 ⊢
  set c : ℝ := ‖(↑l : PadicAlgCl l) ^ n‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  have hmul : ∀ a b : PadicAlgCl l, ‖a * b‖ = ‖a‖ * ‖b‖ := fun a b => norm_mul a b
  have key : un * (D * h) = P * h + (un * D - P) * h := by ring
  have h3 : ‖(un * D - P) * h‖ ≤ c := by
    rw [hmul, norm_sub_rev]
    calc ‖P - un * D‖ * ‖h‖ ≤ c * 1 := mul_le_mul h2 hh (norm_nonneg _) hc0
      _ = c := mul_one c
  have h4 : ‖un * (D * h)‖ ≤ c := by
    rw [key]
    exact (PadicAlgCl.isNonarchimedean l _ _).trans (max_le h1 h3)
  rw [hmul, hu, one_mul] at h4
  exact h4
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixesRootOfUnity
namespace GlobalTheory.InertiaRootOfUnity

theorem eq_one_of_val_sub_lt {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ)
    (N : ℕ) (hN : ¬ w (N : K) < 1) (u : K) (hu : u ^ N = 1) (h : w (u - 1) < 1) : u = 1 := by
  by_contra hne
  have hx : u - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hw1 : w u = 1 := by
    have h' := Valuation.map_add_eq_of_lt_right w (x := u - 1) (y := 1) (by rw [map_one]; exact h)
    rwa [sub_add_cancel, map_one] at h'
  have hpow : ∀ i : ℕ, w (u ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hr : u ^ (i + 1) - 1 = u * (u ^ i - 1) + (u - 1) := by ring
      rw [hr]
      refine Valuation.map_add_lt w ?_ h
      rw [map_mul, hw1, one_mul]
      exact ih
  have hsum : ∑ i ∈ Finset.range N, u ^ i = 0 := by
    have hg := geom_sum_mul u N
    rw [hu, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right hx
  have hNeq : (N : K) = -∑ i ∈ Finset.range N, (u ^ i - 1) := by
    rw [Finset.sum_sub_distrib, hsum]
    simp
  apply hN
  rw [hNeq, Valuation.map_neg]
  exact w.map_sum_lt one_ne_zero fun i _ => hpow i

theorem inertia_fixes_root_of_unity {Ω : Type} [Field Ω] [Algebra ℚ Ω] (N : ℕ) (v : GlobalTheory.Ord2.Pl)
    (B : ValuationSubring Ω) (hB : Formalism.ConjugateSelfDual.IsPlaceOver B v)
    (hN : ¬ ((N : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal))
    (s : Formalism.ConjugateSelfDual.G ℚ Ω) (hs : s ∈ ReciprocityTheory.Gal.Ine B) (ζ : Ω) (hζ : ζ ^ N = 1) : s ζ = ζ := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (by simpa using v.asIdeal.zero_mem)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp [zero_pow hN0] at hζ
  have hwζ : B.valuation ζ = 1 := by
    have hp : B.valuation ζ ^ N = 1 := by rw [← map_pow, hζ, map_one]
    rcases lt_trichotomy (B.valuation ζ) 1 with hlt | heq | hgt
    · exact absurd hp (pow_lt_one₀ zero_le' hlt hN0).ne
    · exact heq
    · exact absurd hp (one_lt_pow₀ hgt hN0).ne'
  have hI := (ReciprocityTheory.Gal.mem_Ine.mp hs).2 ζ hwζ.le
  have hsζ : s ζ ^ N = 1 := by rw [← map_pow, hζ, map_one]
  have hone := eq_one_of_val_sub_lt B.valuation N ?_ (s ζ * ζ⁻¹) ?_ ?_
  · exact (mul_inv_eq_one₀ hζ0).mp hone
  · intro hlt
    exact hN ((hB N).mp (by simpa using hlt))
  · rw [mul_pow, hsζ, inv_pow, hζ, inv_one, mul_one]
  · have hr : s ζ * ζ⁻¹ - 1 = (s ζ - ζ) * ζ⁻¹ := by field_simp
    rw [hr, map_mul, map_inv₀, hwζ, inv_one, mul_one]
    exact hI

end GlobalTheory.InertiaRootOfUnity
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColRepApplyOfOne
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.ZeroSubmodule

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact (Nat.Prime l)]

theorem colRep_apply_of_one (V : GlobalTheory.Ord2.R2 Ω l) (s : G ℚ Ω)
    (hs : (V : G ℚ Ω → GL (Fin 2) (Qbar l)) s = 1) (v : Fin 2 → Qbar l) :
    UpperTheory.V.Loc.colRep V s v = v := by
  show Matrix.toLin' ((V s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) v = v
  rw [hs]
  simp

def zeroSub (V : GlobalTheory.Ord2.R2 Ω l) (H : Subgroup (G ℚ Ω)) (x : G ℚ Ω → Fin 2 → Qbar l)
    (hV : ∀ a ∈ H, (V : G ℚ Ω → GL (Fin 2) (Qbar l)) a = 1)
    (hx : x ∈ Z1 (UpperTheory.V.Loc.colRep V)) : Subgroup (G ℚ Ω) where
  carrier := {s | s ∈ H ∧ x s = 0}
  one_mem' := by
    refine ⟨H.one_mem, ?_⟩
    have h := ((mem_Z1_iff_cocycle _ x).1 hx).2 1 1
    rw [mul_one, colRep_apply_of_one V 1 (map_one V)] at h
    simpa using h
  mul_mem' := by
    rintro s t ⟨hs, hs0⟩ ⟨ht, ht0⟩
    refine ⟨H.mul_mem hs ht, ?_⟩
    rw [((mem_Z1_iff_cocycle _ x).1 hx).2 s t, colRep_apply_of_one V s (hV s hs), hs0, ht0, add_zero]
  inv_mem' := by
    rintro s ⟨hs, hs0⟩
    refine ⟨H.inv_mem hs, ?_⟩
    have h := ((mem_Z1_iff_cocycle _ x).1 hx).2 s s⁻¹
    rw [mul_inv_cancel, colRep_apply_of_one V s (hV s hs), hs0, zero_add] at h
    have h1 : x 1 = 0 := by
      have h := ((mem_Z1_iff_cocycle _ x).1 hx).2 1 1
      rw [mul_one, colRep_apply_of_one V 1 (map_one V)] at h
      simpa using h
    rw [← h, h1]

theorem cocycle_one (V : GlobalTheory.Ord2.R2 Ω l) (x : G ℚ Ω → Fin 2 → Qbar l)
    (hx : x ∈ Z1 (UpperTheory.V.Loc.colRep V)) : x 1 = 0 := by
  have h := ((mem_Z1_iff_cocycle _ x).1 hx).2 1 1
  rw [mul_one, colRep_apply_of_one V 1 (map_one V)] at h
  simpa using h

theorem zeroSub_normal (V : GlobalTheory.Ord2.R2 Ω l) (H : Subgroup (G ℚ Ω)) (x : G ℚ Ω → Fin 2 → Qbar l)
    (hH : H.Normal) (hV : ∀ a ∈ H, (V : G ℚ Ω → GL (Fin 2) (Qbar l)) a = 1)
    (hx : x ∈ Z1 (UpperTheory.V.Loc.colRep V)) : (zeroSub V H x hV hx).Normal := by
  constructor
  rintro s ⟨hs, hs0⟩ g
  refine ⟨hH.conj_mem s hs g, ?_⟩
  have hc := ((mem_Z1_iff_cocycle _ x).1 hx).2
  rw [hc (g * s) g⁻¹, hc g s, hs0, map_zero, add_zero, map_mul, Module.End.mul_apply,
    colRep_apply_of_one V s (hV s hs), ← hc g g⁻¹, mul_inv_cancel, cocycle_one V x hx]

theorem zeroSub_isClosed (V : GlobalTheory.Ord2.R2 Ω l) (H : Subgroup (G ℚ Ω)) (x : G ℚ Ω → Fin 2 → Qbar l)
    (hHc : IsClosed (H : Set (G ℚ Ω))) (hV : ∀ a ∈ H, (V : G ℚ Ω → GL (Fin 2) (Qbar l)) a = 1)
    (hx : x ∈ Z1 (UpperTheory.V.Loc.colRep V)) : IsClosed (zeroSub V H x hV hx : Set (G ℚ Ω)) := by
  have : (zeroSub V H x hV hx : Set (G ℚ Ω)) = (H : Set (G ℚ Ω)) ∩ x ⁻¹' {0} := rfl
  rw [this]
  exact hHc.inter (isClosed_singleton.preimage ((mem_Z1_iff_cocycle _ x).1 hx).1)

theorem main : ∀ {Ω : Type} [inst : Field Ω] [inst_1 : Algebra ℚ Ω] {l : ℕ} [inst_2 : Fact (Nat.Prime l)] (S : Set GlobalTheory.Ord2.Pl) (V : GlobalTheory.Ord2.R2 Ω l) (H : Subgroup (Formalism.ConjugateSelfDual.G ℚ Ω)) (x : Formalism.ConjugateSelfDual.G ℚ Ω → Fin (2 : ℕ) → Formalism.ConjugateSelfDual.Qbar l), Subgroup.Normal H → IsClosed (↑H : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) → (∀ a ∈ H, (V : Formalism.ConjugateSelfDual.G ℚ Ω → GL (Fin (2 : ℕ)) (Formalism.ConjugateSelfDual.Qbar l)) a = (1 : GL (Fin (2 : ℕ)) (Formalism.ConjugateSelfDual.Qbar l))) → x ∈ ReciprocityTheory.Gal.Z1 (UpperTheory.V.Loc.colRep V) → (∀ v ∉ S, ∀ (B : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver B v → ∀ s ∈ ReciprocityTheory.Gal.Ine B, s ∈ H ∧ x s = (0 : Fin (2 : ℕ) → Formalism.ConjugateSelfDual.Qbar l)) → ∀ a ∈ ReciprocityTheory.Gal.NS Ω S, x a = (0 : Fin (2 : ℕ) → Formalism.ConjugateSelfDual.Qbar l) := by
  intro Ω _ _ l _ S V H x hH hHc hV hx hI a ha
  haveI := zeroSub_normal V H x hH hV hx
  have hle : NS Ω S ≤ zeroSub V H x hV hx := by
    apply Subgroup.topologicalClosure_minimal _ _ (zeroSub_isClosed V H x hHc hV hx)
    apply Subgroup.normalClosure_le_normal
    intro s hs
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hs
    obtain ⟨v, hv, B, hB, hsB⟩ := hs
    exact hI v hv B hB s hsB
  exact (hle ha).2

end GlobalTheory.ZeroSubmodule
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenKerAndIsLocallyConstant
namespace GlobalTheory.OpenKernelLocallyConstant

theorem isOpen_ker_and_isLocallyConstant {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (C : Type) [Group C] (N : ℕ) (ψ : Formalism.ConjugateSelfDual.G ℚ Ω →* C) (hN : N ≠ 0)
    (hψ : UpperTheory.V.Af.KillsMu N ψ) :
    IsOpen (↑(MonoidHom.ker ψ) : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) ∧
      IsLocallyConstant (⇑ψ : Formalism.ConjugateSelfDual.G ℚ Ω → C) := by
  classical
  have hopen : IsOpen (↑(MonoidHom.ker ψ) : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) := by
    have halg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
    let S : Set Ω := {z | z ^ N = 1}
    have hS : S.Finite := by
      refine (Polynomial.nthRoots N (1 : Ω)).toFinset.finite_toSet.subset ?_
      intro z hz
      have hz' : z ^ N = 1 := hz
      simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hN)] using hz'
    have : Finite S := hS.to_subtype
    have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => (halg.isAlgebraic x).isIntegral
    refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ S).fixingSubgroup) ?_
      (IntermediateField.fixingSubgroup_isOpen _)
    intro s hs
    rw [MonoidHom.mem_ker]
    refine hψ s ?_
    intro z hz
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs z
      (IntermediateField.subset_adjoin ℚ S hz)
  refine ⟨hopen, ?_⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (MonoidHom.ker ψ : Set (Formalism.ConjugateSelfDual.G ℚ Ω)),
    hopen.preimage (continuous_const.mul continuous_id), by simp, ?_⟩
  intro y hy
  have h : ψ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  exact h.symm

end GlobalTheory.OpenKernelLocallyConstant
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemOfFinTwo
namespace GlobalTheory.FinTwoMembership

open Matrix

theorem mem_of_fin_two {R : Type*} [CommRing R] (S : Subring R) (M : Matrix (Fin 2) (Fin 2) R)
    (y z : Fin 2 → R) (u : R) (hM : ∀ i j, M i j ∈ S) (hy : ∀ i, y i ∈ S) (hz : ∀ i, z i ∈ S)
    (hu : u ∈ S) :
    M.det * u - ((M.adjugate *ᵥ y) 0 * z 1 - (M.adjugate *ᵥ y) 1 * z 0) ∈ S := by
  have hadj : ∀ i j, M.adjugate i j ∈ S := by
    intro i j
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp [S.neg_mem, hM]
  have hv : ∀ i, (M.adjugate *ᵥ y) i ∈ S := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact S.add_mem (S.mul_mem (hadj _ _) (hy _)) (S.mul_mem (hadj _ _) (hy _))
  have hdet : M.det ∈ S := by
    rw [Matrix.det_fin_two]
    exact S.sub_mem (S.mul_mem (hM _ _) (hM _ _)) (S.mul_mem (hM _ _) (hM _ _))
  exact S.sub_mem (S.mul_mem hdet hu)
    (S.sub_mem (S.mul_mem (hv _) (hz _)) (S.mul_mem (hv _) (hz _)))

theorem ht_mem : ∀ {Ω : Type} [inst : Field Ω] [inst_1 : Algebra ℚ Ω] {l : ℕ} [inst_2 : Fact (Nat.Prime l)]
    (c : UpperTheory.V.HV.Coef l) (W : GlobalTheory.Ord2.R2 Ω l) (y z : Formalism.ConjugateSelfDual.G ℚ Ω → Fin (2 : ℕ) → Formalism.ConjugateSelfDual.Qbar l)
    (u : Formalism.ConjugateSelfDual.G ℚ Ω → Formalism.ConjugateSelfDual.Qbar l),
    (∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω) (i j : Fin (2 : ℕ)), GlobalTheory.Ord2.mat W s i j ∈ UpperTheory.V.HV.Coef.O c) →
    (∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω) (i : Fin (2 : ℕ)), y s i ∈ UpperTheory.V.HV.Coef.O c) →
    (∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω) (i : Fin (2 : ℕ)), z s i ∈ UpperTheory.V.HV.Coef.O c) →
    (∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω), u s ∈ UpperTheory.V.HV.Coef.O c) →
    ∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω), GlobalTheory.Ord2.ht W y z u s ∈ UpperTheory.V.HV.Coef.O c := by
  intro Ω _ _ l _ c W y z u hW hy hz hu s
  have hM : ∀ i j, (GlobalTheory.Ord2.mat W s - 1) i j ∈ c.O.toSubring := by
    intro i j
    rw [Matrix.sub_apply]
    refine c.O.toSubring.sub_mem (hW s i j) ?_
    rw [Matrix.one_apply]
    split_ifs
    · exact c.O.toSubring.one_mem
    · exact c.O.toSubring.zero_mem
  exact mem_of_fin_two c.O.toSubring _ (y s) (z s) (u s) hM (hy s) (hz s) (hu s)

end GlobalTheory.FinTwoMembership
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAuxiliaryPrimeFrobeniusNearCommutator
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAuxiliaryPrimeFrobeniusNearCommutator
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.AuxiliaryInertOddPrime

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem fix_root {l : ℕ} [Fact l.Prime] {s : G ℚ Ω} (hs : s ∈ (cycBar ℚ Ω l).ker) {n : ℕ} {x : Ω}
    (hx : x ^ (l ^ n) = 1) : s x = x := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have h1 : cycZ ℚ Ω l s = 1 := by
    have h := congrArg Units.val (MonoidHom.mem_ker.1 hs)
    apply Units.ext
    have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
      (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
    apply hinj
    simpa [cycBar] using h
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have h2 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) x hx
  have h3 : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) = 1 := h1
  rw [h3] at h2
  have h4 : (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) x = s x := rfl
  rw [h4, Units.val_one, map_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hx, pow_one] at h2
  exact h2

theorem comm_apply {l : ℕ} [Fact l.Prime] {n : ℕ} {a : Ω} (ha : ∀ g : G ℚ Ω, g a = a)
    {s t : G ℚ Ω} (hs : s ∈ (cycBar ℚ Ω l).ker) (ht : t ∈ (cycBar ℚ Ω l).ker) {y : Ω}
    (hy : y ^ (l ^ n) = a) : s (t y) = t (s y) := by
  by_cases h0 : y = 0
  · simp [h0]
  have key : ∀ g : G ℚ Ω, (g y / y) ^ (l ^ n) = 1 := fun g => by
    rw [div_pow, ← map_pow, hy, ha, ← hy]
    exact div_self (pow_ne_zero _ h0)
  obtain ⟨c, hcr, es⟩ : ∃ c : Ω, c ^ (l ^ n) = 1 ∧ s y = c * y :=
    ⟨s y / y, key s, (div_mul_cancel₀ _ h0).symm⟩
  obtain ⟨d, hdr, et⟩ : ∃ d : Ω, d ^ (l ^ n) = 1 ∧ t y = d * y :=
    ⟨t y / y, key t, (div_mul_cancel₀ _ h0).symm⟩
  rw [et, es, map_mul, map_mul, fix_root hs hdr, fix_root ht hcr, es, et]
  ring

theorem comm_fix {l : ℕ} [Fact l.Prime] {n : ℕ} {a : Ω} (ha : ∀ g : G ℚ Ω, g a = a) {σ : G ℚ Ω}
    (hσ : σ ∈ ⁅(cycBar ℚ Ω l).ker, (cycBar ℚ Ω l).ker⁆) {y : Ω} (hy : y ^ (l ^ n) = a) : σ y = y := by
  let K : Subgroup (G ℚ Ω) := ⨅ z : {z : Ω // z ^ (l ^ n) = a}, MulAction.stabilizer (G ℚ Ω) (z : Ω)
  have hK : ∀ g, g ∈ K ↔ ∀ z : Ω, z ^ (l ^ n) = a → g z = z := fun g => by
    simp only [K, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, Subtype.forall]
  have hle : ⁅(cycBar ℚ Ω l).ker, (cycBar ℚ Ω l).ker⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro s hs t ht
    rw [hK]
    intro z hz
    have hz' : ((t * s)⁻¹ z) ^ (l ^ n) = a := by rw [← map_pow, hz, ha]
    have e : s * t * s⁻¹ * t⁻¹ = (s * t) * (t * s)⁻¹ := by group
    rw [commutatorElement_def, e, AlgEquiv.mul_apply, AlgEquiv.mul_apply, comm_apply ha hs ht hz', ← AlgEquiv.mul_apply,
      ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  exact (hK σ).1 (hle hσ) y hy

theorem isOpen_stab (x : Ω) : IsOpen {τ : G ℚ Ω | τ x = x} := by
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hx : IsIntegral ℚ x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) := IntermediateField.adjoin.finiteDimensional hx
  have h := IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {x})
  have hle : (IntermediateField.adjoin ℚ {x}).fixingSubgroup ≤ MulAction.stabilizer (G ℚ Ω) x := fun g hg => by
    rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (IntermediateField.mem_adjoin_simple_self ℚ x)
  have e : {τ : G ℚ Ω | τ x = x} = (MulAction.stabilizer (G ℚ Ω) x : Set (G ℚ Ω)) := by
    ext τ; simp [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  rw [e]
  exact Subgroup.isOpen_mono hle h

theorem root_mod {B : ValuationSubring Ω} {p m N : ℕ} (hp : p.Prime) (hpB : B.valuation (p : Ω) < 1) (hm : m ≠ 0)
    {α : Ω} (hα : α ^ m = (N : Ω)) (hfr : B.valuation α ≤ 1 → B.valuation (α - α ^ p) < 1) :
    ∃ x : ZMod p, x ^ m = (N : ZMod p) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hαle : B.valuation α ≤ 1 := by
    have h1 : B.valuation α ^ m ≤ 1 := by
      rw [← map_pow, hα]; exact (B.valuation_le_one_iff _).2 (natCast_mem B N)
    exact (pow_le_one_iff hm).1 h1
  have hαB : α ∈ B := (B.valuation_le_one_iff α).1 hαle
  let a : B := ⟨α, hαB⟩
  have hmax : ∀ b : B, B.valuation (b : Ω) < 1 → IsLocalRing.residue B b = 0 := fun b hb =>
    (IsLocalRing.residue_eq_zero_iff b).2 ((B.valuation_lt_one_iff b).2 hb)
  have hpk : ((p : ℕ) : IsLocalRing.ResidueField B) = 0 := by
    have := hmax (p : B) (by simpa using hpB)
    simpa using this
  haveI : CharP (IsLocalRing.ResidueField B) p := (CharP.charP_iff_prime_eq_zero hp).2 hpk
  let φ : ZMod p →+* IsLocalRing.ResidueField B := ZMod.castHom (dvd_refl p) _
  have hφ : Function.Injective φ := φ.injective
  have hr : IsLocalRing.residue B a ^ p = IsLocalRing.residue B a := by
    have := hmax (a - a ^ p) (by simpa [a] using hfr hαle)
    rw [map_sub, map_pow, sub_eq_zero] at this
    exact this.symm
  have hP : (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)) ≠ 0 :=
    Polynomial.X_pow_sub_X_ne_zero hp.one_lt
  have hsub : Finset.univ.image φ ⊆
      (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).roots.toFinset := by
    intro y hy
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, ← map_pow, ZMod.pow_card, sub_self]
  have hcard : (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).roots.toFinset.card ≤
      (Finset.univ.image φ).card := by
    rw [Finset.card_image_of_injective _ hφ, Finset.card_univ, ZMod.card]
    calc _ ≤ Multiset.card (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).roots :=
          Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).natDegree :=
          Polynomial.card_roots' _
      _ = p := Polynomial.natDegree_X_pow_sub_X hp.one_lt
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hrmem : IsLocalRing.residue B a ∈
      (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, hr, sub_self]
  rw [← heq] at hrmem
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hrmem
  refine ⟨x, hφ ?_⟩
  have ha : a ^ m = (N : B) := Subtype.ext (by simp [a, hα])
  rw [map_pow, hx, map_natCast, ← map_pow, ha, map_natCast]

end GlobalTheory.Ord2.AuxiliaryInertOddPrime

namespace GlobalTheory.Ord2.AuxiliaryInertOddPrime

theorem normV_eq_absNorm (v : Pl) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem absNorm_dvd_of_mem {I : Ideal (𝓞 ℚ)} {n : ℕ} (h : (n : 𝓞 ℚ) ∈ I) : Ideal.absNorm I ∣ n := by
  have h1 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem I).2 h)
  rwa [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one] at h1

theorem natCast_mem_iff (v : Pl) (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ normV v ∣ n := by
  rw [normV_eq_absNorm]
  refine ⟨absNorm_dvd_of_mem, ?_⟩
  rintro ⟨c, rfl⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem normV_prime' (v : Pl) : (normV v).Prime := by
  have h1 : 1 < normV v := by
    rw [normV_eq_absNorm]
    exact NumberField.HeightOneSpectrum.one_lt_absNorm v
  refine Nat.prime_def.2 ⟨h1, fun m hm => ?_⟩
  obtain ⟨c, hc⟩ := hm
  have h2 := (natCast_mem_iff v _).2 dvd_rfl
  rw [hc, Nat.cast_mul] at h2
  rcases v.isPrime.mem_or_mem h2 with h | h
  · exact Or.inr (Nat.dvd_antisymm ⟨c, hc⟩ ((natCast_mem_iff v _).1 h))
  · have h3 := Nat.dvd_antisymm (Dvd.intro_left m hc.symm) ((natCast_mem_iff v _).1 h)
    rw [h3] at hc
    exact Or.inl (Nat.eq_of_mul_eq_mul_right (by omega) (hc.symm.trans (one_mul _).symm))

theorem val_natCast_lt_one_iff {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {w : Pl}
    (h : IsPlaceOver A w) (n : ℕ) : A.valuation (n : Ω) < 1 ↔ normV w ∣ n := by
  rw [← natCast_mem_iff, ← h]
  simp

end GlobalTheory.Ord2.AuxiliaryInertOddPrime

namespace GlobalTheory.Ord2.AuxiliaryInertOddPrime

theorem exists_odd_prime_gt_two_bounds : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ)
    (S S' : Finset Pl) (U : Subgroup (G ℚ Ω)) (σ : G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) →
    σ ∈ ⁅(cycBar ℚ Ω l).ker, (cycBar ℚ Ω l).ker⁆ → ∃ (w : Pl) (B : ValuationSubring Ω) (τ : G ℚ Ω),
      w ∉ S ∧ w ∉ S' ∧ IsPlaceOver B w ∧ IsFrob B (normV w) τ ∧ τ ∈ Dec (F := ℚ) B ∧ σ⁻¹ * τ ∈ U ∧
      l ^ n ∣ normV w - 1 ∧ ∀ v ∈ S, ∃ x : ZMod (normV w), x ^ (l ^ n) = (normV v : ZMod (normV w)) := by
  intro l hl Ω _ _ _ n S S' U σ hU hσ
  classical
  haveI hΩ : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hm : 0 < l ^ n := pow_pos hl.out.pos n
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ (l ^ n) := by
    haveI : NeZero ((l ^ n : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hm.ne'⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ n) Ω)
      (Polynomial.degree_cyclotomic_pos _ Ω hm).ne'
    exact ⟨z, Polynomial.isRoot_cyclotomic_iff.1 hz⟩
  have hα : ∀ v : Pl, ∃ α : Ω, α ^ (l ^ n) = (normV v : Ω) := fun v => IsAlgClosed.exists_pow_nat_eq _ hm
  choose α hα using hα
  let T : Finset Ω := insert ζ (S.image α)
  let O : Set (G ℚ Ω) := {τ | σ⁻¹ * τ ∈ U} ∩ ⋂ x ∈ T, {τ | τ x = x}
  have hO : IsOpen O := (hU.preimage (continuous_const_mul σ⁻¹)).inter
    (isOpen_biInter_finset fun x _ => isOpen_stab x)
  have hσker : σ ∈ (cycBar ℚ Ω l).ker := Subgroup.commutator_le_left _ _ hσ
  have hσO : σ ∈ O := by
    refine ⟨by simp [U.one_mem], Set.mem_iInter₂.2 fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact fix_root hσker hζ.pow_eq_one
    · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hx
      exact comm_fix (fun g => map_natCast g _) hσ (hα v)
  have hl0 : Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hl.out.ne_zero
  have hTfin : ((S : Set Pl) ∪ (S' : Set Pl) ∪ {v : Pl | v.asIdeal ∣ Ideal.span {((l : ℕ) : 𝓞 ℚ)}}).Finite :=
    ((S.finite_toSet).union (S'.finite_toSet)).union (Ideal.finite_factors hl0)
  have hdense := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hTfin
  obtain ⟨τ, hτO, w, hwT, -, B, hB, hτ⟩ := hdense.inter_open_nonempty O hO ⟨σ, hσO⟩
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or] at hwT
  obtain ⟨⟨hwS, hwS'⟩, hwl⟩ := hwT
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h =>
    hwl (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h))
  have hfix : ∀ x ∈ T, τ x = x := fun x hx => Set.mem_iInter₂.1 hτO.2 x hx
  have hp : (normV w).Prime := normV_prime' w
  have hpB : B.valuation ((normV w : ℕ) : Ω) < 1 := (val_natCast_lt_one_iff hB _).2 dvd_rfl
  have hlB : ¬ B.valuation ((l : ℕ) : Ω) < 1 := fun h => hlw ((hB _).1 (by simpa using h))
  have hnot : ¬ B.valuation ((l ^ n : ℕ) : Ω) < 1 := fun h =>
    hlB ((val_natCast_lt_one_iff hB l).2 (hp.dvd_of_dvd_pow ((val_natCast_lt_one_iff hB (l ^ n)).1 h)))
  have hpows := (ML.placeBasic Ω).2.2.2.2.2.2.1 B (normV w) (l ^ n) τ hτ hnot
  have h1 : ζ ^ normV w = ζ := (hpows ζ hζ.pow_eq_one).symm.trans (hfix ζ (Finset.mem_insert_self _ _))
  have h2 : ζ ^ (normV w - 1) = 1 := by
    have hz : ζ ≠ 0 := hζ.ne_zero hm.ne'
    refine mul_right_cancel₀ hz ?_
    rw [← pow_succ, Nat.sub_add_cancel hp.one_le, one_mul, h1]
  refine ⟨w, B, τ, hwS, hwS', hB, hτ, hτ.1, hτO.1, hζ.dvd_of_pow_eq_one _ h2, fun v hv => ?_⟩
  have hτv : τ (α v) = α v := hfix _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem α hv))
  refine root_mod hp hpB hm.ne' (hα v) fun h => ?_
  have := hτ.2 (α v) h
  rwa [hτv] at this

end GlobalTheory.Ord2.AuxiliaryInertOddPrime
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAuxiliaryPrimeFrobeniusNearCommutatorStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_auxiliary_prime_frobenius_near_commutator : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (S S' : Finset Pl) (U : Subgroup (G ℚ Ω)) (σ : G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → σ ∈ ⁅(cycBar ℚ Ω l).ker, (cycBar ℚ Ω l).ker⁆ → ∃ (w : Pl) (B : ValuationSubring Ω) (τ : G ℚ Ω), w ∉ S ∧ w ∉ S' ∧ IsPlaceOver B w ∧ IsFrob B (normV w) τ ∧ τ ∈ Dec (F := ℚ) B ∧ σ⁻¹ * τ ∈ U ∧ l ^ n ∣ normV w - 1 ∧ ∀ v ∈ S, ∃ x : ZMod (normV w), x ^ (l ^ n) = (normV v : ZMod (normV w)) := by
  first | exact @GlobalTheory.Ord2.AuxiliaryInertOddPrime.exists_odd_prime_gt_two_bounds | exact GlobalTheory.Ord2.AuxiliaryInertOddPrime.exists_odd_prime_gt_two_bounds | (intros; apply GlobalTheory.Ord2.AuxiliaryInertOddPrime.exists_odd_prime_gt_two_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormAlgebraMapLeOne
namespace GlobalTheory.IntegralAlgebraMapNormBound

open Polynomial

lemma norm_algebraMap_le_one {l : ℕ} [Fact (Nat.Prime l)] (c : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) c‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  have h1 : ‖algebraMap ℚ_[l] (PadicAlgCl l) (algebraMap ℤ_[l] ℚ_[l] c)‖
      = ‖algebraMap ℤ_[l] ℚ_[l] c‖ := PadicAlgCl.norm_extends l _
  rw [h1]
  exact PadicInt.norm_le_one c

theorem norm_le_one_of_isIntegral {l : ℕ} [Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨p, hmon, hp⟩ := hx
  set n := p.natDegree with hn
  have hx0 : 0 < ‖x‖ := lt_trans one_pos hlt
  rw [eval₂_eq_sum_range, Finset.sum_range_succ, ← hn] at hp
  have hlead : p.coeff n = 1 := hmon
  rw [hlead, map_one, one_mul] at hp
  have heq : x ^ n = -∑ i ∈ Finset.range n, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hp
  have hbound : ‖∑ i ∈ Finset.range n, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i‖
      ≤ ‖x‖ ^ n / ‖x‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow, le_div_iff₀ hx0]
    calc ‖algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i)‖ * ‖x‖ ^ i * ‖x‖
        ≤ 1 * ‖x‖ ^ i * ‖x‖ := by
          gcongr
          exact norm_algebraMap_le_one _
      _ = ‖x‖ ^ (i + 1) := by ring
      _ ≤ ‖x‖ ^ n := pow_le_pow_right₀ hlt.le (by omega)
  have hxn : ‖x‖ ^ n ≤ ‖x‖ ^ n / ‖x‖ := by
    calc ‖x‖ ^ n = ‖x ^ n‖ := (norm_pow x n).symm
      _ = _ := by rw [heq, norm_neg]
      _ ≤ _ := hbound
  have hpos : 0 < ‖x‖ ^ n := pow_pos hx0 n
  have : ‖x‖ ^ n / ‖x‖ < ‖x‖ ^ n := div_lt_self hpos hlt
  linarith

theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l),
    IsIntegral ℤ_[l] x → ‖x‖ ≤ (1 : ℝ) :=
  fun x hx => norm_le_one_of_isIntegral x hx

end GlobalTheory.IntegralAlgebraMapNormBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CohomologyUnramifiedLift
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

section HtComm

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

private theorem htc_norm_le_one_of_isIntegral (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.GlobalTheory.IntegralAlgebraMapNormBound.main x hx

theorem htc_norm_le_one (c : Coef l) (x : Qbar l) (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  htc_norm_le_one_of_isIntegral x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

theorem htc_continuous_cycBar : Continuous (cycBar ℚ Ω l) :=
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ ℚ Ω l)

theorem htc_dual1_eq_one {W : R2 Ω l} {s : G ℚ Ω} (hs : s ∈ N0g W) : dual1 W s = 1 := by
  obtain ⟨hc, hw⟩ := Subgroup.mem_inf.1 hs
  rw [MonoidHom.mem_ker] at hc hw
  have hd : dt W s = 1 := by simp [dt, hw]
  simp [dual1, Af.tw, hw, hc, hd]

theorem htc_cocycle {W : R2 Ω l} {x : G ℚ Ω → Fin 2 → Qbar l} (hx : x ∈ Z1 (Loc.colRep W)) (s t : G ℚ Ω) :
    x (s * t) = x s + mat W s *ᵥ x t := by
  have := hx.2 s t
  simpa [Loc.colRep, Matrix.toLin'_apply] using this

theorem htc_open_near (f : G ℚ Ω → Qbar l) (hf : Continuous f) (σ : G ℚ Ω) (r : ℝ) (hr : 0 < r) :
    ∃ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ a ∈ U, ‖f (σ * a) - f σ‖ < r := by
  have hc : Continuous fun a : G ℚ Ω => ‖f (σ * a) - f σ‖ :=
    ((hf.comp (continuous_const_mul σ)).sub continuous_const).norm
  have h1 : {a : G ℚ Ω | ‖f (σ * a) - f σ‖ < r} ∈ nhds (1 : G ℚ Ω) :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp [hr])
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).1 h1
  haveI := hE
  exact ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, fun a ha => hsub ha⟩

theorem htc_ker_toGS (S : Set Pl) : (toGS Ω S).ker = NS (F := ℚ) Ω S := by
  unfold toGS
  exact QuotientGroup.ker_mk' _

theorem htc_NS_anti {S S' : Set Pl} (h : S ⊆ S') : NS (F := ℚ) Ω S' ≤ NS (F := ℚ) Ω S := by
  unfold NS
  refine Subgroup.topologicalClosure_minimal _ (le_trans (Subgroup.normalClosure_mono ?_)
    (Subgroup.le_topologicalClosure _)) (Subgroup.isClosed_topologicalClosure _)
  intro x hx
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨v, hv, A, hA, hx⟩ := hx
  exact ⟨v, fun h' => hv (h h'), A, hA, hx⟩

theorem htc_Ine_le_NS {S : Set Pl} {v : Pl} (hv : v ∉ S) {B : ValuationSubring Ω} (hB : IsPlaceOver B v) :
    Ine (F := ℚ) B ≤ NS (F := ℚ) Ω S := fun s hs =>
  Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (by
    simp only [Set.mem_iUnion]
    exact ⟨v, hv, B, hB, hs⟩))

theorem htc_NS_le (S : Set Pl) (H : Subgroup (G ℚ Ω)) [H.Normal] (hc : IsClosed (H : Set (G ℚ Ω)))
    (h : ∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → Ine (F := ℚ) B ≤ H) : NS (F := ℚ) Ω S ≤ H := by
  unfold NS
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hc
  intro s hs
  simp only [Set.mem_iUnion] at hs
  obtain ⟨v, hv, B, hB, hs⟩ := hs
  exact h v hv B hB hs

theorem htc_ht_mem (c : Coef l) (W : R2 Ω l) (y z : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l)
    (hO : ∀ s i j, mat W s i j ∈ c.O) (hyO : ∀ s i, y s i ∈ c.O) (hzO : ∀ s i, z s i ∈ c.O) (huO : ∀ s, u s ∈ c.O)
    (s : G ℚ Ω) : ht W y z u s ∈ c.O :=
  _root_.GlobalTheory.FinTwoMembership.ht_mem c W y z u hO hyO hzO huO s

theorem congruence_mul_of_unit_factor {n : ℕ} {P h un D : Qbar l} (h1 : Cg n (P * h) 0) (h2 : Cg n P (un * D)) (hun : ‖un‖ = 1)
    (hh : ‖h‖ ≤ 1) : Cg n (D * h) 0 :=
  _root_.UpperTheory.Reformulated.B.Yza4.congruence_mul_of_unit_factor h1 h2 hun hh

theorem htc_cocycle_NS (S : Set Pl) (V : R2 Ω l) (H : Subgroup (G ℚ Ω)) (x : G ℚ Ω → Fin 2 → Qbar l) (hN : H.Normal)
    (hc : IsClosed (H : Set (G ℚ Ω))) (hV : ∀ a ∈ H, V a = 1) (hx : x ∈ Z1 (Loc.colRep V))
    (h : ∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ s ∈ Ine (F := ℚ) B, s ∈ H ∧ x s = 0) :
    ∀ a ∈ NS (F := ℚ) Ω S, x a = 0 :=
  _root_.GlobalTheory.ZeroSubmodule.main S V H x hN hc hV hx h

theorem htc_killsMu_open [IsAlgClosure ℚ Ω] (C : Type) [Group C] (N : ℕ) (ψ : G ℚ Ω →* C) (hN : N ≠ 0)
    (h : KillsMu N ψ) : IsOpen (ψ.ker : Set (G ℚ Ω)) ∧ IsLocallyConstant ψ :=
  _root_.GlobalTheory.OpenKernelLocallyConstant.isOpen_ker_and_isLocallyConstant C N ψ hN h

theorem htc_Ine_fix_mu (N : ℕ) (v : Pl) (B : ValuationSubring Ω) (hB : IsPlaceOver B v) (hN : ((N : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    ∀ s ∈ Ine (F := ℚ) B, ∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ :=
  _root_.GlobalTheory.InertiaRootOfUnity.inertia_fixes_root_of_unity N v B hB hN

theorem htc_places (w : Pl) : normV w ≠ 0 ∧ (∀ v : Pl, v ≠ w → ((normV w : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) ∧
    ∀ (p : ℕ), p.Prime → ∀ v v' : Pl, ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → ((p : ℕ) : 𝓞 ℚ) ∈ v'.asIdeal → v = v' :=
  _root_.UpperTheory.Reformulated.B.Yza3.htc_places w

end HtComm

theorem ht_vanish_commutator : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (y z : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l) (S' : Finset Pl) (n : ℕ), 1 ≤ n → (∀ s i j, mat W s i j ∈ c.O) → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, y s i ∈ c.O) → (∀ s i, z s i ∈ c.O) → Unr W y → (∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c.O) ∧ ∀ s ∈ Ine (F := ℚ) B, z s = mat (dual1 W) s *ᵥ x - x) → (∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c.O) ∧ ∀ s ∈ Dec (F := ℚ) A, z s = mat (dual1 W) s *ᵥ x - x) → (∀ w : Pl, w ∉ S' → l ^ n ∣ normV w - 1 → ∀ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)), KillsMu (normV w) ψ → Function.Surjective ψ → Tame c W y n w ψ) → Continuous u → (∀ s, u s ∈ c.O) → (∀ s, ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cg n (u (s * a)) (u s)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → ∀ σ ∈ ⁅H0g W, H0g W⁆, Cg n ((mat W σ - 1).det * ht W y z u σ) 0 := by
  intro hLit l _ Ω _ _ _ e S A W hW c y z u S' n hn hO hy hz hyO hzO hyU hzq hzl hTame huc huO huS hcup σ hσ
  classical
  have hWc : Continuous W := hW.cont
  have hdet2 : dt W ^ 2 = 1 := hW.det2
  have hAbove : ContainsAbove S l := hW.above
  have hyc : Continuous y := hy.1
  have hzc : Continuous z := hz.1
  have hσH : σ ∈ H0g W := by
    refine (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_) hσ
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hσcyc : σ ∈ ⁅(cycBar ℚ Ω l).ker, (cycBar ℚ Ω l).ker⁆ := Subgroup.commutator_mono inf_le_left inf_le_left hσ
  have hdtσ : dt W σ = 1 := (Subgroup.mem_inf.1 hσH).2
  set F : G ℚ Ω → Qbar l := fun s => (mat W s - 1).det * ht W y z u s with hF
  have hmatc : Continuous fun s => mat W s := Units.continuous_val.comp hWc
  have hFc : Continuous F := by
    have h1 : Continuous fun s => mat W s - 1 := hmatc.sub continuous_const
    have h2 : Continuous fun s => (mat W s - 1).det := h1.matrix_det
    have h3 : Continuous fun s => (mat W s - 1).adjugate *ᵥ y s := h1.matrix_adjugate.matrix_mulVec hyc
    refine h2.mul ?_
    unfold ht om
    refine (h2.mul huc).sub ?_
    have hz0 := (continuous_apply 0).comp hzc
    have hz1 := (continuous_apply 1).comp hzc
    have h30 := (continuous_apply 0).comp h3
    have h31 := (continuous_apply 1).comp h3
    exact (h30.mul hz1).sub (h31.mul hz0)
  have hr : (0 : ℝ) < ‖((l : ℕ) : Qbar l) ^ n‖ :=
    norm_pos_iff.2 (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  have hr2 : (0 : ℝ) < ‖(2 : Qbar l)‖ := norm_pos_iff.2 two_ne_zero
  obtain ⟨U₁, hU₁o, hU₁⟩ := htc_open_near F hFc σ _ hr
  obtain ⟨U₂, hU₂o, hU₂⟩ := htc_open_near (fun s => (mat W s).det) hmatc.matrix_det σ _ hr2
  have hdtv : ∀ s, ((dt W s : (Qbar l)ˣ) : Qbar l) = (mat W s).det := fun s => rfl
  obtain ⟨w, B, τ, hwS, hwS', hB, hFrob, hτD, hστ, hdiv, hpow⟩ :=
    GlobalTheory.T.exists_auxiliary_prime_frobenius_near_commutator l Ω n S S' (U₁ ⊓ U₂) σ (by rw [Subgroup.coe_inf]; exact hU₁o.inter hU₂o) hσcyc
  have hdtτ : dt W τ = 1 := by
    have h := congrArg (fun f : G ℚ Ω →* (Qbar l)ˣ => f τ) hdet2
    simp only [pow_two, MonoidHom.mul_apply, MonoidHom.one_apply] at h
    have hsq : ((dt W τ : (Qbar l)ˣ) : Qbar l) * (dt W τ : Qbar l) = 1 := by rw [← Units.val_mul, h, Units.val_one]
    rcases mul_self_eq_one_iff.1 hsq with h1 | h1
    · exact Units.ext h1
    · exfalso
      have h3 := hU₂ _ (Subgroup.mem_inf.1 hστ).2
      simp only [mul_inv_cancel_left] at h3
      rw [← hdtv, ← hdtv, h1, hdtσ, Units.val_one, show (-1 : Qbar l) - 1 = -2 by ring, norm_neg] at h3
      exact lt_irrefl _ h3
  have hwl : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => hwS (hAbove w h)
  obtain ⟨ψ, hKill, hSurj, hIne1, hDecK⟩ := GlobalTheory.T.exists_character_primeConductor_degree_prime_pow l Ω n w hn hdiv
  have hT := hTame w hwS' hdiv ψ hKill hSurj
  obtain ⟨P, un, d, hPO, hun, hPfrob, hdc, hdO, hdrel, hdker, hdq⟩ :=
    GlobalTheory.T.unramified_cocycle_kills_roots l Ω c n S W y w ψ hWc hO hAbove hW.unr hyO hKill hwS hT
  obtain ⟨hNw, hNwv, hpl⟩ := htc_places w
  obtain ⟨hψo, hψlc⟩ := htc_killsMu_open _ (normV w) ψ hNw hKill
  have hψIne : ∀ v, v ≠ w → ∀ B' : ValuationSubring Ω, IsPlaceOver B' v → Ine (F := ℚ) B' ≤ ψ.ker :=
    fun v hv B' hB' s hs => hKill s (fun ζ hζ => htc_Ine_fix_mu (normV w) v B' hB' (hNwv v hv) s hs ζ hζ)

  haveI hN0n : (N0g W).Normal := by unfold N0g; infer_instance
  have hN0c : IsClosed (N0g W : Set (G ℚ Ω)) := by
    unfold N0g
    rw [Subgroup.coe_inf, MonoidHom.coe_ker, MonoidHom.coe_ker]
    exact (isClosed_singleton.preimage htc_continuous_cycBar).inter (isClosed_singleton.preimage hWc)
  have hIneN0 : ∀ v, v ∉ (S : Set Pl) → ∀ B' : ValuationSubring Ω, IsPlaceOver B' v → Ine (F := ℚ) B' ≤ N0g W := by
    intro v hv B' hB' s hs
    have hvl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (hAbove v h)
    refine Subgroup.mem_inf.2 ⟨?_, hW.unr v hv B' hB' hs⟩
    rw [MonoidHom.mem_ker]
    exact cyc_eq_one_of_mem_Ine hvl hB' hs
  have hNS_N0 : NS (F := ℚ) Ω (S : Set Pl) ≤ N0g W := htc_NS_le _ _ hN0c hIneN0
  have hNSy : ∀ a ∈ NS (F := ℚ) Ω (S : Set Pl), y a = 0 :=
    htc_cocycle_NS _ W (N0g W) y hN0n hN0c (fun a ha => (Subgroup.mem_inf.1 ha).2) hy (by
      intro v hv B' hB' s hs
      have hvl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (hAbove v h)
      have hWs : W s = 1 := (hIneN0 v hv B' hB' hs).2
      obtain ⟨B0, hB0, hcob⟩ := hyU v hvl
      obtain ⟨x, hx⟩ := (GlobalTheory.T.localConditions_independent_of_place_over l Ω W y hy v B0 B' hB0 hB').1 hcob
      refine ⟨hIneN0 v hv B' hB' hs, ?_⟩
      rw [hx s hs, show mat W s = 1 by simp [mat, hWs], Matrix.one_mulVec, sub_self])
  have hNSz : ∀ a ∈ NS (F := ℚ) Ω (S : Set Pl), z a = 0 :=
    htc_cocycle_NS _ (dual1 W) (N0g W) z hN0n hN0c (fun a ha => htc_dual1_eq_one ha) hz (by
      intro v hv B' hB' s hs
      have hvl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (hAbove v h)
      have hd1 : dual1 W s = 1 := htc_dual1_eq_one (hIneN0 v hv B' hB' hs)
      obtain ⟨x, -, hx⟩ := hzq v hvl B' hB'
      refine ⟨hIneN0 v hv B' hB' hs, ?_⟩
      rw [hx s hs, show mat (dual1 W) s = 1 by simp [mat, hd1], Matrix.one_mulVec, sub_self])
  set S2 : Finset Pl := insert w S with hS2
  have hsub : (S : Set Pl) ⊆ (S2 : Set Pl) := Finset.coe_subset.2 (Finset.subset_insert _ _)
  have hNSψ : NS (F := ℚ) Ω (S2 : Set Pl) ≤ ψ.ker := by
    refine htc_NS_le _ _ (Subgroup.isClosed_of_isOpen _ hψo) fun v hv B' hB' => hψIne v ?_ B' hB'
    rintro rfl
    exact hv (by simp [hS2])
  have hker2 : (toGS Ω (S2 : Set Pl)).ker ≤ N0g W ⊓ ψ.ker := by
    rw [htc_ker_toGS]
    exact le_inf ((htc_NS_anti hsub).trans hNS_N0) hNSψ
  have hxi := GlobalTheory.T.cocycle_pairing_locally_constant l Ω c n S2 W y z d u P ψ hWc hO hdet2 hker2 hψlc hPO hy hz hyO hzO
    (fun a ha => by
      rw [htc_ker_toGS] at ha
      have ha' := htc_NS_anti hsub ha
      refine ⟨hNSy a ha', hNSz a ha', hdker a ?_⟩
      rw [htc_ker_toGS, ← Finset.coe_insert]
      exact ha)
    huc huO (fun s a ha => huS s a (by rw [htc_ker_toGS] at ha ⊢; exact htc_NS_anti hsub ha)) hcup hdc hdO hdrel

  have hψ0 : ∀ s, ψ s = 1 → (((ψ s).toAdd.val : ℕ) : Qbar l) = 0 := fun s hs => by rw [hs]; simp
  have hDecψ : ∀ v ∈ S, ∀ B' : ValuationSubring Ω, IsPlaceOver B' v → ∀ s ∈ Dec (F := ℚ) B', ψ s = 1 :=
    fun v hv B' hB' s hs => hDecK v (fun h => hwS (h ▸ hv)) (hpow v hv) B' hB' hs
  have hCv : ∀ a : Fin 2 → Qbar l, Cv n a a := fun a i => by simp [Cg]
  have hCocd : ∀ v ∈ S, ∀ B' : ValuationSubring Ω, IsPlaceOver B' v → Coc1 c n W (Dec (F := ℚ) B') d :=
    fun v hv B' hB' => ⟨hdc.continuousOn, hdO, fun s hs t _ => by
      have := hdrel s t
      rw [hψ0 s (hDecψ v hv B' hB' s hs), zero_mul, zero_smul, add_zero] at this
      exact this⟩
  have hCocz : ∀ H : Subgroup (G ℚ Ω), Coc1 c n (dual1 W) H z :=
    fun H => ⟨hzc.continuousOn, hzO, fun s _ t _ => by rw [htc_cocycle hz]; exact hCv _⟩
  set ξ : G ℚ Ω → G ℚ Ω → Qbar l := fun s t => cup W d z s t - (((ψ s).toAdd.val : ℕ) : Qbar l) * P * eps l s * u t
    with hξ
  have hξDec : ∀ v ∈ S, ∀ B' : ValuationSubring Ω, IsPlaceOver B' v → Cob2 c n (Dec (F := ℚ) B') (cup W d z) →
      Cob2 c n (Dec (F := ℚ) B') ξ := by
    rintro v hv B' hB' ⟨x, hx1, hx2, hx3⟩
    refine ⟨x, hx1, hx2, fun s hs t ht => ?_⟩
    have e : ξ s t = cup W d z s t := by
      simp only [hξ, hψ0 s (hDecψ v hv B' hB' s hs), zero_mul, sub_zero]
    rw [e]
    exact hx3 s hs t ht
  have hloc : ∀ v ∈ S2, v ≠ w → ∃ B' : ValuationSubring Ω, IsPlaceOver B' v ∧ Cob2 c n (Dec (F := ℚ) B') ξ := by
    intro v hv hvw
    have hvS : v ∈ S := (Finset.mem_insert.1 hv).resolve_left hvw
    by_cases hvl : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
    · obtain ⟨v', hAv', hlv'⟩ := hW.atL
      have hvv' : v = v' := hpl l (Fact.out : l.Prime) v v' hvl hlv'
      subst hvv'
      refine ⟨A, hAv', hξDec v hvS A hAv' ?_⟩
      obtain ⟨x, hxO, hx⟩ := hzl
      exact GlobalTheory.T.cup_product_coboundary_mod l Ω c n W (Dec (F := ℚ) A) d z hWc hO hdet2 (hCocd v hvS A hAv') (hCocz _)
        (Or.inr ⟨x, hxO, fun s hs => by rw [hx s hs]; exact hCv _⟩)
    · obtain ⟨B', hB', hcobd⟩ := hdq v hvS hvl
      obtain ⟨x, hxO, hx⟩ := hzq v hvl B' hB'
      refine ⟨B', hB', hξDec v hvS B' hB' ?_⟩
      exact GlobalTheory.T.cupProduct_unramifiedClasses_vanishes hLit l Ω c n W v B' d z hWc hO hdet2 hB' hvl (hCocd v hvS B' hB') (hCocz _) hcobd
        ⟨x, hxO, fun s hs => by rw [hx s hs]; exact hCv _⟩
  have hAbove2 : ContainsAbove S2 l := fun v hv => Finset.mem_insert_of_mem (hAbove v hv)
  have hCobw := GlobalTheory.T.integralTwoCocycle_reciprocity_trivial_at_last_place hLit l Ω c n S2 ξ w hW.l_odd hAbove2 hxi (Finset.mem_insert_self w S) hloc B hB
  have hIneB : Ine (F := ℚ) B ≤ NS (F := ℚ) Ω (S : Set Pl) := htc_Ine_le_NS (by exact_mod_cast hwS) hB
  have hlocw := GlobalTheory.T.local_height_frobenius_place l Ω c n W y z d u P ψ w B τ hn hWc hO hdet2 hB hdiv hFrob hτD hdtτ (hW.unr w hwS B hB)
    hψlc (hIne1 B hB) hPO hy hz hyO hzO (fun a ha => ⟨hNSy a (hIneB ha), hNSz a (hIneB ha)⟩) huc huO
    (fun s a ha => huS s a (by rw [htc_ker_toGS]; exact hIneB ha)) hcup hdc hdO hdrel hCobw
  have hFτ : Cg n (F τ) 0 := congruence_mul_of_unit_factor hlocw (hPfrob B τ hB hFrob) hun
    (htc_norm_le_one c _ (htc_ht_mem c W y z u hO hyO hzO huO τ))
  have hFσ := hU₁ _ (Subgroup.mem_inf.1 hστ).1
  simp only [mul_inv_cancel_left] at hFσ
  show ‖F σ - 0‖ ≤ _
  unfold Cg at hFτ
  rw [sub_zero] at hFτ ⊢
  have e : F σ = F τ + -(F τ - F σ) := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hFτ ?_)
  rw [norm_neg]
  exact hFσ.le

end GlobalTheory.Ord2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CohomologyUnramifiedLiftStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_unramified_lift : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (y z : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l) (S' : Finset Pl) (n : ℕ), 1 ≤ n → (∀ s i j, mat W s i j ∈ c.O) → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, y s i ∈ c.O) → (∀ s i, z s i ∈ c.O) → Unr W y → (∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c.O) ∧ ∀ s ∈ Ine (F := ℚ) B, z s = mat (dual1 W) s *ᵥ x - x) → (∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c.O) ∧ ∀ s ∈ Dec (F := ℚ) A, z s = mat (dual1 W) s *ᵥ x - x) → (∀ w : Pl, w ∉ S' → l ^ n ∣ normV w - 1 → ∀ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)), KillsMu (normV w) ψ → Function.Surjective ψ → Tame c W y n w ψ) → Continuous u → (∀ s, u s ∈ c.O) → (∀ s, ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cg n (u (s * a)) (u s)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → ∀ σ ∈ ⁅H0g W, H0g W⁆, Cg n ((mat W σ - 1).det * ht W y z u σ) 0 := by
  first | exact @GlobalTheory.Ord2.ht_vanish_commutator | exact GlobalTheory.Ord2.ht_vanish_commutator | (intros; apply GlobalTheory.Ord2.ht_vanish_commutator <;> assumption)
end
