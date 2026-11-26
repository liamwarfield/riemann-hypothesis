module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostDualTraceDataCyclotomicAlgebra

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainEqDlogExplicitReciprocity
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AnnihilatorKaehlerDerivationPrimitiveRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsZetaDerivationInertiaCyclotomicAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicDvdOfAevalPrimitiveRootInertiaFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicDvdOfAevalPrimitiveRootInertiaFixed
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne.CycDvd

theorem apply_eq_pow (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (s : G ℚ Ω)
    {t : Ω} (ht : t ^ (l ^ n) = 1) : s t = t ^ ((cycMod ℚ Ω l n s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) t ht
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val.toZModPow n =
      ((cycMod ℚ Ω l n s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) := by
    simp [cycMod, cycZ]
  rw [h2] at h1
  exact h1

theorem exists_Ine_apply_eq (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (n : ℕ) {z μ : Ω} (hz : IsPrimitiveRoot z (l ^ n))
    (hμ : IsPrimitiveRoot μ (l ^ n)) : ∃ s ∈ Ine (F := ℚ) A, s z = μ := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  obtain ⟨i, hi, hcop, rfl⟩ := (hz.isPrimitiveRoot_iff).1 hμ
  obtain ⟨⟨s, hs⟩, hsu⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A hA n (ZMod.unitOfCoprime i hcop)
  refine ⟨s, hs, ?_⟩
  have hsu' : cycMod ℚ Ω l n s = ZMod.unitOfCoprime i hcop := hsu
  rw [apply_eq_pow l Ω n s hz.pow_eq_one, hsu', ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]

theorem cyclotomic_dvd : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ n) → ∀ R : Polynomial (fixA A), Polynomial.aeval z R = 0 → Polynomial.cyclotomic (l ^ n) (fixA A) ∣ R := by
  intro l _ Ω _ _ _ A hO n z hz R hR
  classical
  have hA : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hv, hl⟩ := hO
    have h1 := (hv ((l : ℕ) : 𝓞 ℚ)).2 hl
    simpa using h1
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  let f : fixA A →+* Ω := A.subtype.comp (fixA A).subtype
  have hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  have h0 : Polynomial.eval₂ f (z : Ω) R = 0 := by
    have := Polynomial.hom_eval₂ R (algebraMap (fixA A) A) A.subtype z
    rw [← Polynomial.aeval_def, hR, map_zero] at this
    exact this.symm
  have hroot : ∀ μ ∈ primitiveRoots (l ^ n) Ω, (R.map f).eval μ = 0 := by
    intro μ hμ
    obtain ⟨s, hs, rfl⟩ := exists_Ine_apply_eq l Ω A hA n hz ((mem_primitiveRoots hpos).1 hμ)
    have e := Polynomial.hom_eval₂ R f (s : Ω →+* Ω) (z : Ω)
    have e2 : (s : Ω →+* Ω).comp f = f := RingHom.ext fun a => a.2 s hs
    rw [h0, map_zero, e2] at e
    rw [Polynomial.eval_map]
    exact e.symm
  rw [← Polynomial.map_dvd_map f hf (Polynomial.cyclotomic.monic _ _), Polynomial.map_cyclotomic,
    Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz]
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro a _ b _ hab
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hab).isUnit
  · intro μ hμ
    exact Polynomial.dvd_iff_isRoot.2 (hroot μ hμ)

end GlobalTheory.RecOne.CycDvd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicDvdOfAevalPrimitiveRootInertiaFixedStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_dvd_of_aeval_primitive_root_inertia_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ n) → ∀ R : Polynomial (fixA A), Polynomial.aeval z R = 0 → Polynomial.cyclotomic (l ^ n) (fixA A) ∣ R := by
  first | (exact @GlobalTheory.RecOne.CycDvd.cyclotomic_dvd) | (exact GlobalTheory.RecOne.CycDvd.cyclotomic_dvd) | (intros; apply GlobalTheory.RecOne.CycDvd.cyclotomic_dvd  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsZetaDerivationInertiaCyclotomicAlgebra
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

noncomputable section

namespace GlobalTheory.RecOne.ZetaDer

open Polynomial

section Gen
variable {R S M : Type} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module S M]

theorem exists_der_one (z : S) (μ : M)
    (hwd : ∀ Q : R[X], aeval z Q = 0 → aeval z (derivative Q) • μ = 0) :
    ∃ D : S → M, IsDerOn (Algebra.adjoin R {z}) D ∧ D z = μ := by
  classical
  let e : R[X] → S := fun Q => aeval z Q
  let D : S → M := fun x => aeval z (derivative (Function.invFun e x)) • μ
  have key : ∀ f : R[X], D (aeval z f) = aeval z (derivative f) • μ := by
    intro f
    have h1 : e (Function.invFun e (e f)) = e f := Function.invFun_eq ⟨f, rfl⟩
    have h2 := hwd (Function.invFun e (e f) - f) (by rw [map_sub]; exact sub_eq_zero.2 h1)
    rw [derivative_sub, map_sub, sub_smul, sub_eq_zero] at h2
    exact h2
  have hm : ∀ x ∈ Algebra.adjoin R {z}, ∃ f : R[X], aeval z f = x := by
    intro x hx
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    exact hx
  refine ⟨D, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx y hy
    obtain ⟨f, rfl⟩ := hm x hx
    obtain ⟨g, rfl⟩ := hm y hy
    rw [← map_add (f := _), key, key, key, derivative_add, map_add (f := _), add_smul]
  · intro x hx y hy
    obtain ⟨f, rfl⟩ := hm x hx
    obtain ⟨g, rfl⟩ := hm y hy
    rw [← map_mul, key, key, key, derivative_mul, map_add (f := _), add_smul, map_mul, map_mul, smul_smul, smul_smul,
      add_comm, mul_comm (aeval z (derivative f))]
  · intro a
    have : algebraMap R S a = aeval z (C a) := by simp
    rw [this, key]
    simp
  · have : z = aeval z (X : R[X]) := by simp
    conv_lhs => rw [this]
    rw [key]
    simp

end Gen

variable {Ω : Type} [Field Ω]

theorem frac_smul_mk {A : ValuationSubring Ω} (s : A) (x : Ω) :
    s • (Submodule.Quotient.mk x : FracA A) = Submodule.Quotient.mk ((s : Ω) * x) := by
  rw [← Submodule.Quotient.mk_smul]; rfl

theorem frac_mk_eq_zero {A : ValuationSubring Ω} (s : A) :
    (Submodule.Quotient.mk (s : Ω) : FracA A) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨s, rfl⟩

theorem cyc_rel [CharZero Ω] {p : ℕ} [hp : Fact p.Prime] {A : ValuationSubring Ω} {R : Type} [CommRing R] [Algebra R A]
    (m : ℕ) (z : A) (hz : IsPrimitiveRoot (z : Ω) (p ^ (m + 1))) :
    (aeval z (derivative (cyclotomic (p ^ (m + 1)) R))) •
      (Submodule.Quotient.mk ((z : Ω) * p / (p : Ω) ^ (m + 1)) : FracA A) = 0 := by
  have hp1 : 1 < p := hp.out.one_lt
  have hpos : 0 < p ^ (m + 1) := pow_pos hp.out.pos _
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hzA : IsPrimitiveRoot z (p ^ (m + 1)) :=
    IsPrimitiveRoot.of_map_of_injective (f := A.subtype) hz Subtype.val_injective
  have hξ : IsPrimitiveRoot ((z : Ω) ^ p ^ m) p := by
    have := hz.pow_of_dvd (pow_ne_zero m hp.out.ne_zero) (pow_dvd_pow p (Nat.le_succ m))
    simpa [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos m)] using this
  set gS : A := ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, (z ^ p ^ m) ^ j
  have hgval : (gS : Ω) = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ((z : Ω) ^ p ^ m) ^ j := by
    simp [gS]
  have hg : (gS : Ω) * ((z : Ω) ^ p ^ m - 1) = - p := by
    rw [hgval, Finset.sum_mul]
    simp_rw [geom_sum_mul]
    rw [Finset.sum_sub_distrib, hξ.geom_sum_eq_zero hp1]
    simp
  have hroot : aeval z (cyclotomic (p ^ (m + 1)) R) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hzA.isRoot_cyclotomic hpos
  have hid := congrArg (fun f => aeval z (derivative f))
    (cyclotomic_prime_pow_mul_X_pow_sub_one R p m)
  simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, map_add (f := _), map_mul,
    map_sub, hroot, zero_mul, add_zero, sub_zero] at hid
  rw [frac_smul_mk]
  set F := aeval z (derivative (cyclotomic (p ^ (m + 1)) R))
  have hζ1 : (z : Ω) ^ p ^ (m + 1) = 1 := hz.pow_eq_one
  have hF : (F : Ω) * ((z : Ω) ^ p ^ m - 1) * z = (p : Ω) ^ (m + 1) := by
    have h2 : F * (z ^ p ^ m - 1) = (p : A) ^ (m + 1) * z ^ (p ^ (m + 1) - 1) := by
      simpa [map_natCast] using hid
    have h3 : (F : Ω) * ((z : Ω) ^ p ^ m - 1) = (p : Ω) ^ (m + 1) * (z : Ω) ^ (p ^ (m + 1) - 1) := by
      have := congrArg (A.subtype) h2
      simpa using this
    rw [h3, mul_assoc, pow_sub_one_mul (pow_ne_zero _ hp.out.ne_zero), hζ1, mul_one]
  have hξ1 : (z : Ω) ^ p ^ m - 1 ≠ 0 := sub_ne_zero.2 (hξ.ne_one hp1)
  have key : (F : Ω) * ((z : Ω) * p / (p : Ω) ^ (m + 1)) = ((-gS : A) : Ω) := by
    apply mul_right_cancel₀ hξ1
    push_cast
    rw [neg_mul, hg, neg_neg]
    have hpm : (p : Ω) ^ (m + 1) ≠ 0 := pow_ne_zero _ hp0
    rw [div_eq_mul_inv]
    linear_combination ((p : Ω) * ((p : Ω) ^ (m + 1))⁻¹) * hF + (p : Ω) * mul_inv_cancel₀ hpm
  rw [key, frac_mk_eq_zero]

theorem exists_root_succ [CharZero Ω] [IsAlgClosed Ω] {p : ℕ} [hp : Fact p.Prime] (A : ValuationSubring Ω)
    (n : ℕ) (z : A) (hz : IsPrimitiveRoot (z : Ω) (p ^ n)) :
    ∃ w : A, IsPrimitiveRoot (w : Ω) (p ^ (n + 1)) ∧ w ^ p = z := by
  have hpos : 0 < p ^ (n + 1) := pow_pos hp.out.pos _
  haveI : NeZero (p ^ (n + 1)) := ⟨hpos.ne'⟩
  haveI : NeZero (p ^ n) := ⟨(pow_pos hp.out.pos _).ne'⟩
  haveI : NeZero ((p ^ (n + 1) : ℕ) : Ω) := ⟨by exact_mod_cast hpos.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p ^ (n + 1))
  have h1 : IsPrimitiveRoot (ζ ^ p) (p ^ n) := hζ.pow hpos (by rw [pow_succ'])
  obtain ⟨i, -, hi, hiz⟩ := h1.isPrimitiveRoot_iff.1 hz

  obtain ⟨j, hj, hjz⟩ : ∃ j : ℕ, j.Coprime (p ^ (n + 1)) ∧ (ζ ^ p) ^ j = z := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨1, Nat.coprime_one_left _, ?_⟩
      have a1 : ζ ^ p = 1 := by simpa using h1.pow_eq_one
      have a2 : (z : Ω) = 1 := by simpa using hz.pow_eq_one
      rw [a1, a2, one_pow]
    · refine ⟨i, ?_, hiz⟩
      rw [Nat.coprime_pow_right_iff hn] at hi
      exact hi.pow_right _
  have hw : IsPrimitiveRoot (ζ ^ j) (p ^ (n + 1)) := hζ.pow_of_coprime j hj
  have hmem : ζ ^ j ∈ A := mem_of_pow_mem A hpos.ne' (by rw [hw.pow_eq_one]; exact A.one_mem)
  refine ⟨⟨ζ ^ j, hmem⟩, hw, Subtype.ext ?_⟩
  rw [← hjz]
  show (ζ ^ j) ^ p = _
  rw [← pow_mul, ← pow_mul, mul_comm]

theorem exists_seq [CharZero Ω] [IsAlgClosed Ω] {p : ℕ} [hp : Fact p.Prime] (A : ValuationSubring Ω)
    (N : ℕ) (z : A) (hz : IsPrimitiveRoot (z : Ω) (p ^ N)) :
    ∃ zs : ℕ → A, zs 0 = z ∧ (∀ k, IsPrimitiveRoot (zs k : Ω) (p ^ (N + k))) ∧ ∀ k, zs (k + 1) ^ p = zs k := by
  choose f hf hf' using exists_root_succ (p := p) A
  let s : (k : ℕ) → {w : A // IsPrimitiveRoot (w : Ω) (p ^ (N + k))} := fun k =>
    Nat.rec (motive := fun k => {w : A // IsPrimitiveRoot (w : Ω) (p ^ (N + k))}) ⟨z, hz⟩
      (fun k w => ⟨f (N + k) w.1 w.2, hf (N + k) w.1 w.2⟩) k
  exact ⟨fun k => (s k).1, rfl, fun k => (s k).2, fun k => hf' (N + k) (s k).1 (s k).2⟩

end GlobalTheory.RecOne.ZetaDer

namespace GlobalTheory.RecOne

open ZetaDer Polynomial

theorem zeta_derivation_cyc : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω), OverL l A → ∀ (N : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ N) →
    ∃ D : A → FracA A, IsDerOn (cycAlg l A) D ∧
      D z = Submodule.Quotient.mk ((z : Ω) * (l : Ω) / (l : Ω) ^ N) := by
  intro p hp Ω _ _ hc A hO N z hz
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨zs, hz0, hprim, hpow⟩ := exists_seq A N z hz
  let B : ℕ → Subalgebra (fixA A) A := fun m => Algebra.adjoin (fixA A) {zs (m + 1)}
  have hmem1 : ∀ m, zs (m + 1) ∈ B m := fun m => Algebra.subset_adjoin (Set.mem_singleton _)
  have hmem0 : ∀ m, zs m ∈ B m := fun m => by rw [← hpow m]; exact pow_mem (hmem1 m) _
  have hle1 : ∀ m, B m ≤ B (m + 1) := fun m =>
    Algebra.adjoin_le (Set.singleton_subset_iff.2 (hmem0 (m + 1)))
  have hlev : ∀ m : ℕ, ∃ D : A → FracA A, IsDerOn (B m) D ∧
      D (zs (m + 1)) = Submodule.Quotient.mk ((zs (m + 1) : Ω) * p / (p : Ω) ^ (N + m + 1)) := by
    intro m
    refine exists_der_one (zs (m + 1)) _ fun Q hQ => ?_
    obtain ⟨R, rfl⟩ := GlobalTheory.T.cyclotomic_dvd_of_aeval_primitive_root_inertia_fixed p Ω A hO (N + m + 1) (zs (m + 1)) (hprim (m + 1)) Q hQ
    have hzA : IsPrimitiveRoot (zs (m + 1)) (p ^ (N + m + 1)) :=
      IsPrimitiveRoot.of_map_of_injective (f := A.subtype) (hprim (m + 1)) Subtype.val_injective
    have hroot : aeval (zs (m + 1)) (cyclotomic (p ^ (N + m + 1)) (fixA A)) = 0 := by
      rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
      exact hzA.isRoot_cyclotomic (pow_pos hp.out.pos _)
    rw [derivative_mul, map_add (f := _), map_mul, map_mul, hroot, zero_mul, add_zero, mul_comm, mul_smul,
      cyc_rel (N + m) (zs (m + 1)) (hprim (m + 1)), smul_zero]
  choose D hD hDz using hlev
  have hval : ∀ m, D m (zs m) = Submodule.Quotient.mk ((zs m : Ω) * p / (p : Ω) ^ (N + m)) := by
    intro m
    have hc1 : ((zs m : A) : Ω) = (zs (m + 1) : Ω) ^ p := by rw [← hpow m]; rfl
    rw [hc1]
    conv_lhs => rw [← hpow m]
    rw [(hD m).pow_der (hmem1 m) hp.out.pos, hDz m, ZetaDer.frac_smul_mk]
    congr 1
    push_cast
    rw [← pow_sub_one_mul hp.out.ne_zero (zs (m + 1) : Ω)]
    field_simp
    ring
  have hcompat : ∀ m, ∀ x ∈ B m, D (m + 1) x = D m x := by
    intro m
    refine IsDerOn.eq_on_adjoin (s := {zs (m + 1)}) ((hD (m + 1)).mono' (hle1 m)) (hD m) ?_
    intro x hx
    rw [Set.mem_singleton_iff.1 hx, hval (m + 1), hDz m]
    rfl
  have hmono : Monotone B := monotone_nat_of_le_succ hle1
  obtain ⟨D', hD', hD'eq⟩ := isDerOn_iSup_glue (fixA A) A (FracA A) B hmono D hD hcompat
  have hle : cycAlg p A ≤ ⨆ m, B m := by
    refine Algebra.adjoin_le ?_
    rintro x ⟨n, hx⟩
    haveI : NeZero (p ^ (N + n)) := ⟨(pow_pos hp.out.pos _).ne'⟩
    have hzA : IsPrimitiveRoot (zs n) (p ^ (N + n)) :=
      IsPrimitiveRoot.of_map_of_injective (f := A.subtype) (hprim n) Subtype.val_injective
    obtain ⟨i, -, rfl⟩ := hzA.eq_pow_of_pow_eq_one (ξ := x) (by rw [pow_add, mul_comm, pow_mul, hx, one_pow])
    exact (le_iSup B n) (pow_mem (hmem0 n) i)
  refine ⟨D', hD'.mono' hle, ?_⟩
  rw [← hz0, hD'eq 0 _ (hmem0 0), hval 0]
  rfl

end GlobalTheory.RecOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsZetaDerivationInertiaCyclotomicAlgebraStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zeta_derivation_inertia_cyclotomic_algebra : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (N : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ N) → ∃ D : A → FracA A, IsDerOn (cycAlg l A) D ∧ D z = Submodule.Quotient.mk ((z : Ω) * (l : Ω) / (l : Ω) ^ N) := by
  first | (exact @GlobalTheory.RecOne.zeta_derivation_cyc) | (exact GlobalTheory.RecOne.zeta_derivation_cyc) | (intros; apply GlobalTheory.RecOne.zeta_derivation_cyc  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AnnihilatorKaehlerDerivationPrimitiveRoot
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

theorem pow_four_mul_mem_of_smul_dA_eq_zero : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (N : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ N) → ∀ a : A, a • dA A z = 0 → ∃ w ∈ A, (l : Ω) ^ 4 * (a : Ω) = (l : Ω) ^ N * w := by
  intro l _ hl2 Ω _ _ _ A hA N z hz a hrel
  have hlΩ : (l : Ω) ≠ 0 := by
    haveI : CharZero Ω := algebraRat.charZero Ω
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hpos : 0 < l ^ N := pow_pos (Fact.out : l.Prime).pos N
  have hz1 : (z : Ω) ^ (l ^ N) = 1 := hz.pow_eq_one
  have hzA : z ^ (l ^ N) = 1 := Subtype.ext (by simpa using hz1)
  have hzT : z ∈ cycAlg l A := mem_cycAlg_of_pow hzA
  have hrel' : ∑ i : Fin 1, (fun _ => a) i •
      KaehlerDifferential.D (fixA A) A ((fun _ => z) i) = 0 := by
    simpa using hrel
  obtain ⟨F, hF⟩ := kaehler_rel_local (fixA A) A 1 _ _ hrel'
  obtain ⟨C, tr, m, α, β, hFC, htr⟩ := GlobalTheory.T.exists_almostDualTraceData_cyclotomicAlgebra l hl2 Ω A hA F
  obtain ⟨D, hD, hDv⟩ := GlobalTheory.T.exists_zeta_derivation_inertia_cyclotomic_algebra l Ω A hA N z hz
  obtain ⟨D', hD', hD'v⟩ := exists_derOn_ext (fixA A) A (FracA A) (cycAlg l A) C tr m α β _ htr D hD
  have h := hF C hFC (fun _ => htr.le hzT) (FracA A) D' hD'
  rw [Fin.sum_univ_one, hD'v _ hzT, hDv, smul_smul, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨t, ht⟩ := h
  have ht' : (t : Ω) = (a : Ω) * (l : Ω) ^ 3 * ((z : Ω) * (l : Ω) / (l : Ω) ^ N) := by
    simpa [Algebra.smul_def] using ht
  refine ⟨((t * z ^ (l ^ N - 1) : A) : Ω), (t * z ^ (l ^ N - 1)).2, ?_⟩
  have hzz : (z : Ω) * (z : Ω) ^ (l ^ N - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hpos, hz1]
  push_cast
  rw [ht']
  field_simp
  linear_combination (-((a : Ω))) * hzz

end GlobalTheory.RecOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AnnihilatorKaehlerDerivationPrimitiveRootStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilator_kaehlerDerivation_primitiveRoot : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (N : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ N) → ∀ a : A, a • dA A z = 0 → ∃ w ∈ A, (l : Ω) ^ 4 * (a : Ω) = (l : Ω) ^ N * w := by
  first | exact @GlobalTheory.RecOne.pow_four_mul_mem_of_smul_dA_eq_zero | exact GlobalTheory.RecOne.pow_four_mul_mem_of_smul_dA_eq_zero | (intros; apply GlobalTheory.RecOne.pow_four_mul_mem_of_smul_dA_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SqPrimeSmulKaehlerDerivationEqSmulRootOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SqPrimeSmulKaehlerDerivationEqSmulRootOfUnity
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

section Gen

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def evMul (l : ℕ) (A : ValuationSubring Ω) : Submodule A (KaehlerDifferential (fixA A) A) where
  carrier := {ω | ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ z : A, IsPrimitiveRoot (z : Ω) (l ^ N) →
    ω ∈ Submodule.span A {dA A z}}
  add_mem' := by
    rintro a b ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    exact ⟨max N₁ N₂, fun N hN z hz =>
      add_mem (h₁ N (le_trans (le_max_left _ _) hN) z hz) (h₂ N (le_trans (le_max_right _ _) hN) z hz)⟩
  zero_mem' := ⟨0, fun _ _ _ _ => zero_mem _⟩
  smul_mem' := by
    rintro c a ⟨N₁, h₁⟩
    exact ⟨N₁, fun N hN z hz => Submodule.smul_mem _ c (h₁ N hN z hz)⟩

theorem dA_mem_evMul (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) {x : A} {n : ℕ}
    (hx : x ^ (l ^ n) = 1) : dA A x ∈ evMul l A := by
  refine ⟨n, fun N hN z hz => ?_⟩
  have : NeZero (l ^ N) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h1 : (x : Ω) ^ (l ^ N) = 1 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
    have h0 : (x : Ω) ^ (l ^ n) = 1 := by
      have := congrArg (fun t : A => (t : Ω)) hx
      simpa using this
    rw [pow_add, pow_mul, h0, one_pow]
  obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one h1
  have h2 : x = z ^ i := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hi]
  rw [h2, Derivation.leibniz_pow]
  exact Submodule.smul_of_tower_mem _ _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

end Gen

theorem l_sq_smul_dA_eq_smul : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ v : A, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ z : A, IsPrimitiveRoot (z : Ω) (l ^ N) → ∃ y : A, ((l : A) ^ 2) • dA A v = y • dA A z := by
  intro l _ hl2 Ω _ _ _ A hA v
  have hder : ∀ B : Subalgebra (fixA A) A, IsDerOn B (fun x => dA A x) := fun B =>
    ⟨fun x _ y _ => map_add (dA A) x y, fun x _ y _ => Derivation.leibniz (dA A) x y,
      fun a => (dA A).map_algebraMap a⟩
  obtain ⟨C, tr, k, a, b, hF, htr⟩ := GlobalTheory.T.exists_almostDualTraceData_cyclotomicAlgebra l hl2 Ω A hA {v}
  have h1 := GlobalTheory.AlmostEt.derOn_mem_span_of_trData (fixA A) A _ (cycAlg l A) C tr k a b _ htr
    (fun x => dA A x) (hder C) v (hF (by simp))
  have h2 : Submodule.span A ((fun x => dA A x) '' (cycAlg l A : Set A)) ≤ evMul l A := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h3 := GlobalTheory.AlmostEt.derOn_adjoin_mem_span (fixA A) A _ {z : A | ∃ n : ℕ, z ^ (l ^ n) = 1}
      (fun x => dA A x) (hder _) x hx
    refine Submodule.span_le.2 ?_ h3
    rintro _ ⟨y, ⟨n, hn⟩, rfl⟩
    exact dA_mem_evMul l A hn
  obtain ⟨N₀, h⟩ := h2 h1
  refine ⟨N₀, fun N hN z hz => ?_⟩
  obtain ⟨y, hy⟩ := Submodule.mem_span_singleton.1 (h N hN z hz)
  exact ⟨y, by rw [pow_two]; exact hy.symm⟩

end GlobalTheory.RecOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SqPrimeSmulKaehlerDerivationEqSmulRootOfUnityStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_prime_smul_kaehlerDerivation_eq_smul_rootOfUnity : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ v : A, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ z : A, IsPrimitiveRoot (z : Ω) (l ^ N) → ∃ y : A, ((l : A) ^ 2) • dA A v = y • dA A z := by
  first | exact @GlobalTheory.RecOne.l_sq_smul_dA_eq_smul | exact GlobalTheory.RecOne.l_sq_smul_dA_eq_smul | (intros; apply GlobalTheory.RecOne.l_sq_smul_dA_eq_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTransportsKaehlerRelationsOverInvariants
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTransportsKaehlerRelationsOverInvariants
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

noncomputable section

namespace GlobalTheory.RecOne

def decRingHom {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (s : G ℚ Ω)
    (hs : s ∈ Dec (F := ℚ) A) : A →+* A where
  toFun x := ⟨s x, (apply_mem_iff_of_mem_Dec hs (x : Ω)).2 x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

def TwDiff {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (_τ : A →+* A) : Type :=
  KaehlerDifferential (fixA A) A

instance {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (τ : A →+* A) :
    AddCommGroup (TwDiff A τ) :=
  inferInstanceAs (AddCommGroup (KaehlerDifferential (fixA A) A))

instance {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (τ : A →+* A) :
    Module A (TwDiff A τ) :=
  Module.compHom (KaehlerDifferential (fixA A) A) τ

theorem transp_rel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (s : G ℚ Ω),
    s ∈ Ine (F := ℚ) A → ∀ a b a' b' c d c' d' : A, (c : Ω) = s a → (d : Ω) = s b →
    (c' : Ω) = s a' → (d' : Ω) = s b' → a • dA A b = a' • dA A b' → c • dA A d = c' • dA A d' := by
  intro Ω _ _ A s hs a b a' b' c d c' d' hc hd hc' hd' h
  set τ := decRingHom A s (Ine_le_Dec A hs) with hτ
  have hτc : τ a = c := Subtype.ext hc.symm
  have hτd : τ b = d := Subtype.ext hd.symm
  have hτc' : τ a' = c' := Subtype.ext hc'.symm
  have hτd' : τ b' = d' := Subtype.ext hd'.symm
  obtain ⟨T, hT⟩ := kaehler_rel_local (fixA A) A 2 ![a, -a'] ![b, b']
    (by simp [Fin.sum_univ_two, h])
  let D : A → TwDiff A τ := fun x => (dA A (τ x) : KaehlerDifferential (fixA A) A)
  have hD : IsDerOn (⊤ : Subalgebra (fixA A) A) D :=
    { add := fun x _ y _ => by
        show dA A (τ (x + y)) = dA A (τ x) + dA A (τ y)
        rw [map_add (f := _), map_add (f := _)]
      mul := fun x _ y _ => by
        show dA A (τ (x * y)) = τ x • dA A (τ y) + τ y • dA A (τ x)
        rw [map_mul, Derivation.leibniz]
      alg := fun r => by
        show dA A (τ (algebraMap (fixA A) A r)) = 0
        have e : τ (algebraMap (fixA A) A r) = algebraMap (fixA A) A r :=
          Subtype.ext (r.2 s hs)
        rw [e, Derivation.map_algebraMap] }
  have key := hT ⊤ (by simp) (by simp) (TwDiff A τ) D hD
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at key
  change τ a • dA A (τ b) + τ (-a') • dA A (τ b') = (0 : KaehlerDifferential (fixA A) A) at key
  rw [map_neg, hτc, hτd, hτc', hτd', neg_smul, ← sub_eq_add_neg, sub_eq_zero] at key
  exact key

end GlobalTheory.RecOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTransportsKaehlerRelationsOverInvariantsStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_transports_kaehler_relations_over_invariants : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (s : G ℚ Ω), s ∈ Ine (F := ℚ) A → ∀ a b a' b' c d c' d' : A, (c : Ω) = s a → (d : Ω) = s b → (c' : Ω) = s a' → (d' : Ω) = s b' → a • dA A b = a' • dA A b' → c • dA A d = c' • dA A d' := by
  first | (exact @GlobalTheory.RecOne.transp_rel) | (exact GlobalTheory.RecOne.transp_rel) | (intros; apply GlobalTheory.RecOne.transp_rel  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainEqDlogExplicitReciprocity
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.RecOne

section Der

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [Module S M]

theorem smul_der_pow (d : Derivation R S M) (x : S) (n : ℕ) : x • d (x ^ n) = ((n : S) * x ^ n) • d x := by
  rcases n with _ | n
  · simp
  · rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S, smul_smul, smul_smul]
    congr 1
    rw [Nat.add_sub_cancel]; ring

theorem rel_one (d : Derivation R S M) (e V Z p y : S) (L n : ℕ) (h1 : e • d V = y • d Z)
    (h2 : d (V ^ L) = p • d (Z ^ n)) :
    ((L : S) * V ^ L * Z * y - e * V * p * n * Z ^ n) • d Z = 0 := by
  have a1 := smul_der_pow d V L
  have a2 := smul_der_pow d Z n
  linear_combination (norm := module) (-((L : S) * V ^ L * Z)) • h1 - (e * Z) • a1 + (e * Z * V) • h2 +
    (e * V * p) • a2

theorem rel_two (d : Derivation R S M) (e V Z y y' : S) (n k c : ℕ) (h1 : e • d V = y • d Z)
    (h2 : e • d ((Z ^ n) ^ k * V) = y' • d (Z ^ c)) :
    (y' * c * Z ^ c - Z * (Z ^ n) ^ k * y - e * V * k * n * (Z ^ n) ^ k) • d Z = 0 := by
  have a1 := smul_der_pow d Z c
  have a2 := smul_der_pow d Z (n * k)
  rw [pow_mul, Nat.cast_mul] at a2
  rw [Derivation.leibniz] at h2
  linear_combination (norm := module) (Z * (Z ^ n) ^ k) • h1 - y' • a1 - Z • h2 + (e * V) • a2

end Der

theorem field_step {F : Type*} [Field F] (l L α u V Z ζ K p y y' Z' w w' w₂ k t c e : F) (hL : L ≠ 0) (hα : α ≠ 0)
    (hu : u ≠ 0) (hV : V ≠ 0) (hK : K ≠ 0)
    (h1 : l ^ 4 * (L * u * Z * y - l ^ 2 * V * p * (α * L) * ζ) = α * L * L * w)
    (h1' : l ^ 4 * (L * u * Z' * y' - l ^ 2 * (K * V) * p * (α * L) * ζ) = α * L * L * w')
    (h2 : l ^ 4 * (y' * c * Z' - Z * K * y - l ^ 2 * V * k * (α * L) * K) = α * L * L * w₂)
    (hc : c = 1 + t * L + e * L * L) :
    l ^ 6 * k - (l ^ 6 * (t * (ζ * p / u)) + (w' * u⁻¹ * (K * V)⁻¹ - w * u⁻¹ * V⁻¹)) =
      L * (l ^ 6 * e * (ζ * p * u⁻¹) + (t + e * L) * (w' * u⁻¹ * (K⁻¹ * V⁻¹)) - w₂ * (K⁻¹ * V⁻¹)) := by
  have h3 : (α * L * L) * (l ^ 6 * k * u * K * V - l ^ 6 * t * ζ * p * K * V - w' + w * K) =
      (α * L * L) * (L * (l ^ 6 * e * ζ * p * K * V + (t + e * L) * w' - w₂ * u)) := by
    subst hc
    linear_combination (-(L * u)) * h2 + (1 + t * L + e * L * L) * h1' - K * h1
  have h4 := mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hα hL) hL) h3
  field_simp
  linear_combination h4

theorem kummer_eq_dlog_one : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (m : ℕ) (ζ ζ' : Ω), IsPrimitiveRoot ζ (l ^ m) → ζ' ^ (l ^ m) = ζ →
  ∀ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) → P.eval ζ ∈ A → (P.eval ζ)⁻¹ ∈ A → P.eval ζ ≠ 0 →
  ∃ x ∈ A, ∀ s, s ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m s = 1 → ∀ k t : ZMod (l ^ m),
    GlobalTheory.Col.KumVal m ζ (P.eval ζ) s k → s ζ' = ζ ^ t.val * ζ' →
    GlobalTheory.Glue.CgA A l m ((l : Ω) ^ c * (k.val : Ω))
      ((l : Ω) ^ c * ((t.val : Ω) * (ζ * (Polynomial.derivative P).eval ζ / P.eval ζ)) + (s x - x)) := by
  intro l hl hl2
  refine ⟨6, ?_⟩
  intro Ω _ _ _ A hA m ζ ζ' hζ hζ' P hP hu hu' hu0
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hlp : l.Prime := Fact.out
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  have hpos : ∀ j : ℕ, 0 < l ^ j := fun j => pow_pos hlp.pos j
  haveI : ∀ j : ℕ, NeZero (l ^ j) := fun j => ⟨(hpos j).ne'⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, A.zero_mem, fun s _ _ k t _ _ => ⟨0, A.zero_mem, ?_⟩⟩
    have hk : k.val = 0 := by have := ZMod.val_lt k; simpa using this
    have ht : t.val = 0 := by have := ZMod.val_lt t; simpa using this
    rw [hk, ht]; simp
  set φ : fixA A →+* Ω := A.subtype.comp (fixA A).subtype with hφ
  obtain ⟨Q, rfl⟩ : ∃ Q : Polynomial (fixA A), Q.map φ = P := by
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases h0 : P.coeff n = 0
    · exact ⟨0, by simp [h0]⟩
    · obtain ⟨h1, h2⟩ := hP _ (Polynomial.coeff_mem_coeffs h0)
      exact ⟨⟨⟨P.coeff n, h1⟩, h2⟩, rfl⟩
  have hev : ∀ (R : Polynomial (fixA A)) (x : A), ((Polynomial.aeval x R : A) : Ω) = (R.map φ).eval (x : Ω) := by
    intro R x
    rw [Polynomial.eval_map, Polynomial.aeval_def]
    exact Polynomial.hom_eval₂ R (algebraMap (fixA A) A) A.subtype x
  have hsev : ∀ s ∈ Ine (F := ℚ) A, ∀ (R : Polynomial (fixA A)) (x : Ω),
      s ((R.map φ).eval x) = (R.map φ).eval (s x) := by
    intro s hs R x
    rw [Polynomial.eval_map, Polynomial.eval_map]
    have h := Polynomial.hom_eval₂ R φ (s : Ω →+* Ω) x
    have e : (s : Ω →+* Ω).comp φ = φ := RingHom.ext fun a => a.2 s hs
    rw [e] at h
    exact h
  rw [Polynomial.derivative_map]
  set u := (Q.map φ).eval ζ with hudef
  set p := ((Polynomial.derivative Q).map φ).eval ζ with hpdef
  obtain ⟨V, hV⟩ := IsAlgClosed.exists_pow_nat_eq u (hpos m)
  have hV0 : V ≠ 0 := by
    rintro rfl
    exact hu0 (by rw [← hV, zero_pow (hpos m).ne'])
  have hVA : V ∈ A := mem_of_pow_mem A (hpos m).ne' (hV ▸ hu)
  have hVA' : V⁻¹ ∈ A := mem_of_pow_mem A (hpos m).ne' (by rw [inv_pow, hV]; exact hu')
  obtain ⟨α, hα⟩ := GlobalTheory.T.sq_prime_smul_kaehlerDerivation_eq_smul_rootOfUnity l hl2 Ω A hA ⟨V, hVA⟩
  obtain ⟨Z, hZ⟩ := IsAlgClosed.exists_pow_nat_eq ζ' (hpos α)
  have hZζ : Z ^ l ^ (α + m) = ζ := by rw [pow_add, pow_mul, hZ, hζ']
  have hZp : IsPrimitiveRoot Z (l ^ (α + m + m)) := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h1 : ¬ Z ^ l ^ (α + (m' + 1) + m') = 1 := by
      rw [pow_add, pow_mul, hZζ]
      exact hζ.pow_ne_one_of_pos_of_lt (hpos m').ne' (Nat.pow_lt_pow_right hlp.one_lt (by omega))
    have h2 : Z ^ l ^ (α + (m' + 1) + m' + 1) = 1 := by
      rw [add_assoc (α + (m' + 1)), pow_add, pow_mul, hZζ, hζ.pow_eq_one]
    have h3 := orderOf_eq_prime_pow h1 h2
    have h4 := IsPrimitiveRoot.orderOf Z
    rwa [h3] at h4
  have hZA : Z ∈ A := mem_of_pow_mem A (hpos (α + m + m)).ne' (by rw [hZp.pow_eq_one]; exact A.one_mem)
  have hζA : ζ ∈ A := hZζ ▸ pow_mem hZA _
  have hζA' : ζ⁻¹ ∈ A := mem_of_pow_mem A (hpos m).ne' (by rw [inv_pow, hζ.pow_eq_one, inv_one]; exact A.one_mem)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (hpos m).ne'
  set VA : A := ⟨V, hVA⟩
  set ZA : A := ⟨Z, hZA⟩
  obtain ⟨y, hy⟩ := hα (α + m + m) (by omega) ZA hZp
  have hZAζ : ((ZA ^ l ^ (α + m) : A) : Ω) = ζ := by simpa using hZζ
  set pA : A := Polynomial.aeval (ZA ^ l ^ (α + m)) (Polynomial.derivative Q) with hpA
  have hpAp : (pA : Ω) = p := by rw [hpA, hev, hZAζ]
  have hpmem : p ∈ A := hpAp ▸ pA.2
  have hVu : VA ^ l ^ m = Polynomial.aeval (ZA ^ l ^ (α + m)) Q := by
    apply Subtype.ext
    rw [hev, hZAζ]
    simpa using hV
  have hd : dA A (VA ^ l ^ m) = pA • dA A (ZA ^ l ^ (α + m)) := by
    rw [hVu, Derivation.map_aeval]
  obtain ⟨w, hwA, hw⟩ := GlobalTheory.T.annihilator_kaehlerDerivation_primitiveRoot l hl2 Ω A hA _ ZA hZp _ (rel_one (dA A) _ VA ZA pA y _ _ hy hd)
  have hw1 : (l : Ω) ^ 4 * ((l : Ω) ^ m * u * Z * y - (l : Ω) ^ 2 * V * p * ((l : Ω) ^ α * (l : Ω) ^ m) * ζ) =
      (l : Ω) ^ α * (l : Ω) ^ m * (l : Ω) ^ m * w := by
    rw [← hV, ← hpAp, ← hZζ, ← pow_add, ← pow_add, ← hw]
    push_cast
    rfl
  refine ⟨w * u⁻¹ * V⁻¹, mul_mem (mul_mem hwA hu') hVA', ?_⟩
  rintro s hs hcyc k t ⟨v, hv, hsv⟩ hst
  have hsA : ∀ x ∈ A, s x ∈ A := fun x hx => (apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs) x).2 hx
  have hsζ : s ζ = ζ := GlobalTheory.Col.fix_of_cycMod le_rfl hcyc hζ.pow_eq_one
  have hsu : s u = u := by rw [hudef, hsev s hs, hsζ]
  have hsp : s p = p := by rw [hpdef, hsev s hs, hsζ]
  have hsV : s V = ζ ^ k.val * V := by
    have h1 : (v / V) ^ l ^ m = 1 := by rw [div_pow, hv, hV, div_self hu0]
    obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one h1
    have h2 : v = ζ ^ j * V := by rw [hj]; field_simp
    rw [h2, map_mul, map_pow, hsζ] at hsv
    exact mul_left_cancel₀ (pow_ne_zero j hζ0) (by rw [hsv]; ring)
  obtain ⟨c, -, hc⟩ := hZp.eq_pow_of_pow_eq_one (ξ := s Z) (by rw [← map_pow, hZp.pow_eq_one, map_one])
  have htr := GlobalTheory.T.inertia_transports_kaehler_relations_over_invariants Ω A s hs ((l : A) ^ 2) VA y ZA ((l : A) ^ 2) ((ZA ^ l ^ (α + m)) ^ k.val * VA)
    ⟨s y, hsA _ y.2⟩ (ZA ^ c) (by simp) (by push_cast; rw [hZζ]; exact hsV.symm) rfl (by simpa using hc) hy
  obtain ⟨w₂, hw₂A, hw₂⟩ := GlobalTheory.T.annihilator_kaehlerDerivation_primitiveRoot l hl2 Ω A hA _ ZA hZp _ (rel_two (dA A) _ VA ZA y _ _ _ _ hy htr)
  have hw2 : (l : Ω) ^ 4 * (s y * (c : Ω) * s Z - Z * ζ ^ k.val * y -
      (l : Ω) ^ 2 * V * (k.val : Ω) * ((l : Ω) ^ α * (l : Ω) ^ m) * ζ ^ k.val) =
      (l : Ω) ^ α * (l : Ω) ^ m * (l : Ω) ^ m * w₂ := by
    rw [← hc, ← hZζ, ← pow_add, ← pow_add, ← hw₂]
    push_cast
    rfl
  have hw1' := congrArg s hw1
  simp only [map_mul, map_sub, map_pow, map_natCast, hsu, hsp, hsζ, hsV] at hw1'
  obtain ⟨e, he⟩ : ∃ e : ℤ, (c : Ω) = 1 + (t.val : Ω) * (l : Ω) ^ m + (e : Ω) * (l : Ω) ^ m * (l : Ω) ^ m := by
    have h1 : Z ^ (c * l ^ α) = Z ^ (l ^ (α + m) * t.val + l ^ α) := by
      rw [pow_mul, hc, ← map_pow, hZ, hst, pow_add, pow_mul, hZζ, hZ]
    rw [(hZp.isOfFinOrder (hpos _).ne').pow_eq_pow_iff_modEq, ← hZp.eq_orderOf, Nat.modEq_iff_dvd] at h1
    obtain ⟨e, he⟩ := h1
    refine ⟨-e, ?_⟩
    have h2 := congrArg (Int.cast : ℤ → Ω) he
    push_cast at h2
    apply mul_left_cancel₀ (pow_ne_zero α hl0)
    push_cast
    linear_combination -h2
  have hfin := field_step (l : Ω) ((l : Ω) ^ m) ((l : Ω) ^ α) u V Z ζ (ζ ^ k.val) p y (s y) (s Z) w (s w) w₂
    (k.val : Ω) (t.val : Ω) (c : Ω) (e : Ω) (pow_ne_zero _ hl0) (pow_ne_zero _ hl0) hu0 hV0 (pow_ne_zero _ hζ0)
    hw1 hw1' hw2 he
  have hlA : (l : Ω) ∈ A := natCast_mem A l
  have hKV : (ζ ^ k.val)⁻¹ * V⁻¹ ∈ A := mul_mem (by rw [← inv_pow]; exact pow_mem hζA' _) hVA'
  refine ⟨_, ?_, by rw [map_mul, map_mul, map_inv₀, map_inv₀, hsu, hsV]; exact hfin⟩
  refine sub_mem (add_mem (mul_mem (mul_mem (pow_mem hlA _) (intCast_mem A e)) (mul_mem (mul_mem hζA hpmem) hu'))
    (mul_mem (add_mem (natCast_mem A _) (mul_mem (intCast_mem A e) (pow_mem hlA _)))
      (mul_mem (mul_mem (hsA w hwA) hu') hKV))) (mul_mem hw₂A hKV)

end GlobalTheory.RecOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainEqDlogExplicitReciprocityStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCochain_eq_dlog_explicitReciprocity : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (m : ℕ) (ζ ζ' : Ω), IsPrimitiveRoot ζ (l ^ m) → ζ' ^ (l ^ m) = ζ →
  ∀ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) → P.eval ζ ∈ A → (P.eval ζ)⁻¹ ∈ A → P.eval ζ ≠ 0 →
  ∃ x ∈ A, ∀ s, s ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m s = 1 → ∀ k t : ZMod (l ^ m),
    GlobalTheory.Col.KumVal m ζ (P.eval ζ) s k → s ζ' = ζ ^ t.val * ζ' →
    GlobalTheory.Glue.CgA A l m ((l : Ω) ^ c * (k.val : Ω))
      ((l : Ω) ^ c * ((t.val : Ω) * (ζ * (Polynomial.derivative P).eval ζ / P.eval ζ)) + (s x - x)) := by
  first | exact @GlobalTheory.RecOne.kummer_eq_dlog_one | exact GlobalTheory.RecOne.kummer_eq_dlog_one | (intros; apply GlobalTheory.RecOne.kummer_eq_dlog_one <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.RecConj

open Polynomial

theorem apply_root {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {m : ℕ} (s : G ℚ Ω)
    {t : Ω} (ht : t ^ (l ^ m) = 1) : s t = t ^ (cycMod ℚ Ω l m s : ZMod (l ^ m)).val := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := algebraRat.charZero Ω
  exact cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) t ht

theorem nat_cg {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {L a b : ℕ} (h : (a : ZMod L) = (b : ZMod L)) :
    ∃ z ∈ A, (a : Ω) - b = (L : Ω) * z := by
  obtain ⟨q, hq⟩ := Nat.modEq_iff_dvd.1 ((ZMod.natCast_eq_natCast_iff a b L).1 h).symm
  refine ⟨(q : Ω), intCast_mem A q, ?_⟩
  have := congrArg (Int.cast : ℤ → Ω) hq
  push_cast at this
  exact this

def fixSub {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) : Subring Ω where
  carrier := {x | x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x}
  mul_mem' := fun ha hb => ⟨A.mul_mem _ _ ha.1 hb.1, fun s hs => by rw [map_mul, ha.2 s hs, hb.2 s hs]⟩
  one_mem' := ⟨A.one_mem, fun s _ => map_one s⟩
  add_mem' := fun ha hb => ⟨A.add_mem _ _ ha.1 hb.1, fun s hs => by rw [map_add (f := _), ha.2 s hs, hb.2 s hs]⟩
  zero_mem' := ⟨A.zero_mem, fun s _ => map_zero s⟩
  neg_mem' := fun ha => ⟨A.neg_mem _ ha.1, fun s hs => by rw [map_neg, ha.2 s hs]⟩

theorem eval_mem {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (P : Polynomial Ω) (hP : ∀ i, P.coeff i ∈ A) {y : Ω}
    (hy : y ∈ A) : P.eval y ∈ A := by
  rw [eval_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (hP i) (pow_mem hy i)

theorem recip_conj : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (m : ℕ) (ζ ζ' : Ω), IsPrimitiveRoot ζ (l ^ m) → ζ' ^ (l ^ m) = ζ →
  ∀ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) → P.eval ζ ∈ A → (P.eval ζ)⁻¹ ∈ A → P.eval ζ ≠ 0 →
  ∀ (τ : G ℚ Ω) (b : (ZMod (l ^ m))ˣ), τ ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m τ = b⁻¹ →
  ∃ x ∈ A, ζ ^ (b : ZMod (l ^ m)).val * (Polynomial.derivative P).eval (ζ ^ (b : ZMod (l ^ m)).val) / P.eval (ζ ^ (b : ZMod (l ^ m)).val) ∈ A ∧
    ∀ s, s ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m s = 1 → ∀ k t : ZMod (l ^ m),
    GlobalTheory.Col.KumVal m ζ (P.eval ζ) (τ * s * τ⁻¹) k → s ζ' = ζ ^ t.val * ζ' →
    GlobalTheory.Glue.CgA A l m ((l : Ω) ^ c * (k.val : Ω))
      ((l : Ω) ^ c * ((t.val : Ω) * (ζ ^ (b : ZMod (l ^ m)).val * (Polynomial.derivative P).eval (ζ ^ (b : ZMod (l ^ m)).val) / P.eval (ζ ^ (b : ZMod (l ^ m)).val))) + (s x - x)) := by
  intro l _ hl
  obtain ⟨c, hc⟩ := GlobalTheory.T.kummerCochain_eq_dlog_explicitReciprocity l hl
  refine ⟨c, ?_⟩
  intro Ω _ _ _ A hA m ζ ζ' hζ hζ' P hP hPA hPi hP0 τ b hτ hb
  have hpos : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  have : NeZero (l ^ m) := ⟨hpos.ne'⟩
  set n := (b : ZMod (l ^ m)).val with hn
  set N := ((b⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)).val with hN
  have hτi : τ⁻¹ ∈ Ine (F := ℚ) A := inv_mem hτ
  have hτD := Ine_le_Dec A hτi
  have hζ1 : ζ ^ (l ^ m) = 1 := hζ.pow_eq_one
  have hτζ : τ⁻¹ ζ = ζ ^ n := by
    rw [apply_root τ⁻¹ hζ1, map_inv, hb, inv_inv]
  have hco : ∀ i, P.coeff i ∈ fixSub A := by
    intro i
    by_cases h : P.coeff i = 0
    · rw [h]; exact zero_mem _
    · exact hP _ (coeff_mem_coeffs h)
  have hτP : τ⁻¹ (P.eval ζ) = P.eval (ζ ^ n) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eval_eq_sum_range, eval_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hτζ, (hco i).2 _ hτi]
  have hζA : ζ ∈ A := by
    rw [← A.valuation_le_one_iff]
    have h1 : A.valuation ζ ^ (l ^ m) = 1 := by rw [← map_pow, hζ1, map_one]
    exact ((pow_eq_one_iff_of_nonneg zero_le' hpos.ne').1 h1).le
  have hQ1 : P.eval (ζ ^ n) ∈ A := hτP ▸ (apply_mem_iff_of_mem_Dec hτD _).2 hPA
  have hQ2 : (P.eval (ζ ^ n))⁻¹ ∈ A := by
    rw [← hτP, ← map_inv₀]; exact (apply_mem_iff_of_mem_Dec hτD _).2 hPi
  have hQ3 : P.eval (ζ ^ n) ≠ 0 := by
    rw [← hτP]; exact (_root_.map_ne_zero _).2 hP0
  have hg : ζ ^ n * (derivative P).eval (ζ ^ n) / P.eval (ζ ^ n) ∈ A := by
    rw [div_eq_mul_inv]
    refine mul_mem (mul_mem (pow_mem hζA n) (eval_mem A _ (fun i => ?_) (pow_mem hζA n))) hQ2
    rw [coeff_derivative]
    exact mul_mem (hco _).1 (add_mem (natCast_mem A i) (one_mem A))
  have hQe : (P.comp (X ^ n)).eval ζ = P.eval (ζ ^ n) := by simp [eval_comp]
  have hQc : ∀ x ∈ (P.comp (X ^ n)).coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x := by
    obtain ⟨P₀, hP₀⟩ : P ∈ lifts (fixSub A).subtype :=
      (lifts_iff_coeff_lifts P).2 fun i => ⟨⟨_, hco i⟩, rfl⟩
    have e : P.comp (X ^ n) = (P₀.comp (X ^ n)).map (fixSub A).subtype := by
      rw [Polynomial.map_comp, ← hP₀]; simp
    intro x hx
    obtain ⟨i, -, rfl⟩ := mem_coeffs_iff.1 hx
    rw [e, coeff_map]
    exact ((P₀.comp (X ^ n)).coeff i).2
  have hD : ζ * (derivative (P.comp (X ^ n))).eval ζ / (P.comp (X ^ n)).eval ζ
      = (n : Ω) * (ζ ^ n * (derivative P).eval (ζ ^ n) / P.eval (ζ ^ n)) := by
    have e : ζ * ((n : Ω) * ζ ^ (n - 1)) = n * ζ ^ n := by
      rcases n with _ | n
      · simp
      · rw [Nat.add_sub_cancel, pow_succ]; ring
    rw [hQe, derivative_comp, derivative_X_pow, eval_mul, eval_comp, eval_mul, eval_C, eval_pow, eval_pow, eval_X,
      ← mul_assoc, e]
    ring
  obtain ⟨x, hxA, hx⟩ := hc Ω A hA m ζ ζ' hζ hζ' (P.comp (X ^ n)) hQc (hQe ▸ hQ1) (hQe ▸ hQ2) (hQe ▸ hQ3)
  refine ⟨(N : Ω) * x, mul_mem (natCast_mem A N) hxA, hg, ?_⟩
  intro s hs hs1 k t hk ht
  obtain ⟨v, hv, hsv⟩ := hk
  have hk' : GlobalTheory.Col.KumVal m ζ ((P.comp (X ^ n)).eval ζ) s ((b : ZMod (l ^ m)) * k) := by
    refine ⟨τ⁻¹ v, by rw [← map_pow, hv, hτP, hQe], ?_⟩
    have e1 : s (τ⁻¹ v) = τ⁻¹ ((τ * s * τ⁻¹) v) := by
      have e : s * τ⁻¹ = τ⁻¹ * (τ * s * τ⁻¹) := by group
      rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply τ⁻¹, e]
    rw [e1, hsv, map_mul, map_pow, hτζ, ← pow_mul, ZMod.val_mul, ← hn]
    congr 1
    conv_lhs => rw [← Nat.mod_add_div (n * k.val) (l ^ m), pow_add, pow_mul, hζ1, one_pow, mul_one]
  obtain ⟨z, hzA, hz⟩ := hx s hs hs1 _ t hk' ht
  rw [hD] at hz
  obtain ⟨z1, hz1A, hz1⟩ := nat_cg A (L := l ^ m) (a := k.val) (b := N * ((b : ZMod (l ^ m)) * k).val) (by
    push_cast
    rw [hN, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← mul_assoc, Units.inv_mul, one_mul])
  obtain ⟨z2, hz2A, hz2⟩ := nat_cg A (L := l ^ m) (a := N * n) (b := 1) (by
    push_cast
    rw [hN, hn, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, Units.inv_mul])
  push_cast at hz1 hz2
  set g := ζ ^ n * (derivative P).eval (ζ ^ n) / P.eval (ζ ^ n) with hgdef
  refine ⟨(l : Ω) ^ c * z1 + N * z + (l : Ω) ^ c * t.val * g * z2, ?_, ?_⟩
  · exact add_mem (add_mem (mul_mem (pow_mem (natCast_mem A l) c) hz1A) (mul_mem (natCast_mem A N) hzA))
      (mul_mem (mul_mem (mul_mem (pow_mem (natCast_mem A l) c) (natCast_mem A _)) hg) hz2A)
  · rw [map_mul, map_natCast]
    linear_combination (l : Ω) ^ c * hz1 + (N : Ω) * hz + (l : Ω) ^ c * t.val * g * hz2

end GlobalTheory.RecConj
