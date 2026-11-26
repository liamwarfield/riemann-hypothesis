module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorsionLift

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupResidueFieldTateLevelSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomLiftResiduePointFiniteFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomLiftResiduePointFiniteFlat
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.ResiduePointLift

theorem exists_algHom_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O →
    ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A]
    (c : A →ₐ[O] IsLocalRing.ResidueField O), ∃ x : A →ₐ[O] O, ∀ a, IsLocalRing.residue O (x a) = c a := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv A _ _ _ _ c
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI : IsIntegrallyClosed O := hv.isIntegrallyClosed
  obtain ⟨ψ, h1, h2⟩ := GlobalTheory.UT.ExactTerm.exists_ringHom_lift C (c : A →+* IsLocalRing.ResidueField O)
    (RingHom.ext fun o => by simp [IsLocalRing.ResidueField.algebraMap_eq])
  refine ⟨{ ψ with commutes' := fun o => RingHom.congr_fun h1 o }, fun a => RingHom.congr_fun h2 a⟩

end GlobalTheory.ResiduePointLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomLiftResiduePointFiniteFlatStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algHom_lift_residuePoint_finite_flat : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] (c : A →ₐ[O] IsLocalRing.ResidueField O), ∃ x : A →ₐ[O] O, ∀ a, IsLocalRing.residue O (x a) = c a := by
  first | exact @GlobalTheory.ResiduePointLift.exists_algHom_lift | exact GlobalTheory.ResiduePointLift.exists_algHom_lift | (intros; apply GlobalTheory.ResiduePointLift.exists_algHom_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupResidueFieldTateLevelSection
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.TateResidue

open WithConv

theorem conv_eq_one_of_mul {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (G : PDivGroup p O)
    {B : Type} [CommRing B] [Algebra O B] (n : ℕ) (a b : WithConv (G.A n →ₐ[O] B))
    (h : a * b = b) : a = 1 :=
  (IsUnit.of_pow_eq_one (G.pts_pow_self n b)
    (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mul_right_cancel (h.trans (one_mul _).symm)

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, (∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O), ∃ t : G.TateOver (IsLocalRing.ResidueField O), t.pt n = c) ∧ ∃ s : G.TateOver (IsLocalRing.ResidueField O) →ₗ[ℤ_[p]] G.Tate, (∀ t, G.tatePush (Algebra.ofId O (IsLocalRing.ResidueField O)) (s t) = t) ∧ ∀ (n : ℕ) (t t' : G.TateOver (IsLocalRing.ResidueField O)), t.pt n = t'.pt n → (s t).pt n = (s t').pt n := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv G
  have : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h =>
    hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 h)⟩
  set k := IsLocalRing.ResidueField O
  set π := G.tatePush (Algebra.ofId O k)

  have hlift : ∀ (n : ℕ) (c : G.A n →ₐ[O] k), ∃ t : G.Tate, (π t).pt n = c := by
    intro n c
    obtain ⟨x, hx⟩ := GlobalTheory.T.exists_algHom_lift_residuePoint_finite_flat p C v O hv (G.A n) c
    obtain ⟨t, ht⟩ := G.pt_surjective C n x
    refine ⟨t, AlgHom.ext fun a => ?_⟩
    rw [tatePush_pt]
    change IsLocalRing.residue O (t.pt n a) = c a
    rw [show t.pt n = x from ht]
    exact hx a
  refine ⟨fun n c => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hlift n c
    exact ⟨π t, ht⟩
  have := G.finite_tate C
  have hπ : Function.Surjective π := by
    refine TateFree.surjective_of_mod π TateOver.eq_zero_of_forall_pow_smul fun y => ?_
    obtain ⟨x, hx⟩ := hlift 1 (y.pt 1)
    obtain ⟨z, hz⟩ := (TateOver.conv_eq_one_iff (y - π x) 1).1 <| by
      have h1 : (y - π x + π x).conv 1 = y.conv 1 := by rw [sub_add_cancel]
      rw [TateOver.add_conv] at h1
      have h2 : (π x).conv 1 = y.conv 1 := congrArg toConv hx
      rw [h2] at h1
      exact conv_eq_one_of_mul G _ _ _ h1
    exact ⟨x, z, by rwa [pow_one] at hz⟩
  have : Module.Finite ℤ_[p] (G.TateOver k) := Module.Finite.of_surjective π hπ
  have : Module.Free ℤ_[p] (G.TateOver k) := inferInstance
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  refine ⟨s, fun t => LinearMap.congr_fun hs t, fun n t t' h => ?_⟩
  have hd : (t - t').conv n = 1 := by
    have h1 : (t - t' + t').conv n = t.conv n := by rw [sub_add_cancel]
    rw [TateOver.add_conv, show t'.conv n = t.conv n from congrArg toConv h.symm] at h1
    exact conv_eq_one_of_mul G _ _ _ h1
  obtain ⟨u, hu⟩ := (TateOver.conv_eq_one_iff (t - t') n).1 hd
  have h3 : (s t - s t').conv n = 1 := by
    rw [← map_sub, ← hu, map_smul]
    exact (TateOver.conv_eq_one_iff _ n).2 ⟨_, rfl⟩
  have h4 : (s t - s t' + s t').conv n = (s t).conv n := by rw [sub_add_cancel]
  rw [TateOver.add_conv, h3, one_mul] at h4
  exact congrArg ofConv h4.symm

end GlobalTheory.TateResidue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupResidueFieldTateLevelSectionStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_residueField_tate_level_section : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, (∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O), ∃ t : G.TateOver (IsLocalRing.ResidueField O), t.pt n = c) ∧ ∃ s : G.TateOver (IsLocalRing.ResidueField O) →ₗ[ℤ_[p]] G.Tate, (∀ t, G.tatePush (Algebra.ofId O (IsLocalRing.ResidueField O)) (s t) = t) ∧ ∀ (n : ℕ) (t t' : G.TateOver (IsLocalRing.ResidueField O)), t.pt n = t'.pt n → (s t).pt n = (s t').pt n := by
  first | exact @GlobalTheory.TateResidue.main | exact GlobalTheory.TateResidue.main | (intros; apply GlobalTheory.TateResidue.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraResiduePointIdempotentsOverOC
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraResiduePointIdempotentsOverOC
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FiniteAlgIdem

open Polynomial

theorem isCoprime_multiset_prod_left {R : Type} [CommRing R] (s : Multiset R) (y : R)
    (h : ∀ x ∈ s, IsCoprime x y) : IsCoprime s.prod y := by
  induction s using Multiset.induction_on with
  | empty => exact isCoprime_one_left
  | cons a s ih =>
    rw [Multiset.prod_cons]
    exact (h a (Multiset.mem_cons_self a s)).mul_left
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

theorem monic_eq_prod_X_sub_C {L : Type} [Field L] [IsAlgClosed L] {v : Valuation L NNReal}
    {O : Type} [CommRing O] [Algebra O L] (hv : v.Integers O) (f : O[X]) (hf : f.Monic) :
    ∃ r : Multiset O, f = (r.map fun x => X - C x).prod := by
  classical
  have hinj : Function.Injective (algebraMap O L) := hv.hom_inj
  have hs : (f.map (algebraMap O L)).Splits := IsAlgClosed.splits _
  have hm : (f.map (algebraMap O L)).Monic := hf.map _
  have hroot : ∀ x ∈ (f.map (algebraMap O L)).roots, ∃ y, algebraMap O L y = x := by
    intro x hx
    have hint : IsIntegral O x := ⟨f, hf, by
      rw [← Polynomial.eval_map]
      exact (Polynomial.mem_roots hm.ne_zero).1 hx⟩
    exact hv.exists_of_le_one ((Valuation.mem_integer_iff _ _).1 (hv.mem_of_integral hint))
  refine ⟨(f.map (algebraMap O L)).roots.map (Function.invFun (algebraMap O L)), ?_⟩
  apply Polynomial.map_injective _ hinj
  conv_lhs => rw [hs.eq_prod_roots_of_monic hm]
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro x hx
  simp [Function.invFun_eq (hroot x hx)]

theorem exists_prod_sub_eq_zero {L : Type} [Field L] [IsAlgClosed L] {v : Valuation L NNReal}
    {O : Type} [CommRing O] [Algebra O L] (hv : v.Integers O) {A : Type} [CommRing A]
    [Algebra O A] [Algebra.IsIntegral O A] (a : A) :
    ∃ r : Multiset O, (r.map fun x => a - algebraMap O A x).prod = 0 := by
  obtain ⟨f, hf, hfa⟩ := Algebra.IsIntegral.isIntegral (R := O) a
  obtain ⟨r, hr⟩ := monic_eq_prod_X_sub_C hv f hf
  refine ⟨r, ?_⟩
  have h : aeval a f = 0 := hfa
  rw [hr, map_multiset_prod, Multiset.map_map] at h
  simpa [Function.comp_def] using h

theorem exists_mem_eq {O : Type} [CommRing O] {A K : Type} [CommRing A] [Algebra O A]
    [CommRing K] [IsDomain K] [Algebra O K] (c : A →ₐ[O] K) {a : A} {r : Multiset O}
    (hr : (r.map fun x => a - algebraMap O A x).prod = 0) :
    ∃ x ∈ r, c a = algebraMap O K x := by
  have h := congrArg c hr
  rw [map_multiset_prod, Multiset.map_map, map_zero, Multiset.prod_eq_zero_iff] at h
  obtain ⟨x, hx, hx0⟩ := Multiset.mem_map.1 h
  refine ⟨x, hx, ?_⟩
  simp only [Function.comp_apply, map_sub, AlgHom.commutes] at hx0
  exact sub_eq_zero.1 hx0


open Classical in
theorem exists_idempotent {O : Type} [CommRing O] [IsLocalRing O] {A : Type} [CommRing A]
    [Algebra O A] {a : A} {r : Multiset O} (hr : (r.map fun x => a - algebraMap O A x).prod = 0)
    (ρ : IsLocalRing.ResidueField O) :
    ∃ e : A, IsIdempotentElem e ∧ ∀ c : A →ₐ[O] IsLocalRing.ResidueField O,
      c e = if c a = ρ then 1 else 0 := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : O[X],
      g = ((r.filter fun x => IsLocalRing.residue O x = ρ).map fun x => X - C x).prod := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : O[X],
      h = ((r.filter fun x => ¬ IsLocalRing.residue O x = ρ).map fun x => X - C x).prod :=
    ⟨_, rfl⟩
  have hgh : g * h = (r.map fun x => X - C x).prod := by
    rw [hg, hh, ← Multiset.prod_add, ← Multiset.map_add (f := _), Multiset.filter_add_not]
  have hcop : IsCoprime g h := by
    rw [hg]
    apply isCoprime_multiset_prod_left
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hp
    rw [hh]
    apply IsCoprime.symm
    apply isCoprime_multiset_prod_left
    intro q hq
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hq
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).1
    rw [map_sub, (Multiset.mem_filter.1 hx).2, sub_ne_zero]
    exact (Multiset.mem_filter.1 hy).2
  obtain ⟨u, w, huw⟩ := hcop
  have hF : aeval a (g * h) = 0 := by
    rw [hgh, map_multiset_prod, Multiset.map_map]
    simpa [Function.comp_def] using hr
  refine ⟨aeval a (w * h), ?_, ?_⟩
  · have key : w * h * (w * h) = w * h - u * w * (g * h) := by
      linear_combination (w * h) * huw
    show aeval a (w * h) * aeval a (w * h) = aeval a (w * h)
    rw [← map_mul, key, map_sub, map_mul (aeval a) (u * w), hF, mul_zero, sub_zero]
  · intro c
    rw [← Polynomial.aeval_algHom_apply]
    obtain ⟨x, hx, hcx⟩ := exists_mem_eq c hr
    rw [IsLocalRing.ResidueField.algebraMap_eq] at hcx
    have h1 := congrArg (aeval (c a)) huw
    rw [map_add (f := _), map_mul, map_mul, map_one] at h1
    by_cases hρ : IsLocalRing.residue O x = ρ
    · have hg0 : aeval (c a) g = 0 := by
        rw [hg, map_multiset_prod, Multiset.map_map]
        apply Multiset.prod_eq_zero
        refine Multiset.mem_map.2 ⟨x, Multiset.mem_filter.2 ⟨hx, hρ⟩, ?_⟩
        simp [hcx]
      rw [if_pos (hcx.trans hρ), map_mul]
      rw [hg0, mul_zero, zero_add] at h1
      exact h1
    · have hh0 : aeval (c a) h = 0 := by
        rw [hh, map_multiset_prod, Multiset.map_map]
        apply Multiset.prod_eq_zero
        refine Multiset.mem_map.2 ⟨x, Multiset.mem_filter.2 ⟨hx, hρ⟩, ?_⟩
        simp [hcx]
      rw [if_neg (show ¬ c a = ρ by rwa [hcx]), map_mul, hh0, mul_zero]

end GlobalTheory.FiniteAlgIdem

namespace GlobalTheory.FiniteAlgIdem

theorem idempotent_eq_zero {L : Type} [Field L] [IsAlgClosed L] {v : Valuation L NNReal}
    {O : Type} [CommRing O] [Algebra O L] [IsLocalRing O] (hv : v.Integers O) {A : Type}
    [CommRing A] [Algebra O A] [Algebra.IsIntegral O A] {s : A} (hs : IsIdempotentElem s)
    (h : ∀ c : A →ₐ[O] IsLocalRing.ResidueField O, c s = 0) : s = 0 := by
  by_contra hne
  have hI : Ideal.span {1 - s} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    apply hne
    have h0 : (1 - s) * s = 0 := by rw [sub_mul, one_mul, hs.eq, sub_self]
    exact hu.mul_right_eq_zero.1 h0
  obtain ⟨M, hM, hsM⟩ := Ideal.exists_le_maximal _ hI
  let ψ : O →ₐ[O] A ⧸ M := Algebra.ofId O (A ⧸ M)
  have hψ : Function.Surjective ψ := by
    intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨r, hr⟩ := exists_prod_sub_eq_zero hv b
    obtain ⟨x, -, hbx⟩ := exists_mem_eq (Ideal.Quotient.mkₐ O M) hr
    exact ⟨x, by rw [Algebra.ofId_apply, ← hbx]; rfl⟩
  have hker : ∀ y ∈ RingHom.ker ψ, (Algebra.ofId O (IsLocalRing.ResidueField O)) y = 0 := by
    intro y hy
    have hne : RingHom.ker ψ ≠ ⊤ := by
      rw [Ne, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]
      exact one_ne_zero
    rw [Algebra.ofId_apply, IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.residue_eq_zero_iff]
    exact IsLocalRing.le_maximalIdeal hne hy
  let c : A →ₐ[O] IsLocalRing.ResidueField O :=
    (Ideal.Quotient.liftₐ (RingHom.ker ψ) (Algebra.ofId O _) hker).comp
      ((Ideal.quotientKerAlgEquivOfSurjective hψ).symm.toAlgHom.comp (Ideal.Quotient.mkₐ O M))
  have hm : Ideal.Quotient.mkₐ O M (1 - s) = 0 := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hsM (Ideal.mem_span_singleton_self _)
  have h1 : c (1 - s) = 0 := by
    simp only [c, AlgHom.comp_apply, hm, map_zero]
  rw [map_sub, map_one, h c, sub_zero] at h1
  exact one_ne_zero h1

theorem finite_and_idempotents {L : Type} [Field L] [IsAlgClosed L] {v : Valuation L NNReal}
    {O : Type} [CommRing O] [Algebra O L] [IsLocalRing O] (hv : v.Integers O) (A : Type)
    [CommRing A] [Algebra O A] [Module.Finite O A] :
    Finite (A →ₐ[O] IsLocalRing.ResidueField O) ∧
      ∃ e : (A →ₐ[O] IsLocalRing.ResidueField O) → A, (∀ c, IsIdempotentElem (e c)) ∧
        (∀ c c', c ≠ c' → e c * e c' = 0) ∧ (∑ᶠ c, e c) = 1 ∧
        ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O, c' (e c) = 1 ↔ c = c' := by
  classical
  haveI : Algebra.IsIntegral O A := Algebra.IsIntegral.of_finite O A
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := O) (M := A)
  choose r hr using fun a : A => exists_prod_sub_eq_zero hv a
  choose E hEi hEc using fun (a : A) (ρ : IsLocalRing.ResidueField O) =>
    exists_idempotent (hr a) ρ
  have hsep : ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O,
      (∀ j ∈ S, c' j = c j) → c' = c := by
    intro c c' hcc
    apply AlgHom.toLinearMap_injective
    exact LinearMap.ext_on hS fun x hx => hcc x hx
  let e : (A →ₐ[O] IsLocalRing.ResidueField O) → A := fun c => ∏ j ∈ S, E j (c j)
  have hec : ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O,
      c' (e c) = if c = c' then 1 else 0 := by
    intro c c'
    simp only [e, map_prod, hEc]
    by_cases hcc : c = c'
    · subst hcc
      rw [if_pos rfl, Finset.prod_boole, if_pos (fun j _ => rfl)]
    · rw [if_neg hcc, Finset.prod_boole, if_neg (fun hh => hcc (hsep c c' hh).symm)]
  have hei : ∀ c, IsIdempotentElem (e c) := fun c =>
    Finset.prod_induction _ IsIdempotentElem (fun _ _ ha hb => ha.mul hb)
      IsIdempotentElem.one (fun j _ => hEi _ _)
  have hort : ∀ c c', c ≠ c' → e c * e c' = 0 := by
    intro c c' hne
    apply idempotent_eq_zero hv ((hei c).mul (hei c'))
    intro c''
    rw [map_mul, hec, hec]
    split_ifs with h1 h2 <;> simp_all
  have hfin : Finite (A →ₐ[O] IsLocalRing.ResidueField O) := by
    let T : S → Finset (IsLocalRing.ResidueField O) := fun j =>
      ((r j).map (algebraMap O (IsLocalRing.ResidueField O))).toFinset
    let F : (A →ₐ[O] IsLocalRing.ResidueField O) → (∀ j : S, T j) := fun c j =>
      ⟨c j, by
        obtain ⟨x, hx, hcx⟩ := exists_mem_eq c (hr j)
        simp only [T, Multiset.mem_toFinset, Multiset.mem_map]
        exact ⟨x, hx, hcx.symm⟩⟩
    refine Finite.of_injective F ?_
    intro c c' hcc
    exact hsep c' c fun j hj => congrArg Subtype.val (congrFun hcc ⟨j, hj⟩)
  refine ⟨hfin, e, hei, hort, ?_, ?_⟩
  · haveI := hfin
    letI := Fintype.ofFinite (A →ₐ[O] IsLocalRing.ResidueField O)
    rw [finsum_eq_sum_of_fintype]
    have horth : OrthogonalIdempotents e := ⟨hei, fun c c' h => hort c c' h⟩
    have hsum := horth.isIdempotentElem_sum (s := Finset.univ)
    have h0 := idempotent_eq_zero hv hsum.one_sub (fun c'' => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_one, map_sum]
      simp [hec])
    exact (sub_eq_zero.1 h0).symm
  · intro c c'
    rw [hec]
    split_ifs with h <;> simp [h]

end GlobalTheory.FiniteAlgIdem

theorem GlobalTheory.FiniteAlgIdem.idempotents_at_residue_points :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O →
    ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A],
    Finite (A →ₐ[O] IsLocalRing.ResidueField O) ∧
    ∃ e : (A →ₐ[O] IsLocalRing.ResidueField O) → A, (∀ c, IsIdempotentElem (e c)) ∧
    (∀ c c', c ≠ c' → e c * e c' = 0) ∧ (∑ᶠ c, e c) = 1 ∧
    ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O, c' (e c) = 1 ↔ c = c' := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv A _ _ _
  exact GlobalTheory.FiniteAlgIdem.finite_and_idempotents hv A
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraResiduePointIdempotentsOverOCStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAlgebra_residuePoint_idempotents_over_OC : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A], Finite (A →ₐ[O] IsLocalRing.ResidueField O) ∧ ∃ e : (A →ₐ[O] IsLocalRing.ResidueField O) → A, (∀ c, IsIdempotentElem (e c)) ∧ (∀ c c', c ≠ c' → e c * e c' = 0) ∧ (∑ᶠ c, e c) = 1 ∧ ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O, c' (e c) = 1 ↔ c = c' := by
  first | exact @GlobalTheory.FiniteAlgIdem.idempotents_at_residue_points | exact GlobalTheory.FiniteAlgIdem.idempotents_at_residue_points | (intros; apply GlobalTheory.FiniteAlgIdem.idempotents_at_residue_points <;> assumption)
end
end

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv

namespace GlobalTheory.ConstPart

open Classical

variable {O : Type} [CommRing O] [IsLocalRing O]

def IdemData (A : Type) [CommRing A] [Algebra O A]
    (e : (A →ₐ[O] IsLocalRing.ResidueField O) → A) : Prop :=
  (∀ c, IsIdempotentElem (e c)) ∧ (∀ c c', c ≠ c' → e c * e c' = 0) ∧ (∑ᶠ c, e c) = 1 ∧
    ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O, c' (e c) = 1 ↔ c = c'

def HasIdem (O : Type) [CommRing O] [IsLocalRing O] : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A],
    Finite (A →ₐ[O] IsLocalRing.ResidueField O) ∧
      ∃ e : (A →ₐ[O] IsLocalRing.ResidueField O) → A, IdemData A e

section Idem

variable {A : Type} [CommRing A] [Algebra O A] {e : (A →ₐ[O] IsLocalRing.ResidueField O) → A}

theorem IdemData.pt (he : IdemData A e) (c c' : A →ₐ[O] IsLocalRing.ResidueField O) :
    c' (e c) = if c = c' then 1 else 0 := by
  split_ifs with h
  · exact (he.2.2.2 c c').2 h
  · rcases IsIdempotentElem.iff_eq_zero_or_one.1 ((he.1 c).map c') with h0 | h1
    · exact h0
    · exact absurd ((he.2.2.2 c c').1 h1) h

theorem IdemData.ptO [IsDomain O] (he : IdemData A e) (c : A →ₐ[O] IsLocalRing.ResidueField O)
    (x : A →ₐ[O] O) :
    x (e c) = if c = (Algebra.ofId O (IsLocalRing.ResidueField O)).comp x then 1 else 0 := by
  have h := he.pt c ((Algebra.ofId O (IsLocalRing.ResidueField O)).comp x)
  rw [AlgHom.comp_apply] at h
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 ((he.1 c).map x) with h0 | h1
  · rw [h0, map_zero] at h
    rw [h0]
    split_ifs at h ⊢ with hc
    · exact absurd h.symm one_ne_zero
    · rfl
  · rw [h1, map_one] at h
    rw [h1]
    split_ifs at h ⊢ with hc
    · rfl
    · exact absurd h one_ne_zero

theorem IdemData.mul_eq (he : IdemData A e) (c c' : A →ₐ[O] IsLocalRing.ResidueField O) :
    e c * e c' = if c = c' then e c else 0 := by
  split_ifs with h
  · subst h; exact (he.1 c).eq
  · exact he.2.1 c c' h

theorem IdemData.sum_eq [Fintype (A →ₐ[O] IsLocalRing.ResidueField O)] (he : IdemData A e) :
    ∑ c, e c = 1 := by
  rw [← finsum_eq_sum_of_fintype]; exact he.2.2.1

end Idem

theorem isIdempotentElem_sum_ite {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (f : ι → R) (hf : ∀ i j, f i * f j = if i = j then f i else 0) (q : ι → Prop)
    [DecidablePred q] : IsIdempotentElem (∑ i, if q i then f i else 0) := by
  unfold IsIdempotentElem
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [ite_mul, mul_ite, mul_zero, zero_mul, hf]
  split_ifs with hi
  · rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    simp [hi]
  · simp

theorem idem_eq_zero (H : HasIdem O) {A : Type} [CommRing A] [Algebra O A] [Module.Finite O A]
    {g : A} (hg : IsIdempotentElem g)
    (h : ∀ c : A →ₐ[O] IsLocalRing.ResidueField O, c g = 0) : g = 0 := by
  set I : Ideal A := Ideal.span {1 - g}
  haveI : Module.Finite O (A ⧸ I) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ O I).toLinearMap (Ideal.Quotient.mkₐ_surjective O I)
  obtain ⟨-, e, -, -, hsum, -⟩ := H (A ⧸ I)
  have hE : IsEmpty ((A ⧸ I) →ₐ[O] IsLocalRing.ResidueField O) := ⟨fun d => by
    have h1 : d (Ideal.Quotient.mk I (1 - g)) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), map_zero]
    have h2 := h (d.comp (Ideal.Quotient.mkₐ O I))
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h2
    rw [map_sub, map_one, map_sub, map_one, h2, sub_zero] at h1
    exact one_ne_zero h1⟩
  rw [finsum_of_isEmpty] at hsum
  have h1 : (1 : A) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_one]; exact hsum.symm
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h1
  calc g = b * (1 - g) * g := by rw [hb, one_mul]
    _ = b * (g - g * g) := by ring
    _ = 0 := by rw [hg.eq, sub_self, mul_zero]

theorem idem_eq (H : HasIdem O) {A : Type} [CommRing A] [Algebra O A] [Module.Finite O A]
    {f g : A} (hf : IsIdempotentElem f) (hg : IsIdempotentElem g)
    (h : ∀ c : A →ₐ[O] IsLocalRing.ResidueField O, c f = c g) : f = g := by
  have key : ∀ a b : A, IsIdempotentElem a → IsIdempotentElem b →
      (∀ c : A →ₐ[O] IsLocalRing.ResidueField O, c a = c b) → a * (1 - b) = 0 := by
    intro a b ha hb hab
    refine idem_eq_zero H (ha.mul hb.one_sub) fun c => ?_
    rw [map_mul, map_sub, map_one, hab c, mul_sub, mul_one, (hb.map c).eq, sub_self]
  have h1 := key f g hf hg h
  have h2 := key g f hg hf fun c => (h c).symm
  calc f = f * g := by rw [mul_sub, mul_one, sub_eq_zero] at h1; exact h1
    _ = g * f := mul_comm _ _
    _ = g := by rw [mul_sub, mul_one, sub_eq_zero] at h2; exact h2.symm

section Sum

variable {A : Type} [CommRing A] [Algebra O A] {e : (A →ₐ[O] IsLocalRing.ResidueField O) → A}
  [Fintype (A →ₐ[O] IsLocalRing.ResidueField O)]

def sumE (he : IdemData A e) : ((A →ₐ[O] IsLocalRing.ResidueField O) → O) →ₐ[O] A where
  toFun f := ∑ c, f c • e c
  map_one' := by simp only [Pi.one_apply, one_smul]; exact he.sum_eq
  map_mul' f g := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp_rw [smul_mul_smul_comm, he.mul_eq, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq]
    simp [Pi.mul_apply]
  map_zero' := by simp
  map_add' f g := by simp [add_smul, Finset.sum_add_distrib]
  commutes' r := by
    simp only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← Finset.smul_sum, he.sum_eq, Algebra.algebraMap_eq_smul_one]

theorem sumE_apply (he : IdemData A e) (f : (A →ₐ[O] IsLocalRing.ResidueField O) → O) :
    sumE he f = ∑ c, f c • e c := rfl

end Sum

theorem push_e (H : HasIdem O) {A A' : Type} [CommRing A] [Algebra O A] [CommRing A']
    [Algebra O A'] [Module.Finite O A'] [Fintype (A' →ₐ[O] IsLocalRing.ResidueField O)]
    {e : (A →ₐ[O] IsLocalRing.ResidueField O) → A} {e' : (A' →ₐ[O] IsLocalRing.ResidueField O) → A'}
    (he : IdemData A e) (he' : IdemData A' e') (φ : A →ₐ[O] A')
    (c : A →ₐ[O] IsLocalRing.ResidueField O) :
    φ (e c) = ∑ c', if c'.comp φ = c then e' c' else 0 := by
  refine idem_eq H ((he.1 c).map φ) (isIdempotentElem_sum_ite e' he'.mul_eq _) fun d => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← AlgHom.comp_apply, he.pt, map_sum]
  simp_rw [apply_ite d, map_zero, he'.pt]
  rw [Finset.sum_eq_single d (fun b _ hb => by simp [hb]) (by simp)]
  simp [eq_comm]

theorem comul_e (H : HasIdem O) {A : Type} [CommRing A] [Bialgebra O A] [Module.Finite O A]
    [Fintype (A →ₐ[O] IsLocalRing.ResidueField O)]
    {e : (A →ₐ[O] IsLocalRing.ResidueField O) → A} (he : IdemData A e)
    (c : A →ₐ[O] IsLocalRing.ResidueField O) :
    comul (R := O) (e c) = ∑ x : (A →ₐ[O] IsLocalRing.ResidueField O) ×
      (A →ₐ[O] IsLocalRing.ResidueField O),
      if ofConv (toConv x.1 * toConv x.2) = c then e x.1 ⊗ₜ[O] e x.2 else 0 := by
  have horth : ∀ x y : (A →ₐ[O] IsLocalRing.ResidueField O) × (A →ₐ[O] IsLocalRing.ResidueField O),
      (e x.1 ⊗ₜ[O] e x.2) * (e y.1 ⊗ₜ[O] e y.2) = if x = y then e x.1 ⊗ₜ[O] e x.2 else 0 := by
    intro x y
    rw [Algebra.TensorProduct.tmul_mul_tmul, he.mul_eq, he.mul_eq]
    by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;> simp [h1, h2, Prod.ext_iff]
  have hc : comul (R := O) (e c) = comulAlgHom O A (e c) := rfl
  rw [hc]
  refine idem_eq H ((he.1 c).map _) (isIdempotentElem_sum_ite _ horth _) fun d => ?_
  set d₁ : A →ₐ[O] IsLocalRing.ResidueField O := d.comp Algebra.TensorProduct.includeLeft
  set d₂ : A →ₐ[O] IsLocalRing.ResidueField O := d.comp Algebra.TensorProduct.includeRight
  have hd : Algebra.TensorProduct.lift d₁ d₂ (fun _ _ => .all _ _) = d :=
    Algebra.TensorProduct.ext' fun a b => by
      rw [Algebra.TensorProduct.lift_tmul]
      simp only [d₁, d₂, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul]
  have hdt : ∀ a b : A, d (a ⊗ₜ[O] b) = d₁ a * d₂ b := fun a b => by
    rw [← hd, Algebra.TensorProduct.lift_tmul]
  have hl : d (comulAlgHom O A (e c)) = ofConv (toConv d₁ * toConv d₂) (e c) := by
    rw [AlgHom.convMul_apply, hd]; rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hl, he.pt, map_sum]
  simp_rw [apply_ite d, map_zero, hdt, he.pt]
  rw [Finset.sum_eq_single (d₁, d₂) (fun b _ hb => by
    by_cases h1 : b.1 = d₁ <;> by_cases h2 : b.2 = d₂ <;> simp_all [Prod.ext_iff]) (by simp)]
  simp [eq_comm]

section Group

variable {p : ℕ} [Fact p.Prime] [IsDomain O] (G : PDivGroup p O)
  (s : G.TateOver (IsLocalRing.ResidueField O) →ₗ[ℤ_[p]] G.Tate)
  (hpt : ∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O),
    ∃ t : G.TateOver (IsLocalRing.ResidueField O), t.pt n = c)

def sig (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O) : G.A n →ₐ[O] O :=
  (s (Classical.choose (hpt n c))).pt n

variable {G s hpt}
variable (hs : ∀ t, G.tatePush (Algebra.ofId O (IsLocalRing.ResidueField O)) (s t) = t)
  (hw : ∀ (n : ℕ) (t t' : G.TateOver (IsLocalRing.ResidueField O)),
    t.pt n = t'.pt n → (s t).pt n = (s t').pt n)

include hw in
theorem sig_eq (n : ℕ) (t : G.TateOver (IsLocalRing.ResidueField O)) :
    sig G s hpt n (t.pt n) = (s t).pt n :=
  hw n _ _ (Classical.choose_spec (hpt n (t.pt n)))

include hs hw in
theorem ofId_comp_sig (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O) :
    (Algebra.ofId O (IsLocalRing.ResidueField O)).comp (sig G s hpt n c) = c := by
  obtain ⟨t, rfl⟩ := hpt n c
  rw [sig_eq hw]
  exact congrArg (fun y => TateOver.pt y n) (hs t)

include hw in
theorem sig_mul (n : ℕ) (c₁ c₂ : G.A n →ₐ[O] IsLocalRing.ResidueField O) :
    sig G s hpt n (ofConv (toConv c₁ * toConv c₂)) =
      ofConv (toConv (sig G s hpt n c₁) * toConv (sig G s hpt n c₂)) := by
  obtain ⟨t₁, rfl⟩ := hpt n c₁
  obtain ⟨t₂, rfl⟩ := hpt n c₂
  have h : ofConv (toConv (t₁.pt n) * toConv (t₂.pt n)) = (t₁ + t₂).pt n := rfl
  rw [h, sig_eq hw, sig_eq hw, sig_eq hw, map_add (f := _)]
  rfl

include hw in
theorem sig_one (n : ℕ) :
    sig G s hpt n (ofConv (1 : WithConv (G.A n →ₐ[O] IsLocalRing.ResidueField O))) =
      ofConv (1 : WithConv (G.A n →ₐ[O] O)) := by
  have h : ofConv (1 : WithConv (G.A n →ₐ[O] IsLocalRing.ResidueField O)) =
    (0 : G.TateOver (IsLocalRing.ResidueField O)).pt n := rfl
  rw [h, sig_eq hw, map_zero]
  rfl


omit [IsLocalRing O] [IsDomain O] in
theorem smul_p_pt {B : Type} [CommRing B] [Algebra O B] (x : G.TateOver B) (n : ℕ) :
    ((p : ℤ_[p]) • x).pt (n + 1) = (x.pt n).comp (G.res n : G.A (n + 1) →ₐ[O] G.A n) := by
  have h1 : ((p : ℤ_[p]) • x).conv (n + 1) = x.conv (n + 1) ^ p := by
    rw [TateOver.smul_conv]
    exact GlobalTheory.PDiv.pow_digit_natCast (G.pts_pow_self (n + 1) _) p
  exact congrArg ofConv (h1.trans (x.conv_succ_pow n))

include hw in
theorem sig_res (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O) :
    sig G s hpt (n + 1) (c.comp (G.res n : G.A (n + 1) →ₐ[O] G.A n)) =
      (sig G s hpt n c).comp (G.res n : G.A (n + 1) →ₐ[O] G.A n) := by
  obtain ⟨t, rfl⟩ := hpt n c
  rw [← smul_p_pt, sig_eq hw, map_smul, smul_p_pt, sig_eq hw]

end Group

section Endo

variable {p : ℕ} [Fact p.Prime] [IsDomain O] {G : PDivGroup p O}
  {s : G.TateOver (IsLocalRing.ResidueField O) →ₗ[ℤ_[p]] G.Tate}
  {hpt : ∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O),
    ∃ t : G.TateOver (IsLocalRing.ResidueField O), t.pt n = c}
  (hs : ∀ t, G.tatePush (Algebra.ofId O (IsLocalRing.ResidueField O)) (s t) = t)
  (hw : ∀ (n : ℕ) (t t' : G.TateOver (IsLocalRing.ResidueField O)),
    t.pt n = t'.pt n → (s t).pt n = (s t').pt n)
  [∀ n, Fintype (G.A n →ₐ[O] IsLocalRing.ResidueField O)]
  {e : ∀ n, (G.A n →ₐ[O] IsLocalRing.ResidueField O) → G.A n} (he : ∀ n, IdemData (G.A n) (e n))


variable (s hpt) in
def endo (n : ℕ) : G.A n →ₐ[O] G.A n :=
  (sumE (he n)).comp (AlgHom.pi (sig G s hpt n))

theorem endo_apply (n : ℕ) (a : G.A n) :
    endo s hpt he n a = ∑ c, sig G s hpt n c a • e n c := rfl

include hs hw in
theorem sig_sumE (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O)
    (f : (G.A n →ₐ[O] IsLocalRing.ResidueField O) → O) :
    sig G s hpt n c (sumE (he n) f) = f c := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [sumE_apply, map_sum]
  simp_rw [map_smul, (he n).ptO, ofId_comp_sig hs hw]
  simp

include hs hw in
theorem endo_sumE (n : ℕ) (f : (G.A n →ₐ[O] IsLocalRing.ResidueField O) → O) :
    endo s hpt he n (sumE (he n) f) = sumE (he n) f := by
  have h : AlgHom.pi (sig G s hpt n) (sumE (he n) f) = f :=
    funext fun c => sig_sumE hs hw he n c f
  change sumE (he n) (AlgHom.pi (sig G s hpt n) (sumE (he n) f)) = _
  rw [h]

include hs hw in
theorem endo_endo (n : ℕ) (a : G.A n) : endo s hpt he n (endo s hpt he n a) = endo s hpt he n a :=
  endo_sumE hs hw he n _

include hs hw in
theorem counit_endo (n : ℕ) :
    (counitAlgHom O (G.A n)).comp (endo s hpt he n) = counitAlgHom O (G.A n) := by
  ext a
  set_option synthInstance.maxHeartbeats 100000 in
    rw [AlgHom.comp_apply, endo_apply, map_sum]
  simp_rw [map_smul, (he n).ptO]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have h := congrArg (fun x : G.A n →ₐ[O] O => x a) (sig_one (hpt := hpt) hw n)
  exact h

end Endo

section Endo2

variable {p : ℕ} [Fact p.Prime] [IsDomain O] {G : PDivGroup p O}
  {s : G.TateOver (IsLocalRing.ResidueField O) →ₗ[ℤ_[p]] G.Tate}
  {hpt : ∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O),
    ∃ t : G.TateOver (IsLocalRing.ResidueField O), t.pt n = c}
  (hs : ∀ t, G.tatePush (Algebra.ofId O (IsLocalRing.ResidueField O)) (s t) = t)
  (hw : ∀ (n : ℕ) (t t' : G.TateOver (IsLocalRing.ResidueField O)),
    t.pt n = t'.pt n → (s t).pt n = (s t').pt n)
  [∀ n, Fintype (G.A n →ₐ[O] IsLocalRing.ResidueField O)]
  {e : ∀ n, (G.A n →ₐ[O] IsLocalRing.ResidueField O) → G.A n} (he : ∀ n, IdemData (G.A n) (e n))

theorem map_endo_endo (n : ℕ) (z : G.A n ⊗[O] G.A n) :
    Algebra.TensorProduct.map (endo s hpt he n) (endo s hpt he n) z =
      ∑ x : (G.A n →ₐ[O] IsLocalRing.ResidueField O) × (G.A n →ₐ[O] IsLocalRing.ResidueField O),
        Algebra.TensorProduct.lift (sig G s hpt n x.1) (sig G s hpt n x.2) (fun _ _ => .all _ _) z •
          (e n x.1 ⊗ₜ[O] e n x.2) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, endo_apply, endo_apply, TensorProduct.sum_tmul,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c₁ _ => ?_
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun c₂ _ => ?_
    rw [Algebra.TensorProduct.lift_tmul, TensorProduct.smul_tmul_smul]
  | add x y hx hy =>
    simp only [map_add (f := _), hx, hy, add_smul, Finset.sum_add_distrib]

include hw in
theorem comul_endo (H : HasIdem O) (n : ℕ) :
    (Algebra.TensorProduct.map (endo s hpt he n) (endo s hpt he n)).comp
      (comulAlgHom O (G.A n)) = (comulAlgHom O (G.A n)).comp (endo s hpt he n) := by
  refine AlgHom.ext fun a => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [AlgHom.comp_apply, AlgHom.comp_apply, map_endo_endo, endo_apply, map_sum]
  simp_rw [map_smul, Bialgebra.comulAlgHom_apply, comul_e H (he n), Finset.smul_sum, smul_ite,
    smul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  rw [sig_mul hw]
  congr 1
  exact (AlgHom.convMul_apply _ _ a).symm

include hw in
theorem res_endo (H : HasIdem O) (n : ℕ) (a : G.A (n + 1)) :
    G.res n (endo s hpt he (n + 1) a) = endo s hpt he n (G.res n a) := by
  have hp : ∀ c, G.res n (e (n + 1) c) = ∑ c', if c'.comp (G.res n : G.A (n + 1) →ₐ[O] G.A n) = c
      then e n c' else 0 := fun c => by
    exact push_e H (he (n + 1)) (he n) (G.res n : G.A (n + 1) →ₐ[O] G.A n) c
  set_option synthInstance.maxHeartbeats 100000 in
    rw [endo_apply, endo_apply, map_sum]
  simp_rw [map_smul, hp, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  rw [sig_res hw]
  rfl


variable (s hpt) in
include hpt he in
def uEnd (H : HasIdem O) : G ⟶ G where
  app n := BialgHom.ofAlgHom (endo s hpt he n) (counit_endo hs hw he n) (comul_endo hw he H n)
  comm n := BialgHom.ext fun a => res_endo hw he H n a

include hs hw hpt in
theorem sumE_injective (n : ℕ) : Function.Injective (sumE (he n)) := fun f g h =>
  funext fun c => by
    have h1 := congrArg (sig G s hpt n c) h
    rwa [sig_sumE hs hw he, sig_sumE hs hw he] at h1

include hs hw in
theorem range_endo (n : ℕ) : (endo s hpt he n).range = (sumE (he n)).range := by
  refine le_antisymm (AlgHom.range_comp_le_range _ _) ?_
  rintro x ⟨f, rfl⟩
  exact ⟨sumE (he n) f, endo_sumE hs hw he n f⟩

include hs hw hpt he in
theorem exists_endo (H : HasIdem O) : ∃ u : G ⟶ G, u ≫ u = u ∧
    (∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O) (a : G.A n), c (u.app n a) = c a) ∧
    ∀ n, ∃ N : ℕ, Nonempty ((u.app n : G.A n →ₐ[O] G.A n).range ≃ₐ[O] (Fin N → O)) := by
  refine ⟨uEnd s hpt hs hw he H, PDivGroup.Hom.ext (funext fun n => BialgHom.ext fun a => endo_endo hs hw he n a),
    fun n c a => ?_, fun n => ⟨Fintype.card (G.A n →ₐ[O] IsLocalRing.ResidueField O), ⟨?_⟩⟩⟩
  · change c (endo s hpt he n a) = c a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [endo_apply, map_sum]
    simp_rw [map_smul, (he n).pt, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true, Algebra.smul_def, mul_one]
    exact DFunLike.congr_fun (ofId_comp_sig (hpt := hpt) hs hw n c) a
  · have h : ((uEnd s hpt hs hw he H).app n : G.A n →ₐ[O] G.A n) = endo s hpt he n := rfl
    rw [h]
    exact ((Subalgebra.equivOfEq _ _ (range_endo hs hw he n)).trans
      (AlgEquiv.ofInjective _ (sumE_injective (hpt := hpt) hs hw he n)).symm).trans
      (AlgEquiv.piCongrLeft O (fun _ => O) (Fintype.equivFin _).symm).symm

end Endo2

theorem exists_idempotent_constPart : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, ∃ u : G ⟶ G, u ≫ u = u ∧ (∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O) (a : G.A n), c (u.app n a) = c a) ∧ ∀ n, ∃ N : ℕ, Nonempty ((u.app n : G.A n →ₐ[O] G.A n).range ≃ₐ[O] (Fin N → O)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv G
  have H : HasIdem O := fun A _ _ _ => GlobalTheory.T.finiteAlgebra_residuePoint_idempotents_over_OC p C v O hv A
  obtain ⟨hpt, s, hs, hw⟩ := GlobalTheory.T.pDivGroup_residueField_tate_level_section p C v O hv G
  have hH : ∀ n, Finite (G.A n →ₐ[O] IsLocalRing.ResidueField O) ∧
      ∃ e, IdemData (G.A n) e := fun n => H (G.A n)
  choose hfin e he using hH
  haveI : ∀ n, Fintype (G.A n →ₐ[O] IsLocalRing.ResidueField O) := fun n => Fintype.ofFinite _
  exact exists_endo (hpt := hpt) hs hw he H

end GlobalTheory.ConstPart
