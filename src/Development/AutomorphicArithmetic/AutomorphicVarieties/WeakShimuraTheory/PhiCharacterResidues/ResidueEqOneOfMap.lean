module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CpRedProdScaleRoots

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CoprimeOfResidue
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem coprime_of_residue {B : Type} [CommRing B] [IsLocalRing B] (p q : B[X]) (hp : p.Monic)
    (h : IsCoprime (p.map (residue B)) (q.map (residue B))) : IsCoprime p q := by
  rw [← isUnit_resultant_iff_isCoprime hp]
  have hp' : (p.map (residue B)).Monic := hp.map _
  have h1 := (isUnit_resultant_iff_isCoprime hp').2 h
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (natDegree_map_le (f := residue B) (p := q))
  have h2 : residue B (p.resultant q) = (p.map (residue B)).resultant (q.map (residue B)) := by
    rw [← resultant_map_map, hj, resultant_add_right_deg _ _ _ _ _ le_rfl,
      ← hp.natDegree_map (residue B), hp'.coeff_natDegree, one_pow, one_mul]
  rw [← h2] at h1
  exact (isUnit_map_iff (residue B) _).1 h1

theorem UpperTheory.V.Ws.phiRigid :
    ∀ {B E k : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field k] (f : B →+* k), (∀ x, f x = 0 → x ∈ maximalIdeal B) → ∀ (M : E) (p : B[X]) (d m : ℕ), p.Monic → aeval M p = 0 → p.map f = (Polynomial.X - 1) ^ d → M ^ m = 1 → IsUnit (m : B) → M = 1 := by
  intro B E k _ _ _ _ _ f hf M p d m hp hM hpf hm hu
  have h1 : p.map (residue B) = (Polynomial.X - 1) ^ d := by
    have h0 : (p - (Polynomial.X - 1) ^ d).map f = 0 := by
      simp [Polynomial.map_sub, Polynomial.map_pow, hpf]
    have h2 : (p - (Polynomial.X - 1) ^ d).map (residue B) = 0 := by
      ext i
      rw [coeff_map, coeff_zero, residue_eq_zero_iff]
      apply hf
      rw [← coeff_map, h0, coeff_zero]
    simpa [Polynomial.map_sub, Polynomial.map_pow, sub_eq_zero] using h2
  set S : B[X] := ∑ i ∈ Finset.range m, Polynomial.X ^ i with hS
  have hc : IsCoprime p S := by
    apply coprime_of_residue p S hp
    rw [h1]
    apply IsCoprime.pow_left
    have hirr : Irreducible (Polynomial.X - C (1 : ResidueField B)) := irreducible_X_sub_C 1
    rw [← C_1, hirr.coprime_iff_not_dvd, dvd_iff_isRoot]
    have h3 : ((m : ℕ) : ResidueField B) ≠ 0 := by
      have := (hu.map (residue B)).ne_zero
      rwa [map_natCast] at this
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [hS, Polynomial.map_sum, eval_finsetSum] using h3
  obtain ⟨a, b, hab⟩ := hc
  have h4 : aeval M b * aeval M S = 1 := by
    have := congrArg (aeval M) hab
    simpa [hM] using this
  have h5 : aeval M S * (M - 1) = 0 := by
    have : aeval M S = ∑ i ∈ Finset.range m, M ^ i := by simp [hS]
    rw [this, geom_sum_mul, hm, sub_self]
  have h6 : M - 1 = 0 := by
    have := congrArg (aeval M b * ·) h5
    simpa only [← mul_assoc, h4, one_mul, mul_zero] using this
  exact sub_eq_zero.1 h6
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem residue_eq_one_of_map {R S : Type} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (f : R →+* S) (x : R)
    (hx : residue S (f x) = 1) : residue R x = 1 := by
  rw [← map_one (residue R), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  rw [← map_one (residue S), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← map_one f, ← map_sub] at hx
  exact fun hu => hx (hu.map f)

private theorem lab_surj (pr : Bool) : Function.Surjective (lab pr) := by
  cases pr
  · exact Function.surjective_id
  · decide

private theorem ine_resLe {Ω : Type} [Field Ω] [CharZero Ω] {F L : IntermediateField ℚ Ω} [NumberField F] [NumberField L]
    (h : F ≤ L) (A : ValuationSubring Ω) (g : G L Ω) (hg : g ∈ Ine (F := L) A) : resLe h g ∈ Ine (F := F) A :=
  ⟨hg.1, hg.2⟩

theorem UpperTheory.V.Ws.phiIne :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ u, ∀ g ∈ K.r.Ip u, ∃ g', K.V.pr g' = g ∧ K.rho X n g' = 1 := by
  intro Ω _ _ _ l hl c D T c' h K X n u g hg
  obtain ⟨⟨g', hg', rfl⟩, hk⟩ := hg
  refine ⟨g', rfl, ?_⟩
  have hk' : ∀ i, K.r.chib i (K.V.pr g') = 1 := fun i => Subgroup.mem_iInf.1 hk i
  have hA : ¬ (K.s.A u.1).valuation (l : Ω) < 1 := fun hv => K.s.St_l u.1 u.2 ((K.s.hA u.1 l).1 (by simpa using hv))
  obtain ⟨m, hm, hκ⟩ := K.tame
  have hβ : K.β g' = 1 := K.β_t (K.t_unr _ hA hg')
  have hκm : K.κ (g' ^ m) = 1 := by rw [map_pow]; exact hκ _ hA g' hg'
  have hbar : D.rbar (resQ T.F (resLe T.F_le (g' ^ m))) = 1 := by
    have h1 : ∀ j, residue c.O (D.ps j (resQ T.L (g' ^ m)) : c.O) = 1 := fun j => by
      obtain ⟨i, rfl⟩ := lab_surj T.pr j
      have h2 := K.chib i (g' ^ m)
      have h3 : K.r.chib i (K.V.pr (g' ^ m)) = 1 :=
        (map_pow ((K.r.chib i).comp K.V.pr) g' m).trans ((congrArg (· ^ m) (hk' i)).trans (one_pow m))
      rw [hκm, h3, Units.val_one, Units.val_one, one_mul] at h2
      exact residue_eq_one_of_map (inc h) _ h2.symm
    show (Matrix.diagonal fun j => (D.ps j (resQ T.L (g' ^ m)) : c.O)).map (residue c.O) = 1
    rw [Matrix.diagonal_map (map_zero _), ← Matrix.diagonal_one]
    exact congrArg _ (funext h1)
  have hr : X.P.r (resLe T.F_le (g' ^ m)) = 1 := by
    refine X.pair.kill _ ⟨K.s.A u.1, fun p hp => ?_, ine_resLe _ _ _ (pow_mem hg' m), hbar⟩
    obtain rfl : p = l := by simpa using hp
    exact hA
  have hpow : K.rho X n g' ^ m = 1 := by
    rw [← map_pow, Link.rho_apply, hr, Link.sc, hκm, map_pow K.β, hβ]
    simp
  obtain ⟨-, -, hmon, hmap⟩ := phiCpMap K X n g'
  refine phiRigid (res c'.O X.B : X.B →+* ResidueField c'.O) (fun x hx => (res_eq_zero_iff c'.O X.B x).1 hx) _ (K.cpT X n g') 4 m
    hmon ?_ ?_ hpow ?_
  · rw [← aeval_map_algebraMap X.A, hmap, Matrix.aeval_self_charpoly]
  · rw [phiCpRed K X n g']
    simp [hk']
  · obtain ⟨-, -, -, -, -, -, -, -, hu⟩ := dvrFacts l c'.O
    simpa using (hu m ((Nat.Prime.coprime_iff_not_dvd hl.out).1 hm)).map (algebraMap c'.O X.B)
