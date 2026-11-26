module

public import Formalism.PadicSubsetSums.StableGradedCounts.IRRIrredCountUpper
public import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
public import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots
public import Lemmata.FirstBlockLemmaG.Imports
public import Lemmata.MiscLemmasA.Imports

@[expose] public section

section -- merged from Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeToPartEqIff
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem pow_lpow_add {M : Type*} [Monoid M] {l a : ℕ} {x z : M} (h : x ^ (l ^ a) = z ^ (l ^ a))
    (b : ℕ) : x ^ (l ^ (a + b)) = z ^ (l ^ (a + b)) := by
  rw [pow_add, pow_mul, pow_mul, h]

theorem eq_of_pow_eq_of_coprime_order {M : Type*} [Monoid M] {r : ℕ} {u w : M}
    (hu : 0 < orderOf u) (hw : 0 < orderOf w) (hcu : Nat.Coprime r (orderOf u))
    (hcw : Nat.Coprime r (orderOf w)) (h : u ^ r = w ^ r) : u = w := by
  by_cases h1 : orderOf u * orderOf w = 1
  · have hu1 : orderOf u = 1 := Nat.eq_one_of_mul_eq_one_right h1
    have hw1 : orderOf w = 1 := Nat.eq_one_of_mul_eq_one_left h1
    rw [orderOf_eq_one_iff.mp hu1, orderOf_eq_one_iff.mp hw1]
  · have hpos : 0 < orderOf u * orderOf w := Nat.mul_pos hu hw
    have hlt : 1 < orderOf u * orderOf w := by omega
    obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime (Nat.Coprime.mul_right hcu hcw) hlt
    have hmod : r * s ≡ 1 [MOD orderOf u * orderOf w] := by
      unfold Nat.ModEq
      rw [hs, Nat.mod_eq_of_lt hlt]
    have hm1 : r * s ≡ 1 [MOD orderOf u] := Nat.ModEq.of_mul_right (orderOf w) hmod
    have hm2 : r * s ≡ 1 [MOD orderOf w] := Nat.ModEq.of_mul_left (orderOf u) hmod
    have hu' : u ^ (r * s) = u := by
      rw [← pow_mod_orderOf, show r * s % orderOf u = 1 % orderOf u from hm1, pow_mod_orderOf,
        pow_one]
    have hw' : w ^ (r * s) = w := by
      rw [← pow_mod_orderOf, show r * s % orderOf w = 1 % orderOf w from hm2, pow_mod_orderOf,
        pow_one]
    rw [← hu', ← hw', pow_mul, pow_mul, h]

theorem prime_to_part_eq_iff : PrimeToPartEqIff := by
  intro M _ l x y hl hx hy
  obtain ⟨hox, a, ha⟩ := prime_to_part_spec M l x hl hx
  obtain ⟨hoy, b, hb⟩ := prime_to_part_spec M l y hl hy
  have hnx : orderOf x ≠ 0 := (orderOf_pos_iff.mpr hx).ne'
  have hny : orderOf y ≠ 0 := (orderOf_pos_iff.mpr hy).ne'
  constructor
  · intro h
    refine ⟨a + b, ?_⟩
    rw [pow_lpow_add ha b, h, add_comm a b, pow_lpow_add hb a]
  · rintro ⟨c, hc⟩
    have e1 : primeToPart l x ^ (l ^ (a + (b + c))) = x ^ (l ^ (a + (b + c))) :=
      (pow_lpow_add ha _).symm
    have e2 : primeToPart l y ^ (l ^ (b + (a + c))) = y ^ (l ^ (b + (a + c))) :=
      (pow_lpow_add hb _).symm
    have e3 : x ^ (l ^ (c + (a + b))) = y ^ (l ^ (c + (a + b))) := pow_lpow_add hc _
    have s1 : a + (b + c) = c + (a + b) := by omega
    have s2 : b + (a + c) = c + (a + b) := by omega
    rw [s1] at e1
    rw [s2] at e2
    refine eq_of_pow_eq_of_coprime_order (r := l ^ (c + (a + b))) ?_ ?_ ?_ ?_ (by rw [e1, e2, e3])
    · rw [hox]; exact Nat.ordCompl_pos l hnx
    · rw [hoy]; exact Nat.ordCompl_pos l hny
    · rw [hox]; exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hnx)
    · rw [hoy]; exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hny)

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section -- merged from Formalism.PadicSubsetSums.StableGradedCounts.ExistsNeZeroAevalEqZero
open Polynomial
open scoped TensorProduct

namespace Formalism.IrreducibleCountingLemmas.Z

theorem exists_ne_zero_aeval_eq_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (p : K[X]) (hp : Irreducible p)
    (hdvd : p ∣ g.charpoly) : ∃ w : V, w ≠ 0 ∧ aeval g p w = 0 := by
  classical
  by_contra hcon
  have hinj : Function.Injective (aeval g p) := by
    refine (injective_iff_map_eq_zero (aeval g p)).2 fun w hw => ?_
    by_contra hw0
    exact hcon ⟨w, hw0, hw⟩
  haveI : Fact (Irreducible p) := ⟨hp⟩
  have hunit : IsUnit (aeval g p) := by
    first
      | exact (Module.End.isUnit_iff _).2 ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
      | exact (LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot.2 hinj)
  have hunitL := hunit.map (Module.End.baseChangeHom K (AdjoinRoot p) V)
  have hE : Module.End.baseChangeHom K (AdjoinRoot p) V (aeval g p)
      = aeval (g.baseChange (AdjoinRoot p)) (p.map (algebraMap K (AdjoinRoot p))) := by
    rw [Polynomial.aeval_map_algebraMap, ← Polynomial.aeval_algHom_apply]
    rfl
  have hpr : Polynomial.eval (AdjoinRoot.root p) (p.map (algebraMap K (AdjoinRoot p))) = 0 := by
    rw [Polynomial.eval_map, AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root p
  have hev : Module.End.HasEigenvalue (g.baseChange (AdjoinRoot p)) (AdjoinRoot.root p) := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, LinearMap.charpoly_baseChange]
    exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (Polynomial.map_dvd _ hdvd) hpr
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have h0 : aeval (g.baseChange (AdjoinRoot p)) (p.map (algebraMap K (AdjoinRoot p))) v = 0 := by
    rw [Module.End.aeval_apply_of_hasEigenvector hv, hpr, zero_smul]
  rw [← hE] at h0
  have hbij : Function.Injective (Module.End.baseChangeHom K (AdjoinRoot p) V (aeval g p)) := by
    first
      | exact ((Module.End.isUnit_iff _).1 hunitL).1
      | exact LinearMap.ker_eq_bot.1 ((LinearMap.isUnit_iff_ker_eq_bot _).1 hunitL)
  exact hv.2 (hbij (h0.trans (map_zero _).symm))

theorem exists_annihilator_eq {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (hs : g.charpoly.Separable) (d : K[X]) :
    d ∣ g.charpoly → ∃ e : V, aeval g d e = 0 ∧ ∀ q : K[X], aeval g q e = 0 → d ∣ q := by
  classical
  have hm : ∀ (f h : Module.End K V) (x : V), (f * h) x = f (h x) := fun _ _ _ => rfl
  have hadd : ∀ (f h : Module.End K V) (x : V), (f + h) x = f x + h x := fun _ _ _ => rfl
  have hone : ∀ x : V, (1 : Module.End K V) x = x := fun _ => rfl
  have hkill : ∀ (s t : K[X]) (x : V), aeval g s x = 0 → aeval g (t * s) x = 0 := by
    intro s t x hx
    rw [map_mul, hm, hx, map_zero]
  have hsq : Squarefree g.charpoly := hs.squarefree
  refine WfDvdMonoid.induction_on_irreducible d ?_ ?_ ?_
  · intro h0
    exact absurd (zero_dvd_iff.1 h0) (LinearMap.charpoly_monic g).ne_zero
  · intro u hu _
    exact ⟨0, map_zero _, fun q _ => hu.dvd⟩
  · intro a i _ hi ih hdvd
    have ha : a ∣ g.charpoly := dvd_of_mul_left_dvd hdvd
    have hid : i ∣ g.charpoly := dvd_of_mul_right_dvd hdvd
    obtain ⟨ea, hea0, hea⟩ := ih ha
    obtain ⟨w, hw0, hw⟩ := exists_ne_zero_aeval_eq_zero g i hi hid
    have hcopOf : ∀ n : K[X], ¬ i ∣ n → IsCoprime i n := fun n h => by
      first
        | exact (Irreducible.coprime_iff_not_dvd hi).2 h
        | exact (Irreducible.isCoprime_iff_not_dvd hi).2 h
    have hcop : IsCoprime i a := hcopOf a fun hia =>
      hi.1 (hsq i (dvd_trans (mul_dvd_mul_left i hia) hdvd))
    refine ⟨ea + w, ?_, fun q hq => ?_⟩
    · rw [map_add (f := _), hkill a i ea hea0, mul_comm, hkill i a w hw, add_zero]
    · have hw' : aeval g (i * q) w = 0 := by
        rw [mul_comm]
        exact hkill i q w hw
      have hqi : aeval g (i * q) ea = 0 := by
        have h1 := hkill q i _ hq
        rwa [map_add, hw', add_zero] at h1
      have haq : a ∣ q := by
        have h2 : a ∣ i * q := hea _ hqi
        first
          | exact hcop.symm.dvd_of_dvd_mul_left h2
          | exact hcop.symm.dvd_of_dvd_mul_right (by rwa [mul_comm] at h2)
      have hea' : aeval g (a * q) ea = 0 := by
        rw [mul_comm]
        exact hkill a q ea hea0
      have hwq : aeval g (a * q) w = 0 := by
        have h1 := hkill q a _ hq
        rwa [map_add, hea', zero_add] at h1
      have hiaq : i ∣ a * q := by
        by_contra hn
        obtain ⟨u, t, hut⟩ := hcopOf _ hn
        apply hw0
        have h2 : aeval g (u * i + t * (a * q)) w = 0 := by
          rw [map_add (f := _), hadd, hkill i u w hw, hkill (a * q) t w hwq, add_zero]
        rwa [hut, map_one, hone] at h2
      have hiq : i ∣ q := by
        first
          | exact hcop.dvd_of_dvd_mul_left hiaq
          | exact hcop.dvd_of_dvd_mul_right (by rwa [mul_comm] at hiaq)
      exact hcop.mul_dvd hiq haq

theorem base_change_cyclic_vector : BCCyclicVector := by
  unfold BCCyclicVector
  intro K V _ _ _ _ g hs
  classical
  obtain ⟨e, -, he⟩ := exists_annihilator_eq g hs g.charpoly dvd_rfl
  let φ : K[X] →ₗ[K] V :=
    { toFun := fun q => aeval g q e
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  let ψ : Polynomial.degreeLT K (Module.finrank K V) →ₗ[K] V :=
    φ.comp (Polynomial.degreeLT K (Module.finrank K V)).subtype
  have hdeg : g.charpoly.degree = (Module.finrank K V : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree (LinearMap.charpoly_monic g).ne_zero,
      LinearMap.charpoly_natDegree]
  have hinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).2 fun x hx => ?_
    have hmem := Polynomial.mem_degreeLT.1 x.2
    have hd : g.charpoly ∣ x.1 := he x.1 hx
    exact Subtype.ext (Polynomial.eq_zero_of_dvd_of_degree_lt hd (by rw [hdeg]; exact hmem))
  haveI : FiniteDimensional K (Polynomial.degreeLT K (Module.finrank K V)) :=
    LinearEquiv.finiteDimensional (Polynomial.degreeLTEquiv K (Module.finrank K V)).symm
  have hfr : Module.finrank K (Polynomial.degreeLT K (Module.finrank K V)) = Module.finrank K V := by
    rw [(Polynomial.degreeLTEquiv K (Module.finrank K V)).finrank_eq]
    simp
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj
  refine ⟨e, fun v => ?_⟩
  obtain ⟨x, hx⟩ := hsurj v
  exact ⟨x.1, hx⟩

end Formalism.IrreducibleCountingLemmas.Z
end

section -- merged from Formalism.PadicSubsetSums.StableGradedCounts.FixedByAutomorphismInField
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem exists_algEquiv_extending {F E : Type} [Field F] [Field E] [Algebra F E] [IsAlgClosed E]
    (σ₀ : algebraicClosure F E ≃ₐ[F] algebraicClosure F E) :
    ∃ σ : E ≃ₐ[F] E, ∀ a : algebraicClosure F E, σ (a : E) = (σ₀ a : E) := by
  obtain ⟨ι, B, hB⟩ := exists_isTranscendenceBasis' (algebraicClosure F E) E
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis B hB
  let e₁ : MvPolynomial ι (algebraicClosure F E) ≃ₐ[algebraicClosure F E]
      Algebra.adjoin (algebraicClosure F E) (Set.range B) := hB.1.aevalEquiv
  let m : MvPolynomial ι (algebraicClosure F E) ≃+* MvPolynomial ι (algebraicClosure F E) :=
    MvPolynomial.mapEquiv ι σ₀.toRingEquiv
  let e : Algebra.adjoin (algebraicClosure F E) (Set.range B) ≃+*
      Algebra.adjoin (algebraicClosure F E) (Set.range B) :=
    e₁.symm.toRingEquiv.trans (m.trans e₁.toRingEquiv)
  let σ : E ≃+* E := IsAlgClosure.equivOfEquiv E E e
  have he : ∀ a : algebraicClosure F E,
      e (algebraMap _ _ a) = algebraMap _ _ (σ₀ a) := by
    intro a
    simp only [e, m, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C,
      ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rfl
  have hσ : ∀ a : algebraicClosure F E, σ (a : E) = (σ₀ a : E) := by
    intro a
    have h1 : (a : E) = algebraMap (Algebra.adjoin (algebraicClosure F E) (Set.range B)) E
        (algebraMap _ _ a) := rfl
    rw [h1, IsAlgClosure.equivOfEquiv_algebraMap, he]
    rfl
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) ?_, hσ⟩
  intro r
  have h1 : algebraMap F E r = ((algebraMap F (algebraicClosure F E) r : algebraicClosure F E) : E) :=
    rfl
  rw [h1, hσ, AlgEquiv.commutes]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section -- merged from Formalism.PadicSubsetSums.StableGradedCounts.IRRSquarefreeCount
open Polynomial
open scoped Classical

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


open Classical in
theorem card_mult_le {K : Type} [Field K] [Fintype K] (N j : ℕ) (P : K[X]) (hP : P.Monic)
    (hj : P.natDegree = j) :
    ((Finset.univ : Finset (Fin N → K)).filter (fun c => P * P ∣ monicOf c)).card
      ≤ Fintype.card K ^ (N - 2 * j) := by
  have hPP : (P * P).Monic := hP.mul hP
  have hcard : Fintype.card (Fin (N - 2 * j) → K) = Fintype.card K ^ (N - 2 * j) := by simp
  rw [← hcard, ← Finset.card_univ]
  apply Finset.card_le_card_of_injOn
    (fun c => fun i : Fin (N - 2 * j) => ((monicOf c) /ₘ (P * P)).coeff i)
  · intro c _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
  · have key : ∀ c : Fin N → K, P * P ∣ monicOf c →
        ((monicOf c) /ₘ (P * P)).Monic ∧ ((monicOf c) /ₘ (P * P)).natDegree = N - 2 * j ∧
        monicOf c = P * P * ((monicOf c) /ₘ (P * P)) := by
      intro c hc
      obtain ⟨g, hg⟩ := hc
      have hdiv : (monicOf c) /ₘ (P * P) = g := by
        rw [hg]; exact mul_divByMonic_cancel_left g hPP
      have hgm : g.Monic := hPP.of_mul_monic_left (hg ▸ monicOf_monic c)
      have hdeg : (monicOf c).natDegree = (P * P).natDegree + g.natDegree := by
        rw [hg]; exact hPP.natDegree_mul hgm
      rw [monicOf_natDegree, hP.natDegree_mul hP, hj] at hdeg
      rw [hdiv]
      exact ⟨hgm, by omega, hg⟩
    intro c hc c' hc' h
    obtain ⟨h1, h2, h3⟩ := key c (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2
    obtain ⟨h1', h2', h3'⟩ := key c' (Finset.mem_filter.mp (Finset.mem_coe.mp hc')).2
    apply monicOf_injective
    rw [h3, h3', ← monicOf_coeffs h1 h2, ← monicOf_coeffs h1' h2']
    exact congrArg (fun v => P * P * monicOf v) h

theorem geom_tail (q N m : ℕ) (hq : 2 ≤ q) (hN : 2 ≤ N) (hm : m ≤ N) :
    ∑ j ∈ Finset.Icc 2 m, q ^ (N - j) ≤ 2 * q ^ (N - 2) := by
  have key : ∀ m, 1 ≤ m → m ≤ N →
      (∑ j ∈ Finset.Icc 2 m, q ^ (N - j)) * (q - 1) + q ^ (N - m) = q ^ (N - 1) := by
    intro m
    induction m with
    | zero => intro h; omega
    | succ m ih =>
      intro h1 h2
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp
      · rw [Finset.sum_Icc_succ_top (by omega), add_mul, add_assoc]
        have e : q ^ (N - (m + 1)) * (q - 1) + q ^ (N - (m + 1)) = q ^ (N - m) := by
          have h3 : N - m = (N - (m + 1)) + 1 := by omega
          rw [h3, pow_succ, ← Nat.mul_succ]
          congr 1
          omega
        rw [e]
        exact ih hm (by omega)
  by_cases hm1 : 1 ≤ m
  · have h := key m hm1 hm
    have hN1 : q ^ (N - 1) = q ^ (N - 2) * q := by
      rw [← pow_succ]; congr 1; omega
    obtain ⟨p, hp⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
    subst hp
    have hq1 : p + 2 - 1 = p + 1 := by omega
    rw [hq1, hN1] at h
    set S := ∑ j ∈ Finset.Icc 2 m, (p + 2) ^ (N - j)
    set Q := (p + 2) ^ (N - 2)
    by_contra hc
    push_neg at hc
    have h4 := Nat.mul_le_mul_right (p + 1) (show 2 * Q + 1 ≤ S by omega)
    clear_value S Q
    ring_nf at h h4
    nlinarith [Nat.zero_le (p * Q), Nat.zero_le ((2 + p) ^ (N - m))]
  · have : m = 0 := by omega
    subst this
    simp

theorem squarefree_count : SquarefreeCount := by
  classical
  intro K _ _ N hN
  set q := Fintype.card K with hq
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  set Ω := (Finset.univ : Finset (Fin N → K)) with hΩ
  set Good := Ω.filter (fun c => Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0) with hGood
  set Bad0 := Ω.filter (fun c => (monicOf c).coeff 0 = 0) with hBad0
  set BadS := Ω.filter (fun c => ¬ Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0) with hBadS
  have hΩcard : Ω.card = q ^ N := by simp [hΩ, hq]
  have hcover : Ω ⊆ Good ∪ (Bad0 ∪ BadS) := by
    intro c hc
    simp only [hGood, hBad0, hBadS, Finset.mem_union, Finset.mem_filter]
    by_cases h0 : (monicOf c).coeff 0 = 0
    · exact Or.inr (Or.inl ⟨hc, h0⟩)
    · by_cases hs : Squarefree (monicOf c)
      · exact Or.inl ⟨hc, hs, h0⟩
      · exact Or.inr (Or.inr ⟨hc, hs, h0⟩)
  have hB0 : Bad0.card ≤ q ^ (N - 1) := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hcard : Fintype.card (Fin M → K) = q ^ (M + 1 - 1) := by simp [hq]
    rw [← hcard, ← Finset.card_univ]
    apply Finset.card_le_card_of_injOn (fun c => Fin.tail c)
    · intro c _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro c hc c' hc' h
      have h0 : c 0 = 0 := by
        have := (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2
        rwa [← monicOf_coeff c 0]
      have h0' : c' 0 = 0 := by
        have := (Finset.mem_filter.mp (Finset.mem_coe.mp hc')).2
        rwa [← monicOf_coeff c' 0]
      rw [← Fin.cons_self_tail c, ← Fin.cons_self_tail c', h0, h0']
      exact congrArg (Fin.cons 0) h
  set I : ℕ → ℕ := fun j => ((Finset.univ : Finset (Fin j → K)).filter
      (fun p => Irreducible (monicOf p) ∧ (monicOf p).coeff 0 ≠ 0)).card with hI
  have hBS : BadS.card ≤ ∑ j ∈ Finset.Icc 1 (N / 2), I j * q ^ (N - 2 * j) := by
    have hsub : BadS ⊆ (Finset.Icc 1 (N / 2)).biUnion (fun j =>
        ((Finset.univ : Finset (Fin j → K)).filter
          (fun p => Irreducible (monicOf p) ∧ (monicOf p).coeff 0 ≠ 0)).biUnion (fun p =>
            Ω.filter (fun c => monicOf p * monicOf p ∣ monicOf c))) := by
      intro c hc
      obtain ⟨_, hns, h0⟩ := Finset.mem_filter.mp hc
      have hne : monicOf c ≠ 0 := (monicOf_monic c).ne_zero
      rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hne] at hns
      push Not at hns
      obtain ⟨P, hPirr, hPdvd⟩ := hns
      set P' := normalize P with hP'
      have hass : Associated P' P := normalize_associated P
      have hP'irr : Irreducible P' := hass.symm.irreducible hPirr
      have hP'mon : P'.Monic := monic_normalize hPirr.ne_zero
      have hP'dvd : P' * P' ∣ monicOf c :=
        (mul_dvd_mul hass.dvd hass.dvd).trans hPdvd
      obtain ⟨g, hg⟩ := hP'dvd
      have hgm : g.Monic := (hP'mon.mul hP'mon).of_mul_monic_left (hg ▸ monicOf_monic c)
      have hdeg : (monicOf c).natDegree = (P' * P').natDegree + g.natDegree := by
        rw [hg]; exact (hP'mon.mul hP'mon).natDegree_mul hgm
      rw [monicOf_natDegree, hP'mon.natDegree_mul hP'mon] at hdeg
      have hj1 : 1 ≤ P'.natDegree := hP'irr.natDegree_pos
      have hc0 : P'.coeff 0 ≠ 0 := by
        intro hz
        apply h0
        rw [hg, mul_coeff_zero, mul_coeff_zero, hz]
        simp
      refine Finset.mem_biUnion.mpr ⟨P'.natDegree, Finset.mem_Icc.mpr ⟨hj1, by omega⟩, ?_⟩
      refine Finset.mem_biUnion.mpr ⟨fun i => P'.coeff i, ?_, ?_⟩
      · rw [Finset.mem_filter, monicOf_coeffs hP'mon rfl]
        exact ⟨Finset.mem_univ _, hP'irr, hc0⟩
      · rw [Finset.mem_filter, monicOf_coeffs hP'mon rfl]
        exact ⟨Finset.mem_univ _, ⟨g, hg⟩⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    apply Finset.sum_le_sum
    intro j _
    refine Finset.card_biUnion_le.trans ?_
    rw [hI]
    simp only
    rw [← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p _
    exact card_mult_le N j (monicOf p) (monicOf_monic p) (monicOf_natDegree p)
  have hI1 : I 1 ≤ q - 1 := by
    have hsub : ((Finset.univ : Finset (Fin 1 → K)).filter
        (fun p => Irreducible (monicOf p) ∧ (monicOf p).coeff 0 ≠ 0)) ⊆
        (Finset.univ : Finset (Fin 1 → K)).erase 0 := by
      intro p hp
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      have := (Finset.mem_filter.mp hp).2.2
      apply this
      have h := monicOf_coeff (0 : Fin 1 → K) 0
      simpa using h
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
    simpa [hI, hq] using this
  have hI2 : ∀ j, 2 ≤ j → 2 * I j ≤ q ^ j := by
    intro j hj
    have h1 := irreducible_count_upper K j (by omega)
    have h2 : I j ≤ ((Finset.univ : Finset (Fin j → K)).filter
        (fun c => Irreducible (monicOf c))).card := by
      apply Finset.card_le_card
      intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2.1⟩
    calc 2 * I j ≤ j * I j := Nat.mul_le_mul_right _ hj
      _ ≤ j * _ := Nat.mul_le_mul_left _ h2
      _ ≤ q ^ j := h1
  have hsum : ∑ j ∈ Finset.Icc 1 (N / 2), I j * q ^ (N - 2 * j) ≤ q ^ (N - 1) := by
    rcases Nat.lt_or_ge N 2 with hlt | hge
    · have : N / 2 = 0 := by omega
      rw [this]; simp
    · have hm1 : 1 ≤ N / 2 := by omega
      rw [← Finset.add_sum_Ioc_eq_sum_Icc hm1]
      have hIoc : Finset.Ioc 1 (N / 2) = Finset.Icc 2 (N / 2) := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
      rw [hIoc]
      have h2 : 2 * ∑ j ∈ Finset.Icc 2 (N / 2), I j * q ^ (N - 2 * j) ≤ 2 * q ^ (N - 2) := by
        rw [Finset.mul_sum]
        refine le_trans (Finset.sum_le_sum (fun j hj => ?_)) (geom_tail q N (N / 2) hq2 hge
          (Nat.div_le_self _ _))
        obtain ⟨hj2, hjm⟩ := Finset.mem_Icc.mp hj
        calc 2 * (I j * q ^ (N - 2 * j)) = (2 * I j) * q ^ (N - 2 * j) := by ring
          _ ≤ q ^ j * q ^ (N - 2 * j) := Nat.mul_le_mul_right _ (hI2 j hj2)
          _ = q ^ (N - j) := by rw [← pow_add]; congr 1; omega
      have h3 : I 1 * q ^ (N - 2 * 1) ≤ (q - 1) * q ^ (N - 2) := Nat.mul_le_mul_right _ hI1
      have h4 : q ^ (N - 1) = (q - 1) * q ^ (N - 2) + q ^ (N - 2) := by
        have : N - 1 = (N - 2) + 1 := by omega
        rw [this, pow_succ]
        obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
        rw [hr]
        simp only [Nat.add_sub_cancel]
        ring
      omega
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_union_le Good (Bad0 ∪ BadS)
  have h3 := Finset.card_union_le Bad0 BadS
  rw [hΩcard] at h1
  have h5 := hBS.trans hsum
  omega

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section -- merged from Formalism.PadicSubsetSums.StableGradedCounts.IRRTypeCountExact
open Polynomial UniqueFactorizationMonoid

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


set_option maxHeartbeats 800000 in
theorem type_count_exact : TypeCountExact := by
  classical
  intro K _ _ N n hN
  suffices H : ((Finset.univ : Finset (Fin N → K)).filter (fun c =>
      Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0 ∧
      ∀ d ∈ Finset.Icc 1 N, ((normalizedFactors (monicOf c)).map
        Polynomial.natDegree).count d = n d)).card =
      ∏ d ∈ Finset.Icc 1 N,
        (((Finset.univ : Finset (Fin d → K)).filter
          (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card).choose (n d) by
    convert H
  have L1 : ∀ m : Multiset K[X], (∀ q ∈ m, q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0) →
      m.prod.Monic ∧ normalizedFactors m.prod = m ∧
        m.prod.natDegree = (m.map Polynomial.natDegree).sum ∧ m.prod.coeff 0 ≠ 0 := by
    intro m
    induction m using Multiset.induction_on with
    | empty => intro _; simp
    | cons a s ih =>
      intro h
      have ha := h a (by simp)
      obtain ⟨h1, h2, h3, h4⟩ := ih (fun q hq => h q (by simp [hq]))
      have hna : normalize a = a := by
        first
          | exact ha.1.normalize_eq_self
          | exact Polynomial.Monic.normalize_eq_self ha.1
          | simp [normalize_apply, Polynomial.coe_normUnit, ha.1.leadingCoeff]
      rw [Multiset.prod_cons]
      refine ⟨ha.1.mul h1, ?_, ?_, ?_⟩
      · rw [normalizedFactors_mul ha.2.1.ne_zero h1.ne_zero, normalizedFactors_irreducible ha.2.1,
          hna, h2, Multiset.singleton_add]
      · rw [ha.1.natDegree_mul h1, h3, Multiset.map_cons, Multiset.sum_cons]
      · rw [Polynomial.mul_coeff_zero]
        exact mul_ne_zero ha.2.2 h4
  have L2 : ∀ (T : Finset K[X]) (d : ℕ), (T.val.map Polynomial.natDegree).count d =
      (T.filter (fun q => q.natDegree = d)).card := by
    intro T d
    rw [Multiset.count_map]
    exact congrArg Multiset.card (Multiset.filter_congr (fun x _ => eq_comm))
  have F : ∀ c : Fin N → K, (monicOf c).coeff 0 ≠ 0 → ∀ q ∈ normalizedFactors (monicOf c),
      q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0 ∧ 1 ≤ q.natDegree ∧ q.natDegree ≤ N := by
    intro c hc q hq
    have hirr : Irreducible q := by
      first
        | exact irreducible_of_normalized_factor q hq
        | exact UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
    have hq0 : q ≠ 0 := hirr.ne_zero
    have hnq : normalize q = q := by
      first
        | exact normalize_normalized_factor q hq
        | exact UniqueFactorizationMonoid.normalize_normalized_factor q hq
    have hmon : q.Monic := by
      have h := Polynomial.monic_normalize hq0
      rwa [hnq] at h
    have hdvd : q ∣ monicOf c := by
      first
        | exact dvd_of_mem_normalizedFactors hq
        | exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq
    have hp0 : monicOf c ≠ 0 := (monicOf_monic c).ne_zero
    refine ⟨hmon, hirr, ?_, ?_, ?_⟩
    · intro h0
      apply hc
      exact Polynomial.X_dvd_iff.mp ((Polynomial.X_dvd_iff.mpr h0).trans hdvd)
    · by_contra hlt
      have hz : q.natDegree = 0 := by omega
      have h1 : q = 1 := by
        first
          | exact hmon.natDegree_eq_zero_iff_eq_one.mp hz
          | exact Polynomial.eq_one_of_monic_natDegree_zero hmon hz
      apply hirr.not_isUnit
      rw [h1]
      exact isUnit_one
    · have h := Polynomial.natDegree_le_of_dvd hdvd hp0
      rwa [monicOf_natDegree] at h
  have P : ∀ c : Fin N → K, (monicOf c).coeff 0 ≠ 0 →
      (normalizedFactors (monicOf c)).prod = monicOf c := by
    intro c hc
    have hp0 : monicOf c ≠ 0 := (monicOf_monic c).ne_zero
    have hm := (L1 _ (fun q hq => ⟨(F c hc q hq).1, (F c hc q hq).2.1, (F c hc q hq).2.2.1⟩)).1
    apply Polynomial.eq_of_monic_of_associated hm (monicOf_monic c)
    first
      | exact prod_normalizedFactors hp0
      | exact normalizedFactors_prod hp0
      | exact UniqueFactorizationMonoid.prod_normalizedFactors hp0
      | exact UniqueFactorizationMonoid.normalizedFactors_prod hp0
  set Irr : ℕ → Finset K[X] := fun d => ((Finset.univ : Finset (Fin d → K)).filter
    (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).image monicOf with hIrrdef
  have hIrr : ∀ (d : ℕ) (q : K[X]), q ∈ Irr d ↔
      q.Monic ∧ q.natDegree = d ∧ Irreducible q ∧ q.coeff 0 ≠ 0 := by
    intro d q
    simp only [Irr, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, ⟨h1, h2⟩, rfl⟩
      exact ⟨monicOf_monic c, monicOf_natDegree c, h1, h2⟩
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun i => q.coeff i, ?_, monicOf_coeffs h1 h2⟩
      rw [monicOf_coeffs h1 h2]
      exact ⟨h3, h4⟩
  set U : ((d : ℕ) → d ∈ Finset.Icc 1 N → Finset K[X]) → Finset K[X] :=
    fun f => (Finset.Icc 1 N).attach.biUnion (fun x => f x.1 x.2) with hUdef
  have hmemT : ∀ (f : (d : ℕ) → d ∈ Finset.Icc 1 N → Finset K[X]) (q : K[X]),
      q ∈ U f ↔ ∃ d, ∃ hd : d ∈ Finset.Icc 1 N, q ∈ f d hd := by
    intro f q
    simp only [U]
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨x, _, hx⟩
      exact ⟨x.1, x.2, hx⟩
    · rintro ⟨d, hd, hq⟩
      exact ⟨⟨d, hd⟩, Finset.mem_attach _ _, hq⟩
  have key : ∀ f : ((d : ℕ) → d ∈ Finset.Icc 1 N → Finset K[X]),
      (∀ d (hd : d ∈ Finset.Icc 1 N), f d hd ∈ (Irr d).powersetCard (n d)) →
      (U f).val.prod.Monic ∧ normalizedFactors (U f).val.prod = (U f).val ∧
        (U f).val.prod.natDegree = N ∧ (U f).val.prod.coeff 0 ≠ 0 ∧
        ∀ d (hd : d ∈ Finset.Icc 1 N), (U f).filter (fun q => q.natDegree = d) = f d hd := by
    intro f hf
    have hprop : ∀ d (hd : d ∈ Finset.Icc 1 N) q, q ∈ f d hd →
        q.Monic ∧ q.natDegree = d ∧ Irreducible q ∧ q.coeff 0 ≠ 0 := fun d hd q hq =>
      (hIrr d q).mp ((Finset.mem_powersetCard.mp (hf d hd)).1 hq)
    have hfib : ∀ d (hd : d ∈ Finset.Icc 1 N),
        (U f).filter (fun q => q.natDegree = d) = f d hd := by
      intro d hd
      ext q
      rw [Finset.mem_filter, hmemT]
      constructor
      · rintro ⟨⟨d', hd', hq⟩, hdeg⟩
        have hdd : d' = d := (hprop d' hd' q hq).2.1.symm.trans hdeg
        subst hdd
        exact hq
      · intro hq
        exact ⟨⟨d, hd, hq⟩, (hprop d hd q hq).2.1⟩
    have hall : ∀ q ∈ (U f).val, q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0 := by
      intro q hq
      obtain ⟨d, hd, hq'⟩ := (hmemT f q).mp hq
      obtain ⟨h1, _, h3, h4⟩ := hprop d hd q hq'
      exact ⟨h1, h3, h4⟩
    obtain ⟨hmon, hnf, hdeg, hc0⟩ := L1 _ hall
    refine ⟨hmon, hnf, ?_, hc0, hfib⟩
    rw [hdeg, ← hN]
    have hmaps : ∀ q ∈ U f, q.natDegree ∈ Finset.Icc 1 N := by
      intro q hq
      obtain ⟨d, hd, hq'⟩ := (hmemT f q).mp hq
      rw [(hprop d hd q hq').2.1]
      exact hd
    have hsum : ((U f).val.map Polynomial.natDegree).sum = ∑ q ∈ U f, q.natDegree := rfl
    rw [hsum, ← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [hfib d hd, Finset.sum_const_nat (fun q hq => (hprop d hd q hq).2.1),
      (Finset.mem_powersetCard.mp (hf d hd)).2, mul_comm]
  have hTval : ∀ c : Fin N → K, Squarefree (monicOf c) →
      (normalizedFactors (monicOf c)).toFinset.val = normalizedFactors (monicOf c) := by
    intro c hsq
    rw [Multiset.toFinset_val]
    exact Multiset.dedup_eq_self.mpr
      ((squarefree_iff_nodup_normalizedFactors (monicOf_monic c).ne_zero).mp hsq)
  refine (Finset.card_nbij' (t := (Finset.Icc 1 N).pi (fun d => (Irr d).powersetCard (n d)))
    (fun (c : Fin N → K) (d : ℕ) (_ : d ∈ Finset.Icc 1 N) =>
      (normalizedFactors (monicOf c)).toFinset.filter (fun q => q.natDegree = d))
    (fun (f : (d : ℕ) → d ∈ Finset.Icc 1 N → Finset K[X]) (k : Fin N) => ((U f).val.prod).coeff k)
    ?_ ?_ ?_ ?_).trans ?_
  · intro c hc
    rw [Finset.mem_coe, Finset.filter_congr_decidable, Finset.mem_filter] at hc
    obtain ⟨_, hsq, hc0, hcount⟩ := hc
    rw [Finset.mem_coe, Finset.mem_pi]
    intro d hd
    rw [Finset.mem_powersetCard]
    constructor
    · intro q hq
      rw [Finset.mem_filter, Multiset.mem_toFinset] at hq
      obtain ⟨h1, h2, h3, _, _⟩ := F c hc0 q hq.1
      exact (hIrr d q).mpr ⟨h1, hq.2, h2, h3⟩
    · have h := L2 (normalizedFactors (monicOf c)).toFinset d
      rw [hTval c hsq] at h
      rw [← h]
      exact hcount d hd
  · intro f hf
    rw [Finset.mem_coe, Finset.mem_pi] at hf
    obtain ⟨hmon, hnf, hdeg, hc0, hfib⟩ := key f hf
    have hp := monicOf_coeffs hmon hdeg
    rw [Finset.mem_coe, Finset.filter_congr_decidable, Finset.mem_filter]
    dsimp only
    rw [hp]
    refine ⟨Finset.mem_univ _, (squarefree_iff_nodup_normalizedFactors hmon.ne_zero).mpr ?_, hc0, ?_⟩
    · rw [hnf]
      exact (U f).nodup
    · intro d hd
      rw [hnf, L2, hfib d hd]
      exact (Finset.mem_powersetCard.mp (hf d hd)).2
  · intro c hc
    rw [Finset.mem_coe, Finset.filter_congr_decidable, Finset.mem_filter] at hc
    obtain ⟨_, hsq, hc0, _⟩ := hc
    have hU : U (fun d _ => (normalizedFactors (monicOf c)).toFinset.filter
        (fun q => q.natDegree = d)) = (normalizedFactors (monicOf c)).toFinset := by
      ext q
      simp only [U]
      rw [Finset.mem_biUnion]
      constructor
      · rintro ⟨x, _, hq⟩
        exact (Finset.mem_filter.mp hq).1
      · intro hq
        obtain ⟨_, _, _, h4, h5⟩ := F c hc0 q (Multiset.mem_toFinset.mp hq)
        exact ⟨⟨q.natDegree, Finset.mem_Icc.mpr ⟨h4, h5⟩⟩, Finset.mem_attach _ _,
          Finset.mem_filter.mpr ⟨hq, rfl⟩⟩
    funext k
    dsimp only
    rw [hU, hTval c hsq, P c hc0, monicOf_coeff]
  · intro f hf
    rw [Finset.mem_coe, Finset.mem_pi] at hf
    obtain ⟨hmon, hnf, hdeg, _, hfib⟩ := key f hf
    funext d hd
    dsimp only
    rw [monicOf_coeffs hmon hdeg, hnf, Finset.val_toFinset, hfib d hd]
  · rw [Finset.card_pi]
    refine Finset.prod_congr rfl ?_
    intro d _
    rw [Finset.card_powersetCard]
    simp only [Irr]
    rw [Finset.card_image_of_injective _ monicOf_injective]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section -- merged from Formalism.PadicSubsetSums.StableGradedCounts.BaseChangeIwahoriFactorization
namespace Formalism.IrreducibleCountingLemmas.Z

theorem isUnit_sub_of_mem_maximalIdeal {O : Type} [CommRing O] [IsLocalRing O] {a m : O}
    (ha : IsUnit a) (hm : m ∈ IsLocalRing.maximalIdeal O) : IsUnit (a - m) := by
  first | exact Bl.FirstBlockLemmaG.goal1 .. | (apply Bl.FirstBlockLemmaG.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaG.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaG.goal1 <;> assumption) | (intros; apply @Bl.FirstBlockLemmaG.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaG.goal1 <;> first | assumption | infer_instance) | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a m ha hm | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a m ha | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a m | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› | exact @Bl.FirstBlockLemmaG.goal1 O

theorem iwahori_factorization_exists (O : Type) [CommRing O] [IsLocalRing O] (U L : Ideal O)
    (hL : L ≤ IsLocalRing.maximalIdeal O) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), (∀ i, IsUnit (g i i)) →
    (∀ i j, i < j → g i j ∈ U) → (∀ i j, j < i → g i j ∈ L) →
    ∃ (x y : Matrix (Fin n) (Fin n) O) (δ : Fin n → O),
      (∀ i j, g i j = ∑ k, x i k * δ k * y k j) ∧
      (∀ i, x i i = 1) ∧ (∀ i j, j < i → x i j = 0) ∧ (∀ i j, i < j → x i j ∈ U) ∧
      (∀ i, IsUnit (δ i)) ∧ (∀ i, δ i - g i i ∈ U * L) ∧
      (∀ i, y i i = 1) ∧ (∀ i j, i < j → y i j = 0) ∧ (∀ i j, j < i → y i j ∈ L) := by
  first | exact Bl.SecondBlockLemmaB.goal1 .. | (apply Bl.SecondBlockLemmaB.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaB.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaB.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaB.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaB.goal1 <;> first | assumption | infer_instance) | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n g ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n g ‹_› ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n g ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n g | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O

end Formalism.IrreducibleCountingLemmas.Z
end

section -- merged from Formalism.PadicSubsetSums.StableGradedCounts.IRRCentralIdemOrthogonal
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem central_idempotents_orthogonal : CentralIdemOrthogonal := by
  intro G V W _ _ _ _ _ _ _ _ _ _ ρ σ hρ hσ hne
  obtain ⟨μ, h1, h2⟩ := centralIdem_mul ρ σ hσ
  have hirrρ : ρ.IsIrreducible := isIrreducible_of ρ hρ
  have hirrσ : σ.IsIrreducible := isIrreducible_of σ hσ
  have hc0 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  have hno : ¬ Nonempty (Representation.Equiv ρ σ) := by
    rintro ⟨φ⟩
    exact hne ⟨φ.toLinearEquiv, fun g x => LinearMap.congr_fun (φ.isIntertwining' g) x⟩
  have horth := Representation.char_orthonormal σ ρ
  rw [if_neg hno, Nat.card_eq_fintype_card] at horth
  have h3 : ∑ g, ρ.character g⁻¹ * σ.character g = 0 := by
    have e : ∑ g, ρ.character g⁻¹ * σ.character g = ∑ g, σ.character g * ρ.character g⁻¹ :=
      Finset.sum_congr rfl fun g _ => mul_comm _ _
    rw [e]
    simpa using horth
  rw [h3] at h1
  have hd : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  have hμ : μ = 0 := (mul_eq_zero.mp h1).resolve_right hd
  rw [h2, hμ, mul_zero, zero_smul]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section -- merged from Formalism.PadicSubsetSums.StableGradedCounts.DegreeOneSplit
open scoped NumberField

namespace Formalism.IrreducibleCountingLemmas.Z

theorem degree_one_split : DegreeOneSplit := by
  intro F E _ _ _ _ _ h2 P _ hP hf he
  classical
  set p : Ideal (𝓞 F) := P.under (𝓞 F) with hp
  have hfin : (p.primesOver (𝓞 E)).Finite := Algebra.QuasiFinite.finite_primesOver p
  let _ : Fintype (p.primesOver (𝓞 E)) := hfin.fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  have hrank : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← h2]
    exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
  rw [hrank] at hsum
  have hf1 : P.inertiaDeg (𝓞 F) = 1 := by
    have := Ideal.inertiaDeg_tower (R := ℤ) p P
    rw [hf] at this
    exact Nat.eq_one_of_mul_eq_one_left this.symm
  have hPmem : P ∈ p.primesOver (𝓞 E) := ⟨inferInstance, ⟨rfl⟩⟩
  have hpos : ∀ q : p.primesOver (𝓞 E), 1 ≤ q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) := by
    intro q
    have : q.1.IsPrime := q.2.1
    exact Nat.mul_pos (Ideal.ramificationIdx_pos (R := 𝓞 F) q.1) (Ideal.inertiaDeg_pos q.1 (𝓞 F))
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨P, hPmem⟩ : p.primesOver (𝓞 E)))] at hsum
  simp only [he, hf1, mul_one] at hsum
  have hrest : ∑ q ∈ Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E)),
      q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) = 1 := by omega
  have hle : (Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E))).card ≤ 1 := by
    calc _ = ∑ q ∈ Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E)), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun q _ => hpos q
      _ = 1 := hrest
  have hge : (Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E))).card ≠ 0 := by
    intro h0
    rw [Finset.card_eq_zero] at h0
    rw [h0] at hrest
    simp at hrest
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hle hge
  have key : Fintype.card { x // x ∈ p.primesOver (𝓞 E) } = 2 := by omega
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact key

end Formalism.IrreducibleCountingLemmas.Z
end
