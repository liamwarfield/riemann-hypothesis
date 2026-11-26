module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomSum

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwThetaEx
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem thetaEx_split {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (t : Fin n → kˣ) :
    ∃ c : kˣ, ∀ s : Fin n → kˣ, (s = 1 ∨ s = t) → ∀ i j : Fin n, i ≤ j →
      valuation k ((s i * c ^ (n - i) : kˣ) : k) ≤ valuation k ((s j * c ^ (n - j) : kˣ) : k) := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨1, fun _ _ i => h.elim i⟩
  obtain ⟨p, hp⟩ := Finite.exists_min (fun p : Fin n × Fin n => valuation k ((t p.2 * (t p.1)⁻¹ : kˣ) : k))
  set c : kˣ := t p.2 * (t p.1)⁻¹ with hc
  have h1 : valuation k (c : k) ≤ 1 := by simpa using hp (p.1, p.1)
  refine ⟨c, fun s hs i j hij => ?_⟩
  rcases hij.eq_or_lt with rfl | hlt
  · exact le_rfl
  have h2 : valuation k (s i : k) * valuation k (c : k) ≤ valuation k (s j : k) := by
    rcases hs with rfl | rfl
    · simpa using h1
    · have := mul_le_mul_right (hp (i, j)) (valuation k (s i : k))
      refine this.trans (le_of_eq ?_)
      rw [← map_mul, ← Units.val_mul]
      congr 2
      simp
  have hj := j.2
  have hlt' : (i : ℕ) < j := hlt
  have e : n - (i : ℕ) = 1 + ((n - j) + (j - i - 1)) := by omega
  rw [e]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, pow_add, pow_one]
  rw [← mul_assoc]
  exact mul_le_mul' h2 (mul_le_of_le_one_right' (pow_le_one' h1 _))

theorem UpperTheory.V.AlgebraTools.thetaEx :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M), IsUnit (resCard k : A) → ∃! θ : (Fin n → kˣ) →* (Module.End A (fixd ρ (iwC k n C)))ˣ, ∀ t, Dom t → (θ t : Module.End A (fixd ρ (iwC k n C))) = hk ρ (iwC k n C) (diagT k (Fin n) t) := by
  intro k _ _ _ _ n C A M _ _ _ ρ hq
  obtain ⟨hmul, hunit, -⟩ := domMul k n C A M ρ
  let P : Submonoid (Fin n → kˣ) :=
    { carrier := {t | Dom t}
      one_mem' := dom_one
      mul_mem' := fun {a b} ha hb i j hij => by
        simp only [Pi.mul_apply, Units.val_mul, map_mul]
        exact mul_le_mul' (ha i j hij) (hb i j hij) }
  refine monoidExt (Fin n → kˣ) _ P (fun t => hk ρ (iwC k n C) (diagT k (Fin n) t)) (fun t => ?_) ?_
    (fun a ha b hb => (hmul a b ha hb).symm) (fun a ha => hunit hq a ha)
  · obtain ⟨c, hc⟩ := thetaEx_split t
    refine ⟨t * (fun i : Fin n => c ^ (n - (i : ℕ))), hc t (Or.inr rfl), (1 : Fin n → kˣ) * (fun i : Fin n => c ^ (n - (i : ℕ))), hc 1 (Or.inl rfl), ?_⟩
    simp
  · have h := hmul 1 1 dom_one dom_one
    rw [mul_one] at h
    exact (hunit hq 1 dom_one).mul_left_cancel (h.trans (mul_one _).symm)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwUnitHk
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section

variable {A G : Type} [CommRing A] [Group G] {I : Subgroup G}

private theorem unitHk_apply (hI : HeckePair I) (x : G) (v : fixd (permRep A I) I) :
    (hk (permRep A I) I x v : MonoidAlgebra A (G ⧸ I)) =
      ∑ᶠ q : MulAction.orbit I (x : G ⧸ I), permRep A I (q : G ⧸ I).out v := by
  have hx : FinOrb I I x := hI x
  have e := (hkApply A G _ (permRep A I) I I x hx).1 v
  change ((hk2 (permRep A I) I I x v : fixd (permRep A I) I) : MonoidAlgebra A (G ⧸ I)) = _
  rw [e]
  haveI : Fintype (MulAction.orbit I (x : G ⧸ I)) := Set.Finite.fintype hx
  unfold dc
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

private noncomputable def unitHk_e (A : Type) {G : Type} [CommRing A] [Group G] (I : Subgroup G) :
    fixd (permRep A I) I :=
  ⟨MonoidAlgebra.single ((1 : G) : G ⧸ I) 1, fun u hu => by
    rw [Representation.ofMulAction_single]
    congr 1
    exact QuotientGroup.eq.2 (by simpa using hu)⟩

private noncomputable def unitHk_phi (v : fixd (permRep A I) I) :
    MonoidAlgebra A (G ⧸ I) →ₗ[A] MonoidAlgebra A (G ⧸ I) :=
  (MonoidAlgebra.basis (G ⧸ I) A).constr A fun q => permRep A I q.out v

private theorem unitHk_phi_single (v : fixd (permRep A I) I) (g : G) :
    unitHk_phi v (MonoidAlgebra.single (g : G ⧸ I) 1) = permRep A I g v := by
  unfold unitHk_phi
  have hb : MonoidAlgebra.single (g : G ⧸ I) (1 : A) = MonoidAlgebra.basis (G ⧸ I) A (g : G ⧸ I) := by simp
  rw [hb, Module.Basis.constr_basis]
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul I g
  rw [hh, map_mul, Module.End.mul_apply, v.2 h h.2]

private theorem unitHk_phi_comm (v : fixd (permRep A I) I) (g : G) (w : MonoidAlgebra A (G ⧸ I)) :
    unitHk_phi v (permRep A I g w) = permRep A I g (unitHk_phi v w) := by
  have key : unitHk_phi v ∘ₗ permRep A I g = permRep A I g ∘ₗ unitHk_phi v := by
    refine (MonoidAlgebra.basis (G ⧸ I) A).ext fun q => ?_
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    have hb : MonoidAlgebra.basis (G ⧸ I) A (h : G ⧸ I) = MonoidAlgebra.single (h : G ⧸ I) 1 := by simp
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hb]
    have hs : permRep A I g (MonoidAlgebra.single (h : G ⧸ I) 1) =
        MonoidAlgebra.single ((g * h : G) : G ⧸ I) 1 := Representation.ofMulAction_single _ _ _
    rw [hs, unitHk_phi_single, unitHk_phi_single, map_mul, Module.End.mul_apply]
  exact LinearMap.congr_fun key w

private theorem unitHk_alg_comm (hI : HeckePair I) (v : fixd (permRep A I) I) (T : Module.End A (fixd (permRep A I) I))
    (hT : T ∈ HkAlg A I) : ∀ w w' : fixd (permRep A I) I, unitHk_phi v w = w' → unitHk_phi v (T w) = T w' := by
  unfold HkAlg at hT
  induction hT using Algebra.adjoin_induction with
  | mem T hT =>
    obtain ⟨x, rfl⟩ := hT
    intro w w' hw
    haveI : Fintype (MulAction.orbit I (x : G ⧸ I)) := Set.Finite.fintype (hI x)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [unitHk_apply hI, unitHk_apply hI, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, ← hw]
    simp only [unitHk_phi_comm]
  | algebraMap r =>
    intro w w' hw
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
      Module.End.one_apply, Submodule.coe_smul, Submodule.coe_smul, map_smul, hw]
  | add T1 T2 _ _ h1 h2 =>
    intro w w' hw
    rw [LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, Submodule.coe_add, map_add (f := _), h1 w w' hw, h2 w w' hw]
  | mul T1 T2 _ _ h1 h2 =>
    intro w w' hw
    rw [Module.End.mul_apply, Module.End.mul_apply]
    exact h1 _ _ (h2 w w' hw)

private theorem unitHk_inj (hI : HeckePair I) (T : Module.End A (fixd (permRep A I) I))
    (hT : T ∈ HkAlg A I) (h : T (unitHk_e A I) = unitHk_e A I) : T = 1 := by
  apply LinearMap.ext
  intro v
  have he : unitHk_phi v (unitHk_e A I : MonoidAlgebra A (G ⧸ I)) = v := by
    show unitHk_phi v (MonoidAlgebra.single ((1 : G) : G ⧸ I) 1) = v
    rw [unitHk_phi_single, map_one, Module.End.one_apply]
  have key := unitHk_alg_comm hI v T hT (unitHk_e A I) v he
  rw [h, he] at key
  rw [Module.End.one_apply]
  exact Subtype.ext key.symm

open Classical in
private theorem unitHk_coeff (hI : HeckePair I) (x : G) (p : G ⧸ I) :
    (hk (permRep A I) I x (unitHk_e A I) : MonoidAlgebra A (G ⧸ I)).coeff p =
      if p ∈ MulAction.orbit I (x : G ⧸ I) then 1 else 0 := by
  haveI : Fintype (MulAction.orbit I (x : G ⧸ I)) := Set.Finite.fintype (hI x)
  rw [unitHk_apply hI, finsum_eq_sum_of_fintype]
  have hs : ∀ q : MulAction.orbit I (x : G ⧸ I),
      permRep A I (q : G ⧸ I).out (unitHk_e A I : MonoidAlgebra A (G ⧸ I)) = MonoidAlgebra.single (q : G ⧸ I) 1 := by
    intro q
    have h1 : permRep A I (q : G ⧸ I).out (MonoidAlgebra.single ((1 : G) : G ⧸ I) (1 : A)) =
        MonoidAlgebra.single ((q : G ⧸ I).out • ((1 : G) : G ⧸ I)) 1 := Representation.ofMulAction_single _ _ _
    refine h1.trans ?_
    congr 1
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.out_eq']
  simp only [hs, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finsetSum_apply, Finsupp.single_apply]
  by_cases hp : p ∈ MulAction.orbit I (x : G ⧸ I)
  · rw [if_pos hp, Finset.sum_eq_single ⟨p, hp⟩]
    · simp
    · intro q _ hq
      rw [if_neg]
      intro e
      exact hq (Subtype.ext e)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hp]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    intro e
    exact hp (e ▸ q.2)

private theorem unitHk_surj (hI : HeckePair I) (v : fixd (permRep A I) I) :
    ∃ T ∈ HkAlg A I, T (unitHk_e A I) = v := by
  classical
  suffices H : ∀ n (v : fixd (permRep A I) I),
      ((v : MonoidAlgebra A (G ⧸ I)).coeff.support.card = n) → ∃ T ∈ HkAlg A I, T (unitHk_e A I) = v from
    H _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v hv
  by_cases h0 : (v : MonoidAlgebra A (G ⧸ I)).coeff.support = ∅
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [LinearMap.zero_apply]
    apply Subtype.ext
    apply MonoidAlgebra.ext
    rw [Finsupp.support_eq_empty] at h0
    rw [h0, Submodule.coe_zero, MonoidAlgebra.coeff_zero]
  · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.2 h0
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
    set c := (v : MonoidAlgebra A (G ⧸ I)).coeff (x : G ⧸ I) with hc
    have hT1 : c • hk (permRep A I) I x ∈ HkAlg A I :=
      Subalgebra.smul_mem _
        (show hk (permRep A I) I x ∈ HkAlg A I from Algebra.subset_adjoin (Set.mem_range_self x)) c
    have inv : ∀ q ∈ MulAction.orbit I (x : G ⧸ I), (v : MonoidAlgebra A (G ⧸ I)).coeff q = c := by
      rintro q ⟨u, rfl⟩
      have hv' : permRep A I (u : G) (v : MonoidAlgebra A (G ⧸ I)) = v := v.2 u u.2
      show (v : MonoidAlgebra A (G ⧸ I)).coeff ((u : G) • (x : G ⧸ I)) = c
      calc (v : MonoidAlgebra A (G ⧸ I)).coeff ((u : G) • (x : G ⧸ I))
          = (permRep A I (u : G) (v : MonoidAlgebra A (G ⧸ I))).coeff ((u : G) • (x : G ⧸ I)) := by rw [hv']
        _ = (v : MonoidAlgebra A (G ⧸ I)).coeff ((u : G)⁻¹ • (u : G) • (x : G ⧸ I)) :=
          Representation.ofMulAction_apply _ _ _
        _ = c := by rw [inv_smul_smul]
    set v' : fixd (permRep A I) I := v - c • hk (permRep A I) I x (unitHk_e A I) with hv'
    have hco : ∀ q, (v' : MonoidAlgebra A (G ⧸ I)).coeff q =
        (v : MonoidAlgebra A (G ⧸ I)).coeff q - c * (if q ∈ MulAction.orbit I (x : G ⧸ I) then 1 else 0) := by
      intro q
      rw [← unitHk_coeff hI x q, hv']
      simp
    have hsub : (v' : MonoidAlgebra A (G ⧸ I)).coeff.support ⊂ (v : MonoidAlgebra A (G ⧸ I)).coeff.support := by
      refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨(x : G ⧸ I), hp, ?_⟩
      · intro q hq
        rw [Finsupp.mem_support_iff] at hq ⊢
        intro hq0
        apply hq
        rw [hco]
        by_cases ho : q ∈ MulAction.orbit I (x : G ⧸ I)
        · rw [inv q ho] at hq0
          exact absurd hq0 (Finsupp.mem_support_iff.1 hp)
        · rw [if_neg ho, hq0]
          simp
      · rw [Finsupp.mem_support_iff, not_not, hco, if_pos (MulAction.mem_orbit_self _)]
        simp [hc]
    obtain ⟨T', hT', hTe⟩ := ih _ (hv ▸ Finset.card_lt_card hsub) v' rfl
    refine ⟨T' + c • hk (permRep A I) I x, Subalgebra.add_mem _ hT' hT1, ?_⟩
    rw [LinearMap.add_apply, hTe, hv', LinearMap.smul_apply, sub_add_cancel]

private theorem unitHk_unit (hI : HeckePair I) (T : HkAlg A I)
    (h : IsUnit (T : Module.End A (fixd (permRep A I) I))) : IsUnit T := by
  obtain ⟨U, hU⟩ := h
  obtain ⟨T', hT', hT'e⟩ := unitHk_surj hI (((U⁻¹ : (Module.End A (fixd (permRep A I) I))ˣ) :
    Module.End A (fixd (permRep A I) I)) (unitHk_e A I))
  have h1 : (T : Module.End A (fixd (permRep A I) I)) * T' = 1 := by
    refine unitHk_inj hI _ (Subalgebra.mul_mem _ T.2 hT') ?_
    rw [Module.End.mul_apply, hT'e, ← hU, ← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
  have h2 : T' = ((U⁻¹ : (Module.End A (fixd (permRep A I) I))ˣ) : Module.End A (fixd (permRep A I) I)) := by
    calc T' = ((U⁻¹ : (Module.End A (fixd (permRep A I) I))ˣ) : Module.End A (fixd (permRep A I) I)) *
          ((U : Module.End A (fixd (permRep A I) I)) * T') := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [hU, h1, mul_one]
  refine ⟨⟨T, ⟨T', hT'⟩, Subtype.ext h1, Subtype.ext ?_⟩, rfl⟩
  show T' * (T : Module.End A (fixd (permRep A I) I)) = 1
  rw [h2, ← hU, Units.inv_mul]

end

theorem UpperTheory.V.AlgebraTools.unitHk :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A : Type) [CommRing A], IsUnit (resCard k : A) → (∀ w : Equiv.Perm (Fin n), IsUnit (hT A (iwC k n ⊤) (pm k n w))) ∧ ∀ t : Fin n → kˣ, Dom t → IsUnit (hT A (iwC k n ⊤) (diagT k (Fin n) t)) := by
  intro k _ _ _ _ n A _ hq
  have hI := (heckePairIwC k n ⊤).1
  exact ⟨fun w => unitHk_unit hI _ (permUnit k n ⊤ A _ _ w hq),
    fun t ht => unitHk_unit hI _ ((domMul k n ⊤ A _ _).2.1 hq t ht)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomCard
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem unif_lt {x : kˣ} (hx : IsUnif x) (y : k) :
    valuation k y < 1 ↔ valuation k y ≤ valuation k (x : k) := by
  obtain ⟨p, hp, e⟩ := hx
  have hI := Valuation.integer.integers (valuation k)
  have h1 : valuation k (x : k) < 1 := by
    rw [← e]
    refine lt_of_le_of_ne p.2 fun h => hp.not_isUnit (hI.isUnit_iff_valuation_eq_one.2 h)
  refine ⟨fun h => ?_, fun h => h.trans_lt h1⟩
  let z : 𝒪[k] := ⟨y, h.le⟩
  have hz : z ∈ IsLocalRing.maximalIdeal 𝒪[k] := fun hu => h.ne (hI.isUnit_iff_valuation_eq_one.1 hu)
  rw [hp.maximalIdeal_eq, Ideal.mem_span_singleton] at hz
  rw [← e]
  exact hI.le_of_dvd hz

private def Bd (x : kˣ) (g : GL (Fin n) k) : Prop :=
  ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k (x : k) ^ (if j < i then 1 else 0 : ℤ)

private theorem mem_iw_iff {x : kˣ} (hx : IsUnif x) (g : GL (Fin n) k) :
    g ∈ iwahori k (Fin n) ↔ Bd x g ∧ Bd x g⁻¹ := by
  have h1 : valuation k (x : k) ≤ 1 := ((unif_lt hx x).2 le_rfl).le
  have A : ∀ g ∈ iwahori k (Fin n), Bd x g := by
    intro g hg i j
    have hg' := mem_iwahori.1 hg
    split_ifs with h
    · simpa using (unif_lt hx _).1 (hg'.2 i j h)
    · rw [zpow_zero]
      exact ((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg'.1).1 i j
  have B : ∀ g : GL (Fin n) k, Bd x g → ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro g hg i j
    have := hg i j
    split_ifs at this with h
    · exact le_trans (by simpa using this) h1
    · simpa using this
  refine ⟨fun hg => ⟨A g hg, A _ (inv_mem hg)⟩, fun ⟨ha, hb⟩ => mem_iwahori.2
    ⟨(GlobalTheory.SplitFlip.mem_KO_iff g).2 ⟨B _ ha, B _ hb⟩, fun i j h => (unif_lt hx _).2 ?_⟩⟩
  simpa [h] using ha i j

private theorem conj_entry (x : kˣ) (a : Fin n → ℤ) (w : Equiv.Perm (Fin n)) (g : GL (Fin n) k) (i j : Fin n) :
    ((pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (w i) (w j) =
      (x : k) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) k) i j := by
  have e : pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹ =
      pm k n w * (pw x a * g * diagT k (Fin n) (fun i => x ^ a i)⁻¹) * pm k n w⁻¹ := by
    rw [map_inv, map_inv, pw]; group
  rw [e]
  simp only [Units.val_mul, pw, val_diagT]
  generalize hM : (diagonal (fun i => ((x ^ a i : kˣ) : k)) * (g : Matrix (Fin n) (Fin n) k) *
    diagonal fun i => (((fun i => x ^ a i)⁻¹ i : kˣ) : k)) = M
  have hM' : M i j = (x : k) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) k) i j := by
    rw [← hM, mul_diagonal, diagonal_mul, zpow_sub₀ x.ne_zero]
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val]
    ring
  rw [← hM']
  simp only [Matrix.mul_apply, pm_apply]
  simp

private theorem bd_conj (x : kˣ) (a : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (hw : ∀ i j, (if w j < w i then 1 else 0 : ℤ) = (a i - a j) + (if j < i then 1 else 0)) (g : GL (Fin n) k) :
    Bd x (pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹) ↔ Bd x g := by
  have h0 : 0 < valuation k (x : k) := zero_lt_iff.2 (by simp)
  unfold Bd
  rw [w.surjective.forall₂]
  refine forall₂_congr fun i j => ?_
  rw [conj_entry, hw, map_mul, map_zpow₀, zpow_add₀ h0.ne', mul_le_mul_iff_right₀ (zpow_pos h0 _)]

private theorem exists_rot (n m : ℕ) (hm : m ≤ n) : ∃ w : Equiv.Perm (Fin n),
    ∀ i j, (if w j < w i then 1 else 0 : ℤ) = (fund n m i - fund n m j) + (if j < i then 1 else 0) := by
  let f : Fin n → Fin n := fun i => ⟨if (i : ℕ) < m then n - m + i else i - m, by
    have := i.2; split_ifs <;> omega⟩
  have hf : Function.Injective f := by
    intro i j h
    have h' := congrArg Fin.val h
    have := i.2; have := j.2
    simp only [f] at h'
    ext
    split_ifs at h' <;> omega
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), fun i j => ?_⟩
  have := i.2; have := j.2
  simp only [Equiv.ofBijective_apply, f, fund, Fin.lt_def]
  split_ifs <;> omega

private theorem dom_zpow {x : kˣ} (hx : IsUnif x) {a : Fin n → ℤ} (ha : Antitone a) : Dom fun i => x ^ a i := by
  intro i j hij
  have h0 : 0 < valuation k (x : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 x.ne_zero)
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact (zpow_le_zpow_iff_right_of_lt_one₀ h0 ((unif_lt hx x).2 le_rfl)).2 (ha hij)

private theorem exists_cut (a : Fin n → ℤ) (ha : Antitone a) (c : ℤ) :
    ∃ m ≤ n, ∀ i : Fin n, (i : ℕ) < m ↔ c < a i := by
  classical
  have hex : ∃ m : ℕ, ∀ i : Fin n, m ≤ (i : ℕ) → a i ≤ c := ⟨n, fun i hi => absurd i.2 (not_lt.2 hi)⟩
  refine ⟨Nat.find hex, Nat.find_min' hex fun i hi => absurd i.2 (not_lt.2 hi), fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · have := Nat.find_min hex hi
    push Not at this
    obtain ⟨j, hj, hc⟩ := this
    exact hc.trans_le (ha (Fin.le_def.2 hj))
  · by_contra h
    exact absurd (Nat.find_spec hex i (not_lt.1 h)) (not_le.2 hi)

private theorem const_central (y : kˣ) : diagT k (Fin n) (fun _ => y) ∈ Subgroup.center (GL (Fin n) k) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  simp only [Units.val_mul, val_diagT, mul_diagonal, diagonal_mul, mul_comm]

private theorem rot_norm (C : Subgroup 𝓀[k]ˣ) {x : kˣ} (hx : IsUnif x) (a : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (hw : ∀ i j, (if w j < w i then 1 else 0 : ℤ) = (a i - a j) + (if j < i then 1 else 0)) :
    pm k n w * pw x a ∈ Subgroup.normalizer (iwC k n C : Set (GL (Fin n) k)) := by
  refine Subgroup.mem_normalizer_iff.2 fun g => ?_
  have e : (pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹)⁻¹ =
      pm k n w * pw x a * g⁻¹ * (pm k n w * pw x a)⁻¹ := by group
  rw [(memIwC k n C).1, (memIwC k n C).1, mem_iw_iff hx, mem_iw_iff hx, e, bd_conj x _ w hw, bd_conj x _ w hw]
  refine and_congr Iff.rfl ?_
  conv_rhs => rw [w.surjective.forall]
  simp only [conj_entry, sub_self, zpow_zero, one_mul]

private theorem invLen_inv (w : Equiv.Perm (Fin n)) : invLen w⁻¹ = invLen w := by
  unfold invLen
  refine Finset.card_bij' (fun p _ => (w⁻¹ p.2, w⁻¹ p.1)) (fun p _ => (w p.2, w p.1)) ?_ ?_ ?_ ?_
  · intro p hp
    simpa [and_comm] using hp
  · intro p hp
    simpa [and_comm] using hp
  · intro p _
    simp
  · intro p _
    simp

private theorem invLen_eq (a : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (hw : ∀ i j, (if w j < w i then 1 else 0 : ℤ) = (a i - a j) + (if j < i then 1 else 0)) :
    invLen w = ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), (a p.1 - a p.2).toNat := by
  rw [invLen, ← Finset.filter_filter, Finset.card_filter]
  refine Finset.sum_congr rfl fun p hp => ?_
  have h := hw p.1 p.2
  rw [if_neg (lt_asymm (Finset.mem_filter.1 hp).2), add_zero] at h
  rw [← h]
  split_ifs <;> rfl

private theorem hk_triv {G : Type} [Group G] (I : Subgroup G) (hI : HeckePair I) (x : G) :
    hk (Representation.trivial ℤ G ℤ) I x = ((MulAction.orbit I (x : G ⧸ I)).ncard : Module.End ℤ _) := by
  have : Finite (MulAction.orbit I (x : G ⧸ I)) := hI x
  have := Fintype.ofFinite (MulAction.orbit I (x : G ⧸ I))
  ext v
  rw [hk, (hkApply ℤ G _ (Representation.trivial ℤ G ℤ) I I x (hI x)).1 v, dc, finsum_eq_sum_of_fintype,
    LinearMap.sum_apply, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  simp

private theorem endCast_inj {G : Type} [Group G] (I : Subgroup G) {a b : ℕ}
    (h : (a : Module.End ℤ (fixd (Representation.trivial ℤ G ℤ) I)) = b) : a = b := by
  have := congrArg Subtype.val (LinearMap.congr_fun h ⟨1, fun _ _ => rfl⟩)
  simpa using this

private theorem hk_norm {G : Type} [Group G] (I : Subgroup G) (hI : HeckePair I) (u : G)
    (hu : u ∈ Subgroup.normalizer (I : Set G)) : hk (Representation.trivial ℤ G ℤ) I u = 1 := by
  ext v
  rw [(hkNorm ℤ G ℤ _ I u hI hu).1 v]
  simp

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.domCard :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (x : kˣ), IsUnif x → ∀ a : Fin n → ℤ, Antitone a → (MulAction.orbit (iwC k n C) ((pw x a : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).ncard = resCard k ^ (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), (a p.1 - a p.2).toNat) := by
  intro k _ _ _ _ n C x hx a ha
  have hH := (heckePairIwC k n C).1
  have hmul := (domMul k n C ℤ ℤ (Representation.trivial ℤ (GL (Fin n) k) ℤ)).1
  refine endCast_inj (iwC k n C) ?_
  rw [← hk_triv _ hH]
  have hfund : ∀ m ≤ n, hk (Representation.trivial ℤ (GL (Fin n) k) ℤ) (iwC k n C) (pw x (fund n m)) =
      ((resCard k ^ (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
        (fund n m p.1 - fund n m p.2).toNat) : ℕ) : Module.End ℤ _) := by
    intro m hm
    obtain ⟨w, hw⟩ := exists_rot n m hm
    have hn := rot_norm C hx _ w hw
    have e : pw x (fund n m) = pm k n w⁻¹ * (pm k n w * pw x (fund n m)) := by
      rw [map_inv, inv_mul_cancel_left]
    rw [e, ((hkNorm ℤ _ ℤ _ _ _ hH hn).2.2.2 _).2, hk_norm _ hH _ hn, mul_one, hk_triv _ hH, permCard,
      invLen_inv, invLen_eq _ w hw]
  have key : ∀ (c : ℤ) (N : ℕ) (a : Fin n → ℤ), Antitone a → (∀ i, c ≤ a i ∧ a i ≤ c + N) →
      hk (Representation.trivial ℤ (GL (Fin n) k) ℤ) (iwC k n C) (pw x a) =
      ((resCard k ^ (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
        (a p.1 - a p.2).toNat) : ℕ) : Module.End ℤ _) := by
    intro c N
    induction N with
    | zero =>
      intro a _ hb
      have e : a = fun _ : Fin n => c := by
        funext i
        have := hb i
        omega
      rw [e, pw, hk_norm _ hH _ (Subgroup.center_le_normalizer _ (const_central _))]
      simp
    | succ N ih =>
      intro a ha hb
      obtain ⟨m, hm, hc⟩ := exists_cut a ha c
      have hfa : Antitone (fund n m) := by
        intro i j hij
        have := Fin.le_def.1 hij
        simp only [fund]
        split_ifs <;> omega
      have ha' : Antitone (a - fund n m) := by
        intro i j hij
        have h1 := ha hij
        have h2 := hc i
        have h3 := hc j
        have h4 := hb i
        have h5 := hb j
        simp only [fund, Pi.sub_apply]
        split_ifs <;> omega
      have hb' : ∀ i, c ≤ (a - fund n m) i ∧ (a - fund n m) i ≤ c + N := by
        intro i
        have h2 := hc i
        have h4 := hb i
        simp only [fund, Pi.sub_apply]
        split_ifs <;> omega
      have e : (fun i => x ^ a i) = (fun i => x ^ (a - fund n m) i) * fun i => x ^ fund n m i := by
        funext i
        simp only [Pi.mul_apply, Pi.sub_apply, ← _root_.zpow_add, sub_add_cancel]
      have h1 := ih _ ha' hb'
      have h2 := hfund m hm
      rw [pw] at h1 h2 ⊢
      rw [e, ← hmul _ _ (dom_zpow hx ha') (dom_zpow hx hfa), h1, h2, ← Nat.cast_mul, ← pow_add,
        ← Finset.sum_add_distrib]
      congr 2
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := (Finset.mem_filter.1 hp).2.le
      have h3 := ha' hp'
      have h4 := hfa hp'
      simp only [Pi.sub_apply] at h3 ⊢
      omega
  obtain ⟨c, hc⟩ := (Set.finite_range a).bddBelow
  obtain ⟨d, hd⟩ := (Set.finite_range a).bddAbove
  exact key c (d - c).toNat a ha fun i => by
    have h1 : c ≤ a i := hc ⟨i, rfl⟩
    have h2 : a i ≤ d := hd ⟨i, rfl⟩
    omega
end
