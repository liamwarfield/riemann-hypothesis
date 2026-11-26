module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.CoarseLabelFactorisation

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FrobeniusReductionProduct
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem expand_pow_zmod (p : ℕ) [Fact p.Prime] {σ : Type} (f : MvPolynomial σ (ZMod p)) (n : ℕ) :
    expand (p ^ n) f = f ^ (p ^ n) := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [expand_C, ← map_pow, ZMod.pow_card_pow]
  | add u v hu hv => rw [map_add (f := _), hu, hv, add_pow_char_pow]
  | mul_X q v h => rw [map_mul, h, expand_X, mul_pow]

theorem charP_FF {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) : CharP (FF O) p := by
  have h0 : ((p : ℕ) : FF O) = 0 := by
    have := (IsLocalRing.residue_eq_zero_iff (p : O)).mpr S.p_mem
    simpa using this
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr h0

theorem expand_pow_of_map (p : ℕ) [Fact p.Prime] {Fd : Type} [Field Fd] (φ : ZMod p →+* Fd) {σ : Type}
    (f : MvPolynomial σ (ZMod p)) (n : ℕ) :
    expand (p ^ n) (MvPolynomial.map φ f) = (MvPolynomial.map φ f) ^ (p ^ n) := by
  rw [← map_expand, expand_pow_zmod, map_pow]

theorem map_detPl {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x : ℤ) :
    MvPolynomial.map f (X.detPl R j x) = X.detPl S j x := by
  unfold Dat.detPl
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

theorem map_DlSeg {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n' r : ℕ} [NeZero n'] (X : Dat n' r)
    (p K : ℕ) (j : ℤ) : MvPolynomial.map f (X.DlSeg p K R j) = X.DlSeg p K S j := by
  unfold Dat.DlSeg
  rw [map_prod]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [map_pow, map_detPl]

theorem ell_split {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (R : Type) [CommRing R] (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (he : X.IsEll p K j e) :
    (monomial e 1 : SegRing R r K) = plEmb R r K (X.ellP K R j e) * nmEmb R r K (X.ellN K R j e) := by
  classical
  rw [monomial_eq, map_one, one_mul]
  have hsub : e.support ⊆ X.toLate j ×ˢ (Finset.univ : Finset (Fin (r + K))) := by
    intro v hv
    rw [Finset.mem_product]
    exact ⟨he.1 v (Finsupp.mem_support_iff.mp hv), Finset.mem_univ _⟩
  rw [Finsupp.prod_of_support_subset e hsub _ (fun _ _ => pow_zero _), Finset.prod_product]
  unfold Dat.ellP Dat.ellN plEmb nmEmb
  simp only [map_prod, map_pow, rename_X]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Fin.prod_univ_add]

theorem frobenius_reduction_product (C₀ : ℝ) : FrobeniusReductionProduct C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S j b e q I' I'' hc
  have : Fact p.Prime := ⟨hc.hX.prime⟩
  have : CharP (FF O) p := charP_FF S
  let φ : ZMod p →+* FF O := ZMod.castHom (dvd_refl p) (FF O)
  have hW : MvPolynomial.map (IsLocalRing.residue O) (segRen X.F j O (r + K) (PsiPl O q.1 I' * PsiTan O q.2 I'')) =
      MvPolynomial.map φ (segRen X.F j (ZMod p) (r + K) (PsiPl (ZMod p) q.1 I' * PsiTan (ZMod p) q.2 I'')) := by
    simp only [segRen, map_rename, map_mul, PsiPl_map, PsiTan_map]
  have hW2 : MvPolynomial.map (IsLocalRing.residue O) (segRen X.F j O (r + K) (PsiPl O q.1 I' * PsiTan O q.2 I'')) =
      plEmb (FF O) r K (segRen X.F j (FF O) r (Psi (FF O) q.1 I')) *
        nmEmb (FF O) r K (segRen X.F j (FF O) K (Psi (FF O) q.2 I'')) := by
    rw [← segRen_mul]
    simp only [segRen, map_rename, map_mul, PsiPl_map, PsiTan_map]
    rfl
  unfold Dat.zSeg Dat.Aw Dat.Gw
  rw [map_mul, map_mul, map_expand, hW, expand_pow_of_map, ← hW, hW2, map_monomial, map_one,
    ell_split X p K (FF O) j e hc.he]
  have hD : MvPolynomial.map (IsLocalRing.residue O) (plEmb O r K (X.DlSeg p K O j)) =
      plEmb (FF O) r K (X.DlSeg p K (FF O) j) := by
    unfold plEmb
    rw [map_rename, map_DlSeg]
  rw [hD]
  simp only [map_mul, map_pow, mul_pow]
  ring

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.LateVectorsDistinctTops
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantNonzeroOfInjectiveTops
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def LateVectorsDistinctLeadingTerms : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ j, ∀ x ∈ X.toLate j,
    Function.Injective fun a : Fin r => posOf n' (X.row j x a)


open Classical in
theorem ph_detPl_ne_zero {R : Type} [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)
    (hp : 0 < p) (j x : ℤ) (hinj : Function.Injective fun a : Fin r => posOf n' (X.row j x a)) :
    phSeg R K p X.F j (plEmb R r K (X.detPl R j x)) ≠ 0 := by
  intro h
  let v : Fin n' × Fin (r + K) → R := fun tc =>
    if ∃ a : Fin r, posOf n' (X.row j x a) = tc.1 ∧ tc.2 = Fin.castAdd K a then 1 else 0
  let f : MvPolynomial (ℤ × Fin r) R →+* R :=
    (MvPolynomial.eval v).comp ((phSeg R K p X.F j).toRingHom.comp (plEmb R r K).toRingHom)
  have h1 : f (X.detPl R j x) = 0 := by
    show MvPolynomial.eval v (phSeg R K p X.F j (plEmb R r K (X.detPl R j x))) = 0
    rw [h, map_zero]
  have hm : f.mapMatrix (Matrix.of fun a b : Fin r => MvPolynomial.X (X.row j x a, b)) = 1 := by
    ext a b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    show MvPolynomial.eval v (phSeg R K p X.F j (plEmb R r K (MvPolynomial.X (X.row j x a, b)))) = (1 : Matrix (Fin r) (Fin r) R) a b
    simp only [plEmb, rename_X, phSeg, aeval_X, map_pow, eval_X]
    by_cases hab : a = b
    · subst hab
      have hv : v (posOf n' (X.row j x a), Fin.castAdd K a) = 1 := if_pos ⟨a, rfl, rfl⟩
      rw [hv, one_pow, Matrix.one_apply_eq]
    · have hv : v (posOf n' (X.row j x a), Fin.castAdd K b) = 0 := by
        apply if_neg
        rintro ⟨a', ha, hb⟩
        have e1 : a' = a := hinj ha
        have e2 : b = a' := Fin.castAdd_injective _ _ hb
        exact hab (e2.trans e1).symm
      rw [hv, zero_pow (pow_ne_zero _ hp.ne'), Matrix.one_apply_ne hab]
  have h2 : f (X.detPl R j x) = 1 := by
    unfold Dat.detPl
    rw [RingHom.map_det, hm, Matrix.det_one]
  rw [h1] at h2
  exact zero_ne_one h2

theorem discriminant_nonzero_of_injective_tops (hInj : LateVectorsDistinctLeadingTerms) : DiscriminantNonzeroModUniformiser := by
  intro p n' r K _ _ _ X O _ _ _ hX
  have hp : 0 < p := hX.prime.pos
  have hpl : ∀ P : MvPolynomial (ℤ × Fin r) O,
      map (IsLocalRing.residue O) (plEmb O r K P) = plEmb _ r K (map (IsLocalRing.residue O) P) := by
    intro P
    simp [plEmb, MvPolynomial.map_rename]
  simp only [Dat.Dl, Dat.DlSeg, map_prod, map_pow, map_phSeg, hpl, map_detPl]
  rw [Finset.prod_ne_zero_iff]
  intro j _
  rw [Finset.prod_ne_zero_iff]
  intro x hx
  exact pow_ne_zero _ (ph_detPl_ne_zero X p K hp _ _ (hInj p n' r K X hX _ x hx))

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem late_vectors_distinct_tops : LateVectorsDistinctLeadingTerms := by
  intro p n' r K _ _ _ X hX j x hx
  obtain ⟨-, -, -, hnext, hTT, -⟩ := hX.valid
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hn : (0 : ℤ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  have hstep : ∀ t : ℤ, ∀ i < r, ∀ i' < r, X.F.fr t i < X.F.fr (t + 1) i' := by
    intro t i hi i' hi'
    calc X.F.fr t i ≤ X.F.fr t (r - 1) := bk_fr_le hX.valid t i (r - 1) (by omega) (by omega)
      _ < X.F.fr (t + 1) 0 := hnext t
      _ ≤ X.F.fr (t + 1) i' := fr_zero_le hX.valid (t + 1) i' hi'
  have hlt' : ∀ t : ℤ, ∀ k : ℕ, ∀ i < r, ∀ i' < r, X.F.fr t i < X.F.fr (t + 1 + k) i' := by
    intro t k
    induction k with
    | zero =>
      intro i hi i' hi'
      simpa using hstep t i hi i' hi'
    | succ k ih =>
      intro i hi i' hi'
      rw [show t + 1 + ((k + 1 : ℕ) : ℤ) = t + 1 + k + 1 by push_cast; ring]
      exact (ih i hi 0 hr).trans (hstep _ 0 hr i' hi')
  have hlt : ∀ t t' : ℤ, t < t' → ∀ i < r, ∀ i' < r, X.F.fr t i < X.F.fr t' i' := by
    intro t t' htt i hi i' hi'
    obtain ⟨k, hk⟩ : ∃ k : ℕ, t' = t + 1 + k := ⟨(t' - t - 1).toNat, by omega⟩
    rw [hk]
    exact hlt' t k i hi i' hi'
  have hinjfr : ∀ t t' : ℤ, ∀ i < r, ∀ i' < r, X.F.fr t i = X.F.fr t' i' → t = t' ∧ i = i' := by
    intro t t' i hi i' hi' h
    rcases lt_trichotomy t t' with h1 | rfl | h1
    · exact absurd h (hlt t t' h1 i hi i' hi').ne
    · refine ⟨rfl, ?_⟩
      rcases lt_trichotomy i i' with h2 | h2 | h2
      · exact absurd h (bk_fr_lt hX.valid t i i' h2 hi').ne
      · exact h2
      · exact absurd h.symm (bk_fr_lt hX.valid t i' i h2 hi).ne
    · exact absurd h.symm (hlt t' t h1 i' hi' i hi).ne
  rw [mem_late] at hx
  obtain ⟨-, hxW⟩ := hx
  simp only [Frames.IsW, not_le] at hxW
  obtain ⟨S, hS⟩ : ∃ S : Finset ℤ, S = {z ∈ X.F.letters j | Even z ∧ z < x} := ⟨_, rfl⟩
  have hmem : ∀ z, z ∈ evL X.F j x ↔ z ∈ S := fun z => by
    rw [hS]
    exact Finset.mem_sort _
  have hsort : (evL X.F j x).Pairwise (· < ·) := by
    rw [evL, ← hS]
    exact ((Finset.pairwise_sort S _).and (Finset.sort_nodup S _)).imp (fun h => lt_of_le_of_ne h.1 h.2)
  have hlen : (evL X.F j x).length = S.card := by
    rw [evL, ← hS]
    exact Finset.length_sort _
  have hfrS : ∀ t : ℤ, ∀ i < r, X.F.fr (j - 1) 0 ≤ X.F.fr t i → X.F.fr t i ≤ X.F.fr j (r - 1) →
      X.F.fr t i < x → X.F.fr t i ∈ S := by
    intro t i hi h1 h2 h3
    rw [hS]
    simp only [Finset.mem_filter, Frames.letters, Finset.mem_Icc]
    exact ⟨⟨⟨h1, h2⟩, (hTT t i hi).1⟩, (hTT t i hi).2, h3⟩
  have hSlo : ∀ z ∈ S, X.F.fr (j - 1) 0 ≤ z ∧ z ≤ X.F.fr j (r - 1) ∧ z < x := by
    intro z hz
    rw [hS, Finset.mem_filter] at hz
    have hb := mem_letters_bounds hz.1
    exact ⟨hb.1, hb.2.1, hz.2.2⟩
  have hlenr : r ≤ S.card := by
    have hsub : (Finset.range r).image (fun i => X.F.fr (j - 1) i) ⊆ S := by
      intro z hz
      simp only [Finset.mem_image, Finset.mem_range] at hz
      obtain ⟨i, hi, rfl⟩ := hz
      have hA : X.F.fr (j - 1) i ≤ X.F.fr (j - 1) (r - 1) :=
        bk_fr_le hX.valid _ i (r - 1) (by omega) (by omega)
      have hB : X.F.fr (j - 1) i < X.F.fr j (r - 1) := hlt (j - 1) j (by omega) i hi (r - 1) (by omega)
      exact hfrS _ i hi (fr_zero_le hX.valid _ i hi) hB.le (lt_of_le_of_lt hA hxW)
    have hinj' : Set.InjOn (fun i => X.F.fr (j - 1) i) ↑(Finset.range r) := by
      intro a ha b hb h
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      exact (hinjfr _ _ a ha b hb h).2
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj', Finset.card_range] at hc
    exact hc
  simp only [row_eq]
  generalize evL X.F j x = l at hmem hsort hlen ⊢
  have hNr : r ≤ l.length := hlen ▸ hlenr
  have hget : ∀ k (hk : k < l.length), l.getD k 0 = l[k] := fun k hk => List.getD_eq_getElem _ _ hk
  have hpw := List.pairwise_iff_getElem.mp hsort
  have hm : l.length - r < l.length := by omega
  have hinS : ∀ k, k < l.length → l.getD k 0 ∈ S := by
    intro k hk
    rw [hget k hk]
    exact (hmem _).1 (List.getElem_mem _)
  have hbound : ∀ k, l.length - r ≤ k → k < l.length →
      l.getD (l.length - r) 0 ≤ l.getD k 0 ∧ l.getD k 0 < l.getD (l.length - r) 0 + n' := by
    intro k hk1 hk2
    refine ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le hk1 with h | h
      · rw [h]
      · rw [hget _ hm, hget _ hk2]
        exact (hpw _ _ hm hk2 h).le
    · by_contra hz
      push_neg at hz
      have hy1S := hinS _ hm
      have hzS := hinS _ hk2
      obtain ⟨hy1lo, -, -⟩ := hSlo _ hy1S
      obtain ⟨-, hzhi, hzx⟩ := hSlo _ hzS
      obtain ⟨y1, hy1⟩ : ∃ y1, y1 = l.getD (l.length - r) 0 := ⟨_, rfl⟩
      obtain ⟨z, hzdef⟩ : ∃ z, z = l.getD k 0 := ⟨_, rfl⟩
      rw [← hy1, ← hzdef] at hz
      rw [← hy1] at hy1lo hy1S
      rw [← hzdef] at hzhi hzx hzS
      let w : ℕ → ℤ := fun i => X.F.fr (0 + (-((X.F.fr 0 i - y1) / n')) * X.F.J) i
      have hwr : ∀ i < r, y1 ≤ w i ∧ w i < y1 + n' := by
        intro i hi
        have hw : w i = X.F.fr 0 i + (-((X.F.fr 0 i - y1) / n')) * n' :=
          fr_period hX.valid 0 i (-((X.F.fr 0 i - y1) / n'))
        have e1 := Int.mul_ediv_add_emod (X.F.fr 0 i - y1) (n' : ℤ)
        have e2 := Int.emod_nonneg (X.F.fr 0 i - y1) (ne_of_gt hn)
        have e3 := Int.emod_lt_of_pos (X.F.fr 0 i - y1) hn
        have e4 : (-((X.F.fr 0 i - y1) / n')) * (n' : ℤ) = -((n' : ℤ) * ((X.F.fr 0 i - y1) / n')) := by ring
        constructor <;> linarith
      obtain ⟨T, hT⟩ : ∃ T : Finset ℤ, T = S.filter (fun s => y1 ≤ s) := ⟨_, rfl⟩
      have hTcard : T.card ≤ r := by
        have hsub : T ⊆ (Finset.Ico (l.length - r) l.length).image (fun k => l.getD k 0) := by
          intro s hs
          rw [hT, Finset.mem_filter] at hs
          obtain ⟨k', hk', rfl⟩ := List.getElem_of_mem ((hmem _).2 hs.1)
          refine Finset.mem_image.2 ⟨k', Finset.mem_Ico.2 ⟨?_, hk'⟩, hget k' hk'⟩
          by_contra hlt2
          push_neg at hlt2
          have h3 := hpw k' _ hk' hm hlt2
          have h2 := hs.2
          rw [hy1, hget _ hm] at h2
          exact absurd h2 (not_le.2 h3)
        have := (Finset.card_le_card hsub).trans Finset.card_image_le
        rw [Nat.card_Ico] at this
        omega
      have hwinj : Set.InjOn w ↑(Finset.range r) := by
        intro a ha b hb h
        simp only [Finset.coe_range, Set.mem_Iio] at ha hb
        exact (hinjfr _ _ a ha b hb h).2
      have hznot : z ∉ (Finset.range r).image w := by
        intro hzin
        simp only [Finset.mem_image, Finset.mem_range] at hzin
        obtain ⟨i, hi, hwi⟩ := hzin
        have := (hwr i hi).2
        linarith
      have hUsub : insert z ((Finset.range r).image w) ⊆ T := by
        intro s hs
        rw [Finset.mem_insert] at hs
        rw [hT, Finset.mem_filter]
        rcases hs with rfl | hs
        · exact ⟨hzS, by linarith⟩
        · simp only [Finset.mem_image, Finset.mem_range] at hs
          obtain ⟨i, hi, rfl⟩ := hs
          obtain ⟨hw1, hw2⟩ := hwr i hi
          exact ⟨hfrS _ i hi (by linarith) (by linarith) (by linarith), hw1⟩
      have hc := Finset.card_le_card hUsub
      rw [Finset.card_insert_of_notMem hznot, Finset.card_image_of_injOn hwinj, Finset.card_range] at hc
      omega
  intro a b hab
  simp only at hab
  have ha := hbound (l.length - r + a) (by omega) (by omega)
  have hb := hbound (l.length - r + b) (by omega) (by omega)
  have he := posOf_injOn (l.getD (l.length - r) 0 - 1)
    (show l.getD (l.length - r + a) 0 ∈ Set.Ioc _ _ from ⟨by linarith [ha.1], by linarith [ha.2]⟩)
    (show l.getD (l.length - r + b) 0 ∈ Set.Ioc _ _ from ⟨by linarith [hb.1], by linarith [hb.2]⟩) hab
  have hia : l.length - r + (a : ℕ) < l.length := by omega
  have hib : l.length - r + (b : ℕ) < l.length := by omega
  rw [hget _ hia, hget _ hib] at he
  apply Fin.ext
  rcases lt_trichotomy (l.length - r + (a : ℕ)) (l.length - r + (b : ℕ)) with h | h | h
  · exact absurd he (hpw _ _ hia hib h).ne
  · omega
  · exact absurd he.symm (hpw _ _ hib hia h).ne

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.WordOrderBoundOfNumericBound
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem ell_degree_le_power_bound : EllDegreeLePowerBound := by
  intro p n' r K _ _ _ X hX j e he
  classical
  unfold Dat.dS Dat.dV
  rw [← Finset.sum_add_distrib]
  have h1 : ∀ x ∈ X.toLate j, ((if Even x then 0 else ∑ c : Fin r, e (x, Fin.castAdd K c)) +
      (if Even x then ∑ c : Fin K, e (x, Fin.natAdd r c) else 0)) ≤ (r + K) * p ^ X.Rj p K j := by
    intro x _
    have a1 : ∑ c : Fin r, e (x, Fin.castAdd K c) ≤ r * p ^ X.Rj p K j := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin r => e (x, Fin.castAdd K c)) (p ^ X.Rj p K j)
        (fun c _ => (he.2 _).le)
      simpa using this
    have a2 : ∑ c : Fin K, e (x, Fin.natAdd r c) ≤ K * p ^ X.Rj p K j := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin K => e (x, Fin.natAdd r c)) (p ^ X.Rj p K j)
        (fun c _ => (he.2 _).le)
      simpa using this
    rw [add_mul]
    split_ifs <;> omega
  have h2 := Finset.sum_le_card_nsmul (X.toLate j) _ _ h1
  have h3 : (X.toLate j).card ≤ X.Ns := le_trans (by unfold Dat.toLate; exact Finset.card_filter_le _ _) (hX.card j)
  calc _ ≤ (X.toLate j).card • ((r + K) * p ^ X.Rj p K j) := h2
    _ = (X.toLate j).card * ((r + K) * p ^ X.Rj p K j) := smul_eq_mul _ _
    _ ≤ X.Ns * ((r + K) * p ^ X.Rj p K j) := Nat.mul_le_mul_right _ h3
    _ = (r + K) * X.Ns * p ^ X.Rj p K j := by ring

theorem degAt_ellP {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ) (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (x : ℤ) (hx : x ∈ X.toLate j) :
    DegAt x (∑ c : Fin r, e (x, Fin.castAdd K c)) (X.ellP K R j e) := by
  classical
  have h := degAt_prod (R := R) (x := x) (X.toLate j)
    (fun x' => ∏ c : Fin r, (MvPolynomial.X (x', c) : MvPolynomial (ℤ × Fin r) R) ^ e (x', Fin.castAdd K c))
    (fun x' => ∑ c : Fin r, e (x', Fin.castAdd K c) * (if x' = x then 1 else 0))
    (fun x' _ => degAt_prod Finset.univ _ _ (fun c _ => degAt_pow (degAt_X (x := x) (x', c)) _))
  have hD : (∑ x' ∈ X.toLate j, ∑ c : Fin r, e (x', Fin.castAdd K c) * (if x' = x then 1 else 0)) =
      ∑ c : Fin r, e (x, Fin.castAdd K c) := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [hy]
    · intro h; exact absurd hx h
  rw [hD] at h
  exact h

theorem degAt_ellN {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ) (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (x : ℤ) (hx : x ∈ X.toLate j) :
    DegAt x (∑ c : Fin K, e (x, Fin.natAdd r c)) (X.ellN K R j e) := by
  classical
  have h := degAt_prod (R := R) (x := x) (X.toLate j)
    (fun x' => ∏ c : Fin K, (MvPolynomial.X (x', c) : MvPolynomial (ℤ × Fin K) R) ^ e (x', Fin.natAdd r c))
    (fun x' => ∑ c : Fin K, e (x', Fin.natAdd r c) * (if x' = x then 1 else 0))
    (fun x' _ => degAt_prod Finset.univ _ _ (fun c _ => degAt_pow (degAt_X (x := x) (x', c)) _))
  have hD : (∑ x' ∈ X.toLate j, ∑ c : Fin K, e (x', Fin.natAdd r c) * (if x' = x then 1 else 0)) =
      ∑ c : Fin K, e (x, Fin.natAdd r c) := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [hy]
    · intro h; exact absurd hx h
  rw [hD] at h
  exact h

theorem word_order_bound_of_numeric_bound (D : Formalism.BasicNotions.D7) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) (C₀ : ℝ) (hRow : LateIndexInjective) (hN3 : OrderNumericBound C₀) :
    ProductOrdersBounded C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S j b e q I' I'' hc mm hmm x hx hW
  have : Fact p.Prime := ⟨hc.hX.prime⟩
  obtain ⟨i, rfl⟩ := segE_surj X.F j hx
  obtain ⟨nu, ka⟩ := q
  obtain ⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩, hcond⟩ := hc.hq
  have hI' := hc.hI'
  have hI'' := hc.hI''
  simp only at h1 h2 hcond hI' hI'' hmm
  rw [← h1] at hI' hcond hmm
  rw [← h2] at hI'' hcond hmm
  have u1 := standard_polynomial_mem_bounds (segLL X.F j) b' (fun th M => (hA3 p O S _ r (segLL X.F j) b' th M).2) P1 I' hI'
  have u2 := standard_polynomial_mem_bounds (segLL X.F j) b'' (fun th M => (hA3 p O S _ K (segLL X.F j) b'' th M).2) P2 I'' hI''
  obtain ⟨cE, cO, -⟩ := (hcond i).2 hW
  have hxl : segE X.F j i ∈ X.toLate j := (mem_late X j _).mpr ⟨hx, hW⟩
  have hrows := hRow p n' r K X hc.hX j
  have n3 := hN3 p n' r K X hc.hX hc.hLa hc.hk j _ hxl
  have hQ0 : (0 : ℝ) ≤ ((p ^ X.Rj p K j : ℕ) : ℝ) := Nat.cast_nonneg _
  have dG : DegAt (segE X.F j i) (p ^ X.Rj p K j * b'' i + ∑ c : Fin K, e (segE X.F j i, Fin.natAdd r c))
      (X.Gw p K (FF O) j e P2.mu I'') := by
    unfold Dat.Gw
    exact degAt_mul (degAt_pow (degAt_segRen X.F j u2.1 i) _) (degAt_ellN X K j e _ hxl)
  have dA : ¬ Even (segE X.F j i) →
      DegAt (segE X.F j i) (p ^ X.Rj p K j * b' i + ∑ c : Fin r, e (segE X.F j i, Fin.castAdd K c) + 0)
      (X.Aw p K (FF O) j e P1.mu I') := by
    intro he
    unfold Dat.Aw
    refine degAt_mul (degAt_mul (degAt_pow (degAt_segRen X.F j u1.1 i) _) (degAt_ellP X K j e _ hxl)) ?_
    refine degAt_of_supported {v : ℤ × Fin r | Even v.1} (DlSeg_supported _ X p K j _
      fun x' hx' a _ => ((hrows x' hx').2 a).2.1) ?_
    intro v hv hvx
    exact he (hvx ▸ hv)
  have a1 : ∑ c : Fin r, e (segE X.F j i, Fin.castAdd K c) ≤ r * p ^ X.Rj p K j := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin r => e (segE X.F j i, Fin.castAdd K c))
      (p ^ X.Rj p K j) (fun c _ => (hc.he.2 _).le)
    simpa using this
  have a2 : ∑ c : Fin K, e (segE X.F j i, Fin.natAdd r c) ≤ K * p ^ X.Rj p K j := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin K => e (segE X.F j i, Fin.natAdd r c))
      (p ^ X.Rj p K j) (fun c _ => (hc.he.2 _).le)
    simpa using this
  have a1r : ((∑ c : Fin r, e (segE X.F j i, Fin.castAdd K c) : ℕ) : ℝ) ≤ (r : ℝ) * ((p ^ X.Rj p K j : ℕ) : ℝ) := by
    exact_mod_cast a1
  have a2r : ((∑ c : Fin K, e (segE X.F j i, Fin.natAdd r c) : ℕ) : ℝ) ≤ (K : ℝ) * ((p ^ X.Rj p K j : ℕ) : ℝ) := by
    exact_mod_cast a2
  have hkd : Dat.k (r := r) K = (r : ℝ) + K := by unfold Dat.k; push_cast; ring
  rw [hkd] at n3
  have hr0 : (0 : ℝ) ≤ (r : ℝ) * ((p ^ X.Rj p K j : ℕ) : ℝ) := by positivity
  have hK0 : (0 : ℝ) ≤ (K : ℝ) * ((p ^ X.Rj p K j : ℕ) : ℝ) := by positivity
  rw [ordDeg_prod dA (fun _ => dG) mm hmm]
  refine le_trans ?_ n3
  split_ifs with he
  · have hb := mul_le_mul_of_nonneg_left (cE he).2 hQ0
    rw [Nat.cast_add, Nat.cast_mul]
    linarith
  · have hb := mul_le_mul_of_nonneg_left (cO he).2 hQ0
    rw [add_zero, Nat.cast_add, Nat.cast_mul]
    linarith

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem discriminant_nonzero_mod_uniformiser : DiscriminantNonzeroModUniformiser := discriminant_nonzero_of_injective_tops late_vectors_distinct_tops

theorem generator_modulo_uniformiser_of_adm (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) (hC : 32 ≤ C₀) : GeneratorModuloUniformiser C₀ := by
  have hV1 : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D := hAdm.2.2.2.2.2.2.2.1.1
  have hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D := hAdm.2.2.2.2.2.2.2.2.1
  have hB12 : NestedTypeBound D := hAdm.2.2.2.2.2.2.2.2.2.2.2.1
  have h41b : TopCountLowerBounds C₀ := top_count_lower_bounds_of_occurrence C₀ hC top_occurs_in_at_most_two_segments
  have hW3 := column_conditions_of_numeric_bounds D hV1 hA3 C₀ late_row_injective ell_degree_le_power_bound (power_exceeds_max_multiplicity C₀) (threshold_power_bound_of_counts C₀ h41b oldest_letter_in_segment)
  have hW4 := word_order_bound_of_numeric_bound D hA3 C₀ late_row_injective (order_numeric_bound_of_oldest C₀ oldest_letter_in_segment)
  have hW2 := allowed_letters_of_late_rows D hA3 C₀ late_row_injective
  have hWord := column_word_reduction_of_four D hB12 C₀ (frobenius_reduction_product C₀) hW2 hW3 hW4
  exact generator_of_segment_reductions C₀ coarse_label_factorisation top_degree_comparison discriminant_multihomogeneous (discriminant_ne_zero_of_residue_ne_zero discriminant_nonzero_mod_uniformiser) h41b (segment_reduction_of_column_words D hB12 C₀ hWord)
    segment_image_multihomogeneous segment_product_degree_determined

theorem top_count_lower_bounds (C₀ : ℝ) (hC : 32 ≤ C₀) : TopCountLowerBounds C₀ := top_count_lower_bounds_of_occurrence C₀ hC top_occurs_in_at_most_two_segments

end Formalism.MainNotions.SelectionLemmas.Pf
