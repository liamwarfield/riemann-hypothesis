module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsBergDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.FibreStB

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.FibreStE
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.FibreStD
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.FibreStC
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def psumQ (δ k : ℕ) : MvPolynomial (Fin δ) ℤ :=
  (esymmAlgHom_fin_surjective ℤ (le_refl δ)
    ⟨psum (Fin δ) ℤ k, psum_isSymmetric _ _ _⟩).choose

theorem aeval_psumQ (δ k : ℕ) :
    aeval (fun i : Fin δ => esymm (Fin δ) ℤ (i + 1)) (psumQ δ k) = psum (Fin δ) ℤ k := by
  have h := (esymmAlgHom_fin_surjective ℤ (le_refl δ)
    ⟨psum (Fin δ) ℤ k, psum_isSymmetric _ _ _⟩).choose_spec
  have h2 := congrArg Subtype.val h
  first
  | (rw [esymmAlgHom_apply] at h2; exact h2)
  | exact h2
  | simpa [psumQ, esymmAlgHom_apply] using h2

theorem sum_pow_eq_aeval_psumQ {S : Type*} [CommRing S] {δ : ℕ} (f : Fin δ → S) (k : ℕ) :
    ∑ i, f i ^ k =
      aeval (fun i : Fin δ => (Finset.univ.val.map f).esymm (i + 1)) (psumQ δ k) := by
  have h := congrArg (aeval f) (aeval_psumQ δ k)
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval] at h
  simp only [MvPolynomial.aeval_esymm_eq_multiset_esymm] at h
  rw [h]
  simp [MvPolynomial.psum]

theorem multiset_sum_pow_eq {S : Type*} [CommRing S] (s : Multiset S) {n : ℕ}
    (hn : Multiset.card s = n) (k : ℕ) :
    (s.map (· ^ k)).sum = aeval (fun i : Fin n => s.esymm (i + 1)) (psumQ n k) := by
  obtain ⟨l, rfl⟩ : ∃ l : List S, (l : Multiset S) = s := ⟨_, (Quotient.exists_rep s).choose_spec⟩
  rw [Multiset.coe_card] at hn
  subst hn
  have hs : (Finset.univ.val.map l.get : Multiset S) = (l : Multiset S) := by
    first
    | rw [Fin.univ_val_map, List.ofFn_get]
    | simp [Fin.univ_val_map, List.ofFn_get]
  have key := sum_pow_eq_aeval_psumQ l.get k
  rw [hs] at key
  rw [← key, Finset.sum_eq_multiset_sum, ← hs, Multiset.map_map] <;> rfl

def psumC {R : Type*} [CommRing R] (p : Polynomial R) (n k : ℕ) : R :=
  aeval (fun i : Fin n => (-1) ^ (i.val + 1) * p.coeff (n - (i.val + 1))) (psumQ n k)

theorem map_psumC {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : Polynomial R)
    (n k : ℕ) : φ (psumC p n k) = psumC (p.map φ) n k := by
  unfold psumC
  induction psumQ n k using MvPolynomial.induction_on
  next a => simp
  next P1 P2 h1 h2 => simp only [map_add (f := _), h1, h2]
  next P1 i h1 => simp [h1, Polynomial.coeff_map]

theorem sum_roots_pow {K : Type*} [Field K] (p : Polynomial K) (hm : p.Monic)
    (hroots : Multiset.card p.roots = p.natDegree) (k : ℕ) :
    (p.roots.map (· ^ k)).sum = psumC p p.natDegree k := by
  rw [multiset_sum_pow_eq p.roots hroots k, psumC]
  refine congrArg (fun F => aeval F (psumQ _ k)) (funext fun i => ?_)
  have hi : (i : ℕ) + 1 ≤ p.natDegree := i.isLt
  rw [Polynomial.coeff_eq_esymm_roots_of_card hroots (Nat.sub_le _ _), hm.leadingCoeff,
    Nat.sub_sub_self hi, one_mul, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}

def Gen.S (G : Gen x e) (j : ℕ) : MvPolynomial (Fin (D + 1)) ℤ :=
  psumC G.P G.P.natDegree j

def Gen.TrP (G : Gen x e) (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)) :
    MvPolynomial (Fin (D + 1)) ℤ :=
  ∑ j ∈ Finset.range (H.natDegree + 1), H.coeff j * G.S j

variable [DecidableEq ι] (G : Gen x e)

theorem Gen.deh_S {w : Fin (D + 1) → ℂ} (j : ℕ) :
    deh w 0 (G.S j) = ((G.P.map (deh w 0)).roots.map (· ^ j)).sum := by
  have hm : (G.P.map (deh w 0)).Monic := G.monic.map _
  have hd : (G.P.map (deh w 0)).natDegree = G.P.natDegree := G.monic.natDegree_map _
  have hc : Multiset.card (G.P.map (deh w 0)).roots = (G.P.map (deh w 0)).natDegree := by
    first
    | exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
    | exact (IsAlgClosed.splits _).card_roots
    | exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits _)).symm
  rw [sum_roots_pow _ hm hc j, hd, Gen.S, map_psumC]

private theorem eval₂_deh_eq_zero_of_mem_roots {w : Fin (D + 1) → ℂ} (hw : G.Good w)
    (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ))
    (hH : H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0) {ρ : ℂ}
    (hρ : ρ ∈ (G.P.map (deh w 0)).roots) : H.eval₂ (deh w 0) ρ = 0 := by
  have hP1 : G.P ≠ 1 := by
    intro h1
    have h2 := G.root
    rw [h1, Polynomial.eval₂_one] at h2
    exact one_ne_zero h2
  have hdecomp : H %ₘ G.P + G.P * (H /ₘ G.P) = H := by
    first
    | exact Polynomial.modByMonic_add_div H G.monic
    | exact Polynomial.modByMonic_add_div H G.P
    | exact Polynomial.modByMonic_add_div H G.P G.monic
  have hr : (H %ₘ G.P).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0 := by
    have h1 := congrArg (Polynomial.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) hdecomp
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, G.root, zero_mul, add_zero, hH] at h1
    exact h1
  have hcoef := G.min (H %ₘ G.P) (Polynomial.natDegree_modByMonic_lt H G.monic hP1) hr
  have hrw : (H %ₘ G.P).map (deh w 0) = 0 := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact hw.ker _ (hcoef j)
  have hPρ : G.P.eval₂ (deh w 0) ρ = 0 := by
    have h3 := (Polynomial.mem_roots (G.monic.map _).ne_zero).mp hρ
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at h3
  have h2 := congrArg (Polynomial.eval₂ (deh w 0) ρ) hdecomp
  rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, hPρ, zero_mul, add_zero] at h2
  rw [← h2, ← Polynomial.eval_map, hrw, Polynomial.eval_zero]

private theorem deh_dd_mul_deh_zOf_X_eq_eval₂_Q {w : Fin (D + 1) → ℂ} (hw : G.Good w) (i : ι) {ρ : ℂ}
    (hρ : ρ ∈ (G.P.map (deh w 0)).roots) :
    deh w 0 G.dd * deh (G.zOf w ρ) (e 0) (X i) = (G.Q i).eval₂ (deh w 0) ρ := by
  have hx : ∀ j, deh x (e 0) (X j) = x j / x (e 0) := fun j => by simp [deh]
  have hz : ∀ j, deh (G.zOf w ρ) (e 0) (X j) = G.zOf w ρ j / G.zOf w ρ (e 0) :=
    fun j => by simp [deh]
  have hzj : ∀ j, G.zOf w ρ j = w 0 * ((G.Q j).eval₂ (deh w 0) ρ / deh w 0 G.dd) := fun j => rfl
  have hd := hw.dd
  have h0 := hw.w0
  rw [hz, hzj, hzj]
  by_cases hxe : x (e 0) = 0
  · have hq : ∀ j, (G.Q j).eval₂ (deh w 0) ρ = 0 := by
      intro j
      refine eval₂_deh_eq_zero_of_mem_roots G hw (G.Q j) ?_ hρ
      rw [← G.hQ j, hx, hxe, div_zero, mul_zero]
    simp [hq]
  · have hxs : (G.Q (e 0) - Polynomial.C G.dd).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0 := by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, ← G.hQ (e 0), hx, div_self hxe, mul_one,
        sub_self]
    have h1 := eval₂_deh_eq_zero_of_mem_roots G hw _ hxs hρ
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, sub_eq_zero] at h1
    rw [h1]
    field_simp
    first | done | ring

private theorem exists_pow_mul_eq_eval₂_theta {w : Fin (D + 1) → ℂ} (hw : G.Good w) (f : MvPolynomial ι ℤ) :
    ∃ (N : ℕ) (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)),
      deh (x ∘ e) 0 G.dd ^ N * deh x (e 0) f = H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) ∧
      ∀ ρ ∈ (G.P.map (deh w 0)).roots,
        deh w 0 G.dd ^ N * deh (G.zOf w ρ) (e 0) f = H.eval₂ (deh w 0) ρ := by
  induction f using MvPolynomial.induction_on
  next a =>
    refine ⟨0, Polynomial.C (MvPolynomial.C a), ?_, fun ρ _ => ?_⟩ <;>
      (rw [pow_zero, one_mul, Polynomial.eval₂_C]; simp [deh])
  next f1 f2 h1 h2 =>
    obtain ⟨N1, H1, hx1, hw1⟩ := h1
    obtain ⟨N2, H2, hx2, hw2⟩ := h2
    refine ⟨N1 + N2, Polynomial.C (G.dd ^ N2) * H1 + Polynomial.C (G.dd ^ N1) * H2, ?_,
      fun ρ hρ => ?_⟩
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, ← hx1, ← hx2, map_add, map_pow, map_pow]
      ring
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, ← hw1 ρ hρ, ← hw2 ρ hρ, map_add, map_pow, map_pow]
      ring
  next f1 i h1 =>
    obtain ⟨N, H, hx1, hw1⟩ := h1
    refine ⟨N + 1, H * G.Q i, ?_, fun ρ hρ => ?_⟩
    · rw [Polynomial.eval₂_mul, ← hx1, ← G.hQ i, map_mul]
      ring
    · rw [Polynomial.eval₂_mul, ← hw1 ρ hρ, ← deh_dd_mul_deh_zOf_X_eq_eval₂_Q G hw i hρ, map_mul]
      ring

theorem Gen.trace_w {w : Fin (D + 1) → ℂ} (hw : G.Good w) (Tr : Ω → Ω)
    (hTr : ∀ H, Tr (H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) = deh (x ∘ e) 0 (G.TrP H))
    (hsc : ∀ (m : MvPolynomial (Fin (D + 1)) ℤ) (F : MvPolynomial ι ℤ),
      Tr (deh (x ∘ e) 0 m * deh x (e 0) F) = deh (x ∘ e) 0 m * Tr (deh x (e 0) F))
    {f : MvPolynomial ι ℤ} {g : MvPolynomial (Fin (D + 1)) ℤ}
    (h : deh (x ∘ e) 0 g = Tr (deh x (e 0) f)) :
    deh w 0 g = ((G.P.map (deh w 0)).roots.map fun ρ => deh (G.zOf w ρ) (e 0) f).sum := by
  obtain ⟨N, H, hx, hwr⟩ := exists_pow_mul_eq_eval₂_theta G hw f
  have hker : deh (x ∘ e) 0 (G.dd ^ N * g - G.TrP H) = 0 := by
    rw [map_sub, map_mul, h, ← hTr H, ← hx, ← hsc, map_pow, sub_self]
  have hwk := hw.ker _ hker
  rw [map_sub, map_mul, map_pow, sub_eq_zero] at hwk
  have hTrw : deh w 0 (G.TrP H) =
      ((G.P.map (deh w 0)).roots.map fun ρ => H.eval₂ (deh w 0) ρ).sum := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Gen.TrP, map_sum]
    simp only [map_mul, G.deh_S, Polynomial.eval₂_eq_sum_range]
    generalize (G.P.map (deh w 0)).roots = s
    refine Multiset.induction_on s ?_ ?_
    · simp
    · intro a s ih
      simp [Multiset.map_cons, Multiset.sum_cons, mul_add, Finset.sum_add_distrib, ih]
  have hdN : deh w 0 G.dd ^ N ≠ 0 := pow_ne_zero _ hw.dd
  apply mul_left_cancel₀ hdN
  rw [hwk, hTrw, ← Multiset.sum_map_mul_left]
  congr 1
  exact Multiset.map_congr rfl fun ρ hρ => (hwr ρ hρ).symm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open Polynomial IntermediateField

private lemma exists_int_primitive_element_pair {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero E] [Finite (IntermediateField F E)] (α β : E) :
    ∃ n : ℤ, α ∈ F⟮α + (n : E) * β⟯ ∧ β ∈ F⟮α + (n : E) * β⟯ := by
  obtain ⟨a, b, hab, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℤ => F⟮α + (n : E) * β⟯)
  have ha : α + (a : E) * β ∈ F⟮α + (b : E) * β⟯ := by
    rw [← heq]; exact IntermediateField.mem_adjoin_simple_self F _
  have hb : α + (b : E) * β ∈ F⟮α + (b : E) * β⟯ := IntermediateField.mem_adjoin_simple_self F _
  have hne : (a : E) - b ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hab
  have hβ : β ∈ F⟮α + (b : E) * β⟯ := by
    have hsub := sub_mem ha hb
    have h1 : (α + (a : E) * β) - (α + (b : E) * β) = ((a : E) - b) * β := by ring
    rw [h1] at hsub
    have hc : (a : E) - b ∈ F⟮α + (b : E) * β⟯ := sub_mem (intCast_mem _ a) (intCast_mem _ b)
    have := mul_mem (inv_mem hc) hsub
    rwa [← mul_assoc, inv_mul_cancel₀ hne, one_mul] at this
  refine ⟨b, ?_, hβ⟩
  have := sub_mem hb (mul_mem (intCast_mem _ b) hβ)
  simpa using this

theorem exists_int_primitive {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero F]
    [CharZero E] [FiniteDimensional F E] {ι : Type*} [Fintype ι] (v : ι → E)
    (hv : adjoin F (Set.range v) = ⊤) : ∃ c : ι → ℤ, F⟮∑ i, (c i : E) * v i⟯ = ⊤ := by
  classical
  haveI hfinite : Finite (IntermediateField F E) := by
    first
    | exact inferInstance
    | exact Field.finite_intermediateField_of_exists_primitive_element F E
        (Field.exists_primitive_element F E)
    | exact Field.finite_intermediateField_of_exists_primitive_element
        (Field.exists_primitive_element F E)
    | exact (Field.exists_primitive_element_iff_finite_intermediateField F E).mp
        ⟨inferInstance, Field.exists_primitive_element F E⟩
    | exact Field.exists_primitive_element_iff_finite_intermediateField.mp
        ⟨inferInstance, Field.exists_primitive_element F E⟩
  have key : ∀ s : Finset ι, ∃ c : ι → ℤ, ∀ i ∈ s, v i ∈ F⟮∑ j, (c j : E) * v j⟯ := by
    intro s
    refine Finset.induction_on s ⟨0, by simp⟩ ?_
    intro j s _ ih
    obtain ⟨c, hc⟩ := ih
    obtain ⟨n, hα, hβ⟩ := exists_int_primitive_element_pair (F := F) (∑ i, (c i : E) * v i) (v j)
    refine ⟨c + Pi.single j n, ?_⟩
    have h2 : ∑ i, (((Pi.single j n : ι → ℤ) i : ℤ) : E) * v i = (n : E) * v j := by
      rw [Fintype.sum_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]
      simp
    have hsum : ∑ i, (((c + Pi.single j n : ι → ℤ) i : ℤ) : E) * v i =
        ∑ i, (c i : E) * v i + (n : E) * v j := by
      simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib, h2]
    rw [hsum]
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hβ
    · exact (IntermediateField.adjoin_simple_le_iff.mpr hα) (hc i hi)
  obtain ⟨c, hc⟩ := key Finset.univ
  refine ⟨c, top_le_iff.mp ?_⟩
  rw [← hv, IntermediateField.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  exact hc i (Finset.mem_univ i)

theorem trace_pow_eq_psumC {K E : Type*} [Field K] [Field E] [Algebra K E] [CharZero K]
    [FiniteDimensional K E] {θ : E} (hθ : K⟮θ⟯ = ⊤) (j : ℕ) :
    Algebra.trace K E (θ ^ j) = psumC (minpoly K θ) (minpoly K θ).natDegree j := by
  classical
  have hint : IsIntegral K θ := IsIntegral.of_finite K θ
  have hmon := minpoly.monic hint
  have hsep : (minpoly K θ).Separable := Algebra.IsSeparable.isSeparable K θ
  have hc : Multiset.card ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots =
      ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).natDegree := by
    first
    | exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
    | exact (IsAlgClosed.splits _).card_roots
    | exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits _)).symm
  have hnd : ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots.Nodup :=
    Polynomial.nodup_roots hsep.map
  have hadj : Algebra.adjoin K {θ} = ⊤ := by
    first
    | rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθ,
        IntermediateField.top_toSubalgebra]
    | rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral hint, hθ,
        IntermediateField.top_toSubalgebra]
    | rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
          (fun x hx => (Set.mem_singleton_iff.mp hx) ▸ hint.isAlgebraic), hθ,
        IntermediateField.top_toSubalgebra]
  have hinj : Function.Injective (fun σ : E →ₐ[K] AlgebraicClosure K => σ θ) := by
    intro σ τ h
    exact AlgHom.ext_of_adjoin_eq_top hadj (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact h)
  have hfin : Module.finrank K E = (minpoly K θ).natDegree := by
    rw [← IntermediateField.finrank_top', ← hθ, IntermediateField.adjoin.finrank hint]
  have himg : Finset.univ.image (fun σ : E →ₐ[K] AlgebraicClosure K => σ θ) =
      ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots.toFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hy
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (hmon.map _).ne_zero]
      first
      | rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def,
          Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
      | simp [Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply]
    · rw [Multiset.toFinset_card_of_nodup hnd, hc, hmon.natDegree_map,
        Finset.card_image_of_injective _ hinj, Finset.card_univ, ← hfin]
      exact (AlgHom.card K E (AlgebraicClosure K)).ge
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [map_psumC, ← hmon.natDegree_map (algebraMap K (AlgebraicClosure K)),
    ← sum_roots_pow _ (hmon.map _) hc j]
  first
  | rw [trace_eq_sum_embeddings (AlgebraicClosure K)]
  | rw [trace_eq_sum_embeddings]
  | rw [Algebra.trace_eq_sum_embeddings (AlgebraicClosure K)]
  simp only [map_pow]
  have hsum := Finset.sum_image (s := Finset.univ)
    (g := fun σ : E →ₐ[K] AlgebraicClosure K => σ θ) (f := fun y => y ^ j)
    (fun σ _ τ _ h => hinj h)
  rw [himg] at hsum
  rw [← hsum, Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]

theorem exists_clear {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {ι : Type*} [Fintype ι] (q : ι → K[X]) :
    ∃ (b : A) (Q : ι → A[X]), b ≠ 0 ∧
      ∀ i, (Q i).map (algebraMap A K) = C (algebraMap A K b) * q i := by
  classical
  choose b hb using fun i =>
    IsLocalization.integerNormalization_spec (M := nonZeroDivisors A) (q i)
  refine ⟨∏ i, (b i : A), fun i => C (∏ j ∈ Finset.univ.erase i, (b j : A)) *
    IsLocalization.integerNormalization (nonZeroDivisors A) (q i), ?_, fun i => ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => nonZeroDivisors.ne_zero (hb i).1
  · rw [Polynomial.map_mul, (hb i).2, Polynomial.map_C, ← algebraMap_smul K (b i : A) (q i),
      Polynomial.smul_eq_C_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    simp only [map_mul, Polynomial.C_mul, mul_assoc]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
end
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}

theorem coord_ne_zero {ι : Type*} (y : ι → Ω) (h : coordIdeal ℤ y = ⊥) (k : ι) : y k ≠ 0 := by
  intro hk
  have hmem : (MvPolynomial.X k : MvPolynomial ι ℤ) ∈ coordIdeal ℤ y := by
    rw [coordIdeal, RingHom.mem_ker, coneMap]
    simp [hk]
  rw [h, Ideal.mem_bot] at hmem
  exact MvPolynomial.X_ne_zero k hmem

theorem div_mem_fnField (x : κ → Ω) (i j : κ) : x i / x j ∈ fnField x := by
  exact IntermediateField.subset_adjoin ℚ {t | ∃ i j, t = x i / x j} ⟨i, j, rfl⟩

theorem deh_mem_fnField {ι : Type*} (y : ι → Ω) (i₀ : ι) (m : MvPolynomial ι ℤ) :
    deh y i₀ m ∈ fnField y := by
  rw [deh_apply]
  induction m using MvPolynomial.induction_on
  · rw [MvPolynomial.eval₂_C]
    simpa using intCast_mem (fnField y) _
  · rw [MvPolynomial.eval₂_add]
    exact add_mem ‹_› ‹_›
  · rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact mul_mem ‹_› (div_mem_fnField y _ i₀)

def dehK (y : Fin (D + 1) → Ω) : MvPolynomial (Fin (D + 1)) ℤ →+* fnField y :=
  (deh y 0).codRestrict (fnField y).toSubfield.toSubring fun m => deh_mem_fnField y 0 m

@[simp] theorem coe_dehK (y : Fin (D + 1) → Ω) (m : MvPolynomial (Fin (D + 1)) ℤ) :
    ((dehK y m : fnField y) : Ω) = deh y 0 m := rfl

def chartGen (y : Fin (D + 1) → Ω) (k : {k : Fin (D + 1) // k ≠ 0}) : fnField y :=
  ⟨y k / y 0, div_mem_fnField y k 0⟩

def chartRing (y : Fin (D + 1) → Ω) : Subalgebra ℤ (fnField y) :=
  Algebra.adjoin ℤ (Set.range (chartGen y))

theorem aeval_chartGen (y : Fin (D + 1) → Ω) (g : MvPolynomial {k : Fin (D + 1) // k ≠ 0} ℤ) :
    ((MvPolynomial.aeval (chartGen y) g : fnField y) : Ω) =
      deh y 0 (MvPolynomial.rename Subtype.val g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [deh_apply]
  | add p q hp hq => simp only [map_add (f := _), AddMemClass.coe_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.rename_X, MulMemClass.coe_mul, hp]
    congr 1
    simp [deh_apply, chartGen]

theorem chartGen_indep (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) :
    AlgebraicIndependent ℤ (chartGen y) := by
  classical
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro g hg
  have hy0 := coord_ne_zero y hfree 0
  set G := MvPolynomial.rename Subtype.val g
  have h1 : deh y 0 G = 0 := by
    rw [← aeval_chartGen]
    change (((MvPolynomial.aeval (chartGen y) g : fnField y)) : Ω) = 0
    rw [hg]; rfl
  have hH := homog_isHomogeneous (0 : Fin (D + 1)) G le_rfl
  have h2 : MvPolynomial.aeval y (homog 0 G.totalDegree G) = 0 := by
    rw [MvPolynomial.aeval_def, algebraMap_int_eq, eval₂_homog y 0 hy0 G le_rfl, h1, mul_zero]
  have h3 := mem_coordIdeal_of_isHomogeneous ℤ y hH h2
  rw [hfree, Ideal.mem_bot] at h3
  apply MvPolynomial.funext
  intro u
  let v : Fin (D + 1) → ℚ := fun k => if h : k = 0 then 1 else (u ⟨k, h⟩ : ℚ)
  have h4 := eval₂_homog v 0 (by simp [v]) G le_rfl
  rw [h3, MvPolynomial.eval₂_zero] at h4
  have h5 : deh v 0 G = ((MvPolynomial.eval u g : ℤ) : ℚ) := by
    rw [deh_apply, MvPolynomial.eval₂_rename, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
      ← eq_intCast (Int.castRingHom ℚ), MvPolynomial.eval₂_comp_left]
    congr 1
    funext k
    simp [v, k.2]
  rw [h5] at h4
  have h6 : ((MvPolynomial.eval u g : ℤ) : ℚ) = 0 := by
    have := h4.symm
    rwa [mul_eq_zero, or_iff_right (pow_ne_zero _ (by simp [v]))] at this
  simpa using h6

theorem chartRing_closed (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) :
    IsIntegrallyClosed (chartRing y) := by
  have hind := chartGen_indep y hfree
  haveI : UniqueFactorizationMonoid (chartRing y) :=
    MulEquiv.uniqueFactorizationMonoid hind.aevalEquiv.toRingEquiv.toMulEquiv inferInstance
  haveI : IsDomain (chartRing y) := Subalgebra.isDomain _
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed

theorem chartRing_frac (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) :
    IsFractionRing (chartRing y) (fnField y) := by
  have hl : y 0 ≠ 0 := coord_ne_zero y hfree 0
  refine IsFractionRing.of_field _ _ fun z => ?_
  have hinj : Function.Injective (algebraMap (chartRing y) Ω) := by
    intro a b hab
    exact Subtype.val_injective (Subtype.val_injective hab)
  let F : Subfield Ω := (IsFractionRing.lift (K := FractionRing (chartRing y)) hinj).fieldRange
  have hgen : ∀ i, y i / y 0 ∈ F := by
    intro i
    by_cases hi : i = 0
    · subst hi; rw [div_self hl]; exact F.one_mem
    · refine ⟨algebraMap (chartRing y) (FractionRing (chartRing y))
        ⟨chartGen y ⟨i, hi⟩, Algebra.subset_adjoin ⟨_, rfl⟩⟩, ?_⟩
      rw [IsFractionRing.lift_algebraMap hinj]
      rfl
  have hle : (fnField y).toSubfield ≤ F := by
    unfold fnField
    refine IntermediateField.adjoin_le_subfield ℚ _ ?_ ?_
    · rintro _ ⟨q, rfl⟩
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem F q
    · rintro _ ⟨i, j, rfl⟩
      have : y i / y j = (y i / y 0) / (y j / y 0) := by
        rw [div_div_div_cancel_right₀ hl]
      change y i / y j ∈ F
      rw [this]
      exact F.div_mem (hgen i) (hgen j)
  obtain ⟨w, hw⟩ := hle z.2
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := chartRing y) w
  refine ⟨a, b, Subtype.val_injective ?_⟩
  rw [map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap] at hw
  rw [← hw]
  exact (map_div₀ (fnField y).val _ _).symm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module IntermediateField

variable {Ω : Type*} [Field Ω] [CharZero Ω] {ι : Type} [Fintype ι] {D : ℕ}

theorem coord_div_isIntegral (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) (i : ι) :
    IsIntegral (chartRing (x ∘ e)) (x i / x (e 0)) := by
  set y := x ∘ e with hy
  change IsIntegral _ (x i / y 0)
  have hl : y 0 ≠ 0 := coord_ne_zero y h.free 0
  have hinj : Function.Injective (coneMap ℤ y) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    have : f ∈ coordIdeal ℤ y := by rw [coordIdeal, RingHom.mem_ker]; exact hf
    rwa [h.free, Ideal.mem_bot] at this
  let eqv : MvPolynomial (Fin (D + 1)) ℤ ≃ₐ[ℤ] coneRing ℤ y := AlgEquiv.ofInjective (coneMap ℤ y) hinj
  let w : Fin (D + 1) → chartRing y := fun k =>
    if hk : k = 0 then 1 else ⟨chartGen y ⟨k, hk⟩, Algebra.subset_adjoin ⟨_, rfl⟩⟩
  have hw : ∀ k, algebraMap (chartRing y) Ω (w k) = y k * (y 0)⁻¹ := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp [w, mul_inv_cancel₀ hl]
    · simp only [w, dif_neg hk]
      change y k / y 0 = _
      exact div_eq_mul_inv _ _
  let ψ : Polynomial Ω →+* Ω := Polynomial.evalRingHom (y 0)⁻¹
  have hev : ∀ f : MvPolynomial (Fin (D + 1)) ℤ,
      ψ (coneMap ℤ y f) = MvPolynomial.aeval (fun k => y k * (y 0)⁻¹) f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [coneMap, ψ]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    | mul_X p k hp => rw [map_mul, map_mul, map_mul, hp]; simp [coneMap, ψ]
  let φ : coneRing ℤ y →+* chartRing y :=
    (MvPolynomial.aeval w).toRingHom.comp eqv.symm.toAlgHom.toRingHom
  have hrel : (algebraMap (chartRing y) Ω).comp φ = ψ.comp (algebraMap (coneRing ℤ y) _) := by
    ext r
    obtain ⟨f, rfl⟩ := eqv.surjective r
    have h1 : ((eqv f : coneRing ℤ y) : Polynomial Ω) = coneMap ℤ y f := rfl
    change algebraMap _ Ω (MvPolynomial.aeval w (eqv.symm (eqv f))) =
      ψ ((eqv f : coneRing ℤ y) : Polynomial Ω)
    rw [eqv.symm_apply_apply, h1, hev, ← MvPolynomial.aeval_algebraMap_apply,
      show (⇑(algebraMap (chartRing y) Ω) ∘ w) = fun k => y k * (y 0)⁻¹ from funext hw]
  have := IsIntegral.map_of_comp_eq φ ψ hrel (h.integral i)
  simpa [ψ, div_eq_mul_inv] using this

abbrev Lx (x : ι → Ω) (e : Fin (D + 1) → ι) : IntermediateField (fnField (x ∘ e)) Ω :=
  extendScalars (fnField_comp_le x e)

theorem Lx_eq (x : ι → Ω) (e : Fin (D + 1) → ι) (hx0 : x (e 0) ≠ 0) :
    Lx x e = adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) := by
  apply le_antisymm
  · intro t ht
    have key : fnField x ≤
        (adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0))).restrictScalars ℚ := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro s ⟨i, j, rfl⟩
      have hi : x i / x (e 0) ∈ adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) :=
        subset_adjoin _ _ ⟨i, rfl⟩
      have hj : x j / x (e 0) ∈ adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) :=
        subset_adjoin _ _ ⟨j, rfl⟩
      have hq := div_mem hi hj
      have e2 : x i / x (e 0) / (x j / x (e 0)) = x i / x j := by
        by_cases hj0 : x j = 0
        · simp [hj0]
        · field_simp
      rw [e2] at hq
      exact hq
    exact key ht
  · rw [IntermediateField.adjoin_le_iff]
    rintro t ⟨i, rfl⟩
    exact div_mem_fnField x i (e 0)

theorem Lx_finite (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) :
    FiniteDimensional (fnField (x ∘ e)) (Lx x e) := by
  have hx0 : x (e 0) ≠ 0 := coord_ne_zero (x ∘ e) h.free 0
  have hint : ∀ t ∈ Set.range (fun i => x i / x (e 0)), IsIntegral (fnField (x ∘ e)) t := by
    rintro t ⟨i, rfl⟩
    exact (coord_div_isIntegral x e h i).tower_top
  rw [Lx_eq x e hx0]
  exact IntermediateField.finiteDimensional_adjoin hint

def gL (x : ι → Ω) (e : Fin (D + 1) → ι) (i : ι) : Lx x e :=
  ⟨x i / x (e 0), div_mem_fnField x i (e 0)⟩

theorem adjoin_gL (x : ι → Ω) (e : Fin (D + 1) → ι) (hx0 : x (e 0) ≠ 0) :
    adjoin (fnField (x ∘ e)) (Set.range (gL x e)) = ⊤ := by
  apply IntermediateField.map_injective (Lx x e).val
  have htop : (⊤ : IntermediateField (fnField (x ∘ e)) (Lx x e)).map (Lx x e).val = Lx x e := by
    ext z
    rw [IntermediateField.mem_map]
    constructor
    · rintro ⟨w, -, rfl⟩
      exact w.2
    · intro hz
      exact ⟨⟨z, hz⟩, IntermediateField.mem_top, rfl⟩
  rw [IntermediateField.adjoin_map, ← Set.range_comp, htop]
  exact (Lx_eq x e hx0).symm

theorem exists_primitive (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) :
    ∃ c : ι → ℤ, (fnField (x ∘ e))⟮∑ i, (c i : Lx x e) * gL x e i⟯ = ⊤ := by
  have hx0 : x (e 0) ≠ 0 := coord_ne_zero (x ∘ e) h.free 0
  have := Lx_finite x e h
  exact exists_int_primitive (gL x e) (adjoin_gL x e hx0)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
end
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module IntermediateField

variable {Ω : Type*} [Field Ω] [CharZero Ω] {ι : Type} [Fintype ι] {D : ℕ}

theorem fnTrace_coe (x : ι → Ω) (e : Fin (D + 1) → ι) (s : Lx x e) :
    fnTrace x e (s : Ω) =
      ((Algebra.trace (fnField (x ∘ e)) (Lx x e) s : fnField (x ∘ e)) : Ω) := by
  have hs : (s : Ω) ∈ fnField x := (IntermediateField.mem_extendScalars _).mp s.2
  unfold fnTrace
  rw [dite_eq_left hs]

theorem exists_gen (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) :
    ∃ G : Gen x e, G.P.natDegree = projDeg x e ∧
      (∀ H, fnTrace x e (H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) =
        deh (x ∘ e) 0 (G.TrP H)) ∧
      (∀ m F, fnTrace x e (deh (x ∘ e) 0 m * deh x (e 0) F) =
        deh (x ∘ e) 0 m * fnTrace x e (deh x (e 0) F)) := by
  classical
  set y := x ∘ e with hy
  have hx0 : x (e 0) ≠ 0 := coord_ne_zero y h.free 0
  have hfin := Lx_finite x e h
  obtain ⟨c, hc⟩ := exists_primitive x e h
  set θL : Lx x e := ∑ i, (c i : Lx x e) * gL x e i with hθLdef
  let Θ : MvPolynomial ι ℤ := ∑ i, MvPolynomial.C (c i) * MvPolynomial.X i
  have hθ : deh x (e 0) Θ = (θL : Ω) := by
    simp [Θ, θL, gL, deh_X]
  obtain ⟨θ, hθdef⟩ : ∃ θ : Ω, θ = deh x (e 0) Θ := ⟨_, rfl⟩
  have hθθ : θ = (θL : Ω) := hθdef.trans hθ

  have hfrac := chartRing_frac y h.free
  have hclosed := chartRing_closed y h.free
  have hθA : IsIntegral (chartRing y) θ := by
    have : (θL : Ω) = ∑ i, (c i : Ω) * (x i / x (e 0)) := by simp [θL, gL]
    rw [hθθ, this]
    refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ (coord_div_isIntegral x e h i)
    simpa using isIntegral_algebraMap (R := chartRing y) (A := Ω) (x := ((c i : ℤ) : chartRing y))
  have hθK : IsIntegral (fnField y) θ := hθA.tower_top
  have hPK : minpoly (fnField y) θ = (minpoly (chartRing y) θ).map (algebraMap (chartRing y) (fnField y)) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' (fnField y) hθA
  have hθL : minpoly (fnField y) θ = minpoly (fnField y) θL := by
    rw [hθθ]
    exact minpoly.algebraMap_eq (algebraMap (Lx x e) Ω).injective θL
  have hδ : (minpoly (fnField y) θL).natDegree = projDeg x e := by
    rw [projDeg, relfinrank_eq_finrank_of_le (fnField_comp_le x e), ← IntermediateField.finrank_top',
      ← hc, IntermediateField.adjoin.finrank (.of_finite _ _)]

  have hind := chartGen_indep y h.free
  let r : chartRing y →+* MvPolynomial (Fin (D + 1)) ℤ :=
    (MvPolynomial.rename Subtype.val).toRingHom.comp hind.aevalEquiv.symm.toRingHom
  have hr : ∀ a : chartRing y, deh y 0 (r a) = algebraMap (chartRing y) Ω a := by
    intro a
    obtain ⟨g, rfl⟩ := hind.aevalEquiv.surjective a
    have h1 : r (hind.aevalEquiv g) = MvPolynomial.rename Subtype.val g := by
      show MvPolynomial.rename Subtype.val (hind.aevalEquiv.symm (hind.aevalEquiv g)) = _
      rw [AlgEquiv.symm_apply_apply]
    have h2 : ((hind.aevalEquiv g : Algebra.adjoin ℤ (Set.range (chartGen y))) : fnField y) =
        MvPolynomial.aeval (chartGen y) g := hind.algebraMap_aevalEquiv g
    rw [h1, ← aeval_chartGen, ← h2]
    rfl
  have hrc : (deh y 0).comp r = algebraMap (chartRing y) Ω := RingHom.ext hr
  have hrK : (dehK y).comp r = algebraMap (chartRing y) (fnField y) := by
    ext a
    rw [RingHom.comp_apply, coe_dehK, hr, IsScalarTower.algebraMap_apply (chartRing y) (fnField y) Ω]
    rfl
  have hev : ∀ (p : (chartRing y)[X]) (t : Ω),
      (p.map r).eval₂ (deh y 0) t = aeval t (p.map (algebraMap (chartRing y) (fnField y))) := by
    intro p t
    rw [eval₂_map, hrc, IsScalarTower.algebraMap_eq (chartRing y) (fnField y) Ω, ← eval₂_map,
      aeval_def]
  have hdehK : (algebraMap (fnField y) Ω).comp (dehK y) = deh y 0 := RingHom.ext fun _ => rfl
  set Pa := minpoly (chartRing y) θ with hPa
  have hPa_deg : (Pa.map r).natDegree = (minpoly (fnField y) θL).natDegree := by
    rw [(minpoly.monic hθA).natDegree_map, ← hθL, hPK, (minpoly.monic hθA).natDegree_map]

  have hq : ∀ i, ∃ q : (fnField y)[X], aeval θL q = gL x e i := by
    intro i
    have htop : Algebra.adjoin (fnField y) {θL} = ⊤ := by
      rw [← adjoin_simple_toSubalgebra_of_isAlgebraic (IsIntegral.of_finite _ θL).isAlgebraic, hc,
        top_toSubalgebra]
    have hm : gL x e i ∈ Algebra.adjoin (fnField y) {θL} := htop ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
    obtain ⟨q, hq⟩ := hm
    exact ⟨q, hq⟩
  choose q hq using hq
  have hqΩ : ∀ i, aeval θ (q i) = x i / x (e 0) := by
    intro i
    have : (θL : Ω) = algebraMap (Lx x e) Ω θL := rfl
    rw [hθθ, this, aeval_algebraMap_apply, hq i]
    rfl
  obtain ⟨b, Qa, hb0, hQa⟩ := exists_clear (A := chartRing y) (K := fnField y) q
  have hsep : (minpoly (fnField y) θ).Separable := (minpoly.irreducible hθK).separable
  obtain ⟨u, v, huv⟩ := hsep
  obtain ⟨b', UV, hb'0, hUV⟩ := exists_clear (A := chartRing y) (K := fnField y) ![u, v]
  have hinjA : Function.Injective (algebraMap (chartRing y) Ω) := by
    rw [IsScalarTower.algebraMap_eq (chartRing y) (fnField y) Ω]
    exact (algebraMap (fnField y) Ω).injective.comp (IsFractionRing.injective _ _)
  have hne : ∀ a : chartRing y, a ≠ 0 → deh y 0 (r a) ≠ 0 := fun a ha => by
    rw [hr]; exact (map_ne_zero_iff _ hinjA).mpr ha
  let G : Gen x e :=
    { Θ := Θ
      P := Pa.map r
      monic := (minpoly.monic hθA).map r
      root := by rw [← hθdef, hev, ← hPK]; exact minpoly.aeval _ _
      min := by
        intro H hH h0 j
        have hm : H.map (dehK y) = 0 := by
          by_contra hne'
          have h1 : aeval θ (H.map (dehK y)) = 0 := by
            rw [aeval_def, eval₂_map, hdehK, hθdef]; exact h0
          have h2 := natDegree_le_natDegree (minpoly.degree_le_of_ne_zero (fnField y) θ hne' h1)
          have h3 := natDegree_map_le (f := dehK y) (p := H)
          rw [hθL] at h2
          rw [hPa_deg] at hH
          omega
        have := congrArg (fun p => p.coeff j) hm
        simp only [coeff_map, coeff_zero] at this
        rw [← coe_dehK, this]
        simp
      dd := r b
      dd_ne := hne b hb0
      Q := fun i => (Qa i).map r
      hQ := by
        intro i
        rw [← hθdef, hev, hQa i, map_mul, aeval_C, hqΩ i, deh_X, hr,
          IsScalarTower.algebraMap_apply (chartRing y) (fnField y) Ω]
      cc := r b'
      cc_ne := hne b' hb'0
      U := (UV 0).map r
      V := (UV 1).map r
      hUV := by
        have e1 : (UV 0).map r * Pa.map r + (UV 1).map r * derivative (Pa.map r) - C (r b') =
            (UV 0 * Pa + UV 1 * derivative Pa - C b').map r := by
          rw [Polynomial.map_sub, Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul,
            Polynomial.derivative_map, Polynomial.map_C]
        have e2 : (UV 0 * Pa + UV 1 * derivative Pa - C b').map
            (algebraMap (chartRing y) (fnField y)) = 0 := by
          rw [Polynomial.map_sub, Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul,
            ← Polynomial.derivative_map, Polynomial.map_C, hUV 0, hUV 1, ← hPK]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linear_combination (C (algebraMap (chartRing y) (fnField y) b')) * huv
        rw [e1, Polynomial.map_map, hrc, IsScalarTower.algebraMap_eq (chartRing y) (fnField y) Ω, ← Polynomial.map_map,
          e2, Polynomial.map_zero] }
  refine ⟨G, ?_, ?_, ?_⟩
  · show (Pa.map r).natDegree = _
    rw [hPa_deg, hδ]
  · intro H
    have hS : ∀ j, (dehK y (G.S j) : fnField y) =
        psumC (minpoly (fnField y) θL) (minpoly (fnField y) θL).natDegree j := by
      intro j
      show dehK y (psumC (Pa.map r) (Pa.map r).natDegree j) = _
      rw [map_psumC, Polynomial.map_map, hrK, ← hPK, hθL, hPa_deg]
    set s : Lx x e := ∑ j ∈ Finset.range (H.natDegree + 1), dehK y (H.coeff j) • θL ^ j with hsdef
    have hs : (s : Ω) = H.eval₂ (deh y 0) (deh x (e 0) G.Θ) := by
      show _ = H.eval₂ (deh y 0) (deh x (e 0) Θ)
      rw [eval₂_eq_sum_range, hθ, hsdef]
      simp [Algebra.smul_def]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hs, fnTrace_coe, map_sum]
    simp only [LinearMap.map_smul, smul_eq_mul, trace_pow_eq_psumC hc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Gen.TrP, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← coe_dehK y (G.S j), hS j]
    rfl
  · intro m F
    let t : Lx x e := ⟨deh x (e 0) F, deh_mem_fnField x (e 0) F⟩
    have h1 : deh y 0 m * deh x (e 0) F = ((dehK y m • t : Lx x e) : Ω) := by
      rw [Algebra.smul_def]; rfl
    rw [h1, fnTrace_coe, show deh x (e 0) F = (t : Ω) from rfl, fnTrace_coe, LinearMap.map_smul,
      smul_eq_mul]
    push_cast
    rfl

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
end
end

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

def prFib (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (w : Fin (D + 1) → ℂ) : Set (Ix κ → ℂ) :=
  {z | z ∈ pts (coordIdeal ℤ x) ∧ ∀ k, z (e k) = w k}

theorem exists_proj_ne_zero {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e)
    {z : Ix κ → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) : ∃ k, z (e k) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h; push Not at h; exact hz.1 (funext h)
  obtain ⟨q, hqm, hq⟩ := hfr.integral i
  have hg : ∀ j, ∃ g, coneMap ℤ (x ∘ e) g = ((q.coeff j : coneRing ℤ (x ∘ e)) : Polynomial Ω) :=
    fun j => (q.coeff j).2
  choose g hg using hg
  set n := q.natDegree
  let Q : MvPolynomial (Ix κ) ℤ := ∑ j ∈ Finset.range (n + 1), rename e (g j) * X i ^ j
  have hQ : Q ∈ coordIdeal ℤ x := by
    rw [coordIdeal, RingHom.mem_ker]
    rw [Polynomial.eval₂_eq_sum_range] at hq
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Q, map_sum, map_mul, map_pow, Fib.coneMap_rename, hg]
    convert hq using 2
    simp [coneMap]
  have hz0 := Fib.coneMap_eq_zero_of_mem_pts (coordIdeal_isHomogIdeal ℤ x) hz hQ
  have hze : z ∘ e = 0 := funext hcon
  have hcn : constantCoeff (g n) = 1 := by
    have h1 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 0) (hg n)
    simp only [coeff_coneMap, homogeneousComponent_zero, aeval_C] at h1
    rw [hqm.coeff_natDegree] at h1
    simp at h1
    exact_mod_cast h1
  have h2 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n) hz0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Q, map_sum, map_mul, map_pow, Fib.coneMap_rename, hze] at h2
  have h3 : ∀ j, coneMap ℤ (0 : Fin (D + 1) → ℂ) (g j) =
      Polynomial.C ((constantCoeff (g j) : ℤ) : ℂ) := by
    intro j
    simp [coneMap]
  have hX : coneMap ℤ z (X i) = Polynomial.C (z i) * Polynomial.X := by simp [coneMap]
  simp only [h3, hX, Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at h2
  rw [Finset.sum_eq_single n] at h2
  · rw [mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow,
      if_pos rfl, hcn] at h2
    simp at h2
    exact hi h2.1
  · intro j _ hj
    rw [mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow,
      if_neg (Ne.symm hj)]
  · intro h; simp at h

def IsDiscr (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (Δ : MvPolynomial (Fin (D + 1)) ℂ) : Prop :=
  Δ ≠ 0 ∧ ∀ w, eval w Δ ≠ 0 →
    (prFib x e w).Finite ∧ (prFib x e w).ncard = projDeg x e ∧
    (∀ z ∈ prFib x e w, ∃ (U : Set (Fin (D + 1) → ℂ)) (γ : (Fin (D + 1) → ℂ) → Ix κ → ℂ),
      IsOpen U ∧ w ∈ U ∧ DifferentiableOn ℂ γ U ∧ γ w = z ∧ ∀ w' ∈ U, γ w' ∈ prFib x e w') ∧
    ∀ (n : ℕ) (f : MvPolynomial (Ix κ) ℤ) (g : MvPolynomial (Fin (D + 1)) ℤ),
      f.IsHomogeneous n → g.IsHomogeneous n → aeval (x ∘ e) g = secTrace x e n (aeval x f) →
      eval w (map (Int.castRingHom ℂ) g) = ∑ᶠ z ∈ prFib x e w, eval z (map (Int.castRingHom ℂ) f)

theorem exists_isDiscr {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) :
    ∃ Δ, IsDiscr x e Δ := by
  classical
  obtain ⟨G, hdeg, hTr, hsc⟩ := Fib.exists_gen x e hfr
  have hy0 : (x ∘ e) 0 ≠ 0 := Fib.coord_ne_zero _ hfr.free 0
  have hx0 : x (e 0) ≠ 0 := hy0
  let Δ0 : MvPolynomial (Fin (D + 1)) ℤ :=
    X 0 * Fib.homog 0 G.dd.totalDegree G.dd * Fib.homog 0 G.cc.totalDegree G.cc
  have hevΔ : ∀ w : Fin (D + 1) → ℂ, w 0 ≠ 0 →
      eval w (map (Int.castRingHom ℂ) Δ0) = w 0 * (w 0 ^ G.dd.totalDegree * Fib.deh w 0 G.dd) *
        (w 0 ^ G.cc.totalDegree * Fib.deh w 0 G.cc) := by
    intro w hw0
    rw [eval_map]
    simp only [Δ0, eval₂_mul, eval₂_X, Fib.eval₂_homog w 0 hw0 _ le_rfl]
  have hgood : ∀ w : Fin (D + 1) → ℂ, eval w (map (Int.castRingHom ℂ) Δ0) ≠ 0 → G.Good w := by
    intro w hw
    have hw0 : w 0 ≠ 0 := by
      intro h0
      apply hw
      rw [eval_map]
      simp [Δ0, h0]
    rw [hevΔ w hw0] at hw
    refine ⟨hw0, fun m hm => ?_, fun h0 => hw (by rw [h0]; ring), fun h0 => hw (by rw [h0]; ring)⟩
    exact Fib.deh_eq_zero_of_deh_eq_zero (x ∘ e) w 0 hy0 hw0
      (fun f hf => by rw [hfr.free, Ideal.mem_bot] at hf; simp [hf]) hm
  refine ⟨map (Int.castRingHom ℂ) Δ0, ?_, fun w hw => ?_⟩
  · intro h0
    have h1 : Δ0 = 0 :=
      map_injective _ (RingHom.injective_int (Int.castRingHom ℂ)) (by rw [h0, map_zero])
    have h2 : aeval (x ∘ e) Δ0 = (x ∘ e) 0 * ((x ∘ e) 0 ^ G.dd.totalDegree *
        Fib.deh (x ∘ e) 0 G.dd) * ((x ∘ e) 0 ^ G.cc.totalDegree * Fib.deh (x ∘ e) 0 G.cc) := by
      simp only [Δ0, aeval_def, algebraMap_int_eq, eval₂_mul, eval₂_X,
        Fib.eval₂_homog _ 0 hy0 _ le_rfl]
    rw [h1, map_zero] at h2
    exact (mul_ne_zero (mul_ne_zero hy0 (mul_ne_zero (pow_ne_zero _ hy0) G.dd_ne))
      (mul_ne_zero (pow_ne_zero _ hy0) G.cc_ne)) h2.symm
  have hgw := hgood w hw
  have hfib : prFib x e w = Fib.fib x e w := rfl
  refine ⟨hfib ▸ G.fib_finite hx0 hgw, by rw [hfib, G.fib_ncard hx0 hgw, hdeg], ?_, ?_⟩
  · intro z hz
    have hWo : IsOpen {w : Fin (D + 1) → ℂ | eval w (map (Int.castRingHom ℂ) Δ0) ≠ 0} :=
      isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const
    obtain ⟨U, γ, hU, hwU, hγ, hγw, hγf⟩ :=
      G.exists_section hx0 hWo (fun w' hw' => hgood w' hw') (w := w) hw (z := z) hz
    exact ⟨U, γ, hU, hwU, hγ, hγw, hγf⟩
  · intro n f g hf hg hfg
    have hdf : aeval x f = x (e 0) ^ n * Fib.deh x (e 0) f :=
      Fib.aeval_eq_pow_mul_deh x (e 0) hx0 hf
    have hdg : aeval (x ∘ e) g = (x ∘ e) 0 ^ n * Fib.deh (x ∘ e) 0 g :=
      Fib.aeval_eq_pow_mul_deh (x ∘ e) 0 hy0 hg
    have hT : Fib.deh (x ∘ e) 0 g = fnTrace x e (Fib.deh x (e 0) f) := by
      rw [hdg, secTrace, hdf, mul_div_cancel_left₀ _ (pow_ne_zero _ hx0)] at hfg
      exact mul_left_cancel₀ (pow_ne_zero _ hy0) hfg
    have htw := G.trace_w hgw (fnTrace x e) hTr hsc hT
    have hw0 := hgw.w0
    rw [hfib, G.finsum_fib hx0 hgw, eval_map, ← algebraMap_int_eq, ← aeval_def,
      Fib.aeval_eq_pow_mul_deh w 0 hw0 hg, htw, ← Multiset.sum_map_mul_left]
    congr 1
    refine Multiset.map_congr rfl fun ρ hρ => ?_
    have hρ' := (G.mem_roots).1 hρ
    rw [eval_map, ← aeval_def,
      Fib.aeval_eq_pow_mul_deh _ (e 0) (by rw [G.zOf_e hgw hρ' 0]; exact hw0) hf, G.zOf_e hgw hρ' 0]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
