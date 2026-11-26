module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharpoly
noncomputable section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
namespace GlobalTheory.MemN.SerInhab

theorem trace_mulLeft {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ _ (LinearMap.mulLeft ℂ a) = (Fintype.card G : ℂ) * a.coeff 1 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]
  have : ∀ x : G, (LinearMap.toMatrix (MonoidAlgebra.basis G ℂ) (MonoidAlgebra.basis G ℂ)
      (LinearMap.mulLeft ℂ a)).diag x = a.coeff 1 := by
    intro x
    simp [Matrix.diag, LinearMap.toMatrix_apply, MonoidAlgebra.basis]
  rw [Finset.sum_congr rfl fun x _ => this x]
  simp

theorem coeff_mem {G : Type} [Group G] [Finite G] {N : ℕ} (hN : 0 < N) (hG : Nat.card G ∣ N)
    (e : MonoidAlgebra ℂ G) (he : e * e = e) (hc : ∀ a, e * a = a * e) (x : G) :
    e.coeff x ∈ IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  classical
  haveI := Fintype.ofFinite G
  set K := IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} with hK
  set s : MonoidAlgebra ℂ G := MonoidAlgebra.single x⁻¹ 1 with hs
  have hsN : s ^ N = 1 := by
    rw [hs, MonoidAlgebra.single_pow, one_pow,
      orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard x⁻¹).trans hG)]
    rfl
  have hpow : (e * s) ^ (N + 1) = e * s := by
    rw [Commute.mul_pow (hc s), IsIdempotentElem.pow_succ_eq N he, pow_succ, hsN, one_mul]
  have hζ := Complex.isPrimitiveRoot_exp N hN.ne'
  have hζK : Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ K :=
    IntermediateField.mem_adjoin_simple_self _ _
  have htr : LinearMap.trace ℂ _ (LinearMap.mulLeft ℂ (e * s)) ∈ K := by
    rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
    refine multiset_sum_mem _ fun μ hμ => ?_
    have hroot := isRoot_of_mem_roots hμ
    have h1 := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mpr hroot
    obtain ⟨v, hv⟩ := h1.exists_hasEigenvector
    have h2 := hv.pow_apply (N + 1)
    rw [LinearMap.pow_mulLeft, hpow, hv.apply_eq_smul] at h2
    have h3 : μ = μ ^ (N + 1) := smul_left_injective ℂ hv.2 h2
    by_cases h0 : μ = 0
    · rw [h0]; exact zero_mem _
    · have h4 : μ ^ N = 1 := by
        rw [pow_succ] at h3
        exact mul_right_cancel₀ h0 (by rw [one_mul]; exact h3.symm)
      haveI : NeZero N := ⟨hN.ne'⟩
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h4
      rw [← hi]; exact pow_mem hζK i
  rw [trace_mulLeft] at htr
  have h5 : (e * s).coeff 1 = e.coeff x := by simp [hs]
  rw [h5] at htr
  have h6 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have := mul_mem (inv_mem (natCast_mem K (Fintype.card G))) htr
  rwa [← mul_assoc, inv_mul_cancel₀ h6, one_mul] at this

theorem exists_primitive (G : Type) [Group G] [Finite G] :
    ∃ (n : ℕ) (p : Fin n → MonoidAlgebra ℂ G), (∀ i, p i * p i = p i) ∧ (∀ i a, p i * a = a * p i) ∧
      (∀ i j, i ≠ j → p i * p j = 0) ∧ (∀ i, p i ≠ 0) ∧ ∑ i, p i = 1 ∧
      ∀ z, (∀ a, z * a = a * z) → z ∈ Submodule.span ℂ (Set.range p) := by
  classical
  have : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨n, d, hd, ⟨φ⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ G)
  refine ⟨n, fun i => φ.symm (Pi.single i 1), fun i => ?_, fun i a => ?_, fun i j hij => ?_, fun i => ?_, ?_,
    fun z hz => ?_⟩
  · rw [← map_mul, ← Pi.single_mul, one_mul]
  · apply φ.injective
    simp only [map_mul, AlgEquiv.apply_symm_apply]
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  · rw [← map_mul, map_eq_zero_iff _ φ.symm.injective]
    funext k
    by_cases h : k = i
    · subst h; simp [hij]
    · simp [h]
  · rw [ne_eq, map_eq_zero_iff _ φ.symm.injective]
    intro h
    haveI := hd i
    have h' := congrFun h i
    rw [Pi.single_eq_same] at h'
    exact one_ne_zero h'
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← map_sum, Finset.univ_sum_single, ← map_one φ.symm]; rfl
  · have hc : ∀ y, φ z * y = y * φ z := by
      intro y
      obtain ⟨x, rfl⟩ := φ.surjective y
      rw [← map_mul, ← map_mul, hz]
    have h1 : ∀ i, ∃ c : ℂ, φ z i = c • 1 := by
      intro i
      have hci : ∀ M : Matrix (Fin (d i)) (Fin (d i)) ℂ, φ z i * M = M * φ z i := by
        intro M
        have := congrFun (hc (Pi.single i M)) i
        simpa using this
      obtain ⟨c, hcc⟩ := Matrix.mem_range_scalar_of_commute_single (M := φ z i) (fun a b _ => (hci _).symm)
      exact ⟨c, by rw [← hcc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
    choose c hc' using h1
    have h2 : z = ∑ i, c i • φ.symm (Pi.single i 1) := by
      apply φ.injective
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, AlgEquiv.apply_symm_apply]
      funext j
      rw [hc', Finset.sum_apply, Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb.symm]
      · simp
    rw [h2]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_family {G S : Type} [Group G] [Finite G] (c : G → S) (hc : Function.Surjective c)
    (hconj : ∀ x y, c (x * y) = c (y * x)) [Fintype S] :
    ∃ (q : S → MonoidAlgebra ℂ G), (∀ i, q i * q i = q i) ∧ (∀ i a, q i * a = a * q i) ∧
      (∀ i j, i ≠ j → q i * q j = 0) ∧ (∀ i, q i ≠ 0) ∧ ∑ i, q i = 1 := by
  classical
  obtain ⟨n, p, h1, h2, h3, h4, h5, h6⟩ := exists_primitive G
  let z : S → MonoidAlgebra ℂ G := fun s =>
    .ofCoeff (Finsupp.equivFunOnFinite.symm fun x => if c x = s then 1 else 0)
  have hz : ∀ s x, (z s).coeff x = if c x = s then 1 else 0 := fun s x => rfl
  have hzc : ∀ s a, z s * a = a * z s := by
    intro s a
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [mul_add, add_mul, ha, hb]
    | single x r =>
      ext y
      simp [hz, hconj y, mul_comm]
  have hli : LinearIndependent ℂ z := by
    rw [Fintype.linearIndependent_iff]
    intro a ha s
    obtain ⟨x, rfl⟩ := hc s
    have := congrArg (fun w : MonoidAlgebra ℂ G => w.coeff x) ha
    simpa [hz, Finsupp.finsetSum_apply] using this
  have hcard : Fintype.card S ≤ Fintype.card (Fin n) := by
    have := linearIndependent_le_span_aux' z hli (Set.range p) (by rintro _ ⟨s, rfl⟩; exact h6 _ (hzc s))
    exact this.trans (Fintype.card_range_le p)
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  haveI : Nonempty S := ⟨c 1⟩
  obtain ⟨π, hπ⟩ : ∃ π : Fin n → S, Function.Surjective π :=
    ⟨Function.invFun ι, Function.invFun_surjective ι.injective⟩
  let q : S → MonoidAlgebra ℂ G := fun s => ∑ i ∈ Finset.univ.filter (fun i => π i = s), p i
  have hpq : ∀ i s, p i * q s = if π i = s then p i else 0 := by
    intro i s
    simp only [q, Finset.mul_sum]
    rw [Finset.sum_filter, Finset.sum_eq_single i]
    · rw [h1]
    · intro b _ hb; rw [h3 i b hb.symm]; simp
    · simp
  refine ⟨q, fun s => ?_, fun s a => ?_, fun s t hst => ?_, fun s h => ?_, ?_⟩
  · conv_lhs => enter [1]; simp only [q]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [hpq, if_pos (by simpa using hi)]
  · simp only [q, Finset.sum_mul, Finset.mul_sum, h2]
  · conv_lhs => enter [1]; simp only [q]
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun i hi => ?_
    have : π i = s := by simpa using hi
    rw [hpq, if_neg (this ▸ hst)]
  · obtain ⟨i, rfl⟩ := hπ s
    have := hpq i (π i)
    rw [h, mul_zero, if_pos rfl] at this
    exact h4 i this.symm
  · rw [← h5]; exact Finset.sum_fiberwise _ _ _

theorem exists_charpoly {F : Type} [Field F] {r : ℕ} (f : F[X]) (hm : f.Monic) (hd : f.natDegree = r)
    (h0 : f.coeff 0 ≠ 0) : ∃ x : GL (Fin r) F, (x : Matrix (Fin r) (Fin r) F).charpoly = f := by
  subst hd
  let pb := AdjoinRoot.powerBasis' hm
  have h : (Algebra.leftMulMatrix pb.basis pb.gen).charpoly = f := by
    rw [charpoly_leftMulMatrix]
    exact AdjoinRoot.minpoly_powerBasis_gen_of_monic hm
  let M : Matrix (Fin f.natDegree) (Fin f.natDegree) F := Algebra.leftMulMatrix pb.basis pb.gen
  have hM : M.charpoly = f := h
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hM]
    exact mul_ne_zero (pow_ne_zero _ (by simp)) h0
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, hM⟩

theorem exists_isSer : ∀ (r g N : ℕ), g.Prime → 0 < N → Nat.card (GL (Fin r) (ZMod g)) ∣ N →
    ∃ e, IsSer r g N e := by
  intro r g N hg hN hG
  classical
  haveI : Fact g.Prime := ⟨hg⟩
  let P : (ZMod g)[X] → Prop := fun f => f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0
  let c : GL (Fin r) (ZMod g) → {f // P f} := fun x =>
    ⟨(x : Matrix (Fin r) (Fin r) (ZMod g)).charpoly, Matrix.charpoly_monic _, by simp, by
      intro h
      have h2 := Matrix.det_eq_sign_charpoly_coeff (x : Matrix (Fin r) (Fin r) (ZMod g))
      rw [h, mul_zero] at h2
      exact x.det_ne_zero h2⟩
  have hc : Function.Surjective c := by
    rintro ⟨f, h1, h2, h3⟩
    obtain ⟨x, hx⟩ := exists_charpoly f h1 h2 h3
    exact ⟨x, Subtype.ext hx⟩
  haveI : Finite {f // P f} := Finite.of_surjective c hc
  haveI := Fintype.ofFinite {f // P f}
  obtain ⟨q, h1, h2, h3, h4, h5⟩ := exists_family c hc (fun x y => Subtype.ext (by
    simp only [c, Units.val_mul]; exact Matrix.charpoly_mul_comm _ _))
  let e : (ZMod g)[X] → MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) := fun f => if h : P f then q ⟨f, h⟩ else 0
  have hi : ∀ f, e f * e f = e f := by
    intro f; by_cases h : P f <;> simp [e, h, h1]
  have hce : ∀ f a, e f * a = a * e f := by
    intro f a; by_cases h : P f <;> simp [e, h, h2]
  refine ⟨e, hi, hce, fun f f' hf => ?_, fun f => ?_, ⟨Finset.univ.map (Function.Embedding.subtype P), fun f => ?_, ?_⟩,
    fun f x => coeff_mem hN hG _ (hi f) (hce f) x⟩
  · by_cases h : P f
    · by_cases h' : P f'
      · simp only [e, dif_pos h, dif_pos h']
        exact h3 _ _ (fun hh => hf (congrArg Subtype.val hh))
      · simp [e, h']
    · simp [e, h]
  · change e f = 0 ↔ ¬ P f
    by_cases h : P f <;> simp [e, h, h4]
  · change _ ↔ P f
    simp
  · rw [Finset.sum_map, ← h5]
    exact Finset.sum_congr rfl fun s _ => by simp [e, s.2]

end GlobalTheory.MemN.SerInhab
end
end

noncomputable section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
namespace GlobalTheory.MemN.TypesInhab

section Tensor

variable {I : Type} [Fintype I] {Γ : I → Type} [∀ i, Group (Γ i)] [∀ i, Finite (Γ i)]

def ten (x : ∀ i, MonoidAlgebra ℂ (Γ i)) : MonoidAlgebra ℂ (∀ i, Γ i) :=
  MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun g => ∏ i, (x i).coeff (g i)

theorem coeff_ten (x : ∀ i, MonoidAlgebra ℂ (Γ i)) (g : ∀ i, Γ i) :
    (ten x).coeff g = ∏ i, (x i).coeff (g i) := rfl

theorem coeff_mul_sum {Δ : Type} [Group Δ] [Fintype Δ] (x y : MonoidAlgebra ℂ Δ) (g : Δ) :
    (x * y).coeff g = ∑ h, x.coeff h * y.coeff (h⁻¹ * g) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  simp

theorem ten_mul (x y : ∀ i, MonoidAlgebra ℂ (Γ i)) : ten x * ten y = ten fun i => x i * y i := by
  classical
  haveI := fun i => Fintype.ofFinite (Γ i)
  ext g
  simp only [coeff_mul_sum, coeff_ten]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.prod_mul_distrib]
  rfl

theorem ten_single (g : ∀ i, Γ i) :
    ten (fun i => MonoidAlgebra.single (g i) (1 : ℂ)) = MonoidAlgebra.single g 1 := by
  classical
  ext h
  rw [coeff_ten]
  by_cases hh : g = h
  · subst hh; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hh
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp [hh]

theorem ten_central (x : ∀ i, MonoidAlgebra ℂ (Γ i)) (hx : ∀ i a, x i * a = a * x i) :
    ten x ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ i, Γ i)) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_on with
  | of g => simp only [MonoidAlgebra.of_apply, ← ten_single, ten_mul, hx]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]
  | smul c a ha => rw [smul_mul_assoc, mul_smul_comm, ha]

theorem ten_eq_zero {x : ∀ i, MonoidAlgebra ℂ (Γ i)} {i : I} (h : x i = 0) : ten x = 0 := by
  ext g
  rw [coeff_ten, Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])]
  simp

theorem ten_ne_zero {x : ∀ i, MonoidAlgebra ℂ (Γ i)} (h : ∀ i, x i ≠ 0) : ten x ≠ 0 := by
  have h1 : ∀ i, ∃ g, (x i).coeff g ≠ 0 := by
    intro i
    by_contra hh
    push Not at hh
    exact h i (by ext g; simp [hh g])
  choose g hg using h1
  intro h0
  have h2 := coeff_ten x g
  rw [h0] at h2
  exact Finset.prod_ne_zero_iff.2 (fun i _ => hg i) (by simpa using h2.symm)

end Tensor

theorem exists_char {A : Type} [Ring A] [Algebra ℂ A] [Module.Finite ℂ A] (z : Subalgebra.center ℂ A) {t : A}
    (ht : t ≠ 0) (h : (z : A) * t = 0) : ∃ ω : Subalgebra.center ℂ A →ₐ[ℂ] ℂ, ω z = 0 := by
  have hz : Ideal.span {z} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨u, hu⟩ := hu.exists_left_inv
    have h1 : (u : A) * z = 1 := congrArg Subtype.val hu
    apply ht
    rw [← one_mul t, ← h1, mul_assoc, h, mul_zero]
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hz
  letI := Ideal.Quotient.field M
  haveI : Module.Finite ℂ (Subalgebra.center ℂ A) :=
    Module.Finite.of_injective (Subalgebra.center ℂ A).val.toLinearMap Subtype.val_injective
  haveI : Module.Finite ℂ (Subalgebra.center ℂ A ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℂ M).toLinearMap (Ideal.Quotient.mkₐ_surjective ℂ M)
  let l : (Subalgebra.center ℂ A ⧸ M) →ₐ[ℂ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨l.comp (Ideal.Quotient.mkₐ ℂ M), ?_⟩
  exact (congrArg l (Ideal.Quotient.eq_zero_iff_mem.2 (hle (Ideal.mem_span_singleton_self z)))).trans (map_zero l)


open Classical in
theorem good_sum {I : Type} [Fintype I] {Γ : I → Type} [∀ i, Group (Γ i)] [∀ i, Finite (Γ i)]
    {P : I → Type} [∀ i, Finite (P i)] (E : ∀ i, P i → MonoidAlgebra ℂ (Γ i)) (good : (∀ i, P i) → Prop)
    (e : MonoidAlgebra ℂ (∀ i, Γ i))
    (he : ∀ g, e.coeff g = ∑ᶠ a, if good a then ∏ i, (E i (a i)).coeff (g i) else 0)
    (h1 : ∀ i p, E i p * E i p = E i p) (h2 : ∀ i p a, E i p * a = a * E i p)
    (h3 : ∀ i p q, p ≠ q → E i p * E i q = 0) :
    e ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ i, Γ i)) ∧
      ∀ a : ∀ i, P i, e * ten (fun i => E i (a i)) = if good a then ten (fun i => E i (a i)) else 0 := by
  haveI := Fintype.ofFinite (∀ i, P i)
  have h : e = ∑ a : ∀ i, P i, if good a then ten (fun i => E i (a i)) else 0 := by
    ext g
    rw [he, finsum_eq_sum_of_fintype, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs
    · rfl
    · rfl
  refine ⟨?_, fun a => ?_⟩
  · rw [h]
    refine sum_mem fun a _ => ?_
    split_ifs
    · exact ten_central _ fun i => h2 i _
    · exact zero_mem _
  · rw [h, Finset.sum_mul, Finset.sum_eq_single a]
    · split_ifs
      · simp only [ten_mul, h1]
      · rw [zero_mul]
    · intro b _ hb
      split_ifs
      · obtain ⟨i, hi⟩ := Function.ne_iff.1 hb
        rw [ten_mul]
        exact ten_eq_zero (i := i) (h3 i _ _ hi)
      · rw [zero_mul]
    · simp

section Types

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem goodTupleIdempotent_central_and_action (T : NTypes A) (hs : ∀ k f, f.Monic ∧ f.natDegree = R.r ∧ f.coeff 0 ≠ 0 → T.eSer k f ≠ 0) :
    T.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) ∧
      ∀ f : ∀ k, N.PlG k → (ZMod (H.g k))[X], (∀ k v, (f k v).Monic ∧ (f k v).natDegree = R.r ∧ (f k v).coeff 0 ≠ 0) →
        ∃ t : MonoidAlgebra ℂ (G0g N), t ≠ 0 ∧ (T.goodTuple f → T.e0 * t = t) ∧ (¬ T.goodTuple f → T.e0 * t = 0) := by
  haveI : ∀ k, NeZero (H.g k) := fun k => ⟨(H.g_prime k).ne_zero⟩
  haveI : ∀ k, Fact (H.g k).Prime := fun k => ⟨H.g_prime k⟩
  obtain ⟨hc, hm⟩ := good_sum (I := Σ k : Fin 2, N.PlG k) (P := fun kv => Fin R.r → ZMod (H.g kv.1))
    (fun kv p => T.eSer kv.1 (Formalism.CyclotomicNorms.monicOf p))
    (fun a => T.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))) T.e0 (fun g => rfl)
    (fun _ _ => T.eSer_idem _ _) (fun _ _ => T.eSer_central _ _)
    (fun _ p q hpq => T.eSer_orth _ _ _ fun h => hpq (funext fun i => by
      rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt p i, h, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]))
  refine ⟨hc, fun f hf => ?_⟩
  let a : ∀ kv : (Σ k : Fin 2, N.PlG k), Fin R.r → ZMod (H.g kv.1) := fun kv i => (f kv.1 kv.2).coeff i
  have ha : ∀ kv, Formalism.CyclotomicNorms.monicOf (a kv) = f kv.1 kv.2 := fun kv =>
    Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ (hf _ _).1 (hf _ _).2.1
  have ha' : (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) = f := by
    funext k v
    exact ha ⟨k, v⟩
  have := hm a
  rw [ha'] at this
  refine ⟨_, ten_ne_zero fun kv => ?_, fun h => this.trans (if_pos h), fun h => this.trans (if_neg h)⟩
  rw [ha]
  exact hs _ _ (hf _ _)

theorem not_good_unip (T : NTypes A) : ¬ T.goodTuple (fun _ _ => (X - 1) ^ R.r) := by
  intro h
  haveI : Fact (H.g 0).Prime := ⟨H.g_prime 0⟩
  have hne : Nonempty (N.PlG 0) := by
    rw [← Fintype.card_pos_iff, N.card_PlG]
    exact GaloisStage.f_pos R
  obtain ⟨v⟩ := hne
  have hf : Squarefree ((X - 1 : (ZMod (H.g 0))[X]) ^ R.r) := (h 0).1.2.1 v
  have h1 : IsUnit (X - 1 : (ZMod (H.g 0))[X]) :=
    hf _ (by rw [← sq]; exact pow_dvd_pow _ (GaloisStage.two_le_r R))
  have h2 := natDegree_eq_zero_of_isUnit h1
  have h3 := (GaloisStage.monic_unip (K := ZMod (H.g 0)) 1).2
  rw [pow_one] at h3
  omega

theorem goodTupleIdempotent_coeff_mem_subring (T : NTypes A) (S : Subring ℂ) (hS : ∀ k f x, (T.eSer k f).coeff x ∈ S) (x : G0g N) :
    T.e0.coeff x ∈ S := by
  haveI : ∀ k, NeZero (H.g k) := fun k => ⟨(H.g_prime k).ne_zero⟩
  simp only [NTypes.e0, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
  refine finsum_induction (· ∈ S) (zero_mem S) (fun _ _ => add_mem) fun a => ?_
  split_ifs
  · exact prod_mem fun _ _ => hS _ _ _
  · exact zero_mem S


set_option synthInstance.maxHeartbeats 400000 in
def types0 [IsEmpty N.Loc] (hl : ∀ k w (p : A.LP w), A.items₂ k w p = (X - 1) ^ A.lpDim p)
    (hi : ∀ w (p : A.LP w) σ, A.inePol p σ = (X - 1) ^ A.lpDim p)
    (hc : ∀ k, H.g k % (H.QS * H.q * H.d) = 1)
    (hB : Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)))
    (tg : ∀ k, N.PlG k → G H.E N.Om) (htg : ∀ k v, TameGenAt (N.plOm.1 (A.plGw k v)) (tg k v))
    {n : ℕ} (e : ∀ k, (ZMod (H.g k))[X] → MonoidAlgebra ℂ (GL (Fin R.r) (ZMod (H.g k))))
    (he : ∀ k, IsSer R.r (H.g k) n (e k)) : NTypes A where
  Mray := H.K
  Mray_gal := inferInstance
  Mray_ab := fun σ τ => Subsingleton.elim _ _
  Mray_unr := fun p _ h => by
    rw [GaloisStage.discr_K, dvd_neg] at h
    exact Dvd.dvd.mul_left (by exact_mod_cast h) _
  g_Mray := fun k => GaloisStage.split_K H (H.g_prime k) (hc k)
  g_cond := hc
  BB_disj := hB
  bc := fun _ => {(R.r, 1)}
  bc_pos := fun _ p hp => by
    have := GaloisStage.two_le_r R
    rw [Multiset.mem_singleton.1 hp]
    exact ⟨by show 0 < R.r; omega, one_pos⟩
  bc_sum := fun _ => by simp
  rbar := fun _ _ => 1
  rbar_open := fun _ _ => by
    rw [MonoidHom.ker_one]
    exact isOpen_univ
  tg := tg
  tg_mem := fun k v => (htg k v).1
  tg_gen := htg
  iota := fun k _ w =>
    (@GaloisStage.exists_iota (H.g k) _ ⟨H.g_prime k⟩ ⟨what₂.places.resChar_prime w⟩).choose
  iota_inj := fun k _ w =>
    (@GaloisStage.exists_iota (H.g k) _ ⟨H.g_prime k⟩ ⟨what₂.places.resChar_prime w⟩).choose_spec
  teichC := fun k => (@GaloisStage.exists_teichC (H.g k) ⟨H.g_prime k⟩).choose
  teichC_inj := fun k => (@GaloisStage.exists_teichC (H.g k) ⟨H.g_prime k⟩).choose_spec
  inertiaCharpoly_type := fun k v L _ => by
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    rw [hi, hl, GaloisStage.rootsBar_unip, Multiset.map_replicate, Multiset.prod_replicate, map_one, C_1]
  eSer := e
  eSer_idem := fun k => (he k).idem
  eSer_central := fun k => (he k).central
  eSer_orth := fun k => (he k).orth
  eSer_zero := fun k f => ((he k).zero f).2
  eSer_sum := fun k => (he k).sum
  cenAmb := fun _ => GaloisStage.cenTriv _ _
  cenMt := fun _ _ => GaloisStage.cenTriv _ _
  Par := Empty
  labPar := fun _ σ => σ.elim
  labPar_monic := fun _ σ => σ.elim
  locPar := fun σ => σ.elim
  locPar_dim := fun σ => σ.elim
  labPar_def := fun _ σ => σ.elim
  MtPar := fun _ _ σ => σ.elim
  AmbPar := fun _ σ => σ.elim
  heckeLoc_gamma_places := fun i => isEmptyElim i
  chiT_tg := fun i => isEmptyElim i

end Types

theorem isGood_comp {n g : ℕ} [Fact g.Prime] {P Q J : Type} (e : P ≃ Q) {f : Q → (ZMod g)[X]}
    {χ : Q → J → (ZMod g)ˣ} (h : Formalism.CyclotomicNorms.IsGood n g f χ) :
    Formalism.CyclotomicNorms.IsGood n g (fun v => f (e v)) (fun v => χ (e v)) := by
  obtain ⟨h1, h2, h3, h4, h5, v, h6⟩ := h
  refine ⟨fun v => h1 _, fun v => h2 _, fun l hl hb v => h3 l hl hb _, fun l hl hb v => h4 l hl hb _,
    fun a ha hb => ?_, e.symm v, by simpa using h6⟩
  obtain ⟨v, hv⟩ := h5 a ha hb
  exact ⟨e.symm v, by simpa using hv⟩

theorem adjoin_le (B : Base) : ∀ z ∈ IntermediateField.adjoin ℚ
    {Complex.exp (2 * Real.pi * Complex.I / (B.toPre.restRowsFiniteGroupCard : ℕ))}, z ∈ (B.LL0.toSubfield.map B.embLL).toSubring := by
  have h3 : IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (B.toPre.restRowsFiniteGroupCard : ℕ))} ≤
      (B.LL0.toSubfield.map B.embLL).toIntermediateField
        (fun q => by simpa using ratCast_mem (B.LL0.toSubfield.map B.embLL) q) := by
    rw [IntermediateField.adjoin_simple_le_iff]
    obtain ⟨z, hz, hz'⟩ := B.roots_Ks _ List.mem_cons_self
    exact ⟨z, B.Ks_le hz, hz'⟩
  exact fun z hz => h3 hz

end GlobalTheory.MemN.TypesInhab
