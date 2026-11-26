module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.IrrTI
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DerCont

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DerExt
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

section Cofinal

variable {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]

private theorem artinian_quot (j : ℕ) : IsArtinianRing (B ⧸ maximalIdeal B ^ j) := by
  have : Ring.KrullDimLE 0 (B ⧸ maximalIdeal B ^ j) := by
    refine Ring.krullDimLE_zero_iff.2 fun P hP => ?_
    have hc : (P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j))).IsPrime := Ideal.comap_isPrime _ _
    have hle : maximalIdeal B ≤ P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) := fun x hx => by
      refine hc.mem_of_pow_mem j ?_
      have : Ideal.Quotient.mk (maximalIdeal B ^ j) (x ^ j) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hx j)
      show Ideal.Quotient.mk _ (x ^ j) ∈ P
      rw [this]
      exact zero_mem _
    have he : P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) = maximalIdeal B :=
      ((maximalIdeal.isMaximal B).eq_of_le hc.ne_top hle).symm
    refine ⟨⟨hP.ne_top, fun J hJ => ?_⟩⟩
    by_contra hne
    have hc' : J.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) ≠ ⊤ := fun h =>
      hne (by rw [Ideal.eq_top_iff_one]; simpa using (Ideal.eq_top_iff_one _).1 h)
    have h1 : J.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) = P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) :=
      le_antisymm ((le_maximalIdeal hc').trans he.ge) (Ideal.comap_mono hJ.le)
    exact hJ.ne' (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective h1)
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

private theorem stab (I : ℕ → Ideal B) (hI : Antitone I) (j : ℕ) :
    ∃ e, ∀ N, e ≤ N → ∀ a ∈ I e, ∃ b ∈ I N, a - b ∈ maximalIdeal B ^ j := by
  haveI := artinian_quot (B := B) j
  let f : ℕ →o (Ideal (B ⧸ maximalIdeal B ^ j))ᵒᵈ :=
    ⟨fun N => OrderDual.toDual ((I N).map (Ideal.Quotient.mk _)), fun a b h => Ideal.map_mono (hI h)⟩
  obtain ⟨e, he⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨e, fun N hN a ha => ?_⟩
  have h1 : Ideal.Quotient.mk (maximalIdeal B ^ j) a ∈ (I N).map (Ideal.Quotient.mk _) := by
    have h2 : (I e).map (Ideal.Quotient.mk (maximalIdeal B ^ j)) = (I N).map (Ideal.Quotient.mk _) := he N hN
    rw [← h2]
    exact Ideal.mem_map_of_mem _ ha
  obtain ⟨b, hb, h3⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h1
  exact ⟨b, hb, Ideal.Quotient.eq.1 h3.symm⟩

private theorem cofinal [IsAdicComplete (maximalIdeal B) B] (I : ℕ → Ideal B) (hI : Antitone I)
    (h0 : ⨅ N, I N = ⊥) (k : ℕ) : ∃ N, I N ≤ maximalIdeal B ^ k := by
  by_contra hcon
  push_neg at hcon
  choose e he using fun j => stab I hI (k + j)

  let E : ℕ → ℕ := fun j => (Finset.range (j + 1)).sup e + j
  have hE : Monotone E := monotone_nat_of_le_succ fun j =>
    Nat.add_le_add (Finset.sup_mono (Finset.range_mono (Nat.le_succ _))) (Nat.le_succ _)
  have hEe : ∀ j, e j ≤ E j := fun j =>
    le_trans (Finset.le_sup (f := e) (Finset.self_mem_range_succ j)) (Nat.le_add_right _ _)
  have hEj : ∀ j, j ≤ E j := fun j => Nat.le_add_left _ _
  let P : ℕ → B → Prop := fun j x => x ∈ I (E j) ∧ x ∉ maximalIdeal B ^ k
  have step : ∀ j x, P j x → ∃ y, P (j + 1) y ∧ x - y ∈ maximalIdeal B ^ (k + j) := by
    rintro j x ⟨h1, h2⟩
    obtain ⟨y, hy, hd⟩ := he j (E (j + 1)) ((hEe j).trans (hE (Nat.le_succ j))) x (hI (hEe j) h1)
    refine ⟨y, ⟨hy, fun h => h2 ?_⟩, hd⟩
    have := add_mem (Ideal.pow_le_pow_right (Nat.le_add_right k j) hd) h
    rwa [sub_add_cancel] at this
  obtain ⟨x₀, h1, h2⟩ := SetLike.not_le_iff_exists.1 (hcon (E 0))
  let a : ∀ j, {x // P j x} := fun j => Nat.rec ⟨x₀, h1, h2⟩
    (fun j x => ⟨(step j x.1 x.2).choose, (step j x.1 x.2).choose_spec.1⟩) j
  have ha : ∀ j, (a j).1 - (a (j + 1)).1 ∈ maximalIdeal B ^ (k + j) := fun j =>
    (step j (a j).1 (a j).2).choose_spec.2
  have hchain : ∀ m n, m ≤ n → (a m).1 - (a n).1 ∈ maximalIdeal B ^ (k + m) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem ih (Ideal.pow_le_pow_right (Nat.add_le_add_left hmn k) (ha n))
      rwa [sub_add_sub_cancel] at this
  have hsm : ∀ j : ℕ, (maximalIdeal B ^ j • ⊤ : Ideal B) = maximalIdeal B ^ j := fun j => by simp
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := maximalIdeal B) (M := B) inferInstance
    (f := fun j => (a j).1) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm]
      exact Ideal.pow_le_pow_right (Nat.le_add_left _ _) (hchain m n hmn))
  have hL' : ∀ j, (a j).1 - L ∈ maximalIdeal B ^ j := fun j => by
    have := SModEq.sub_mem.1 (hL j)
    simpa using this
  have hmem : ∀ N, L ∈ I N := by
    intro N
    by_cases hNt : I N = ⊤
    · simp [hNt]
    have hb : ⨅ i, maximalIdeal B ^ i • (⊤ : Submodule B (B ⧸ I N)) = ⊥ :=
      Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal B).ne_top
    have : Ideal.Quotient.mk (I N) L ∈ (⊥ : Submodule B (B ⧸ I N)) := by
      rw [← hb]
      refine (Submodule.mem_iInf _).2 fun j => ?_
      have h3 : (a (max j N)).1 ∈ I N := hI ((le_max_right j N).trans (hEj _)) (a (max j N)).2.1
      have h4 := Ideal.pow_le_pow_right (le_max_left j N) (hL' (max j N))
      have h5 : Ideal.Quotient.mk (I N) L = ((a (max j N)).1 - L) • (-1 : B ⧸ I N) := by
        rw [Algebra.smul_def]
        have : Ideal.Quotient.mk (I N) (a (max j N)).1 = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h3
        simp [Ideal.Quotient.algebraMap_eq, this]
      rw [h5]
      exact Submodule.smul_mem_smul h4 trivial
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  have hz : L = 0 := by
    have : L ∈ ⨅ N, I N := (Submodule.mem_iInf _).2 hmem
    rwa [h0] at this
  have := hL' k
  rw [hz, sub_zero] at this
  have h6 := (a k).2.2
  exact h6 this

end Cofinal

section Der

variable {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing K] [Algebra O K]

private theorem kill (A : Subalgebra O R) (ξ : A →ₐ[O] K) (D : A →ₗ[O] K)
    (hD : ∀ f g, D (f * g) = ξ f * D g + ξ g * D f) (s : Set R)
    (h : ∀ x ∈ s, ∃ hx : x ∈ A, D ⟨x, hx⟩ = 0) {x : R} (hx : x ∈ Algebra.adjoin O s) :
    ∃ h : x ∈ A, D ⟨x, h⟩ = 0 := by
  have h1 : D 1 = 0 := by
    have := hD 1 1
    simp only [mul_one, map_one, one_mul] at this
    linear_combination (-1 : K) * this
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap a =>
    refine ⟨A.algebraMap_mem a, ?_⟩
    have : (⟨algebraMap O R a, A.algebraMap_mem a⟩ : A) = a • (1 : A) := by
      ext
      simp [Algebra.smul_def]
    rw [this, map_smul, h1, smul_zero]
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨add_mem a b, ?_⟩
    have : (⟨x + y, add_mem a b⟩ : A) = ⟨x, a⟩ + ⟨y, b⟩ := rfl
    rw [this, map_add (f := _), ha, hb, add_zero]
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨mul_mem a b, ?_⟩
    have : (⟨x * y, mul_mem a b⟩ : A) = ⟨x, a⟩ * ⟨y, b⟩ := rfl
    rw [this, hD, ha, hb, mul_zero, mul_zero, add_zero]

end Der

section Close

variable {O R K : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
  [NormedField K] [Algebra O K]

private theorem close_zero (B : Subalgebra O R) [hB : IsCO O B]
    (hm : maximalIdeal B = (maximalIdeal R).comap (B.val : B →+* R)) (E : B →ₗ[O] K)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a ∈ maximalIdeal B ^ k, ‖E a‖ ≤ ε) (T : Set B) (hT : ∀ t ∈ T, E t = 0)
    (hd : ∀ x : B, ∀ N : ℕ, ∃ t ∈ T, ((x - t : B) : R) ∈ maximalIdeal R ^ N) : E = 0 := by
  let I : ℕ → Ideal B := fun N => (maximalIdeal R ^ N).comap (B.val : B →+* R)
  have hI : Antitone I := fun a b h => Ideal.comap_mono (Ideal.pow_le_pow_right h)
  have h0 : ⨅ N, I N = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have h1 : (x : R) ∈ ⨅ N : ℕ, maximalIdeal R ^ N := (Submodule.mem_iInf _).2 fun N =>
      (Submodule.mem_iInf _).1 hx N
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top, Ideal.mem_bot] at h1
    exact Subtype.ext h1
  ext x
  by_contra hne
  have hpos : 0 < ‖E x‖ / 2 := half_pos (norm_pos_iff.2 hne)
  obtain ⟨k, hk⟩ := hc _ hpos
  obtain ⟨N, hN⟩ := cofinal I hI h0 k
  obtain ⟨t, ht, hd'⟩ := hd x N
  have h2 := hk (x - t) (hN hd')
  rw [map_sub, hT t ht, sub_zero] at h2
  linarith

end Close

set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.V.J.derExt :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, ∀ D ∈ PtDer ξ (Qbar l), (∀ g i j, D (S.u.r g i j) = 0) → (∀ v i g, D (S.u.ψ v i g : S.A) = 0) → D = 0 := by
  intro l _ c _ F C₀ n hF hn S ξ D hD hr hψ
  obtain ⟨hco, hm⟩ := Fr.co_B hF hn S
  haveI := hco
  have hD' : ∀ f g, D (f * g) = ξ f * D g + ξ g * D f := hD

  have hs : ∀ x ∈ ({x | ∃ g i j, x = S.ρ.r g i j} ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)} : Set S.R),
      ∃ hx : x ∈ S.A, D ⟨x, hx⟩ = 0 := by
    rintro x (⟨g, i, j, rfl⟩ | ⟨v, i, g, rfl⟩)
    · exact ⟨S.r_mem g i j, hr g i j⟩
    · exact ⟨S.B_le_A (S.ψ_mem v i g), hψ v i g⟩
  have hadj : Algebra.adjoin c.O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) ≤
      Algebra.adjoin c.O ({x | ∃ g i j, x = S.ρ.r g i j} ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) := by
    refine Algebra.adjoin_le ?_
    rintro x (⟨L, -, rfl⟩ | hx)
    · refine Subalgebra.list_prod_mem _ fun y hy => ?_
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hy
      exact Algebra.subset_adjoin (Or.inl ⟨_, _, _, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inr hx)

  have hB : D ∘ₗ S.inc.toLinearMap = 0 := by
    refine close_zero S.B (hm.trans rfl) _ (fun ε hε => ?_)
      {t | (t : S.R) ∈ Algebra.adjoin c.O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)})} (fun t ht => ?_)
      (fun x N => ?_)
    · have hDB : D ∘ₗ S.inc.toLinearMap ∈ PtDer (ξ.comp S.inc) (Qbar l) := fun f g => by
        simpa using hD (S.inc f) (S.inc g)
      obtain ⟨k, hk⟩ := derCont l c S.B (ξ.comp S.inc) _ hDB ε hε
      exact ⟨k, fun a ha => (hk a ha).1⟩
    · obtain ⟨_, h⟩ := kill S.A ξ D hD' _ hs (hadj ht)
      exact h
    · obtain ⟨y, hy, h⟩ := x.2 N
      exact ⟨⟨y, Fr.le_adicClosure _ hy⟩, hy, h⟩

  ext ⟨x, hx⟩
  obtain ⟨_, h⟩ := kill S.A ξ D hD' ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j}) (by
    rintro x (hx | ⟨g, i, j, rfl⟩)
    · exact ⟨S.B_le_A hx, LinearMap.congr_fun hB ⟨x, hx⟩⟩
    · exact ⟨S.r_mem g i j, hr g i j⟩) hx
  exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FreeEtaleSheafZmodExistsHomSendingGenerator
set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

namespace UpperTheory.V.J.TorusDerivation

open Matrix

variable {K : Type} [Field K]

private theorem offDiag_zero {n : ℕ} (X Z : Matrix (Fin n) (Fin n) K) (hZ : ∀ i j, i ≠ j → Z i j = 0)
    (hd : ∀ i j, i ≠ j → Z i i ≠ Z j j) (h : ∀ i j, i ≠ j → (X * Z - Z * X) i j = 0) :
    ∀ i j, i ≠ j → X i j = 0 := by
  intro i j hij
  have hZd : Z = Matrix.diagonal fun i => Z i i := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, hZ a b hab]
  have h1 := h i j hij
  rw [hZd] at h1
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have h2 : X i j * (Z j j - Z i i) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.1 h3).symm (hd i j hij)

private theorem scalar_of_irr {G : Type} [Group G] {m : ℕ} (a : G → Matrix (Fin m) (Fin m) K)
    (hI : MatIrr (⊤ : Subgroup G) a) (y : Fin m → K)
    (hc : ∀ g i j, (y i - y j) * a g i j = 0) (i j : Fin m) : y i = y j := by
  classical
  have hcm : ∀ g, (Matrix.diagonal y - y i • (1 : Matrix (Fin m) (Fin m) K)) * a g =
      a g * (Matrix.diagonal y - y i • (1 : Matrix (Fin m) (Fin m) K)) := by
    intro g
    ext p q
    have := hc g p q
    simp only [sub_mul, mul_sub, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul]
    linear_combination this
  have hW := hI (LinearMap.ker (Matrix.mulVecLin (Matrix.diagonal y - y i • (1 : Matrix (Fin m) (Fin m) K))))
    (fun g _ v hv => by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
      rw [Matrix.mulVec_mulVec, hcm, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero])
  have hmem : Pi.single i (1 : K) ∈ LinearMap.ker
      (Matrix.mulVecLin (Matrix.diagonal y - y i • (1 : Matrix (Fin m) (Fin m) K))) := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    ext p
    by_cases hp : p = i
    · subst hp
      simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.mulVec_diagonal]
    · simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.mulVec_diagonal, hp]
  rcases hW with hW | hW
  · rw [hW, Submodule.mem_bot] at hmem
    have := congrFun hmem i
    simp at this
  · have h2 : Pi.single j (1 : K) ∈ LinearMap.ker
        (Matrix.mulVecLin (Matrix.diagonal y - y i • (1 : Matrix (Fin m) (Fin m) K))) := by
      rw [hW]; trivial
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
    have := congrFun h2 j
    simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.mulVec_diagonal] at this
    have h3 : y j = y i := by linear_combination this
    exact h3.symm

private theorem J_entry {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Jmat R n * Mᵀ * Jmat R n) i j = M j.rev i.rev := by
  have hJ : ∀ a b : Fin n, Jmat R n a b = if b = a.rev then 1 else 0 := fun _ _ => rfl
  have h1 : ∀ b, (Jmat R n * Mᵀ) i b = M b i.rev := by
    intro b
    rw [Matrix.mul_apply, Finset.sum_eq_single i.rev (fun c _ hc => by rw [hJ, if_neg hc, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h), hJ, if_pos rfl, one_mul, Matrix.transpose_apply]
  rw [Matrix.mul_apply, Finset.sum_eq_single j.rev (fun c _ hc => by
      rw [hJ, if_neg (fun h => hc (by rw [h, Fin.rev_rev])), mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), hJ, if_pos (Fin.rev_rev j).symm, mul_one, h1]

private theorem free_etale_sheaf_zmod_exists_hom_sending_generator [CharZero K] {n : ℕ} (hn : n = 2 ∨ n = 3) (x : Fin n → K)
    (h : ∀ i j, x i + x i.rev = x j + x j.rev) :
    ∃ t : K, ∀ i j, x i - x j = t * ((Fr.w n i - Fr.w n j : ℤ) : K) := by
  rcases hn with rfl | rfl
  · refine ⟨(x 0 - x 1) / 2, fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;> simp [Fr.w] <;> ring
  · have h1 : x 0 + x 2 = x 1 + x 1 := by simpa [Fin.rev] using h 0 1
    refine ⟨x 0 - x 1, fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;> simp [Fr.w] <;> first | ring1 | linear_combination h1 | linear_combination (-1 : K) * h1

private theorem der_mul {A : Type} [CommRing A] {n : ℕ} (ξ : A →+* K) (D : A →+ K)
    (hD : ∀ f g, D (f * g) = ξ f * D g + ξ g * D f) (P Q : Matrix (Fin n) (Fin n) A) :
    (P * Q).map D = P.map ξ * Q.map D + P.map D * Q.map ξ := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_sum, hD, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

private theorem der_shift {A : Type} [CommRing A] {n : ℕ} (ξ : A →+* K) (D : A →+ K)
    (hD : ∀ f g, D (f * g) = ξ f * D g + ξ g * D f) (X : Matrix (Fin n) (Fin n) K)
    (R : Matrix (Fin n) (Fin n) A) (p : A) (hR : R.map D = X * R.map ξ - R.map ξ * X) :
    (R - p • (1 : Matrix (Fin n) (Fin n) A)).map ξ = R.map ξ - ξ p • (1 : Matrix (Fin n) (Fin n) K) ∧
    (R - p • (1 : Matrix (Fin n) (Fin n) A)).map D =
      X * (R.map ξ - ξ p • (1 : Matrix (Fin n) (Fin n) K)) - (R.map ξ - ξ p • (1 : Matrix (Fin n) (Fin n) K)) * X
        - D p • (1 : Matrix (Fin n) (Fin n) K) := by
  have h1 : D 1 = 0 := by
    have := hD 1 1
    simp only [mul_one, map_one, one_mul] at this
    linear_combination -this
  constructor
  · ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  · have h2 : (R - p • (1 : Matrix (Fin n) (Fin n) A)).map D = R.map D - D p • (1 : Matrix (Fin n) (Fin n) K) := by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · simp [h]
    rw [h2, hR]
    simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    abel

private theorem ordDer2 {A : Type} [CommRing A] {n : ℕ} (ξ : A →+* K) (D : A →+ K)
    (hD : ∀ f g, D (f * g) = ξ f * D g + ξ g * D f) (X : Matrix (Fin n) (Fin n) K)
    (R₀ R₁ : Matrix (Fin n) (Fin n) A) (p₀ p₁ : A)
    (h₀ : R₀.map D = X * R₀.map ξ - R₀.map ξ * X) (h₁ : R₁.map D = X * R₁.map ξ - R₁.map ξ * X)
    (h : (R₀ - p₀ • (1 : Matrix (Fin n) (Fin n) A)) * (R₁ - p₁ • (1 : Matrix (Fin n) (Fin n) A)) = 0) :
    (R₀.map ξ - ξ p₀ • (1 : Matrix (Fin n) (Fin n) K)) * (R₁.map ξ - ξ p₁ • (1 : Matrix (Fin n) (Fin n) K)) = 0 ∧
    D p₀ • (R₁.map ξ - ξ p₁ • (1 : Matrix (Fin n) (Fin n) K)) +
      D p₁ • (R₀.map ξ - ξ p₀ • (1 : Matrix (Fin n) (Fin n) K)) = 0 := by
  obtain ⟨a₀, b₀⟩ := der_shift ξ D hD X R₀ p₀ h₀
  obtain ⟨a₁, b₁⟩ := der_shift ξ D hD X R₁ p₁ h₁
  have hz := der_mul ξ D hD (R₀ - p₀ • (1 : Matrix (Fin n) (Fin n) A)) (R₁ - p₁ • (1 : Matrix (Fin n) (Fin n) A))
  have hm := congrArg ξ.mapMatrix h
  rw [map_mul, map_zero, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, a₀, a₁] at hm
  rw [a₀, a₁, b₀, b₁, h] at hz
  set M₀ := R₀.map ξ - ξ p₀ • (1 : Matrix (Fin n) (Fin n) K)
  set M₁ := R₁.map ξ - ξ p₁ • (1 : Matrix (Fin n) (Fin n) K)
  have hm' : M₀ * M₁ = 0 := hm
  refine ⟨hm', ?_⟩
  have h0 : (0 : Matrix (Fin n) (Fin n) A).map D = 0 := by ext; simp
  rw [h0] at hz
  have e : M₀ * (X * M₁ - M₁ * X - D p₁ • (1 : Matrix (Fin n) (Fin n) K)) +
      (X * M₀ - M₀ * X - D p₀ • (1 : Matrix (Fin n) (Fin n) K)) * M₁ =
      X * (M₀ * M₁) - (M₀ * M₁) * X - (D p₀ • M₁ + D p₁ • M₀) := by
    simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, ← mul_assoc]
    abel
  rw [e, hm'] at hz
  rw [mul_zero, zero_mul, sub_zero, zero_sub] at hz
  exact neg_eq_zero.1 hz.symm

private theorem ordDer3 {A : Type} [CommRing A] {n : ℕ} (ξ : A →+* K) (D : A →+ K)
    (hD : ∀ f g, D (f * g) = ξ f * D g + ξ g * D f) (X : Matrix (Fin n) (Fin n) K)
    (R₀ R₁ R₂ : Matrix (Fin n) (Fin n) A) (p₀ p₁ p₂ : A)
    (h₀ : R₀.map D = X * R₀.map ξ - R₀.map ξ * X) (h₁ : R₁.map D = X * R₁.map ξ - R₁.map ξ * X)
    (h₂ : R₂.map D = X * R₂.map ξ - R₂.map ξ * X)
    (h : (R₀ - p₀ • (1 : Matrix (Fin n) (Fin n) A)) * ((R₁ - p₁ • (1 : Matrix (Fin n) (Fin n) A)) *
      (R₂ - p₂ • (1 : Matrix (Fin n) (Fin n) A))) = 0) :
    (R₀.map ξ - ξ p₀ • (1 : Matrix (Fin n) (Fin n) K)) * ((R₁.map ξ - ξ p₁ • (1 : Matrix (Fin n) (Fin n) K)) *
      (R₂.map ξ - ξ p₂ • (1 : Matrix (Fin n) (Fin n) K))) = 0 ∧
    D p₀ • ((R₁.map ξ - ξ p₁ • (1 : Matrix (Fin n) (Fin n) K)) * (R₂.map ξ - ξ p₂ • (1 : Matrix (Fin n) (Fin n) K))) +
      D p₁ • ((R₀.map ξ - ξ p₀ • (1 : Matrix (Fin n) (Fin n) K)) * (R₂.map ξ - ξ p₂ • (1 : Matrix (Fin n) (Fin n) K))) +
      D p₂ • ((R₀.map ξ - ξ p₀ • (1 : Matrix (Fin n) (Fin n) K)) * (R₁.map ξ - ξ p₁ • (1 : Matrix (Fin n) (Fin n) K))) = 0 := by
  obtain ⟨a₀, b₀⟩ := der_shift ξ D hD X R₀ p₀ h₀
  obtain ⟨a₁, b₁⟩ := der_shift ξ D hD X R₁ p₁ h₁
  obtain ⟨a₂, b₂⟩ := der_shift ξ D hD X R₂ p₂ h₂
  have hz := der_mul ξ D hD (R₀ - p₀ • (1 : Matrix (Fin n) (Fin n) A))
    ((R₁ - p₁ • (1 : Matrix (Fin n) (Fin n) A)) * (R₂ - p₂ • (1 : Matrix (Fin n) (Fin n) A)))
  have hz' := der_mul ξ D hD (R₁ - p₁ • (1 : Matrix (Fin n) (Fin n) A)) (R₂ - p₂ • (1 : Matrix (Fin n) (Fin n) A))
  have hm := congrArg ξ.mapMatrix h
  rw [map_mul, map_mul, map_zero, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
    RingHom.mapMatrix_apply, a₀, a₁, a₂] at hm
  have hmm : ((R₁ - p₁ • (1 : Matrix (Fin n) (Fin n) A)) * (R₂ - p₂ • (1 : Matrix (Fin n) (Fin n) A))).map ξ =
      (R₁.map ξ - ξ p₁ • (1 : Matrix (Fin n) (Fin n) K)) * (R₂.map ξ - ξ p₂ • (1 : Matrix (Fin n) (Fin n) K)) := by
    rw [← RingHom.mapMatrix_apply, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, a₁, a₂]
  rw [hz', hmm, a₀, a₁, a₂, b₀, b₁, b₂, h] at hz
  set M₀ := R₀.map ξ - ξ p₀ • (1 : Matrix (Fin n) (Fin n) K)
  set M₁ := R₁.map ξ - ξ p₁ • (1 : Matrix (Fin n) (Fin n) K)
  set M₂ := R₂.map ξ - ξ p₂ • (1 : Matrix (Fin n) (Fin n) K)
  have hm' : M₀ * (M₁ * M₂) = 0 := hm
  refine ⟨hm', ?_⟩
  have h0 : (0 : Matrix (Fin n) (Fin n) A).map D = 0 := by ext; simp
  rw [h0] at hz
  have e : M₀ * (M₁ * (X * M₂ - M₂ * X - D p₂ • (1 : Matrix (Fin n) (Fin n) K)) +
      (X * M₁ - M₁ * X - D p₁ • (1 : Matrix (Fin n) (Fin n) K)) * M₂) +
      (X * M₀ - M₀ * X - D p₀ • (1 : Matrix (Fin n) (Fin n) K)) * (M₁ * M₂) =
      X * (M₀ * (M₁ * M₂)) - (M₀ * (M₁ * M₂)) * X -
        (D p₀ • (M₁ * M₂) + D p₁ • (M₀ * M₂) + D p₂ • (M₀ * M₁)) := by
    simp only [mul_sub, sub_mul, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, ← mul_assoc]
    abel
  rw [e, hm'] at hz
  rw [mul_zero, zero_mul, sub_zero, zero_sub] at hz
  exact neg_eq_zero.1 hz.symm

private theorem sc_mul {n : ℕ} (R W : Matrix (Fin n) (Fin n) K) (a b : K)
    (h : (R - a • (1 : Matrix (Fin n) (Fin n) K)) * W = 0) :
    (R - b • (1 : Matrix (Fin n) (Fin n) K)) * W = (a - b) • W := by
  have h1 : R * W = a • W := by
    rw [sub_mul, sub_eq_zero] at h
    simpa using h
  rw [sub_mul, h1, sub_smul]
  simp

private theorem sc_comm {n : ℕ} (R : Matrix (Fin n) (Fin n) K) (a b : K) :
    (R - a • (1 : Matrix (Fin n) (Fin n) K)) * (R - b • (1 : Matrix (Fin n) (Fin n) K)) =
      (R - b • (1 : Matrix (Fin n) (Fin n) K)) * (R - a • (1 : Matrix (Fin n) (Fin n) K)) := by
  simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul, mul_comm a b]
  abel

private theorem smul_cancel {n : ℕ} {s : K} {W : Matrix (Fin n) (Fin n) K} (h : s • W = 0) (hW : W ≠ 0) : s = 0 := by
  by_contra hs
  refine hW ?_
  ext i j
  have h1 : s * W i j = 0 := congrFun (congrFun h i) j
  exact (mul_eq_zero.1 h1).resolve_left hs

private theorem kill3 {n : ℕ} (R : Matrix (Fin n) (Fin n) K) (a b c d e f : K) (hab : a ≠ b) (hac : a ≠ c)
    (hW : (R - b • (1 : Matrix (Fin n) (Fin n) K)) * (R - c • (1 : Matrix (Fin n) (Fin n) K)) ≠ 0)
    (h : (R - a • (1 : Matrix (Fin n) (Fin n) K)) * ((R - b • (1 : Matrix (Fin n) (Fin n) K)) *
      (R - c • (1 : Matrix (Fin n) (Fin n) K))) = 0)
    (hT : d • ((R - b • (1 : Matrix (Fin n) (Fin n) K)) * (R - c • (1 : Matrix (Fin n) (Fin n) K))) +
      e • ((R - a • (1 : Matrix (Fin n) (Fin n) K)) * (R - c • (1 : Matrix (Fin n) (Fin n) K))) +
      f • ((R - a • (1 : Matrix (Fin n) (Fin n) K)) * (R - b • (1 : Matrix (Fin n) (Fin n) K))) = 0) : d = 0 := by
  set W := (R - b • (1 : Matrix (Fin n) (Fin n) K)) * (R - c • (1 : Matrix (Fin n) (Fin n) K)) with hWd
  have hb := sc_mul R W a b h
  have hc := sc_mul R W a c h
  have h1 := congrArg (· * W) hT
  simp only [add_mul, Matrix.smul_mul, zero_mul] at h1
  have e1 : W * W = ((a - b) * (a - c)) • W := by
    nth_rw 1 [hWd]
    rw [mul_assoc, hc, Matrix.mul_smul, hb, smul_smul, mul_comm]
  have e2 : (R - a • (1 : Matrix (Fin n) (Fin n) K)) * (R - c • (1 : Matrix (Fin n) (Fin n) K)) * W = 0 := by
    rw [mul_assoc, hc, Matrix.mul_smul, h, smul_zero]
  have e3 : (R - a • (1 : Matrix (Fin n) (Fin n) K)) * (R - b • (1 : Matrix (Fin n) (Fin n) K)) * W = 0 := by
    rw [mul_assoc, hb, Matrix.mul_smul, h, smul_zero]
  rw [e1, e2, e3] at h1
  simp only [smul_zero, add_zero, smul_smul] at h1
  rcases mul_eq_zero.1 (smul_cancel h1 hW) with h3 | h3
  · exact h3
  · exact absurd h3 (mul_ne_zero (sub_ne_zero.2 hab) (sub_ne_zero.2 hac))

private theorem kill2 {n : ℕ} (R : Matrix (Fin n) (Fin n) K) (a b d e : K) (hab : a ≠ b)
    (hW : R - b • (1 : Matrix (Fin n) (Fin n) K) ≠ 0)
    (h : (R - a • (1 : Matrix (Fin n) (Fin n) K)) * (R - b • (1 : Matrix (Fin n) (Fin n) K)) = 0)
    (hT : d • (R - b • (1 : Matrix (Fin n) (Fin n) K)) + e • (R - a • (1 : Matrix (Fin n) (Fin n) K)) = 0) : d = 0 := by
  set W := R - b • (1 : Matrix (Fin n) (Fin n) K) with hWd
  have hb := sc_mul R W a b h
  have h1 := congrArg (· * W) hT
  simp only [add_mul, Matrix.smul_mul, zero_mul] at h1
  have e1 : W * W = (a - b) • W := by
    nth_rw 1 [hWd]
    exact hb
  rw [e1, h] at h1
  simp only [smul_zero, add_zero, smul_smul] at h1
  rcases mul_eq_zero.1 (smul_cancel h1 hW) with h3 | h3
  · exact h3
  · exact absurd h3 (sub_ne_zero.2 hab)

end UpperTheory.V.J.TorusDerivation

namespace UpperTheory.V.J.TorusDerivation

open Matrix

variable {K : Type} [Field K]

private theorem comm_entry {n : ℕ} (X M : Matrix (Fin n) (Fin n) K) (h : ∀ i j, i ≠ j → X i j = 0) (i j : Fin n) :
    (X * M - M * X) i j = (X i i - X j j) * M i j := by
  have hX : X = Matrix.diagonal fun i => X i i := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, h a b hab]
  rw [hX]
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply_eq]
  ring

private theorem quad_entry {n : ℕ} (M M₂ : Matrix (Fin n) (Fin n) K) (hM : M₂ = M * M) (b b' : K) (k : Fin n) :
    ((M - b • (1 : Matrix (Fin n) (Fin n) K)) * (M - b' • (1 : Matrix (Fin n) (Fin n) K))) k k =
      M₂ k k - (b + b') * M k k + b * b' := by
  subst hM
  simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq]
  ring

private theorem finish2 {H : Type} {n : ℕ} (Mr : H → Matrix (Fin n) (Fin n) K) (p₀ p₁ d₀ d₁ : H → K) (s : H)
    (hL : ∀ g h, (Mr g - p₀ g • (1 : Matrix (Fin n) (Fin n) K)) * (Mr h - p₁ h • (1 : Matrix (Fin n) (Fin n) K)) = 0 ∧
      d₀ g • (Mr h - p₁ h • (1 : Matrix (Fin n) (Fin n) K)) + d₁ h • (Mr g - p₀ g • (1 : Matrix (Fin n) (Fin n) K)) = 0)
    (hab : p₀ s ≠ p₁ s) (Q₀ : Mr s - p₁ s • (1 : Matrix (Fin n) (Fin n) K) ≠ 0)
    (Q₁ : Mr s - p₀ s • (1 : Matrix (Fin n) (Fin n) K) ≠ 0) : (∀ g, d₀ g = 0) ∧ ∀ g, d₁ g = 0 := by
  have e₀ : d₀ s = 0 := kill2 (Mr s) _ _ _ (d₁ s) hab Q₀ (hL s s).1 (hL s s).2
  have e₁ : d₁ s = 0 := kill2 (Mr s) (p₁ s) (p₀ s) _ (d₀ s) hab.symm Q₁
    (by rw [sc_comm]; exact (hL s s).1) (by rw [add_comm]; exact (hL s s).2)
  refine ⟨fun g => smul_cancel (W := Mr s - p₁ s • (1 : Matrix (Fin n) (Fin n) K)) ?_ Q₀,
    fun g => smul_cancel (W := Mr s - p₀ s • (1 : Matrix (Fin n) (Fin n) K)) ?_ Q₁⟩
  · have := (hL g s).2
    rwa [e₁, zero_smul, add_zero] at this
  · have := (hL s g).2
    rwa [e₀, zero_smul, zero_add] at this

private theorem finish3 {H : Type} {n : ℕ} (Mr : H → Matrix (Fin n) (Fin n) K) (p₀ p₁ p₂ d₀ d₁ d₂ : H → K) (s : H)
    (hL : ∀ g h k, (Mr g - p₀ g • (1 : Matrix (Fin n) (Fin n) K)) * ((Mr h - p₁ h • (1 : Matrix (Fin n) (Fin n) K)) *
        (Mr k - p₂ k • (1 : Matrix (Fin n) (Fin n) K))) = 0 ∧
      d₀ g • ((Mr h - p₁ h • (1 : Matrix (Fin n) (Fin n) K)) * (Mr k - p₂ k • (1 : Matrix (Fin n) (Fin n) K))) +
      d₁ h • ((Mr g - p₀ g • (1 : Matrix (Fin n) (Fin n) K)) * (Mr k - p₂ k • (1 : Matrix (Fin n) (Fin n) K))) +
      d₂ k • ((Mr g - p₀ g • (1 : Matrix (Fin n) (Fin n) K)) * (Mr h - p₁ h • (1 : Matrix (Fin n) (Fin n) K))) = 0)
    (h01 : p₀ s ≠ p₁ s) (h02 : p₀ s ≠ p₂ s) (h12 : p₁ s ≠ p₂ s)
    (Q₀ : (Mr s - p₁ s • (1 : Matrix (Fin n) (Fin n) K)) * (Mr s - p₂ s • (1 : Matrix (Fin n) (Fin n) K)) ≠ 0)
    (Q₁ : (Mr s - p₀ s • (1 : Matrix (Fin n) (Fin n) K)) * (Mr s - p₂ s • (1 : Matrix (Fin n) (Fin n) K)) ≠ 0)
    (Q₂ : (Mr s - p₀ s • (1 : Matrix (Fin n) (Fin n) K)) * (Mr s - p₁ s • (1 : Matrix (Fin n) (Fin n) K)) ≠ 0) :
    (∀ g, d₀ g = 0) ∧ (∀ g, d₁ g = 0) ∧ ∀ g, d₂ g = 0 := by
  obtain ⟨hz, hT⟩ := hL s s s
  have e₀ : d₀ s = 0 := kill3 (Mr s) _ _ _ _ (d₁ s) (d₂ s) h01 h02 Q₀ hz hT
  have e₁ : d₁ s = 0 := by
    refine kill3 (Mr s) (p₁ s) (p₀ s) (p₂ s) _ (d₀ s) (d₂ s) h01.symm h12 Q₁ ?_ ?_
    · rw [← mul_assoc, sc_comm, mul_assoc]; exact hz
    · rw [sc_comm (Mr s) (p₁ s) (p₀ s), add_comm (d₁ s • _)]; exact hT
  have e₂ : d₂ s = 0 := by
    refine kill3 (Mr s) (p₂ s) (p₀ s) (p₁ s) _ (d₀ s) (d₁ s) h02.symm h12.symm Q₂ ?_ ?_
    · rw [← mul_assoc, sc_comm (Mr s) (p₂ s) (p₀ s), mul_assoc, sc_comm (Mr s) (p₂ s) (p₁ s)]; exact hz
    · rw [sc_comm (Mr s) (p₂ s) (p₁ s), sc_comm (Mr s) (p₂ s) (p₀ s)]
      rw [← hT]; abel
  refine ⟨fun g => smul_cancel (W := _) ?_ Q₀, fun g => smul_cancel (W := _) ?_ Q₁, fun g => smul_cancel (W := _) ?_ Q₂⟩
  · have := (hL g s s).2
    rwa [e₁, e₂, zero_smul, zero_smul, add_zero, add_zero] at this
  · have := (hL s g s).2
    rwa [e₀, e₂, zero_smul, zero_smul, zero_add, add_zero] at this
  · have := (hL s s g).2
    rwa [e₀, e₁, zero_smul, zero_smul, zero_add, zero_add] at this

private theorem ordProd2 {H A : Type} [CommRing A] (r : H → Matrix (Fin 2) (Fin 2) A) (ψ : Fin 2 → H → A) (g h : H) :
    Fr.ordProd r ψ ![g, h] = (r g - ψ 0 g • (1 : Matrix (Fin 2) (Fin 2) A)) * (r h - ψ 1 h • (1 : Matrix (Fin 2) (Fin 2) A)) := by
  simp [Fr.ordProd, List.ofFn_succ]

private theorem ordProd3 {H A : Type} [CommRing A] (r : H → Matrix (Fin 3) (Fin 3) A) (ψ : Fin 3 → H → A) (g h k : H) :
    Fr.ordProd r ψ ![g, h, k] = (r g - ψ 0 g • (1 : Matrix (Fin 3) (Fin 3) A)) *
      ((r h - ψ 1 h • (1 : Matrix (Fin 3) (Fin 3) A)) * (r k - ψ 2 k • (1 : Matrix (Fin 3) (Fin 3) A))) := by
  simp [Fr.ordProd, List.ofFn_succ]

private theorem w_ne {k : Type} [Field k] {n : ℕ} (hn : n = 2 ∨ n = 3) (ζ : kˣ) (h : ζ ^ 2 ≠ 1) (i j : Fin n)
    (hij : i ≠ j) : ((ζ ^ Fr.w n i : kˣ) : k) ≠ ((ζ ^ Fr.w n j : kˣ) : k) := by
  intro h0
  have h1 : ζ ^ Fr.w n i = ζ ^ Fr.w n j := Units.ext h0
  have h2 : ζ ^ (Fr.w n i - Fr.w n j) = 1 := by rw [_root_.zpow_sub, h1, mul_inv_cancel]
  have key : ∀ m : ℤ, (m = 1 ∨ m = -1 ∨ m = 2 ∨ m = -2) → ζ ^ m ≠ 1 := by
    have h3 : ζ ≠ 1 := fun e => h (by rw [e, one_pow])
    rintro m (rfl | rfl | rfl | rfl)
    · simpa using h3
    · simpa using h3
    · exact fun e => h (by exact_mod_cast e)
    · intro e
      refine h ?_
      have : (ζ ^ (-2 : ℤ))⁻¹ = 1 := by rw [e, inv_one]
      rw [← _root_.zpow_neg] at this
      exact_mod_cast this
  refine key _ ?_ h2
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp [Fr.w] at hij ⊢

private theorem z_ne {k : Type} [Field k] (h2 : (2 : k) ≠ 0) {n : ℕ} (hn : n = 2 ∨ n = 3) (ζ : kˣ) (h : ζ ^ 2 ≠ 1)
    (i j : Fin n) (hij : i ≠ j) :
    ((ζ ^ Fr.w n i : kˣ) : k) - ((ζ⁻¹ ^ Fr.w n i : kˣ) : k) - (((ζ ^ Fr.w n j : kˣ) : k) - ((ζ⁻¹ ^ Fr.w n j : kˣ) : k)) ≠ 0 := by
  have h3 : (ζ : k) - ((ζ⁻¹ : kˣ) : k) ≠ 0 := fun e => h (by
    have : ζ = ζ⁻¹ := Units.ext (sub_eq_zero.1 e)
    rw [sq]; nth_rw 1 [this]; simp)
  rw [Units.val_inv_eq_inv_val] at h3
  have h5 : (2 : k) * ((ζ : k) - (ζ : k)⁻¹) ≠ 0 := mul_ne_zero h2 h3
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp [Fr.w] at hij ⊢
  all_goals
    intro e
    first
      | exact h3 (by linear_combination e)
      | exact h3 (by linear_combination (-1 : k) * e)
      | exact h5 (by linear_combination e)
      | exact h5 (by linear_combination (-1 : k) * e)

end UpperTheory.V.J.TorusDerivation

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.J.TorusDerivation

open Matrix

variable {l : ℕ} [Fact l.Prime] {c : Coef l} [Fr.IsCoef l c.O] {F : Fr.Frame l (ResidueField c.O)} {n : ℕ}

private theorem ne_of_res (S : Fr.Space c.O F n) (ξ : S.A →ₐ[c.O] Qbar l) (hξ : IntPt S ξ) (b : S.B)
    (hb : res c.O S.R (b : S.R) ≠ 0) : ξ (S.inc b) ≠ 0 := by
  intro h0
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := c.O) (b : S.R)
  have hu : IsUnit a := by
    by_contra hn
    have h1 : algebraMap c.O S.R a ∈ maximalIdeal S.R := by
      have h2 : a ∈ maximalIdeal c.O := hn
      have h3 : ¬ IsUnit (algebraMap c.O S.R a) := fun h => hn (isUnit_of_map_unit (algebraMap c.O S.R) a h)
      exact h3
    exact hb ((res_eq_zero_iff c.O S.R _).2 (by simpa using Ideal.add_mem _ ha h1))
  obtain ⟨u, rfl⟩ := hu
  have hm : b - algebraMap c.O S.B u ∈ S.mB := ha
  have h1 := hξ.2 _ hm
  have e : ξ (S.inc (b - algebraMap c.O S.B u)) = - ξ (algebraMap c.O S.A u) := by
    rw [map_sub, map_sub, h0, zero_sub, AlgHom.commutes]
  rw [e, norm_neg] at h1
  have h2 : ξ (algebraMap c.O S.A u) * ξ (algebraMap c.O S.A (u⁻¹ : (c.O)ˣ)) = 1 := by
    rw [← map_mul, ← map_mul]
    simp
  have h3 := hξ.1 (algebraMap c.O S.A (u⁻¹ : (c.O)ˣ))
  have h4 : ‖ξ (algebraMap c.O S.A u)‖ * ‖ξ (algebraMap c.O S.A (u⁻¹ : (c.O)ˣ))‖ = 1 := by
    rw [← norm_mul, h2, norm_one]
  nlinarith [norm_nonneg (ξ (algebraMap c.O S.A u)), norm_nonneg (ξ (algebraMap c.O S.A (u⁻¹ : (c.O)ˣ)))]

private theorem res_aB (S : Fr.Space c.O F n) (g : F.G0) (i : Fin n) :
    res c.O S.R ((S.aB g i : S.B) : S.R) = ((F.Ψ g ^ Fr.w n i : (ResidueField c.O)ˣ) : ResidueField c.O) :=
  S.lift.2.1.1 g i

private theorem res_ψB (S : Fr.Space c.O F n) (v : F.V) (i : Fin n) (g : F.Gv v) :
    res c.O S.R ((S.ψB v i g : S.B) : S.R) = ((F.Ψ (F.loc v g) ^ Fr.w n i : (ResidueField c.O)ˣ) : ResidueField c.O) :=
  S.lift.2.1.2 v i g

private theorem inc_aB (S : Fr.Space c.O F n) (ξ : S.A →ₐ[c.O] Qbar l) (g : F.G0) (i : Fin n) :
    ξ (S.inc (S.aB g i)) = (ptRep S ξ).r g i i := rfl

private theorem inc_ψB (S : Fr.Space c.O F n) (ξ : S.A →ₐ[c.O] Qbar l) (v : F.V) (i : Fin n) (g : F.Gv v) :
    ξ (S.inc (S.ψB v i g)) = ξ (S.u.ψ v i g : S.A) := rfl

private theorem ne_lin (S : Fr.Space c.O F n) (ξ : S.A →ₐ[c.O] Qbar l) (hξ : IntPt S ξ) (g : F.G0) (k : Fin n)
    (b : S.B) (hb : res c.O S.R (b : S.R) ≠ res c.O S.R ((S.aB g k : S.B) : S.R)) :
    (ptRep S ξ).r g - ξ (S.inc b) • (1 : Matrix (Fin n) (Fin n) (Qbar l)) ≠ 0 := by
  intro h0
  have h1 := congrFun (congrFun h0 k) k
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] at h1
  refine ne_of_res S ξ hξ (S.aB g k - b) ?_ ?_
  · rw [Subalgebra.coe_sub, map_sub]
    exact sub_ne_zero.2 hb.symm
  · rw [map_sub, map_sub, inc_aB]
    exact h1

private theorem ne_quad (S : Fr.Space c.O F n) (ξ : S.A →ₐ[c.O] Qbar l) (hξ : IntPt S ξ) (g : F.G0) (k : Fin n)
    (b b' : S.B) (hb : res c.O S.R (b : S.R) ≠ res c.O S.R ((S.aB g k : S.B) : S.R))
    (hb' : res c.O S.R (b' : S.R) ≠ res c.O S.R ((S.aB g k : S.B) : S.R)) :
    ((ptRep S ξ).r g - ξ (S.inc b) • (1 : Matrix (Fin n) (Fin n) (Qbar l))) *
      ((ptRep S ξ).r g - ξ (S.inc b') • (1 : Matrix (Fin n) (Fin n) (Qbar l))) ≠ 0 := by
  intro h0
  have h1 := congrFun (congrFun h0 k) k
  rw [quad_entry _ _ (map_mul (ptRep S ξ).r g g) _ _ k, Matrix.zero_apply] at h1
  refine ne_of_res S ξ hξ (S.aB (g * g) k - (b + b') * S.aB g k + b * b') ?_ ?_
  · have e : res c.O S.R ((S.aB (g * g) k : S.B) : S.R) =
        res c.O S.R ((S.aB g k : S.B) : S.R) * res c.O S.R ((S.aB g k : S.B) : S.R) := by
      rw [res_aB, res_aB, Subgroup.coe_mul, map_mul, mul_zpow, Units.val_mul]
    simp only [Subalgebra.coe_add, Subalgebra.coe_sub, Subalgebra.coe_mul, map_add (f := _), map_sub, map_mul, e]
    have e2 : ∀ z β β' : ResidueField c.O, z * z - (β + β') * z + β * β' = (z - β) * (z - β') := fun _ _ _ => by ring
    rw [e2]
    exact mul_ne_zero (sub_ne_zero.2 hb.symm) (sub_ne_zero.2 hb'.symm)
  · simp only [map_add (f := _), map_sub, map_mul, inc_aB]
    rw [← map_mul (ptRep S ξ).r]
    exact h1

private theorem two_ne [Fact l.Prime] {C₀ : ℕ} (hF : F.Ok C₀) : (2 : ResidueField c.O) ≠ 0 := by
  intro h
  have h1 : ((2 : ℕ) : ResidueField c.O) = 0 := by exact_mod_cast h
  have h2 := (CharP.cast_eq_zero_iff (ResidueField c.O) l 2).1 h1
  exact hF.l_odd ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h2)

end UpperTheory.V.J.TorusDerivation

open UpperTheory.V.J.TorusDerivation in
theorem UpperTheory.V.J.torus :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, IntPt S ξ → ∀ D ∈ PtDer ξ (Qbar l), MatIrr ⊤ (ptRep S ξ).r →
          ∀ X : Matrix (Fin n) (Fin n) (Qbar l), (∀ g, (S.u.r g).map D = X * (ptRep S ξ).r g - (ptRep S ξ).r g * X) →
          ∃ t : Qbar l, (∀ g i j, D (S.u.r g i j) = t * ((Fr.w n i - Fr.w n j : ℤ) : Qbar l) * ξ (S.u.r g i j)) ∧ ∀ v i g, D (S.u.ψ v i g : S.A) = 0 := by
  intro l _ c _ F C₀ n hF hn S ξ hξ D hD hI X hX
  have hXe : ∀ g i j, D (S.u.r g i j) = (X * (ptRep S ξ).r g - (ptRep S ξ).r g * X) i j :=
    fun g i j => by rw [← hX g]; rfl
  obtain ⟨-, -, sΨ, -, -⟩ := UpperTheory.V.Fr.star hF
  obtain ⟨sstar, -⟩ := UpperTheory.V.Fr.star hF

  have hdiag : ∀ i j, i ≠ j → X i j = 0 := by
    refine offDiag_zero X ((ptRep S ξ).r F.g0 - (ptRep S ξ).r (F.star F.g0)) (ptRep S ξ).diag ?_ ?_
    · intro i j hij h0
      refine ne_of_res S ξ hξ (S.aB F.g0 i - S.aB (F.star F.g0) i - (S.aB F.g0 j - S.aB (F.star F.g0) j)) ?_ ?_
      · simp only [Subalgebra.coe_sub, map_sub, res_aB, sΨ]
        have := z_ne (two_ne (c := c) hF) hn (F.Ψ F.g0) hF.baseSubgroup_spec i j hij
        exact this
      · simp only [map_sub, inc_aB]
        exact sub_eq_zero.2 h0
    · intro i j hij
      have h1 : D (S.u.r F.g0 i j) - D (S.u.r (F.star F.g0) i j) = 0 := by
        rw [← map_sub]
        have h2 : S.u.r F.g0 i j - S.u.r (F.star F.g0) i j = 0 := S.u.diag i j hij
        rw [h2, map_zero]
      rw [hXe, hXe] at h1
      have e : (X * ((ptRep S ξ).r F.g0 - (ptRep S ξ).r (F.star F.g0)) -
          ((ptRep S ξ).r F.g0 - (ptRep S ξ).r (F.star F.g0)) * X) i j =
          (X * (ptRep S ξ).r F.g0 - (ptRep S ξ).r F.g0 * X) i j -
          (X * (ptRep S ξ).r (F.star F.g0) - (ptRep S ξ).r (F.star F.g0) * X) i j := by
        simp only [mul_sub, sub_mul, Matrix.sub_apply]
        ring
      rw [e]
      exact h1
  have hent : ∀ g i j, D (S.u.r g i j) = (X i i - X j j) * ξ (S.u.r g i j) := fun g i j => by
    rw [hXe, comm_entry X _ hdiag]
    rfl
  have hpol : ∀ g i j, S.u.r (F.star g) i j = S.u.r g j.rev i.rev := fun g i j => by
    rw [S.u.pol g, J_entry]
  have hc : ∀ g i j, ((X i i + X i.rev i.rev) - (X j j + X j.rev j.rev)) * (ptRep S ξ).r g i j = 0 := by
    intro g i j
    have e1 : S.u.r g i j = S.u.r (F.star g) j.rev i.rev := by
      have := hpol (F.star g) i j
      rwa [sstar] at this
    have e2 := congrArg D e1
    rw [hent, hent, ← e1] at e2
    have e3 : (ptRep S ξ).r g i j = ξ (S.u.r g i j) := rfl
    rw [e3]
    linear_combination e2
  have hy := scalar_of_irr (ptRep S ξ).r hI (fun i => X i i + X i.rev i.rev) hc
  obtain ⟨t, ht⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator hn (fun i => X i i) hy
  refine ⟨t, fun g i j => ?_, ?_⟩
  · rw [hent]
    have e : X i i - X j j = t * ((Fr.w n i - Fr.w n j : ℤ) : Qbar l) := ht i j
    rw [e]
  intro v
  obtain ⟨s, hs⟩ := hF.f3 v
  let ξ' : S.A →+* Qbar l := (ξ : S.A →+* Qbar l)
  let D' : S.A →+ Qbar l := D.toAddMonoidHom
  have hD' : ∀ f g, D' (f * g) = ξ' f * D' g + ξ' g * D' f := fun f g => hD f g
  have hR : ∀ g : F.Gv v, (S.u.r (F.loc0 v g)).map D' =
      X * (S.u.r (F.loc0 v g)).map ξ' - (S.u.r (F.loc0 v g)).map ξ' * X := fun g => hX _
  have hra : ∀ i j, i ≠ j → res c.O S.R ((S.ψB v i s : S.B) : S.R) ≠
      res c.O S.R ((S.aB (F.loc0 v s) j : S.B) : S.R) := fun i j hij => by
    rw [res_ψB, res_aB]
    exact w_ne hn _ hs i j hij
  have hpne : ∀ i j, i ≠ j → ξ (S.u.ψ v i s : S.A) ≠ ξ (S.u.ψ v j s : S.A) := fun i j hij h0 => by
    refine ne_of_res S ξ hξ (S.ψB v i s - S.ψB v j s) ?_ ?_
    · rw [Subalgebra.coe_sub, map_sub, res_ψB, res_ψB]
      exact sub_ne_zero.2 (w_ne hn _ hs i j hij)
    · rw [map_sub, map_sub, inc_ψB, inc_ψB]
      exact sub_eq_zero.2 h0
  rcases hn with rfl | rfl
  · have hfin := finish2 (fun g : F.Gv v => (ptRep S ξ).r (F.loc0 v g)) (fun g => ξ (S.u.ψ v 0 g : S.A))
      (fun g => ξ (S.u.ψ v 1 g : S.A)) (fun g => D (S.u.ψ v 0 g : S.A)) (fun g => D (S.u.ψ v 1 g : S.A)) s
      (fun g h => ordDer2 ξ' D' hD' X _ _ _ _ (hR g) (hR h) (by
        have := S.u.ord v ![g, h]
        rw [ordProd2] at this
        exact this))
      (hpne 0 1 (by decide))
      (ne_lin S ξ hξ (F.loc0 v s) 0 (S.ψB v 1 s) (hra 1 0 (by decide)))
      (ne_lin S ξ hξ (F.loc0 v s) 1 (S.ψB v 0 s) (hra 0 1 (by decide)))
    intro i g
    fin_cases i
    · exact hfin.1 g
    · exact hfin.2 g
  · have hfin := finish3 (fun g : F.Gv v => (ptRep S ξ).r (F.loc0 v g)) (fun g => ξ (S.u.ψ v 0 g : S.A))
      (fun g => ξ (S.u.ψ v 1 g : S.A)) (fun g => ξ (S.u.ψ v 2 g : S.A)) (fun g => D (S.u.ψ v 0 g : S.A))
      (fun g => D (S.u.ψ v 1 g : S.A)) (fun g => D (S.u.ψ v 2 g : S.A)) s
      (fun g h k => ordDer3 ξ' D' hD' X _ _ _ _ _ _ (hR g) (hR h) (hR k) (by
        have := S.u.ord v ![g, h, k]
        rw [ordProd3] at this
        exact this))
      (hpne 0 1 (by decide)) (hpne 0 2 (by decide)) (hpne 1 2 (by decide))
      (ne_quad S ξ hξ (F.loc0 v s) 0 (S.ψB v 1 s) (S.ψB v 2 s) (hra 1 0 (by decide)) (hra 2 0 (by decide)))
      (ne_quad S ξ hξ (F.loc0 v s) 1 (S.ψB v 0 s) (S.ψB v 2 s) (hra 0 1 (by decide)) (hra 2 1 (by decide)))
      (ne_quad S ξ hξ (F.loc0 v s) 2 (S.ψB v 0 s) (S.ψB v 1 s) (hra 0 2 (by decide)) (hra 1 2 (by decide)))
    intro i g
    fin_cases i
    · exact hfin.1 g
    · exact hfin.2.1 g
    · exact hfin.2.2 g
end

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.V.J.fixLe :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, IntPt S ξ → S.u.TI (RingHom.ker ξ) →
          (∀ D ∈ FixTan S ξ, ∃ X : Matrix (Fin n) (Fin n) (Qbar l), ∀ g, (S.u.r g).map D = X * (ptRep S ξ).r g - (ptRep S ξ).r g * X) →
          Module.rank (Qbar l) (FixTan S ξ) ≤ 1 := by
  intro l _ c _ F C₀ n hF hn S ξ hI hT hX
  have hirr : MatIrr ⊤ (ptRep S ξ).r :=
    (Fr.types hF hn S (Qbar l) (ξ : S.A →+* Qbar l)).1.2 hT
  have key : ∀ D ∈ FixTan S ξ, ∃ t : Qbar l,
      (∀ (g : F.G0) (i j : Fin n), D (S.u.r g i j) = t * ↑(Fr.w n i - Fr.w n j) * ξ (S.u.r g i j)) ∧
      ∀ (v : F.V) (i : Fin n) (g : F.Gv v), D ↑((S.u.ψ v i) g) = 0 := by
    intro D hD
    obtain ⟨X, hXD⟩ := hX D hD
    exact torus l c F C₀ n hF hn S ξ hI D hD.1 hirr X hXD
  by_cases h0 : ∀ D ∈ FixTan S ξ, D = 0
  · have hbot : FixTan S ξ = ⊥ := eq_bot_iff.2 fun D hD => (Submodule.mem_bot _).2 (h0 D hD)
    rw [hbot]
    simp
  push_neg at h0
  obtain ⟨D1, hD1, hne⟩ := h0
  obtain ⟨t1, h1r, h1ψ⟩ := key D1 hD1
  have ht1 : t1 ≠ 0 := by
    rintro rfl
    exact hne (derExt l c F C₀ n hF hn S ξ D1 hD1.1 (fun g i j => by simp [h1r]) h1ψ)
  haveI : Module.Free (Qbar l) (FixTan S ξ) := Module.Free.of_divisionRing _ _
  refine (rank_submodule_le_one_iff _).2 ⟨D1, hD1, fun D hD => ?_⟩
  obtain ⟨t, hr, hψ⟩ := key D hD
  have hE : t1 • D - t • D1 = 0 :=
    derExt l c F C₀ n hF hn S ξ _
      (Submodule.sub_mem _ (Submodule.smul_mem _ _ hD.1) (Submodule.smul_mem _ _ hD1.1))
      (fun g i j => by
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hr, h1r]
        ring)
      (fun v i g => by simp [hψ, h1ψ])
  rw [Submodule.mem_span_singleton]
  refine ⟨t1⁻¹ * t, ?_⟩
  rw [mul_smul, ← sub_eq_zero.1 hE, smul_smul, inv_mul_cancel₀ ht1, one_smul]
