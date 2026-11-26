module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackO1IsoBlowupTwistDual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1fDeRham
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerLawUpperTriangularUnipotentAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerLawUpperTriangularUnipotentAdelic
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

section Entries

variable {R : Type} [CommRing R] {a : ℕ}

theorem posM_block_entry {r m : ℕ} (x : UnipotentBlockColumnIndex a r m → R) (i j : Fin a) :
    posM (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) x i j =
      if h : (i : ℕ) < r ∧ r ≤ (j : ℕ) ∧ (j : ℕ) ≤ m then x ⟨(i, j), h⟩ else 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro t _ ht
      rw [if_neg]
      rintro ⟨e1, e2⟩
      exact ht (Subtype.ext (Prod.ext e1 e2))
    · simp
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨e1, e2⟩
    apply h
    have := t.2
    rw [← e1, ← e2]
    exact this

theorem posM_col_mul {n : ℕ} (x : UnipotentBlockColumnIndex a n n → R) (M : Matrix (Fin a) (Fin a) R)
    (h : ∀ k : Fin a, (k : ℕ) = n → ∀ j, M k j = (1 : Matrix (Fin a) (Fin a) R) k j) :
    posM (Subtype.val : UnipotentBlockColumnIndex a n n → Fin a × Fin a) x * M = posM Subtype.val x := by
  simp only [posM, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht : ((t.1.2 : Fin a) : ℕ) = n := by have := t.2; omega
  ext i j
  by_cases hi : i = t.1.1
  · subst hi
    rw [Matrix.single_mul_apply_same, h _ ht, Matrix.one_apply, Matrix.single_apply]
    by_cases hj : t.1.2 = j <;> simp [hj]
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hi, Matrix.single_apply, if_neg]
    rintro ⟨e1, _⟩
    exact hi e1.symm

theorem sum_posM_col {n : ℕ} (x : UnipotentBlockColumnIndex a n n → R) :
    (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, posM (Subtype.val : UnipotentBlockColumnIndex a n n → Fin a × Fin a) x p.1 p.2) =
      ∑ t : UnipotentBlockColumnIndex a n n, if (t.1.1 : ℕ) + 1 = n then x t else 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht : ((t.1.2 : Fin a) : ℕ) = n := by have := t.2; omega
  by_cases h : (t.1.1 : ℕ) + 1 = n
  · rw [if_pos h, Finset.sum_eq_single t.1]
    · simp
    · intro p _ hp
      rw [if_neg]
      rintro ⟨e1, e2⟩
      exact hp (Prod.ext e1.symm e2.symm)
    · intro hp
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩) hp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp2 := (Finset.mem_filter.1 hp).2
    rw [if_neg]
    rintro ⟨e1, e2⟩
    apply h
    rw [e1, ← ht, e2]
    exact hp2.symm

end Entries

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem whittakerLaw_upperUnipotent_identityColumns (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ)
    (hf : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g) (n : ℕ) :
    ∀ u : GL (Fin a) (Ad E), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) →
      (∀ i j : Fin a, n ≤ (j : ℕ) → i ≠ j → u.val i j = 0) →
      ∀ g : GA E a, f (u * g) = ψ (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2) * f g := by
  induction n with
  | zero =>
    intro u _ hd hc g
    have hu : u = 1 := by
      apply Units.ext
      ext i j
      by_cases h : i = j
      · subst h; simp [hd]
      · simp [hc i j (Nat.zero_le _) h, h]
    subst hu
    have hs : (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (1 : GL (Fin a) (Ad E)).val p.1 p.2) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hp2 := (Finset.mem_filter.1 hp).2
      have : p.1 ≠ p.2 := fun e => by rw [e] at hp2; omega
      simp [this]
    rw [hs, AddChar.map_zero_eq_one, one_mul, one_mul]
  | succ n ih =>
    intro u ht hd hc g
    by_cases hn : n = 0
    · subst hn
      refine ih u ht hd (fun i j _ hij => ?_) g
      rcases lt_or_gt_of_ne hij with h | h
      · exact hc i j (by have : (i : ℕ) < j := h; omega) hij
      · exact ht i j h
    set y : UnipotentBlockColumnIndex a n n → Ad E := fun t => u.val t.1.1 t.1.2 with hy
    have hrow : ∀ k : Fin a, (k : ℕ) = n → ∀ j, u.val k j = (1 : Matrix (Fin a) (Fin a) (Ad E)) k j := by
      intro k hk j
      by_cases h : k = j
      · subst h; simp [hd]
      · rw [Matrix.one_apply, if_neg h]
        rcases lt_or_gt_of_ne h with h' | h'
        · exact hc k j (by have : (k : ℕ) < j := h'; omega) h
        · exact ht k j h'
    have hval : ∀ i j, ((blkU y)⁻¹ * u).val i j = u.val i j - posM Subtype.val y i j := by
      intro i j
      have e : ((blkU y)⁻¹ * u).val = (1 - posM Subtype.val y) * u.val := rfl
      rw [e, sub_mul, one_mul, posM_col_mul y _ hrow, Matrix.sub_apply]
    have hz : ∀ i j : Fin a, ¬ ((i : ℕ) < n ∧ (j : ℕ) = n) → posM (Subtype.val : UnipotentBlockColumnIndex a n n → Fin a × Fin a) y i j = 0 := by
      intro i j h
      rw [posM_block_entry, dite_eq_right]
      rintro ⟨h1, h2, h3⟩
      exact h ⟨h1, by omega⟩
    have e1 := ih ((blkU y)⁻¹ * u) ?_ ?_ ?_ g
    · have e2 : u * g = blkU y * (((blkU y)⁻¹ * u) * g) := by group
      rw [e2, hf n (by omega), e1, ← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      simp only [hval, Finset.sum_sub_distrib, sum_posM_col, dot, eLast]
      have hd2 : (∑ t : UnipotentBlockColumnIndex a n n, algebraMap E (Ad E) (if (t.1.1 : ℕ) + 1 = n then 1 else 0) * y t) =
          ∑ t : UnipotentBlockColumnIndex a n n, if (t.1.1 : ℕ) + 1 = n then y t else 0 := by
        refine Finset.sum_congr rfl fun t _ => ?_
        split_ifs <;> simp
      rw [hd2, add_sub_cancel]
    · intro i j hji
      rw [hval, ht i j hji, hz i j, sub_zero]
      rintro ⟨h1, h2⟩
      have : (j : ℕ) < i := hji
      omega
    · intro j
      rw [hval, hd, hz j j, sub_zero]
      rintro ⟨h1, h2⟩
      omega
    · intro i j hj hij
      rw [hval]
      by_cases hjn : (j : ℕ) = n
      · by_cases hin : (i : ℕ) < n
        · rw [posM_block_entry, dite_eq_left ⟨hin, by omega, by omega⟩, sub_eq_zero]
        · rw [hz i j (fun h => hin h.1), sub_zero]
          exact ht i j (by
            have : (j : ℕ) < i := by
              have : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
              omega
            exact this)
      · rw [hc i j (by omega) hij, hz i j (fun h => hjn h.2), sub_zero]

theorem tri_law (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ)
    (hf : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g)
    (u : GL (Fin a) (Ad E)) (ht : ∀ i j : Fin a, j < i → u.val i j = 0) (hd : ∀ j : Fin a, u.val j j = 1) (g : GA E a) :
    f (u * g) = ψ (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2) * f g :=
  whittakerLaw_upperUnipotent_identityColumns ψ f hf a u ht hd (fun _ j h => absurd j.2 (by omega)) g

end GlobalTheory.CuspGeneric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerLawUpperTriangularUnipotentAdelicStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ), (∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g) → ∀ u : GL (Fin a) (Ad E), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) → ∀ g : GA E a, f (u * g) = ψ (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2) * f g := by
  first | exact @GlobalTheory.CuspGeneric.tri_law | exact GlobalTheory.CuspGeneric.tri_law | (intros; apply GlobalTheory.CuspGeneric.tri_law <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaloisRatComplexImageRayClassField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaloisRatComplexImageRayClassField
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Published GlobalTheory.RayTopGalois GlobalTheory.FieldSize

namespace GlobalTheory.RayNatGalois

theorem isModulus_transport {K K' N : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field N]
    [NumberField N] [Algebra K N] [Algebra K' N] (s : K ≃+* K')
    (hs : ∀ x, algebraMap K' N (s x) = algebraMap K N x) [IsGalois K N] [IsGalois K' N] {𝔪 : Ideal (𝓞 K)}
    {𝔪' : Ideal (𝓞 K')} (hm' : 𝔪' ≠ ⊥) (hmm : ∀ x, RingOfIntegers.mapRingEquiv s x ∈ 𝔪' ↔ x ∈ 𝔪)
    (h : ∀ χ : (N ≃ₐ[K] N) →* ℂˣ, IsModulus N χ 𝔪) (χ : (N ≃ₐ[K'] N) →* ℂˣ) : IsModulus N χ 𝔪' := by
  have hc : ∀ a : 𝓞 K, IsCoprime (Ideal.span {RingOfIntegers.mapRingEquiv s a}) 𝔪' →
      IsCoprime (Ideal.span {a}) 𝔪 := fun a H => by
    rw [Ideal.isCoprime_iff_exists] at H ⊢
    obtain ⟨i, hi, j, hj, hij⟩ := H
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hi
    obtain ⟨c, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective c
    obtain ⟨j, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective j
    refine ⟨c * a, Ideal.mem_span_singleton'.2 ⟨c, rfl⟩, j, (hmm j).1 hj,
      (RingOfIntegers.mapRingEquiv s).injective ?_⟩
    rw [map_add (f := _), map_mul, hij, map_one]
  refine ⟨hm', fun 𝔭 hp => ?_, fun α β hr => ?_⟩
  · obtain ⟨𝔮, rfl⟩ := (primeEquiv s).surjective 𝔭
    rw [heckeVal_transport s hs]
    refine (h _).2.1 𝔮 fun H => hp (Ideal.dvd_iff_le.2 fun x hx => ?_)
    obtain ⟨y, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective x
    change (RingOfIntegers.mapRingEquiv s).symm (RingOfIntegers.mapRingEquiv s y) ∈ 𝔮.asIdeal
    rw [RingEquiv.symm_apply_apply]
    exact Ideal.le_of_dvd H ((hmm y).1 hx)
  · obtain ⟨a, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective α
    obtain ⟨b, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective β
    have ha : a ≠ 0 := fun h => hr.1 (by rw [h, map_zero])
    have hb : b ≠ 0 := fun h => hr.2.1 (by rw [h, map_zero])
    rw [heckeIdeal_transport s hs χ ha, heckeIdeal_transport s hs χ hb]
    refine (h _).2.2 a b ⟨ha, hb, hc _ hr.2.2.1, hc _ hr.2.2.2.1, (hmm _).1 ?_, fun φ => ?_⟩
    · rw [map_sub]; exact hr.2.2.2.2.1
    · have := hr.2.2.2.2.2 (φ.comp s.symm.toRingHom)
      change 0 < φ (s.symm (s a)) * φ (s.symm (s b)) at this
      rwa [s.symm_apply_apply, s.symm_apply_apply] at this

theorem exists_extension {L N : Type} [Field L] [NumberField L] [Field N] [NumberField N] [i : Algebra L N]
    [hab : IsAbelianGalois L N] {n : ℕ} (hn : n ≠ 0) (h : IsRay N (Ideal.span {(n : 𝓞 L)})) (s : L ≃+* L) :
    ∃ f : N →+* N, ∀ x, f (algebraMap L N x) = algebraMap L N (s x) := by
  have hb : Ideal.span {(n : 𝓞 L)} ≠ ⊥ := by simpa using hn
  have hmm : ∀ x, RingOfIntegers.mapRingEquiv s x ∈ Ideal.span {(n : 𝓞 L)} ↔ x ∈ Ideal.span {(n : 𝓞 L)} :=
    fun x => by
      rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton,
        ← map_dvd_iff (RingOfIntegers.mapRingEquiv s) (a := (n : 𝓞 L)) (b := x), map_natCast]
  let j : Algebra L N := ((@algebraMap L N _ _ i).comp s.symm.toRingHom).toAlgebra
  have hs : ∀ x, @algebraMap L N _ _ j (s x) = @algebraMap L N _ _ i x := fun x =>
    congrArg (@algebraMap L N _ _ i) (s.symm_apply_apply x)
  have hab' := @isAbelianGalois_transport L L N _ _ _ _ i j s hs _ hab
  have hm := @GlobalTheory.RayMaximal.isModulus_of_isRay L _ _ N _ _ i hab _ _ h dvd_rfl hb
  obtain ⟨f⟩ := @rayClassFieldMaximalSt_holds L N N _ _ _ _ i hab _ _ j hab' _ hb h
    (@isModulus_transport L L N _ _ _ _ _ _ i j s hs (@IsAbelianGalois.toIsGalois _ _ _ _ i hab)
      (@IsAbelianGalois.toIsGalois _ _ _ _ j hab') _ _ hb hmm hm)
  refine ⟨@AlgHom.toRingHom L N N _ _ _ j i f, fun x => ?_⟩
  rw [← hs]
  exact @AlgHom.commutes L N N _ _ _ j i f (s x)

theorem isGalois_of_isRay_nat (K : Type) {L N : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field N]
    [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L]
    [IsAbelianGalois L N] {n : ℕ} (hn : n ≠ 0) (h : IsRay N (Ideal.span {(n : 𝓞 L)})) : IsGalois K N := by
  refine IsGalois.of_fixedField_eq_bot K N (eq_bot_iff.2 fun x hx => ?_)
  rw [IntermediateField.mem_fixedField_iff] at hx
  obtain ⟨y, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := L) x).2 fun σ =>
    hx (σ.restrictScalars K) trivial
  obtain ⟨z, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) y).2 fun s => by
    obtain ⟨f, hf⟩ := exists_extension hn h s.toRingEquiv
    let g : N →ₐ[K] N := { f with
      commutes' := fun k => by
        rw [IsScalarTower.algebraMap_apply K L N]
        exact (hf _).trans (congrArg _ (s.commutes k)) }
    exact (algebraMap L N).injective ((hf y).symm.trans
      (hx (AlgEquiv.ofBijective g (Algebra.IsAlgebraic.algHom_bijective g)) trivial))
  rw [← IsScalarTower.algebraMap_apply]
  exact IntermediateField.algebraMap_mem _ z

theorem isGalois_fieldRange : ∀ {K H : Type} [Field K] [NumberField K] [IsGalois ℚ K] [Field H] [NumberField H]
    [Algebra K H] [IsAbelianGalois K H] {n : ℕ}, n ≠ 0 → GlobalTheory.FieldSize.IsRay H (Ideal.span {(n : 𝓞 K)}) →
    ∀ j : H →+* ℂ, IsGalois ℚ j.toRatAlgHom.fieldRange := by
  intro K H _ _ _ _ _ _ _ n hn h j
  have : IsGalois ℚ H := isGalois_of_isRay_nat ℚ hn h
  exact IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField j.toRatAlgHom)

end GlobalTheory.RayNatGalois

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaloisRatComplexImageRayClassFieldStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGalois_rat_complexImage_rayClassField : ∀ {K H : Type} [Field K] [NumberField K] [IsGalois ℚ K] [Field H] [NumberField H] [Algebra K H] [IsAbelianGalois K H] {n : ℕ}, n ≠ 0 → GlobalTheory.FieldSize.IsRay H (Ideal.span {(n : 𝓞 K)}) → ∀ j : H →+* ℂ, IsGalois ℚ j.toRatAlgHom.fieldRange := by
  first | exact @GlobalTheory.RayNatGalois.isGalois_fieldRange | exact GlobalTheory.RayNatGalois.isGalois_fieldRange | (intros; apply GlobalTheory.RayNatGalois.isGalois_fieldRange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedTrivialLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedTrivialLocal
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.UnramifiedTrivial

theorem unramifiedCocycles_le_blochKatoFinite_trivial {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (T : LocTied l P AI) (K LL : FinExt l) :
    Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K) ≤
      finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) := by
  intro c hc
  obtain ⟨hZ, x, hx⟩ := hc
  refine ⟨hZ, ?_⟩
  obtain ⟨hcont, hadd⟩ := hZ
  haveI := LL.2
  let v := Module.finBasis ℚ_[l] ↥LL.1
  have hI : ∀ g ∈ IK K, c g = 0 := fun g hg => by simpa using hx g hg
  have hex : ∀ i, ∃ b : P.R.B, ∀ g : ↥(GK K),
      P.actQ g b - b = algebraMap ℚ_[l] _ (v.coord i (c g)) := fun i =>
    GlobalTheory.UnramifiedCrys.exists_rat AI T K (fun g => v.coord i (c g))
      ((v.coord i).continuous_of_finiteDimensional.comp hcont)
      (fun g h => by rw [hadd, map_add (f := _)]; rfl) (fun g hg => by rw [hI g hg, map_zero])
  choose b hb using hex
  refine ⟨∑ i, v i ⊗ₜ[ℚ_[l]] b i, fun g => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_sub_distrib]
  conv_lhs => rw [← v.sum_repr (c g), TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : actVB (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) g (v i ⊗ₜ[ℚ_[l]] b i) =
      v i ⊗ₜ[ℚ_[l]] P.actQ g (b i) := by
    rw [← P.PD_actB]
    rfl
  rw [h1, ← TensorProduct.tmul_sub, hb, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  rfl

theorem Z1ur_ne_bot {l : ℕ} [Fact l.Prime] (K LL : FinExt l) :
    Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K) ≠ ⊥ := by
  obtain ⟨δ, hδc, hδa, hδI, g₀, hg₀⟩ := GlobalTheory.UnramZl.exists_unramified_character l K
  haveI := LL.2
  let c : ↥(GK K) → ↥LL.1 := fun g => algebraMap ℚ_[l] ↥LL.1 (δ g)
  have hcc : Continuous c :=
    (Algebra.linearMap ℚ_[l] ↥LL.1).continuous_of_finiteDimensional.comp hδc
  have hmem : c ∈ Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K) := by
    refine ⟨⟨hcc, fun g h => ?_⟩, 0, fun g hg => ?_⟩
    · simp [c, hδa, map_add (f := _)]
    · simp [c, hδI g hg]
  intro h
  rw [h] at hmem
  have := congrFun ((Submodule.mem_bot _).1 hmem) g₀
  exact hg₀ (by simpa [c] using this)

end GlobalTheory.UnramifiedTrivial

namespace GlobalTheory.UnramifiedTrivial
theorem finrank_Z1f_trivial {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) :
    finrank ↥LL.1 ↥(finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) =
      finrank ↥LL.1 (FiniteCohomology (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) := by
  have hB1 : B1 (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    ext g
    simp [cob]
  have hc : (B1 (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)).comap
      (finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)).subtype = ⊥ := by
    rw [hB1, Submodule.comap_bot, Submodule.ker_subtype]
  exact (Submodule.quotEquivOfEqBot _ hc).finrank_eq.symm
end GlobalTheory.UnramifiedTrivial

namespace GlobalTheory.UnramifiedTrivial
theorem unrTriv_of_finrank {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (T : LocTied l P AI) (K LL : FinExt l)
    (h1 : finrank ↥LL.1 (FiniteCohomology (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) = 1) :
    UnrTriv (P.PD K) (LL := ↥LL.1) (IK K) := by
  have hZ : finrank ↥LL.1 ↥(finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) = 1 :=
    (finrank_Z1f_trivial P K LL).trans h1
  haveI : FiniteDimensional ↥LL.1 ↥(finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) :=
    Module.finite_of_finrank_eq_succ hZ
  have hle := unramifiedCocycles_le_blochKatoFinite_trivial AI T K LL
  haveI := Submodule.finiteDimensional_of_le hle
  have hpos : 0 < finrank ↥LL.1 ↥(Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K)) := by
    refine Nat.pos_of_ne_zero fun h0 => Z1ur_ne_bot K LL ?_
    exact Submodule.finrank_eq_zero.1 h0
  unfold UnrTriv
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hZ]; exact hpos)).symm
end GlobalTheory.UnramifiedTrivial

namespace GlobalTheory.UnramifiedTrivial

theorem unrTriv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL : FinExt l), UnrTriv (P.PD K) (LL := ↥LL.1) (IK K) := by
  intro l _ P AI T K LL
  haveI := LL.2
  obtain ⟨hgood, -⟩ := GlobalTheory.LocalIntegers.good_integers l LL
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := ↥LL.1
      ρ := 1
      cont := fun x => (continuous_const : Continuous fun _ : ↥(GK K) => x) }
  have hDR : IsDR (P.PD K) A.ρ := GlobalTheory.CrysExt.isDR_trivial (P.PD K)
  obtain ⟨hfin, hdim⟩ := GlobalTheory.T.finrank_H1f_de_rham l P AI T K ↥LL.1 ↥(OL LL) hgood A hDR
  have hH0 : H0V A.ρ = ⊤ := by
    refine eq_top_iff.2 fun x _ => (Submodule.mem_iInf _).2 fun g => ?_
    simp [A, H0V]
  have hFil : DdR (P.PD K) A.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := A.V) 0 = DdR (P.PD K) A.ρ := by
    refine inf_eq_left.2 fun x hx => ?_
    change x ∈ DdR (P.PD K) (Representation.trivial ↥LL.1 ↥(GK K) ↥LL.1) at hx
    rw [GlobalTheory.CrysExt.ddR_trivial] at hx
    obtain ⟨z, rfl⟩ := hx
    exact GlobalTheory.CrysExt.incl_mem_FilV (P.PD K) le_rfl z
  have e1 : finrank ↥LL.1 ↥(H0V A.ρ) = 1 := by rw [hH0, finrank_top]; exact Module.finrank_self _
  rw [hFil] at hdim
  have h1' : finrank ↥LL.1 (FiniteCohomology (P.PD K) A.ρ) = 1 := by omega
  have h1 : finrank ↥LL.1 (FiniteCohomology (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) = 1 := h1'
  exact unrTriv_of_finrank AI T K LL h1

end GlobalTheory.UnramifiedTrivial
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedTrivialLocalStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_trivial_local : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), UnrTriv (P.PD K) (LL := ↥LL.1) (IK K) := by
  first | exact @GlobalTheory.UnramifiedTrivial.unrTriv | exact GlobalTheory.UnramifiedTrivial.unrTriv | (intros; apply GlobalTheory.UnramifiedTrivial.unrTriv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumUniversalDeterminantDatumCoeffEqPrimitive
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardSubspacesSupEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetModNeZeroIff
open scoped Classical BigOperators
open IsLocalRing Module Matrix

noncomputable section

namespace GlobalTheory.AdaptedLocalData

section Field

variable {k : Type} [Field k]

theorem card_isCompl [Finite k] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (R : Submodule k V) :
    Nat.card {U : Submodule k V // IsCompl R U} =
      Nat.card k ^ (finrank k (V ⧸ R) * finrank k R) := by
  obtain ⟨f₀, hf₀⟩ := R.subtype.exists_leftInverse_of_injective R.ker_subtype
  have h₀ : ∀ x : R, f₀ x = x := fun x => LinearMap.congr_fun hf₀ x
  rw [Nat.card_congr R.isComplEquivProj, ← Module.finrank_linearMap k k,
    ← Module.natCard_eq_pow_finrank (K := k)]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun g => ⟨f₀ + g.comp R.mkQ, fun x => by
      have : R.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero R).2 x.2
      rw [LinearMap.add_apply, LinearMap.comp_apply, this, map_zero, add_zero, h₀]⟩) ⟨?_, ?_⟩)
  · intro g g' h
    have h1 : g.comp R.mkQ = g'.comp R.mkQ := add_left_cancel (congrArg Subtype.val h)
    exact R.linearMap_qext h1
  · rintro ⟨f, hf⟩
    refine ⟨R.liftQ (f - f₀) fun x hx => ?_, Subtype.ext ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, hf ⟨x, hx⟩, h₀ ⟨x, hx⟩, sub_self]
    · simp

theorem card_sup_eq_top [Finite k] (r t : ℕ) (R : Submodule k (Fin (r + t) → k))
    (hR : finrank k R ≤ r) :
    Nat.card {U : Submodule k (Fin (r + t) → k) // finrank k U = t ∧ R ⊔ U = ⊤} =
      if finrank k R = r then Nat.card k ^ (r * t) else 0 := by
  have key : ∀ U : Submodule k (Fin (r + t) → k), R ⊔ U = ⊤ →
      r + t + finrank k ↥(R ⊓ U) = finrank k R + finrank k U := fun U h => by
    have := Submodule.finrank_sup_add_finrank_inf_eq R U
    rwa [h, finrank_top, finrank_fin_fun] at this
  split_ifs with h
  · have hq : finrank k ((Fin (r + t) → k) ⧸ R) = t := by
      have := R.finrank_quotient_add_finrank
      rw [finrank_fin_fun] at this
      omega
    have := card_isCompl R
    rw [hq, h, mul_comm] at this
    rw [← this]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun U => ⟨fun ⟨h1, h2⟩ => ?_, fun hc => ?_⟩)
    · refine ⟨disjoint_iff.2 (Submodule.finrank_eq_zero.1 ?_), codisjoint_iff.2 h2⟩
      have := key U h2
      omega
    · have := key U hc.sup_eq_top
      rw [hc.inf_eq_bot, finrank_bot] at this
      exact ⟨by omega, hc.sup_eq_top⟩
  · haveI : IsEmpty {U : Submodule k (Fin (r + t) → k) // finrank k U = t ∧ R ⊔ U = ⊤} :=
      ⟨fun U => by have := key U.1 U.2.2; have := U.2.1; omega⟩
    exact Nat.card_of_isEmpty

end Field

section Local

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]

variable [Finite (ResidueField O)]

end Local

end GlobalTheory.AdaptedLocalData
end
end

open scoped BigOperators

namespace GlobalTheory

theorem card_subspaces_sup_eq_top :
    ∀ (k : Type) [Field k] [Finite k] (r t : ℕ) (R : Submodule k (Fin (r + t) → k)),
      Module.finrank k R ≤ r →
      Nat.card {U : Submodule k (Fin (r + t) → k) // Module.finrank k U = t ∧ R ⊔ U = ⊤} =
        if Module.finrank k R = r then Nat.card k ^ (r * t) else 0 := by
  intro k _ _ r t R hR
  convert AdaptedLocalData.card_sup_eq_top r t R hR

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumUniversalDeterminantDatumCoeffEqPrimitive
open Matrix GlobalTheory.ExportSeries

namespace GlobalTheory.ExportSeries

theorem sum_univCoef_eq_prim : ∀ (k C : Type) [Field k] [Finite k] [AddCommGroup C] [Fintype C] (r n : ℕ), r ≤ n →
    ∀ (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (y : Matrix (Fin r) (Fin n) k), ∑ c, univCoef β κ c y = prim y := by
  intro k C _ _ _ _ r n hrn β κ y
  classical
  letI := Fintype.ofFinite (Planes k r n)

  have hterm : ∀ U : Planes k r n, ∑ c, (univTerm β κ y U).coeff c = if Compl U.1 y then 1 else 0 := by
    intro U
    unfold univTerm
    by_cases h : Compl U.1 y
    · rw [dite_eq_left h, if_pos h]
      simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    · rw [dite_eq_right h, if_neg h]
      simp
  have hsum : ∑ c, univCoef β κ c y = ((Nat.card k : ℚ) ^ (r * (n - r)))⁻¹ *
      (Nat.card {U : Planes k r n // Compl U.1 y} : ℚ) := by
    simp only [univCoef, univ, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, AddMonoidAlgebra.coeff_sum,
      Finsupp.finsetSum_apply]
    rw [← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl fun U _ => hterm U, Finset.sum_boole]
    congr 2
    rw [Nat.card_eq_fintype_card (α := {U : Planes k r n // Compl U.1 y}), Fintype.card_subtype]
  rw [hsum]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrn
  have ht : r + t - r = t := by omega
  rw [ht]
  set R := Submodule.span k (Set.range y.row) with hR
  have hRle : Module.finrank k R ≤ r := by
    have := finrank_range_le_card (R := k) y.row
    rw [Fintype.card_fin] at this
    exact this
  have hcard : Nat.card {U : Planes k r (r + t) // Compl U.1 y} =
      Nat.card {U : Submodule k (Fin (r + t) → k) // Module.finrank k U = t ∧ R ⊔ U = ⊤} := by
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter _ (fun U => Compl U y)).trans
      (Equiv.subtypeEquivRight fun U => ?_))
    simp only [Compl, hR]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  rw [hcard, GlobalTheory.card_subspaces_sup_eq_top k r t R hRle]
  have hq : ((Nat.card k : ℚ) ^ (r * t)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.card_pos.ne')
  have hli : LinearIndependent k y.row ↔ Module.finrank k R = r := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank, eq_comm]
  unfold prim
  by_cases h : Module.finrank k R = r
  · rw [if_pos h, if_pos (hli.2 h)]
    push_cast
    exact inv_mul_cancel₀ hq
  · rw [if_neg h, if_neg (fun h' => h (hli.1 h'))]
    simp

end GlobalTheory.ExportSeries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumUniversalDeterminantDatumCoeffEqPrimitiveStatement
open Matrix GlobalTheory.ExportSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_universalDeterminantDatumCoeff_eq_primitive : ∀ (k C : Type) [Field k] [Finite k] [AddCommGroup C] [Fintype C] (r n : ℕ), r ≤ n → ∀ (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (y : Matrix (Fin r) (Fin n) k), ∑ c, univCoef β κ c y = prim y := by
  first | exact @GlobalTheory.ExportSeries.sum_univCoef_eq_prim | exact GlobalTheory.ExportSeries.sum_univCoef_eq_prim | (intros; apply GlobalTheory.ExportSeries.sum_univCoef_eq_prim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fTSpanCardBound
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fTSpanCardBound
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.H1fGeneratorsAlt

section Eval

variable {G V LL : Type} [Field LL] [AddCommGroup V] [Module LL V]

theorem exists_finset_eval (W : Submodule LL (G → V)) [Module.Finite LL ↥W] :
    ∃ s : Finset G, ∀ c ∈ W, (∀ g ∈ s, c g = 0) → c = 0 := by
  classical
  let Ks : Finset G → Submodule LL (G → V) := fun s =>
    W ⊓ ⨅ g ∈ s, LinearMap.ker (LinearMap.proj (R := LL) (φ := fun _ : G => V) g)
  have hmem : ∀ s c, c ∈ Ks s ↔ c ∈ W ∧ ∀ g ∈ s, c g = 0 := by
    intro s c
    simp [Ks, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  obtain ⟨s, -, hs⟩ := (measure fun s => finrank LL ↥(Ks s)).wf.has_min Set.univ ⟨∅, trivial⟩
  refine ⟨s, fun c hc h0 => ?_⟩
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g, c g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hlt : Ks (insert g s) < Ks s := by
    refine lt_of_le_of_ne (fun x hx => ?_) fun heq => ?_
    · rw [hmem] at hx ⊢
      exact ⟨hx.1, fun g' hg' => hx.2 g' (Finset.mem_insert_of_mem hg')⟩
    · have h1 : c ∈ Ks s := (hmem s c).2 ⟨hc, h0⟩
      rw [← heq, hmem] at h1
      exact hg (h1.2 g (Finset.mem_insert_self g s))
  haveI : Module.Finite LL ↥(Ks s) := Submodule.finiteDimensional_of_le inf_le_left
  exact hs (insert g s) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem fg_of_le_of_values {O : Type} [CommRing O] [IsNoetherianRing O] [Algebra O LL] [Module O V]
    [IsScalarTower O LL V] (W : Submodule LL (G → V)) [Module.Finite LL ↥W]
    (T : Submodule O V) (hT : T.FG) (N : Submodule O (G → V)) (hNW : N ≤ W.restrictScalars O)
    (hNT : ∀ c ∈ N, ∀ g, c g ∈ T) : N.FG := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_eval W
  haveI : IsNoetherian O ↥T := isNoetherian_of_fg_of_noetherian T hT
  let φ : ↥N →ₗ[O] (↥s → ↥T) :=
    { toFun := fun c i => ⟨(c : G → V) i, hNT _ c.2 _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := by
    intro c c' h
    apply Subtype.ext
    rw [← sub_eq_zero]
    refine hs _ (W.sub_mem (hNW c.2) (hNW c'.2)) fun g hg => ?_
    have := congrArg (fun f => ((f ⟨g, hg⟩ : ↥T) : V)) h
    simpa [φ, sub_eq_zero] using this
  haveI : IsNoetherian O ↥N := isNoetherian_of_injective φ hφ
  exact Module.Finite.iff_fg.1 inferInstance

end Eval

section Cohomology

open GlobalTheory.H1fGeneratorBoundAlt GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ρ : Representation LL G V}
    [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul LL V]
    {O : Type} [CommRing O] [Algebra O LL] [IsDomain O] [IsDiscreteValuationRing O]
    [IsFractionRing O LL] [Module O V] [IsScalarTower O LL V]

theorem finite_Z1f_of_H1fV [FiniteDimensional LL V] (hρ : ∀ x, Continuous fun g => ρ g x)
    [Module.Finite LL (FiniteCohomology PD ρ)] : Module.Finite LL ↥(finiteCocycles PD ρ) := by
  have hle : B1 ρ ≤ finiteCocycles PD ρ := by
    rintro _ ⟨x, rfl⟩
    exact coboundary_mem_blochKatoCocycles PD hρ x
  haveI : Module.Finite LL ↥(B1 ρ) := LinearMap.finiteDimensional_range _
  haveI : Module.Finite LL ↥((B1 ρ).comap (finiteCocycles PD ρ).subtype) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hle).symm
  haveI : IsNoetherian LL ↥(finiteCocycles PD ρ) :=
    isNoetherian_of_range_eq_ker ((B1 ρ).comap (finiteCocycles PD ρ).subtype).subtype
      (Submodule.mkQ _) (by rw [Submodule.range_subtype, Submodule.ker_mkQ])
  infer_instance

theorem finite_Z1fT_of (L : Lattice (O := O) ρ) [Module.Finite LL ↥(finiteCocycles PD ρ)] :
    Module.Finite O ↥(latticeFiniteCocycles PD L) :=
  Module.Finite.iff_fg.2 (fg_of_le_of_values (finiteCocycles PD ρ) L.T L.fg (latticeFiniteCocycles PD L) inf_le_right
    fun _ hc g => hc.1.2 g (Set.mem_univ g))

theorem exists_generators_H1fT' [FiniteDimensional LL V] (L : Lattice (O := O) ρ)
    (hρ : ∀ x, Continuous fun g => ρ g x) [Module.Finite LL (FiniteCohomology PD ρ)]
    {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ m : ℕ, GeneratedByAtMost (latticeFiniteCohomology PD L) m ∧
      m + finrank LL ↥(H0V ρ) ≤ finrank LL (FiniteCohomology PD ρ) + h0ModResidueDim L ϖ := by
  classical
  haveI hI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  haveI := L.free
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  haveI := finite_Z1f_of_H1fV PD hρ
  haveI := finite_Z1fT_of PD L
  haveI : Module.IsTorsionFree O LL := inferInstance
  haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.trans LL
  haveI : Module.Free O ↥(latticeFiniteCocycles PD L) := inferInstance
  obtain ⟨m, z, hz, hm⟩ := exists_generators (Ideal.span {ϖ}) (cobT PD L hρ)
  refine ⟨m, ⟨Finset.univ.image fun i => classT PD L (z i), ?_, ?_⟩, ?_⟩
  · have := congrArg (Submodule.map (classT PD L)) hz
    rw [Submodule.map_sup, ← ker_classT, Submodule.map_top, range_classT,
      (Submodule.map_le_iff_le_comap.2 le_rfl : (LinearMap.ker (classT PD L)).map (classT PD L) ≤ ⊥).antisymm bot_le,
      sup_bot_eq, Submodule.map_span, ← Set.range_comp] at this
    rw [← this, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rfl
  · simpa using Finset.card_image_le (s := Finset.univ) (f := fun i => classT PD L (z i))
  · haveI := finite_latMod L (Ideal.span {ϖ})
    have h1 := Submodule.finrank_mono (ker_redMap_le PD L hρ (Ideal.span {ϖ}))
    have h2 := finrank_bloch_kato_cocycles PD hρ
    have h3 := finrank_lattice L
    have h4 : finrank O ↥(latticeFiniteCocycles PD L) ≤ finrank LL ↥(finiteCocycles PD ρ) :=
      finrank_le_of_injective (W := ↥(finiteCocycles PD ρ))
        { toFun := fun c => ⟨c, c.2.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl } fun _ _ h =>
          Subtype.ext (congrArg (fun c : ↥(finiteCocycles PD ρ) => (c : G → V)) h)
    have h5 : finrank (O ⧸ Ideal.span {ϖ}) ↥(LinearMap.ker (redMap (Ideal.span {ϖ}) (cobT PD L hρ))) ≤
      h0ModResidueDim L ϖ := h1
    omega

end Cohomology

open GlobalTheory.H1fGeneratorBoundAlt GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions

theorem h1fT_generators : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ T : LocLat ↥(GK K) ℚ_[l] LL O, IsDR (P.PD K) T.ρ → ∃ s : Finset (LatticeCohomology T.L), Submodule.span O (s : Set (LatticeCohomology T.L)) = latticeFiniteCohomology (P.PD K) T.L ∧ s.card + finrank LL ↥(H0V T.ρ) ≤ finrank LL (FiniteCohomology (P.PD K) T.ρ) + finrank LL T.V := by
  intro l _ P AI hTied K LL _ _ _ O _ _ hO T hDR
  have hH1f := (GlobalTheory.SeqDim.h1f_finrank l P AI hTied K LL O hO (toGRep T) hDR).1
  obtain ⟨⟨hD, hDVR, hF⟩, -⟩ := hO
  haveI : IsTopologicalAddGroup T.V := IsModuleTopology.topologicalAddGroup LL T.V
  haveI : Module.Finite LL (FiniteCohomology (P.PD K) T.ρ) := hH1f
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, ⟨s, hs, hc⟩, hm⟩ := exists_generators_H1fT' (P.PD K) T.L T.cont hϖ
  have h5 := h0_mod_uniformizer_le_rank T.L hϖ
  have h3 := finrank_lattice T.L
  exact ⟨s, hs, by omega⟩

end GlobalTheory.H1fGeneratorsAlt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fTSpanCardBoundStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h1fT_span_card_bound : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ T : LocLat ↥(GK K) ℚ_[l] LL O, IsDR (P.PD K) T.ρ → ∃ s : Finset (LatticeCohomology T.L), Submodule.span O (s : Set (LatticeCohomology T.L)) = latticeFiniteCohomology (P.PD K) T.L ∧ s.card + finrank LL ↥(H0V T.ρ) ≤ finrank LL (FiniteCohomology (P.PD K) T.ρ) + finrank LL T.V := by
  first | exact @GlobalTheory.H1fGeneratorsAlt.h1fT_generators | exact GlobalTheory.H1fGeneratorsAlt.h1fT_generators | (intros; apply GlobalTheory.H1fGeneratorsAlt.h1fT_generators <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialRankinSelbergProductConjSwapReal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialRankinSelbergProductConjSwapReal
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

noncomputable section

namespace GlobalTheory.RSConj

theorem conj_tprod {β : Type} (f : β → ℂ) :
    starRingEnd ℂ (∏' i, f i) = ∏' i, starRingEnd ℂ (f i) := by
  by_cases hf : Multipliable f
  · exact hf.map_tprod (starRingEnd ℂ) Complex.continuous_conj
  · have hg : ¬ Multipliable fun i => starRingEnd ℂ (f i) := by
      intro hg
      apply hf
      have := hg.map (starRingEnd ℂ) Complex.continuous_conj
      convert this using 1
      funext i
      simp
    rw [tprod_eq_one_of_not_multipliable hf, tprod_eq_one_of_not_multipliable hg, map_one]

theorem conj_natCast_cpow_neg (q : ℕ) (x : ℝ) :
    starRingEnd ℂ ((q : ℂ) ^ (-(x : ℂ))) = (q : ℂ) ^ (-(x : ℂ)) := by
  have h : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]
    push_cast
    rfl
  rw [h, Complex.conj_ofReal]

theorem conj_locL (q : ℕ) (A B : Multiset ℂˣ) (x : ℝ) :
    starRingEnd ℂ (locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) =
      locL q B (A.map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) := by
  unfold locL
  rw [map_multiset_prod]
  simp only [SProd.sprod, Multiset.product, Multiset.map_bind, Multiset.prod_bind, Multiset.map_map, Function.comp_def]
  rw [Multiset.prod_map_prod_map]
  congr 1
  refine Multiset.map_congr rfl fun b _ => ?_
  congr 1
  refine Multiset.map_congr rfl fun a _ => ?_
  simp only [map_inv₀, map_sub, map_one, map_mul, conj_natCast_cpow_neg, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Complex.conj_conj]
  ring

theorem partial_conj : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b),
    σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' →
    ∀ x : ℝ, 1 < x → ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1 =
      starRingEnd ℂ (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1) := by
  intro E _ _ _ a b σ σ' _ _ T _ _ x _
  rw [conj_tprod]
  congr 1
  funext w
  exact (conj_locL _ _ _ x).symm

end GlobalTheory.RSConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialRankinSelbergProductConjSwapRealStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_rankinSelberg_product_conj_swap_real : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∀ x : ℝ, 1 < x → ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1 = starRingEnd ℂ (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1) := by
  first | exact @GlobalTheory.RSConj.partial_conj | exact GlobalTheory.RSConj.partial_conj | (intros; apply GlobalTheory.RSConj.partial_conj; all_goals assumption)
end
end
