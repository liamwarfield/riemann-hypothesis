module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulEqZeroOfEqXSubOneSmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FlatQuotSMulTopCokerOfMatrixWitnesses
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

open scoped Pointwise

namespace GlobalTheory

theorem flat_quotSMulTop_coker_of_matrix_witnesses :
    ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (r a b : ℕ) (g : Fin r → S) (u : S) (Φ : Matrix (Fin a) (Fin b) S), Module.Flat R (S ⧸ Ideal.span (Set.range g)) → (∃ c : Fin r → S, u = ∑ k, c k * g k) → (∀ k, ∃ (C : Matrix (Fin b) (Fin a) S) (C' : Matrix (Fin a) (Fin a) S), g k • (1 : Matrix (Fin a) (Fin a) S) = Φ * C + u • C') → (∃ (Ψ : Matrix (Fin b) (Fin a) S) (E : Fin r → Matrix (Fin a) (Fin b) S), Φ * Ψ * Φ = Φ + ∑ k, g k • E k) → Module.Flat R (QuotSMulTop u ((Fin a → S) ⧸ LinearMap.range Φ.mulVecLin)) := by
  intro R S _ _ _ r a b g u Φ hflat hu hker hreg
  obtain ⟨c, hc⟩ := hu
  obtain ⟨Ψ, E, hΨ⟩ := hreg
  let I : Ideal S := Ideal.span (Set.range g)
  have hgI : ∀ k, g k ∈ I := fun k => Ideal.subset_span ⟨k, rfl⟩
  have huI : u ∈ I := by
    rw [hc]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hgI k)
  have hmv : ∀ {m : ℕ} (A : Matrix (Fin a) (Fin m) S), (∀ j i, A j i ∈ I) →
      ∀ y j, (Matrix.mulVec A y) j ∈ I := by
    intro m A hA y j
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hA j i)
  let K := LinearMap.range Φ.mulVecLin
  let M := (Fin a → S) ⧸ K
  let T : Submodule S M := u • (⊤ : Submodule S M)
  let pr : (Fin a → S) →ₗ[S] QuotSMulTop u M := T.mkQ ∘ₗ K.mkQ
  have hK : ∀ y, pr (Matrix.mulVec Φ y) = 0 := by
    intro y
    simp only [pr, LinearMap.comp_apply, Submodule.mkQ_apply]
    have hy : K.mkQ (Matrix.mulVec Φ y) = 0 := (Submodule.Quotient.mk_eq_zero K).2 ⟨y, rfl⟩
    rw [hy, Submodule.Quotient.mk_zero]
  have hU : ∀ z, pr (u • z) = 0 := by
    intro z
    simp only [pr, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [map_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  have hG : ∀ k x, g k • pr x = 0 := by
    intro k x
    obtain ⟨C, C', h⟩ := hker k
    have hx : g k • x = Matrix.mulVec Φ (Matrix.mulVec C x) + u • Matrix.mulVec C' x := by
      have := congrArg (fun A => Matrix.mulVec A x) h
      simp only [Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.add_mulVec,
        ← Matrix.mulVec_mulVec] at this
      exact this
    rw [← map_smul, hx, map_add (f := _), hK, hU, add_zero]
  have hI : ∀ s ∈ I, ∀ x, s • pr x = 0 := by
    intro s hs x
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hs
    simp only [Finset.sum_smul, smul_eq_mul, mul_smul, hG, smul_zero, Finset.sum_const_zero]
  let q : (Fin a → S) →ₗ[S] (Fin a → S ⧸ I) :=
    LinearMap.pi fun j => (Submodule.mkQ I) ∘ₗ LinearMap.proj j
  have hq : ∀ v, (∀ j, v j ∈ I) → q v = 0 := by
    intro v hv
    funext j
    exact (Submodule.Quotient.mk_eq_zero I).2 (hv j)
  have hqI : ∀ s ∈ I, ∀ w : Fin a → S ⧸ I, s • w = 0 := by
    intro s hs w
    funext j
    obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective I (w j)
    rw [Pi.smul_apply, ← ht, ← Submodule.Quotient.mk_smul, Pi.zero_apply,
      Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hs
  have hE : ∀ j i, (∑ k, g k • E k) j i ∈ I := by
    intro j i
    rw [Matrix.sum_apply]
    exact Ideal.sum_mem _ fun k _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (hgI k)
  let f0 : (Fin a → S) →ₗ[S] (Fin a → S ⧸ I) := q ∘ₗ (LinearMap.id - (Φ * Ψ).mulVecLin)
  have h1 : K ≤ LinearMap.ker f0 := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    simp only [f0, LinearMap.comp_apply]
    apply hq
    intro j
    have hy : Φ.mulVecLin y - (Φ * Ψ).mulVecLin (Φ.mulVecLin y) = -(Matrix.mulVec (∑ k, g k • E k) y) := by
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hΨ, Matrix.add_mulVec]
      abel
    rw [LinearMap.sub_apply, LinearMap.id_apply, hy, Pi.neg_apply]
    exact Submodule.neg_mem _ (hmv _ hE y j)
  let f1 : M →ₗ[S] (Fin a → S ⧸ I) := K.liftQ f0 h1
  have h2 : T ≤ LinearMap.ker f1 := by
    intro m hm
    obtain ⟨m', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
    rw [LinearMap.mem_ker, map_smul]
    exact hqI u huI _
  let i : QuotSMulTop u M →ₗ[S] (Fin a → S ⧸ I) := T.liftQ f1 h2
  let p : (Fin a → S ⧸ I) →ₗ[S] QuotSMulTop u M :=
    ∑ j, (Submodule.liftQ I (LinearMap.toSpanSingleton S _ (pr (Pi.single j 1)))
      (fun s hs => by
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
        exact hI s hs _)) ∘ₗ LinearMap.proj j
  have hpq : ∀ v, p (q v) = pr v := by
    intro v
    simp only [p, q, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, LinearMap.pi_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
      LinearMap.toSpanSingleton_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← Finset.univ_sum_single v, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul]
    refine congrArg pr ?_
    funext k
    by_cases h : k = j <;> simp [h]
  have hpi : p ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun n => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective T n
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K m
    show p (q (x - (Φ * Ψ).mulVecLin x)) = pr x
    rw [hpq, map_sub, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, hK, sub_zero]
  have := hflat
  have : Module.Flat R (Fin a → S ⧸ I) :=
    Module.Flat.of_linearEquiv
      (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun _ : Fin a => S ⧸ I)).symm
  exact Module.Flat.of_retract (i.restrictScalars R) (p.restrictScalars R)
    (LinearMap.ext fun n => LinearMap.congr_fun hpi n)

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

private theorem exists_generalized_inverse_mod_ideal {R S B P : Type} [CommRing R] [CommRing S]
    [Algebra R S] [CommRing B] [Algebra R B] [AddCommGroup P] [Module B P] {a b r : ℕ}
    (Φ : Matrix (Fin a) (Fin b) S) (u : S) (g : Fin r → S) (π : S →ₐ[R] B)
    (hker : RingHom.ker (π : S →+* B) = Ideal.span (Set.range g))
    (hπ : Function.Surjective π) (ε : (Fin a → S) →ₛₗ[(π : S →+* B)] P)
    (hproj : Module.Projective B P) (hε : Function.Surjective ε)
    (hkerε : ∀ y, ε y = 0 ↔ ∃ w w', y = Φ.mulVec w + u • w') (hu : π u = 0) :
    ∃ (Ψ : Matrix (Fin b) (Fin a) S) (E : Fin r → Matrix (Fin a) (Fin b) S),
      Φ * Ψ * Φ = Φ + ∑ k, g k • E k := by
  classical
  let p : Fin a → P := fun m => ε (Pi.single m 1)
  have hεsum : ∀ y : Fin a → S, ε y = ∑ m, π (y m) • p m := by
    intro y
    conv_lhs => rw [show y = ∑ m, y m • Pi.single m 1 from by
      funext j; simp [Finset.sum_apply, Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, p]
  let F : (Fin a → B) →ₗ[B] P := Fintype.linearCombination B p
  have hF : ∀ β, F β = ∑ m, β m • p m := fun β => Fintype.linearCombination_apply B p β
  have hFsurj : Function.Surjective F := by
    intro x
    obtain ⟨y, rfl⟩ := hε x
    exact ⟨fun m => π (y m), by rw [hF, hεsum]⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property F LinearMap.id hFsurj
  have hlift : ∀ β : Fin a → B, ∃ y : Fin a → S, (fun m => π (y m)) = β := by
    intro β
    choose y hy using fun m => hπ (β m)
    exact ⟨y, funext hy⟩
  have hcol : ∀ m : Fin a, ∃ w : Fin b → S,
      (fun j => π ((Φ.mulVec w) j)) = Pi.single m 1 - s (p m) := by
    intro m
    obtain ⟨y, hy⟩ := hlift (Pi.single m 1 - s (p m))
    have h0 : ε y = 0 := by
      rw [hεsum, ← hF]
      have : (fun m => π (y m)) = Pi.single m 1 - s (p m) := hy
      rw [show (fun m => π (y m)) = _ from this, map_sub, hF]
      have hs' : F (s (p m)) = p m := by
        have := congr_arg (fun φ => φ (p m)) hs
        simpa using this
      rw [hs']
      simp [Pi.single_apply]
    obtain ⟨w, w', hw⟩ := (hkerε y).1 h0
    refine ⟨w, ?_⟩
    rw [← hy, hw]
    funext j
    simp [hu]
  choose w hw using hcol
  have hs' : ∀ x, F (s x) = x := fun x => by
    have := congr_arg (fun φ => φ x) hs
    simpa using this
  have hcolε : ∀ j, ε (fun l => Φ l j) = 0 := by
    intro j
    refine (hkerε _).2 ⟨Pi.single j 1, 0, ?_⟩
    funext l
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  let Ψ : Matrix (Fin b) (Fin a) S := Matrix.of fun j m => w m j
  have hD : ∀ l j, (Φ * Ψ * Φ - Φ) l j ∈ Ideal.span (Set.range g) := by
    intro l j
    rw [← hker, RingHom.mem_ker]
    have hcomp : ∀ m, π ((Φ * Ψ) l m) = (Pi.single m 1 - s (p m) : Fin a → B) l := by
      intro m
      have := congr_fun (hw m) l
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Ψ] using this
    have hsum : ∑ m, π (Φ m j) • s (p m) = 0 := by
      have h1 := hεsum (fun l => Φ l j)
      rw [hcolε j] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        simp_rw [← LinearMap.map_smul, ← map_sum, ← h1, map_zero]
    have hsuml := congr_fun hsum l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hsuml
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.sub_apply, map_sub, Matrix.mul_apply, map_sum]
    simp only [AlgHom.coe_toRingHom, map_mul, hcomp, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [show ∑ m, s (p m) l * π (Φ m j) = ∑ m, π (Φ m j) * s (p m) l from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, hsuml]
    ring
  choose c hc using fun l j => (Submodule.mem_span_range_iff_exists_fun S).1 (hD l j)
  refine ⟨Ψ, fun k => Matrix.of fun l j => c l j k, ?_⟩
  ext l j
  have h1 := hc l j
  simp only [smul_eq_mul] at h1
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [show ∑ k, g k * c l j k = ∑ k, c l j k * g k from Finset.sum_congr rfl fun _ _ => mul_comm _ _, h1]
  simp

private theorem chart_witnesses_lemma {ι : Type} [Fintype ι] {R : Type} [CommRing R] {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)) (i : ι)
    (H : ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P) (ε : (Fin a → MvPolynomial ι R) →ₛₗ[(π : MvPolynomial ι R →+* B)] P), Algebra.Smooth R B ∧ Module.Projective B P ∧ Function.Surjective π ∧ π (X i) = 1 ∧ Function.Surjective ε ∧ ∀ y, ε y = 0 ↔ ∃ w w', y = Φ.mulVec w + (X i - 1 : MvPolynomial ι R) • w') :
    ∃ (r : ℕ) (g : Fin r → MvPolynomial ι R),
      Algebra.FormallySmooth R (MvPolynomial ι R ⧸ Ideal.span (Set.range g)) ∧
      (∃ c : Fin r → MvPolynomial ι R, (X i - 1 : MvPolynomial ι R) = ∑ k, c k * g k) ∧
      (∀ k, ∃ (C : Matrix (Fin b) (Fin a) (MvPolynomial ι R)) (C' : Matrix (Fin a) (Fin a) (MvPolynomial ι R)),
        g k • (1 : Matrix (Fin a) (Fin a) (MvPolynomial ι R)) = Φ * C + (X i - 1 : MvPolynomial ι R) • C') ∧
      (∃ (Ψ : Matrix (Fin b) (Fin a) (MvPolynomial ι R)) (E : Fin r → Matrix (Fin a) (Fin b) (MvPolynomial ι R)),
        Φ * Ψ * Φ = Φ + ∑ k, g k • E k) := by
  classical
  obtain ⟨B, _, _, π, P, _, _, ε, hsm, hproj, hπ, hX, hεs, hkerε⟩ := H
  have hfg := Algebra.FinitePresentation.ker_fG_of_surjective π hπ
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hker : RingHom.ker (π : MvPolynomial ι R →+* B) = Ideal.span (Set.range g) := hg.symm
  have hu : π (X i - 1) = 0 := by rw [map_sub, hX, map_one, sub_self]
  refine ⟨r, g, ?_, ?_, ?_, ?_⟩
  · have e : (MvPolynomial ι R ⧸ RingHom.ker (π : MvPolynomial ι R →+* B)) ≃ₐ[R] B :=
      Ideal.quotientKerAlgEquivOfSurjective hπ
    have : Algebra.FormallySmooth R (MvPolynomial ι R ⧸ RingHom.ker (π : MvPolynomial ι R →+* B)) :=
      Algebra.FormallySmooth.of_equiv e.symm
    rw [hker] at this
    exact this
  · have hmem : (X i - 1 : MvPolynomial ι R) ∈ Ideal.span (Set.range g) := by
      rw [← hker, RingHom.mem_ker]; exact hu
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPolynomial ι R)).1 hmem
    exact ⟨c, by rw [← hc]; simp [smul_eq_mul]⟩
  · intro k
    have hgk : π (g k) = 0 := by
      have : g k ∈ RingHom.ker (π : MvPolynomial ι R →+* B) := by
        rw [hker]; exact Ideal.subset_span ⟨k, rfl⟩
      exact this
    have hcol : ∀ m : Fin a, ∃ w w', g k • (Pi.single m 1 : Fin a → MvPolynomial ι R) =
        Φ.mulVec w + (X i - 1 : MvPolynomial ι R) • w' := by
      intro m
      refine (hkerε _).1 ?_
      rw [LinearMap.map_smulₛₗ]
      simp [hgk]
    choose w w' hw using hcol
    refine ⟨Matrix.of fun j m => w m j, Matrix.of fun l m => w' m l, ?_⟩
    ext l m
    have h1 := congr_fun (hw m) l
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.single_apply] at h1
    simp only [Matrix.smul_apply, Matrix.one_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.of_apply, smul_eq_mul]
    rw [h1]
    simp [Matrix.mulVec, dotProduct]
  · exact exists_generalized_inverse_mod_ideal Φ (X i - 1) g π hker hπ ε hproj hεs hkerε hu

private theorem formallySmooth_quotient_of_aeval_shift_mem_sq {ι R : Type} [CommRing R] {r : ℕ}
    (g : Fin r → MvPolynomial ι R) (a : ι → Fin r → MvPolynomial ι R)
    (b : Fin r → Fin r → Fin r → MvPolynomial ι R)
    (h : ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) = ∑ k, ∑ l, b j k l * (g k * g l)) :
    Algebra.FormallySmooth R (MvPolynomial ι R ⧸ Ideal.span (Set.range g)) := by
  set I := Ideal.span (Set.range g) with hI
  let f : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ I := Ideal.Quotient.mkₐ R I
  have hkerf : RingHom.ker f.toRingHom = I := Ideal.Quotient.mkₐ_ker R I
  let x : ι → MvPolynomial ι R := fun i => X i + ∑ k, a i k * g k
  let φ : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ RingHom.ker f.toRingHom ^ 2 :=
    (Ideal.Quotient.mkₐ R _).comp (aeval x)
  have hgI : ∀ k, g k ∈ I := fun k => Ideal.subset_span ⟨k, rfl⟩
  have hφ : ∀ p ∈ I, φ p = 0 := by
    have hle : I ≤ RingHom.ker φ := by
      show Ideal.span (Set.range g) ≤ RingHom.ker φ
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      show Ideal.Quotient.mk _ (aeval x (g j)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, hkerf, h j, pow_two]
      exact Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun l _ =>
        Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul (hgI k) (hgI l))
    exact fun p hp => hle hp
  let s := Ideal.Quotient.liftₐ I φ hφ
  refine Algebra.FormallySmooth.of_split f s ?_
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  have hs : s (Ideal.Quotient.mkₐ R I (X i)) = Ideal.Quotient.mk _ (x i) := by
    show (Ideal.Quotient.liftₐ I φ hφ) (Ideal.Quotient.mk I (X i)) = _
    rw [Ideal.Quotient.liftₐ_apply]
    erw [Ideal.Quotient.lift_mk]
    show (Ideal.Quotient.mkₐ R _) (aeval x (X i)) = _
    rw [aeval_X]
    rfl
  simp only [AlgHom.comp_apply, hs, AlgHom.id_apply]
  rw [AlgHom.kerSquareLift_mk]
  simp [f, x, Ideal.Quotient.eq_zero_iff_mem.2 (hgI _)]

theorem _root_.GlobalTheory.exists_noetherian_subring_homogeneous_matrix_flat_charts :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (a b : ℕ) (d : Fin a → ℤ) (e : Fin b → ℤ) (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)), (∀ l j, Φ l j ∈ _root_.GlobalTheory.polyGrading ι R (e j - d l)) → (∀ i : ι, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P) (ε : (Fin a → MvPolynomial ι R) →ₛₗ[(π : MvPolynomial ι R →+* B)] P), Algebra.Smooth R B ∧ Module.Projective B P ∧ Function.Surjective π ∧ π (X i) = 1 ∧ Function.Surjective ε ∧ ∀ y, ε y = 0 ↔ ∃ w w', y = Φ.mulVec w + (X i - 1 : MvPolynomial ι R) • w') → ∃ (R₀ : Subring R) (Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀)), IsNoetherianRing R₀ ∧ Φ₀.map (MvPolynomial.map R₀.subtype) = Φ ∧ (∀ l j, Φ₀ l j ∈ _root_.GlobalTheory.polyGrading ι R₀ (e j - d l)) ∧ ∀ i : ι, Module.Flat R₀ (QuotSMulTop (X i - 1 : MvPolynomial ι R₀) ((Fin a → MvPolynomial ι R₀) ⧸ LinearMap.range Φ₀.mulVecLin)) := by
  intro ι _ _ R _ a b d e Φ hΦ H
  classical
  choose r g hsm hc hC hΨ using fun i => chart_witnesses_lemma Φ i (H i)
  choose wa wb hwit using fun i => _root_.GlobalTheory.exists_witnesses_of_formallySmooth_quotient ι R (r i) (g i) (hsm i)
  choose c hc' using hc
  choose C C' hCC using hC
  choose Ψ E hΨE using hΨ
  let pols : (Fin a × Fin b) ⊕ (Σ i, Fin (r i)) ⊕ (Σ i, ι × Fin (r i)) ⊕
      (Σ i, Fin (r i) × Fin (r i) × Fin (r i)) ⊕ (Σ i, Fin (r i)) ⊕ (Σ i, Fin (r i) × Fin b × Fin a) ⊕
      (Σ i, Fin (r i) × Fin a × Fin a) ⊕ (Σ i, Fin b × Fin a) ⊕ (Σ i, Fin (r i) × Fin a × Fin b) →
      MvPolynomial ι R :=
    Sum.elim (fun x => Φ x.1 x.2) (Sum.elim (fun x => g x.1 x.2) (Sum.elim (fun x => wa x.1 x.2.1 x.2.2)
      (Sum.elim (fun x => wb x.1 x.2.1 x.2.2.1 x.2.2.2) (Sum.elim (fun x => c x.1 x.2)
      (Sum.elim (fun x => C x.1 x.2.1 x.2.2.1 x.2.2.2) (Sum.elim (fun x => C' x.1 x.2.1 x.2.2.1 x.2.2.2)
      (Sum.elim (fun x => Ψ x.1 x.2.1 x.2.2) (fun x => E x.1 x.2.1 x.2.2.1 x.2.2.2))))))))
  let T : Set R := ⋃ j, ↑(pols j).coeffs
  have hT : T.Finite := Set.finite_iUnion fun j => Finset.finite_toSet _
  let R₀ := Subring.closure T
  have hnoeth : IsNoetherianRing R₀ := is_noetherian_subring_closure T hT
  let φ : MvPolynomial ι R₀ →+* MvPolynomial ι R := MvPolynomial.map R₀.subtype
  have hφinj : Function.Injective φ := MvPolynomial.map_injective _ Subtype.val_injective
  have hlift : ∀ j, ∃ p₀, φ p₀ = pols j := by
    intro j
    have : pols j ∈ Set.range φ := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro x hx
      exact ⟨⟨x, Subring.subset_closure (Set.mem_iUnion.2 ⟨j, hx⟩)⟩, rfl⟩
    exact this
  choose L hL using hlift
  let Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀) := Matrix.of fun l j => L (Sum.inl (l, j))
  let g₀ : ∀ i, Fin (r i) → MvPolynomial ι R₀ := fun i k => L (Sum.inr (Sum.inl ⟨i, k⟩))
  let wa₀ : ∀ i, ι → Fin (r i) → MvPolynomial ι R₀ := fun i v k =>
    L (Sum.inr (Sum.inr (Sum.inl ⟨i, v, k⟩)))
  let wb₀ : ∀ i, Fin (r i) → Fin (r i) → Fin (r i) → MvPolynomial ι R₀ := fun i j k l =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, j, k, l⟩))))
  let c₀ : ∀ i, Fin (r i) → MvPolynomial ι R₀ := fun i k =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k⟩)))))
  let C₀ : ∀ i, Fin (r i) → Matrix (Fin b) (Fin a) (MvPolynomial ι R₀) := fun i k => Matrix.of fun j m =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k, j, m⟩))))))
  let C'₀ : ∀ i, Fin (r i) → Matrix (Fin a) (Fin a) (MvPolynomial ι R₀) := fun i k => Matrix.of fun l m =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k, l, m⟩)))))))
  let Ψ₀ : ∀ i, Matrix (Fin b) (Fin a) (MvPolynomial ι R₀) := fun i => Matrix.of fun j m =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, j, m⟩))))))))
  let E₀ : ∀ i, Fin (r i) → Matrix (Fin a) (Fin b) (MvPolynomial ι R₀) := fun i k => Matrix.of fun l j =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨i, k, l, j⟩))))))))
  have hΦ₀ : ∀ l j, φ (Φ₀ l j) = Φ l j := fun l j => hL _
  have hg₀ : ∀ i k, φ (g₀ i k) = g i k := fun i k => hL _
  have hwa₀ : ∀ i v k, φ (wa₀ i v k) = wa i v k := fun i v k => hL _
  have hwb₀ : ∀ i j k l, φ (wb₀ i j k l) = wb i j k l := fun i j k l => hL _
  have hc₀ : ∀ i k, φ (c₀ i k) = c i k := fun i k => hL _
  have hC₀ : ∀ i k j m, φ (C₀ i k j m) = C i k j m := fun i k j m => hL _
  have hC'₀ : ∀ i k l m, φ (C'₀ i k l m) = C' i k l m := fun i k l m => hL _
  have hΨ₀ : ∀ i j m, φ (Ψ₀ i j m) = Ψ i j m := fun i j m => hL _
  have hE₀ : ∀ i k l j, φ (E₀ i k l j) = E i k l j := fun i k l j => hL _
  have hφX : ∀ v, φ (X v) = X v := fun v => MvPolynomial.map_X _ _
  refine ⟨R₀, Φ₀, hnoeth, ?_, ?_, ?_⟩
  · exact Matrix.ext fun l j => hΦ₀ l j
  · intro l j
    rw [_root_.GlobalTheory.mem_polyGrading_iff]
    intro α hα
    refine (_root_.GlobalTheory.mem_polyGrading_iff.1 (hΦ l j)) α ?_
    rw [← hΦ₀ l j, MvPolynomial.coeff_map]
    intro h0
    exact hα (Subtype.val_injective (by simpa using h0))
  · intro i
    have hwit₀ : ∀ j, aeval (fun v => X v + ∑ k, wa₀ i v k * g₀ i k) (g₀ i j) =
        ∑ k, ∑ l, wb₀ i j k l * (g₀ i k * g₀ i l) := by
      intro j
      apply hφinj
      rw [aeval_eq_bind₁, MvPolynomial.map_bind₁]
      simp only [φ] at hg₀ hwa₀ hwb₀ hφX ⊢
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_mul, hg₀, hwa₀, hwb₀, hφX]
      rw [← aeval_eq_bind₁]
      exact hwit i j
    haveI : Algebra.FormallySmooth R₀ (MvPolynomial ι R₀ ⧸ Ideal.span (Set.range (g₀ i))) :=
      formallySmooth_quotient_of_aeval_shift_mem_sq (g₀ i) (wa₀ i) (wb₀ i) hwit₀
    haveI : Algebra.FinitePresentation R₀ (MvPolynomial ι R₀ ⧸ Ideal.span (Set.range (g₀ i))) :=
      Algebra.FinitePresentation.of_finiteType.1 inferInstance
    haveI : Algebra.Smooth R₀ (MvPolynomial ι R₀ ⧸ Ideal.span (Set.range (g₀ i))) :=
      ⟨inferInstance, inferInstance⟩
    refine _root_.GlobalTheory.flat_quotSMulTop_coker_of_matrix_witnesses R₀ (MvPolynomial ι R₀) (r i) a b (g₀ i)
      (X i - 1) Φ₀ inferInstance ⟨c₀ i, ?_⟩ (fun k => ⟨C₀ i k, C'₀ i k, ?_⟩) ⟨Ψ₀ i, E₀ i, ?_⟩
    · apply hφinj
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_one, map_sum, map_mul, hc₀, hg₀, hφX]
      exact hc' i
    · refine Matrix.ext fun l m => ?_
      apply hφinj
      have h1 := congr_fun (congr_fun (hCC i k) l) m
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply,
        smul_eq_mul] at h1 ⊢
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_mul, map_sum, map_sub, map_one, hg₀, hφX, hΦ₀, hC₀, hC'₀,
        apply_ite φ, map_zero, map_one]
      simpa [Φ₀, C₀, C'₀] using h1
    · refine Matrix.ext fun l j => ?_
      apply hφinj
      have h1 := congr_fun (congr_fun (hΨE i) l) j
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul] at h1 ⊢
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_mul, map_sum, hΦ₀, hΨ₀, hE₀, hg₀]
      exact h1

end GlobalTheory
