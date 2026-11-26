module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTensorCommutant
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTensorCommutant
noncomputable section

open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

section Columns

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def colMat (c : n → Matrix n n A) (v : n → A) : Matrix n n A :=
  Matrix.of fun i j => (c j *ᵥ v) i

omit [DecidableEq n] in
theorem colMat_mulVec (c : n → Matrix n n A) (v a : n → A) :
    colMat c v *ᵥ a = (∑ j, a j • c j) *ᵥ v := by
  rw [Matrix.sum_mulVec]
  funext i
  simp only [Finset.sum_apply, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  simp [colMat, Matrix.mulVec, dotProduct, mul_comm]

omit [DecidableEq n] in
theorem colMat_map {B : Type} [CommRing B] (f : A →+* B) (c : n → Matrix n n A) (v : n → A) :
    (colMat c v).map f = colMat (fun j => (c j).map f) (fun i => f (v i)) := by
  ext i j
  simp [colMat, Matrix.mulVec, dotProduct]

theorem eq_sum_of_commute_cols {c : n → Matrix n n A} {v : n → A} (hB : IsUnit (colMat c v))
    (hc : ∀ i j, c i * c j = c j * c i) {N : Matrix n n A} (hN : ∀ j, N * c j = c j * N) :
    ∃ a : n → A, ∑ j, a j • c j = N := by
  obtain ⟨a, ha⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hB (N *ᵥ v)
  refine ⟨a, Matrix.toLin'.injective (LinearMap.ext fun y => ?_)⟩
  obtain ⟨t, rfl⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hB y
  have ha' : (∑ j, a j • c j) *ᵥ v = N *ᵥ v := by rw [← colMat_mulVec]; exact ha
  have h1 : N * (∑ j, t j • c j) = (∑ j, t j • c j) * N := by
    simp [Finset.mul_sum, Finset.sum_mul, hN]
  have h2 : (∑ j, a j • c j) * (∑ j, t j • c j) = (∑ j, t j • c j) * (∑ j, a j • c j) :=
    Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ =>
      (Commute.smul_left (Commute.smul_right (hc i j) _) _)
  simp only [Matrix.toLin'_apply, colMat_mulVec, Matrix.mulVec_mulVec]
  rw [h1, h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha']

theorem map_commute_of_mem_genAlg {B : Type} [CommRing B] (f : A →+* B) {M l : Matrix n n A}
    {N : Matrix n n B} (h : N * M.map f = M.map f * N) (hl : l ∈ genAlg M) :
    N * l.map f = l.map f * N := by
  unfold genAlg at hl
  induction hl using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact h
  | algebraMap r =>
    have : (algebraMap A (Matrix n n A) r).map f = f r • (1 : Matrix n n B) := by
      ext i j; by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
    rw [this]; simp
  | add x y _ _ hx hy => rw [Matrix.map_add _ (map_add f), Matrix.mul_add, Matrix.add_mul, hx, hy]
  | mul x y _ _ hx hy =>
    rw [Matrix.map_mul, ← Matrix.mul_assoc, hx, Matrix.mul_assoc, hy, Matrix.mul_assoc]

end Columns

theorem exists_sum_basis_tmul {F P A : Type} [Field F] [AddCommGroup P] [Module F P]
    [AddCommGroup A] [Module F A] {n : Type} [Fintype n] (b : Module.Basis n F P)
    (x : P ⊗[F] A) : ∃ a : n → A, ∑ j, b j ⊗ₜ[F] a j = x := by
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_left b x
  exact ⟨c, by rw [← hc, Finsupp.sum_fintype]; simp⟩

theorem toMat_tmul_eq_smul {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type}
    [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R]
    [Algebra F R] (l : plusAlg σ J γ) (a : E ⊗[F] R) :
    toMat σ J γ R (l ⊗ₜ a) = a • ((l : genAlg γ) : Matrix n n E).map (inclE (F := F) R) := by
  rw [Algebra.smul_def, Algebra.commutes]
  exact Algebra.TensorProduct.lift_tmul _ _ _ l a

theorem pointsCommutant : PointsCommutant := by
  intro F E _ _ _ _ n _ _ σ J γ _ hA hP R _ _
  obtain ⟨-, ⟨b⟩, hbij⟩ := hP
  obtain ⟨-, -, -, ⟨v, hv⟩, -⟩ := hA
  let c : n → Matrix n n E := fun j => ((b j : genAlg (γ : Matrix n n E)) : Matrix n n E)
  have hB : IsUnit (colMat c v) := by
    refine Matrix.mulVec_surjective_iff_isUnit.1 fun y => ?_
    obtain ⟨l, rfl⟩ := hv.2 y
    obtain ⟨x, rfl⟩ := hbij.2 l
    obtain ⟨a, rfl⟩ := exists_sum_basis_tmul b x
    refine ⟨a, ?_⟩
    rw [colMat_mulVec]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [plusTensor, Algebra.TensorProduct.productMap_apply_tmul, mul_comm]
    exact Algebra.smul_def (a j) (c j)
  let f : E →+* E ⊗[F] R := inclE (F := F) R
  have hB' : IsUnit (colMat (fun j => (c j).map f) (fun i => f (v i))) := by
    rw [← colMat_map]; exact hB.map f.mapMatrix
  have hsum : ∀ a : n → E ⊗[F] R, toMat σ J (γ : Matrix n n E) R (∑ j, b j ⊗ₜ[F] a j) =
      ∑ j, a j • (c j).map f := fun a => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; exact Finset.sum_congr rfl fun j _ => toMat_tmul_eq_smul _ _ _ _ _ _
  refine ⟨(injective_iff_map_eq_zero _).2 fun u hu => ?_, fun N => ⟨fun hN => ?_, ?_⟩⟩
  · obtain ⟨a, rfl⟩ := exists_sum_basis_tmul b u
    rw [hsum] at hu
    have : a = 0 := Matrix.mulVec_injective_of_isUnit hB'
      (by rw [colMat_mulVec, hu, Matrix.zero_mulVec, Matrix.mulVec_zero])
    simp [this]
  · obtain ⟨a, ha⟩ := eq_sum_of_commute_cols hB' (fun i j => by
      rw [← Matrix.map_mul, ← Matrix.map_mul]
      exact congrArg (fun l : genAlg (γ : Matrix n n E) => (l : Matrix n n E).map f)
        (mul_comm (b i : genAlg (γ : Matrix n n E)) (b j)))
      (fun j => map_commute_of_mem_genAlg f hN (b j : genAlg (γ : Matrix n n E)).2)
    exact ⟨_, (hsum a).trans ha⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨a, rfl⟩ := exists_sum_basis_tmul b u
    rw [hsum]
    refine Commute.sum_left _ _ _ fun j _ => Commute.smul_left ?_ _
    exact (map_commute_of_mem_genAlg f rfl (b j : genAlg (γ : Matrix n n E)).2).symm

end GlobalTheory.RegSS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTensorCommutantStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_tensor_commutant : GlobalTheory.RegSS.PointsCommutant := by
  first | exact @GlobalTheory.RegSS.pointsCommutant | exact GlobalTheory.RegSS.pointsCommutant | (intros; apply GlobalTheory.RegSS.pointsCommutant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianTraceFormOfTraceFormPerfect
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianTraceFormOfTraceFormPerfect
noncomputable section

open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms

namespace GlobalTheory.RegSS

section

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem form_conj_symm (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {J : Matrix n n A}
    (hJ : IsHerm σ J) (a b : n → A) : σ (form σ J b a) = form σ J a b := by
  have hJij : ∀ i j, σ (J i j) = J j i := fun i j => by
    have := congrFun (congrFun hJ j) i
    simpa [cT] using this
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, hform, map_sum, map_mul, hσ, hJij]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem eq_zero_of_form_eq_zero (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det)
    (a : n → A) (h0 : ∀ w, form σ J a w = 0) : a = 0 := by
  have hJa : J *ᵥ a = 0 := by
    funext i
    have := h0 (Pi.single i 1)
    have hs : (fun k => σ ((Pi.single i (1 : A) : n → A) k)) = Pi.single i 1 := by
      funext k; by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rw [form, hform_eq, hs] at this
    simpa [dotProduct, Pi.single_apply] using this
  calc a = (J⁻¹ * J) *ᵥ a := by rw [Matrix.nonsing_inv_mul _ hJ, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hJa, Matrix.mulVec_zero]

end

theorem traceClause_of_tracePerfect (hP : TracePerfect) : TraceClause := by
  intro F E _ _ _ _ n _ _ σ J γ h hA
  haveI := quad_finite h.quad
  haveI := genAlg_isReduced h hA
  obtain ⟨b⟩ := hA.2.2.1
  haveI : Module.Free E (genAlg (γ : Matrix n n E)) := Module.Free.of_basis b
  haveI : Module.Finite E (genAlg (γ : Matrix n n E)) := Module.Finite.of_basis b
  obtain ⟨v, hv⟩ := hA.2.2.2.1
  obtain ⟨τ, hτ, hττ, hτE, hplus⟩ := exists_adjEquiv h hA
  have hP' := hP F E (genAlg (γ : Matrix n n E))
  let φ : genAlg (γ : Matrix n n E) →ₗ[E] E :=
    { toFun := fun y => form (σ : E →+* E) J ((y : Matrix n n E) *ᵥ v) v
      map_add' := fun a b => by
        simp only [form, hform_eq, Subalgebra.coe_add, Matrix.add_mulVec, Matrix.mulVec_add,
          dotProduct_add]
      map_smul' := fun c a => by
        simp only [form, hform_eq, Subalgebra.coe_smul, Matrix.smul_mulVec,
          Matrix.mulVec_smul, dotProduct_smul, RingHom.id_apply, smul_eq_mul] }
  obtain ⟨x, hx⟩ := hP'.2 φ
  have hxy : ∀ y, Algebra.trace E _ (x * y) = form (σ : E →+* E) J ((y : Matrix n n E) *ᵥ v) v :=
    fun y => by
      have := LinearMap.congr_fun hx y
      rwa [Algebra.traceForm_apply] at this

  have hK : ∀ y y' : genAlg (γ : Matrix n n E),
      form (σ : E →+* E) J ((y : Matrix n n E) *ᵥ v) ((y' : Matrix n n E) *ᵥ v) =
        Algebra.trace E _ (x * (τ y' * y)) := fun y y' => by
    rw [hxy, form_adj _ h.nondeg, ← hτ, Matrix.mulVec_mulVec]
    rfl

  let σE : E ≃+* E := RingEquiv.ofBijective (σ : E →+* E) (Function.Involutive.bijective h.quad.invol)
  have hTr : ∀ z, Algebra.trace E _ (τ z) = σ (Algebra.trace E (genAlg (γ : Matrix n n E)) z) := by
    intro z
    have he : (algebraMap E (genAlg (γ : Matrix n n E))).comp (σE : E →+* E) =
        (τ.toRingEquiv : genAlg (γ : Matrix n n E) →+* genAlg (γ : Matrix n n E)).comp
          (algebraMap E (genAlg (γ : Matrix n n E))) := RingHom.ext fun e => (hτE e).symm
    have := Algebra.trace_eq_of_equiv_equiv σE τ.toRingEquiv he z
    rw [this]
    exact (σE.apply_symm_apply _).symm

  have hxτ : τ x = x := by
    refine hP'.1 (LinearMap.ext fun y => ?_)
    simp only [Algebra.traceForm_apply]
    have e1 : τ x * y = τ (x * (τ y * 1)) := by rw [mul_one, map_mul, hττ]
    rw [e1, hTr, ← hK]
    have hs := form_conj_symm (σ : E →+* E) h.quad.invol h.herm
      ((y : Matrix n n E) *ᵥ v) (((1 : genAlg (γ : Matrix n n E)) : Matrix n n E) *ᵥ v)
    simp only [RingHom.coe_coe] at hs
    rw [hs, hK, map_one, one_mul]
  have hxplus : x ∈ plusAlg σ J (γ : Matrix n n E) := (hplus x).2 hxτ

  have hinj : ∀ y : genAlg (γ : Matrix n n E), x * y = 0 → y = 0 := by
    intro y hy
    have h0 : (y : Matrix n n E) *ᵥ v = 0 := by
      refine eq_zero_of_form_eq_zero (σ : E →+* E) h.nondeg _ fun w => ?_
      obtain ⟨y', rfl⟩ := hv.2 w
      simp only
      rw [hK, mul_left_comm, hy, mul_zero, map_zero]
    refine hv.1 ?_
    simp only [h0, ZeroMemClass.coe_zero, Matrix.zero_mulVec]

  let xp : plusAlg σ J (γ : Matrix n n E) := ⟨x, hxplus⟩
  haveI : Module.Finite F (genAlg (γ : Matrix n n E)) := Module.Finite.trans E _
  have hsurj : Function.Surjective (LinearMap.mulLeft F xp) := by
    refine LinearMap.injective_iff_surjective.1 fun a c hac => ?_
    have : x * ((a : genAlg (γ : Matrix n n E)) - c) = 0 := by
      have := congrArg Subtype.val hac
      simp only [LinearMap.mulLeft_apply] at this
      rw [mul_sub]; exact sub_eq_zero.2 this
    exact Subtype.ext (sub_eq_zero.1 (hinj _ this))
  obtain ⟨w, hw⟩ := hsurj 1
  have hu : IsUnit xp := ⟨⟨xp, w, hw, by rw [mul_comm]; exact hw⟩, rfl⟩
  refine ⟨hu.unit, v, hv, fun y y' => ⟨τ y', hτ y', ?_⟩⟩
  rw [hK]
  congr 1
  change x * (τ y' * y) = x * y * τ y'
  ring

end GlobalTheory.RegSS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianTraceFormOfTraceFormPerfectStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTraceForm_of_traceForm_perfect : GlobalTheory.RegSS.TracePerfect → GlobalTheory.RegSS.TraceClause := by
  first | exact @GlobalTheory.RegSS.traceClause_of_tracePerfect | exact GlobalTheory.RegSS.traceClause_of_tracePerfect | (intros; apply GlobalTheory.RegSS.traceClause_of_tracePerfect <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerSplitRankUpperBound
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerSplitRankUpperBound
open GlobalTheory.RegSS

noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS.SplitRankBound

theorem zpow_sum_eq {M : Type} [CommGroup M] (a : M) {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, _root_.zpow_add, ih]

theorem two_zpow_eq_one {F : Type} [Field F] [CharZero F] {m : ℤ} (h : (2:F) ^ m = 1) : m = 0 := by
  have h2 : ((2:ℚ) ^ m : ℚ) = (2:ℚ) ^ (0:ℤ) := by
    rw [zpow_zero]
    apply (algebraMap ℚ F).injective
    rw [map_zpow₀, map_ofNat, h, map_one]
  exact (zpow_right_strictMono₀ one_lt_two).injective h2

set_option maxHeartbeats 1000000 in
theorem splitRankUpper (hL : SubtorusLaurent) (hM : CharacterMonomial) (hP : SeparatingPoints) :
    SplitRankUpper := by
  intro F E _ _ _ _ n _ _ σ J γ hR hPl hPC k K _ _ he s hA
  classical
  obtain ⟨A⟩ := hA
  haveI : Module.Finite F (plusAlg σ J (γ : Matrix n n E)) := Module.Finite.of_basis hPl.2.1.some
  obtain ⟨ψ, hsep, hfield⟩ := hP F E σ hR.quad (plusAlg σ J (γ : Matrix n n E)) k K he
  have hinj := (hPC F).1
  have hcent := (hPC F).2.2
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective
    (toMat σ J (γ : Matrix n n E) F).toLinearMap (LinearMap.ker_eq_bot.2 hinj)
  have hρT : ∀ x, ρ (toMat σ J (γ : Matrix n n E) F x) = x := fun x => LinearMap.congr_fun hρ x
  have hex : ∀ t : Fin s → Fˣ, ∃ u ∈ normOne σ J (γ : Matrix n n E) F,
      toMat σ J (γ : Matrix n n E) F (u : LPts σ J (γ : Matrix n n E) F) =
        ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) :=
    fun t => (hcent _).1 (A.mem F t)
  have hTu : ∀ t : Fin s → Fˣ, toMat σ J (γ : Matrix n n E) F
      (ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F))) =
        ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) := by
    intro t; obtain ⟨u, -, hu⟩ := hex t; rw [← hu, hρT]
  have hnorm : ∀ t : Fin s → Fˣ,
      ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) *
        lConj σ J (γ : Matrix n n E) F (ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)))
          = 1 := by
    intro t; obtain ⟨u, hu, hu'⟩ := hex t; rw [← hu', hρT]; exact hu
  let uu : (Fin s → Fˣ) →* LPts σ J (γ : Matrix n n E) F :=
    { toFun := fun t => ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F))
      map_one' := hinj (by rw [hTu, map_one, Units.val_one, map_one])
      map_mul' := fun a b => hinj (by
        rw [map_mul (toMat σ J (γ : Matrix n n E) F), hTu a, hTu b, ← Units.val_mul, ← map_mul, hTu]) }
  have huu : ∀ t, uu t = ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) := fun _ => rfl
  clear_value uu
  obtain ⟨S, C, hC⟩ := hL F E n σ J γ s A
  have hmono : ∀ i, ∃ a : Fin s → ℤ, ∀ t : Fin s → Fˣ,
      ψ i (uu t) = algebraMap F (AlgebraicClosure F) ((∏ j, t j ^ a j : Fˣ) : F) := by
    intro i
    refine hM F (AlgebraicClosure F) s ((ψ i : _ →+* AlgebraicClosure F).toMonoidHom.comp uu) S
      (fun a => ψ i (ρ (C a))) (fun t => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, RingHom.coe_coe, huu, hC t, map_sum, map_smul]
  choose a ha using hmono
  have hconj : ∀ i t, ψ i (uu t) * ψ i (lConj σ J (γ : Matrix n n E) F (uu t)) = 1 := by
    intro i t; rw [← map_mul, huu, hnorm, map_one]
  have hlc : tConj3 (plusAlg σ J (γ : Matrix n n E)) σ F = lConj σ J (γ : Matrix n n E) F := rfl
  have hsq : ∀ i, IsField (K i ⊗[F] E) → ∀ t : Fin s → Fˣ,
      ((∏ j, t j ^ a i j : Fˣ) : F) * ((∏ j, t j ^ a i j : Fˣ) : F) = 1 := by
    intro i hi t
    have h0 : ψ i (uu t - algebraMap F _ ((∏ j, t j ^ a i j : Fˣ) : F)) = 0 := by
      rw [map_sub, AlgHom.commutes, ha, sub_self]
    have h1 := hfield i hi _ h0
    rw [hlc, map_sub, AlgHom.commutes, map_sub, AlgHom.commutes, sub_eq_zero] at h1
    have h2 := hconj i t
    rw [ha, h1, ← map_mul] at h2
    exact (algebraMap F (AlgebraicClosure F)).injective (h2.trans (map_one _).symm)
  let M : Matrix {i : Fin k // ¬ IsField (K i ⊗[F] E)} (Fin s) ℤ := Matrix.of fun i j => a i.1 j
  have hfinj : Function.Injective M.mulVecLin := by
    refine (injective_iff_map_eq_zero M.mulVecLin).2 fun w hw => ?_
    have hw' : ∀ i : {i : Fin k // ¬ IsField (K i ⊗[F] E)}, ∑ j, a i.1 j * w j = 0 := by
      intro i
      have := congrFun hw i
      simpa [M, Matrix.mulVec, dotProduct] using this
    let u2 : Fˣ := Units.mk0 2 two_ne_zero
    let t : Fin s → Fˣ := fun j => u2 ^ w j
    have hprod : ∀ i, ((∏ j, t j ^ a i j : Fˣ) : F) = (2:F) ^ (∑ j, a i j * w j) := by
      intro i
      have : (∏ j, t j ^ a i j : Fˣ) = u2 ^ (∑ j, a i j * w j) := by
        rw [zpow_sum_eq]
        refine Finset.prod_congr rfl fun j _ => ?_
        simp only [t]
        rw [← _root_.zpow_mul, mul_comm]
      rw [this, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    have hone : ∀ i, ((∏ j, t j ^ a i j : Fˣ) : F) = 1 := by
      intro i
      by_cases hi : IsField (K i ⊗[F] E)
      · have h := hsq i hi t
        rw [hprod, ← zpow_add₀ (two_ne_zero)] at h
        have h0 := two_zpow_eq_one h
        rw [hprod, show ∑ j, a i j * w j = 0 by omega, zpow_zero]
      · rw [hprod, hw' ⟨i, hi⟩, zpow_zero]
    have hψ1 : ∀ i, ψ i (uu t) = 1 := fun i => by rw [ha, hone, map_one]
    have hψc : ∀ i, ψ i (lConj σ J (γ : Matrix n n E) F (uu t)) = 1 := fun i => by
      have h := hconj i t; rwa [hψ1, one_mul] at h
    have hut : uu t = 1 := by
      have := hsep (uu t - 1) fun i => ⟨by rw [map_sub, hψ1, map_one, sub_self],
        by rw [hlc, map_sub, map_sub, hψc, map_one, map_one, sub_self]⟩
      rwa [sub_eq_zero] at this
    have hhom : A.hom F t = A.hom F 1 := by
      refine Units.ext ?_
      rw [(A.hom F).map_one, Units.val_one, ← hTu t, ← huu, hut,
        map_one]
    have ht1 : t = 1 := A.inj F hhom
    funext j
    have hj := congrFun ht1 j
    have hj' : ((u2 ^ w j : Fˣ) : F) = 1 := by
      have := congrArg Units.val hj
      simpa [t] using this
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0] at hj'
    exact two_zpow_eq_one hj'
  have hle := LinearMap.finrank_le_finrank_of_injective hfinj
  rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card] at hle
  rw [Nat.card_eq_fintype_card]
  exact hle

end GlobalTheory.RegSS.SplitRankBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerSplitRankUpperBoundStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_splitRank_upper_bound : GlobalTheory.RegSS.SubtorusLaurent → GlobalTheory.RegSS.CharacterMonomial → GlobalTheory.RegSS.SeparatingPoints → GlobalTheory.RegSS.SplitRankUpper := by
  first | exact @GlobalTheory.RegSS.SplitRankBound.splitRankUpper | exact GlobalTheory.RegSS.SplitRankBound.splitRankUpper | (intros; apply GlobalTheory.RegSS.SplitRankBound.splitRankUpper <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetRestrictRangeIdempotentMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetRestrictRangeIdempotentMatrix
open GlobalTheory.RegSS

noncomputable section

open Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.RegSS.IdemDet

theorem exists_factor {F m : Type} [Field F] [Fintype m] [DecidableEq m] (p : Matrix m m F)
    (h0 : p ≠ 0) (hp : p * p = p) :
    ∃ (d : ℕ) (A : Matrix m (Fin d) F) (B : Matrix (Fin d) m F), 0 < d ∧ A * B = p ∧ B * A = 1 := by
  let f := Matrix.toLin' p
  let c := Module.finBasis F (LinearMap.range f)
  let e := Pi.basisFun F m
  have hAB : LinearMap.toMatrix c e (LinearMap.range f).subtype *
      LinearMap.toMatrix e c f.rangeRestrict = p := by
    rw [← LinearMap.toMatrix_comp, show (LinearMap.range f).subtype ∘ₗ f.rangeRestrict = f from rfl]
    simp [e, f]
  refine ⟨_, _, _, ?_, hAB, ?_⟩
  · refine Nat.pos_of_ne_zero fun h => h0 ?_
    haveI : IsEmpty (Fin (Module.finrank F (LinearMap.range f))) := by rw [h]; infer_instance
    rw [← hAB]; ext i j; simp [Matrix.mul_apply]
  · rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id c]
    congr 1
    ext ⟨_, v, rfl⟩ : 2
    simp [f, hp]

theorem det_smul_idem {R m : Type} [CommRing R] [Fintype m] [DecidableEq m] {d : ℕ}
    (A : Matrix m (Fin d) R) (B : Matrix (Fin d) m R) (h : B * A = 1) (t : R) :
    (t • (A * B) + 1 - A * B).det = t ^ d := by
  have e : t • (A * B) + 1 - A * B = 1 + ((t - 1) • A) * B := by
    rw [Matrix.smul_mul, sub_smul, one_smul]; abel
  rw [e, Matrix.det_one_add_mul_comm, Matrix.mul_smul, h, sub_smul, one_smul, add_sub_cancel]
  simp

section Rep

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {ι : Type} [Fintype ι] [DecidableEq ι]

def regRep (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R] :
    E ⊗[F] R →ₐ[F] Matrix ι ι R :=
  Algebra.TensorProduct.lift
    ((AlgHom.mapMatrix (Algebra.ofId F R)).comp (Algebra.leftMulMatrix b))
    (IsScalarTower.toAlgHom F R (Matrix ι ι R))
    (fun _ a => (Algebra.commutes a _).symm)

theorem regRep_tmul (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R] (x : E) (t : R) :
    regRep b R (x ⊗ₜ t) = t • (Algebra.leftMulMatrix b x).map (algebraMap F R) := by
  refine (Algebra.TensorProduct.lift_tmul _ _ _ x t).trans ?_
  rw [IsScalarTower.toAlgHom_apply, ← Algebra.commutes, ← Algebra.smul_def]
  rfl

theorem continuous_regRep (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] :
    @Continuous _ _ (Formalism.BasicNotions.tensTopL (F := F) (E := E) R) _ (regRep b R) := by
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  letI := moduleTopology R (E ⊗[F] R)
  haveI : IsModuleTopology R (E ⊗[F] R) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := R) (regRep b R).toRingHom ?_
  have : ⇑((regRep b R).toRingHom.comp (algebraMap R (E ⊗[F] R))) =
      fun t : R => t • (Algebra.leftMulMatrix b 1).map (algebraMap F R) :=
    funext fun t => regRep_tmul b R 1 t
  rw [this]
  fun_prop

variable {n : Type} [Fintype n] [DecidableEq n]

def blockRep (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R] :
    Matrix n n (E ⊗[F] R) →+* Matrix (n × ι) (n × ι) R :=
  (Matrix.compRingEquiv n ι R).toRingHom.comp (regRep b R).toRingHom.mapMatrix

def blockRat (b : Module.Basis ι F E) : Matrix n n E →+* Matrix (n × ι) (n × ι) F :=
  (Matrix.compRingEquiv n ι F).toRingHom.comp (Algebra.leftMulMatrix b).toRingHom.mapMatrix

theorem blockRep_apply (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R]
    (g : Matrix n n (E ⊗[F] R)) (i j : n × ι) :
    blockRep b R g i j = regRep b R (g i.1 j.1) i.2 j.2 := rfl

theorem blockRat_apply (b : Module.Basis ι F E) (g : Matrix n n E) (i j : n × ι) :
    blockRat b g i j = Algebra.leftMulMatrix b (g i.1 j.1) i.2 j.2 := rfl

theorem blockRat_injective (b : Module.Basis ι F E) :
    Function.Injective (blockRat (n := n) b) := by
  intro g h e
  ext i j
  apply Algebra.leftMulMatrix_injective b
  ext k l
  exact congrFun (congrFun e (i, k)) (j, l)

theorem blockRep_map (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R]
    (g : Matrix n n E) :
    blockRep b R (g.map (inclE (F := F) R)) = (blockRat b g).map (algebraMap F R) := by
  ext i j
  rw [blockRep_apply, Matrix.map_apply, Matrix.map_apply, blockRat_apply]
  change regRep b R (g i.1 j.1 ⊗ₜ 1) _ _ = _
  rw [regRep_tmul, one_smul, Matrix.map_apply]

theorem blockRep_smul (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R]
    (t : R) (g : Matrix n n (E ⊗[F] R)) :
    blockRep b R (((1 : E) ⊗ₜ[F] t) • g) = t • blockRep b R g := by
  ext i j
  rw [blockRep_apply, Matrix.smul_apply, Matrix.smul_apply, blockRep_apply, smul_eq_mul, map_mul,
    regRep_tmul, map_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.smul_mul,
    Matrix.one_mul, Matrix.smul_apply]

end Rep

end GlobalTheory.RegSS.IdemDet

namespace GlobalTheory.RegSS

open IdemDet

theorem idempotentDet : IdempotentDet := by
  intro F E _ _ _ _ n _ _ ε h0 hε R _ _ _ _
  letI : TopologicalSpace (E ⊗[F] R) := Formalism.BasicNotions.tensTopL (F := F) (E := E) R
  let b := Module.finBasis F E
  have hq : blockRat b ε * blockRat b ε = blockRat b ε := by rw [← map_mul, hε]
  obtain ⟨d, A, B, hd, hAB, hBA⟩ := exists_factor (blockRat b ε)
    (fun h => h0 (blockRat_injective b (by rw [h, map_zero]))) hq
  set p := blockRep b R (ε.map (inclE (F := F) R)) with hp
  have hpq : p = (blockRat b ε).map (algebraMap F R) := blockRep_map b R ε
  have hpp : p * p = p := by rw [hpq, ← Matrix.map_mul, hq]
  refine ⟨d, fun g => (blockRep b R g * p + 1 - p).det, hd, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : Continuous (blockRep (n := n) b R) := by
      refine continuous_matrix fun i j => ?_
      exact ((continuous_regRep b R).comp (continuous_id.matrix_elem i.1 j.1)).matrix_elem i.2 j.2
    exact (((hc.matrix_mul continuous_const).add continuous_const).sub continuous_const).matrix_det
  · simp
  · intro g h hh
    have hc : blockRep b R h * p = p * blockRep b R h := by
      rw [hp, ← map_mul, ← map_mul, hh]
    have h1 : p * (blockRep b R h * p) = blockRep b R h * p := by
      rw [← mul_assoc, ← hc, mul_assoc, hpp]
    simp only
    rw [← Matrix.det_mul, map_mul]
    congr 1
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_assoc, h1, hpp, mul_one, one_mul]
    abel
  · intro g
    refine ⟨(blockRat b g * blockRat b ε + 1 - blockRat b ε).det, ?_⟩
    simp only
    rw [RingHom.map_det, map_sub, map_add (f := _), map_mul, map_one, blockRep_map, hpq]
    rfl
  · intro g t hg
    have h1 : blockRep b R g * p = t • p := by
      rw [hp, ← map_mul, hg, blockRep_smul]
    simp only
    rw [h1, hpq, ← hAB, Matrix.map_mul]
    refine det_smul_idem _ _ ?_ t
    rw [← Matrix.map_mul, hBA, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.RegSS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetRestrictRangeIdempotentMatrixStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_restrict_range_idempotent_matrix : GlobalTheory.RegSS.IdempotentDet := by
  first | exact @GlobalTheory.RegSS.idempotentDet | exact GlobalTheory.RegSS.idempotentDet | (intros; apply GlobalTheory.RegSS.idempotentDet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupCommutantScalars
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupCommutantScalars
noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms

namespace GlobalTheory.RegSS.UComm

variable {A : Type} [Field A] {n : Type} [Fintype n] [DecidableEq n]

theorem hform_add_left (σ : A →+* A) (J : Matrix n n A) (x y z : n → A) :
    hform σ J (x + y) z = hform σ J x z + hform σ J y z := by
  simp only [hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_add_right (σ : A →+* A) (J : Matrix n n A) (x y z : n → A) :
    hform σ J x (y + z) = hform σ J x y + hform σ J x z := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_left (σ : A →+* A) (J : Matrix n n A) (c : A) (x y : n → A) :
    hform σ J (c • x) y = σ c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_smul_right (σ : A →+* A) (J : Matrix n n A) (c : A) (x y : n → A) :
    hform σ J x (c • y) = c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem herm_apply (σ : A →+* A) {J : Matrix n n A} (hH : IsHerm σ J) (i j : n) :
    σ (J j i) = J i j := by
  have := congrFun (congrFun hH i) j
  simpa [cT] using this

theorem sigma_hform (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {J : Matrix n n A} (hH : IsHerm σ J)
    (x y : n → A) : σ (hform σ J x y) = hform σ J y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [herm_apply σ hH]; ring

def rowv (σ : A →+* A) (J : Matrix n n A) (v : n → A) : n → A := (fun i => σ (v i)) ᵥ* J

theorem rowv_dot (σ : A →+* A) (J : Matrix n n A) (v x : n → A) :
    rowv σ J v ⬝ᵥ x = hform σ J v x := by
  rw [hform_eq, rowv, dotProduct_mulVec]

def proj (σ : A →+* A) (J : Matrix n n A) (v : n → A) : Matrix n n A := vecMulVec v (rowv σ J v)

theorem proj_mul_proj (σ : A →+* A) (J : Matrix n n A) (v : n → A) :
    proj σ J v * proj σ J v = hform σ J v v • proj σ J v := by
  rw [proj, vecMulVec_mul_vecMulVec, rowv_dot]
  ext i j; simp [vecMulVec_apply, mul_left_comm]

theorem proj_mulVec (σ : A →+* A) (J : Matrix n n A) (v x : n → A) :
    proj σ J v *ᵥ x = hform σ J v x • v := by
  rw [proj, vecMulVec_mulVec, rowv_dot, op_smul_eq_smul]

theorem cT_proj (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {J : Matrix n n A} (hH : IsHerm σ J)
    (v : n → A) : cT σ (proj σ J v) = vecMulVec (J *ᵥ v) (fun i => σ (v i)) := by
  ext i k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cT, proj, rowv, transpose_apply, map_apply, vecMulVec_apply, vecMul, dotProduct,
    mulVec, map_mul, map_sum, hσ, herm_apply σ hH]
  rw [mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem cT_proj_mul (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {J : Matrix n n A} (hH : IsHerm σ J)
    (v : n → A) : cT σ (proj σ J v) * J = J * proj σ J v := by
  rw [cT_proj σ hσ hH, vecMulVec_mul, proj, mul_vecMulVec]; rfl

def refl (σ : A →+* A) (J : Matrix n n A) (v : n → A) : Matrix n n A :=
  1 + (-(2 / hform σ J v v)) • proj σ J v

theorem refl_mul_self (σ : A →+* A) (J : Matrix n n A) (v : n → A) (hv : hform σ J v v ≠ 0) :
    refl σ J v * refl σ J v = 1 := by
  set q := hform σ J v v
  have hP := proj_mul_proj σ J v
  have hc : -(2 / q) + -(2 / q) + -(2 / q) * -(2 / q) * q = 0 := by field_simp; ring
  simp only [refl, add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hP, smul_smul]
  rw [add_assoc, ← add_assoc ((-(2 / q)) • proj σ J v), ← add_smul, ← add_smul, hc, zero_smul,
    add_zero]

theorem refl_unitary (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {J : Matrix n n A} (hH : IsHerm σ J)
    (v : n → A) (hv : hform σ J v v ≠ 0) :
    cT σ (refl σ J v) * J * refl σ J v = J := by
  have hq : σ (hform σ J v v) = hform σ J v v := sigma_hform σ hσ hH v v
  have hc : σ (-(2 / hform σ J v v)) = -(2 / hform σ J v v) := by
    rw [map_neg, map_div₀, hq, map_ofNat]
  have h1 : cT σ (refl σ J v) * J = J * refl σ J v := by
    rw [refl, cT_add, cT_smul, Formalism.UG.cT_one, hc, add_mul, Matrix.one_mul, Matrix.smul_mul,
      cT_proj_mul σ hσ hH, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  rw [h1, Matrix.mul_assoc, refl_mul_self σ J v hv, Matrix.mul_one]

theorem eigen [CharZero A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {J : Matrix n n A} (hH : IsHerm σ J)
    (a : Matrix n n A) (hcomm : ∀ g ∈ UJ σ J, (g : Matrix n n A) * a = a * (g : Matrix n n A))
    (v : n → A) (hv : hform σ J v v ≠ 0) : ∃ μ : A, a *ᵥ v = μ • v := by
  let g : GL n A := ⟨refl σ J v, refl σ J v, refl_mul_self σ J v hv, refl_mul_self σ J v hv⟩
  have hg : g ∈ UJ σ J := refl_unitary σ hσ hH v hv
  have h1 : refl σ J v * a = a * refl σ J v := hcomm g hg
  have hc : -(2 / hform σ J v v) ≠ 0 := neg_ne_zero.2 (div_ne_zero two_ne_zero hv)
  have h2 : proj σ J v * a = a * proj σ J v := by
    simp only [refl, add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul] at h1
    exact smul_right_injective _ hc (add_left_cancel h1)
  have h3 := congrArg (· *ᵥ v) h2
  simp only [← mulVec_mulVec, proj_mulVec, mulVec_smul] at h3
  refine ⟨(hform σ J v v)⁻¹ * hform σ J v (a *ᵥ v), ?_⟩
  rw [mul_smul, h3, smul_smul, inv_mul_cancel₀ hv, one_smul]

theorem exists_nonisotropic (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) [CharZero A] {J : Matrix n n A}
    (hH : IsHerm σ J) (hJ : IsUnit J.det) (hn : Nonempty n) : ∃ w, hform σ J w w ≠ 0 := by
  by_contra hall
  push_neg at hall
  obtain ⟨i⟩ := hn
  set x : n → A := Pi.single i 1
  set y : n → A := J⁻¹ *ᵥ Pi.single i 1
  have hsx : (fun k => σ (x k)) = x := by
    funext k; by_cases hk : k = i
    · subst hk; simp [x]
    · simp [x, hk]
  have hxy : hform σ J x y = 1 := by
    rw [hform_eq, hsx, mulVec_mulVec, mul_nonsing_inv _ hJ, one_mulVec]
    simp [x]
  have hyx : hform σ J y x = 1 := by rw [← sigma_hform σ hσ hH, hxy, map_one]
  have h := hall (x + y)
  rw [hform_add_left, hform_add_right, hform_add_right, hall x, hall y, hxy, hyx] at h
  norm_num at h

theorem comb (M : Matrix n n A) (v w : n → A) (hw : w ≠ 0) (l μ μ' c c' : A) (hc : c ≠ c')
    (h1 : M *ᵥ w = l • w) (h2 : M *ᵥ (v + c • w) = μ • (v + c • w))
    (h3 : M *ᵥ (v + c' • w) = μ' • (v + c' • w)) : M *ᵥ v = l • v := by
  rw [mulVec_add, mulVec_smul, h1] at h2 h3
  by_cases hμ : μ = μ'
  · subst hμ
    have h4 : (c - c') • ((l - μ) • w) = 0 := by linear_combination (norm := module) h2 - h3
    rcases smul_eq_zero.1 h4 with h | h
    · exact absurd (sub_eq_zero.1 h) hc
    rcases smul_eq_zero.1 h with h | h
    · have hl : l = μ := sub_eq_zero.1 h
      subst hl
      linear_combination (norm := module) h2
    · exact absurd h hw
  · have h5 : (μ - μ') • v = (c • l - c' • l - μ * c + μ' * c') • w := by
      linear_combination (norm := module) h3 - h2
    have hv : v = ((μ - μ')⁻¹ * (c • l - c' • l - μ * c + μ' * c')) • w := by
      rw [← smul_smul, ← h5, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hμ), one_smul]
    rw [hv, mulVec_smul, h1, smul_comm]

theorem quad [CharZero A] (α β γ : A) (hα : α ≠ 0) : ∃ c c' : A, c ≠ c' ∧
    (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) ∧ (c' = 0 ∨ c' = 1 ∨ c' = 2 ∨ c' = 3) ∧
    γ + c * β + c * c * α ≠ 0 ∧ γ + c' * β + c' * c' * α ≠ 0 := by
  by_cases h0 : γ + 0 * β + 0 * 0 * α = 0 <;> by_cases h1 : γ + 1 * β + 1 * 1 * α = 0 <;>
    by_cases h2 : γ + 2 * β + 2 * 2 * α = 0 <;> by_cases h3 : γ + 3 * β + 3 * 3 * α = 0
  all_goals first
    | exact absurd (show α = 0 by linear_combination (1/2 : A) * h0 - h1 + (1/2 : A) * h2) hα
    | exact absurd (show α = 0 by linear_combination (1/2 : A) * h1 - h2 + (1/2 : A) * h3) hα
    | exact absurd (show α = 0 by linear_combination (1/3 : A) * h0 - (1/2 : A) * h1 + (1/6 : A) * h3) hα
    | exact absurd (show α = 0 by linear_combination (1/6 : A) * h0 - (1/2 : A) * h2 + (1/3 : A) * h3) hα
    | exact ⟨0, 1, by norm_num, by norm_num, by norm_num, h0, h1⟩
    | exact ⟨0, 2, by norm_num, by norm_num, by norm_num, h0, h2⟩
    | exact ⟨0, 3, by norm_num, by norm_num, by norm_num, h0, h3⟩
    | exact ⟨1, 2, by norm_num, by norm_num, by norm_num, h1, h2⟩
    | exact ⟨1, 3, by norm_num, by norm_num, by norm_num, h1, h3⟩
    | exact ⟨2, 3, by norm_num, by norm_num, by norm_num, h2, h3⟩

end GlobalTheory.RegSS.UComm

namespace GlobalTheory.RegSS

open UComm in
theorem unitaryCommutant : UnitaryCommutant := by
  intro A _ _ hA σ hσ n _ _ J hH hJ a hcomm
  letI := hA.toField
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨0, by ext i; exact isEmptyElim i⟩
  obtain ⟨w, hw⟩ := exists_nonisotropic σ hσ hH hJ hn
  obtain ⟨l, hl⟩ := eigen σ hσ hH a hcomm w hw
  have hw0 : w ≠ 0 := by rintro rfl; simp [hform] at hw
  have hall : ∀ v, a *ᵥ v = l • v := by
    intro v
    have hexp : ∀ c : A, σ c = c → hform σ J (v + c • w) (v + c • w) =
        hform σ J v v + c * (hform σ J v w + hform σ J w v) + c * c * hform σ J w w := by
      intro c hc
      rw [hform_add_left, hform_add_right, hform_add_right, hform_smul_left, hform_smul_left,
        hform_smul_right, hform_smul_right, hc]
      ring
    have hfix : ∀ c : A, (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) → σ c = c := by
      rintro c (rfl | rfl | rfl | rfl) <;> simp [map_ofNat]
    obtain ⟨c, c', hcc, hc, hc', h1, h2⟩ :=
      quad (hform σ J w w) (hform σ J v w + hform σ J w v) (hform σ J v v) hw
    rw [← hexp c (hfix c hc)] at h1
    rw [← hexp c' (hfix c' hc')] at h2
    obtain ⟨μ, hμ⟩ := eigen σ hσ hH a hcomm _ h1
    obtain ⟨μ', hμ'⟩ := eigen σ hσ hH a hcomm _ h2
    exact comb a v w hw0 l μ μ' c c' hcc hl hμ hμ'
  refine ⟨l, ?_⟩
  ext i j
  have := congrFun (hall (Pi.single j 1)) i
  rw [mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

end GlobalTheory.RegSS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupCommutantScalarsStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_commutant_scalars : GlobalTheory.RegSS.UnitaryCommutant := by
  first | exact @GlobalTheory.RegSS.unitaryCommutant | exact GlobalTheory.RegSS.unitaryCommutant | (intros; apply GlobalTheory.RegSS.unitaryCommutant <;> assumption)
end
end
