module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenLevelInner

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstitutionMaximalMinorProductEqSumCauchyBinet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstitutionMaximalMinorProductEqSumCauchyBinet
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormDict

theorem substF_minorPol_eq_sum : ∀ (D : D7) {a d : ℕ} {m : D.what₂.Tau → ℕ} (K : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ)
    (T : Tup D a d m), GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) (minorPol D T) =
      ∑ T' : Tup D a d m, (∏ τ, ∏ r, (Matrix.of fun i i' : Fin a => K τ ((T' τ r).1 i') ((T τ r).1 i)).det) •
        minorPol D T' := by
  intro D a d m K T
  have hmin : ∀ τ (s : Fin a → Fin d), GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ))
      (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).det =
      ∑ s' : {s : Fin a → Fin d // StrictMono s},
        MvPolynomial.C ((Matrix.of fun i i' : Fin a => K τ (s'.1 i') (s i)).det) *
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s'.1 i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).det := by
    intro τ s
    rw [AlgHom.map_det]
    have hM : (GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ))).mapMatrix
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) =
        (Matrix.of fun (i : Fin a) (k : Fin d) => (MvPolynomial.C (K τ k (s i)) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) *
        (Matrix.of fun (k : Fin d) (i' : Fin a) => (MvPolynomial.X (τ, k, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) := by
      refine Matrix.ext fun i i' => ?_
      simp only [RingHom.mapMatrix_apply, AlgHom.coe_toRingHom, Matrix.map_apply, Matrix.of_apply,
        GlobalTheory.CompactHowe.substF_X, Matrix.mul_apply, Matrix.one_apply]
      rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, GlobalTheory.CompactHowe.substF_X]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single i']
      · simp
      · intro l _ hl; simp [Matrix.one_apply_ne hl]
      · simp
    rw [hM, GlobalTheory.MinorFrame.det_mul_eq_sum_sm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    congr 1
    rw [show (Matrix.of fun (i : Fin a) (k : Fin d) =>
        (MvPolynomial.C (K τ k (s i)) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).submatrix id s'.1 =
        (MvPolynomial.C : ℂ →+* MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ).mapMatrix
          (Matrix.of fun i i' : Fin a => K τ (s'.1 i') (s i)) from by ext; simp]
    rw [← RingHom.map_det]
  unfold minorPol
  simp only [map_prod, hmin]
  rw [Finset.prod_congr rfl fun τ _ => Fintype.prod_sum _, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun T' _ => ?_
  rw [← MvPolynomial.C_mul']
  simp only [Finset.prod_mul_distrib, map_prod]

end GlobalTheory.NormDict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstitutionMaximalMinorProductEqSumCauchyBinetStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.substitution_maximalMinorProduct_eq_sum_cauchyBinet : ∀ (D : D7) {a d : ℕ} {m : D.what₂.Tau → ℕ} (K : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) (T : Tup D a d m), GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) (minorPol D T) = ∑ T' : Tup D a d m, (∏ τ, ∏ r, (Matrix.of fun i i' : Fin a => K τ ((T' τ r).1 i') ((T τ r).1 i)).det) • minorPol D T' := by
  first | exact @GlobalTheory.NormDict.substF_minorPol_eq_sum | exact GlobalTheory.NormDict.substF_minorPol_eq_sum | (intros; apply GlobalTheory.NormDict.substF_minorPol_eq_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalMinorsMatrixMemUnitaryGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalMinorsMatrixMemUnitaryGroup
open Matrix
open scoped Classical

namespace GlobalTheory

noncomputable def strictMonoEquivPowersetCard (a : ℕ) (n : Type*) [LinearOrder n] :
    {s : Fin a → n // StrictMono s} ≃ Set.powersetCard n a :=
  ({ toFun := fun s => OrderEmbedding.ofStrictMono s.1 s.2
     invFun := fun f => ⟨f, f.strictMono⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => by ext; rfl } : {s : Fin a → n // StrictMono s} ≃ (Fin a ↪o n)).trans
    Set.powersetCard.ofFinEmbEquiv

theorem subsetEnum_strictMonoEquivPowersetCard (a : ℕ) {n : Type*} [LinearOrder n]
    (s : {s : Fin a → n // StrictMono s}) :
    subsetEnum (strictMonoEquivPowersetCard a n s) = s.1 := by
  have h : Set.powersetCard.ofFinEmbEquiv.symm (strictMonoEquivPowersetCard a n s) =
      OrderEmbedding.ofStrictMono s.1 s.2 := Equiv.symm_apply_apply _ _
  exact congrArg (fun f : Fin a ↪o n => (f : Fin a → n)) h

theorem minorsMatrix_mem_unitaryGroup : ∀ {N a : ℕ} (M : Matrix (Fin N) (Fin N) ℂ),
    M ∈ Matrix.unitaryGroup (Fin N) ℂ →
    (Matrix.of fun s s' : {s : Fin a → Fin N // StrictMono s} =>
      (Matrix.of fun i i' : Fin a => M (s'.1 i') (s.1 i)).det) ∈
      Matrix.unitaryGroup {s : Fin a → Fin N // StrictMono s} ℂ := by
  intro N a M hM
  set e := strictMonoEquivPowersetCard a (Fin N)
  have hC : (Matrix.of fun s s' : {s : Fin a → Fin N // StrictMono s} =>
      (Matrix.of fun i i' : Fin a => M (s'.1 i') (s.1 i)).det) =
      (compoundMatrix a Mᵀ).submatrix e e := by
    ext s s'
    have he : ∀ s, subsetEnum (e s) = s.1 := subsetEnum_strictMonoEquivPowersetCard a
    simp only [submatrix_apply, compoundMatrix, of_apply, he]
    rfl
  have hT : Mᵀ * (Mᵀ)ᴴ = 1 := by
    rw [mem_unitaryGroup_iff'] at hM
    have h1 : Mᵀ * (Mᵀ)ᴴ = (star M * M)ᵀ := by
      ext i j
      simp [Matrix.mul_apply, mul_comm]
    rw [h1, hM, transpose_one]
  rw [hC, mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_submatrix,
    submatrix_mul_equiv, ← compoundMatrix_conjTranspose, ← compoundMatrix_mul, hT,
    compoundMatrix_one, submatrix_one_equiv]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalMinorsMatrixMemUnitaryGroupStatement
open Matrix
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalMinorsMatrix_mem_unitaryGroup : ∀ {N a : ℕ} (M : Matrix (Fin N) (Fin N) ℂ), M ∈ Matrix.unitaryGroup (Fin N) ℂ → (Matrix.of fun s s' : {s : Fin a → Fin N // StrictMono s} => (Matrix.of fun i i' : Fin a => M (s'.1 i') (s.1 i)).det) ∈ Matrix.unitaryGroup {s : Fin a → Fin N // StrictMono s} ℂ := by
  first | exact @GlobalTheory.minorsMatrix_mem_unitaryGroup | exact GlobalTheory.minorsMatrix_mem_unitaryGroup | (intros; apply GlobalTheory.minorsMatrix_mem_unitaryGroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTensorPlacesSlots
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTensorPlacesSlots
open Matrix
open scoped Classical

namespace GlobalTheory

theorem pi_prod_rows_orthonormal {K : Type} [Fintype K] [DecidableEq K] {κ : K → Type}
    [∀ k, Fintype (κ k)] [∀ k, DecidableEq (κ k)] [DecidableEq (∀ k, κ k)]
    (A : ∀ k, Matrix (κ k) (κ k) ℂ)
    (hA : ∀ k a b, ∑ y, A k a y * star (A k b y) = if a = b then 1 else 0)
    (T T'' : ∀ k, κ k) :
    ∑ x : ∀ k, κ k, (∏ k, A k (T k) (x k)) * star (∏ k, A k (T'' k) (x k)) =
      if T = T'' then 1 else 0 := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k y => A k (T k) y * star (A k (T'' k) y))]
  rw [Finset.prod_congr rfl (fun k _ => hA k (T k) (T'' k)), Finset.prod_boole]
  by_cases hT : T = T''
  · subst hT; simp
  · rw [if_neg hT, if_neg]
    intro hall
    exact hT (funext fun k => hall k (Finset.mem_univ k))

theorem unitary_tensor_places_positions : ∀ (J ι : Type) [Fintype J] [DecidableEq J] [Fintype ι]
    [DecidableEq ι] (n : J → ℕ) (C : J → Matrix ι ι ℂ), (∀ j, C j ∈ Matrix.unitaryGroup ι ℂ) →
    (Matrix.of fun T T' : (∀ j, Fin (n j) → ι) => ∏ j, ∏ r, C j (T j r) (T' j r)) ∈
      Matrix.unitaryGroup (∀ j, Fin (n j) → ι) ℂ := by
  intro J ι _ _ _ _ n C hC
  have hC' : ∀ j (a b : ι), ∑ y, C j a y * star (C j b y) = if a = b then 1 else 0 := by
    intro j a b
    have := congrFun (congrFun ((mem_unitaryGroup_iff).1 (hC j)) a) b
    simpa only [Matrix.mul_apply, star_apply, Matrix.one_apply] using this
  have hD : ∀ j (S S'' : Fin (n j) → ι),
      ∑ y : Fin (n j) → ι, (∏ r, C j (S r) (y r)) * star (∏ r, C j (S'' r) (y r)) =
        if S = S'' then 1 else 0 := fun j =>
    pi_prod_rows_orthonormal (κ := fun _ => ι) (fun _ => C j) (fun _ => hC' j)
  have key := pi_prod_rows_orthonormal (κ := fun j => Fin (n j) → ι)
    (fun j => of fun S S' : Fin (n j) → ι => ∏ r, C j (S r) (S' r))
    (fun j a b => by simpa only [of_apply] using hD j a b)
  rw [mem_unitaryGroup_iff]
  ext T T''
  simpa only [Matrix.mul_apply, star_apply, of_apply, Matrix.one_apply] using key T T''

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTensorPlacesSlotsStatement
open Matrix
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_unitary_mem_unitaryGroup_pi : ∀ (J ι : Type) [Fintype J] [DecidableEq J] [Fintype ι] [DecidableEq ι] (n : J → ℕ) (C : J → Matrix ι ι ℂ), (∀ j, C j ∈ Matrix.unitaryGroup ι ℂ) → (Matrix.of fun T T' : (∀ j, Fin (n j) → ι) => ∏ j, ∏ r, C j (T j r) (T' j r)) ∈ Matrix.unitaryGroup (∀ j, Fin (n j) → ι) ℂ := by
  first | exact @GlobalTheory.unitary_tensor_places_positions | exact GlobalTheory.unitary_tensor_places_positions | (intros; apply GlobalTheory.unitary_tensor_places_positions <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsMixMaximalMinorFockVectorsUnitary
open NumberField MeasureTheory
open scoped Classical ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.NormDict.RealB.subst_minorPol_unitary : ∀ (D : D7) {a d N n : ℕ} {m : D.what₂.Tau → ℕ} (hN : N = d) (hn : n = a) (K : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ), (∀ τ, K τ ∈ Matrix.unitaryGroup (Fin N) ℂ) → ∃ U : Matrix (Tup D a d m) (Tup D a d m) ℂ, U ∈ Matrix.unitaryGroup (Tup D a d m) ℂ ∧ ∀ T : Tup D a d m, GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D a d => ((k.1, Fin.cast hN.symm k.2.1, Fin.cast hn.symm k.2.2) : D.what₂.Tau × Fin N × Fin n)) (minorPol D T)) = ∑ T', U T T' • MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D a d => ((k.1, Fin.cast hN.symm k.2.1, Fin.cast hn.symm k.2.2) : D.what₂.Tau × Fin N × Fin n)) (minorPol D T') := by
  intro D a d N n m hN hn K hK
  subst hN hn
  have hr : (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D n N => ((k.1, Fin.cast rfl k.2.1, Fin.cast rfl k.2.2) : D.what₂.Tau × Fin N × Fin n)) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D n N) ℂ →ₐ[ℂ] _) = AlgHom.id ℂ _ := by
    simp only [Fin.cast_eq_self, Prod.mk.eta]
    exact MvPolynomial.rename_id
  simp only [hr, AlgHom.id_apply]
  exact ⟨_, GlobalTheory.T.prod_unitary_mem_unitaryGroup_pi D.what₂.Tau {s : Fin n → Fin N // StrictMono s} m _ fun τ => GlobalTheory.T.maximalMinorsMatrix_mem_unitaryGroup (a := n) (K τ) (hK τ),
    fun T => by rw [GlobalTheory.T.substitution_maximalMinorProduct_eq_sum_cauchyBinet D K T]; rfl⟩

namespace GlobalTheory.NormDict.RealB

theorem real_mix : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
    ∀ k ∈ GinfC X.B, ∃ U : Matrix (Tup D P.a P.d P.n) (Tup D P.a P.d P.n) ℂ, U ∈ Matrix.unitaryGroup (Tup D P.a P.d P.n) ℂ ∧
      ∀ T, X.om (1, k) (X.fock T) = ∑ T', U T T' • X.fock T' := by
  intro D cc δ t0 Q P X hX k hk
  have hF := hX.1
  have hW := hX.2.weil
  have hθ := hX.2.inf
  let K : D.what₂.Tau → Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ := fun τ => compAt X.θ τ (Formalism.L2.Theta.mt X.B k)
  have hKu : ∀ τ, K τ ∈ Matrix.unitaryGroup (Fin X.B.rank) ℂ := fun τ => GlobalTheory.RealColAct.compAt_mem_unitary hθ hF.gramB k τ
  obtain ⟨U₀, hU₀, hsub⟩ := GlobalTheory.NormDict.RealB.subst_minorPol_unitary D (m := P.n) X.rkB X.rkA K hKu
  have c1 : ∀ (V : HSp D) τ, compAt X.θ τ (Formalism.L2.Theta.mt V 1) = 1 := fun V τ =>
    Matrix.map_one (f := (X.θ τ).comp (infPart D)) (map_zero _) (map_one _)
  have gr1 : ∀ (V : HSp D), V.gram = 1 → ∀ τ, gramAt D V τ = 1 := fun V h τ => by
    rw [gramAt, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have cart : ∀ (V : HSp D), V.gram = 1 → ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun V h τ => by
    rw [gr1 V h]; exact ⟨Matrix.mul_one _, by simp, by rw [Matrix.mul_one]; exact Matrix.PosDef.one⟩
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_unramifiedHeckeChar_halfExponent_restrict_quadratic D
  obtain ⟨x, hx, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ X.A (fun τ => by rw [gr1 _ hF.gramA]; simp) 1 (one_mem _)
  obtain ⟨y, hy, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ X.B (fun τ => by rw [gr1 _ hF.gramB]; simp) k hk
  have hvac := GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D X.ψ hW.std X.A X.B X.θ hθ X.χA X.χB X.om η ⟨e1, e4, e3, e2⟩ hW (fun _ => 1) (fun _ => 1)
    (cart _ hF.gramA) (cart _ hF.gramB) 1 (one_mem _) k hk (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) x y hx hy X.vac hX.2.vac_theta hX.2.vac_fock
  obtain ⟨c, hc1, hcv⟩ : ∃ c : ℂ, ‖c‖ = 1 ∧ X.om (1, k) X.vac = c • X.vac := by
    refine ⟨_, ?_, hvac⟩
    rw [norm_mul, Circle.norm_coe, one_mul, norm_prod]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [GlobalTheory.KJReal.detPlus_one_one, inv_one, c1, Matrix.det_one, one_pow, mul_one, norm_pow]
    have hd := Matrix.det_of_mem_unitary (hKu τ)
    rw [show ‖(compAt X.θ τ (Formalism.L2.Theta.mt X.B k)).det‖ = 1 from CStarRing.norm_of_mem_unitary hd, one_pow]
  refine ⟨c • U₀, ?_, fun T => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff] at hU₀ ⊢
    rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, hU₀, smul_smul, RCLike.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hc1]
    simp
  · have e2 := (GlobalTheory.OrientedHeis.om_pureTensorO D X.ψ X.θ X.A X.B X.χA X.χB X.om hW hθ (fun _ => 1) (fun _ => 1)
      (fun _ => 1) (fun _ => 1 * 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun τ => 1 * K τ) 1 k
      (fun τ => by rw [c1, Matrix.one_mul]) (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [c1, Matrix.one_mul]) (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) X.vac hX.2.vac_theta
      (MvPolynomial.rename X.var (minorPol D T))).2
    have e3 := GlobalTheory.T.fockPolynomialVector_basisChange_eq_substitution D X.ψ X.θ X.A X.B hW.std hθ (fun _ => 1) (fun _ => 1) (fun _ => 1) K X.vac hX.2.vac_theta
      (MvPolynomial.rename X.var (minorPol D T))
    have e4 := hsub T
    simp only [inv_one, Matrix.transpose_one] at e3
    change X.om (1, k) (pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac _) = _
    rw [e2, hcv, GlobalTheory.FiniteFock.pureTensorO_smul, e3]
    change c • (pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac) (GlobalTheory.CompactHowe.substF K (fun _ => 1) (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D P.a P.d => ((k.1, Fin.cast X.rkB.symm k.2.1, Fin.cast X.rkA.symm k.2.2) : D.what₂.Tau × Fin X.B.rank × Fin X.A.rank)) (minorPol D T))) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e4, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun T' _ => ?_
    rw [map_smul, smul_smul, Matrix.smul_apply, smul_eq_mul]
    rfl

end GlobalTheory.NormDict.RealB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsMixMaximalMinorFockVectorsUnitaryStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoints_mix_maximalMinorFockVectors_unitary : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  ∀ k ∈ GinfC X.B, ∃ U : Matrix (Tup D P.a P.d P.n) (Tup D P.a P.d P.n) ℂ, U ∈ Matrix.unitaryGroup (Tup D P.a P.d P.n) ℂ ∧
    ∀ T, X.om (1, k) (X.fock T) = ∑ T', U T T' • X.fock T' := by
  first | exact @GlobalTheory.NormDict.RealB.real_mix | exact GlobalTheory.NormDict.RealB.real_mix | (intros; apply GlobalTheory.NormDict.RealB.real_mix <;> assumption)
end
