module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundIpow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularLatticeFundamentalSetVolume
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularLatticeFundamentalSetVolume
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical nonZeroDivisors

noncomputable section
namespace GlobalTheory.UnimodCov
open GlobalTheory.HomCovolume
attribute [local instance] GlobalTheory.HomCovolume.haar_two

theorem star_mem_one {K : Type} [Field K] [NumberField K] [StarRing K] {a : K}
    (ha : a ∈ (1 : Submodule (𝓞 K) K)) : star a ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 ha
  refine Submodule.mem_one.2 ⟨⟨star (algebraMap (𝓞 K) K r), ?_⟩, rfl⟩
  exact (mem_integralClosure_iff ℤ K).2 ((RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom)

theorem mem_one_iff' {K : Type} [Field K] [NumberField K] (x : K) :
    x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔ x ∈ (1 : Submodule (𝓞 K) K) := by
  rw [FractionalIdeal.mem_one_iff, Submodule.mem_one]

theorem det_Hb (k : ℕ) : (Hb k).det = -1 := by
  rw [Hb, det_diagonal, Fin.prod_univ_castSucc]
  simp [Fin.castSucc_ne_last]

theorem exists_pseudo (K W : Type) [Field K] [NumberField K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (m : ℕ) (hm : Module.finrank K W = m) (L : Submodule (𝓞 K) W)
    (hL : L.FG ∧ Submodule.span K (L : Set W) = ⊤) :
    ∃ (e : Module.Basis (Fin m) K W) (c : Fin m → FractionalIdeal (𝓞 K)⁰ K), (∀ i, c i ≠ 0) ∧
      ∀ x, x ∈ L ↔ ∀ i, e.repr x i ∈ c i := by
  obtain ⟨-, f, c, hf, hc, hΛ, -⟩ :=
    GlobalTheory.exists_pseudoCoords (R := 𝓞 K) (K := K) m W hm L ⊥ hL.1 hL.2
  have hinj : Function.Injective (LinearMap.pi f) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact hf v fun a => congrFun hv a
  have hsurj : Function.Surjective (LinearMap.pi f) := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hm])]
    exact hinj
  let φ : W ≃ₗ[K] (Fin m → K) := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine ⟨Module.Basis.ofEquivFun φ, c, hc, fun x => ?_⟩
  rw [hΛ]
  simp only [Module.Basis.ofEquivFun_repr_apply]
  rfl

theorem mem_smul_iff {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] {m : ℕ} (L : Submodule (𝓞 K) W) (e : Module.Basis (Fin m) K W)
    (c : Fin m → FractionalIdeal (𝓞 K)⁰ K) (hL : ∀ x, x ∈ L ↔ ∀ i, e.repr x i ∈ c i)
    (I : FractionalIdeal (𝓞 K)⁰ K) (x : W) :
    x ∈ (I : Submodule (𝓞 K) K) • L ↔ ∀ i, e.repr x i ∈ I * c i := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun x y hx hy => ?_)
    · intro i
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact FractionalIdeal.mul_mem_mul hr ((hL y).1 hy i)
    · intro i
      rw [map_add (f := _), Finsupp.add_apply]
      exact Submodule.add_mem _ (hx i) (hy i)
  · intro hx
    rw [← e.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    refine FractionalIdeal.mul_induction_on (hx i) (fun r hr s hs => ?_) (fun t u ht hu => ?_)
    · rw [mul_smul]
      refine Submodule.smul_mem_smul hr ((hL _).2 fun j => ?_)
      rw [map_smul, e.repr_self, Finsupp.smul_apply, smul_eq_mul]
      by_cases hj : i = j
      · subst hj; simpa using hs
      · rw [Finsupp.single_apply, if_neg hj, mul_zero]; exact FractionalIdeal.zero_mem _
    · rw [add_smul]; exact Submodule.add_mem _ ht hu

theorem exists_coordLat (K : Type) [Field K] [NumberField K] (hK : IsTotallyComplex K) (ι : Type) [Fintype ι]
    (σ : ι → (K →+* ℂ)) (hσ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (σ v) = w) (m : ℕ)
    (a : Fin m → FractionalIdeal (𝓞 K)⁰ K) (ha : ∀ i, a i ≠ 0)
    (A : ι → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ v, (A v).det ≠ 0) :
    ∃ Λ : Submodule ℤ (ι → Fin m → ℂ),
      (∀ z, z ∈ Λ ↔ ∃ y : Fin m → K, (∀ i, y i ∈ a i) ∧ ∀ v, z v = A v *ᵥ fun i => σ v (y i)) ∧
      HasCov volume Λ ((∏ i, (FractionalIdeal.absNorm (a i) : ℝ) * Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι) *
        ∏ v, ‖(A v).det‖ ^ 2) := by
  choose L hL hcov using fun i => GlobalTheory.IdealFund.exists_lat K hK ι σ hσ (a i) (ha i)
  let e₀ : (ι → Fin m → ℂ) ≃ₗ[ℝ] (Fin m → ι → ℂ) :=
    { toFun := fun z i v => z v i, invFun := fun z v i => z i v, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hmp : MeasurePreserving e₀.toContinuousLinearEquiv volume volume := by
    refine measurePreserving_of_ball _ _ _ (fun x => ?_) ?_
    · simp only [pi_norm_le_iff_of_nonneg zero_le_one]
      exact forall_comm
    · simp [volume_pi_closedBall _ zero_le_one, ← pow_mul, mul_comm]
  have hΛ0 := HasCov.of_measurePreserving (L := ZLattice.comap ℝ (Submodule.pi Set.univ L)
    e₀.toContinuousLinearEquiv.toLinearMap) _ hmp (fun _ => Iff.rfl) (HasCov.pi hcov)
  let f : (ι → Fin m → ℂ) →ₗ[ℝ] (ι → Fin m → ℂ) :=
    LinearMap.pi fun v => ((Matrix.toLin' (A v)⁻¹).restrictScalars ℝ).comp (LinearMap.proj v)
  have hf : ∀ z v, f z v = (A v)⁻¹ *ᵥ z v := fun _ _ => rfl
  have hdet : LinearMap.det f = (∏ v, ‖(A v).det‖ ^ 2)⁻¹ := by
    rw [LinearMap.det_pi, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [det_real_mulVec, det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, inv_pow]
  have hpos : 0 < ∏ v, ‖(A v).det‖ ^ 2 := Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 (hA v)) _
  let Λ : Submodule ℤ (ι → Fin m → ℂ) :=
    (ZLattice.comap ℝ (Submodule.pi Set.univ L) e₀.toContinuousLinearEquiv.toLinearMap).comap (f.restrictScalars ℤ)
  have h := HasCov.of_det f (L := Λ) (by rw [hdet]; exact (inv_pos.2 hpos).ne') (fun _ => Iff.rfl) hΛ0
  rw [hdet, abs_of_pos (inv_pos.2 hpos), div_inv_eq_mul] at h
  refine ⟨Λ, fun z => ?_, h⟩
  change (∀ i ∈ Set.univ, e₀ (f z) i ∈ L i) ↔ _
  simp only [Set.mem_univ, true_imp_iff, hL]
  change (∀ i, ∃ y ∈ a i, ∀ v, ((A v)⁻¹ *ᵥ z v) i = σ v y) ↔ _
  constructor
  · intro h1
    choose y hy hz using h1
    refine ⟨y, hy, fun v => ?_⟩
    have h2 : (A v)⁻¹ *ᵥ z v = fun i => σ v (y i) := funext fun i => hz i v
    rw [← h2, mulVec_mulVec, mul_nonsing_inv _ (hA v).isUnit, one_mulVec]
  · rintro ⟨y, hy, hz⟩ i
    refine ⟨y i, hy i, fun v => ?_⟩
    rw [hz v, mulVec_mulVec, nonsing_inv_mul _ (hA v).isUnit, one_mulVec]

theorem unimod_coords {K W : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup W] [Module K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (HW : Formalism.HermitianLatticeCounting.S6.HermSpace K W) {m : ℕ} (L : Submodule (𝓞 K) W)
    (hU : IsUnimod HW L) (e : Module.Basis (Fin m) K W)
    (c : Fin m → FractionalIdeal (𝓞 K)⁰ K) (hc : ∀ i, c i ≠ 0) (hL : ∀ x, x ∈ L ↔ ∀ i, e.repr x i ∈ c i)
    (y : Fin m → K) :
    (∀ i, y i ∈ c i) ↔ ∀ i, ((Matrix.of fun i j => HW.B (e i) (e j)) *ᵥ fun j => star (y j)) i ∈ (c i)⁻¹ := by
  have hspan : Submodule.span K (L : Set W) = ⊤ := hU.1.2
  have hdualL : ∀ x, x ∈ L ↔ ∀ x' ∈ L, HW.B x x' ∈ (1 : Submodule (𝓞 K) K) := fun x => by
    conv_lhs => rw [← hU.2]
    rw [mem_dual_iff, hspan]
    simp
  have hte : ∀ (t : K) i, t ∈ c i → t • e i ∈ L := fun t i ht => (hL _).2 fun j => by
    rw [map_smul, e.repr_self, Finsupp.smul_apply, smul_eq_mul]
    by_cases hj : i = j
    · subst hj; simpa using ht
    · rw [Finsupp.single_apply, if_neg hj, mul_zero]; exact FractionalIdeal.zero_mem _
  set x : W := e.equivFun.symm y with hxdef
  have hrx : ∀ i, e.repr x i = y i := fun i => by
    show e.equivFun (e.equivFun.symm y) i = y i
    rw [LinearEquiv.apply_symm_apply]
  have hB2 : ∀ i, HW.B (e i) x = ((Matrix.of fun i j => HW.B (e i) (e j)) *ᵥ fun j => star (y j)) i := fun i => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hxdef, e.equivFun_symm_apply, map_sum]
    simp only [LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul, mulVec, dotProduct, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hyL : (∀ i, y i ∈ c i) ↔ x ∈ L := by rw [hL]; simp only [hrx]
  rw [hyL]
  simp only [← hB2]
  constructor
  · intro hx i
    rw [FractionalIdeal.mem_inv_iff (hc i)]
    intro t ht
    rw [mem_one_iff', mul_comm, ← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul]
    exact (hdualL _).1 (hte t i ht) x hx
  · intro hx
    refine (hdualL x).2 fun x' hx' => ?_
    rw [← HW.herm x' x]
    refine star_mem_one ?_
    conv => arg 2; rw [← e.sum_repr x']
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm, ← mem_one_iff']
    exact (FractionalIdeal.mem_inv_iff (hc i)).1 (hx i) _ ((hL x').1 hx' i)

theorem det_gram_ne_zero {K W : Type} [Field K] [StarRing K] [AddCommGroup W] [Module K W]
    (HW : Formalism.HermitianLatticeCounting.S6.HermSpace K W) {m : ℕ} (e : Module.Basis (Fin m) K W) :
    (Matrix.of fun i j => HW.B (e i) (e j)).det ≠ 0 := by
  intro h
  obtain ⟨w, hw, hw0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  set x : W := e.equivFun.symm w with hxdef
  have hx : ∀ j, HW.B x (e j) = 0 := fun j => by
    have h1 := congrFun hw0 j
    simp only [vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hxdef, e.equivFun_symm_apply, map_sum, LinearMap.sum_apply]
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul] using h1
  have hB : HW.B x = 0 := e.ext fun j => by rw [hx j, LinearMap.zero_apply]
  have hx0 : x = 0 := HW.nondeg x fun y => by rw [hB, LinearMap.zero_apply]
  apply hw
  have : w = e.equivFun x := by rw [hxdef, LinearEquiv.apply_symm_apply]
  rw [this, hx0, map_zero]

theorem norm_det_sq {K W : Type} [Field K] [StarRing K] [AddCommGroup W] [Module K W]
    (HW : Formalism.HermitianLatticeCounting.S6.HermSpace K W) {k : ℕ} (e : Module.Basis (Fin (k + 1)) K W) (σ : K →+* ℂ) (Ψ : W → Fin (k + 1) → ℂ)
    (hherm : ∀ x y, herm (Hb k) (Ψ x) (Ψ y) = σ (HW.B x y)) :
    ‖(Matrix.of fun j i => Ψ (e i) j).det‖ ^ 2 = ‖σ (Matrix.of fun i j => HW.B (e i) (e j)).det‖ := by
  set M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := Matrix.of fun j i => Ψ (e i) j with hM
  have hmat : Mᴴ * (Hb k * M) = ((Matrix.of fun i j => HW.B (e i) (e j)).map σ)ᵀ := by
    ext j i
    rw [transpose_apply, map_apply, of_apply, ← hherm]
    simp [M, herm, Matrix.mul_apply, mulVec, dotProduct, conjTranspose_apply]
  have h1 := congrArg Matrix.det hmat
  rw [det_mul, det_mul, det_conjTranspose, det_Hb, det_transpose,
    show ((Matrix.of fun i j => HW.B (e i) (e j)).map σ).det = σ (Matrix.of fun i j => HW.B (e i) (e j)).det
      from (RingHom.map_det σ _).symm] at h1
  rw [← h1, norm_mul, norm_mul, norm_neg, norm_one, one_mul, norm_star, sq]

theorem mul_eq_one_of_covolume_identity (P D X : ℝ) (hP : 0 < P) (hD : 0 < D) (hX : 0 < X) (h : P * X = P⁻¹ * X * (D ^ 2)⁻¹) :
    P * D = 1 := by
  have h1 : (P * D) ^ 2 * X = 1 * X := by
    rw [show (P * D) ^ 2 * X = (P * X) * P * D ^ 2 by ring, h]
    field_simp
  have h2 : (P * D) ^ 2 = 1 := mul_right_cancel₀ hX.ne' h1
  exact (pow_eq_one_iff_of_nonneg (mul_pos hP hD).le two_ne_zero).1 h2

theorem unimod_fund : ∀ (K W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (HW : Formalism.HermitianLatticeCounting.S6.HermSpace K W), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (Ψ : ι → W → Fin (k + 1) → ℂ), IsPlaces σ → Module.finrank K W = k + 1 → (∀ v x y, Ψ v (x + y) = Ψ v x + Ψ v y) → (∀ v (c : K) x, Ψ v (c • x) = σ v c • Ψ v x) → (∀ v x y, herm (Hb k) (Ψ v x) (Ψ v y) = σ v (HW.B x y)) → ∀ (L : Submodule (𝓞 K) W) (𝔡 : Ideal (𝓞 K)) (n : ℤ) (ρ : ℝ), IsUnimod HW L → 𝔡 ≠ ⊥ → 0 < ρ → ∃ F : Set (ι → Fin (k + 1) → ℂ), MeasurableSet F ∧ (∀ a : ι → Fin (k + 1) → ℂ, ∃! x : W, x ∈ ipow 𝔡 n • L ∧ ((fun v => (ρ : ℂ) • Ψ v x) + a) ∈ F) ∧ volume F = ENNReal.ofReal ((Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι * (Ideal.absNorm 𝔡 : ℝ) ^ n * ρ ^ (2 * Fintype.card ι)) ^ (k + 1)) := by
  intro K W _ _ _ _ _ _ _ _ HW hK k ι _ σ Ψ hσ hdim hadd hsmul hherm L 𝔡 n ρ hU h𝔡 hρ
  obtain ⟨hLat, -⟩ := (isUnimod_iff HW L).1 hU
  obtain ⟨e, c, hc, hLc⟩ := exists_pseudo K W (k + 1) hdim L hLat
  set S : Matrix (Fin (k + 1)) (Fin (k + 1)) K := Matrix.of fun i j => HW.B (e i) (e j) with hSdef
  have hS : S.det ≠ 0 := det_gram_ne_zero HW e
  set V : ℝ := Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι with hV
  have hvpos : 0 < Formalism.HermitianLatticesTheory.vInv K := by
    have : (discr K : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero K
    rw [Formalism.HermitianLatticesTheory.vInv]; positivity
  have hVpos : 0 < V := by positivity
  let σ' : ι → (K →+* ℂ) := fun v => ComplexEmbedding.conjugate (σ v)
  have hσ'a : ∀ v t, σ' v t = σ v (star t) := fun v t => by
    rw [ComplexEmbedding.conjugate_coe_eq, hσ.1]
  have hσ' : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (σ' v) = w := by
    simpa only [σ', InfinitePlace.mk_conjugate_eq] using hσ.2
  have hmapv : ∀ (f : K →+* ℂ) (A : Matrix (Fin (k + 1)) (Fin (k + 1)) K) (u : Fin (k + 1) → K),
      (A.map f *ᵥ fun i => f (u i)) = fun i => f ((A *ᵥ u) i) := fun f A u => by
    funext i; exact (RingHom.map_mulVec f A u i).symm
  have hdetS : ∀ v, ‖((S⁻¹).map (σ' v)).det‖ = ‖σ v S.det‖⁻¹ := fun v => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀,
      norm_inv, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
  have hSinv : ∀ v, ((S⁻¹).map (σ' v)).det ≠ 0 := fun v => by
    rw [← norm_ne_zero_iff, hdetS]
    exact inv_ne_zero (norm_ne_zero_iff.2 ((map_ne_zero _).2 hS))
  obtain ⟨Λ1, h1, hc1⟩ := exists_coordLat K hK.1 ι σ hσ.2 (k + 1) c hc (fun _ => 1) (fun _ => by simp)
  obtain ⟨Λ2, h2, hc2⟩ := exists_coordLat K hK.1 ι σ' hσ' (k + 1) (fun i => (c i)⁻¹)
    (fun i => inv_ne_zero (hc i)) (fun v => (S⁻¹).map (σ' v)) hSinv
  have hΛ : Λ1 = Λ2 := by
    ext z
    rw [h1, h2]
    constructor
    · rintro ⟨y, hy, hz⟩
      refine ⟨S *ᵥ fun j => star (y j), (unimod_coords HW L hU e c hc hLc y).1 hy, fun v => ?_⟩
      rw [hz, one_mulVec, hmapv, mulVec_mulVec, nonsing_inv_mul _ hS.isUnit, one_mulVec]
      funext i; rw [hσ'a, star_star]
    · rintro ⟨u, hu, hz⟩
      refine ⟨fun j => star ((S⁻¹ *ᵥ u) j), (unimod_coords HW L hU e c hc hLc _).2 ?_, fun v => ?_⟩
      · simp only [star_star]
        rw [mulVec_mulVec, mul_nonsing_inv _ hS.isUnit, one_mulVec]
        exact hu
      · rw [hz, one_mulVec, hmapv]
        funext i; rw [hσ'a]
  have hPD : (∏ i, (FractionalIdeal.absNorm (c i) : ℝ)) * ∏ v, ‖σ v S.det‖ = 1 := by
    subst hΛ
    obtain ⟨_, _, e1⟩ := hc1
    obtain ⟨_, _, e2⟩ := hc2
    have h := e1.symm.trans e2
    simp only [det_one, norm_one, one_pow, Finset.prod_const_one, mul_one, hdetS, map_inv₀, Rat.cast_inv,
      inv_pow, Finset.prod_mul_distrib, Finset.prod_inv_distrib] at h
    have hP : 0 < ∏ i, (FractionalIdeal.absNorm (c i) : ℝ) := Finset.prod_pos fun i _ => by
      have h0 : (FractionalIdeal.absNorm (c i) : ℝ) ≠ 0 := by
        exact_mod_cast fun h0 => hc i (FractionalIdeal.absNorm_eq_zero_iff.1 h0)
      exact lt_of_le_of_ne (by exact_mod_cast FractionalIdeal.absNorm_nonneg _) (Ne.symm h0)
    have hD : 0 < ∏ v, ‖σ v S.det‖ := Finset.prod_pos fun v _ => norm_pos_iff.2 ((map_ne_zero _).2 hS)
    rw [Finset.prod_pow _ 2 (fun v => ‖σ v S.det‖)] at h
    generalize ∏ i, (FractionalIdeal.absNorm (c i) : ℝ) = P at h hP ⊢
    generalize ∏ v, ‖σ v S.det‖ = D at h hD ⊢
    exact mul_eq_one_of_covolume_identity P D _ hP hD (by positivity) h

  set I : FractionalIdeal (𝓞 K)⁰ K := (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ n with hIdef
  have hI : I ≠ 0 := zpow_ne_zero n (FractionalIdeal.coeIdeal_ne_zero.2 h𝔡)
  set M : ι → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun v => Matrix.of fun j i => Ψ v (e i) j with hMdef
  have hMdet : ∀ v, ‖(M v).det‖ ^ 2 = ‖σ v S.det‖ := fun v => norm_det_sq HW e (σ v) (Ψ v) (hherm v)
  have hM : ∀ v, ((ρ : ℂ) • M v).det ≠ 0 := fun v => by
    rw [det_smul]
    refine mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hρ.ne')) ?_
    rw [← norm_ne_zero_iff, ← pow_ne_zero_iff two_ne_zero, hMdet]
    exact norm_ne_zero_iff.2 ((map_ne_zero _).2 hS)
  obtain ⟨Λ3, h3, hc3⟩ := exists_coordLat K hK.1 ι σ hσ.2 (k + 1) (fun i => I * c i)
    (fun i => mul_ne_zero hI (hc i)) (fun v => (ρ : ℂ) • M v) hM
  let φ : ι → W →+ (Fin (k + 1) → ℂ) := fun v => AddMonoidHom.mk' (Ψ v) (hadd v)
  have key : ∀ x v, (ρ : ℂ) • Ψ v x = ((ρ : ℂ) • M v) *ᵥ fun i => σ v (e.repr x i) := fun x v => by
    have h0 : Ψ v x = ∑ i, σ v (e.repr x i) • Ψ v (e i) := by
      conv_lhs => rw [← e.sum_repr x]
      change φ v _ = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => hsmul v _ _
    rw [Matrix.smul_mulVec, h0]
    congr 1
    funext j
    simp [hMdef, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hmem : ∀ x, x ∈ ipow 𝔡 n • L ↔ ∀ i, e.repr x i ∈ I * c i := fun x => mem_smul_iff L e c hLc I x
  have hinj : ∀ x x' : W, (fun v => (ρ : ℂ) • Ψ v x) = (fun v => (ρ : ℂ) • Ψ v x') → x = x' := by
    intro x x' hxx
    obtain ⟨v₀, -⟩ := (hσ.2 (Classical.arbitrary _)).exists
    have h0 : Ψ v₀ x = Ψ v₀ x' :=
      smul_right_injective _ (by exact_mod_cast hρ.ne' : (ρ : ℂ) ≠ 0) (congrFun hxx v₀)
    have h1 : Ψ v₀ (x - x') = 0 := by
      change φ v₀ (x - x') = 0
      rw [map_sub]; exact sub_eq_zero.2 h0
    refine sub_eq_zero.1 (HW.nondeg _ fun y => ?_)
    have h2 := hherm v₀ (x - x') y
    rw [h1] at h2
    simp only [herm, mulVec_zero, dotProduct_zero] at h2
    exact (map_eq_zero _).1 h2.symm
  obtain ⟨hd, hz, hcv⟩ := hc3
  refine ⟨GlobalTheory.latticeDomain Λ3, GlobalTheory.measurableSet_latticeDomain Λ3, fun a => ?_, ?_⟩
  · obtain ⟨p, hp, hu⟩ := GlobalTheory.existsUnique_add_mem_latticeDomain Λ3 a
    obtain ⟨y, hy, hzy⟩ := (h3 p).1 p.2
    set x : W := e.equivFun.symm y with hxdef
    have hrx : ∀ i, e.repr x i = y i := fun i => by
      show e.equivFun (e.equivFun.symm y) i = y i
      rw [LinearEquiv.apply_symm_apply]
    have hxp : (fun v => (ρ : ℂ) • Ψ v x) = (p : ι → Fin (k + 1) → ℂ) := by
      funext v
      rw [key, hzy v]
      simp only [hrx]
    refine ⟨x, ⟨(hmem x).2 fun i => by rw [hrx]; exact hy i, by rw [hxp, add_comm (p : ι → Fin (k + 1) → ℂ) a]; exact hp⟩, ?_⟩
    rintro x' ⟨hx', h'⟩
    have hp' : (fun v => (ρ : ℂ) • Ψ v x') ∈ Λ3 :=
      (h3 _).2 ⟨fun i => e.repr x' i, (hmem x').1 hx', fun v => key x' v⟩
    have h4 := hu ⟨_, hp'⟩ (by
      have h5 := h'
      rw [add_comm (fun v => (ρ : ℂ) • Ψ v x') a] at h5
      exact h5)
    exact hinj _ _ ((congrArg Subtype.val h4).trans hxp.symm)
  · rw [GlobalTheory.measure_latticeDomain Λ3 volume, hcv]
    congr 1
    have hN : ∀ i, (FractionalIdeal.absNorm (I * c i) : ℝ) =
        (Ideal.absNorm 𝔡 : ℝ) ^ n * (FractionalIdeal.absNorm (c i) : ℝ) := fun i => by
      rw [map_mul, hIdef, map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
      push_cast; ring
    have hdet : ∀ v, ‖((ρ : ℂ) • M v).det‖ ^ 2 = (ρ ^ 2) ^ (k + 1) * ‖σ v S.det‖ := fun v => by
      rw [det_smul, norm_mul, norm_pow, Fintype.card_fin, mul_pow, hMdet, Complex.norm_real,
        Real.norm_of_nonneg hρ.le, ← pow_mul, ← pow_mul, mul_comm (k + 1) 2]
    simp only [hN, hdet]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.card_univ, Fintype.card_fin]
    linear_combination (((Ideal.absNorm 𝔡 : ℝ) ^ n) ^ (k + 1) * (Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι) ^ (k + 1) *
      ((ρ ^ 2) ^ (k + 1)) ^ Fintype.card ι) * hPD

end GlobalTheory.UnimodCov
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularLatticeFundamentalSetVolumeStatement
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodular_lattice_fundamentalSet_volume : ∀ (K W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (HW : Formalism.HermitianLatticeCounting.S6.HermSpace K W), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (Ψ : ι → W → Fin (k + 1) → ℂ), IsPlaces σ → Module.finrank K W = k + 1 → (∀ v x y, Ψ v (x + y) = Ψ v x + Ψ v y) → (∀ v (c : K) x, Ψ v (c • x) = σ v c • Ψ v x) → (∀ v x y, herm (Hb k) (Ψ v x) (Ψ v y) = σ v (HW.B x y)) → ∀ (L : Submodule (𝓞 K) W) (𝔡 : Ideal (𝓞 K)) (n : ℤ) (ρ : ℝ), IsUnimod HW L → 𝔡 ≠ ⊥ → 0 < ρ → ∃ F : Set (ι → Fin (k + 1) → ℂ), MeasurableSet F ∧ (∀ a : ι → Fin (k + 1) → ℂ, ∃! x : W, x ∈ ipow 𝔡 n • L ∧ ((fun v => (ρ : ℂ) • Ψ v x) + a) ∈ F) ∧ volume F = ENNReal.ofReal ((Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι * (Ideal.absNorm 𝔡 : ℝ) ^ n * ρ ^ (2 * Fintype.card ι)) ^ (k + 1)) := by
  first | exact @GlobalTheory.UnimodCov.unimod_fund | exact GlobalTheory.UnimodCov.unimod_fund | (intros; apply GlobalTheory.UnimodCov.unimod_fund <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalSetRowsMiddleSpace
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

noncomputable section

namespace GlobalTheory.DegVol.RefCov

theorem hermPk_eq_Hb {k r : ℕ} (u w : Fin (2 * r + k + 1) → ℂ) (hu : inWb k r u) (hw : inWb k r w) :
    herm (Hpk k r) u w = herm (Hb k) (fun l => u (wI k r l)) (fun l => w (wI k r l)) := by
  have ue : ∀ a : Fin r, u (eI k r a) = 0 := fun a => hu _ (Or.inl (by simp [eI]))
  have us : ∀ b : Fin r, u (esI k r b) = 0 := fun b => hu _ (Or.inr (by have := b.2; simp [esI]; omega))
  have we : ∀ a : Fin r, w (eI k r a) = 0 := fun a => hw _ (Or.inl (by simp [eI]))
  have ws : ∀ b : Fin r, w (esI k r b) = 0 := fun b => hw _ (Or.inr (by have := b.2; simp [esI]; omega))
  have inner : ∀ l, (Hpk k r *ᵥ u) (wI k r l) = Rad.sg k l * u (wI k r l) := by
    intro l
    rw [Matrix.mulVec, dotProduct, Rad.sum3 (fun j => Hpk k r (wI k r l) j * u j)]
    simp only [ue, us, mul_zero, Finset.sum_const_zero, add_zero, zero_add, Rad.H_ww]
    rw [Finset.sum_eq_single l] <;> simp +contextual [eq_comm]
  rw [Rad.herm_Hb, herm, dotProduct, Rad.sum3 (fun i => star w i * (Hpk k r *ᵥ u) i)]
  simp only [Pi.star_apply, we, ws, star_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, inner]

theorem mem_smul_inf_rs {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (S : Submodule K V) (A : Submodule (𝓞 K) K)
    (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ A • (L ⊓ rs (𝓞 K) S) ↔ ∃ y : S, y ∈ A • L.comap (S.subtype.restrictScalars (𝓞 K)) ∧ (y : V) = x := by
  set f : S →ₗ[𝓞 K] V := S.subtype.restrictScalars (𝓞 K)
  have h1 : L ⊓ rs (𝓞 K) S = (L.comap f).map f := by
    ext z
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_map, Submodule.mem_comap]
    constructor
    · rintro ⟨hz, hs⟩; exact ⟨⟨z, hs⟩, hz, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨hy, y.2⟩
  have h2 : A • (L.comap f).map f = (A • L.comap f).map f := by
    apply le_antisymm
    · rw [Submodule.smul_le]
      rintro c hc _ ⟨y, hy, rfl⟩
      exact ⟨c • y, Submodule.smul_mem_smul hc hy, rfl⟩
    · rw [Submodule.map_le_iff_le_comap, Submodule.smul_le]
      intro c hc y hy
      rw [Submodule.mem_comap]
      change ((c • y : S) : V) ∈ A • Submodule.map f (Submodule.comap f L)
      rw [Submodule.coe_smul_of_tower]
      exact Submodule.smul_mem_smul hc ⟨y, hy, rfl⟩
  rw [h1, h2, Submodule.mem_map]
  rfl

end GlobalTheory.DegVol.RefCov

theorem _root_.GlobalTheory.DegVol.RefCov.rowsFund : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (S : Submodule K V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace K S) (k r : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ), (∀ x y : S, HW.B x y = H.B x y) → IsPlaces σ → Module.finrank K S = k + 1 → (∀ v, IsReal H k r (σ v) (Φ v)) → (∀ v, ∀ w ∈ S, inWb k r (Φ v w)) → ∀ (L : Submodule (𝓞 K) V) (𝔡 : Ideal (𝓞 K)) (n : ℤ) (ρ : ℝ), GlobalTheory.HermLat.IsUnimod HW (L.comap (S.subtype.restrictScalars (𝓞 K))) → 𝔡 ≠ ⊥ → 0 < ρ → ∃ F : Set (ι → Fin (k + 1) → ℂ), MeasurableSet F ∧ (∀ a : ι → Fin (k + 1) → ℂ, ∃! x : V, x ∈ ipow 𝔡 n • (L ⊓ rs (𝓞 K) S) ∧ ((fun v => (ρ : ℂ) • fun l => Φ v x (wI k r l)) + a) ∈ F) ∧ volume F = ENNReal.ofReal ((Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι * (Ideal.absNorm 𝔡 : ℝ) ^ n * ρ ^ (2 * Fintype.card ι)) ^ (k + 1)) := by
  intro K V _ _ _ _ _ _ _ _ H hK S HW k r ι _ σ Φ hHW hσ hk hΦ hWb L 𝔡 n ρ hL h𝔡 hρ
  obtain ⟨F, hF, hU, hvol⟩ := GlobalTheory.T.unimodular_lattice_fundamentalSet_volume K S HW hK k ι σ (fun v x l => Φ v (x : V) (wI k r l)) hσ hk
    (fun v x y => by funext l; simp [(hΦ v).1 (x : V) y])
    (fun v c x => by funext l; simp [(hΦ v).2.1 c (x : V)])
    (fun v x y => by
      rw [← GlobalTheory.DegVol.RefCov.hermPk_eq_Hb _ _ (hWb v x x.2) (hWb v y y.2), (hΦ v).2.2.1, hHW])
    (L.comap (S.subtype.restrictScalars (𝓞 K))) 𝔡 n ρ hL h𝔡 hρ
  refine ⟨F, hF, fun a => ?_, hvol⟩
  obtain ⟨y, ⟨hy, hyF⟩, hyu⟩ := hU a
  refine ⟨(y : V), ⟨(GlobalTheory.DegVol.RefCov.mem_smul_inf_rs S _ L _).2 ⟨y, hy, rfl⟩, hyF⟩, ?_⟩
  rintro x ⟨hx, hxF⟩
  obtain ⟨y', hy', rfl⟩ := (GlobalTheory.DegVol.RefCov.mem_smul_inf_rs S _ L _).1 hx
  rw [hyu y' ⟨hy', hxF⟩]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalSetRowsMiddleSpaceStatement
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamental_set_rows_middleSpace : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (S : Submodule K V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace K S) (k r : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ), (∀ x y : S, HW.B x y = H.B x y) → IsPlaces σ → Module.finrank K S = k + 1 → (∀ v, IsReal H k r (σ v) (Φ v)) → (∀ v, ∀ w ∈ S, inWb k r (Φ v w)) → ∀ (L : Submodule (𝓞 K) V) (𝔡 : Ideal (𝓞 K)) (n : ℤ) (ρ : ℝ), GlobalTheory.HermLat.IsUnimod HW (L.comap (S.subtype.restrictScalars (𝓞 K))) → 𝔡 ≠ ⊥ → 0 < ρ → ∃ F : Set (ι → Fin (k + 1) → ℂ), MeasurableSet F ∧ (∀ a : ι → Fin (k + 1) → ℂ, ∃! x : V, x ∈ ipow 𝔡 n • (L ⊓ rs (𝓞 K) S) ∧ ((fun v => (ρ : ℂ) • fun l => Φ v x (wI k r l)) + a) ∈ F) ∧ volume F = ENNReal.ofReal ((Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι * (Ideal.absNorm 𝔡 : ℝ) ^ n * ρ ^ (2 * Fintype.card ι)) ^ (k + 1)) := by
  first | exact @GlobalTheory.DegVol.RefCov.rowsFund | exact GlobalTheory.DegVol.RefCov.rowsFund | (intros; apply GlobalTheory.DegVol.RefCov.rowsFund <;> assumption)
end
