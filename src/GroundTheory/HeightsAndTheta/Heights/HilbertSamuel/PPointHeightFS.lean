module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResVolume
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatNoetherFrame

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPointHeightFS
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace PointHeightFSAux

abbrev fsOne : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (GlobalTheory (Fin 1)) := ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofCone (fsMetric (ι := Ix (Fin 1)))

abbrev x0 : MRing (GlobalTheory (Fin 1)) := X ⟨(), 0⟩

theorem isSmoothHerm_fsOne : IsSmoothHerm fsOne := by
  refine (ProjLine.isSmoothMetric_fs (J := Ix (Fin 1))).mono fun z hz h0 => ?_
  obtain ⟨i, hi⟩ := hz ()
  exact hi (congrFun h0 _)

theorem divisorSupport_coordinate_point : divSupp (⊥ : Ideal (MRing (GlobalTheory (Fin 1)))) x0 = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun W hW => ?_
  obtain ⟨i, hi⟩ := hW.2 ()
  have hle := hW.1.1.2
  have hi0 : i = 0 := Subsingleton.elim _ _
  subst hi0
  exact hi (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))

theorem logNorm_coordinate_point : logNorm fsOne x0 = fun _ => 0 := by
  funext z
  have hρ : fsOne.h z = ‖z ⟨(), 0⟩‖ := by
    let _ : Unique (Ix (Fin 1)) :=
      ⟨⟨⟨(), 0⟩⟩, fun p => by rcases p with ⟨⟨⟩, i⟩; rw [Subsingleton.elim i 0]; rfl⟩
    show ‖WithLp.toLp 2 z‖ = _
    rw [EuclideanSpace.norm_eq, Fintype.sum_unique, Real.sqrt_sq (norm_nonneg _)]
    rfl
  simp only [logNorm, hρ, map_X, eval_X]
  rcases eq_or_ne (z ⟨(), 0⟩) 0 with h | h
  · simp [h]
  · rw [div_self (norm_ne_zero_iff.mpr h), Real.log_one]

theorem ptsIntegral_zero {e : ℕ} (P : Ideal (MRing (GlobalTheory (Fin 1))))
    (φ : Fin e → (Ix (Fin 1) → ℂ) → ℝ) : ptsIntegral P φ (fun _ => 0) = 0 := by
  classical
  unfold ptsIntegral
  split_ifs
  · simp [ptsIntegralAt, sheetDensity]
  · rfl

end PointHeightFSAux


open PointHeightFSAux in
theorem PointHeightFS.proof : PointHeightFS.Statement := by
  intro I hI
  classical
  have hP : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (Fin 1)))) (0 + 1) := IndefiniteRowSideFullHecke.Inter.isArithVar_bot 0
  have hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog x0 fun _ => 1 := IndefiniteRowSideFullHecke.Inter.isMultiHomog_Xb 1 0
  have hx0 : x0 ∉ (⊥ : Ideal (MRing (GlobalTheory (Fin 1)))) := by
    rw [Ideal.mem_bot]
    exact X_ne_zero _
  have hR := (hI Unit (GlobalTheory (Fin 1))).2.2 ⊥ 0 Fin.elim0 fsOne x0 (fun _ => 1) hP (fun j => j.elim0)
    isSmoothHerm_fsOne (fun _ => rfl) hs hx0
  have hL : (Fin.snoc (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (GlobalTheory (Fin 1))) fsOne : Fin 1 → _) =
      fun _ => fsOne := by
    funext j
    fin_cases j
    rfl
  rw [hL] at hR
  unfold hhOf
  rw [hR, recR, divisorSupport_coordinate_point, finsum_mem_empty, zero_sub, arInt, logNorm_coordinate_point, ptsIntegral_zero, neg_zero]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegMatAct
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenDegMatAct

section Subst

variable {J : Type} [Fintype J]

def linSubst (B : Matrix J J ℚ) : MvPolynomial J ℚ →ₐ[ℚ] MvPolynomial J ℚ :=
  aeval fun i => ∑ j, C (B i j) * X j

theorem linSubst_comp (B B' : Matrix J J ℚ) :
    (linSubst B).comp (linSubst B') = linSubst (B' * B) := by
  apply MvPolynomial.algHom_ext
  intro i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [linSubst, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem linSubst_one [DecidableEq J] : linSubst (1 : Matrix J J ℚ) = AlgHom.id ℚ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [linSubst, Matrix.one_apply, apply_ite C, ite_mul]

theorem exists_inv [DecidableEq J] {B : Matrix J J ℚ} (hB : IsInvMat B) : ∃ B' : Matrix J J ℚ, B * B' = 1 ∧ B' * B = 1 := by
  classical
  obtain ⟨B', h⟩ := hB
  refine ⟨B', ?_, ?_⟩ <;> rw [Matrix.ext_iff_mulVec] <;> intro v <;>
    simp [← Matrix.mulVec_mulVec, (h v).1, (h v).2]

def linEquiv [DecidableEq J] (B B' : Matrix J J ℚ) (h₁ : B * B' = 1) (h₂ : B' * B = 1) :
    MvPolynomial J ℚ ≃ₐ[ℚ] MvPolynomial J ℚ :=
  AlgEquiv.ofAlgHom (linSubst B) (linSubst B') (by rw [linSubst_comp, h₂, linSubst_one])
    (by rw [linSubst_comp, h₁, linSubst_one])

theorem isHomogeneous_linSubst (B : Matrix J J ℚ) {f : MvPolynomial J ℚ} {n : ℕ} (hf : f.IsHomogeneous n) :
    (linSubst B f).IsHomogeneous n := by
  have h := hf.aeval (fun i => ∑ j, C (B i j) * X j) (n := 1) fun i =>
    IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_C J (B i j)).mul (isHomogeneous_X ℚ j)
  simpa [linSubst] using h

end Subst

section Ideals

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem coneMap_matAct (B : Matrix J J ℚ) (x : J → Ω) :
    coneMap ℚ (matAct B x) = (coneMap ℚ x).comp (linSubst B) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [coneMap, matAct, linSubst, Finset.sum_mul, mul_assoc, Polynomial.algebraMap_apply]

theorem coordIdeal_matAct (B : Matrix J J ℚ) (x : J → Ω) :
    coordIdeal ℚ (matAct B x) = (coordIdeal ℚ x).comap (linSubst B) := by
  ext f
  simp [coordIdeal, RingHom.mem_ker, coneMap_matAct]


omit [Fintype J] in
theorem map_coordIdeal_int (x : J → Ω) :
    (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) = coordIdeal ℚ x := by
  have hring : ((coneMap ℚ x : MvPolynomial J ℚ →+* Polynomial Ω).comp
      (MvPolynomial.map (Int.castRingHom ℚ))) = (coneMap ℤ x : MvPolynomial J ℤ →+* Polynomial Ω) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coneMap]
    · intro i
      simp [coneMap]
  have hker : coordIdeal ℤ x = (coordIdeal ℚ x).comap (MvPolynomial.map (Int.castRingHom ℚ)) := by
    ext f
    rw [Ideal.mem_comap]
    simp only [coordIdeal, RingHom.mem_ker]
    have h := RingHom.congr_fun hring f
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at h
    rw [h]
  let _ := MvPolynomial.algebraMvPolynomial (σ := J) (R := ℤ) (S := ℚ)
  have e : algebraMap (MvPolynomial J ℤ) (MvPolynomial J ℚ) = MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  have h := IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := J))) (MvPolynomial J ℚ)
    (coordIdeal ℚ x)
  rw [e] at h
  rw [hker]
  exact h

end Ideals

section Hilbert

variable {κ : Type} [Fintype κ]

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem isWeightedHomogeneous_iff (f : MvPolynomial (Ix κ) ℚ) (m : Unit → ℕ) :
    IsWeightedHomogeneous (blockWeight (GlobalTheory κ)) f m ↔ f.IsHomogeneous (m ()) := by
  have hdeg : ∀ d : Ix κ →₀ ℕ, ∑ i : κ, d ⟨(), i⟩ = Finsupp.weight 1 d := by
    intro d
    have h1 : d.degree = Finsupp.weight 1 d := by
      rw [Finsupp.degree_eq_weight_one]
      rfl
    rw [← h1, Finsupp.degree_eq_sum, Fintype.sum_sigma]
    exact (Fintype.sum_unique (fun u : Unit => ∑ y : GlobalTheory κ u, d ⟨u, y⟩)).symm
  have hw : ∀ d : Ix κ →₀ ℕ, Finsupp.weight (blockWeight (GlobalTheory κ)) d = fun _ => Finsupp.weight 1 d := by
    intro d
    funext u
    cases u
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
    simp [NumbersDVR.blockWeight]
  simp only [IsHomogeneous, IsWeightedHomogeneous, hw]
  constructor
  · intro h d hd
    exact congrFun (h hd) ()
  · intro h d hd
    funext u
    exact h hd

theorem mem_weighted_linSubst (B : Matrix (Ix κ) (Ix κ) ℚ) {m : Unit → ℕ} {f : MvPolynomial (Ix κ) ℚ}
    (hf : f ∈ weightedHomogeneousSubmodule ℚ (blockWeight (GlobalTheory κ)) m) :
    linSubst B f ∈ weightedHomogeneousSubmodule ℚ (blockWeight (GlobalTheory κ)) m := by
  rw [mem_weightedHomogeneousSubmodule, isWeightedHomogeneous_iff] at hf ⊢
  exact isHomogeneous_linSubst B hf

theorem hilbFn_comap [DecidableEq κ] (B B' : Matrix (Ix κ) (Ix κ) ℚ) (h₁ : B * B' = 1) (h₂ : B' * B = 1)
    (P : Ideal (MRing (GlobalTheory κ) ℚ)) : NumbersDVR.hilbFn (P.comap (linSubst B)) = NumbersDVR.hilbFn P := by
  set e := linEquiv B B' h₁ h₂
  have hc : P.comap (linSubst B) = P.comap e := by
    ext f
    rfl
  have hIJ : P = (P.comap e).map (e : MRing (GlobalTheory κ) ℚ →+* MRing (GlobalTheory κ) ℚ) :=
    (Ideal.map_comap_of_surjective _ e.surjective P).symm
  set E := Ideal.quotientEquivAlg (R₁ := ℚ) (P.comap e) P e hIJ
  have hpiece : ∀ m : Unit → ℕ, (NumbersDVR.gradedPiece (P.comap e) m).map E.toLinearEquiv.toLinearMap = NumbersDVR.gradedPiece P m := by
    intro m
    ext y
    simp only [NumbersDVR.gradedPiece, Submodule.mem_map]
    constructor
    · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      refine ⟨e f, mem_weighted_linSubst B hf, ?_⟩
      simp [E, Ideal.quotientEquivAlg_mk]
    · rintro ⟨g, hg, rfl⟩
      refine ⟨_, ⟨e.symm g, mem_weighted_linSubst B' hg, rfl⟩, ?_⟩
      simp [E, Ideal.quotientEquivAlg_mk]
  funext m
  unfold NumbersDVR.hilbFn
  rw [hc]
  split_ifs
  · rw [← hpiece, LinearEquiv.finrank_map_eq]
  · rfl

end Hilbert

end GenDegMatAct

theorem GenDegMatAct.proof : GenDegMatAct.Statement := by
  intro D Ω _ _ κ _ x B hB
  classical
  obtain ⟨B', h₁, h₂⟩ := GenDegMatAct.exists_inv hB
  unfold genDeg
  rw [GenDegMatAct.map_coordIdeal_int, GenDegMatAct.map_coordIdeal_int, GenDegMatAct.coordIdeal_matAct]
  unfold NumbersDVR.intNum
  congr 2
  convert GenDegMatAct.hilbFn_comap B B' h₁ h₂ (coordIdeal ℚ x)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHeightsirationalHilb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockBirationalHilbert

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def blockSum (γ : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, γ ⟨k, i⟩

omit [Fintype K] in
theorem isMultiHomog_monomial {γ : (Σ k, ι k) →₀ ℕ} {a : K → ℕ} (h : blockSum γ = a) (r : ℤ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (monomial γ r : MRing ι) a := by
  intro m hm k
  rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
  exact congrFun h k

omit [Fintype K] in
theorem isMultiHomog_mul {f g : MRing ι} {a b c : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b)
    (habc : a + b = c) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f * g) c := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf m₁ hm₁ k, hg m₂ hm₂ k, ← habc, Pi.add_apply]

omit [Fintype K] in
theorem isMultiHomog_prod {J : Type} (s : Finset J) (f : J → MRing ι) (d : J → K → ℕ)
    (h : ∀ j ∈ s, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f j) (d j)) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ j ∈ s, f j) (∑ j ∈ s, d j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h1 := isMultiHomog_monomial (ι := ι) (γ := 0) (a := 0) (by funext k; simp [blockSum]) 1
    simpa using h1
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact isMultiHomog_mul (h j (Finset.mem_insert_self j s))
      (ih fun j' hj' => h j' (Finset.mem_insert_of_mem hj')) rfl


open Classical in
def monoSet (a : K → ℕ) : Finset ((Σ k, ι k) →₀ ℕ) :=
  (Finset.Icc 0 (Finsupp.equivFunOnFinite.symm fun p : (Σ k, ι k) => a p.1)).filter (blockSum · = a)

theorem mem_monoSet {a : K → ℕ} {γ : (Σ k, ι k) →₀ ℕ} : γ ∈ monoSet a ↔ blockSum γ = a := by
  classical
  unfold monoSet
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨Finset.mem_Icc.mpr ⟨by simp, fun p => ?_⟩, h⟩⟩
  rw [Finsupp.coe_equivFunOnFinite_symm, ← h]
  exact Finset.single_le_sum (f := fun i => γ ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)

omit [Fintype K] [∀ k, Fintype (ι k)] [CharZero Ω] in
theorem aeval_monomial_int (y : (Σ k, ι k) → Ω) (γ : (Σ k, ι k) →₀ ℕ) (r : ℤ) :
    aeval y (monomial γ r : MRing ι) = ((r : ℚ) : Ω) * aeval y (monomial γ (1 : ℤ) : MRing ι) := by
  simp [aeval_monomial]


omit [Fintype K] in
theorem valueSpan_le (y : (Σ k, ι k) → Ω) (a : K → ℕ) (W : Submodule ℚ Ω)
    (hW : ∀ γ : (Σ k, ι k) →₀ ℕ, blockSum γ = a → aeval y (monomial γ (1 : ℤ) : MRing ι) ∈ W) :
    valueSpan y a ≤ W := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [g.as_sum, map_sum]
  refine Submodule.sum_mem _ fun γ hγ => ?_
  rw [aeval_monomial_int, ← Rat.smul_def]
  exact W.smul_mem _ (hW γ (funext fun k => hg γ hγ k))

theorem finiteDimensional_valueSpan (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    FiniteDimensional ℚ (valueSpan y a) := by
  classical
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ
    (((monoSet a).image fun γ => aeval y (monomial γ (1 : ℤ) : MRing ι) : Finset Ω) : Set Ω))
    (valueSpan_le y a _ fun γ hγ => Submodule.subset_span ?_)
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  exact ⟨γ, mem_monoSet.mpr hγ, rfl⟩


omit [Fintype K] [∀ k, Fintype (ι k)] [CharZero Ω] in
theorem finrank_le_of_mul [CharZero Ω] {V W : Submodule ℚ Ω} [FiniteDimensional ℚ W] {t : Ω} (ht : t ≠ 0)
    (h : V ≤ W.comap (LinearMap.mulLeft ℚ t)) : Module.finrank ℚ V ≤ Module.finrank ℚ W := by
  have hinj : Function.Injective (LinearMap.mulLeft ℚ t) := fun a b hab => mul_left_cancel₀ ht hab
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj V)]
  exact Submodule.finrank_mono (Submodule.map_le_iff_le_comap.mpr h)

end BlockBirationalHilbert


open BlockBirationalHilbert in
theorem BlockBirationalHilbert.proof (hV : HilbFnValueSpan.Statement) : BlockBirationalHilbert.Statement := by
  intro K _ _ ι _ Ω _ _ y k₀ hy hbir m
  classical
  choose i hi using hy
  have hV' := hV K ι Ω y
  have := finiteDimensional_valueSpan (Ω := Ω) y

  have L : ∀ n : ℕ, GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn
      ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun k => if k = k₀ then (n : ℤ) else 0) =
      (Module.finrank ℚ (valueSpan y (blockDeg k₀ n)) : ℤ) := fun n => by
    rw [← hV']; congr 1; funext k; by_cases hk : k = k₀ <;> simp [hk, blockDeg]
  have M : ∀ n : ℕ, GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn
      ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun k => if k = k₀ then (n : ℤ) else m k) =
      (Module.finrank ℚ (valueSpan y (fun k => if k = k₀ then n else m k)) : ℤ) := fun n => by
    rw [← hV']; congr 1; funext k; by_cases hk : k = k₀ <;> simp [hk]

  set m₀ : K → ℕ := fun k => if k = k₀ then 0 else m k with hm₀
  let β : (Σ k, ι k) →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun p => if p.1 ≠ k₀ ∧ p.2 = i p.1 then m p.1 else 0
  have hβ : blockSum β = m₀ := by
    funext k
    by_cases hk : k = k₀ <;> simp [blockSum, β, hk, m₀]
  set u : Ω := aeval y (monomial β (1 : ℤ) : MRing ι) with hu_def
  have hu : u ≠ 0 := by
    rw [hu_def, aeval_monomial, map_one, one_mul, Finsupp.prod]
    refine Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ ?_
    rcases p with ⟨k, j⟩
    have h0 : β ⟨k, j⟩ ≠ 0 := Finsupp.mem_support_iff.mp hp
    simp only [β, Finsupp.coe_equivFunOnFinite_symm] at h0
    split_ifs at h0 with h
    · obtain ⟨_, rfl⟩ := h
      exact hi k
    · exact absurd rfl h0

  have key : ∀ α ∈ monoSet (ι := ι) m₀, ∃ (c : ℕ) (g h : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g (blockDeg k₀ c) ∧
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h (blockDeg k₀ c) ∧ aeval y h ≠ 0 ∧
      aeval y (monomial α (1 : ℤ) : MRing ι) * aeval y h = aeval y g * u := fun α hα =>
    hbir m₀ _ _ (isMultiHomog_monomial (mem_monoSet.mp hα) 1) (isMultiHomog_monomial hβ 1) hu
  choose c g h hg hh hh0 hgh using key
  refine ⟨∑ a ∈ (monoSet (ι := ι) m₀).attach, c a.1 a.2, fun n => ⟨?_, ?_⟩⟩
  ·
    rw [L, M]
    refine Nat.cast_le.mpr (finrank_le_of_mul hu (valueSpan_le y _ _ fun γ hγ => ?_))
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    refine Submodule.subset_span ⟨monomial β 1 * monomial γ 1,
      isMultiHomog_mul (isMultiHomog_monomial hβ 1) (isMultiHomog_monomial hγ 1) ?_, by
        simp only [map_mul, hu_def]⟩
    funext k; by_cases hk : k = k₀ <;> simp [hk, m₀, blockDeg]
  ·
    rw [M, L]
    have hH : aeval y (∏ a ∈ (monoSet (ι := ι) m₀).attach, h a.1 a.2) ≠ 0 := by
      rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun a _ => hh0 a.1 a.2
    refine Nat.cast_le.mpr (finrank_le_of_mul (mul_ne_zero (inv_ne_zero hu) hH)
      (valueSpan_le y _ _ fun γ hγ => ?_))
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]

    set γ₀ := γ.filter (fun p => p.1 = k₀) with hγ₀
    set α := γ.filter (fun p => ¬ p.1 = k₀) with hα_def
    have hsplit : γ₀ + α = γ := Finsupp.filter_add_filter_not γ _
    have hα : blockSum α = m₀ := by
      funext k
      have := congrFun hγ k
      by_cases hk : k = k₀ <;> simp_all [blockSum, m₀]
    have hγ₀' : blockSum γ₀ = blockDeg k₀ n := by
      funext k
      have := congrFun hγ k
      by_cases hk : k = k₀ <;> simp_all [blockSum, blockDeg]
    have hαS : α ∈ monoSet (ι := ι) m₀ := mem_monoSet.mpr hα
    have hmem : (⟨α, hαS⟩ : {x // x ∈ monoSet (ι := ι) m₀}) ∈ (monoSet (ι := ι) m₀).attach :=
      Finset.mem_attach _ _
    refine Submodule.subset_span ⟨monomial γ₀ 1 * g α hαS *
      ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, h a.1 a.2,
      isMultiHomog_mul (isMultiHomog_mul (isMultiHomog_monomial hγ₀' 1) (hg α hαS) rfl)
        (isMultiHomog_prod _ _ (fun a => blockDeg k₀ (c a.1 a.2)) fun a _ => hh a.1 a.2) ?_, ?_⟩
    · funext k
      by_cases hk : k = k₀
      · simp only [Pi.add_apply, Finset.sum_apply, blockDeg, hk, if_true]
        rw [← Finset.add_sum_erase _ _ hmem]
        ring
      · simp [blockDeg, hk, Finset.sum_apply]
    · have e1 : aeval y (monomial γ (1 : ℤ) : MRing ι) =
          aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (monomial α (1 : ℤ) : MRing ι) := by
        rw [← map_mul, monomial_mul, hsplit, mul_one]
      rw [map_mul, map_mul, e1, map_prod, map_prod, ← Finset.mul_prod_erase _ _ hmem]
      have e2 := hgh α hαS
      calc aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (g α hαS) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)
          = (u⁻¹ * u) * (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (g α hαS) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) := by
            rw [inv_mul_cancel₀ hu, one_mul]
        _ = u⁻¹ * (aeval y (g α hαS) * u) * (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) := by ring
        _ = u⁻¹ * (aeval y (monomial α (1 : ℤ) : MRing ι) * aeval y (h α hαS)) *
            (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) := by rw [e2]
        _ = u⁻¹ * (aeval y (h α hαS) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) *
            (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (monomial α (1 : ℤ) : MRing ι)) := by ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
