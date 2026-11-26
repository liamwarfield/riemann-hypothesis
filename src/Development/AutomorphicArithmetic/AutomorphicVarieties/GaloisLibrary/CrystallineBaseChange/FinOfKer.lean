module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TeichmullerCharacterSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralityOfNormCoefficients
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepPropertiesInvariantUnderConjugation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PCuspFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UpQuad
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HyperbolicKernelAlgebraProof

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CuspSet
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.IwasawaA
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GroundTheory.Automorphic
open scoped Matrix

private theorem upper_eq {R : Type} [CommRing R] (b : GL (Fin 2) R) (h : b 1 0 = 0) (h0 : IsUnit (b 0 0)) (h1 : IsUnit (b 1 1)) :
    ∃ (z y : Rˣ) (x : R), b = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y x := by
  obtain ⟨a, ha⟩ := h0
  obtain ⟨d, hd⟩ := h1
  refine ⟨d, d⁻¹ * a, (d⁻¹ : Rˣ) * b 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.GeneralLinearGroup.scalar, h, ← ha, ← hd]

private theorem orth {E : Type} [NormedField E] (φ : E ≃+* ℝ) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (k : Matrix (Fin 2) (Fin 2) E)
    (hk : ∀ y : Fin 2 → E, Reduction.euclidNorm (y ᵥ* k) = Reduction.euclidNorm y) (i j : Fin 2) :
    φ (k i 0) * φ (k j 0) + φ (k i 1) * φ (k j 1) = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  have h : ∀ s t : E, (φ s * φ (k 0 0) + φ t * φ (k 1 0)) ^ 2 + (φ s * φ (k 0 1) + φ t * φ (k 1 1)) ^ 2 = φ s ^ 2 + φ t ^ 2 := by
    intro s t
    have := hk ![s, t]
    unfold Reduction.euclidNorm at this
    rw [Real.sqrt_inj (by positivity) (by positivity)] at this
    simpa [← hφ, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] using this
  have h1 := h 1 0
  have h2 := h 0 1
  have h3 := h 1 1
  simp only [map_one, map_zero] at h1 h2 h3
  fin_cases i <;> fin_cases j <;> simp <;> nlinarith

theorem UpperTheory.V.Br.iwasawaA :
    UpperTheory.V.Br.IwasawaA := by
  intro F _ _ _ g
  obtain ⟨b, hb, k, hk, rfl⟩ := Reduction.exists_adelicBorel_mul_maxCompact g
  obtain ⟨z, y, x, hz⟩ := upper_eq b (hb (show (0 : Fin 2) < 1 by decide))
    (Reduction.isUnit_apply_self_of_mem_adelicBorel hb 0) (Reduction.isUnit_apply_self_of_mem_adelicBorel hb 1)
  have hr : ((Matrix.GeneralLinearGroup.map (TR.pInf F) k : GL (Fin 2) (TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) ∈
      Matrix.unitaryGroup (Fin 2) (TR.Rinf F) := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j w
    have := orth (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w))
      (fun x => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)).norm_map_of_map_zero
        (map_zero _) x) _ (hk.1 w) i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine Eq.trans this ?_
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  have hu : Matrix.GeneralLinearGroup.map (pFin F) k ∈ AdelicGLn.integralFiniteGL F 2 :=
    (AdelicGLn.mem_integralFiniteGL_iff_forall F 2).2 hk.2
  obtain ⟨hu1, hu2⟩ := (AdelicGLn.mem_integralFiniteGL_iff F 2).1 hu
  refine ⟨z, y, x, ⟨_, hr⟩, Matrix.GeneralLinearGroup.map (pFin F) k, ?_, ?_⟩
  · refine mem_KLev.2 ⟨fun a c => mem_Ohat.2 (hu1 a c), fun a c => mem_Ohat.2 (hu2 a c), fun a c => ⟨_, ?_, by rw [Nat.cast_one, one_mul]⟩⟩
    refine sub_mem (mem_Ohat.2 (hu1 a c)) ?_
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  · have e : Unitary.toUnits (⟨_, hr⟩ : TR.Kinf F 2) = Matrix.GeneralLinearGroup.map (TR.pInf F) k := Units.ext rfl
    rw [e, TR.infGL_mul_finGL, ← hz]
end

open NumberField IsDedekindDomain Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Eis
open scoped Matrix

namespace UpperTheory.V.Br.CuspStabilizer

section Aff
variable {R S : Type} [CommRing R] [CommRing S]

private theorem aff_mul (y y' : Rˣ) (x x' : R) : aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem aff_one : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

private theorem corner_aff (s : R →ₙ+* S) (y : Rˣ) (x : R) : cornerGL 2 s (aff y x) = aff (Units.map (corner s) y) (s x) := by
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (aff y x i j) = _
  fin_cases i <;> fin_cases j <;> simp [aff, corner]

private theorem continuous_aff [TopologicalSpace R] [IsTopologicalRing R] : Continuous fun y : Rˣ => aff y (0 : R) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop

end Aff

variable {F : Type} [Field F] [NumberField F]

private noncomputable def rot (θ : TR.Rinf F) : TR.Kinf F 2 :=
  ⟨!![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq (θ v)]⟩

private noncomputable def eps (s : InfinitePlace F → ℤˣ) : TR.Kinf F 2 :=
  ⟨!![1, 0; 0, fun v => ((s v : ℤ) : ℝ)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
    rcases Int.units_eq_one_or (s v) with h | h <;> simp [h]⟩

private theorem real_dec {a b c d : ℝ} (h1 : a * a + b * b = 1) (h2 : a * c + b * d = 0) (h3 : c * c + d * d = 1) :
    ∃ (s : ℤˣ) (t : ℝ), a = Real.cos t ∧ b = Real.sin t ∧ c = -((s : ℤ) * Real.sin t) ∧ d = (s : ℤ) * Real.cos t := by
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, h1, Real.sqrt_one]
  have h0 : (⟨a, b⟩ : ℂ) ≠ 0 := fun h => by simp [h] at hn
  have ha : a = Real.cos (Complex.arg ⟨a, b⟩) := by rw [Complex.cos_arg h0, hn, div_one]
  have hb : b = Real.sin (Complex.arg ⟨a, b⟩) := by rw [Complex.sin_arg, hn, div_one]
  have hc : c = -((a * d - b * c) * b) := by linear_combination (-c) * h1 + a * h2
  have hd : d = (a * d - b * c) * a := by linear_combination (-d) * h1 + b * h2
  have hs : (a * d - b * c) * (a * d - b * c) = 1 := by
    linear_combination (c * c + d * d) * h1 + h3 - (a * c + b * d) * h2
  rcases mul_self_eq_one_iff.1 hs with h | h
  · exact ⟨1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩
  · exact ⟨-1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩

omit [NumberField F] in
private theorem dec (x : TR.Kinf F 2) : ∃ s θ, x = eps s * rot θ := by
  have h := Matrix.mem_unitaryGroup_iff.1 x.2
  have e : ∀ i j v, x.1 i 0 v * x.1 j 0 v + x.1 i 1 v * x.1 j 1 v = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j v := fun i j v => by
    rw [← h]; simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
  choose s θ h1 h2 h3 h4 using fun v => real_dec (a := x.1 0 0 v) (b := x.1 0 1 v) (c := x.1 1 0 v) (d := x.1 1 1 v)
    (by simpa using e 0 0 v) (by simpa using e 0 1 v) (by simpa using e 1 1 v)
  refine ⟨s, θ, ?_⟩
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, eps, Matrix.mul_apply, Fin.sum_univ_succ, h1, h2, h3, h4]

variable [IsTotallyReal F]

private def stab (M : ℕ) (g : GA F 2) : Subgroup (Ideles F) where
  carrier := {u | ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff (t * u) 0 * g ∈ Z ↔ aff t 0 * g ∈ Z}
  one_mem' := fun Z _ t => by rw [mul_one]
  mul_mem' := fun {a b} ha hb Z hZ t => by rw [← mul_assoc, hb Z hZ, ha Z hZ]
  inv_mem' := fun {a} ha Z hZ t => by rw [← ha Z hZ, inv_mul_cancel_right]

private theorem mem_stab {M : ℕ} {g : GA F 2} {u : Ideles F}
    (h1 : ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z → aff (t * u) 0 * g ∈ Z)
    (h2 : ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z → aff (t * u⁻¹) 0 * g ∈ Z) : u ∈ stab M g :=
  fun Z hZ t => ⟨fun h => by simpa only [mul_inv_cancel_right] using h2 Z hZ _ h, h1 Z hZ t⟩

private theorem stab_fin {M : ℕ} (hM : 1 ≤ M) (g : GA F 2) : (stab M g).FiniteIndex := by
  have am : ∀ t u : Ideles F, aff (t * u) (0 : Ad F) = aff u 0 * aff t 0 := fun t u => by rw [aff_mul, mul_comm]; simp
  have h1 : ∀ a : Fˣ, ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z → aff (t * diagUnits F a) 0 * g ∈ Z :=
    fun a Z hZ t h => by rw [am, mul_assoc]; exact hZ.rat a _ h
  have h2 : ∀ y : (TR.Rinf F)ˣ, (∀ v, 0 < y.val v) → ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z →
      aff (t * TR.infId F y) 0 * g ∈ Z := fun y hy Z hZ t h => by
    have := hZ.pos y hy _ h
    rw [TR.infGL, corner_aff, map_zero] at this
    rw [am, mul_assoc]; exact this
  set k := Matrix.GeneralLinearGroup.map (pFin F) g with hk
  have h3 : ∀ u : (Af F)ˣ, k⁻¹ * aff u 0 * k ∈ KLev F 2 M → ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z →
      aff (t * finId F u) 0 * g ∈ Z := fun u hu Z hZ t h => by
    have e : aff (finId F u) 0 * g = g * finGL F 2 (k⁻¹ * aff u 0 * k) := by
      have : aff (finId F u) 0 = finGL F 2 (aff u 0) := by rw [finGL, corner_aff, map_zero]; rfl
      rw [this]
      exact TR.ga_ext (by simp) (by simp [k, mul_assoc])
    rw [mul_comm t, am, mul_assoc, e, ← mul_assoc]
    exact hZ.lev _ hu _ h
  refine (UpperTheory.ray_class_group_finite F (stab M g) (fun a => mem_stab (h1 a) ?_) (fun y hy => mem_stab (h2 y hy) ?_) ?_).2
  · rw [← map_inv]; exact h1 _
  · rw [← map_inv]
    refine h2 _ fun v => ?_
    have h : y.val v * (y⁻¹).val v = 1 := congrFun y.mul_inv v
    exact (mul_pos_iff_of_pos_left (hy v)).1 (h ▸ one_pos)
  · have h4 := ((isOpen_KLev (F := F) (n := 2) hM).preimage (f := fun u : (Af F)ˣ => k⁻¹ * aff u 0 * k)
      ((continuous_const.mul continuous_aff).mul continuous_const)).mem_nhds (x := 1) (by simp [aff_one])
    filter_upwards [h4] with u hu
    refine mem_stab (h3 u hu) ?_
    rw [← map_inv]
    refine h3 _ ?_
    have e : aff u⁻¹ (0 : Af F) = (aff u 0)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [aff_mul]; simp [aff_one])
    have := (KLev F 2 M).inv_mem hu
    rw [e]
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using this

end UpperTheory.V.Br.CuspStabilizer

open UpperTheory.V.Br.CuspStabilizer in
theorem UpperTheory.V.Br.cuspSet :
    UpperTheory.V.Br.CuspSet := by
  intro F _ _ _ M hM
  haveI : CompactSpace (KLev F 2 1) := isCompact_iff_compactSpace.1 (isCompact_KLev le_rfl)
  haveI : Finite (KLev F 2 1 ⧸ (KLev F 2 M).subgroupOf (KLev F 2 1)) :=
    Subgroup.quotient_finite_of_isOpen _ ((isOpen_KLev hM).preimage continuous_subtype_val)
  let b : (InfinitePlace F → ℤˣ) × (KLev F 2 1 ⧸ (KLev F 2 M).subgroupOf (KLev F 2 1)) → GA F 2 := fun p =>
    TR.infGL F 2 (Unitary.toUnits (eps p.1)) * finGL F 2 p.2.out.1
  haveI : ∀ g : GA F 2, (stab M g).FiniteIndex := stab_fin hM
  refine ⟨⋃ p, Set.range fun q : Ideles F ⧸ stab M (b p) => aff q.out 0 * b p,
    Set.finite_iUnion fun p => Set.finite_range _, fun Z hS hZ => Set.eq_univ_of_forall fun g => ?_⟩
  have h1 : ∀ p t, aff t 0 * b p ∈ Z := fun p t => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (stab M (b p)) t
    refine (h.2 Z hZ t).1 ?_
    rw [← hh]
    exact hS (Set.mem_iUnion.2 ⟨p, _, rfl⟩)
  obtain ⟨z, y, x, r, u, hu, rfl⟩ := UpperTheory.V.Br.iwasawaA F g
  obtain ⟨s, θ, rfl⟩ := dec r
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((KLev F 2 M).subgroupOf (KLev F 2 1)) ⟨u, hu⟩
  have h2 := hZ.lev _ ((KLev F 2 M).inv_mem h.2) _ (h1 (s, QuotientGroup.mk ⟨u, hu⟩) y)
  have h3 := hZ.cent z _ (hZ.unip x _ (hZ.rot θ (Unitary.toUnits (rot θ)) rfl _ h2))
  have e1 : aff y x = aff 1 x * aff y 0 := by rw [aff_mul]; simp
  convert h3 using 1
  simp only [b, hh, e1, mul_assoc, map_mul, Subgroup.coe_mul, map_inv]
  rw [TR.infGL_comm]
  simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HolCuspFin
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.GlobalFixedVectors UpperTheory.V.Sd

namespace UpperTheory.V.Br.HolomorphicCuspFiniteness

private theorem exists_rep {K ι A : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [Finite ι] (e : ι → K) (r : A → K)
    (χ : A → ℂ) (h : ∀ x, ∃ i a, x = e i * r a) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W) (ρ : Representation ℂ K W),
      GlobalTheory.Published.AutFin.IsContRep ρ ∧
        ∀ f : K → ℂ, Continuous f → (∀ x a, f (x * r a) = χ a * f x) → f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := _root_.UpperTheory.Esk.HFinCAux.exists_rep (K := K) (ι := ι) (A := A) e r χ h

variable {F : Type} [Field F] [NumberField F]

private theorem local_mem_principal_congruence {M : ℕ} (w : HeightOneSpectrum (𝓞 F)) (c : ℕ)
    (hM : (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)
    {k : GL (Fin 2) (Af F)} (hk : k ∈ KLev F 2 M) : GeneralLinearGroup.map (pLoc F w) k ∈ K1 w c := by
  obtain ⟨g, hg, rfl⟩ := hk
  let p : Ohat F →+* w.adicCompletionIntegers F :=
    ((pLoc F w).comp (Ohat F).subtype).codRestrict (w.adicCompletionIntegers F) fun x => GlobalFixedVectors.mem_Ohat.1 x.2 w
  refine ⟨GeneralLinearGroup.map p g, ?_, Units.ext rfl⟩
  have key : GeneralLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)) (GeneralLinearGroup.map p g) = 1 := by
    let q := Ideal.quotientMap (I := Ideal.span {(M : ↥(Ohat F))}) (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c) p
      ((Ideal.span_singleton_le_iff_mem _).2 (by simpa using hM))
    have := congrArg (GeneralLinearGroup.map q) (MonoidHom.mem_ker.1 hg)
    rw [map_one] at this
    rw [← this]
    rfl
  exact Subgroup.mem_comap.2 (key ▸ one_mem _)

private theorem exists_level (c : HeightOneSpectrum (𝓞 F) → ℕ) (hc : {w | c w ≠ 0}.Finite) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c w := _root_.UpperTheory.Esk.HFinCAux.exists_level c hc

private theorem fixed_KLev {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (Af F)) V) {M : ℕ} (v : V)
    (ho : IsOpen {k | ρ k v = v}) (h : ∀ w, ∀ k ∈ KLev F 2 M, ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) v = v) :
    ∀ k ∈ KLev F 2 M, ρ k v = v := _root_.UpperTheory.Esk.HFinCAux.fixed_KLev (V := V) (M := M) ρ v ho h

private noncomputable def rot (θ : TR.Rinf F) : TR.Kinf F 2 :=
  ⟨!![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq (θ v)]⟩

private noncomputable def eps (s : InfinitePlace F → ℤˣ) : TR.Kinf F 2 :=
  ⟨!![1, 0; 0, fun v => ((s v : ℤ) : ℝ)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
    rcases Int.units_eq_one_or (s v) with h | h <;> simp [h]⟩

private theorem real_dec {a b c d : ℝ} (h1 : a * a + b * b = 1) (h2 : a * c + b * d = 0) (h3 : c * c + d * d = 1) :
    ∃ (s : ℤˣ) (t : ℝ), a = Real.cos t ∧ b = Real.sin t ∧ c = -((s : ℤ) * Real.sin t) ∧ d = (s : ℤ) * Real.cos t := by
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, h1, Real.sqrt_one]
  have h0 : (⟨a, b⟩ : ℂ) ≠ 0 := fun h => by simp [h] at hn
  have ha : a = Real.cos (Complex.arg ⟨a, b⟩) := by rw [Complex.cos_arg h0, hn, div_one]
  have hb : b = Real.sin (Complex.arg ⟨a, b⟩) := by rw [Complex.sin_arg, hn, div_one]
  have hc : c = -((a * d - b * c) * b) := by linear_combination (-c) * h1 + a * h2
  have hd : d = (a * d - b * c) * a := by linear_combination (-d) * h1 + b * h2
  have hs : (a * d - b * c) * (a * d - b * c) = 1 := by
    linear_combination (c * c + d * d) * h1 + h3 - (a * c + b * d) * h2
  rcases mul_self_eq_one_iff.1 hs with h | h
  · exact ⟨1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩
  · exact ⟨-1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩

omit [NumberField F] in
private theorem dec (x : TR.Kinf F 2) : ∃ s θ, x = eps s * rot θ := by
  have h := Matrix.mem_unitaryGroup_iff.1 x.2
  have e : ∀ i j v, x.1 i 0 v * x.1 j 0 v + x.1 i 1 v * x.1 j 1 v = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j v := fun i j v => by
    rw [← h]; simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
  choose s θ h1 h2 h3 h4 using fun v => real_dec (a := x.1 0 0 v) (b := x.1 0 1 v) (c := x.1 1 0 v) (d := x.1 1 1 v)
    (by simpa using e 0 0 v) (by simpa using e 0 1 v) (by simpa using e 1 1 v)
  refine ⟨s, θ, ?_⟩
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, eps, Matrix.mul_apply, Fin.sum_univ_succ, h1, h2, h3, h4]

variable [IsTotallyReal F]

private theorem cont (φ : TR.Sm F 2) (g : GA F 2) : Continuous fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g := by
  have e : (fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g) = fun k : TR.Kinf F 2 => TR.chart φ.1 g (TR.toL k.1) :=
    funext fun k => (TR.chart_val φ.1 g (Unitary.toUnits k)).symm
  rw [e]
  exact (φ.2 g).continuousOn.comp_continuous continuous_subtype_val fun k => TR.val_mem_invSet (Unitary.toUnits k)

end UpperTheory.V.Br.HolomorphicCuspFiniteness

open UpperTheory.V.Br.HolomorphicCuspFiniteness in
theorem UpperTheory.V.Br.holCuspFin : UpperTheory.V.Br.HolCuspFin := by
  intro F _ _ _ k c hc ω hω
  obtain ⟨M, hM1, hM⟩ := exists_level c hc
  have hlev : ∀ φ : TR.Sm F 2, IsHol k c ω φ → ∀ u ∈ KLev F 2 M, TR.finRep F 2 u φ = φ := fun φ hφ =>
    fixed_KLev _ φ hφ.aut.level fun w u hu => hφ.level w _ (local_mem_principal_congruence w _ (hM w) hu)
  refine ⟨⟨M, hM1, hlev⟩, ?_⟩
  obtain ⟨W, _, _, _, ρ, hρ, hf⟩ := exists_rep (eps (F := F)) (rot (F := F))
    (fun θ => Complex.exp (Complex.I * k * ∑ v, (θ v : ℂ))) dec
  haveI := cuspFormsFiniteReal F 2 (KLev F 2 M) (isOpen_KLev hM1) W ρ hρ
    fun _ u => (u + ((k : ℂ) - 1) / 2) * (u - ((k : ℂ) - 1) / 2)
  refine Submodule.finiteDimensional_of_le (S₂ := _) (Submodule.span_mono (fun φ hφ => ?_) : _ ≤ Submodule.span ℂ
    {φ : TR.Sm F 2 | TR.IsCuspForm φ ∧ (∀ k ∈ KLev F 2 M, TR.finRep F 2 k φ = φ) ∧
      (∀ g : GA F 2, (fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
      ∀ v u, TR.cap v u φ = ((u + ((k : ℂ) - 1) / 2) * (u - ((k : ℂ) - 1) / 2)) • φ})
  have hφ' : IsHol k c ω φ := hφ.1
  refine ⟨hφ.2, hlev φ hφ', fun g => hf _ (cont φ g) fun x θ => ?_, (holCap F k c ω hω φ hφ').2⟩
  have := UpperTheory.V.Br.rotEig F φ _ hφ'.wt θ (Unitary.toUnits (rot θ)) rfl (g * TR.infGL F 2 (Unitary.toUnits x))
  rw [mul_assoc, ← map_mul, ← map_mul] at this
  exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CtMoves
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Eis

namespace UpperTheory.V.Br

section Aff
variable {R : Type} [CommRing R]

private theorem cm_aff_mul (y y' : Rˣ) (x x' : R) : aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem cm_aff_one : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

private theorem cm_scalar_comm (y : Rˣ) (g : GL (Fin 2) R) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) y = Matrix.GeneralLinearGroup.scalar (Fin 2) y * g := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_comm]

end Aff

private theorem cm_ode {f : ℝ → ℂ} {κ : ℂ} (h : ∀ t, HasDerivAt f (κ * f t) t) : f 1 = Complex.exp κ * f 0 := by
  have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-κ * t) * f t) 0 t := fun t => by
    have := (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-κ)).cexp).mul (h t)
    refine this.congr_deriv ?_
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one]; ring
  have h2 := is_const_of_deriv_eq_zero (fun t => (h1 t).differentiableAt) (fun t => (h1 t).deriv) 1 0
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h2
  rw [← h2, ← mul_assoc, ← Complex.exp_add]; simp

variable {F : Type} [Field F] [NumberField F]

private theorem cm_scal [MeasurableSpace (NA F)] (μ : Measure (NA F)) (D : Set (NA F)) (φ : GA F 2 → ℂ) {k : GA F 2} {z : ℂ}
    (hk : ∀ g, φ (g * k) = z * φ g) (g : GA F 2) (hg : cterm μ D φ g = 0) : cterm μ D φ (g * k) = 0 := by
  unfold cterm at hg ⊢
  simp only [← mul_assoc, hk]
  rw [integral_const_mul, hg, mul_zero]

variable [IsTotallyReal F]

private theorem cm_arch {ψ : GA F 2 → ℂ} {k : ℕ} (h : ∀ (u : TR.Rinf F) (y : ℝ → (TR.Rinf F)ˣ),
    (∀ t v, (y t).val v = Real.exp (t * u v)) → ∀ g,
    HasDerivAt (fun t => ψ (TR.infGL F 2 (aff (y t) 0) * g)) ((k : ℂ) / 2 * ((∑ v, u v : ℝ) : ℂ) * ψ g) 0)
    (y : (TR.Rinf F)ˣ) (hy : ∀ v, 0 < y.val v) (g : GA F 2) (hg : ψ g = 0) :
    ψ (TR.infGL F 2 (aff y 0) * g) = 0 := by
  let u : TR.Rinf F := fun v => Real.log (y.val v)
  let z : ℝ → (TR.Rinf F)ˣ := fun t => ⟨fun v => Real.exp (t * u v), fun v => Real.exp (-(t * u v)),
    by funext v; simp [← Real.exp_add], by funext v; simp [← Real.exp_add]⟩
  have hz : ∀ s t, z (s + t) = z s * z t := fun s t => Units.ext (funext fun v => by simp [z, add_mul, Real.exp_add])
  have h0 : z 0 = 1 := Units.ext (funext fun v => by simp [z])
  have h1 : z 1 = y := Units.ext (funext fun v => by simp [z, u, Real.exp_log (hy v)])
  have := cm_ode (f := fun t => ψ (TR.infGL F 2 (aff (z t) 0) * g)) (κ := (k : ℂ) / 2 * ((∑ v, u v : ℝ) : ℂ)) fun t => by
    have h2 := h u z (fun _ _ => rfl) (TR.infGL F 2 (aff (z t) 0) * g)
    have h3 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h2)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    beta_reduce
    rw [← mul_assoc, ← map_mul, cm_aff_mul, ← hz]; simp
  rw [h1, h0, cm_aff_one, map_one, one_mul, hg, mul_zero] at this
  exact this

end UpperTheory.V.Br

theorem UpperTheory.V.Br.ctMoves :
    UpperTheory.V.Br.CtMoves := by
  intro F _ _ _ _ _ μ _ D hD k c ω hω φ hφ M hM
  have hB := UpperTheory.eisenstein_constantTerm_of_periodMean_of_upperBlock UpperTheory.periodic_integral_fundamentalDomain_invariant UpperTheory.eisenstein_constantTerm_upperBlock
  have hL := UpperTheory.eisenstein_continuous_left_action UpperTheory.eisenstein_smooth_continuous hB (UpperTheory.constant_term_automorphy UpperTheory.eisenstein_smooth_continuous UpperTheory.periodic_integral_fundamentalDomain_invariant UpperTheory.eisenstein_period_derivative UpperTheory.eisenstein_constantTerm_upperBlock)
    UpperTheory.eisenstein_lie_algebra_action UpperTheory.eisenstein_central_lie_action
  obtain ⟨-, hN, hT⟩ := hB F μ D hD φ.1 (UpperTheory.eisenstein_smooth_continuous F 2 φ hφ.aut.level) hφ.aut.left
  refine ⟨fun x g hg => (hN x g).trans hg, fun a g hg => (hT a g).trans hg,
    fun y hy g hg => cm_arch (hL F μ D hD k c ω hω φ hφ) y hy g hg, fun z g hg => ?_, fun u hu g hg => ?_, fun θ h hh g hg => ?_⟩
  · rw [← cm_scalar_comm]
    exact cm_scal μ D φ.1 (fun g => by rw [cm_scalar_comm, hφ.cent]) g hg
  · exact cm_scal μ D φ.1 (z := 1) (fun g => by rw [one_mul]; exact congrFun (congrArg Subtype.val (hM u hu)) g) g hg
  · exact cm_scal μ D φ.1 (rotEig F φ _ hφ.wt θ h hh) g hg
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CoRatAff
open NumberField MeasureTheory GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Sd UpperTheory.V.Sd.Eis

private theorem co_aff_mul {R : Type} [CommRing R] (y y' : Rˣ) (x x' : R) :
    aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem co_rat_aff (F : Type) [Field F] [NumberField F] (a : Fˣ) (y : F) :
    ratGL F 2 (aff a y) =
      aff (Units.map (algebraMap F (Ad F)).toMonoidHom a) (algebraMap F (Ad F) y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, ratGL]

theorem UpperTheory.V.Br.ctOne :
    UpperTheory.V.Br.CtOne := by
  intro F _ _
  obtain ⟨h1, h2, h3, h4, -, -, hx⟩ := UpperTheory.eisenstein_constantTerm_upperBlock F
  letI iM : MeasurableSpace (UPos 2 1 → AdeleRing (𝓞 F) F) := MeasurableSpace.pi
  have hμ : (unipMeasure F 2 1).IsAddHaarMeasure := inferInstance
  have hB : BorelSpace (UPos 2 1 → AdeleRing (𝓞 F) F) := Pi.borelSpace
  have hL : ratN F 2 1 = unipLattice F 2 1 := AddSubgroup.ext fun x =>
    ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩
  have hF : IsAddFundamentalDomain (ratN F 2 1) (unipFundamentalDomain F 2 1) (unipMeasure F 2 1) := by
    rw [hL]; exact isAddFundamentalDomain_unipFundamentalDomain
  have main : ∀ [MeasurableSpace (NA F)] [BorelSpace (NA F)] (ν : Measure (NA F)) [ν.IsAddHaarMeasure] (D₀ : Set (NA F)),
      IsAddFundamentalDomain (ratN F 2 1) D₀ ν → ∀ φ : GA F 2 → ℂ, (∀ γ g, φ (ratGL F 2 γ * g) = φ g) →
      (∀ g, cterm ν D₀ φ g = 0) → GlobalTheory.CuspRep.IsCuspidal φ := by
    intro j1 j2 ν _ D₀ hD₀ φ hl h0 r hr0 hr1 i1 i2 μ D hμ' hD g
    obtain rfl : r = 1 := by omega
    obtain rfl : i1 = j1 :=
      (@BorelSpace.measurable_eq _ _ i1 i2).trans (@BorelSpace.measurable_eq _ _ j1 j2).symm
    have hper : ∀ γ ∈ ratN F 2 1, ∀ x : NA F, φ (unip (γ + x) * g) = φ (unip x * g) := by
      rintro _ ⟨y, rfl⟩ x
      rw [hx, hx x]
      refine Eq.trans ?_ (hl (aff 1 (y ⟨(0, 1), by decide⟩)) _)
      rw [← mul_assoc, co_rat_aff, co_aff_mul, map_one, one_mul, Units.val_one, one_mul, add_comm (x _)]
      rfl
    have hD' : IsAddFundamentalDomain (ratN F 2 1) D ν := hD.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
    have h : ∫ x in D, φ (unip x * g) ∂ν = 0 :=
      (hD'.setIntegral_eq hD₀ (f := fun x => φ (unip x * g)) fun γ x => hper γ γ.2 x).trans (h0 g)
    rw [Measure.isAddLeftInvariant_eq_smul μ ν, Measure.restrict_smul, integral_smul_nnreal_measure, h, smul_zero]
  exact ⟨iM, hB, unipMeasure F 2 1, hμ, unipFundamentalDomain F 2 1, hF, @main iM hB _ hμ _ hF⟩
end

open NumberField IsDedekindDomain MeasureTheory Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Eis

private theorem fin_of_ker {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Finite ι] (P Q : Set V) (h0 : (0 : V) ∈ P)
    (hP : ∀ x y (z : ℂ), x ∈ P → y ∈ P → x + z • y ∈ P) (hQ : FiniteDimensional ℂ (Submodule.span ℂ Q)) (L : V → ι → ℂ)
    (hL0 : L 0 = 0) (hL : ∀ x y (z : ℂ), x ∈ P → y ∈ P → L (x + z • y) = L x + z • L y) (hk : ∀ x ∈ P, L x = 0 → x ∈ Q) :
    FiniteDimensional ℂ (Submodule.span ℂ P) := by
  let W : Submodule ℂ V :=
    { carrier := P
      zero_mem' := h0
      add_mem' := fun {x y} hx hy => by simpa using hP x y 1 hx hy
      smul_mem' := fun z y hy => by simpa using hP 0 y z h0 hy }
  have hW : Submodule.span ℂ P = W := Submodule.span_eq W
  rw [hW]
  let f : W →ₗ[ℂ] (ι → ℂ) :=
    { toFun := fun x => L x.1
      map_add' := fun x y => by simpa using hL x.1 y.1 1 x.2 y.2
      map_smul' := fun z y => by simpa [hL0] using hL 0 y.1 z h0 y.2 }
  let j : LinearMap.ker f →ₗ[ℂ] Submodule.span ℂ Q :=
    LinearMap.codRestrict _ (W.subtype.comp (LinearMap.ker f).subtype) fun x =>
      Submodule.subset_span (hk _ x.1.2 x.2)
  have hj : Function.Injective j := fun x y h => by
    have e := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext e)
  haveI : Module.Finite ℂ (LinearMap.ker f) := Module.Finite.of_injective j hj
  haveI : Module.Finite ℂ (W ⧸ LinearMap.ker f) := Module.Finite.equiv f.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker f)

theorem UpperTheory.V.Br.holFin0 :
    UpperTheory.V.Sd.HolFin := by
  intro F _ _ _ k c hc ω hω
  obtain ⟨⟨M, hM, hlev⟩, hfin⟩ := UpperTheory.V.Br.holCuspFin F k c hc ω hω
  obtain ⟨S, hS, hgen⟩ := UpperTheory.V.Br.cuspSet F M hM
  obtain ⟨_, _, μ, _, D, hD, hone⟩ := UpperTheory.V.Br.ctOne F
  obtain ⟨h0, -, hadd, -⟩ := UpperTheory.V.Sd.holLin F k c ω
  have hint : ∀ φ : TR.Sm F 2, IsHol k c ω φ → ∀ g, IntegrableOn (fun x : NA F => φ.1 (unip x * g)) D μ := fun φ hφ =>
    (UpperTheory.eisenstein_constantTerm_of_periodMean_of_upperBlock UpperTheory.periodic_integral_fundamentalDomain_invariant UpperTheory.eisenstein_constantTerm_upperBlock F μ D hD φ.1 (UpperTheory.eisenstein_smooth_continuous F 2 φ hφ.aut.level) hφ.aut.left).1
  haveI : Finite S := hS
  refine fin_of_ker _ _ h0 hadd hfin (fun φ (s : S) => cterm μ D φ.1 s.1) ?_ (fun φ ψ z hφ hψ => ?_) fun φ hφ h => ?_
  · funext s
    simp [cterm]
  · funext s
    simp only [cterm, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add (hint φ hφ s.1) ((hint ψ hψ s.1).const_mul z), integral_const_mul]
  · have hu := hgen {g | cterm μ D φ.1 g = 0} (fun s hs => congrFun h ⟨s, hs⟩)
      (UpperTheory.V.Br.ctMoves F μ D hD k c ω hω φ hφ M (hlev φ hφ))
    exact ⟨hφ, hφ.aut, hone φ.1 hφ.aut.left fun g => (hu.ge (Set.mem_univ g) :)⟩
