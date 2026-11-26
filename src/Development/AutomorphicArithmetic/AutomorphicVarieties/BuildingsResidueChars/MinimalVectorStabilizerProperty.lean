module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Nearvec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AcycSimp

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MinimalVectorStabilizerProperty
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped Pointwise

theorem UpperTheory.minimal_vector_stabilizer_property :
    UpperTheory.V.Af.BA.MinStab := by
  intro L _ _ _ N h hv hsp
  classical
  have hfin : (minVec h).Finite := by
    obtain ⟨S, hS, hev⟩ := locfin L N h (rypos L N hv) 1
    refine hS.subset fun y hy => ?_
    by_contra hn
    exact (hev.self_of_nhds y hn).ne' hy
  obtain ⟨A, hA, hcol⟩ := exbasis L N _ hsp
  haveI : Finite (minVec h) := hfin.to_subtype
  have hmem : ∀ (g : MulAction.stabilizer (Gm L N) (minVec h)) (a : Fin N),
      (g.1 • (fun i => A i a : Lat L N)) ∈ minVec h := fun g a => by
    have h1 : g.1 • minVec h = minVec h := g.2
    have h2 := Set.smul_mem_smul_set (a := g.1) (hcol a)
    rw [h1] at h2
    exact h2
  refine Finite.of_injective
    (fun (g : MulAction.stabilizer (Gm L N) (minVec h)) (a : Fin N) =>
      (⟨_, hmem g a⟩ : minVec h)) fun g k e => ?_
  have h1 : (g.1 : Matrix (Fin N) (Fin N) (𝓞 L)) * A =
      (k.1 : Matrix (Fin N) (Fin N) (𝓞 L)) * A := by
    refine Matrix.ext fun i a => ?_
    exact congrFun (congrArg Subtype.val (congrFun e a)) i
  have h2 := congrArg (· * A.adjugate) h1
  simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h2
  refine Subtype.ext (Units.ext ?_)
  refine Matrix.ext fun i j => ?_
  exact mul_left_cancel₀ hA (congrFun (congrFun h2 i) j)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PermutationModuleHomologyRank
open CategoryTheory UpperTheory.V.Af.BA in
theorem UpperTheory.permutation_module_homology_rank :
    UpperTheory.V.Af.BA.RankHomPerm := by
  intro Γ X _ _ h
  obtain ⟨R, hR, hRx⟩ := h
  haveI := hR.fintype
  refine ⟨Fintype.card R, fun A => ?_⟩
  let Φ : (PC Γ X ⟶ A) →ₗ[ℂ] (R → A) :=
    { toFun := fun φ r => φ.hom (Finsupp.single (r : X) 1)
      map_add' := fun φ ψ => by
        ext r
        rfl
      map_smul' := fun c φ => by
        ext r
        rfl }
  have key : ∀ (χ : PC Γ X ⟶ A) (g : Γ) (x : X),
      χ.hom (Finsupp.single x 1) = A.ρ g⁻¹ (χ.hom (Finsupp.single (g • x) 1)) := by
    intro χ g x
    rw [← Rep.hom_comm_apply]
    congr 1
    show _ = permC Γ X g⁻¹ (Finsupp.single (g • x) 1)
    rw [permC_single, inv_smul_smul]
  have hinj : Function.Injective Φ := by
    intro φ ψ hφψ
    apply PC_ext
    intro x
    obtain ⟨g, hg⟩ := hRx x
    have h1 := congrFun hφψ ⟨g • x, hg⟩
    rw [key φ g x, key ψ g x]
    exact congrArg _ h1
  calc Module.rank ℂ (PC Γ X ⟶ A) ≤ Module.rank ℂ (R → A) := Φ.rank_le_of_injective hinj
    _ = _ := by rw [rank_fun_eq_lift_mul, Cardinal.lift_id]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MinimalOrbitRepresentatives
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped Pointwise

theorem UpperTheory.minimal_orbit_representatives :
    UpperTheory.V.Af.BA.MinOrb := by
  intro L _ _ _ N p
  classical
  obtain ⟨S, -, hS⟩ := hnf L N (I0 L N)
  refine ⟨⋃ B ∈ {B | B ∈ S ∧ B.det ≠ 0}, Set.pi Set.univ (fun _ => (nearVec B).powerset), ?_, ?_⟩
  · refine Set.Finite.biUnion ?_ ?_
    · exact S.finite_toSet.subset (fun B hB => hB.1)
    · intro B hB
      exact Set.Finite.pi (fun _ => (nearvec L N B hB.2).1.powerset)
  · intro h hR hsp
    obtain ⟨A, hA, hcol⟩ := exbasis L N _ hsp
    have hcm : ∀ j, ColsMin A (h j) := fun j a => hcol a j
    obtain ⟨g, hg⟩ := hS A hA (nrmle L N (h 0) A (hR 0) (hcm 0) hA).1
    have hdet : ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A).det ≠ 0 := by
      rw [Matrix.det_mul]
      exact mul_ne_zero (Matrix.isUnits_det_units g).ne_zero hA
    refine ⟨g, ?_⟩
    rw [Set.mem_iUnion₂]
    refine ⟨(g : Matrix (Fin N) (Fin N) (𝓞 L)) * A, ⟨hg, hdet⟩, ?_⟩
    intro j _
    rintro y ⟨x, hx, rfl⟩
    refine ⟨g • h j, smul_mem_Ry g (hR j), fun a => ?_, ?_⟩
    · have hc : (fun i => ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A) i a) = g • (fun i => A i a) := by
        funext i
        rfl
      rw [hc, q_smul, inv_smul_smul]
      exact hcm j a
    · rw [q_smul]
      change q (h j) (g⁻¹ • g • x) = 1
      rw [inv_smul_smul]
      exact hx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExtVanishingOfResolutionEndo
open CategoryTheory Limits in
private theorem homologyMap_zero_of_f {C : Type*} [Category C] [Abelian C] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (Ψ : K ⟶ L) (q : ι) (h : Ψ.f q = 0) :
    HomologicalComplex.homologyMap Ψ q = 0 := by
  have h1 : HomologicalComplex.cyclesMap Ψ q = 0 := by
    rw [← cancel_mono (L.iCycles q), zero_comp, HomologicalComplex.cyclesMap_i, h, comp_zero]
  rw [← cancel_epi (K.homologyπ q), comp_zero, HomologicalComplex.homologyπ_naturality, h1, zero_comp]

open CategoryTheory Limits in
private theorem isZero_yoneda {R : Type*} [Ring R] {C : Type*} [Category C] [Abelian C]
    [Linear R C] {X : C} (Y : C) (P : ProjectiveResolution X) (e : P.complex ⟶ P.complex)
    (he : e ≫ P.π = P.π) (q : ℕ) (hq : e.f q = 0) :
    IsZero ((P.complex.linearYonedaObj R Y).homology q) := by
  let F := ((linearYoneda R C).obj Y).rightOp
  have h1 : Homotopy e (𝟙 P.complex) :=
    ProjectiveResolution.liftHomotopy (𝟙 X) e (𝟙 _) (by simpa using he) (by simp)
  have h2 := (F.mapHomotopy h1).unop
  have h3 := h2.homologyMap_eq q
  have hz : ((HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map e).op).f q = 0 := by
    show (F.map (e.f q)).unop = 0
    rw [hq, F.map_zero]
    rfl
  rw [homologyMap_zero_of_f _ q hz] at h3
  simp only [CategoryTheory.Functor.map_id, op_id, HomologicalComplex.homologyMap_id] at h3
  rw [IsZero.iff_id_eq_zero]
  exact h3.symm

open CategoryTheory Limits in
theorem UpperTheory.ext_vanishing_of_resolution_endo :
    UpperTheory.V.Af.BA.VanishOf := by
  intro Γ _ P e he q hq A
  have h2 : IsZero (groupCohomology A q) :=
    (isZero_yoneda (R := ℂ) A P e he q hq).of_iso (groupCohomologyIso A q P)
  haveI := ModuleCat.subsingleton_of_isZero h2
  exact rank_subsingleton' ℂ _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExactBaseIntegralToComplex
open TensorProduct

private theorem ladder {X Y : Type} [DecidableEq X] [DecidableEq Y] (f : (X →₀ ℤ) →ₗ[ℤ] (Y →₀ ℤ)) (f' : (X →₀ ℂ) →ₗ[ℂ] (Y →₀ ℂ))
    (h : ∀ x y, f' (Finsupp.single x 1) y = (f (Finsupp.single x 1) y : ℤ)) (u : ℂ ⊗[ℤ] (X →₀ ℤ)) :
    f' (TensorProduct.finsuppScalarRight ℤ ℤ ℂ X u) = TensorProduct.finsuppScalarRight ℤ ℤ ℂ Y (f.lTensor ℂ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul c v =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
    | single x n =>
      have e1 : TensorProduct.finsuppScalarRight ℤ ℤ ℂ X (c ⊗ₜ[ℤ] Finsupp.single x n)
          = ((n : ℂ) * c) • Finsupp.single x (1 : ℂ) := by
        ext x'
        rw [TensorProduct.finsuppScalarRight_apply_tmul_apply]
        by_cases hx : x = x'
        · subst hx; simp
        · simp [Finsupp.single_apply, hx]
      have e2 : Finsupp.single x n = n • Finsupp.single x (1 : ℤ) := by simp
      ext y
      rw [e1, map_smul, LinearMap.lTensor_tmul, TensorProduct.finsuppScalarRight_apply_tmul_apply, e2, map_smul,
        Finsupp.smul_apply, Finsupp.smul_apply, h]
      simp only [smul_eq_mul, zsmul_eq_mul, Int.cast_mul]
      push_cast
      ring

theorem UpperTheory.exactBase_integral_to_complex :
    UpperTheory.V.Af.BA.ExactBase := by
  intro X Y Z f g f' g' hf hg hfg
  classical
  have hex := Module.Flat.lTensor_exact ℂ hfg
  refine Function.Exact.of_ladder_addEquiv_of_exact
    (TensorProduct.finsuppScalarRight ℤ ℤ ℂ X).toAddEquiv
    (TensorProduct.finsuppScalarRight ℤ ℤ ℂ Y).toAddEquiv
    (TensorProduct.finsuppScalarRight ℤ ℤ ℂ Z).toAddEquiv
    (f₁₂ := (f.lTensor ℂ).toAddMonoidHom) (f₂₃ := (g.lTensor ℂ).toAddMonoidHom)
    (g₁₂ := f'.toAddMonoidHom) (g₂₃ := g'.toAddMonoidHom) ?_ ?_ hex
  · exact AddMonoidHom.ext fun u => ladder f f' hf u
  · exact AddMonoidHom.ext fun u => ladder g g' hg u
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AltChainOfPermSplit
open CategoryTheory

theorem UpperTheory.altChain_of_permSplit :
    UpperTheory.V.Af.BA.PermSplit → UpperTheory.V.Af.BA.AltChain := by
  intro hP Γ I _ _ K p
  simp only [UpperTheory.V.Af.BA.Cx.alt, UpperTheory.V.Af.BA.Cx.d, Linear.smul_comp, Linear.comp_smul,
    Preadditive.sum_comp, Preadditive.comp_sum, UpperTheory.V.Af.BA.Cx.reC_comp]
  simp only [Finset.smul_sum, smul_smul]
  set c : ℂ := ((p + 1 + 1).factorial : ℂ)⁻¹ with hc
  have hx : ∀ x : Fin (p + 2),
      ∑ σ : Equiv.Perm (Fin (p + 2)),
        ((-1 : ℂ) ^ (x : ℕ) * (c * (((Equiv.Perm.sign σ : ℤ)) : ℂ))) • K.reC (σ ∘ x.succAbove) =
      ∑ q : Fin (p + 2) × Equiv.Perm (Fin (p + 1)),
        (c * ((-1 : ℂ) ^ (q.1 : ℕ) * ((Equiv.Perm.sign q.2 : ℤ) : ℂ))) • K.reC (q.1.succAbove ∘ q.2) := by
    intro x
    obtain ⟨e, he⟩ := hP (p + 1) x
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl ?_
    rintro ⟨i, τ⟩ -
    obtain ⟨hs, hk⟩ := he i τ
    have hf : (e (i, τ) : Fin (p + 2) → Fin (p + 2)) ∘ x.succAbove = i.succAbove ∘ τ := funext hk
    rw [hf, hs]
    congr 1
    push_cast
    have h1 : (-1 : ℂ) ^ (x : ℕ) * (-1 : ℂ) ^ (x : ℕ) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      simp
    linear_combination (c * (-1 : ℂ) ^ (i : ℕ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) * h1
  rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  conv_rhs => rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨i, τ⟩ -
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  have hF : ((p + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hP2 : ((p : ℂ) + 2) ≠ 0 := by exact_mod_cast (by omega : p + 2 ≠ 0)
  rw [hc, Nat.factorial_succ (p + 1)]
  push_cast
  field_simp
  ring_nf
  have h2 : (2 + (p : ℂ)) ≠ 0 := by rwa [add_comm]
  field_simp
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRealPartInvariant
open NumberField Matrix UpperTheory.V.KT UpperTheory.V.Af.BA in
theorem UpperTheory.adelic_realPart_invariant :
    UpperTheory.V.Af.BA.ReInv := by
  intro L _ _ N σ hσ
  refine ⟨fun x => ?_, fun h hh => ⟨fun y => ?_, fun g hg => ?_⟩⟩
  · obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
    have e : embO w (σ (σ x)) = embO w x := by rw [hσ, hσ]; simp
    apply RingOfIntegers.coe_injective
    exact w.embedding.injective (by simpa [embO] using e)
  · have hz : ∀ w i, toR (sLat σ y) w i = star (toR y w i) := fun w i => hσ w (y i)
    simp only [q, qR]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum, hz]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have him : ((mat h w) i j).im = 0 := hh w i j
    simp only [Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, him]
    ring
  · have hfix : ∀ i j, σ ((↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)) i j)
        = (↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)) i j := fun i j => by
      have := congrArg (fun u : Gm L N => (u : Matrix (Fin N) (Fin N) (𝓞 L)) i j)
        (mem_Fix.mp (inv_mem hg))
      exact this
    intro w i j
    have hs : g • h = pull (↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)) h := rfl
    show ((mat (g • h) w) i j).im = 0
    rw [hs, mat_pull]
    set B := (↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) with hBdef
    have hB : B.map (starRingEnd ℂ) = B := by
      ext a b
      simp only [hBdef, Matrix.map_apply]
      rw [← hσ w, hfix]
    have hM : (mat h w).map (starRingEnd ℂ) = mat h w := by
      ext a b
      simp only [Matrix.map_apply]
      exact Complex.conj_eq_iff_im.mpr (hh w a b)
    have hBt : Bᴴ.map (starRingEnd ℂ) = Bᴴ := by
      ext a b
      have := congrFun (congrFun hB b) a
      simp only [Matrix.map_apply, Matrix.conjTranspose_apply] at this ⊢
      simp only [Complex.star_def, Complex.conj_conj]
      exact this.symm
    have hP : (Bᴴ * mat h w * B).map (starRingEnd ℂ) = Bᴴ * mat h w * B := by
      rw [Matrix.map_mul, Matrix.map_mul, hBt, hM, hB]
    have := congrFun (congrFun hP i) j
    simp only [Matrix.map_apply] at this
    exact Complex.conj_eq_iff_im.mp this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PermSplitFinSucc
private theorem cycle_range_conjugate_succAbove {n : ℕ} (i j : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) (k : Fin n) :
    ((Fin.cycleRange i)⁻¹ * Equiv.Perm.decomposeFin.symm (0, τ) * Fin.cycleRange j : Equiv.Perm (Fin (n + 1)))
      (j.succAbove k) = i.succAbove (τ k) := by
  simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Fin.cycleRange_succAbove,
    Equiv.Perm.decomposeFin_symm_apply_succ, Fin.cycleRange_symm_succ]

private theorem cycle_range_conjugate_pivot {n : ℕ} (i j : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    ((Fin.cycleRange i)⁻¹ * Equiv.Perm.decomposeFin.symm (0, τ) * Fin.cycleRange j : Equiv.Perm (Fin (n + 1)))
      j = i := by
  simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Fin.cycleRange_self,
    Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]

theorem UpperTheory.perm_split_fin_succ :
    UpperTheory.V.Af.BA.PermSplit := by
  intro n j
  classical
  let F : Fin (n + 1) × Equiv.Perm (Fin n) → Equiv.Perm (Fin (n + 1)) := fun p =>
    (Fin.cycleRange p.1)⁻¹ * Equiv.Perm.decomposeFin.symm (0, p.2) * Fin.cycleRange j
  have hinj : Function.Injective F := by
    rintro ⟨i, τ⟩ ⟨i', τ'⟩ h
    have hi : i = i' := by
      have h1 := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ j) h
      simp only [F] at h1
      rw [cycle_range_conjugate_pivot, cycle_range_conjugate_pivot] at h1
      exact h1
    subst hi
    simp only [F] at h
    have h2 := Equiv.injective _ (mul_left_cancel (mul_right_cancel h))
    rw [Prod.mk.injEq] at h2
    rw [h2.2]
  have hsurj : Function.Surjective F := by
    intro σ
    have hρ : (Fin.cycleRange (σ j) * σ * (Fin.cycleRange j)⁻¹) 0 = 0 := by
      simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Fin.cycleRange_symm_zero, Fin.cycleRange_self]
    obtain ⟨⟨p, τ⟩, hp⟩ := Equiv.Perm.decomposeFin.symm.surjective
      (Fin.cycleRange (σ j) * σ * (Fin.cycleRange j)⁻¹)
    have hp0 : p = 0 := by
      have h0 := congrArg (fun s : Equiv.Perm (Fin (n + 1)) => s 0) hp
      simp only [Equiv.Perm.decomposeFin_symm_apply_zero] at h0
      rw [h0, hρ]
    subst hp0
    refine ⟨(σ j, τ), ?_⟩
    simp only [F]
    rw [hp]
    group
  refine ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, ?_⟩
  intro i τ
  refine ⟨?_, fun k => cycle_range_conjugate_succAbove i j τ k⟩
  show ((Equiv.Perm.sign (F (i, τ)) : ℤ) : _) = _
  simp only [F, map_mul, map_inv, Fin.sign_cycleRange,
    Equiv.Perm.decomposeFin.symm_sign, if_pos rfl, one_mul, inv_pow, Int.units_inv_eq_self]
  push_cast
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExactCOfOfExactBase
open CategoryTheory UpperTheory.V UpperTheory.V.Af.BA

private theorem hom_sum_apply {Γ : Type} [Group Γ] {A B : Rep.{0} ℂ Γ} {ι : Type} (s : Finset ι)
    (c : ι → ℂ) (f : ι → (A ⟶ B)) (x : A) :
    (∑ i ∈ s, c i • f i).hom x = ∑ i ∈ s, c i • (f i).hom x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Rep.add_hom, Rep.smul_hom]
    simp [ih]

private theorem d_coeff {Γ I : Type} [Group Γ] [MulAction Γ I] (K : Cx Γ I) (p : ℕ)
    (x : K.Tup (p + 1)) (y : K.Tup p) :
    ((K.d p).hom.toLinearMap (Finsupp.single x 1) : K.Tup p →₀ ℂ) y =
      ((KH.faceD (fun (i : Fin (p + 2)) => K.re i.succAbove) (Finsupp.single x 1) y : ℤ) : ℂ) := by
  classical
  show (Rep.Hom.hom (K.d p)) (Finsupp.single x 1) y = _
  simp only [Cx.d]
  rw [hom_sum_apply]
  simp [KH.faceD_single, Finsupp.finsetSum_apply, Finsupp.single_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Cx.reC_single, Finsupp.single_apply]
  split_ifs <;> simp

theorem UpperTheory.exactCOf_of_exactBase :
    UpperTheory.V.Af.BA.ExactBase → UpperTheory.V.Af.BA.ExactCOf := by
  intro hB Γ I _ _ K hZ
  classical
  obtain ⟨hs, he0, -⟩ := hZ 0
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hs 1
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    obtain ⟨t, -⟩ := Finsupp.support_nonempty_iff.2 hv0
    intro c
    exact ⟨Finsupp.single t c, by rw [augC_single]⟩
  · have key := hB (K.Tup 1) (K.Tup 0) Unit _
      ((Finsupp.lsingle ()) ∘ₗ KH.aug (K.Tup 0)) _
      ((Finsupp.lsingle ()) ∘ₗ (Rep.Hom.hom (augC Γ (K.Tup 0))).toLinearMap) (d_coeff K 0) ?_ ?_
    · intro y
      have hy := key y
      simpa [Finsupp.single_eq_zero] using hy
    · intro y z
      simp [KH.aug_single]
      exact augC_single y 1
    · intro y
      have hy := he0 y
      simpa [Finsupp.single_eq_zero] using hy
  · intro p
    exact hB _ _ _ _ _ _ _ (d_coeff K (p + 1)) (d_coeff K p) ((hZ (p + 1)).2.2 p (Nat.lt_succ_self p))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepBoundedOfSubgroupBounded
open CategoryTheory UpperTheory.V.Af.CohB in
theorem UpperTheory.adelic_rep_bounded_of_subgroup_bounded :
    UpperTheory.V.Af.BA.BddSub := by
  classical
  unfold UpperTheory.V.Af.BA.BddSub
  intro G _ S hS hB
  haveI := hS
  unfold UpperTheory.V.Af.CohB.Bdd at hB ⊢
  obtain ⟨c, hc⟩ := hB
  haveI : Finite (Quotient (QuotientGroup.rightRel S)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm
  have hrank : ∀ B : Rep.{0,0,0} ℂ S, Module.rank ℂ ↑(Rep.coind S.subtype B) ≤
      (Nat.card (Quotient (QuotientGroup.rightRel S)) : Cardinal) * Module.rank ℂ ↑B := by
    intro B
    let L : ↥(Representation.coindV S.subtype B.ρ) →ₗ[ℂ]
        (Quotient (QuotientGroup.rightRel S) → ↑B) :=
      { toFun := fun f q => f.1 q.out
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hL : Function.Injective L := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro f hf
      apply Subtype.ext
      funext g
      show f.1 g = 0
      let o : G := (Quotient.mk (QuotientGroup.rightRel S) g).out
      have h1 : Quotient.mk (QuotientGroup.rightRel S) o = Quotient.mk (QuotientGroup.rightRel S) g :=
        Quotient.out_eq _
      have h2 : g * o⁻¹ ∈ S := QuotientGroup.rightRel_apply.mp (Quotient.exact h1)
      let s : S := ⟨g * o⁻¹, h2⟩
      have hfo : f.1 o = 0 := congrFun hf (Quotient.mk (QuotientGroup.rightRel S) g)
      have hso : S.subtype s * o = g := by
        show g * o⁻¹ * o = g
        rw [inv_mul_cancel_right]
      calc f.1 g = f.1 (S.subtype s * o) := by rw [hso]
        _ = B.ρ s (f.1 o) := f.2 s o
        _ = 0 := by rw [hfo, map_zero]
    calc Module.rank ℂ ↑(Rep.coind S.subtype B)
        = Module.rank ℂ ↥(Representation.coindV S.subtype B.ρ) := rfl
      _ ≤ Module.rank ℂ (Quotient (QuotientGroup.rightRel S) → ↑B) :=
        LinearMap.rank_le_of_injective L hL
      _ = Cardinal.mk (Quotient (QuotientGroup.rightRel S)) * Module.rank ℂ ↑B := by
        rw [rank_pi, Cardinal.sum_const']
      _ = (Nat.card (Quotient (QuotientGroup.rightRel S)) : Cardinal) * Module.rank ℂ ↑B := by
        rw [Nat.cast_card]
  refine ⟨c * Nat.card (Quotient (QuotientGroup.rightRel S)), fun B => ?_⟩
  have htot : UpperTheory.V.Af.CohB.totCoh B = UpperTheory.V.Af.CohB.totCoh (Rep.coind S.subtype B) := by
    unfold UpperTheory.V.Af.CohB.totCoh
    congr 1
    funext q
    exact ((groupCohomology.coindIso B q).toLinearEquiv).rank_eq.symm
  rw [htot, Nat.cast_mul, mul_assoc]
  refine (hc _).trans ?_
  gcongr
  exact hrank B
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RepHomAlternatingSumEqZero
open CategoryTheory UpperTheory.V.Af.BA in
private def repHomEvalLinearMap {Γ : Type} [Group Γ] {A B : Rep.{0} ℂ Γ} (x : A) : (A ⟶ B) →ₗ[ℂ] B where
  toFun φ := φ.hom x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open CategoryTheory UpperTheory.V.Af.BA in
theorem UpperTheory.rep_hom_alternating_sum_eq_zero :
    UpperTheory.V.Af.BA.AltZero := by
  intro Γ I _ _ K
  have key : ∀ (p : ℕ) (t : K.Tup p), (K.alt p).hom (Finsupp.single t 1) =
      ((p + 1).factorial : ℂ)⁻¹ • ∑ π : Equiv.Perm (Fin (p + 1)),
        ((Equiv.Perm.sign π : ℤ) : ℂ) • Finsupp.single (K.re π t) (1 : ℂ) := by
    intro p t
    show repHomEvalLinearMap (B := PC Γ (K.Tup p)) (Finsupp.single t (1 : ℂ)) (K.alt p) = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Cx.alt, map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro π _
    congr 1
    exact Cx.reC_single K _ t 1
  refine ⟨?_, ?_⟩
  · apply PC_ext
    intro x
    rw [key 0 x]
    have hre : K.re (id : Fin 1 → Fin 1) x = x := Subtype.ext rfl
    simp [Fintype.sum_unique, hre]
  · intro p hp
    apply PC_ext
    intro t
    rw [key p t]
    have hnt := hp t
    simp only [Function.Injective, not_forall] at hnt
    obtain ⟨a, b, htab, hab⟩ := hnt
    have ht : ∀ y, Subtype.val t (Equiv.swap a b y) = Subtype.val t y := by
      intro y
      rw [Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, htab]
      · rw [h2, htab]
      · rfl
    set S := ∑ π : Equiv.Perm (Fin (p + 1)),
      ((Equiv.Perm.sign π : ℤ) : ℂ) • Finsupp.single (K.re π t) (1 : ℂ) with hSdef
    have hS : S = -S := by
      conv_lhs => rw [hSdef, ← Equiv.sum_comp (Equiv.mulLeft (Equiv.swap a b))]
      rw [hSdef, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro π _
      have hre : K.re (⇑((Equiv.mulLeft (Equiv.swap a b)) π)) t = K.re π t :=
        Subtype.ext (funext fun k => by simp [Cx.re, Equiv.Perm.mul_apply, ht])
      rw [hre, Equiv.coe_mulLeft, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
      push_cast
      rw [neg_one_mul, neg_smul]
    have hS0 : S = 0 := self_eq_neg.1 hS
    rw [hS0, smul_zero]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RepResolutionExists
open CategoryTheory

namespace UpperTheory.V.Af.BA.ResolutionExactness

variable {Γ : Type} [Group Γ]

private theorem comp_zero_of {A B C : Rep.{0} ℂ Γ} {f : A ⟶ B} {g : B ⟶ C}
    (h : Function.Exact f.hom g.hom) : f ≫ g = 0 := by
  ext x
  exact h.apply_apply_eq_zero x

private theorem exact_of {A B C : Rep.{0} ℂ Γ} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0)
    (h : Function.Exact f.hom g.hom) : (ShortComplex.mk f g w).Exact := by
  exact (forget₂ (Rep ℂ Γ) (ModuleCat ℂ)).reflects_exact_of_faithful _
    ((ShortComplex.moduleCat_exact_iff _).2 fun x hx => (h x).1 hx)

set_option backward.isDefEq.respectTransparency false in
private theorem main : UpperTheory.V.Af.BA.ResOf := by
  intro Γ _ X d ε hX hε h0 hd
  have hdd : ∀ p, d (p + 1) ≫ d p = 0 := fun p => comp_zero_of (hd p)
  let K : ChainComplex (Rep ℂ Γ) ℕ := ChainComplex.of X d hdd
  have hK : ∀ j, K.d (j + 1) j = d j := fun j => by simp [K]
  have hK0 : K.d 1 0 ≫ ε = 0 := by
    rw [hK 0]
    exact comp_zero_of h0
  let π : K ⟶ (ChainComplex.single₀ (Rep ℂ Γ)).obj (Rep.trivial ℂ Γ ℂ) :=
    (ChainComplex.toSingle₀Equiv _ _).symm ⟨ε, hK0⟩
  have hπ0 : π.f 0 = ε := by simp [π]
  let P : ProjectiveResolution (Rep.trivial ℂ Γ ℂ) :=
    { complex := K
      projective := hX
      π := π
      quasiIso := ⟨fun n => by
        cases n with
        | zero =>
          rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
          · refine ⟨exact_of _ ?_, ?_⟩
            · show Function.Exact (K.d 1 0).hom (π.f 0).hom
              rw [hπ0, hK 0]
              exact h0
            · show Epi (π.f 0)
              rw [hπ0, Rep.epi_iff_surjective]
              exact hε
          all_goals rfl
        | succ m =>
          rw [quasiIsoAt_iff_exactAt']
          · rw [HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp)]
            refine exact_of _ ?_
            show Function.Exact (K.d (m + 2) (m + 1)).hom (K.d (m + 1) m).hom
            rw [hK, hK]
            exact hd m
          · apply ChainComplex.exactAt_succ_single_obj⟩ }
  refine ⟨P, fun p => ⟨Iso.refl _⟩, fun e he0 he => ?_⟩
  refine ⟨ChainComplex.ofHom (X := K) (Y := K) e (fun i => by rw [hK]; exact he i), ?_, fun p hp => hp⟩
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  ext1
  simp [P, hπ0, he0]

end UpperTheory.V.Af.BA.ResolutionExactness

theorem UpperTheory.repResolution_exists :
    UpperTheory.V.Af.BA.ResOf :=
  UpperTheory.V.Af.BA.ResolutionExactness.main
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BddFixOfBoundedComplex
open UpperTheory.V UpperTheory.V.Af.BA UpperTheory.V.KT Pointwise in
theorem UpperTheory.bddFix_of_bounded_complex :
    UpperTheory.V.Af.BA.BddCx → UpperTheory.V.Af.BA.GoodRe → UpperTheory.V.Af.BA.ActRe → UpperTheory.V.Af.BA.SpanRe → UpperTheory.V.Af.BA.OrbRe → UpperTheory.V.Af.BA.MinStab → UpperTheory.V.Af.BA.BddFix := by
  intro hB hGood hAct hSpan hOrb hMin L _ _ _ N σ hσ
  obtain ⟨x, hx1, hx2⟩ := hAct L N σ hσ
  letI := x
  obtain ⟨hFC, hS0, hA⟩ := UpperTheory.V.ConeExtensionAcyclic.acyc_simp (hGood L N σ hσ)
  let K : Cx (Fix N σ) (UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) :=
    { S := UpperTheory.V.ConeExtensionAcyclic.simp (qr L N) (Tr L N)
      comp := fun f t ht => by
        obtain ⟨z, hz, hzt⟩ := ht
        exact ⟨z, hz, fun j => hzt (f j)⟩
      smul := fun g t ht => hx2 _ g t ht }
  refine hB _ _ K (fun m => UpperTheory.V.KT.faceexact _ _ hFC hS0 hA m) ?_ ?_
  · intro p
    obtain ⟨R, hRf, hR⟩ := hOrb L N σ hσ p
    refine ⟨{t : K.Tup p | (fun j => (((t.1 j : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) : HR L N) : UpperTheory.V.KT.HS L N)) ∈ R}, ?_, ?_⟩
    · refine hRf.preimage ?_
      intro a _ b _ hab
      apply Subtype.ext
      funext j
      exact Subtype.ext (Subtype.ext (congrFun hab j))
    · intro t
      obtain ⟨g, hg, hgR⟩ := hR t.1 t.2
      refine ⟨⟨g, hg⟩, ?_⟩
      have hfun : (fun j => ((((⟨g, hg⟩ : Fix N σ) • t.1 j : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) : HR L N) : UpperTheory.V.KT.HS L N))
          = fun j => g • (((t.1 j : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) : HR L N) : UpperTheory.V.KT.HS L N) :=
        funext fun j => hx1 _ _
      show (fun j => ((((⟨g, hg⟩ : Fix N σ) • t.1 j : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) : HR L N) : UpperTheory.V.KT.HS L N)) ∈ R
      rw [hfun]
      exact hgR
  · intro t
    set v : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N) := t.1 0 with hv
    set hh : UpperTheory.V.KT.HS L N := ((v : HR L N) : UpperTheory.V.KT.HS L N) with hhh
    have hRy : hh ∈ UpperTheory.V.KT.Ry L N := by
      intro y hy
      exact v.2.1 ⟨y, hy⟩
    have hsp := hSpan L N σ hσ 0 t.1 t.2
    have hmv : UpperTheory.V.KT.minVec hh = {y | ∀ j : Fin (0 + 1), UpperTheory.V.KT.q (((t.1 j : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) : HR L N) : UpperTheory.V.KT.HS L N) y = 1} := by
      ext y
      constructor
      · intro hy j
        have hj : j = 0 := Fin.ext (by omega)
        rw [hj]
        exact hy
      · intro hy
        exact hy 0
    have hsp' : UpperTheory.V.KT.Spans (UpperTheory.V.KT.minVec hh) := by
      rw [hmv]
      exact hsp
    haveI := hMin L N hh hRy hsp'
    refine Finite.of_injective
      (β := MulAction.stabilizer (UpperTheory.V.KT.Gm L N) (UpperTheory.V.KT.minVec hh))
      (fun g => ⟨((g.1 : Fix N σ) : UpperTheory.V.KT.Gm L N), ?_⟩) ?_
    · have hgt : (g.1 : Fix N σ) • t = t := g.2
      have hgv : (g.1 : Fix N σ) • v = v := congrArg (fun s : K.Tup 0 => s.1 0) hgt
      have hgh : ((g.1 : Fix N σ) : UpperTheory.V.KT.Gm L N) • hh = hh := by
        rw [hhh, ← hx1, hgv]
      rw [MulAction.mem_stabilizer_iff]
      ext z
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      show UpperTheory.V.KT.q hh (((g.1 : Fix N σ) : UpperTheory.V.KT.Gm L N)⁻¹ • z) = 1 ↔ UpperTheory.V.KT.q hh z = 1
      rw [← UpperTheory.V.KT.q_smul, hgh]
    · intro a b hab
      have hab' := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext hab')
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixedOrbitsFiniteRepresentatives
private theorem fixOrb_reps {Z T : Type} (f : Z → T) (W : Set Z) (h : (f '' W).Finite) :
    ∃ B : Set Z, B ⊆ W ∧ B.Finite ∧ ∀ z ∈ W, ∃ z' ∈ B, f z' = f z := by
  classical
  rcases W.eq_empty_or_nonempty with hW | ⟨w, hw⟩
  · exact ⟨∅, by simp, Set.finite_empty, by simp [hW]⟩
  · haveI : Nonempty Z := ⟨w⟩
    refine ⟨Function.invFunOn f W '' (f '' W), ?_, h.image _, ?_⟩
    · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact Function.invFunOn_mem ⟨z, hz, rfl⟩
    · intro z hz
      exact ⟨Function.invFunOn f W (f z), ⟨f z, ⟨z, hz, rfl⟩, rfl⟩,
        Function.invFunOn_eq ⟨z, hz, rfl⟩⟩

theorem UpperTheory.fixedOrbits_finite_representatives :
    UpperTheory.V.Af.BA.FixOrb := by
  classical
  intro G Z _ _ σ s hs W hfix hstab ⟨R, hR, hRW⟩
  have himg : ((fun z => MulAction.orbit G z) '' W).Finite := by
    refine (hR.image (fun z => MulAction.orbit G z)).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨g, hg⟩ := hRW z hz
    exact ⟨g • z, hg, MulAction.orbit_smul g z⟩
  obtain ⟨B1, hB1W, hB1, hB1r⟩ := fixOrb_reps _ W himg
  have hb : ∀ z ∈ W, ∃ b ∈ B1, ∃ h : G, h • b = z := by
    intro z hz
    obtain ⟨b, hbB, hbo⟩ := hB1r z hz
    have hbo' : MulAction.orbit G b = MulAction.orbit G z := hbo
    have hm : z ∈ MulAction.orbit G b := by
      rw [hbo']
      exact MulAction.mem_orbit_self z
    obtain ⟨h, hh⟩ := hm
    exact ⟨b, hbB, h, hh⟩
  let bb : Z → Z := fun z => if hz : z ∈ W then (hb z hz).choose else z
  let hh : Z → G := fun z => if hz : z ∈ W then (hb z hz).choose_spec.2.choose else 1
  have bbB : ∀ z ∈ W, bb z ∈ B1 := fun z hz => by
    simp only [bb, dif_pos hz]
    exact (hb z hz).choose_spec.1
  have hhb : ∀ z ∈ W, hh z • bb z = z := fun z hz => by
    simp only [bb, hh, dif_pos hz]
    exact (hb z hz).choose_spec.2.choose_spec
  have hcoc : ∀ z ∈ W, (hh z)⁻¹ * σ (hh z) ∈ MulAction.stabilizer G (bb z) := by
    intro z hz
    have hbW : bb z ∈ W := hB1W (bbB z hz)
    rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
    calc σ (hh z) • bb z = σ (hh z) • s (bb z) := by rw [hfix _ hbW]
      _ = s (hh z • bb z) := (hs _ _).symm
      _ = hh z • bb z := by rw [hhb z hz, hfix z hz]
  let key : Z → Z × G := fun z => (bb z, (hh z)⁻¹ * σ (hh z))
  have hkey : (key '' W).Finite := by
    refine (hB1.prod (hB1.biUnion (fun b hbB =>
      (haveI := hstab b (hB1W hbB); Set.toFinite (MulAction.stabilizer G b : Set G))))).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨bbB z hz, Set.mem_biUnion (bbB z hz) (hcoc z hz)⟩
  obtain ⟨B, hBW, hB, hBr⟩ := fixOrb_reps key W hkey
  refine ⟨B, hB, fun z hz => ?_⟩
  obtain ⟨z', hz'B, hk⟩ := hBr z hz
  have hz'W := hBW hz'B
  simp only [key, Prod.mk.injEq] at hk
  obtain ⟨h1, h2⟩ := hk
  refine ⟨hh z' * (hh z)⁻¹, ?_, ?_⟩
  · have : σ (hh z') = hh z' * ((hh z)⁻¹ * σ (hh z)) := by
      rw [← h2, mul_inv_cancel_left]
    rw [map_mul, map_inv, this]
    group
  · rw [mul_smul, inv_smul_eq_iff.mpr (hhb z hz).symm, ← h1, hhb z' hz'W]
    exact hz'B
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicBaseChangeRealPart
open NumberField Matrix UpperTheory.V.KT UpperTheory.V.Af.BA ComplexOrder in
theorem UpperTheory.adelicBaseChange_realPart :
    UpperTheory.V.Af.BA.RePart := by
  intro L _ _ N σ hσ k
  let A : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ :=
    fun w => Matrix.of fun i j => (((mat k w) i j).re : ℂ)
  have hre : ∀ w i j, ((mat k w) j i).re = ((mat k w) i j).re := by
    intro w i j
    have := (mat_herm k w).apply i j
    rw [← this]
    simp
  have hA : ∀ w, (A w).IsHermitian := by
    intro w
    ext i j
    simp [A, Matrix.conjTranspose_apply, hre w i j]
  have hmat : ∀ w, mat (mkHS A hA) w = A w := fun w => rfl
  have hAeq : ∀ w, A w = (1 / 2 : ℝ) • (mat k w + (mat k w).transpose) := by
    intro w
    ext i j
    have h1 := (mat_herm k w).apply i j
    have h2 : (mat k w) j i = star ((mat k w) i j) := by rw [← h1, star_star]
    simp only [A, Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, h2]
    apply Complex.ext <;> simp <;> ring
  refine ⟨⟨mkHS A hA, ?_⟩, ?_, ?_⟩
  · intro w i j
    show ((mat (mkHS A hA) w) i j).im = 0
    rw [hmat]
    simp [A]
  · intro y
    show q (mkHS A hA) y = _
    have hz : ∀ w i, toR (sLat σ y) w i = star (toR y w i) := fun w i => hσ w (y i)
    simp only [q, qR]
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hmat]
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum,
      ← Finset.sum_add_distrib, Finset.sum_div, hz]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [A, Matrix.of_apply, Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · intro hk
    have hpsd : ∀ w, (A w).PosSemidef := by
      intro w
      rw [hAeq w]
      exact ((hk w).add (hk w).transpose).smul (by norm_num)
    refine ⟨fun w => by rw [hmat]; exact hpsd w, fun h0 => ?_⟩
    apply HS_ext
    intro w
    have hA0 : A w = 0 := by
      have := congrArg (fun x : HR L N => mat (x : HS L N) w) h0
      simpa [hmat, mat_zero] using this
    rw [mat_zero]
    apply ((hk w).trace_eq_zero_iff).mp
    have hd : ∀ i, (mat k w) i i = (((mat k w) i i).re : ℂ) := by
      intro i
      apply Complex.ext
      · simp
      · have := (mat_herm k w).apply i i
        have h3 := congrArg Complex.im this
        simp at h3
        simp
        linarith
    rw [Matrix.trace]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.diag_apply, hd i]
    have := congrFun (congrFun hA0 i) i
    simpa [A] using this
end
