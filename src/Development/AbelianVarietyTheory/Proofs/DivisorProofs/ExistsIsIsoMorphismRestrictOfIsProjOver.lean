module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckDeformationOfLifting
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsoMorphismRestrictOfIsProjOver
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsoMorphismRestrictOfIsProjOver
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem exists_isIso_morphismRestrict_of_isProjOver : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω), IsProjOver Y.s → ∀ q : Y.Z ⟶ M.Z, M.IsHom Y (AlgHom.id o Ω) q → ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ IsIso (q ∣_ U) := by
  intro o Ω _ _ _ Y M hY q hq
  have := M.sep
  have : IsSeparated (q ≫ M.s) := hq.inducedModelMorphism_comp_structureMap.symm ▸ Y.sep
  have : IsSeparated q := IsSeparated.of_comp q M.s
  obtain ⟨m, d, hd⟩ := exists_isCl_of_isProjOver hY
  obtain ⟨i, hi⟩ := hd.1 (genericPoint Y.Z)
  obtain ⟨U, hU, hD, hR⟩ := hd.2 i hi.1
  obtain ⟨V, hV, hzV, hle⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨_, M.isOpen_setOf_div d i⟩) (x := genericPoint M.Z)
      (div_genericPoint hi.1)
  refine ⟨V, ⟨_, hzV⟩, isIso_morphismRestrict_of_local_dominant_sections q V fun z hz => ?_⟩
  obtain ⟨g, hg⟩ := exists_hom_of_map_ringOn (φ := AlgHom.id o Ω) hU
    ⟨genericPoint Y.Z, hD ▸ hi⟩ (V := V) ⟨z, hz⟩
    fun x hx => mem_ringOn.2 fun w hw =>
      Div.map_mem_O_of_mem_adjoin (M' := M) (φ := AlgHom.id o Ω) (t := d) (i := i) (z := w) (hle hw) (hR ▸ hx)
  have hp := specMap_valMap_fromSpec hV M.pt (M.top_le_preimage_pt ⟨z, hz⟩)
  have hid : ∀ {X : Scheme.{0}} (a : Spec (CommRingCat.of Ω) ⟶ X),
      Spec.map (CommRingCat.ofHom (AlgHom.id o Ω).toRingHom) ≫ a = a := fun a =>
    (congrArg (· ≫ a) (Spec.map_id _)).trans (Category.id_comp _)
  have hdom : IsDominant (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hz⟩)) ≫ g) := by
    rw [hg, hid]
    infer_instance
  refine ⟨_, hV.fromSpec, inferInstance, g, hV.range_fromSpec ▸ hz, hV.range_fromSpec ▸ fun w hw => hw,
    IsDominant.of_comp (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hz⟩))) g, ?_⟩
  refine hom_ext_of_isOpenImmersion (φ := AlgHom.id o Ω) hV.fromSpec hp ?_ (hp.trans (hid _).symm)
  rw [← Category.assoc, hg, hid]
  exact hq

end GlobalTheory.ZH.RatModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsoMorphismRestrictOfIsProjOverStatement
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonempty_isIso_morphismRestrict_of_isProjOver : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω), IsProjOver Y.s → ∀ q : Y.Z ⟶ M.Z, M.IsHom Y (AlgHom.id o Ω) q → ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ IsIso (q ∣_ U) := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isProjOver | exact GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isProjOver | (intros; apply GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isProjOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyShiftMem
set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

namespace GlobalTheory.AnPer.CloseTaylor

variable {I : Type} [Fintype I] [DecidableEq I] {g : ℕ}

def splitL (I : Type) [Fintype I] (g : ℕ) : (I ⊕ Fin g → ℂ) →L[ℂ] Tot I g :=
  (ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj (Sum.inl i)).prod
    (ContinuousLinearMap.pi fun b ↦ ContinuousLinearMap.proj (Sum.inr b))


omit [DecidableEq I] in
theorem shift_eq (w : Fin g → ℂ) (x : I ⊕ Fin g → ℂ) :
    (((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b)) : Tot I g) = (0, w) + splitL I g x := by
  ext <;> simp [splitL]

theorem splitL_single (b : Fin g) :
    splitL I g (Pi.single (Sum.inr b) 1) = ((0, Pi.single b 1) : Tot I g) := by
  ext i <;> simp [splitL, Pi.single_apply]


omit [DecidableEq I] in
theorem eventually_shift_mem {W : Opens (Tot I g)} {w : Fin g → ℂ} (hw : ((0 : I → ℂ), w) ∈ W) :
    ∀ᶠ x : I ⊕ Fin g → ℂ in 𝓝 0, (0, w) + splitL I g x ∈ W := by
  have hc : Continuous (fun x : I ⊕ Fin g → ℂ ↦ ((0, w) : Tot I g) + splitL I g x) :=
    continuous_const.add (splitL I g).continuous
  refine hc.continuousAt.eventually (W.isOpen.mem_nhds ?_)
  simpa using hw


omit [DecidableEq I] in
theorem analyticAt_shifted {W : Opens (Tot I g)} (h : Hol W) {w : Fin g → ℂ} (hw : ((0 : I → ℂ), w) ∈ W) :
    AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦ h.fn ((0, w) + splitL I g x)) 0 :=
  AnalyticAt.comp_of_eq (f := fun x : I ⊕ Fin g → ℂ ↦ ((0, w) : Tot I g) + splitL I g x)
    (h.analytic _ hw) (analyticAt_const.add ((splitL I g).analyticAt 0)) (by simp)

theorem fderiv_shifted {W : Opens (Tot I g)} (h : Hol W) {w : Fin g → ℂ} (hw : ((0 : I → ℂ), w) ∈ W)
    (b : Fin g) :
    (fun z ↦ fderiv ℂ (fun x : I ⊕ Fin g → ℂ ↦ h.fn ((0, w) + splitL I g x)) z (Pi.single (Sum.inr b) 1))
      =ᶠ[𝓝 0] fun x : I ⊕ Fin g → ℂ ↦ (dw b h).fn ((0, w) + splitL I g x) := by
  filter_upwards [eventually_shift_mem hw] with z hz
  have e : HasFDerivAt (fun x : I ⊕ Fin g → ℂ ↦ h.fn ((0, w) + splitL I g x))
      ((fderiv ℂ h.fn ((0, w) + splitL I g z)).comp (splitL I g)) z :=
    HasFDerivAt.comp (f := fun x : I ⊕ Fin g → ℂ ↦ ((0, w) : Tot I g) + splitL I g x) z
      (h.analytic _ hz).differentiableAt.hasFDerivAt ((splitL I g).hasFDerivAt.const_add _)
  rw [e.fderiv, ContinuousLinearMap.comp_apply, splitL_single]
  exact (Hol.fn_der _ h hz).symm

end GlobalTheory.AnPer.CloseTaylor


open GlobalTheory.AnPer.CloseTaylor in
theorem GlobalTheory.AnPer.close_of_sliceTaylor : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] (J : Ideal D) (N : ℕ), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (t : I → D), (∀ i, t i ∈ J) → ∀ (r : ℕ) (n : Fin r → Fin g → D), (∀ j a, n j a ∈ J) → (∀ j a b, n j a * n j b = 0) → ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens (Tot I g)) (W₀ : Opens E) (a : E → Fin g → ℂ), AnalyticOnNhd ℂ a W₀ → (∀ p ∈ W₀, ((0 : I → ℂ), a p) ∈ W) → ∀ ρ₁ ρ₂ : Hol W →+* D ⊗[ℂ] Hol W₀, (∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ₁ h) = GlobalTheory.PeriodFamily.taylor N (Sum.elim t fun b ↦ ∑ j, n j b) (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b)))) → (∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ₂ h) = GlobalTheory.PeriodFamily.taylor N (Sum.elim t fun _ ↦ 0) (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b)))) → Close (J.map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol W₀)) ρ₁ ρ₂ := by
  intro I _ _ g D _ _ J N hJ t ht r n hn hnn E _ _ _ W W₀ a ha hW ρ₁ ρ₂ h₁ h₂
  induction r generalizing ρ₁ with
  | zero =>
    have : ρ₁ = ρ₂ := RingHom.ext fun h ↦ GlobalTheory.tensor_hol_ext_of_values W₀ D _ _ fun p hp ↦ by
      rw [h₁, h₂]; simp
    rw [this]
    exact Relation.ReflTransGen.refl
  | succ r ih =>
    obtain ⟨ρ', hρ'⟩ := GlobalTheory.T.tensorLift_ev_rho_eq_taylor_slice N (Sum.elim t fun b ↦ ∑ j : Fin r, n j.succ b)
      (fun s ↦ hJ _ fun c ↦ by
        rcases s c with i | b
        · exact ht i
        · exact J.sum_mem fun j _ ↦ hn _ _) W W₀ a ha hW
    refine Relation.ReflTransGen.head (b := (ρ' : Hol W →+* D ⊗[ℂ] Hol W₀)) ?_
      (ih (fun j ↦ n j.succ) (fun j ↦ hn _) (fun j ↦ hnn _) _ hρ')
    refine ⟨fun b ↦ (-n 0 b) ⊗ₜ[ℂ] 1, fun b ↦ Ideal.mem_map_of_mem _ (J.neg_mem (hn 0 b)), fun b c ↦ ?_, fun h ↦ ?_⟩
    · rw [Algebra.TensorProduct.tmul_mul_tmul, neg_mul_neg, hnn, zero_tmul]
    refine GlobalTheory.tensor_hol_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    have e : (Sum.elim t fun b ↦ ∑ j : Fin r, n j.succ b) = fun i : I ⊕ Fin g ↦
        (Sum.elim t fun b ↦ ∑ j, n j b) i + (Sum.elim (fun _ ↦ 0) fun b ↦ -n 0 b) i := by
      ext (i | b)
      · simp
      · simp [Fin.sum_univ_succ]
    have hs := GlobalTheory.T.taylor_add_square_zero_nilpotent N (Sum.elim t fun b ↦ ∑ j, n j b) (Sum.elim (fun _ : I ↦ 0) fun b ↦ -n 0 b)
      (fun s hs ↦ hJ s fun c ↦ (Ideal.span_le.2 (by
        rintro _ (⟨i | b, rfl⟩ | ⟨i | b, rfl⟩)
        · exact ht i
        · exact J.sum_mem fun j _ ↦ hn _ _
        · exact J.zero_mem
        · exact J.neg_mem (hn 0 b))) (hs c))
      (by rintro (i | b) (j | c) <;> simp [hnn]) _ (analyticAt_shifted h (hW p hp))
    obtain ⟨-, -, -, hcongr, -, -⟩ :=
      GlobalTheory.PeriodFamily.taylor_formal_properties N (Sum.elim t fun b ↦ ∑ j, n j b)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.coe_coe, hρ', map_add (f := _), map_sum, h₁, e]
    simp only [map_mul, h₁, shift_eq]
    rw [hs, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, zero_add]
    refine congrArg _ (Finset.sum_congr rfl fun b _ ↦ ?_)
    rw [hcongr _ _ (fderiv_shifted h (hW p hp) b)]
    simp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylWeightSpreadBoundProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylWeightSpreadBoundProof
open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.LeviCut

theorem nablaBdd_rename_eq_rowAct {N : ℕ} (σ : Equiv.Perm (Fin N)) (f : MvPolynomial (Fin N × Fin N) ℚ) :
    rename (Prod.map σ id) f = rowAct ℚ (Matrix.of fun a b => if b = σ a then (1 : ℚ) else 0) f := by
  classical
  have : (rename (Prod.map σ id) : MvPolynomial (Fin N × Fin N) ℚ →ₐ[ℚ] _) =
      rowAct ℚ (Matrix.of fun a b => if b = σ a then (1 : ℚ) else 0) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [rowAct, rename_X]
  rw [this]

theorem nablaBdd_rowDeg_bounds {M : ℕ} (ν : Fin (M + 1) → ℕ) (f : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ)
    (hf : f ∈ dualWeyl ℚ (M + 1) (M + 1) ν) (m : Fin (M + 1) × Fin (M + 1) →₀ ℕ) (hm : m ∈ f.support)
    (c : Fin (M + 1)) : rowDeg m c ≤ ν 0 ∧ ν (Fin.last M) ≤ rowDeg m c := by
  classical
  have key : ∀ σ : Equiv.Perm (Fin (M + 1)), rename (Prod.map σ id) f ∈ dualWeyl ℚ (M + 1) (M + 1) ν ∧
      Finsupp.mapDomain (Prod.map σ id) m ∈ (rename (Prod.map σ id) f).support ∧
      rowDeg (Finsupp.mapDomain (Prod.map σ id) m) (σ c) = rowDeg m c := by
    intro σ
    have hinj : Function.Injective (Prod.map σ (id : Fin (M + 1) → Fin (M + 1))) :=
      σ.injective.prodMap Function.injective_id
    refine ⟨?_, ?_, ?_⟩
    · rw [nablaBdd_rename_eq_rowAct]
      exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℚ _ _ ν _ f hf
    · rw [mem_support_iff, coeff_rename_mapDomain _ hinj]
      exact mem_support_iff.mp hm
    · unfold rowDeg
      refine Finset.sum_congr rfl fun s _ => ?_
      exact Finsupp.mapDomain_apply_of_injective hinj m (c, s)
  constructor
  · obtain ⟨h1, h2, h3⟩ := key (Equiv.swap c 0)
    have dom := (GlobalTheory.DualWeyl.rowDeg_dominated_of_mem_nabla ν _ h1 _ h2).1 1
    have e : (Finset.univ.filter fun a : Fin (M + 1) => a.val < 1) = {0} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, Fin.val_zero]
      omega
    rw [e, Finset.sum_singleton, Finset.sum_singleton] at dom
    rw [Equiv.swap_apply_left] at h3
    omega
  · obtain ⟨h1, h2, h3⟩ := key (Equiv.swap c (Fin.last M))
    have dom := GlobalTheory.DualWeyl.rowDeg_dominated_of_mem_nabla ν _ h1 _ h2
    have e2 : ∀ g : Fin (M + 1) → ℕ, ∑ a, g a = (∑ a : Fin (M + 1) with a.val < M, g a) + g (Fin.last M) := by
      intro g
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : Fin (M + 1) => a.val < M) g]
      congr 1
      have : (Finset.univ.filter fun a : Fin (M + 1) => ¬ a.val < M) = {Fin.last M} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, Fin.val_last]
        omega
      rw [this, Finset.sum_singleton]
    have d1 := dom.1 M
    have d2 := dom.2
    rw [e2, e2] at d2
    rw [Equiv.swap_apply_left] at h3
    omega

theorem nablaBdd : NablaBdd := by
  intro N ν _ K hK a ha b hb n x hx hn
  by_contra hx0
  have hx0' : (x : MvPolynomial (Fin N × Fin N) ℚ) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨m, hm⟩ := support_nonempty.mpr hx0'
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hea : ∀ (c : ℕ) (hc : c < M + 1) (y : dualWeyl ℚ (M + 1) (M + 1) ν),
      ((eV (M + 1) ν c c y : dualWeyl ℚ (M + 1) (M + 1) ν) : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ) =
        Formalism.CohomologicalDescent.LR.der (M + 1) (M + 1) ⟨c, hc⟩ ⟨c, hc⟩ (y : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ) := by
    intro c hc y
    unfold eV
    rw [dite_eq_left ⟨hc, hc⟩]
    rfl
  have hc := congrArg (fun y : dualWeyl ℚ (M + 1) (M + 1) ν => AddMonoidAlgebra.coeff (y : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ) m) hx
  simp only [Submodule.coe_sub, Submodule.coe_smul, hea a ha, hea b hb, coeff_sub,
    Formalism.CohomologicalDescent.LR.coeff_der_diag, coeff_smul, smul_eq_mul, Formalism.GradedWeylDivisibility.ldrow_weight_rowW] at hc
  have hne : AddMonoidAlgebra.coeff (x : MvPolynomial (Fin (M + 1) × Fin (M + 1)) ℚ) m ≠ 0 := mem_support_iff.mp hm
  have key : (((rowDeg m ⟨a, ha⟩ : ℕ) : ℚ) - ((rowDeg m ⟨b, hb⟩ : ℕ) : ℚ)) = (n : ℚ) := by
    apply mul_right_cancel₀ hne
    rw [sub_mul]
    exact hc
  have key' : ((rowDeg m ⟨a, ha⟩ : ℕ) : ℤ) - ((rowDeg m ⟨b, hb⟩ : ℕ) : ℤ) = n := by exact_mod_cast key
  have B1 := (nablaBdd_rowDeg_bounds ν _ x.2 m hm ⟨a, ha⟩).1
  have B2 := (nablaBdd_rowDeg_bounds ν _ x.2 m hm ⟨b, hb⟩).2
  have B3 := hK 0 (Fin.last M)
  omega

end GlobalTheory.LeviCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylWeightSpreadBoundProofStatement
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylWeightSpreadBound_proof : GlobalTheory.LeviCut.NablaBdd := by
  first | exact @GlobalTheory.LeviCut.nablaBdd | exact GlobalTheory.LeviCut.nablaBdd | (intros; apply GlobalTheory.LeviCut.nablaBdd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylModuleStructureGlProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylModuleStructureGlProof
open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.LeviCut

namespace NablaStr

theorem coeff_der_diag_row {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ) (m : Fin r × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (Formalism.CohomologicalDescent.LR.der r n a a f) m = ((Finsupp.weight (rowW r n) m a : ℕ) : ℚ) * AddMonoidAlgebra.coeff f m := by
  rw [← Formalism.CohomologicalDescent.LR.rowDiv_one, lgraded_coeff_euler, lgraded_weight_rowW]

theorem der_diag_eq_weight_smul_of_isWeightedHomogeneous {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) ℚ) (μ : Fin r → ℕ) :
    IsWeightedHomogeneous (rowW r n) f μ → ∀ a, Formalism.CohomologicalDescent.LR.der r n a a f = (μ a : ℚ) • f := by
  intro h a
  ext m
  rw [coeff_der_diag_row, coeff_smul, smul_eq_mul]
  by_cases hm : AddMonoidAlgebra.coeff f m = 0
  · rw [hm, mul_zero, mul_zero]
  · rw [h hm]

theorem eV_val {N : ℕ} (ν : Fin N → ℕ) (a b : ℕ) (ha : a < N) (hb : b < N) (x : dualWeyl ℚ N N ν) :
    ((eV N ν a b x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) =
      Formalism.CohomologicalDescent.LR.der N N ⟨a, ha⟩ ⟨b, hb⟩ (x : MvPolynomial (Fin N × Fin N) ℚ) := by
  unfold eV
  rw [dif_pos ⟨ha, hb⟩]
  rfl

theorem eV_pow_val {N : ℕ} (ν : Fin N → ℕ) (a b : ℕ) (ha : a < N) (hb : b < N) (k : ℕ) (x : dualWeyl ℚ N N ν) :
    (((eV N ν a b ^ k) x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) =
      ((Formalism.CohomologicalDescent.LR.der N N ⟨a, ha⟩ ⟨b, hb⟩ : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ)) ^ k)
        (x : MvPolynomial (Fin N × Fin N) ℚ) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, eV_val ν a b ha hb, pow_succ, Module.End.mul_apply]
    rfl

theorem weight_rowW_eq {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (rowW N N) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp [rowW, rowDeg]
  · intro b _ hb
    simp [rowW, Pi.single_apply, Ne.symm hb]
  · simp

theorem glRel_eV (N : ℕ) (ν : Fin N → ℕ) : GlRel N (eV N ν) := by
  intro a b c d ha hb hc hd
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := Formalism.CohomologicalDescent.LR.der_comm (n := N) ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ (x : MvPolynomial (Fin N × Fin N) ℚ)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
  rw [eV_val ν a b ha hb, eV_val ν c d hc hd, eV_val ν c d hc hd, eV_val ν a b ha hb, h]
  by_cases hbc : b = c <;> by_cases hda : d = a
  · subst hbc hda
    simp only [if_true, LinearMap.sub_apply, Submodule.coe_sub, eV_val ν d d ha hd, eV_val ν b b hc hb]
  · subst hbc
    have : (⟨d, hd⟩ : Fin N) ≠ ⟨a, ha⟩ := fun h => hda (Fin.mk.inj h)
    simp only [if_true, this, if_false, hda, sub_zero, eV_val ν a d ha hd]
    simp
  · subst hda
    have : (⟨b, hb⟩ : Fin N) ≠ ⟨c, hc⟩ := fun h => hbc (Fin.mk.inj h)
    simp only [if_true, this, if_false, hbc, zero_sub, LinearMap.neg_apply, Submodule.coe_neg, eV_val ν c b hc hb]
    simp
  · have h1 : (⟨b, hb⟩ : Fin N) ≠ ⟨c, hc⟩ := fun h => hbc (Fin.mk.inj h)
    have h2 : (⟨d, hd⟩ : Fin N) ≠ ⟨a, ha⟩ := fun h => hda (Fin.mk.inj h)
    simp [h1, h2, hbc, hda]

theorem wtSpan_eV (N : ℕ) (ν : Fin N → ℕ) : WtSpan N (eV N ν) := by
  classical
  rw [WtSpan, eq_top_iff]
  rintro x -
  set f : MvPolynomial (Fin N × Fin N) ℚ := (x : MvPolynomial (Fin N × Fin N) ℚ) with hf
  have hfin := weightedHomogeneousComponent_finsupp (w := rowW N N) f
  have hsum : f = ∑ μ ∈ hfin.toFinset, weightedHomogeneousComponent (rowW N N) μ f := by
    conv_lhs => rw [← sum_weightedHomogeneousComponent (rowW N N) f]
    exact finsum_eq_sum_of_support_subset _ (fun μ hμ => (Set.Finite.mem_toFinset hfin).mpr hμ)
  have hmem : ∀ μ, weightedHomogeneousComponent (rowW N N) μ f ∈ dualWeyl ℚ N N ν :=
    fun μ => dualWeylRowGraded ℚ N N ν μ f x.2
  have hx : x = ∑ μ ∈ hfin.toFinset, (⟨_, hmem μ⟩ : dualWeyl ℚ N N ν) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact hsum
  rw [hx]
  refine Submodule.sum_mem _ fun μ _ => Submodule.subset_span ?_
  refine ⟨fun c => if h : c < N then (μ ⟨c, h⟩ : ℤ) else 0, fun c hc => ?_⟩
  apply Subtype.ext
  rw [eV_val ν c c hc hc]
  simp only [dif_pos hc]
  have h := der_diag_eq_weight_smul_of_isWeightedHomogeneous _ μ
    (weightedHomogeneousComponent_isWeightedHomogeneous μ f) ⟨c, hc⟩
  rw [Submodule.coe_smul]
  simpa using h

theorem sum_range_dite (N k : ℕ) (hk : k ≤ N) (F : Fin N → ℕ) :
    ∑ c ∈ Finset.range k, (if h : c < N then (F ⟨c, h⟩ : ℤ) else 0) =
      ((∑ a : Fin N with a.val < k, F a : ℕ) : ℤ) := by
  push_cast
  rw [Finset.sum_filter]
  have e : ∀ a : Fin N, (if a.val < k then (F a : ℤ) else 0) =
      (fun i : ℕ => if i < k then (if h : i < N then (F ⟨i, h⟩ : ℤ) else 0) else 0) a.val := by
    intro a
    simp [a.isLt]
  rw [Finset.sum_congr rfl (fun a _ => e a),
    Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < k then (if h : i < N then (F ⟨i, h⟩ : ℤ) else 0) else 0) N,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem dom_eV (N : ℕ) (ν : Fin N → ℕ) : Dom N (eV N ν) (wtZ ν) := by
  classical
  intro μ x hx hx0
  have hx0' : (x : MvPolynomial (Fin N × Fin N) ℚ) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hx0'
  have hμ : ∀ c (hc : c < N), μ c = (rowDeg m ⟨c, hc⟩ : ℤ) := by
    intro c hc
    have h1 := congrArg (fun y : dualWeyl ℚ N N ν => AddMonoidAlgebra.coeff (y : MvPolynomial (Fin N × Fin N) ℚ) m) (hx c hc)
    simp only [eV_val ν c c hc hc, coeff_der_diag_row, Submodule.coe_smul, coeff_smul, smul_eq_mul,
      weight_rowW_eq] at h1
    have h2 := mul_right_cancel₀ hm h1
    exact_mod_cast h2.symm
  have hdom := GlobalTheory.DualWeyl.rowDeg_dominated_of_mem_nabla ν (x : MvPolynomial (Fin N × Fin N) ℚ) x.2 m
    (mem_support_iff.mpr hm)
  have hsμ : ∀ k ≤ N, ∑ c ∈ Finset.range k, μ c = ((∑ a : Fin N with a.val < k, rowDeg m a : ℕ) : ℤ) := by
    intro k hk
    rw [← sum_range_dite N k hk]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hcN : c < N := lt_of_lt_of_le (Finset.mem_range.mp hc) hk
    rw [dif_pos hcN, hμ c hcN]
  have hsν : ∀ k ≤ N, ∑ c ∈ Finset.range k, wtZ ν c = ((∑ a : Fin N with a.val < k, ν a : ℕ) : ℤ) := by
    intro k hk
    rw [← sum_range_dite N k hk]
    exact Finset.sum_congr rfl fun c _ => rfl
  have hall : ∀ F : Fin N → ℕ, (∑ a : Fin N with a.val < N, F a) = ∑ a : Fin N, F a := by
    intro F
    rw [Finset.filter_true_of_mem (fun a _ => a.isLt)]
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [hsμ k hk, hsν k hk]
    exact_mod_cast hdom.1 k
  · rw [hsμ N le_rfl, hsν N le_rfl, hall, hall]
    exact_mod_cast hdom.2

theorem divStable_eV (N : ℕ) (ν : Fin N → ℕ) (M : Submodule ℤ (MvPolynomial (Fin N × Fin N) ℤ))
    (hM : ∀ (a b : Fin N) (k : ℕ), ∀ f ∈ M, rowDiv ℤ a b k f ∈ M) : DivStable N (eV N ν) (latV N ν M) := by
  intro i hi j hj hij k x hx
  simp only [latV, Submodule.mem_comap, Submodule.mem_map] at hx ⊢
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : map (Int.castRingHom ℚ) y = (x : MvPolynomial (Fin N × Fin N) ℚ) := hyx
  refine ⟨rowDiv ℤ ⟨i, hi⟩ ⟨j, hj⟩ k y, hM _ _ k y hy, ?_⟩
  have hne : (⟨i, hi⟩ : Fin N) ≠ ⟨j, hj⟩ := fun h => hij (Fin.mk.inj h)
  change map (Int.castRingHom ℚ) (rowDiv ℤ ⟨i, hi⟩ ⟨j, hj⟩ k y) =
    (((k.factorial : ℚ)⁻¹ • (eV N ν i j ^ k) x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ)
  rw [Submodule.coe_smul, eV_pow_val ν i j hi hj, ← Formalism.CohomologicalDescent.LR.der_pow _ _ hne, ← lclosedeq_rowDiv_map, hyx']

end NablaStr

open NablaStr

theorem nablaGl : NablaGl := by
  intro N ν _
  refine ⟨glRel_eV N ν, wtSpan_eV N ν, dom_eV N ν, divStable_eV N ν _ ?_, divStable_eV N ν _ ?_⟩
  · intro a b k f hf
    exact rowDivStable ℤ N N ν a b k f hf
  · intro a b k f hf
    exact weylRowDivStable ℤ N N le_rfl ν a b k f hf

end GlobalTheory.LeviCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylModuleStructureGlProofStatement
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylModuleStructureGl_proof : GlobalTheory.LeviCut.NablaGl := by
  first | exact @GlobalTheory.LeviCut.nablaGl | exact GlobalTheory.LeviCut.nablaGl | (intros; apply GlobalTheory.LeviCut.nablaGl <;> assumption)
end
end
