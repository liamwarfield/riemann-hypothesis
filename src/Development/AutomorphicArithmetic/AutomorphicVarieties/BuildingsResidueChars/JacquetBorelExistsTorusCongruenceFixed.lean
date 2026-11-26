module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixedCongruenceNeBotOfJacquetTorusFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsMultilinearIntertwinerOfCommutingSubgroups

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetBorelExistsTorusCongruenceFixed
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetExistsLeviCongruenceFixedOfCharSupport
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EqOneOfIrreduciblePiAbelianFixedNeBot
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.eq_one_of_irreducible_pi_abelian_fixed_ne_bot :
    ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ a, Group (Γ a)], (∀ a (x y : Γ a), x * y = y * x) →
    ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (∀ a, Γ a) Y) (H : ∀ a, Subgroup (Γ a)), τ.IsIrreducible →
    (∀ a, fixed (τ.comp (MonoidHom.mulSingle Γ a) : Representation ℂ (Γ a) Y) (H a) ≠ ⊥) → ∀ g : ∀ a, Γ a, (∀ a, g a ∈ H a) → τ g = 1 := by
  intro α _ _ Γ _ hcomm Y _ _ τ H hirr hne g hg
  have hfixall : ∀ a (h : H a) (y : Y), τ (Pi.mulSingle a (h : Γ a)) y = y := by
    intro a
    have hc : ∀ (x : Γ a) (g' : ∀ b, Γ b), Pi.mulSingle a x * g' = g' * Pi.mulSingle a x := by
      intro x g'
      funext b
      simp only [Pi.mul_apply]
      exact hcomm b _ _
    let R : Subrepresentation τ :=
      { toSubmodule := fixed (τ.comp (MonoidHom.mulSingle Γ a) : Representation ℂ (Γ a) Y) (H a)
        apply_mem_toSubmodule := by
          intro g' y hy h
          have hy' := hy h
          simp only [MonoidHom.one_apply, Units.val_one, one_smul, MonoidHom.comp_apply,
            MonoidHom.mulSingle_apply] at hy' ⊢
          rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply, hy'] }
    have hR : R = ⊤ := by
      rcases IsSimpleOrder.eq_bot_or_eq_top R with h | h
      · exfalso
        apply hne a
        have := congrArg Subrepresentation.toSubmodule h
        exact this
      · exact h
    intro h y
    have hy : y ∈ R.toSubmodule := by
      rw [hR]
      exact Submodule.mem_top
    have := hy h
    simpa using this
  letI : ∀ a, CommGroup (Γ a) := fun a => { (inferInstance : Group (Γ a)) with mul_comm := hcomm a }
  have hs : ∀ (s : Finset α) (y : Y), τ (∏ a ∈ s, Pi.mulSingle a (g a)) y = y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y
      rw [Finset.prod_empty, map_one, Module.End.one_apply]
    | insert a s ha ih =>
      intro y
      rw [Finset.prod_insert ha, map_mul, Module.End.mul_apply, ih]
      exact hfixall a ⟨g a, hg a⟩ y
  have hg' : g = ∏ a, Pi.mulSingle a (g a) := (Finset.univ_prod_mulSingle g).symm
  ext y
  rw [Module.End.one_apply]
  conv_lhs => rw [hg']
  exact hs Finset.univ y
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

private theorem UpperTheory.smooth_gl_one_cuspidal {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin 1) k) V} (hs : IsSmooth π) : IsCuspidal π := by
  refine ⟨hs, fun s d e he => absurd ?_ he⟩
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
  ext i j
  obtain rfl : i = j := Subsingleton.elim _ _
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  simpa using (mem_unipRad.1 hu).2 a i i

private theorem UpperTheory.fixed_vectors_nonzero_character {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (y : IrrRep (GL (Fin 1) k)) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1)
    (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (h : IrrGL.of y.ρ y.smooth y.irr = IrrGL.ofChar χ hχ)
    (h1 : ∀ u : kˣ, valuation k ((u : k) - 1) < γ → χ u = 1) :
    fixed y.ρ (GlobalTheory.CentralExponent.cong (Fin 1) γ hγ) ≠ ⊥ := by
  have h' : IrrGL.of y.ρ y.smooth y.irr = IrrGL.of (detRep (Fin 1) χ) (isCuspidal_detRep_one hχ).1
      (isIrreducible_ofChar _) := h
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 h'
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible y.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : y.V)
  refine (Submodule.ne_bot_iff _).2 ⟨v, fun g => ?_, hv⟩
  have hg : valuation k ((g.1.val - 1) 0 0) < γ := g.2 0 0
  have h2 : χ (Matrix.GeneralLinearGroup.det g.1) = 1 := by
    refine h1 _ ?_
    simpa [Matrix.det_unique] using hg
  refine φ.toLinearEquiv.injective ?_
  have h3 := φ.toIntertwiningMap.isIntertwining _ _ g.1 v
  refine h3.trans ?_
  simp only [detRep, ofChar_apply, detChar_apply, h2, MonoidHom.one_apply, Units.val_one, one_mul, one_smul]
  rfl

theorem UpperTheory.jacquet_exists_levi_congruence_fixed_of_char_support :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (s : Multiset (IrrGL (k := k))) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1), HasSupport π s → (∀ y ∈ s, ∃ χ hχ, y = IrrGL.ofChar χ hχ ∧ ∀ u : kˣ, valuation k ((u : k) - 1) < γ → χ u = 1) →
    ∀ e : (Σ _ : Fin N, Fin 1) ≃ Fin N, Nontrivial (Jacquet π (unipRad k e)) →
    ∃ y : Jacquet π (unipRad k e), y ≠ 0 ∧ ∀ g : Levi k fun _ : Fin N => Fin 1,
      (∀ a, g a ∈ GlobalTheory.CentralExponent.cong (Fin 1) γ hγ) → jac e π g y = y := by
  intro hG hZ k _ _ _ _ N V _ _ π s γ hγ hs hχ e hJ
  have hjs : IsSmooth (jac e π) := isSmooth_jac e hs.isSmooth
  obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (jac e π) hJ
  have hτsm : IsSmooth τ := hτs.isSmooth hjs
  have hsm : ∀ j : Fin N, IsSmooth (τ.comp (MonoidHom.mulSingle (fun _ : Fin N => GL (Fin 1) k) j) :
      Representation ℂ (GL (Fin 1) k) Y) := fun j =>
    isSmooth_comp hτsm _ (continuous_mulSingle (A := fun _ : Fin N => GL (Fin 1) k) j)
  have hy : ∀ j : Fin N, ∃ y : IrrRep (GL (Fin 1) k), IsSubquotient y.ρ
      (τ.comp (MonoidHom.mulSingle (fun _ : Fin N => GL (Fin 1) k) j) : Representation ℂ (GL (Fin 1) k) Y) := by
    intro j
    obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
      (τ.comp (MonoidHom.mulSingle (fun _ : Fin N => GL (Fin 1) k) j))
      (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ)
    exact ⟨⟨X, υ, hυs.isSmooth (hsm j), hυ⟩, hυs⟩
  choose y hy using hy
  obtain ⟨u, hu, rfl⟩ := SupportUnique.exists_sum_of_jac (d := fun _ : Fin N => 1) hG hZ hs e hτ hτs y hy
  have hfix : ∀ j : Fin N, fixed (τ.comp (MonoidHom.mulSingle (fun _ : Fin N => GL (Fin 1) k) j) :
      Representation ℂ (GL (Fin 1) k) Y) (GlobalTheory.CentralExponent.cong (Fin 1) γ hγ) ≠ ⊥ := by
    intro j
    have hc : (IrrGL.of (y j).ρ (y j).smooth (y j).irr).IsCusp :=
      ⟨Nat.one_pos, UpperTheory.smooth_gl_one_cuspidal (IrrGL.of (y j).ρ (y j).smooth (y j).irr).2.rep.smooth⟩
    have h1 := SupportUnique.eq_singleton_of_isCusp hc ((hu j).of_equiv (IrrGL.equivOf _ _ _))
    obtain ⟨χ, hχs, h2, h3⟩ := hχ (IrrGL.of (y j).ρ (y j).smooth (y j).irr)
      (Multiset.mem_sum.2 ⟨j, Finset.mem_univ j, by rw [h1]; exact Multiset.mem_singleton_self _⟩)
    exact UpperTheory.fixed_ne_bot_of_isSubquotient_of_isCompact _ _ _ _ _ _ (hsm j) (hy j) (GlobalTheory.CentralExponent.isCompact_cong γ hγ)
      (UpperTheory.fixed_vectors_nonzero_character (y j) γ hγ χ hχs h2 h3)
  have hcomm : ∀ (_ : Fin N) (x z : GL (Fin 1) k), x * z = z * x := by
    intro _ x z
    ext i j
    simp [Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0, mul_comm]
  have htriv := UpperTheory.eq_one_of_irreducible_pi_abelian_fixed_ne_bot (Fin N) (fun _ => GL (Fin 1) k) hcomm Y τ
    (fun _ => GlobalTheory.CentralExponent.cong (Fin 1) γ hγ) hτ hfix
  let H : Subgroup (Levi k fun _ : Fin N => Fin 1) :=
    Subgroup.pi Set.univ fun _ => GlobalTheory.CentralExponent.cong (Fin 1) γ hγ
  have hH : IsCompact (H : Set (Levi k fun _ : Fin N => Fin 1)) :=
    isCompact_univ_pi fun _ => GlobalTheory.CentralExponent.isCompact_cong γ hγ
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ
  obtain ⟨v, hv⟩ := exists_ne (0 : Y)
  have hτf : fixed τ H ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨v, fun g => by
    rw [htriv g.1 fun a => g.2 a trivial]
    simp, hv⟩
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 (UpperTheory.fixed_ne_bot_of_isSubquotient_of_isCompact _ _ _ τ (jac e π) H hjs hτs hH hτf)
  refine ⟨w, hw0, fun g hg => ?_⟩
  simpa using hw ⟨g, fun a _ => hg a⟩
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.jacquet_borel_exists_torus_congruence_fixed :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (s : Multiset (IrrGL (k := k))) (γ : (ValueGroupWithZero k)ˣ), γ ≤ 1 → HasSupport π s → (∀ y ∈ s, ∃ χ hχ, y = IrrGL.ofChar χ hχ ∧ ∀ u : kˣ, valuation k ((u : k) - 1) < γ → χ u = 1) →
    Nontrivial (Jacquet π (unipB k (Fin N))) →
    ∃ y : Jacquet π (unipB k (Fin N)), y ≠ 0 ∧ ∀ t : Fin N → kˣ, (∀ i, valuation k ((t i : k) - 1) < γ) → jacBU π t y = y := by
  intro hG hZ k _ _ _ _ N V _ _ π s γ hγ hs hχ hnt
  let f := Equiv.sigmaUnique (Fin N) fun _ : Fin N => Fin 1
  have hmono : StrictMono (blk f) := fun a b h => by simpa [blk, f] using h
  have h3 : twKer π (unipRad k f) 1 = twKer π (unipB k (Fin N)) 1 := by
    rw [EmptyBlocks.unipRad_eq k f hmono]
  let E : Jacquet π (unipRad k f) ≃ₗ[ℂ] Jacquet π (unipB k (Fin N)) := Submodule.quotEquivOfEq _ _ h3
  have hE : ∀ v : V, E (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := fun _ => rfl
  obtain ⟨y, hy0, hy⟩ := UpperTheory.jacquet_exists_levi_congruence_fixed_of_char_support hG hZ k N V π s γ hγ hs hχ f E.toEquiv.nontrivial
  refine ⟨E y, E.map_ne_zero_iff.2 hy0, fun t ht => ?_⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hγ' : (γ : ValueGroupWithZero k) ≤ 1 := hγ
  have h1 := hy (EmptyBlocks.torusToLevi k f t) fun a i j => by
    rw [EmptyBlocks.val_torusToLevi, Subsingleton.elim i j, Matrix.sub_apply, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq]
    exact ht _
  have hv : ∀ i, valuation k (t i : k) = 1 := fun i => by
    have := Valuation.map_one_add_of_lt (valuation k) ((ht i).trans_le hγ')
    rwa [add_sub_cancel] at this
  have hd : deltaHalf k (fun _ : Fin N => Fin 1) (EmptyBlocks.torusToLevi k f t) = 1 := by
    rw [deltaHalf_apply]
    refine Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ ?_
    have := (EmptyBlocks.det_torusToLevi k f t a).trans (Fin.prod_univ_one _)
    exact (congrArg (fun u : kˣ => valuation k (u : k)) this).trans (hv _)
  rw [jac_mk, hd, inv_one, Units.val_one, one_smul, EmptyBlocks.leviEmb_torusToLevi] at h1
  have h2 := congrArg E h1
  rw [hE, hE] at h2
  rw [hE, jacBU_mk]
  exact h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsTensorDualEmbeddingOfHasWeightAt
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsDualSchurModuleIsoDualWeight
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

private theorem detPow_invTr (n : ℕ) (g : GL (Fin n) ℂ) (c : ℤ) :
    detPow ℂ n (inside₂ ℂ n g) c = detPow ℂ n g⁻¹ c := by
  unfold detPow
  congr 2
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_transpose _

private theorem toDual_invTr (n : ℕ) (lam : DomWeight n) (g : GL (Fin n) ℂ) (x : nablaSq ℂ n lam) :
    GlobalTheory.ConjDual.toDual n lam (GlobalTheory.Branching.sqRep ℂ n lam (inside₂ ℂ n g) x) =
      GlobalTheory.ConjDual.toDual n lam x ∘ₗ GlobalTheory.Branching.sqRep ℂ n lam g⁻¹ := by
  ext y
  change GlobalTheory.ConjDual.bil _ (sqAct ℂ n lam (inside₂ ℂ n g) x.1) y.1 =
    GlobalTheory.ConjDual.bil _ x.1 (sqAct ℂ n lam g⁻¹ y.1)
  unfold sqAct
  rw [map_smul, map_smul, LinearMap.smul_apply, detPow_invTr, GlobalTheory.ConjDual.bil_rowAct,
    Matrix.transpose_transpose]
  rfl

theorem UpperTheory.exists_dual_schur_module_iso_dual_weight :
    ∀ (n : ℕ), 1 ≤ n → ∀ lam : DomWeight n, ∃ κ : Module.Dual ℂ (nablaSq ℂ n lam) ≃ₗ[ℂ] nablaSq ℂ n lam.dual, ∀ (g : GL (Fin n) ℂ) (ℓ : Module.Dual ℂ (nablaSq ℂ n lam)), κ (ℓ ∘ₗ GlobalTheory.Branching.sqRep ℂ n lam g⁻¹) = GlobalTheory.Branching.sqRep ℂ n lam.dual g (κ ℓ) := by
  intro n hn lam
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨κ, hκ⟩ := GlobalTheory.DefiniteBC.exists_equiv_dual lam
  let T : nablaSq ℂ (m + 1) lam ≃ₗ[ℂ] Module.Dual ℂ (nablaSq ℂ (m + 1) lam) :=
    (GlobalTheory.ConjDual.toDual (m + 1) lam).linearEquivOfInjective (GlobalTheory.ConjDual.toDual_injective _ lam)
      Subspace.dual_finrank_eq.symm
  have hT : ∀ x, T x = GlobalTheory.ConjDual.toDual (m + 1) lam x := fun _ => rfl
  refine ⟨T.symm.trans κ, fun g ℓ => ?_⟩
  obtain ⟨x, rfl⟩ := T.surjective ℓ
  rw [hT x, ← toDual_invTr, ← hT, ← hT, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    T.symm_apply_apply, T.symm_apply_apply, hκ, GlobalTheory.DefiniteBC.invTr_invTr]
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

section
open GlobalTheory.DefU GlobalTheory.Branching
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem irr_emb (τ : E →+* ℂ) (lam : DomWeight n) :
    Representation.IsIrreducible ((sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype)) := by
  obtain ⟨e, he⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n τ
  have heq : (sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype) =
      (smallRep (unitaryIncl n) lam).comp e.toMulEquiv.toMonoidHom := by
    ext x : 1
    change sqRep ℂ n lam (cEmb τ (x : UA E n)) = sqRep ℂ n lam (unitaryIncl n (e x))
    rw [he]
  rw [heq]
  exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv _ e.toMulEquiv (isIrreducible_smallRep_unitary n lam)

private noncomputable def locRep (τ : E →+* ℂ) (lam : DomWeight n) :
    Representation ℂ ((embU n τ).subgroupOf (infU E n)) (nablaSq ℂ n lam) :=
  (sqRep ℂ n lam).comp ((cEmb τ).comp ((infU E n).subtype.comp (Subgroup.subtype _)))

private theorem irr_locRep (τ : E →+* ℂ) (lam : DomWeight n) : (locRep τ lam).IsIrreducible :=
  GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv _ (Subgroup.subgroupOfEquivOfLe (embU_le_infU τ)) (irr_emb τ lam)

private noncomputable def repN {m : ℕ} (N : Submodule ℂ (Fin m → UA E n → ℂ))
    (hN : ∀ x ∈ infU E n, ∀ F ∈ N, (fun k => RU E n x (F k)) ∈ N) : Representation ℂ (infU E n) N where
  toFun x :=
    { toFun := fun F => ⟨fun k => RU E n x (F.1 k), hN x x.2 F.1 F.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext F k g
    simp
  map_mul' x y := by
    ext F k : 3
    exact (RU_RU x.1 y.1 (F.1 k)).symm

private theorem isoN {m : ℕ} (N : Submodule ℂ (Fin m → UA E n → ℂ))
    (hN : ∀ x ∈ infU E n, ∀ F ∈ N, (fun k => RU E n x (F k)) ∈ N) (σ : Submodule ℂ (UA E n → ℂ))
    (hσ : IsAutRepU σ) (hNσ : ∀ F ∈ N, ∀ k, F k ∈ σ) (τ : E →+* ℂ) (lam : DomWeight n) (h : HasWeightAt σ τ lam) :
    (⨆ f : {f : nablaSq ℂ n lam →ₗ[ℂ] N // ∀ (g : (embU n τ).subgroupOf (infU E n)) v,
      f (locRep τ lam g v) = repN N hN g (f v)}, LinearMap.range f.1) = ⊤ := by
  let π : AutSub E n := ⟨σ, hσ⟩
  have h1 := iSup_range_weight_eq_top E n π τ lam h
  refine UpperTheory.isotypic_of_jointly_injective_into_isotypic _ _ π.V (locRep τ lam) (π.rep.comp ((infU E n).subtype.comp (Subgroup.subtype _)))
    (irr_locRep τ lam) ?_ N ((repN N hN).comp (Subgroup.subtype _)) (Fin m)
    (fun k => ((LinearMap.proj k).comp N.subtype).codRestrict σ fun F => hNσ F.1 F.2 k) (fun _ _ _ => rfl)
    (fun y hy => Subtype.ext (funext fun k => congrArg Subtype.val (hy k)))
  refine top_le_iff.1 (h1.ge.trans (iSup_le fun f => ?_))
  exact le_iSup_of_le ⟨f.toLinearMap, fun g v => LinearMap.congr_fun (f.isIntertwining' ⟨g.1.1, g.2⟩) v⟩ le_rfl

private theorem exists_multi {I : Type} [Finite I] (emb : I → (E →+* ℂ))
    (hb : Function.Bijective (fun i => InfinitePlace.mk (emb i))) (lam : I → DomWeight n)
    (σ : Submodule ℂ (UA E n → ℂ)) (hσ : IsAutRepU σ) (hw : ∀ i, HasWeightAt σ (emb i) (lam i)) {m : ℕ}
    (N : Submodule ℂ (Fin m → UA E n → ℂ)) (h0 : N ≠ ⊥) (hNσ : ∀ F ∈ N, ∀ k, F k ∈ σ)
    (hN : ∀ x ∈ infU E n, ∀ F ∈ N, (fun k => RU E n x (F k)) ∈ N) :
    ∃ μ : MultilinearMap (RingHom.id ℂ) (fun i => nablaSq ℂ n (lam i)) N, μ ≠ 0 ∧ ∀ x ∈ infU E n, ∀ v k,
      RU E n x ((μ v).1 k) = (μ fun i => sqRep ℂ n (lam i) (cEmb (emb i) x) (v i)).1 k := by
  classical
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 h0
  obtain ⟨hgen, hcomm⟩ := UpperTheory.archimedeanUnitary_le_iSup_embU_and_commute E n
  obtain ⟨μ, hμ0, hμ⟩ := UpperTheory.exists_multilinear_intertwiner_of_commuting_subgroups (infU E n) I (fun i => (embU n (emb i)).subgroupOf (infU E n))
    (fun i j hij a ha b hb' => Subtype.ext (hcomm (emb i) (emb j) (fun e => hij (hb.1 e)) a.1 ha b.1 hb'))
    (fun i => nablaSq ℂ n (lam i)) (fun i => locRep (emb i) (lam i)) (fun i => irr_locRep _ _) N (repN N hN)
    (fun i => isoN N hN σ hσ hNσ (emb i) (lam i) (hw i))
  refine ⟨μ, hμ0, fun x hx => ?_⟩
  refine Subgroup.iSup_induction _ (C := fun x => ∀ v k,
      RU E n x ((μ v).1 k) = (μ fun i => sqRep ℂ n (lam i) (cEmb (emb i) x) (v i)).1 k) (hgen hx) ?_ ?_ ?_
  · intro τ y hy v k
    obtain ⟨i, hi⟩ := hb.2 (InfinitePlace.mk τ)
    have hi' : InfinitePlace.mk (emb i) = InfinitePlace.mk τ := hi
    have hy' : y ∈ embU n (emb i) := by
      unfold embU at hy ⊢
      rwa [hi']
    have h2 := hμ i ⟨⟨y, embU_le_infU _ hy'⟩, hy'⟩ v
    have h3 : (fun j => sqRep ℂ n (lam j) (cEmb (emb j) y) (v j)) =
        Function.update v i (locRep (emb i) (lam i) ⟨⟨y, embU_le_infU _ hy'⟩, hy'⟩ (v i)) := by
      funext j
      by_cases e : j = i
      · subst e
        rw [Function.update_self]
        rfl
      · have h4 := (Subgroup.mem_inf.1 hy').2
        rw [Subgroup.mem_iInf] at h4
        have h5 := h4 (emb j)
        rw [Subgroup.mem_iInf] at h5
        have h6 : cEmb (emb j) y = 1 := h5 fun e' => e (hb.1 e')
        rw [Function.update_of_ne e, h6, map_one, Module.End.one_apply]
    rw [h3, h2]
    rfl
  · intro v k
    simp only [map_one, Module.End.one_apply]
  · intro a b ha hb v k
    rw [← RU_RU, hb, ha]
    simp only [map_mul, Module.End.mul_apply]

end

private theorem dualDistrib_comp_map {I : Type} [Finite I] {M : I → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (f : ∀ i, Module.Dual ℂ (M i)) (g : ∀ i, M i →ₗ[ℂ] M i) :
    PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ f) ∘ₗ PiTensorProduct.map g =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ fun i => f i ∘ₗ g i) := by
  have := Fintype.ofFinite I
  ext v
  simp [PiTensorProduct.dualDistrib_apply]

theorem UpperTheory.exists_tensor_dual_embedding_of_hasWeightAt :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (I : Type) [Finite I] (emb : I → (E →+* ℂ)), Function.Bijective (fun i => InfinitePlace.mk (emb i)) → ∀ (lam : I → DomWeight n) (σ : Submodule ℂ (UA E n → ℂ)), IsAutRepU σ → (∀ i, HasWeightAt σ (emb i) (lam i).dual) → ∀ (m : ℕ) (N : Submodule ℂ (Fin m → UA E n → ℂ)), N ≠ ⊥ → (∀ F ∈ N, ∀ k, F k ∈ σ) → (∀ x ∈ infU E n, ∀ F ∈ N, (fun k => RU E n x (F k)) ∈ N) → ∃ Φ : Module.Dual ℂ (⨂[ℂ] i : I, nablaSq ℂ n (lam i)) →ₗ[ℂ] (Fin m → UA E n → ℂ), Φ ≠ 0 ∧ (∀ ℓ, Φ ℓ ∈ N) ∧ ∀ ℓ, ∀ x ∈ infU E n, ∀ k, RU E n x (Φ ℓ k) = Φ (ℓ ∘ₗ PiTensorProduct.map fun i => GlobalTheory.Branching.sqRep ℂ n (lam i) (cEmb (emb i) x⁻¹)) k := by
  intro E _ _ _ n hn I _ emb hb lam σ hσ hw m N h0 hNσ hN
  obtain ⟨μ, hμ0, hμ⟩ := exists_multi emb hb (fun i => (lam i).dual) σ hσ hw N h0 hNσ hN
  choose κ hκ using fun i => UpperTheory.exists_dual_schur_module_iso_dual_weight n hn (lam i)
  let D := PiTensorProduct.dualDistribEquiv (R := ℂ) (M := fun i => nablaSq ℂ n (lam i))
  have hD : ∀ t, D t = PiTensorProduct.dualDistrib t := fun _ => rfl
  let Ψ := PiTensorProduct.lift (μ.compLinearMap fun i => (κ i).toLinearMap)
  have hΦ : ∀ f, (N.subtype ∘ₗ Ψ ∘ₗ D.symm.toLinearMap) (D (PiTensorProduct.tprod ℂ f)) =
      (μ fun i => κ i (f i)).1 := by
    intro f
    change (Ψ (D.symm (D _))).1 = _
    rw [D.symm_apply_apply, PiTensorProduct.lift.tprod]
    rfl
  refine ⟨N.subtype ∘ₗ Ψ ∘ₗ D.symm.toLinearMap, fun h => hμ0 ?_, fun ℓ => (Ψ (D.symm ℓ)).2, fun ℓ x hx k => ?_⟩
  · ext v : 1
    have := hΦ fun i => (κ i).symm (v i)
    rw [h] at this
    simp only [LinearEquiv.apply_symm_apply] at this
    exact Subtype.ext this.symm
  · obtain ⟨t, rfl⟩ := D.surjective ℓ
    generalize (N.subtype ∘ₗ Ψ ∘ₗ D.symm.toLinearMap) = Φ at hΦ
    induction t using PiTensorProduct.induction_on with
    | smul_tprod c f =>
      rw [map_smul, LinearMap.smul_comp, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, map_smul]
      congr 1
      rw [hΦ, hμ x hx, hD, dualDistrib_comp_map, ← hD, hΦ]
      simp only [map_inv (cEmb _), hκ]
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_comp, Pi.add_apply, ha, hb]
end
