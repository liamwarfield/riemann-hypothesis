module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpoCo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.AmFin

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PatchedModuleFreeFiniteOverIwasawaAlgebra
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem tens_free {Λ B S M X : Type} [CommRing Λ] [CommRing B] [CommRing S] [Algebra B S]
    [AddCommGroup M] [Module B M] [Module Λ M] [Module.Free B S] [Module.Finite B S]
    [Module.Free Λ M] [Module.Finite Λ M] [Nontrivial B] [AddCommGroup X] [Module Λ X]
    (lam : Λ → B) (hl : ∀ (a : Λ) (m : M), a • m = lam a • m) (e : X ≃+ S ⊗[B] M)
    (he : ∀ (a : Λ) (x : X), e (a • x) = algebraMap B S (lam a) • e x) :
    Module.Free Λ X ∧ Module.Finite Λ X := by
  classical
  let φ : S ⊗[B] M ≃ₗ[B] (Module.Free.ChooseBasisIndex B S →₀ M) :=
    (TensorProduct.congr (Module.Free.chooseBasis B S).repr (LinearEquiv.refl B M)).trans
      (TensorProduct.finsuppScalarLeft B M _)
  have key : ∀ (a : Λ) (x : X), φ (e (a • x)) = a • φ (e x) := by
    intro a x
    rw [he, algebraMap_smul, map_smul]
    ext i
    simp only [Finsupp.smul_apply, hl]
  let ψ : X ≃ₗ[Λ] (Module.Free.ChooseBasisIndex B S →₀ M) :=
    { toFun := fun x => φ (e x)
      invFun := fun f => e.symm (φ.symm f)
      map_add' := fun x y => by simp
      map_smul' := key
      left_inv := fun x => by simp
      right_inv := fun f => by simp }
  exact ⟨Module.Free.of_equiv ψ.symm, Module.Finite.equiv ψ.symm⟩

theorem UpperTheory.V.Pa.Core.patchedModule_free_finite_over_iwasawaAlgebra :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → Module.Free (abelian₂ O Unit D) (X0 m) ∧ Module.Finite (abelian₂ O Unit D) (X0 m) ∧ (∀ (a : abelian₂ O Unit D) (x : X0 m), a • x = m.s.toRingHom (MvPowerSeries.C a) • x) ∧ ∀ p (x : X0 m), m.s.toRingHom (MvPowerSeries.X p) • x = 0 := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hT
  obtain ⟨⟨hco, hfree, hfin, -⟩, -⟩ := spoCo l L G0 T Λ n O r B u J D A hT
  haveI := A.b.free
  haveI := A.b.fin
  haveI := hfree
  haveI := hfin
  have hs : ∀ (t : W.R) (x : X0 m), t • x = m.π t • x := fun _ _ => rfl
  obtain ⟨h1, h2⟩ := tens_free (Λ := abelian₂ O Unit D) (X := X0 m) A.b.lam A.b.smul_lam (AddEquiv.refl _)
    (fun a x => X0.lam_smul_def m a x)
  refine ⟨h1, h2, fun a x => ?_, fun p x => ?_⟩
  · rw [X0.lam_smul_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hs, m.π_s,
      MvPowerSeries.constantCoeff_C]
  · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hs, m.π_s, MvPowerSeries.constantCoeff_X,
      map_zero, map_zero, zero_smul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.EventuallyTraceInertiaCongruenceOfAdapted
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem lam_push {n : ℕ} {R S H G : Type} [CommRing R] [CommRing S] [Group H] [Group G]
    {E : GDet n R H} {D : GDet n S G} {f : R →+* S} {φ : H →* G}
    (h : E.map f = D.comap φ) (i : ℕ) (y : MonoidAlgebra R H) :
    f (E.lam i y) = D.lam i (MonoidAlgebra.mapDomainRingHom S φ (MonoidAlgebra.mapRingHom H f y)) := by
  rw [← ((UpperTheory.V.CA.d_gmap E).2.2.1 f y).2 i, h]
  unfold GDet.lam
  generalize MonoidAlgebra.mapRingHom H f y = z
  congr 2
  change (D.D (Polynomial S) (MonoidAlgebra.mapDomainRingHom (Polynomial S) φ _)).coeff =
    (D.D (Polynomial S) _).coeff
  ext k
  have hcomm : ∀ z : MonoidAlgebra S H,
      MonoidAlgebra.mapDomainRingHom (Polynomial S) φ (MonoidAlgebra.mapRingHom H Polynomial.C z) =
        MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom S φ z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp
  congr 1
  rw [map_sub]
  rw [hcomm]
  simp

theorem UpperTheory.V.Pa.Core.eventually_trace_inertia_congruence_of_adapted :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (w : L.St) (g : L.Gu w) (ga h : Ph0 Λ), g ∈ L.Ju w → πo0 Λ ga = Λ.G.φu w g → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single ga 1 - 1)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m had w g ga h hg hga j
  obtain ⟨V, hV0, hV⟩ := phSees l L G0 T Λ n O r B u J D A W j
  filter_upwards [Λ.ker_lim V, Λ.φu_lim V] with N hk hφ
  obtain ⟨g', hg', hgv⟩ := (closeLift _ _ _ (Λ.π N) Λ.πo V.toSubgroup hk).1 _ _ (ga : Λ.Ph) (hφ w g)
    (congrArg Subtype.val hga)
  have hm : g' ∈ Ph0 Λ := by
    simpa using mul_mem ga.2 (hV0 hgv)
  let gN : Ph0 Λ := ⟨g', hm⟩
  have e0 : πN0 Λ N gN = (T.GN N).φu w g := Subtype.ext hg'
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single gN 1 - 1)), hV 1 _ _ ?_, Or.inl ?_⟩
  · have e : QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) ga =
        QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) gN := QuotientGroup.eq.2 hgv
    simp only [map_mul, map_sub, map_one, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, e]
  · have e1 : πN0 Λ N gN ∈ (A.A N).rN.Ip w := by
      rw [e0]
      refine ⟨⟨g, hg, rfl⟩, Subgroup.mem_iInf.2 fun i => ?_⟩
      have h1 : G0.φu w g ∈ r.Ip w := by
        rw [had.2]
        exact ⟨g, hg, rfl⟩
      rw [MonoidHom.mem_ker, (A.A N).compat.1 i, MonoidHom.comp_apply, (T.h N).p₀_φu]
      exact Subgroup.mem_iInf.1 h1.2 i
    have hl := lam_push (m.ρ_maps N).1 1 (MonoidAlgebra.single h 1 * (MonoidAlgebra.single gN 1 - 1))
    simp only [map_mul, map_sub, map_one, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single] at hl
    exact hl.trans ((A.A N).p.I w _ e1 _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.MapRingHomSingleMulCharpolyElement
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem lam_dom {n : ℕ} {S H G : Type} [CommRing S] [Group H] [Group G] (D : GDet n S G) (φ : H →* G)
    (i : ℕ) (z : MonoidAlgebra S H) : (D.comap φ).lam i z = D.lam i (MonoidAlgebra.mapDomainRingHom S φ z) := by
  unfold GDet.lam
  congr 2
  change (D.D (Polynomial S) (MonoidAlgebra.mapDomainRingHom (Polynomial S) φ _)).coeff =
    (D.D (Polynomial S) _).coeff
  ext k
  have hcomm : ∀ z : MonoidAlgebra S H,
      MonoidAlgebra.mapDomainRingHom (Polynomial S) φ (MonoidAlgebra.mapRingHom H Polynomial.C z) =
        MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom S φ z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp
  congr 1
  rw [map_sub]
  rw [hcomm]
  simp

private theorem mapDomain_single_mul_charpoly_element {n : ℕ} {S H G : Type} [CommRing S] [Group H] [Group G] (φ : H →* G) (h g : H)
    (U : Fin n → S) : MonoidAlgebra.mapDomainRingHom S φ (MonoidAlgebra.single h 1 * q1El g U) =
      MonoidAlgebra.single (φ h) 1 * q1El (φ g) U := by
  rw [map_mul, q1El, q1El, map_list_prod, List.map_ofFn]
  congr 1
  · simp
  · congr 2
    funext i
    rw [Function.comp_apply, map_sub]
    simp

private theorem mapRingHom_single_mul_charpoly_element {n : ℕ} {R S H : Type} [CommRing R] [CommRing S] [Group H] (f : R →+* S) (h g : H)
    (U : Fin n → R) : MonoidAlgebra.mapRingHom H f (MonoidAlgebra.single h 1 * q1El g U) =
      MonoidAlgebra.single h 1 * q1El g fun i => f (U i) := by
  rw [map_mul, q1El, q1El, map_list_prod, List.map_ofFn, MonoidAlgebra.mapRingHom_single, map_one]
  congr 3
  funext i
  simp

theorem UpperTheory.V.Pa.Core.t3Q1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (a : Fin T.q) (ph h : Ph0 Λ), πo0 Λ ph = Λ.ph a → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * q1El ph (W.t.U a)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m _ a ph h hph j
  obtain ⟨V, hV0, hV⟩ := phSees l L G0 T Λ n O r B u J D A W j
  filter_upwards [Λ.ker_lim V, Λ.ph_lim V] with N hk hc
  obtain ⟨g', hg', hgV⟩ := (closeLift _ _ _ (Λ.π N) Λ.πo V.toSubgroup hk).1 _ _ (ph : Λ.Ph) (hc a)
    (congrArg Subtype.val hph)
  have hmem : g' ∈ Ph0 Λ := by
    have := mul_mem ph.2 (hV0 hgV)
    rwa [mul_inv_cancel_left] at this
  let p' : Ph0 Λ := ⟨g', hmem⟩
  have hp' : πN0 Λ N p' = T.ph N a := Subtype.ext hg'
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * q1El p' (W.t.U a)), hV 1 _ _ ?_, Or.inr fun x => ?_⟩
  · have e : QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) ph =
        QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) p' :=
      QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hgV)
    rw [mapDomain_single_mul_charpoly_element, mapDomain_single_mul_charpoly_element, e]
  · obtain ⟨hD, -, -, hU, -⟩ := m.ρ_maps N
    have e : m.ρ N (W.t.D.tr (MonoidAlgebra.single h 1 * q1El p' (W.t.U a))) =
        (A.A N).p.D.tr (MonoidAlgebra.single (πN0 Λ N h) 1 * q1El (T.ph N a) ((A.A N).U a)) := by
      have h1 := ((UpperTheory.V.CA.d_gmap W.t.D).2.2.1 (m.ρ N).toRingHom
        (MonoidAlgebra.single h 1 * q1El p' (W.t.U a))).2 1
      rw [hD, lam_dom, mapRingHom_single_mul_charpoly_element, mapDomain_single_mul_charpoly_element, hp', funext (hU a)] at h1
      exact h1.symm
    rw [e]
    exact (A.m N).rel1 a _ x
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PatchedTraceSingleMulSubOneApproxAnnihilated
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem tr_zero {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (hn : 1 ≤ n) : D.tr 0 = 0 := by
  have h1 : (MonoidAlgebra.single (1 : G) (Polynomial.X : Polynomial A))
      = (Polynomial.X : Polynomial A) • (1 : MonoidAlgebra (Polynomial A) G) := by
    rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single', mul_one]
  have hchi : D.chi 0 = Polynomial.X ^ n := by
    simp only [GDet.chi, map_zero, sub_zero]
    rw [h1, D.homog, map_one, mul_one]
  simp only [GDet.tr, GDet.lam, hchi, Polynomial.coeff_X_pow]
  rw [if_neg (by omega)]
  simp

theorem UpperTheory.V.Pa.Core.patched_trace_single_mul_sub_one_approx_annihilated :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), 1 ≤ n → Adapted T (r := r) → ∀ (h k : Ph0 Λ), πo0 Λ k = 1 → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k 1 - 1)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hn _ h k hk j
  obtain ⟨V, hVle, hV⟩ := phSees l L G0 T Λ n O r B u J D A W j
  refine (Λ.ker_lim V).mono fun N hN => ?_
  have hk1 : Λ.πo (k : Λ.Ph) = 1 := congrArg Subtype.val hk
  have hkmem : (k : Λ.Ph) ∈ (Λ.π N).ker ⊔ (V.toOpenSubgroup : Subgroup Λ.Ph) := by
    rw [hN]
    exact Subgroup.mem_sup_left hk1
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.1 hkmem
  have haPh : a ∈ Ph0 Λ := by
    have : a = (k : Λ.Ph) * b⁻¹ := by rw [← hab]; group
    rw [this]
    exact (Ph0 Λ).mul_mem k.2 ((Ph0 Λ).inv_mem (hVle hb))
  set k' : Ph0 Λ := ⟨a, haPh⟩ with hk'
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1)), ?_, Or.inl ?_⟩
  · have hq : (QuotientGroup.mk' ((V.toOpenSubgroup : Subgroup Λ.Ph).subgroupOf (Ph0 Λ))) k
        = QuotientGroup.mk' ((V.toOpenSubgroup : Subgroup Λ.Ph).subgroupOf (Ph0 Λ)) k' := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : ((k⁻¹ * k' : Ph0 Λ) : Λ.Ph) = b⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hk']
        rw [← hab]
        group
      rw [this]
      exact inv_mem hb
    have hxy : (MonoidAlgebra.mapDomainRingHom W.R
          (QuotientGroup.mk' ((V.toOpenSubgroup : Subgroup Λ.Ph).subgroupOf (Ph0 Λ))))
          (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k 1 - 1))
        = (MonoidAlgebra.mapDomainRingHom W.R
          (QuotientGroup.mk' ((V.toOpenSubgroup : Subgroup Λ.Ph).subgroupOf (Ph0 Λ))))
          (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1)) := by
      simp only [map_mul, map_sub, map_one, MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single, hq]
    exact hV 1 _ _ hxy
  · have hπ : πN0 Λ N k' = 1 := Subtype.ext (MonoidHom.mem_ker.1 ha)
    have hmaps := (m.ρ_maps N).1
    have h1 := ((UpperTheory.V.CA.d_gmap W.t.D).2.2.1 (m.ρ N).toRingHom
      (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))).2 1
    have hy : (MonoidAlgebra.mapRingHom (Ph0 Λ) (m.ρ N).toRingHom)
        (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))
        = MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1) := by
      simp
    have h2 := (comap_lam n _ _ _ (πN0 Λ N) (A.A N).p.D).2.2.1
      (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))
    have h3 : (MonoidAlgebra.mapDomainRingHom (A.A N).R (πN0 Λ N))
        (MonoidAlgebra.single h (1 : (A.A N).R) * (MonoidAlgebra.single k' (1 : (A.A N).R) - 1)) = 0 := by
      rw [map_mul, map_sub, map_one]
      simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, hπ]
      rw [← MonoidAlgebra.one_def, sub_self, mul_zero]
    calc m.ρ N (W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1)))
        = (m.ρ N).toRingHom (W.t.D.lam 1 (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))) := rfl
      _ = (W.t.D.map (m.ρ N).toRingHom).lam 1 ((MonoidAlgebra.mapRingHom (Ph0 Λ) (m.ρ N).toRingHom)
          (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))) := h1.symm
      _ = ((A.A N).p.D.comap (πN0 Λ N)).tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1)) := by
          rw [hy, hmaps]
          rfl
      _ = 0 := by rw [h2, h3]; exact tr_zero _ hn
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.MapRingHomSingleMulPartialCharpolyElement
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem mapDomain_partial_charpoly_power_zero {n : ℕ} {R G H : Type} [CommRing R] [Group G] [Group H] (φ : G →* H) (h ph ta : G)
    (u : Fin n → R) (i : Fin n) (y : R) :
    MonoidAlgebra.mapDomainRingHom R φ (MonoidAlgebra.single h 1 * q2El ph ta u i y) =
      MonoidAlgebra.single (φ h) 1 * q2El (φ ph) (φ ta) u i y := by
  have hs : ∀ (g : G) (c : R), MonoidAlgebra.mapDomainRingHom R φ (MonoidAlgebra.single g c) =
      MonoidAlgebra.single (φ g) c := fun g c => by simp
  simp only [q2El, map_mul, map_sub, map_one, map_list_prod, List.map_ofFn, hs]
  congr 4
  funext k
  by_cases hk : k = i
  · simp only [Function.comp_apply, if_pos hk, map_one]
  · simp only [Function.comp_apply, if_neg hk, map_sub, hs, map_one]

private theorem mapRingHom_single_mul_partial_charpoly_element {n : ℕ} {R S G : Type} [CommRing R] [CommRing S] [Group G] (f : R →+* S) (h ph ta : G)
    (u : Fin n → R) (i : Fin n) (y : R) :
    MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single h 1 * q2El ph ta u i y) =
      MonoidAlgebra.single h 1 * q2El ph ta (fun k => f (u k)) i (f y) := by
  have hs : ∀ (g : G) (c : R), MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g c) =
      MonoidAlgebra.single g (f c) := fun g c => by simp
  simp only [q2El, map_mul, map_sub, map_one, map_list_prod, List.map_ofFn, hs]
  congr 4
  funext k
  by_cases hk : k = i
  · simp only [Function.comp_apply, if_pos hk, map_one]
  · simp only [Function.comp_apply, if_neg hk, map_sub, hs, map_one]

private theorem comap_tr {n : ℕ} {R G H : Type} [CommRing R] [Group G] [Group H] (D : GDet n R H) (φ : G →* H)
    (z : MonoidAlgebra R G) : (D.comap φ).tr z = D.tr (MonoidAlgebra.mapDomainRingHom R φ z) := by
  have hc : (D.comap φ).chi z = D.chi (MonoidAlgebra.mapDomainRingHom R φ z) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom (Polynomial R) φ _) = D.D _ _
    congr 1
    rw [map_sub]
    congr 1
    · simp
    · induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | single g r => simp
  simp only [GDet.tr, GDet.lam, hc]

theorem UpperTheory.V.Pa.Core.t3Q2 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (a : Fin T.q) (i : Fin n) (ph ta h : Ph0 Λ), πo0 Λ ph = Λ.ph a → πo0 Λ ta = Λ.ta a → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * q2El ph ta (W.t.U a) i (W.t.y a i)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m _ a i ph ta h hph hta j
  obtain ⟨V, hV0, hV⟩ := UpperTheory.V.Pa.Core.phSees l L G0 T Λ n O r B u J D A W j
  filter_upwards [Λ.ker_lim V, Λ.ph_lim V, Λ.ta_lim V] with N hk h1 h2
  have lift : ∀ (g : Ph0 Λ) (x : (T.GN N).G₀) (b : Λ.G.G₀), Close (Λ.π N) Λ.πo V.toSubgroup (x : (T.GN N).Γ) (b : Λ.G.Γ) →
      πo0 Λ g = b → ∃ g' : Ph0 Λ, πN0 Λ N g' = x ∧
        QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) g = QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) g' := by
    intro g x b hc hg
    obtain ⟨g', e, hv⟩ := (UpperTheory.V.Pa.Core.closeLift _ _ _ (Λ.π N) Λ.πo V.toSubgroup hk).1 _ _ (g : Λ.Ph) hc
      (congrArg Subtype.val hg)
    have hm : g' ∈ Ph0 Λ := by
      have := (Ph0 Λ).mul_mem g.2 (hV0 hv)
      rwa [mul_inv_cancel_left] at this
    exact ⟨⟨g', hm⟩, Subtype.ext e, QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hv)⟩
  obtain ⟨ph', e1, q1⟩ := lift ph _ _ (h1 a) hph
  obtain ⟨ta', e2, q2⟩ := lift ta _ _ (h2 a) hta
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * q2El ph' ta' (W.t.U a) i (W.t.y a i)), ?_, Or.inr fun x => ?_⟩
  · apply hV 1
    rw [mapDomain_partial_charpoly_power_zero, mapDomain_partial_charpoly_power_zero, q1, q2]
  · obtain ⟨hD, -, -, hU, hy⟩ := m.ρ_maps N
    have key : m.ρ N (W.t.D.tr (MonoidAlgebra.single h 1 * q2El ph' ta' (W.t.U a) i (W.t.y a i))) =
        (A.A N).p.D.tr (MonoidAlgebra.single (πN0 Λ N h) 1 *
          q2El (T.ph N a) (T.ta N a) ((A.A N).U a) i ((A.A N).s (MvPowerSeries.X (a, i)))) := by
      have h3 := ((UpperTheory.V.CA.d_gmap W.t.D).2.2.1 (m.ρ N).toRingHom
        (MonoidAlgebra.single h 1 * q2El ph' ta' (W.t.U a) i (W.t.y a i))).2 1
      refine h3.symm.trans ?_
      rw [hD, mapRingHom_single_mul_partial_charpoly_element, hy a i, funext (hU a)]
      refine (comap_tr _ _ _).trans ?_
      rw [mapDomain_partial_charpoly_power_zero, e1, e2]
    rw [key]
    exact (A.m N).rel2 a i _ x
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PatchedTraceLocalCharPolyApproxAnnihilated
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem gDet_chi_map_mapRingHom {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G]
    (D : GDet n R G) (f : R →+* R') (x : MonoidAlgebra R G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f x) = (D.chi x).map f := by
  unfold GDet.chi GDet.map
  dsimp only
  letI : Algebra R (Polynomial R') := ((algebraMap R' (Polynomial R')).comp f).toAlgebra
  let g : Polynomial R →ₐ[R] Polynomial R' :=
    { Polynomial.mapRingHom f with
      commutes' := fun c => by
        simp [RingHom.algebraMap_toAlgebra, Polynomial.algebraMap_apply] }
  have h := D.nat (Polynomial R) (Polynomial R') g
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C x)
  refine Eq.trans ?_ h
  congr 1
  rw [map_sub]
  congr 1
  · ext a
    simp [g, MonoidAlgebra.mapRingHom, Polynomial.mapRingHom]
  · ext a
    simp [g, MonoidAlgebra.mapRingHom, Polynomial.mapRingHom]

private theorem gDet_tr_map_mapRingHom {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G]
    (D : GDet n R G) (f : R →+* R') (x : MonoidAlgebra R G) :
    (D.map f).tr (MonoidAlgebra.mapRingHom G f x) = f (D.tr x) := by
  unfold GDet.tr GDet.lam
  rw [gDet_chi_map_mapRingHom, Polynomial.coeff_map]
  simp

private theorem gDet_tr_comap_eq_tr_mapDomainRingHom {n : ℕ} {R G H : Type} [CommRing R] [Group G] [Group H]
    (D : GDet n R G) (φ : H →* G) (x : MonoidAlgebra R H) :
    (D.comap φ).tr x = D.tr (MonoidAlgebra.mapDomainRingHom R φ x) := by
  unfold GDet.tr GDet.lam GDet.chi GDet.comap
  dsimp only
  rw [MonoidHom.comp_apply]
  congr 3
  congr 1
  show MonoidAlgebra.mapDomainRingHom (Polynomial R) φ _ = _
  rw [map_sub]
  congr 1
  · simp [MonoidAlgebra.mapDomainRingHom_apply]
  · ext a
    simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapRingHom]
    rw [Finsupp.mapDomain_mapRange _ _ _ _ (fun a b => Polynomial.C_add)]
    simp

theorem UpperTheory.V.Pa.Core.patched_trace_local_charPoly_approx_annihilated :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (v : L.Vl) (g : Fin n → L.Gv v) (ga : Fin n → Ph0 Λ) (h : Ph0 Λ), (∀ i, πo0 Λ (ga i) = Λ.G.φ v (g i)) → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * (List.ofFn fun i => MonoidAlgebra.single (ga i) (1 : W.R) - MonoidAlgebra.single 1 ((W.t.ψ v i (g i) : W.Rˣ) : W.R)).prod) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hT v g ga h hga j
  obtain ⟨V, hVle, hsees⟩ := phSees l L G0 T Λ n O r B u J D A W j
  filter_upwards [Λ.ker_lim V, Λ.φ_lim V] with N hker hφ
  have hπo : ∀ i, Λ.πo (ga i) = ((Λ.G.φ v (g i) : Λ.G.G₀) : Λ.G.Γ) := fun i =>
    congrArg Subtype.val (hga i)
  have lift : ∀ i, ∃ x : Λ.Ph, Λ.π N x = (((T.GN N).φ v (g i) : (T.GN N).G₀) : (T.GN N).Γ) ∧
      (ga i : Λ.Ph)⁻¹ * x ∈ (V.toOpenSubgroup : Subgroup Λ.Ph) := fun i =>
    (closeLift _ _ _ (Λ.π N) Λ.πo _ hker).1 _ _ (ga i) (hφ v (g i)) (hπo i)
  choose x hx1 hx2 using lift
  have hmem : ∀ i, x i ∈ Ph0 Λ := fun i => by
    have := (Ph0 Λ).mul_mem (ga i).2 (hVle (hx2 i))
    simpa using this
  let gb : Fin n → Ph0 Λ := fun i => ⟨x i, hmem i⟩
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * (List.ofFn fun i =>
    MonoidAlgebra.single (gb i) (1 : W.R) - MonoidAlgebra.single 1 ((W.t.ψ v i (g i) : W.Rˣ) : W.R)).prod), ?_, Or.inl ?_⟩
  · refine hsees 1 _ _ ?_
    simp only [map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single]
    congr 2
    congr 1
    funext i
    congr 2
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hx2 i
  · show (m.ρ N).toRingHom _ = 0
    rw [← gDet_tr_map_mapRingHom, (m.ρ_maps N).1, gDet_tr_comap_eq_tr_mapDomainRingHom]
    refine Eq.trans ?_ ((A.A N).p.Ord v g (πN0 Λ N h))
    congr 1
    unfold GFrame.oEl
    simp only [map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapRingHom_single, map_one]
    congr 2
    congr 1
    funext i
    rw [← (m.ρ_maps N).2.1 v i]
    congr 2
    exact Subtype.ext (hx1 i)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PiSurj
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem mem_iff {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (y : R) :
    f y ∈ maximalIdeal R' ↔ y ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem surj_of_gen {O : Type} [CommRing O] [IsLocalRing O] {R B C : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing B] [Algebra O B] [IsCO O B] [CommRing C] [Algebra O C] [IsCO O C] [Algebra B C] [IsScalarTower O B C]
    (f : R →ₐ[O] C) (S : Set B) (U : Set C) (hS : GenBy O S) (hU : Algebra.adjoin B U = ⊤)
    (h1 : ∀ b ∈ S, algebraMap B C b ∈ f.range) (h2 : ∀ c ∈ U, c ∈ f.range) : Function.Surjective f := by
  have hmB : ∀ y : B, algebraMap B C y ∈ maximalIdeal C ↔ y ∈ maximalIdeal B := fun y => by
    simpa using mem_iff (IsScalarTower.toAlgHom O B C) y
  have hpow : ∀ N (y : B), y ∈ maximalIdeal B ^ N → algebraMap B C y ∈ maximalIdeal C ^ N := by
    intro N y hy
    have hle : Ideal.map (algebraMap B C) (maximalIdeal B) ≤ maximalIdeal C := by
      rw [Ideal.map_le_iff_le_comap]
      intro z hz
      exact (hmB z).2 hz
    have h1' : algebraMap B C y ∈ Ideal.map (algebraMap B C) (maximalIdeal B ^ N) :=
      Ideal.mem_map_of_mem _ hy
    rw [Ideal.map_pow] at h1'
    exact Ideal.pow_right_mono hle N h1'
  have hadj : Algebra.adjoin O S ≤ (f.range).comap (IsScalarTower.toAlgHom O B C) := by
    rw [Algebra.adjoin_le_iff]
    intro b hb
    simpa using h1 b hb
  let P : Subalgebra B C :=
    { carrier := {c | ∀ N, ∃ r, c - f r ∈ maximalIdeal C ^ N}
      mul_mem' := by
        intro a b ha hb N
        obtain ⟨r1, hr1⟩ := ha N
        obtain ⟨r2, hr2⟩ := hb N
        refine ⟨r1 * r2, ?_⟩
        have e : a * b - f (r1 * r2) = (a - f r1) * b + f r1 * (b - f r2) := by
          rw [map_mul]
          ring
        rw [e]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hr1) (Ideal.mul_mem_left _ _ hr2)
      add_mem' := by
        intro a b ha hb N
        obtain ⟨r1, hr1⟩ := ha N
        obtain ⟨r2, hr2⟩ := hb N
        refine ⟨r1 + r2, ?_⟩
        have e : a + b - f (r1 + r2) = (a - f r1) + (b - f r2) := by
          rw [map_add (f := _)]
          ring
        rw [e]
        exact Ideal.add_mem _ hr1 hr2
      algebraMap_mem' := by
        intro b N
        obtain ⟨a, ha, hba⟩ := hS N b
        have ha' := hadj ha
        rw [Subalgebra.mem_comap, AlgHom.mem_range] at ha'
        obtain ⟨r, hr⟩ := ha'
        refine ⟨r, ?_⟩
        have hr' : f r = algebraMap B C a := by simpa using hr
        rw [hr', ← map_sub]
        exact hpow N _ hba }
  have hUP : Algebra.adjoin B U ≤ P := by
    rw [Algebra.adjoin_le_iff]
    intro c hc N
    obtain ⟨r, hr⟩ := (AlgHom.mem_range f).1 (h2 c hc)
    exact ⟨r, by rw [hr, sub_self]; exact Ideal.zero_mem _⟩
  have hall : ∀ c : C, ∀ N, ∃ r, c - f r ∈ maximalIdeal C ^ N := by
    intro c
    have hc : c ∈ Algebra.adjoin B U := by
      rw [hU]
      exact Algebra.mem_top
    exact hUP hc
  apply co_surj O R C f
  intro m hm
  obtain ⟨r, hr⟩ := hall m 2
  have hfr : f r ∈ maximalIdeal C := by
    have e : m - (m - f r) = f r := by ring
    rw [← e]
    exact Ideal.sub_mem _ hm (Ideal.pow_le_self two_ne_zero hr)
  have hrm : r ∈ maximalIdeal R := (mem_iff f r).1 hfr
  have e : m = f r + (m - f r) := by ring
  rw [e]
  exact Submodule.add_mem_sup (Ideal.mem_map_of_mem f hrm) hr

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  have e : (MonoidAlgebra.mapDomainRingHom (Polynomial A) φ)
      (MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom H Polynomial.C) (MonoidAlgebra.single g 1))
      = MonoidAlgebra.single 1 Polynomial.X
        - (MonoidAlgebra.mapRingHom G Polynomial.C) (MonoidAlgebra.single (φ g) 1) := by
    rw [map_sub]
    simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
  simp only [GDet.lam, GDet.chi, GDet.comap, MonoidHom.coe_comp, Function.comp_apply]
  exact congrArg (fun y => (-1) ^ i * ((D.D (Polynomial A)) y).coeff (n - i)) e

private theorem lam_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B)
    (i : ℕ) (g : G) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 i
  rwa [MonoidAlgebra.mapRingHom_single, map_one] at this

theorem UpperTheory.V.Pa.Core.piSurj :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → GenBy O (pairVals u ∪ {(A.b.lam (MvPowerSeries.X (.inl ())))}) → Function.Surjective m.π := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hAd hgen
  letI := W.ring
  letI := W.alg
  haveI := W.co
  obtain ⟨⟨hco, -, -, hadj⟩, -⟩ := spoCo l L G0 T Λ n O r B u J D A hAd
  haveI := hco
  obtain ⟨hD, hψ, -, hU, -⟩ := m.π_maps
  have hsurj : Function.Surjective (Λ.h.p₀.comp (πo0 Λ)) :=
    (Glob.Hom.p₀_surj Λ.h).comp (Lim.πo0_surj Λ)
  refine surj_of_gen (O := O) m.π _ _ hgen hadj ?_ ?_
  · intro b hb
    rcases hb with (⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩) | hb
    · obtain ⟨h, rfl⟩ := hsurj g
      refine (AlgHom.mem_range _).2 ⟨W.t.D.lam i (MonoidAlgebra.single h 1), ?_⟩
      have e := congrArg (fun E => E.lam i (MonoidAlgebra.single h 1)) hD
      simp only [lam_map, lam_comap] at e
      exact e
    · refine (AlgHom.mem_range _).2 ⟨↑(W.t.ψ v i g), ?_⟩
      have e := congrArg (fun χ => ((χ g : (Spo A)ˣ) : Spo A)) (hψ v i)
      simpa using e
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      refine (AlgHom.mem_range _).2 ⟨m.s (MvPowerSeries.C (MvPowerSeries.X (Sum.inl ()))), ?_⟩
      rw [m.π_s]
      simp
  · rintro c ⟨p, rfl⟩
    exact (AlgHom.mem_range _).2 ⟨W.t.U p.1 p.2, hU p.1 p.2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.InjOfProd
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.RrGen
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.rrGen :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A), GenBy O ({b | ∃ i g, b = W.t.D.lam i (MonoidAlgebra.single g 1)} ∪ {b | ∃ v i g, b = ((W.t.ψ v i g : W.Rˣ) : W.R)} ∪ {b | ∃ j i, b = W.t.U j i ∨ b = W.t.y j i} ∪ {W.t.s}) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W N x
  refine UpperTheory.V.CA.u_gen O W.R _ (fun R' _ _ _ f f' h => ?_) N x
  refine UpperTheory.V.Pa.Core.rrExt l L G0 T Λ n O r B u J D A W R' f f' (fun i g => h _ ?_) (fun v i g => h _ ?_)
    (h _ ?_) (fun j i => h _ ?_) (fun j i => h _ ?_)
  · exact .inl (.inl (.inl ⟨i, g, rfl⟩))
  · exact .inl (.inl (.inr ⟨v, i, g, rfl⟩))
  · exact .inr rfl
  · exact .inl (.inr ⟨j, i, .inl rfl⟩)
  · exact .inl (.inr ⟨j, i, .inr rfl⟩)
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem chi_rep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly, Matrix.charmatrix]
  congr 2
  · ext1 a b
    by_cases hab : a = b <;> simp [GDet.repAlg, hab, Matrix.one_apply, Matrix.diagonal_apply]
  · ext1 a b
    simp [GDet.repAlg]

private theorem inj_of_prod {n : ℕ} {A : Type} [CommRing A] [IsDomain A] {a b : Fin n → A}
    (h : ∏ i, (Polynomial.X - Polynomial.C (a i)) = ∏ i, (Polynomial.X - Polynomial.C (b i)))
    (hb : Function.Injective b) : Function.Injective a := by
  have e : ∀ c : Fin n → A, (∏ i, (Polynomial.X - Polynomial.C (c i))).roots = Finset.univ.val.map c := fun c => by
    rw [← Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map c), Multiset.map_map]
    rfl
  have h1 : Finset.univ.val.map a = Finset.univ.val.map b := by rw [← e, ← e, h]
  have h2 : (Finset.univ.val.map a).Nodup := h1 ▸ Finset.univ.nodup.map hb
  exact fun i j hij => Multiset.inj_on_of_nodup_map h2 i (Finset.mem_univ_val i) j (Finset.mem_univ_val j) hij

private theorem lam_lift {n : ℕ} {R S H G : Type} [CommRing R] [CommRing S] [Group H] [Group G]
    {E : GDet n R H} {D : GDet n S G} {f : R →+* S} {φ : H →* G}
    (h : D.comap φ = E.map f) (i : ℕ) (y : MonoidAlgebra R H) :
    D.lam i (MonoidAlgebra.mapDomainRingHom S φ (MonoidAlgebra.mapRingHom H f y)) = f (E.lam i y) := by
  rw [← ((UpperTheory.V.CA.d_gmap E).2.2.1 f y).2 i, ← h]
  unfold GDet.lam
  generalize MonoidAlgebra.mapRingHom H f y = z
  apply congrArg (fun p : Polynomial S => (-1) ^ i * p.coeff (n - i))
  change D.D (Polynomial S) _ = D.D (Polynomial S) (MonoidAlgebra.mapDomainRingHom (Polynomial S) φ _)
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp

private theorem rep_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (φ : H →* G) : (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ) := by
  refine GDet.ext fun S _ _ z => ?_
  change (GDet.repAlg ρ S (MonoidAlgebra.mapDomainRingHom S φ z)).det = (GDet.repAlg (ρ.comp φ) S z).det
  congr 1
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => simp [GDet.repAlg]

private theorem genBy_img {O R S : Type} [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] [CommRing S]
    [Algebra O S] [IsLocalRing S] (f : R →ₐ[O] S) (hf : Function.Surjective f) {s : Set R} {t : Set S}
    (h : GenBy O s) (hst : ∀ a ∈ s, f a ∈ t) : GenBy O t := by
  intro N b
  obtain ⟨b, rfl⟩ := hf b
  obtain ⟨a, ha, hb⟩ := h N b
  haveI : IsLocalHom (f : R →+* S) := IsLocalHom.of_surjective _ hf
  refine ⟨f a, ?_, ?_⟩
  · have : Algebra.adjoin O s ≤ (Algebra.adjoin O t).comap f :=
      Algebra.adjoin_le fun c hc => Algebra.subset_adjoin (hst c hc)
    exact this ha
  · rw [← map_sub]
    have h1 : (maximalIdeal R).map (f : R →+* S) ≤ maximalIdeal S :=
      Ideal.map_le_iff_le_comap.2 fun c hc => map_nonunit (f : R →+* S) c hc
    have h2 := Ideal.mem_map_of_mem (f : R →+* S) hb
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 N h2

theorem UpperTheory.V.Pa.Core.ooPt :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) [IsCO O (W.R ⧸ ii W)] (o : OoPair W) (πb : (W.R ⧸ ii W) →ₐ[O] Spo A), (∀ a, πb (Ideal.Quotient.mk (ii W) a) = m.π a) → Adapted T (r := r) → ∀ (D0 : ℕ) (x : Pt T u D0) (x' : Spo A →ₐ[O] x.x.A), (∀ b, x' (algebraMap B (Spo A) b) = x.f b) → Function.Surjective (algebraMap O x.x.K) → x.f (A.b.lam (MvPowerSeries.X (.inl ()))) = x.x.t → x' (m.π (fo W)) ≠ 0 ∧ ∃ P : OoPt Λ.h x.x o.p, P.f = x'.comp πb ∧ P.ker = ooKer o := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m _ o πb hπ had D0 x x' hx' hsurj ht
  obtain ⟨-, -, hs, hU, hy⟩ := m.π_maps
  obtain ⟨hD, hψ⟩ := ooMaps l L G0 T Λ n O r B u J D A W m o πb hπ
  have hc : x'.toRingHom.comp (algebraMap B (Spo A)) = x.f.toRingHom := RingHom.ext hx'
  have heig : ∀ j, (mat x.x.ρ (T.sg j)).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C (x' (m.π (W.t.U j i)))) := fun j => by
    have h1 := congrArg (Polynomial.map x'.toRingHom) (spRoots B T.q n
      (fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1)) (fun j i => algebraMap O B (A.ut j i)) j).1
    rw [Polynomial.map_map, hc, ← ((UpperTheory.V.CA.d_gmap u.D).2.2.1 _ _).1, x.maps.1, MonoidAlgebra.mapRingHom_single,
      map_one, chi_rep, Polynomial.map_prod] at h1
    rw [← h1]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact congrArg (fun a => Polynomial.X - Polynomial.C (x' a)) (hU j i).symm
  have hinj : ∀ j, Function.Injective fun i => x' (m.π (W.t.U j i)) := fun j =>
    inj_of_prod ((heig j).symm.trans (x.eig j).2) (x.eig j).1
  have hl := lam_lift o.D_eq
  set Φ : MonoidAlgebra W.R (Ph0 Λ) →+* MonoidAlgebra (W.R ⧸ ii W) Λ.G.G₀ :=
    (MonoidAlgebra.mapDomainRingHom _ (πo0 Λ)).comp (MonoidAlgebra.mapRingHom _ (Ideal.Quotient.mk (ii W))) with hΦ
  have hp : ∀ g a, Φ (MonoidAlgebra.single g a) = MonoidAlgebra.single (πo0 Λ g) (Ideal.Quotient.mk (ii W) a) :=
    fun g a => by simp [hΦ]
  have hl' : ∀ i y, o.p.D.lam i (Φ y) = Ideal.Quotient.mk (ii W) (W.t.D.lam i y) := hl
  have hrel : ∀ y, Rel W (W.t.D.tr y) → o.p.D.tr (Φ y) = 0 := fun y h =>
    (hl' 1 y).trans (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span h))
  have hsj : Function.Surjective (πo0 Λ) := Λ.πo0_surj
  refine ⟨?_, ⟨{
      fg := ?_, Ip := fun w => ?_, surj := hsurj, q := T.q, ph := Λ.ph, ta := Λ.ta, comm := Λ.comm, p_ta := Λ.p_ta
      U := fun j i => Ideal.Quotient.mk (ii W) (W.t.U j i), y := fun j i => Ideal.Quotient.mk (ii W) (W.t.y j i)
      s := Ideal.Quotient.mk (ii W) W.t.s, q1 := fun j g => ?_, q2 := fun j i g => ?_, gen := ?_
      f := x'.comp πb, maps := ⟨?_, fun v i => ?_⟩, f_s := ?_, f_y := fun j i => ?_, f_U := fun j => ?_
      eig := fun j => ?_ }, rfl, rfl⟩⟩
  · simp only [fo, fEl, map_prod, map_mul, map_sub, Nat.cast_one, one_mul]
    refine Finset.prod_ne_zero_iff.2 fun j _ => Finset.prod_ne_zero_iff.2 fun i _ =>
      Finset.prod_ne_zero_iff.2 fun i' hi' => ?_
    have := sub_ne_zero.2 ((hinj j).ne (Finset.ne_of_mem_erase hi').symm)
    exact mul_ne_zero this this
  · classical
    obtain ⟨s, hs⟩ := Λ.fg
    refine ⟨s.image Λ.πo, ?_⟩
    rw [Finset.coe_image, ← MonoidHom.map_closure]
    exact Λ.πo_surj.denseRange.topologicalClosure_map_subgroup Λ.πo_cont hs
  · refine inf_eq_left.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    refine Subgroup.mem_iInf.2 fun i => ?_
    have h1 : G0.φu w g ∈ r.Ip w := by rw [had.2]; exact ⟨g, hg, rfl⟩
    have h2 := Subgroup.mem_iInf.1 h1.2 i
    rw [o.compat.1 i]
    change r.chib i (Λ.h.p₀ (Λ.G.φu w g)) = 1
    rw [Λ.h.p₀_φu]
    exact h2
  · obtain ⟨g, rfl⟩ := hsj g
    obtain ⟨ph, hph⟩ := hsj (Λ.ph j)
    have := hrel _ (Rel.q1 j ph g hph)
    rw [map_mul, hp, map_one, q1El, map_list_prod, List.map_ofFn] at this
    refine Eq.trans ?_ this
    rw [q1El]
    congr 4
    funext k
    simp only [Function.comp_apply, map_sub, hp, map_one, hph]
  · obtain ⟨g, rfl⟩ := hsj g
    obtain ⟨ph, hph⟩ := hsj (Λ.ph j)
    obtain ⟨ta, hta⟩ := hsj (Λ.ta j)
    have := hrel _ (Rel.q2 j i ph ta g hph hta)
    rw [map_mul, hp, map_one, q2El, map_mul, map_list_prod, List.map_ofFn, map_sub, map_sub, hp, hp, hta] at this
    simp only [map_one] at this
    refine Eq.trans ?_ this
    rw [q2El]
    congr 5
    funext k
    by_cases hk : k = i <;> simp only [Function.comp_apply, map_sub, hp, map_one, hph, hk, if_true, if_false]
  · refine genBy_img (Ideal.Quotient.mkₐ O (ii W)) Ideal.Quotient.mk_surjective
      (rrGen l L G0 T Λ n O r B u J D A W) ?_
    rintro a (((⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩) | ⟨j, i, h⟩) | rfl)
    · refine Or.inl (Or.inl (Or.inl ⟨i, πo0 Λ g, ?_⟩))
      have := hl' i (MonoidAlgebra.single g 1)
      rw [hp, map_one] at this
      exact this.symm
    · refine Or.inl (Or.inl (Or.inr ⟨v, i, g, ?_⟩))
      rw [o.ψ_eq]
      rfl
    · exact Or.inl (Or.inr ⟨j, i, h.imp (congrArg _) (congrArg _)⟩)
    · exact Or.inr rfl
  · have e : (x'.comp πb).toRingHom = x'.toRingHom.comp πb.toRingHom := rfl
    rw [e, ← (UpperTheory.V.CA.d_gmap o.p.D).2.1, hD, (UpperTheory.V.CA.d_gmap _).2.1, hc]
    change (u.D.map x.f.toRingHom).comap Λ.h.p₀ = _
    rw [x.maps.1, rep_comap]
    rfl
  · rw [← x.maps.2 v i, ← hc]
    exact congrArg (pushCh x'.toRingHom) (hψ v i)
  · rw [AlgHom.comp_apply, hπ, ← ht, ← hx']
    exact congrArg x' hs
  · rw [AlgHom.comp_apply, hπ, ← map_zero x']
    exact congrArg x' (hy j i)
  · simpa only [AlgHom.comp_apply, hπ] using hinj j
  · simpa only [AlgHom.comp_apply, hπ, Λ.p_ph] using heig j
end
