module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndomorphismFamilyDirectSummandCancellation
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CancelArtinianNoetherianSummand
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndomorphismIndecomposableNilpotentOrBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndomorphismIndecomposableNilpotentOrBijective
namespace GlobalTheory

theorem endo_indecomposable_finite_length_nilpotent_or_bijective :
    ∀ (R P : Type) [Ring R] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P],
      (∀ A B : Submodule R P, IsCompl A B → A = ⊥ ∨ B = ⊥) →
      ∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f := by
  intro R P _ _ _ _ _ hind f
  obtain ⟨n, hn⟩ := (LinearMap.eventually_isCompl_ker_pow_range_pow f).exists_forall_of_atTop
  have hc := hn (n + 1) (Nat.le_succ n)
  rcases hind _ _ hc with hk | hr
  · right
    have hk1 : LinearMap.ker f = ⊥ := by
      rw [eq_bot_iff, ← hk]
      intro x hx
      have hx' : f x = 0 := hx
      rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply, hx', map_zero]
    have hr1 : LinearMap.range (f ^ (n + 1)) = ⊤ := by
      have := hc.sup_eq_top
      rwa [hk, bot_sup_eq] at this
    have hs : LinearMap.range f = ⊤ := by
      rw [eq_top_iff, ← hr1]
      rintro _ ⟨x, rfl⟩
      rw [pow_succ', Module.End.mul_apply]
      exact ⟨_, rfl⟩
    exact ⟨LinearMap.ker_eq_bot.mp hk1, LinearMap.range_eq_top.mp hs⟩
  · left
    refine ⟨n + 1, ?_⟩
    have hk1 : LinearMap.ker (f ^ (n + 1)) = ⊤ := by
      have := hc.sup_eq_top
      rwa [hr, sup_bot_eq] at this
    exact LinearMap.ker_eq_top.mp hk1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndomorphismIndecomposableNilpotentOrBijectiveStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endomorphism_indecomposable_nilpotent_or_bijective : ∀ (R P : Type) [Ring R] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P], (∀ A B : Submodule R P, IsCompl A B → A = ⊥ ∨ B = ⊥) → ∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f := by
  first | exact @GlobalTheory.endo_indecomposable_finite_length_nilpotent_or_bijective | exact GlobalTheory.endo_indecomposable_finite_length_nilpotent_or_bijective | (intros; apply GlobalTheory.endo_indecomposable_finite_length_nilpotent_or_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CancelProdSummandNilpotentOrBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CancelProdSummandNilpotentOrBijective
namespace GlobalTheory

section CancelSummand

variable {R M M' P : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup P] [Module R P]

theorem linearEquiv_of_prod_corner_bijective (e : (M × P) ≃ₗ[R] (M' × P))
    (hd : Function.Bijective ((LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P)) :
    Nonempty (M ≃ₗ[R] M') := by
  set d : P →ₗ[R] P := (LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P with hd_def
  let dE : P ≃ₗ[R] P := LinearEquiv.ofBijective d hd
  let c : M →ₗ[R] P := (LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inl R M P
  let φ : M →ₗ[R] M' := (LinearMap.fst R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      (LinearMap.prod LinearMap.id (-((dE.symm : P →ₗ[R] P) ∘ₗ c)))
  let ψ : M' →ₗ[R] M := (LinearMap.fst R M P) ∘ₗ (e.symm : (M' × P) →ₗ[R] (M × P)) ∘ₗ
      LinearMap.inl R M' P
  have hsplit : ∀ x : M × P, (e x).2 = c x.1 + d x.2 := by
    intro x
    have hx : x = ((x.1, 0) : M × P) + (0, x.2) := by simp
    conv_lhs => rw [hx]
    rw [map_add (f := _)]
    rfl
  have hdd : ∀ p : P, d (dE.symm p) = p := fun p => dE.apply_symm_apply p
  have key : ∀ m : M, e (m, -dE.symm (c m)) = (φ m, 0) := by
    intro m
    ext
    · rfl
    · rw [hsplit]
      simp only [map_neg, hdd]
      simp
  refine ⟨LinearEquiv.ofLinear φ ψ ?_ ?_⟩
  · apply LinearMap.ext
    intro m'
    set x := e.symm (m', 0) with hx
    have hex : e x = (m', 0) := by simp [hx]
    have hp : -dE.symm (c x.1) = x.2 := by
      have h0 := hsplit x
      rw [hex] at h0
      have h1 : d x.2 = -c x.1 := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact h0.symm
      have h2 : dE.symm (d x.2) = x.2 := dE.symm_apply_apply x.2
      rw [h1, map_neg] at h2
      exact h2
    have hk := key x.1
    rw [hp] at hk
    have hψ : ψ m' = x.1 := rfl
    show φ (ψ m') = m'
    rw [hψ]
    have h3 : ((φ x.1, (0 : P)) : M' × P) = (m', 0) := by rw [← hk]; exact hex
    exact congrArg Prod.fst h3
  · apply LinearMap.ext
    intro m
    show ψ (φ m) = m
    have h : ψ (φ m) = (e.symm (φ m, 0)).1 := rfl
    rw [h, ← key m, LinearEquiv.symm_apply_apply]

theorem linearEquiv_cancel_of_nilpotent_or_bijective
    (hP : ∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f)
    (e : (M × P) ≃ₗ[R] (M' × P)) : Nonempty (M ≃ₗ[R] M') := by
  set d : Module.End R P := (LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P with hd_def
  by_cases hd : Function.Bijective d
  · exact linearEquiv_of_prod_corner_bijective e hd
  let b : P →ₗ[R] M' := (LinearMap.fst R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P
  let c' : M' →ₗ[R] P := (LinearMap.snd R M P) ∘ₗ (e.symm : (M' × P) →ₗ[R] (M × P)) ∘ₗ
      LinearMap.inl R M' P
  let d' : Module.End R P := (LinearMap.snd R M P) ∘ₗ (e.symm : (M' × P) →ₗ[R] (M × P)) ∘ₗ
      LinearMap.inr R M' P
  have hsum : c' ∘ₗ b = 1 - d' * d := by
    apply LinearMap.ext
    intro p
    have h : e (0, p) = ((b p, 0) : M' × P) + (0, d p) := by
      ext
      · simp; rfl
      · simp; rfl
    have h2 := congrArg Prod.snd (e.symm_apply_apply (0, p))
    rw [h, map_add (f := _)] at h2
    show c' (b p) = p - d' (d p)
    rw [eq_sub_iff_add_eq]
    exact h2
  have hnil : IsNilpotent (d' * d) := by
    rcases hP (d' * d) with h | h
    · exact h
    · exfalso
      apply hd
      have hinj : Function.Injective d := fun x y hxy => h.1 (by
        show d' (d x) = d' (d y)
        rw [hxy])
      rcases hP d with ⟨n, hn⟩ | h2
      · have hsub : ∀ x : P, x = 0 := by
          intro x
          apply hinj.iterate n
          have h3 : (d ^ n) x = (d ^ n) 0 := by rw [hn]; simp
          simpa [Module.End.pow_apply] using h3
        exact ⟨hinj, fun y => ⟨0, by rw [map_zero, hsub y]⟩⟩
      · exact h2
  have hw : IsUnit (c' ∘ₗ b : Module.End R P) := by
    rw [hsum]; exact hnil.isUnit_one_sub
  let winv : Module.End R P := ↑(hw.unit⁻¹)
  let g : M' →ₗ[R] P := ((1 - d) * winv) ∘ₗ c'
  let τ : (M' × P) ≃ₗ[R] (M' × P) :=
    LinearEquiv.skewProd (LinearEquiv.refl R M') (LinearEquiv.refl R P) g
  have hcorner : (LinearMap.snd R M' P) ∘ₗ ((e.trans τ : (M × P) ≃ₗ[R] (M' × P)) :
      (M × P) →ₗ[R] (M' × P)) ∘ₗ LinearMap.inr R M P = LinearMap.id := by
    apply LinearMap.ext
    intro p
    have h1 : g (b p) = p - d p := by
      have h4 : (winv * (c' ∘ₗ b : Module.End R P)) p = p := by
        rw [hw.val_inv_mul]; rfl
      show ((1 - d) * winv) (c' (b p)) = p - d p
      change (1 - d) ((winv * (c' ∘ₗ b : Module.End R P)) p) = p - d p
      rw [h4]
      simp
    show (e (0, p)).2 + g ((e (0, p)).1) = p
    change d p + g (b p) = p
    rw [h1]
    abel
  exact linearEquiv_of_prod_corner_bijective (e.trans τ) (by rw [hcorner]; exact Function.bijective_id)

end CancelSummand

theorem cancel_summand_nilpotent_or_bijective : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup P] [Module R P],
    (∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f) →
    Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by
  intro R M M' P _ _ _ _ _ _ _ hP he
  obtain ⟨e⟩ := he
  exact linearEquiv_cancel_of_nilpotent_or_bijective hP e

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CancelProdSummandNilpotentOrBijectiveStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cancel_prod_summand_nilpotent_or_bijective : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup P] [Module R P], (∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f) → Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by
  first | exact @GlobalTheory.cancel_summand_nilpotent_or_bijective | exact GlobalTheory.cancel_summand_nilpotent_or_bijective | (intros; apply GlobalTheory.cancel_summand_nilpotent_or_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CancelArtinianNoetherianSummand
namespace GlobalTheory

theorem ks_cancel_submodule (R P : Type) [Ring R] [AddCommGroup P] [Module R P] [IsArtinian R P]
    [IsNoetherian R P] (N : Submodule R P) :
    ∀ (M M' : Type) [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'],
      Nonempty ((M × N) ≃ₗ[R] (M' × N)) → Nonempty (M ≃ₗ[R] M') := by
  induction N using WellFoundedLT.induction with
  | _ N ih =>
  intro M M' _ _ _ _ e
  by_cases hind : ∀ A B : Submodule R N, IsCompl A B → A = ⊥ ∨ B = ⊥
  · exact GlobalTheory.T.cancel_prod_summand_nilpotent_or_bijective R M M' N (GlobalTheory.T.endomorphism_indecomposable_nilpotent_or_bijective R N hind) e
  · push_neg at hind
    obtain ⟨A, B, hAB, hA, hB⟩ := hind
    have hAlt : A.map N.subtype < N := by
      have h1 : A < ⊤ := lt_top_iff_ne_top.mpr (fun h => hB (by
        have := hAB.inf_eq_bot; rw [h, top_inf_eq] at this; exact this))
      have := Submodule.map_strictMono_of_injective N.injective_subtype h1
      rwa [Submodule.map_subtype_top] at this
    have hBlt : B.map N.subtype < N := by
      have h1 : B < ⊤ := lt_top_iff_ne_top.mpr (fun h => hA (by
        have := hAB.inf_eq_bot; rw [h, inf_top_eq] at this; exact this))
      have := Submodule.map_strictMono_of_injective N.injective_subtype h1
      rwa [Submodule.map_subtype_top] at this
    let eA : A ≃ₗ[R] A.map N.subtype := Submodule.equivMapOfInjective _ N.injective_subtype A
    let eB : B ≃ₗ[R] B.map N.subtype := Submodule.equivMapOfInjective _ N.injective_subtype B
    let eN : N ≃ₗ[R] (A.map N.subtype × B.map N.subtype) :=
      (Submodule.prodEquivOfIsCompl A B hAB).symm ≪≫ₗ LinearEquiv.prodCongr eA eB
    obtain ⟨e⟩ := e
    let f : ((M × A.map N.subtype) × B.map N.subtype) ≃ₗ[R]
        ((M' × A.map N.subtype) × B.map N.subtype) :=
      (LinearEquiv.prodAssoc R M _ _) ≪≫ₗ (LinearEquiv.prodCongr (LinearEquiv.refl R M) eN).symm ≪≫ₗ e ≪≫ₗ
        (LinearEquiv.prodCongr (LinearEquiv.refl R M') eN) ≪≫ₗ (LinearEquiv.prodAssoc R M' _ _).symm
    obtain ⟨g⟩ := ih _ hBlt _ _ ⟨f⟩
    exact ih _ hAlt M M' ⟨g⟩

theorem ks_cancel : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P],
    Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by
  intro R M M' P _ _ _ _ _ _ _ _ _ ⟨e⟩
  let t : (⊤ : Submodule R P) ≃ₗ[R] P := Submodule.topEquiv
  exact ks_cancel_submodule R P ⊤ M M'
    ⟨(LinearEquiv.prodCongr (LinearEquiv.refl R M) t) ≪≫ₗ e ≪≫ₗ
      (LinearEquiv.prodCongr (LinearEquiv.refl R M') t).symm⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CancelArtinianNoetherianSummandStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cancel_artinian_noetherian_summand : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P], Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by
  first | exact @GlobalTheory.ks_cancel | exact GlobalTheory.ks_cancel | (intros; apply GlobalTheory.ks_cancel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndomorphismFamilyDirectSummandCancellation
namespace GlobalTheory

theorem freeAlgebra_compHom_isScalarTower {k ι W : Type} [Field k] [AddCommGroup W] [Module k W]
    (φ : FreeAlgebra k ι →ₐ[k] Module.End k W) :
    @IsScalarTower k (FreeAlgebra k ι) W _ (Module.compHom W φ.toRingHom).toSMul _ := by
  letI : Module (FreeAlgebra k ι) W := Module.compHom W φ.toRingHom
  refine ⟨fun c r w => ?_⟩
  show φ (c • r) w = c • φ r w
  rw [map_smul]
  rfl

theorem endFamily_cancel : ∀ (k ι V V' U : Type) [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    [AddCommGroup U] [Module k U] [FiniteDimensional k U] (a : ι → Module.End k V)
    (b : ι → Module.End k V') (c : ι → Module.End k U),
    (∃ e : (V × U) ≃ₗ[k] (V' × U), ∀ i x, e ((a i).prodMap (c i) x) = (b i).prodMap (c i) (e x)) →
      ∃ e : V ≃ₗ[k] V', ∀ i x, e (a i x) = b i (e x) := by
  intro k ι V V' U _ _ _ _ _ _ _ _ _ _ a b c ⟨e, he⟩
  let φa : (FreeAlgebra k ι) →ₐ[k] Module.End k V := FreeAlgebra.lift k a
  let φb : (FreeAlgebra k ι) →ₐ[k] Module.End k V' := FreeAlgebra.lift k b
  let φc : (FreeAlgebra k ι) →ₐ[k] Module.End k U := FreeAlgebra.lift k c
  letI iV : Module (FreeAlgebra k ι) V := Module.compHom V φa.toRingHom
  letI iV' : Module (FreeAlgebra k ι) V' := Module.compHom V' φb.toRingHom
  letI iU : Module (FreeAlgebra k ι) U := Module.compHom U φc.toRingHom
  haveI tV : IsScalarTower k (FreeAlgebra k ι) V := freeAlgebra_compHom_isScalarTower φa
  haveI tV' : IsScalarTower k (FreeAlgebra k ι) V' := freeAlgebra_compHom_isScalarTower φb
  haveI tU : IsScalarTower k (FreeAlgebra k ι) U := freeAlgebra_compHom_isScalarTower φc
  haveI : IsArtinian (FreeAlgebra k ι) U := isArtinian_of_tower k inferInstance
  haveI : IsNoetherian (FreeAlgebra k ι) U := isNoetherian_of_tower k inferInstance

  have key : ∀ r : (FreeAlgebra k ι), ∀ x : V × U, e (φa r x.1, φc r x.2) = (φb r (e x).1, φc r (e x).2) := by
    intro r
    induction r using FreeAlgebra.induction with
    | grade0 s =>
      intro x
      simp only [φa, φb, φc, AlgHom.commutes, Module.algebraMap_end_apply]
      exact e.map_smul s x
    | grade1 i =>
      intro x
      have := he i x
      simp only [φa, φb, φc, FreeAlgebra.lift_ι_apply]
      simpa using this
    | mul r s hr hs =>
      intro x
      have h1 := hs x
      have h2 := hr (φa s x.1, φc s x.2)
      simp only [map_mul, Module.End.mul_apply]
      rw [h2, h1]
    | add r s hr hs =>
      intro x
      have h1 := hr x
      have h2 := hs x
      have hsum : ((φa (r + s)) x.1, (φc (r + s)) x.2)
          = ((φa r) x.1, (φc r) x.2) + ((φa s) x.1, (φc s) x.2) := by
        simp [map_add (f := _)]
      rw [hsum, map_add (f := _), h1, h2]
      simp [map_add (f := _)]
  let eR : (V × U) ≃ₗ[(FreeAlgebra k ι)] (V' × U) :=
    { e.toAddEquiv with
      map_smul' := fun r x => key r x }
  obtain ⟨f⟩ := GlobalTheory.T.cancel_artinian_noetherian_summand (FreeAlgebra k ι) V V' U ⟨eR⟩
  refine ⟨f.restrictScalars k, fun i x => ?_⟩
  have h : f (FreeAlgebra.ι k i • x) = FreeAlgebra.ι k i • f x := f.map_smul _ _
  change f (φa (FreeAlgebra.ι k i) x) = φb (FreeAlgebra.ι k i) (f x) at h
  simp only [φa, φb, FreeAlgebra.lift_ι_apply] at h
  exact h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndomorphismFamilyDirectSummandCancellationStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endomorphismFamily_direct_summand_cancellation : ∀ (k ι V V' U : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup V'] [Module k V'] [FiniteDimensional k V'] [AddCommGroup U] [Module k U] [FiniteDimensional k U] (a : ι → Module.End k V) (b : ι → Module.End k V') (c : ι → Module.End k U), (∃ e : (V × U) ≃ₗ[k] (V' × U), ∀ i x, e ((a i).prodMap (c i) x) = (b i).prodMap (c i) (e x)) → ∃ e : V ≃ₗ[k] V', ∀ i x, e (a i x) = b i (e x) := by
  first | exact @GlobalTheory.endFamily_cancel | exact GlobalTheory.endFamily_cancel | (intros; apply GlobalTheory.endFamily_cancel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DirectSumCancelRight
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.WD

theorem lpSum_cancel_right : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (a b c : WD h), a.lpSum c = b.lpSum c → a = b := by
  intro E Ω _ _ _ _ _ A w h a b c
  induction a using ind with
  | hP n a =>
  induction b using ind with
  | hP m b =>
  induction c using ind with
  | hP k c =>
  intro hab
  rw [lpSum_mk, lpSum_mk, mk_eq_mk] at hab
  obtain ⟨e, h1, h2⟩ := hab
  let fa : Option (Weil h) → Module.End ℂ (Fin n → ℂ) := fun o => o.elim a.N a.ρ
  let fb : Option (Weil h) → Module.End ℂ (Fin m → ℂ) := fun o => o.elim b.N b.ρ
  let fc : Option (Weil h) → Module.End ℂ (Fin k → ℂ) := fun o => o.elim c.N c.ρ
  obtain ⟨e', he'⟩ := GlobalTheory.T.endomorphismFamily_direct_summand_cancellation ℂ (Option (Weil h)) (Fin n → ℂ) (Fin m → ℂ) (Fin k → ℂ)
    fa fb fc ⟨e, fun i x => by
      cases i with
      | none => exact h2 x
      | some σ => exact h1 σ x⟩
  exact sound ⟨e', fun σ v => he' (some σ) v, fun v => he' none v⟩

end GlobalTheory.WeilDeligne.WD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DirectSumCancelRightStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.directSum_cancel_right : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a b c : WD h), a.lpSum c = b.lpSum c → a = b := by
  first | exact @GlobalTheory.WeilDeligne.WD.lpSum_cancel_right | exact GlobalTheory.WeilDeligne.WD.lpSum_cancel_right | (intros; apply GlobalTheory.WeilDeligne.WD.lpSum_cancel_right <;> assumption)
end
