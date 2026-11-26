module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLevelLocalDualQuotientLengthOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGLConjLatticePairsCovByDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGLConjLatticePairsCovByDvr
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem exists_equiv_ker_prod {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (ψ : M →ₗ[O] O) (hψ : Function.Surjective ψ) :
    ∃ E : M ≃ₗ[O] (LinearMap.ker ψ × O), ∀ x, (E x).2 = ψ x := by
  obtain ⟨x₀, hx₀⟩ := hψ 1
  let p : M →ₗ[O] LinearMap.ker ψ :=
    LinearMap.codRestrict _ (LinearMap.id - LinearMap.toSpanSingleton O M x₀ ∘ₗ ψ)
      (fun x => by simp [hx₀])
  refine ⟨LinearEquiv.ofLinearMap (p.prod ψ)
    ((LinearMap.ker ψ).subtype.coprod (LinearMap.toSpanSingleton O M x₀)) ?_ ?_, fun x => rfl⟩
  · apply LinearMap.prod_ext
    · ext y
      · simp [p]
      · simp
    · ext
      · simp [p, hx₀]
      · simp [hx₀]
  · ext x
    simp [p]

theorem exists_equiv_comp_eq_of_surjective {O M M' : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    [Module.Free O M] [Module.Finite O M] [Module.Free O M'] [Module.Finite O M']
    (h : Module.finrank O M = Module.finrank O M')
    (ψ : M →ₗ[O] O) (hψ : Function.Surjective ψ)
    (ψ' : M' →ₗ[O] O) (hψ' : Function.Surjective ψ') :
    ∃ e : M ≃ₗ[O] M', ∀ x, ψ' (e x) = ψ x := by
  obtain ⟨E, hE⟩ := exists_equiv_ker_prod ψ hψ
  obtain ⟨E', hE'⟩ := exists_equiv_ker_prod ψ' hψ'
  have hk : Module.finrank O (LinearMap.ker ψ) = Module.finrank O (LinearMap.ker ψ') := by
    have h₁ := E.finrank_eq
    have h₂ := E'.finrank_eq
    rw [Module.finrank_prod, Module.finrank_self] at h₁ h₂
    omega
  obtain ⟨k⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hk
  refine ⟨E.trans ((k.prodCongr (LinearEquiv.refl O O)).trans E'.symm), fun x => ?_⟩
  rw [← hE', ← hE]
  simp

theorem exists_form_of_covBy {O V : Type} [CommRing O] [IsLocalRing O] [AddCommGroup V]
    [Module O V] (A B : Submodule O V) [Module.Projective O B] (h : A ⋖ B) :
    ∃ ψ : B →ₗ[O] O, Function.Surjective ψ ∧
      ∀ x : B, (x : V) ∈ A ↔ ψ x ∈ IsLocalRing.maximalIdeal O := by
  have hs := (covBy_iff_quot_is_simple h.le).1 h
  obtain ⟨I, hI, ⟨f⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
  obtain rfl := IsLocalRing.eq_maximalIdeal hI
  set m := IsLocalRing.maximalIdeal O
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property m.mkQ
    (f.toLinearMap ∘ₗ (A.comap B.subtype).mkQ) m.mkQ_surjective
  have key : ∀ x, m.mkQ (ψ x) = f ((A.comap B.subtype).mkQ x) := fun x =>
    LinearMap.congr_fun hψ x
  have hmem : ∀ x : B, (x : V) ∈ A ↔ ψ x ∈ m := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero m, ← Submodule.mkQ_apply, key,
      LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.subtype_apply]
  refine ⟨ψ, ?_, hmem⟩
  obtain ⟨y, hy⟩ := f.surjective (m.mkQ 1)
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  have hu : IsUnit (ψ x) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hx
    have h1 : m.mkQ 1 = 0 := by
      rw [← hy, ← key, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  intro r
  refine ⟨(r * hu.unit⁻¹.1) • x, ?_⟩
  rw [map_smul, smul_eq_mul, mul_assoc, hu.val_inv_mul, mul_one]

theorem exists_extend_latticeEquiv {O K V : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (B B' : Submodule O V) [B.IsFullLattice K] [B'.IsLattice K] (e : B ≃ₗ[O] B') :
    ∃ g : V ≃ₗ[K] V, ∀ x : B, g x = e x := by
  have := Submodule.IsLattice.finite K B
  have := Submodule.IsLattice.free K B
  have : B'.IsFullLattice K := Submodule.IsFullLattice.of_rank_le K B' (by
    rw [← Submodule.IsFullLattice.rank_eq K B, e.rank_eq])
  let b := Module.Free.chooseBasis O B
  let c := b.map e
  let g := (b.extendOfIsFullLattice K).equiv (c.extendOfIsFullLattice K) (Equiv.refl _)
  refine ⟨g, fun x => ?_⟩
  have key : (g.toLinearMap.restrictScalars O) ∘ₗ B.subtype = B'.subtype ∘ₗ e.toLinearMap := by
    refine b.ext fun i => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, Submodule.coe_subtype, g, c]
    rw [← Module.Basis.extendOfIsFullLattice_apply K b i, Module.Basis.equiv_apply]
    simp
  exact LinearMap.congr_fun key x

theorem exists_conj_of_covBy : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (n : ℕ) (A B A' B' : Submodule O (Fin n → K)), B.FG → B'.FG → Submodule.span K (A : Set (Fin n → K)) = ⊤ → Submodule.span K (A' : Set (Fin n → K)) = ⊤ → A ⋖ B → A' ⋖ B' → ∃ g : GL (Fin n) K, (∀ x, x ∈ A ↔ g.1 *ᵥ x ∈ A') ∧ ∀ x, x ∈ B ↔ g.1 *ᵥ x ∈ B' := by
  intro O K _ _ _ _ _ _ n A B A' B' hB hB' hA hA' h h'
  have : B.IsLattice K := Submodule.IsLattice.of_fg K hB
  have : B'.IsLattice K := Submodule.IsLattice.of_fg K hB'
  have : B.IsFullLattice K :=
    ⟨eq_top_iff.2 (hA ▸ Submodule.span_mono (show (A : Set (Fin n → K)) ⊆ B from h.le))⟩
  have : B'.IsFullLattice K :=
    ⟨eq_top_iff.2 (hA' ▸ Submodule.span_mono (show (A' : Set (Fin n → K)) ⊆ B' from h'.le))⟩
  have : Module.Free O B := Submodule.IsLattice.free K B
  have : Module.Free O B' := Submodule.IsLattice.free K B'
  have : Module.Finite O B := Submodule.IsLattice.finite K B
  have : Module.Finite O B' := Submodule.IsLattice.finite K B'
  have hr : Module.finrank O B = Module.finrank O B' := by
    rw [((Submodule.IsFullLattice.finrank_eq K B).trans (Module.finrank_fintype_fun_eq_card K)), ((Submodule.IsFullLattice.finrank_eq K B').trans (Module.finrank_fintype_fun_eq_card K))]
  obtain ⟨ψ, hψs, hψ⟩ := exists_form_of_covBy A B h
  obtain ⟨ψ', hψs', hψ'⟩ := exists_form_of_covBy A' B' h'
  obtain ⟨e, he⟩ := exists_equiv_comp_eq_of_surjective hr ψ hψs ψ' hψs'
  obtain ⟨g, hg⟩ := exists_extend_latticeEquiv (K := K) B B' e
  have hBg : ∀ x, x ∈ B ↔ g x ∈ B' := by
    intro x
    constructor
    · intro hx
      rw [show g x = e ⟨x, hx⟩ from hg ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).2
    · intro hx
      have hy : ((e.symm ⟨g x, hx⟩ : B) : Fin n → K) = x :=
        g.injective (by rw [hg]; simp)
      rw [← hy]
      exact (e.symm _).2
  have hpt : ∀ x (hx : x ∈ B), (⟨g x, (hBg x).1 hx⟩ : B') = e ⟨x, hx⟩ := fun x hx =>
    Subtype.ext (hg ⟨x, hx⟩)
  let G : GL (Fin n) K :=
    ⟨LinearMap.toMatrix' g.toLinearMap, LinearMap.toMatrix' g.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hG : ∀ x, G.1 *ᵥ x = g x := fun x => LinearMap.toMatrix'_mulVec _ x
  refine ⟨G, fun x => ?_, fun x => ?_⟩
  · rw [hG]
    constructor
    · intro hx
      have hxB := h.le hx
      have hgB := (hBg x).1 hxB
      rw [hψ' ⟨g x, hgB⟩, hpt x hxB, he]
      exact (hψ ⟨x, hxB⟩).1 hx
    · intro hx
      have hgB := h'.le hx
      have hxB := (hBg x).2 hgB
      rw [hψ ⟨x, hxB⟩, ← he, ← hpt x hxB]
      exact (hψ' ⟨g x, hgB⟩).1 hx
  · rw [hG]
    exact hBg x

end GlobalTheory.St.G
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGLConjLatticePairsCovByDvrStatement
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GL_conj_lattice_pairs_covBy_dvr : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (n : ℕ) (A B A' B' : Submodule O (Fin n → K)), B.FG → B'.FG → Submodule.span K (A : Set (Fin n → K)) = ⊤ → Submodule.span K (A' : Set (Fin n → K)) = ⊤ → A ⋖ B → A' ⋖ B' → ∃ g : GL (Fin n) K, (∀ x, x ∈ A ↔ g.1 *ᵥ x ∈ A') ∧ ∀ x, x ∈ B ↔ g.1 *ᵥ x ∈ B' := by
  first | exact @GlobalTheory.St.G.exists_conj_of_covBy | exact GlobalTheory.St.G.exists_conj_of_covBy | (intros; apply GlobalTheory.St.G.exists_conj_of_covBy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLocalUnitaryLatticesOfLevel
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.LevelConj

section General

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] {n : ℕ}

omit [IsFractionRing O K] in
theorem covBy_of_cyclic {A B : Submodule O (Fin n → K)} (hle : A ≤ B) (hne : A ≠ B) (d : Fin n → K)
    (hx : ∀ x ∈ B, ∃ a : O, x - a • d ∈ A) (hd : d ∈ B)
    (hm : ∀ a ∈ IsLocalRing.maximalIdeal O, a • d ∈ A) : A ⋖ B := by
  refine ⟨lt_of_le_of_ne hle hne, fun C hAC hCB => ?_⟩
  obtain ⟨x, hxC, hxA⟩ := SetLike.exists_of_lt hAC
  obtain ⟨a, ha⟩ := hx x (hCB.le hxC)
  have hu : IsUnit a := by
    by_contra h
    exact hxA (by simpa using add_mem ha (hm a h))
  have h1 : a • d ∈ C := by simpa using sub_mem hxC (hAC.le ha)
  have h2 : d ∈ C := (Submodule.smul_mem_iff_of_isUnit C hu).1 h1
  refine hCB.not_ge fun y hy => ?_
  obtain ⟨b, hb⟩ := hx y hy
  simpa using add_mem (hAC.le hb) (C.smul_mem b h2)

theorem bidual (B : LinearMap.BilinForm K (Fin n → K)) (hB : B.Nondegenerate)
    (N : Submodule O (Fin n → K)) (hfg : N.FG) (hsp : Submodule.span K (N : Set (Fin n → K)) = ⊤)
    (u : Fin n → K)
    (hu : ∀ w, (∀ u' ∈ N, B u' w ∈ (1 : Submodule O K)) → B u w ∈ (1 : Submodule O K)) : u ∈ N := by
  classical
  haveI : N.IsFullLattice K := { toIsLattice := Submodule.IsLattice.of_fg K hfg, span_eq_top := hsp }
  have := Submodule.IsLattice.finite K N
  have := Submodule.IsLattice.free K N
  let b := Module.Free.chooseBasis O N
  have h : Submodule.span O (Set.range (b.extendOfIsFullLattice K)) = N := by
    have h1 : Set.range (b.extendOfIsFullLattice K) = N.subtype '' Set.range b := by
      rw [← Set.range_comp]
      congr 1
      exact funext fun i => b.extendOfIsFullLattice_apply K i
    rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
  have e := LinearMap.BilinForm.dualSubmodule_dualSubmodule_flip_of_basis (R := O) B hB
    (b.extendOfIsFullLattice K)
  rw [h] at e
  rw [← e]
  exact fun w hw => hu w hw

end General

section Comp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 F)}

noncomputable def cmp (π : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F) :=
  Submodule.span _ ((fun x i => π (inclE (F := F) _ (x i))) '' (L : Set (Fin n → E)))

variable {π : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F}

theorem mem_cmp (hπ : ∀ a, π ((1 : E) ⊗ₜ[F] a) = a)
    (hint : ∀ t ∈ intV E v, π t ∈ v.adicCompletionIntegers F) (L : Submodule (𝓞 E) (Fin n → E))
    (a : Fin n → v.adicCompletion F) :
    a ∈ cmp π L ↔ ∃ y ∈ loc v L, (fun b => π (y b)) = a := by
  constructor
  · intro ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨_, Submodule.subset_span ⟨y, hy, rfl⟩, rfl⟩
    | zero => exact ⟨0, zero_mem _, by funext b; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      exact ⟨x + y, add_mem hx hy, by funext b; simp⟩
    | smul c x _ hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      have hc : (1 : E) ⊗ₜ[F] (c : v.adicCompletion F) ∈ intV E v :=
        Subring.subset_closure (Or.inr ⟨⟨c.1, c.2⟩, rfl⟩)
      refine ⟨_, (loc v L).smul_mem ⟨_, hc⟩ hx, ?_⟩
      funext b
      change π ((1 : E) ⊗ₜ[F] (c : v.adicCompletion F) * x b) = (c : v.adicCompletion F) * π (x b)
      rw [map_mul, hπ]
  · rintro ⟨y, hy, rfl⟩
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, map_add (f := _)]; exact add_mem hx hy
    | smul c x _ hx =>
      have := (cmp π L).smul_mem ⟨_, hint _ c.2⟩ hx
      convert this using 1
      funext b
      exact map_mul π (c : E ⊗[F] v.adicCompletion F) (x b)

theorem cmp_fg (hint : ∀ t ∈ intV E v, π t ∈ v.adicCompletionIntegers F)
    {L : Submodule (𝓞 E) (Fin n → E)} (hL : IsLat L) : (cmp π L).FG := by
  obtain ⟨s, hs⟩ := (Module.Finite.iff_fg).1 hL.1
  refine Submodule.fg_def.2 ⟨(fun x i => π (inclE (F := F) _ (x i))) '' (s : Set (Fin n → E)),
    s.finite_toSet.image _, le_antisymm (Submodule.span_mono (Set.image_mono ?_)) ?_⟩
  · rw [← hs]; exact Submodule.subset_span
  · rw [cmp, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, map_add (f := _)]; exact add_mem hx hy
    | smul c x _ hx =>
      have hc : inclE (F := F) (v.adicCompletion F) (c : E) ∈ intV E v :=
        Subring.subset_closure (Or.inl ⟨⟨c, c, rfl⟩, rfl⟩)
      have := Submodule.smul_mem _ (⟨_, hint _ hc⟩ : v.adicCompletionIntegers F) hx
      refine Set.mem_of_eq_of_mem ?_ this
      funext b
      change π (inclE _ ((c : E) * x b)) = π _ * π _
      rw [map_mul, map_mul]

theorem cmp_span {L : Submodule (𝓞 E) (Fin n → E)} (hL : IsLat L) :
    Submodule.span (v.adicCompletion F) (cmp π L : Set (Fin n → v.adicCompletion F)) = ⊤ := by
  have key : ∀ x : Fin n → E, (fun i => π (inclE (F := F) _ (x i))) ∈
      Submodule.span (v.adicCompletion F) (cmp π L : Set (Fin n → v.adicCompletion F)) := by
    intro x
    have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL.2 ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
    | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, map_add (f := _)]; exact add_mem hx hy
    | smul c x _ hx =>
      have := Submodule.smul_mem _ (π (inclE (F := F) _ c)) hx
      convert this using 1
      funext b
      change π (inclE _ ((c : E) * x b)) = π _ * π _
      rw [map_mul, map_mul]
  rw [eq_top_iff, ← (Pi.basisFun (v.adicCompletion F) (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine Set.mem_of_eq_of_mem ?_ (key (Pi.single i 1))
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem cmp_nsmul (T : ℕ) {L M : Submodule (𝓞 E) (Fin n → E)} (h : ∀ y ∈ M, T • y ∈ L) :
    ∀ y ∈ cmp π M, T • y ∈ cmp π L := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨_, h y hy, ?_⟩
    funext b
    simp only [Pi.smul_apply, map_nsmul]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

end Comp

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {n : ℕ} {v : HeightOneSpectrum (𝓞 F)}
  (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)

noncomputable abbrev p₁ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F :=
  (RingHom.fst _ _).comp sp.toRingHom

noncomputable abbrev p₂ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F :=
  (RingHom.snd _ _).comp sp.toRingHom

noncomputable def pairing (J : Matrix (Fin n) (Fin n) E) :
    LinearMap.BilinForm (v.adicCompletion F) (Fin n → v.adicCompletion F) :=
  Matrix.toBilin' (J.map ((p₁ sp).comp (inclE (F := F) (v.adicCompletion F))))

omit [StarRing E] in
theorem pairing_nondegenerate {J : Matrix (Fin n) (Fin n) E} (hdet : J.det ≠ 0) :
    (pairing sp J).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).2 hdet

theorem mem_one_iff (a : v.adicCompletion F) :
    a ∈ (1 : Submodule (v.adicCompletionIntegers F) (v.adicCompletion F)) ↔
      a ∈ v.adicCompletionIntegers F := by
  rw [Submodule.mem_one]
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨a, h⟩, rfl⟩⟩

variable {sp} {cm : CMData F E} {J : Matrix (Fin n) (Fin n) E}
  (hJ : IsHerm (cm.sig : E →+* E) J) (hdet : J.det ≠ 0)
  (hsig : ∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x))
  (hdiag : ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a))

include hsig in
theorem fst_hR (x y : Fin n → E ⊗[F] v.adicCompletion F) :
    p₁ sp (hR cm.sig J (v.adicCompletion F) x y) =
      pairing sp J (fun b => p₂ sp (x b)) (fun b => p₁ sp (y b)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pairing, Matrix.toBilin'_apply, hR, hform, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul]
  have : p₁ sp (sigR cm.sig (v.adicCompletion F) (x i)) = p₂ sp (x i) := congrArg Prod.fst (hsig _)
  rw [this]
  rfl

include hsig hJ in
theorem snd_hR (x y : Fin n → E ⊗[F] v.adicCompletion F) :
    p₂ sp (hR cm.sig J (v.adicCompletion F) x y) =
      pairing sp J (fun b => p₂ sp (y b)) (fun b => p₁ sp (x b)) := by
  rw [← fst_hR hsig]
  have hτ : ∀ a, sigR cm.sig (v.adicCompletion F) (sigR cm.sig (v.adicCompletion F) a) = a :=
    fun a => sp.injective (by rw [hsig, hsig]; rfl)
  have hJ' : IsHerm (sigR cm.sig (v.adicCompletion F))
      (J.map (inclE (F := F) (v.adicCompletion F))) := by
    funext i j
    exact congrArg (inclE (F := F) (v.adicCompletion F)) (congrFun (congrFun hJ i) j)
  have := GlobalTheory.DualFrames.hform_swap _ hτ _ hJ' x y
  rw [hR, hR, ← this]
  exact (congrArg Prod.fst (hsig _)).symm

omit [StarRing E] in
include hdiag in
theorem int_iff (t : E ⊗[F] v.adicCompletion F) : t ∈ intV E v ↔
    p₁ sp t ∈ v.adicCompletionIntegers F ∧ p₂ sp t ∈ v.adicCompletionIntegers F :=
  split_integral_local F E v sp hdiag t

omit [StarRing E] in
include hdiag in
theorem mem_cmp₁ (L : Submodule (𝓞 E) (Fin n → E)) (a : Fin n → v.adicCompletion F) :
    a ∈ cmp (p₁ sp) L ↔ ∃ y ∈ loc v L, (fun b => p₁ sp (y b)) = a :=
  mem_cmp (fun a => congrArg Prod.fst (hdiag a)) (fun t ht => ((int_iff hdiag t).1 ht).1) L a

omit [StarRing E] in
include hdiag in
theorem mem_cmp₂ (L : Submodule (𝓞 E) (Fin n → E)) (a : Fin n → v.adicCompletion F) :
    a ∈ cmp (p₂ sp) L ↔ ∃ y ∈ loc v L, (fun b => p₂ sp (y b)) = a :=
  mem_cmp (fun a => congrArg Prod.snd (hdiag a)) (fun t ht => ((int_iff hdiag t).1 ht).2) L a

include hJ hdet hsig hdiag

theorem mem_loc_iff (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E ⊗[F] v.adicCompletion F) :
    y ∈ loc v L ↔ (fun b => p₁ sp (y b)) ∈ cmp (p₁ sp) L ∧ (fun b => p₂ sp (y b)) ∈ cmp (p₂ sp) L := by
  rw [(split_components F E cm n J hJ hdet v sp hsig hdiag).1 L y, mem_cmp₁ hdiag, mem_cmp₂ hdiag]
  simp only [funext_iff]
  rfl

theorem mem_cmp₂_iff {L : Submodule (𝓞 E) (Fin n → E)} (hL : IsLat L)
    (u : Fin n → v.adicCompletion F) :
    u ∈ cmp (p₂ sp) L ↔
      ∀ w ∈ cmp (p₁ sp) (dualL cm.sig J L), pairing sp J u w ∈ v.adicCompletionIntegers F := by
  have hD := (GlobalTheory.T.dual_lattice_local_characterization F E cm n J hJ hdet L hL).2.1 v
  constructor
  · intro hu w hw
    obtain ⟨z, hz, rfl⟩ := (mem_cmp₂ hdiag _ _).1 hu
    obtain ⟨x, hx, rfl⟩ := (mem_cmp₁ hdiag _ _).1 hw
    rw [← fst_hR hsig]
    exact ((int_iff hdiag _).1 ((hD x).1 hx z hz)).1
  · intro hu
    refine bidual _ (pairing_nondegenerate sp hdet) _
      (cmp_fg (fun t ht => ((int_iff hdiag t).1 ht).2) hL) (cmp_span hL) u fun w hw => ?_
    rw [mem_one_iff]
    refine hu w ((mem_cmp₁ hdiag _ _).2 ⟨fun b => sp.symm (w b, 0), ?_, ?_⟩)
    · refine (hD _).2 fun z hz => (int_iff hdiag _).2 ⟨?_, ?_⟩
      · rw [fst_hR hsig, ← mem_one_iff]
        have := hw _ ((mem_cmp₂ hdiag _ _).2 ⟨z, hz, rfl⟩)
        simpa [p₁] using this
      · rw [snd_hR hJ hsig]
        have : (fun b => p₂ sp (sp.symm (w b, 0))) = 0 := by funext b; simp [p₂]
        rw [this, map_zero, LinearMap.zero_apply]
        exact zero_mem _
    · funext b; simp [p₁]

theorem cmp₁_covBy {T f : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} (hT : T.Prime) (hs : SplitsIn E T)
    (hf : Module.finrank ℚ E = 2 * f) (hL : TLat cm.sig J T f L) (hv : (T : 𝓞 F) ∈ v.asIdeal) :
    cmp (p₁ sp) L ⋖ cmp (p₁ sp) (dualL cm.sig J L) := by
  have hD := (GlobalTheory.T.dual_lattice_local_characterization F E cm n J hJ hdet L hL.1).2.1 v
  obtain ⟨-, d, hd, hcyc⟩ := GlobalTheory.T.hermitianLattice_level_local_dual_quotient_length_one F E cm n J hJ hdet T f L hT hs hf hL v hv
  have hmax := ((SplitPrime.split_place F E cm T hT hs).2 v hv).2.1
  have hd' := (mem_cmp₁ hdiag _ _).2 ⟨d, hd, rfl⟩
  refine covBy_of_cyclic ?_ ?_ _ ?_ hd' ?_
  · exact Submodule.span_mono (Set.image_mono fun x hx => Submodule.subset_span (hL.2.1 x hx))
  · intro hAB
    obtain ⟨x, hx, hxL⟩ := hL.2.2.2.2 v hv
    refine hxL ((mem_loc_iff hJ hdet hsig hdiag L x).2
      ⟨hAB ▸ (mem_cmp₁ hdiag _ _).2 ⟨x, hx, rfl⟩, (mem_cmp₂_iff hJ hdet hsig hdiag hL.1 _).2 ?_⟩)
    rw [← hAB]
    intro w hw
    obtain ⟨z, hz, rfl⟩ := (mem_cmp₁ hdiag _ _).1 hw
    rw [← snd_hR hJ hsig]
    exact ((int_iff hdiag _).1 ((hD x).1 hx z hz)).2
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := (mem_cmp₁ hdiag _ _).1 hw
    obtain ⟨a, ha, hxa⟩ := hcyc x hx
    refine ⟨⟨_, ((int_iff hdiag _).1 ha).1⟩, (mem_cmp₁ hdiag _ _).2 ⟨_, hxa, ?_⟩⟩
    funext b
    change p₁ sp (x b - a * d b) = p₁ sp (x b) - p₁ sp a * p₁ sp (d b)
    rw [map_sub, map_mul]
  · intro a ha
    rw [hmax, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
    refine Submodule.smul_mem _ _ (cmp_nsmul T ?_ _ hd')
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => rw [← Nat.cast_smul_eq_nsmul E]; exact hL.2.2.1 x hx
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

end Split

end GlobalTheory.St.G.LevelConj

namespace GlobalTheory.St.G

open LevelConj

theorem exists_unitary_of_TLat :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → TLat cm.sig J T f M → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∃ h ∈ UPts cm.sig J (v.adicCompletion F), ∀ x, x ∈ loc v L ↔ h.1 *ᵥ x ∈ loc v M := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L M hT hs hf hL hM v hv
  obtain ⟨sp, hsig, hdiag⟩ := ((SplitPrime.split_place F E cm T hT hs).2 v hv).2.2
  have hint : ∀ t ∈ intV E v, p₁ sp t ∈ v.adicCompletionIntegers F :=
    fun t ht => ((int_iff hdiag t).1 ht).1
  obtain ⟨g, hA, hB⟩ := GlobalTheory.T.exists_GL_conj_lattice_pairs_covBy_dvr (v.adicCompletionIntegers F) (v.adicCompletion F) n _ _ _ _
    (cmp_fg hint (GlobalTheory.T.dual_lattice_local_characterization F E cm n J hJ hdet L hL.1).1)
    (cmp_fg hint (GlobalTheory.T.dual_lattice_local_characterization F E cm n J hJ hdet M hM.1).1) (cmp_span hL.1) (cmp_span hM.1)
    (cmp₁_covBy hJ hdet hsig hdiag hT hs hf hL hv) (cmp₁_covBy hJ hdet hsig hdiag hT hs hf hM hv)
  obtain ⟨⟨h, hh⟩, hg, -⟩ := (split_components F E cm n J hJ hdet v sp hsig hdiag).2.1 g
  have hg' : ∀ x, (fun b => p₁ sp ((h.1 *ᵥ x) b)) = g.1 *ᵥ fun b => p₁ sp (x b) := by
    intro x
    funext b
    rw [← hg]
    exact RingHom.map_mulVec (p₁ sp) h.1 x b
  have hinv : ∀ x y, hR cm.sig J (v.adicCompletion F) (h.1 *ᵥ x) (h.1 *ᵥ y) =
      hR cm.sig J (v.adicCompletion F) x y := by
    intro x y
    have h0 : cT (sigR cm.sig (v.adicCompletion F)) h.1 * J.map (inclE (F := F) (v.adicCompletion F)) * h.1 =
      J.map (inclE (F := F) (v.adicCompletion F)) := hh
    have h1 : sigR cm.sig (v.adicCompletion F) ∘ (h.1 *ᵥ x) =
        (h.1.map (sigR cm.sig (v.adicCompletion F))) *ᵥ (sigR cm.sig (v.adicCompletion F) ∘ x) := by
      funext i
      exact RingHom.map_mulVec _ h.1 x i
    rw [hR, hR, GlobalTheory.DualFrames.hform_eq_dot, GlobalTheory.DualFrames.hform_eq_dot, h1, ← vecMul_transpose,
      ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
    exact congrArg (fun N => _ ⬝ᵥ N *ᵥ y) h0
  have hp : ∀ x w, pairing sp J (fun b => p₂ sp ((h.1 *ᵥ x) b)) (g.1 *ᵥ w) =
      pairing sp J (fun b => p₂ sp (x b)) w := by
    intro x w
    have hw : w = fun b => p₁ sp (sp.symm (w b, 0)) := by funext b; simp [p₁]
    rw [hw, ← hg', ← fst_hR hsig, ← fst_hR hsig, hinv]
  refine ⟨h, hh, fun x => ?_⟩
  rw [mem_loc_iff hJ hdet hsig hdiag, mem_loc_iff hJ hdet hsig hdiag, hg', ← hA,
    mem_cmp₂_iff hJ hdet hsig hdiag hL.1, mem_cmp₂_iff hJ hdet hsig hdiag hM.1]
  refine and_congr Iff.rfl ⟨fun H w' hw' => ?_, fun H w hw => ?_⟩
  · obtain ⟨w, rfl⟩ := GlobalTheory.DualFrames.exists_mulVec g w'
    rw [hp]
    exact H w ((hB w).2 hw')
  · rw [← hp]
    exact H _ ((hB w).1 hw)

end GlobalTheory.St.G
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLocalUnitaryLatticesOfLevelStatement
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localUnitary_lattices_of_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → TLat cm.sig J T f M → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∃ h ∈ UPts cm.sig J (v.adicCompletion F), ∀ x, x ∈ loc v L ↔ h.1 *ᵥ x ∈ loc v M := by
  first | exact @GlobalTheory.St.G.exists_unitary_of_TLat | exact GlobalTheory.St.G.exists_unitary_of_TLat | (intros; apply GlobalTheory.St.G.exists_unitary_of_TLat <;> assumption)
end
