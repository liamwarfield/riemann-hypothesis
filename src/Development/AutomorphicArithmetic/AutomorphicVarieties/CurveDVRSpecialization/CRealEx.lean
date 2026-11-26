module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GdEndOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CocycleTransportH1fSurjective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.NontrivTr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SpaceEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairMapOfAlgHom

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ResidualDatumInertiaCharactersTrivial
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

private theorem unit_eq_one_of_pow {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (x : kˣ) (m : ℕ)
    (h : x ^ l ^ m = 1) : x = 1 := by
  apply Units.ext
  have h' : ((x : k) - 1) ^ l ^ m = 0 := by
    rw [sub_pow_char_pow, one_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero m (Fact.out : l.Prime).ne_zero)).mp h')

private theorem mu_pow {l : ℕ} [Fact l.Prime] (F : GFrame l) (v : F.Vl) (g : F.mu v) :
    ∃ m : ℕ, (g : F.Gv v) ^ l ^ m ∈ (commutator (F.Gv v)).topologicalClosure := by
  have hg : (QuotientGroup.mk' (commutator (F.Gv v)).topologicalClosure (g : F.Gv v)) ∈
      CommGroup.primaryComponent (TopologicalAbelianization (F.Gv v)) l := g.2
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (QuotientGroup.mk' (commutator (F.Gv v)).topologicalClosure (g : F.Gv v)) ^ l ^ m = 1 := by
    first
      | exact hg
      | (obtain ⟨m, hm⟩ := hg; exact ⟨m, by rw [← hm]; exact pow_orderOf_eq_one _⟩)
  refine ⟨m, ?_⟩
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm
  exact hm

theorem UpperTheory.V.W.residualDatum_inertia_characters_trivial :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [CharP (ResidueField O) l] (n : ℕ) (r : Resid F O n) (v : F.Vl) (i : Fin n) (g : F.mu v), r.psib v i g = 1 ∧ Units.map (residue O : O →* ResidueField O) (r.th v i g) = 1 := by
  intro l _ F O _ _ _ _ n r v i g
  obtain ⟨m, hm⟩ := mu_pow F v g
  constructor
  · apply unit_eq_one_of_pow l _ m
    rw [← map_pow]
    have hle : (commutator (F.Gv v)).topologicalClosure ≤ (r.psib v i).ker :=
      Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker _)
        (Subgroup.isClosed_of_isOpen _ (r.psib_open v i))
    exact hle hm
  · apply unit_eq_one_of_pow l _ m
    rw [← map_pow, ← map_pow, r.th_comm v i (g ^ l ^ m) (by simpa using hm), map_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ResidualOkOfLocalCharsRestrict
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

section
open Polynomial UpperTheory.V.W

private theorem chi_ofRep' {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (y : MonoidAlgebra A G) : (GDet.ofRep ρ).chi y =
      (Matrix.scalar (Fin n) X - GDet.repAlg ρ A[X] (MonoidAlgebra.mapRingHom G C y)).det := by
  show Matrix.det (GDet.repAlg ρ A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)) = _
  rw [map_sub]
  congr 2
  simp [GDet.repAlg, MonoidAlgebra.lift_single, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

private theorem prod_diagonal {n : ℕ} {A : Type} [CommRing A] (L : List (Fin n → A)) :
    (L.map Matrix.diagonal).prod = Matrix.diagonal L.prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.prod_cons, Matrix.diagonal_mul_diagonal]
    rfl

private theorem rep_oEl {l : ℕ} [Fact l.Prime] {G : GFrame l} {k : Type} [CommRing k] {n : ℕ}
    (χ : Fin n → G.G₀ →* kˣ) (v : G.Vl) (ψ : Fin n → G.Gv v →* kˣ) (h : ∀ i g, ψ i g = χ i (G.φ v g))
    (g : Fin n → G.Gv v) :
    GDet.repAlg (diagRep χ) k[X] (MonoidAlgebra.mapRingHom _ C (G.oEl v ψ g)) = 0 := by
  have hf : ∀ i, GDet.repAlg (diagRep χ) k[X] (MonoidAlgebra.mapRingHom _ C
      (MonoidAlgebra.single (G.φ v (g i)) 1 - MonoidAlgebra.single 1 ((ψ i (g i) : kˣ) : k))) =
      Matrix.diagonal (fun j => C ((χ j (G.φ v (g i)) : kˣ) : k) - C ((ψ i (g i) : kˣ) : k)) := by
    intro i
    simp [GDet.repAlg, MonoidAlgebra.lift_single, diagRep, Matrix.smul_one_eq_diagonal,
      Matrix.diagonal_sub]
  unfold GFrame.oEl
  rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
  simp only [Function.comp_def, hf]
  have key : (List.ofFn fun i => Matrix.diagonal
      (fun j => C ((χ j (G.φ v (g i)) : kˣ) : k) - C ((ψ i (g i) : kˣ) : k))) =
      (List.ofFn fun i j => C ((χ j (G.φ v (g i)) : kˣ) : k) - C ((ψ i (g i) : kˣ) : k)).map
        Matrix.diagonal := by
    rw [List.map_ofFn]
    rfl
  rw [key, prod_diagonal]
  have hz : (List.ofFn fun i j => C ((χ j (G.φ v (g i)) : kˣ) : k) - C ((ψ i (g i) : kˣ) : k)).prod
      = 0 := by
    funext j
    rw [List.prod_ofFn, Finset.prod_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [h]
  rw [hz]
  exact Matrix.diagonal_zero

end

theorem UpperTheory.residual_ok_of_local_chars_restrict :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [CharP (ResidueField O) l]
      {G : W.GFrame l} {n : ℕ} (r : W.Resid G O n), 1 ≤ n →
      (∀ v i g, r.psib v i g = r.chib i (G.φ v g)) → r.Ok := by
  intro l _ O _ _ _ _ G n r hn hps
  refine ⟨fun v g h => ?_, fun v i g => ?_⟩
  · simp only [W.Resid.Dbar, W.GDet.tr, W.GDet.lam]
    rw [chi_ofRep', map_mul, map_mul, rep_oEl r.chib v (r.psib v) (hps v) g, mul_zero, sub_zero,
      Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  · rw [(W.residualDatum_inertia_characters_trivial l G O n r v i g).1, (W.residualDatum_inertia_characters_trivial l G O n r v i g).2]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionDecompositionGroups
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

private theorem open_toZMod (l : ℕ) [Fact l.Prime] : IsOpen {x : ℤ_[l] | PadicInt.toZMod x = 1} := by
  have hS : {x : ℤ_[l] | PadicInt.toZMod x = 1} = {x | ‖x - 1‖ < 1} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod,
      RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
  rw [hS]
  exact isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const

theorem UpperTheory.frame_criterion_decomposition_groups :
    UpperTheory.V.Pr.ExistsPrimeSplitInKernelWithNontrivialCyclotomic := by
  unfold UpperTheory.V.Pr.ExistsPrimeSplitInKernelWithNontrivialCyclotomic
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k hK g hg hc M' hM'
  let ρ : G (W.Lp L) Ω →* Φ.Γ := k.p.comp (toUpl Ω L)
  have hemb : Continuous (galEmb ℚ (W.Lp L) Ω) := (galEmbTop ℚ (W.Lp L) Ω).1.continuous
  have hρ : Continuous ρ := by
    have hto : Continuous (toUpl Ω L) := continuous_induced_rng.2 hemb
    exact k.p_cont.comp hto
  let U1 : Subgroup (G (W.Lp L) Ω) := Φ.Ψ.ker.comap ρ
  let U2 : Subgroup (G (W.Lp L) Ω) :=
    ((Units.map (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toMonoidHom).comp (cycZ (W.Lp L) Ω l)).ker
  let U3 : Subgroup (G (W.Lp L) Ω) := (η.comp (galEmb ℚ (W.Lp L) Ω)).ker
  have hU2 : ∀ τ, τ ∈ U2 ↔ PadicInt.toZMod (cycZ (W.Lp L) Ω l τ : ℤ_[l]) = 1 := by
    intro τ
    simp [U2, MonoidHom.mem_ker, Units.ext_iff]
  have hfix : ∀ τ : G (W.Lp L) Ω, τ ∈ galOf (W.Lp L) L Ω ↔ τ ∈ U3 := by
    intro τ
    change _ ↔ η (galEmb ℚ (W.Lp L) Ω τ) = 1
    rw [← k.mem_range_resP τ, mem_galOf]
    constructor
    · intro hτ
      exact ⟨AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) (fun x => hτ x), AlgEquiv.ext fun y => rfl⟩
    · rintro ⟨t, rfl⟩ x
      exact t.commutes x
  have hO1 : IsOpen (U1 : Set (G (W.Lp L) Ω)) := hK.preimage hρ
  have hO2 : IsOpen (U2 : Set (G (W.Lp L) Ω)) := by
    have hset : (U2 : Set (G (W.Lp L) Ω)) =
        (fun τ => (cycZ (W.Lp L) Ω l τ : ℤ_[l])) ⁻¹' {x : ℤ_[l] | PadicInt.toZMod x = 1} := by
      ext τ
      exact hU2 τ
    rw [hset]
    exact (open_toZMod l).preimage (Units.continuous_val.comp (continuous_cycZ (W.Lp L) Ω l))
  have hO3 : IsOpen (U3 : Set (G (W.Lp L) Ω)) := by
    have hset : (U3 : Set (G (W.Lp L) Ω)) = galOf (W.Lp L) L Ω := by
      ext τ
      exact (hfix τ).symm
    rw [hset]
    exact (galEmbTop (W.Lp L) L Ω).2.1
  haveI hN1 : U1.Normal := (Φ.Ψ.normal_ker).comap ρ
  let U : Subgroup (G (W.Lp L) Ω) := U1 ⊓ U2 ⊓ U3
  haveI : U.Normal := inferInstance
  have hOU : IsOpen (U : Set (G (W.Lp L) Ω)) := (hO1.inter hO2).inter hO3
  let g' : G (W.Lp L) Ω := W.resP L Ω g
  obtain ⟨w, A, p, σ', -, hp, hpM, -, hpw, hnorm, -, hA, hIne, hFrob, hσU⟩ :=
    Loc.v00 U hOU g' ∅ M' hM'
  have hg'1 : g' ∈ U1 := hg
  have hg'3 : g' ∈ U3 := (k.mem_range_resP g').1 ⟨g, rfl⟩
  have hσeq : σ' = g' * (σ'⁻¹ * g')⁻¹ := by group
  have hσ1 : σ' ∈ U1 := by
    rw [hσeq]
    exact U1.mul_mem hg'1 (U1.inv_mem hσU.1.1)
  have hσ3 : σ' ∈ U3 := by
    rw [hσeq]
    exact U3.mul_mem hg'3 (U3.inv_mem hσU.2)
  have hσ2 : σ' ∉ U2 := by
    intro h
    have h2 := U2.mul_mem h hσU.1.2
    rw [mul_inv_cancel_left] at h2
    exact hc ((hU2 g').1 h2)
  let H : Subgroup (G (W.Lp L) Ω) := U1 ⊓ U3
  have hOH : IsOpen (H : Set (G (W.Lp L) Ω)) := hO1.inter hO3
  have hIH : Ine A ≤ H := fun τ hτ => ⟨(hIne hτ).1.1, (hIne hτ).2⟩
  have hFrob' : IsFrob A (normV w) σ' := by
    rw [hnorm]
    exact hFrob
  have hDec : (Dec A : Subgroup (G (W.Lp L) Ω)) ≤ H :=
    Kum.decGen (W.Lp L) Ω A w σ' H hA hFrob' hOH hIH ⟨hσ1, hσ3⟩
  refine ⟨w, A, p, hp, hpM, hnorm, hpw, hA, ?_, ?_, ?_⟩
  · intro τ hτ
    exact (k.mem_range_resP τ).2 (hDec hτ).2
  · intro t ht
    have ht' : W.resP L Ω t ∈ (Dec A : Subgroup (G (W.Lp L) Ω)) := ht
    exact (hDec ht').1
  · obtain ⟨t, ht⟩ := (k.mem_range_resP σ').2 hσ3
    refine ⟨t, ?_, ?_⟩
    · change W.resP L Ω t ∈ (Dec A : Subgroup (G (W.Lp L) Ω))
      rw [ht]
      exact hFrob.1
    · change PadicInt.toZMod (cycZ (W.Lp L) Ω l (W.resP L Ω t) : ℤ_[l]) ≠ 1
      rw [ht]
      exact fun h => hσ2 ((hU2 σ').2 h)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionLambdaCharacters
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

theorem UpperTheory.frame_criterion_lambda_characters :
    UpperTheory.V.Pr.CrLam := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k v A hA hM
  haveI := Φ.cv v
  haveI := Φ.t2v v
  obtain ⟨hemb, -, -⟩ := galEmbTop ℚ L Ω
  let e1 : Dec (F := L) A →* G ℚ Ω := (galEmb ℚ L Ω).comp (Dec (F := L) A).subtype
  let e2 : Φ.Gv v →* G ℚ Ω := (upl Ω L).subtype.comp (k.j v)
  have he1 : Function.Injective e1 := hemb.injective.comp Subtype.val_injective
  have he2 : Function.Injective e2 := Subtype.val_injective.comp (k.j_inj v)
  have hrange : e1.range = e2.range := by
    ext τ
    constructor
    · rintro ⟨g, rfl⟩
      have hup : e1 g ∈ upl Ω L := by
        have := galEmb_mem ℚ L Ω (g : G L Ω)
        rw [k.gal] at this
        exact this.1
      have hdec : e1 g ∈ Dec (F := ℚ) (k.pl v) := by
        show galEmb ℚ L Ω g ∈ _
        rw [← hA, galEmb_mem_Dec]
        exact g.2
      obtain ⟨x, hx⟩ := (k.j_range v ⟨_, hup⟩).2 hdec
      exact ⟨x, congrArg Subtype.val hx⟩
    · rintro ⟨x, rfl⟩
      have hdec : e2 x ∈ Dec (F := ℚ) A := by
        rw [hA]
        exact (k.j_range v (k.j v x)).1 ⟨x, rfl⟩
      have hup : e2 x ∈ upl Ω L := (k.j v x).2
      have hker : e2 x ∈ η.ker := k.split A hM ⟨hdec, hup⟩
      have hfix : e2 x ∈ galOf ℚ L Ω := by
        rw [k.gal]
        exact ⟨hup, hker⟩
      let g : G L Ω := AlgEquiv.ofRingEquiv (f := (e2 x).toRingEquiv) (fun y => hfix y)
      have hg : galEmb ℚ L Ω g = e2 x := by
        ext y
        rfl
      have hgd : g ∈ Dec (F := L) A := by
        rw [← galEmb_mem_Dec (k := ℚ), hg]
        exact hdec
      exact ⟨⟨g, hgd⟩, hg⟩
  let m : Dec (F := L) A ≃* Φ.Gv v :=
    (MonoidHom.ofInjective he1).trans ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective he2).symm)
  have hm : ∀ g, e2 (m g) = e1 g := by
    intro g
    have := MonoidHom.ofInjective_apply he2 (x := m g)
    rw [← this, ← MonoidHom.ofInjective_apply he1 (x := g)]
    simp [m]
  have hinv : Continuous m.symm := by
    have hcomp : e1 ∘ m.symm = e2 := by
      funext x
      rw [Function.comp_apply, ← hm, MulEquiv.apply_symm_apply]
    have he1emb : Topology.IsEmbedding e1 := hemb.comp Topology.IsEmbedding.subtypeVal
    rw [he1emb.continuous_iff, hcomp]
    exact continuous_subtype_val.comp (k.j_cont v)
  have hfwd : Continuous m := by
    have := hinv.continuous_symm_of_equiv_compact_to_t2 (f := m.symm.toEquiv)
    simpa using this
  refine ⟨{ m with continuous_toFun := hfwd, continuous_invFun := hinv }, fun g => ?_⟩
  exact hm g
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionKernel
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

open scoped Pointwise in
private theorem conj_ine {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : W.Plc k} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) :
    ∃ g : G k Ω, ∀ τ ∈ Ine (F := k) B, g⁻¹ * τ * g ∈ Ine (F := k) A := by
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hB
  have hlift : IsLift (RingEquiv.refl k) σ.toRingEquiv := fun x => σ.commutes x
  have hmem : ∀ x : Ω, σ.toRingEquiv x ∈ B ↔ x ∈ A := by
    intro x
    rw [← hσ]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨σ, fun τ hτ => ?_⟩
  have h1 := conjGal_mem_Ine hlift hmem hτ
  have heq : conjGal hlift τ = σ⁻¹ * τ * σ := AlgEquiv.ext fun x => rfl
  rw [← heq]
  exact h1

private theorem ine_NS {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {S : Set (W.Plc k)} {A : ValuationSubring Ω} {v : W.Plc k} (hv : v ∉ S)
    (hA : IsPlaceOver A v) {t : G k Ω} (ht : t ∈ Ine (F := k) A) : toGS Ω S t = 1 := by
  refine (QuotientGroup.eq_one_iff t).2 (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_))
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, ht⟩

private theorem normal_map {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (N : Subgroup F.G₀) (hN : N.Normal)
    (hc : ∀ g ∈ N, F.conj g ∈ N) : (N.map F.η.ker.subtype).Normal := by
  constructor
  rintro _ ⟨m, hm, rfl⟩ γ
  by_cases hγ : F.η γ = 1
  · exact ⟨⟨γ, hγ⟩ * m * (⟨γ, hγ⟩ : F.G₀)⁻¹, hN.conj_mem m hm _, rfl⟩
  · have hγ' : F.η γ = -1 := (Int.units_eq_one_or _).resolve_left hγ
    have h0 : F.η (F.c⁻¹ * γ) = 1 := by
      rw [map_mul, map_inv, F.η_c, hγ']
      simp
    let γ0 : F.G₀ := ⟨F.c⁻¹ * γ, h0⟩
    refine ⟨F.conj (γ0 * m * γ0⁻¹), hc _ (hN.conj_mem m hm γ0), ?_⟩
    show F.c * (F.c⁻¹ * γ * (m : F.Γ) * (F.c⁻¹ * γ)⁻¹) * F.c⁻¹ = γ * (m : F.Γ) * γ⁻¹
    group

theorem UpperTheory.frame_criterion_kernel :
    UpperTheory.V.Pr.CrKer := by
  unfold UpperTheory.V.Pr.CrKer
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k s x V hS π hπ N hN hNc hNconj hIu hI0
  let N' : Subgroup V.frame.Γ := N.map V.frame.η.ker.subtype
  haveI hN'n : N'.Normal := normal_map V.frame N hN hNconj
  have hG0c : IsClosed (V.frame.η.ker : Set V.frame.Γ) :=
    Subgroup.isClosed_of_isOpen _ V.frame.η_open
  have hN'c : IsClosed (N' : Set V.frame.Γ) := by
    rw [Subgroup.coe_map]
    exact hG0c.isClosedEmbedding_subtypeVal.isClosedMap _ hNc
  let K : Subgroup (G (W.Lp L) Ω) := N'.comap (toGS Ω V.S')
  have hKc : IsClosed (K : Set (G (W.Lp L) Ω)) := hN'c.preimage (continuous_toGS Ω V.S')
  haveI hKn : K.Normal := hN'n.comap _
  let Kup : Subgroup (upl Ω L) := K.map (toUpl Ω L)
  haveI hKupn : Kup.Normal := hKn.map _ toUpl_surj
  have hind : Topology.IsInducing (toUpl Ω L) :=
    (Topology.IsInducing.subtypeVal.of_comp_iff).1 (galEmbTop ℚ (W.Lp L) Ω).1.isInducing
  have hKupc : IsClosed (Kup : Set (upl Ω L)) := by
    obtain ⟨t, ht, hpre⟩ := hind.isClosed_iff.1 hKc
    rw [Subgroup.coe_map, ← hpre, Set.image_preimage_eq t toUpl_surj]
    exact ht
  have hgen : ∀ u : upl Ω L, ∀ B' : ValuationSubring Ω, ¬B'.valuation (l : Ω) < 1 →
      (u : G ℚ Ω) ∈ Ine B' → barChar O Ψ (u : G ℚ Ω) = 1 → u ∈ Kup := by
    intro u B' hl hIne hbar
    obtain ⟨τ, hτ⟩ := toUpl_surj (Ω := Ω) (L := L) u
    refine ⟨τ, ?_, hτ⟩
    have hτI : τ ∈ Ine (F := W.Lp L) B' := by
      rw [← hτ] at hIne
      exact hIne
    by_cases htop : B' = ⊤
    · have hbot := ((places (W.Lp L) Ω l B').2.1 htop).1
      rw [hbot] at hτI
      rw [Subgroup.mem_bot.1 hτI]
      exact K.one_mem
    obtain ⟨v, hv⟩ := (places (W.Lp L) Ω l B').1 htop
    by_cases hvS : v ∈ V.S'
    · have hvS' : v ∈ s.S := hS ▸ hvS
      obtain ⟨h, hh⟩ := conj_ine (s.hA v) hv
      have hτ' := hh τ hτI
      obtain ⟨t, ht⟩ := s.unr (s.A v) v (s.hA v) hτ'
      have htI : t ∈ Ine (F := L) (s.A v) := by
        have h1 : W.resP L Ω t ∈ Ine (F := W.Lp L) (s.A v) := by
          rw [ht]
          exact hτ'
        exact h1
      have hprN : V.pr t ∈ N := by
        rcases hvS' with hlv | hvSt | hv0
        · exfalso
          exact hl ((natCast_place hv l).2 hlv)
        · apply hIu ⟨v, hvSt⟩ (V.pr t) ⟨t, htI, rfl⟩
          rw [hπ t, k.galois_link_projection_coe, k.psi]
          change barChar O Ψ (galEmb ℚ (W.Lp L) Ω (W.resP L Ω t)) = 1
          rw [ht, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv,
            mul_comm ((barChar O Ψ) ((galEmb ℚ (W.Lp L) Ω) h))⁻¹ _, inv_mul_cancel_right]
          have hu : (galEmb ℚ (W.Lp L) Ω) τ = (u : G ℚ Ω) := by
            rw [← hτ]
            rfl
          rw [hu]
          exact hbar
        · apply hI0
          subst hv0
          exact ⟨t, htI, rfl⟩
      have hτ'N : toGS Ω V.S' (h⁻¹ * τ * h) ∈ N' := by
        refine ⟨V.pr t, hprN, ?_⟩
        change toGS Ω V.S' (W.resP L Ω t) = _
        rw [ht]
      have hconj := hN'n.conj_mem _ hτ'N (toGS Ω V.S' h)
      have heq : toGS Ω V.S' h * toGS Ω V.S' (h⁻¹ * τ * h) * (toGS Ω V.S' h)⁻¹ = toGS Ω V.S' τ := by
        simp only [map_mul, map_inv]
        group
      change toGS Ω V.S' τ ∈ N'
      rw [← heq]
      exact hconj
    · change toGS Ω V.S' τ ∈ N'
      rw [ine_NS hvS hv hτI]
      exact N'.one_mem
  have hpker : k.p.ker ≤ Kup := by
    rw [k.p_ker]
    apply Subgroup.topologicalClosure_minimal _ _ hKupc
    apply Subgroup.normalClosure_le_normal
    rintro u ⟨B', hl, hIne, -, hbar⟩
    exact hgen u B' hl hIne hbar
  intro g0 hg0
  obtain ⟨g, rfl⟩ := pr_surj V g0
  have hp0 : k.p0 g = 1 := by
    rw [← hπ g]
    exact hg0
  have hpk : toUpl Ω L (W.resP L Ω g) ∈ k.p.ker := by
    rw [MonoidHom.mem_ker, ← k.galois_link_projection_coe, hp0]
    rfl
  obtain ⟨τ, hτK, hτeq⟩ := hpker hpk
  have hτg : τ = W.resP L Ω g := toUpl_inj hτeq
  obtain ⟨m, hm, hmeq⟩ := hτK
  have hpr : V.pr g = m := by
    apply Subtype.ext
    change toGS Ω V.S' (W.resP L Ω g) = (m : V.frame.Γ)
    rw [← hτg]
    exact hmeq.symm
  rw [hpr]
  exact hm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionProjection
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

theorem UpperTheory.frame_criterion_projection :
    UpperTheory.V.Pr.CrPi := by
  unfold UpperTheory.V.Pr.CrPi
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k s x V hS
  have hup : Continuous (toUpl Ω L) := by
    unfold UpperTheory.V.Pr.toUpl
    exact (continuous_restrictScalarsHom ℚ (W.Lp L) Ω).subtype_mk _
  let f : G (W.Lp L) Ω →* Φ.Γ := k.p.comp (toUpl Ω L)
  have hf : Continuous f := k.p_cont.comp hup
  have hclosed : IsClosed (f.ker : Set (G (W.Lp L) Ω)) := by
    have h := (isClosed_singleton (x := (1 : Φ.Γ))).preimage hf
    exact h
  have hNS : NS Ω V.S' ≤ f.ker := by
    unfold ReciprocityTheory.Gal.NS
    apply Subgroup.topologicalClosure_minimal _ _ hclosed
    apply Subgroup.normalClosure_le_normal
    intro t ht
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff] at ht
    obtain ⟨v, hv, A, hA, ht⟩ := ht
    rw [hS] at hv
    unfold UpperTheory.V.W.HidaSetting.S at hv
    simp only [Set.mem_setOf_eq, not_or] at hv
    obtain ⟨hl, hSt, -⟩ := hv
    have hMv := fun hM => hSt ((x.St v).2 ⟨hM, hl⟩)
    have hti : galEmb ℚ (W.Lp L) Ω t ∈ Ine A := (galEmb_mem_Ine A t).2 ht
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    show k.p (toUpl Ω L t) = 1
    rw [← MonoidHom.mem_ker, k.p_ker]
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    refine ⟨A, ?_, hti, ?_, ?_⟩
    · rw [natCast_place hA]
      exact hl
    · exact k.unr A ⟨hti, (toUpl Ω L t).2⟩
    · have hΨ : Ψ (galEmb ℚ (W.Lp L) Ω t) = 1 :=
        x.unr A (by rw [natCast_place hA]; exact hMv) hti
      unfold barChar
      show Units.map _ (Ψ (galEmb ℚ (W.Lp L) Ω t)) = 1
      rw [hΨ, map_one]
  let πt : GS Ω V.S' →* Φ.Γ := QuotientGroup.lift (NS Ω V.S') f hNS
  have hπt : ∀ t, πt (toGS Ω V.S' t) = f t := fun t => rfl
  have hπtc : Continuous πt := continuous_coinduced_dom.2 hf
  have hmem : ∀ y : V.η.ker, πt y.1 ∈ Φ.del.ker := by
    intro y
    obtain ⟨g, hg⟩ := pr_surj V y
    rw [← hg]
    exact (k.p0 g).2
  let π : V.η.ker →* Φ.del.ker := (πt.comp V.η.ker.subtype).codRestrict _ hmem
  have hcs : f s.c = Φ.c := by
    obtain ⟨h, hpc⟩ := k.c
    have h2 : toUpl Ω L s.c = ⟨σ, h⟩ := Subtype.ext x.c
    show k.p (toUpl Ω L s.c) = Φ.c
    rw [h2, hpc]
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · exact (hπtc.comp continuous_subtype_val).subtype_mk _
  · intro g
    rfl
  · intro y0
    let y : V.η.ker := y0
    apply Subtype.ext
    show πt (toGS Ω V.S' s.c * y.1 * (toGS Ω V.S' s.c)⁻¹) = Φ.c * πt y.1 * Φ.c⁻¹
    rw [map_mul, map_mul, map_inv, hπt, hcs]
  · intro y0
    let y : V.η.ker := y0
    obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective (NS Ω V.S') y.1
    show Φ.eps (πt y.1) = V.ε y.1
    have ht' : toGS Ω V.S' t = y.1 := ht
    rw [← ht', hπt]
    show Φ.eps (k.p (toUpl Ω L t)) = V.ε (toGS Ω V.S' t)
    rw [k.eps, ← MonoidHom.comp_apply V.ε, V.hε]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FrameCriterionResidual
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

namespace UpperTheory.V.Pr

end UpperTheory.V.Pr

theorem UpperTheory.frame_criterion_residual :
    UpperTheory.V.Pr.CrResid := by
  intro l _ O _ _ _ F G n hn hk hg π hπ hs hc κ hκ hκe
  let χ : Fin n → G.G₀ →* (ResidueField O)ˣ := fun i =>
    { toFun := fun g => F.Ψ (π g : F.Γ) ^ Fr.w n i * W.pushCh (residue O) κ g
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [map_mul, Subgroup.coe_mul, mul_zpow]
        exact mul_mul_mul_comm _ _ _ _ }
  have hψ : IsOpen ((F.Ψ.comp (F.del.ker.subtype.comp π)).ker : Set G.G₀) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact hk.preimage (continuous_subtype_val.comp hπ)
  have hκo : IsOpen ((W.pushCh (residue O) κ).ker : Set G.G₀) := by
    have h1 := (hκ 1).isOpen_fiber (Ideal.Quotient.mk (maximalIdeal O ^ 1) 1)
    convert h1 using 1
    ext g
    rw [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq, Ideal.Quotient.eq, pow_one, Units.ext_iff]
    show residue O (κ g : O) = 1 ↔ _
    rw [← map_one (residue O)]
    exact Ideal.Quotient.eq
  have hopen : ∀ i, IsOpen ((χ i).ker : Set G.G₀) := by
    intro i
    refine Subgroup.isOpen_mono (H₁ := (F.Ψ.comp (F.del.ker.subtype.comp π)).ker ⊓ (W.pushCh (residue O) κ).ker) ?_ (by rw [Subgroup.coe_inf]; exact hψ.inter hκo)
    intro g hg
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker]
    show F.Ψ (π g : F.Γ) ^ Fr.w n i * W.pushCh (residue O) κ g = 1
    rw [hg.2, mul_one]
    have : F.Ψ (π g : F.Γ) = 1 := hg.1
    rw [this, one_zpow]
  have hinj : Function.Injective χ := by
    intro i j hij
    obtain ⟨g, hg0⟩ := hs F.g0
    have h := DFunLike.congr_fun hij g
    change F.Ψ (π g : F.Γ) ^ Fr.w n i * _ = F.Ψ (π g : F.Γ) ^ Fr.w n j * _ at h
    rw [mul_right_cancel_iff, hg0] at h
    have key : F.Ψ (F.g0 : F.Γ) ^ (Fr.w n i - Fr.w n j) = 1 := by
      rw [zpow_sub, h, mul_inv_cancel]
    have hu2 : F.Ψ (F.g0 : F.Γ) ^ (2:ℤ) ≠ 1 := by exact_mod_cast hg
    have hu1 : F.Ψ (F.g0 : F.Γ) ≠ 1 := by
      intro h1
      apply hu2
      rw [h1, one_zpow]
    rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp [Fr.w] at key ⊢
    all_goals first
      | exact hg key
      | exact hu1 key
      | exact hu2 key
      | exact hu1 (inv_eq_one.mp key)
      | exact hg (inv_eq_one.mp (by simpa [zpow_neg] using key))
  have hw : ∀ i : Fin n, Fr.w n (Fin.rev i) = - Fr.w n i := by
    intro i
    rcases hn with rfl | rfl <;> fin_cases i <;> simp [Fr.w] <;> decide
  have hΨc : ∀ g, F.Ψ (π (G.conj g) : F.Γ) = F.Ψ (π g : F.Γ) := by
    intro g
    rw [hc]
    simp [Fr.Frame.conj, MulAut.conjNormal_apply]
  have heps : ∀ g, Units.map (residue O : O →* ResidueField O) (G.eps O O g) = G.eps O (ResidueField O) g := by
    intro g
    ext
    simp [W.GFrame.eps, W.pushCh]
  have hκc : ∀ g, W.pushCh (residue O) κ (G.conj g) = (G.eps O (ResidueField O) g) ^ (1 - (n:ℤ)) * (W.pushCh (residue O) κ g)⁻¹ := by
    intro g
    have h1 : κ (G.conj g) = (G.eps O O g) ^ (1 - (n:ℤ)) * (κ g)⁻¹ := by
      rw [← hκe g, mul_comm (κ g) (κ (G.conj g)), mul_inv_cancel_right]
    show Units.map (residue O : O →* ResidueField O) (κ (G.conj g)) = _
    rw [h1, map_mul, map_inv, map_zpow, heps]
    rfl
  have hstar : ∀ i g, (G.eps O (ResidueField O) g) ^ (1 - (n:ℤ)) * (χ i (G.conj g))⁻¹ = χ (Fin.rev i) g := by
    intro i g
    show _ * (F.Ψ (π (G.conj g) : F.Γ) ^ Fr.w n i * W.pushCh (residue O) κ (G.conj g))⁻¹ = F.Ψ (π g : F.Γ) ^ Fr.w n (Fin.rev i) * W.pushCh (residue O) κ g
    rw [hΨc, hκc, hw, zpow_neg, mul_inv, mul_inv, inv_inv, mul_left_comm, mul_inv_cancel_left]
  have hpolar : G.IsPolar O (W.GDet.ofRep (W.diagRep χ)) := by
    intro B _ _ _ _ y
    let f : Fin n → G.G₀ →* B := fun i => (algebraMap (ResidueField O) B : ResidueField O →* B).comp ((Units.coeHom (ResidueField O)).comp (χ i))
    have hdiag : ∀ z : MonoidAlgebra B G.G₀, W.GDet.repAlg (W.diagRep χ) B z = Matrix.diagonal (fun i => MonoidAlgebra.lift B B G.G₀ (f i) z) := by
      intro z
      induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy =>
        rw [map_add (f := _), hx, hy, Matrix.diagonal_add]
        congr 1
        ext i
        simp [map_add (f := _)]
      | single g b =>
        ext i j
        simp [f, W.GDet.repAlg, W.diagRep, MonoidAlgebra.lift_single, Matrix.diagonal_apply]
    have hepsB : ∀ g, Units.map (algebraMap (ResidueField O) B : ResidueField O →* B) (G.eps O (ResidueField O) g) = G.eps O B g := by
      intro g
      ext
      simp [W.GFrame.eps, W.pushCh, IsScalarTower.algebraMap_apply O (ResidueField O) B]
    have hs1 : ∀ (g : G.G₀) (b : B), G.star O B n (MonoidAlgebra.single g b) = MonoidAlgebra.single (G.conj g)⁻¹ (b * ((G.eps O B g ^ (1 - (n:ℤ)) : Bˣ) : B)) := by
      intro g b
      simp [W.GFrame.star, W.GFrame.starOp, MonoidAlgebra.lift_single, MonoidAlgebra.smul_single']
    have hrev : ∀ i z, MonoidAlgebra.lift B B G.G₀ (f i) (G.star O B n z) = MonoidAlgebra.lift B B G.G₀ (f (Fin.rev i)) z := by
      intro i z
      induction z using MonoidAlgebra.induction_linear with
      | zero => simp [W.GFrame.star]
      | add x y hx hy =>
        have hadd : G.star O B n (x + y) = G.star O B n x + G.star O B n y := by simp [W.GFrame.star]
        rw [hadd, map_add (f := _), map_add (f := _), hx, hy]
      | single g b =>
        rw [hs1 g b, MonoidAlgebra.lift_single, MonoidAlgebra.lift_single, smul_eq_mul, smul_eq_mul, mul_assoc]
        congr 1
        rw [← hepsB g, ← map_zpow, Units.coe_map]
        show _ = algebraMap (ResidueField O) B ((χ (Fin.rev i) g : (ResidueField O)ˣ) : ResidueField O)
        rw [← hstar i g, Units.val_mul, map_mul]
        simp [f]
    show Matrix.det (W.GDet.repAlg (W.diagRep χ) B (G.star O B n y)) = Matrix.det (W.GDet.repAlg (W.diagRep χ) B y)
    rw [hdiag, hdiag, Matrix.det_diagonal, Matrix.det_diagonal]
    simp only [hrev]
    exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => rfl)
  refine ⟨⟨χ, hopen, hinj, hpolar, fun v i => (χ i).comp (G.φ v), ?_, fun _ _ => 1, ?_⟩, ?_, ?_⟩
  · intro v i
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact (hopen i).preimage (G.φ_cont v)
  · intro v i g _
    rfl
  · intro i g
    rfl
  · intro v i g
    rfl
end

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
  UpperTheory.V.Pr UpperTheory.V
open scoped Pointwise

private theorem toZMod_one_iff {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) :
    PadicInt.toZMod x = 1 ↔ PadicInt.toZModPow 1 x = 1 := by
  rw [← map_one (PadicInt.toZMod (p := l)), ← map_one (PadicInt.toZModPow (p := l) 1), ← RingHom.sub_mem_ker_iff,
    ← RingHom.sub_mem_ker_iff, PadicInt.ker_toZMod, PadicInt.ker_toZModPow, PadicInt.maximalIdeal_eq_span_p, pow_one]

private theorem exists_kernel_element_nontrivial_cyclotomic {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (F : Fr.Frame l k) {C₀ : ℕ} (h : F.Ok C₀) :
    ∃ g : F.G0, F.Ψ g = 1 ∧ PadicInt.toZMod ((F.eps g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1 := by
  haveI := h.fin
  let χ : F.G0 →* kˣ := F.Ψ.comp F.del.ker.subtype
  let ω : F.G0 →* kˣ := (F.om k).comp F.del.ker.subtype
  obtain ⟨g, h1, h2⟩ := (Loc.v0e (ι := Bool) (fun b => if b then χ else 1) ω).2 fun hm => h.f5 (by
    have hle : Subgroup.closure (Set.range fun q : Bool × Bool =>
        (if q.1 then χ else 1) / (if q.2 then χ else 1)) ≤ Subgroup.zpowers χ := by
      rw [Subgroup.closure_le]
      rintro _ ⟨⟨a, b⟩, rfl⟩
      cases a <;> cases b <;> simp
    obtain ⟨j, hj⟩ := hle hm
    exact ⟨j, fun g => (DFunLike.congr_fun hj g).symm⟩)
  refine ⟨g, h1 true false, fun e => h2 (Units.ext ?_)⟩
  show ZMod.castHom (dvd_refl l) k (PadicInt.toZMod ((F.eps g : ℤ_[l]ˣ) : ℤ_[l])) = 1
  rw [e, map_one]

private theorem val_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : ℕ} (h : a ∣ b) (ha : A.valuation (a : Ω) < 1) :
    A.valuation (b : Ω) < 1 := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_lt_one_of_lt_of_le ha ((A.valuation_le_one_iff _).2 (natCast_mem A c))

private theorem cr_unr {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] {N M : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter O N) (h : l * N ∣ M) (A : ValuationSubring Ω)
    (hA : ¬ A.valuation (M : Ω) < 1) : Ine (F := ℚ) A ≤ (Chr.Psi l e (Chr.dirG ℚ Ω ψ)).ker := fun g hg => by
  have h1 : cycZ ℚ Ω l g = 1 :=
    (Base.places ℚ Ω l A).2.2.2 (fun h' => hA (val_dvd A ((dvd_mul_right l N).trans h) h')) hg
  have h2 : Chr.cls ℚ Ω N g = 1 :=
    (Chr.clsFacts ℚ Ω N).2.2.2.2 A (fun h' => hA (val_dvd A ((dvd_mul_left N l).trans h) h')) hg
  simp [MonoidHom.mem_ker, Chr.Psi, Chr.dirG, chiO, h1, h2]

private theorem cr_mu {L Ω : Type} [Field L] [NumberField L] [Field Ω] [CharZero Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ}
    [Fact l.Prime] (A : ValuationSubring Ω) (w : W.Plc L) (hA : IsPlaceOver A w) (hl : A.valuation (l : Ω) < 1)
    (h : ∃ g ∈ Dec (F := L) A, PadicInt.toZMod ((cycZ L Ω l g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) :
    W.muG l (Dec (F := L) A) ≤ (commutator (Dec (F := L) A)).topologicalClosure := by
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := l)).1 A w hA ((natCast_place hA l).1 hl)
  obtain ⟨-, φ, b1, -, -, -, b5, -⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j
  obtain ⟨g, hg, h⟩ := h
  exact fun x hx => Loc.muNone φ b1 ⟨⟨g, hg⟩, by rw [b5]; exact h⟩ x hx

private theorem ne_top {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {v : W.Plc F}
    (h : IsPlaceOver A v) : A ≠ ⊤ := by
  rintro rfl
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have h1 := (h x).2 hx
  rw [valuation_lt_one_iff'] at h1
  have h2 := h1.2.resolve_right fun h' => h' (ValuationSubring.mem_top _)
  exact hx0 (Subtype.ext ((algebraMap F Ω).injective (h2.trans (map_zero _).symm)))

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}

private theorem cr_tame [Finite (ResidueField O)] (k : GalLink η Ψ σ g₁ B M L Φ) (A : ValuationSubring Ω)
    (hA : ¬ A.valuation (l : Ω) < 1) (g : G L Ω) (hg : g ∈ Ine (F := L) A) :
    k.p0 g ^ Nat.card (ResidueField O)ˣ = 1 := by
  show k.p0h g ^ _ = 1
  rw [← map_pow]
  refine Subtype.ext ?_
  show k.p (toUpl Ω L (W.resP L Ω (g ^ _))) ∈ ({1} : Set _)
  change toUpl Ω L (W.resP L Ω (g ^ _)) ∈ k.p.ker
  rw [k.p_ker]
  refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨A, hA, ?_, ?_, ?_⟩)
  · exact (Ine (F := L) A).pow_mem hg _
  · exact (k.mem_range_resP _).1 ⟨_, rfl⟩
  · rw [map_pow, map_pow, Subgroup.coe_pow, map_pow, pow_card_eq_one']

private theorem cr_split (k : GalLink η Ψ σ g₁ B M L Φ) (A : ValuationSubring Ω) (hA : A.valuation (M : Ω) < 1) :
    Dec (F := W.Lp L) A ≤ (W.resP L Ω).range := fun g hg =>
  (k.mem_range_resP g).2 (k.split A hA ⟨hg, (toUpl Ω L g).2⟩)

private theorem cr_set [CharP (ResidueField O) l] (k : GalLink η Ψ σ g₁ B M L Φ) {C₀ : ℕ} (ok : Φ.Ok C₀) (hlM : l ∣ M) (hM : M ≠ 0)
    (hB : B.valuation (l : Ω) < 1) (hσ : Sd.IsCC σ)
    (hΨ : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → Ine (F := ℚ) A ≤ Ψ.ker) :
    ∃ s : W.HidaSetting l L Ω, Nonempty (Ad k s) := by
  classical
  have hl : l.Prime := Fact.out
  obtain ⟨e, he⟩ := UpperTheory.frame_criterion_galois_equivariance k hB
  obtain ⟨x, hx1, hx2⟩ := exists_kernel_element_nontrivial_cyclotomic Φ ok
  obtain ⟨g, rfl⟩ := k.surjective_levelChangeBaseGroupHom x
  have hx3 : Φ.eps (k.p0 g) = cycZ L Ω l g := k.eps _
  rw [hx3] at hx2
  obtain ⟨v0, A0, p, hp, hpM, hn, hpv, hA0, hsp, hΨ0, hω⟩ := UpperTheory.frame_criterion_decomposition_groups k ok.Ψ_open g hx1 hx2
    (2 * M * (discr L).natAbs) (mul_ne_zero (mul_ne_zero two_ne_zero hM) (Int.natAbs_ne_zero.2 (discr_ne_zero L)))
  have hpM' : ¬ p ∣ M := fun h => hpM ((h.mul_left _).mul_right _)
  have hMv : ((M : ℕ) : 𝓞 (W.Lp L)) ∉ v0.asIdeal := fun h => by
    have hc : IsCoprime ((p : ℕ) : 𝓞 (W.Lp L)) (M : ℕ) := Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM')
    obtain ⟨a, b, hab⟩ := hc
    exact v0.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ hpv) (Ideal.mul_mem_left _ _ h)))
  have hlv : ∀ v : W.Plc (W.Lp L), ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal → ((M : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal := fun v h => by
    obtain ⟨c, rfl⟩ := hlM
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h
  let A : W.Plc (W.Lp L) → ValuationSubring Ω := fun v =>
    if h : ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal then k.pl (e ⟨v, h⟩) else if v = v0 then A0 else placeOf Ω v
  have hA : ∀ v, IsPlaceOver (A v) v := fun v => by
    simp only [A]
    split_ifs with h1 h2
    · exact he ⟨v, h1⟩
    · exact h2 ▸ hA0
    · exact isPlaceOver_placeOf Ω v
  have hAv : A v0 = A0 := by simp only [A, dif_neg fun h => hMv (hlv _ h), if_true]
  choose w hw using fun v => (Base.places L Ω l (A v)).1 (ne_top (hA v))
  have hfin : {v : W.Plc (W.Lp L) | ((M : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal ∧ ((l : ℕ) : 𝓞 (W.Lp L)) ∉ v.asIdeal}.Finite :=
    (Ideal.finite_factors (I := Ideal.span {((M : ℕ) : 𝓞 (W.Lp L))}) (fun h => hM (Nat.cast_eq_zero.1 (Ideal.span_singleton_eq_bot.1 h)))).subset fun v hv =>
      Ideal.dvd_span_singleton.2 hv.1
  obtain ⟨hc, -⟩ := k.c
  obtain ⟨c, hc'⟩ := toUpl_surj (L := L) ⟨σ, hc⟩
  have hcσ : galEmb ℚ (W.Lp L) Ω c = σ := congrArg Subtype.val hc'
  refine ⟨{ odd := ok.l_odd
            unr := fun A v _ g hg => (k.mem_range_resP g).2 (k.unr A ⟨hg, (toUpl Ω L g).2⟩)
            c := c
            hc := by subst hcσ; exact hσ
            w := w, A := A, hw := hw, hA := hA
            St := hfin.toFinset
            St_l := fun u hu => (hfin.mem_toFinset.1 hu).2
            v0 := v0
            v0_St := fun h => hMv (hfin.mem_toFinset.1 h).1
            p := p, p_prime := hp
            p_odd := fun h => hpM (by rw [h]; exact (dvd_mul_right 2 M).mul_right _)
            p_ne := fun h => hpM' (h ▸ hlM)
            p_unr := fun h => hpM ((Int.natCast_dvd.1 h).mul_left _)
            norm_v0_eq_one := hn
            split := ?_ }, ⟨⟨hlM, hΨ, hcσ, fun u => hfin.mem_toFinset, e, fun v => dif_pos v.2, ?_, ?_, ?_⟩⟩⟩
  · rintro v (h | h | rfl)
    · exact cr_split k _ ((natCast_place (hA v) M).2 (hlv v h))
    · exact cr_split k _ ((natCast_place (hA v) M).2 (hfin.mem_toFinset.1 h).1)
    · rw [hAv]; exact hsp
  · exact fun h => hMv ((natCast_place (hA v0) M).1 h)
  · show ∀ g ∈ Dec (F := L) (A v0), _
    rw [hAv]; exact hΨ0
  · show ∃ g ∈ Dec (F := L) (A v0), _
    rw [hAv]; exact hω

end

theorem UpperTheory.V.Pr.cRealEx :
    GlobalTheory.Published.GlobalArtinReciprocity → UpperTheory.V.W.LocCFTAll → UpperTheory.V.W.LevEx → UpperTheory.V.W.ProModularRingExists → UpperTheory.V.Pr.CRealEx := by
  intro _ _ hLev hB0 Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f n ka C₀ hn ok big hle hf hka hkO
  have hl : l.Prime := Fact.out
  haveI := ok.fin
  have hlM : l ∣ M := (dvd_mul_right l N).trans H.dvd
  obtain ⟨s, ⟨a⟩⟩ := cr_set k ok hlM H.M_pos H.atl H.cc (cr_unr e ψ H.dvd)
  have hSfin : s.S.Finite := by
    refine ((Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 (W.Lp L))})
      (fun h => hl.ne_zero (Nat.cast_eq_zero.1 (Ideal.span_singleton_eq_bot.1 h)))).union
        (s.St.finite_toSet.union (Set.finite_singleton s.v0))).subset ?_
    rintro v (h | h | h)
    · exact Or.inl (Ideal.dvd_span_singleton.2 h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨V, hV⟩ := hLev l L Ω s s.S hSfin subset_rfl s.split
  obtain ⟨π, π1, π2, π3, π4⟩ := UpperTheory.frame_criterion_projection k s a V hV
  have π5 : Function.Surjective π := fun x => by
    obtain ⟨g, rfl⟩ := k.surjective_levelChangeBaseGroupHom x
    exact ⟨_, π2 g⟩
  obtain ⟨κ, κ1, κ2, κ3⟩ := UpperTheory.frame_criterion_level_kernel k s a V hV c₁ ι n ka hka hkO
  have hκ : ∀ (g : G L Ω) (m : ℕ), ka g ^ m = 1 → κ (V.pr g) ^ m = 1 := fun g m h => by
    refine Units.ext (Subtype.ext ?_)
    rw [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, κ1, ← Units.val_pow_eq_pow_val, h]
    rfl
  have ok' : (Φ.ext f).Ok C₀ := Fr.ok_ext f ok
  obtain ⟨r, r1, r2⟩ := UpperTheory.frame_criterion_residual (Φ.ext f) V.frame n hn ok'.Ψ_open ok'.baseSubgroup_spec π π1 π5 π3 κ κ2 κ3
  have hAl : ∀ v : W.Vl l L, (s.A v).valuation (l : Ω) < 1 := fun v => (natCast_place (s.hA v) l).2 v.2
  choose lam hlam using fun v : W.Vl l L => UpperTheory.frame_criterion_lambda_characters k (a.e v) (s.A v) (a.A_pl v) (val_dvd _ hlM (hAl v))
  have hram : ∀ g ∈ V.frame.I0, κ g = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    simpa using hκ g 1 (by rw [pow_one]; exact hka.unr _ a.v0M g hg)
  have hext : ∀ x : Φ.Γ, Φ.Ψ x = 1 → (Φ.ext f).Ψ x = 1 := fun x hx => by
    show Units.map f.toMonoidHom (Φ.Ψ x) = 1
    rw [hx, map_one]
  have hD0 : ∀ g ∈ V.frame.D0, ∀ i, r.chib i g = W.pushCh (residue c₁.O) κ g := by
    rintro _ ⟨g, hg, rfl⟩ i
    have h1 : (Φ.ext f).Ψ (π (V.pr g)).1 = 1 := hext _ ((congrArg (fun x : Φ.G0 => Φ.Ψ x) (π2 g)).trans (a.v0Ψ g hg))
    exact (r1 i _).trans ((congrArg (fun x => x ^ Fr.w n i * W.pushCh (residue c₁.O) κ (V.pr g)) h1).trans (by simp))
  have hI : ∀ (v : W.Vl l L) (g : Dec (F := L) (s.A v)), lam v g ∈ Φ.Iv (a.e v) ↔ g.1 ∈ Ine (F := L) (s.A v) := fun v g => by
    rw [k.j_ine, hlam, ← a.A_pl]
    exact galEmb_mem_Ine _ _
  let K : TwLink (Φ.ext f) r :=
    { π := π, π_cont := π1, π_surj := π5, π_conj := π3, π_eps := π4
      e := a.e
      lam := lam
      lam_loc := fun v g => by
        refine Subtype.ext ?_
        show Φ.loc (a.e v) (lam v g) = (π (V.pr g.1)).1
        rw [π2, k.j_loc, k.galois_link_projection_coe]
        exact congrArg k.p (Subtype.ext (hlam v g))
      lam_I := fun v g => by
        exact hI v g
      κ := κ, κ_cont := κ2, κ_conj := κ3, chib := r1, psib := r2
      mu := fun v => by
        refine cr_mu (s.A v.1) (s.w v.1) (s.hw v.1) (hAl v) ?_
        obtain ⟨x, hx⟩ := k.mu (a.e v)
        obtain ⟨g, rfl⟩ := (lam v).surjective x
        refine ⟨g.1, g.2, fun h => hx (Units.ext ?_)⟩
        exact (congrArg (fun x => ((cycMod ℚ Ω l 1 x : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1))) (hlam v g)).trans ((toZMod_one_iff _).1 h)
      tame := by
        rintro u _ ⟨g, hg, rfl⟩
        obtain ⟨m, hm, hm'⟩ := hka.ord
        have hu : ¬ (s.A u.1).valuation (l : Ω) < 1 := fun h => s.St_l u.1 u.2 ((natCast_place (s.hA u.1) l).1 h)
        refine ⟨Nat.card (ResidueField c.O)ˣ * m, fun h => ?_, ?_, hκ g _ ?_⟩
        · refine hm ((hl.dvd_mul.1 h).resolve_left fun h' => ?_)
          haveI := Fintype.ofFinite (ResidueField c.O)
          rw [Nat.card_units, ← CharP.cast_eq_zero_iff (ResidueField c.O), Nat.cast_pred Nat.card_pos,
            Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero] at h'
          simp at h'
        · exact (congrArg (fun x : Φ.G0 => x ^ _) (π2 g)).trans (by rw [pow_mul, cr_tame k _ hu g hg, one_pow]; rfl)
        · rw [mul_comm, pow_mul, hm' _ hu g hg, one_pow]
      ramκ := hram
      ker := fun N h1 h2 h3 h4 h5 =>
        UpperTheory.frame_criterion_kernel k s a V hV π π2 N h1 h2 h3 (fun u g hg h => h4 u g hg (hext _ h)) h5 }
  have hv0 : r.V0ok := by
    refine ⟨fun i g hg => ?_, fun g hg i j => (hD0 g hg i).trans (hD0 g hg j).symm, ?_⟩
    · have hg' : g ∈ V.frame.D0 := Subgroup.map_mono (Ine_le_Dec _) hg
      rw [MonoidHom.mem_ker, hD0 g hg', MonoidHom.comp_apply, hram g hg, map_one]
    · obtain ⟨g, hg, h⟩ := a.v0ω
      refine ⟨V.pr g, ⟨g, hg, rfl⟩, fun h' => h ?_⟩
      have h1 : V.ε (V.pr g).1 = cycZ L Ω l g := DFunLike.congr_fun V.hε (W.resP L Ω g)
      have h2 : ((algebraMap c₁.O (ResidueField c₁.O)).comp (algebraMap ℤ_[l] c₁.O)) (V.ε (V.pr g).1 : ℤ_[l]) = 1 :=
        congrArg Units.val h'
      rw [h1, ← map_one ((algebraMap c₁.O (ResidueField c₁.O)).comp (algebraMap ℤ_[l] c₁.O)),
        ← RingHom.sub_mem_ker_iff] at h2
      rw [← map_one (PadicInt.toZMod (p := l)), ← RingHom.sub_mem_ker_iff, PadicInt.ker_toZMod]
      exact le_maximalIdeal (RingHom.ker_ne_top _) h2
  haveI : IsCO c₁.O (ResidueField c₁.O) := (co_res c₁.O).1
  obtain ⟨p, -⟩ := W.residual_diagonal_determinant_isPolar l V.frame c₁.O n r (by omega) (UpperTheory.residual_ok_of_local_chars_restrict r (by omega) r2)
  obtain ⟨B₀⟩ := hB0 l L Ω s V c₁ n r _ ⟨p⟩
  obtain ⟨S⟩ := Fr.space_ex ok' hn
  exact ⟨⟨hn, C₀, ok', big, hle, hf, s, V, hV, r, K, π2, κ1, hlam, a.A_pl, hv0, a.v0M, B₀, S⟩⟩
