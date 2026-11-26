module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwIwQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LamFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.EqOnTors
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.HeckePolCoeff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ClParts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  have h1 := s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)
  have h2 := s.hA v x
  exact h1.symm.trans h2

private theorem l_notMem {l : ℕ} {L : Type} [Field L] [NumberField L] [IsCMField L] {w u : Plc L}
    (h : ((l : ℕ) : 𝓞 (Lp L)) ∉ (w.under (𝓞 (Lp L))).asIdeal) (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    ((l : ℕ) : 𝓞 L) ∉ u.asIdeal := fun h' => h <| by
  rw [← hu]
  change algebraMap (𝓞 (Lp L)) (𝓞 L) (l : 𝓞 (Lp L)) ∈ u.asIdeal
  rwa [map_natCast]

private theorem cmp_of {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) : cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dite_eq_left h]
  rfl

private theorem cmp_loc {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w u : Plc L}
    {x : UA L n} (hx : x ∈ locU n w) (hu : u.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) :
    cmp n u ((away l L n).rangeRestrict x) = 1 := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ u.asIdeal
  · rw [cmp_of h]
    exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu)
  · unfold CaseU.cmp
    rw [dite_eq_right h]
    rfl

private theorem cLoc_conj {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w u : Plc L} (hw : IsSplitAt w)
    (x : UA L n) (h1 : cLoc w x = 1) (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) : cLoc u x = 1 := by
  have hw1 : ∀ v, v = w → cLoc v x = 1 := by
    rintro v rfl
    exact h1
  rcases (GlobalTheory.SplitPts.over_split hw).2.2 u hu with rfl | rfl
  · exact h1
  · have hce := GlobalTheory.SplitPts.comp_eq x (conjSrc (GlobalTheory.SplitPts.conjE L) w)
    rw [hw1 _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w), Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one, Matrix.one_mul] at hce
    exact Units.ext hce

theorem UpperTheory.V.Hi.secU :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ w : Plc L, IsSplitAt w → (∃ j : GLw n w →* UA L n, (∀ g, j g ∈ locU n w) ∧ (∀ g, cLoc w (j g) = g) ∧ Continuous j ∧ ∀ x ∈ locU n w, x = j (cLoc w x)) ∧ (w.under (𝓞 (Lp L)) ∉ s.S → Function.Bijective (((cmp n w).comp (Ub n s).subtype).comp (locA n s w).subtype) ∧ (∀ g, cmp n w ((sec n s w g : Ub n s) : Ga l L n) = g) ∧ ∀ g, sec n s w g ∈ locA n s w) := by
  intro l _ L Ω _ _ _ _ _ _ s n _ w hw
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL L n w hw
  have hs : ∀ y, cLoc w (e.symm y : UA L n) = y := fun y => by
    rw [← he, e.apply_symm_apply]
  refine ⟨⟨(locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom, fun g => (e.symm g).2, hs,
    continuous_subtype_val.comp e.symm.continuous, fun x hx => ?_⟩, fun hS => ?_⟩
  · have h1 := he ⟨x, hx⟩
    change x = (e.symm (cLoc w x) : UA L n)
    rw [← h1, e.symm_apply_apply]
  have hl : ((l : ℕ) : 𝓞 (Lp L)) ∉ (w.under (𝓞 (Lp L))).asIdeal := fun h => hS (Or.inl h)
  have hb : Function.Bijective (((cmp n w).comp (Ub n s).subtype).comp (locA n s w).subtype) := by
    refine ⟨(injective_iff_map_eq_one _).2 ?_, fun y => ?_⟩
    · rintro ⟨⟨g, hg⟩, hA⟩ h1
      obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective g
      have h2 : cLoc w x = 1 := (cmp_of (l_notMem hl rfl) x).symm.trans h1
      refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun u => ?_)))
      change cLoc u.1 x = 1
      by_cases hu : u.1.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · exact cLoc_conj hw x h2 hu
      · exact (cmp_of u.2 x).symm.trans
          (MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hA u.1) hu))
    · have hU : (away l L n).rangeRestrict (e.symm y : UA L n) ∈ Ub n s := by
        refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun u => ?_, ?_⟩
        · rw [Subgroup.mem_comap, cmp_loc (e.symm y).2 (by
            rw [w_under]
            exact fun h => hS (Or.inr (Or.inl (h ▸ u.2))))]
          exact one_mem _
        · rw [Subgroup.mem_comap, cmp_loc (e.symm y).2 (by
            rw [w_under]
            exact fun h => hS (Or.inr (Or.inr h.symm)))]
          exact one_mem _
      refine ⟨⟨⟨_, hU⟩, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu =>
        MonoidHom.mem_ker.2 (cmp_loc (e.symm y).2 hu)⟩, ?_⟩
      exact (cmp_of (l_notMem hl rfl) _).trans (hs y)
  refine ⟨hb, fun g => ?_, fun g => ?_⟩
  · unfold CaseU.sec
    rw [dite_eq_left hb]
    exact (MulEquiv.ofBijective _ hb).apply_symm_apply g
  · unfold CaseU.sec
    rw [dite_eq_left hb]
    exact ((MulEquiv.ofBijective _ hb).symm g).2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2MemSpan
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem UpperTheory.V.Hi.partUR2Mem_span {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ}
    {V : s.Lev} (ι : Qbar l ≃+* ℂ) (m : ℕ)
    {lam : Wt L l n} {d : ℕ} (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (σ : Submodule ℂ (UA L n → ℂ))
    (F : Fin m → (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ))
    (h : F ∈ Submodule.span ℂ {F : Fin m → (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) | ∀ i ℓ, toForm ι e (F i) ℓ ∈ σ}) :
    ∀ i ℓ, toForm ι e (F i) ℓ ∈ σ := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    intro i ℓ
    have : toForm ι e ((0 : Fin m → (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ)) i) ℓ = 0 := by
      funext g
      simp only [toForm, Pi.zero_apply, map_zero]
    rw [this]; exact σ.zero_mem
  | add x y _ _ hx hy =>
    intro i ℓ
    have : toForm ι e ((x + y) i) ℓ = toForm ι e (x i) ℓ + toForm ι e (y i) ℓ := by
      funext g
      simp only [toForm, Pi.add_apply, map_add (f := _)]
    rw [this]; exact σ.add_mem (hx i ℓ) (hy i ℓ)
  | smul a x _ hx =>
    intro i ℓ
    have : toForm ι e ((a • x) i) ℓ = a • toForm ι e (x i) ℓ := by
      funext g
      simp only [toForm, Pi.smul_apply, map_smul]
    rw [this]; exact σ.smul_mem a (hx i ℓ)

theorem UpperTheory.V.Hi.partUR2Mem :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (σ : Submodule ℂ (UA L n → ℂ)) (F : Fin m → (hset Q τ₀).X.Fn ℂ d),
    F ∈ YOf Q ι τ₀ e ξ σ ↔ F ∈ (hset Q τ₀).Big ι ξ ∧ ∀ i ℓ, toForm ι e (F i) ℓ ∈ σ := by
  intro l _ L Ω _ _ _ _ _ _ s n _ V Q c ι m τ₀ lam d e ξ σ F
  constructor
  · intro h
    exact ⟨h.1, UpperTheory.V.Hi.partUR2Mem_span ι m e σ F h.2⟩
  · intro h
    exact ⟨h.1, Submodule.subset_span h.2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.NonemptyUnitaryHeckeParts
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ProjectiveTransportAlongEquiv
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem UpperTheory.V.Hi.projective_transport_along_equiv {Λ₀ Λ V₀ V Q : Type} [CommRing Λ₀] [CommRing Λ] [AddCommGroup V₀] [AddCommGroup V]
    [Module Λ₀ V₀] [Module Λ V] [Group Q] (e : Λ₀ ≃+* Λ) (φ : V ≃+ V₀) (hφ : ∀ a v, φ (e a • v) = a • φ v)
    (ρ' : Representation Λ Q V) (hP : Module.Projective (MonoidAlgebra Λ Q) ρ'.asModule) :
    ∃ ρ'' : Representation Λ₀ Q V₀, (∀ q v, ρ'' q v = φ (ρ' q (φ.symm v))) ∧
      Module.Projective (MonoidAlgebra Λ₀ Q) ρ''.asModule := by
  have hφ' : ∀ (a : Λ₀) v, φ.symm (a • v) = e a • φ.symm v := fun a v => by
    apply φ.injective
    rw [hφ, φ.apply_symm_apply, φ.apply_symm_apply]
  let ρ'' : Representation Λ₀ Q V₀ :=
    { toFun := fun q =>
        { toFun := fun v => φ (ρ' q (φ.symm v))
          map_add' := fun x y => by simp only [map_add (f := _)]
          map_smul' := fun a v => by rw [hφ', map_smul, hφ]; rfl }
      map_one' := by ext v; simp
      map_mul' := fun g h => by ext v; simp }
  refine ⟨ρ'', fun _ _ => rfl, ?_⟩
  let E : MonoidAlgebra Λ Q ≃+* MonoidAlgebra Λ₀ Q := MonoidAlgebra.mapRingEquiv Q e.symm
  haveI := RingHomInvPair.of_ringEquiv E
  haveI := RingHomInvPair.of_ringEquiv_symm E
  let ψ : ρ'.asModule ≃+ ρ''.asModule :=
    (ρ'.asModuleEquiv.toAddEquiv.trans φ).trans ρ''.asModuleEquiv.symm.toAddEquiv
  have hψ : ∀ (r : MonoidAlgebra Λ Q) (x : ρ'.asModule), ψ (r • x) = E r • ψ x := by
    intro r x
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [add_smul, map_add (f := _), map_add (f := _), add_smul, ha, hb]
    | single g a =>
      have hE : E (MonoidAlgebra.single g a) = MonoidAlgebra.single g (e.symm a) := by
        simp [E]
      rw [hE, Representation.single_smul, Representation.single_smul]
      change φ (a • ρ' g (ρ'.asModuleEquiv x)) = e.symm a • φ (ρ' g (φ.symm (φ (ρ'.asModuleEquiv x))))
      rw [φ.symm_apply_apply, ← hφ, e.apply_symm_apply]
  let Ψ : ρ'.asModule ≃ₛₗ[(E : MonoidAlgebra Λ Q →+* MonoidAlgebra Λ₀ Q)] ρ''.asModule :=
    { ψ with map_smul' := hψ }
  exact Module.Projective.of_equiv Ψ

theorem UpperTheory.V.Hi.levelUR2ProjTr :
    ∀ (Λ₀ Λ R P G : Type) [CommRing Λ₀] [CommRing Λ] [CommRing R] [Algebra Λ₀ R] [AddCommGroup P] [Module R P] [Module Λ₀ P] [IsScalarTower Λ₀ R P] [Module Λ P] [Group G] (e : Λ₀ ≃+* Λ), (∀ (a : Λ₀) (p : P), a • p = e a • p) → ∀ (ρ : Representation Λ G P) (ρR : Representation R G P), (∀ g p, ρR g p = ρ g p) → ∀ (U U₁ : Subgroup G) [(U₁.subgroupOf U).Normal], (Module.Finite Λ (fixd ρ U₁) → Module.Finite Λ₀ (fixd ρR U₁)) ∧ ∀ ρ' : Representation Λ (U ⧸ U₁.subgroupOf U) (fixd ρ U₁), (∀ (u : U) f, (ρ' (u : U ⧸ U₁.subgroupOf U) f).1 = ρ u f) → Module.Projective (MonoidAlgebra Λ (U ⧸ U₁.subgroupOf U)) ρ'.asModule → ∃ ρ'' : Representation Λ₀ (U ⧸ U₁.subgroupOf U) (fixd ρR U₁), (∀ (u : U) f, (ρ'' (u : U ⧸ U₁.subgroupOf U) f : P) = ρR u f) ∧ Module.Projective (MonoidAlgebra Λ₀ (U ⧸ U₁.subgroupOf U)) ρ''.asModule := by
  intro Λ₀ Λ R P G _ _ _ _ _ _ _ _ _ _ e he ρ ρR hρ U U₁ _
  have hmem : ∀ p : P, p ∈ fixd ρ U₁ ↔ p ∈ fixd ρR U₁ := fun p =>
    forall_congr' fun u => forall_congr' fun _ => by rw [hρ]
  let φ : fixd ρ U₁ ≃+ fixd ρR U₁ :=
    { toFun := fun v => ⟨v.1, (hmem _).1 v.2⟩
      invFun := fun v => ⟨v.1, (hmem _).2 v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hφ : ∀ (a : Λ₀) v, φ (e a • v) = a • φ v := fun a v => Subtype.ext (he a v.1).symm
  refine ⟨fun hfin => ?_, fun ρ' h' hP => ?_⟩
  · let f : fixd ρ U₁ →ₛₗ[(e.symm : Λ →+* Λ₀)] fixd ρR U₁ :=
      { toFun := φ
        map_add' := φ.map_add
        map_smul' := fun a v => by
          rw [← hφ]
          simp }
    haveI : RingHomSurjective (e.symm : Λ →+* Λ₀) := ⟨e.symm.surjective⟩
    exact Module.Finite.of_surjective f φ.surjective
  · obtain ⟨ρ'', h1, h2⟩ := UpperTheory.V.Hi.projective_transport_along_equiv e φ hφ ρ' hP
    refine ⟨ρ'', fun u f => ?_, h2⟩
    rw [h1, hρ]
    exact h' u (φ.symm f)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem UpperTheory.V.Hi.module_structure_of_commuting {A R P G : Type} [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] [Group G]
    (ρ : Representation A G P) (α : R →+* Module.End A P) (hc : ∀ t g z, α t (ρ g z) = ρ g (α t z)) :
    ∃ (_ : Module R P) (ρR : Representation R G P), (∀ (t : R) (z : P), t • z = α t z) ∧ ∀ g z, ρR g z = ρ g z := by
  letI : Module R P := Module.compHom P α
  have hs : ∀ (t : R) (z : P), t • z = α t z := fun _ _ => rfl
  refine ⟨inferInstance,
    { toFun := fun g =>
        { toFun := fun z => ρ g z
          map_add' := fun x y => map_add _ x y
          map_smul' := fun t z => by rw [hs, RingHom.id_apply, hs, hc] }
      map_one' := by ext z; simp
      map_mul' := fun g h => by ext z; simp }, hs, fun _ _ => rfl⟩

theorem UpperTheory.V.Hi.levelUR2ModPack :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V₀ : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V₀.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : Pa.TWBase (Pa.pairOf B.u) J Empty D) (V : s.Lev) (h : (Pa.globOf r V).Hom (Pa.globOf r V₀)) (q : ℕ) (w : Fin q → Plc L) (rN : Resid (Pa.globOf r V).frame O n), Pa.Glob.Compat h rN (Pa.residOf r) → ∀ (R : Type) [CommRing R] [Algebra O R] [Alg.IsCO O R] (p : Pair rN R) (A : Type) [CommRing A] [Algebra O A] (e : Pa.abelian₂ O Empty D ≃ₐ[O] A) (lam : A →ₐ[O] R), (∀ k, lam (e (MvPowerSeries.X (.inr k))) = algebraMap O R (b.wt.c k) * (p.ψ (b.wt.v k) (b.wt.i k) (b.wt.γ k) : R) - 1) → ∀ β : R →ₐ[O] B.B, p.Maps β.toRingHom ((Pa.pairOf B.u).D.comap h.p₀) (Pa.pairOf B.u).ψ → ∀ (P : Type) [AddCommGroup P] [Module A P] (ρ : Representation A (GV n w) P) (α : R →+* Module.End A P), (∀ a z, α (lam a) z = a • z) → (∀ t g z, α t (ρ g z) = ρ g (α t z)) → Module.Finite A (fixd ρ (Pa.UIw1 l n w)) → ∀ [((Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)).Normal] (ρ' : Representation A (Pa.UIw n w ⧸ (Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)) (fixd ρ (Pa.UIw1 l n w))), (∀ (u : Pa.UIw n w) f, (ρ' (u : Pa.UIw n w ⧸ (Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)) f).1 = ρ u f) → Module.Projective (MonoidAlgebra A (Pa.UIw n w ⧸ (Pa.UIw1 l n w).subgroupOf (Pa.UIw n w))) ρ'.asModule → ∀ eM : fixd ρ (Pa.UK n w) ≃+ b.M, (∀ (t : R) (m m' : fixd ρ (Pa.UK n w)), (m' : P) = α t m → eM m' = β t • eM m) → ∀ ι : Qbar l ≃+* ℂ, (∀ z : P, z ≠ 0 → ∃ (x : R →+* Qbar l) (ρx : (Pa.globOf r V).G₀ →* GL (Fin n) (Qbar l)) (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (π : Representation ℂ (GV n w) Y) (sp : P →+ Y) (σ : ∀ j, SmIrr (GLw n (w j))), sp z ≠ 0 ∧ Continuous ρx ∧ p.D.map x = W.GDet.ofRep (W.mat ρx) ∧ (∀ t y, sp (α t y) = ι (x t) • sp y) ∧ (∀ g y, sp (ρ g y) = π g (sp y)) ∧ (∀ j, IsoSum (π.comp (Pa.atJ n w j)) ⊤ (σ j)) ∧ ∀ j (Bq : ValuationSubring Ω) (hB : IsPlaceOver Bq (w j)) (rc : IrrGL (k := (w j).adicCompletion L) → WD hB), IsRec hB rc → UpperTheory.V.Lev.WO ι (ρx.comp V.pr) (rc (algNorm (σ j)))) → ∃ M : Pa.LevMod b h w, M.Classical := by
  intro l _ L Ω _ _ _ _ _ _ s V₀ O _ _ _ n r B J D b V h q w rN hcomp R _ _ _ p A _ _ e lam hlam β hβ P _ _ ρ α hα hc hfin
    hN ρ' hρ' hproj eM heM ι hcl
  obtain ⟨modR, ρR, hs, hρR⟩ := UpperTheory.V.Hi.module_structure_of_commuting ρ α hc
  letI algL : Algebra (Pa.abelian₂ O Empty D) R := (lam.toRingHom.comp e.toRingEquiv.toRingHom).toAlgebra
  have halg : ∀ a : Pa.abelian₂ O Empty D, algebraMap (Pa.abelian₂ O Empty D) R a = lam (e a) := fun _ => rfl
  haveI towO : IsScalarTower O (Pa.abelian₂ O Empty D) R := IsScalarTower.of_algebraMap_eq fun x => by
    rw [halg, e.commutes, lam.commutes]
  letI modL : Module (Pa.abelian₂ O Empty D) P := Module.compHom P e.toRingEquiv.toRingHom
  have hL : ∀ (a : Pa.abelian₂ O Empty D) (z : P), a • z = e.toRingEquiv a • z := fun _ _ => rfl
  haveI tow : IsScalarTower (Pa.abelian₂ O Empty D) R P := ⟨fun a t z => by
    rw [Algebra.smul_def, halg, mul_smul, hs, hα, hL]; rfl⟩
  obtain ⟨hF, hP⟩ := UpperTheory.V.Hi.levelUR2ProjTr (Pa.abelian₂ O Empty D) A R P (GV n w) e.toRingEquiv hL ρ ρR hρR
    (Pa.UIw n w) (Pa.UIw1 l n w)
  obtain ⟨ρ'', h1, h2⟩ := hP ρ' hρ' hproj
  have hmem : ∀ z : P, z ∈ fixd ρR (Pa.UK n w) ↔ z ∈ fixd ρ (Pa.UK n w) := fun z =>
    forall_congr' fun u => forall_congr' fun _ => by rw [hρR]
  let φ : fixd ρR (Pa.UK n w) ≃+ fixd ρ (Pa.UK n w) :=
    { toFun := fun v => ⟨v.1, (hmem _).1 v.2⟩
      invFun := fun v => ⟨v.1, (hmem _).2 v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let M : Pa.LevMod b h w :=
    { rN := rN
      compat := hcomp
      R := R
      p := p
      segmentWeightExponent := fun k => (halg _).trans (hlam k)
      β := β
      β_pair := hβ
      P := P
      ρ := ρR
      fin := hF hfin
      proj := ⟨hN, ρ'', h1, h2⟩
      eM := φ.trans eM
      eM_smul := fun t m => heM t (φ m) (φ (t • m)) (hs t m.1) }
  refine ⟨M, ι, fun m hm => ?_⟩
  by_contra h0
  obtain ⟨x, ρx, Y, iY, mY, π, sp, σ, hne, hcont, hdet, hsm, hact, hiso, hlg⟩ := hcl m h0
  exact hne (hm
    { θ := x
      rep := ρx
      cont := hcont
      det := hdet
      Y := Y
      π := π
      sp := sp
      sp_smul := fun t y => (congrArg sp (hs t y)).trans (hsm t y)
      sp_act := fun g y => (congrArg sp (hρR g y)).trans (hact g y)
      σ := σ
      iso := hiso
      lg := hlg })
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2BaseAct
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2BaseAct :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) (K : H.Lev) (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (lam : A →ₐ[c.O] R) (J : Ideal R), H.IsJ θ a K D₀ ψ₀ lam J → ∃ μ : R →+* Module.End A (H.MK θ a K), (∀ b y, μ (lam b) y = b • y) ∧ RingHom.ker μ = J ∧ (H.MK θ a K = ⊥ ∨ ∃ (_ : Fact (CommOn (H.MK θ a K) (H.op A))) (_ : Alg.IsCO c.O (H.TK θ a K)) (f : R →ₐ[c.O] H.TK θ a K), H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K))) := by
  intro L Ω _ _ _ _ _ l _ n c H _ A _ _ _ θ _ a K R _ _ D₀ ψ₀ lam J hJ
  rcases hJ with ⟨h0, hJ⟩ | ⟨x, x1, f, hne, hmap, hsurj, hlam, hker⟩
  · haveI : Subsingleton (H.MK θ a K) := by
      rw [h0]
      infer_instance
    haveI : Subsingleton (Module.End A (H.MK θ a K)) := inferInstance
    let μ : R →+* Module.End A (H.MK θ a K) :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := rfl
        map_add' := fun _ _ => Subsingleton.elim _ _ }
    refine ⟨μ, ?_, ?_, Or.inl h0⟩
    · intro b y
      exact Subsingleton.elim _ _
    · rw [hJ]
      ext t
      simp only [RingHom.mem_ker, Submodule.mem_top, iff_true]
      exact Subsingleton.elim _ _
  · refine ⟨(UpperTheory.V.Hi.heckeAlg (H.MK θ a K) (H.op A)).val.toRingHom.comp f.toRingHom, ?_, ?_, Or.inr ⟨x, x1, f, hmap, fun t => rfl⟩⟩
    · intro b y
      have h := hlam b
      show ((f (lam b) : Module.End A (H.MK θ a K))) y = b • y
      rw [h]
      rfl
    · rw [hker]
      ext t
      simp only [RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      constructor
      · intro ht
        exact Subtype.ext ht
      · intro ht
        rw [ht]
        rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2IwLev
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section Loc
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
  (C : Subgroup 𝓀[k]ˣ)

private theorem iwLev_loc : IsOpen (AlgebraTools.iwC k n C : Set (GL (Fin n) k)) ∧ IsCompact (AlgebraTools.iwC k n C : Set (GL (Fin n) k)) ∧
    AlgebraTools.iwC k n C ≤ AlgebraTools.iwC k n ⊤ := by
  have h1 := (AlgebraTools.memIwC k n C).1
  have h2 := (AlgebraTools.memIwC k n C).2.1
  have hle : AlgebraTools.iwC k n C ≤ AlgebraTools.iwC k n ⊤ := by
    intro g hg
    rw [h2]
    exact ((h1 g).1 hg).1
  have hopen : IsOpen (AlgebraTools.iwC k n C : Set (GL (Fin n) k)) :=
    Subgroup.isOpen_mono (show KOne k (Fin n) ≤ AlgebraTools.iwC k n C from le_sup_left.trans le_sup_left)
      GlobalTheory.StepData.isOpen_KOne
  refine ⟨hopen, ?_, hle⟩
  refine IsCompact.of_isClosed_subset GlobalTheory.SplitFlip.isCompact_KO (Subgroup.isClosed_of_isOpen _ hopen) ?_
  intro g hg
  exact GlobalTheory.SmGL.iwahori_le_KO k (Fin n) ((h1 g).1 hg).1

private theorem iwLev_conj {x g : GL (Fin n) k} (hx : x ∈ AlgebraTools.iwC k n C) (hg : g ∈ AlgebraTools.iwC k n ⊤) :
    g * x * g⁻¹ ∈ AlgebraTools.iwC k n C := by
  have h2 := (AlgebraTools.memIwC k n C).2.1
  have h3 := (AlgebraTools.memIwC k n C).2.2.1
  rw [h2] at hg
  exact h3 g hg x hx

end Loc

theorem UpperTheory.V.Hi.levelUR2IwLev :
    ∀ (l : ℕ) (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L), (∀ j C, IsOpen (AlgebraTools.iwC ((w j).adicCompletion L) n C : Set (GLw n (w j))) ∧ IsCompact (AlgebraTools.iwC ((w j).adicCompletion L) n C : Set (GLw n (w j))) ∧ AlgebraTools.iwC ((w j).adicCompletion L) n C ≤ AlgebraTools.iwC ((w j).adicCompletion L) n ⊤) ∧ ((Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)).Normal := by
  intro l L _ _ n q w
  refine ⟨fun j C => iwLev_loc _ n C, ?_⟩
  have hle : Pa.UIw1 l n w ≤ Pa.UIw n w := by
    intro g hg
    simp only [Pa.UIw, Pa.UIw1, Subgroup.mem_pi] at hg ⊢
    intro j hj
    exact (iwLev_loc _ n _).2.2 (hg j hj)
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro h g hh hg
  simp only [Pa.UIw, Pa.UIw1, Subgroup.mem_pi] at hh hg ⊢
  intro j hj
  exact iwLev_conj _ n _ (hh j hj) (hg j hj)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WeightVariablesExist
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem weight_variables_exist (l : ℕ) [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (n : ℕ)
    (r : Resid F O n) (d : F.Vl → ℕ) (A : ∀ v, W.LocAb l (F.Gv v) (F.Iv v) (d v)) (Λ : LamObj r) (D : ℕ)
    (hD : ∑ v, d v = D) :
    ∃ (v : Fin (n * D) → F.Vl) (i : Fin (n * D) → Fin n) (γ : ∀ k, F.Gv (v k)) (c : Fin (n * D) → O)
      (e : MvPowerSeries (Empty ⊕ Fin (n * D)) O ≃ₐ[O] Λ.Λ), ∀ k, ∃ hγ : γ k ∈ F.Iv (v k),
      residue O (c k) * (r.psib (v k) (i k) (γ k) : ResidueField O) = 1 ∧
      e (MvPowerSeries.X (.inr k)) = algebraMap O Λ.Λ (c k) * (Λ.κ (v k) (i k) ⟨γ k, hγ⟩ : Λ.Λˣ) - 1 := by
  obtain ⟨e, ψ₀, hψ₀, he⟩ := (W.lam_ex_free l F O n r d A).2 Λ
  have hc : Fintype.card (Σ v : F.Vl, Fin n × Fin (d v)) = n * D := by
    rw [Fintype.card_sigma, ← hD, Finset.mul_sum]
    simp
  let ε : Fin (n * D) ≃ (Σ v : F.Vl, Fin n × Fin (d v)) := (Fintype.equivFinOfCardEq hc).symm
  choose g hgI hg using fun (v : F.Vl) (j : Fin (d v)) => ((A v).inertia (Pi.single j 1, 0)).2 rfl
  let ε' : Empty ⊕ Fin (n * D) ≃ (Σ v : F.Vl, Fin n × Fin (d v)) :=
    (@Equiv.emptySum Empty (Fin (n * D)) ⟨Empty.elim⟩).trans ε
  refine ⟨fun k => (ε k).1, fun k => (ε k).2.1, fun k => g (ε k).1 (ε k).2.2,
    fun k => ((ψ₀ (ε k).1 (ε k).2.1 (g (ε k).1 (ε k).2.2))⁻¹ : Oˣ),
    (MvPowerSeries.renameEquiv O ε').trans e, fun k => ⟨hgI _ _, ?_, ?_⟩⟩
  · have h1 := (hψ₀ (ε k).1 (ε k).2.1).red (g (ε k).1 (ε k).2.2)
    have h2 : ∀ x : O, Alg.res O O x = residue O x := fun x => (Alg.res O O).commutes x
    rw [h2] at h1
    show residue O _ * ((r.psib (ε k).1 (ε k).2.1 (g (ε k).1 (ε k).2.2) : (ResidueField O)ˣ) : ResidueField O) = 1
    rw [← h1, ← map_mul, Units.inv_mul, map_one]
  · have h1 := he (ε k).1 (ε k).2.1 (ε k).2.2 ⟨g (ε k).1 (ε k).2.2, hgI _ _⟩ (hg _ _)
    have h2 : MvPowerSeries.renameEquiv O ε' (MvPowerSeries.X (.inr k)) = MvPowerSeries.X (ε k) := by
      exact MvPowerSeries.rename_X _ _
    show e (MvPowerSeries.renameEquiv O ε' (MvPowerSeries.X (.inr k))) =
      algebraMap O Λ.Λ ((ψ₀ (ε k).1 (ε k).2.1 (g (ε k).1 (ε k).2.2))⁻¹ : Oˣ) *
        ((Λ.κ (ε k).1 (ε k).2.1 ⟨g (ε k).1 (ε k).2.2, hgI _ _⟩ : Λ.Λˣ) : Λ.Λ) - 1
    rw [h1, h2, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul, add_sub_cancel_left]

theorem UpperTheory.V.Hi.levelUR2WtVars :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (c : Coef l) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r), Pa.LocCFT s → ∃ (wt : Pa.WtVars (Pa.locOf r) c.O n (n * Module.finrank ℚ (Lp L))) (e : Pa.abelian₂ c.O Empty (n * Module.finrank ℚ (Lp L)) ≃ₐ[c.O] Λ.Λ), ∀ k, ∃ hγ : wt.γ k ∈ V.frame.Iv (wt.v k), residue c.O (wt.c k) * (r.psib (wt.v k) (wt.i k) (wt.γ k) : ResidueField c.O) = 1 ∧ e (MvPowerSeries.X (.inr k)) = algebraMap c.O Λ.Λ (wt.c k) * (Λ.κ (wt.v k) (wt.i k) ⟨wt.γ k, hγ⟩ : Λ.Λˣ) - 1 := by
  intro l hl L Ω _ _ _ _ _ _ s n V c r _ Λ h
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField ℤ_[l]) l :=
    charP_of_injective_ringHom (f := (PadicInt.residueField (p := l)).symm.toRingHom)
      (PadicInt.residueField (p := l)).symm.injective l
  haveI : CharP (ResidueField c.O) l :=
    charP_of_injective_ringHom (algebraMap (ResidueField ℤ_[l]) (ResidueField c.O)).injective l
  obtain ⟨d₀, hd, hA⟩ := h
  let d : V.frame.Vl → ℕ := d₀
  have hsum : ∑ v : V.frame.Vl, d v = Module.finrank ℚ (Lp L) :=
    (finsum_eq_sum_of_fintype (α := V.frame.Vl) d).symm.trans hd
  obtain ⟨v, i, γ, cc, e, H⟩ := weight_variables_exist l V.frame c.O n r d (fun v => (hA v).some) Λ _ hsum
  exact ⟨⟨v, i, γ, cc⟩, e, H⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2BasePack
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2BasePack :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V₀ : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V₀.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (wt : Pa.WtVars (Pa.locOf r) O n D) (A : Type) [CommRing A] [Algebra O A] (e : Pa.abelian₂ O Empty D ≃ₐ[O] A) (lam : A →ₐ[O] B.B), (∀ k, residue O (wt.c k) * (r.psib (wt.v k) (wt.i k) (wt.γ k) : ResidueField O) = 1) → (∀ k, lam (e (MvPowerSeries.X (.inr k))) = algebraMap O B.B (wt.c k) * (B.u.ψ (wt.v k) (wt.i k) (wt.γ k) : B.B) - 1) → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Free A M] (μ : B.B →+* Module.End A M), (∀ a y, μ (lam a) y = a • y) → RingHom.ker μ = J → ∃ (b : Pa.TWBase (Pa.pairOf B.u) J Empty D) (eb : M ≃+ b.M), b.wt = wt ∧ ∀ t y, eb (μ t y) = t • eb y := by
  intro l _ L Ω _ _ _ _ _ _ s V₀ O _ _ _ n r B J D wt A _ _ e lam hres hlam M _ _ _ _ μ hμ hker
  letI mB : Module B.B M := Module.compHom M μ
  letI mL : Module (Pa.abelian₂ O Empty D) M := Module.compHom M (e : Pa.abelian₂ O Empty D →+* A)
  have hsm : ∀ (a : Pa.abelian₂ O Empty D) (m : M), a • m = (lam.comp e.toAlgHom) a • m := by
    intro a m
    exact (hμ (e a) m).symm
  haveI : Nontrivial A := e.injective.nontrivial
  let bL := (Module.Free.chooseBasis A M).mapCoeffs e.symm.toRingEquiv (fun c x => by
    show e (e.symm c) • x = c • x
    rw [AlgEquiv.apply_symm_apply])
  haveI : Module.Free (Pa.abelian₂ O Empty D) M := Module.Free.of_basis bL
  haveI : Module.Finite (Pa.abelian₂ O Empty D) M := Module.Finite.of_basis bL
  have hann : Module.annihilator B.B M = J := by
    rw [← hker]
    ext b
    rw [Module.mem_annihilator, RingHom.mem_ker]
    constructor
    · intro hb
      ext m
      exact hb m
    · intro hb m
      show μ b m = 0
      rw [hb]
      rfl
  exact ⟨Pa.TWBase.mk wt hres (lam.comp e.toAlgHom) (fun k => hlam k) M hsm inferInstance inferInstance
    (fun p _ => by rw [hann]), AddEquiv.refl M, rfl, fun t y => rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HeckeDeterminantReductionEqResidual
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.heckeDeterminant_reduction_eq_residual :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (Λ : LamObj r) (R : HD Q ι Λ), (hset Q R.τ₀).Ax →
    ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (gen : (hset Q R.τ₀).Op → T), (∀ i, gen i - algebraMap c.O T (R.a i) ∈ maximalIdeal T) →
    ∀ D : W.GDet n T V.frame.G₀, D.IsCont (maximalIdeal T) →
    (∀ (w : (hset Q R.τ₀).Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ →
      D.chi (MonoidAlgebra.single (V.pr σ⁻¹) 1) = heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) →
    D.map (Alg.res c.O T : T →+* ResidueField c.O) = r.Dbar := by
  intro l _ L Ω _ _ _ _ _ _ s n V Q c r ι Λ R hA T _ _ _ gen hgen D hD hF
  refine JEx.red_eq r D hD _ hA.dense ?_
  rintro g ⟨w, hw, B, σ, hB, hσ, rfl⟩
  have h1 := hF ⟨w, hw⟩ B σ hB hσ
  have h2 := R.res.frob ⟨w, hw⟩ B σ hB hσ
  refine (congrArg (Polynomial.map _) h1).trans (Eq.trans ?_ h2.symm)
  rw [JEx.heckePol_map]
  congr 1
  funext j
  split_ifs with h
  · have h3 := (Alg.res_eq_zero_iff c.O T _).2 (hgen (.inl (⟨w, hw⟩, ⟨j - 1, h.2⟩)))
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at h3
    exact h3
  · exact map_one _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HeckeDeterminantSatisfiesDeformationRelations
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.heckeDeterminant_satisfies_deformation_relations :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (T : Type) [CommRing T] [Algebra c.O T] (D : W.GDet n T V.frame.G₀) (ψ : ∀ v : V.frame.Vl, Fin n → V.frame.Gv v →* Tˣ) (Gd : (T →ₐ[c.O] Qbar l) → Prop),
    (∀ t : T, (∀ x, Gd x → x t = 0) → t = 0) →
    (∀ x, Gd x → ∃ ρ : V.frame.G₀ →* GL (Fin n) (Qbar l), PU r ι lam ρ ∧ D.map x.toRingHom = W.GDet.ofRep (W.mat ρ) ∧ ∀ v, W.HasFlag (ρ.comp (V.frame.φ v)) fun i => W.pushCh x.toRingHom (ψ v i)) →
    (∀ i g, D.lam i (V.frame.star c.O T n (MonoidAlgebra.single g 1)) = D.lam i (MonoidAlgebra.single g 1)) ∧
    (∀ v (g : Fin n → V.frame.Gv v) (h : V.frame.G₀), D.tr (MonoidAlgebra.single h 1 * V.frame.oEl v (ψ v) g) = 0) ∧
    ∀ u, ∀ g ∈ r.Ip u, ∀ h : V.frame.G₀, D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) = 0 := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V c r ι lam T _ _ D ψ Gd hsep hex
  choose ρ hPU hD hfl using hex
  obtain ⟨hP, hO, hI⟩ := JEx.rels V.frame c.O T D ψ (X := {x // Gd x}) (Qbar l) (fun x => x.1) (fun x => ρ x.1 x.2)
    (fun a ha => hsep a fun x hx => ha ⟨x, hx⟩) (fun x => hD x.1 x.2) (fun x => (hPU x.1 x.2).form) (fun x => hfl x.1 x.2)
  refine ⟨(AlgebraTools.Det.polarIffLam _ _ _ _ D).1 hP, fun v g h => AlgebraTools.Det.killsLam D _ (hO v g) _ 1 le_rfl hn,
    fun u g hg h => AlgebraTools.Det.killsLam D _ (hI g fun x => ?_) _ 1 le_rfl hn⟩
  obtain ⟨t, ht, ht1⟩ := JEx.teich c r
  obtain ⟨a, ha⟩ := (hPU x.1 x.2).type t ht u
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  have h1 : a * ρ x.1 x.2 g * a⁻¹ = 1 := by
    refine Units.ext ((ha g hg1).trans ?_)
    have e : ∀ i, t i g = 1 := fun i => ht1 i g (Subgroup.mem_iInf.1 hg2 i)
    simp only [e, Units.val_one, map_one, Matrix.diagonal_one]
  exact conj_eq_one_iff.1 h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2HeckeMap
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2HeckeMap :
    ∀ (A M M' ι ι' : Type) [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] (Y : Submodule A M) (Y' : Submodule A M') (op : ι → Module.End A M) (op' : ι' → Module.End A M') [Fact (CommOn Y op)] [Fact (CommOn Y' op')] (φ : Y →ₗ[A] Y') (j : ι' → ι), Function.Injective φ → (∀ i (y : Y), ((φ ((heckeGen Y op (j i) : Module.End A Y) y) : Y') : M') = op' i (φ y)) → ∃ ψ : heckeAlg Y' op' →ₐ[A] heckeAlg Y op, (∀ i, ψ (heckeGen Y' op' i) = heckeGen Y op (j i)) ∧ ∀ (t : heckeAlg Y' op') (y : Y), φ ((ψ t : Module.End A Y) y) = (t : Module.End A Y') (φ y) := by
  intro A M M' ι ι' _ _ _ _ _ Y Y' op op' _ _ φ j hφ hop
  have uniq : ∀ (t : Module.End A Y') (s s' : heckeAlg Y op),
      (∀ y : Y, φ ((s : Module.End A Y) y) = t (φ y)) → (∀ y : Y, φ ((s' : Module.End A Y) y) = t (φ y)) → s = s' := by
    intro t s s' h h'
    exact Subtype.ext (LinearMap.ext fun y => hφ ((h y).trans (h' y).symm))
  have ex : ∀ t : heckeAlg Y' op', ∃ s : heckeAlg Y op,
      ∀ y : Y, φ ((s : Module.End A Y) y) = (t : Module.End A Y') (φ y) := by
    rintro ⟨t, ht⟩
    change ∃ s : heckeAlg Y op, ∀ y : Y, φ ((s : Module.End A Y) y) = t (φ y)
    induction ht using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, hi⟩ := hx
      exact ⟨heckeGen Y op (j i), fun y => Subtype.ext ((hop i y).trans (hi (φ y)).symm)⟩
    | algebraMap r =>
      refine ⟨algebraMap A _ r, fun y => ?_⟩
      change φ (r • y) = r • φ y
      exact map_smul φ r y
    | add a b _ _ ha hb =>
      obtain ⟨s, hs⟩ := ha
      obtain ⟨s', hs'⟩ := hb
      refine ⟨s + s', fun y => ?_⟩
      change φ ((s : Module.End A Y) y + (s' : Module.End A Y) y) = a (φ y) + b (φ y)
      rw [map_add (f := _), hs, hs']
    | mul a b _ _ ha hb =>
      obtain ⟨s, hs⟩ := ha
      obtain ⟨s', hs'⟩ := hb
      refine ⟨s * s', fun y => ?_⟩
      change φ ((s : Module.End A Y) ((s' : Module.End A Y) y)) = a (b (φ y))
      rw [hs, hs']
  choose f hf using ex
  refine ⟨{ toFun := f
            map_one' := uniq _ _ _ (hf 1) fun y => rfl
            map_mul' := fun a b => uniq _ _ _ (hf (a * b)) fun y => ?_
            map_zero' := uniq _ _ _ (hf 0) fun y => map_zero φ
            map_add' := fun a b => uniq _ _ _ (hf (a + b)) fun y => ?_
            commutes' := fun r => uniq _ _ _ (hf (algebraMap A _ r)) fun y => map_smul φ r y }, fun i => ?_, hf⟩
  · change φ ((f a : Module.End A Y) ((f b : Module.End A Y) y)) = (a : Module.End A Y') ((b : Module.End A Y') (φ y))
    rw [hf, hf]
  · change φ ((f a : Module.End A Y) y + (f b : Module.End A Y) y) = (a : Module.End A Y') (φ y) + (b : Module.End A Y') (φ y)
    rw [map_add (f := _), hf, hf]
  · exact uniq _ _ _ (hf (heckeGen Y' op' i)) fun y => Subtype.ext (hop i y)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ExistsOrdinaryCharactersHeckeAlgebra
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.exists_ordinaryCharacters_heckeAlgebra :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (Λ : LamObj r) (R : HD Q ι Λ), (hset Q R.τ₀).Ax →
    ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (φ : Λ.Λ →ₐ[c.O] T) (gen : (hset Q R.τ₀).Op → T), (∀ i, gen i - algebraMap c.O T (R.a i) ∈ maximalIdeal T) →
    ∀ ψ : ∀ v : V.frame.Vl, Fin n → Dec (F := L) (s.A v.1) →* Tˣ, (∀ v i, Alg.AdicCont (maximalIdeal T) fun g => (ψ v i g : T)) →
    (∀ (v : V.frame.Vl) (i : Fin n) (x : Weil (s.hw v.1)) (g : Dec (F := L) (s.A v.1)) (y : Uo ((s.w v.1).adicCompletion L)), (g : G L Ω) = (x : G L Ω) → artOf (s.hw v.1) x = y →
      (ψ v i g * (hset Q R.τ₀).epsV T v g ^ (i : ℕ) : Tˣ) * φ (R.θ (eV n (hset Q R.τ₀).Sl v i y)) = 1) →
    (∀ (v : V.frame.Vl) (j : Fin n) (x : Weil (s.hw v.1)) (g : Dec (F := L) (s.A v.1)), (g : G L Ω) = (x : G L Ω) → artOf (s.hw v.1) x = unif _ →
      ((∏ i with i ≤ j, ψ v i g * (hset Q R.τ₀).epsV T v g ^ (i : ℕ) : Tˣ) : T) = gen (.inr (v, j))) →
    ∀ v i, r.IsPsi v i (ψ v i) ∧ W.pushCh (φ : Λ.Λ →+* T) (Λ.κ v i) = (ψ v i).comp (V.frame.Iv v).subtype := by
  intro l _ L Ω _ _ _ _ _ _ s n V Q c r ι Λ R hAx T _ _ _ φ gen hgen ψ hc hu hϖ v
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : Finite (ResidueField T) := Finite.of_surjective _ (Alg.resMap_bijective c.O T).2
  have ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := hAx.art_spec v
  have hI : ∀ i (g : Dec (F := L) (s.A v.1)) (hg : g ∈ V.frame.Iv v), (ψ v i g : T) = φ (Λ.κ v i ⟨g, hg⟩) := by
    intro i g hg
    have h1 := hu v i (ineIncl (s.hw v.1) ⟨g, hg⟩) g ⟨_, JEx.art_ine _ ha ⟨g, hg⟩⟩ rfl rfl
    have h2 := congrArg (fun z : Λ.Λˣ => φ z) (R.theta v i (ineIncl (s.hw v.1) ⟨g, hg⟩) g hg ⟨_, JEx.art_ine _ ha ⟨g, hg⟩⟩ rfl rfl)
    have h3 : φ ((hset Q R.τ₀).epsV Λ.Λ v g) = (hset Q R.τ₀).epsV T v g := φ.commutes _
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, Units.val_one, map_one, h3, mul_assoc] at h1 h2
    exact (left_inv_eq_right_inv h1 ((mul_comm _ _).trans h2))
  choose ψ₀ hψ₀ hκ using Λ.inert v
  have hI' : ∀ i (g : Dec (F := L) (s.A v.1)), (g : G L Ω) ∈ Ine (F := L) (s.A v.1) → (ψ v i g : T) = φ (ψ₀ i g) := by
    intro i g hg
    rw [hI i g hg, hκ]
    rfl
  obtain ⟨x, hx⟩ := ha.surj (unif _)
  let p : T →+* ResidueField c.O := Alg.res c.O T
  have hx' : ∀ i, W.pushCh p (ψ v i) (Subgroup.inclusion (Weil_le_Dec _) x) = r.psib v i (Subgroup.inclusion (Weil_le_Dec _) x) := by
    intro i
    refine mul_right_cancel (JEx.eq_of_prod
      (fun i : Fin n => W.pushCh p (ψ v i) (Subgroup.inclusion (Weil_le_Dec _) x) *
        (hset Q R.τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec _) x) ^ (i : ℕ))
      (fun i : Fin n => r.psib v i (Subgroup.inclusion (Weil_le_Dec _) x) *
        (hset Q R.τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec _) x) ^ (i : ℕ)) (fun j => Units.ext ?_) i)
    have h1 := congrArg p (hϖ v j x (Subgroup.inclusion (Weil_le_Dec _) x) rfl hx)
    have h2 := R.res.unif v j x (Subgroup.inclusion (Weil_le_Dec _) x) rfl hx
    have h3 := (Alg.res_eq_zero_iff c.O T _).2 (hgen (.inr (v, j)))
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at h3
    have h4 : p ((hset Q R.τ₀).epsV T v (Subgroup.inclusion (Weil_le_Dec _) x)) =
        (hset Q R.τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec _) x) := (Alg.res c.O T).commutes _
    refine Eq.trans ?_ ((h1.trans h3).trans h2.symm)
    simp only [Units.coe_prod, map_prod, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
    exact Finset.prod_congr rfl fun k _ => congrArg₂ (· * ·) rfl (congrArg (· ^ (k : ℕ)) h4.symm)
  intro i
  refine ⟨⟨hc v i, fun g => ?_, fun g => ?_⟩, MonoidHom.ext fun g => Units.ext (hI i g.1 g.2).symm⟩
  · have h1 : IsLocallyConstant (W.pushCh p (ψ v i)) :=
      IsLocallyConstant.desc _ Units.val (JEx.res_lc (O := c.O) (hc v i)) Units.val_injective
    let β : Dec (F := L) (s.A v.1) →* (ResidueField c.O)ˣ := r.psib v i
    have h2 : IsLocallyConstant β := JEx.lc_of_open _ (r.psib_open v i)
    have h3 := JEx.char_triv (s.hw v.1) ha (W.pushCh p (ψ v i) / β) (h1.div h2) (fun y hy => by
      rw [MonoidHom.div_apply, div_eq_one]
      refine Units.ext ?_
      exact (congrArg p (hI' i y hy)).trans ((Alg.res_map φ _).trans ((hψ₀ i).red y))) x hx (by rw [MonoidHom.div_apply, div_eq_one]; exact hx' i)
    have h4 : W.pushCh p (ψ v i) g / β g = 1 := DFunLike.congr_fun h3 g
    exact congrArg Units.val (div_eq_one.1 h4)
  · obtain ⟨k, hk⟩ := g.2
    have h1 := JEx.eq_on_tors (s.hw v.1) (ψ v i) (W.pushCh (φ : Λ.Λ →+* T) (ψ₀ i)) (hc v i) (JEx.cont_map φ (hψ₀ i).cont)
      (fun y hy => Units.ext (hI' i y hy)) g.1 (l ^ k) (pow_pos (Fact.out : l.Prime).pos k)
      ((QuotientGroup.eq_one_iff _).1 ((map_pow (QuotientGroup.mk' _) _ _).trans hk))
    exact (congrArg Units.val h1).trans ((congrArg φ ((hψ₀ i).mu g)).trans (φ.commutes _))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2OrdPt
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2EigPart
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2EigPart :
    ∀ (K W ι : Type) [Field K] [AddCommGroup W] [Module K W] (J : Type 1) (op : ι → Module.End K W) (Z : J → Submodule K W) (μ : J → ι → K), (∀ j i, ∀ F ∈ Z j, op i F = μ j i • F) → ∀ F ∈ ⨆ j, Z j, F ≠ 0 → ∀ ν : ι → K, (∀ i, op i F = ν i • F) → ∃ j, μ j = ν := by
  intro K W ι _ _ _ J op Z μ hZ F hF hF0 ν hν
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hF
  have inv : ∀ (t : Finset J) i, ∀ G ∈ ⨆ j ∈ t, Z j, op i G ∈ ⨆ j ∈ t, Z j := by
    intro t i
    have hle : (⨆ j ∈ t, Z j) ≤ (⨆ j ∈ t, Z j).comap (op i) := by
      refine iSup₂_le fun j hj => ?_
      intro G hG
      rw [Submodule.mem_comap, hZ j i G hG]
      exact Submodule.smul_mem _ _ ((le_iSup₂ (f := fun j (_ : j ∈ t) => Z j) j hj) hG)
    exact fun G hG => hle hG
  suffices key : ∀ t : Finset J, ∀ G ∈ ⨆ j ∈ t, Z j, G ≠ 0 → (∀ i, op i G = ν i • G) → ∃ j, μ j = ν from
    key s F hs hF0 hν
  intro t
  refine Finset.induction_on t ?_ ?_
  · intro G hG hG0 _
    simp at hG
    exact absurd hG hG0
  · intro a t ha ih G hG hG0 hGν
    rw [Finset.iSup_insert, Submodule.mem_sup] at hG
    obtain ⟨H, hH, G', hG', rfl⟩ := hG
    by_cases hμ : μ a = ν
    · exact ⟨a, hμ⟩
    obtain ⟨i, hi⟩ : ∃ i, μ a i ≠ ν i := by
      by_contra h
      push_neg at h
      exact hμ (funext h)
    have e : (μ a i - ν i) • H = ν i • G' - op i G' := by
      have h1 := hGν i
      rw [map_add (f := _), hZ a i H hH, smul_add] at h1
      rw [sub_smul, sub_eq_sub_iff_add_eq_add, h1, add_comm]
    have hsub : (μ a i - ν i) • H ∈ ⨆ j ∈ t, Z j := by
      rw [e]
      exact sub_mem (Submodule.smul_mem _ _ hG') (inv t i G' hG')
    have hH' : H ∈ ⨆ j ∈ t, Z j := by
      have hne : μ a i - ν i ≠ 0 := sub_ne_zero.mpr hi
      have h2 := Submodule.smul_mem _ (μ a i - ν i)⁻¹ hsub
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
    exact ih (H + G') (add_mem hH' hG') hG0 hGν
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

open TensorProduct in
private theorem op_eig {A K M W ι : Type} [CommRing A] [Field K] [AddCommGroup M] [Module A M]
    [AddCommGroup W] [Module K W] (Y : Submodule A M) [Module.Free A Y] [Module.Finite A Y]
    (op : ι → Module.End A M) [hc : Fact (CommOn Y op)] (χ : A →+* K) (sp : M → W)
    (hadd : ∀ f ∈ Y, ∀ f' ∈ Y, sp (f + f') = sp f + sp f') (hsmul : ∀ f ∈ Y, ∀ b : A, sp (b • f) = χ b • sp f)
    (hind : ∀ (κ : Type) (b : Module.Basis κ A Y), LinearIndependent K fun i => sp (b i))
    (opC : ι → Module.End K W) (hop : ∀ i, ∀ f ∈ Y, sp (op i f) = opC i (sp f))
    (z : heckeAlg Y op →+* K) (hz : z.comp (algebraMap A _) = χ) :
    ∃ F ∈ Submodule.span K (sp '' Y), F ≠ 0 ∧ ∀ i, opC i F = z (heckeGen Y op i) • F := by
  letI : Algebra A K := χ.toAlgebra
  letI : Module A W := Module.compHom W χ
  haveI : IsScalarTower A K W := ⟨fun a k w => mul_smul (χ a) k w⟩
  let s : Y →ₗ[A] W :=
    { toFun := fun f => sp f
      map_add' := fun f g => hadd _ f.2 _ g.2
      map_smul' := fun b f => hsmul _ f.2 b }
  have hs : Function.Injective (s.liftBaseChange K) := by
    let b := Module.Free.chooseBasis A Y
    have h1 : s.liftBaseChange K = Finsupp.linearCombination K (fun i => sp (b i)) ∘ₗ (b.baseChange K).repr.toLinearMap :=
      (b.baseChange K).ext fun i => by
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.linearCombination_single,
          Module.Basis.baseChange_apply, LinearMap.liftBaseChange_tmul]
        rfl
    rw [h1, LinearMap.coe_comp]
    exact Function.Injective.comp (hind _ b) (b.baseChange K).repr.injective
  obtain ⟨v, hv, hv'⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.pointEig (M := Y)
    ({ z with commutes' := fun b => RingHom.congr_fun hz b } : heckeAlg Y op →ₐ[A] K)
  refine ⟨s.liftBaseChange K v, ?_, fun h => hv (hs (h.trans (map_zero _).symm)), fun i => ?_⟩
  · have h : s.liftBaseChange K v ∈ LinearMap.range (s.liftBaseChange K) := ⟨v, rfl⟩
    rw [LinearMap.range_liftBaseChange] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨f, rfl⟩
    exact ⟨f, f.2, rfl⟩
  · have h1 : opC i ∘ₗ s.liftBaseChange K =
        s.liftBaseChange K ∘ₗ (Algebra.lsmul A A Y (heckeGen Y op i)).baseChange K := by
      ext y
      simp only [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self, curry_apply, LinearMap.coe_restrictScalars,
        LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, one_smul]
      exact (hop i _ y.2).symm
    have h2 := LinearMap.congr_fun h1 v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hv', map_smul] at h2
    exact h2

theorem UpperTheory.V.Hi.levelUR2OrdPt :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P → ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → lam ∈ H.admitted → ∀ (K : H.Lev) [Fact (CommOn (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A))] (z : heckeAlg (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) →+* Qbar l), z.comp (algebraMap A _) = x.toRingHom → ∃ Y : H.Part ι lam ξ, ∀ (w : H.Wp) (k : Fin n), Y.a w (k + 1) = ι (z (heckeGen _ (H.op A) (.inl (w, k)))) := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam d ξ c0 sp hsp hlam K _ z hz
  obtain ⟨-, hfin, hfree, -⟩ := hiComm L Ω l n c H hH A θ hθ K
  obtain ⟨F, hF, hF0, h⟩ := op_eig (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) (ι.toRingHom.comp x.toRingHom) sp
    (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K) (ι.toRingHom.comp z)
    (by rw [RingHom.comp_assoc, hz])
  rw [hsp.span K c0 le_rfl, (clParts L Ω l n c H hH A θ hθ ι P hP x lam d ξ c0 sp hsp hlam K c0 le_rfl).2] at hF
  obtain ⟨Y, hY⟩ := levelUR2EigPart ℂ _ (H.Wp × Fin n) {Y : H.Part ι lam ξ // P lam Y.r}
    (fun i => H.opC ι lam d (.inl i)) (fun Y => Y.1.Y) (fun Y i => Y.1.a i.1 (i.2 + 1))
    (fun Y i G hG => Y.1.sph i.1 _ G hG) F (SetLike.le_def.1 (iSup_mono fun _ => inf_le_left) hF) hF0
    (fun i => ι (z (heckeGen _ (H.op A) (.inl i)))) (fun i => h (.inl i))
  exact ⟨Y.1, fun w k => congrFun hY (w, k)⟩
end
