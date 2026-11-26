module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ImportsVariant
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.AlgSatSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.ExistsTens
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.ExistsScalar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.AbsTrans
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.PartH
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspSupportOf
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ClozelCohomological
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlgIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.BorelInjC
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.RelOnto
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.relOnto :
    UpperTheory.V.Cj.RelOnto := by
  intro hA E _ _ _ a ha σ Ξ Ξ' h hσ q M hM1 hM2 ω ⟨U, uo, uc, hω⟩ dω rω
  obtain ⟨α, a1, a2, a3, a4⟩ := UpperTheory.V.Lit.Geo.g2 E a ha U uo uc Ξ q ω hω dω rω
  obtain ⟨U', -, uo', uc', β, b1, b2, b3⟩ := hA E a ha U uo uc σ Ξ Ξ' h hσ q α a1 a2 a3
  have bL : Lev Ξ' β := ⟨U', uo', uc', b3.2.1⟩
  obtain ⟨β', hβ', hex⟩ := hM2 β bL b1 b2
  obtain ⟨R1, -, -, R4⟩ := UpperTheory.V.Cj.relFacts E a ha σ Ξ Ξ' h hσ q
  obtain ⟨-, -, L, L1, -⟩ := UpperTheory.V.Cj.levSub E a Ξ q
  obtain ⟨-, -, L', L1', -⟩ := UpperTheory.V.Cj.levSub E a Ξ' q
  obtain ⟨B, B1, -⟩ := UpperTheory.V.Cj.exactSub E a Ξ' q
  have dsub : ∀ (Θ : AlgRep E a) (x y : Co Θ q), dCo (smLie Θ) x = 0 → dCo (smLie Θ) y = 0 →
      dCo (smLie Θ) (x - y) = 0 := fun Θ x y hx hy => by
    have e : x - y = (-1 : ℂ) • y + x := by rw [neg_one_smul ℂ y]; abel
    rw [e, dCo_comb, hx, hy, smul_zero, add_zero]
  have hx : Exact Ξ' (β' - β) := (B1 _).1 (by rw [← neg_sub]; exact B.neg_mem ((B1 _).2 hex))
  have r1 : Rel σ h (ω - α) (β' - β) :=
    R4 _ _ ((L1 _).1 (L.sub_mem ((L1 _).2 ⟨U, uo, uc, hω⟩) ((L1 _).2 ⟨U, uo, uc, a1⟩)))
      ((L1' _).1 (L'.sub_mem ((L1' _).2 (hM1 _ hβ').1) ((L1' _).2 bL)))
      (dsub _ _ _ dω a2) (dsub _ _ _ (hM1 _ hβ').2 b1) ⟨U, uo, uc, a4⟩ hx
  have r2 := R1 1 _ _ _ _ r1 ⟨U', uo', uc', b3⟩
  rw [map_one, one_smul, one_smul, sub_add_cancel, sub_add_cancel] at r2
  exact ⟨β', hβ', r2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.HarmInj
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.harmInj :
    UpperTheory.V.Cj.HarmInj := by
  intro E _ _ _ a ha π Ξ r n e he hr q ω ⟨⟨U, u1, u2, u3⟩, _, hco, hV⟩ ⟨U', v1, v2, v3⟩
  cases q with
  | zero => exact v3
  | succ q =>
    have ho : IsOpen ((U ⊓ U' : Subgroup _) : Set (GL (Fin a) (Af E))) := u1.inter v1
    have hc : IsCompact ((U ⊓ U' : Subgroup _) : Set (GL (Fin a) (Af E))) :=
      u2.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun k hk => hk.1
    have hm := (levSub E a Ξ (q + 1)).2.1
    have hL := (hm U (U ⊓ U') inf_le_left ω).1 u3
    obtain ⟨η, hη, rfl⟩ := (hm U' (U ⊓ U') inf_le_right ω).2 v3
    have hR : Rapid (dCo (smLie Ξ) η) := fun X N => cuspRapid E a π Ξ (q + 1) _ hV [] X N
    obtain ⟨χ, hχ⟩ := twEx E a ha r
    obtain ⟨G, hG⟩ := admEx E a Ξ
    have hd : IsData Ξ r χ G e := ⟨hr, hχ, hG, he⟩
    have hM : Moderate (dCo (smLie Ξ) η) := ⟨0, fun X => by
      obtain ⟨C, hC⟩ := hR X 0
      exact ⟨C, fun g => by simpa using hC g⟩⟩
    set_option synthInstance.maxHeartbeats 400000 in
    have hP := pairFacts E a ha MeasureTheory.Measure.haar _ ho Ξ r χ G n e hd (q + 1)
    set_option synthInstance.maxHeartbeats 400000 in
    exact hP.2.2.1 _ hL (hP.1 _ _ hL hL hR hM)
      (g1 E a ha MeasureTheory.Measure.haar _ ho hc Ξ r χ G n e hd q _ η hL hη hR hco hM)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.HarmNe
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.harmNe :
    UpperTheory.V.Cj.HarmNe := by
  intro E _ _ _ a ha π Ξ r n e he hr hC
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have h0' : (⟨φ, hφ⟩ : π.V) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  let S : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | π.finPart k ⟨φ, hφ⟩ = ⟨φ, hφ⟩}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        change π.finPart (x * y) _ = _
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        change π.finPart x⁻¹ _ = _
        conv_lhs => rw [← show π.finPart x ⟨φ, hφ⟩ = ⟨φ, hφ⟩ from hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hL : IsOpen (S : Set (GL (Fin a) (Af E))) := π.isSmooth_finPart _
  obtain ⟨K₀, ho₀, hc₀⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a
  have ho : IsOpen ((K₀ ⊓ S : Subgroup _) : Set (GL (Fin a) (Af E))) := ho₀.inter hL
  have hc : IsCompact ((K₀ ⊓ S : Subgroup _) : Set (GL (Fin a) (Af E))) :=
    hc₀.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun k hk => hk.1
  obtain ⟨q, ω, w0, wH, wV⟩ := harmEx E a ha n e he _ hc π Ξ r hr hC ⟨⟨φ, hφ⟩, h0', fun k hk => hk.2⟩
  exact ⟨q, ω, w0, ⟨_, ho, hc, ((harmLin E a n e _ Ξ r q).2 ω).1 wH⟩, wH.closed, wH.coclosed, wV⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ConjEx
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private def Cv (_ : ℂ ≃+* ℂ) (V : Type) : Type := V

private instance (σ : ℂ ≃+* ℂ) (V : Type) [i : AddCommGroup V] : AddCommGroup (Cv σ V) := i

private noncomputable instance (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] : Module ℂ (Cv σ V) :=
  Module.compHom V σ.symm.toRingHom

private def toCv (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] : V ≃+ Cv σ V := AddEquiv.refl V

private theorem smul_toCv (σ : ℂ ≃+* ℂ) {V : Type} [AddCommGroup V] [Module ℂ V] (c : ℂ) (v : V) :
    c • toCv σ V v = toCv σ V (σ.symm c • v) := rfl

private theorem toCv_smul (σ : ℂ ≃+* ℂ) {V : Type} [AddCommGroup V] [Module ℂ V] (c : ℂ) (v : V) :
    toCv σ V (c • v) = σ c • toCv σ V v := by
  rw [smul_toCv, RingEquiv.symm_apply_apply]

private noncomputable def cvRep (σ : ℂ ≃+* ℂ) {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Representation ℂ G (Cv σ V) where
  toFun g :=
    { toFun := fun v => toCv σ V (ρ g ((toCv σ V).symm v))
      map_add' := fun x y => by simp only [map_add (f := _)]
      map_smul' := fun c x => congrArg (toCv σ V) (map_smul (ρ g) (σ.symm c) ((toCv σ V).symm x)) }
  map_one' := LinearMap.ext fun v => by simp
  map_mul' x y := LinearMap.ext fun v => by
    simp only [map_mul]
    rfl

private theorem cvRep_irr (σ : ℂ ≃+* ℂ) {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : (cvRep σ ρ).IsIrreducible := by
  obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff ρ).1 h
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => ?_⟩
  let W' : Submodule ℂ V :=
    { carrier := {v | toCv σ V v ∈ W}
      add_mem' := fun {x y} hx hy => W.add_mem hx hy
      zero_mem' := W.zero_mem
      smul_mem' := fun c x hx => by
        change toCv σ V (c • x) ∈ W
        rw [toCv_smul]
        exact W.smul_mem _ hx }
  rcases h1 W' (fun g v hv => hW g _ hv) with e | e
  · exact Or.inl ((Submodule.eq_bot_iff _).2 fun v hv => (Submodule.eq_bot_iff _).1 e ((toCv σ V).symm v) hv)
  · exact Or.inr (Submodule.eq_top_iff'.2 fun v => Submodule.eq_top_iff'.1 e ((toCv σ V).symm v))

theorem UpperTheory.V.Cj.conjEx :
    UpperTheory.V.Cj.ConjEx := by
  intro E _ _ a σ τ
  exact ⟨SmIrr.mk (Cv σ τ.V) (cvRep σ τ.ρ) τ.5 (cvRep_irr σ τ.ρ τ.irred), toCv σ τ.V, toCv_smul σ, fun _ _ => rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.Graph
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.graph :
    UpperTheory.V.Cj.Graph := by
  intro G V V' W _ _ _ _ _ _ _ ρ ρ' ρW σ T hTs hTg M hM R hlin hg hex hiff
  have huniq : ∀ v w1 w2, w1 ∈ M → w2 ∈ M → R v w1 → R v w2 → w1 = w2 := by
    intro v w1 w2 m1 m2 r1 r2
    have h := hlin (-1) v v w1 w2 r1 r2
    have hm : σ (-1) • w1 + w2 ∈ M := M.add_mem (M.smul_mem _ m1) m2
    have h0 : (-1 : ℂ) • v + v = 0 := by simp
    rw [h0] at h
    have h1 := (hiff 0 _ hm h).1 rfl
    rw [map_neg, map_one, neg_one_smul, neg_add_eq_zero] at h1
    exact h1
  have hR0 : R 0 0 := by
    obtain ⟨w, hw, hr⟩ := hex 0
    rwa [(hiff 0 w hw hr).1 rfl] at hr
  choose j hjM hjR using fun v' : V' => hex (T.symm v')
  have hTsymm_smul : ∀ (c : ℂ) (v' : V'), T.symm (c • v') = σ.symm c • T.symm v' := by
    intro c v'
    apply T.injective
    rw [hTs, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hTsymm_g : ∀ (g : G) (v' : V'), T.symm (ρ' g v') = ρ g (T.symm v') := by
    intro g v'
    apply T.injective
    rw [hTg, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let J : V' →ₗ[ℂ] W :=
    { toFun := j
      map_add' := by
        intro a b
        apply huniq (T.symm (a + b)) _ _ (hjM _) (M.add_mem (hjM a) (hjM b)) (hjR _)
        have h := hlin 1 _ _ _ _ (hjR a) (hjR b)
        simpa [map_add (f := _)] using h
      map_smul' := by
        intro c a
        apply huniq (T.symm (c • a)) _ _ (hjM _) (M.smul_mem c (hjM a)) (hjR _)
        have h := hlin (σ.symm c) _ _ _ _ (hjR a) hR0
        simpa [hTsymm_smul] using h }
  refine ⟨J, ?_, hjM, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v' hv'
    have h := (hiff (T.symm v') (j v') (hjM v') (hjR v')).2 hv'
    simpa using congrArg T h
  · intro g v'
    apply huniq (T.symm (ρ' g v')) _ _ (hjM _) (hM g _ (hjM v')) (hjR _)
    rw [hTsymm_g]
    exact hg g _ _ (hjR v')
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.IrrCo
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.IrrAbs
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem irrAbs_module {R M S W κ ι : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S] [Module R S]
    [AddCommGroup W] [Module R W] [IsSimpleModule R S] [Finite ι] (Φ : (κ →₀ S) →ₗ[R] M) (hs : Function.Surjective Φ)
    (p : ι → W →ₗ[R] M) (hp : ∀ w, (∀ i, p i w = 0) → w = 0) (x : W) (hx : x ≠ 0) :
    ∃ f : S →ₗ[R] W, Function.Injective f := by
  haveI := IsSemisimpleModule.range Φ
  haveI : IsSemisimpleModule R M :=
    IsSemisimpleModule.congr (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 hs)).symm
  let e : W →ₗ[R] (ι → M) := LinearMap.pi p
  have he : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact hp w fun i => congrFun hw i
  haveI : IsSemisimpleModule R W := IsSemisimpleModule.of_injective e he
  haveI : Nontrivial W := ⟨⟨x, 0, hx⟩⟩
  obtain ⟨N, hN⟩ := IsSemisimpleModule.exists_simple_submodule R W
  haveI := hN
  haveI := IsSimpleModule.nontrivial R N
  obtain ⟨y, hy⟩ := exists_ne (0 : N)
  have hex : ∃ i, p i (y : W) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy (Subtype.ext (hp _ h))
  obtain ⟨i, hi⟩ := hex
  let g : N →ₗ[R] M := (p i).comp N.subtype
  have hg : Function.Injective g := by
    rcases g.injective_or_eq_zero with h | h
    · exact h
    · exact absurd (LinearMap.congr_fun h y) hi
  obtain ⟨r, hr⟩ := IsSemisimpleModule.extension_property g hg LinearMap.id
  have hrΦ : r.comp Φ ≠ 0 := by
    obtain ⟨z, hz⟩ := hs (g y)
    intro h
    apply hy
    have h1 := LinearMap.congr_fun h z
    have h2 := LinearMap.congr_fun hr y
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at h1 h2
    rw [hz] at h1
    rw [← h2, h1]
  have hex2 : ∃ k, (r.comp Φ).comp (Finsupp.lsingle k) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hrΦ
    apply Finsupp.lhom_ext
    intro a b
    simpa using LinearMap.congr_fun (h a) b
  obtain ⟨k, hk⟩ := hex2
  have hf0 : Function.Injective ((r.comp Φ).comp (Finsupp.lsingle k)) :=
    (LinearMap.injective_or_eq_zero _).resolve_right hk
  exact ⟨N.subtype.comp ((r.comp Φ).comp (Finsupp.lsingle k)), N.injective_subtype.comp hf0⟩

theorem UpperTheory.V.Cj.irrAbs :
    UpperTheory.V.Cj.IrrAbs := by
  intro G S V W ι _ _ _ _ _ _ _ _ _ ρS ρV ρW hirr hsup p hp hsep
  classical
  let F : {f : S →ₗ[ℂ] V // ∀ (g : G) (v : S), f ((ρS g) v) = (ρV g) (f v)} →
      (ρS.asModule →ₗ[MonoidAlgebra ℂ G] ρV.asModule) := fun f =>
    Representation.IntertwiningMap.equivLinearMapAsModule ρS ρV
      ((f.1).intertwiningMap_of_isIntertwiningMap ρS ρV f.2)
  let Φ := Finsupp.lsum ℕ F
  have key : ∀ u : V, u ∈ (⨆ f : {f : S →ₗ[ℂ] V // ∀ (g : G) (v : S), f ((ρS g) v) = (ρV g) (f v)},
      LinearMap.range f.1) → ∃ z, Φ z = (show ρV.asModule from u) := by
    intro u hu
    refine Submodule.iSup_induction (motive := fun u : V => ∃ z, Φ z = (show ρV.asModule from u)) _ hu ?_ ?_ ?_
    · rintro f u ⟨s, rfl⟩
      exact ⟨Finsupp.single f s, Finsupp.lsum_single ℕ F f s⟩
    · exact ⟨0, map_zero Φ⟩
    · rintro a b ⟨za, ha⟩ ⟨zb, hb⟩
      exact ⟨za + zb, by rw [map_add (f := _), ha, hb]; rfl⟩
  have hΦ : Function.Surjective Φ := by
    intro v
    exact key v (by rw [hsup]; exact Submodule.mem_top)
  let P : ι → (ρW.asModule →ₗ[MonoidAlgebra ℂ G] ρV.asModule) := fun i =>
    Representation.IntertwiningMap.equivLinearMapAsModule ρW ρV
      ((p i).intertwiningMap_of_isIntertwiningMap ρW ρV (hp i))
  have hP : ∀ w : ρW.asModule, (∀ i, P i w = 0) → w = 0 := fun w h => hsep w h
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  haveI : IsSimpleModule (MonoidAlgebra ℂ G) ρS.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρS).1 hirr
  obtain ⟨f, hf⟩ := irrAbs_module Φ hΦ P hP (show ρW.asModule from x) hx
  let f' := (Representation.IntertwiningMap.equivLinearMapAsModule ρS ρW).symm f
  exact ⟨f'.toLinearMap, hf, fun g v => f'.isIntertwining ρS ρW g v⟩
end

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.irrCo :
    UpperTheory.V.Cj.IrrCo := by
  intro E _ _ _ a π τ hτ Ξ q P hP hst hV
  haveI : Nontrivial P := Submodule.nontrivial_iff_ne_bot.2 hP
  haveI : Module.Finite ℝ (Herm E a) := inferInstance
  let b := Module.finBasis ℝ (Herm E a)
  let ρW : Representation ℂ (GL (Fin a) (Af E)) P :=
    { toFun := fun x => (transRep Ξ q x).restrict (fun ω hω => hst x ω hω)
      map_one' := LinearMap.ext fun w => Subtype.ext (by simp)
      map_mul' := fun x y => LinearMap.ext fun w =>
        Subtype.ext (LinearMap.congr_fun (map_mul (transRep Ξ q) x y) w.1) }
  let p : (Fin q → Fin (Module.finrank ℝ (Herm E a))) × Fin Ξ.d → P →ₗ[ℂ] π.V := fun j =>
    { toFun := fun w => ⟨Bor.cmp j.2 (w.1 fun k => b (j.1 k)), mem_tens.1 (hV w.1 w.2 _) j.2⟩
      map_add' := fun x y => Subtype.ext (by
        change Bor.cmp j.2 ((x.1 + y.1) _) = Bor.cmp j.2 _ + Bor.cmp j.2 _
        rw [AlternatingMap.add_apply, map_add (f := _)])
      map_smul' := fun c x => Subtype.ext (by
        change Bor.cmp j.2 ((c • x.1) _) = c • Bor.cmp j.2 _
        rw [AlternatingMap.smul_apply, map_smul]) }
  obtain ⟨Φ, h1, h2⟩ := irrAbs _ τ.V π.V P _ τ.ρ π.finPart ρW τ.irred hτ.iSup_range p
    (fun j g w => Subtype.ext (cmp_trans g w.1 _ j.2))
    (fun w hw => Subtype.ext (by
      refine Module.Basis.ext_alternating b fun v _ => ?_
      rw [← sum_cmp (w.1 _)]
      have : ∀ i, Bor.cmp i (w.1 fun k => b (v k)) = 0 := fun i => congrArg Subtype.val (hw (v, i))
      simp [this]))
  exact ⟨P.subtype ∘ₗ Φ, P.subtype_injective.comp h1, fun v => (Φ v).2, fun g v => congrArg Subtype.val (h2 g v)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.ExAlgRepCusp
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WindowBoundReduction.ExistsAlgRepQdetEqSmulOneOfIsReg
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.WeylC UpperTheory.V.Cj.R

theorem UpperTheory.exists_algRep_qdet_eq_smul_one_of_isReg :
    ∀ (E : Type) [Field E] [NumberField E] (a D : ℕ), 0 < D → ∀ (ρ : GL (Fin a) (Cinf E) →* Matrix (Fin D) (Fin D) ℂ), IsReg ρ → ∀ s : (E →+* ℂ) → ℂ → ℂ, (∀ τ u, Formalism.REAL.qdet (eOf ρ τ) u = s τ u • 1) → ∃ Ξ : AlgRep E a, ∀ τ u, Formalism.REAL.qdet (eOf Ξ.mat τ) u = s τ u • 1 := by
  intro E _ _ a D hD ρ hreg s hs
  obtain ⟨d, A, B, σ, hd, -, hBA, hσ, hint, hirr⟩ := UpperTheory.V.Weyl.irrSub _ D ρ hD
  have hσreg : IsReg σ := by simpa only [← hσ] using isReg_conj hreg B A
  refine ⟨⟨d, σ, hσreg, hd, hirr⟩, fun τ u => ?_⟩
  have hlie : ∀ i j, eOf ρ τ i j * A = A * eOf σ τ i j := by
    intro i j
    have l := eOf_conj hreg (1 : Matrix (Fin D) (Fin D) ℂ) A τ i j
    have r := eOf_conj hσreg A (1 : Matrix (Fin d) (Fin d) ℂ) τ i j
    simp only [Matrix.one_mul, Matrix.mul_one, hint] at l r
    exact l.symm.trans r
  have hq := UpperTheory.V.Weyl.qdetRect a D d _ _ A hlie u
  calc Formalism.REAL.qdet (eOf σ τ) u = B * (A * Formalism.REAL.qdet (eOf σ τ) u) := by
        rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
    _ = s τ u • 1 := by
        rw [← hq, hs, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hBA]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WindowBoundReduction.WindowIntegerGapBound
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.WeylC UpperTheory.V.Cj.R

private theorem lift_int (c : ℂ) (m : Multiset ℂ) (h : ∀ z ∈ m, ∃ n : ℤ, z = (n : ℂ) + c) :
    ∃ m' : Multiset ℤ, m = m'.map (fun n : ℤ => (n : ℂ) + c) := by
  induction m using Multiset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | cons z m ih =>
    obtain ⟨m', rfl⟩ := ih (fun w hw => h w (Multiset.mem_cons_of_mem hw))
    obtain ⟨n, rfl⟩ := h z (Multiset.mem_cons_self _ _)
    exact ⟨n ::ₘ m', by simp⟩

private theorem gap {a : ℕ} (e : Fin a → ℤ) (he : StrictMono e) (i : Fin a) :
    ∀ (d : ℕ) (j : Fin a), (j : ℕ) = i + d → e i + d ≤ e j := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have : j = i := Fin.ext (by simpa using hj)
    subst this; simp
  | succ d ih =>
    intro j hj
    have hlt : (i : ℕ) + d < a := by have := j.2; omega
    have h1 := ih ⟨i + d, hlt⟩ rfl
    have h2 : e ⟨i + d, hlt⟩ < e j := he (by rw [Fin.lt_def]; simp only; omega)
    push_cast; omega

theorem UpperTheory.window_integer_gap_bound :
    ∀ (a : ℕ) (m : Multiset ℂ), IsRegInt a m → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ ν : Fin a → ℕ, Antitone ν ∧ ∀ u : ℂ, ∏ k : Fin a, (u + ((a : ℂ) - 1) / 2 - (N : ℂ) - (k : ℂ) + (ν k : ℂ)) = ((m.map Neg.neg).map (u + ·)).prod := by
  rintro a m ⟨hc, hn, hz⟩
  obtain ⟨m', rfl⟩ := lift_int _ m hz
  have hn' : m'.Nodup := Multiset.Nodup.of_map _ hn
  let s : Finset ℤ := ⟨m', hn'⟩
  have hs : s.card = a := by simpa [s, Finset.card] using hc
  let e := s.orderEmbOfFin hs
  have hm : m' = (Finset.univ : Finset (Fin a)).val.map e := by
    have := congrArg Finset.val (Finset.map_orderEmbOfFin_univ s hs)
    rw [Finset.map_val] at this
    exact this.symm
  refine ⟨a + ∑ k : Fin a, (e k).toNat, fun N hN => ?_⟩
  have hpos : ∀ k : Fin a, 0 ≤ (N : ℤ) + k + 1 - a - e k := by
    intro k
    have := Finset.single_le_sum (f := fun k : Fin a => (e k).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    omega
  refine ⟨fun k => ((N : ℤ) + k + 1 - a - e k).toNat, ?_, fun u => ?_⟩
  · intro i j hij
    have h1 := gap e e.strictMono i (j - i) j (by have : (i : ℕ) ≤ j := hij; omega)
    have : (i : ℕ) ≤ j := hij
    simp only
    omega
  · rw [hm, Multiset.map_map, Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun k _ => ?_
    have h : ((((N : ℤ) + k + 1 - a - e k).toNat : ℕ) : ℂ) = (N : ℂ) + (k : ℕ) + 1 - a - (e k : ℤ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (hpos k)]
      push_cast; ring
    simp only [Function.comp, h]
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WindowBoundReduction.WindowLinearEntryEstimate
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.WeylC UpperTheory.V.Cj.R

private theorem lin_entry {d D : ℕ} (φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin D) :
    φ A i j = ∑ k, ∑ l, φ (Matrix.single k l 1) i j * A k l := by
  have e : A = ∑ k, ∑ l, A k l • Matrix.single k l (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single A]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

theorem UpperTheory.window_linear_entry_estimate :
    ∀ (E : Type) [Field E] [NumberField E] (a d D : ℕ) (φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) (M : GL (Fin a) (Cinf E) → Matrix (Fin d) (Fin d) ℂ), IsReg M → IsReg (fun y => φ (M y)) ∧ ∀ τ i j, eOf (fun y => φ (M y)) τ i j = φ (eOf M τ i j) := by
  intro E _ _ a d D φ M h
  refine ⟨fun i j => ?_, ?_⟩
  · have e : (fun y => φ (M y) i j) = ∑ k, ∑ l, (φ (Matrix.single k l 1) i j) • fun y => M y k l := by
      funext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact lin_entry φ (M y) i j
    rw [e]
    exact Subalgebra.sum_mem _ fun l _ => Subalgebra.sum_mem _ fun k _ => Subalgebra.smul_mem _ (h l k) _
  · have hd : ∀ X, dOf (fun y => φ (M y)) X = φ (dOf M X) := by
      intro X
      ext i j
      have h1 := HasFDerivAt.fun_sum (u := Finset.univ) fun k _ =>
        HasFDerivAt.fun_sum (u := Finset.univ) fun l _ => (h.diff k l).const_mul (φ (Matrix.single k l 1) i j)
      have h2 := h1.congr_of_eventuallyEq (extGL_eventuallyEq (f := fun y => φ (M y) i j)
        (fun y => by simp only [extGL_val]; exact lin_entry φ (M y) i j) (x := oneL E a) isUnit_one)
      rw [lin_entry φ (dOf M X), dOf, Matrix.of_apply, h2.fderiv]
      simp [dOf]
    intro τ i j
    simp only [eOf, hd, map_smul, map_sub]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.MapInfChar
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.WeylC UpperTheory.V.Af UpperTheory.V.Lit.Bor

namespace UpperTheory.V.Cj.R

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def dF (f : GL (Fin a) (Cinf E) → ℂ) : Lie E a →L[ℝ] ℂ := fderiv ℝ (extGL f) (oneL E a)

private def eF (f : GL (Fin a) (Cinf E) → ℂ) (τ : E →+* ℂ) (i j : Fin a) : ℂ :=
  (1 / 2 : ℂ) * (dF f (toL (Matrix.single i j (atEmb τ 1))) - Complex.I * dF f (toL (Matrix.single i j (atEmb τ Complex.I))))

private theorem eOf_apply {ι κ : Type} (M : GL (Fin a) (Cinf E) → Matrix ι κ ℂ) (τ : E →+* ℂ) (i j : Fin a) (k : ι) (l : κ) :
    eOf M τ i j k l = eF (fun y => M y k l) τ i j := rfl

private theorem has_dF {f : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) : HasFDerivAt (extGL f) (dF f) (oneL E a) :=
  (differentiableAt_extGL hf (x := oneL E a) isUnit_one).hasFDerivAt

private theorem dF_eq {f : GL (Fin a) (Cinf E) → ℂ} {F : Lie E a → ℂ} {D : Lie E a →L[ℝ] ℂ} (h : ∀ y, f y = F (toL y.val))
    (hD : HasFDerivAt F D (oneL E a)) : dF f = D :=
  (hD.congr_of_eventuallyEq (extGL_eventuallyEq h (x := oneL E a) isUnit_one)).fderiv

private theorem eF_const (c : ℂ) (τ : E →+* ℂ) (i j : Fin a) : eF (fun _ : GL (Fin a) (Cinf E) => c) τ i j = 0 := by
  rw [eF, dF_eq (F := fun _ => c) (fun _ => rfl) (hasFDerivAt_const c _)]
  simp

private theorem eF_add {f g : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) (hg : g ∈ regFun E a) (τ : E →+* ℂ) (i j : Fin a) :
    eF (f + g) τ i j = eF f τ i j + eF g τ i j := by
  rw [eF, dF_eq (fun y => by simp [extGL_val]) ((has_dF hf).add (has_dF hg))]
  simp only [eF, ContinuousLinearMap.add_apply]
  ring

private theorem eF_mul {f g : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) (hg : g ∈ regFun E a) (τ : E →+* ℂ) (i j : Fin a) :
    eF (f * g) τ i j = f 1 * eF g τ i j + g 1 * eF f τ i j := by
  rw [eF, dF_eq (fun y => by simp [extGL_val]) ((has_dF hf).mul (has_dF hg))]
  simp only [eF, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, extGL_one]
  ring

variable [_root_.NumberField.IsTotallyComplex E]

open Classical in
private theorem eF_coord (t τ : E →+* ℂ) (k l i j : Fin a) :
    eF (fun y : GL (Fin a) (Cinf E) => coord t (y.val k l)) τ i j = if t = τ ∧ i = k ∧ j = l then 1 else 0 := by
  have h := dF_eq (f := fun y : GL (Fin a) (Cinf E) => coord t (y.val k l)) (fun _ => rfl)
    ((coordL t).comp ((ContinuousLinearMap.proj l).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => Fin a → Cinf E) k))).hasFDerivAt
  have h2 : ∀ x : Cinf E, dF (fun y : GL (Fin a) (Cinf E) => coord t (y.val k l)) (toL (Matrix.single i j x)) =
      if i = k ∧ j = l then coord t x else 0 := fun x => by
    rw [h]
    change coord t (Matrix.single i j x k l) = _
    rw [Matrix.single_apply, apply_ite (coord t), map_zero]
  rw [eF, h2, h2]
  by_cases h3 : i = k ∧ j = l
  · simp only [h3, and_self, and_true, if_true]
    exact coord_hol τ t
  · simp [h3]

open Classical in
private theorem eF_det (t τ : E →+* ℂ) (i j : Fin a) :
    eF (fun y : GL (Fin a) (Cinf E) => (coord t y.val.det)⁻¹) τ i j = if t = τ ∧ i = j then -1 else 0 := by
  have h0 := (coordL t).hasFDerivAt.comp (oneL E a) (contDiff_det.differentiable (by simp) (oneL E a)).hasFDerivAt
  have hd : (Matrix.of (oneL E a)).det = 1 := Matrix.det_one
  have h1 := (hasDerivAt_inv (x := coordL t (Matrix.of (oneL E a)).det) (by simp [hd])).hasFDerivAt.restrictScalars ℝ
  have h := dF_eq (f := fun y : GL (Fin a) (Cinf E) => (coord t y.val.det)⁻¹) (fun _ => rfl) (h1.comp (oneL E a) h0)
  have h2 : ∀ x : Cinf E, dF (fun y : GL (Fin a) (Cinf E) => (coord t y.val.det)⁻¹) (toL (Matrix.single i j x)) =
      if i = j then -coord t x else 0 := fun x => by
    have e0 : Matrix.of (toL (Matrix.single i j x)) = Matrix.single i j x := rfl
    rw [h, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, fderiv_det_one, e0]
    split_ifs with h3
    · subst h3; simp [hd]
    · simp [hd, h3]
  rw [eF, h2, h2]
  by_cases h3 : i = j
  · have h4 := coord_hol τ t
    simp only [h3, and_true, if_true]
    split_ifs at h4 ⊢ <;> linear_combination -h4
  · simp [h3]

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private def tw (σ : ℂ ≃+* ℂ) : ((E →+* ℂ) → ℂ) →+* ((E →+* ℂ) → ℂ) :=
  Pi.ringHom fun τ => σ.symm.toRingHom.comp (Pi.evalRingHom (fun _ : E →+* ℂ => ℂ) (σ.toRingHom.comp τ))

private def tE (σ : ℂ ≃+* ℂ) : Cinf E →+* ((E →+* ℂ) → ℂ) := (tw σ).comp (emb E)

private theorem tE_apply (σ : ℂ ≃+* ℂ) (x : Cinf E) (τ : E →+* ℂ) : σ (tE σ x τ) = coord (σ.toRingHom.comp τ) x :=
  σ.apply_symm_apply _

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem comp_inj (σ : ℂ ≃+* ℂ) (t τ : E →+* ℂ) : σ.toRingHom.comp t = σ.toRingHom.comp τ ↔ t = τ :=
  ⟨fun h => RingHom.ext fun x => σ.injective (RingHom.congr_fun h x), fun h => h ▸ rfl⟩

private theorem conj_fun (σ : ℂ ≃+* ℂ) {f : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) :
    ∃ Φ : (Fin a → Fin a → (E →+* ℂ) → ℂ) → ℂ, DifferentiableOn ℂ Φ {x | IsUnit (Matrix.of x)} ∧
      (∀ y : GL (Fin a) (Cinf E), Φ (fun i j => emb E (y.val i j)) = f y) ∧
      (fun y : GL (Fin a) (Cinf E) => σ (Φ fun i j => tE σ (y.val i j))) ∈ regFun E a ∧
      ∀ τ i j, eF (fun y : GL (Fin a) (Cinf E) => σ (Φ fun i j => tE σ (y.val i j))) (σ.toRingHom.comp τ) i j = σ (eF f τ i j) := by
  classical
  have one : ∀ i j, tE σ ((1 : GL (Fin a) (Cinf E)).val i j) = emb E ((1 : GL (Fin a) (Cinf E)).val i j) := fun i j => by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    rcases hf with ⟨t, k, l, rfl⟩ | ⟨t, rfl⟩
    · refine ⟨fun x => x k l t, by fun_prop, fun _ => rfl, ?_, fun τ i j => ?_⟩
      · simp only [tE_apply]
        exact Algebra.subset_adjoin (Or.inl ⟨_, k, l, rfl⟩)
      · simp only [tE_apply, eF_coord]
        rw [if_congr (and_congr_left' (comp_inj σ t τ)) rfl rfl]
        split_ifs <;> simp
    · have e : ∀ y : GL (Fin a) (Cinf E), σ ((Matrix.of fun i j => tE σ (y.val i j)).det t)⁻¹ =
          (coord (σ.toRingHom.comp t) y.val.det)⁻¹ := fun y => by
        rw [map_inv₀, ← tE_apply, (tE σ).map_det]
        rfl
      refine ⟨fun x => ((Matrix.of x).det t)⁻¹, DifferentiableOn.inv ?_ fun x hx => ?_, fun y => ?_, ?_, fun τ i j => ?_⟩
      · simp only [Matrix.det_apply', Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Matrix.of_apply]
        exact Differentiable.differentiableOn (Differentiable.fun_sum fun σ _ =>
          (differentiable_const _).mul (by fun_prop))
      · exact (((Matrix.isUnit_iff_isUnit_det _).1 hx).map (Pi.evalRingHom (fun _ : E →+* ℂ => ℂ) t)).ne_zero
      · exact congrArg (fun z : (E →+* ℂ) → ℂ => (z t)⁻¹) ((emb E).map_det y.val).symm
      · simp only [e]
        exact Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)
      · simp only [e, eF_det]
        rw [if_congr (and_congr_left' (comp_inj σ t τ)) rfl rfl]
        split_ifs <;> simp
  | algebraMap c =>
    refine ⟨fun _ => c, differentiableOn_const c, fun _ => rfl, (regFun E a).algebraMap_mem (σ c), fun τ i j => ?_⟩
    exact (eF_const _ _ _ _).trans ((congrArg σ (eF_const c τ i j)).trans (map_zero σ)).symm
  | add f g hf hg h1 h2 =>
    obtain ⟨Φ, hΦ, e1, r1, d1⟩ := h1
    obtain ⟨Ψ, hΨ, e2, r2, d2⟩ := h2
    refine ⟨Φ + Ψ, hΦ.add hΨ, fun y => by rw [Pi.add_apply, Pi.add_apply, e1, e2], ?_, fun τ i j => ?_⟩
    · simp only [Pi.add_apply, map_add (f := _)]
      exact (regFun E a).add_mem r1 r2
    · simp only [Pi.add_apply, map_add (f := _)]
      rw [eF_add hf hg, map_add (f := _), ← d1, ← d2]
      exact eF_add r1 r2 _ i j
  | mul f g hf hg h1 h2 =>
    obtain ⟨Φ, hΦ, e1, r1, d1⟩ := h1
    obtain ⟨Ψ, hΨ, e2, r2, d2⟩ := h2
    refine ⟨Φ * Ψ, hΦ.mul hΨ, fun y => by rw [Pi.mul_apply, Pi.mul_apply, e1, e2], ?_, fun τ i j => ?_⟩
    · simp only [Pi.mul_apply, map_mul]
      exact (regFun E a).mul_mem r1 r2
    · simp only [Pi.mul_apply, map_mul]
      rw [eF_mul hf hg, map_add (f := _), map_mul, map_mul, ← d1, ← d2, ← e1, ← e2]
      simp only [← one]
      exact eF_mul r1 r2 _ i j

omit [_root_.NumberField.IsTotallyComplex E] in
private theorem stab_eOf {d : ℕ} {M : GL (Fin a) (Cinf E) → Matrix (Fin d) (Fin d) ℂ} (hM : IsReg M)
    (W : Submodule ℂ (Fin d → ℂ)) (hW : ∀ y, ∀ v ∈ W, M y *ᵥ v ∈ W) (τ : E →+* ℂ) (i j : Fin a) {v : Fin d → ℂ} (hv : v ∈ W) :
    eOf M τ i j *ᵥ v ∈ W := by
  refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).1 fun φ hφ => ?_
  let B : Matrix Unit (Fin d) ℂ := Matrix.of fun _ k => φ (Pi.single k 1)
  let A : Matrix (Fin d) Unit ℂ := Matrix.of fun k _ => v k
  have key : ∀ P : Matrix (Fin d) (Fin d) ℂ, (B * P * A) () () = φ (P *ᵥ v) := fun P => by
    rw [Matrix.mul_assoc, Matrix.mul_apply, LinearMap.pi_apply_eq_sum_univ]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_eq_mul, mul_comm]
    congr 1
    exact congrArg φ (funext fun l => by simp [Pi.single_apply, eq_comm])
  rw [← key, ← eOf_conj hM, eOf_apply]
  simp only [key, fun y => (Submodule.mem_dualAnnihilator φ).1 hφ _ (hW y v hv)]
  exact eF_const 0 τ i j

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem qdet_map (σ : ℂ ≃+* ℂ) {d : ℕ} (X : Fin a → Fin a → Matrix (Fin d) (Fin d) ℂ) (u : ℂ) :
    Formalism.REAL.qdet (fun i j => (X i j).map σ) (σ u) = (Formalism.REAL.qdet X u).map σ := by
  let f : Matrix (Fin d) (Fin d) ℂ →+* Matrix (Fin d) (Fin d) ℂ := σ.toRingHom.mapMatrix
  have hf : ∀ c : ℂ, f (algebraMap ℂ _ c) = algebraMap ℂ _ (σ c) := fun c => by
    ext k l
    simp [f, Matrix.algebraMap_matrix_apply, apply_ite σ]
  change Formalism.REAL.qdet (fun i j => f (X i j)) (σ u) = f _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, Formalism.REAL.Tm, map_add, apply_ite f, hf, map_zero, map_sub, map_natCast]

private theorem map_infChar (σ : ℂ ≃+* ℂ) (Ξ : AlgRep E a) {τ : E →+* ℂ} {m : Multiset ℂ} (h : AlgInfChar Ξ τ m) :
    ∀ z ∈ m, σ z = z := by
  obtain ⟨m', e1, -, e3⟩ := GlobalTheory.AlgInfChar.exists_dualInfChar E a Ξ τ
  have e2 := (AlgRepEndIrreducible.dualIff E a Ξ τ m').2 e1
  have e : m = m'.map Neg.neg := AlgRepEndIrreducible.msetSep _ _ fun u => by
    haveI : Nonempty (Fin Ξ.d) := ⟨⟨0, Ξ.pos⟩⟩
    exact smul_left_injective ℂ one_ne_zero ((h.2 u).symm.trans (e2.2 u))
  intro z hz
  rw [e] at hz
  obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨n, rfl⟩ := e3 w hw
  simp [map_ofNat]

theorem conjAlgMat : ConjAlgMat := by
  intro E _ _ _ a Ξ σ
  obtain ⟨R, Φ₀, hd, hR, hy⟩ := cxGrp E a Ξ
  choose Φ h1 h2 h3 h4 using fun k l => conj_fun σ (Ξ.reg k l)
  have hRΦ : ∀ g k l, R g k l = Φ k l (fun i j => g.val i j) := fun g k l => by
    rw [hR, ← sub_eq_zero]
    refine holId E a (fun x => Φ₀ k l x - Φ k l x) ((hd k l).sub (h1 k l)) (fun y => ?_) g
    rw [h2, ← hy, hR, sub_eq_zero]
    rfl
  let M : GL (Fin a) (Cinf E) →* Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
    (σ.toRingHom.mapMatrix.toMonoidHom.comp R).comp (GeneralLinearGroup.map (tE σ))
  have hM : ∀ k l, (fun y => M y k l) = fun y => σ (Φ k l fun i j => tE σ (y.val i j)) := fun k l =>
    funext fun y => congrArg σ (hRΦ _ k l)
  have hr : IsReg M := fun k l => by rw [hM]; exact h3 k l
  have hE : ∀ τ i j, eOf M (σ.toRingHom.comp τ) i j = (eOf Ξ.mat τ i j).map σ := fun τ i j => by
    ext k l
    rw [eOf_apply, hM, h4]
    rfl
  refine ⟨M, hr, fun W hW => ?_, fun γ => ?_, fun τ m hm => ⟨hm.1, fun u => ?_⟩⟩
  · let W' : Submodule ℂ (Fin Ξ.d → ℂ) :=
      { carrier := {v | σ ∘ v ∈ W}
        add_mem' := fun {v w} hv hw =>
          (congrArg (· ∈ W) (funext fun k => map_add σ (v k) (w k))).mpr (W.add_mem hv hw)
        zero_mem' := (congrArg (· ∈ W) (funext fun _ => map_zero σ)).mpr W.zero_mem
        smul_mem' := fun c v hv =>
          (congrArg (· ∈ W) (funext fun k => map_mul σ c (v k))).mpr (W.smul_mem (σ c) hv) }
    have back : ∀ v : Fin Ξ.d → ℂ, σ ∘ (σ.symm ∘ v) = v := fun v => funext fun k => σ.apply_symm_apply _
    rcases (AlgRepEndIrreducible.algIrr E a Ξ).2 W' (fun τ i j w hw => by
      have h5 := stab_eOf hr W hW (σ.toRingHom.comp τ) i j hw
      rw [hE] at h5
      change σ ∘ (eOf Ξ.mat τ i j *ᵥ w) ∈ W
      convert h5 using 1
      exact funext fun k => RingHom.map_mulVec σ.toRingHom _ _ k) with h | h
    · refine Or.inl ((Submodule.eq_bot_iff _).2 fun v hv => ?_)
      have h6 : σ.symm ∘ v = 0 := (Submodule.eq_bot_iff _).1 h _ (show σ ∘ (σ.symm ∘ v) ∈ W by rwa [back])
      rw [← back v, h6]
      exact funext fun k => map_zero σ
    · refine Or.inr (eq_top_iff.2 fun v _ => ?_)
      have h6 : σ.symm ∘ v ∈ W' := h ▸ Submodule.mem_top
      rw [← back v]
      exact h6
  · change (R _).map σ = (Ξ.mat _).map σ
    rw [← hy]
    congr 2
    ext i j τ
    apply σ.injective
    exact (tE_apply σ _ τ).trans ((coord_algebraMap _ _).trans (congrArg σ (coord_algebraMap τ _).symm))
  · obtain ⟨w, rfl⟩ := σ.surjective u
    have e1 : σ w + ((a : ℂ) - 1) / 2 = σ (w + ((a : ℂ) - 1) / 2) := by simp [map_ofNat]
    have e2 : eOf M (σ.toRingHom.comp τ) = fun i j => (eOf Ξ.mat τ i j).map σ := funext fun i => funext fun j => hE τ i j
    have e3 : (m.map (σ w + ·)).prod = σ (m.map (w + ·)).prod := by
      rw [map_multiset_prod, Multiset.map_map]
      exact congrArg _ (Multiset.map_congr rfl fun z hz => by simp [map_infChar σ Ξ hm z hz])
    change Formalism.REAL.qdet (eOf M (σ.toRingHom.comp τ)) _ = _
    rw [e1, e2, qdet_map, ((algInfChar_iff _ _ _).1 hm).2 w, e3]
    ext k l
    simp [Matrix.one_apply, apply_ite σ]

theorem conjAlgRep : ConjAlgRep := conjAlgRep_of conjAlgMat

end UpperTheory.V.Cj.R
end
end

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.WeylC UpperTheory.V.Af

namespace UpperTheory.V.Cj.R

private theorem ex_pad {d D : ℕ} (h : d ∣ D) :
    Nonempty (Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ) := by
  obtain ⟨k, rfl⟩ := h
  let b : Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Matrix (Fin d × Fin k) (Fin d × Fin k) ℂ :=
    AlgHom.mk' ((Matrix.blockDiagonalRingHom (Fin d) (Fin k) ℂ).comp (Pi.constRingHom (Fin k) _))
      fun c A => Matrix.blockDiagonal_smul c fun _ : Fin k => A
  exact ⟨(Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv).toAlgHom.comp b⟩

private theorem ex_tens {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (P : (E →+* ℂ) → Weyl.Pre a)
    (hP : ∀ τ, 0 < (P τ).d) (ν : (E →+* ℂ) → Fin a → ℂ) (hν : ∀ τ, (P τ).HasWt (ν τ)) (N : ℕ) :
    ∃ Ξ : AlgRep E a, ∀ τ u, Formalism.REAL.qdet (eOf Ξ.mat τ) u = (∏ k : Fin a, (u - N - (k : ℂ) + ν τ k)) • 1 := by
  classical
  let D := ∏ τ, (P τ).d
  have hD : 0 < D := Finset.prod_pos fun τ _ => hP τ
  let φ := fun τ => (ex_pad (Finset.dvd_prod_of_mem (fun τ => (P τ).d) (Finset.mem_univ τ))).some
  let F : (E →+* ℂ) → GL (Fin a) (Cinf E) →* Matrix (Fin D) (Fin D) ℂ := fun τ => (φ τ).toMonoidHom.comp (fac (P τ) N τ)
  have hF := fun τ => UpperTheory.window_linear_entry_estimate E a _ D (φ τ).toLinearMap _ (isReg_fac (P τ) N τ)
  have hreg : ∀ τ, IsReg (F τ) := fun τ => (hF τ).1
  have hder : ∀ t τ i j, eOf (F t) τ i j = φ t (eOf (fac (P t) N t) τ i j) := fun t => (hF t).2
  let r := Matrix.reindexAlgEquiv ℂ ℂ
    (Fintype.equivFinOfCardEq (by simp) : ((E →+* ℂ) → Fin D) ≃ Fin (D ^ Fintype.card (E →+* ℂ)))
  refine UpperTheory.exists_algRep_qdet_eq_smul_one_of_isReg E a _ (pow_pos hD _) ((r.toAlgHom.toMonoidHom.comp piK).comp (MonoidHom.pi F))
    (fun i j => isReg_piK hreg _ _) _ fun τ u => ?_
  have h1 : eOf ((r.toAlgHom.toMonoidHom.comp piK).comp (MonoidHom.pi F)) τ = fun i j =>
      ((r.toAlgHom.comp (intersection_update_fsHerm_neg_one τ)).comp (φ τ)) ((P τ).E i j + (if i = j then algebraMap ℂ _ (-(N : ℂ)) else 0)) := by
    funext i j
    change r (eOf (fun y => piK fun t => F t y) τ i j) = _
    rw [eOf_piK hreg (fun t => map_one _), Finset.sum_eq_single τ (fun t _ ht => by
      rw [hder, eOf_fac, if_neg ht, map_zero, map_zero]) (by simp), hder, eOf_fac, if_pos rfl]
    rfl
  rw [h1, ← map_qdet, qdet_shift, hν, map_smul, map_one]
  simp only [sub_eq_add_neg]

theorem exAlgRep : ExAlgRep := by
  intro E _ _ _ a m hm
  choose N₀ hN using fun τ => UpperTheory.window_integer_gap_bound a (m τ) (hm τ)
  choose ν h1 h2 using fun τ => hN τ (∑ t, N₀ t) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ))
  choose P h3 h4 h5 using fun τ => Weyl.existsScalar a (ν τ) (h1 τ) (∑ k, ν τ k)
    fun k => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  obtain ⟨Ξ, h⟩ := ex_tens P h3 _ h5 (∑ t, N₀ t)
  refine ⟨Ξ, fun τ => (algInfChar_iff _ _ _).2 ⟨by rw [Multiset.card_map, (hm τ).1], fun u => ?_⟩⟩
  rw [h, h2]

theorem exAlgRepCusp : ExAlgRepCusp := by
  intro E _ _ _ a π hπ
  have h := fun τ => ParLaws.hasInfChar_infChar (CG.mk π) τ
  obtain ⟨Ξ, hΞ⟩ := exAlgRep E a (CG.mk π).infChar fun τ => ⟨(h τ).1, hπ τ⟩
  exact ⟨Ξ, fun τ => ⟨_, h τ, hΞ τ⟩⟩

end UpperTheory.V.Cj.R
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ClozelCohC
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible

theorem UpperTheory.V.Z.Coh.clozelCohC :
    UpperTheory.V.Published.ClozelCohC := by
  intro E _ _ _ a ha π Ξ h
  choose m h1 h2 using h
  have hd : ∀ τ, GlobalTheory.WignerGL.HasDualInfChar Ξ τ (m τ) := fun τ => (dualIff E a Ξ τ _).1 (h2 τ)
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    obtain ⟨m', e1, e2, e3⟩ := GlobalTheory.AlgInfChar.exists_dualInfChar E a Ξ τ
    have e : m τ = m' := msetSep _ _ fun u => by
      haveI : Nonempty (Fin Ξ.d) := ⟨⟨0, Ξ.pos⟩⟩
      exact smul_left_injective ℂ one_ne_zero (((hd τ).2 u).symm.trans (e1.2 u))
    have h3 : (CG.mk π).HasInfChar τ (m τ) := h1 τ
    rw [h3.infChar_eq, e]
    exact ⟨e2, e3⟩
  obtain ⟨Ξ', hΞ'⟩ := PositivityTheory.Rg.Cz.clozelCohomological E a ha π hreg
  choose m' g1 g2 g3 using GlobalTheory.AlgInfChar.exists_dualInfChar E a Ξ'
  have e : m = m' := by
    by_contra hne
    exact wigner E a π Ξ' m m' h1 g1 hne hΞ'
  subst e
  obtain ⟨T, hT⟩ := algIso E a Ξ' Ξ (fun τ => (m τ).map Neg.neg) (fun τ => (dualIff E a Ξ' τ _).2 (g1 τ)) h2
  exact cohTransport E a π Ξ' Ξ T hT hΞ'
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.NullBotOrTop
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix GlobalTheory.PRep GlobalTheory.Published GlobalTheory.CuspRep.LocEx

namespace UpperTheory.V.Z.Coh.FiniteTypesComponentExistence

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private def types (π : CuspSub E a) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) :
    Submodule ℂ π.V where
  carrier := {ψ | ∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k ψ.1).1 g) ∈ AutFin.coeffSpan ρ}
  add_mem' := fun hx hy g => add_mem (hx g) (hy g)
  zero_mem' := fun _ => zero_mem _
  smul_mem' := fun c _ hx g => Submodule.smul_mem _ c (hx g)

private theorem types_act (π : CuspSub E a) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (g : GL (Fin a) (Af E)) (x : π.V) (hx : x ∈ types π ρ) :
    π.finPart g x ∈ types π ρ := fun y => by
  convert hx (y * finGL E a g) using 2 with k
  change x.1.1 (y * infGL E a _ * finGL E a _) = x.1.1 (y * finGL E a _ * infGL E a _)
  rw [mul_assoc, mul_assoc, infGL_comm]

private theorem types_fin (h : AutomorphicFormsFiniteGL) (π : CuspSub E a)
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {ρ : Representation ℂ (Kinf E a) W}
    (hρ : AutFin.IsContRep ρ) (K : Subgroup (GL (Fin a) (Af E))) (hK : IsOpen (K : Set (GL (Fin a) (Af E)))) :
    FiniteDimensional ℂ ↥(types π ρ ⊓ fixed π.finPart K) := by
  have hc : ∀ τ u, ∃ c : ℂ, ∀ φ ∈ π.V, cap τ u φ = c • φ := fun τ u =>
    π.exists_scalar (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) fun o => by
      cases o with
      | fin k => exact commute_cap_finRep τ u k
      | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
      | lie X => exact commute_cap_lie τ u X
  choose c hc using hc
  have := h E a K hK W ρ hρ c
  exact FiniteDimensional.of_injective ((π.V.subtype ∘ₗ (types π ρ ⊓ fixed π.finPart K).subtype).codRestrict
    (Submodule.span ℂ (AutFinGL.forms K ρ c))
    fun v => Submodule.subset_span ⟨(π.cusp _ v.1.2).1, fun k hk => congrArg Subtype.val (mem_fix.1 v.2.2 k hk),
      v.2.1, fun τ u => hc τ u _ v.1.2⟩)
    fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))

private theorem null_bot_or_top (π : CuspSub E a) (K : Subgroup (GL (Fin a) (Af E))) :
    nullPart π.finPart K = ⊥ ∨ nullPart π.finPart K = ⊤ := by
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ o, ∀ x ∈ nullPart π.finPart K, π.op o x ∈ nullPart π.finPart K := fun o x hx => by
    cases o with
    | fin k => exact nullPart_act _ K k hx
    | cpt k =>
      refine nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx
      change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a g)) y.1 =
        (rt E a (finGL E a g) * rt E a (infGL E a (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, infGL_comm]
    | lie X => exact nullPart_comm _ K _ (fun g y => Subtype.ext (LinearMap.congr_fun (lie_rt_fin X g) y.1)) hx
  refine (π.irred ((nullPart π.finPart K).map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩)).imp (fun e => hi (e.trans (Submodule.map_bot _).symm))
    fun e => hi (e.trans (Submodule.map_subtype_top _).symm)

private theorem exists_comp (h : AutomorphicFormsFiniteGL) (π : CuspSub E a) : ∃ τ, UpperTheory.V.Af.IsFinComp π τ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have h0' : (⟨φ, hφ⟩ : π.V) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  have hL : IsOpen (stab π.finPart ⟨φ, hφ⟩ : Set (GL (Fin a) (Af E))) := π.isSmooth_finPart _
  obtain ⟨K₀, ho₀, hc₀⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a
  have ho : IsOpen ((K₀ ⊓ stab π.finPart ⟨φ, hφ⟩ : Subgroup _) : Set (GL (Fin a) (Af E))) := ho₀.inter hL
  have hc : IsCompact ((K₀ ⊓ stab π.finPart ⟨φ, hφ⟩ : Subgroup _) : Set (GL (Fin a) (Af E))) :=
    hc₀.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun k hk => hk.1
  have : FiniteDimensional ℂ (orbSpan φ) := (π.cusp φ hφ).1.kfin
  obtain ⟨σ, hσ, -⟩ := exists_irred π.isSmooth_finPart ho (fun W hW e => by
      rcases null_bot_or_top π (K₀ ⊓ stab π.finPart ⟨φ, hφ⟩) with h2 | h2
      · exact le_bot_iff.1 (h2 ▸ le_nullPart π.isSmooth_finPart hc W hW e)
      · exact absurd (eq_zero_of_mem_nullPart π.isSmooth_finPart hc (mem_fix.2 fun k hk => hk.2)
          (h2 ▸ Submodule.mem_top)) h0')
    (types π (sub (cptRep E a) (orbSpan φ) (orbSpan_stable φ))) (types_act π _)
    ((Submodule.ne_bot_iff _).2 ⟨⟨φ, hφ⟩,
      AutFinGL.type_of_map (sub (cptRep E a) (orbSpan φ) (orbSpan_stable φ)) (orbSpan φ).subtype (fun _ _ => rfl)
        ⟨φ, Submodule.subset_span ⟨1, by simp⟩⟩, h0'⟩)
    (types_fin h π (isContRep_sub _ _))
  exact ⟨σ, hσ⟩

end UpperTheory.V.Z.Coh.FiniteTypesComponentExistence

theorem UpperTheory.V.Z.Coh.finExC :
    UpperTheory.V.Lit.FinExC := fun _ _ _ _ _ π =>
  UpperTheory.V.Z.Coh.FiniteTypesComponentExistence.exists_comp UpperTheory.V.Af.formsFiniteGL π
end
end

namespace UpperTheory.V.Z.Coh

open UpperTheory.V.Cj

theorem clozelConjC : Published.ClozelConjC :=
  clozelConjC_of_steps PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity clozelCohC finExC R.exAlgRepCusp R.conjAlgRep S.cuspSupport conjEx
    (embed_of partH relFacts partA relOnto harmSub harmNe harmInj irrCo graph Lit.Bor.frameEx Lit.Bor.oneReal Lit.Geo.cuspRapid)
    noEis

theorem borelInjC : Published.BorelInjC := Lit.Geo.borelInjC

end UpperTheory.V.Z.Coh
