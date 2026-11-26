module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.Clifford
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AcycSimp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.ColsMinSmul

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.WeilDeligne in
theorem UpperTheory.weil_group_dense_in_galois_group :
    UpperTheory.V.Af.Wd.WeilDense := by
  intro F Ω _ _ _ _ _ w A h
  have hσ := isFrob_frob (h := h)
  have h1 := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A w h ⟨_, hσ.1⟩ hσ
  have h2 : (Subgroup.zpowers (⟨_, hσ.1⟩ : Dec (F := F) A) ⊔
      (Ine (F := F) A).subgroupOf (Dec (F := F) A)) ≤ (Subgroup.inclusion (Weil_le_Dec h)).range := by
    refine sup_le ?_ fun x hx => ⟨⟨x, Ine_le_Weil h hx⟩, rfl⟩
    exact (Subgroup.zpowers_le).2 ⟨frob h, rfl⟩
  have h3 := Subgroup.topologicalClosure_mono h2
  rw [h1] at h3
  intro g
  exact h3 (Subgroup.mem_top g)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SemisimpleRestrictionToNormalSubgroup
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

private theorem UpperTheory.V.Af.Cr.semisimple_restriction_normal {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : Representation K Γ V) (N : Subgroup Γ) (hN : N.Normal)
    (hss : ∀ W : Submodule K V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) →
      ∃ W' : Submodule K V, (∀ g, ∀ v ∈ W', ρ g v ∈ W') ∧ IsCompl W W')
    (W : Submodule K V) (hW : ∀ g ∈ N, ∀ v ∈ W, ρ g v ∈ W) :
    ∃ W' : Submodule K V, (∀ g ∈ N, ∀ v ∈ W', ρ g v ∈ W') ∧ IsCompl W W' := by
  have hmul : ∀ (a b : Γ) (v : V), ρ a (ρ b v) = ρ (a * b) v := by
    intro a b v; rw [map_mul]; rfl
  obtain ⟨W', ⟨hW's, hW'd⟩, hmax⟩ := exists_maximal_of_wellFoundedGT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ Disjoint W U)
    ⟨⊥, by intro g _ v hv; rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], disjoint_bot_right⟩
  refine ⟨W', hW's, hW'd, ?_⟩
  rw [codisjoint_iff]
  obtain ⟨C, hCs, hC⟩ := hss (⨅ g : Γ, (W ⊔ W').comap (ρ g)) (by
    intro g v hv
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv ⊢
    intro h
    rw [hmul]; exact hv _)
  by_cases hC0 : C = ⊥
  · have hU := hC.sup_eq_top
    rw [hC0, sup_bot_eq] at hU
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ (⨅ g : Γ, (W ⊔ W').comap (ρ g)) := hU ▸ Submodule.mem_top
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv
    simpa using hv 1
  exfalso
  obtain ⟨S, ⟨hSs, hS0, hSC⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ U ≠ ⊥ ∧ U ≤ C)
    ⟨C, fun g _ v hv => hCs g v hv, hC0, le_rfl⟩
  have hsup : ∀ n ∈ N, ∀ v ∈ W ⊔ W', ρ n v ∈ W ⊔ W' := by
    intro n hn v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hW n hn a ha) (hW's n hn b hb)
  have key : ∀ g : Γ, ∀ s ∈ S, ρ g s ∈ W ⊔ W' := by
    intro g
    by_cases hA : S ⊓ (W ⊔ W').comap (ρ g) = ⊥
    · have hle : W' ⊔ S.map (ρ g) ≤ W' := by
        refine hmax ⟨?_, ?_⟩ le_sup_left
        · intro n hn v hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          rw [map_add (f := _)]
          refine Submodule.add_mem_sup (hW's n hn a ha) ?_
          refine Submodule.mem_map.mpr ⟨ρ (g⁻¹ * n * g) s, hSs _ (hN.conj_mem' n hn g) s hs, ?_⟩
          rw [hmul, hmul]; congr 2; group
        · rw [Submodule.disjoint_def]
          intro v hvW hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          have h1 : ρ g s ∈ W ⊔ W' := by
            have := (W ⊔ W').sub_mem (Submodule.mem_sup_left hvW) (Submodule.mem_sup_right ha)
            simpa using this
          have h2 : s ∈ S ⊓ (W ⊔ W').comap (ρ g) := ⟨hs, h1⟩
          rw [hA, Submodule.mem_bot] at h2
          subst h2
          rw [map_zero, add_zero] at hvW ⊢
          exact Submodule.disjoint_def.mp hW'd a hvW ha
      intro s hs
      exact Submodule.mem_sup_right (hle (Submodule.mem_sup_right (Submodule.mem_map_of_mem hs)))
    · have hle : S ≤ S ⊓ (W ⊔ W').comap (ρ g) := by
        refine hmin ⟨?_, hA, inf_le_left.trans hSC⟩ inf_le_left
        intro n hn v hv
        refine ⟨hSs n hn v hv.1, ?_⟩
        have h1 : ρ g v ∈ W ⊔ W' := hv.2
        have h2 := hsup _ (hN.conj_mem n hn g) _ h1
        show ρ g (ρ n v) ∈ W ⊔ W'
        rw [hmul] at h2 ⊢
        have : g * n * g⁻¹ * g = g * n := by group
        rwa [this] at h2
      intro s hs
      exact (hle hs).2
  apply hS0
  rw [eq_bot_iff, ← hC.inf_eq_bot]
  intro s hs
  refine ⟨?_, hSC hs⟩
  have : s ∈ (⨅ g : Γ, (W ⊔ W').comap (ρ g)) := by
    simp only [Submodule.mem_iInf, Submodule.mem_comap]
    exact fun g => key g s hs
  exact this

theorem UpperTheory.semisimple_restriction_to_normal_subgroup :
    UpperTheory.V.Af.Cr.SSRes := by
  intro Γ Γ' k _ _ _ n r φ hN hss W hW
  let ρ : Representation k Γ (Fin n → k) :=
    { toFun := fun g => Matrix.toLin' (r g : Matrix (Fin n) (Fin n) k)
      map_one' := by simp; rfl
      map_mul' := fun a b => by rw [map_mul, Units.val_mul, Matrix.toLin'_mul]; rfl }
  obtain ⟨W', h1, h2⟩ := UpperTheory.V.Af.Cr.semisimple_restriction_normal ρ φ.range hN (fun U hU => hss U hU) W (by
    rintro _ ⟨g, rfl⟩ v hv
    exact hW g v hv)
  exact ⟨W', fun g v hv => h1 (φ g) ⟨g, rfl⟩ v hv, h2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharAlgebraicOfSign
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

section Real

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]

private noncomputable def diagR (E : Type) [Field E] [NumberField E] [IsTotallyReal E] : E →+* TR.Rinf E :=
  (TR.pInf E).comp (algebraMap E (Ad E))

private theorem infDiag_eqR (k : Eˣ) : infDiag k = TR.infId E (Units.map (diagR E).toMonoidHom k) := by
  classical
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace E, w.Completion) →* AdeleRing (𝓞 E) E :=
      MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
    change ∏ w : InfinitePlace E, ι (Pi.mulSingle w (algebraMap E w.Completion k)) =
      ι (fun w => algebraMap E w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [h]
  refine Prod.ext ?_ ?_
  · change _ = 1 - TR.infEq E 1 + TR.infEq E ((TR.infEq E).symm (algebraMap E (InfiniteAdeleRing E) k))
    simp
  · change (1 : Af E) = 1 - 0 + 0
    simp

private theorem denseRange_diagR : DenseRange (diagR E) := by
  have hc : Continuous (TR.infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact (TR.infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc

private theorem denseRange_unitsR : DenseRange (Units.map (diagR E).toMonoidHom) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨k, v, hv, hk⟩ := denseRange_diagR.exists_mem_open (Units.isOpenEmbedding_val.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have h0 : k ≠ 0 := by
    rintro rfl
    exact v.ne_zero (hk.trans (map_zero _))
  exact ⟨v, hv, Units.mk0 k h0, Units.ext hk.symm⟩

private theorem diagR_mk (φ : E →+* ℂ) (k : E) : ((diagR E k (InfinitePlace.mk φ) : ℝ) : ℂ) = φ k := by
  have hr := IsTotallyReal.isReal (InfinitePlace.mk φ)
  have e : diagR E k (InfinitePlace.mk φ) = InfinitePlace.embedding_of_isReal hr k := by
    change InfinitePlace.Completion.extensionEmbeddingOfIsReal hr
      (algebraMap E (InfinitePlace.mk φ).Completion k) = _
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hr (WithAbs.toAbs _ k)
  rw [e, InfinitePlace.embedding_of_isReal_apply,
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hr)]

private theorem chiInf_pos {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (u : (TR.Rinf E)ˣ)
    (hu : ∀ v, 0 < u.val v) :
    ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ := by
  have hc : ∀ v, Continuous fun u : (TR.Rinf E)ˣ => u.val v := fun v => (continuous_apply v).comp Units.continuous_val
  have ho : IsOpen {u : (TR.Rinf E)ˣ | ∀ v, 0 < u.val v} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (hc v)
  have hcl : IsClosed {u : (TR.Rinf E)ˣ |
      ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ} :=
    isClosed_eq (Units.continuous_val.comp (TR.continuous_chiInf χ)) (continuous_finsetProd _ fun φ _ =>
      (Complex.continuous_ofReal.comp (hc _)).zpow₀ _ fun u => Or.inl
        (Complex.ofReal_ne_zero.2 (TR.unit_ne_zero u _)))
  refine closure_minimal ?_ hcl (denseRange_unitsR.open_subset_closure_inter ho hu)
  rintro _ ⟨hk, k, rfl⟩
  have h1 := h k fun φ => by
    have h2 := hk (InfinitePlace.mk (Complex.ofRealHom.comp φ))
    have h3 := diagR_mk (Complex.ofRealHom.comp φ) (k : E)
    exact h2.trans_eq (Complex.ofReal_injective h3)
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR] at h1
  refine h1.trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ n φ) (diagR_mk φ (k : E)).symm

open Classical in
private noncomputable def negAt (v : InfinitePlace E) : (TR.Rinf E)ˣ :=
  Units.map (MonoidHom.mulSingle (fun _ : InfinitePlace E => ℝ) v) (-1)

private theorem infId_negAt (v : InfinitePlace E) : TR.infId E (negAt v) = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E v (-1) := by
  classical
  apply Units.ext
  refine Prod.ext ?_ ?_
  · change 1 - TR.infEq E 1 + TR.infEq E (Pi.mulSingle v (-1)) = Pi.mulSingle v (-1)
    rw [map_one, sub_self]
    refine (zero_add _).trans (funext fun w => ?_)
    change (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm
      ((Pi.mulSingle v (-1) : TR.Rinf E) w) = _
    by_cases h : w = v
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, map_neg, map_one]
    · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, map_one]
  · change (1 : Af E) - 0 + 0 = 1
    simp

private theorem bij_mk : Function.Bijective (InfinitePlace.mk : (E →+* ℂ) → InfinitePlace E) := by
  refine ⟨fun φ ψ h => ?_, fun w => ⟨w.embedding, w.mk_embedding⟩⟩
  rw [← InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ), h,
    InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal ψ)]

private theorem chiInf_all {χ : HChar E} {b : ℤ} (h : IsAlgPos χ fun _ => b)
    (hs : ∀ v : InfinitePlace E, χ.locInf v (-1) = (-1) ^ b) (u : (TR.Rinf E)ˣ) :
    ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ b := by
  classical
  let s : (TR.Rinf E)ˣ := ∏ v, if u.val v < 0 then negAt v else 1
  have h1 : ∀ w, s.val w = if u.val w < 0 then -1 else 1 := fun w => by
    simp only [s, Units.coe_prod, Finset.prod_apply]
    rw [Finset.prod_eq_single w _ fun hw => absurd (Finset.mem_univ w) hw]
    · split_ifs
      · exact Pi.mulSingle_eq_same (M := fun _ : InfinitePlace E => ℝ) w _
      · rfl
    · intro v _ hv
      split_ifs
      · exact Pi.mulSingle_eq_of_ne (M := fun _ : InfinitePlace E => ℝ) hv.symm _
      · rfl
  have h2 : ((TR.chiInf χ s : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((s.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ b := by
    rw [bij_mk.prod_comp fun w => ((s.val w : ℝ) : ℂ) ^ b]
    simp only [h1]
    simp only [s, map_prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    split_ifs
    · have e : TR.chiInf χ (negAt v) = χ.locInf v (-1) := congrArg χ.1 (infId_negAt v)
      rw [e, hs]
      simp
    · simp
  have h3 := chiInf_pos h (s * u) fun w => by
    change 0 < s.val w * u.val w
    rw [h1]
    split_ifs with hw
    · linarith
    · rw [one_mul]
      exact lt_of_le_of_ne (not_lt.1 hw) (TR.unit_ne_zero u w).symm
  rw [map_mul, Units.val_mul] at h3
  refine mul_left_cancel₀ (TR.chiInf χ s).ne_zero (h3.trans ?_)
  rw [h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun φ _ => ?_
  rw [← mul_zpow, ← Complex.ofReal_mul]
  rfl

end Real

theorem UpperTheory.heckeChar_algebraic_of_sign :
    UpperTheory.V.Af.Cr.AlgOfSign := by
  intro F _ _ _ χ b h hs k
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR]
  refine (chiInf_all h hs _).trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ b) (diagR_mk φ (k : F))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepValuesInFiniteExtension
theorem UpperTheory.galois_rep_values_in_finite_extension :
    UpperTheory.V.Af.Wd.FinVal := by
  intro F Ω C _ _ _ _ M hM χ hχ
  classical
  have hpos : 0 < M := by omega
  have hR : {ζ : Ω | ζ ^ M = 1}.Finite := by
    refine (Multiset.toFinset (Polynomial.nthRoots M (1 : Ω))).finite_toSet.subset ?_
    intro ζ hζ
    simpa [Polynomial.mem_nthRoots hpos] using hζ
  haveI : Finite {ζ : Ω | ζ ^ M = 1} := hR.to_subtype
  let π : (Ω ≃ₐ[F] Ω) → ({ζ : Ω | ζ ^ M = 1} → {ζ : Ω | ζ ^ M = 1}) := fun s ζ =>
    ⟨s ζ, by
      show (s ζ) ^ M = 1
      rw [← map_pow, show (ζ : Ω) ^ M = 1 from ζ.2, map_one]⟩
  have hfac : ∀ s t, π s = π t → χ s = χ t := by
    intro s t hst
    have h1 : χ (t⁻¹ * s) = 1 := by
      refine hχ _ (fun ζ hζ => ?_)
      have h := congrArg (fun f => (f ⟨ζ, hζ⟩ : Ω)) hst
      simp only [π] at h
      rw [AlgEquiv.mul_apply, h, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  refine (Set.finite_range (fun x : Set.range π => χ x.2.choose)).subset ?_
  rintro _ ⟨s, rfl⟩
  exact ⟨⟨π s, s, rfl⟩, hfac _ _ (⟨s, rfl⟩ : π s ∈ Set.range π).choose_spec⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharRealTransport
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
open ReciprocityTheory.Neutral.Bridge.HCFR

private theorem comap_surj {E L : Type} [Field E] [Field L] (j : E ≃+* L) (v' : InfinitePlace E) :
    ∃ v : InfinitePlace L, v.comap j.toRingHom = v' := by
  refine ⟨v'.comap j.symm.toRingHom, ?_⟩
  ext x
  show v' (j.symm (j x)) = v' x
  rw [RingEquiv.symm_apply_apply]

private theorem comap_inj {E L : Type} [Field E] [Field L] (j : E ≃+* L) (u v : InfinitePlace L)
    (h : u.comap j.toRingHom = v.comap j.toRingHom) : u = v := by
  ext x
  have h1 : (u.comap j.toRingHom) (j.symm x) = (v.comap j.toRingHom) (j.symm x) := by rw [h]
  change u (j (j.symm x)) = v (j (j.symm x)) at h1
  rwa [RingEquiv.apply_symm_apply] at h1

private theorem idMap_infIdele {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (j : E ≃+* L)
    (v : InfinitePlace L) :
    CT.idMap j (infIdele E (v.comap j.toRingHom) (-1)) = infIdele L v (-1) := by
  classical
  apply Units.ext
  apply Prod.ext
  · funext u
    show CT.infEquiv j u (Pi.mulSingle (M := fun w : InfinitePlace E => w.Completion) (v.comap j.toRingHom) (-1)
      (u.comap j.toRingHom)) = Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) v (-1) u
    by_cases h : u = v
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, map_neg, map_one]
    · have h' : u.comap j.toRingHom ≠ v.comap j.toRingHom := fun e => h (comap_inj j u v e)
      rw [Pi.mulSingle_eq_of_ne h', Pi.mulSingle_eq_of_ne h, map_one]
  · show CT.finMap j 1 = 1
    exact map_one _

theorem UpperTheory.heckeChar_realTransport :
    UpperTheory.V.Af.Cr.RealTransport := by
  intro F K _ _ _ _ _ _ _ h2 χ
  haveI : Algebra.IsQuadraticExtension F K := { finrank_eq_two' := h2 }
  let j : maximalRealSubfield K ≃+* F := (CMExtension.equivMaximalRealSubfield F K).symm
  refine ⟨CT.transport j χ, fun v' => ?_, fun w => ?_⟩
  · obtain ⟨v, rfl⟩ := comap_surj j v'
    refine ⟨v, ?_⟩
    show χ.1 (CT.idMap j (infIdele _ (v.comap j.toRingHom) (-1))) = χ.1 (infIdele F v (-1))
    rw [idMap_infIdele]
  · have hp : CT.plMap j (w.under (𝓞 (maximalRealSubfield K))) = w.under (𝓞 F) := by
      ext x
      show algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) ((RingOfIntegers.mapRingEquiv j).symm x) ∈ w.asIdeal ↔
        algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal
      have e : algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) ((RingOfIntegers.mapRingEquiv j).symm x) =
          algebraMap (𝓞 F) (𝓞 K) x := RingOfIntegers.ext rfl
      rw [e]
    refine ⟨?_, fun hu => ?_⟩
    · have h := CT.absNorm_plMap j (w.under (𝓞 (maximalRealSubfield K)))
      rw [hp, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h
      exact h.symm
    · rw [← hp] at hu
      refine ⟨(CT.transport_unrAt_iff j χ _).mpr hu, ?_⟩
      rw [CT.transport_val j χ _ hu, hp]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QuadraticComplexMultiplication
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

theorem UpperTheory.quadratic_complex_multiplication :
    UpperTheory.V.Af.Cr.QuadCM := by
  intro F Ω _ _ _ _ _ _ d δ hδ hd
  have halg : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral F δ := (halg.isAlgebraic δ).isIntegral
  let K : IntermediateField F Ω := IntermediateField.adjoin F {δ}
  haveI : FiniteDimensional F K := IntermediateField.adjoin.finiteDimensional hint
  haveI : NumberField K := NumberField.of_module_finite F K
  let y : K := IntermediateField.AdjoinSimple.gen F δ
  have hy : algebraMap K Ω y = δ := rfl
  have hy2 : y ^ 2 = algebraMap F K d := by
    apply (algebraMap K Ω).injective
    rw [map_pow, hy, hδ, ← IsScalarTower.algebraMap_apply]
  have hle : (minpoly F δ).natDegree ≤ 2 := by
    have hm : (X ^ 2 - C d : F[X]).Monic := monic_X_pow_sub_C d (by norm_num)
    have h1 := minpoly.min F δ hm (by simp [hδ])
    have h2 := natDegree_le_natDegree h1
    rwa [natDegree_X_pow_sub_C _] at h2
  have hne : (minpoly F δ).natDegree ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := (minpoly.natDegree_eq_one_iff).1 h
    have hcd : c ^ 2 = d := by
      apply (algebraMap F Ω).injective
      rw [map_pow, hc, hδ]
    let v : InfinitePlace F := Classical.arbitrary _
    have h3 := hd (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))
    rw [← hcd, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  have hpos := minpoly.natDegree_pos hint
  have hdeg : (minpoly F δ).natDegree = 2 := by omega
  have hrk : Module.finrank F K = 2 := by
    rw [← hdeg]; exact IntermediateField.adjoin.finrank hint
  haveI : IsTotallyComplex K := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have h3 := hd ((InfinitePlace.embedding_of_isReal hv).comp (algebraMap F K))
    rw [RingHom.comp_apply, ← hy2, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  haveI : Algebra.IsQuadraticExtension F K := { finrank_eq_two' := hrk }
  haveI : IsAlgClosure K Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed F
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := F) K }
  refine ⟨K, inferInstance, inferInstance, IsCMField.ofCMExtension F K, inferInstance, inferInstance,
    inferInstance, inferInstance, hrk, y, hy, fun x => ?_⟩
  obtain ⟨f, hf, hx⟩ := (IntermediateField.adjoin.powerBasis hint).exists_eq_aeval x
  rw [IntermediateField.adjoin.powerBasis_dim, hdeg] at hf
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  rw [hx, IntermediateField.adjoin.powerBasis_gen]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one (p := f) (by omega)]
  simp only [map_add (f := _), map_mul, aeval_C, aeval_X]
  exact add_comm _ _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CmInertiaRestrictionHolds
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

theorem UpperTheory.cm_inertia_restriction_holds : UpperTheory.V.Af.Cr.IneRes := by
  intro F₀ F Ω _ _ _ _ _ _ _ _ _ _
  classical
  unfold Ine IsPlaceOver Inertia
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have hint : ∀ (A : ValuationSubring Ω) (x : Ω), IsIntegral ℤ x → A.valuation x ≤ 1 := by
    intro A x h
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (h.tower_top : IsIntegral A x)
    exact A.valuation_le_one y
  obtain ⟨α₁, hα₁⟩ := Field.exists_primitive_element F₀ F
  have hα₁alg : IsAlgebraic ℤ α₁ :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (.of_finite ℚ α₁)
  obtain ⟨m, hm0, hmint⟩ := hα₁alg.exists_integral_multiple
  set α : F := m • α₁ with hαdef
  set g : Polynomial ℤ := minpoly ℤ α with hgdef
  set f : Polynomial F₀ := g.map (algebraMap ℤ F₀) with hfdef
  have hgmonic : g.Monic := minpoly.monic hmint
  have hfα : Polynomial.aeval α f = 0 := by
    rw [hfdef, Polynomial.aeval_map_algebraMap, hgdef, minpoly.aeval]
  have hfsep : f.Separable := by
    have h1 : (minpoly ℚ α).Separable := Algebra.IsSeparable.isSeparable ℚ α
    have h2 := h1.map (f := algebraMap ℚ F₀)
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hmint, Polynomial.map_map] at h2
    have h3 : (algebraMap ℚ F₀).comp (algebraMap ℤ ℚ) = algebraMap ℤ F₀ := RingHom.ext_int _ _
    rw [h3] at h2
    exact h2
  set c : F := Polynomial.aeval α (Polynomial.derivative f) with hcdef
  have hc0 : c ≠ 0 := hfsep.aeval_derivative_ne_zero hfα
  have hcint : IsIntegral ℤ c := by
    have h1 : c = Polynomial.aeval α (Polynomial.derivative g) := by
      rw [hcdef, hfdef, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]
    have key := Polynomial.aeval_algHom_apply (integralClosure ℤ F).val
      (⟨α, hmint⟩ : integralClosure ℤ F) (Polynomial.derivative g)
    rw [h1]
    refine key ▸ ?_
    exact (Polynomial.aeval (⟨α, hmint⟩ : integralClosure ℤ F) (Polynomial.derivative g)).2
  set d : F₀ := Algebra.norm F₀ c with hddef
  have hdint : IsIntegral ℤ d := Algebra.isIntegral_norm F₀ hcint
  have hd0 : d ≠ 0 := Algebra.norm_ne_zero_iff.mpr hc0
  set D : 𝓞 F₀ := ⟨d, hdint⟩ with hDdef
  have hD0 : D ≠ 0 := by
    intro h
    apply hd0
    exact congrArg (fun x : 𝓞 F₀ => (x : F₀)) h
  have hspan : Ideal.span {D} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hD0
  refine Filter.eventually_cofinite.mpr ((Ideal.finite_factors hspan).subset ?_)
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  by_contra hDv
  apply hv
  intro A hA σ hσ
  have hσ2 : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x) < 1 := hσ.2
  set α₀ : Ω := algebraMap F Ω α with hα₀def
  have h0 : Polynomial.aeval α₀ f = 0 := by
    rw [hα₀def, Polynomial.aeval_algebraMap_apply, hfα, map_zero]
  have hfix : σ α₀ = α₀ := by
    by_contra hne
    set fΩ : Polynomial Ω := f.map (algebraMap F₀ Ω) with hfΩ
    have hfΩ_monic : fΩ.Monic := (hgmonic.map _).map _
    have hfΩ0 : fΩ ≠ 0 := hfΩ_monic.ne_zero
    have hroot : ∀ y : Ω, Polynomial.aeval y f = 0 → y ∈ fΩ.roots := by
      intro y hy
      rw [Polynomial.mem_roots hfΩ0, Polynomial.IsRoot, hfΩ, Polynomial.eval_map_algebraMap]
      exact hy
    have hα₀root : α₀ ∈ fΩ.roots := hroot _ h0
    have hβroot : σ α₀ ∈ fΩ.roots := by
      apply hroot
      have := Polynomial.aeval_algHom_apply (σ : Ω ≃ₐ[F₀] Ω).toAlgHom α₀ f
      rw [h0, map_zero] at this
      exact this
    have hrootint : ∀ y ∈ fΩ.roots, IsIntegral ℤ y := by
      intro y hy
      refine ⟨g, hgmonic, ?_⟩
      rw [Polynomial.mem_roots hfΩ0, Polynomial.IsRoot, hfΩ, hfdef, Polynomial.map_map,
        ← Polynomial.eval₂_eq_eval_map] at hy
      have hZ : algebraMap ℤ Ω = (algebraMap F₀ Ω).comp (algebraMap ℤ F₀) := RingHom.ext_int _ _
      rw [hZ]
      exact hy
    have hder : algebraMap F Ω c = ((fΩ.roots.erase α₀).map (α₀ - ·)).prod := by
      rw [← (IsAlgClosed.splits fΩ).eval_root_derivative hfΩ_monic hα₀root]
      rw [hfΩ, Polynomial.derivative_map, Polynomial.eval_map_algebraMap, hcdef, hα₀def,
        Polynomial.aeval_algebraMap_apply]
    have hβmem : σ α₀ ∈ fΩ.roots.erase α₀ := (Multiset.mem_erase_of_ne hne).mpr hβroot
    have hcv : A.valuation (algebraMap F Ω c) < 1 := by
      rw [hder, ← Multiset.cons_erase hβmem, Multiset.map_cons, Multiset.prod_cons, Valuation.map_mul]
      have h1 : A.valuation (α₀ - σ α₀) < 1 := by
        rw [Valuation.map_sub_swap]
        exact hσ2 α₀ (hint A α₀ (hrootint α₀ hα₀root))
      have h2 : A.valuation (((fΩ.roots.erase α₀).erase (σ α₀)).map (α₀ - ·)).prod ≤ 1 := by
        apply hint
        apply IsIntegral.multiset_prod
        intro z hz
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
        exact (hrootint α₀ hα₀root).sub
          (hrootint y (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hy)))
      exact lt_of_le_of_lt (mul_le_of_le_one_right' h2) h1
    have hnorm := Algebra.norm_eq_prod_embeddings F₀ Ω c
    set φ₀ : F →ₐ[F₀] Ω := IsScalarTower.toAlgHom F₀ F Ω with hφ₀
    rw [← Finset.mul_prod_erase Finset.univ (fun φ : F →ₐ[F₀] Ω => φ c) (Finset.mem_univ φ₀)] at hnorm
    have hdv : A.valuation (algebraMap F₀ Ω d) < 1 := by
      rw [hddef, hnorm, Valuation.map_mul]
      have h2 : A.valuation (∏ φ ∈ Finset.univ.erase φ₀, φ c) ≤ 1 := by
        apply hint
        apply IsIntegral.prod
        intro φ _
        exact hcint.map φ.toRingHom.toIntAlgHom
      exact lt_of_le_of_lt (mul_le_of_le_one_right' h2) hcv
    exact hDv ((hA D).mp hdv)
  have hfix1 : σ (algebraMap F Ω α₁) = algebraMap F Ω α₁ := by
    have h : σ (algebraMap F Ω α) = algebraMap F Ω α := hfix
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
    simp only [hαdef, zsmul_eq_mul, map_mul, map_intCast] at h
    exact mul_left_cancel₀ (Int.cast_ne_zero.mpr hm0) h
  have hφ : ((σ : Ω ≃ₐ[F₀] Ω).toAlgHom).comp (IsScalarTower.toAlgHom F₀ F Ω) =
      IsScalarTower.toAlgHom F₀ F Ω := by
    have hadj : Algebra.adjoin F₀ {α₁} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic α₁), hα₁, IntermediateField.top_toSubalgebra]
    refine AlgHom.ext_of_adjoin_eq_top hadj ?_
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hfix1
  have hcomm : ∀ y : F, σ (algebraMap F Ω y) = algebraMap F Ω y := fun y => DFunLike.congr_fun hφ y
  refine ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[F₀] Ω).toRingEquiv) hcomm, ?_⟩
  ext x
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneFunctorExactness
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneDpstLeftExact
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.Pst.DpstMap

private theorem tensV_eq_rT {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V']
    [IsScalarTower ℚ_[l] LL V'] (f : V →ₗ[LL] V') (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f x = (f.restrictScalars ℚ_[l]).rTensor (Bst P) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem UpperTheory.weilDeligne_dpst_leftExact :
    UpperTheory.V.Af.Wd.DLeft := by
  intro l _ P K L V' V V'' _ _ _ _ _ _ _ _ _ _ _ _ ρ' ρ ρ'' f p hf hp hfi hex0
  have hex : Function.Exact (f.restrictScalars ℚ_[l]) (p.restrictScalars ℚ_[l]) := hex0
  have hexT := Module.Flat.rTensor_exact (Bst P) hex
  have hinj : Function.Injective ((f.restrictScalars ℚ_[l]).rTensor (Bst P)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hfi
  refine ⟨fun x y hxy => Subtype.ext (hinj ?_), fun y => ⟨fun hy => ?_, ?_⟩⟩
  · rw [← tensV_eq_rT, ← tensV_eq_rT]
    exact congrArg Subtype.val hxy
  · have h0 : tensV P p (y : V ⊗[ℚ_[l]] Bst P) = 0 := congrArg Subtype.val hy
    rw [tensV_eq_rT] at h0
    obtain ⟨z, hz⟩ := (hexT _).mp h0
    have hz' : tensV P f z = y := by rw [tensV_eq_rT]; exact hz
    obtain ⟨K', hK'⟩ := (mem_Dpst P ρ).mp y.2
    have hzD : z ∈ Dpst P ρ' := by
      refine (mem_Dpst P ρ').mpr ⟨K', fun g hg => hinj ?_⟩
      rw [← tensV_eq_rT, ← tensV_eq_rT, tensV_stRep P ρ' ρ f hf, hz', hK' g hg]
    exact ⟨⟨z, hzD⟩, Subtype.ext hz'⟩
  · rintro ⟨x, rfl⟩
    refine Subtype.ext ?_
    show tensV P p (tensV P f x.1) = 0
    rw [tensV_eq_rT, tensV_eq_rT]
    exact (hexT _).mpr ⟨x.1, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DpstRightExact
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.Pst.DpstMap

private theorem count_dims {F D' D D'' : Type} [Field F] [AddCommGroup D'] [Module F D'] [AddCommGroup D] [Module F D]
    [AddCommGroup D''] [Module F D''] (j : D' →ₗ[F] D) (q : D →ₗ[F] D'') (hj : Function.Injective j)
    (hex : Function.Exact j q) (a c : ℕ) (h' : Module.rank F D' ≤ a) (h'' : Module.rank F D'' ≤ c)
    (h : Module.rank F D = (a + c : ℕ)) :
    Module.rank F D' = a ∧ Module.rank F D'' = c ∧ Function.Surjective q := by
  haveI : FiniteDimensional F D' := Module.rank_lt_aleph0_iff.mp (h'.trans_lt (Cardinal.natCast_lt_aleph0))
  haveI : FiniteDimensional F D'' := Module.rank_lt_aleph0_iff.mp (h''.trans_lt (Cardinal.natCast_lt_aleph0))
  haveI : FiniteDimensional F D := Module.rank_lt_aleph0_iff.mp (h.le.trans_lt (Cardinal.natCast_lt_aleph0))
  rw [← finrank_eq_rank] at h' h'' h
  rw [← finrank_eq_rank, ← finrank_eq_rank]
  have e1 : finrank F D' ≤ a := Nat.cast_le.mp h'
  have e2 : finrank F D'' ≤ c := Nat.cast_le.mp h''
  have e3 : finrank F D = a + c := Nat.cast_injective h
  have e4 := q.finrank_range_add_finrank_ker
  have e5 : finrank F (LinearMap.ker q) = finrank F D' := by
    rw [LinearMap.exact_iff.mp hex, LinearMap.finrank_range_of_inj hj]
  have e6 : finrank F (LinearMap.range q) ≤ finrank F D'' := Submodule.finrank_le _
  refine ⟨by rw [show finrank F D' = a by omega], by rw [show finrank F D'' = c by omega], ?_⟩
  rw [← LinearMap.range_eq_top]
  exact Submodule.eq_top_of_finrank_eq (by omega)

private noncomputable def dmapUr {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL]
    [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'} {f : V →ₗ[LL] V'}
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) : DpstUr P ρ →ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ' where
  toFun := fun x => toUr P ρ' (dmap P hf ((toUr P ρ).symm x))
  map_add' := fun x y => by simp only [map_add (f := _)]
  map_smul' := fun c x => dmap_mulD P hf c ((toUr P ρ).symm x)

theorem UpperTheory.dpst_right_exact :
    UpperTheory.V.Af.Wd.DRight := by
  intro l _ K L V' V V'' _ _ _ _ _ _ _ _ _ _ _ _ _ ρ' ρ ρ'' f p hf hp hfi hps hex hV
  obtain ⟨hdom, hreg, -⟩ := GlobalTheory.Pst.stRegular l (UpperTheory.V.Loc.PP l) (UpperTheory.V.Loc.AIP l) (UpperTheory.V.Loc.tiedP l)
  haveI : FiniteDimensional ℚ_[l] ↥L.1 := L.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥L.1 V
  haveI : FiniteDimensional ℚ_[l] V' := Module.Finite.of_injective (f.restrictScalars ℚ_[l]) hfi
  haveI : FiniteDimensional ℚ_[l] V'' := Module.Finite.of_surjective (p.restrictScalars ℚ_[l]) hps
  obtain ⟨hdi, hdex⟩ := UpperTheory.weilDeligne_dpst_leftExact l (UpperTheory.V.Loc.PP l) K L V' V V'' ρ' ρ ρ'' f p hf hp hfi hex
  have h' := GlobalTheory.T.finrank_dpst_unramified_le_dim_representation (UpperTheory.V.Loc.PP l) hdom hreg ρ'
  have h'' := GlobalTheory.T.finrank_dpst_unramified_le_dim_representation (UpperTheory.V.Loc.PP l) hdom hreg ρ''
  have hsum : finrank ℚ_[l] V = finrank ℚ_[l] V' + finrank ℚ_[l] V'' := by
    have hexq : Function.Exact (f.restrictScalars ℚ_[l]) (p.restrictScalars ℚ_[l]) := hex
    have e4 := (p.restrictScalars ℚ_[l]).finrank_range_add_finrank_ker
    rw [LinearMap.exact_iff.mp hexq, LinearMap.finrank_range_of_inj (f := f.restrictScalars ℚ_[l]) hfi,
      LinearMap.range_eq_top.mpr (show Function.Surjective (p.restrictScalars ℚ_[l]) from hps), finrank_top] at e4
    omega
  have h : Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr (UpperTheory.V.Loc.PP l) ρ) = (finrank ℚ_[l] V' + finrank ℚ_[l] V'' : ℕ) := by
    rw [← hsum, finrank_eq_rank]; exact hV
  obtain ⟨r1, r2, r3⟩ := count_dims (dmapUr (UpperTheory.V.Loc.PP l) hf) (dmapUr (UpperTheory.V.Loc.PP l) hp) hdi hdex _ _ h' h'' h
  rw [finrank_eq_rank] at r1 r2
  exact ⟨r1, r2, r3⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneFunctorExact
open TensorProduct Module GlobalTheory.Pst GlobalTheory.Pst.DpstMap in
theorem UpperTheory.weilDeligne_functor_exact :
    UpperTheory.V.Af.Wd.LetterExact := by
  intro LL U D' D D'' F _ _ _ _ _ _ _ _ _ _ m' m m'' τ T S hT hS hex hsurj
  have hS' : Function.Surjective (S.baseChange F) := LinearMap.lTensor_surjective F hsurj
  have hex' : Function.Exact (T.baseChange F) (S.baseChange F) := lTensor_exact F hex hsurj
  have eT : ∀ y, letterLin m' m F τ T hT (letterQ m' F τ y) = letterQ m F τ (T.baseChange F y) := fun _ => rfl
  have eS : ∀ y, letterLin m m'' F τ S hS (letterQ m F τ y) = letterQ m'' F τ (S.baseChange F y) := fun _ => rfl
  have hker : letterKer m'' F τ ≤ (letterKer m F τ).map (S.baseChange F) := iSup_le fun c => by
    rintro _ ⟨y, rfl⟩
    obtain ⟨y, rfl⟩ := hS' y
    refine ⟨_, Submodule.mem_iSup_of_mem c ⟨y, rfl⟩, ?_⟩
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange F) (hS c)) y
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply] at this
    simp [this]
  refine ⟨fun y => ?_, fun y => ?_⟩
  · obtain ⟨y, rfl⟩ := letterQ_surjective m F τ y
    constructor
    · intro h
      rw [eS, ← LinearMap.mem_ker, ker_letterQ] at h
      obtain ⟨z, hz, hzy⟩ := hker h
      obtain ⟨w, hw⟩ := (hex' (y - z)).mp (by rw [map_sub, hzy, sub_self])
      refine ⟨letterQ m' F τ w, ?_⟩
      have hz0 : letterQ m F τ z = 0 := by
        rw [← LinearMap.mem_ker, ker_letterQ]; exact hz
      rw [eT, hw, map_sub, hz0, sub_zero]
    · rintro ⟨w, hw⟩
      obtain ⟨w, rfl⟩ := letterQ_surjective m' F τ w
      rw [← hw, eT, eS, hex'.apply_apply_eq_zero, map_zero]
  · obtain ⟨y, rfl⟩ := letterQ_surjective m'' F τ y
    obtain ⟨y, rfl⟩ := hS' y
    exact ⟨letterQ m F τ y, eS y⟩
end

open Module

private theorem finrank_add_of_exact {k A B C : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] [AddCommGroup C] [Module k C] [FiniteDimensional k A] [FiniteDimensional k B] (f : A →ₗ[k] B)
    (p : B →ₗ[k] C) (hp : Function.Surjective p) (hex : Function.Exact f p) :
    finrank k (LinearMap.ker f) + finrank k B = finrank k A + finrank k C := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker p
  rw [LinearMap.range_eq_top.mpr hp, finrank_top, LinearMap.exact_iff.mp hex] at h2
  omega

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.Pst.DpstMap in
theorem UpperTheory.weil_deligne_functor_exactness :
    UpperTheory.V.Af.Wd.WdExact := by
  intro l _ ι K L V' V V'' _ _ _ _ _ _ _ _ _ _ _ _ _ ρ' ρ ρ'' f p hf hp hfi hps hex hV
  obtain ⟨hV', hV'', hds⟩ := UpperTheory.dpst_right_exact l K L V' V V'' ρ' ρ ρ'' f p hf hp hfi hps hex hV
  obtain ⟨-, hde⟩ := UpperTheory.weilDeligne_dpst_leftExact l (UpperTheory.V.Loc.PP l) K L V' V V'' ρ' ρ ρ'' f p hf hp hfi hex
  haveI : FiniteDimensional ↥L.1 V' := FiniteDimensional.of_injective f hfi
  haveI : FiniteDimensional ↥L.1 V'' := Module.Finite.of_surjective p hps
  have key : Function.Exact (wdLin (UpperTheory.V.Loc.PP l) ι hf) (wdLin (UpperTheory.V.Loc.PP l) ι hp) ∧
      Function.Surjective (wdLin (UpperTheory.V.Loc.PP l) ι hp) :=
    letI := algC ι L
    UpperTheory.weilDeligne_functor_exact _ _ _ _ _ ℂ (mulD (UpperTheory.V.Loc.PP l) ρ') (mulD (UpperTheory.V.Loc.PP l) ρ) (mulD (UpperTheory.V.Loc.PP l) ρ'') (urC ι)
      (dmap (UpperTheory.V.Loc.PP l) hf) (dmap (UpperTheory.V.Loc.PP l) hp) _ _ hde hds
  refine ⟨hV', hV'', ?_, key.2, key.1⟩
  haveI := hV.finite
  haveI := hV'.finite
  have h1 := finrank_add_of_exact _ _ key.2 key.1
  have h2 := finrank_add_of_exact f p hps hex
  rw [LetterDim.finrank_wdSpace l _ ι K L V ρ hV, LetterDim.finrank_wdSpace l _ ι K L V' ρ' hV',
    LetterDim.finrank_wdSpace l _ ι K L V'' ρ'' hV''] at h1
  rw [LinearMap.ker_eq_bot.mpr hfi, finrank_bot] at h2
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RankCohHomOfRankHomology
open CategoryTheory in
theorem UpperTheory.rankCohHom_of_rankHomology :
    UpperTheory.V.Af.CohB.RankHomology → UpperTheory.V.Af.BA.RankCohHom := by
  intro hR Γ _ P q X hX A
  obtain ⟨i⟩ := hX
  rw [(groupCohomologyIsoExt A q ≪≫ P.isoExt q A).toLinearEquiv.rank_eq]
  refine (hR _ q).trans ?_
  rw [ChainComplex.linearYonedaObj_X]
  exact (Linear.homCongr ℂ i (Iso.refl A)).rank_eq.le
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RealSpanOfGoodRealForm
open UpperTheory.V UpperTheory.V.KT UpperTheory.V.Af.BA in
theorem UpperTheory.real_span_of_good_real_form :
    UpperTheory.V.Af.BA.RePart → UpperTheory.V.Af.BA.ReInv → UpperTheory.V.Af.BA.GoodRe → UpperTheory.V.Af.BA.SpanRe := by
  intro hRP hRI hG L _ _ _ N σ hσ p t ht
  apply spanpsd
  intro k hk hzero
  obtain ⟨k', hk'q, hk'P⟩ := hRP L N σ hσ k
  obtain ⟨hk'psd, hk'0⟩ := hk'P hk
  apply hk'0
  refine ConeExtensionAcyclic.simp_span (hG L N σ hσ).locFin p t ht k' hk'psd ?_
  intro y hy
  have hM : ∀ (j : Fin (p + 1)), q (((t j : HR L N)) : HS L N) (y : Lat L N) = 1 := by
    intro j
    have := hy j
    rw [qr_apply] at this
    exact this
  have hinvq : ∀ (j : Fin (p + 1)), q (((t j : HR L N)) : HS L N) (sLat σ (y : Lat L N)) = 1 := by
    intro j
    rw [((hRI L N σ hσ).2 _ (t j).1.2).1 (y : Lat L N)]
    exact hM j
  rw [qr_apply, hk'q, hzero _ hM, hzero _ hinvq]
  norm_num
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepBoundedOfDegreeBounded
private theorem UpperTheory.cardinal_sum_eq_finite_sum_range (N : ℕ) : ∀ f : ℕ → Cardinal.{0}, (∀ q, N ≤ q → f q = 0) →
    Cardinal.sum f = ∑ q ∈ Finset.range N, f q := by
  induction N with
  | zero =>
    intro f hf
    have hf0 : f = fun _ => 0 := funext fun q => hf q (Nat.zero_le q)
    subst hf0
    rw [Cardinal.sum_const', mul_zero, Finset.sum_range_zero]
  | succ N ih =>
    intro f hf
    rw [Cardinal.sum_nat_eq_add_sum_succ, ih (fun i => f (i+1)) (fun q hq => hf (q+1) (by omega)),
      Finset.sum_range_succ', add_comm]

theorem UpperTheory.adelic_rep_bounded_of_degree_bounded :
    UpperTheory.V.Af.BA.BddOfDeg := by
  unfold UpperTheory.V.Af.BA.BddOfDeg
  intro Γ _ hc hD
  choose c hc using hc
  obtain ⟨D, hD⟩ := hD
  unfold UpperTheory.V.Af.CohB.Bdd
  refine ⟨∑ q ∈ Finset.range D, c q, fun A => ?_⟩
  unfold UpperTheory.V.Af.CohB.totCoh
  rw [UpperTheory.cardinal_sum_eq_finite_sum_range D _ (fun q hq => hD q hq A), Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun q _ => hc q A
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BoundedComplexOfBoundedSimplicialComplex
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.SxExact
open NumberField UpperTheory.V

theorem UpperTheory.V.ConeExtensionAcyclic.sx_exact (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N m : ℕ) :
    KH.FaceExactTo (KT.Sx L N) (KT.Sx.face L N) m :=
  have h := ConeExtensionAcyclic.acyc_simp (KT.good L N)
  KT.faceexact _ _ h.1 h.2.1 h.2.2 m
end

open NumberField UpperTheory.V UpperTheory.V.Af.BA

private noncomputable def cxK (L : Type) [Field L] [NumberField L] (N : ℕ) : Cx (KT.Gm L N) (KT.Vx L N) where
  S := ConeExtensionAcyclic.simp (KT.qc L N) (KT.Psd L N)
  comp := fun f t ht => by
    obtain ⟨y, hy, h⟩ := ht
    exact ⟨y, hy, fun j => h (f j)⟩
  smul := fun g t ht => KT.smul_mem_simp g ht

theorem UpperTheory.bounded_complex_of_bounded_simplicial_complex :
    UpperTheory.V.Af.BA.BddCx → UpperTheory.V.Af.BA.BddComplex := by
  intro H L _ _ _ N
  refine H (KT.Gm L N) (KT.Vx L N) (cxK L N) (fun m => ConeExtensionAcyclic.sx_exact L N m) (fun p => ?_) (fun t => ?_)
  · haveI : Finite (MulAction.orbitRel.Quotient (KT.Gm L N) ((cxK L N).Tup p)) := (KT.orb L N p).1
    refine ⟨Set.range (fun c : MulAction.orbitRel.Quotient (KT.Gm L N) ((cxK L N).Tup p) => Quotient.out c),
      Set.finite_range _, fun x => ?_⟩
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.1
      (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel (KT.Gm L N) ((cxK L N).Tup p)) x)))
    exact ⟨g, _, hg.symm⟩
  · haveI := KT.stabfin L N (t.1 0)
    refine Finite.of_injective (fun g : MulAction.stabilizer (KT.Gm L N) t =>
      (⟨g.1, congrFun (congrArg Subtype.val g.2) 0⟩ : MulAction.stabilizer (KT.Gm L N) (t.1 0))) fun g k e => ?_
    exact Subtype.ext (Subtype.mk.inj e)
end
