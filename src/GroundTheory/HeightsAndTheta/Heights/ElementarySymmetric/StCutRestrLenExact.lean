module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumCut
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOrdFiniteNonZeroDivisor
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseComap
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZFamily
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.StatementsGluing
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PGeoNumCut
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogIdealChain
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StCutRestrLenExact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def CutRestrLenExact.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (e : ℕ) (pp : Ideal (Poly k N)) (Lc : LineBundle k x) (s : Ω),
      IsSubvar x pp e → s ∈ Lc.secs → (∃ I, s ∉ (Lc.twist (idealSys x pp)).sub I) →
      ∀ Q : LineBundle k x, ∀ᶠ c : ℕ in atTop,
        restrLen pp ((Q.toSubSystem.twist Lc.toSubSystem).twist (twistSys k x (c : ℤ))) -
            restrLen pp (Q.toSubSystem.twist (twistSys k x (c : ℤ))) =
          restrLen (pp ⊔ zeroIdeal Lc.toSubSystem s)
            ((Q.toSubSystem.twist Lc.toSubSystem).twist (twistSys k x (c : ℤ)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PIntegralIndep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem IntegralIndep.closed : IntegralIndep.Statement :=
  IntegralIndep.proof
    (PosPartIndep.proof
      (SheetOnlyNull.proof IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof
        IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.proof)
      PosPartLocal.proof PosPartSplit.proof)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSubFamilyTwistX
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

section

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]


omit [Module S E] [IsScalarTower S Ω E] in
theorem SubSystem.twist_sub_fg (F : SubSystem S x E) (Q : SubSystem S x Ω) (I : Chart x)
    (hF : (F.sub I).FG) (hQ : (Q.sub I).FG) : ((F.twist Q).sub I).FG := by
  obtain ⟨sF, hsF⟩ := hF
  obtain ⟨sQ, hsQ⟩ := hQ
  classical
  refine ⟨Finset.image₂ (fun q y => q • y) sQ sF, ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    rw [Finset.coe_image₂] at hz
    obtain ⟨q, hq, y, hy, rfl⟩ := hz
    exact Submodule.subset_span ⟨q, hsQ ▸ Submodule.subset_span hq, y, hsF ▸ Submodule.subset_span hy, rfl⟩
  · change Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨q, hq, y, hy, rfl⟩
    rw [← hsQ] at hq
    rw [← hsF] at hy
    refine Submodule.span_induction (p := fun q _ => q • y ∈
      Submodule.span (chartRing S x I) ((Finset.image₂ (fun q y => q • y) sQ sF : Finset E) : Set E)) ?_ ?_ ?_ ?_ hq
    · intro q hq
      refine Submodule.span_induction (p := fun y _ => q • y ∈
        Submodule.span (chartRing S x I) ((Finset.image₂ (fun q y => q • y) sQ sF : Finset E) : Set E)) ?_ ?_ ?_ ?_ hy
      · intro y hy
        exact Submodule.subset_span (by rw [Finset.coe_image₂]; exact ⟨q, hq, y, hy, rfl⟩)
      · rw [smul_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
      · intro a z _ hz
        rw [Subalgebra.smul_def, smul_comm]
        exact Submodule.smul_mem _ a hz
    · rw [zero_smul]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [add_smul]; exact Submodule.add_mem _ ha hb
    · intro a q _ hq
      rw [smul_assoc]
      exact Submodule.smul_mem _ a hq

end

theorem SubFamilyTwist.proof : SubFamilyTwist.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F Q hF
  exact ⟨F.twistFam Q.toSubFamily, rfl, fun I =>
    SubSystem.twist_sub_fg F.toSubSystem Q.toSubSystem I (hF I) (Q.fg I)⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.InterSumEventuallyEqInterNum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Symmetry

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem tensorSub_eq_foldl_map {n : ℕ} (L : Fin n → SubSystem S x Ω) (T : Finset (Fin n)) :
    tensorSub L T = (((List.finRange n).filter (· ∈ T)).map L).foldl
      (fun F Q => F.twist Q) (twistSys S x 0) := by
  unfold tensorSub
  rw [List.foldl_map]

theorem tensorSub_comp_perm {n : ℕ} (L : Fin n → SubSystem S x Ω) (σ : Equiv.Perm (Fin n))
    (T : Finset (Fin n)) :
    tensorSub (fun i => L (σ i)) T = tensorSub L (T.map σ.toEmbedding) := by
  rw [tensorSub_eq_foldl_map, tensorSub_eq_foldl_map]
  have hp : (((List.finRange n).filter (· ∈ T)).map σ).Perm
      ((List.finRange n).filter (· ∈ T.map σ.toEmbedding)) := by
    rw [List.perm_ext_iff_of_nodup (((List.nodup_finRange n).filter _).map σ.injective)
      ((List.nodup_finRange n).filter _)]
    intro a
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      Finset.mem_map_equiv]
    constructor
    · rintro ⟨b, hb, rfl⟩
      simpa using hb
    · intro ha
      exact ⟨σ.symm a, ha, by simp⟩
  have hfun : (fun i => L (σ i)) = L ∘ σ := rfl
  rw [hfun, ← List.map_map]
  exact (hp.map L).foldl_eq' (fun F _ P _ Q => by
    rw [SubSystem.twist_assoc, SubSystem.twist_comm F, ← SubSystem.twist_assoc]) _

theorem interSum_comp_perm (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    (σ : Equiv.Perm (Fin n)) (c : ℕ) :
    interSum pp (fun i => L (σ i)) c = interSum pp L c := by
  unfold interSum
  refine Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ fun T => ?_
  rw [Equiv.finsetCongr_apply, Finset.card_map, tensorSub_comp_perm]

theorem interNum_comp_perm (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    (σ : Equiv.Perm (Fin n)) :
    interNum pp (fun i => L (σ i)) = interNum pp L := by
  unfold interNum
  congr 1
  funext c
  exact interSum_comp_perm pp L σ c

theorem interSum_eventually_eq_interNum (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    {m : ℤ} (h : ∀ᶠ c : ℕ in atTop, interSum pp L c = m) :
    ∀ᶠ c : ℕ in atTop, interSum pp L c = interNum pp L := by
  have ht : Tendsto (interSum pp L) atTop (nhds m) :=
    tendsto_const_nhds.congr' (h.mono fun _ hc => hc.symm)
  have hm : interNum pp L = m := ht.limUnder_eq
  rw [hm]
  exact h

end Symmetry

theorem GenericPointSectionInput.proof (hE : InterNumEventual.Statement.{u, w})
    (hA : InterNumAdditive.Statement.{u, w}) (hC : InterNumCut.Statement.{u, w})
    (hP : InterNumPointDeg.Statement.{u, w}) : GenericPointSectionInput.Statement.{u, w} := by
  intro k _ Ω _ _ N x
  refine ⟨fun n pp L hW => ?_, fun n pp L σ _ => ?_, fun n pp L i L' L'' hW => ?_,
    fun n pp L Lc s hW hs hne => ?_, fun pp hW => ?_⟩
  · obtain ⟨m, hm⟩ := hE k Ω N x n pp L hW
    exact interSum_eventually_eq_interNum pp _ hm
  · exact interNum_comp_perm pp (fun i => (L i).toSubSystem) σ
  · exact hA k Ω N x n pp L i L' L'' hW
  · exact hC k Ω N x n pp L Lc s hW hs hne
  · exact hP k Ω N x pp hW

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PVeryAmpleZTwistX
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem VeryAmpleZTwist.proof_closed : VeryAmpleZTwist.Statement.{u, v, w} :=
  VeryAmpleZTwist.proof VeryAmpleZFamily.proof

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNefAddBlock
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

namespace NefAddBlock

section Reduction

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (p : ℕ) [Fact p.Prime]


theorem map_red {W : Ideal (Geo.MRing ι)} (hW : Geo.IsMultiProjPrime W)
    (hpW : (C (p : ℤ) : Geo.MRing ι) ∈ W) (n : ℕ)
    (hdim : ringKrullDim (Geo.MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    NumbersDVR.IsMultiProjPrime (W.map (Bridge.GeoNum.red p)) ∧
      FieldNumbers.relDim (W.map (Bridge.GeoNum.red p)) = ((n : ℕ) : WithBot (WithTop ℤ)) := by
  have hker : RingHom.ker (Bridge.GeoNum.red (ι := ι) p) ≤ W := by
    rw [Bridge.GeoNum.ker_red, Ideal.span_le, Set.singleton_subset_iff]
    exact hpW
  have hcm : (W.map (Bridge.GeoNum.red p)).comap (Bridge.GeoNum.red p) = W :=
    Bridge.GeoNum.comap_map_eq p hker
  have : W.IsPrime := hW.1
  refine ⟨⟨Ideal.map_isPrime_of_surjective (Bridge.GeoNum.red_surjective p) hker, ?_, ?_⟩, ?_⟩
  · rw [Bridge.isMultiHomogIdeal_iff]
    obtain ⟨S, hS, hWS⟩ := hW.2.1
    refine ⟨Bridge.GeoNum.red p '' S, ?_, by rw [hWS, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨b, hb⟩ := hS f hf
    exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [← Bridge.GeoNum.isRelevant_comap_iff p, hcm]
    exact hW.2.2
  · rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, ← hdim]
    have := ringKrullDim_eq_of_ringEquiv (Bridge.GeoNum.quotEquiv p (W.map (Bridge.GeoNum.red p)))
    rw [hcm] at this
    exact this.symm

end Reduction

end NefAddBlock

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumPointDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace InterNumPointDeg

variable {k : Type u} [Field k] {N : ℕ}

abbrev OneRing (k : Type u) [Field k] (N : ℕ) : Type u := NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k

abbrev coneField (P : Ideal (OneRing k N)) [P.IsPrime] : Type u := FractionRing (OneRing k N ⧸ P)

instance small_coneField [Small.{w} k] (P : Ideal (OneRing k N)) [P.IsPrime] : Small.{w} (coneField P) := by
  have : Small.{w} (OneRing k N ⧸ P) := small_of_surjective Ideal.Quotient.mk_surjective
  refine small_of_surjective (α := (OneRing k N ⧸ P) × nonZeroDivisors (OneRing k N ⧸ P))
    (f := fun z => IsLocalization.mk' (coneField P) z.1 z.2) fun z => ?_
  obtain ⟨q, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (OneRing k N ⧸ P)) z
  exact ⟨q, rfl⟩

variable [Small.{w} k] (pp : Ideal (Poly k N)) [pp.IsPrime]

def coneHom : OneRing k N →ₐ[k] Shrink.{w} (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom)) :=
  (Shrink.algEquiv k _).symm.toAlgHom.comp
    ((IsScalarTower.toAlgHom k (OneRing k N ⧸ pp.comap (oneBlock (S := k) (N := N)).toRingHom) _).comp
      (Ideal.Quotient.mkₐ k (pp.comap (oneBlock (S := k) (N := N)).toRingHom)))

def pt : Fin (N + 1) → Shrink.{w} (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom)) :=
  fun i => coneHom pp (X ⟨(), i⟩)

theorem coneHom_eq_zero_iff (f : OneRing k N) :
    coneHom.{u, w} pp f = 0 ↔ oneBlock (S := k) (N := N) f ∈ pp := by
  show (Shrink.algEquiv k (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom))).symm
    (algebraMap _ (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom)) (Ideal.Quotient.mk (pp.comap (oneBlock (S := k) (N := N)).toRingHom) f)) = 0 ↔ _
  rw [map_eq_zero_iff _ (AlgEquiv.injective _), IsFractionRing.to_map_eq_zero_iff,
    Ideal.Quotient.eq_zero_iff_mem]
  rfl

theorem aeval_pt_oneBlock (f : OneRing k N) :
    aeval (pt.{u, w} pp) (oneBlock (S := k) (N := N) f) = coneHom pp f := by
  rw [← AlgHom.comp_apply]
  refine congrFun (congrArg DFunLike.coe (MvPolynomial.algHom_ext fun v => ?_)) f
  rcases v with ⟨⟨⟩, i⟩
  rw [AlgHom.comp_apply]
  show aeval (pt.{u, w} pp) (rename (fun v : Σ _ : Unit, Fin (N + 1) => v.2) (X ⟨(), i⟩)) = _
  rw [rename_X, aeval_X]
  rfl

theorem oneBlock_surjective (f : Poly k N) :
    oneBlock (S := k) (N := N) (rename (HilbertPositive.blockEquiv N).symm f) = f := by
  rw [oneBlock, rename_rename]
  exact (congrArg (fun g => rename g f) (HilbertPositive.blockEquiv N).self_comp_symm).trans (rename_id_apply f)

theorem aeval_pt_eq_zero_iff (f : Poly k N) : aeval (pt.{u, w} pp) f = 0 ↔ f ∈ pp := by
  rw [← oneBlock_surjective f, aeval_pt_oneBlock, coneHom_eq_zero_iff]

theorem primeOf_pt (hh : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) :
    primeOf (S := k) (pt.{u, w} pp) = pp := by
  ext f
  constructor
  · intro hf
    rw [← sum_homogeneousComponent f]
    refine Ideal.sum_mem _ fun d _ => ?_
    exact (aeval_pt_eq_zero_iff pp _).1 ((mem_primeOf_of_isHomogeneous _
      (homogeneousComponent_isHomogeneous d f)).1 (homogeneousComponent_mem_primeOf _ hf d))
  · intro hf
    rw [← sum_homogeneousComponent f]
    exact Ideal.sum_mem _ fun d _ => (mem_primeOf_of_isHomogeneous _
      (homogeneousComponent_isHomogeneous d f)).2 ((aeval_pt_eq_zero_iff pp _).2 (hh f hf d))

theorem isHomogeneous_oneBlock {f : OneRing k N} {b : Unit → ℕ} (hf : NumbersDVR.IsMultiHomog f b) :
    (oneBlock (S := k) (N := N) f).IsHomogeneous (b ()) := by
  have h1 : f.IsHomogeneous (b ()) := by
    intro d hd
    have := congrFun (hf hd) ()
    rw [HilbertPositive.weight_blockWeight_one] at this
    show Finsupp.weight (fun _ => 1) d = b ()
    rw [← Finsupp.degree_eq_weight_one]
    exact this
  exact h1.rename_isHomogeneous

theorem finrank_funField_pt (hrel : ∃ i, (X i : Poly k N) ∉ pp) :
    Module.finrank k (funField (k := k) (pt.{u, w} pp)) =
      FieldNumbers.resDeg (pp.comap (oneBlock (S := k) (N := N)).toRingHom) := by
  set P := pp.comap (oneBlock (S := k) (N := N)).toRingHom
  have hΦ : ∀ f : OneRing k N, (Shrink.algEquiv k (coneField P)).symm
      (algebraMap (OneRing k N ⧸ P) (coneField P) (Ideal.Quotient.mk P f)) =
        aeval (pt.{u, w} pp) (oneBlock (S := k) (N := N) f) := fun f => by
    rw [aeval_pt_oneBlock]; rfl
  obtain ⟨i, hi⟩ := hrel
  have hyi : pt.{u, w} pp i ≠ 0 := by
    rw [← aeval_X (R := k) (pt.{u, w} pp) i, Ne, aeval_pt_eq_zero_iff]; exact hi
  have hmap : (FieldNumbers.homFracDegZero P).map (Shrink.algEquiv k (coneField P)).symm.toAlgHom =
      funField (k := k) (pt.{u, w} pp) := by
    rw [FieldNumbers.homFracDegZero, IntermediateField.adjoin_map]
    refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_) (IntermediateField.adjoin_le_iff.mpr ?_)
    · rintro _ ⟨_, ⟨b, f, g, hf, hg, hgP, rfl⟩, rfl⟩
      have hF := isHomogeneous_oneBlock hf
      have hG := isHomogeneous_oneBlock hg
      have hchart : ∀ (F : Poly k N), F.IsHomogeneous (b ()) →
          aeval (pt.{u, w} pp) F / pt.{u, w} pp i ^ b () ∈ funField (k := k) (pt.{u, w} pp) := fun F hF' =>
        VeryAmpleDim.mem_funField_of_mem_chartRing hyi ⟨F, X i ^ b (), b (), pow_mem (X_mem_monos
          (Finset.mem_singleton_self i)) _, hF', isHomogeneous_X_pow _ _, by rw [map_pow, aeval_X]⟩
      convert IntermediateField.div_mem _ (hchart _ hF) (hchart _ hG) using 1
      rw [div_div_div_cancel_right₀ (pow_ne_zero (b ()) hyi), ← hΦ, ← hΦ, map_div₀]
      rfl
    · rintro _ ⟨j, l, hj, rfl⟩
      apply IntermediateField.subset_adjoin
      have hjP : (X (⟨(), j⟩ : Σ _ : Unit, Fin (N + 1)) : OneRing k N) ∉ P := by
        change oneBlock (S := k) (N := N) (X (⟨(), j⟩ : Σ _ : Unit, Fin (N + 1))) ∉ pp
        rw [← aeval_pt_eq_zero_iff, aeval_pt_oneBlock]; exact hj
      refine ⟨_, ⟨NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1)) ⟨(), l⟩, X ⟨(), l⟩, X ⟨(), j⟩,
        isWeightedHomogeneous_X k _ _,
        isWeightedHomogeneous_X k _ _, hjP, rfl⟩, ?_⟩
      simp only [AlgEquiv.coe_toAlgHom, AlgHom.coe_coe, map_div₀, hΦ, aeval_pt_oneBlock]
      rfl
  unfold FieldNumbers.resDeg
  rw [dite_eq_left (inferInstance : P.IsPrime), ← hmap]
  exact ((FieldNumbers.homFracDegZero P).equivMap _).toLinearEquiv.finrank_eq.symm

end InterNumPointDeg

theorem InterNumPointDeg.proof (hIR : InterNumRestrict.Statement.{u, w}) : InterNumPointDeg.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp h
  haveI : Small.{w} k := small_of_injective (algebraMap k Ω).injective
  haveI := h.isPrime
  have hpt := InterNumPointDeg.primeOf_pt.{u, w} pp h.homog
  have hsub : IsSubvar (InterNumPointDeg.pt.{u, w} pp) pp 0 := ⟨h.isPrime, h.homog, hpt.le, h.relevant, h.dim⟩
  have hxy : ∀ i, InterNumPointDeg.pt.{u, w} pp i ≠ 0 → x i ≠ 0 := by
    intro i hi hx
    apply hi
    rw [← aeval_X (R := k) (InterNumPointDeg.pt.{u, w} pp) i, InterNumPointDeg.aeval_pt_eq_zero_iff]
    exact h.le ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i)).2 (by rw [aeval_X, hx]))
  have h1 := hIR k Ω N x _ (InterNumPointDeg.pt.{u, w} pp) hxy (hpt.symm ▸ h.le) pp 0 hsub
    Fin.elim0 Fin.elim0 Fin.elim0 (fun i => i.elim0)
  have h2 := InterNumPoint.proof HilbertPoint.proof k _ N (InterNumPointDeg.pt.{u, w} pp)
    (hpt.symm ▸ hsub) ![]
  rw [hpt] at h2
  calc interNum pp (![] : Fin 0 → SubSystem k x Ω)
      = interNum pp (fun i : Fin 0 => (Fin.elim0 i : LineBundle k x).toSubSystem) :=
        congrArg _ (Subsingleton.elim _ _)
    _ = _ := h1.symm
    _ = interNum pp (![] : Fin 0 → SubSystem k (InterNumPointDeg.pt.{u, w} pp) _) :=
        congrArg _ (Subsingleton.elim _ _)
    _ = _ := h2
    _ = _ := by rw [InterNumPointDeg.finrank_funField_pt pp h.relevant]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBranchChartIntX
section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchChartInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace BranchChartInt

theorem analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

theorem differentiable_mulVec {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) :=
  (Matrix.mulVecLin A).toContinuousLinearMap.differentiable


open Classical in
theorem chartDens_indicator_image {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {p : Fin n → ℂ} (γ : VarBranch J d p) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (y : Fin d → ℂ) :
    chartDens J A (γ.image.indicator g) φ y =
      ∑ᶠ t ∈ {t | t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius ∧ A *ᵥ γ.toFun t = y},
        (if h : ∃ s, IsSheetAt J A (γ.toFun t) s then
          g (γ.toFun t) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ γ.toFun t) else 0) := by
  set T : (Fin n → ℂ) → ℝ := fun x => if h : ∃ s, IsSheetAt J A x s then
      γ.image.indicator g x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y else 0 with hT
  have h1 : chartDens J A (γ.image.indicator g) φ y = ∑ᶠ x ∈ ComplexSets.fibre J A y, T x := rfl
  have h2 : ∑ᶠ x ∈ ComplexSets.fibre J A y, T x =
      ∑ᶠ x ∈ γ.toFun '' {t | t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius ∧ A *ᵥ γ.toFun t = y}, T x := by
    apply finsum_mem_inter_support_eq
    ext x
    simp only [Set.mem_inter_iff, Function.mem_support]
    constructor
    · rintro ⟨hx, hTx⟩
      have hxi : x ∈ γ.image := by
        by_contra hni
        apply hTx
        simp only [hT, Set.indicator_of_notMem hni, zero_mul, dite_eq_ite, ite_self]
      obtain ⟨t, ht, rfl⟩ := hxi
      exact ⟨⟨t, ⟨ht, hx.2⟩, rfl⟩, hTx⟩
    · rintro ⟨⟨t, ⟨ht, hty⟩, rfl⟩, hTx⟩
      exact ⟨⟨γ.mapsTo ht, hty⟩, hTx⟩
  have hinj : Set.InjOn γ.toFun {t | t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius ∧ A *ᵥ γ.toFun t = y} :=
    γ.injOn.mono (by intro t ht; exact ht.1)
  rw [h1, h2, finsum_mem_image hinj]
  refine finsum_mem_congr rfl fun t ht => ?_
  have hti : γ.toFun t ∈ γ.image := ⟨t, ht.1, rfl⟩
  simp only [hT, Set.indicator_of_mem hti, ht.2]

theorem maDens_branch_eq {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {p : Fin n → ℂ} (γ : VarBranch J d p) {φ : Fin d → (Fin n → ℂ) → ℝ}
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k)) {t : Fin d → ℂ} (ht : t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius)
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A (γ.toFun t) s) :
    ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t =
      ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (A *ᵥ γ.toFun t) *
        Complex.normSq (jacC (fun t => A *ᵥ γ.toFun t) t).det := by
  obtain ⟨U, hUo, hxU, hsd, hsx, -, V, hV, hVeq⟩ := hs
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun t => A *ᵥ γ.toFun t with hτ
  have hτd : DifferentiableOn ℂ τ (Metric.ball 0 γ.radius) :=
    (differentiable_mulVec A).comp_differentiableOn γ.differentiableOn
  have hτa : AnalyticAt ℂ τ t := analyticOnNhd_of_differentiableOn Metric.isOpen_ball hτd t ht
  have hΔ : Metric.ball (0 : Fin d → ℂ) γ.radius ∈ 𝓝 t := Metric.isOpen_ball.mem_nhds ht
  have hγc : ContinuousAt γ.toFun t := γ.differentiableOn.continuousOn.continuousAt hΔ
  have hev : ∀ k, φ k ∘ γ.toFun =ᶠ[𝓝 t] (φ k ∘ s) ∘ τ := by
    intro k
    filter_upwards [hΔ, hγc.preimage_mem_nhds hV,
      hτa.continuousAt.preimage_mem_nhds (hUo.mem_nhds hxU)] with t' ht' hV' hU'
    simp only [Function.comp_apply]
    rw [← hVeq (γ.toFun t') ⟨γ.mapsTo ht', hV'⟩ hU']
  have hmd : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t =
      ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) t := by
    unfold ReciprocityTheory.AnForm.maDens
    congr 3
    funext k
    have h2 : fderiv ℝ (fderiv ℝ (φ k ∘ γ.toFun)) t = fderiv ℝ (fderiv ℝ ((φ k ∘ s) ∘ τ)) t :=
      ((hev k).fderiv (𝕜 := ℝ)).fderiv_eq
    unfold ReciprocityTheory.AnForm.hessC
    rw [h2]
  have hsa : AnalyticAt ℂ s (τ t) := analyticOnNhd_of_differentiableOn hUo hsd (τ t) hxU
  have hc : ∀ k, ContDiffAt ℝ 2 (φ k ∘ s) (τ t) := by
    intro k
    obtain ⟨O, hOo, hZO, hφO⟩ := hφ k
    have hmem : s (τ t) ∈ O := by
      rw [show s (τ t) = γ.toFun t from hsx]
      exact hZO (γ.mapsTo ht)
    exact ((hφO.contDiffAt (hOo.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top)).comp (τ t)
      (hsa.contDiffAt.restrict_scalars ℝ)
  rw [hmd]
  exact maDens_comp (fun k => φ k ∘ s) τ t hτa hc

theorem integrableOn_branch {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (γ : VarBranch J d p) {g : (Fin n → ℂ) → ℝ} {φ : Fin d → (Fin n → ℂ) → ℝ} (hg : Continuous g)
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k))
    (hK : ∃ K : Set (Fin d → ℂ), IsCompact K ∧ K ⊆ Metric.ball 0 γ.radius ∧
      ∀ t ∈ Metric.ball 0 γ.radius, t ∉ K → g (γ.toFun t) = 0) :
    IntegrableOn (fun t => (g ∘ γ.toFun) t * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t)
      (Metric.ball 0 γ.radius) := by
  obtain ⟨K, hKc, hKΔ, hK0⟩ := hK
  have hγ : ContDiffOn ℝ 2 γ.toFun (Metric.ball 0 γ.radius) :=
    ((analyticOnNhd_of_differentiableOn Metric.isOpen_ball γ.differentiableOn).contDiffOn_of_completeSpace
      ).restrict_scalars ℝ
  have hc2 : ∀ k, ContDiffOn ℝ 2 (φ k ∘ γ.toFun) (Metric.ball 0 γ.radius) := by
    intro k
    obtain ⟨O, -, hZO, hφO⟩ := hφ k
    exact (hφO.of_le (WithTop.coe_le_coe.2 le_top)).comp hγ fun t ht => hZO (γ.mapsTo ht)
  have hcont : ContinuousOn (fun t => (g ∘ γ.toFun) t * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t)
      (Metric.ball 0 γ.radius) :=
    (hg.comp_continuousOn γ.differentiableOn.continuousOn).mul
      (ReciprocityTheory.AnForm.M.maDens_continuousOn _ _ Metric.isOpen_ball hc2)
  refine ((hcont.mono hKΔ).integrableOn_compact hKc).of_forall_sdiff_eq_zero measurableSet_ball ?_
  rintro t ⟨htΔ, htK⟩
  simp [hK0 t htΔ htK]

end BranchChartInt


open BranchChartInt in
theorem BranchChartInt.proof (hA : HolomorphicFibreSumInt.Statement) (hS : BranchSheetAE.Statement)
    (hF : ComplexSets.FibreBound.Statement) : BranchChartInt.Statement := by
  classical
  intro n d J A p γ g φ hJ hdim hfin hg hφ hK
  set Δ := Metric.ball (0 : Fin d → ℂ) γ.radius with hΔ
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun t => A *ᵥ γ.toFun t with hτ
  set H : (Fin d → ℂ) → ℝ := fun t => if h : ∃ s, IsSheetAt J A (γ.toFun t) s then
      g (γ.toFun t) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ γ.toFun t) else 0 with hH
  have hτd : DifferentiableOn ℂ τ Δ := (differentiable_mulVec A).comp_differentiableOn γ.differentiableOn
  have hFin : ∀ y, {t | t ∈ Δ ∧ τ t = y}.Finite := by
    intro y
    refine Set.Finite.of_finite_image ((hF n d J A hJ hdim hfin y).2.1.subset ?_)
      (γ.injOn.mono fun t ht => ht.1)
    rintro x ⟨t, ⟨ht, hty⟩, rfl⟩
    exact ⟨γ.mapsTo ht, hty⟩
  have hae : ∀ᵐ t ∂(volume.restrict Δ), (g ∘ γ.toFun) t * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t =
      Complex.normSq (jacC τ t).det * H t := by
    filter_upwards [hS n d J A p γ hJ hdim hfin, ae_restrict_mem measurableSet_ball] with t hts htΔ
    simp only [hH, dif_pos hts, Function.comp_apply]
    rw [maDens_branch_eq γ hφ htΔ hts.choose_spec]
    ring
  have hint : IntegrableOn (fun t => Complex.normSq (jacC τ t).det * H t) Δ :=
    (integrableOn_branch γ hg hφ hK).congr hae
  obtain ⟨hIi, hIeq⟩ := hA d Δ τ H Metric.isOpen_ball hτd hFin hint
  have hcd : chartDens J A (γ.image.indicator g) φ = fun y => ∑ᶠ t ∈ {t | t ∈ Δ ∧ τ t = y}, H t :=
    funext fun y => chartDens_indicator_image J A γ g φ y
  refine ⟨hcd ▸ hIi, ?_⟩
  unfold chartInt ReciprocityTheory.AnForm.maInt
  rw [hcd, hIeq]
  exact (integral_congr_ae hae).symm

end

end GroundTheory.Heights₂.Heights
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem BranchChartInt.proof : GroundTheory.Heights₂.Heights.BranchChartInt.Statement :=
  GroundTheory.Heights₂.Heights.BranchChartInt.proof
    (GroundTheory.Heights₂.Heights.HolomorphicFibreSumInt.proof GroundTheory.Heights₂.Heights.WeightedAreaFormula.proof)
    (GroundTheory.Heights₂.Heights.BranchSheetAE.proof
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RankDeficientFibreInfinite.proof
      GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.proof
      (GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof
        (GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.proof
          GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres.proof)))
    GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.proof

end GroundTheory.Heights₂.Heights.Swarm
end
