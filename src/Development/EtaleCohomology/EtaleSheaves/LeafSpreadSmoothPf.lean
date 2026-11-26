module

public import Development.EtaleCohomology.EtaleSheaves.PropertyDescent.LeafPropsDescendOf
public import Development.EtaleCohomology.EtaleSheaves.LeafReducedSmooth
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling.LeafKill2Of

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSpreadSmoothPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf LateralTheory.E.LeafPropsDescendPf.Split

namespace LateralTheory.E.LeafSpreadSmoothPf

def LeafSpreadSmoothAff : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    LocallyOfFinitePresentation q → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → SmoothOfRelativeDimension 1 q'

def LeafSpreadSmoothAffAt : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    LocallyOfFinitePresentation q → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω) (h : R ≤ S), S.FG ∧ SmoothOfRelativeDimension 1 (pullback.snd q (incl h))

theorem incl_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R S R' : Subalgebra k Ω} (h1 : R ≤ S)
    (h2 : S ≤ R') : incl h2 ≫ incl h1 = incl (h1.trans h2) := by
  rw [← Spec.map_comp]; rfl

theorem LeafSpreadSmoothAff_of (hA : LeafSpreadSmoothAffAt) : LeafSpreadSmoothAff := by
  intro k _ Ω _ _ R hR C D c q v hD hlfp hs hv
  obtain ⟨S, hRS, hSfg, hsm⟩ := hA k Ω R hR c q v hD hlfp hs hv
  refine ⟨S, hRS, hSfg, fun R' hSR' hRR' E q' r hE => ?_⟩
  have hw : r ≫ q = (q' ≫ incl hSR') ≫ incl hRS := by
    rw [Category.assoc, incl_incl]; exact hE.w
  have hsq : IsPullback (pullback.lift r (q' ≫ incl hSR') hw) q' (pullback.snd q (incl hRS)) (incl hSR') := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl hRS))
    rw [pullback.lift_fst, incl_incl]; exact hE
  exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback hsq hsm

theorem fg_finset_sup {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {ι : Type} (t : Finset ι)
    (S : ι → Subalgebra k Ω) (h : ∀ i, (S i).FG) : (t.sup S).FG := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (Subalgebra.fg_bot : (⊥ : Subalgebra k Ω).FG)
  | insert a t _ ih => rw [Finset.sup_insert]; exact (h a).sup ih

theorem LeafSpreadSmooth_of_aff (hA : LeafSpreadSmoothAff) : LeafSpreadSmooth := by
  intro k _ Ω _ _ R hR C D c q v hf hs hv
  obtain ⟨hlfp, hqc, hqs⟩ := hf
  have hL : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
  have := hlfp; have := hqc; have := hs
  have : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace q

  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i : D.affineOpens => ((i : D.Opens) : Set D))
    (fun i => (i : D.Opens).isOpen) (by
      intro x _
      have : x ∈ (⊤ : D.Opens) := trivial
      rw [← iSup_affineOpens_eq_top D] at this
      simpa [TopologicalSpace.Opens.mem_iSup] using this)

  have piece : ∀ U : D.affineOpens, ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' →
      ∀ (hR : R ≤ R') (E : Scheme.{0}) (q' : E ⟶ Sp R') (r : E ⟶ (U : D.Opens)),
      IsPullback r q' ((U : D.Opens).ι ≫ q) (incl hR) → SmoothOfRelativeDimension 1 q' := by
    intro U
    have : IsAffine (U : D.Opens) := U.2
    have h1 := (isPullback_morphismRestrict v (U : D.Opens)).paste_vert hv
    exact hA k Ω R hR (((v ⁻¹ᵁ (U : D.Opens)).ι) ≫ c) ((U : D.Opens).ι ≫ q) (v ∣_ (U : D.Opens)) U.2
      inferInstance (IsZariskiLocalAtSource.comp hs _) h1
  choose S hRS hSfg hS using piece
  refine ⟨R ⊔ t.sup S, le_sup_left, hR.sup (fg_finset_sup t S hSfg), ?_⟩
  intro R' hR' hRR E q' r hE
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1)
    (fun j : t => r ⁻¹ᵁ ((j.1 : D.Opens))) ?_ ?_
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (r x)))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hx⟩
  · intro j
    have h2 := (isPullback_morphismRestrict r (j.1 : D.Opens)).paste_vert hE
    exact hS j.1 R' ((Finset.le_sup j.2).trans (le_sup_right.trans hR')) hRR _ _ (r ∣_ (j.1 : D.Opens)) h2

def LeafSpreadSmoothAffSm : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    LocallyOfFinitePresentation q → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω) (h : R ≤ S), S.FG ∧ Smooth (pullback.snd q (incl h))

def LeafSpreadRelDim : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    LocallyOfFinitePresentation q → Smooth q → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → SmoothOfRelativeDimension 1 q'

theorem LeafSpreadSmoothAffAt_of (hA : LeafSpreadSmoothAffSm) (hB : LeafSpreadRelDim) : LeafSpreadSmoothAffAt := by
  intro k _ Ω _ _ R hR C D c q v hD hlfp hs hv
  obtain ⟨S1, h1, f1, hsm1⟩ := hA k Ω R hR c q v hD hlfp hs hv
  have ht : toR S1 ≫ incl h1 = toR R := by
    rw [← Spec.map_comp]; rfl
  have hw1 : v ≫ q = (c ≫ toR S1) ≫ incl h1 := by
    rw [Category.assoc, ht]; exact hv.w
  have sq1 : IsPullback (pullback.lift v (c ≫ toR S1) hw1) c
      (pullback.snd q (incl h1)) (toR S1) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl h1))
    rw [pullback.lift_fst, ht]; exact hv
  obtain ⟨S2, h12, f2, H⟩ := hB k Ω S1 f1 c (pullback.snd q (incl h1)) _ inferInstance inferInstance hsm1 hs sq1
  refine ⟨S2, h1.trans h12, f2, ?_⟩
  have hw : pullback.fst q (incl (h1.trans h12)) ≫ q = (pullback.snd q (incl (h1.trans h12)) ≫ incl h12) ≫ incl h1 := by
    rw [Category.assoc, incl_incl]; exact pullback.condition
  refine H S2 le_rfl h12 _ _ (pullback.lift _ _ hw) ?_
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl h1))
  rw [pullback.lift_fst, incl_incl]; exact IsPullback.of_hasPullback q (incl (h1.trans h12))

theorem LeafSpreadSmooth_of (hA : LeafSpreadSmoothAffSm) (hB : LeafSpreadRelDim) : LeafSpreadSmooth :=
  LeafSpreadSmooth_of_aff (LeafSpreadSmoothAff_of (LeafSpreadSmoothAffAt_of hA hB))

end LateralTheory.E.LeafSpreadSmoothPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.FMrangePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut LateralTheory.E.SysFMPf Topology

namespace LateralTheory.E.FMrangePf

def RRsub : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ q : PrimeSpectrum W,
    RR w q ⊆ closure (w.toNormalization.base '' {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal})

theorem range_spec_atPrime {W : Type} [CommRing W] (q : PrimeSpectrum W) :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))).base =
      {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal} := by
  have h := PrimeSpectrum.localization_comap_range (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
  ext p
  change p ∈ Set.range (PrimeSpectrum.comap (algebraMap W (Localization.AtPrime q.asIdeal))) ↔ _
  rw [h]
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hd x hx
    by_contra hq
    exact Set.disjoint_left.1 hd (show x ∈ (q.asIdeal.primeCompl : Set W) from hq) hx
  · intro hle
    exact Set.disjoint_left.2 fun x hx hp => hx (hle hp)

theorem mem_basicOpen_toNorm {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (s : Γ(w.normalization, ⊤)) (p : Spec (CommRingCat.of W)) :
    w.toNormalization p ∈ w.normalization.basicOpen s ↔ phi w s ∉ p.asIdeal := by
  change p ∈ w.toNormalization ⁻¹ᵁ w.normalization.basicOpen s ↔ _
  rw [Scheme.preimage_basicOpen_top, AlgebraicGeometry.basicOpen_eq_of_affine']
  rfl

theorem phi_injective {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) : Function.Injective (phi w) := by
  have h1 : Function.Injective (w.toNormalization.appTop) := w.toNormalization.app_injective ⊤
  have h2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of W)).hom :=
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).hom)).1
  exact h2.comp h1

theorem closure_sub_RR {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (q : PrimeSpectrum W) :
    closure (w.toNormalization.base '' {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal}) ⊆ RR w q := by
  intro y hy s hs hsq
  have hid : IsIdempotentElem s := phi_injective w (by rw [map_mul]; exact hs.eq)
  have hcl : IsClosed (w.normalization.basicOpen s : Set w.normalization) := by
    rw [← isOpen_compl_iff]
    have : (w.normalization.basicOpen s : Set w.normalization)ᶜ = w.normalization.basicOpen (1 - s) := by
      ext x
      exact LateralTheory.E.SysFMPfSys.basicOpen_one_sub hid x
    rw [this]
    exact (w.normalization.basicOpen (1 - s)).isOpen
  refine closure_minimal ?_ hcl hy
  rintro _ ⟨p, hp, rfl⟩
  exact (mem_basicOpen_toNorm w s p).2 fun h => hsq (hp h)

def IdemLift : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ e : W, IsIdempotentElem e → ∃ s, phi w s = e

def QcIdem : Prop := ∀ (W : Type) [CommRing W], ProdACF W → ∀ U : (Spec (CommRingCat.of W)).Opens,
  IsCompact (U : Set (Spec (CommRingCat.of W))) → ∃ e : W, IsIdempotentElem e ∧ ∀ p : Spec (CommRingCat.of W),
    p ∈ U ↔ e ∉ p.asIdeal

theorem RRsub_of (hI : IdemLift) (hQ : QcIdem) : RRsub := by
  intro P _ _ W _ w hW q y hy
  by_contra hc
  rw [mem_closure_iff] at hc
  push Not at hc
  obtain ⟨o, ho, hyo, hoT⟩ := hc
  obtain ⟨V, hV, hyV, hVo⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens w.normalization))
    (show y ∈ (⟨o, ho⟩ : TopologicalSpace.Opens w.normalization) from hyo)
  have hVc : IsCompact (w.toNormalization ⁻¹ᵁ V : Set (Spec (CommRingCat.of W))) :=
    QuasiCompact.isCompact_preimage _ V.isOpen (IsAffineOpen.isCompact hV)
  obtain ⟨e, he, hpe⟩ := hQ W hW _ hVc
  have heq : e ∈ q.asIdeal := by
    by_contra hnq
    have hmem : w.toNormalization q ∈ V := (hpe q).2 hnq
    have : w.toNormalization q ∈ o ∩ (w.toNormalization.base '' {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal}) :=
      ⟨hVo hmem, q, show q.asIdeal ≤ q.asIdeal from le_refl _, rfl⟩
    rw [hoT] at this
    exact this
  have hf : IsIdempotentElem (1 - e) := he.one_sub
  have hfq : (1 - e) ∉ q.asIdeal := fun h => q.2.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using q.asIdeal.add_mem heq h))
  obtain ⟨s, hs⟩ := hI W w hW (1 - e) hf
  have hys : y ∈ w.normalization.basicOpen s := hy s (by rw [hs]; exact hf) (by rw [hs]; exact hfq)
  obtain ⟨_, ⟨hz1, hz2⟩, p, rfl⟩ := w.toNormalization.denseRange.inter_open_nonempty
    ((w.normalization.basicOpen s ⊓ V : w.normalization.Opens) : Set w.normalization)
    (w.normalization.basicOpen s ⊓ V).isOpen ⟨y, hys, hyV⟩
  have h1 : phi w s ∉ p.asIdeal := (mem_basicOpen_toNorm w s p).1 hz1
  have h2 : e ∉ p.asIdeal := (hpe p).1 hz2
  rw [hs] at h1
  have : e * (1 - e) ∈ p.asIdeal := by rw [mul_sub, mul_one, he.eq, sub_self]; exact p.asIdeal.zero_mem
  rcases p.2.mem_or_mem this with h | h
  · exact h2 h
  · exact h1 h

theorem FMrange_of (hC : RRsub) : FMrange := by
  intro P _ _ W _ w hW q m e1 e2
  set a := Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))
  have : IsIntegralHom (m ≫ w.fromNormalization) := by rw [e2]; infer_instance
  have : IsIntegralHom m := IsIntegralHom.of_comp m w.fromNormalization
  have hcl : IsClosedMap m.base := m.isClosedMap
  have hd : closure (Set.range (a ≫ w).toNormalization.base) = Set.univ :=
    (a ≫ w).toNormalization.denseRange.closure_range
  have himg : m.base '' Set.range (a ≫ w).toNormalization.base =
      w.toNormalization.base '' Set.range a.base := by
    rw [← Set.range_comp, ← Set.range_comp]
    congr 1
    funext x
    simpa only [Function.comp_apply, ← Scheme.Hom.comp_apply] using
      congrArg (fun f : Spec (CommRingCat.of (Localization.AtPrime q.asIdeal)) ⟶
        w.normalization => f x) e1.symm
  rw [subset_antisymm (hC W w hW q) (closure_sub_RR w q), ← range_spec_atPrime q, ← Set.image_univ, ← hd,
    ← hcl.closure_image_eq_of_continuous m.continuous, himg]

theorem FMrange_of_leaves (hI : IdemLift) (hQ : QcIdem) : FMrange :=
  FMrange_of (RRsub_of hI hQ)

end LateralTheory.E.FMrangePf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.StalkVanishing
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StalkVanishing
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem goal_of (hN : LateralTheory.E.SecondDegreeKilling.Nbhd.LeafKillNbhd) : LateralTheory.E.LeafVan0Pf.LeafVanStalk := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m hsub y
  refine LateralTheory.E.SecondDegreeKilling.Nbhd.killPt_of hN hH q k hq i toK ι p hp U m y ?_
  intro A _ t hA
  have := hsub A t hA
  exact Subsingleton.elim _ _

end LateralTheory.E.StalkVanishing
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.IdemSecPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.SysFMPf

namespace LateralTheory.E.IdemSecPf

theorem phi_injective {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) : Function.Injective (phi w) := by
  have h1 : Function.Injective (w.toNormalization.app ⊤) := w.toNormalization.app_injective ⊤
  have h2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of W)).hom :=
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).hom)).1
  intro a b h
  exact h1 (h2 h)

theorem phi_idem {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (e : W) (he : IsIdempotentElem e) : ∃ s, phi w s = e := by
  let t : Γ(Spec (CommRingCat.of W), w.toNormalization ⁻¹ᵁ ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv e
  have ht : (w.toNormalization.app ⊤).hom.IsIntegralElem t := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num))
    · have : t * t = t := by
        show (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom e * (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom e = _
        rw [← map_mul, he.eq]
      rw [sq, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X, this, sub_self]
  obtain ⟨s, hs⟩ := GlobalTheory.mem_range_toNormalization_app w ⊤ t ht
  refine ⟨s, ?_⟩
  show (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (w.toNormalization.app ⊤ s) = e
  rw [hs]
  show ((Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom e = e
  simp

theorem IdemSec_of : LateralTheory.E.SysFMPfSys.IdemSec := by
  intro P _ _ W _ w
  exact ⟨phi_injective w, fun e he => phi_idem w e he⟩

end LateralTheory.E.IdemSecPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafGlueDimPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 Order TopologicalSpace Topology

namespace LateralTheory.E.LeafGlueDimPf

theorem dim_le_of_cover {X U V : Type*} [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace V]
    (f : U → X) (g : V → X) (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (hc : Set.range f ∪ Set.range g = Set.univ) :
    topologicalKrullDim X ≤ max (topologicalKrullDim U) (topologicalKrullDim V) := by
  unfold topologicalKrullDim
  rw [krullDim_eq_iSup_coheight]
  refine iSup_le fun Z => ?_
  obtain ⟨z, hz⟩ := Z.2.nonempty
  have hzu : z ∈ Set.range f ∪ Set.range g := hc ▸ Set.mem_univ z
  rcases hzu with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · let T := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).symm ⟨Z, ⟨w, hz⟩⟩
    have hT : IrreducibleCloseds.map f hf.continuous T = Z := by
      have := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).apply_symm_apply ⟨Z, ⟨w, hz⟩⟩
      exact congrArg Subtype.val this
    rw [← hT, hf.coheight_map]
    exact le_trans (coheight_le_krullDim T) le_sup_left
  · let T := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding g hg).symm ⟨Z, ⟨w, hz⟩⟩
    have hT : IrreducibleCloseds.map g hg.continuous T = Z := by
      have := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding g hg).apply_symm_apply ⟨Z, ⟨w, hz⟩⟩
      exact congrArg Subtype.val this
    rw [← hT, hg.coheight_map]
    exact le_trans (coheight_le_krullDim T) le_sup_right

theorem dim_eq_of_cover {X U V : Type*} [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace V]
    (f : U → X) (g : V → X) (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (hc : Set.range f ∪ Set.range g = Set.univ) :
    topologicalKrullDim X = max (topologicalKrullDim U) (topologicalKrullDim V) :=
  le_antisymm (dim_le_of_cover f g hf hg hc)
    (max_le hf.isInducing.topologicalKrullDim_le hg.isInducing.topologicalKrullDim_le)

theorem dim_Sp {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A : Subalgebra Ω L) :
    topologicalKrullDim (Sp A) = ringKrullDim A :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A

theorem LeafGlueDim_of : LateralTheory.E.LeafGlueProperPf.LeafGlueDim := by
  intro Ω L _ _ _ A B u h G
  have hA : topologicalKrullDim (Sp A) = 1 := (dim_Sp A).trans h.2.2.2.2.2.2.2.1
  have hB : topologicalKrullDim (Sp B) = 1 := (dim_Sp B).trans h.2.2.2.2.2.2.2.2.1
  have := G.hiA; have := G.hiB
  rw [dim_eq_of_cover G.iA.base G.iB.base G.iA.isOpenEmbedding G.iB.isOpenEmbedding G.cover, hA, hB, max_self]

end LateralTheory.E.LeafGlueDimPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafGlueGenericPf
noncomputable section
open AlgebraicGeometry.StructureSheaf CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.LeafGlueGenericPf

def eta (A : Type) [CommRing A] [IsDomain A] : Sp A := ⟨⊥, Ideal.isPrime_bot⟩

theorem eta_generic (A : Type) [CommRing A] [IsDomain A] : IsGenericPoint (eta A) (⊤ : Set (Sp A)) := by
  rw [isGenericPoint_iff_specializes]
  intro y
  simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
  exact (PrimeSpectrum.le_iff_specializes (eta A) y).1 bot_le

def etaT (A : Type) [CommRing A] [IsDomain A] : PrimeSpectrum.Top A := ⟨⊥, Ideal.isPrime_bot⟩

def psi0 {A L : Type} [CommRing A] [IsDomain A] [Field L] [Algebra A L] [IsFractionRing A L] :
    L →+* (structurePresheafInCommRingCat A).stalk (etaT A) := by
  have : (etaT A).asIdeal.IsPrime := Ideal.isPrime_bot
  exact IsLocalization.lift (M := nonZeroDivisors A) (S := L)
    (g := algebraMap A ((structurePresheafInCommRingCat A).stalk (etaT A))) (by
      intro y
      have hy : (y : A) ∈ (etaT A).asIdeal.primeCompl := by
        intro h0; exact nonZeroDivisors.ne_zero y.2 h0
      exact IsLocalization.map_units ((structurePresheafInCommRingCat A).stalk (etaT A))
        (⟨y, hy⟩ : (etaT A).asIdeal.primeCompl))

theorem fractionFieldToGenericStalk_algebraMap_eq {A L : Type} [CommRing A] [IsDomain A] [Field L] [Algebra A L] [IsFractionRing A L] (a : A) :
    psi0 (L := L) (algebraMap A L a) = StructureSheaf.toStalk A (etaT A) a := by
  unfold psi0; simp only [IsLocalization.lift_eq]; rfl

theorem glued_curve_generic_point_maps_to_function_field : LeafGlueGeneric := by
  intro Ω L _ _ _ A B u h G
  have := G.hiA
  have : IsFractionRing A L := h.2.2.2.2.2.2.2.2.2.1
  have : IsIntegral G.C0 := glued_affine_curve_is_integral_scheme Ω L A B u h G
  let s := G.iA.stalkMap (eta A)
  refine ⟨G.iA.base (eta A), Spec.map (inv s) ≫ Spec.map (CommRingCat.ofHom (psi0 (L := L))), ?_, ?_⟩
  · have hg := (eta_generic A).image G.iA.base.hom.continuous
    rw [Set.top_eq_univ, Set.image_univ,
      (G.iA.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)).closure_eq] at hg
    exact hg
  · have key := Scheme.SpecMap_stalkMap_fromSpecStalk G.iA (x := eta A)
    have hinv : G.C0.fromSpecStalk (G.iA.base (eta A)) =
        Spec.map (inv s) ≫ (Sp A).fromSpecStalk (eta A) ≫ G.iA := by
      rw [← key, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
    rw [Category.assoc, hinv, Category.assoc, Category.assoc, G.hcA]
    congr 1
    rw [Spec.fromSpecStalk_eq']
    erw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    have ha : algebraMap Ω L a = algebraMap A L (algebraMap Ω A a) := rfl
    change psi0 (L := L) (algebraMap Ω L a) = StructureSheaf.toStalk A (etaT A) (algebraMap Ω A a)
    rw [ha, fractionFieldToGenericStalk_algebraMap_eq]

end LateralTheory.E.LeafGlueGenericPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.GeometricDataOfLines
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.ChartsGeom_vpaPf

namespace LateralTheory.E.GeometricData

theorem rA_top {A : Type} [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) :
    rA p ⊤ = p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
  have h : p.appLE ⊤ ⊤ le_top = p.appTop := p.appLE_eq_app (U := ⊤)
  rw [rA, h]

theorem topInt : TopInt := by
  intro A _ _ Z p hIL
  obtain ⟨L, u, l, hu, hl, rfl⟩ := hIL
  have : UniversallyClosed u := (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp hu).1
  have : UniversallyClosed l := hl.1.toUniversallyClosed
  have h1 := isIntegral_appTop_of_universallyClosed (u ≫ l)
  rw [rA_top]
  refine RingHom.IsIntegral.trans _ _ ?_ h1
  exact RingHom.isIntegral_of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective

theorem germ_res_eq {Z : Scheme.{0}} [IsIntegral Z] (U W : Z.Opens) (h : W ≤ U) [Nonempty U] [Nonempty W]
    (s : Γ(Z, U)) : Z.germToFunctionField W (Z.presheaf.map (homOfLE h).op s) = Z.germToFunctionField U s := by
  simp only [Scheme.germToFunctionField]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

theorem embedAffine : EmbedAffine := by
  intro A _ _ Z p hI hTop hAff
  obtain ⟨z⟩ : Nonempty Z := inferInstance
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨z, trivial⟩⟩
  have : Nonempty (⊤ ⊓ ⊤ : Z.Opens) := ⟨⟨z, trivial, trivial⟩⟩
  let φ : Γ(Z, ⊤) →+* Z.functionField := (Z.germToFunctionField ⊤).hom
  let _ : Algebra A Z.functionField := (φ.comp (rA p ⊤)).toAlgebra
  let B : Subalgebra A Z.functionField :=
    { toSubsemiring := φ.rangeS, algebraMap_mem' := fun a => ⟨rA p ⊤ a, rfl⟩ }
  have hBint : ∀ x ∈ B, IsIntegral A x := by
    rintro x ⟨g, rfl⟩
    obtain ⟨P, hP, hP0⟩ := hTop g
    refine ⟨P, hP, ?_⟩
    have : Polynomial.eval₂ (algebraMap A Z.functionField) (φ g) P = φ (Polynomial.eval₂ (rA p ⊤) g P) := by
      rw [Polynomial.hom_eval₂]; rfl
    rw [this, hP0, map_zero]
  have hDov : AdjoinInv B 1 = B := by
    apply le_antisymm
    · rw [AdjoinInv, Algebra.adjoin_le_iff]
      rintro x (hx | hx)
      · exact hx
      · rw [Set.mem_singleton_iff.mp hx, inv_one]; exact B.one_mem
    · intro x hx
      exact Algebra.subset_adjoin (Or.inl hx)
  refine ⟨Z.functionField, inferInstance, inferInstance, B, B, 1, ?_, fun x hx _ => hBint x hx, ?_⟩
  · refine ⟨one_ne_zero, B.one_mem, by rw [inv_one]; exact B.one_mem, ?_, ?_, ?_⟩
    · intro b hb; exact (hBint b hb).tower_top
    · intro b hb; exact (hBint b hb).tower_top
    · rw [hDov]
      apply le_antisymm
      · intro x hx; exact Algebra.subset_adjoin (Or.inl hx)
      · rw [Algebra.adjoin_le_iff]
        rintro x (hx | hx)
        · exact hx
        · rw [Set.mem_singleton_iff.mp hx]; exact B.one_mem
  · refine ⟨⊤, ⊤, φ, φ, (Z.germToFunctionField (⊤ ⊓ ⊤)).hom, hAff, hAff, by simpa using hAff, sup_idem _,
      Z.germToFunctionField_injective _, Z.germToFunctionField_injective _, Z.germToFunctionField_injective _,
      rfl, rfl, ?_, ?_, ?_, fun a => rfl, fun a => rfl⟩
    · rw [hDov]
      ext x
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨_, germ_res_eq (⊤ ⊓ ⊤) ⊤ (le_inf le_rfl le_rfl) s⟩
      · rintro ⟨s, rfl⟩
        exact ⟨Z.presheaf.map (homOfLE inf_le_left).op s, germ_res_eq _ _ _ s⟩
    · intro s; exact germ_res_eq _ _ _ s
    · intro s; exact germ_res_eq _ _ _ s

end LateralTheory.E.GeometricData
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafPtVPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex

namespace LateralTheory.E.LeafPtVPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.SecondDegreeKilling
  LateralTheory.E.SecondDegreeKilling.Comp LateralTheory.E.SecondDegreeKilling.Nbhd

theorem isZero_sec_empty (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) [IsEmpty X] :
    IsZero (F.obj.obj (op X)) :=
  (Sheaf.isTerminalOfBotCover F X (Scheme.bot_mem_grothendieckTopology (P := @Etale) X)).isZero

theorem isZero_free_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] :
    IsZero ((free R).obj (yoneda.obj X)) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).injective
  ext1
  ext1 U
  by_cases hU : IsEmpty U.unop
  · exact (isZero_sec_empty R ((free R).obj (yoneda.obj X)) U.unop).eq_of_tgt _ _
  · have hE : IsEmpty (ULift.{1} (unop U ⟶ X)) := ⟨fun f => by
      obtain ⟨x⟩ := not_isEmpty_iff.1 hU; exact IsEmpty.false (f.down.base x)⟩
    haveI : Subsingleton ↑(((freeP R).obj (yoneda.obj X)).obj U) := by
      change Subsingleton (ULift.{1} (unop U ⟶ X) →₀ ULift.{1} R); infer_instance
    exact (ModuleCat.isZero_of_subsingleton _).eq_of_src _ _

theorem isZero_chains_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] (n : ℤ) :
    IsZero (((chains R).obj (sch.obj X)).X n) := by
  obtain ⟨p, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rcases p with _ | k
    · exact (isZero_free_empty R X).of_iso (chainsXIso R (sch.obj X) 0)
    · exact HomologicalComplex.isZero_extend_X _ _ _ (by
        intro j; change -(j : ℤ) ≠ (k : ℤ) + 1; omega)
  · exact (isZero_free_empty R X).of_iso (chainsXIso R (sch.obj X) p)

theorem isIso_inr (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (hK : ∀ n, IsZero (K.X n)) :
    IsIso (mappingCone.inr φ) := by
  have : ∀ p, IsIso ((mappingCone.inr φ).f p) := fun p => ⟨⟨(mappingCone.snd φ).v p p (add_zero p), by simp, by
    rw [← mappingCone.id_X φ p (p + 1) rfl, (hK (p + 1)).eq_of_tgt ((mappingCone.fst φ).1.v p (p + 1) rfl) 0]
    simp⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components _

theorem fgt_bij (hH : Hyps) (R : Type) [CommRing R] (F : Shv R) {X : Scheme.{0}} [IsEmpty X] {E : Spc}
    (f : sch.obj X ⟶ E) (n : ℤ) : Function.Bijective (fgt R f F n) := by
  haveI := isIso_inr R ((chains R).map f) (isZero_chains_empty R X)
  exact hH.1 R (mappingCone.inr ((chains R).map f)) F n

theorem rpl_zero (hH : Hyps) (q : ℕ) (i : ℤ) {U E U' E' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') [IsEmpty U']
    (u : U' ⟶ U) (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (n : ℤ) (he : pl q i e n = 0)
    (x : Hrel (ZMod q) (sch.map f) (tw q i) n) : rpl q i f f' u e comm n x = 0 := by
  apply (fgt_bij hH (ZMod q) (tw q i) (sch.map f') n).1
  rw [map_zero]
  refine (relNat (ZMod q) (tw q i) (sch.map f) (sch.map f') (sch.map u) (sch.map e)
    (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) n x).trans ?_
  change pl q i e n _ = 0
  rw [he]; rfl

theorem isEmpty_pullback_closed_subscheme_section_into_complement {B W Y S : Scheme.{0}} (ι : W ⟶ B) (V : B.Opens) (hVW : (V : Set B) = (Set.range ι)ᶜ)
    (p : Y ⟶ B) (s : S ⟶ B) (hs : Set.range ⇑s ⊆ (V : Set B)) :
    IsEmpty ↥(pullback (pullback.snd p s ≫ s) ι : Scheme.{0}) := ⟨fun x => by
  have h1 : (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s ≫ s) x = (pullback.snd (pullback.snd p s ≫ s) ι ≫ ι) x := by
    rw [pullback.condition]
  have h2 : (pullback.snd (pullback.snd p s ≫ s) ι ≫ ι) x ∈ (V : Set B) := by
    rw [← h1]; apply hs; simp only [Scheme.Hom.comp_apply]; exact ⟨_, rfl⟩
  rw [hVW] at h2; simp only [Scheme.Hom.comp_apply] at h2; exact h2 ⟨_, rfl⟩⟩

theorem LeafPtV_of : LateralTheory.E.SecondDegreeKilling.LeafPtV := by
  intro hH q _ k _ hq i B W Y Y' toK ι _ V hVW p g hp hgp U A _ t hA hV m hpl y
  haveI := isEmpty_pullback_closed_subscheme_section_into_complement ι V hVW (g ≫ p) (t ≫ U.hom) hV
  let wA : pullback (pullback.snd (g ≫ p) (t ≫ U.hom) ≫ (t ≫ U.hom)) ι ⟶
      pullback (pullback.snd p (t ≫ U.hom) ≫ (t ≫ U.hom)) ι :=
    pullback.map _ ι _ ι (fibMap g p (t ≫ U.hom)) (𝟙 W) (𝟙 B)
      (by rw [Category.comp_id, ← Category.assoc (fibMap g p (t ≫ U.hom)), pullback.lift_snd, Category.comp_id]) (by simp)
  have commA : prS (g ≫ p) ι (t ≫ U.hom) ≫ fibMap g p (t ≫ U.hom) = wA ≫ prS p ι (t ≫ U.hom) :=
    (pullback.lift_fst _ _ _).symm
  have hA : prS p ι (t ≫ U.hom) ≫ tY p U t = tW p ι U t ≫ prU p ι U := (pullback.lift_fst _ _ _).symm
  have hB : prS (g ≫ p) ι (t ≫ U.hom) ≫ tY (g ≫ p) U t = tW (g ≫ p) ι U t ≫ prU (g ≫ p) ι U :=
    (pullback.lift_fst _ _ _).symm
  have hC : prU (g ≫ p) ι U ≫ mY p g U = mW p g ι U ≫ prU p ι U := (pullback.lift_fst _ _ _).symm
  have E1 : tY (g ≫ p) U t ≫ mY p g U = fibMap g p (t ≫ U.hom) ≫ tY p U t := by
    simp only [tY, mY, fibMap, pullback.map_comp, Category.id_comp, Category.comp_id]
  have c1 : prS (g ≫ p) ι (t ≫ U.hom) ≫ (tY (g ≫ p) U t ≫ mY p g U) =
      (tW (g ≫ p) ι U t ≫ mW p g ι U) ≫ prU p ι U := by
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ mY p g U) hB).trans ((Category.assoc _ _ _).trans
      ((congrArg (tW (g ≫ p) ι U t ≫ ·) hC).trans (Category.assoc _ _ _).symm)))
  have c2 : prS (g ≫ p) ι (t ≫ U.hom) ≫ (fibMap g p (t ≫ U.hom) ≫ tY p U t) =
      (wA ≫ tW p ι U t) ≫ prU p ι U := by
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ tY p U t) commA).trans ((Category.assoc _ _ _).trans
      ((congrArg (wA ≫ ·) hA).trans (Category.assoc _ _ _).symm)))
  have E2 : tW (g ≫ p) ι U t ≫ mW p g ι U = wA ≫ tW p ι U t := by
    simp only [tW, mW, wA, pullback.map_comp]
    congr 1
  rw [rpl_comp q i _ _ _ _ _ _ _ _ _ c1, rpl_congr q i _ _ _ _ _ _ c1 c2 E2 E1, ← rpl_comp q i _ _ _ _ _ hA _ _ commA c2]
  exact rpl_zero hH q i _ _ _ _ commA m hpl _

end LateralTheory.E.LeafPtVPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.GluingExistence
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluingExistence

theorem mul_pow_mem {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (C : Subalgebra Ω L) (v : L)
    (hv : v ∈ C) (hv0 : v ≠ 0) (x : L) (hx : x ∈ Algebra.adjoin Ω ((C : Set L) ∪ {v⁻¹})) :
    ∃ n : ℕ, x * v ^ n ∈ C := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · rw [Set.mem_singleton_iff.mp hx]; exact ⟨1, by rw [pow_one, inv_mul_cancel₀ hv0]; exact C.one_mem⟩
  | algebraMap r => exact ⟨0, by simpa using C.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x + y) * v ^ (n + m) = (x * v ^ n) * v ^ m + (y * v ^ m) * v ^ n := by ring
    rw [this]; exact C.add_mem (C.mul_mem hn (C.pow_mem hv _)) (C.mul_mem hm (C.pow_mem hv _))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x * y) * v ^ (n + m) = (x * v ^ n) * (y * v ^ m) := by ring
    rw [this]; exact C.mul_mem hn hm

theorem away {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (C E : Subalgebra Ω L) (v : L)
    (hv : v ∈ C) (hv0 : v ≠ 0) (hCE : C ≤ E) (hE : E = Algebra.adjoin Ω ((C : Set L) ∪ {v⁻¹})) :
    letI := (Subalgebra.inclusion hCE).toRingHom.toAlgebra
    IsLocalization.Away (⟨v, hv⟩ : C) E := by
  letI := (Subalgebra.inclusion hCE).toRingHom.toAlgebra
  have hvi : v⁻¹ ∈ E := hE ▸ Algebra.subset_adjoin (Set.mem_union_right _ rfl)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨v⁻¹, hvi⟩ ^ n, Subtype.ext ?_⟩
    show (v ^ n) * (v⁻¹) ^ n = 1
    rw [← mul_pow, mul_inv_cancel₀ hv0, one_pow]
  · rintro ⟨z, hz⟩
    obtain ⟨n, hn⟩ := mul_pow_mem C v hv hv0 z (hE ▸ hz)
    exact ⟨(⟨z * v ^ n, hn⟩, ⟨⟨v, hv⟩ ^ n, n, rfl⟩), Subtype.ext rfl⟩
  · intro x y h
    refine ⟨1, ?_⟩
    have : (x : L) = y := congrArg (fun w : E => (w : L)) h
    simp [Subtype.ext this]

theorem LeafGlueExists_of : LeafGlueExists := by
  intro Ω L _ _ _ A B u h
  obtain ⟨hu, huA, huB, -, -, -, -, -, -, -, -, hadj, -⟩ := h
  set D := Dr Ω A u
  have hAD : A ≤ D := le_Dr_A A u
  have hBD : B ≤ D := le_Dr_B A B u hadj
  letI iAD : Algebra A D := (Subalgebra.inclusion hAD).toRingHom.toAlgebra
  letI iBD : Algebra B D := (Subalgebra.inclusion hBD).toRingHom.toAlgebra
  haveI : IsLocalization.Away (⟨u, huA⟩ : A) D := away A D u huA hu hAD rfl
  haveI : IsLocalization.Away (⟨u⁻¹, huB⟩ : B) D :=
    away B D u⁻¹ huB (inv_ne_zero hu) hBD (by rw [inv_inv]; exact hadj)
  let fA : Sp D ⟶ Sp A := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAD).toRingHom)
  let fB : Sp D ⟶ Sp B := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hBD).toRingHom)
  haveI hfA : IsOpenImmersion fA := IsOpenImmersion.of_isLocalization (S := D) (⟨u, huA⟩ : A)
  haveI hfB : IsOpenImmersion fB := IsOpenImmersion.of_isLocalization (S := D) (⟨u⁻¹, huB⟩ : B)
  haveI : ∀ {i j : WalkingSpan} (f : i ⟶ j), IsOpenImmersion ((span fA fB).map f) := by
    intro i j f
    rcases f with _ | j
    · exact inferInstanceAs (IsOpenImmersion (𝟙 _))
    · rcases j with _ | _
      · exact hfA
      · exact hfB
  have hc : fA ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω A)) =
      fB ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) := by
    simp only [fA, fB, ← Spec.map_comp]; rfl
  refine ⟨{
    C0 := pushout fA fB
    c0 := pushout.desc _ _ hc
    iA := pushout.inl fA fB
    iB := pushout.inr fA fB
    hiA := inferInstanceAs (IsOpenImmersion (colimit.ι (span fA fB) _))
    hiB := inferInstanceAs (IsOpenImmersion (colimit.ι (span fA fB) _))
    hcA := pushout.inl_desc _ _ _
    hcB := pushout.inr_desc _ _ _
    agree := pushout.condition
    cover := ?_
    inter := ?_ }⟩
  · ext x
    simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, xi, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span fA fB) x
    rcases i with _ | j
    · left; refine ⟨fA xi, ?_⟩
      rw [← colimit.w (span fA fB) (WidePushoutShape.Hom.init WalkingPair.left)]; rfl
    · rcases j with _ | _
      · left; exact ⟨xi, rfl⟩
      · right; exact ⟨xi, rfl⟩
  · ext x
    constructor
    · rintro ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
      have hab : colimit.ι (span fA fB) (some WalkingPair.left) a =
          colimit.ι (span fA fB) (some WalkingPair.right) b := hb.symm
      obtain ⟨k, fi, fj, y, hy1, hy2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (span fA fB)).mp hab
      rcases k with _ | k
      · refine ⟨y, ?_⟩
        rw [← hy1, Subsingleton.elim fi (WidePushoutShape.Hom.init WalkingPair.left)]; rfl
      · rcases k with _ | _
        · cases (show WidePushoutShape.Hom (J := WalkingPair) (some WalkingPair.left) (some WalkingPair.right) from fj)
        · cases (show WidePushoutShape.Hom (J := WalkingPair) (some WalkingPair.right) (some WalkingPair.left) from fi)
    · rintro ⟨y, rfl⟩
      refine ⟨⟨fA y, rfl⟩, ⟨fB y, ?_⟩⟩
      show (fB ≫ pushout.inr fA fB).base y = (fA ≫ pushout.inl fA fB).base y
      rw [pushout.condition]

end LateralTheory.E.GluingExistence
end
end
