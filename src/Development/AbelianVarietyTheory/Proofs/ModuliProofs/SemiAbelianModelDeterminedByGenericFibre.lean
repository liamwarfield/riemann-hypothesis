module

public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmPointObjectExistsOfLaws
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem semiAbelian_model_determined_by_generic_fibre : ExtVStatement :=
  GlobalTheory.ModelUniqueChecks.extV_holds

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.MulFiniteFlat

open GlobalTheory.AbLaw.MulN

theorem finite_preimage_of_geomFibres {S : Scheme.{0}} {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      IsFinite ((Over.pullback t).map f).left) (y : Y.left) : (f.left ⁻¹' {y}).Finite := by
  let K := AlgebraicClosure (Y.left.residueField y)
  let u : Spec (CommRingCat.of K) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) K)) ≫
      Y.left.fromSpecResidueField y
  let t := u ≫ Y.hom
  have hs := h K t
  let p : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  let v : Spec (CommRingCat.of K) ⟶ pullback Y.hom t := pullback.lift u (𝟙 _) (by simp [t])
  have hv : pullback.fst Y.hom t (v p) = y := by
    rw [← Scheme.Hom.comp_apply]
    have : v ≫ pullback.fst Y.hom t = u := pullback.lift_fst _ _ _
    rw [this]
    exact (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply y _)
  have hfin := ((Over.pullback t).map f).left.finite_preimage_singleton (v p)
  refine (hfin.image (pullback.fst X.hom t)).subset fun x hx => ?_
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback (isPullback_baseChange t f) x (v p)
    ((show f.left x = y from hx).trans hv.symm)
  exact ⟨z, hz₂, hz₁⟩

theorem pullback_map_mulA {S T : Scheme.{0}} (t : T ⟶ S) (A : Over S) [GrpObj A] (n : ℕ) :
    (Over.pullback t).map (mulA A n) = mulA ((Over.pullback t).obj A) n := by
  change (Over.pullback t).map (𝟙 A ^ n) = 𝟙 _ ^ n
  induction n with
  | zero => rw [pow_zero, pow_zero, Functor.map_one]
  | succ n ih => rw [pow_succ, pow_succ, Functor.map_mul, ih, CategoryTheory.Functor.map_id]

theorem isFinite_and_flat_mul : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ k : ℕ, 1 ≤ k → IsFinite ((𝟙 A) ^ k : A ⟶ A).left ∧ Flat ((𝟙 A) ^ k : A ⟶ A).left := by
  intro S _ A _ _ hA k hk
  change IsFinite (mulA A k).left ∧ Flat (mulA A k).left
  have hsm := hA.smooth
  have hpr := hA.proper
  have hm := isMonHom_mulA A k
  have hg : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      IsFinite ((Over.pullback t).map (mulA A k)).left := fun K _ _ t => by
    rw [pullback_map_mulA]
    exact GlobalTheory.MulFiniteAny.isFinite_mulA K _ (TLinPf.isAb_pullback t A hA) k hk
  have h1 : IsProper ((mulA A k).left ≫ A.hom) := by rw [Over.w]; exact hpr
  have h2 : IsProper (mulA A k).left := IsProper.of_comp _ A.hom
  have h3 : LocallyQuasiFinite (mulA A k).left :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (finite_preimage_of_geomFibres _ hg)
  have hf : IsFinite (mulA A k).left := .of_isProper_of_locallyQuasiFinite _
  refine ⟨hf, GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres S _ _ _ inferInstance inferInstance hf
    fun K _ _ t => ?_⟩
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    (TLinPf.isAb_pullback t A hA) _ inferInstance (hg K t)).1

end GlobalTheory.MulFiniteFlat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_and_flat_mul_abelianScheme : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ k : ℕ, 1 ≤ k → IsFinite ((𝟙 A) ^ k : A ⟶ A).left ∧ Flat ((𝟙 A) ^ k : A ⟶ A).left := by
  first | exact @GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul | exact GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul | (intros; apply GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyFamilyUnifIffUnifAt
section -- merged from Development.AbelianVarietyTheory.BlockTheory.CMModuli.SymplecticBasisLevel
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Lattice

end Lattice

section Fibre

variable {D : Datum H} {l : Level H} (Xo : Moduli D l) {g : ℕ} (ty : Fin g → (E →+* ℂ))

abbrev univG : Over Xo.X := Xo.univ.t.G

end Fibre

section Component

variable {D : Datum H} {l : Level H} (Xo : Moduli D l) (σ : KA l →+* ℂ) {g : ℕ} (ty : Fin g → (E →+* ℂ))
  (D' : Datum H) (u : (D'.La →+ (Fin g → ℂ)) → (Sp ℂ ⟶ Xo.X))
  (ex : ∀ P : D'.La →+ (Fin g → ℂ), (Fin g → ℂ) → (Over.mk (u P) ⟶ univG Xo))

end Component

end GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel
end
end

noncomputable section

namespace GlobalTheory.UnifCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel GlobalTheory.PeriodCompare
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Lattice

theorem isPeriod_move {D' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P₀ P₁ P : D'.La →+ (Fin g → ℂ)}
    (h₀ : IsPeriod D' ty P₀) (h₁ : IsPeriod D' ty P₁) (hP : IsPeriod D' ty P) (gam : D'.La ≃ₗ[𝓞 E] D'.La)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hgam : ∀ a b, D'.EF (gam a) (gam b) = D'.EF a b)
    (hh : ∀ a, P₁ (gam a) = h (P₀ a)) :
    IsPeriod D' ty (h.toLinearMap.toAddMonoidHom.comp (P.comp gam.symm.toLinearMap.toAddMonoidHom)) := by
  have tr : ∀ {Q : D'.La →+ (Fin g → ℂ)}, IsPeriod D' ty Q →
      IsPeriod D' ty (Q.comp gam.symm.toLinearMap.toAddMonoidHom) := by
    rintro Q ⟨h1, h2, h3, h4, Hm, h5, h6, h7⟩
    have hr : (Q.comp gam.symm.toLinearMap.toAddMonoidHom).range = Q.range :=
      SetLike.ext' (gam.symm.surjective.range_comp Q)
    refine ⟨fun a x i => ?_, h2.comp gam.symm.injective, by rw [hr]; exact h3, ?_, Hm, h5, h6, fun x y => ?_⟩
    · simpa using h1 a (gam.symm x) i
    · rw [← h4, ← AddMonoidHom.coe_range, hr, AddMonoidHom.coe_range]
    · change (hermForm Hm (Q (gam.symm x)) (Q (gam.symm y))).im = _
      rw [h7, ← hgam, gam.apply_symm_apply, gam.apply_symm_apply]
  let A := LinearMap.toMatrix' h.toLinearMap
  have hA : A.mulVecLin = h.toLinearMap := by
    rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  have hdet : A.det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact h.isUnit_det'.ne_zero
  rw [← hA]
  refine PeriodConn.isPeriod_mulVec (tr hP) hdet (PeriodConn.entry_eq_zero (tr h₀) h₁ fun x => ?_)
  rw [← Matrix.mulVecLin_apply, hA]
  exact (congrArg P₁ (gam.apply_symm_apply x)).symm.trans (hh _)

variable {g : ℕ}

variable {D' : Datum H} {ty : Fin g → (E →+* ℂ)}

end Lattice

section Deriv

variable {X S : Scheme.{0}} {g : ℕ}

theorem isDerivAt0_smul {F : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (hv : IsDerivAt0 F w v) (c : ℂ) : IsDerivAt0 F (c • w) (spMap (epsScale c) ≫ v) := by
  have h0 : spMap TangentOrigin.fstC ≫ spMap (epsScale c) ≫ v = spMap TangentOrigin.fstC ≫ v := by
    rw [← Category.assoc, TanMod.spMap_comp']
    congr 2
    exact RingHom.ext fun x => by simp [epsScale]
  refine ⟨h0.trans hv.1, fun U h f => ?_⟩
  have h' : ⊤ ≤ v ⁻¹ᵁ U := by
    rw [TangentOrigin.top_le_preimage_iff] at h ⊢
    exact h0 ▸ h
  refine (congrArg TrivSqZeroExt.snd (TangentOrigin.evalPt_spMap_comp (epsScale c) v U h' h f)).trans ?_
  rw [map_smul, ← hv.2 U h' f]
  exact TrivSqZeroExt.snd_map _ _

theorem isDerivAt0_mul {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {F : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)}
    (h0 : F 0 = (1 : Over.mk y ⟶ G).left) {w w' : Fin g → ℂ} {v v' : epsPt y ⟶ G}
    (hv : IsDerivAt0 F w v.left) (hv' : IsDerivAt0 F w' v'.left) : IsDerivAt0 F (w + w') (v * v').left := by
  have t := TanMod.smT_zero_of y v (hv.1.trans h0)
  have t' := TanMod.smT_zero_of y v' (hv'.1.trans h0)
  have t'' : spMap TangentOrigin.fstC ≫ (v * v').left = F 0 :=
    (TanMod.unit_of_smT_zero y (v * v') (by rw [TanMod.smT_mul, t, t', _root_.mul_one])).trans h0.symm
  refine ⟨t'', fun U h f => ?_⟩
  have hF : ⊤ ≤ F 0 ⁻¹ᵁ U := t'' ▸ (TangentOrigin.top_le_preimage_iff _ U).1 h
  have h1 := (TangentOrigin.top_le_preimage_iff v.left U).2 (hv.1.symm ▸ hF)
  have h2 := (TangentOrigin.top_le_preimage_iff v'.left U).2 (hv'.1.symm ▸ hF)
  rw [map_add (f := _), ← hv.2 U h1 f, ← hv'.2 U h2 f]
  exact TanDeriv.snd_evAt_mul v v' t t' U h1 h2 h f

end Deriv

section Piece

variable {D : Datum H} {l : Level H} (Xo : Moduli D l) {g : ℕ} (ty : Fin g → (E →+* ℂ))
  (D' : Datum H) (u : (D'.La →+ (Fin g → ℂ)) → (Sp ℂ ⟶ Xo.X))
  (ex : ∀ P : D'.La →+ (Fin g → ℂ), (Fin g → ℂ) → (Over.mk (u P) ⟶ univG Xo))

variable {Xo ty D' u ex}

end Piece

section Main

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

end Main

end GlobalTheory.UnifCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory

namespace SectionQuot

open PointQuot

variable {S : Scheme.{0}}

lemma exists_geomPt (Z : Over S) (z : Z.left) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (t : Sp k ⟶ S), Nonempty (Over.mk t ⟶ Z) := by
  let k := AlgebraicClosure (Z.left.residueField z)
  let p : Sp k ⟶ Z.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z.left.residueField z) k)) ≫
      Z.left.fromSpecResidueField z
  exact ⟨k, inferInstance, inferInstance, p ≫ Z.hom, ⟨Over.homMk p rfl⟩⟩

lemma mono_constDesc_of_geom {I : Type} {A : Over S} (x : I → (𝟙_ (Over S) ⟶ A))
    (hx : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (c d : I),
      toUnit (Over.mk t) ≫ x c = toUnit (Over.mk t) ≫ x d → c = d) : Mono (constDesc x) := by
  refine ⟨fun {Z} f g h => hom_ext_local f g fun z => ?_⟩
  obtain ⟨V, hV, c, hc⟩ := locally_const f z
  obtain ⟨W, hW, d, hd⟩ := locally_const g z
  have hc' := const_of_le (inf_le_left : V ⊓ W ≤ V) hc
  have hd' := const_of_le (inf_le_right : V ⊓ W ≤ W) hd
  obtain ⟨k, _, _, t, ⟨p⟩⟩ :=
    exists_geomPt (openObj Z (V ⊓ W)) (⟨z, hV, hW⟩ : (V ⊓ W : Z.left.Opens))
  obtain rfl : c = d := by
    apply hx k t
    rw [toUnit_unique (toUnit _) (p ≫ toUnit _), Category.assoc, Category.assoc,
      ← constPt_desc x c, ← constPt_desc x d, ← reassoc_of% hc', ← reassoc_of% hd', h]
  exact ⟨V ⊓ W, ⟨hV, hW⟩, hc'.trans hd'.symm⟩

end SectionQuot


open PointQuot SectionQuot in
theorem exists_quotient_by_finite_group_of_sections :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (C : Type) [CommGroup C] [Finite C] (i : C →* (𝟙_ (Over (Sp R)) ⟶ P.A)), (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (c : C), toUnit (Over.mk t) ≫ i c = 1 → c = 1) → ∃ (B : Over (Sp R)) (_ : GrpObj B) (ψ : P.A ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ c, i c ≫ ψ = 1) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (x : Over.mk t ⟶ P.A), x ≫ ψ = 1 ↔ ∃ c, x = toUnit _ ≫ i c := by
  open SectionQuot PointQuot in
    intro R _ _ P C _ _ i hi
    have L : Out.Laws := GlobalTheory.firstFiveLaws.1
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin C
    let x : Fin n → (𝟙_ (Over (Sp R)) ⟶ P.A) := fun c => i (e.symm c)
    have hr : Set.range x = i.range := by
      ext y
      exact ⟨by rintro ⟨c, rfl⟩; exact ⟨e.symm c, rfl⟩,
        by rintro ⟨c, rfl⟩; exact ⟨e c, by simp [x]⟩⟩
    have hmono : Mono (constDesc x) := mono_constDesc_of_geom x fun k _ _ t c d h => by
      apply e.symm.injective
      rw [← div_eq_one]
      apply hi k t
      rw [map_div, GrpObj.comp_div, div_eq_one]
      exact h
    obtain ⟨_, hhom⟩ := exists_grpObj_constObj x i.range hr
    have hs : FinEt.IsSplitOfRank (constObj (Sp R) (Fin n)).hom n :=
      (FinEt.isSplitOfRank_iff_exists_iso _ _).mpr ⟨Iso.refl _, Category.id_comp _⟩
    have het := hs.etale
    obtain ⟨B, _, hB, q, hq, hfin, hflat, hsurj, hker⟩ :=
      L.quotient R P (constObj (Sp R) (Fin n)) (constDesc x) hhom hmono hs.isFinite inferInstance
    have hw : constDesc x ≫ q = 1 := hker.w
    have hkill : ∀ c, i c ≫ q = 1 := fun c => by
      have : i c = x (e c) := by simp [x]
      rw [this, ← constPt_desc x (e c), Category.assoc, hw, MonObj.comp_one]
    refine ⟨B, inferInstance, q, hB, hq, hfin, ?_, hsurj, hkill,
      fun k _ _ t y => ⟨fun hy => ?_, ?_⟩⟩
    · refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
        ((H1.torsor_pullback (constDesc x) q hker).map (Over.forget _)).flip
        ⟨⟨hsurj, hflat⟩, inferInstanceAs (QuasiCompact q.left)⟩ ?_
      exact MorphismProperty.of_isPullback (P := @Etale) (IsPullback.of_hasPullback _ _) het
    · obtain ⟨z⟩ : Nonempty (Over.mk t).left := inferInstanceAs (Nonempty (PrimeSpectrum k))
      have : Subsingleton (Over.mk t).left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
      obtain ⟨V, hV, c, hc⟩ := locally_const_desc x (hker.lift y (toUnit _) hy) z
      rw [hker.lift_fst] at hc
      refine ⟨e.symm c, hom_ext_local _ _ fun z' => ⟨V, Subsingleton.elim z z' ▸ hV, ?_⟩⟩
      rw [hc, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
    · rintro ⟨c, rfl⟩
      rw [Category.assoc, hkill, MonObj.comp_one]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmExistsClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

theorem cmExists_closed : CMExistsSt :=
  GlobalTheory.T.cmPointObject_exists_of_laws GlobalTheory.T.exists_cmEllipticCurve_withPeriod GlobalTheory.cmPoint_closed GlobalTheory.thetaUnifAV_closed
    GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    (GlobalTheory.CM.homExtDvr_of_card_torsion GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional)
    GlobalTheory.kernelFiniteFlat_holds

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalWeilPairingEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FlatTors

theorem weilIs_of_cubWeil_of_proper {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (hpr : IsProper (pullback.snd G.hom f)) {L : RigLB G} (c : CubicalStr G L) (k : ℕ)
    (T : Over S') (x y : Over.mk (T.hom ≫ f) ⟶ G) (z : Γ(T.left, ⊤)ˣ) (h : GlobalTheory.UU.CubWeil c k x y z) :
    WeilIs G L.L (k : ℤ) x y z := by
  let G' : Over S' := (Over.pullback f).obj G
  have hp : IsGrpPullback G' G f (pullback.fst G.hom f) := isGrpPullback_pullback G f
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback f G hG
  have := hG'.comm
  have hA : IsAbelianScheme G' := ⟨hG'.comm, hG'.smooth, hpr, hG'.geomConnected⟩
  obtain ⟨hL, hr, ⟨c', hc'⟩, -⟩ := CubePf.cubePull _ _ G G' (cubeMapOf hp) L c
  have hw : pullback.fst G.hom f ≫ G.hom = G'.hom ≫ f := pullback.condition
  let β := GlobalTheory.UU.toBaseHom (GlobalTheory.UU.toBase_mul_pullback G f) T
  have inj : Function.Injective β := fun a b e =>
    Over.OverMorphism.ext (hp.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w a).trans (Over.w b).symm))
  have sur : Function.Surjective β := fun p =>
    ⟨Over.homMk (hp.1.lift p.left T.hom (Over.w p)) (hp.1.lift_snd _ _ _),
      Over.OverMorphism.ext (hp.1.lift_fst _ _ _)⟩
  obtain ⟨u, rfl⟩ := sur x
  obtain ⟨v, rfl⟩ := sur y
  have hu : u ^ k = 1 := inj (by rw [map_pow, map_one]; exact h.1)
  have hv : v ^ k = 1 := inj (by rw [map_pow, map_one]; exact h.2.1)
  obtain ⟨z', hz', -⟩ := GlobalTheory.UU.existsUnique_cubWeil c' hu hv
  have h₁ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f G G' (cubeMapOf hp) hw (GlobalTheory.UU.toBase_mul_pullback G f) L _ c c' hc'
    k T u v z' hz'
  obtain rfl : z = z' := h.unique h₁
  have h₂ := (GlobalTheory.UU.cubWeil_iff_weilIs GlobalTheory.SemiRigid.globalFns hA hu hv z).1 hz'
  exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ G G' f _ L.L _ L.isLB hL hp
    ⟨GlobalTheory.UU.pullIso _ _, GlobalTheory.UU.pullIso_isGen L.isLB _⟩ T k u v (β u) (β v) z rfl rfl).1 h₂

end GlobalTheory.FlatTors
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionToG
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FlatTors

open GlobalTheory.TorusModel GlobalTheory.TorsionFormCompare GlobalTheory.KernelNoTorsion

theorem exists_torsion_toG : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∃ (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), IsFinite N.hom ∧ Flat N.hom ∧ Etale (pullback.snd N.hom (jK R)) ∧ GtTors k g₀ ∧ (∀ (T : Over (Sp R)) (g : GtPt P.D.toPre T), GtTors k g → ∃! h : T ⟶ N, GtPt.IsPull h.left g₀ g) ∧ x₀ ^ k = 1 ∧ FormalEq P.U.toUnifPre x₀ g₀ := by
  intro E _ _ _ H R _ _ _ _ hR t P W _ _ ψW k hk
  obtain ⟨_, -, -, hc⟩ := hR
  have hL := abelianSchemeLaws_all.1
  obtain ⟨Gt, _, _, hH⟩ := exists_isGt hL.globalFns (splitExt P.D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hL.globalFns hH
  have hΦ : Represents Φ := hΦ
  have hfin : IsFinite (torsion Gt k).hom ∧ Flat (torsion Gt k).hom := by
    obtain ⟨h₁, h₂, -⟩ := hL.mulN _ P.D.toPre.P k hk
    have h₁' : IsFinite (𝟙 P.D.toPre.P.A ^ k).left := h₁
    have h₂' : Flat (𝟙 P.D.toPre.P.A ^ k).left := h₂
    rw [← MulEtaleDvr.mulN_eq_pow] at h₁' h₂'
    have Q := MulEtaleDvr.isPullback_torsion P.D.toPre.P.A k
    exact isFinite_flat_torsion_of_isGt _ (splitExt P.D.toPre) Gt hH k hk
      (MorphismProperty.of_isPullback (P := @IsFinite) Q h₁') (MorphismProperty.of_isPullback (P := @Flat) Q h₂')
  obtain ⟨hf, hl⟩ := hfin
  have hs := (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ _ hH).1
  haveI : CharZero (FractionRing R) := (RingHom.charZero_iff (IsFractionRing.injective R _)).1 inferInstance
  have hu : IsUnit (k : Γ(Sp (FractionRing R), ⊤)) :=
    MulEtaleDvr.isUnit_natCast_sections (Nat.cast_ne_zero.mpr (by omega)).isUnit
  have het : Etale (pullback.snd (torsion Gt k).hom (jK R)) := GlobalTheory.LamF.etale_pullback_torsion (jK R) Gt hu
  obtain ⟨J, hJ⟩ := exists_mulEquiv P.U.toUnifPre hL.globalFns hΦ
  have hN := isAdicColimit_of_isFinite hc (torsion Gt k)
  refine ⟨torsion Gt k, Φ _ (torsion.ι Gt k), J _ hN (torsion.ι Gt k), hf, hl, het,
    (tors_iff hΦ k _).2 (torsionι_pow Gt k), fun T g hg => ?_, ?_,
    (formalEq_iff _ _ _).2 ((hJ _ hN _ _).1 rfl)⟩
  · obtain ⟨x, rfl⟩ := (Φ T).surjective g
    have hx := (tors_iff hΦ k x).1 hg
    refine ⟨torsionLift x hx, (isPull_iff_comp hΦ _ _ _).2 (torsionLift_ι _ _), fun h hh => torsion_hom_ext ?_⟩
    rw [torsionLift_ι]
    exact (isPull_iff_comp hΦ _ _ _).1 hh
  · rw [← map_pow, torsionι_pow, map_one]

end GlobalTheory.FlatTors
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinFlatEtSplitTorus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TorusTorsion

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Sp R)}

theorem val_unitGen {X Y Z : Scheme.{0}} {L : LB X} (u : Γ(Y, ⊤)ˣ) (r : Z ⟶ Y) {z : Z} {J} (hJ : Good L z J) :
    val (GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.unitGen L u) r z J = gm r z ⊤ u :=
  gm_res _ z le_top (hJ.mem PEmpty.elim _) _

theorem isGen_unitGen {X Y : Scheme.{0}} (L : LB X) (u : Γ(Y, ⊤)ˣ) : (GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.unitGen L u).IsGen :=
  fun i j => by
    obtain rfl : i = j := funext fun k => k.elim
    exact ((congrArg₂ (· * ·) (Fintype.prod_empty _) rfl).trans (_root_.one_mul _)).symm

theorem TorusVal.val_eq {g : GtPt D T} {χ : D.X} {u : Γ(T.left, ⊤)ˣ} (h : TorusVal g χ u) {Z : Scheme.{0}}
    (r : Z ⟶ T.left) {z : Z} {J} (hJ : Good D.P.L z J) : val (g.s χ) r z J = gm r z ⊤ u :=
  (val_corr hJ h.2 r).trans (val_unitGen u r hJ)

theorem exists_torusPt (u : D.X →+ Additive Γ(T.left, ⊤)ˣ) :
    ∃ g : GtPt D T, ∀ χ, TorusVal g χ (Additive.toMul (u χ)) := by
  obtain ⟨g, hb, hv⟩ := exists_pt (D := D) (T := T) 1 (K := PEmpty) (φ := fun _ => PEmpty.elim) (ε := PEmpty.elim)
    (fun χ => GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.unitGen D.P.L (Additive.toMul (u χ))) (fun χ => isGen_unitGen _ _)
    (fun χ U i h => (GlobalTheory.FieldRestrictionTest.formEq_zero (D := D) (T := T) χ U h).symm)
    (fun y J hJ => by rw [val_unitGen _ _ hJ, map_zero, toMul_zero, map_one]) (fun χ χ' y J hJ => by
      have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      rw [C.face₃, val_unitGen _ _ hJ, val_unitGen _ _ hJ, val_unitGen _ _ hJ, map_add (f := _), toMul_add, map_mul,
        _root_.mul_one])
  exact ⟨g, fun χ => ⟨hb, corr_of_val D.P.isLB fun y J hJ => hv χ _ _ y J hJ⟩⟩

theorem isZero_iff' (g : GtPt D T) : g.IsZero ↔ g.b = 1 ∧ ∀ χ y J, Good D.P.L y J → cv g χ y J = 1 :=
  and_congr Iff.rfl (forall_congr' fun _ => ⟨fun h _ _ hJ => (val_corr hJ h _).trans (val_one _),
    fun h => corr_of_val D.P.isLB fun y J hJ => (h y J hJ).trans (val_one _).symm⟩)

theorem exists_nsmul_zero (k : ℕ) (u : D.X →+ Additive Γ(T.left, ⊤)ˣ) (hu : k • u = 0) {g : GtPt D T}
    (hg : ∀ χ, TorusVal g χ (Additive.toMul (u χ))) : ∃ h : GtPt D T, GtPt.IsNsmul k g h ∧ h.IsZero := by
  choose gs hgs using fun i : ℕ => exists_torusPt (D := D) (T := T) (i • u)
  have z : ∀ i : ℕ, i • u = 0 → (gs i).IsZero := fun i hi => (isZero_iff' _).2 ⟨(hgs i 0).1, fun χ y J hJ => by
    have := TorusVal.val_eq (hgs i χ) (𝟙 _) hJ
    rw [hi] at this
    exact this.trans (map_one _)⟩
  refine ⟨gs k, ⟨fun i => gs i, z 0 (zero_smul _ _), fun i => (TorusModel.isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩,
    rfl⟩, z k hu⟩
  · rw [(hgs _ 0).1, (hgs _ 0).1, (hg 0).1]
    exact (_root_.mul_one (1 : T ⟶ D.P.A)).symm
  · have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
    have hb : g.b = 1 := (hg 0).1
    rw [show th D y J (cP D _ χ) (gs (i.castSucc : Fin (k + 1))).b g.b = 1 by rw [hb, C.face₃], _root_.mul_one]
    refine (TorusVal.val_eq (hgs _ χ) _ hJ).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (TorusVal.val_eq (hgs _ χ) _ hJ) (TorusVal.val_eq (hg χ) _ hJ)).symm)
    rw [Fin.val_succ, Fin.val_castSucc, succ_nsmul, AddMonoidHom.add_apply, toMul_add, map_mul]

theorem isPull_of_units (h : T' ⟶ T) {g : GtPt D T} {g' : GtPt D T'} {u : D.X → Γ(T.left, ⊤)ˣ}
    {u' : D.X → Γ(T'.left, ⊤)ˣ} (hg : ∀ χ, TorusVal g χ (u χ)) (hg' : ∀ χ, TorusVal g' χ (u' χ))
    (e : ∀ χ, h.left.appTop.hom (u χ).val = (u' χ).val) : GtPt.IsPull h.left g g' := by
  refine (TorusModel.isPull_iff h g g').2 ⟨?_, fun χ y J hJ => ?_⟩
  · rw [(hg 0).1, (hg' 0).1]
    exact (MonObj.comp_one h).symm
  · refine (TorusVal.val_eq (hg' χ) _ hJ).trans (Eq.trans (Units.ext ?_) (TorusVal.val_eq (hg χ) _ hJ).symm)
    rw [gm_val _ y ⊤ trivial, gm_val _ y ⊤ trivial, ← e χ]
    rfl

variable {W : (Sp R).Opens}

end Points

end GlobalTheory.TorusTorsion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TrivOfAxesTrivPullbackEtaleIsogeny
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TrivOfAxesTrivPullbackEtaleIsogeny
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam GlobalTheory.AbLaw GlobalTheory.Biadditive

namespace GlobalTheory.IsogenyBitriv

theorem triv_pow {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {G : Type} [Monoid G] (F : G → (Y ⟶ X))
    (h₁ : Triv (L.pull (F 1)))
    (hm : ∀ x x', Triv (LB.LinComb L (K := Fin 3) ![F (x * x'), F x, F x'] ![1, -1, -1])) (x : G) (n : ℕ) :
    Triv (LB.LinComb L (K := Fin 2) ![F (x ^ n), F x] ![1, -(n : ℤ)]) := by
  induction n with
  | zero =>
    refine triv_of_formal hL h₁ fun U _ k => ?_
    simp [Fin.prod_univ_two]
  | succ n ih =>
    refine triv_of_formal hL (triv_mul (hm (x ^ n) x) ih) fun U _ k => ?_
    simp [Fin.prod_univ_two, Fin.prod_univ_three, Fintype.prod_sum_type, pow_succ, zpow_add, mul_comm,
      mul_left_comm, _root_.mul_assoc]
    exact Additive.ofMul.injective (by simp only [ofMul_mul, ofMul_inv]; abel)

theorem triv_of_triv_pull_isogeny :
    ∀ (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (ψ : A ⟶ B) (M : LB B.left) (N : LB (B ⊗ B).left) (n : ℕ), IsAbelianScheme A → IsAbelianScheme B → M.IsLB → Out.RelAmple B M → N.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → 0 < n → IsUnit (n : Γ(S, ⊤)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A), x ≫ ψ = 1 → x ^ n = 1) → (∃ t : (N.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) → (∃ t : (N.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen) → (∃ t : (N.pull (ψ ⊗ₘ ψ).left).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro S _ A B _ _ _ _ ψ M N n hA hB hM hamp hN hψ hfin het hsurj _ hn hker h₁ h₂ h₃
  have hG : Out.GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨mA, -, -, sA⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S A n hA hn
  have := hA.proper
  have := hB.smooth
  obtain ⟨ψ', hψ', e, -⟩ := GlobalTheory.HkFactor.exists_unique_factor S A B A ψ ((𝟙 A) ^ n) hA hB inferInstance hψ
    hfin het hsurj mA (fun k _ _ t x hx => by rw [MonObj.comp_pow, Category.comp_id]; exact hker k t x hx)
  have e' : ψ' ≫ ψ = (𝟙 B) ^ n := by
    have : Epi ψ.left := Flat.epi_of_flat_of_surjective ψ.left
    have : Epi ψ := Over.epi_of_epi_left ψ
    rw [← cancel_epi ψ, ← Category.assoc, e, MonObj.pow_comp, MonObj.comp_pow, Category.comp_id,
      Category.id_comp]
  have a₁ : ∀ {T : Over S} (y : T ⟶ B), Triv (N.pull (lift 1 y).left) := fun y => by
    have := triv_pull_comp h₁ y.left
    rwa [← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id] at this
  have a₂ : ∀ {T : Over S} (y : T ⟶ B), Triv (N.pull (lift y 1).left) := fun y => by
    have := triv_pull_comp h₂ y.left
    rwa [← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id] at this
  have key : ∀ {T : Over S} (a : T ⟶ A) (y : T ⟶ B), Triv (N.pull (lift ((a ≫ ψ) ^ n) y).left) := by
    intro T a y
    have bi := biadditive_of_triv_axes hG S B M hB hM hamp N hN h₁ h₂ T
    have p₁ := triv_pow hN (fun x : T ⟶ B => (lift x y).left) (a₁ y) (fun x x' => (bi x x' y).1) (a ≫ ψ) n
    have p₂ := triv_pow hN (fun x : T ⟶ B => (lift (a ≫ ψ) x).left) (a₂ _)
      (fun x x' => (bi x x' (a ≫ ψ)).2) y n
    have p₃ : Triv (N.pull (lift (a ≫ ψ) (y ^ n)).left) := by
      have := triv_pull_comp h₃ (lift a (y ≫ ψ')).left
      rwa [← Over.comp_left, lift_map, Category.assoc, e', MonObj.comp_pow, Category.comp_id] at this
    refine triv_of_formal hN (triv_mul (triv_mul p₁ (triv_inv p₂)) p₃) fun U _ k => ?_
    simp [Fin.prod_univ_two, Fintype.prod_sum_type, _root_.mul_assoc]
  have : IsReduced B.left := GlobalTheory.isReduced_of_smooth_of_isReduced B.hom
  have hp : IsPullback (snd B B).left (fst B B).left B.hom B.hom :=
    (IsPullback.of_hasPullback B.hom B.hom).flip
  refine GlobalTheory.seesaw_reduced_of_dense hG S B M hB hM hamp B.left (B ⊗ B).left B.hom (snd B B).left
    (fst B B).left N hp hN ?_ (lift (𝟙 B) (1 : B ⟶ B)).left ?_ h₂
  · intro p
    refine subset_closure ?_
    have : Surjective ((𝟙 A ^ n) ≫ ψ).left := by rw [Over.comp_left]; infer_instance
    obtain ⟨a, ha⟩ := ((𝟙 A ^ n) ≫ ψ).left.surjective p
    have hr : Set.range (A.left.fromSpecResidueField a) = {a} := Scheme.range_fromSpecResidueField _
    obtain ⟨z, hz⟩ := hr.ge rfl
    let j := A.left.fromSpecResidueField a
    let g := j ≫ ((𝟙 A ^ n) ≫ ψ).left
    refine ⟨A.left.residueField a, inferInstance, g, _, _, _, ⟨z, ?_⟩,
      IsPullback.of_hasPullback (fst B B).left g, ?_⟩
    · exact (congrArg (fun w => ((𝟙 A ^ n) ≫ ψ).left w) hz).trans ha
    · let ρ := pullback.fst (fst B B).left g
      let T : Over S := Over.mk (ρ ≫ (B ⊗ B).hom)
      let r : T ⟶ B ⊗ B := Over.homMk ρ rfl
      let b : T ⟶ A := Over.homMk (pullback.snd (fst B B).left g ≫ j) (by
        have c := congrArg (· ≫ B.hom) (pullback.condition (f := (fst B B).left) (g := g))
        simp only [g, Category.assoc, Over.w] at c
        exact (Category.assoc _ _ _).trans c.symm)
      have hr : r ≫ fst B B = (b ≫ ψ) ^ n := by
        have : (b ≫ ψ) ^ n = b ≫ (𝟙 A ^ n) ≫ ψ := by
          rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, MonObj.pow_comp]
        rw [this]
        apply Over.OverMorphism.ext
        exact pullback.condition.trans (Category.assoc _ _ _).symm
      have := key b (r ≫ snd B B)
      rw [← hr, lift_comp_fst_snd] at this
      exact this
  · rw [← Over.comp_left, lift_fst, Over.id_left]

end GlobalTheory.IsogenyBitriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TrivOfAxesTrivPullbackEtaleIsogenyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triv_of_axes_triv_pullback_etale_isogeny : ∀ (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (ψ : A ⟶ B) (M : LB B.left) (N : LB (B ⊗ B).left) (n : ℕ), IsAbelianScheme A → IsAbelianScheme B → M.IsLB → Out.RelAmple B M → N.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → 0 < n → IsUnit (n : Γ(S, ⊤)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A), x ≫ ψ = 1 → x ^ n = 1) → (∃ t : (N.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) → (∃ t : (N.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen) → (∃ t : (N.pull (ψ ⊗ₘ ψ).left).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  first | exact @GlobalTheory.IsogenyBitriv.triv_of_triv_pull_isogeny | exact GlobalTheory.IsogenyBitriv.triv_of_triv_pull_isogeny | (intros; apply GlobalTheory.IsogenyBitriv.triv_of_triv_pull_isogeny <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPullbackPow
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.ExtensionMul

section General

variable {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]

theorem exists_isPullback_pow [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ)
    {P P' Q : Over S} {a : P ⟶ G} {b : P ⟶ B} (hP : IsPullback a b q ((𝟙 B) ^ N))
    {φ : G ⟶ P} (hφa : φ ≫ a = (𝟙 G) ^ N) (hφb : φ ≫ b = q)
    {p : P' ⟶ P} {y : P' ⟶ G} (hP' : IsPullback y p q b)
    {s : Q ⟶ P'} {r : Q ⟶ G} (hQ : IsPullback s r p φ) :
    ∃ (c : P' ⟶ T) (t : Q ⟶ T), IsPullback s t c ((𝟙 T) ^ N) := by
  have inj : ∀ {W : Over S} {x y : W ⟶ T}, x ≫ i = y ≫ i → x = y := fun h =>
    hk.hom_ext h (toUnit_unique _ _)
  have ex : ∀ {W : Over S} (x : W ⟶ G), x ≫ q = 1 → ∃ y : W ⟶ T, y ≫ i = x := fun x h =>
    ⟨hk.lift x (toUnit _) (by rw [h, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hiq : i ≫ q = 1 := by rw [hk.w, Hom.one_def]
  obtain ⟨c, hc⟩ := ex ((p ≫ a) / y ^ N) (by
    rw [GrpObj.div_comp, Category.assoc, hP.w, MonObj.pow_comp, hP'.w, ← Category.assoc, MonObj.comp_pow,
      Category.comp_id, div_self'])
  have hsr : s ≫ y ≫ q = r ≫ q := by
    rw [hP'.w, ← Category.assoc, hQ.w, Category.assoc, hφb]
  have hsa : s ≫ p ≫ a = r ^ N := by
    rw [← Category.assoc, hQ.w, Category.assoc, hφa, MonObj.comp_pow, Category.comp_id]
  obtain ⟨t, ht⟩ := ex (r / (s ≫ y)) (by
    rw [GrpObj.div_comp, Category.assoc, hsr, div_self'])
  refine ⟨c, t, ⟨?_⟩, ⟨PullbackCone.isLimitAux' _ fun W => ?_⟩⟩
  · apply inj
    rw [MonObj.comp_pow, Category.comp_id, MonObj.pow_comp, ht, div_pow, Category.assoc, hc, GrpObj.comp_div, hsa,
      MonObj.comp_pow]
  · have hW : W.fst ≫ c = W.snd ^ N := by rw [W.condition, MonObj.comp_pow, Category.comp_id]
    have hl : W.fst ≫ p = ((W.snd ≫ i) * (W.fst ≫ y)) ≫ φ := by
      refine hP.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, hφa, MonObj.comp_pow, Category.comp_id, mul_pow,
          ← MonObj.pow_comp _ _ i, ← hW, Category.assoc, hc, GrpObj.comp_div, MonObj.comp_pow, div_mul_cancel]
      · rw [Category.assoc, Category.assoc, hφb, MonObj.mul_comp, Category.assoc, Category.assoc, hiq,
          MonObj.comp_one, _root_.one_mul, hP'.w]
    refine ⟨hQ.lift W.fst _ hl, hQ.lift_fst _ _ _, ?_, ?_⟩
    · apply inj
      change (_ ≫ t) ≫ i = _
      rw [Category.assoc, ht, GrpObj.comp_div, ← Category.assoc, hQ.lift_fst, hQ.lift_snd, mul_div_cancel_right]
    · intro (m : W.pt ⟶ Q) (h1 : m ≫ s = W.fst) (h2 : m ≫ t = W.snd)
      change m = _
      refine hQ.hom_ext (by rw [hQ.lift_fst, h1]) ?_
      rw [hQ.lift_snd, ← h1, ← h2, Category.assoc, Category.assoc, ht, GrpObj.comp_div, div_mul_cancel]

theorem of_pow_kernel (Pr : MorphismProperty Scheme.{0}) [Pr.IsStableUnderBaseChange]
    [Pr.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    [Surjective q.left] [Flat q.left] [QuasiCompact q.left]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ)
    {P : Over S} {a : P ⟶ G} {b : P ⟶ B} (hP : IsPullback a b q ((𝟙 B) ^ N))
    {φ : G ⟶ P} (hφa : φ ≫ a = (𝟙 G) ^ N) (hφb : φ ≫ b = q) (h : Pr ((𝟙 T) ^ N : T ⟶ T).left) :
    Pr φ.left := by
  have hP' := IsPullback.of_hasPullback q b
  have hQ := IsPullback.of_hasPullback (pullback.snd q b) φ
  obtain ⟨c, t, H⟩ := exists_isPullback_pow i q hk N hP hφa hφb hP' hQ
  have hP'' := hP'.map (Over.forget S)
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := Pr)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (hQ.map (Over.forget S)) ⟨⟨?_, ?_⟩, ?_⟩ ?_
  · exact MorphismProperty.of_isPullback (P := @Surjective) hP'' ‹_›
  · exact MorphismProperty.of_isPullback (P := @Flat) hP'' ‹_›
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hP'' ‹_›
  · exact MorphismProperty.of_isPullback (P := Pr) (H.map (Over.forget S)).flip h

end General

theorem pow_of_isGt {S : Scheme.{0}} (E : SplitExt S) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : E.IsGt G)
    (N : ℕ) (hN : 1 ≤ N) (h1 : IsFinite ((𝟙 E.B) ^ N : E.B ⟶ E.B).left) (h2 : Flat ((𝟙 E.B) ^ N : E.B ⟶ E.B).left)
    (h3 : Surjective ((𝟙 E.B) ^ N : E.B ⟶ E.B).left) :
    IsFinite ((𝟙 G) ^ N : G ⟶ G).left ∧ Flat ((𝟙 G) ^ N : G ⟶ G).left ∧ Surjective ((𝟙 G) ^ N : G ⟶ G).left := by
  obtain ⟨D⟩ := hG
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have hN' : N ≠ 0 := by omega
  have hf : IsFinite (mulN (splitTorus S E.X) N).left := Diag.isFinite_mulN S E.X hN'
  have hl : Flat (mulN (splitTorus S E.X) N).left := Diag.flat_mulN S E.X hN'
  have hs : Surjective (mulN (splitTorus S E.X) N).left := Diag.surjective_mulN S E.X hN'
  rw [MulEtaleDvr.mulN_eq_pow] at hf hl hs
  have := flat_descendsAlong_fpqc
  have := isAffineHom_descendsAlong_fpqc.{0}
  have hP := IsPullback.of_hasPullback D.q ((𝟙 E.B) ^ N)
  have w : ((𝟙 G) ^ N) ≫ D.q = D.q ≫ ((𝟙 E.B) ^ N) := by
    rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have ha := hP.lift_fst _ _ w
  have hb := hP.lift_snd _ _ w
  have a0 : Surjective (hP.lift _ _ w).left := of_pow_kernel @Surjective D.i D.q D.isKernel N hP ha hb hs
  have a1 : Flat (hP.lift _ _ w).left := of_pow_kernel @Flat D.i D.q D.isKernel N hP ha hb hl
  have a2 : IsAffineHom (hP.lift _ _ w).left :=
    of_pow_kernel @IsAffineHom D.i D.q D.isKernel N hP ha hb inferInstance
  have a3 : UniversallyClosed (hP.lift _ _ w).left :=
    of_pow_kernel @UniversallyClosed D.i D.q D.isKernel N hP ha hb inferInstance
  have a4 : LocallyOfFiniteType (hP.lift _ _ w).left :=
    of_pow_kernel @LocallyOfFiniteType D.i D.q D.isKernel N hP ha hb inferInstance
  have a5 : IsFinite (hP.lift _ _ w).left :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
      ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩
  have hP' := (hP.map (Over.forget S)).flip
  have b1 : IsFinite (pullback.fst D.q ((𝟙 E.B) ^ N)).left := MorphismProperty.of_isPullback (P := @IsFinite) hP' h1
  have b2 : Flat (pullback.fst D.q ((𝟙 E.B) ^ N)).left := MorphismProperty.of_isPullback (P := @Flat) hP' h2
  have b3 : Surjective (pullback.fst D.q ((𝟙 E.B) ^ N)).left :=
    MorphismProperty.of_isPullback (P := @Surjective) hP' h3
  rw [← ha, Over.comp_left]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem exists_represents_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), ∃ (Gt : Over (Sp R)) (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ ∧ Smooth Gt.hom ∧ IsSeparated Gt.hom ∧ ∀ k : ℕ, 1 ≤ k → IsFinite ((𝟙 Gt) ^ k : Gt ⟶ Gt).left ∧ Flat ((𝟙 Gt) ^ k : Gt ⟶ Gt).left ∧ Surjective ((𝟙 Gt) ^ k : Gt ⟶ Gt).left := by
  intro R _ _ _ D
  have hL := abelianSchemeLaws_all.1
  obtain ⟨H, _, _, hH⟩ := TorusModel.exists_isGt hL.globalFns (TorusModel.splitExt D)
  obtain ⟨Φ, hΦ⟩ := TorusModel.exists_points hL.globalFns hH
  refine ⟨H, inferInstance, inferInstance, Φ, hΦ,
    (UnitRigidity.smooth_geometricallyConnected_of_isGt _ H hH).1, ?_, fun k hk => ?_⟩
  · obtain ⟨d⟩ := hH
    have := d.q_affine
    have := (TorusModel.splitExt D).isAbelian.proper
    rw [← Over.w d.q]
    infer_instance
  · obtain ⟨h₁, h₂, h₃, -⟩ := hL.mulN _ D.P k hk
    exact pow_of_isGt _ H hH k hk h₁ h₂ h₃

end GlobalTheory.ExtensionMul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TensorObjectAndCurveExistsIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.ExCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]; rfl

theorem weilIs_iff {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (s' : Sp ℂ ⟶ S') (s : Sp ℂ ⟶ S) (hs : s = s' ≫ f) (k : ℤ) (x y : Over.mk s' ⟶ t'.G) (x₀ y₀ : Over.mk s ⟶ t.G)
    (c : ℂˣ) (hx : x₀.left = x.left ≫ m.φ) (hy : y₀.left = y.left ≫ m.φ) :
    Out.WeilIs t'.G t'.PP.L k x y (unitOn c) ↔ Out.WeilIs t.G t.PP.L k x₀ y₀ (unitOn c) := by
  subst hs
  have hL : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  exact weilIs_grpPullback_of_comm _ _ _ _ _ m.φ _ _ t.PP.isLB t'.PP.isLB m.cart hL (Over.mk s') k x y x₀ y₀ _ hx hy

theorem exists_isExp_of_family {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ₀ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ₀ ty) (i : Fin FU.n) {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (FU.Di i) ty Pe) {R K : Type} [CommRing R] [Field K] (f : R →+* K) (σ : K →+* ℂ)
    (B : PAT H (Sp R)) {y : Sp K ⟶ Xo.X} {t : SAB H (Sp K)} (m : SABMap t Xo.univ.t y) (n : SABMap t B.t (spMap f))
    (hy : spMap σ ≫ y = FU.u i Pe) :
    ∃ eB : (Fin g → ℂ) → (Over.mk (spMap (σ.comp f)) ⟶ B.t.G), IsExp B (σ.comp f) (FU.Di i) ty Pe eB ∧
      ∀ z, ∃ x : Sp ℂ ⟶ t.G.left, x ≫ t.G.hom = spMap σ ∧ x ≫ n.φ = (eB z).left ∧ x ≫ m.φ = (FU.ex i Pe z).left := by
  obtain ⟨p, hp⟩ := LiePull.exists_pushEquiv m.cart (Over.mk (spMap σ)) (FU.u i Pe) hy.symm
  obtain ⟨q, hq⟩ := LiePull.exists_pushEquiv n.cart (Over.mk (spMap σ)) (spMap (σ.comp f)) (spMap_comp f σ).symm
  have hp' : ∀ z, (p.symm (FU.ex i Pe z)).left ≫ m.φ = (FU.ex i Pe z).left := fun z => by
    rw [← hp, p.apply_symm_apply]
  refine ⟨fun z => q (p.symm (FU.ex i Pe z)), ⟨hP, ?_, fun z w => ?_,
    q.surjective.comp (p.symm.surjective.comp (FU.ex_onto i Pe hP)), fun z => ?_, fun a z => ?_,
    fun k a b c hk hc => ?_⟩, fun z => ⟨(p.symm (FU.ex i Pe z)).left, Over.w _, (hq _).symm, hp' z⟩⟩
  · have hpb := (IsPullback.of_hasPullback t.G.hom (spMap σ)).paste_horiz m.cart.1
    let c : (Fin g → ℂ) → (Sp ℂ ⟶ pullback t.G.hom (spMap σ)) := fun z =>
      pullback.lift (p.symm (FU.ex i Pe z)).left (𝟙 _) ((Over.w _).trans (Category.id_comp _).symm)
    have hc := ThetaPoint.isHolTo_fibre hpb c (fun z => pullback.lift_snd _ _ _) (by
      have e : (fun z => c z ≫ pullback.fst t.G.hom (spMap σ) ≫ m.cm.F) = fun z => (FU.ex i Pe z).left :=
        funext fun z => by rw [← Category.assoc, pullback.lift_fst]; exact hp' z
      rw [e]
      exact ExpUniqFamily.isHolTo_ex FU i Pe hP)
    have e : (fun z => (q (p.symm (FU.ex i Pe z))).left) = fun z => c z ≫ pullback.fst t.G.hom (spMap σ) ≫ n.φ :=
      funext fun z => by rw [← Category.assoc, pullback.lift_fst]; exact hq _
    rw [e]
    exact isHolTo_comp_hom hc _
  · beta_reduce
    rw [FU.ex_add i Pe hP, map_mul, map_mul]
  · exact (map_eq_one_iff q q.injective).trans ((map_eq_one_iff _ p.symm.injective).trans (FU.ex_ker i Pe hP z))
  · have e : p.symm (FU.ex i Pe z ≫ Xo.univ.t.act.act a) = p.symm (FU.ex i Pe z) ≫ t.act.act a := by
      rw [p.symm_apply_eq]
      apply Over.OverMorphism.ext
      rw [hp, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc]
      exact congrArg (· ≫ _) (hp' z).symm
    apply Over.OverMorphism.ext
    beta_reduce
    rw [FU.ex_lin i Pe hP, e, Over.comp_left, hq, hq, Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg _ (n.act a)
  · exact (weilIs_iff n _ _ (spMap_comp f σ).symm k _ _ _ _ c (hq _) (hq _)).1
      ((weilIs_iff m _ _ hy.symm k _ _ _ _ c (hp' _).symm (hp' _).symm).2 (FU.ex_weil i Pe hP k a b c hk hc))

section Comparison₂

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n} {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
  {hP : IsPeriod (FU.Di i) ty Pe}

end Comparison₂

section CMStatement

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n} {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
  {hP : IsPeriod (FU.Di i) ty Pe}

end CMStatement

section Tensor

end Tensor

section TensorStatement

variable {M : Type} [Field M] [NumberField M] {ω : 𝓞 M}

end TensorStatement

end GlobalTheory.CM.ExCompare
end
end
