module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaImmersionTorusExtensionProjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaFamilyPrescribedLeadingTerm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAlongPlaceNeighboursRingEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFromBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsFiniteQCHomModOfExact

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionAppLESurjectiveAndKer
open CategoryTheory Limits

namespace GlobalTheory.TorsionChart

theorem pushout_inl_surjective_and_ker {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ D} {j : C ⟶ D} (po : IsPushout f g i j) (hg : Function.Surjective g.hom) :
    Function.Surjective i.hom ∧ RingHom.ker i.hom = Ideal.map f.hom (RingHom.ker g.hom) := by
  set I := Ideal.map f.hom (RingHom.ker g.hom) with hIdef
  have hw : ∀ a, i.hom (f.hom a) = j.hom (g.hom a) := fun a => congr($(po.w).hom a)
  have hI : I ≤ RingHom.ker i.hom := by
    rw [hIdef, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, hw, (RingHom.mem_ker).1 ha, map_zero]
  let mk : B ⟶ CommRingCat.of (B ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have hker : RingHom.ker g.hom ≤ RingHom.ker ((Ideal.Quotient.mk I).comp f.hom) := by
    intro a ha
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  let φ : {g' : A →+* B ⧸ I // RingHom.ker g.hom ≤ RingHom.ker g'} :=
    ⟨(Ideal.Quotient.mk I).comp f.hom, hker⟩
  let ψ : C ⟶ CommRingCat.of (B ⧸ I) := CommRingCat.ofHom (g.hom.liftOfSurjective hg φ)
  have hψ : f ≫ mk = g ≫ ψ := by
    ext a
    exact (RingHom.liftOfSurjective_comp_apply g.hom hg φ a).symm
  let lift : CommRingCat.of (B ⧸ I) ⟶ D := CommRingCat.ofHom (Ideal.Quotient.lift I i.hom hI)
  have h1 : i ≫ po.desc mk ψ hψ = mk := po.inl_desc _ _ _
  have h2 : po.desc mk ψ hψ ≫ lift = 𝟙 D := by
    refine po.hom_ext ?_ ?_
    · rw [← Category.assoc, h1, Category.comp_id]
      ext b
      rfl
    · rw [← Category.assoc, po.inr_desc, Category.comp_id]
      ext c
      obtain ⟨a, rfl⟩ := hg c
      change lift.hom (ψ.hom (g.hom a)) = j.hom (g.hom a)
      rw [show ψ.hom (g.hom a) = mk.hom (f.hom a) from
        (RingHom.liftOfSurjective_comp_apply g.hom hg φ a), ← hw]
      rfl
  refine ⟨fun d => ?_, le_antisymm (fun b hb => ?_) hI⟩
  · obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((po.desc mk ψ hψ).hom d)
    refine ⟨b, ?_⟩
    have := congr($(h2).hom d)
    change lift.hom ((po.desc mk ψ hψ).hom d) = d at this
    rw [← hb] at this
    exact this
  · have := congr($(h1).hom b)
    change (po.desc mk ψ hψ).hom (i.hom b) = Ideal.Quotient.mk I b at this
    rw [(RingHom.mem_ker).1 hb, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm

end GlobalTheory.TorsionChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteThetaSectionsThickeningCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreThetaSectionGermEqFourierRatioMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreThetaSectionGermEqFourierRatioMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mum.FibreGerm.secGerm_eq_secRatio_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (ψ : Over.mk ((thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0) ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) (𝟙 (thickObj R (maximalIdeal R) 0 G).left) (Y.Φ _ ψ) → ∀ (k N : ℕ) (α : Fin N → D.toPre.X) (b : ∀ j, D.toPre.SecB k (α j)) (τ : Fin N → SecK D.toPre.P.L Y.q.left k) (F : Fin N → IntFam (maximalIdeal R) D.toPre k) (s : Fin N → H0 U.LG.L k), (∀ j, IsTermOf Y (b j) (τ j)) → (∀ j, (F j).Lead (α j) (b j)) → (∀ j, U.ExpandsAt 0 k (s j) (F j).f) → ∀ (z : (thickObj R (maximalIdeal R) 0 G).left) (j : Fin N) (i : Fin 1 → U.LG.L.ι), ψ.left z ∈ nonzeroLocus (τ j) → (fstG (maximalIdeal R) 0 G).left z ∈ secChart U.LG.L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s l) i = gs (Y := (thickObj R (maximalIdeal R) 0 G).left) ψ.left z (nonzeroLocus (τ j)) (GlobalTheory.ProjSpace.secRatio (τ j) (τ l)) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s j) i := by
  intro R _ _ _ D A G _ _ U Y ψ hP k N α b τ F s hT hL hE z j i hτz hi
  obtain ⟨J, hJ⟩ := GlobalTheory.TorusCoord.exists_good' U.LG.isLB z
  obtain ⟨J', hJ'⟩ := GlobalTheory.TorusCoord.exists_good' D.toPre.P.isLB z
  obtain ⟨c, hc⟩ := GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term R D A G U Y _ (𝟙 _) ψ hP k z J J' hJ hJ'
  have hv : ∀ l, secGerm (fstG (maximalIdeal R) 0 G).left z (s l)
      (fun _ => J ((fstG (maximalIdeal R) 0 G).left ≫ 𝟙 _)) = c.val * sval (τ l) ψ.left z J' := by
    intro l
    have := hc (α l) (b l) (τ l) (F l) (s l) (hT l) (hL l) (hE l)
    rw [Category.id_comp] at this
    exact this
  obtain ⟨a, ha⟩ := exists_unit_secGerm k (fstG (maximalIdeal R) 0 G).left z hi
    (hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (fstG (maximalIdeal R) 0 G).left)
  let jt : Fin 1 → D.toPre.P.L.ι := fun _ => J' (ψ.left ≫ Y.q.left)
  have hzt : ψ.left z ∈ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) jt :=
    hJ'.mem (fun _ : Fin 1 => Y.q.left) ψ.left
  have hzW : ψ.left z ∈ nonzeroLocus (τ j) ⊓ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) jt := ⟨hτz, hzt⟩
  have hk : nonzeroLocus (τ j) ⊓ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) jt ≤
      (LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => Y.q.left) (fun _ => (k : ℤ))).U jt := inf_le_right
  have ha' : nonzeroLocus (τ j) ⊓ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) jt ≤ nonzeroLocus (τ j) :=
    inf_le_left
  have hu : ∀ l, sval (τ l) ψ.left z J' =
      gs ψ.left z (nonzeroLocus (τ j)) (GlobalTheory.ProjSpace.secRatio (τ j) (τ l)) * sval (τ j) ψ.left z J' := by
    intro l
    have e := congrArg (gs ψ.left z _) (GlobalTheory.ProjSpace.secRatio_on (τ j) (τ l) jt ha' hk)
    rw [sval_of (τ l) ψ.left z J' jt (fun _ => rfl), sval_of (τ j) ψ.left z J' jt (fun _ => rfl)]
    exact ((gs_res _ _ hk hzW _).symm.trans e).trans ((gs_mul _ _ _ hzW _ _).trans
      (congrArg₂ (· * ·) (gs_res _ _ ha' hzW _) (gs_res _ _ hk hzW _)))
  have hunit : IsUnit (sval (τ j) ψ.left z J') := by
    obtain ⟨w, hw⟩ := GlobalTheory.ProjSpace.isUnit_resG_sec (τ j) jt ha' hk
    rw [sval_of (τ j) ψ.left z J' jt (fun _ => rfl)]
    have e : gs ψ.left z _ ((τ j).f jt) = (gm ψ.left z _ w).val :=
      (gs_res _ _ hk hzW _).symm.trans ((congrArg (gs ψ.left z _) hw.symm).trans (gs_unit _ _ _ hzW w))
    exact e ▸ Units.isUnit _
  refine ⟨?_, fun l => ?_⟩
  · rw [ha, hv j]
    exact a.isUnit.mul (c.isUnit.mul hunit)
  · rw [ha, ha, hv, hv, hu l]
    ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreThetaSectionGermEqFourierRatioMulStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_thetaSectionGerm_eq_fourierRatio_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (ψ : Over.mk ((thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0) ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) (𝟙 (thickObj R (maximalIdeal R) 0 G).left) (Y.Φ _ ψ) → ∀ (k N : ℕ) (α : Fin N → D.toPre.X) (b : ∀ j, D.toPre.SecB k (α j)) (τ : Fin N → SecK D.toPre.P.L Y.q.left k) (F : Fin N → IntFam (maximalIdeal R) D.toPre k) (s : Fin N → H0 U.LG.L k), (∀ j, IsTermOf Y (b j) (τ j)) → (∀ j, (F j).Lead (α j) (b j)) → (∀ j, U.ExpandsAt 0 k (s j) (F j).f) → ∀ (z : (thickObj R (maximalIdeal R) 0 G).left) (j : Fin N) (i : Fin 1 → U.LG.L.ι), ψ.left z ∈ nonzeroLocus (τ j) → (fstG (maximalIdeal R) 0 G).left z ∈ secChart U.LG.L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s l) i = gs (Y := (thickObj R (maximalIdeal R) 0 G).left) ψ.left z (nonzeroLocus (τ j)) (GlobalTheory.ProjSpace.secRatio (τ j) (τ l)) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s j) i := by
  first | exact @GlobalTheory.Mum.FibreGerm.secGerm_eq_secRatio_mul | exact GlobalTheory.Mum.FibreGerm.secGerm_eq_secRatio_mul | (intros; apply GlobalTheory.Mum.FibreGerm.secGerm_eq_secRatio_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreTorusCoordinatesIsImmersion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreTorusCoordinatesIsImmersion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.ClosedFibreImm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (ψ : Over.mk ((thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0) ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) (𝟙 (thickObj R (maximalIdeal R) 0 G).left) (Y.Φ _ ψ) → IsImmersion ψ.left := by
  intro R _ _ _ D A G _ _ U Y ψ h
  set g := U.gt 0 with hg
  let G₀ := thickObj R (maximalIdeal R) 0 G
  let T : Over (Sp R) := Over.mk (G₀.hom ≫ thick R (maximalIdeal R) 0)
  have hcl : IsClosedImmersion (thick R (maximalIdeal R) 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  let T₀ : Over (Sp R) := Over.mk (pullback.fst Y.H.hom (thick R (maximalIdeal R) 0) ≫ Y.H.hom)
  let ξ := Y.Φ T₀ (Over.homMk (pullback.fst Y.H.hom (thick R (maximalIdeal R) 0)) rfl)
  obtain ⟨χ, hχ⟩ := GlobalTheory.TorusCoord.exists_point g (T := T₀) (pullback.snd Y.H.hom (thick R (maximalIdeal R) 0))
    pullback.condition.symm ξ
  let ψ' : G₀.left ⟶ pullback Y.H.hom (thick R (maximalIdeal R) 0) := pullback.lift ψ.left G₀.hom (Over.w ψ)
  have hψ' : ψ' ≫ pullback.fst _ _ = ψ.left := pullback.lift_fst _ _ _

  have hw1 : ψ' ≫ pullback.fst Y.H.hom (thick R (maximalIdeal R) 0) ≫ Y.H.hom = T.hom := by
    rw [← Category.assoc, hψ']; exact Over.w ψ
  let k : T ⟶ T₀ := Over.homMk ψ' hw1
  have hkx : k ≫ (Over.homMk (pullback.fst Y.H.hom (thick R (maximalIdeal R) 0)) rfl : T₀ ⟶ Y.H) = ψ :=
    Over.OverMorphism.ext (by simpa [k] using hψ')
  have hpull := Y.rep.1 T T₀ k (Over.homMk (pullback.fst Y.H.hom (thick R (maximalIdeal R) 0)) rfl)
  rw [hkx] at hpull
  have h1 : GlobalTheory.TorusCoord.IsPointOf g (ψ' ≫ χ) (Y.Φ T ψ) := hχ.pull g hpull
  have e1 : ψ' ≫ χ = 𝟙 _ := h1.unique_left g h
  have hc := hχ.comp_hom g
  have hw2 : χ ≫ T.hom = T₀.hom := hc
  let k' : T₀ ⟶ T := Over.homMk χ hw2
  have hpull' := Y.rep.1 T₀ T k' ψ
  have h2 : GlobalTheory.TorusCoord.IsPointOf g (χ ≫ 𝟙 _) (Y.Φ T₀ (k' ≫ ψ)) := h.pull g hpull'
  rw [Category.comp_id] at h2
  have e2 : Y.Φ T₀ (k' ≫ ψ) = ξ := h2.unique_right g hχ
  have e3 : k' ≫ ψ = Over.homMk (pullback.fst Y.H.hom (thick R (maximalIdeal R) 0)) rfl := (Y.Φ T₀).injective e2
  have e4 : χ ≫ ψ.left = pullback.fst Y.H.hom (thick R (maximalIdeal R) 0) := congrArg (·.left) e3
  have e5 : χ ≫ G₀.hom = pullback.snd Y.H.hom (thick R (maximalIdeal R) 0) := by
    rw [← cancel_mono (thick R (maximalIdeal R) 0), Category.assoc, ← pullback.condition]
    exact hc
  have e6 : χ ≫ ψ' = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hψ', e4, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, e5, Category.id_comp]
  have : IsIso ψ' := ⟨⟨χ, e1, e6⟩⟩
  rw [← hψ']
  infer_instance

end GlobalTheory.Mum.ClosedFibreImm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreTorusCoordinatesIsImmersionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_torusCoordinates_isImmersion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (ψ : Over.mk ((thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0) ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) (𝟙 (thickObj R (maximalIdeal R) 0 G).left) (Y.Φ _ ψ) → IsImmersion ψ.left := by
  first | exact @GlobalTheory.Mum.ClosedFibreImm.main | exact GlobalTheory.Mum.ClosedFibreImm.main | (intros; apply GlobalTheory.Mum.ClosedFibreImm.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFractionsProjSpaceImmersion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFractionsProjSpaceImmersion
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ProjSpace

theorem surjective_appLE_of_eq {X Z : Scheme.{0}} {f : Z ⟶ X} {A A' : X.Opens} {B B' : Z.Opens}
    (hA : A = A') (hB : B = B') (h : B ≤ f ⁻¹ᵁ A) (h' : B' ≤ f ⁻¹ᵁ A') :
    Function.Surjective (f.appLE A B h).hom → Function.Surjective (f.appLE A' B' h').hom := by
  subst hA hB
  exact id

theorem exists_affineOpen_fraction_pullRatio : ∀ (R : Type) [CommRing R] (N : ℕ) (Y : Scheme.{0}) (φ : Y ⟶ PSpace R N), IsImmersion φ → ∀ (y : Y) (V : Y.Opens) (i : Fin (N + 1)), y ∈ V → φ y ∈ GlobalTheory.ProjSpace.chart R N i → ∃ (W : Y.Opens) (hW : W ≤ φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N i), y ∈ W ∧ W ≤ V ∧ IsAffineOpen W ∧ ∀ g : Γ(Y, W), ∃ P Q : MvPolynomial (Fin (N + 1)) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) Q = MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) P := by
  intro R _ N Y φ hφ y V i hyV hyi
  obtain ⟨U', hU', hU⟩ := φ.isEmbedding.isInducing.isOpen_iff.1 V.isOpen
  let O : (PSpace R N).Opens := ⟨U', hU'⟩ ⊓ φ.coborderRange
  have hyO : φ y ∈ O := ⟨show φ y ∈ U' by rw [← Set.mem_preimage, hU]; exact hyV, subset_coborder ⟨y, rfl⟩⟩
  obtain ⟨h, hhO, hyh⟩ := (isAffineOpen_chart R N i).exists_basicOpen_le (V := O) ⟨φ y, hyO⟩ hyi
  have hD : IsAffineOpen ((PSpace R N).basicOpen h) := (isAffineOpen_chart R N i).basicOpen h
  have hDc : (PSpace R N).basicOpen h ≤ chart R N i := (PSpace R N).basicOpen_le h
  have hle : (PSpace R N).basicOpen h ≤ φ.coborderRange := fun z hz => (hhO hz).2
  haveI : IsAffine ((PSpace R N).basicOpen h) := hD
  have hp : IsPullback (φ ∣_ (PSpace R N).basicOpen h) (φ ⁻¹ᵁ (PSpace R N).basicOpen h).ι
      ((PSpace R N).homOfLE hle) φ.liftCoborder := by
    refine IsPullback.of_bot (h₃₁ := φ) (v₂₁ := 𝟙 _) (v₂₂ := φ.coborderRange.ι) ?_ ?_ ?_
    · rw [Category.comp_id, Scheme.homOfLE_ι]
      exact isPullback_morphismRestrict φ _
    · rw [← cancel_mono φ.coborderRange.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
        Scheme.Hom.liftCoborder_ι, morphismRestrict_ι]
    · exact IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, Scheme.Hom.liftCoborder_ι]⟩
  haveI : IsClosedImmersion (φ ∣_ (PSpace R N).basicOpen h) := MorphismProperty.of_isPullback hp.flip inferInstance
  obtain ⟨hWa, hsurj0⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (φ ∣_ (PSpace R N).basicOpen h)
  have hsurj : Function.Surjective
      (φ.appLE ((PSpace R N).basicOpen h) (φ ⁻¹ᵁ (PSpace R N).basicOpen h) le_rfl).hom := by
    rw [Scheme.Hom.appTop, morphismRestrict_app'] at hsurj0
    exact surjective_appLE_of_eq (by simp) (by simp) _ _ hsurj0
  have hWc : φ ⁻¹ᵁ (PSpace R N).basicOpen h ≤ φ ⁻¹ᵁ chart R N i := φ.preimage_mono hDc
  refine ⟨φ ⁻¹ᵁ (PSpace R N).basicOpen h, hWc, hyh, ?_, hWa, ?_⟩
  · intro z hz
    have : φ z ∈ U' := (hhO hz).1
    rw [← Set.mem_preimage, hU] at this
    exact this
  · intro g
    obtain ⟨a, rfl⟩ := hsurj g
    have hloc := (isAffineOpen_chart R N i).isLocalization_basicOpen h
    have key : ∀ p : MvPolynomial (Fin (N + 1)) R,
        (φ.appLE ((PSpace R N).basicOpen h) (φ ⁻¹ᵁ (PSpace R N).basicOpen h) le_rfl).hom
          (algebraMap Γ(PSpace R N, chart R N i) Γ(PSpace R N, (PSpace R N).basicOpen h)
            (MvPolynomial.aeval (R := R) (ratio R N i) p)) =
        MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) _).hom
          (pullRatio φ _ i hWc) p := by
      intro p
      have e1 := appLE_resG φ hDc (le_rfl : φ ⁻¹ᵁ (PSpace R N).basicOpen h ≤ _) (MvPolynomial.aeval (R := R) (ratio R N i) p)
      have e2 := congrArg (fun t => t p) (appLE_comp_aeval_ratio (φ := φ) (W := φ ⁻¹ᵁ (PSpace R N).basicOpen h) (i := i) (hi := hWc))
      exact e1.trans e2
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) a
    obtain ⟨m, hm⟩ := s.2
    obtain ⟨P, rfl⟩ := aeval_ratio_surjective R N i b
    obtain ⟨h₀, hh₀⟩ := aeval_ratio_surjective R N i h
    have hQ : MvPolynomial.aeval (R := R) (ratio R N i) (h₀ ^ m) = (s : Γ(PSpace R N, chart R N i)) := by
      rw [map_pow, hh₀, ← hm]
    refine ⟨P, h₀ ^ m, ?_, ?_⟩
    · rw [← key, hQ]
      exact (IsLocalization.map_units _ s).map _
    · rw [← key, ← key, hQ, ← map_mul]
      exact congrArg _ hs

end GlobalTheory.ProjSpace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFractionsProjSpaceImmersionStatement
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_fractions_projSpace_immersion : ∀ (R : Type) [CommRing R] (N : ℕ) (Y : Scheme.{0}) (φ : Y ⟶ PSpace R N), IsImmersion φ → ∀ (y : Y) (V : Y.Opens) (i : Fin (N + 1)), y ∈ V → φ y ∈ GlobalTheory.ProjSpace.chart R N i → ∃ (W : Y.Opens) (hW : W ≤ φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N i), y ∈ W ∧ W ≤ V ∧ IsAffineOpen W ∧ ∀ g : Γ(Y, W), ∃ P Q : MvPolynomial (Fin (N + 1)) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) Q = MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) P := by
  first | exact @GlobalTheory.ProjSpace.exists_affineOpen_fraction_pullRatio | exact GlobalTheory.ProjSpace.exists_affineOpen_fraction_pullRatio | (intros; apply GlobalTheory.ProjSpace.exists_affineOpen_fraction_pullRatio <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteThetaSectionsThickeningCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ClosedGen

theorem cst_eq_baseRingHom {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) :
    (GlobalTheory.QCoh.Qcqs.baseRingHom f W).hom = GlobalTheory.AbLaw.cst f W := by
  rfl

end GlobalTheory.Mum.ClosedGen


open GlobalTheory.Mum.ClosedGen in
theorem GlobalTheory.Mum.exists_ratio_gen_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∃ (n : ℕ) (τ : Fin n → H0 U.LG.L k), ∀ w : (thickObj R (maximalIdeal R) 0 G).left, ∃ (j : Fin n) (i : Fin 1 → U.LG.L.ι) (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (r : Fin n → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P := by
  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨Y⟩ : Nonempty (Ext D.toPre) := inferInstance
  obtain ⟨S, k₁, hk₁⟩ := GlobalTheory.T.exists_theta_immersion_torus_extension_projective R hB D Y
  choose k₀f hk₀f using (GlobalTheory.T.exists_integralThetaFamily_prescribed_leadingTerm R hB D).1
  refine ⟨max 3 (max k₁ (S.sup k₀f)), le_max_left _ _, ?_⟩
  intro k hk
  have hk3 : 3 ≤ k := le_trans (le_max_left _ _) hk
  have hkk₁ : k₁ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkS : S.sup k₀f ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨N, α, b, τ, hτ, hαb, himm⟩ := hk₁ k hkk₁
  have hF : ∀ j, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead (α j) (b j) := fun j =>
    hk₀f (α j) k (le_trans (Finset.le_sup (hαb j).1) hkS) (b j)
  choose F hF using hF
  have hs : ∀ j, ∃ σ : H0 U.LG.L k, ∀ e, U.ExpandsAt e k σ (F j).f := fun j =>
    IntFam.exists_expandsAt R hB D A G U hG k (by omega) (F j)
  choose s hs using hs
  let T : Over (Sp R) := Over.mk ((thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0)
  obtain ⟨ξ, hξ⟩ := GlobalTheory.TorusCoord.exists_isPointOf (U.gt 0) (T := T) (𝟙 (thickObj R (maximalIdeal R) 0 G).left)
    (Category.id_comp _)
  let ψ : T ⟶ Y.H := (Y.Φ T).symm ξ
  have hψ : GlobalTheory.TorusCoord.IsPointOf (U.gt 0) (𝟙 (thickObj R (maximalIdeal R) 0 G).left) (Y.Φ T ψ) := by
    simp only [ψ, Equiv.apply_symm_apply]; exact hξ
  haveI hψi : IsImmersion ψ.left := GlobalTheory.T.closedFibre_torusCoordinates_isImmersion R D A G U.toUnifPre Y ψ hψ
  set p₀ := (fstG (maximalIdeal R) 0 G).left with hp₀
  let φ := ψ.left ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ
  haveI : IsImmersion φ := IsImmersion.comp _ _
  have hpre : ∀ j, φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N j = ψ.left ⁻¹ᵁ nonzeroLocus (τ j) := fun j => by
    simp only [φ, Scheme.Hom.comp_preimage, GlobalTheory.ProjSpace.toProj_preimage_chart]
  have hstr : φ ≫ PSpace.str R N = p₀ ≫ G.hom := by
    simp only [φ, Category.assoc, GlobalTheory.ProjSpace.toProj_str]
    rw [Over.w ψ]
    exact (pullback.condition).symm
  refine ⟨N + 1, s, fun w => ?_⟩
  have hw : ψ.left w ∈ ⨆ i, nonzeroLocus (τ i) := by rw [hτ]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hw
  obtain ⟨J, hJ⟩ := GlobalTheory.TorusCoord.exists_good' U.LG.isLB w
  let i : Fin 1 → U.LG.L.ι := fun _ => J (p₀ ≫ 𝟙 G.left)
  have hi : p₀ w ∈ secChart U.LG.L i := hJ.mem (fun _ : Fin 1 => 𝟙 G.left) p₀
  have hφw : φ w ∈ GlobalTheory.ProjSpace.chart R N j := by
    show w ∈ φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N j
    rw [hpre]; exact hj
  obtain ⟨W, hW, hwW, hWV, hWa, hgen⟩ := GlobalTheory.T.exists_affineOpen_fractions_projSpace_immersion R N _ φ inferInstance w (p₀ ⁻¹ᵁ secChart U.LG.L i) j hi hφw
  have hWψ : W ≤ ψ.left ⁻¹ᵁ nonzeroLocus (τ j) := hW.trans (hpre j).le
  have hr : ∀ l, GlobalTheory.ProjSpace.pullRatio φ W j hW l =
      (ψ.left.appLE (nonzeroLocus (τ j)) W hWψ).hom (GlobalTheory.ProjSpace.secRatio (τ j) (τ l)) := by
    intro l
    rw [← GlobalTheory.ProjSpace.pullRatio_toProj Y.H.hom τ hτ j l, GlobalTheory.ProjSpace.appLE_pullRatio]
  refine ⟨j, i, W, GlobalTheory.ProjSpace.pullRatio φ W j hW, hwW, hWa, hWV, fun y hy => ?_, fun g => ?_⟩
  · have hyψ : ψ.left y ∈ nonzeroLocus (τ j) := hWψ hy
    obtain ⟨hu, hl⟩ := GlobalTheory.T.closedFibre_thetaSectionGerm_eq_fourierRatio_mul R D A G U.toUnifPre Y ψ hψ k (N + 1) α b τ F s (fun j => (hαb j).2) hF
      (fun j => hs j 0) y j i hyψ (hWV hy)
    refine ⟨hu, fun l => ?_⟩
    rw [hl l, hr l, gs_appLE _ _ _ _ (𝟙 _) y hy, Category.id_comp]
  · obtain ⟨P, Q, hQ, hPQ⟩ := hgen g
    have hc : (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom = GlobalTheory.AbLaw.cst (p₀ ≫ G.hom) W := by
      rw [hstr]; exact cst_eq_baseRingHom _ _
    rw [hc] at hQ hPQ
    exact ⟨P, Q, hQ, hPQ⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteThetaSectionsThickeningCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_theta_sections_thickening_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∃ (n : ℕ) (τ : Fin n → H0 U.LG.L k), ∀ w : (thickObj R (maximalIdeal R) 0 G).left, ∃ (j : Fin n) (i : Fin 1 → U.LG.L.ι) (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (r : Fin n → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P := by
  first | exact @GlobalTheory.Mum.exists_ratio_gen_closed | exact GlobalTheory.Mum.exists_ratio_gen_closed | (intros; apply GlobalTheory.Mum.exists_ratio_gen_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatioGenerationModMaxIdealOfClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatioGenerationModMaxIdealOfClosedFibre
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ClosedFibre

variable (R : Type) [CommRing R] (I : Ideal R)

abbrev baseIncl (e : ℕ) : Spec (CommRingCat.of (R ⧸ I ^ (0 + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : 0 + 1 ≤ e + 1))))

theorem baseIncl_comp (e : ℕ) : baseIncl R I e ≫ thick R I e = thick R I 0 := by
  simp only [baseIncl, thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]

def incl (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    (thickObj R I 0 G).left ⟶ (thickObj R I e G).left :=
  pullback.map G.hom (thick R I 0) G.hom (thick R I e) (𝟙 _) (baseIncl R I e) (𝟙 _)
    (by simp) (by simp [baseIncl_comp])

theorem incl_fst (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    incl R I e G ≫ (fstG I e G).left = (fstG I 0 G).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem incl_snd (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    incl R I e G ≫ pullback.snd G.hom (thick R I e) = pullback.snd G.hom (thick R I 0) ≫ baseIncl R I e :=
  pullback.lift_snd _ _ _

theorem isPullback_incl (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    IsPullback (incl R I e G) (pullback.snd G.hom (thick R I 0)) (pullback.snd G.hom (thick R I e))
      (baseIncl R I e) := by
  refine IsPullback.of_right ?_ (incl_snd R I e G) (IsPullback.of_hasPullback G.hom (thick R I e))
  have h1 : incl R I e G ≫ pullback.fst G.hom (thick R I e) = pullback.fst G.hom (thick R I 0) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  rw [h1, baseIncl_comp]
  exact IsPullback.of_hasPullback G.hom (thick R I 0)

end GlobalTheory.ClosedFibre

namespace GlobalTheory.ClosedFibre

variable (R : Type) [CommRing R] (I : Ideal R)

theorem cst_fst (e : ℕ) (G : Over (Spec (CommRingCat.of R))) (V : (thickObj R I e G).left.Opens) (a : R) :
    GlobalTheory.AbLaw.cst ((fstG I e G).left ≫ G.hom) V a =
      GlobalTheory.AbLaw.cst (pullback.snd G.hom (thick R I e)) V (Ideal.Quotient.mk (I ^ (e + 1)) a) := by
  have hc : (fstG I e G).left ≫ G.hom = pullback.snd G.hom (thick R I e) ≫ thick R I e := pullback.condition
  rw [hc]
  have h := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))).hom a)
  simp only [GlobalTheory.AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom] at h ⊢
  erw [← h]
  rfl

theorem cst_eq_zero (e : ℕ) (G : Over (Spec (CommRingCat.of R)))
    (V : (thickObj R I e G).left.Opens) (a : R) (ha : a ∈ I ^ (e + 1)) :
    GlobalTheory.AbLaw.cst ((fstG I e G).left ≫ G.hom) V a = 0 := by
  rw [cst_fst, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

theorem app_cst (e : ℕ) (G : Over (Spec (CommRingCat.of R)))
    (V : (thickObj R I e G).left.Opens) (a : R) :
    (Scheme.Hom.app (incl R I e G) V).hom (GlobalTheory.AbLaw.cst ((fstG I e G).left ≫ G.hom) V a) =
      GlobalTheory.AbLaw.cst ((fstG I 0 G).left ≫ G.hom) (incl R I e G ⁻¹ᵁ V) a := by
  have hq : incl R I e G ≫ ((fstG I e G).left ≫ G.hom) = (fstG I 0 G).left ≫ G.hom := by
    rw [← Category.assoc, incl_fst]
  rw [← hq]
  simp only [GlobalTheory.AbLaw.cst, GlobalTheory.AbLaw.rs, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  have := congr($((incl R I e G).naturality (homOfLE (le_top : V ≤ ⊤)).op).hom
    (((fstG I e G).left ≫ G.hom).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.trans rfl

theorem surjective_baseIncl (e : ℕ) : Surjective (baseIncl R I e) := by
  refine ⟨fun x => ?_⟩
  have h : I ^ (e + 1) ≤ I ^ (0 + 1) := Ideal.pow_le_pow_right (by omega)
  have hx : (x : PrimeSpectrum (R ⧸ I ^ (e + 1))) ∈
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor h)) := by
    rw [range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective h)]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha' : a ∈ I ^ (0 + 1) := by
      simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using ha
    rw [zero_add, pow_one] at ha'
    refine x.2.mem_of_pow_mem (e + 1) ?_
    have : Ideal.Quotient.mk (I ^ (e + 1)) a ^ (e + 1) = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow ha' _
    rw [this]
    exact Ideal.zero_mem _
  exact hx

theorem incl_surjective (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    Function.Surjective ⇑(incl R I e G) :=
  (MorphismProperty.of_isPullback (P := @Surjective) (isPullback_incl R I e G).flip
    (surjective_baseIncl R I e)).surj

theorem app_incl (e : ℕ) (G : Over (Spec (CommRingCat.of R))) (V : (thickObj R I e G).left.Opens)
    (hV : IsAffineOpen V) :
    IsAffineOpen (incl R I e G ⁻¹ᵁ V) ∧ Function.Surjective (Scheme.Hom.app (incl R I e G) V).hom ∧
      RingHom.ker (Scheme.Hom.app (incl R I e G) V).hom ≤
        Ideal.map (GlobalTheory.AbLaw.cst ((fstG I e G).left ≫ G.hom) V) I := by
  have H := isPullback_incl R I e G
  have po := (GlobalTheory.AbLaw.isPushout_cst H hV (V' := incl R I e G ⁻¹ᵁ V) rfl).flip
  have hsurj : Function.Surjective (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (by omega : 0 + 1 ≤ e + 1) : I ^ (e + 1) ≤ I ^ (0 + 1)))).hom :=
    Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (by omega : 0 + 1 ≤ e + 1))
  obtain ⟨h1, h2⟩ := GlobalTheory.TorsionChart.pushout_inl_surjective_and_ker po hsurj
  rw [← Scheme.Hom.app_eq_appLE] at h1 h2
  refine ⟨GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback H hV, h1, ?_⟩
  rw [h2, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, Ideal.Quotient.factor_ker, Ideal.map_map]
  have hc : (GlobalTheory.AbLaw.cst (pullback.snd G.hom (thick R I e)) V).comp (Ideal.Quotient.mk (I ^ (e + 1))) =
      GlobalTheory.AbLaw.cst ((fstG I e G).left ≫ G.hom) V :=
    RingHom.ext fun a => (cst_fst R I e G V a).symm
  rw [hc, zero_add, pow_one]

end GlobalTheory.ClosedFibre

namespace GlobalTheory.ClosedFibre


open MvPolynomial in
theorem gen_basicOpen {X : Scheme.{0}} {R : Type} [CommRing R] (p : X ⟶ Spec (CommRingCat.of R)) {N₀ : X.Opens}
    (hN₀ : IsAffineOpen N₀) {m : ℕ} (r : Fin m → Γ(X, N₀))
    (hgen : ∀ g : Γ(X, N₀), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (eval₂ (GlobalTheory.AbLaw.cst p N₀) r Q) ∧
      g * eval₂ (GlobalTheory.AbLaw.cst p N₀) r Q = eval₂ (GlobalTheory.AbLaw.cst p N₀) r P)
    (h : Γ(X, N₀)) (D : X.Opens) (hle : D ≤ N₀) (hD : D = X.basicOpen h) (g : Γ(X, D)) :
    ∃ P Q : MvPolynomial (Fin m) R,
      IsUnit (eval₂ (GlobalTheory.AbLaw.cst p D) (fun l => GlobalTheory.AbLaw.rs X hle (r l)) Q) ∧
      g * eval₂ (GlobalTheory.AbLaw.cst p D) (fun l => GlobalTheory.AbLaw.rs X hle (r l)) Q =
        eval₂ (GlobalTheory.AbLaw.cst p D) (fun l => GlobalTheory.AbLaw.rs X hle (r l)) P := by
  subst hD
  have hev : ∀ P : MvPolynomial (Fin m) R, eval₂ (GlobalTheory.AbLaw.cst p (X.basicOpen h))
      (fun l => GlobalTheory.AbLaw.rs X hle (r l)) P = GlobalTheory.AbLaw.rs X hle (eval₂ (GlobalTheory.AbLaw.cst p N₀) r P) := by
    intro P
    rw [MvPolynomial.hom_eval₂]
    congr 1
    exact RingHom.ext fun a => (GlobalTheory.AbLaw.rs_cst p hle a).symm
  have hl := hN₀.isLocalization_basicOpen h
  obtain ⟨⟨a, ⟨s, hs⟩⟩, has⟩ := IsLocalization.surj (Submonoid.powers h) g
  have hsu : IsUnit (GlobalTheory.AbLaw.rs X hle s) := IsLocalization.map_units (M := Submonoid.powers h)
    Γ(X, X.basicOpen h) ⟨s, hs⟩
  obtain ⟨Pa, Qa, hQa, ha⟩ := hgen a
  obtain ⟨Ps, Qs, hQs, hsq⟩ := hgen s
  refine ⟨Pa * Qs, Ps * Qa, ?_, ?_⟩
  · rw [MvPolynomial.eval₂_mul, hev, hev, ← hsq, map_mul]
    exact (hsu.mul (hQs.map _)).mul (hQa.map _)
  · simp only [MvPolynomial.eval₂_mul, hev]
    rw [← hsq, ← ha]
    simp only [map_mul]
    have has' : g * GlobalTheory.AbLaw.rs X hle s = GlobalTheory.AbLaw.rs X hle a := has
    rw [← has']
    ring

end GlobalTheory.ClosedFibre

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.ratio_gen_mod_of_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) (L : LB G.left) (k : ℕ) (s₀ : H0 L k) (i : Fin 1 → L.ι), (∀ w : (thickObj R (maximalIdeal R) 0 G).left, (fstG (maximalIdeal R) 0 G).left w ∈ secChart L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (m : ℕ) (σ : Fin m → H0 L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P) → ∀ (e : ℕ) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) e G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q - MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r P ∈ Ideal.map (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) := by
  intro R _ _ _ G L k s₀ i hyp e w hw hunit
  have hjp : GlobalTheory.ClosedFibre.incl R (maximalIdeal R) e G ≫ (fstG (maximalIdeal R) e G).left =
      (fstG (maximalIdeal R) 0 G).left := GlobalTheory.ClosedFibre.incl_fst R _ e G
  obtain ⟨w₀, rfl⟩ := GlobalTheory.ClosedFibre.incl_surjective R (maximalIdeal R) e G w
  set jm := GlobalTheory.ClosedFibre.incl R (maximalIdeal R) e G with hjdef
  set pe : (thickObj R (maximalIdeal R) e G).left ⟶ G.left := (fstG (maximalIdeal R) e G).left with hpe
  set p₀ : (thickObj R (maximalIdeal R) 0 G).left ⟶ G.left := (fstG (maximalIdeal R) 0 G).left with hp₀

  have hgc : ∀ (y : (thickObj R (maximalIdeal R) 0 G).left) (s : H0 L k), pe (jm y) ∈ secChart L i →
      secGerm p₀ y s i = (jm.stalkMap y).hom (secGerm pe (jm y) s i) := by
    intro y s hy
    rw [← hjp]
    exact secGerm_comp jm pe y s hy
  have hw₀ : p₀ w₀ ∈ secChart L i := by
    rw [← hjp, Scheme.Hom.comp_apply]; exact hw
  have hu₀ : IsUnit (secGerm p₀ w₀ s₀ i) := by rw [hgc w₀ s₀ hw]; exact hunit.map _
  obtain ⟨N₀, m, σ, r₀, hwN₀, hN₀, hN₀le, hgerm₀, hgen₀⟩ := hyp w₀ hw₀ hu₀

  obtain ⟨a, ha⟩ : ∃ a, a = (pe.app (secChart L i)).hom (s₀.f i) := ⟨_, rfl⟩
  have hmemU₁ : ∀ y : (thickObj R (maximalIdeal R) e G).left, (hy : pe y ∈ secChart L i) →
      (y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen a ↔ IsUnit (secGerm pe y s₀ i)) := by
    intro y hy
    rw [Scheme.mem_basicOpen _ a y hy, ha]
    exact (iff_of_eq (congrArg IsUnit (gs_eq pe y _ hy (s₀.f i)))).symm
  have hwU₁ := (hmemU₁ _ hw).2 hunit
  obtain ⟨V, hV, hwV, hVle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 (thickObj R (maximalIdeal R) e G).left.isBasis_affineOpens hwU₁
  have hV' : IsAffineOpen V := hV
  obtain ⟨hVaff, hVsurj, -⟩ := GlobalTheory.ClosedFibre.app_incl R (maximalIdeal R) e G V hV'
  obtain ⟨f₀, g₀, hfg, hw₀f⟩ := exists_basicOpen_le_affine_inter hN₀ hVaff w₀ ⟨hwN₀, hwV⟩
  obtain ⟨F, hF⟩ := hVsurj g₀
  have hNaff : IsAffineOpen ((thickObj R (maximalIdeal R) e G).left.basicOpen F) := hV'.basicOpen F
  have hjN : jm ⁻¹ᵁ (thickObj R (maximalIdeal R) e G).left.basicOpen F =
      (thickObj R (maximalIdeal R) 0 G).left.basicOpen f₀ := by
    rw [Scheme.preimage_basicOpen, hF, hfg]
  have hwN : jm w₀ ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen F := by
    show w₀ ∈ jm ⁻¹ᵁ (thickObj R (maximalIdeal R) e G).left.basicOpen F
    rw [hjN]; exact hw₀f
  have hNU₁ : (thickObj R (maximalIdeal R) e G).left.basicOpen F ≤
      (thickObj R (maximalIdeal R) e G).left.basicOpen a :=
    ((thickObj R (maximalIdeal R) e G).left.basicOpen_le F).trans hVle
  have hU₁c : (thickObj R (maximalIdeal R) e G).left.basicOpen a ≤ pe ⁻¹ᵁ secChart L i :=
    (thickObj R (maximalIdeal R) e G).left.basicOpen_le a
  have hDN₀ : jm ⁻¹ᵁ (thickObj R (maximalIdeal R) e G).left.basicOpen F ≤ N₀ := by
    rw [hjN]; exact (thickObj R (maximalIdeal R) 0 G).left.basicOpen_le f₀

  have hu₁ : IsUnit (GlobalTheory.AbLaw.rs _ hU₁c a) :=
    (thickObj R (maximalIdeal R) e G).left.toRingedSpace.isUnit_res_basicOpen a
  let ρ : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, (thickObj R (maximalIdeal R) e G).left.basicOpen a) :=
    fun l => GlobalTheory.AbLaw.rs _ hU₁c ((pe.app (secChart L i)).hom ((σ l).f i)) * ↑(hu₁.unit⁻¹)
  let r : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, (thickObj R (maximalIdeal R) e G).left.basicOpen F) :=
    fun l => GlobalTheory.AbLaw.rs _ hNU₁ (ρ l)
  have hρ : ∀ l, ρ l * GlobalTheory.AbLaw.rs _ hU₁c a = GlobalTheory.AbLaw.rs _ hU₁c ((pe.app (secChart L i)).hom ((σ l).f i)) := by
    intro l
    simp only [ρ]
    rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]
  have hg1 : ∀ y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen a,
      ∀ x : Γ((thickObj R (maximalIdeal R) e G).left, pe ⁻¹ᵁ secChart L i),
      gs (𝟙 (thickObj R (maximalIdeal R) e G).left) y ((thickObj R (maximalIdeal R) e G).left.basicOpen a)
        (GlobalTheory.AbLaw.rs _ hU₁c x) = gs (𝟙 (thickObj R (maximalIdeal R) e G).left) y (pe ⁻¹ᵁ secChart L i) x :=
    fun y hy x => gs_res (𝟙 _) y hU₁c hy x
  have hg2 : ∀ (y : (thickObj R (maximalIdeal R) e G).left) (hy : pe y ∈ secChart L i) (b : Γ(G.left, secChart L i)),
      gs (𝟙 (thickObj R (maximalIdeal R) e G).left) y (pe ⁻¹ᵁ secChart L i) ((pe.app (secChart L i)).hom b) =
        gs pe y (secChart L i) b := by
    intro y hy b
    rw [gs_pull (𝟙 (thickObj R (maximalIdeal R) e G).left) pe y _ hy, Category.id_comp]
  have hsa : ∀ (y : (thickObj R (maximalIdeal R) e G).left) (hy : pe y ∈ secChart L i),
      gs (𝟙 (thickObj R (maximalIdeal R) e G).left) y (pe ⁻¹ᵁ secChart L i) a = secGerm pe y s₀ i := by
    intro y hy
    rw [ha]; exact hg2 y hy _
  have hgermN : ∀ y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen F, IsUnit (secGerm pe y s₀ i) ∧
      ∀ l, secGerm pe y (σ l) i = gs (𝟙 _) y ((thickObj R (maximalIdeal R) e G).left.basicOpen F) (r l) *
        secGerm pe y s₀ i := by
    intro y hy
    have hy₁ := hNU₁ hy
    have hyc := hU₁c hy₁
    refine ⟨(hmemU₁ y hyc).1 hy₁, fun l => ?_⟩
    have e1 := congrArg (gs (𝟙 _) y ((thickObj R (maximalIdeal R) e G).left.basicOpen a)) (hρ l)
    rw [gs_mul _ _ _ hy₁, hg1 y hy₁, hg1 y hy₁, hsa y hyc] at e1
    change gs pe y _ _ = _ * gs pe y _ _
    rw [← hg2 y hyc ((σ l).f i), ← e1]
    simp only [r]
    rw [gs_res (𝟙 _) y hNU₁ hy]
  refine ⟨(thickObj R (maximalIdeal R) e G).left.basicOpen F, m, σ, r, hwN, hNaff, hNU₁.trans hU₁c, hgermN,
    fun g => ?_⟩

  have hjr : ∀ l, (jm.app _).hom (r l) = GlobalTheory.AbLaw.rs _ hDN₀ (r₀ l) := by
    intro l
    apply fn_ext
    intro y hy
    have hyN₀ := hDN₀ hy
    have hyN : jm y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen F := hy
    have hyc : pe (jm y) ∈ secChart L i := hU₁c (hNU₁ hyN)
    rw [gs_pull (𝟙 _) jm y _ hyN, Category.id_comp, gs_res (𝟙 _) y hDN₀ hy]
    refine (hgerm₀ y hyN₀).1.mul_left_injective ?_
    show gs jm y _ (r l) * secGerm p₀ y s₀ i = gs (𝟙 _) y N₀ (r₀ l) * secGerm p₀ y s₀ i
    rw [← (hgerm₀ y hyN₀).2 l, hgc y (σ l) hyc, hgc y s₀ hyc, (hgermN (jm y) hyN).2 l, map_mul,
      gs_stalkMap jm y _ hyN]
  have hjc : (jm.app _).hom.comp (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F)) =
      GlobalTheory.AbLaw.cst (p₀ ≫ G.hom) (jm ⁻¹ᵁ (thickObj R (maximalIdeal R) e G).left.basicOpen F) :=
    RingHom.ext fun x => GlobalTheory.ClosedFibre.app_cst R (maximalIdeal R) e G _ x
  have hjev : ∀ P : MvPolynomial (Fin m) R,
      (jm.app _).hom (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F)) r P) =
      MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (p₀ ≫ G.hom) (jm ⁻¹ᵁ (thickObj R (maximalIdeal R) e G).left.basicOpen F))
        (fun l => GlobalTheory.AbLaw.rs _ hDN₀ (r₀ l)) P := by
    intro P
    rw [MvPolynomial.hom_eval₂, hjc]
    simp only [hjr]
  obtain ⟨P, Q, hQ, hPQ⟩ := GlobalTheory.ClosedFibre.gen_basicOpen (p₀ ≫ G.hom) hN₀ r₀ hgen₀ f₀ _ hDN₀ hjN ((jm.app _).hom g)
  obtain ⟨-, hNsurj, hNker⟩ := GlobalTheory.ClosedFibre.app_incl R (maximalIdeal R) e G _ hNaff
  have hnil : ∀ x ∈ Ideal.map (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F))
      (maximalIdeal R), IsNilpotent x := by
    intro x hx
    refine ⟨e + 1, ?_⟩
    have h1 : x ^ (e + 1) ∈ Ideal.map (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F))
        (maximalIdeal R ^ (e + 1)) := by
      rw [Ideal.map_pow]; exact Ideal.pow_mem_pow hx _
    have h0 : Ideal.map (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F))
        (maximalIdeal R ^ (e + 1)) = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker]
      intro x hx
      exact RingHom.mem_ker.2 (GlobalTheory.ClosedFibre.cst_eq_zero R (maximalIdeal R) e G _ x hx)
    rw [h0] at h1
    exact h1
  refine ⟨P, Q, ?_, ?_⟩
  · have hQ' : IsUnit ((jm.app _).hom (MvPolynomial.eval₂
        (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F)) r Q)) := by
      rw [hjev]; exact hQ
    obtain ⟨v, hv⟩ := hQ'.exists_right_inv
    obtain ⟨v', rfl⟩ := hNsurj v
    have hk : MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F)) r Q
        * v' - 1 ∈ RingHom.ker (jm.app _).hom := by
      rw [RingHom.mem_ker, RingHom.map_sub, map_mul, map_one, hv, sub_self]
    have hu := (hnil _ (hNker hk)).isUnit_one_add
    rw [add_sub_cancel] at hu
    exact isUnit_of_mul_isUnit_left hu
  · apply hNker
    rw [RingHom.mem_ker, map_sub, map_mul, hjev, hjev, hPQ, sub_self]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatioGenerationModMaxIdealOfClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratioGeneration_mod_maxIdeal_of_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) (L : LB G.left) (k : ℕ) (s₀ : H0 L k) (i : Fin 1 → L.ι), (∀ w : (thickObj R (maximalIdeal R) 0 G).left, (fstG (maximalIdeal R) 0 G).left w ∈ secChart L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (m : ℕ) (σ : Fin m → H0 L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P) → ∀ (e : ℕ) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) e G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q - MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r P ∈ Ideal.map (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) := by
  first | exact @GlobalTheory.Mum.ratio_gen_mod_of_closedFibre | exact GlobalTheory.Mum.ratio_gen_mod_of_closedFibre | (intros; apply GlobalTheory.Mum.ratio_gen_mod_of_closedFibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalGenerationRatiosClosedFibreAnyUnitSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalGenerationRatiosClosedFibreAnyUnitSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.AnySec

open MvPolynomial

theorem exists_homog {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (x : Fin n → S) (j : Fin n) (v : S)
    (hv : x j * v = 1) (F : MvPolynomial (Fin n) R) :
    ∃ (F' : MvPolynomial (Fin n) R) (d : ℕ), eval₂ f (fun l => x l * v) F * x j ^ d = eval₂ f x F' := by
  induction F using MvPolynomial.induction_on with
  | C a => exact ⟨C a, 0, by simp⟩
  | add p q hp hq =>
    obtain ⟨p', dp, ep⟩ := hp
    obtain ⟨q', dq, eq⟩ := hq
    refine ⟨p' * X j ^ dq + q' * X j ^ dp, dp + dq, ?_⟩
    simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X]
    rw [← ep, ← eq]; ring
  | mul_X p l hp =>
    obtain ⟨p', dp, ep⟩ := hp
    refine ⟨p' * X l, dp + 1, ?_⟩
    simp only [eval₂_mul, eval₂_X]
    linear_combination (x l * v * x j) * ep + (x l * eval₂ f x p') * hv

variable {X Y : Scheme.{0}}

theorem isUnit_of_gs {N : X.Opens} (a : Γ(X, N)) (h : ∀ y ∈ N, IsUnit (gs (𝟙 X) y N a)) : IsUnit a :=
  X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    have := h y hy
    rw [gs_eq (𝟙 X) y N hy] at this
    exact this

theorem gs_rs_app (p : X ⟶ Y) {U : Y.Opens} {N : X.Opens} (hle : N ≤ p ⁻¹ᵁ U) {y : X} (hy : y ∈ N) (a : Γ(Y, U)) :
    gs (𝟙 X) y N (GlobalTheory.AbLaw.rs X hle ((p.app U).hom a)) = gs p y U a := by
  rw [gs_res (𝟙 X) y hle hy, gs_pull (𝟙 X) p y U (hle hy) a, Category.id_comp]

theorem rs_comp_cst {R : Type} [CommRing R] (q : X ⟶ Spec (CommRingCat.of R)) {N N₁ : X.Opens} (hle : N ≤ N₁) :
    (GlobalTheory.AbLaw.rs X hle).comp (GlobalTheory.AbLaw.cst q N₁) = GlobalTheory.AbLaw.cst q N := by
  ext c
  simp only [GlobalTheory.AbLaw.cst, GlobalTheory.AbLaw.rs, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.Mum.AnySec

namespace GlobalTheory.Mum.AnySec
open MvPolynomial
variable {X Y : Scheme.{0}}

theorem locGen_anySec_gen {R : Type} [CommRing R] (q : X ⟶ Spec (CommRingCat.of R)) (p : X ⟶ Y) (L : LB Y)
    (k n : ℕ) (τ : Fin n → H0 L k)
    (H : ∀ w : X, ∃ (j : Fin n) (i : Fin 1 → L.ι) (N : X.Opens) (r : Fin n → Γ(X, N)), w ∈ N ∧ IsAffineOpen N ∧
      N ≤ p ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm p y (τ j) i) ∧
        ∀ l, secGerm p y (τ l) i = gs (𝟙 _) y N (r l) * secGerm p y (τ j) i) ∧
      ∀ g : Γ(X, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (eval₂ (GlobalTheory.AbLaw.cst q N) r Q) ∧
        g * eval₂ (GlobalTheory.AbLaw.cst q N) r Q = eval₂ (GlobalTheory.AbLaw.cst q N) r P)
    (s₀ : H0 L k) (i : Fin 1 → L.ι) (w : X) (hw : p w ∈ secChart L i) (hs : IsUnit (secGerm p w s₀ i)) :
    ∃ (N : X.Opens) (r : Fin n → Γ(X, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ p ⁻¹ᵁ secChart L i ∧
      (∀ y ∈ N, IsUnit (secGerm p y s₀ i) ∧ ∀ l, secGerm p y (τ l) i = gs (𝟙 _) y N (r l) * secGerm p y s₀ i) ∧
      ∀ g : Γ(X, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (eval₂ (GlobalTheory.AbLaw.cst q N) r Q) ∧
        g * eval₂ (GlobalTheory.AbLaw.cst q N) r Q = eval₂ (GlobalTheory.AbLaw.cst q N) r P := by
  obtain ⟨j, i', N₁, ρ, hwN, hN₁, hN₁le, hgerm, hgen⟩ := H w
  let V : X.Opens := p ⁻¹ᵁ secChart L i ⊓ X.basicOpen ((p.app (secChart L i)).hom (s₀.f i))
  have hwV : w ∈ V := by
    refine ⟨hw, (Scheme.mem_basicOpen X _ w hw).2 ?_⟩
    have e : secGerm p w s₀ i = _ := gs_eq p w (secChart L i) hw (s₀.f i)
    rw [e] at hs
    exact hs
  obtain ⟨h, hhV, hwh⟩ := hN₁.exists_basicOpen_le ⟨w, hwV⟩ hwN
  have hNN₁ : X.basicOpen h ≤ N₁ := X.basicOpen_le h
  have hNi : X.basicOpen h ≤ p ⁻¹ᵁ secChart L i := hhV.trans inf_le_left
  have hNs : X.basicOpen h ≤ X.basicOpen ((p.app (secChart L i)).hom (s₀.f i)) := hhV.trans inf_le_right
  have hsN : ∀ y ∈ X.basicOpen h, IsUnit (secGerm p y s₀ i) := fun y hy => by
    have := (Scheme.mem_basicOpen _ _ _ (hNi hy)).1 (hNs hy)
    have e : secGerm p y s₀ i = _ := gs_eq p y (secChart L i) (hNi hy) (s₀.f i)
    rw [e]
    exact this
  have hu₀ : IsUnit (GlobalTheory.AbLaw.rs X hNi ((p.app (secChart L i)).hom (s₀.f i))) :=
    isUnit_of_gs _ fun y hy => by rw [gs_rs_app p hNi hy (s₀.f i)]; exact hsN y hy
  obtain ⟨r, hr_def⟩ : ∃ r : Fin n → Γ(X, X.basicOpen h), r = fun l =>
      GlobalTheory.AbLaw.rs X hNi ((p.app (secChart L i)).hom ((τ l).f i)) * (hu₀.unit⁻¹ : (Γ(X, X.basicOpen h))ˣ).val :=
    ⟨_, rfl⟩
  have hr : ∀ y ∈ X.basicOpen h, ∀ l, secGerm p y (τ l) i = gs (𝟙 X) y _ (r l) * secGerm p y s₀ i := by
    intro y hy l
    rw [secGerm, secGerm, ← gs_rs_app p hNi hy ((τ l).f i), ← gs_rs_app p hNi hy (s₀.f i), ← gs_mul _ _ _ hy]
    congr 1
    simp only [hr_def, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]
  refine ⟨X.basicOpen h, r, hwh, hN₁.basicOpen h, hNi, fun y hy => ⟨hsN y hy, hr y hy⟩, fun g => ?_⟩

  have key : ∀ y ∈ X.basicOpen h, ∀ l, gs (𝟙 X) y _ (r l) = gs (𝟙 X) y _ (GlobalTheory.AbLaw.rs X hNN₁ (ρ l) * r j) ∧
      IsUnit (gs (𝟙 X) y _ (r j)) := by
    intro y hy l
    have hy₁ := hNN₁ hy
    obtain ⟨c, hc⟩ := exists_unit_secGerm k p y (hNi hy) (hN₁le hy₁)
    have gρ : gs (𝟙 X) y _ (GlobalTheory.AbLaw.rs X hNN₁ (ρ l)) = gs (𝟙 X) y N₁ (ρ l) := gs_res _ _ hNN₁ hy _
    have e1 := hr y hy l
    have e2 := hr y hy j
    have e3 := (hgerm y hy₁).2 l
    have hcl := hc (τ l)
    have hcj := hc (τ j)
    refine ⟨?_, ?_⟩
    · rw [gs_mul _ _ _ hy, gρ]
      apply (hsN y hy).mul_right_cancel
      linear_combination (-1 : _) * e1 + gs (𝟙 X) y N₁ (ρ l) * e2 + hcl - gs (𝟙 X) y N₁ (ρ l) * hcj + c.val * e3
    · have : IsUnit (gs (𝟙 X) y _ (r j) * secGerm p y s₀ i) := by
        rw [← e2, hcj]; exact c.isUnit.mul (hgerm y hy₁).1
      exact isUnit_of_mul_isUnit_left this
  have hrel : ∀ l, r l = GlobalTheory.AbLaw.rs X hNN₁ (ρ l) * r j := fun l => fn_ext fun y hy => (key y hy l).1
  have huj : IsUnit (r j) := isUnit_of_gs _ fun y hy => (key y hy j).2
  let v : Γ(X, X.basicOpen h) := (huj.unit⁻¹ : (Γ(X, X.basicOpen h))ˣ).val
  have hv : r j * v = 1 := IsUnit.mul_val_inv huj
  have hρ : (fun l => GlobalTheory.AbLaw.rs X hNN₁ (ρ l)) = fun l => r l * v := by
    funext l; rw [hrel l, _root_.mul_assoc, hv, _root_.mul_one]

  have hev : ∀ F : MvPolynomial (Fin n) R, GlobalTheory.AbLaw.rs X hNN₁ (eval₂ (GlobalTheory.AbLaw.cst q N₁) ρ F) =
      eval₂ (GlobalTheory.AbLaw.cst q (X.basicOpen h)) (fun l => r l * v) F := fun F => by
    rw [eval₂_comp_left, rs_comp_cst, ← hρ]; rfl
  haveI := hN₁.isLocalization_basicOpen h
  obtain ⟨⟨a, ⟨_, t, rfl⟩⟩, hga⟩ := IsLocalization.surj (Submonoid.powers h) g
  have hhu : IsUnit (GlobalTheory.AbLaw.rs X hNN₁ h) := IsLocalization.Away.algebraMap_isUnit h
  obtain ⟨Pa, Qa, hQa, ea⟩ := hgen a
  obtain ⟨Ph, Qh, hQh, eh⟩ := hgen h
  have ea' := congrArg (GlobalTheory.AbLaw.rs X hNN₁) ea
  have eh' := congrArg (GlobalTheory.AbLaw.rs X hNN₁) eh
  rw [map_mul, hev, hev] at ea' eh'
  have hQh' := hQh.map (GlobalTheory.AbLaw.rs X hNN₁)
  rw [hev] at hQh'
  have hga' : g * GlobalTheory.AbLaw.rs X hNN₁ h ^ t = GlobalTheory.AbLaw.rs X hNN₁ a := by
    rw [← map_pow]; exact hga
  obtain ⟨A', d3, eA⟩ := exists_homog (GlobalTheory.AbLaw.cst q (X.basicOpen h)) r j v hv Pa
  obtain ⟨B', d2, eB⟩ := exists_homog (GlobalTheory.AbLaw.cst q (X.basicOpen h)) r j v hv Qa
  obtain ⟨C', d1, eC⟩ := exists_homog (GlobalTheory.AbLaw.cst q (X.basicOpen h)) r j v hv Ph
  obtain ⟨D', d4, eD⟩ := exists_homog (GlobalTheory.AbLaw.cst q (X.basicOpen h)) r j v hv Qh
  refine ⟨A' * D' ^ t * MvPolynomial.X j ^ (d1 * t + d2), C' ^ t * B' * MvPolynomial.X j ^ (d3 + d4 * t), ?_, ?_⟩
  · simp only [eval₂_mul, eval₂_pow, eval₂_X]
    rw [← eB, ← eC, ← eh']
    have hQa' := hQa.map (GlobalTheory.AbLaw.rs X hNN₁)
    rw [hev] at hQa'
    exact ((((hhu.mul hQh').mul (huj.pow _)).pow _).mul (hQa'.mul (huj.pow _))).mul (huj.pow _)
  · simp only [eval₂_mul, eval₂_pow, eval₂_X]
    rw [← eA, ← eB, ← eC, ← eD, ← eh', ← ea']
    linear_combination (eval₂ (GlobalTheory.AbLaw.cst q (X.basicOpen h)) (fun l => r l * v) Qa *
      eval₂ (GlobalTheory.AbLaw.cst q (X.basicOpen h)) (fun l => r l * v) Qh ^ t * r j ^ (d1 * t + d2 + d3 + d4 * t)) * hga'

end GlobalTheory.Mum.AnySec

theorem GlobalTheory.Mum.locGen_ratio_anySec : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) (L : LB G.left) (k n : ℕ) (τ : Fin n → H0 L k), (∀ w : (thickObj R (maximalIdeal R) 0 G).left, ∃ (j : Fin n) (i : Fin 1 → L.ι) (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (r : Fin n → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P) → ∀ (s₀ : H0 L k) (i : Fin 1 → L.ι) (w : (thickObj R (maximalIdeal R) 0 G).left), (fstG (maximalIdeal R) 0 G).left w ∈ secChart L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (m : ℕ) (σ : Fin m → H0 L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P := by
  intro R _ _ _ G L k n τ H s₀ i w hw hs
  obtain ⟨N, r, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.Mum.AnySec.locGen_anySec_gen ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) _ L k n τ H s₀ i w hw hs
  exact ⟨N, n, τ, r, h1, h2, h3, h4, h5⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalGenerationRatiosClosedFibreAnyUnitSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localGeneration_ratios_closedFibre_any_unit_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) (L : LB G.left) (k n : ℕ) (τ : Fin n → H0 L k), (∀ w : (thickObj R (maximalIdeal R) 0 G).left, ∃ (j : Fin n) (i : Fin 1 → L.ι) (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (r : Fin n → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P) → ∀ (s₀ : H0 L k) (i : Fin 1 → L.ι) (w : (thickObj R (maximalIdeal R) 0 G).left), (fstG (maximalIdeal R) 0 G).left w ∈ secChart L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (m : ℕ) (σ : Fin m → H0 L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P := by
  first | exact @GlobalTheory.Mum.locGen_ratio_anySec | exact GlobalTheory.Mum.locGen_ratio_anySec | (intros; apply GlobalTheory.Mum.locGen_ratio_anySec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionRatiosGenerateModMaximal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_ratio_gen_mod : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (s₀ : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart U.LG.L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 U.LG.L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) e G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q - MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r P ∈ Ideal.map (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) := by
  intro R _ _ _ hBase D A G _ _ hG U
  obtain ⟨k₀, hk₀, hA⟩ := GlobalTheory.T.exists_finite_theta_sections_thickening_cover R hBase D A G hG U
  refine ⟨k₀, hk₀, fun e k hk s₀ i w hw hu => ?_⟩
  obtain ⟨n, τ, hτ⟩ := hA k hk
  exact GlobalTheory.T.ratioGeneration_mod_maxIdeal_of_closedFibre R G U.LG.L k s₀ i (GlobalTheory.T.localGeneration_ratios_closedFibre_any_unit_section R G U.LG.L k n τ hτ s₀ i) e w hw hu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionRatiosGenerateModMaximalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_ratios_generate_mod_maximal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (s₀ : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart U.LG.L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 U.LG.L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) e G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q - MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r P ∈ Ideal.map (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) := by
  first | exact @GlobalTheory.Mum.exists_ratio_gen_mod | exact GlobalTheory.Mum.exists_ratio_gen_mod | (intros; apply GlobalTheory.Mum.exists_ratio_gen_mod <;> assumption)
end
