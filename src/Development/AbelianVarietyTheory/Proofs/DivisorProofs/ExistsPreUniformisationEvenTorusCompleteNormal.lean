module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffine
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointOverGeometricBasePoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreUniformisationEvenTorusCompleteNormal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreUniformisationEvenTorusCompleteNormal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.PreUnifEven

open GlobalTheory.UU GlobalTheory.LN


set_option maxHeartbeats 1000000 in
theorem nonempty_towerR_of_even {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (P : CP G) (hs : IsSemiAbelian G)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (Q₀ : TQ (thickObj R (maximalIdeal R) 0 G) X) (P₀ : CP (thickObj R (maximalIdeal R) 0 G))
    (lev₀ : IsLevelCP (maximalIdeal R) 0 P₀ P) (even₀ : ∃ σ : CubTriv P₀.c Q₀.i, σ.Even) :
    Nonempty (TowerR (maximalIdeal R) P X) := by
  have := hs.smooth
  have := hs.geomConnected
  have hsm : ∀ e, Smooth (thickObj R (maximalIdeal R) e G).hom := fun e => by
    show Smooth (pullback.snd _ _); infer_instance
  have hc : ∀ e, GeometricallyConnected (thickObj R (maximalIdeal R) e G).hom := fun e => by
    show GeometricallyConnected (pullback.snd _ _); infer_instance
  let L : ℕ → Type 1 := fun e => {l : Lev (maximalIdeal R) P X e // ∃ σ : CubTriv l.Pe.c l.Q.i, σ.Even}
  have step : ∀ (e : ℕ) (l : L e), ∃ l' : L (e + 1),
      TorusCompat (thickTrans R _ e) (thickMap R _ e G) l.1.Q.i l'.1.Q.i := fun e l => by
    obtain ⟨P₁, h₁⟩ := exists_isLevelCP (maximalIdeal R) (e + 1) P
    obtain ⟨_, hP⟩ := TowerEx.exists_isCPMap_thickMap l.1.lev h₁
    obtain ⟨Q, hQ, hσ⟩ := TowerEx.exists_lift (TowerEx.isNilpotent_max (e + 1)) _
      (Ideal.Quotient.factor_surjective _) _ _ (TowerEx.isGrpPullback_thickMap _ e G) hP l.1.Q l.2
    obtain ⟨D⟩ := TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max (e + 1)) _ P₁ Q hσ
    exact ⟨⟨⟨Q, P₁, h₁, D⟩, hσ⟩, hQ⟩
  choose nxt hnxt using step
  obtain ⟨D₀⟩ := TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max 0) _ P₀ Q₀ even₀
  let l : ∀ e, L e := fun e => Nat.rec (motive := L) ⟨⟨Q₀, P₀, lev₀, D₀⟩, even₀⟩ nxt e
  have tor : ∀ e, TorusCompat (thickTrans R _ e) (thickMap R _ e G) (l e).1.Q.i (l (e + 1)).1.Q.i :=
    fun e => hnxt e (l e)
  choose β hβ hq using fun e => TowerEx.exists_levelMap hs (l e).1 (l (e + 1)).1 (tor e)
  exact ⟨⟨fun e => (l e).1, tor, β, hβ, hq⟩⟩


set_option maxHeartbeats 800000 in
theorem fibres (laws : Laws) (hU : USt) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R)
    (hR : admitted R I) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G) (hG : IsSemiAbelian G)
    (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) (hgen : IsMonHom gen.hom)
    (hA : LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))))
    (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (T : TowerR I P X) (k : Type) [Field k]
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))) :
    RelAmple ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) ∧
      KTriv ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) := by
  obtain ⟨⟨hN, _⟩, _, hc, _⟩ := hR
  obtain ⟨a, rfl⟩ : ∃ a : R ⧸ I ^ (0 + 1) →+* k, spMap a = x := ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩
  obtain ⟨V, _, _, _, φ, b, hV, hφ, hab, sq⟩ := ClosedPol.exists_trait R I a
  obtain ⟨ψ, sq'⟩ := ClosedPol.exists_generic_square φ hφ
  obtain ⟨A', gen', hgen', hA'⟩ := ClosedPol.exists_fibre_pull laws sq' P.L.isLB A gen hA
  obtain ⟨P', wP, hP', H⟩ := exists_cp_pull _ _ (spMap φ) G ((Over.pullback (spMap φ)).obj G) _ _
    (toBase_mul_pullback G (spMap φ)) P
  rw [← hP'] at hA'
  obtain ⟨P₀, w₀, H₀⟩ := exists_isLevelCP (IsLocalRing.maximalIdeal V) 0 P'
  obtain ⟨wl, hl⟩ := (T.l 0).lev
  obtain ⟨F, pF, w₃, k₃⟩ := ClosedPol.exists_fourth (G := G) (G' := (Over.pullback (spMap φ)).obj G)
    (H := thickObj R I 0 G)
    (H' := thickObj V (IsLocalRing.maximalIdeal V) 0 ((Over.pullback (spMap φ)).obj G)) (P := P) (P' := P')
    (N := (T.l 0).Pe) (N' := P₀) sq (isGrpPullback_pullback G (spMap φ))
    (isGrpPullback_pullback G (thick R I 0)) (isGrpPullback_pullback _ (thick V (IsLocalRing.maximalIdeal V) 0)) H hl H₀
  obtain ⟨Q₀, D₀, β, pβ, hβ⟩ := ClosedPol.exists_desc_pull pF (T.l 0).Q (T.l 0).D k₃
  have hG' : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hG.comm; infer_instance
    · have := hG.smooth; change Smooth (pullback.snd G.hom (spMap φ)); infer_instance
    · have := hG.separated; change IsSeparated (pullback.snd G.hom (spMap φ)); infer_instance
    · have := hG.quasiCompact; change QuasiCompact (pullback.snd G.hom (spMap φ)); infer_instance
    · have := hG.geomConnected; change GeometricallyConnected (pullback.snd G.hom (spMap φ)); infer_instance
    · intro Ω _ _ q
      obtain ⟨E⟩ := hG.fibres Ω (q ≫ spMap φ)
      let em := (Functor.mapMonNatIso (Over.pullbackComp q (spMap φ)) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)
      let e : (Over.pullback (q ≫ spMap φ)).obj G ≅ (Over.pullback q).obj ((Over.pullback (spMap φ)).obj G) := (Mon.forget _).mapIso em
      haveI : IsMonHom e.hom := by
        show IsMonHom em.hom.hom
        infer_instance
      letI := E.grpB
      haveI := E.q_hom
      haveI := E.i_hom
      exact ⟨{ X := E.X
               addCommGroup := E.addCommGroup
               free := E.free
               finite := E.finite
               B := E.B
               grpB := E.grpB
               isAbelian := E.isAbelian
               q := e.inv ≫ E.q
               q_hom := inferInstance
               q_flat := by rw [Over.comp_left]; have := E.q_flat; have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv; infer_instance
               q_surjective := by rw [Over.comp_left]; have := E.q_surjective; have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv; infer_instance
               q_quasiCompact := by rw [Over.comp_left]; have := E.q_quasiCompact; have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv; infer_instance
               i := E.i ≫ e.hom
               i_hom := inferInstance
               isKernel := by refine IsPullback.of_iso E.isKernel (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp }⟩
  have ev := UniformizationSetting.exists_even_of_desc D₀
  obtain ⟨wA, hwA⟩ := hA'
  have pol := ClosedPol.pol_dvr laws hU
    { cdvr := hV, semi := hG', gen := gen', gen_hom := hgen', P := P', wA := wA, wA_gen := hwA, X := X, Q₀ := Q₀,
      P₀ := P₀, lev₀ := ⟨w₀, H₀⟩, even₀ := ev } D₀
  have : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  let _ : Field (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := Ideal.Quotient.field _
  exact ClosedPol.pol_of_ker_eq a b hab _ (T.l 0).Q.isAb (T.l 0).D.M.L.isLB Q₀.B pβ D₀.M.L.isLB hβ pol

theorem isAdmissibleCompleteLocalDomainPrime_of_completeNormal {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) : admitted R (maximalIdeal R) := by
  refine ⟨hB.1, hB.1.2.2.2, hB.2, (maximalIdeal.isMaximal R).isPrime, ?_⟩
  letI := Ideal.Quotient.field (maximalIdeal R)
  infer_instance

end GlobalTheory.Mum.PreUnifEven


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Mum.exists_preU_even : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → EvenOn P → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegPre R) (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), U.P = P ∧ U.gen = gen := by
  intro R _ _ _ hB G _ _ P hs ⟨X, _, _, _, Q₀, P₀, hlev, hev⟩ A gen hgen hA
  obtain ⟨⟨hL, hL2, hL3, -, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have hE := GlobalTheory.LN.ega_holds
  have hU := GlobalTheory.uniformisation_dvr_unconditional
  have hR := GlobalTheory.Mum.PreUnifEven.isAdmissibleCompleteLocalDomainPrime_of_completeNormal hB
  have hP : IsPrincipalIdealRing (R ⧸ maximalIdeal R) := by
    letI := Ideal.Quotient.field (maximalIdeal R)
    infer_instance
  obtain ⟨T⟩ := GlobalTheory.Mum.PreUnifEven.nonempty_towerR_of_even P hs Q₀ P₀ hlev hev
  have hI : maximalIdeal R ≠ ⊤ := hR.2.2.2.1.ne_top
  have := hR.1.1
  have hf := GlobalTheory.Mum.PreUnifEven.fibres hL hU R _ hR G P hs A gen hgen hA X T
  have := GlobalTheory.PreUnifLocal.isLocalRing_quot hI 0
  have e : maximalIdeal R ^ (0 + 1) = maximalIdeal R := pow_one _
  have : (maximalIdeal R ^ (0 + 1)).IsPrime := e.symm ▸ hR.2.2.2.1
  have : IsPrincipalIdealRing (R ⧸ maximalIdeal R ^ (0 + 1)) := e.symm ▸ hP
  have amp : RelAmple (T.l 0).Q.B (T.l 0).D.M.L.L :=
    GlobalTheory.T.cubical_bundle_relAmple_of_ample_fibres hL hL2 (R ⧸ maximalIdeal R ^ (0 + 1)) (GlobalTheory.PreUnifLocal.isAdicComplete_quot hR.2.1 _) _
      (T.l 0).Q.isAb (T.l 0).D.M fun k _ x => (hf k x).1
  obtain ⟨a⟩ := GlobalTheory.T.nonempty_algebraisation_formal_tower_ample hL hL2 hE R _ hR G P X T amp
  have k₀ : KTriv (T.l 0).Q.B (T.l 0).D.M.L.L :=
    GlobalTheory.T.kTriv_of_closed_fibre_localRing hL hL2 (R ⧸ maximalIdeal R ^ (0 + 1)) _ (T.l 0).Q.isAb _ (T.l 0).D.M.L.isLB amp (hf _ _).2
  obtain ⟨hb, v, hv⟩ := a.b_pb 0
  have hK : KTriv a.B a.M.L.L := GlobalTheory.T.kTriv_of_closed_fibre_localRing hL hL2 R _ a.isAb _ a.M.L.isLB a.ample
    (GlobalTheory.PreUnifLocal.kTriv_closedFibre (e.symm ▸ hI) hb a.M.L.isLB (T.l 0).D.M.L.isLB hv.gen k₀)
  obtain ⟨c, hadd, hw⟩ := GlobalTheory.T.exists_additive_weightPoints_of_torusTower hL hL2 hE R _ hR G P X T a hK
  exact GlobalTheory.PreUnifLocal.exists_preU hL.globalFns (fun D e => GlobalTheory.T.torusCoordinates_compat_of_torus_compat hL.globalFns R _ D e G) hI hs T a hK c hadd
    hw A gen hgen hA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreUniformisationEvenTorusCompleteNormalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_preUniformisation_even_torus_completeNormal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → EvenOn P → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegPre R) (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), U.P = P ∧ U.gen = gen := by
  first | exact @GlobalTheory.Mum.exists_preU_even | exact GlobalTheory.Mum.exists_preU_even | (intros; apply GlobalTheory.Mum.exists_preU_even <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinExtTqClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTqLevelZeroOfTorusExtension
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Raynaud

theorem exists_tq_level_zero_of_torusExtension : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G], Nonempty (TorusExtension ((Over.pullback (spMap (residue R))).obj G)) →
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X),
      Nonempty (TQ (thickObj R (maximalIdeal R) 0 G) X) := by
  intro R _ _ G _ _ hT
  obtain ⟨E, ⟨d⟩⟩ := exists_splitExt_isGt_of_torusExtension (ResidueField R) _ hT
  have := E.free
  have := E.finite
  refine ⟨E.X, inferInstance, inferInstance, inferInstance, ?_⟩
  obtain ⟨Q₁, -⟩ := exists_tq_of_gtDatum _ E _ d
  let r : Sp (R ⧸ maximalIdeal R ^ (0 + 1)) ⟶ Sp (ResidueField R) :=
    spMap (Ideal.Quotient.factor (show maximalIdeal R ≤ maximalIdeal R ^ (0 + 1) by simp))
  have hr : r ≫ spMap (residue R) = thick R (maximalIdeal R) 0 := by
    rw [← Spec.map_comp]
    rfl
  let F : (thickObj R (maximalIdeal R) 0 G).left ⟶ ((Over.pullback (spMap (residue R))).obj G).left :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ r) (by rw [Category.assoc, hr]; exact pullback.condition)
  obtain ⟨Q₀, -⟩ := exists_tq_baseChange _ _ r E.X _ _ F ((isGrpPullback_pullback G _).cancel
    ((isGrpPullback_pullback G (thick R (maximalIdeal R) 0)).congr hr.symm (pullback.lift_fst _ _ _).symm)
    (pullback.lift_snd _ _ _)) Q₁
  exact ⟨Q₀⟩

end GlobalTheory.Raynaud

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_cover_step (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : GlobalTheory.TorRef.IsCN R)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (e₀ : ResidueField R →+* Ω) (t : Ω) (q : Polynomial (ResidueField R))
    (hq : q.Monic) (hqt : q.eval₂ e₀ t = 0) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (_ : IsLocalHom ρ)
      (β : ResidueField R' →+* Ω), GlobalTheory.TorRef.IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧
      β.comp (ResidueField.map ρ) = e₀ ∧ t ∈ Set.range β := by
  letI : Algebra (ResidueField R) Ω := e₀.toAlgebra
  have hint : IsIntegral (ResidueField R) t := ⟨q, hq, hqt⟩
  set p := minpoly (ResidueField R) t with hpdef
  have hpm : p.Monic := minpoly.monic hint
  have hirr : Irreducible p := minpoly.irreducible hint
  have hdeg : 0 < p.degree := minpoly.degree_pos hint
  have hpt : p.eval₂ e₀ t = 0 := minpoly.aeval _ t
  have hlift : p ∈ Polynomial.lifts (residue R) :=
    (Polynomial.lifts_iff_set_range p).2 (Polynomial.map_surjective _ IsLocalRing.residue_surjective p)
  obtain ⟨P, hPmap, hPdeg, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hpm
  let C := AdjoinRoot P
  have hfinC : (AdjoinRoot.of P).Finite := by
    have : Module.Finite R (AdjoinRoot P) := (AdjoinRoot.powerBasis' hPm).finite
    exact RingHom.finite_algebraMap.2 this
  have hinjC : Function.Injective (AdjoinRoot.of P) := by
    refine (injective_iff_map_eq_zero _).2 fun r hr => ?_
    rw [AdjoinRoot.of, RingHom.comp_apply, AdjoinRoot.mk_eq_zero] at hr
    have h0 := Polynomial.eq_zero_of_dvd_of_degree_lt hr
      (lt_of_le_of_lt Polynomial.degree_C_le (hPdeg ▸ hdeg))
    simpa using h0
  obtain ⟨R', i1, i2, i3, ρ, σ, hcn', hinj', hfin', hloc, hσ⟩ :=
    GlobalTheory.LocExt.exists_isCN_cover_of_finite R C (AdjoinRoot.of P) hR hinjC hfinC
  let r : ResidueField R' := residue R' (σ (AdjoinRoot.root P))
  have hres : (ResidueField.map ρ).comp (residue R) = (residue R').comp ρ := ResidueField.map_comp_residue ρ
  have hr : p.eval₂ (ResidueField.map ρ) r = 0 := by
    rw [← hPmap, Polynomial.eval₂_map, hres, ← hσ]
    show Polynomial.eval₂ (((residue R').comp σ).comp (AdjoinRoot.of P)) (((residue R').comp σ) (AdjoinRoot.root P)) P = 0
    rw [← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]
  haveI : Fact (Irreducible p) := ⟨hirr⟩
  let gam : AdjoinRoot p →+* ResidueField R' := AdjoinRoot.lift (ResidueField.map ρ) r hr
  let del : AdjoinRoot p →+* Ω := AdjoinRoot.lift e₀ t hpt
  letI : Algebra (AdjoinRoot p) (ResidueField R') := gam.toAlgebra
  letI : Algebra (AdjoinRoot p) Ω := del.toAlgebra
  have hintR : ρ.IsIntegral := hfin'.to_isIntegral
  haveI : Algebra.IsIntegral (AdjoinRoot p) (ResidueField R') := by
    constructor
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨m, hm, hmx⟩ := hintR x
    refine ⟨(m.map (residue R)).map (AdjoinRoot.of p), (hm.map _).map _, ?_⟩
    show Polynomial.eval₂ gam (residue R' x) ((m.map (residue R)).map (AdjoinRoot.of p)) = 0
    rw [Polynomial.eval₂_map, Polynomial.eval₂_map]
    have hgam : (gam.comp (AdjoinRoot.of p)).comp (residue R) = (residue R').comp ρ := by
      rw [← hres]; congr 1; ext a; exact AdjoinRoot.lift_of hr
    rw [hgam, ← Polynomial.hom_eval₂, hmx, map_zero]
  let β₀ : ResidueField R' →ₐ[AdjoinRoot p] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hβ : ∀ a, β₀ (gam a) = del a := fun a => β₀.commutes a
  refine ⟨R', i1, i2, i3, ρ, hloc, β₀.toRingHom, hcn', hinj', hfin', ?_, ⟨gam (AdjoinRoot.root p), ?_⟩⟩
  · ext a
    have h1 : ResidueField.map ρ a = gam (AdjoinRoot.of p a) := (AdjoinRoot.lift_of hr).symm
    show β₀ (ResidueField.map ρ a) = e₀ a
    rw [h1, hβ]
    exact AdjoinRoot.lift_of hpt
  · show β₀ (gam (AdjoinRoot.root p)) = t
    rw [hβ]
    exact AdjoinRoot.lift_root hpt

theorem exists_cover_residue (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : GlobalTheory.TorRef.IsCN R)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (e₀ : ResidueField R →+* Ω) (s : Finset Ω)
    (hs : ∀ t ∈ s, ∃ q : Polynomial (ResidueField R), q.Monic ∧ q.eval₂ e₀ t = 0) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (_ : IsLocalHom ρ)
      (β : ResidueField R' →+* Ω), GlobalTheory.TorRef.IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧
      β.comp (ResidueField.map ρ) = e₀ ∧ (s : Set Ω) ⊆ Set.range β := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, inferInstance, e₀, hR, Function.injective_id,
      RingHom.Finite.id R, by rw [ResidueField.map_id]; rfl, by simp⟩
  | insert t s ht ih =>
    obtain ⟨R₁, i1, i2, i3, ρ₁, hl₁, β₁, hcn₁, hinj₁, hfin₁, hβ₁, hs₁⟩ :=
      ih fun u hu => hs u (Finset.mem_insert_of_mem hu)
    obtain ⟨q, hq, hqt⟩ := hs t (Finset.mem_insert_self t s)
    have hqt' : (q.map (ResidueField.map ρ₁)).eval₂ β₁ t = 0 := by rw [Polynomial.eval₂_map, hβ₁, hqt]
    obtain ⟨R₂, j1, j2, j3, ρ₂, hl₂, β₂, hcn₂, hinj₂, hfin₂, hβ₂, ht₂⟩ :=
      exists_cover_step R₁ hcn₁ β₁ t _ (hq.map _) hqt'
    refine ⟨R₂, j1, j2, j3, ρ₂.comp ρ₁, inferInstance, β₂, hcn₂, hinj₂.comp hinj₁, hfin₂.comp hfin₁, ?_, ?_⟩
    · rw [ResidueField.map_comp, ← RingHom.comp_assoc, hβ₂, hβ₁]
    · rw [Finset.coe_insert]
      refine Set.insert_subset ht₂ (hs₁.trans ?_)
      rintro _ ⟨a, rfl⟩
      exact ⟨ResidueField.map ρ₂ a, by rw [← hβ₂]; rfl⟩

theorem exists_finExt_tq_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (β : G'.left ⟶ G.left) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X), FinExt ρ ∧ IsGrpPullback G' G (spMap ρ) β ∧ Nonempty (GlobalTheory.UU.TQ (thickObj R' (maximalIdeal R') 0 G') X) := by
  intro R _ _ _ hR G _ _ hG
  have hcn : GlobalTheory.TorRef.IsCN R := ⟨hR.1.1, hR.1.2.2.1, hR.1.2.2.2, hR.2⟩
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue R))).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := h₀.smooth
  haveI := h₀.quasiCompact
  haveI := h₀.separated
  let k := ResidueField R
  let Ω := AlgebraicClosure k
  obtain ⟨T⟩ := h₀.fibres Ω (spMap (algebraMap k Ω))
  obtain ⟨s, hs, H⟩ := GlobalTheory.FieldModel.exists_finite_torusExtension_range (algebraMap k Ω) _ T
  obtain ⟨R', i1, i2, i3, ρ, hl, β, hcn', hinj, hfin, hβ, hr⟩ := exists_cover_residue R hcn (algebraMap k Ω) hs.toFinset
    (fun t _ => ⟨minpoly k t, minpoly.monic (Algebra.IsIntegral.isIntegral t), minpoly.aeval k t⟩)
  have hT := H (ResidueField R') (ResidueField.map ρ) β hβ (by simpa using hr)
  let G' := (Over.pullback (spMap ρ)).obj G
  have hT' : Nonempty (TorusExtension ((Over.pullback (spMap (residue R'))).obj G')) := by
    refine GlobalTheory.nonempty_torusExtension_of_comp_eq ?_ G hT
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ResidueField.map_comp_residue]
  obtain ⟨X, _, _, _, ⟨Q⟩⟩ := GlobalTheory.Raynaud.exists_tq_level_zero_of_torusExtension R' G' hT'
  exact ⟨R', i1, i2, i3, ρ, G', inferInstance, inferInstance, _, X, inferInstance, inferInstance, inferInstance,
    ⟨⟨hcn'.1, inferInstance, hcn'.2.1, hcn'.2.2.1⟩, hinj, hfin⟩, isGrpPullback_pullback G (spMap ρ), ⟨Q⟩⟩

end GlobalTheory.Mum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModification
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.HodgeDominates

theorem exists_sec_div {X : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X] {L A : LB X} (hL : L.IsLB)
    (hA : A.IsLB) (t : L.Sec) (i : A.ι) (hi : nonzeroLocus t ≤ A.U i) :
    ∃ r : ℕ, 0 < r ∧ ∀ (M : LB X) (hM : M.IsLB), cls M hM = r • cls L hL - cls A hA →
      ∃ s : M.Sec, nonzeroLocus t ≤ nonzeroLocus s := by
  have hA' := isLB_dual hA
  obtain ⟨N, u, hu⟩ := TwistGen.exists_sec_of_le_chart hA' hL 1 t.f
    (fun y j j' hj hj' => by rw [pow_one]; exact gs_compat t (𝟙 X) y hj hj')
    (nonzeroLocus t) (fun y j hj => mem_nonzeroLocus_iff_isUnit t hj) i hi
  obtain ⟨v, hv⟩ := TwistGen.exists_mul_pow (1 * N) 1 u t
  refine ⟨1 * N + 1, Nat.succ_pos _, fun M hM e => ?_⟩
  have hT := AbLaw.isLB_tw hA' hL ((1 * N + 1 : ℕ) : ℤ)
  have e' : cls _ hT = cls _ hA' - cls _ (AbLaw.isLB_pw hL (-((1 * N + 1 : ℕ) : ℤ))) :=
    cls_div hA' (AbLaw.isLB_pw hL _) _
  obtain ⟨s, hs⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hM hT ((cls_eq_iff hM hT).1 (by
    rw [e, e', AmpleStabFinite.cls_pw hL, cls_dual hA]
    module)) v
  exact ⟨s, fun y hy => hs.ge (hv ⟨hu hy, hy⟩)⟩

theorem nonzeroLocus_lbSecPull {X Y : Scheme.{0}} (L : LB X) (s : L.Sec) (f : Y ⟶ X) :
    nonzeroLocus (lbSecPull L s f) = f ⁻¹ᵁ nonzeroLocus s := Cartier.nonzeroLocus_secPull _ _

theorem exists_sec_of_common {N X X' : Scheme.{0}} [CompactSpace N] [QuasiSeparatedSpace N] (p : N ⟶ X) (p' : N ⟶ X')
    (hp : ∀ V, Function.Bijective (p.app V).hom) (n₀ : N)
    (hn : ∀ W : X.Opens, p n₀ ∈ W → ∃ W' : X'.Opens, p' n₀ ∈ W' ∧ p' ⁻¹ᵁ W' ≤ p ⁻¹ᵁ W)
    {ω : LB X} {ω' P B : LB X'} (hω : ω.IsLB) (hω' : ω'.IsLB) (hP : IsAmpleLB P) (hB : B.IsLB)
    (e : LBIso (ω.pull p) (ω'.pull p')) {k : ℕ} (hk : 0 < k) (ek : cls P hP.isLB + cls B hB = k • cls ω' hω')
    (b : B.Sec) (hb : p' n₀ ∈ nonzeroLocus b) {A : LB X} (hA : A.IsLB) :
    ∃ m : ℕ, 0 < m ∧ ∃ s : (LB.div (lbPow ω m) A).Sec, p n₀ ∈ nonzeroLocus s := by
  obtain ⟨i, hi⟩ := exists_chart hA (p n₀)
  obtain ⟨W', hW', hle⟩ := hn _ hi
  obtain ⟨n, hn, t, h₁, h₂, -⟩ := hP.exists_affine_le hW'
  have hT := isLB_tens hP.isLB hB
  obtain ⟨t', ht'⟩ := exists_sec_pow_nonzeroLocus_eq_inf hP.isLB hB hT
    ((cls_eq_iff hB (LB.isLB_div hT hP.isLB)).1 (by
      rw [cls_div hT hP.isLB, cls_tens hP.isLB hB]; abel)) t (secToPow b n)
  rw [nonzeroLocus_secToPow b hn] at ht'
  have hL := pull_isLB (isLB_lbPow hT n) p'
  obtain ⟨r, hr, H⟩ := exists_sec_div hL (pull_isLB hA p) (lbSecPull _ t' p') (fun _ => i) (by
    rw [nonzeroLocus_lbSecPull, ht', lb_pull_U]
    exact fun y hy => hle (h₂ hy.2))
  have hD := LB.isLB_div (isLB_lbPow hω (r * (n * k))) hA
  obtain ⟨s', hs'⟩ := H _ (pull_isLB hD p) (by
    have e' := (cls_eq_iff (pull_isLB hω p) (pull_isLB hω' p')).2 e
    rw [cls_pull hω, cls_pull hω'] at e'
    rw [cls_pull hD, cls_pull (isLB_lbPow hT n), cls_pull hA, cls_div (isLB_lbPow hω _) hA, cls_lbPow hω,
      cls_lbPow hT, cls_tens hP.isLB hB, ek, map_sub, map_nsmul, map_nsmul, map_nsmul, e', smul_smul, smul_smul,
      mul_assoc])
  obtain ⟨s, rfl⟩ := (bijective_lbSecPull p hp _).2 s'
  refine ⟨_, Nat.mul_pos hr (Nat.mul_pos hn hk), s, ?_⟩
  have := hs' (show n₀ ∈ _ by rw [nonzeroLocus_lbSecPull, ht']; exact ⟨hb, h₁⟩)
  rwa [nonzeroLocus_lbSecPull] at this

theorem bijective_app {U N X : Scheme.{0}} [GlobalTheory.IsNormalScheme X] [IsLocallyNoetherian X] (u : U ⟶ N) (p : N ⟶ X)
    [QuasiCompact u] [IsSchemeTheoreticallyDominant u] [UniversallyClosed p] [IsOpenImmersion (u ≫ p)]
    [IsDominant (u ≫ p)] (V : X.Opens) :
    Function.Bijective (p.app V).hom := by
  have : IsDominant p := .of_comp u p
  have : IsSchemeTheoreticallyDominant p := .of_isDominant p
  refine ⟨p.app_injective V, fun t => mem_range_app_of_forall_isAffineOpen p V t fun W hW _ => ?_⟩
  generalize N.presheaf.map _ t = t
  have ht : (p.app W).hom.IsIntegralElem t := GenPush.isIntegral_app_of_universallyClosed p W hW t
  have hs : ((u ≫ p).app W).hom.IsIntegralElem (u.app (p ⁻¹ᵁ W) t) := by
    change ((u.app (p ⁻¹ᵁ W)).hom.comp (p.app W).hom).IsIntegralElem _
    exact RingHom.IsIntegralElem.map ht _
  obtain ⟨h, hh⟩ := GenPush.exists_app_eq_of_isIntegralElem (u ≫ p) (u ≫ p).denseRange W _ hs
  refine ⟨h, u.app_injective (p ⁻¹ᵁ W) ?_⟩
  rw [← hh]
  rfl

theorem apply_eq_of_apply_eq {U N X X' : Scheme.{0}} [IsReduced N] [X.IsSeparated] (u : U ⟶ N) (p : N ⟶ X)
    (p' : N ⟶ X') [IsDominant u] [IsOpenImmersion (u ≫ p')] (n : N) (w : U) (h : p' n = (u ≫ p') w) :
    p n = (u ≫ p) w := by
  let O : N.Opens := p' ⁻¹ᵁ (u ≫ p').opensRange
  have h₁ : Set.range (O.ι ≫ p') ⊆ Set.range (u ≫ p') := by
    rintro _ ⟨z, rfl⟩
    exact z.2
  have h₂ : Set.range u ⊆ Set.range O.ι := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨u z, z, rfl⟩, rfl⟩
  let q := IsOpenImmersion.lift (u ≫ p') (O.ι ≫ p') h₁
  let u' := IsOpenImmersion.lift O.ι u h₂
  have hq : q ≫ u ≫ p' = O.ι ≫ p' := IsOpenImmersion.lift_fac _ _ _
  have hu : u' ≫ O.ι = u := IsOpenImmersion.lift_fac _ _ _
  have : IsDominant u' := ⟨by
    refine (u.denseRange.preimage O.ι.isOpenEmbedding.isOpenMap).mono ?_
    rintro z ⟨y, hy⟩
    refine ⟨y, O.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hu, hy]⟩
  have hid : u' ≫ q = 𝟙 U := by
    rw [← cancel_mono (u ≫ p'), Category.assoc, hq, reassoc_of% hu, Category.id_comp]
  have key : q ≫ u ≫ p = O.ι ≫ p := ext_of_isDominant u' (by rw [reassoc_of% hid, reassoc_of% hu])
  let z : O.toScheme := (⟨n, w, h.symm⟩ : O)
  have hz : q z = w := (u ≫ p').isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hq]; exact h)
  rw [← hz, ← Scheme.Hom.comp_apply q, key]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem j_s (Y : Model Xo c (RingHom.id c.F)) : Y.j ≫ Y.s = pullback.snd _ _ := by
  have h1 : spMap (RingHom.id c.F) = 𝟙 _ := by
    unfold spMap; rw [CommRingCat.ofHom_id, Spec.map_id]
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over, h1, Category.comp_id]

theorem exists_common_modification (hE : GlobalTheory.Published.SemiAbelianHomExtension) (Y Y' : Model Xo c (RingHom.id c.F))
    (hY : (FlagMod.detOm Y).IsLB) (hY' : (FlagMod.detOm Y').IsLB) :
    ∃ (N : Scheme.{0}) (_ : CompactSpace N) (_ : QuasiSeparatedSpace N) (u : Xo.XF c ⟶ N) (p : N ⟶ Y.X) (p' : N ⟶ Y'.X),
      u ≫ p = Y.j ∧ u ≫ p' = Y'.j ∧ (∀ V, Function.Bijective (p.app V).hom) ∧ (∀ n w, p' n = Y'.j w → p n = Y.j w) ∧
      LBIso ((FlagMod.detOm Y).pull p) ((FlagMod.detOm Y').pull p') := by
  have := c.fin
  have := Y.flat
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y'.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have : AlgebraicGeometry.IsNoetherian Y.X := {}
  have := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have : Y.X.IsSeparated := ⟨by rw [← terminal.comp_from Y.s]; infer_instance⟩
  have : IsDominant Y.j := ⟨LogKS.dense_interior Y⟩
  have : QuasiCompact Y.j := inferInstance
  have : GlobalTheory.IsNormalScheme (Xo.XF c) := GlobalTheory.IsNormalScheme.of_isIso_stalkMap Y.j
  have : IsLocallyNoetherian (Xo.XF c) := isLocallyNoetherian_of_isOpenImmersion Y.j
  let f : Xo.XF c ⟶ pullback Y.s Y'.s := pullback.lift Y.j Y'.j ((j_s Y).trans (j_s Y').symm)
  have hf₁ : f ≫ pullback.fst Y.s Y'.s = Y.j := pullback.lift_fst _ _ _
  have hf₂ : f ≫ pullback.snd Y.s Y'.s = Y'.j := pullback.lift_snd _ _ _
  have : IsImmersion (f ≫ pullback.fst Y.s Y'.s) := hf₁ ▸ inferInstance
  have : QuasiCompact (f ≫ pullback.fst Y.s Y'.s) := hf₁ ▸ inferInstance
  have : IsImmersion f := .of_comp f (pullback.fst Y.s Y'.s)
  have : QuasiCompact f := .of_comp f (pullback.fst Y.s Y'.s)
  have : Flat (f ≫ pullback.fst Y.s Y'.s ≫ Y.s) := by
    rw [reassoc_of% hf₁]; infer_instance
  have : IsFinite f.fromNormalization := AmpUniq.isFinite_fromNormalization_graph f (pullback.fst Y.s Y'.s ≫ Y.s)
  let u := f.toNormalization
  let p := f.fromNormalization ≫ pullback.fst Y.s Y'.s
  let p' := f.fromNormalization ≫ pullback.snd Y.s Y'.s
  have hu₁ : u ≫ p = Y.j := by simp [u, p, hf₁]
  have hu₂ : u ≫ p' = Y'.j := by simp [u, p', hf₂]
  have : IsOpenImmersion u := inferInstance
  have hN := GlobalTheory.IsNormalScheme.pred f.normalization
  have : IsLocallyNoetherian f.normalization := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace f.normalization := QuasiCompact.compactSpace_of_compactSpace p
  have : AlgebraicGeometry.IsNoetherian f.normalization := {}
  have : IsOpenImmersion (u ≫ p) := hu₁ ▸ inferInstance
  have : IsDominant (u ≫ p) := hu₁ ▸ inferInstance
  have : IsOpenImmersion (u ≫ p') := hu₂ ▸ inferInstance
  refine ⟨f.normalization, inferInstance, inferInstance, u, p, p', hu₁, hu₂, bijective_app u p,
    fun n w h => hu₁ ▸ apply_eq_of_apply_eq u p p' n w (hu₂ ▸ h), ?_⟩
  obtain ⟨_, _, _, _, _, n₁, -⟩ := sabPull Out.CubePf.cubePull p Y.t
  obtain ⟨_, _, _, _, _, n₂, -⟩ := sabPull Out.CubePf.cubePull p' Y'.t
  obtain ⟨m₀, -⟩ := ObjMaps.exists_sab_cancel (g := 𝟙 _) Y'.m0.toSABMap
    (by rw [Category.id_comp]; exact Y.m0.toSABMap : SABMap Y.oF.t Xo.univ.t (𝟙 _ ≫ pullback.fst _ _))
  obtain ⟨m₂, -⟩ := ObjMaps.exists_sab_comp Y'.m m₀
  obtain ⟨a₁, -⟩ := ObjMaps.exists_sab_cancel n₁ (hu₁ ▸ Y.m : SABMap Y.oF.t Y.t (u ≫ p))
  obtain ⟨a₂, -⟩ := ObjMaps.exists_sab_cancel n₂
    ((((Category.id_comp _).trans hu₂.symm : 𝟙 _ ≫ Y'.j = u ≫ p')) ▸ m₂ : SABMap Y.oF.t Y'.t (u ≫ p'))
  obtain ⟨e, ⟨_, -⟩, -⟩ := hE.existsUnique_iso_of_extensions hN (IsSemiAbelian.pullback p Y.t.G Y.t.semi)
    (IsSemiAbelian.pullback p' Y'.t.G Y'.t.semi) a₁.cart a₂.cart
  have h₂ := ((isGrpPullback_of_iso e).comp n₂.cart).congr (Category.id_comp _) rfl
  have hdet := PolExt.lbIso_detLie_pull (G := (Over.pullback p).obj Y.t.G) n₁.cart h₂ fun U U' hU hU' =>
    (PolExt.isAffineOpen_snd_inf_fst Y.s Y'.s hU' hU).preimage f.fromNormalization
  have hL : (FlagMod.detLie Y).IsLB :=
    FlagMod.isLB_of_ev _ hY.cover fun i j k _ _ z => FlagMod.ev_detChg_mul i j k z
  have hL' : (FlagMod.detLie Y').IsLB :=
    FlagMod.isLB_of_ev _ hY'.cover fun i j k _ _ z => FlagMod.ev_detChg_mul i j k z
  have e₁ := (cls_eq_iff (pull_isLB hL p) (pull_isLB hL' p')).2 hdet
  rw [cls_pull hL, cls_pull hL'] at e₁
  refine (cls_eq_iff (pull_isLB hY p) (pull_isLB hY' p')).1 ?_
  rw [cls_pull hY, cls_pull hY', show cls _ hY = _ from cls_dual hL hY, show cls _ hY' = _ from cls_dual hL' hY',
    map_neg, map_neg, e₁]

end GlobalTheory.HodgeDominates
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveLineBundleFamilyOfGeometricFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveLineBundleFamilyOfGeometricFibres
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.ZM GlobalTheory.AbLaw.CubeGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AddFib

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

def quad {Z : Over S} (x x' : Z ⟶ A) (y : Z ⟶ T) : Fin 4 → (Z.left ⟶ (A ⊗ T).left) :=
  ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left, (lift 1 y).left]

abbrev uquad (A T : Over S) [GrpObj A] : Fin 4 → ((A ⊗ (A ⊗ T)).left ⟶ (A ⊗ T).left) :=
  quad (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)

theorem comp_quad {Z Z' : Over S} (r : Z' ⟶ Z) (x x' : Z ⟶ A) (y : Z ⟶ T) (i : Fin 4) :
    r.left ≫ quad x x' y i = quad (r ≫ x) (r ≫ x') (r ≫ y) i := by
  fin_cases i <;>
  · simp only [quad, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
    rw [← Over.comp_left, comp_lift]
    try simp only [MonObj.comp_mul, MonObj.comp_one]

theorem prod_quad {Z : Over S} {x x' : Z ⟶ A} (y : Z ⟶ T) (h : x = 1 ∨ x' = 1)
    (U : Type) [CommGroup U] (k : (Z.left ⟶ (A ⊗ T).left) → U) :
    ∏ i, k (quad x x' y i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i = 1 := by
  rcases h with rfl | rfl
  · simp [Fin.prod_univ_four, quad, -Over.comp_left]
  · simp [Fin.prod_univ_four, quad, -Over.comp_left, mul_comm]

theorem homMk_comp_eq_one {Y : Over S} {Z : Scheme.{0}} (r : Z ⟶ Y.left) (u : Y ⟶ A) (b : Z ⟶ S)
    (h : r ≫ u.left = b ≫ η[A].left) : (Over.homMk r rfl : Over.mk (r ≫ Y.hom) ⟶ Y) ≫ u = 1 := by
  have hb : b = r ≫ Y.hom := by
    have := congrArg (· ≫ A.hom) h
    simp only [Category.assoc, Over.w] at this
    exact (this.trans (Category.comp_id _)).symm
  apply Over.OverMorphism.ext
  rw [Hom.one_def]
  exact h.trans (by rw [hb]; rfl)

theorem formal_quad {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ (A ⊗ T)).left) (b : Z ⟶ S)
    (h : r ≫ (fst A (A ⊗ T)).left = b ≫ η[A].left ∨ r ≫ (snd A (A ⊗ T) ≫ fst A T).left = b ≫ η[A].left)
    (U : Type) [CommGroup U] (k : (Z ⟶ (A ⊗ T).left) → U) :
    ∏ i, k (r ≫ uquad A T i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i = 1 := by
  have e : ∀ i, r ≫ uquad A T i = quad ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ fst A (A ⊗ T))
      ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ snd A (A ⊗ T) ≫ fst A T)
      ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ snd A (A ⊗ T) ≫ snd A T) i :=
    fun i ↦ comp_quad (Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) _ _ _ i
  simp only [e]
  exact prod_quad _ (h.imp (homMk_comp_eq_one r _ b) (homMk_comp_eq_one r _ b)) U k

theorem triv_quad_iff {N : LB (A ⊗ T).left} (hN : N.IsLB) {Z : Over S} (x x' : Z ⟶ A) (y : Z ⟶ T) :
    Triv (LB.LinComb N (quad x x' y) ![1, -1, -1, 1]) ↔
      evc hN (x * x') y - evc hN x y - evc hN x' y + evc hN 1 y = 0 := by
  refine (cls_eq_zero_iff (LB.isLB_linComb hN _ _)).symm.trans ?_
  rw [cls_linComb hN, Fin.sum_univ_four]
  have e : ∀ a b c d : Pic Z.left, (1 : ℤ) • a + (-1 : ℤ) • b + (-1 : ℤ) • c + (1 : ℤ) • d = a - b - c + d :=
    fun a b c d ↦ by simp only [one_smul, neg_smul]; abel
  simp only [quad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
  rw [e]
  rfl


omit [GrpObj A] in
theorem exists_chart {X : Scheme.{0}} (j : X ⟶ T.left) :
    ∃ q : ((Over.pullback (j ≫ T.hom)).obj A ⊗ (Over.pullback (j ≫ T.hom)).obj A).left ⟶ (A ⊗ (A ⊗ T)).left,
      IsPullback q ((Over.pullback (j ≫ T.hom)).obj A ⊗ (Over.pullback (j ≫ T.hom)).obj A).hom
        (snd A (A ⊗ T) ≫ snd A T).left j ∧
      q ≫ (fst A (A ⊗ T)).left =
        (fst _ _ : _ ⟶ (Over.pullback (j ≫ T.hom)).obj A).left ≫ pullback.fst A.hom (j ≫ T.hom) ∧
      q ≫ (snd A (A ⊗ T) ≫ fst A T).left =
        (snd _ _ : _ ⟶ (Over.pullback (j ≫ T.hom)).obj A).left ≫ pullback.fst A.hom (j ≫ T.hom) := by
  set B := (Over.pullback (j ≫ T.hom)).obj A
  have hB : IsPullback (pullback.fst A.hom (j ≫ T.hom)) B.hom A.hom (j ≫ T.hom) := IsPullback.of_hasPullback _ _
  have h2 : IsPullback (fst A T).left (snd A T).left A.hom T.hom := IsPullback.of_hasPullback _ _
  have h3 : IsPullback (fst A (A ⊗ T)).left (snd A (A ⊗ T)).left A.hom (A ⊗ T).hom := IsPullback.of_hasPullback _ _
  have hBB : IsPullback (fst B B).left (snd B B).left B.hom B.hom := IsPullback.of_hasPullback _ _
  obtain ⟨m, m₁, m₂⟩ : ∃ m : B.left ⟶ (A ⊗ T).left, m ≫ (fst A T).left = pullback.fst A.hom (j ≫ T.hom) ∧
      m ≫ (snd A T).left = B.hom ≫ j :=
    ⟨h2.lift _ _ (by rw [hB.w, Category.assoc]), h2.lift_fst _ _ _, h2.lift_snd _ _ _⟩
  have hm : IsPullback m B.hom (snd A T).left j := IsPullback.of_right (by rw [m₁]; exact hB) m₂ h2
  have mw : m ≫ (A ⊗ T).hom = B.hom ≫ j ≫ T.hom := by
    rw [← Over.w (snd A T), ← Category.assoc, m₂, Category.assoc]
  have ho : IsPullback ((fst B B).left ≫ pullback.fst A.hom (j ≫ T.hom)) (snd B B).left A.hom
      (m ≫ (A ⊗ T).hom) := by
    rw [mw]; exact hBB.paste_horiz hB
  obtain ⟨q, q₁, q₂⟩ : ∃ q : (B ⊗ B).left ⟶ (A ⊗ (A ⊗ T)).left,
      q ≫ (fst A (A ⊗ T)).left = (fst B B).left ≫ pullback.fst A.hom (j ≫ T.hom) ∧
      q ≫ (snd A (A ⊗ T)).left = (snd B B).left ≫ m :=
    ⟨h3.lift _ _ (by rw [ho.w, Category.assoc]), h3.lift_fst _ _ _, h3.lift_snd _ _ _⟩
  have hq : IsPullback q (snd B B).left (snd A (A ⊗ T)).left m :=
    IsPullback.of_right (by rw [q₁]; exact ho) q₂ h3
  refine ⟨q, ?_, q₁, ?_⟩
  · rw [← Over.w (snd B B)]
    exact hq.paste_vert hm
  · show q ≫ (snd A (A ⊗ T)).left ≫ (fst A T).left = _
    rw [← Category.assoc, q₂, Category.assoc, m₁]

theorem isAdditive_of_geomFibres (S : Scheme.{0}) (A T : Over S) [GrpObj A] [IsLocallyNoetherian T.left]
    (hA : IsAbelianScheme A) (N : LB (A ⊗ T).left) (hN : N.IsLB) (h0 : Triv (ev N (1 : T ⟶ A) (𝟙 T)))
    (hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (t : Over.mk s ⟶ T),
      IsAdditive (ev N (fst A (Over.mk s)) (snd A (Over.mk s) ≫ t))) : IsAdditive N := by
  have hG : Out.GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  have := hA.geomConnected
  have := hA.smooth
  have := hA.proper
  have one₁ : ∀ {Z : Over S} (y : Z ⟶ T), evc hN (1 : Z ⟶ A) y = 0 := fun y ↦ by
    have e := congrArg (CechPic.pull y.left) ((triv_ev_iff hN _ _).1 h0)
    rwa [pull_evc, map_zero, Category.comp_id, MonObj.comp_one] at e
  have H := GlobalTheory.CubeNoeth.fibTriv_clopen N (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left
    (fun R _ _ j ↦ by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_chart (A := A) j
    have hB := isAb_baseChange hA (j ≫ T.hom)
    have one := one_left_fst (A := A) (j ≫ T.hom)
    let B := (Over.pullback (j ≫ T.hom)).obj A
    have : Smooth B.hom := hB.smooth
    have : IsProper B.hom := hB.proper
    have : GeometricallyConnected B.hom := hB.geomConnected
    have sm : Smooth (B ⊗ B).hom := by
      change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have pr : IsProper (B ⊗ B).hom := by
      change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have gc : GeometricallyConnected (B ⊗ B).hom := by
      change GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)
      exact GeometricallyConnected.comp _ _
    have hN' : (LB.LinComb N (fun k ↦ q ≫ uquad A T k) ![1, -1, -1, 1]).IsLB := DVR.linComb_isLB _ hN _ _
    have pf : ∀ M : LB (B ⊗ B).left, M.IsLB → Nonempty (Perf (B ⊗ B).hom M) := fun M hM ↦
      ProperFinite.nonempty_perf_of_isProper (R := R) (B ⊗ B).hom hM
    refine ⟨_, q, (B ⊗ B).hom, hq, TrivLocus.isClosed_trivLocus R _ _ _ hN' (pf _ hN') (pf _ (isLB_pw hN' _)) pr
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ sm gc),
      fun F _ g Z π f' ↦ CubeOpen.triv_basicOpen_of_triv_fibre hG Seesaw.seesaw
        (SmallExtLift.exists_gen_of_small_extension hG KuennethOne.kuenneth_injective)
        R B hB _ hN' (pf _ hN') ?_ ?_ F g Z π f'⟩
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hN _ (formal_quad _ (B.hom ≫ j ≫ T.hom) (Or.inr ?_))
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact one B
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hN _ (formal_quad _ (B.hom ≫ j ≫ T.hom) (Or.inl ?_))
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact one B)
  have all : ∀ t, t ∈ fibTriv N (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left := fun t ↦ by
    let K := AlgebraicClosure (T.left.residueField t)
    let g : Spec (CommRingCat.of K) ⟶ T.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) K)) ≫ T.left.fromSpecResidueField t
    let s : Sp K ⟶ S := g ≫ T.hom
    let t' : Over.mk s ⟶ T := Over.homMk g rfl
    have hadd := hgeo K s t'
    let π := pullback.fst (snd A (A ⊗ T) ≫ snd A T).left g
    let f' := pullback.snd (snd A (A ⊗ T) ≫ snd A T).left g
    refine ⟨K, inferInstance, g, _, π, f', ⟨IsLocalRing.closedPoint K, ?_⟩, IsPullback.of_hasPullback _ _, ?_⟩
    · have := (Scheme.range_fromSpecResidueField t).le
        ⟨Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) K)) (IsLocalRing.closedPoint K), rfl⟩
      exact this
    let Zs : Over S := Over.mk (f' ≫ s)
    have w : π ≫ (A ⊗ (A ⊗ T)).hom = f' ≫ s := by
      rw [← Over.w (snd A (A ⊗ T) ≫ snd A T), ← Category.assoc, pullback.condition, Category.assoc]
    let x : Zs ⟶ A ⊗ (A ⊗ T) := Over.homMk π w
    let τ : Zs ⟶ Over.mk s := Over.homMk f' rfl
    have hx : x ≫ snd A (A ⊗ T) ≫ snd A T = τ ≫ t' := Over.OverMorphism.ext pullback.condition
    have hM : (ev N (fst A (Over.mk s)) (snd A (Over.mk s) ≫ t')).IsLB := pull_isLB hN _
    have ev₁ : ∀ a : Zs ⟶ A, evc hM a τ = evc hN a (x ≫ snd A (A ⊗ T) ≫ snd A T) := fun a ↦ by
      rw [evc_ev hN, lift_fst, lift_snd_assoc, hx]
    have e := (isAdditive_iff hM).1 hadd Zs (x ≫ fst A (A ⊗ T)) (x ≫ snd A (A ⊗ T) ≫ fst A T) τ
    rw [ev₁, ev₁, ev₁] at e
    have ef : (fun k ↦ π ≫ uquad A T k) = quad (x ≫ fst A (A ⊗ T)) (x ≫ snd A (A ⊗ T) ≫ fst A T)
        (x ≫ snd A (A ⊗ T) ≫ snd A T) := funext fun k ↦ comp_quad x _ _ _ k
    unfold TrivAt
    rw [ef, triv_quad_iff hN, one₁, e]
    abel
  let e : T ⟶ A ⊗ (A ⊗ T) := lift 1 (lift 1 (𝟙 T))
  have e₀ : e ≫ fst A (A ⊗ T) = 1 := by simp [e]
  have e₂ : e ≫ snd A (A ⊗ T) ≫ snd A T = 𝟙 _ := by simp [e]
  have htr := triv_of_local hN (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left e.left
    (congrArg (fun q ↦ q.left) e₂) (fun Z b ↦ formal_quad (b ≫ e.left) (b ≫ T.hom) (Or.inl ?_))
    (fun V ↦ ?_) (fun s ↦ H.1 (all s))
  rotate_left
  · rw [Category.assoc, ← Over.comp_left, e₀, Category.assoc]
    rfl
  · obtain ⟨q, hq, -⟩ := exists_chart (A := A) V.ι
    have hB := isAb_baseChange hA (V.ι ≫ T.hom)
    refine ⟨_, q, _, hq, ?_⟩
    rw [← Over.w (snd _ _)]
    exact surj_comp (surj_snd hG hB _) (hG _ _ hB).2
  refine (isAdditive_iff hN).2 fun Y a a' t ↦ ?_
  have h1 : TrivAt N (uquad A T) ![1, -1, -1, 1] (lift a (lift a' t)).left := by
    have h0' : TrivAt N (uquad A T) ![1, -1, -1, 1] (𝟙 _) := by
      unfold TrivAt; simp only [Category.id_comp]; exact htr
    have := h0'.comp (lift a (lift a' t)).left
    rwa [Category.comp_id] at this
  have ef : (fun k ↦ (lift a (lift a' t)).left ≫ uquad A T k) = quad a a' t := funext fun k ↦ by
    rw [comp_quad]; simp only [lift_fst, lift_snd_assoc, lift_snd]
  have h2 : Triv (LB.LinComb N (quad a a' t) ![1, -1, -1, 1]) := by
    have h1' : Triv (LB.LinComb N (fun k ↦ (lift a (lift a' t)).left ≫ uquad A T k) ![1, -1, -1, 1]) := h1
    rwa [ef] at h1'
  have h3 := (triv_quad_iff hN a a' t).1 h2
  rw [one₁, add_zero, sub_sub, sub_eq_zero] at h3
  exact h3

end GlobalTheory.AddFib
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveLineBundleFamilyOfGeometricFibresStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A] [IsLocallyNoetherian T.left], IsAbelianScheme A → ∀ (N : LB (A ⊗ T).left) (hN : N.IsLB), Triv (ev N (1 : T ⟶ A) (𝟙 T)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (t : Over.mk s ⟶ T), IsAdditive (ev N (fst A (Over.mk s)) (snd A (Over.mk s) ≫ t))) → IsAdditive N := by
  first | exact @GlobalTheory.AddFib.isAdditive_of_geomFibres | exact GlobalTheory.AddFib.isAdditive_of_geomFibres | (intros; apply GlobalTheory.AddFib.isAdditive_of_geomFibres <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfFiniteEtaleOfExistsUniqueLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isIso_of_finite_etale_of_existsUnique_lift (W S : Scheme.{0}) (w : W ⟶ S) (hf : IsFinite w)
    (he : Etale w) (hc : PreconnectedSpace S) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S)
    (hs : ∃! x : Sp Ω ⟶ W, x ≫ w = s) : IsIso w := by
  obtain ⟨z⟩ : Nonempty (Sp Ω) := inferInstance
  obtain ⟨x₀, hx₀, hu⟩ := hs
  have hsub : Subsingleton {x : Sp Ω ⟶ W // x ≫ w = s} :=
    ⟨fun a b => Subtype.ext ((hu a.1 a.2).trans (hu b.1 b.2).symm)⟩
  have hne : Nonempty {x : Sp Ω ⟶ W // x ≫ w = s} := ⟨⟨x₀, hx₀⟩⟩
  obtain ⟨_, hcard⟩ := GlobalTheory.FinEt.card_points_eq_finrank w s z
  have h1 : w.finrank (s z) = 1 := by
    rw [← hcard, Nat.card_eq_one_iff_unique]
    exact ⟨hsub, hne⟩
  rw [Scheme.Hom.isIso_iff_finrank_eq]
  funext y
  rw [Pi.one_apply, ← h1]
  exact (Scheme.Hom.isLocallyConstant_finrank w).apply_eq_of_preconnectedSpace y (s z)

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralImageOfField
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem isIntegral_image_of_field {K : Type} [Field K] {S : Scheme.{0}} (g : Sp K ⟶ S) : IsIntegral g.image := by
  have : QuasiCompact g := inferInstance
  have := GlobalTheory.isSchemeTheoreticallyDominant_toImage g
  have : IsReduced g.image := IsSchemeTheoreticallyDominant.isReduced g.toImage
  have hi : IsIrreducible (Set.range g.toImage) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ g.toImage.continuous.continuousOn
  have hc := hi.closure
  rw [g.toImage.denseRange.closure_range] at hc
  have : IrreducibleSpace g.image := { isPreirreducible_univ := hc.2, toNonempty := ⟨hc.1.some⟩ }
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem lbIso_factor {X Y Z : Scheme.{0}} {L : LB X} {L' : LB Y} {M : LB Z} (hL : L.IsLB) (hL' : L'.IsLB) (hM : M.IsLB)
    {F : Y ⟶ X} {a' : Z ⟶ Y} {a : Z ⟶ X} (e : a' ≫ F = a) (h' : LBIso L' (L.pull F)) (h : LBIso M (L.pull a)) :
    LBIso M (L'.pull a') :=
  LBIso.trans hM (pull_isLB hL _) (pull_isLB hL' _) h
    (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L' a' a' rfl) (chartPullSame L (fun _ => a) (fun _ => F) _ a' fun _ => e.symm) h').symm

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PolFieldDescent

theorem exists_polAV : ∀ (K K' : Type) [Field K] [Field K'] (ga : K →+* K') (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → Out.Sym G L → ∀ (A' : PolAV (Sp K')) (α : A'.A.left ⟶ G.left), IsGrpPullback A'.A G (spMap ga) α → LBIso A'.L (L.pull α) → ∃ (A : PolAV (Sp K)) (gen : G ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) L := by
  intro K K' _ _ ga G _ _ L hL hS A' α hP hw
  letI : Algebra K K' := ga.toAlgebra
  have hP' : IsGrpPullback A'.A G (spMap (algebraMap K K')) α := hP
  have : Flat (spMap ga) := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (spMap ga) := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := K) (B := K')⟩
  have : QuasiCompact (spMap ga) := inferInstance
  have hAb : IsAbelianScheme G := PolFlatDescent.isAbelianScheme_of_pull hP A'.isAb
  have hdim : SmoothOfRelativeDimension A'.g G.hom :=
    CM.smoothOfRelativeDimension_of_fibre K K' ga G A'.A.left α A'.A.hom A'.g hAb hP.1 A'.smoothDim
  have hrig : Out.Rigidified G L := DVR.exists_gen_of_local L hL _ _
  have hamp : Out.RelAmple G L :=
    AmpleDescent.relAmple_of_faithfullyFlat K K' G A'.A α L A'.L hAb hP' hL A'.isLB hw A'.ample
  have hK : Out.KTriv G L := AmpleDescent.kTriv_of_pull hP hL A'.isLB hw A'.ktriv
  refine ⟨⟨G, hAb, A'.g, hdim, L, hL, hrig, hS, hamp, hK⟩, Iso.refl G, ?_, ?_⟩
  · show IsMonHom (𝟙 G); infer_instance
  · exact GlobalTheory.lbIso_pull_id hL

end GlobalTheory.PolFieldDescent
end
end
