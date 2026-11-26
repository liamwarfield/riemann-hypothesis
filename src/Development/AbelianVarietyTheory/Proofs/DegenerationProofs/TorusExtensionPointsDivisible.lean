module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTableAlgClosedCompleteSingleValued
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.SemiDivisible

theorem pow_surj_of_extension {T G B : Type*} [Group T] [CommGroup G] [Group B]
    (i : T →* G) (q : G →* B) (hq : Function.Surjective q) (hk : ∀ x, q x = 1 → ∃ t, i t = x)
    (n : ℕ) (hT : ∀ t : T, ∃ s, s ^ n = t) (hB : ∀ b : B, ∃ c, c ^ n = b) (y : G) :
    ∃ x : G, x ^ n = y := by
  obtain ⟨c, hc⟩ := hB (q y)
  obtain ⟨z, rfl⟩ := hq c
  obtain ⟨t, ht⟩ := hk (y * (z ^ n)⁻¹) (by rw [map_mul, map_inv, map_pow, hc, mul_inv_cancel])
  obtain ⟨s, rfl⟩ := hT t
  refine ⟨i s * z, ?_⟩
  rw [mul_pow, ← map_pow, ht, inv_mul_cancel_right]

theorem pow_surj_chars (X : Type) [AddCommGroup X] [Module.Free ℤ X] (U : Type) [CommGroup U]
    (n : ℕ) (hU : ∀ u : U, ∃ v, v ^ n = u) (t : Multiplicative X →* U) :
    ∃ s : Multiplicative X →* U, s ^ n = t := by
  choose r hr using hU
  let b := Module.Free.chooseBasis ℤ X
  let φ : X →ₗ[ℤ] Additive U :=
    b.constr ℤ fun j => Additive.ofMul (r (t (Multiplicative.ofAdd (b j))))
  let ψ : X →ₗ[ℤ] Additive U := (MonoidHom.toAdditiveRight t).toIntLinearMap
  have h : n • φ = ψ := b.ext fun j => by
    rw [LinearMap.smul_apply, b.constr_basis]
    exact congrArg Additive.ofMul (hr _)
  refine ⟨AddMonoidHom.toMultiplicativeLeft φ.toAddMonoidHom, MonoidHom.ext fun x => ?_⟩
  exact congrArg Additive.toMul (LinearMap.congr_fun h x.toAdd)

theorem pow_surj_units (k : Type) [Field k] [IsAlgClosed k] {n : ℕ} (hn : 1 ≤ n)
    (u : Γ(Sp k, ⊤)ˣ) : ∃ v : Γ(Sp k, ⊤)ˣ, v ^ n = u := by
  let e : Γ(Sp k, ⊤) ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e u.val) (show 0 < n by omega)
  have h : e.symm z ^ n = u.val := by rw [← map_pow, hz, e.symm_apply_apply]
  have hu : IsUnit (e.symm z) := (isUnit_pow_iff (by omega)).1 (h ▸ u.isUnit)
  exact ⟨hu.unit, Units.ext h⟩

theorem exists_lift_point {k : Type} [Field k] [IsAlgClosed k] {G B : Over (Sp k)} (q : G ⟶ B)
    [LocallyOfFiniteType q.left] [QuasiCompact q.left] [Surjective q.left]
    (y : 𝟙_ (Over (Sp k)) ⟶ B) : ∃ x : 𝟙_ (Over (Sp k)) ⟶ G, x ≫ q = y := by
  let x : Sp k ⟶ B.left := y.left
  have : CompactSpace ↥(pullback q.left x) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd q.left x)
  obtain ⟨p, -⟩ := (pullback.snd q.left x).surjective (default : PrimeSpectrum k)
  obtain ⟨z, -, hz⟩ :=
    isClosed_univ.exists_closed_singleton (X := ↥(pullback q.left x)) ⟨p, trivial⟩
  have e : (pointOfClosedPoint (pullback.snd q.left x) z hz ≫ pullback.fst q.left x) ≫ q.left
      = x := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
      Category.id_comp]
  refine ⟨Over.homMk (pointOfClosedPoint (pullback.snd q.left x) z hz ≫ pullback.fst q.left x)
    ?_, ?_⟩
  · rw [← Over.w q, ← Category.assoc]
    exact (congrArg (· ≫ B.hom) e).trans (Over.w y)
  · exact Over.OverMorphism.ext e

theorem pow_surj_abelian (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B]
    (hB : IsAbelianScheme B) {n : ℕ} (hn : 1 ≤ n) (y : 𝟙_ (Over (Sp k)) ⟶ B) :
    ∃ x : 𝟙_ (Over (Sp k)) ⟶ B, x ^ n = y := by
  have := hB.comm
  have hf : IsFinite ((𝟙 B) ^ n : B ⟶ B).left := GlobalTheory.MulFiniteAny.isFinite_mulA k B hB n hn
  have hm : IsMonHom ((𝟙 B) ^ n : B ⟶ B) := GlobalTheory.AbLaw.MulN.isMonHom_mulA B n
  have hs := (flat_and_surjective_of_isFinite_abelianEnd
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected k B hB _ hm hf).2
  obtain ⟨x, hx⟩ := exists_lift_point ((𝟙 B) ^ n : B ⟶ B) y
  exact ⟨x, by rw [← hx, MonObj.comp_pow, Category.comp_id]⟩

end GlobalTheory.SS.SemiDivisible


open GlobalTheory.SS.SemiDivisible in
theorem GlobalTheory.SS.torusExtension_points_divisible : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], Nonempty (TorusExtension G) → ∀ (n : ℕ), 1 ≤ n → ∀ y : (𝟙_ (Over (Sp k)) ⟶ G), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ^ n = y := by
  rintro k _ _ G _ _ ⟨E⟩ n hn
  letI := E.addCommGroup
  letI := E.free
  letI := E.grpB
  haveI := E.q_hom
  haveI := E.i_hom
  haveI := E.q_surjective
  haveI := E.q_quasiCompact
  haveI := (GlobalTheory.torusExtension_smooth_geometricallyConnected G E).1
  have hk := E.isKernel
  refine pow_surj_of_extension (IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k))))
    (IsMonHom.monoidHom E.q (𝟙_ (Over (Sp k)))) (fun b => exists_lift_point E.q b) ?_ n ?_
    (pow_surj_abelian k E.B E.isAbelian hn)
  · intro x hx
    have hx' : x ≫ E.q = 1 := hx
    exact ⟨hk.lift x (toUnit _) (by rw [hx', Hom.one_def]), hk.lift_fst _ _ _⟩
  · intro t
    let e := GlobalTheory.splitTorusPointsEquiv (Sp k) E.X (𝟙_ (Over (Sp k)))
    obtain ⟨s, hs⟩ := pow_surj_chars E.X Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ n
      (pow_surj_units k hn) (e t)
    exact ⟨e.symm s, e.injective (by rw [map_pow, e.apply_symm_apply, hs])⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalPrime
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.LN.UnifPrime

theorem hypW_of_triple {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S) :
    HypW t.G t.PP.L :=
  ⟨t.act.act H.w0, t.act.act (H.bar H.w0), t.act.hom _, t.act.hom _,
    by rw [← t.act.add, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, t.act.one], t.prim, t.adj _⟩

theorem exists_pelUnif : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Ega → USt → PelSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → IsPrincipalIdealRing (R ⧸ I) → ∀ (t : SAB H (Sp R)), PolAt t (jK R) → SplitOver t.G I → ThetaNZ t.G t.PP.L → ∃ P : PELUnif I t, P.TorsionIso := by
  intro h1 h2 h3 _ _ hE hU hP E _ _ _ H R _ _ _ I hA hpi t hpol hs hth
  obtain ⟨A, -, gen, hgen, hL, -⟩ := GlobalTheory.T.exists_polAV_generic_fibre_of_triple h1 h2 E H R t hpol
  have := hA.1.1
  have := hA.2.2.1
  obtain ⟨P, hPL, -⟩ := GlobalTheory.T.exists_cubical_bundle_of_symmetric_semiAbelian h1 R A t.G t.semi gen hgen t.PP t.cub t.sym
  obtain ⟨D, U, hUL, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocalDomain_prime h1 h2 h3 hE hU R I hA hpi t.G P t.semi (hPL ▸ hypW_of_triple t) hs
    (hPL ▸ hth) A gen hgen (hPL ▸ hL)
  obtain ⟨Q, -, -, -, hQ⟩ := hP E H R I hA.1 t D A U (hUL.trans hPL)
  exact ⟨Q, hQ⟩

end GlobalTheory.LN.UnifPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalPrimeStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_complete_local_normal_prime : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Ega → USt → PelSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → IsPrincipalIdealRing (R ⧸ I) → ∀ (t : SAB H (Sp R)), PolAt t (jK R) → SplitOver t.G I → ThetaNZ t.G t.PP.L → ∃ P : PELUnif I t, P.TorsionIso := by
  first | exact @GlobalTheory.LN.UnifPrime.exists_pelUnif | exact GlobalTheory.LN.UnifPrime.exists_pelUnif | (intros; apply GlobalTheory.LN.UnifPrime.exists_pelUnif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullObjectOfThetaPointInAlgClosedSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullObjectOfThetaPointInAlgClosedSubfield
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.ThetaDescent

theorem exists_full_of_theta_in_subfield : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K κ : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field κ] [IsAlgClosed κ] (i : K →+* κ) (m : ℕ) (ρ z : K) (v : D.La → K) (o' : Full D κ), Odd m → Compat H (m ^ 2) z ρ → o'.ρ = i ρ → (o'.I.ζ (m ^ 2) : κ) = i z → o'.Theta m (fun x => i (v x)) → ∃ o : Full D K, o.ρ = ρ ∧ (o.I.ζ (m ^ 2) : K) = z ∧ o.Theta m v := by
  intro hv h6 hU hX hT hE hA E _ _ _ H D l Xo c W₀ Y K κ _ _ _ _ _ i m ρ z v o' hm _ hρ hz hth
  haveI := c.fin
  have hr : H.rt0 ∈ c.F := c.le (baseKA l).ρ.2
  have hζ : zeta l.A ∈ c.F := c.le (baseKA l).ζ.2
  obtain ⟨b, hb⟩ := exists_embedding H c.F hr ρ (i.injective (by rw [map_pow, ← hρ, o'.ρ_sq, map_neg, map_natCast]))
  have hp : IsPrimitiveRoot (i (b ⟨_, hζ⟩)) l.A :=
    ((IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) (ζ := ⟨_, hζ⟩)
      (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne') Subtype.val_injective).map_of_injective
        b.injective).map_of_injective i.injective
  obtain ⟨I, hI⟩ := GlobalTheory.TateRoot.exists_tateIso_zeta_eq E H D l κ _ _ _ o'.I l.A _ l.A_pos hp
  obtain ⟨y, ⟨hy, φ, h₁, h₂, h₃, -⟩, -⟩ := (GlobalTheory.T.fullTorsionObject_existsUnique_moduliPoint hv h6 hU hX hT hE hA E H D l Xo c W₀ Y κ (i.comp b)).1
    { o' with I := I } (fun r h => by
      obtain rfl : r = ⟨_, hr⟩ := Subtype.ext h
      exact hρ.trans (congrArg i hb.symm)) (fun r h => by
      obtain rfl : r = ⟨_, hζ⟩ := Subtype.ext h
      exact hI)
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨o, h₄, h₅⟩ := exists_full hv.1.1 hv.1.2.1.secBaseChangeAny (pullback.snd _ _)
    (IntermediateField.inclusion c.le).toRingHom pullback.condition Y.oF b i y hy o' φ h₁ h₂ h₃ m hm z v hz hth
  exact ⟨o, h₄.trans hb, h₅⟩

end GlobalTheory.Ex.ThetaDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullObjectOfThetaPointInAlgClosedSubfieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullObject_of_thetaPoint_in_algClosed_subfield : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K κ : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field κ] [IsAlgClosed κ] (i : K →+* κ) (m : ℕ) (ρ z : K) (v : D.La → K) (o' : Full D κ), Odd m → Compat H (m ^ 2) z ρ → o'.ρ = i ρ → (o'.I.ζ (m ^ 2) : κ) = i z → o'.Theta m (fun x => i (v x)) → ∃ o : Full D K, o.ρ = ρ ∧ (o.I.ζ (m ^ 2) : K) = z ∧ o.Theta m v := by
  first | exact @GlobalTheory.Ex.ThetaDescent.exists_full_of_theta_in_subfield | exact GlobalTheory.Ex.ThetaDescent.exists_full_of_theta_in_subfield | (intros; apply GlobalTheory.Ex.ThetaDescent.exists_full_of_theta_in_subfield <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TripleStOfLaws
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Ex.Arch

theorem tripleSt_of_laws : Laws → ThetaUnifAV → TripleSt := by
  intro laws hθ E _ _ _ H D La _ _ EF g ty P Hm hty hbij hadj hlin hinj hdisc hspan hH hpos him
  letI := H.starRing
  obtain ⟨D', e, -, -, hEF⟩ := PeriodDatum.exists_datum E H La EF D.p D.q g ty P Hm hty hbij hadj hlin hinj hdisc hspan
    hH hpos him
  let P' : D'.La →+ (Fin g → ℂ) := P.comp e.toAddEquiv.toAddMonoidHom
  have hP' : ∀ a, P' a = P (e a) := fun _ => rfl
  have hr : P'.range = P.range := by
    ext z
    exact ⟨fun ⟨a, h⟩ => ⟨e a, h⟩, fun ⟨a, h⟩ => ⟨e.symm a, by rw [hP', e.apply_symm_apply, h]⟩⟩
  have hper : IsPeriod D' ty P' := by
    refine ⟨fun a x i => ?_, hinj.comp e.injective, by rw [hr]; exact hdisc, ?_, Hm, hH, hpos, fun x y => ?_⟩
    · rw [hP', hP', map_smul, hlin]
    · rw [← hspan]; exact congrArg _ (congrArg SetLike.coe hr)
    · rw [hP', hP', him, hEF]
  obtain ⟨T, L, u, hA, hdim, hamp, hK, ht₁, ht₂, hker, hact, hW⟩ :=
    PeriodPoint.exists_triple laws Moduli.cube_of_isLB principalTorus_algebraic (exists_isMonHom_of_map_lattice hθ laws)
      (lbIso_cubeLB_of_pairing_adjoint laws) (PrimNorm.exists_primitive_normalisation laws.globalFns)
      (kTriv_of_descent laws) relAmple_finite_pow_iso D' ty P' hper
  let Q : PolAV (Sp ℂ) :=
    { A := T.G, isAb := hA, g := g, smoothDim := hdim, L := T.PP.L, isLB := T.PP.isLB,
      rigid := ⟨T.PP.rig, T.PP.rigGen⟩, sym := CechPic.sym_of_isSymmetric T.PP T.sym, ample := hamp, ktriv := hK }
  let oa : Q.OAct (𝓞 E) :=
    { T.act.toRingAct with
      rosati := fun a _ => ⟨⊤, trivial, by
        obtain ⟨r, hr⟩ := NormRos.exists_gen_rosati T.PP.isLB _ _ (T.adj a)
        exact ⟨_, DVR.pullGen_isGen _ _ _ _ hr _⟩⟩ }
  obtain ⟨v, hv, heig⟩ := exists_lieBasis_of_holUnif T.G L g u hA.smooth ht₁ ht₂
  have hdet : DetCond D T.act (spMap (RingHom.id ℂ)) H.rt0 :=
    PeriodPoint.detCond_of_eigenbasis lieMult_of_eigenbasis D T ty hty v hv
      (fun i a => heig _ _ (T.act.hom a) (hact a) i) (RingHom.id ℂ)
  rw [show spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) from Spec.map_id _] at hdet
  refine ⟨Q, oa, L, u, rfl, T.prim, hdet, ht₁, ht₂, fun z => hr ▸ hker z, hact, fun k a b c hk hc => ?_⟩
  have := hW k (e.symm a) (e.symm b) c hk (by rw [hEF, e.apply_symm_apply, e.apply_symm_apply, hc])
  rwa [hP', hP', e.apply_symm_apply, e.apply_symm_apply] at this

end GlobalTheory.Ex.Arch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsomorphismValuesCocycleEqBundleIsoValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsomorphismValuesCocycleEqBundleIsoValue
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section
namespace GlobalTheory.IsoValCocycle
open GlobalTheory.TorusExt GlobalTheory.IsoValConst

theorem exists_th_ne_zero (hL : Laws) (hL₂ : Laws2) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type}
    [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] {N : NumD F} (ν : NumOf D F N) {n : ℕ} (hn : 2 ≤ n)
    (hF : (n : F) ≠ 0) (a : N.A) : ∃ t, t ^ n = 1 ∧ N.th (a * t) ≠ 0 := by
  let y : (TF (R := R) F).left := IsLocalRing.closedPoint F
  obtain ⟨th, ρ, hth, hv⟩ := ThetaInValues.exists_th ν y
  obtain ⟨x, hx, hu⟩ := UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange D.P (jFK (R := R) F ≫ jK R) hn hF th
    (ThetaCoset.ne_zero_of_isGenSec hL₂.secBaseChangeAny D.P _ hth) (ν.eA a)
  obtain ⟨t, rfl⟩ := ν.eA.surjective x
  refine ⟨t, ν.eA.injective (by rw [map_pow, map_one]; exact hx), fun h => ?_⟩
  have q := hu y ν.J (ThetaInValues.good ν y)
  have e := hv (a * t)
  rw [h, MulZeroClass.zero_mul, map_zero, map_mul] at e
  exact not_isUnit_zero ((congrArg IsUnit e).mp q)

theorem cocycle_eq_val : Laws → Laws2 → ∀ (R O' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing O'] [IsDomain O'] [IsNoetherianRing O'] (f : O' →+* R) (P : DegPre R) (D₀ : DegPre O') (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (N' N : NumD C) (ν' : NumOf P C N') (ν : NumOf D₀ C N) (ψ : P.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.P.L (D₀.P.L.pull ψ)) (I : NumB.Iso N.toNumB N'.toNumB), IsGrpPullback P.P.A D₀.P.A (spMap f) ψ → w.IsGen → (∀ x : N.A, (ν'.eA (I.φ x)).left ≫ ψ = (ν.eA x).left) → (∀ x, wVal ν' ν w x ≠ 0) ∧ ∀ x : N.A, (I.h x : C) * wVal ν' ν w (I.φ x) = wVal ν' ν w 1 := by
  intro hL hL₂ R O' _ _ _ _ _ _ f P D₀ C _ _ _ _ _ hf N' N ν' ν ψ w I gp hw he
  let z : Sp C := IsLocalRing.closedPoint C
  have hJ := good ν z
  have hJ' := good ν' z
  have hT : (TF (R := R) C).hom ≫ spMap f = (TF (R := O') C).hom := ArcTransport.base_comm fun r => (hf r).symm
  have hp : ∀ x : N.A, ArcTransport.pushF gp hT (ν'.eA (I.φ x)) = ν.eA x := fun x => Over.OverMorphism.ext (he x)
  have hW : ∀ x : N'.A, stalkConst z (wVal ν' ν w x) = (ArcTransport.wVal w z ν.J ν'.J (ν'.eA x)).val := fun x =>
    toStk_valF (ν'.eA x).left ((D₀.P.L.pull ψ).U (fun _ => ν.J ((ν'.eA x).left ≫ ψ)) ⊓ P.P.L.U (ν'.J (ν'.eA x).left)) z
      ⟨mem_pull.2 (hJ ((ν'.eA x).left ≫ ψ)), hJ' _⟩ _
  refine ⟨fun x h => ?_, ?_⟩
  · have := hW x
    rw [h, map_zero] at this
    exact Units.ne_zero _ this.symm
  let Ω : N.A → ((Sp C).presheaf.stalk z)ˣ := fun x => ArcTransport.wVal w z ν.J ν'.J (ν'.eA (I.φ x))
  have hΩ : ∀ x, stalkUnits z (I.h x) * Ω x = stalkUnits z (I.h 1) * Ω 1 := by
    refine const_of_cube (fun x => stalkUnits z (I.h x) * Ω x) (fun a b c => ?_) (fun a => N.th a ≠ 0) ?_ 2
      (fun x => ?_) (exists_th_ne_zero hL hL₂ ν le_rfl (Nat.cast_ne_zero.2 two_ne_zero))
    · have e := ArcTransport.thS_push gp hT ((isGen_iff _).1 hw) hL.globalFns hJ hJ' (ν'.eA (I.φ a)) (ν'.eA (I.φ b))
        (ν'.eA (I.φ c))
      rw [hp, hp, hp, ← map_one ν'.eA, ← map_one I.φ, ← stalk_θ, ← stalk_θ] at e
      simp only [← map_mul ν'.eA, ← map_mul I.φ] at e
      have e₁ : stalkUnits z (N.θ a b c) = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b *
        Ω c * (Ω 1)⁻¹ * stalkUnits z (N'.θ (I.φ a) (I.φ b) (I.φ c)) := e
      have e₂ := congrArg (stalkUnits z) (I.θ_eq a b c)
      rw [I.h_one, map_one]
      clear_value Ω
      apply Additive.ofMul.injective
      replace e₁ := congrArg Additive.ofMul e₁
      replace e₂ := congrArg Additive.ofMul e₂
      simp only [map_mul, ofMul_mul, ofMul_inv, ofMul_one] at e₁ e₂ ⊢
      linear_combination (norm := abel) -e₁ - e₂
    · obtain ⟨s, hs⟩ := ConstFam.exists_secThrough (φ' := fun _ : Fin 1 => 𝟙 P.P.A.left)
        (φ := fun _ : Fin 1 => 𝟙 D₀.P.A.left) (h := ψ) hw D₀.P.isLB P.P.isLB
        (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) ν.th
      obtain ⟨κ, hκ⟩ := sval_eq ν' z s
      obtain ⟨ρ, hρ⟩ := stalk_th ν z
      obtain ⟨ρ', hρ'⟩ := stalk_th ν' z
      have key : ∀ a : N.A, N.th a ≠ 0 →
          ρ.val = (stalkUnits z (I.h a) * Ω a).val * (κ * stalkConst z I.lam * ρ'.val) := fun a ha => by
        have e := hs.sval (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
          (show Sp C ⟶ _ from (ν'.eA (I.φ a)).left) hJ hJ'
        rw [Fin.prod_univ_one, Category.comp_id] at e
        replace e := e.trans (congrArg (fun q : ((Sp C).presheaf.stalk z)ˣ => q.val * _) (zpow_one _))
        have e' : stalkConst z (N.th a) * ρ.val = (Ω a).val * (κ * (stalkConst z (N'.th (I.φ a)) * ρ'.val)) :=
          (hρ a).trans ((congrArg (fun q => sval (Z := Sp C) ν.th q z ν.J) (he a).symm).trans (e.trans
            (congrArg _ ((hκ _).trans (congrArg _ (hρ' _).symm)))))
        refine ((IsUnit.mk0 _ ha).map (stalkConst z)).mul_left_cancel (e'.trans ?_)
        rw [I.th_eq, Units.val_mul, Units.val_mul, stalkUnits_val, map_mul, map_mul]
        ring
      intro a b ha hb
      have hu : IsUnit (κ * stalkConst z I.lam * ρ'.val) := isUnit_of_mul_isUnit_right (key a ha ▸ ρ.isUnit)
      exact Units.ext (hu.mul_right_cancel ((key a ha).symm.trans (key b hb)))
    · obtain ⟨y, hy⟩ := ValuesTorsion.exists_pow_eq hL D₀.P (jFK (R := O') C ≫ jK O') (ν.eA x) one_le_two
      exact ⟨ν.eA.symm y, by rw [← map_pow, hy, MulEquiv.symm_apply_apply]⟩
  intro x
  apply (stalkConst z).injective
  have e := congrArg Units.val (hΩ x)
  rw [I.h_one, map_one, _root_.one_mul, Units.val_mul, stalkUnits_val] at e
  rw [map_mul, hW, hW, ← map_one I.φ]
  exact e

end GlobalTheory.IsoValCocycle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsomorphismValuesCocycleEqBundleIsoValueStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isomorphismValues_cocycle_eq_bundleIso_value : Laws → Laws2 → ∀ (R O' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing O'] [IsDomain O'] [IsNoetherianRing O'] (f : O' →+* R) (P : DegPre R) (D₀ : DegPre O') (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (N' N : NumD C) (ν' : NumOf P C N') (ν : NumOf D₀ C N) (ψ : P.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.P.L (D₀.P.L.pull ψ)) (I : NumB.Iso N.toNumB N'.toNumB), IsGrpPullback P.P.A D₀.P.A (spMap f) ψ → w.IsGen → (∀ x : N.A, (ν'.eA (I.φ x)).left ≫ ψ = (ν.eA x).left) → (∀ x, wVal ν' ν w x ≠ 0) ∧ ∀ x : N.A, (I.h x : C) * wVal ν' ν w (I.φ x) = wVal ν' ν w 1 := by
  first | exact @GlobalTheory.IsoValCocycle.cocycle_eq_val | exact GlobalTheory.IsoValCocycle.cocycle_eq_val | (intros; apply GlobalTheory.IsoValCocycle.cocycle_eq_val <;> assumption)
end
end
