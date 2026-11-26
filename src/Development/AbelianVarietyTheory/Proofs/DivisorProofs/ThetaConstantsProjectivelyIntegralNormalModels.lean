module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTwoLevelsSameScaleAtTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTwoLevelsSameScaleAtTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CmpTrait

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  rw [← Spec.map_id]; rfl

theorem comp_pow'' {S : Scheme.{0}} {A T T₀ : Over S} [GrpObj A] (ρ : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem card_le_of_thList {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {K : Type} [Field K] [IsAlgClosed K] {x : Sp K ⟶ S} {θ θ' : SecAt G L x} {N N' : ℕ}
    {pt : Fin N → (Over.mk x ⟶ G)} {pt' : Fin N' → (Over.mk x ⟶ G)} {c : Fin N → K} {c' : Fin N' → K}
    (h : ThList G L ρ m x θ pt c) (h' : ThList G L ρ m x θ' pt' c') : N ≤ N' := by
  let e : Over.mk (spMap (RingHom.id K) ≫ x) ⟶ Over.mk x := Over.homMk (spMap (RingHom.id K)) rfl
  have key : ∀ a, ∃ b, pt a = pt' b := fun a => by
    have hp : (e ≫ pt a) ^ (m ^ 2) = 1 := by
      rw [← comp_pow'', (h.2.1 a).1, MonObj.comp_one]
    obtain ⟨b, hb⟩ := h'.2.2 K (RingHom.id K) (e ≫ pt a) hp
    refine ⟨b, Over.OverMorphism.ext ?_⟩
    have hb' : spMap (RingHom.id K) ≫ (pt a).left = spMap (RingHom.id K) ≫ (pt' b).left := hb
    rwa [spMap_id', Category.id_comp, Category.id_comp] at hb'
  choose s hs using key
  have hs' : Function.Injective s := fun a a' he => h.1 ((hs a).trans ((congrArg pt' he).trans (hs a').symm))
  simpa using Fintype.card_le_of_injective s hs'

theorem card_eq_of_thList {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {K : Type} [Field K] [IsAlgClosed K] {x : Sp K ⟶ S} {θ θ' : SecAt G L x} {N N' : ℕ}
    {pt : Fin N → (Over.mk x ⟶ G)} {pt' : Fin N' → (Over.mk x ⟶ G)} {c : Fin N → K} {c' : Fin N' → K}
    (h : ThList G L ρ m x θ pt c) (h' : ThList G L ρ m x θ' pt' c') : N = N' :=
  le_antisymm (card_le_of_thList h h') (card_le_of_thList h' h)

theorem isGenSec_of_nz {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) {g : ℕ} {K : Type}
    [Field K] {x : Sp K ⟶ S} (hP : PolFib G L g x) {θ : SecAt G L x} (hθ : NZ G L x θ) : IsGenSec G L _ θ := by
  obtain ⟨P, α, -, hp, hw⟩ := hP
  obtain ⟨e, he⟩ := exists_univBasis_of_fibre abelianSchemeLaws_all.2 S (Sp K) G L hL P x α hp hw K (𝟙 _) x
    (Category.id_comp x)
  have h0 : spMap (RingHom.id K) ≫ x = x := by rw [spMap_id', Category.id_comp]
  obtain ⟨a, ha⟩ := he.ex (RingHom.id K) h0 (SecM.ofSec G θ)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_smul] at ha
    obtain ⟨q, -, hq⟩ := hθ
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hq
    have e0 : θ.f j = 0 := congrArg (fun s => s.1 j) ha
    rw [e0, Scheme.basicOpen_zero] at hj
    exact hj
  refine (isGenSec_iff θ).2 fun s => ?_
  obtain ⟨b, hb⟩ := he.ex (RingHom.id K) h0 s
  refine ⟨fnR x (b * a⁻¹), ?_⟩
  rw [hb, ha, smul_smul, ← map_mul, _root_.mul_assoc, inv_mul_cancel₀ ha0, _root_.mul_one]

theorem prim_of_finite {V V' K : Type} [CommRing V] [CommRing V'] [Field K] (f : V →+* V') (i : V' →+* K) {J : Type}
    (c : J → K) (hf : f.Finite) (h : Prim i c) : Prim (i.comp f) c := by
  letI := f.toAlgebra
  letI := i.toAlgebra
  letI := (i.comp f).toAlgebra
  haveI : IsScalarTower V V' K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite V V' := hf
  haveI : Algebra.IsIntegral V V' := Algebra.IsIntegral.of_finite V V'
  have key : ∀ z : K, i.IsIntegralElem z → (i.comp f).IsIntegralElem z := fun z hz =>
    isIntegral_trans (R := V) (A := V') z hz
  obtain ⟨h1, a, ha, ha'⟩ := h
  exact ⟨fun b => key _ (h1 b), a, ha, key _ ha'⟩

theorem exists_ext {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (f : V →+* V')
    (fK : FractionRing V →+* FractionRing V') {K : Type} [Field K] [IsAlgClosed K] (io : FractionRing V →+* K)
    (hf : f.Finite) (hfK : ∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) :
    ∃ io' : FractionRing V' →+* K, io'.comp fK = io := by
  letI := fK.toAlgebra
  letI := io.toAlgebra
  letI := f.toAlgebra
  haveI : Module.Finite V V' := hf
  haveI : Algebra.IsIntegral V V' := Algebra.IsIntegral.of_finite V V'
  have hint : ∀ b : V', IsAlgebraic (FractionRing V) (algebraMap V' (FractionRing V') b) := fun b => by
    obtain ⟨p, hp, hp0⟩ := Algebra.IsIntegral.isIntegral (R := V) b
    refine (show IsIntegral (FractionRing V) (algebraMap V' (FractionRing V') b) from
      ⟨p.map (algebraMap V (FractionRing V)), hp.map _, ?_⟩).isAlgebraic
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (FractionRing V) (FractionRing V')).comp (algebraMap V (FractionRing V)) =
        (algebraMap V' (FractionRing V')).comp (algebraMap V V') := RingHom.ext hfK
    rw [e, ← Polynomial.hom_eval₂, hp0, map_zero]
  haveI : Algebra.IsAlgebraic (FractionRing V) (FractionRing V') := ⟨fun z => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V') z
    exact (hint a).mul (hint b).inv⟩
  let φ : FractionRing V' →ₐ[FractionRing V] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩

theorem prim_comp {V K : Type} [CommRing V] [Field K] {i : V →+* K} {J J' : Type} {c : J → K} (h : Prim i c)
    (s : J' → J) (hs : Function.Surjective s) : Prim i (c ∘ s) := by
  obtain ⟨h1, a, ha, ha'⟩ := h
  obtain ⟨b, rfl⟩ := hs a
  exact ⟨fun b => h1 _, b, ha, ha'⟩

theorem cmp_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (y : Sp (FractionRing V) ⟶ Xo.XF c) (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing V →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : V) → Odd m' → 3 ≤ m' → IsUnit (m' : V) → HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m m' (spMap io ≫ y ≫ pullback.fst _ _) d d' → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d' b / a) := by
  intro E _ _ _ H Dw l Xo c V _ _ _ hV y K _ _ io m m' N N' d d' hmo hm3 hmu hmo' hm3' hmu' hd
  have hbase : GlobalTheory.Mum.Base V := ⟨ArcPointDescent.admissibleBase_maximalIdeal_completeDVR hV, hV.2.2⟩
  obtain ⟨T, f, fK, -, -, hff, hfK, hTy⟩ := GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c V hbase hV.1 y
  obtain ⟨io', hio'⟩ := exists_ext f fK io hff hfK
  set i : T.V →+* K := io'.comp (algebraMap T.V (FractionRing T.V)) with hi
  have hinj : Function.Injective i := io'.injective.comp (IsFractionRing.injective T.V (FractionRing T.V))
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  obtain ⟨tK, ⟨mK⟩, ⟨mx⟩⟩ := T.gen
  obtain ⟨m0, -⟩ := ObjMaps.exists_sab_id T.t
  have hpol : GlobalTheory.LN.PolAt T.t (jK T.V) := UnifAfterExt.polAt_of_sabMap m0 mK mx Xo.univ.proper Xo.univ.ample
    Xo.univ.ktriv (jK T.V) (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
  obtain ⟨σ, hσ⟩ := exists_nz_of_polAt abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 E H (Sp T.V) T.t T.V (𝟙 _) T.t m0
    hpol
  have h0 : spMap (RingHom.id T.V) ≫ 𝟙 (Sp T.V) = 𝟙 _ := by rw [Category.comp_id, spMap_id']
  have hσσ : VVRank.pullS T.t.G _ (Over.homMk (spMap (RingHom.id T.V)) h0 : Over.mk (𝟙 (Sp T.V)) ⟶ Over.mk (𝟙 _)) σ = σ := by
    have e : (Over.homMk (spMap (RingHom.id T.V)) h0 : Over.mk (𝟙 (Sp T.V)) ⟶ Over.mk (𝟙 _)) = 𝟙 _ :=
      Over.OverMorphism.ext (spMap_id' T.V)
    rw [e]
    have := VVRank.pullM_id T.t.G T.t.PP.isLB ((1 : ℕ) : ℤ) (SecM.ofSec T.t.G σ)
    rw [VVRank.pullM_ofSec] at this
    exact congrArg (SecM.toSec T.t.G) this
  have hnz : NZ T.t.G T.t.PP.L (𝟙 _) σ := by
    have := hσ T.V (RingHom.id _) _ h0
    rwa [hσσ] at this
  have hmT : ∀ {k : ℕ}, IsUnit (k : V) → IsUnit (k : T.V) := fun h => by simpa using h.map f
  have hmK : ∀ {k : ℕ}, IsUnit (k : V) → (k : K) ≠ 0 := fun h => by
    have := h.map (io.comp (algebraMap V (FractionRing V))); simpa using this.ne_zero
  set x₁ : Sp K ⟶ Sp T.V := spMap i ≫ 𝟙 (Sp T.V) with hx₁
  have ex₁ : spMap io' ≫ jK T.V = x₁ := by rw [hx₁, Category.comp_id, hi, spMap_comp']
  set x : Sp K ⟶ Xo.X := spMap io ≫ y ≫ pullback.fst _ _ with hx
  have ex : spMap io' ≫ T.y ≫ pullback.fst _ _ = x := by rw [hx, hTy, ← hio', spMap_comp']; simp only [Category.assoc]
  set g := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hg
  have hPx : PolFib Xo.univ.t.G Xo.univ.t.PP.L g x := GlobalTheory.T.universalTriple_fibre_principallyPolarised_dimension E H Dw l Xo c K x
  obtain ⟨wK, hwK, -⟩ := mK.lin
  obtain ⟨wx, hwx, -⟩ := mx.lin
  have hPK : PolFib tK.G tK.PP.L g (spMap io') :=
    ((GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback _ _ _ _ _ _ _ _ Xo.univ.t.PP.isLB tK.PP.isLB mx.cart ⟨wx, hwx⟩ g K (spMap io')).1).2 (ex ▸ hPx)
  have hP₁ : PolFib T.t.G T.t.PP.L g x₁ :=
    ex₁ ▸ ((GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback _ _ _ _ _ _ _ _ T.t.PP.isLB tK.PP.isLB mK.cart ⟨wK, hwK⟩ g K (spMap io')).1).1 hPK
  set θ := SecAt.pull T.t.G T.t.PP.L σ i with hθdef
  have hθnz : NZ T.t.G T.t.PP.L x₁ θ := hσ K i x₁ rfl
  have hθ : IsGenSec T.t.G T.t.PP.L _ θ := isGenSec_of_nz T.t.PP.isLB hP₁ hθnz
  obtain ⟨pt, cc, hc⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ T.t.G T.t.PP.L T.t.PP.rig T.t.PP.isLB T.t.PP.rigGen g m _ K x₁ θ hmo (hmK hmu)
    rfl hP₁
  obtain ⟨pt', cc', hc'⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ T.t.G T.t.PP.L T.t.PP.rig T.t.PP.isLB T.t.PP.rigGen g m' _ K x₁ θ hmo'
    (hmK hmu') rfl hP₁
  have hpr : Prim i cc := GlobalTheory.T.thetaConstants_primitive_at_uniformisedTrait E H (Sp T.V) T.t T.V T.cdvr (𝟙 _) T.t ⟨m0⟩ ⟨T.P⟩ σ hnz m _ hmo hm3 (hmT hmu)
    K i pt cc hinj hc
  have hpr' : Prim i cc' := GlobalTheory.T.thetaConstants_primitive_at_uniformisedTrait E H (Sp T.V) T.t T.V T.cdvr (𝟙 _) T.t ⟨m0⟩ ⟨T.P⟩ σ hnz m' _ hmo' hm3'
    (hmT hmu') K i pt' cc' hinj hc'
  have h₁ : HasTh₂ T.t.G T.t.PP.L T.t.PP.rig m m' x₁ cc cc' := ⟨θ, pt, pt', hθ, hc, hc'⟩
  have hK : HasTh₂ tK.G tK.PP.L tK.PP.rig m m' (spMap io') cc cc' :=
    (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian _ T.t.G T.t.PP.L T.t.PP.rig T.t.PP.isLB T.t.PP.rigGen _ tK.G tK.PP.L tK.PP.rig (jK T.V) mK.φ
      tK.PP.isLB tK.PP.rigGen mK.cart ⟨wK, hwK⟩ m m' _ _ K (spMap io') cc cc').2 (ex₁ ▸ h₁)
  have hX : HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m m' x cc cc' :=
    ex ▸ (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB Xo.univ.t.PP.rigGen _ tK.G
      tK.PP.L tK.PP.rig (T.y ≫ pullback.fst _ _) mx.φ tK.PP.isLB tK.PP.rigGen mx.cart ⟨wx, hwx⟩ m m' _ _ K (spMap io')
      cc cc').1 hK
  have eN : N = m ^ (4 * g) := by
    obtain ⟨_, _, _, _, hd1, -⟩ := hd
    obtain ⟨_, _, _, _, hc1, -⟩ := hX
    exact card_eq_of_thList hd1 hc1
  have eN' : N' = m' ^ (4 * g) := by
    obtain ⟨_, _, _, _, -, hd2⟩ := hd
    obtain ⟨_, _, _, _, -, hc2⟩ := hX
    exact card_eq_of_thList hd2 hc2
  subst eN eN'
  obtain ⟨a, s, s', ha, hds, hds'⟩ := (GlobalTheory.T.thetaConstantLists_unique_up_to_perm_scalar _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB
    Xo.univ.t.PP.rigGen g m m' _ _ K x hmo (hmK hmu) hmo' (hmK hmu') hPx).2 cc d cc' d' hX hd
  have ei : i.comp f = io.comp (algebraMap V (FractionRing V)) := by
    ext v
    simp only [hi, RingHom.comp_apply, ← hfK, ← hio']
  have e1 : (fun b => d b / a) = cc ∘ s := funext fun b => by
    rw [hds b, Function.comp_apply, mul_div_cancel_left₀ _ ha]
  have e2 : (fun b => d' b / a) = cc' ∘ s' := funext fun b => by
    rw [hds' b, Function.comp_apply, mul_div_cancel_left₀ _ ha]
  refine ⟨a, ha, ?_, ?_⟩
  · rw [e1, ← ei]
    exact prim_of_finite f i _ hff (prim_comp hpr s s.surjective)
  · rw [e2, ← ei]
    exact prim_of_finite f i _ hff (prim_comp hpr' s' s'.surjective)

end GlobalTheory.UMin.CmpTrait
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTwoLevelsSameScaleAtTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_two_levels_same_scale_at_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (y : Sp (FractionRing V) ⟶ Xo.XF c) (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing V →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : V) → Odd m' → 3 ≤ m' → IsUnit (m' : V) → HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m m' (spMap io ≫ y ≫ pullback.fst _ _) d d' → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d' b / a) := by
  first | exact @GlobalTheory.UMin.CmpTrait.cmp_trait | exact GlobalTheory.UMin.CmpTrait.cmp_trait | (intros; apply GlobalTheory.UMin.CmpTrait.cmp_trait <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsProjectivelyIntegralNormalModels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThInt

theorem spMap_comp_ring' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem grpPullback_self' {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem sec_eq' {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp' {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq' (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem thList_congr' {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {R : Type} [CommRing R] {x : Sp R ⟶ S} (θ : SecAt G L x) {K : Type} [Field K]
    {y y' : Sp K ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x) (hu : u.left = u'.left)
    {N : ℕ} {pt : Fin N → (Over.mk y ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m y (VVRank.pullS G _ u θ) pt c) :
    ∃ pt' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) pt' c := by
  subst e
  obtain rfl : u = u' := Over.OverMorphism.ext hu
  exact ⟨pt, H⟩

theorem thList_pull_pull {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB)
    {ρ : LB.Gen (L.pull (eSec G))} {m : ℕ} {R R' : Type} [CommRing R] [CommRing R'] {K : Type} [Field K]
    (x : Sp R ⟶ S) (θ : SecAt G L x) (i : R →+* R') (j : R' →+* K) {N : ℕ}
    {pt : Fin N → (Over.mk (spMap j ≫ spMap i ≫ x) ⟶ G)} {c : Fin N → K}
    (H : ThList G L ρ m (spMap j ≫ spMap i ≫ x) (SecAt.pull G L (SecAt.pull G L θ i) j) pt c) :
    ∃ pt' : Fin N → (Over.mk (spMap (j.comp i) ≫ x) ⟶ G), ThList G L ρ m (spMap (j.comp i) ≫ x)
      (SecAt.pull G L θ (j.comp i)) pt' c := by
  simp only [SecAt.pull] at H ⊢
  rw [pullS_comp' G hL] at H
  refine thList_congr' θ (by rw [← Category.assoc, spMap_comp_ring']) _ _ ?_ H
  simp only [Over.comp_left, Over.homMk_left]
  rw [spMap_comp_ring']

end GlobalTheory.UMin.ThInt

namespace GlobalTheory.UMin


open GlobalTheory.UMin.ThInt in
theorem thetaInt_hasDiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp (ratHull S.R) ⟶ Xo.XF c), UOver Xo c ρ.P (toRat S.R) u → ∀ (M : RatModel o' Ω) (g : M.Z ⟶ PSpace o n), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ g = spMap (ratHull S.R).val.toRingHom ≫ u ≫ f → M.HasDiv S.th := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm hm3 hmu hn hf o' Ω _ _ _ _ S ρ u hu M g hnorm hg
  haveI : CharZero Ω := ArithBase.char o'
  haveI : IsDedekindDomain o' := ArithBase.ded Ω
  haveI : IsAbelianScheme ρ.P.A := ρ.P.isAb
  haveI : IsCommMonObj ρ.P.A := IsAbelianScheme.comm
  set gd := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hgd
  let vH : ratHull S.R →+* Ω := (ratHull S.R).val.toRingHom
  let v : S.R →+* Ω := S.R.val.toRingHom
  have hv : vH.comp (toRat S.R) = v := RingHom.ext fun _ => rfl
  let x₀ : Sp Ω ⟶ Sp S.R := spMap v ≫ 𝟙 (Sp S.R)
  let θ : SecAt ρ.P.A ρ.P.L x₀ := SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ v
  have hθ : IsGenSec ρ.P.A ρ.P.L _ θ := GlobalTheory.T.realisedThetaSystem_section_generates_field_fibres o' Ω S ρ Ω v
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := hu
  haveI : IsAbelianScheme G := PolPull.isAbelianScheme_of_isGrpPullback ρ.P.isAb hα
  haveI : IsCommMonObj G := IsAbelianScheme.comm
  have hLG : (ρ.P.L.pull α).IsLB := pull_isLB ρ.P.isLB α
  have hU := Xo.univ.t.PP.isLB
  have hUr := Xo.univ.t.PP.rigGen

  have hdim := GlobalTheory.UMin.polFib_univ E H Dw l Xo c Ω (spMap vH ≫ u ≫ pullback.fst _ _)
  have hmv1 := GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback Xo.X (Sp (ratHull S.R)) Xo.univ.t.G Xo.univ.t.PP.L G (ρ.P.L.pull α) (u ≫ pullback.fst _ _) β
    hU hLG hβ hL gd Ω (spMap vH)
  have hmv2 := GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback (Sp S.R) (Sp (ratHull S.R)) ρ.P.A ρ.P.L G (ρ.P.L.pull α) (spMap (toRat S.R)) α
    ρ.P.isLB hLG hα (PolBaseChange.lbIso_refl hLG) gd Ω (spMap vH)
  have hPG : PolFib G (ρ.P.L.pull α) gd (spMap vH) := hmv1.1.2 hdim
  have hPF : PolFib ρ.P.A ρ.P.L gd x₀ := by
    have h := hmv2.1.1 hPG
    rwa [spMap_comp_ring', hv, ← Category.comp_id (spMap v)] at h

  obtain ⟨e, he⟩ := GlobalTheory.T.exists_theta_symmetric_function_values_in_ground_field (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen gd m (n + 1) Ω x₀ θ hm hn hPF

  obtain ⟨P', φG, hgP, hφG, hφGL⟩ := hPG
  have hPL : P'.L.IsLB := P'.isLB
  have hφGα : IsGrpPullback P'.A ρ.P.A x₀ (φG ≫ α) :=
    (hφG.comp hα).congr (by rw [spMap_comp_ring', hv]; exact (Category.comp_id _).symm) rfl
  have hφGβ : IsGrpPullback P'.A Xo.univ.t.G ((spMap vH ≫ u) ≫ pullback.fst _ _) (φG ≫ β) :=
    (hφG.comp hβ).congr (by rw [Category.assoc]) rfl
  have hLα : LBIso P'.L (ρ.P.L.pull (φG ≫ α)) :=
    LBIso.trans hPL (pull_isLB hLG φG) (pull_isLB ρ.P.isLB _) hφGL
      (GenSpread.lbIso_pull_of_lbIso (PolBaseChange.lbIso_refl hLG) φG rfl)
  have hLβ : LBIso P'.L (Xo.univ.t.PP.L.pull (φG ≫ β)) :=
    LBIso.trans hPL (pull_isLB ρ.P.isLB _) (pull_isLB hU _) hLα (GenSpread.lbIso_pull_comp φG rfl rfl hL)
  have hcrd := GlobalTheory.T.thetaMap_coords_of_symmetric_theta_isomorphic_fibre Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hU hUr gd m n o (Xo.XF c)
    (pullback.fst _ _) f (Sp S.R) ρ.P.A ρ.P.L ρ.rig Ω (spMap vH ≫ u) x₀ P' (φG ≫ β) (φG ≫ α) θ e hm hn hf
    ρ.P.isLB ρ.rig_gen hgP hφGβ hLβ hφGα hLα hθ he
  have hdiv : M.HasDiv e := by
    refine GlobalTheory.T.model_hasDiv_of_genericPoint_projectiveCoords o' Ω o M n g e ?_
    rw [hg, ← Category.assoc]
    exact hcrd

  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have hkodd : Odd (S.r * S.N) := by
    obtain ⟨j, -, hj⟩ := ρ.r_eq
    rw [hj, ρ.N_eq]
    exact (ρ.n_odd.pow).mul ((ρ.n_odd.pow).pow)
  have hk3 : 3 ≤ S.r * S.N := by
    have h2 : 2 ≤ S.r * S.N := le_trans S.N_ge (Nat.le_mul_of_pos_left _ S.r_pos)
    obtain ⟨t, ht⟩ := hkodd
    omega
  refine GlobalTheory.T.hasDivisor_of_forall_complete_dvr_points o' Ω M S.Gam (Fin (n + 1)) S.th e (n + 1).factorial (Nat.factorial_pos _) hnorm hdiv ?_
  intro V _ _ _ hV ξ emb _ j₀ hj₀ hej
  haveI : IsDiscreteValuationRing V := hV.1
  let K := AlgebraicClosure (FractionRing V)
  let io : FractionRing V →+* K := algebraMap _ _
  let i : Ω →+* K := io.comp emb
  have hcast : ∀ t : ℕ, t ≠ 0 → (t : K) ≠ 0 := fun t ht => by
    rw [← map_natCast i t]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 ht)
  have hmV : IsUnit (m : V) := by
    simpa using hmu.map (Spec.preimage (ξ ≫ g ≫ PSpace.str o n)).hom
  have hkV : IsUnit ((S.r * S.N : ℕ) : V) := by
    simpa using S.unit.map (Spec.preimage (ξ ≫ M.s)).hom

  have hPK : PolFib ρ.P.A ρ.P.L gd (spMap i ≫ x₀) :=
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback (Sp S.R) (Sp S.R) ρ.P.A ρ.P.L ρ.P.A ρ.P.L (𝟙 _) (𝟙 _) ρ.P.isLB ρ.P.isLB (grpPullback_self' _)
      (ThetaAffineGlue.lbIso_pull_id ρ.P.isLB) gd Ω x₀).2 K i hPF
  have hθK := (GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable (Sp S.R) ρ.P.A ρ.P.L ρ.P.isLB gd Ω x₀ hPF).2 θ hθ K i
  obtain ⟨pt, d, hd⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen gd m (n + 1) K (spMap i ≫ x₀)
    (SecAt.pull ρ.P.A ρ.P.L θ i) hm (hcast m hm.pos.ne') hn hPK
  obtain ⟨pt', d', hd'⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen gd (S.r * S.N)
    ((S.r * S.N) ^ (4 * gd)) K (spMap i ≫ x₀) (SecAt.pull ρ.P.A ρ.P.L θ i) hkodd (hcast _ (NeZero.ne _)) rfl hPK
  have hsym : ∀ j, io (emb (e j)) = symTup d j := he K i pt d hd
  obtain ⟨pt'', hd''⟩ := thList_pull_pull ρ.P.isLB (𝟙 (Sp S.R)) ρ.th₁ v i hd'
  have hT := GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity o' Ω S ρ K (i.comp v) _ pt'' d' hd''

  have h₁ : HasTh₂ ρ.P.A ρ.P.L ρ.rig m (S.r * S.N) (spMap i ≫ x₀) d d' := ⟨_, pt, pt', hθK, hd, hd'⟩
  obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl hLG
  obtain ⟨ρG, hρG, -⟩ := exists_rigidificationPullbackCompatibleIso hα hw ρ.P.isLB hLG ρ.rig_gen
  let xV : Sp K ⟶ Sp (ratHull S.R) := spMap io ≫ spMap emb ≫ spMap vH
  have hxV : spMap i ≫ x₀ = xV ≫ spMap (toRat S.R) := by
    simp only [xV, x₀, i, Category.comp_id, Category.assoc, spMap_comp_ring', ← hv, RingHom.comp_assoc]
  rw [hxV] at h₁
  have h₂ := (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (Sp (ratHull S.R)) G (ρ.P.L.pull α) ρG
    (spMap (toRat S.R)) α hLG hρG hα (PolBaseChange.lbIso_refl hLG) m (S.r * S.N) (n + 1) _ K xV d d').2 h₁
  have h₃ := (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hU hUr (Sp (ratHull S.R)) G (ρ.P.L.pull α) ρG
    (u ≫ pullback.fst _ _) β hLG hρG hβ hL m (S.r * S.N) (n + 1) _ K xV d d').1 h₂
  let y : Sp (FractionRing V) ⟶ Xo.XF c := spMap emb ≫ spMap vH ≫ u
  have h₄ : HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (S.r * S.N) (spMap io ≫ y ≫ pullback.fst _ _) d d' := by
    have e₄ : spMap io ≫ y ≫ pullback.fst _ _ = xV ≫ u ≫ pullback.fst _ _ := by
      simp only [xV, y, Category.assoc]
    rw [e₄]
    exact h₃
  obtain ⟨a, ha, hPa, hPa'⟩ := GlobalTheory.T.thetaConstants_two_levels_same_scale_at_trait E H Dw l Xo c V hV y K io m (S.r * S.N) (n + 1) _ d d' hm hm3 hmV hkodd hk3
    hkV h₄
  have hP := GlobalTheory.T.primitive_families_thetaSymmetric_min_member_compare V K io (n + 1) _ ((S.r * S.N) ^ 2) S.Gam d d' a (fun j => emb (e j)) (fun b => emb (S.th b)) ha
    (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (NeZero.ne _))) hPa hPa' hsym hT.1 hT.2 j₀ ((map_ne_zero emb).2 hj₀)
    (fun j => by simpa [map_div₀] using hej j)
  refine ⟨fun b => by simpa [map_div₀, map_pow] using hP.1 b, ?_⟩
  obtain ⟨b, hb, hb'⟩ := hP.2
  exact ⟨b, fun h0 => hb (by simp [h0]), by simpa [map_div₀, map_pow] using hb'⟩

end GlobalTheory.UMin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsProjectivelyIntegralNormalModelsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_projectively_integral_normalModels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp (ratHull S.R) ⟶ Xo.XF c), UOver Xo c ρ.P (toRat S.R) u → ∀ (M : RatModel o' Ω) (g : M.Z ⟶ PSpace o n), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ g = spMap (ratHull S.R).val.toRingHom ≫ u ≫ f → M.HasDiv S.th := by
  first | exact @GlobalTheory.UMin.thetaInt_hasDiv | exact GlobalTheory.UMin.thetaInt_hasDiv | (intros; apply GlobalTheory.UMin.thetaInt_hasDiv <;> assumption)
end
