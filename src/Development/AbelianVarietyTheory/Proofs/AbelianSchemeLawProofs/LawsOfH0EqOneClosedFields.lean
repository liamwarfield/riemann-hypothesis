module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteEtaleLocalSurjectiveOfIsSeparable
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankSectionsLineBundlePowEqPow
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecMInvariantEqBotOrUnivAtGeometricPoint
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GoodPtOfIrredOfMulPull
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfAssociated
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqIdOfFixesTorsion
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsOddNeZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesDescent
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsOfCubeBundleGenerator
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsOfH0EqOneClosedFields
section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UnramExtLaw
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem unramExt_law : UnramExtSt := unramExt

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsFieldGlobalFnsSpec
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem heis_irred_of_isField
    (H : ∀ (K G V : Type) [Field K] [CommGroup G] [Finite G] [AddCommGroup V] [Module K V] [Module.Finite K V] (U : G → V ≃ₗ[K] V) (e : G → G →* Kˣ), (∀ x y v, U x (U y v) = (e x y : K) • U y (U x v)) → Function.Injective e → Module.finrank K V ^ 2 ≤ Nat.card G → ∀ W : Submodule K V, (∀ x v, v ∈ W → U x v ∈ W) → W = ⊥ ∨ W = ⊤)
    (R G V : Type) [CommRing R] (hR : IsField R) [CommGroup G] [Finite G] [AddCommGroup V]
    [Module R V] (hpos : 0 < Module.finrank R V) (U : G → V ≃ₗ[R] V) (e : G → G →* Rˣ)
    (h1 : ∀ x y v, U x (U y v) = (e x y : R) • U y (U x v)) (h2 : Function.Injective e)
    (h3 : Module.finrank R V ^ 2 ≤ Nat.card G) (W : Submodule R V)
    (hW : ∀ x v, v ∈ W → U x v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  letI := hR.toField
  haveI : Module.Finite R V := Module.finite_of_finrank_pos hpos
  exact H R G V U e h1 h2 h3 W hW

theorem isField_globalFns_spec (K : Type) [Field K] :
    IsField Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
  MulEquiv.isField (Field.toIsField K)
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv

theorem irredSt_of_heis : (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ ρ : ThetaGrp P.A P.L k T → (SecM P.A P.L k T ≃ₗ[Γ(T.left, ⊤)] SecM P.A P.L k T), (∀ θ s s', IsActOf P.A P.L k θ s s' ↔ ρ θ (SecM.ofSec P.A s) = SecM.ofSec P.A s') ∧ (∀ θx θy c, CommIsOf P.A P.L k θx θy c → ∀ v, ρ θx (ρ θy v) = (c : Γ(T.left, ⊤)) • ρ θy (ρ θx v)) ∧ (∀ θ θ', θ.pt = θ'.pt → ∃ c : Γ(T.left, ⊤)ˣ, ∀ v, ρ θ' v = (c : Γ(T.left, ⊤)) • ρ θ v) ∧ ∀ θx θy, ∃ θ, θ.pt = θx.pt * θy.pt ∧ ∀ v, ρ θ v = ρ θx (ρ θy v)) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ (θx θy : ThetaGrp P.A P.L k T) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k θx.pt θy.pt c ↔ CommIsOf P.A P.L k θx θy c) ∧ (∀ x : T ⟶ P.A, x ^ k = 1 → Subsingleton T.left → ∃ θ : ThetaGrp P.A P.L k T, θ.pt = x ∧ (Odd k → SymLift P.A P.L k k x θ))) → (∀ (K G V : Type) [Field K] [CommGroup G] [Finite G] [AddCommGroup V] [Module K V] [Module.Finite K V] (U : G → V ≃ₗ[K] V) (e : G → G →* Kˣ), (∀ x y v, U x (U y v) = (e x y : K) • U y (U x v)) → Function.Injective e → Module.finrank K V ^ 2 ≤ Nat.card G → ∀ W : Submodule K V, (∀ x v, v ∈ W → U x v ∈ W) → W = ⊥ ∨ W = ⊤) → WeilSt → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ x : T ⟶ P.A, x ^ k = 1 → WeilIs P.A P.L k x x 1) ∧ (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧ ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c)) → WeilNondegSt → MulNSt → GlobalSectionsRankAlgClosed → IrredSt := by
  intro hρ hWC hH hW hW3 hND hM hH0 K _ _ P k hk hkK W hstab
  have hk1 : 1 ≤ k := by omega
  obtain ⟨ρ, hact, hcomm, -, -⟩ := hρ _ P k (baseOver (Spec (CommRingCat.of K)))
  obtain ⟨hwc, hlift⟩ := hWC _ P k (baseOver (Spec (CommRingCat.of K)))
  obtain ⟨hex, hmul, -, -⟩ := hW _ P k (baseOver (Spec (CommRingCat.of K)))
  obtain ⟨-, hskew, -⟩ := hW3 _ P k (baseOver (Spec (CommRingCat.of K)))
  have hsub : Subsingleton (baseOver (Spec (CommRingCat.of K))).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let G : Subgroup (baseOver (Spec (CommRingCat.of K)) ⟶ P.A) := (powMonoidHom k).ker
  have hG : ∀ x : G, x.1 ^ k = 1 := fun x => x.2
  have hcard : Nat.card G = k ^ (2 * P.g) :=
    (hM _ P k hk1).2.2.2.2 K (𝟙 _) hkK
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  choose θ hθ using fun x : G => hlift x.1 (hG x) hsub
  choose c hc hcu using fun x y : G => hex x.1 y.1 (hG x) (hG y)
  have hcmul : ∀ x x' y : G, c (x * x') y = c x y * c x' y := fun x x' y =>
    (hcu (x * x') y _ (hmul _ _ _ _ _ (hc x y) (hc x' y))).symm
  have hcskew : ∀ x y : G, c y x = (c x y)⁻¹ := fun x y =>
    (hcu y x _ (hskew _ _ _ (hc x y))).symm
  let e : G → G →* Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ := fun x =>
    MonoidHom.mk' (fun y => c x y) (fun y y' => by
      rw [hcskew (y * y') x, hcmul, hcskew y x, hcskew y' x, mul_inv])
  have hfr := hH0 K P k hk1
  refine heis_irred_of_isField hH _ G _ (isField_globalFns_spec K)
    (by rw [hfr]; positivity) (fun x => ρ (θ x)) e ?_ ?_ ?_ W ?_
  · intro x y v
    refine hcomm _ _ _ ((hwc _ _ _).1 ?_) v
    rw [(hθ x).1, (hθ y).1]
    exact hc x y
  · intro x x' hxx
    have hone : ∀ y : G, c 1 y = 1 := fun y => by
      have := hcmul 1 1 y
      rw [_root_.mul_one] at this
      exact left_eq_mul.1 this
    have h : (x * x'⁻¹).1 = 1 := by
      refine hND K P k hkK _ (hG _) fun y hy => ?_
      have h1 : c x ⟨y, hy⟩ = c x' ⟨y, hy⟩ := DFunLike.congr_fun hxx ⟨y, hy⟩
      have h2 : c (x * x'⁻¹) ⟨y, hy⟩ = 1 := by
        rw [hcmul, h1, ← hcmul, mul_inv_cancel, hone]
      have := hc (x * x'⁻¹) ⟨y, hy⟩
      rwa [h2] at this
    exact mul_inv_eq_one.1 (Subtype.ext h)
  · rw [hfr, hcard, ← pow_mul, mul_comm]
  · intro x v hv
    exact hstab (θ x) (SecM.toSec P.A v) (SecM.toSec P.A (ρ (θ x) v)) ((hact _ _ _).2 rfl) hv

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw.AllLaws

theorem laws_of_h0_eq_one :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) = 1) → Laws ∧ Laws2 := by
  intro h1
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  obtain ⟨g, rig, pbc, lemB, cext⟩ := GlobalTheory.laws_without_cohomology
  obtain ⟨cg, fin, grow⟩ := GlobalTheory.AbLaw.CubeAssembly.cube_and_sections
  obtain ⟨cube, square, mulPull, kerPow, weil, symLift, nondeg, charPair, mulq, rel⟩ :=
    GlobalTheory.AbLaw.FromCube.all_of_cubeGen cg
  have sq := (GlobalTheory.AbSquare.square_of_cube cg).1
  have neg := GlobalTheory.exists_gen_negLB g
  have mp := (GlobalTheory.MulPull.mulPull_of_cube_of_symm cg neg).1
  have ker := (GlobalTheory.kerPow_of_square sq).1
  have lft := (GlobalTheory.kerPow_of_square sq).2.2
  have sym := (GlobalTheory.symLift_odd g lft neg).1
  have wc := GlobalTheory.weilIs_iff_commIsOf_and_lift_subsingleton g lft sym
  have w₃ := GlobalTheory.weilIs_alternating_skew_natural g lft
  have act := GlobalTheory.thetaGrp_acts_linearly g
  have gal := GlobalTheory.torsion_invariant_descends mulq
  have tw := GlobalTheory.twisted_pow_translate sq mulq
  have proj := GlobalTheory.AbLaw.polAV_veryAmpleBy pbc
  have h0 : GlobalSectionsRankAlgClosed := GlobalTheory.FinrankGrowthBounds.finrank_sections_lineBundlePow_eq_pow gi h1 rel grow mulq
  have mulN : MulNSt := GlobalTheory.mulN_of_decomposition mulq rel h0 pbc
  have h0T := (GlobalTheory.secM_invariant_eq_bot_or_univ_at_geometric_point pbc).1 h0
  have van := GlobalTheory.AbLaw.PowVanish.first_cohomology_vanishes_powers proj GlobalTheory.T.serre_vanishing_very_ample.1 GlobalTheory.AbLaw.h1Zero_of_isIso mp mulq gal
  obtain ⟨sbcAny, sbc⟩ := GlobalTheory.AbLaw.SecBC.secBaseChange_of_perf GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj proj van
    GlobalTheory.AbLaw.h1Zero_of_isIso GlobalTheory.exists_matrix_basis_ker_of_exact_at_point pbc h0T
  have stw : SecTwistSt := GlobalTheory.SecTwist.secTwist_of_perf GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj proj van
    GlobalTheory.AbLaw.h1Zero_of_isIso GlobalTheory.exists_matrix_basis_ker_of_exact_at_point pbc h0T tw
  have irred : IrredSt :=
    GlobalTheory.irredSt_of_heis act wc GlobalTheory.heisenberg_family_irreducible weil w₃ nondeg mulN h0
  have irrT := (GlobalTheory.secM_invariant_eq_bot_or_univ_at_geometric_point pbc).2 irred
  have gen := GlobalTheory.NoBasePoint.exists_sec_value_isUnit gi sq h0T mulq
  have mono := GlobalTheory.SepPoints.eq_of_forall_value_eq gi cg sbc mulq
  have ample : AmpleSt :=
    GlobalTheory.VeryAmplePow.ample (GlobalTheory.exists_sections_span_affine sbc) gen mono
  have goodPt : GoodPtSt := GlobalTheory.GoodPoint.goodPt_of_irred gi irred act ker mp mulq gen
  have vv := GlobalTheory.VVRank.vvRank sbcAny irrT mp lft act ker pbc mulq
  have finOrd := GlobalTheory.TorsionFixedAut.eq_id_of_fixes_torsion g symLift act wc irred h0 ample kerPow
  have sep := GlobalTheory.EndDivisible.eq_one_of_forall_pow_dvd gi mp fin
  have serreK := GlobalTheory.SerreField.serre_algClosed mulq
    (GlobalTheory.DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one mulq) sep finOrd
    GlobalTheory.eq_one_of_pow_eq_one_of_congr_one
  have serre : SerreSt := GlobalTheory.serre_of_algClosed pbc g GlobalTheory.local_rigidity serreK
  have ext : Semi.extend_existsSt.{0} :=
    GlobalTheory.ExtendRig.extend_exists gi GlobalTheory.isRegularRing_of_smooth
      (GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
        GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
        GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE)
      GlobalTheory.exists_lineBundle_extension
  have quot : QuotientSt :=
    GlobalTheory.quotient_isAbelianScheme_of_quotientScheme gi
      (GlobalTheory.exists_quotient_scheme_of_finite_flat_subgroup GlobalTheory.FiniteFlatKilled.main
        (GlobalTheory.HopfQuot.affine_quotient GlobalTheory.exists_basis_mem_of_span_eq_top_of_semilocal) mulq)
  exact ⟨⟨h0, sbc, ample, kerPow, mulPull, mulN, cube, square, rig, weil, nondeg, symLift, irred,
    goodPt, serre, ext, cext, lemB, GlobalTheory.EvVal.evValSt, vv, g, pbc, quot, GlobalTheory.unramExt_law⟩,
    ⟨sbcAny, stw, charPair, GlobalTheory.smoothDense⟩⟩

end GlobalTheory.AbLaw.AllLaws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsSixthOfUnifUniq
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem lawsSixth_of_unifUniq : GlobalFnsSt → SecBaseChangeSt → AmpleSt → Laws6 :=
  fun h₁ h₂ h₃ => ⟨GlobalTheory.T.uniformisation_degenerationData_unique h₁ h₂ h₃⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PowEqOneOfLocalLift
section -- merged from Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.WeilPairing
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilPairingLaws

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

def tors {S : Scheme.{0}} (P : PolAV S) (T : Over S) (k : ℕ) : Subgroup (T ⟶ P.A) where
  carrier := {x | x ^ k = 1}
  one_mem' := one_pow k
  mul_mem' := by
    intro x y hx hy
    haveI := P.isAb.comm
    have hc : Commute x y := mul_comm x y
    have hx' : x ^ k = 1 := hx
    have hy' : y ^ k = 1 := hy
    show (x * y) ^ k = 1
    rw [hc.mul_pow, hx', hy', _root_.mul_one]
  inv_mem' := by
    intro x hx
    have hx' : x ^ k = 1 := hx
    show x⁻¹ ^ k = 1
    rw [inv_pow, hx', inv_one]

def unitSpec {K : Type} [CommRing K] (u : Kˣ) : Γ(Spec (CommRingCat.of K), ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom u

end GlobalTheory.IndefiniteRowSideFullHecke.WeilPairingLaws
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PairingLawsCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.WeilPairingLaws

theorem theta_pt_pow {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S}
    (θ : ThetaGrp P.A P.L (k : ℤ) T) : θ.pt ^ k = 1 := by
  refine ((GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube
    GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1).1).1 S P k T θ.pt).1 ?_
  intro p
  refine ⟨⊤, trivial, (GlobalTheory.KerPow.pull_iff _ _ _).2 ?_⟩
  exact GlobalTheory.KerPow.HasGen.pull ⟨θ.φ, θ.isGen⟩ _ fun _ => rfl

theorem pow_eq_one_of_local_lift {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} (x : T ⟶ P.A)
    (h : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp P.A P.L (k : ℤ) (overRes V), θ.pt = overResι V ≫ x) : x ^ k = 1 := by
  ext1
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨V, hV, θ, hθ⟩ := h p
  refine ⟨V, hV, ?_⟩
  have e : overResι V ≫ (x ^ k) = overResι V ≫ (1 : T ⟶ P.A) := by
    rw [MonObj.comp_pow, MonObj.comp_one, ← hθ, theta_pt_pow]
  exact congrArg (fun q => q.left) e

theorem mem_tors_of_weilIs {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} {x y : T ⟶ P.A}
    {c : Γ(T.left, ⊤)ˣ} (h : WeilIs P.A P.L (k : ℤ) x y c) :
    x ∈ tors P T k ∧ y ∈ tors P T k := by
  constructor
  · refine pow_eq_one_of_local_lift P k x fun p => ?_
    obtain ⟨V, hV, ⟨θx, θy, hx, -⟩, -⟩ := h p
    exact ⟨V, hV, θx, hx⟩
  · refine pow_eq_one_of_local_lift P k y fun p => ?_
    obtain ⟨V, hV, ⟨θx, θy, -, hy⟩, -⟩ := h p
    exact ⟨V, hV, θy, hy⟩

section Clauses

variable {S : Scheme.{0}} (P : PolAV S) (k : ℕ) (T : Over S)

end Clauses

end GlobalTheory.PairingLawsCompare
end
end
