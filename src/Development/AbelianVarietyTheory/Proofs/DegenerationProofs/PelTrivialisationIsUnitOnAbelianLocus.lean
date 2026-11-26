module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTestPowerIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PelTrivialisationIsUnitOnAbelianLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PelTrivialisationIsUnitOnAbelianLocus
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

theorem psiUnitOn_abLocus_pel : Laws → Laws2 → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), P.TorsionIso → IsOpen (abLocus t.G) → ∀ y, PsiUnitOn P.D.toPre y (abLocus t.G) :=
  fun h1 h2 h3 h4 h5 _ _ _ _ _ R _ _ _ I hA t P _ ho y =>
    GlobalTheory.T.psiUnitOn_abelian_locus_uniformisation h1 h2 h3 h4 h5 R I hA P.D P.A t.G t.semi P.U ho y

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PelTrivialisationIsUnitOnAbelianLocusStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pelTrivialisation_isUnit_on_abelianLocus : Laws → Laws2 → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), P.TorsionIso → IsOpen (abLocus t.G) → ∀ y, PsiUnitOn P.D.toPre y (abLocus t.G) := by
  first | exact @GlobalTheory.psiUnitOn_abLocus_pel | exact GlobalTheory.psiUnitOn_abLocus_pel | (intros; apply GlobalTheory.psiUnitOn_abLocus_pel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIntegrallyClosedOverring
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.GoodOut

open GlobalTheory.Points

theorem exists_hom_ker {R : Type} [CommRing R] (z : PrimeSpectrum R) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (f : R →+* K), ∀ t, f t = 0 ↔ t ∈ z.asIdeal :=
  ⟨AlgebraicClosure z.asIdeal.ResidueField, inferInstance, inferInstance,
    (algebraMap z.asIdeal.ResidueField _).comp (algebraMap R z.asIdeal.ResidueField), fun _ =>
    (map_eq_zero_iff (algebraMap z.asIdeal.ResidueField _) (RingHom.injective _)).trans
      Ideal.algebraMap_residueField_eq_zero⟩

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}


theorem exists_th_notMem (hL : Laws) (hL₂ : Laws2) (ρ : S.Real) (z : PrimeSpectrum S.R) (a : S.Gam) :
    ∃ c : S.Gam, ρ.n • c = 0 ∧ (⟨S.th (a + c), S.th_mem _⟩ : S.R) ∉ z.asIdeal := by
  obtain ⟨K, _, _, f, hf⟩ := exists_hom_ker z
  let x : Sp K ⟶ Sp S.R := spMap f
  obtain ⟨j, hj, hr⟩ := ρ.r_eq
  have hM : S.r * S.N = ρ.n * ρ.n ^ (j - 1 + ρ.k * 2) := by
    rw [hr, ρ.N_eq, ← pow_mul, ← pow_add, ← pow_succ']
    congr 1
    omega
  have hn : (ρ.n : K) ≠ 0 := by
    have h := (S.unit.map (f.comp (algebraMap o S.R))).ne_zero
    rw [map_natCast, hM, Nat.cast_mul] at h
    exact left_ne_zero_of_mul h
  obtain ⟨θ, hθ, hv⟩ := UnitTheta.exists_sec_of_baseOver S.R ρ.P ρ.th₁
  obtain ⟨y₀, hy₀, e₀⟩ := ThetaFibre.exists_mem_nonzeroLocus_fibre hL₂.secBaseChangeAny S.R ρ.P ρ.th₁ ρ.th₁_basis
    (x (IsLocalRing.closedPoint K))
  let u : Over.mk x ⟶ baseOver (Sp S.R) := Over.homMk x (by simp)
  obtain ⟨y, hy, H⟩ := UnitTheta.exists_good_point_of_sec hL.polBaseChange hL.goodPt _ ρ.P θ K x ρ.n
    ρ.n_prime.two_le hn ⟨_, hθ y₀ hy₀, _, e₀.symm⟩ (u ≫ ρ.pt a)
  have := ρ.P.isAb.comm
  obtain ⟨h0, hsm⟩ := ThetaReal.pt_nsmul ρ.pt ρ.pt_add
  obtain ⟨c, hc, -⟩ := ρ.pt_bij K x y (by rw [hM, pow_mul, hy, one_pow])
  obtain ⟨a₀, -, uniq⟩ := ρ.pt_bij K x 1 (one_pow _)
  refine ⟨c, (uniq _ (by beta_reduce; rw [hsm, MonObj.comp_pow, hc, hy])).trans
    (uniq _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm, fun h => ?_⟩
  have e : (u ≫ ρ.pt a * y).left = spMap f ≫ (ρ.pt (a + c)).left := by
    rw [← hc, ρ.pt_add]
    exact congrArg CommaMorphism.left (MonObj.comp_mul u _ _).symm
  rw [e] at H
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (H (x := IsLocalRing.closedPoint K) trivial)
  have hk' := (le_preimage_iff _ _).2 hk
  have hU := le_preimage_mono _ (Scheme.basicOpen_le _ _) hk'
  refine ((le_preimage_basicOpen_iff _ hU _).1 hk').ne_zero ?_
  rw [hv _ _ _ (ρ.th_val (a + c)) K f k hU, (hf _).2 h, zero_mul]

section Comb

variable {X Z : Scheme.{0}} (p : X ⟶ Z) {B : LB X} {J : Type} [Fintype J] (s : J → B.Sec) (W : Z.Opens)

variable [DecidableEq J] (b c : Matrix J J Γ(Z, W)) (hc : c * b = 1)
include hc

end Comb

section Transfer

variable {Z : Scheme.{0}} (P : PolAV Z)

end Transfer

variable (ρ : S.Real) (c : CubicalStr ρ.P.A ⟨ρ.P.L, ρ.rig, ρ.P.isLB, ρ.rig_gen⟩)


section Support

include ρ

end Support


end GlobalTheory.ZH.GoodOut

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.PerpTorus
open GlobalTheory.ZH.TorusPerp GlobalTheory.TorusExt

theorem exists_form {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) {X : Type} [AddCommGroup X]
    (yy : S.Gam →+ X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range) (hs : Function.Surjective yy)
    (a : S.Gam) (ha : a ∈ S.perp yy.ker) :
    ∃ m : X →+ ZMod (S.r * S.N), ∀ b α, yy b = QuotientAddGroup.mk α → m α = eStd S.g _ a b := by
  choose σ hσ using fun α : X => hs (QuotientAddGroup.mk α)
  have ind : ∀ b b' : S.Gam, yy b = yy b' → eStd S.g _ a b = eStd S.g _ a b' := by
    intro b b' e
    have h0 : eStd S.g _ a (b - b') = 0 := ha _ (by rw [AddMonoidHom.mem_ker, map_sub, e, sub_self])
    rw [← sub_add_cancel b b', eStd_add_right, h0, zero_add]
  refine ⟨AddMonoidHom.mk' (fun α => eStd S.g _ a (σ α)) fun α β => ?_, fun b α e => ind _ _ ((hσ α).trans e.symm)⟩
  rw [← eStd_add_right]
  exact ind _ _ (by rw [map_add (f := _), hσ, hσ, hσ, QuotientAddGroup.mk_add])


attribute [local instance] gtGroup in
theorem exists_torus_point : LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (g : u.Geom) (a : S.Gam) (ha : a ∈ S.perp l.yy.ker), ∃ (q : QkPt u.D.toPre (PadicAlgCl p) S.N) (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) S.N q (g.pt (S.r • a)) ∧ ∀ χ, (τ (Multiplicative.ofAdd χ) : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζN ^ (l.wt χ ⟨a, ha⟩).val)) := by
  intro hL hT o Ω _ _ _ hA S ρ p _ y₀ u l g a ha
  have hG := hL.1.globalFns
  have hN := S.N_ge
  have hr := S.r_pos
  have hn : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : IsDomain o := hA.inj.isDomain _
  have : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have hadm : AdmBase u.V (maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hB := u.D.tau_bimult
  obtain ⟨f, f₁, f₂, -, -, f₅⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hn.pos

  have hζ : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) := S.prim.pow (pow_pos hn.pos 2) (pow_two _)
  let ω : (PadicAlgCl p)ˣ := Units.map (y₀.comp (algebraMap o S.R)).toMonoidHom (hζ.isUnit hn.ne).unit
  have hωv : (ω : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N))) := rfl
  have hω : IsPrimitiveRoot ω (S.r * S.N) := by
    have : NeZero ((S.r * S.N : ℕ) : PadicAlgCl p) := ⟨Nat.cast_ne_zero.2 hn.ne⟩
    rw [← IsPrimitiveRoot.coe_units_iff, ← Polynomial.isRoot_cyclotomic_iff,
      ← Polynomial.map_cyclotomic _ (y₀.comp (algebraMap o S.R))]
    exact (hζ.isRoot_cyclotomic hn.pos).map (y₀.comp (algebraMap o S.R))

  let pt : Multiplicative S.Gam →* (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) :=
    MonoidHom.mk' (fun a => g.pt a.toAdd) fun _ _ => g.pt_add _ _
  have pt_nsmul : ∀ (n : ℕ) b, g.pt (n • b) = g.pt b ^ n := fun n b => map_pow pt (Multiplicative.ofAdd b) n
  have onto : ∀ b, ∃ q, f q = g.pt b := fun b => f₂ _ (by
    rw [← pt_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (S.r * S.N)), ZMod.natCast_self, zero_smul]
    exact map_one pt)
  obtain ⟨m, hm⟩ := exists_form S l.yy l.yy_onto a ha
  let τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ :=
    (AddChar.zmodChar (S.r * S.N) hω.pow_eq_one).toMonoidHom.comp m.toMultiplicative
  have hτ : ∀ α, τ (Multiplicative.ofAdd α) = ω ^ (m α).val := fun _ => rfl
  have hτ1 : τ ^ (S.r * S.N) = 1 := MonoidHom.ext fun α => by
    show (ω ^ (m α.toAdd).val) ^ (S.r * S.N) = 1
    rw [pow_right_comm, hω.pow_eq_one, one_pow]
  obtain ⟨q, hq, hqτ⟩ := exists_qkPt_tor (F := PadicAlgCl p) hB τ hτ1
  obtain ⟨q₁, hq₁, hq₁τ⟩ := exists_qkPt_tor (F := PadicAlgCl p) (k := S.N) hB (τ ^ S.r) (by rw [← pow_mul, hτ1])
  have hq1 : f q ^ (S.r * S.N) = 1 := by
    obtain ⟨w, hw⟩ := u.U.ext
    exact ((f₁ _ _).2 rfl w hw).1
  obtain ⟨a', ha', -⟩ := g.pt_bij (f q) hq1
  have haa : a' = a := by
    rw [← sub_eq_zero]
    refine eq_zero_of_eStd _ _ _ fun b => ?_
    obtain ⟨q', hq'⟩ := onto b
    have w₁ := (f₅ q q' _).1 (weilQkIs_tor hG q q' hq hqτ)
    rw [← ha', hq'] at w₁
    have w₂ := g.weil a' b (ω ^ (eStd S.g _ a' b).val) (by
      rw [Units.val_pow_eq_pow_val, hωv, ← map_pow, ← map_pow, ← pow_mul])
    have e₁ := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG u.A.isAb u.A.isLB w₂ w₁)
    rw [hτ] at e₁
    have e₂ := ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₁)
    rw [hm b _ (l.yy_eq b q' _ ((f₁ _ _).2 hq'.symm) (g.pt_over b))] at e₂
    have e₃ := eStd_add_left S.g _ (a' - a) a b
    rw [sub_add_cancel, e₂] at e₃
    exact left_eq_add.1 (e₃.trans (add_comm _ _))
  subst haa
  refine ⟨q₁, τ ^ S.r, hq₁, hq₁τ, ?_, fun χ => ?_⟩
  · rw [pt_nsmul]
    refine (GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N S.r (S.r * S.N) (by omega) hr
      (mul_comm _ _) q₁ q _).2 (hq₁.trans hq.symm) ((isNsmul_iff_eq _ _ _).2 ?_) ((f₁ _ _).2 ha')
    rw [(isTorusPtF_iff_eq _ _).1 ((isTor_iff _ _).1 hq₁τ), (isTorusPtF_iff_eq _ _).1 ((isTor_iff _ _).1 hqτ),
      ofMul_pow, map_nsmul]
  · obtain ⟨b, hb⟩ := l.yy_onto (QuotientAddGroup.mk χ)
    have z : S.ζN ^ S.N = 1 := by
      rw [ThetaSys.ζN, ← pow_mul, ← S.prim.pow_eq_one]
      congr 1
      ring
    have z' : S.ζN = (S.ζ ^ (S.r * S.N)) ^ S.r := by
      rw [ThetaSys.ζN, ← pow_mul]
      congr 1
      ring
    rw [l.wt_eq b χ hb, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, ← pow_eq_pow_mod _ z,
      MonoidHom.pow_apply, hτ, hm b χ hb, z', pow_right_comm, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hωv,
      ← map_pow, ← map_pow, ← map_pow, ← map_pow]

end GlobalTheory.ZH.PerpTorus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HvHolds
namespace GlobalTheory.Ex

theorem hv_holds : GlobalTheory.Ex.HV :=
  GlobalTheory.TestFibre.laws_all GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1

end GlobalTheory.Ex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFibreSectionValueInFrameLinearUniqueExists
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFibreSectionValueInFrameLinearUniqueExists
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestFibre.CombValue

open GlobalTheory.UT.CoefBasic

variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} {x : TFK (R := R) F ⟶ A.A} {e : FrameAt A x}

theorem valIs_comb {J : Type} [Fintype J] {s : J → SecA A F k} {b c : J → F} {t : SecA A F k} (h : IsComb A s b t)
    (hs : ∀ i, ValIs A (s i) x e (c i)) : ValIs A t x e (∑ i, b i * c i) := fun z I hI => by
  have e₀ : SecM.ofSec A.A t = ∑ l, cF R (b l) • SecM.ofSec A.A (s l) := by
    refine Subtype.ext (funext fun j => (h j).trans ?_)
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  let φ : SecM A.A A.L k (TFK (R := R) F) →+ (TFK (R := R) F).left.presheaf.stalk z :=
    AddMonoidHom.mk' (fun v => ThetaAct.sv v (ptSecT A.A x).left z I) fun a b => ThetaAct.sv_add a b _ z hI
  let ψ : F →+* (TFK (R := R) F).left.presheaf.stalk z := cstH (R := R) z
  have e₁ : ∀ a : F, @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z a) = ψ a := fun a => cst_eq z a
  refine (congrArg φ e₀).trans ((map_sum φ _ _).trans ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e₁, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => (ThetaAct.sv_smul _ _ _ z hI).trans ?_
  rw [ThetaPtMove.ptSecT_fst, map_mul, _root_.mul_assoc, ← e₁, ← e₁]
  exact congrArg (@id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z (b i)) * ·) (hs i z I hI)

theorem valIs_smul {t t' : SecA A F k} {a c : F} (h : ∀ j, t'.f j = liftFun A.A _ (cF R a) * t.f j)
    (ht : ValIs A t x e c) : ValIs A t' x e (a * c) := by
  have := valIs_comb (J := Unit) (s := fun _ => t) (b := fun _ => a) (c := fun _ => c) (t := t')
    (fun j => (h j).trans (by rw [Fintype.sum_unique])) fun _ => ht
  rwa [Fintype.sum_unique] at this

theorem valIs_unique {t : SecA A F k} {c c' : F} (h : ValIs A t x e c) (h' : ValIs A t x e c') : c = c' := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' (Z := (TFK (R := R) F).left) A.isLB z
  have := (Units.mul_left_inj _).1 ((h z J hJ).symm.trans (h' z J hJ))
  simp only [id, cst_eq] at this
  exact cstH_inj z this

theorem exists_valIs (hL : Laws) (he : e.IsGen) (t : SecA A F k) : ∃ c, ValIs A t x e c := by
  obtain ⟨w, hw, -⟩ := hL.evVal _ A k x e he t
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 w
  refine ⟨c, fun z J hJ => ?_⟩
  have := ThetaPtMove.sv_of_isValueAt hw (𝟙 _) z hJ
  rw [Category.id_comp] at this
  exact this

theorem valIs_linear : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (x : TFK (R := R) F ⟶ A.A) (e : FrameAt A x), (∀ (J : Type) [Fintype J] (s : J → SecA A F k) (b c : J → F) (t : SecA A F k), IsComb A s b t → (∀ i, ValIs A (s i) x e (c i)) → ValIs A t x e (∑ i, b i * c i)) ∧ (∀ (t t' : SecA A F k) (a c : F), (∀ j, t'.f j = liftFun A.A _ (cF R a) * t.f j) → ValIs A t x e c → ValIs A t' x e (a * c)) ∧ (∀ (t : SecA A F k) c c', ValIs A t x e c → ValIs A t x e c' → c = c') ∧ (e.IsGen → ∀ t : SecA A F k, ∃ c, ValIs A t x e c) :=
  fun hL _ _ _ _ _ _ _ _ _ _ =>
    ⟨fun _ _ _ _ _ _ h hs => valIs_comb h hs, fun _ _ _ _ h ht => valIs_smul h ht,
      fun _ _ _ h h' => valIs_unique h h', fun he t => exists_valIs hL he t⟩

end GlobalTheory.TestFibre.CombValue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFibreSectionValueInFrameLinearUniqueExistsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFibreSectionValueInFrame_linear_unique_exists : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (x : TFK (R := R) F ⟶ A.A) (e : FrameAt A x), (∀ (J : Type) [Fintype J] (s : J → SecA A F k) (b c : J → F) (t : SecA A F k), IsComb A s b t → (∀ i, ValIs A (s i) x e (c i)) → ValIs A t x e (∑ i, b i * c i)) ∧ (∀ (t t' : SecA A F k) (a c : F), (∀ j, t'.f j = liftFun A.A _ (cF R a) * t.f j) → ValIs A t x e c → ValIs A t' x e (a * c)) ∧ (∀ (t : SecA A F k) c c', ValIs A t x e c → ValIs A t x e c' → c = c') ∧ (e.IsGen → ∀ t : SecA A F k, ∃ c, ValIs A t x e c) := by
  first | exact @GlobalTheory.TestFibre.CombValue.valIs_linear | exact GlobalTheory.TestFibre.CombValue.valIs_linear | (intros; apply GlobalTheory.TestFibre.CombValue.valIs_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsCoordsRelabelledTwistedDataSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsCoordsRelabelledTwistedDataSeries
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.RelabelCoords

theorem isCoordPt_unit_mul {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I : Type} {x : I → (T ⟶ P.A)}
    {z : T ⟶ P.A} {v w : I → Γ(T.left, ⊤)} (u : Γ(T.left, ⊤)ˣ) (h8 : ∀ i, v i = u.val * w i)
    (H : IsCoordPt P k x z w) : IsCoordPt P k x z v := by
  obtain ⟨ho, hu, th, s1, α, τ, U, s2, h1, h2, h3, h4, h5, h6, h7⟩ := H
  refine ⟨ho, hu, th, s1, α, ⟨fun j => τ.s j * InhTate.gv u⁻¹ _⟩, U, s2, h1, h2, fun i j => ?_, h4, h5, h6, fun i j => ?_⟩
  · rw [map_mul, map_mul, h3 i j, InhTate.res_gv, InhTate.res_gv, _root_.mul_assoc]
  · rw [h7 i j, h8 i, map_mul]
    have e : (T.left.presheaf.map (homOfLE (le_top : LB.wchart P.L (fun _ : Fin 1 => z.left) j ≤ ⊤)).op).hom u.val *
        (T.left.presheaf.map (homOfLE (le_top : LB.wchart P.L (fun _ : Fin 1 => z.left) j ≤ ⊤)).op).hom
          (u⁻¹).val = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have key : ∀ {A : Type} [CommRing A] (a b c d : A), a * b = 1 → c * d = a * c * (d * b) := fun a b c d h => by
      linear_combination (-(c * d)) * h
    exact key _ _ _ _ e

theorem twRel_unique {O : Type} [CommRing O] {N : NumD O} {k : ℕ} {β : N.Form k} {u r : Oˣ} {j : ℕ} {q : N.QT j}
    {p p' : (N.twist β u).QT j} (h : TwRel β u r q p) (h' : TwRel β u r q p') : p = p' :=
  Subtype.ext (Prod.ext (h.1.trans h'.1.symm)
    (NumD.Gt.ext (h.2.1.trans h'.2.1.symm) (funext fun z => (h.2.2 z).trans (h'.2.2 z).symm)))

theorem series_iso {C : Type} [NormedField C] {N N' : NumD C} (J : NumD.Iso N N') {m : ℕ} (hm : Odd m)
    {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h₁ : p'.1.1.toAdd = J.e p.1.1.toAdd) (h₂ : J.Rel p.1.2 p'.1.2) :
    N.tx m p = (J.lam⁻¹ : Cˣ) * N'.tx m p' ∧
      ∀ g g', J.Rel g g' → N.ev m p g = ((J.lam * J.h g.b ^ (m ^ 2))⁻¹ : Cˣ) * N'.ev m p' g' := by
  have H := (NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)).2.2.2.2 m hm p p' h₁ h₂
  refine ⟨?_, fun g g' hg => ?_⟩
  · have e : N'.tx m p' = J.lam * N.tx m p := by
      rw [NumD.tx, NumD.tx, ← J.e.toEquiv.tsum_eq, ← tsum_mul_left]
      exact tsum_congr fun χ => (H χ).1
    rw [e, Units.inv_mul_cancel_left]
  · have e : N'.ev m p' g' = (J.lam * J.h g.b ^ (m ^ 2) : Cˣ) * N.ev m p g := by
      rw [NumD.ev, NumD.ev, ← J.e.toEquiv.tsum_eq, ← tsum_mul_left]
      exact tsum_congr fun χ => (H χ).2 g g' hg
    rw [e, Units.inv_mul_cancel_left]

theorem theta_coord : GlobalTheory.UT.LL → BrGtSt → TXSt → EVSt → AllD fun {E} _ _ _ {H} D => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (I : FullI o) (N N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (k : ℕ) (β : N.Form k) (u : Cˣ) (r : ℕ → Cˣ) (J : NumD.Iso (N.twist β u) N') (q : ∀ j : ℕ, D.La → N.QT j), (∀ j, 0 < j → ∀ x, ∃ (q' : N'.QT j) (p' : QkPt M.P.D.toPre C j) (z : TFK (R := M.W) C ⟶ M.P.A.A), TwJ β u (r j) J (q j x) q' ∧ ν'.QPt p' q' ∧ z.left = (I.ev j x).left ≫ M.φ ∧ M.P.ToA C j p' z) → ∀ m, Odd m → ∀ p : D.La → (N.twist β u).QT (m ^ 2), (∀ x, TwRel β u (r (m ^ 2)) (q _ x) (p x)) → (withI o I).Theta m (fun x => (N.twist β u).tx m (p x)) ∧ ∀ j, 0 < j → ∀ z (p₀ : (N.twist β u).QT j), TwRel β u (r j) (q j z) p₀ → (withI o I).Coord m (I.ev j z) fun x => (N.twist β u).ev m (p x) p₀.1.2 := by
  intro hL hB hT hE E _ _ _ H D C _ _ _ _ _ o M I N N' ν' k β u r J q hq m hm p hp
  have hm2 : 0 < m ^ 2 := pow_pos hm.pos 2
  choose q' p' x htw hqp hx hA using hq (m ^ 2) hm2
  have hJ : ∀ a, (q' a).1.1.toAdd = J.e (p a).1.1.toAdd ∧ J.Rel (p a).1.2 (q' a).1.2 := fun a => by
    obtain ⟨p₁, h₁, h₂⟩ := htw a
    rwa [twRel_unique h₁ (hp a)] at h₂
  let τ : (baseOver (Sp C)).left ⟶ (TFK (R := M.W) C).left := 𝟙 (Sp C)
  have : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp C)))
  have hτ : τ ≫ (TFK (R := M.W) C).hom = (baseOver (Sp C)).hom ≫ jFK (R := M.W) C := rfl
  have hx' : ∀ a, τ ≫ (x a).left = (I.ev (m ^ 2) a).left ≫ M.φ := fun a => (Category.id_comp _).trans (hx a)
  have hk : ∀ a, I.ev (m ^ 2) a ^ (m ^ 2) = 1 := fun a => (I.onto _ hm2 _).2 ⟨a, rfl⟩
  have hs : Subsingleton (Sp C) := inferInstanceAs (Subsingleton (PrimeSpectrum C))
  have hn : Nonempty (Sp C) := inferInstanceAs (Nonempty (PrimeSpectrum C))
  have hτv : ∀ (c : Cˣ) (a : C), fnOf (c * a) = (unitOn c).val * (show Γ(Sp C, ⊤) from τ.appTop.hom (fnOf a)) := fun c a =>
    map_mul (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom _ _
  refine ⟨?_, fun j hj z p₀ h₀ => ?_⟩
  · have Q := hT M.W _ M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext N' ν' m hm D.La p' q' x hA hqp
    have : Subsingleton (TFK (R := M.W) C).left := hs
    have : Nonempty (TFK (R := M.W) C).left := hn
    have : Subsingleton (baseOver (Sp C)).left := hs
    have Q₁ := ThetaPtUp.isThetaPtOver_down τ M.cart M.lb hτ hx' hk (ThetaCoord.isThetaPtOver_of_subsingleton _ Q)
    have Q₂ := (isCoordPt_one_iff o.P m (T := baseOver (Sp C)) _ _).2 ⟨hm, Q.2.1, Q₁⟩
    have Q₃ := isCoordPt_unit_mul (v := fun a => fnOf ((N.twist β u).tx m (p a))) (unitOn J.lam⁻¹)
      (fun a => by rw [(series_iso J hm (hJ a).1 (hJ a).2).1]; exact hτv _ _) Q₂
    exact ThetaNest.isThetaPt_of_over _ hm Q.2.1 ((isCoordPt_one_iff _ _ _ _).1 Q₃).2.2
  · obtain ⟨q₁, p₁, y, ⟨p₂, t₁, -, t₂⟩, hq₁, hy, hA₁⟩ := hq j hj z
    obtain rfl := twRel_unique h₀ t₁
    let q₄ : N'.QT (j * 4) := ⟨(q₁.1.1 ^ 4, q₁.1.2), by
      rw [NumD.mem_QT, pow_mul, N'.mem_QT.1 q₁.2, toAdd_pow, NumD.io_nsmul]⟩
    have B := hB M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
    obtain ⟨p₄, hp₄⟩ := (B.2.2.2.2 (j * 4)).2.1 q₄
    have e₁ : p₄.y = 4 • p₁.y := by
      rw [← hp₄.1, ← hq₁.1, ← map_nsmul]; rfl
    have e₂ : p₄.g = p₁.g := (B.2.1 q₁.1.2).unique hp₄.2 hq₁.2
    have := M.admissible_base_of_complete_dvr.2
    have hA₄ := ((GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL M.W _ M.admissible_base_of_complete_dvr.1 M.P.D M.P.A M.t.G M.t.semi M.P.U C j 4 (j * 4) hj (by norm_num) rfl
      p₁ p₄ y).1 e₁ e₂).1 hA₁
    have Q := hE M.W _ M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext N' ν' m hm D.La p' q' x hA hqp
      (j * 4) (by omega) p₄ q₄ y hA₄ hp₄
    have Q₁ := FullExtend.isCoordPt_move τ M.cart M.lb τ (𝟙 _) (Category.comp_id _) hτ (fun th h s => by
      obtain ⟨c, hc⟩ := h s
      have e := VVRank.pullM_id M.P.A.A M.P.A.isLB 1 (SecM.ofSec M.P.A.A th)
      exact ⟨c, fun j => (hc j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e).symm)⟩)
      hx' hk (z := I.ev j z) ((Category.id_comp _).trans hy) Q
    exact isCoordPt_unit_mul (v := fun a => fnOf ((N.twist β u).ev m (p a) p₀.1.2))
      (unitOn (J.lam * J.h p₀.1.2.b ^ (m ^ 2))⁻¹)
      (fun a => by rw [(series_iso J hm (hJ a).1 (hJ a).2).2 _ _ t₂]; exact hτv _ _) Q₁

end GlobalTheory.RelabelCoords
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsCoordsRelabelledTwistedDataSeriesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoints_coords_relabelled_twistedData_series : GlobalTheory.UT.LL → BrGtSt → TXSt → EVSt → AllD fun {E} _ _ _ {H} D => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (I : FullI o) (N N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (k : ℕ) (β : N.Form k) (u : Cˣ) (r : ℕ → Cˣ) (J : NumD.Iso (N.twist β u) N') (q : ∀ j : ℕ, D.La → N.QT j), (∀ j, 0 < j → ∀ x, ∃ (q' : N'.QT j) (p' : QkPt M.P.D.toPre C j) (z : TFK (R := M.W) C ⟶ M.P.A.A), TwJ β u (r j) J (q j x) q' ∧ ν'.QPt p' q' ∧ z.left = (I.ev j x).left ≫ M.φ ∧ M.P.ToA C j p' z) → ∀ m, Odd m → ∀ p : D.La → (N.twist β u).QT (m ^ 2), (∀ x, TwRel β u (r (m ^ 2)) (q _ x) (p x)) → (withI o I).Theta m (fun x => (N.twist β u).tx m (p x)) ∧ ∀ j, 0 < j → ∀ z (p₀ : (N.twist β u).QT j), TwRel β u (r j) (q j z) p₀ → (withI o I).Coord m (I.ev j z) fun x => (N.twist β u).ev m (p x) p₀.1.2 := by
  first | exact @GlobalTheory.RelabelCoords.theta_coord | exact GlobalTheory.RelabelCoords.theta_coord | (intros; apply GlobalTheory.RelabelCoords.theta_coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRootStalk
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.TestVal

theorem hyps (h : Laws) (h₂ : Laws2) :
    LL ∧ TwistBCSpanStatement ∧ TWM.VRatioGtStatement ∧ TWStatement ∧ UUStatement := by
  obtain ⟨h₃, h₄, h₅, -⟩ := GlobalTheory.furtherLaws_of_laws h GlobalTheory.twistBaseChange
  have t := twistBCSpan_of GlobalTheory.twistBaseChange
  have r : TWM.VRatioGtStatement := GlobalTheory.RatioVal.main
  exact ⟨⟨h, h₂, h₃, h₄, h₅⟩, t, r, TWM.tw_of h.globalFns t r, GlobalTheory.UnitBallFree.main h.globalFns GlobalTheory.twistBaseChange⟩

theorem exists_rat_log (p : ℕ) [Fact p.Prime] {x : PadicAlgCl p} (hx : x ≠ 0) :
    ∃ r : ℚ, Real.log ‖x‖ = r * Real.log p := by
  have hi : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have h0 : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hi hx
  have e : ‖x‖ = ‖(minpoly ℚ_[p] x).coeff 0‖ ^ (1 / (minpoly ℚ_[p] x).natDegree : ℝ) :=
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[p] (PadicAlgCl p) x
  refine ⟨1 / (minpoly ℚ_[p] x).natDegree * (-((minpoly ℚ_[p] x).coeff 0).valuation : ℤ), ?_⟩
  rw [e, Real.log_rpow (norm_pos_iff.2 h0), Padic.norm_eq_zpow_neg_valuation h0, Real.log_zpow]
  push_cast
  ring

theorem exists_addVal (p : ℕ) [Fact p.Prime] {π : PadicAlgCl p} (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1) :
    ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ), ∀ (x : PadicAlgCl p) (r : ℚ),
      v x = (r : WithTop ℚ) ↔ ‖x‖ = Real.exp (-(-Real.log ‖π‖ * r)) := by
  classical
  have hl : Real.log ‖π‖ < 0 := Real.log_neg h0 h1
  have key : ∀ x : PadicAlgCl p, x ≠ 0 → ∃ r : ℚ, Real.log ‖x‖ = Real.log ‖π‖ * r := fun x hx => by
    obtain ⟨a, ha⟩ := exists_rat_log p hx
    obtain ⟨b, hb⟩ := exists_rat_log p (norm_pos_iff.1 h0)
    have b0 : (b : ℝ) ≠ 0 := fun h => hl.ne (by rw [hb, h, zero_mul])
    refine ⟨a / b, ?_⟩
    rw [ha, hb]; push_cast; field_simp
  choose! f hf using key
  have inj : ∀ a b : ℚ, Real.log ‖π‖ * a = Real.log ‖π‖ * b → a = b := fun a b h => by
    exact_mod_cast mul_left_cancel₀ hl.ne h
  have mono : ∀ x y, x ≠ 0 → y ≠ 0 → ‖x‖ ≤ ‖y‖ → f y ≤ f x := fun x y hx hy h => by
    have := Real.log_le_log (norm_pos_iff.2 hx) h
    rw [hf x hx, hf y hy] at this
    exact_mod_cast (mul_le_mul_left_of_neg hl).1 this
  refine ⟨AddValuation.of (fun x => if x = 0 then ⊤ else (f x : WithTop ℚ)) (if_pos rfl) ?_ ?_ ?_, fun x r => ?_⟩
  · rw [if_neg one_ne_zero, inj (f 1) 0 (by rw [← hf 1 one_ne_zero]; simp)]; rfl
  · intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    by_cases hs : x + y = 0
    · simp [hs]
    simp only [if_neg hx, if_neg hy, if_neg hs, min_le_iff, WithTop.coe_le_coe]
    exact (le_max_iff.1 (IsUltrametricDist.norm_add_le_max x y)).imp (mono _ _ hs hx) (mono _ _ hs hy)
  · intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    have hs := mul_ne_zero hx hy
    simp only [if_neg hx, if_neg hy, if_neg hs, ← WithTop.coe_add]
    refine congrArg _ (inj _ _ ?_)
    rw [← hf _ hs, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy), hf x hx, hf y hy]
    push_cast; ring
  · rw [AddValuation.of_apply, neg_mul, neg_neg]
    by_cases hx : x = 0
    · simp [hx, (Real.exp_pos _).ne]
    rw [if_neg hx, WithTop.coe_eq_coe]
    refine ⟨fun h => by rw [← h, ← hf x hx, Real.exp_log (norm_pos_iff.2 hx)], fun h => inj _ _ ?_⟩
    rw [← hf x hx, h, Real.log_exp]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem charZero : CharZero u.V :=
  ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero

theorem isUnit_level (h : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) : IsUnit ((S.r * S.N : ℕ) : u.V) := by
  obtain ⟨b, hb⟩ := S.unit.exists_right_inv
  obtain ⟨c, hc⟩ := (u.norm_le (u.yK (algebraMap o S.R b))).1 (by
    rw [← RingHom.comp_apply, u.fac]; exact h b)
  refine IsUnit.of_mul_eq_one c (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  have := congrArg (fun a => u.yK (algebraMap o S.R a)) hb
  simp only [map_mul, map_natCast, map_one] at this ⊢
  rw [hc]; simpa using this

theorem exists_val : ∃ (ϖ : u.V) (_ : Irreducible ϖ) (Q : u.D.toPre.X → ℤ) (_ : QForm.IsQ u.D.toPre ϖ Q)
    (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (_ : ValOver ϖ (PadicAlgCl p) v) (lam : ℝ), 0 < lam ∧
    (∀ (x : PadicAlgCl p) (r : ℚ), v x = (r : WithTop ℚ) ↔ ‖x‖ = Real.exp (-(lam * r))) ∧
    (∀ (x : PadicAlgCl p) (r : ℚ), (r : WithTop ℚ) ≤ v x ↔ ‖x‖ ≤ Real.exp (-(lam * r))) ∧
    ∀ (l : u.Lab) χ, l.q χ = lam * Q χ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  choose Q hQ using QForm.exists_QVal hϖ u.D
  have h0 := PsiForm.norm_pos_of_irreducible (F := PadicAlgCl p) hϖ
  have h1 := PsiForm.norm_lt_one_of_irreducible u.norm_le hϖ
  have hl := neg_pos.2 (Real.log_neg h0 h1)
  obtain ⟨v, hv⟩ := exists_addVal p h0 h1
  refine ⟨ϖ, hϖ, Q, hQ, v, fun c n hc => (hv _ _).2 ?_, _, hl, hv, fun x r => ?_, fun l χ => ?_⟩
  · rw [PsiForm.norm_of_hasVal u.norm_le hϖ hc]; simp
  · by_cases hx : x = 0
    · simp [hx, (Real.exp_pos _).le]
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hx)
    rw [(hv x s).1 hs.symm, ← hs, WithTop.coe_le_coe, Real.exp_le_exp, neg_le_neg_iff, mul_le_mul_iff_right₀ hl,
      Rat.cast_le]
  · obtain ⟨j, hj⟩ := exists_chart u.D.toPre.P.isLB ((u.D.toPre.c χ).left (IsLocalRing.closedPoint u.V))
    have hj' : ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U j :=
      ((IsLocalRing.closedPoint_mem_iff _).1 hj).ge
    have a := l.q_eq χ (fun _ => j) hj'
    have b := PsiForm.norm_of_hasVal u.norm_le hϖ
      (PsiForm.hasVal_valF u.D.toPre.P.L _ _ (QForm.ptK_eq u.D.toPre χ) (-1) _ (hQ χ) (fun _ => j) hj')
    exact neg_injective (Real.exp_injective (a.symm.trans b))

section
open GlobalTheory.ThetaCompare CommPairing

theorem exists_root_stalk {B : Scheme.{0}} (hG : GlobalFnsSt) (P : PolAV B) {T : Over B} {m : ℕ} (hm : Odd m) {k : ℤ}
    (hk : k = (m : ℤ) ^ 2) {rig : LB.Gen (P.L.pull (eSec P.A))} {x : T ⟶ P.A} {τ}
    (hτ : IsTorsFrame P rig m (x ^ m) τ) {th : LB.Sec (LPow P.A P.L 1 T)} {s₁ t : LB.Sec (LPow P.A P.L k T)}
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![k, -1])}
    {θ : ThetaGrp P.A P.L k T} (hα : α.IsGen)
    (hn : LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (rigT P.A P.L rig T (k - 1)))
    (h₁ : IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) k 1 α th s₁)
    (hθ : SymLift P.A P.L k (m ^ 2) x θ) (h₂ : IsActOf P.A P.L k θ s₁ t) {y : T.left} {J} (hJ : Good P.L y J)
    {c c' : T.left.presheaf.stalk y}
    (hc : sval (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => k) t (ptSecT P.A 1).left y J =
      c * (val (rigT P.A P.L rig T k) (𝟙 _) y J).val)
    (hc' : sval (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => 1) th (ptSecT P.A (x ^ m)).left y J =
      c' * (val (powFrame P.A P.L (x ^ m) τ 1) (𝟙 _) y J).val) :
    c ^ (m ^ 2) = c' ^ (m ^ 2) := by
  subst hk
  have hx : x ^ (m ^ 2) = 1 := by rw [sq, pow_mul, hτ.1]
  have a₁ := frame_pow hG P hm hα hx hθ hJ
  have a₂ := torsFrame_pow hG P hα hτ hJ
  have a₃ := val_corr hJ hn (𝟙 _)
  rw [val_pull hJ, val_rigT _ _ hJ, Category.id_comp] at a₃
  have b₂ := sval_twist h₂ (ptSecT P.A 1).left hJ
  have b₃ := sval_twist h₁ (ptSecT P.A x).left hJ
  have p₂ : val (powFrame P.A P.L (x ^ m) τ 1) (𝟙 _) y J = val τ (𝟙 _) y J :=
    (map_zpow _ _ _).trans (zpow_one _)
  rw [pt_translT, _root_.mul_one, congrArg (ptSecT P.A) hθ.pt_eq, b₃, hc, pt_mulT, hc', p₂, val_rigT _ _ hJ] at b₂
  have e : (tval θ (ptSecT P.A 1).left y J * val α (ptSecT P.A x).left y J * val τ (𝟙 _) y J *
      (val rig T.hom y J ^ ((m : ℤ) ^ 2))⁻¹) ^ (m ^ 2) = 1 := by
    apply Additive.ofMul.injective
    replace a₁ := congrArg Additive.ofMul a₁
    replace a₂ := congrArg Additive.ofMul a₂
    replace a₃ := congrArg Additive.ofMul a₃
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one] at a₁ a₂ a₃ ⊢
    linear_combination (norm := module) a₁ + a₂ + (m ^ 2) • a₃
  have e' : c = (tval θ (ptSecT P.A 1).left y J * val α (ptSecT P.A x).left y J * val τ (𝟙 _) y J *
      (val rig T.hom y J ^ ((m : ℤ) ^ 2))⁻¹).val * c' := by
    rw [(Units.eq_mul_inv_iff_mul_eq _).2 b₂]
    simp only [Units.val_mul, tval]
    ring
  rw [e', mul_pow, ← Units.val_pow_eq_pow_val, e, Units.val_one, _root_.one_mul]

theorem pow_eq_of_thC (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V]
    {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {F : Type} [Field F] [Algebra (FractionRing V) F]
    {rig : LB.Gen (A.L.pull (eSec A.A))} {m : ℕ} (hm : Odd m) {th : SecA A F 1} {x : TFK (R := V) F ⟶ A.A} {t} {c c' : F}
    (H : ThC A rig m th x t c) {e} (he : IsTorsFrame A rig m (x ^ m) e)
    (hc : (∀ z J, Good A.L z J → sA th (ptSecT A.A (x ^ m)).left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c') * (val (powFrame A.A A.L (x ^ m) e ((1 : ℕ) : ℤ)) (𝟙 _) z J).val)) :
    c ^ (m ^ 2) = c' ^ (m ^ 2) := by
  obtain ⟨α, s₁, θ, hα, hn, h₁, hθ, h₂, hv⟩ := H
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := V) F).left) A.isLB z
  have := exists_root_stalk hG A hm (Nat.cast_pow m 2) he hα hn h₁ hθ h₂ hJ (hv z J hJ) (hc z J hJ)
  apply CoefBasic.cstH_inj (R := V) z
  rw [map_pow, map_pow, ← CoefBasic.cst_eq, ← CoefBasic.cst_eq]
  exact this

end

theorem val_eq_of_pow_eq {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {n : ℕ} (hn : n ≠ 0) {c c' : F}
    (h : c ^ n = c' ^ n) : v c = v c' := by
  by_cases h0 : c' = 0
  · subst h0
    rw [zero_pow hn] at h
    rw [pow_eq_zero_iff hn |>.1 h]
  have hc : c ≠ 0 := fun e => h0 (pow_eq_zero_iff hn |>.1 (by rw [← h, e, zero_pow hn]))
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc)
  obtain ⟨r', hr'⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 h0)
  have := congrArg v h
  rw [v.map_pow, v.map_pow, ← hr, ← hr', ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, WithTop.coe_eq_coe] at this
  rw [← hr, ← hr', nsmul_right_injective hn this]


open GlobalTheory.TorusExt in
attribute [local instance] gtGroup in
theorem val_theta : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement →
    AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ rig, NormW U.toUnifPre w₀ rig →
      ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ →
      ∀ (m : ℕ), Odd m → IsUnit (m : V) → ∀ (p : QkPt D.toPre F m) x, QkToAkU U.toUnifPre F m p x →
        (∀ e (c : F), IsTorsFrame A rig m x e → (∀ z J, Good A.L z J → sA th (ptSecT A.A x).left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c) * (val (powFrame A.A A.L x e ((1 : ℕ) : ℤ)) (𝟙 _) z J).val) →
          (∀ q : ℚ, (∀ χ, q ≤ (Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v c) ∧
            (v c = 0 → ∃ z, p.y = m • z)) ∧
        ∀ n, 2 ≤ n → n ∣ m → p.y = 0 → ∃ (p' : QkPt D.toPre F m) (x' : _), p'.y = 0 ∧
          QkToAkU U.toUnifPre F m p' x' ∧ (x' * x⁻¹) ^ n = 1 ∧
          ∀ e (c : F), IsTorsFrame A rig m x' e → (∀ z J, Good A.L z J → sA th (ptSecT A.A x').left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c) * (val (powFrame A.A A.L x' e ((1 : ℕ) : ℤ)) (𝟙 _) z J).val) → v c = 0 := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ rig hN th ϑ hE hP m hm hu p x hx
  have hA : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hB := D.tau_bimult
  have m2 : m ^ 2 ≠ 0 := (pow_pos hm.pos 2).ne'
  obtain ⟨ua₁, ua₂⟩ := ThetaConstVal.main hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ rig hN th ϑ hE hP m hm hu
  have up := GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL V _ hA D A G hG U F m m (m ^ 2) hm.pos hm.pos (sq m)
  obtain ⟨g, hg⟩ := (gt_onto_divisible_kernel hL V _ hA D F).2.1 m hm.pos p.g
  have hg' := (isNsmul_iff_eq _ _ _).1 hg
  let q : QkPt D.toPre F (m ^ 2) := ⟨p.y, g, by
    obtain ⟨a, ha, hb⟩ := p.eq
    exact ⟨a, (isNsmul_iff_eq _ _ _).2 (by rw [(isNsmul_iff_eq _ _ _).1 ha, sq, mul_smul, ← hg']), hb⟩⟩
  obtain ⟨f, f₁, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F (m ^ 2) (pow_pos hm.pos 2)
  obtain ⟨f', f₁', -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F m hm.pos
  have hq : QkToAkU U.toUnifPre F (m ^ 2) q (f q) := (f₁ _ _).2 rfl
  have hqy : p.y = q.y := rfl
  have hqg : GtPtF.IsNsmul m q.g p.g := by
    change GtPtF.IsNsmul m g p.g
    exact hg
  obtain rfl : x = f q ^ m := ((f₁' _ _).1 hx).trans ((f₁' _ _).1 ((up p q _).2 hqy hqg hq)).symm
  refine ⟨fun e c he hval => ?_, fun n hn hnm hy => ?_⟩
  · obtain ⟨⟨t, c₀⟩, hT, -⟩ := GlobalTheory.existsUnique_thetaConst hL V A F rig hN.2.1 m hm th (f q) (hq w₀ hN.1).1
    rw [← val_eq_of_pow_eq v m2 (pow_eq_of_thC hL.1.globalFns hm hT he hval)]
    exact ua₁ q _ t c₀ hq hT
  · obtain ⟨q', x', t, c₀, hy', hq', hpow, hT, h0⟩ := ua₂ n hn hnm q _ hy hq
    let p' : QkPt D.toPre F m := ⟨q'.y, m • q'.g, by
      obtain ⟨a, ha, hb⟩ := q'.eq
      exact ⟨a, (isNsmul_iff_eq _ _ _).2 (by rw [(isNsmul_iff_eq _ _ _).1 ha, ← mul_smul, ← sq]), hb⟩⟩
    refine ⟨p', x' ^ m, hy', (up p' q' x').2 rfl ((isNsmul_iff_eq _ _ _).2 rfl) hq', hpow, fun e c he hval => ?_⟩
    rw [← val_eq_of_pow_eq v m2 (pow_eq_of_thC hL.1.globalFns hm hT he hval), h0]

end GlobalTheory.ZH.TestVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionPointsGroupPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionPointsGroupPairing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
noncomputable section
namespace GlobalTheory.TestFibre

theorem ptsOver_group_pairing : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), (∃ x, PtsOver u x) ∧ ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → (∀ a b, x (a + b) = x a * x b) ∧ (∀ a, x a ^ (S.r * S.N) = 1) ∧ (∀ z, z ^ (S.r * S.N) = 1 → ∃! a, x a = z) ∧ ∀ a b (c : (PadicAlgCl p)ˣ), (c : PadicAlgCl p) = y₀ (algebraMap o S.R S.ζ) ^ (S.r * S.N * (eStd S.g _ a b).val) → WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (x a) (x b) (unitOn c) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u
  obtain ⟨x₀, h₀, hadd, hinj, hsurj⟩ := utest_torsion_points o Ω S ρ p y₀ u
  refine ⟨⟨x₀, h₀⟩, fun x hx => ?_⟩
  obtain rfl : x = x₀ := funext fun a => Over.OverMorphism.ext
    (u.cart.1.hom_ext ((hx a).trans (h₀ a).symm) ((Over.w _).trans (Over.w _).symm))
  refine ⟨hadd, fun a => GlobalTheory.FrameMove.pow_eq_one_of (T := baseOver (Sp S.R)) u.cart (hx a) (ρ.fr_tors a).1,
    fun z hz => ?_, fun a b c hc => weilIs_uTest hL o Ω S ρ p y₀ u x hx a b c ?_⟩
  · obtain ⟨a, ha⟩ := hsurj z hz
    exact ⟨a, ha.symm, fun b hb => hinj (hb.trans ha)⟩
  · rw [hc, map_pow, map_pow]

end GlobalTheory.TestFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionPointsGroupPairingStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedModel_torsionPoints_group_pairing : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), (∃ x, PtsOver u x) ∧ ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → (∀ a b, x (a + b) = x a * x b) ∧ (∀ a, x a ^ (S.r * S.N) = 1) ∧ (∀ z, z ^ (S.r * S.N) = 1 → ∃! a, x a = z) ∧ ∀ a b (c : (PadicAlgCl p)ˣ), (c : PadicAlgCl p) = y₀ (algebraMap o S.R S.ζ) ^ (S.r * S.N * (eStd S.g _ a b).val) → WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (x a) (x b) (unitOn c) := by
  first | exact @GlobalTheory.TestFibre.ptsOver_group_pairing | exact GlobalTheory.TestFibre.ptsOver_group_pairing | (intros; apply GlobalTheory.TestFibre.ptsOver_group_pairing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFibreSectionLinearCombIffExpansionSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFibreSectionLinearCombIffExpansionSum
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory.TestFibre

theorem isComb_iff_expandsF_sum : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (J : Type) [Fintype J] (s : J → SecA A F k) (Φ : J → Fam D.toPre F k) (b : J → F) (t : SecA A F k), (∀ i, U.ExpandsF F k w₀ (s i) (Φ i)) → (IsComb A s b t ↔ U.ExpandsF F k w₀ t (∑ i, b i • Φ i)) := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ k hk w₀ hw J _ s Φ b t hs
  obtain ⟨hb, hl⟩ := GlobalTheory.UT.expBijF_and_expandsF_lin hL R I hI D A G hG U
  obtain ⟨h₁, h₂⟩ := hb F k hk w₀ hw
  have h0 : U.ExpandsF F k w₀ (SecOps.secZero : SecA A F k) (0 : Fam D.toPre F k) := by
    obtain ⟨σ, hσ⟩ := (h₁ (SecOps.secZero : SecA A F k)).exists
    have h := hl F k w₀ SecOps.secZero SecOps.secZero SecOps.secZero σ σ (-1) hσ hσ (fun j => ((add_zero _).trans (mul_zero _)).symm)
    rwa [neg_one_smul, neg_add_cancel] at h
  have key : ∀ S : Finset J, ∃ u : SecA A F k,
      (∀ j, u.f j = ∑ l ∈ S, liftFun A.A _ (cF R (b l)) * (s l).f j) ∧
        U.ExpandsF F k w₀ u (∑ i ∈ S, b i • Φ i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨SecOps.secZero, fun j => by rw [Finset.sum_empty]; rfl, by rw [Finset.sum_empty]; exact h0⟩
    | insert a S ha ih =>
      obtain ⟨u, hu, eu⟩ := ih
      refine ⟨SecOps.secAdd (SecOps.secScale ((fst (TFK (R := R) F) A.A).left.appTop.hom (cF R (b a))) (s a)) u,
        fun j => ?_, ?_⟩
      · rw [Finset.sum_insert ha, ← hu j]; rfl
      · rw [Finset.sum_insert ha]
        exact hl F k w₀ (s a) u _ (Φ a) _ (b a) (hs a) eu (fun j => rfl)
  obtain ⟨u, hu, eu⟩ := key Finset.univ
  constructor
  · intro h
    obtain rfl : t = u := SecOps.sec_ext fun j => (h j).trans (hu j).symm
    exact eu
  · intro h
    obtain rfl : t = u := (h₂ _).unique h eu
    exact hu

end GlobalTheory.TestFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFibreSectionLinearCombIffExpansionSumStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFibreSectionLinearComb_iff_expansion_sum : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (J : Type) [Fintype J] (s : J → SecA A F k) (Φ : J → Fam D.toPre F k) (b : J → F) (t : SecA A F k), (∀ i, U.ExpandsF F k w₀ (s i) (Φ i)) → (IsComb A s b t ↔ U.ExpandsF F k w₀ t (∑ i, b i • Φ i)) := by
  first | exact @GlobalTheory.TestFibre.isComb_iff_expandsF_sum | exact GlobalTheory.TestFibre.isComb_iff_expandsF_sum | (intros; apply GlobalTheory.TestFibre.isComb_iff_expandsF_sum <;> assumption)
end
end
