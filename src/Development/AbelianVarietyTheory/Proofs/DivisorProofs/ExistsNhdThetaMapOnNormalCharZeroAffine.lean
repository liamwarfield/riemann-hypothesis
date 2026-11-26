module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsMemNormalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPeriodValueFractionFiel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.SymAtOfThList
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.Ex.OneGen GlobalTheory.ThetaPtMove
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.Model

theorem polFib_self {R : Type} [CommRing R] (P : PolAV (Sp R)) : PolFib P.A P.L P.g (𝟙 _) := by
  exact ⟨P, 𝟙 _, rfl, @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl P.A) (inferInstanceAs (IsMonHom (𝟙 P.A))),
    LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (GlobalTheory.PolBaseChange.lbIso_refl P.isLB)⟩

end GlobalTheory.UMin.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMapAffineNormalBaseUniversalGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantLevelSquareNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantLevelSquareNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThNe

variable {S : Scheme.{0}}

theorem ptSecT_translT_mulT {A : Over S} [GrpObj A] (T : Over S) (y : T ⟶ A) (m : ℕ) :
    ptSecT A (1 : T ⟶ A) ≫ translT A y ≫ mulT A T m = ptSecT A (y ^ m) := by
  have e : ptSecT A (1 : T ⟶ A) ≫ translT A y = ptSecT A y := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [ptSecT, translT]
    · simp only [ptSecT, translT, translPt, Category.assoc, lift_snd, Hom.mul_def, comp_lift_assoc, lift_fst_assoc,
        Category.id_comp]
      rw [← Hom.mul_def, _root_.mul_one]
  rw [← Category.assoc, e]
  apply CartesianMonoidalCategory.hom_ext
  · simp [ptSecT, mulT]
  · simp only [ptSecT, mulT, lift_snd, Category.assoc]
    rw [MonObj.comp_pow, lift_snd]

theorem ne_zero_of_thG {K : Type} [Field K] {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    {ρ : LB.Gen (L.pull (eSec A))} {m : ℕ} {t : Sp K ⟶ S} {th : LB.Sec (LPow A L ((1 : ℕ) : ℤ) (Over.mk t))}
    {y : Over.mk t ⟶ A} {c : K} (H : ThG A L ρ m th y (fn c))
    (hu : ∀ z J, Good L z J → IsUnit (VVRank.sv A th (ptSecT A (y ^ m)).left z J)) : c ≠ 0 := by
  intro hc
  obtain ⟨-, t', α, s₁, θ, -, -, hs₁, hθ, ht, hc'⟩ := H
  obtain ⟨z⟩ : Nonempty (Sp K) := inferInstance
  obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun k => k.elim)
  have q := hc' z J hJ
  have a1 := VVRank.sv_of_isTwistPull A ht (ptSecT A 1).left z hJ
  have a2 := VVRank.sv_of_isTwistPull A hs₁ ((ptSecT A 1).left ≫ (translT A θ.pt).left) z hJ
  have e : ((ptSecT A (1 : Over.mk t ⟶ A)).left ≫ (translT A θ.pt).left) ≫ (mulT A (Over.mk t) m).left =
      (ptSecT A (y ^ m)).left := by
    rw [hθ.pt_eq, ← Over.comp_left, ← Over.comp_left, Category.assoc, ptSecT_translT_mulT]
  rw [e] at a2
  rw [a2] at a1
  have f0 : (fn (0 : K) : Γ((Over.mk t).left, ⊤)) = 0 := map_zero _
  rw [hc, f0, gs_eq _ z ⊤ trivial, map_zero, map_zero, zero_mul] at q
  have q2 := a1.symm.trans q
  rw [Units.mul_right_eq_zero, Units.mul_right_eq_zero] at q2
  exact (hu z J hJ).ne_zero q2

theorem exists_pow_eq_of_card {G : Type} [CommGroup G] {m g : ℕ} (hm : 0 < m)
    (h1 : Nat.card {x : G // x ^ m = 1} = m ^ (2 * g)) (h2 : Nat.card {x : G // x ^ (m ^ 2) = 1} = (m ^ 2) ^ (2 * g))
    (x : G) (hx : x ^ m = 1) : ∃ y : G, y ^ (m ^ 2) = 1 ∧ y ^ m = x := by
  let H2 := (powMonoidHom (m ^ 2) : G →* G).ker
  let H1 := (powMonoidHom m : G →* G).ker
  let f : H2 →* G := (powMonoidHom m).comp H2.subtype
  have cH2 : Nat.card H2 = (m ^ 2) ^ (2 * g) := h2 ▸ Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H2])
  have cH1 : Nat.card H1 = m ^ (2 * g) := h1 ▸ Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H1])
  have cK : Nat.card f.ker = m ^ (2 * g) := by
    rw [← h1]
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1.1, MonoidHom.mem_ker.1 y.2⟩
        invFun := fun x => ⟨⟨x.1, by simp [H2, pow_two, pow_mul, x.2]⟩, MonoidHom.mem_ker.2 x.2⟩
        left_inv := fun y => rfl
        right_inv := fun x => rfl }
  have hpos : 0 < m ^ (2 * g) := pow_pos hm _
  haveI : Finite H2 := Nat.finite_of_card_ne_zero (by rw [cH2]; positivity)
  haveI : Finite H1 := Nat.finite_of_card_ne_zero (by rw [cH1]; positivity)
  have cR : Nat.card f.range = m ^ (2 * g) := by
    have e := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, cK, cH2, show (m ^ 2) ^ (2 * g) = m ^ (2 * g) * m ^ (2 * g) by ring] at e
    exact Nat.eq_of_mul_eq_mul_left hpos e
  have hle : f.range ≤ H1 := by
    rintro _ ⟨y, rfl⟩
    have := y.2
    simp only [H2, MonoidHom.mem_ker, powMonoidHom_apply] at this
    simp [H1, f, ← pow_mul, ← pow_two, this]
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [cH1, cR])
  have hx1 : x ∈ H1 := by simpa [H1] using hx
  rw [← heq] at hx1
  obtain ⟨y, hy⟩ := hx1
  exact ⟨y.1, MonoidHom.mem_ker.1 y.2, hy⟩

end GlobalTheory.UMin.ThNe

namespace GlobalTheory.UMin.ThNe

theorem spMap_id_self (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

theorem th_ne_zero : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left)
    (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S)
    (c : Fin N → K), Odd m → 3 ≤ m → (m : K) ≠ 0 → PolFib G L g x → HasTh G L ρ m x c → ∃ a, c a ≠ 0 := by
  intro S G _ _ L ρ hL hρ g m N K _ x c hm hm3 hmK hpol H
  obtain ⟨hLaws, hLaws2⟩ := abelianSchemeLaws_all
  obtain ⟨P, α, -, hα, hPL⟩ := hpol
  haveI := P.isAb.comm
  obtain ⟨ρ', hρ'⟩ := P.rigid
  have H' : HasTh P.A P.L ρ' m (𝟙 (Sp K)) c := by
    rw [hasTh_iff] at H ⊢
    exact (ThMove.hasTh₂_move S G L ρ hL hρ (Sp K) P.A P.L ρ' x α P.isLB hρ' hα hPL m m N N K (𝟙 _) c c).2
      (by rwa [Category.id_comp])
  obtain ⟨θ, pt, hgθ, hl⟩ := H'
  let i : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  obtain ⟨pt', -, hl'⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension (Sp K) P.A P.L ρ' P.isLB hρ' m N K (AlgebraicClosure K) i (𝟙 _) θ pt c hl
  have hg' : IsGenSec P.A P.L _ (SecAt.pull P.A P.L θ i) :=
    (gen_of_polFib (Sp K) P.A P.L P.isLB P.g K (𝟙 _) (Model.polFib_self P)).2 θ hgθ (AlgebraicClosure K) i
  have hne := ThetaCoset.ne_zero_of_isGenSec hLaws2.secBaseChangeAny P (spMap i ≫ 𝟙 (Sp K)) hg'
  have hmKb : (m : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast i]; exact (map_ne_zero i).2 hmK
  obtain ⟨z, hz, hu⟩ := UT.ExactTerm.exists_good_point hLaws.goodPt hLaws.polBaseChange P (spMap i ≫ 𝟙 (Sp K))
    (n := m) (by omega) hmKb _ hne 1
  have c1 := (hLaws.mulN (Sp K) P m (by omega)).2.2.2.2 (AlgebraicClosure K) (spMap i ≫ 𝟙 (Sp K)) hmKb
  have c2 := (hLaws.mulN (Sp K) P (m ^ 2) (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (by omega)))).2.2.2.2
    (AlgebraicClosure K) (spMap i ≫ 𝟙 (Sp K)) (by push_cast; exact pow_ne_zero _ hmKb)
  obtain ⟨y, hy2, hym⟩ := exists_pow_eq_of_card (by omega) c1 c2 (1 * z) (by rw [_root_.one_mul, hz])
  let π : Over.mk (spMap (RingHom.id (AlgebraicClosure K)) ≫ spMap i ≫ 𝟙 (Sp K)) ⟶ Over.mk (spMap i ≫ 𝟙 (Sp K)) :=
    Over.homMk (spMap (RingHom.id (AlgebraicClosure K))) rfl
  obtain ⟨a, ha⟩ := hl'.2.2 (AlgebraicClosure K) (RingHom.id _) (π ≫ y)
    (by rw [← MonObj.comp_pow, hy2, MonObj.comp_one])
  have hya : y = pt' a := by
    apply Over.OverMorphism.ext
    have := ha
    simp only [π, Over.comp_left, Over.homMk_left] at this
    rwa [spMap_id_self, Category.id_comp, Category.id_comp] at this
  refine ⟨a, fun h0 => ?_⟩
  have hth := hl'.2.1 a
  rw [← hya] at hth
  refine ne_zero_of_thG P.isLB hth (fun p J hJ => ?_) (by show i (c a) = 0; rw [h0, map_zero])
  rw [hym]
  exact hu p J hJ

end GlobalTheory.UMin.ThNe
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantLevelSquareNeZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaConstant_levelSquare_ne_zero : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S) (c : Fin N → K), Odd m → 3 ≤ m → (m : K) ≠ 0 → PolFib G L g x → HasTh G L ρ m x c → ∃ a, c a ≠ 0 := by
  first | exact @GlobalTheory.UMin.ThNe.th_ne_zero | exact GlobalTheory.UMin.ThNe.th_ne_zero | (intros; apply GlobalTheory.UMin.ThNe.th_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMapAffineNormalBaseUniversalGenerator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.MapAff

theorem theta_map_aff : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o R : Type) [CommRing o] [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (β : o →+* R) (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → 3 ≤ m → IsUnit (m : R) → n + 1 = m ^ (4 * g) → PolFib G L g x → (∀ (K : Type) [Field K] (i : R →+* K), IsGenSec G L _ (SecAt.pull G L θ i)) → ∃ f : Sp R ⟶ PSpace o n, f ≫ PSpace.str o n = spMap β ∧ ThMap G L ρ m x f := by
  intro S G _ _ L ρ hL hρ g m n o R _ _ _ _ _ _ β x θ hm hm3 hmu hn hpol hgen
  obtain ⟨e, he⟩ := GlobalTheory.T.thetaSymmetricFunctions_mem_normalDomain S G L ρ hL hρ g m (n + 1) R x θ hm hmu hn hpol
  have hpolK : ∀ (K : Type) [Field K] (i : R →+* K), PolFib G L g (spMap i ≫ x) := fun K _ i =>
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback S S G L G L (𝟙 S) (𝟙 G.left) hL hL (GlobalTheory.SiegLower.isGrpPullback_id G)
      (GlobalTheory.SiegLower.lbIso_pull_id hL) g R x).2 K i hpol
  have hspan : Ideal.span (Set.range e) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    letI := Ideal.Quotient.field M
    let i : R →+* AlgebraicClosure (R ⧸ M) := (algebraMap (R ⧸ M) (AlgebraicClosure (R ⧸ M))).comp (Ideal.Quotient.mk M)
    have hmK : ((m : ℕ) : AlgebraicClosure (R ⧸ M)) ≠ 0 := by
      have := hmu.map i
      rw [map_natCast] at this
      exact this.ne_zero
    have hpK := hpolK _ i
    obtain ⟨pt, c, hl⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed S G L ρ hL hρ g m (n + 1) _ (spMap i ≫ x) (SecAt.pull G L θ i) hm hmK hn hpK
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_thetaConstant_levelSquare_ne_zero S G L ρ hL hρ g m (n + 1) _ (spMap i ≫ x) c hm hm3 hmK hpK ⟨_, pt, hgen _ i, hl⟩
    obtain ⟨j, hj⟩ := GlobalTheory.UMin.symTup_basic.2.2.2 _ (n + 1) c ⟨a, ha⟩
    apply hj
    rw [← he _ i pt c hl j]
    have hM' : e j ∈ M := hle (Ideal.subset_span ⟨j, rfl⟩)
    simp [i, Ideal.Quotient.eq_zero_iff_mem.2 hM']
  have hstr : GlobalTheory.ProjSpace.pt β e hspan ≫ PSpace.str o n = spMap β := by
    rw [GlobalTheory.ProjSpace.pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C β e r
  have hf : PCrd (GlobalTheory.ProjSpace.pt β e hspan) e := (GlobalTheory.UMin.CrdUniq.pCrd_iff _ β hstr e).2 ⟨hspan, rfl⟩
  refine ⟨GlobalTheory.ProjSpace.pt β e hspan, hstr, ?_⟩
  intro K _ x' c ⟨θ', pt, hθ', hl⟩
  obtain ⟨i, rfl⟩ := GlobalTheory.UMin.CrdUniq.exists_spMap' x'
  obtain ⟨r, hr⟩ := hθ' (SecAt.pull G L θ i)
  have hsm : SecM.ofSec G (SecAt.pull G L θ i) = r • SecM.ofSec G θ' := Subtype.ext (funext hr)
  set a : K := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r with ha
  have hra : GlobalTheory.ZH.fn a = r := by
    simp [GlobalTheory.ZH.fn, a]
  have hl0 : ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt (fun b => a * c b) := by
    refine ⟨hl.1, fun b => ?_, hl.2.2⟩
    have h1 := GlobalTheory.Ex.OneGen.ThG.smul hL hsm (hl.2.1 b)
    convert h1 using 1
    rw [← hra]
    exact map_mul _ _ _
  have h2 : PCrd (spMap i ≫ GlobalTheory.ProjSpace.pt β e hspan) (fun j => a ^ (n + 1).factorial * symTup c j) := by
    have := GlobalTheory.T.projectiveHomogeneousCoords_basic_properties.1 o R K n _ e i hf
    convert this using 2 with j
    rw [he K i pt _ hl0 j, GlobalTheory.UMin.symTup_basic.1]
  have ha0 : a ≠ 0 := by
    rintro h0
    obtain ⟨j, hj⟩ := (GlobalTheory.T.projectiveHomogeneousCoords_basic_properties.2.2 o K n _).2 _ h2
    apply hj
    simp [h0, Nat.factorial_ne_zero]
  have h3 := GlobalTheory.T.projectiveHomogeneousCoords_basic_properties.2.1 o K n _ _ ((a ^ (n + 1).factorial)⁻¹) (isUnit_iff_ne_zero.2 (inv_ne_zero (pow_ne_zero _ ha0))) h2
  convert h3 using 1
  funext j
  rw [inv_mul_cancel_left₀ (pow_ne_zero _ ha0)]

end GlobalTheory.UMin.MapAff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMapAffineNormalBaseUniversalGeneratorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaMap_affineNormalBase_universalGenerator : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o R : Type) [CommRing o] [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (β : o →+* R) (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → 3 ≤ m → IsUnit (m : R) → n + 1 = m ^ (4 * g) → PolFib G L g x → (∀ (K : Type) [Field K] (i : R →+* K), IsGenSec G L _ (SecAt.pull G L θ i)) → ∃ f : Sp R ⟶ PSpace o n, f ≫ PSpace.str o n = spMap β ∧ ThMap G L ρ m x f := by
  first | exact @GlobalTheory.UMin.MapAff.theta_map_aff | exact GlobalTheory.UMin.MapAff.theta_map_aff | (intros; apply GlobalTheory.UMin.MapAff.theta_map_aff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenGeneratingSectionAllFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenGeneratingSectionAllFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem exists_basicOpen_genSec_fibres : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB →
    ∀ (g : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S), PolFib G L g x →
    ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧
      ∃ θ : SecAt G L (spMap (algebraMap R (Localization.Away r)) ≫ x),
        ∀ (K : Type) [Field K] (i : Localization.Away r →+* K), IsGenSec G L _ (SecAt.pull G L θ i) := by
  intro S G _ L hL g R _ _ x hx p
  obtain ⟨P, α, -, hp, w, hw⟩ := hx
  have hS : SecBaseChangeAnySt := GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny
  obtain ⟨V, hpV, hV⟩ := GlobalTheory.EmbLocal.exists_isGenSec_near hS P p
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrV⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := p) (u := ((V : Set (Sp R)) : Set (PrimeSpectrum R))) hpV V.isOpen
  let j := algebraMap R (Localization.Away r)
  have hrange : Set.range (spMap j) ⊆ (V : Set (Sp R)) := by
    intro y hy
    apply hrV
    obtain ⟨z, rfl⟩ := hy
    have hz : PrimeSpectrum.comap j z ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact ⟨z, rfl⟩
    exact hz
  obtain ⟨th, hth⟩ := hV (Localization.Away r) (spMap j) hrange
  have hτ : (𝟙 (Sp (Localization.Away r)) : (Over.mk (spMap j)).left ⟶ (Over.mk (spMap j ≫ x)).left) ≫
      (Over.mk (spMap j ≫ x)).hom = (Over.mk (spMap j)).hom ≫ x := Category.id_comp _
  obtain ⟨θ, hθ⟩ := GlobalTheory.ThetaPtMove.exists_secRel_up hp (T := Over.mk (spMap j)) (T₀ := Over.mk (spMap j ≫ x))
    (𝟙 _) hτ hw hL P.isLB (a := ((1 : ℕ) : ℤ)) th
  refine ⟨r, hpr, θ, fun K _ i => ?_⟩
  have hτ' : (𝟙 (Sp K) : (Over.mk (spMap i ≫ spMap j)).left ⟶ (Over.mk (spMap i ≫ spMap j ≫ x)).left) ≫
      (Over.mk (spMap i ≫ spMap j ≫ x)).hom = (Over.mk (spMap i ≫ spMap j)).hom ≫ x := by
    simp [Category.assoc]
  let ξ : Over.mk (spMap i ≫ spMap j) ⟶ Over.mk (spMap j) := Over.homMk (spMap i) rfl
  let ξ₀ : Over.mk (spMap i ≫ spMap j ≫ x) ⟶ Over.mk (spMap j ≫ x) := Over.homMk (spMap i) rfl
  have hξ : (𝟙 (Sp K) : (Over.mk (spMap i ≫ spMap j)).left ⟶ (Over.mk (spMap i ≫ spMap j ≫ x)).left) ≫ ξ₀.left =
      ξ.left ≫ (𝟙 (Sp (Localization.Away r)) : (Over.mk (spMap j)).left ⟶ (Over.mk (spMap j ≫ x)).left) :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  have hrel : GlobalTheory.ThetaPtMove.SecRel hp _ hτ' w (VVRank.pullS P.A ((1 : ℕ) : ℤ) ξ th)
      (VVRank.pullS G ((1 : ℕ) : ℤ) ξ₀ θ) :=
    GlobalTheory.Ex.OneGen.SecRel.pullS hp _ hτ hθ (T' := Over.mk (spMap i ≫ spMap j))
      (T₀' := Over.mk (spMap i ≫ spMap j ≫ x)) _ hτ' ξ ξ₀ hξ
  have : IsAffine (Over.mk (spMap j)).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap i ≫ spMap j)).left := inferInstanceAs (IsAffine (Spec _))
  have hg : IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 ξ th) :=
    GlobalTheory.EmbPull.isGenSec_pullS P hS ξ hth
  have hg' : IsGenSec P.A P.L ((1 : ℕ) : ℤ) (VVRank.pullS P.A ((1 : ℕ) : ℤ) ξ th) := hg
  have : IsIso (C := Scheme.{0}) (X := (Over.mk (spMap i ≫ spMap j)).left)
      (Y := (Over.mk (spMap i ≫ spMap j ≫ x)).left) (𝟙 (Sp K)) := IsIso.id _
  have h2 : IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G ((1 : ℕ) : ℤ) ξ₀ θ) :=
    GlobalTheory.ThetaPtUp.isGenSec_up hp _ hτ' hw hL P.isLB hrel hg'
  exact h2

end GlobalTheory.UMin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenGeneratingSectionAllFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_generating_section_all_fibres : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (g : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S), PolFib G L g x → ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧ ∃ θ : SecAt G L (spMap (algebraMap R (Localization.Away r)) ≫ x), ∀ (K : Type) [Field K] (i : Localization.Away r →+* K), IsGenSec G L _ (SecAt.pull G L θ i) := by
  first | exact @GlobalTheory.UMin.exists_basicOpen_genSec_fibres | exact GlobalTheory.UMin.exists_basicOpen_genSec_fibres | (intros; apply GlobalTheory.UMin.exists_basicOpen_genSec_fibres <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdThetaMapOnNormalCharZeroAffine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem exists_nbhd_thetaMap : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen →
    ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (q : X ⟶ S), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * g) →
    (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), PolFib G L g (x ≫ q)) →
    ∀ (U : X.affineOpens), IsDomain Γ(X, U) → IsNoetherianRing Γ(X, U) → IsIntegrallyClosed Γ(X, U) → CharZero Γ(X, U) →
    ∀ x ∈ (U : X.Opens), ∃ (W : X.Opens) (h : W.toScheme ⟶ PSpace o n), x ∈ W ∧ h ≫ PSpace.str o n = W.ι ≫ s ∧ ThMap G L ρ m (W.ι ≫ q) h := by
  intro S G _ _ L ρ hL hρ g m n o _ X s q hmo hm3 hu hn hP U hD hN hI hC x hx
  let R : Type := Γ(X, U)
  have hU : IsAffineOpen (U : X.Opens) := U.2

  let β : o →+* R := (Spec.preimage (hU.fromSpec ≫ s)).hom
  have hβ : spMap β = hU.fromSpec ≫ s := Spec.map_preimage _
  let p : PrimeSpectrum R := hU.primeIdealOf ⟨x, hx⟩
  obtain ⟨r, hr, θ, hθ⟩ := GlobalTheory.T.exists_basicOpen_generating_section_all_fibres S G L hL g R (hU.fromSpec ≫ q) (hP R hU.fromSpec) p
  let Rr := Localization.Away r
  have hr0 : r ≠ 0 := fun h => hr (h ▸ p.asIdeal.zero_mem)
  have hle : Submonoid.powers r ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hr0
  haveI : IsDomain Rr := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing Rr := IsLocalization.isNoetherianRing (Submonoid.powers r) Rr hN
  haveI : IsIntegrallyClosed Rr := isIntegrallyClosed_of_isLocalization Rr _ hle
  have hinj : Function.Injective (algebraMap R Rr) := IsLocalization.injective Rr hle
  haveI : CharZero Rr := charZero_of_injective_algebraMap hinj
  let β' : o →+* Rr := (algebraMap R Rr).comp β
  have hu' : IsUnit (m : Rr) := by
    have := hu.map β'
    simpa using this
  have hP' : PolFib G L g (spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q) := by
    have := hP Rr (spMap (algebraMap R Rr) ≫ hU.fromSpec)
    simpa [Category.assoc] using this
  obtain ⟨f, hf, hT⟩ := GlobalTheory.T.exists_thetaMap_affineNormalBase_universalGenerator S G L ρ hL hρ g m n o Rr β' (spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q) θ
    hmo hm3 hu' hn hP' hθ

  let Wo : X.Opens := X.basicOpen r
  have hW : IsAffineOpen Wo := hU.basicOpen r
  have hxW : x ∈ Wo := by
    have h1 : hU.fromSpec p ∈ X.basicOpen r := by
      show p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r
      rw [hU.fromSpec_preimage_basicOpen]; exact hr
    rwa [hU.fromSpec_primeIdealOf] at h1
  have hle' : Wo ≤ (U : X.Opens) := X.basicOpen_le r
  let res : R →+* Γ(X, Wo) := (X.presheaf.map (homOfLE hle').op).hom
  have hres : IsUnit (res r) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace r
  let lft : Rr →+* Γ(X, Wo) := IsLocalization.Away.lift r hres
  have hlft : lft.comp (algebraMap R Rr) = res := IsLocalization.Away.lift_comp r hres
  let e : Wo.toScheme ⟶ Sp Rr := hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom lft)
  have he : e ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec = Wo.ι := by
    have : Spec.map (CommRingCat.ofHom lft) ≫ spMap (algebraMap R Rr) =
        Spec.map (X.presheaf.map (homOfLE hle').op) := by
      rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hlft]
      rfl
    simp only [e, Category.assoc]
    rw [reassoc_of% this, hU.map_fromSpec hW, hW.isoSpec_hom_fromSpec]
  refine ⟨Wo, e ≫ f, hxW, ?_, ?_⟩
  · rw [Category.assoc, hf, show spMap β' = spMap (algebraMap R Rr) ≫ spMap β from by
      rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl, hβ, ← he]
    simp only [Category.assoc]
  · intro K _ x' c hc
    have hc' : HasTh G L ρ m ((x' ≫ e) ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q) c := by
      have : (x' ≫ e) ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q = x' ≫ Wo.ι ≫ q := by
        rw [← he]; simp only [Category.assoc]
      rw [this]; exact hc
    have := hT K (x' ≫ e) c hc'
    simpa [Category.assoc] using this

end GlobalTheory.UMin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdThetaMapOnNormalCharZeroAffineStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhd_thetaMap_on_normal_charZero_affine : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen →
    ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (q : X ⟶ S), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * g) →
    (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), PolFib G L g (x ≫ q)) →
    ∀ (U : X.affineOpens), IsDomain Γ(X, U) → IsNoetherianRing Γ(X, U) → IsIntegrallyClosed Γ(X, U) → CharZero Γ(X, U) →
    ∀ x ∈ (U : X.Opens), ∃ (W : X.Opens) (h : W.toScheme ⟶ PSpace o n), x ∈ W ∧ h ≫ PSpace.str o n = W.ι ≫ s ∧ ThMap G L ρ m (W.ι ≫ q) h := by
  first | exact @GlobalTheory.UMin.exists_nbhd_thetaMap | exact GlobalTheory.UMin.exists_nbhd_thetaMap | (intros; apply GlobalTheory.UMin.exists_nbhd_thetaMap <;> assumption)
end
