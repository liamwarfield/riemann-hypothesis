module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExist
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormTorsionSumShortestVectorEq
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeightZeroSectionUnitIntegralTorsionPoint
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTriple

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem hasTests_of_real : GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.HasTests ∧ ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀), l.Match τ ∧ ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)) := by
  intro hS hU hL hL2 hT o Ω _ _ _ _ S ρ
  have key : ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)),
      (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) →
      ∃ (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀), l.Match τ ∧
        ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)) := by
    intro p _ y₀ Fs hy
    obtain ⟨u, hu⟩ := GlobalTheory.T.exists_uniformised_model' hS hU hL.polBaseChange o Ω S ρ p y₀ Fs
    obtain ⟨l⟩ := GlobalTheory.T.uniformisedModel_torsionLabels_exist hL hL2 hT o Ω S ρ p y₀ u hy
    obtain ⟨τ, hτ⟩ := exists_test_match o Ω S ρ p y₀ u l
      (GlobalTheory.T.thetaConstant_bounded_by_shortestVector hL hL2 hT o Ω S ρ p y₀ u l hy)
      (GlobalTheory.T.unitThetaConstants_generate_integralTorsion hL hL2 hT o Ω S ρ p y₀ u l hy)
      (GlobalTheory.T.weightSpace_values_integralTorsion_bound_shortestVector hL hL2 hT o Ω S ρ p y₀ u l hy)
      (GlobalTheory.T.exists_norm_torsionSum_shortestVector_eq hL hL2 hT o Ω S ρ p y₀ u l hy)
      (GlobalTheory.T.exists_weightZeroSection_unit_integralTorsionPoint hL hL2 hT o Ω S ρ p y₀ u l hy)
    exact ⟨u, l, τ, hτ, hu⟩
  refine ⟨?_, key⟩
  intro p _ y hy
  obtain ⟨_, _, τ, _⟩ := key p y ∅ hy
  exact ⟨τ⟩

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSystem_hasTests_of_real_point : GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.HasTests ∧ ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀), l.Match τ ∧ ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)) := by
  first | exact @GlobalTheory.ZH.hasTests_of_real | exact GlobalTheory.ZH.hasTests_of_real | (intros; apply GlobalTheory.ZH.hasTests_of_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionIsometryUniformisedModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionIsometryUniformisedModel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelData.ModelTate

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_level_down {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) (n m : ℕ) (p : QkPt D F (n * m)) :
    ∃ q : QkPt D F n, q.y = p.y ∧ GtPtF.IsNsmul m p.g q.g :=
  ⟨TorusExt.qkMk hB p.y (m • p.g) (by rw [← mul_nsmul', TorusExt.qk_nsmul hB p]), rfl,
    (TorusExt.isNsmul_iff_eq _ _ _).2 rfl⟩

theorem weilIs_of_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hp : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f)
    (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (c : Γ(T.left, ⊤)ˣ) (ex : x₀.left = x.left ≫ φ)
    (ey : y₀.left = y.left ≫ φ) (h : WeilIs G' L' k x y c) : WeilIs G L k x₀ y₀ c := by
  subst hg
  exact (weilIs_grpPullback_of_comm' _ _ _ _ _ _ _ _ hL hL' hp hw T k x y x₀ y₀ c ex ey).1 h

theorem exists_tateIsoQ_of_model : GlobalTheory.UT.LL → BrGtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (C : Type) [NormedField C] (o : Full D C) (M : Mdl o) (N' : NumD C) (_ : NumOf M.P.D.toPre C N'), ∃ I : TateIsoQ D M.P.D.toPre M.P.oD C, I.ζ = o.I.ζ ∧ ∀ k, 0 < k → ∀ x p' (z : TFK (R := M.W) C ⟶ M.P.A.A), QkPt.Equiv _ C (I.ev k x) p' → z.left = (o.I.ev k x).left ≫ M.φ → M.P.ToA C k p' z := by
  intro hL _ E _ _ _ H D C _ o M _ _
  letI := H.starRing
  have := o.closed
  have := o.P.isAb.comm
  have hB := M.P.D.tau_bimult
  obtain ⟨hA, h0⟩ := M.admissible_base_of_complete_dvr
  obtain ⟨-, l₁, l₂, l₃, l₄⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  have hT := GlobalTheory.UT.torsionIso_of_pelUnif hL l₁ l₂ l₃ l₄ E H M.W _ hA M.t M.P
  choose f f₁ f₂ f₃ f₄ f₅ f₆ using hT C
  have hg : jFK (R := M.W) C = (baseOver (Sp C)).hom ≫ jFK (R := M.W) C := (Category.id_comp _).symm
  obtain ⟨e, he⟩ : ∃ e : (baseOver (Sp C) ⟶ o.P.A) ≃* (TFK (R := M.W) C ⟶ M.P.A.A), ∀ x, (e x).left = x.left ≫ M.φ :=
    LiePull.exists_pushEquiv M.cart (baseOver (Sp C)) _ hg
  have eact : ∀ c x, e (x ≫ o.oa.act c) = e x ≫ M.P.oA.act c := fun c x => Over.OverMorphism.ext (by
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, M.act, Category.assoc])
  have tors : ∀ n (hn : 0 < n) p, f n hn p ^ n = 1 := fun n hn p => by
    obtain ⟨w, hw⟩ := M.P.U.ext
    exact ((f₁ n hn p _).2 rfl w hw).1
  have hev : ∀ n a, ∃ p : QkPt M.P.D.toPre C n, ∀ hn : 0 < n, f n hn p = e (o.I.ev n a) := fun n a => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨TorusExt.qkZero hB C 0, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨p, hp⟩ := f₂ n hn (e (o.I.ev n a)) (by rw [← map_pow, (o.I.onto n hn _).2 ⟨a, rfl⟩, map_one])
      exact ⟨p, fun _ => hp⟩
  choose ev evp using hev
  refine ⟨{ ζ := o.I.ζ, ζ_prim := o.I.ζ_prim, ζ_pow := o.I.ζ_pow, ev := ev
            add := fun n hn a b => ?_, lin := fun n hn c a => ?_, ker := fun n hn a b => ?_,
            onto := fun n hn p => ?_, tower := fun n m hn hm a => ?_, isom := fun n hn a b => ?_ },
    rfl, fun k hk x p' z h hz => ?_⟩
  · exact (TorusExt.qkAdd_iff hB _ _ _).2 ((f₃ n hn _ _).1 (by
      rw [f₄ n hn _ _ _ (TorusExt.qkAdd_qkAdd hB _ _), evp, evp, evp, o.I.add, map_mul]))
  · obtain ⟨p, hp⟩ := qkAct_exists hL.1.globalFns hB M.P.oD c (ev n a)
    have h₁ := f₅ n hn _ _ _ hp
    obtain ⟨q, q₁, q₂, q₃⟩ := hp
    refine ⟨q, q₁, q₂, TorusExt.equiv_trans hB q₃ ((f₃ n hn _ _).1 ?_)⟩
    rw [h₁, evp, evp, o.I.lin, eact]
  · rw [← f₃ n hn, evp, evp, e.injective.eq_iff]
    have h₁ : o.I.ev n a = o.I.ev n b * o.I.ev n (a - b) := by rw [← o.I.add, add_sub_cancel]
    rw [h₁, mul_eq_left, o.I.ker n hn]
    exact exists_congr fun c => sub_eq_iff_eq_add'
  · obtain ⟨a, ha⟩ := (o.I.onto n hn (e.symm (f n hn p))).1 (by rw [← map_pow, tors, map_one])
    exact ⟨a, (f₃ n hn _ _).1 (by rw [evp, ha, MulEquiv.apply_symm_apply])⟩
  · obtain ⟨q, q₁, q₂⟩ := exists_level_down hB n m (ev (n * m) a)
    have hN := Nat.mul_pos hn hm
    have h := (GlobalTheory.LevelCompat.qkToAkU_level hL M.W _ hA M.P.D M.P.A M.t.G M.t.semi M.P.U C n m _ hn hm rfl q
      (ev (n * m) a) _).2 q₁ q₂ ((f₁ _ hN _ _).2 rfl)
    refine ⟨q, q₁, q₂, (f₃ n hn _ _).1 ?_⟩
    rw [← (f₁ n hn _ _).1 h, evp, evp, ← map_pow, o.I.tower n m hn hm]
  · refine (f₆ n hn _ _ _).2 ?_
    rw [evp, evp]
    exact weilIs_of_pull M.P.A.isLB o.P.isLB M.cart M.lb (baseOver (Sp C)) _ hg n _ _ _ _ _ (he _) (he _)
      (o.I.isom n hn a b)
  · refine (f₁ k hk _ _).2 ?_
    rw [← (f₃ k hk _ _).2 h]
    exact (Over.OverMorphism.ext (hz.trans (he _).symm)).trans (evp k x hk).symm

end GlobalTheory.ModelData.ModelTate
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionIsometryUniformisedModelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_isometry_uniformised_model : GlobalTheory.UT.LL → BrGtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (C : Type) [NormedField C] (o : Full D C) (M : Mdl o) (N' : NumD C) (_ : NumOf M.P.D.toPre C N'), ∃ I : TateIsoQ D M.P.D.toPre M.P.oD C, I.ζ = o.I.ζ ∧ ∀ k, 0 < k → ∀ x p' (z : TFK (R := M.W) C ⟶ M.P.A.A), QkPt.Equiv _ C (I.ev k x) p' → z.left = (o.I.ev k x).left ≫ M.φ → M.P.ToA C k p' z := by
  first | exact @GlobalTheory.ModelData.ModelTate.exists_tateIsoQ_of_model | exact GlobalTheory.ModelData.ModelTate.exists_tateIsoQ_of_model | (intros; apply GlobalTheory.ModelData.ModelTate.exists_tateIsoQ_of_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullTorsionIsometryOfTateIsoQ
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullTorsionIsometryOfTateIsoQ
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Relabel

theorem weilIs_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hp : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f)
    (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (c : Γ(T.left, ⊤)ˣ) (ex : x₀.left = x.left ≫ φ)
    (ey : y₀.left = y.left ≫ φ) (h : WeilIs G L k x₀ y₀ c) : WeilIs G' L' k x y c := by
  subst hg
  exact (GlobalTheory.weilIs_grpPullback_of_comm' S S' G G' f φ L L' hL hL' hp hw T k x y x₀ y₀ c ex ey).2 h

theorem exists_fullI_of_tateIsoQ : GlobalTheory.UT.LL → AllD fun {E} _ _ _ {H} D => ∀ (C : Type) [NormedField C] (o : Full D C) (M : Mdl o) (I' : TateIsoQ D M.P.D.toPre M.P.oD C), ∃ I : FullI o, I.ζ = I'.ζ ∧ ∀ j, 0 < j → ∀ x, ∃ z : TFK (R := M.W) C ⟶ M.P.A.A, z.left = (I.ev j x).left ≫ M.φ ∧ M.P.ToA C j (I'.ev j x) z := by
  intro hLL E _ _ _ H D C _ o M I'
  let := H.starRing
  have : IsAlgClosed C := o.closed
  obtain ⟨hadm, hcz⟩ := M.admissible_base_of_complete_dvr
  have : CharZero M.W := hcz
  have hall := GlobalTheory.TestFibre.laws_all hLL.1 hLL.2.1
  have hT : M.P.TorsionIso := GlobalTheory.T.torsionIso_of_linear_uniformisation_triple hLL hall.2.1 hall.2.2.1 hall.2.2.2.1 hall.2.2.2.2 E H M.W
    (IsLocalRing.maximalIdeal M.W) hadm M.t M.P
  have hTw := GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hLL M.W (IsLocalRing.maximalIdeal M.W) hadm M.P.D M.P.A M.t.G M.t.semi M.P.U C
  have hT' := fun (k : ℕ) (hk : 1 ≤ k) => hT C k hk
  choose f hfA hfB hfC hfD hfE hfF using hT'
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv M.cart (baseOver (Sp C)) (jFK (R := M.W) C)
    (by simp)

  have gA : ∀ (n : ℕ) (hn : 0 < n) a, M.P.ToA C n (I'.ev n a) (f n hn (I'.ev n a)) := fun n hn a => (hfA n hn _ _).2 rfl
  have gAdd : ∀ (n : ℕ) (hn : 0 < n) a b, f n hn (I'.ev n (a + b)) = f n hn (I'.ev n a) * f n hn (I'.ev n b) :=
    fun n hn a b => hfD n hn _ _ _ (I'.add n hn a b)
  have gLin : ∀ (n : ℕ) (hn : 0 < n) (c : 𝓞 E) a, f n hn (I'.ev n (c • a)) = f n hn (I'.ev n a) ≫ M.P.oA.act c :=
    fun n hn c a => hfE n hn c _ _ (I'.lin n hn c a)
  have gEq : ∀ (n : ℕ) (hn : 0 < n) a b, f n hn (I'.ev n a) = f n hn (I'.ev n b) ↔ ∃ e, a = b + n • e :=
    fun n hn a b => (hfC n hn _ _).trans (I'.ker n hn a b)
  have gZero : ∀ (n : ℕ) (hn : 0 < n), f n hn (I'.ev n 0) = 1 := by
    intro n hn
    have h0 := gAdd n hn 0 0
    rw [add_zero] at h0
    exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
  have gNsmul : ∀ (n : ℕ) (hn : 0 < n) a (m : ℕ), f n hn (I'.ev n (m • a)) = f n hn (I'.ev n a) ^ m := by
    intro n hn a m
    induction m with
    | zero => rw [zero_smul, gZero, pow_zero]
    | succ m ih => rw [succ_nsmul, gAdd, ih, pow_succ]
  have gPow : ∀ (n : ℕ) (hn : 0 < n) a, f n hn (I'.ev n a) ^ n = 1 := by
    intro n hn a
    rw [← gNsmul, ← gZero n hn]
    exact (gEq n hn _ _).2 ⟨a, by rw [zero_add]⟩
  have gOnto : ∀ (n : ℕ) (hn : 0 < n) x, x ^ n = 1 → ∃ a, f n hn (I'.ev n a) = x := by
    intro n hn x hx
    obtain ⟨p, rfl⟩ := hfB n hn x hx
    obtain ⟨a, ha⟩ := I'.onto n hn p
    exact ⟨a, (hfC n hn _ _).2 ha⟩
  have gTower : ∀ (n m : ℕ) (hn : 0 < n) (hm : 0 < m) a,
      f (n * m) (Nat.mul_pos hn hm) (I'.ev (n * m) a) ^ m = f n hn (I'.ev n a) := by
    intro n m hn hm a
    obtain ⟨q, hqy, hqg, hqe⟩ := I'.tower n m hn hm a
    have h1 := (hTw n m (n * m) hn hm rfl q (I'.ev (n * m) a) (f (n * m) (Nat.mul_pos hn hm) (I'.ev (n * m) a))).2
      hqy hqg (gA (n * m) (Nat.mul_pos hn hm) a)
    rw [(hfA n hn q _).1 h1]
    exact (hfC n hn _ _).2 hqe
  have gWeil : ∀ (n : ℕ) (hn : 0 < n) a b, WeilIs M.P.A.A M.P.A.L n (f n hn (I'.ev n a)) (f n hn (I'.ev n b))
      (unitOn (I'.ζ n ^ D.EF a b)) := fun n hn a b => (hfF n hn _ _ _).1 (I'.isom n hn a b)

  have hL : ∀ y, (e.symm y).left ≫ M.φ = y.left := fun y => by rw [← he, e.apply_symm_apply]
  have hComm : ∀ y (c : 𝓞 E), e.symm (y ≫ M.P.oA.act c) = e.symm y ≫ o.oa.act c := by
    intro y c
    apply e.injective
    rw [e.apply_symm_apply]
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, M.act c, ← Category.assoc, hL]
  obtain ⟨ev, hev⟩ : ∃ ev : ℕ → D.La → (baseOver (Sp C) ⟶ o.P.A),
      ∀ n a, ev n a = if hn : 0 < n then e.symm (f n hn (I'.ev n a)) else o.I.ev n a := ⟨_, fun _ _ => rfl⟩
  refine ⟨{ ζ := I'.ζ, ζ_prim := I'.ζ_prim, ζ_pow := I'.ζ_pow, ev := ev, add := ?_, lin := ?_, ker := ?_, onto := ?_, tower := ?_, isom := ?_ }, rfl, ?_⟩
  · intro n a b
    by_cases hn : 0 < n
    · rw [hev, hev, hev, dite_eq_left hn, dite_eq_left hn, dite_eq_left hn, gAdd, map_mul]
    · rw [hev, hev, hev, dite_eq_right hn, dite_eq_right hn, dite_eq_right hn]
      exact o.I.add n a b
  · intro n c a
    by_cases hn : 0 < n
    · rw [hev, hev, dite_eq_left hn, dite_eq_left hn, gLin, hComm]
    · rw [hev, hev, dite_eq_right hn, dite_eq_right hn]
      exact o.I.lin n c a
  · intro n hn a
    rw [hev, dite_eq_left hn, map_eq_one_iff _ e.symm.injective, ← gZero n hn, gEq]
    simp only [zero_add]
  · intro n hn x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := gOnto n hn (e x) (by rw [← map_pow, hx, map_one])
      exact ⟨a, by rw [hev, dite_eq_left hn, ha, e.symm_apply_apply]⟩
    · rintro ⟨a, rfl⟩
      rw [hev, dite_eq_left hn, ← map_pow, gPow, map_one]
  · intro n m hn hm a
    rw [hev, hev, dite_eq_left (Nat.mul_pos hn hm), dite_eq_left hn, ← map_pow, gTower n m hn hm]
  · intro n hn a b
    rw [hev, hev, dite_eq_left hn, dite_eq_left hn]
    exact weilIs_push M.P.A.isLB o.P.isLB M.cart M.lb (baseOver (Sp C)) (jFK (R := M.W) C)
      (by simp) n _ _ _ _ _ (hL _).symm (hL _).symm (gWeil n hn a b)
  · intro j hj x
    refine ⟨f j hj (I'.ev j x), ?_, gA j hj x⟩
    change _ = (ev j x).left ≫ M.φ
    rw [hev, dite_eq_left hj, hL]

end GlobalTheory.Relabel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullTorsionIsometryOfTateIsoQStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_full_torsion_isometry_of_tateIsoQ : GlobalTheory.UT.LL → AllD fun {E} _ _ _ {H} D => ∀ (C : Type) [NormedField C] (o : Full D C) (M : Mdl o) (I' : TateIsoQ D M.P.D.toPre M.P.oD C), ∃ I : FullI o, I.ζ = I'.ζ ∧ ∀ j, 0 < j → ∀ x, ∃ z : TFK (R := M.W) C ⟶ M.P.A.A, z.left = (I.ev j x).left ≫ M.φ ∧ M.P.ToA C j (I'.ev j x) z := by
  first | exact @GlobalTheory.Relabel.exists_fullI_of_tateIsoQ | exact GlobalTheory.Relabel.exists_fullI_of_tateIsoQ | (intros; apply GlobalTheory.Relabel.exists_fullI_of_tateIsoQ <;> assumption)
end
end
