module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPhiRelSmul
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CubBoxVal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoCubePow
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowAdj

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]

theorem psum_comp_hom (q : G' ⟶ G) [IsMonHom q] {T' T : Over S} {n : ℕ} (x : Fin n → (T' ⟶ G'))
    (y : Fin n → (T ⟶ G)) (h : T' ⟶ T) (e : ∀ k, x k ≫ q = h ≫ y k) (I : Finset (Fin n)) :
    psum G' x I ≫ q = h ≫ psum G y I :=
  (Geo.Tor.psum_hom (MonoidHom.mk' (· ≫ q) fun a b => MonObj.mul_comp a b q) x I).trans
    ((congrArg (fun z => psum G z I) (funext e)).trans (Geo.Tor.psum_hom (Geo.Tor.preHom h) y I).symm)

theorem cls_cube_box {j : ℕ} (p : IsPowGrp G' G j) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hb : Geo.Tor.LBIso L' (boxLB L p.pr)) {T' T : Over S} {n : ℕ} (x : Fin n → (T' ⟶ G'))
    (y : Fin n → (T ⟶ G)) (h : Fin j → (T' ⟶ T)) (e : ∀ i k, x k ≫ p.pr i = h i ≫ y k)
    (h₁ : (cubeLB G' x L').IsLB) (h₂ : (cubeLB G y L).IsLB) :
    cls _ h₁ = ∑ i, pull (h i).left (cls _ h₂) := by
  have a := cls_linComb hL' _ _ h₁
  have b := cls_linComb hL _ _ h₂
  have c : cls L' hL' = ∑ i, pull (p.pr i).left (cls L hL) := by
    rw [(cls_eq_iff hL' (LB.isLB_linComb hL _ _)).2 hb, cls_linComb hL]
    simp only [one_smul]
  refine a.trans (Eq.trans ?_ (Finset.sum_congr rfl fun i _ => congrArg (pull (h i).left) b.symm))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [c, map_sum, map_zsmul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun I _ => ?_
  have := p.hom i
  rw [← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, psum_comp_hom (p.pr i) x y (h i) (e i)]

theorem lbIso_cube_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → Geo.Tor.LBIso L' (boxLB L p.pr) → ∀ (f g : G ⟶ G) (f' g' : G' ⟶ G'), (∀ i, f' ≫ p.pr i = p.pr i ≫ f) → (∀ i, g' ≫ p.pr i = p.pr i ≫ g) → Geo.Tor.LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L) → Geo.Tor.LBIso (cubeLB G' ![fst G' G' ≫ f', snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ g'] L') := by
  intro S G' G _ _ _ _ j p L L' hL hL' hb f g f' g' hf hg H
  have i₁ : (cubeLB G ![fst G G ≫ f, snd G G] L).IsLB := LB.isLB_linComb hL _ _
  have i₂ : (cubeLB G ![fst G G, snd G G ≫ g] L).IsLB := LB.isLB_linComb hL _ _
  have i₃ : (cubeLB G' ![fst G' G' ≫ f', snd G' G'] L').IsLB := LB.isLB_linComb hL' _ _
  have i₄ : (cubeLB G' ![fst G' G', snd G' G' ≫ g'] L').IsLB := LB.isLB_linComb hL' _ _
  refine (cls_eq_iff i₃ i₄).1 ?_
  rw [cls_cube_box p hL hL' hb _ _ (fun i => p.pr i ⊗ₘ p.pr i) (fun i k => by fin_cases k <;> simp [hf]) i₃ i₁,
    cls_cube_box p hL hL' hb _ _ (fun i => p.pr i ⊗ₘ p.pr i) (fun i k => by fin_cases k <;> simp [hg]) i₄ i₂,
    (cls_eq_iff i₁ i₂).2 H]

end GlobalTheory.PowAdj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PowPullbackHomExt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace PowOLinear

theorem pow_hom_ext {S : Scheme.{0}} {G' G Z : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G' G j) {a b : Z ⟶ G'} (h : ∀ i, a ≫ p.pr i = b ≫ p.pr i) : a = b :=
  Fan.IsLimit.hom_ext p.lim a b h

theorem pow_pullback_hom_ext {S S' : Scheme.{0}} (f : S' ⟶ S) {G' G : Over S} [GrpObj G']
    [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j) {Z : Over S'} {a b : Z ⟶ (Over.pullback f).obj G'}
    (h : ∀ i, a ≫ (Over.pullback f).map (p.pr i) = b ≫ (Over.pullback f).map (p.pr i)) : a = b :=
  (isLimitOfPreserves (Over.pullback f) p.lim).hom_ext fun i => h i.as

theorem res_pullU_val {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S}
    (g : Z ⟶ splitTorus S X) (χ : X) (h : ⊤ ≤ g.left ⁻¹ᵁ ⊤) :
    (res h (pullU g.left ⊤ (charUnit S X χ))).val = g.left.appTop.hom (charUnit S X χ).val := by
  have : (res h (pullU g.left ⊤ (charUnit S X χ))).val =
      (g.left.appLE ⊤ ⊤ h).hom (charUnit S X χ).val := rfl
  rw [this, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl

theorem charUnit_zero {S : Scheme.{0}} {X : Type} [AddCommGroup X] :
    (charUnit S X 0).val = 1 := by
  have h := SplitTorusHom.charUnit_add (S := S) (0 : X) 0
  rw [add_zero] at h
  exact ((charUnit S X 0).isUnit.mul_eq_left.mp h.symm)

theorem torusEndOf_pow {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {j : ℕ}
    (xe : X' ≃+ (Fin j → X)) (pr : Fin j → (splitTorus S X' ⟶ splitTorus S X))
    (hpr : ∀ (i : Fin j) (χ : X),
      res (fun x _ => show (pr i).left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
        (pullU (pr i).left ⊤ (charUnit S X χ)) = charUnit S X' (xe.symm (Pi.single i χ)))
    (h : X →+ X) (h' : X' →+ X') (hh : ∀ x i, xe (h' x) i = h (xe x i))
    (t : splitTorus S X ⟶ splitTorus S X) (ht : TorusEndOf X h t)
    (t' : splitTorus S X' ⟶ splitTorus S X') (htt : ∀ i, t' ≫ pr i = pr i ≫ t) :
    TorusEndOf X' h' t' := by
  have hpr' : ∀ i χ, (pr i).left.appTop.hom (charUnit S X χ).val =
      (charUnit S X' (xe.symm (Pi.single i χ))).val := fun i χ =>
    (res_pullU_val (pr i) χ _).symm.trans (congrArg Units.val (hpr i χ))
  have ht' : ∀ χ, t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := fun χ =>
    (res_pullU_val t χ _).symm.trans (congrArg Units.val (ht χ))
  have key : ∀ y : Fin j → X, t'.left.appTop.hom (charUnit S X' (xe.symm y)).val =
      (charUnit S X' (h' (xe.symm y))).val := by
    intro y
    induction y using Pi.single_induction with
    | zero => rw [map_zero, map_zero, charUnit_zero, map_one]
    | add u v hu hv =>
      rw [map_add (f := _), map_add (f := _), SplitTorusHom.charUnit_add, SplitTorusHom.charUnit_add, map_mul, hu, hv]
    | single i χ =>
      have e : h' (xe.symm (Pi.single i χ)) = xe.symm (Pi.single i (h χ)) := by
        apply xe.injective
        funext k
        rw [hh, xe.apply_symm_apply, xe.apply_symm_apply]
        by_cases hk : k = i
        · subst hk; simp
        · simp [Pi.single_eq_of_ne hk]
      rw [e, ← hpr', ← hpr', ← SplitTorusHom.appTop_comp, htt, SplitTorusHom.appTop_comp, ht']
  intro x
  apply Units.ext
  refine (res_pullU_val t' x _).trans ?_
  have := key (xe x)
  rwa [xe.symm_apply_apply] at this

end PowOLinear


open PowOLinear in
theorem oLinear_of_unifPow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) (P : UnifPowOf3 pD pA pG U' U) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X], (∀ (a : O) (x : D'.toPre.X), pD.xe (a • x) = a • pD.xe x) → ∀ (ιD : D.OAct O) (ιD' : D'.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O) (ιG' : RingAct G' O), (∀ a i, ιD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ ιD.onB.act a) → (∀ a i, ιA'.act a ≫ pA.pr i = pA.pr i ≫ ιA.act a) → (∀ a i, ιG'.act a ≫ pG.pr i = pG.pr i ≫ ιG.act a) → U.OLinear O ιD ιA ιG → U'.OLinear O ιD' ιA' ιG' := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U P O _ _ _ _ hxe ιD ιD' ιA ιA' ιG ιG'
    hD hA hG hU
  refine ⟨fun a => ?_, fun e a => ?_, fun e a => ?_⟩
  · refine pow_hom_ext pA.toIsPowGrp fun i => ?_
    rw [Category.assoc, Category.assoc, hA, P.gen_pr, ← Category.assoc U'.gen.hom, P.gen_pr,
      ← Functor.map_comp_assoc, hG, Functor.map_comp_assoc, hU.ext, Category.assoc]
  · refine pow_pullback_hom_ext (thick R I e) pD.pw fun i => ?_
    have h₁ := P.q_pr e i
    have h₂ := hU.q_lin e a
    have h₃ := congrArg (Over.pullback (thick R I e)).map (hD a i)
    have h₄ := congrArg (Over.pullback (thick R I e)).map (hG a i)
    rw [Functor.map_comp, Functor.map_comp] at h₃ h₄
    refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    rw [h₃, h₁, ← Category.assoc, h₄, Category.assoc, h₂, ← Category.assoc, ← h₁, Category.assoc]
  · obtain ⟨pT, hi, hc⟩ := GlobalTheory.T.productUniformization_torus_isPower R I j D D' A A' G G' pD pA pG U' U P e
    obtain ⟨t, ht, hti⟩ := hU.i_lin e a
    obtain ⟨t', ht'⟩ : ∃ t' : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X,
        ∀ i, t' ≫ pT.pr i = pT.pr i ≫ t :=
      ⟨Fan.IsLimit.lift pT.lim fun i => pT.pr i ≫ t, fun i => Fan.IsLimit.fac pT.lim _ i⟩
    refine ⟨t', ?_, ?_⟩
    · exact torusEndOf_pow pD.xe pT.pr hc (DistribSMul.toAddMonoidHom _ (star a))
        (DistribSMul.toAddMonoidHom _ (star a)) (fun x i => congrFun (hxe (star a) x) i) t ht t' ht'
    · refine pow_pullback_hom_ext (thick R I e) pG fun i => ?_
      have h₄ := congrArg (Over.pullback (thick R I e)).map (hG a i)
      rw [Functor.map_comp, Functor.map_comp] at h₄
      refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      rw [h₄, hi, ← Category.assoc, hi, Category.assoc, hti, ← Category.assoc, ← ht', Category.assoc]

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory


open Geo.Tor in
theorem isSymmetric_of_symmetry_generator {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (sy : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hsy : sy.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sy (eSec G)) (LB.oneGen L.L)) : L.IsSymmetric := by
  have oi : eSec G ≫ (ι[G]).left = eSec G := by
    have : η[G] ≫ ι[G] = η[G] := by simp
    exact congrArg (fun q => q.left) this
  have mem : ∀ (x : G.left) (a b : L.L.ι), (ι[G]).left x ∈ L.L.U a → x ∈ L.L.U b →
      x ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![a, b] := fun x a b ha hb =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [ha, hb]
  have le : ∀ p : (PUnit → L.L.ι) × L.L.ι, (L.L.pull (ι[G]).left).U p.1 ⊓ L.L.U p.2 ≤
      LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![p.1 PUnit.unit, p.2] := fun p x hx =>
    mem x _ _ (mem_pull.1 hx.1) hx.2
  let w : LB.Iso L.L (L.L.pull (ι[G]).left) := ⟨fun p => res (le p) (sy.s ![p.1 PUnit.unit, p.2])⟩
  have hw : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (a b : L.L.ι), (ι[G]).left (f y) ∈ L.L.U a → f y ∈ L.L.U b →
      gw w f y a b = gm f y (LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![a, b]) (sy.s ![a, b]) :=
    fun Y f y a b ha hb => gm_res f y (le (fun _ => a, b)) ⟨mem_pull.2 ha, hb⟩ _
  have pg : PGen w := by
    intro Y f y j j' k k' hj hj' hk hk'
    rw [hw Y f y j k hj hk, hw Y f y j' k' hj' hk', gen_trans hsy f y (mem _ _ _ hj hk) (mem _ _ _ hj' hk')]
    congr 1
    rw [trF, Fin.prod_univ_two]
    show gm (f ≫ (ι[G]).left) y _ (L.L.g j j') ^ (1 : ℤ) * gm (f ≫ 𝟙 _) y _ (L.L.g k k') ^ (-1 : ℤ) = _
    rw [Category.comp_id, zpow_one, zpow_neg_one]
  refine ⟨oi.trans (Category.id_comp _).symm, w, (isGen_iff w).2 pg, ?_⟩
  refine (maps_iff w (K := PUnit) (fun _ => eSec G) (fun _ => eSec G) (fun _ => 1) L.rig L.rig (𝟙 _) _
    (fun j => rigPull_le _ (𝟙 _) (oi.trans (Category.id_comp _).symm) L.L j) (fun _ => rfl)).2 ?_
  intro Z r z p q hp hq
  have hp₀ : (ι[G]).left ((r ≫ eSec G) z) ∈ L.L.U (p PUnit.unit) := hp PUnit.unit
  have hq₀ : (r ≫ eSec G) z ∈ L.L.U (q PUnit.unit) := hq PUnit.unit
  have ri : (r ≫ eSec G) ≫ (ι[G]).left = r ≫ eSec G := by rw [Category.assoc, oi]
  have hp₁ : (r ≫ eSec G) z ∈ L.L.U (p PUnit.unit) := by rw [← ri]; exact hp₀
  have hq₁ : (ι[G]).left ((r ≫ eSec G) z) ∈ L.L.U (q PUnit.unit) := by
    have := hq₀
    rw [← ri] at this; exact this
  have one : gw w (r ≫ eSec G) z (q PUnit.unit) (q PUnit.unit) = 1 := by
    obtain ⟨J, hJ, e⟩ := exists_good L.L L.isLB z (K := PUnit) (fun _ => r ≫ eSec G) q (fun _ _ _ => rfl)
      (fun _ => hq₀)
    have a := val_corr hJ hr r
    rw [val_pull hJ, val_one, val_of sy (r ≫ eSec G) z J ![q PUnit.unit, q PUnit.unit] (fun k => by
      fin_cases k
      · exact (congrArg J ri).trans (e PUnit.unit)
      · exact (congrArg J (Category.comp_id _)).trans (e PUnit.unit))] at a
    exact (hw _ _ _ _ _ hq₁ hq₀).trans a
  rw [Category.comp_id, Fintype.prod_unique, zpow_one,
    gen_trans L.rigGen r z (j := p) (j' := q) (Set.mem_iInter.2 fun _ => hp₁) (Set.mem_iInter.2 fun _ => hq₀)]
  congr 1
  have b := pg _ (r ≫ eSec G) z (p PUnit.unit) (q PUnit.unit) (q PUnit.unit) (q PUnit.unit) hp₀ hq₁ hq₀ hq₀
  rw [one, gm_self L.isLB _ z hq₀, ri, inv_one, _root_.mul_one, _root_.mul_one] at b
  rw [trF, Fintype.prod_unique, zpow_one]
  exact b.symm

theorem exists_pelUnif_pow : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of R))) (P : Geo.Tor.PELUnif I t) (j : ℕ), UnifPowSt3 (I := I) → (∃ D' : DegData R I, Nonempty (IsPowDeg D'.toPre P.D.toPre j)) → (∃ A' : PolAV (Spec (CommRingCat.of (FractionRing R))), Nonempty (IsPowPolAV A' P.A j)) → ∃ (t' : Geo.Tor.SAB H (Spec (CommRingCat.of R))) (P' : Geo.Tor.PELUnif I t') (pG : IsPowGrp t'.G t.G j) (pD : IsPowDeg P'.D.toPre P.D.toPre j) (pA : IsPowPolAV P'.A P.A j), Nonempty (UnifPowOf3 pD pA pG P'.U P.U) ∧ (∀ a i, t'.act.act a ≫ pG.pr i = pG.pr i ≫ t.act.act a) ∧ ∀ (a : NumberField.RingOfIntegers E) (x : P'.D.toPre.X), pD.xe (a • x) = a • pD.xe x := by
  intro hG R _ _ I E _ _ _ H t P j hU ⟨D', ⟨pD⟩⟩ ⟨A', ⟨pA⟩⟩
  letI := H.starRing
  let pG : IsPowGrp (powObj t.G j) t.G j := powIsPowGrp t.G j
  obtain ⟨U', ⟨Q⟩⟩ := hU P.D P.A t.G P.U j D' A' (powObj t.G j) pD pA pG
  obtain ⟨act', hact⟩ := (GlobalTheory.exists_powAct _ _ _ j pG).2 _ t.act
  have iso : Geo.Tor.LBIso U'.LG.L (boxLB t.PP.L pG.pr) := by
    rw [← P.bundle]; exact ⟨Q.wL, Q.wL_gen⟩
  let t' : Geo.Tor.SAB H (Spec (CommRingCat.of R)) :=
    { G := powObj t.G j
      semi := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ j pG t.semi
      act := act'
      PP := U'.LG
      cub := U'.cubG
      sym := isSymmetric_of_symmetry_generator U'.LG U'.symG U'.symG_gen U'.symG_rig
      adj := fun a => GlobalTheory.PowAdj.lbIso_cube_pow _ _ _ j pG _ _ t.PP.isLB U'.LG.isLB iso _ _ _ _ (hact a) (hact (H.bar a)) (t.adj a)
      prim := GlobalTheory.PowPrimitive.lbIso_cube_pow _ _ _ j pG _ _ t.PP.isLB U'.LG.isLB iso _ _ (hact H.w0) t.prim }
  letI md : Module (NumberField.RingOfIntegers E) D'.toPre.X := pD.xe.module _
  have hx : ∀ (a : NumberField.RingOfIntegers E) (x : D'.toPre.X), pD.xe (a • x) = a • pD.xe x := fun a x =>
    pD.xe.apply_symm_apply _
  obtain ⟨oD', hoD⟩ := GlobalTheory.powDeg_diagonal_action hG R j _ _ pD _ hx P.oD
  obtain ⟨rA, hrA⟩ := (GlobalTheory.exists_powAct _ _ _ j pA.toIsPowGrp).1 _ P.oA.toRingAct
  let oA' : A'.OAct (NumberField.RingOfIntegers E) :=
    { toRingAct := rA
      rosati := fun a => GlobalTheory.rosatiAdj_pow _ _ _ j pA.toIsPowGrp _ _ P.A.isLB A'.isLB ⟨pA.w, pA.w_gen⟩ _ _ _ _ (hrA a)
        (hrA (star a)) (P.oA.rosati a) }
  let P' : Geo.Tor.PELUnif I t' :=
    { D := D'
      oD := oD'
      A := A'
      oA := oA'
      U := U'
      bundle := rfl
      lin := GlobalTheory.oLinear_of_unifPow R I j _ _ _ _ _ _ pD pA pG U' P.U Q _ hx P.oD oD' P.oA oA' t.act.toRingAct act'.toRingAct
        hoD hrA hact P.lin
      w0 := GlobalTheory.PsiWZeroProd.main R j _ _ pD _ hx P.oD oD' hoD H.w0 P.w0 }
  exact ⟨t', P', pG, pD, pA, ⟨Q⟩, hact, hx⟩

end GlobalTheory
