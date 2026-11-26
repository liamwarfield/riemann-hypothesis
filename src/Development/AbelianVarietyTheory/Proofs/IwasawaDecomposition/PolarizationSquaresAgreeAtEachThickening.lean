module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisationsAgreeAtLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GmSqPullG
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqLevel

open TopologicalSpace

variable {X : Scheme.{0}}

abbrev sqLB (L : LB X) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)

theorem mem_sq {L : LB X} {x : X} {J : Fin 1 → L.ι} : x ∈ (sqLB L).U J ↔ x ∈ L.U (J 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem mem_sq_pull {Y : Scheme.{0}} {L : LB X} {F : Y ⟶ X} {y : Y} {J : PUnit → Fin 1 → L.ι} :
    y ∈ ((sqLB L).pull F).U J ↔ F y ∈ L.U (J PUnit.unit 0) :=
  mem_pull.trans mem_sq

theorem gm_sq_g {Y : Scheme.{0}} (L : LB X) (r : Y ⟶ X) (y : Y) (J J' : Fin 1 → L.ι) (hJ : r y ∈ L.U (J 0))
    (hJ' : r y ∈ L.U (J' 0)) :
    gm r y ((sqLB L).U J ⊓ (sqLB L).U J') ((sqLB L).g J J') = gm r y _ (L.g (J 0) (J' 0)) ^ 2 := by
  refine (gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => 2) r y J J' (mem_sq.2 hJ) (mem_sq.2 hJ')).trans ?_
  rw [Fin.prod_univ_one, Category.comp_id]
  exact zpow_two _ |>.trans (pow_two _).symm

theorem gm_sq_pull_g {Y Z : Scheme.{0}} (L : LB X) (F : Y ⟶ X) (r : Z ⟶ Y) (z : Z) (J J' : PUnit → Fin 1 → L.ι)
    (hJ : F (r z) ∈ L.U (J PUnit.unit 0)) (hJ' : F (r z) ∈ L.U (J' PUnit.unit 0)) :
    gm r z (((sqLB L).pull F).U J ⊓ ((sqLB L).pull F).U J') (((sqLB L).pull F).g J J') =
      gm (r ≫ F) z _ (L.g (J PUnit.unit 0) (J' PUnit.unit 0)) ^ 2 :=
  (gm_pull_g (sqLB L) F r z J J' (mem_sq_pull.2 hJ) (mem_sq_pull.2 hJ')).trans
    (gm_sq_g L (r ≫ F) z _ _ hJ hJ')

variable {B G E : Scheme.{0}} {M : LB B} {L : LB G} {p : E ⟶ B} {f : E ⟶ G}

theorem sqIso_le (q : (PUnit → Fin 1 → M.ι) × (PUnit → Fin 1 → L.ι)) :
    ((sqLB M).pull p).U q.1 ⊓ ((sqLB L).pull f).U q.2 ≤
      (M.pull p).U (fun _ => q.1 PUnit.unit 0) ⊓ (L.pull f).U (fun _ => q.2 PUnit.unit 0) :=
  fun _ h => ⟨mem_pull.2 (mem_sq_pull.1 h.1), mem_pull.2 (mem_sq_pull.1 h.2)⟩

def sqIso (w : LB.Iso (L.pull f) (M.pull p)) : LB.Iso ((sqLB L).pull f) ((sqLB M).pull p) :=
  ⟨fun q => res (sqIso_le q) (w.s (fun _ => q.1 PUnit.unit 0, fun _ => q.2 PUnit.unit 0)) ^ 2⟩

theorem gw_sqIso (w : LB.Iso (L.pull f) (M.pull p)) {Z : Scheme.{0}} (r : Z ⟶ E) (z : Z) (J : Fin 1 → M.ι)
    (K : PUnit → Fin 1 → L.ι) (hJ : p (r z) ∈ M.U (J 0)) (hK : f (r z) ∈ L.U (K PUnit.unit 0)) :
    gw (sqIso w) r z J K = gw w r z (J 0) (fun _ => K PUnit.unit 0) ^ 2 := by
  have hm : r z ∈ ((sqLB M).pull p).U (fun _ => J) ⊓ ((sqLB L).pull f).U K :=
    ⟨mem_sq_pull.2 hJ, mem_sq_pull.2 hK⟩
  exact (map_pow _ _ _).trans (congrArg (· ^ 2) (gm_res r z _ hm _))

theorem sqIso_isGen {w : LB.Iso (L.pull f) (M.pull p)} (hw : w.IsGen) : (sqIso w).IsGen := by
  rw [isGen_iff] at hw ⊢
  intro Y r y j j' k k' hj hj' hk hk'
  have hj₀ := mem_sq.1 hj
  have hj₀' := mem_sq.1 hj'
  have hk₀ := mem_sq_pull.1 hk
  have hk₀' := mem_sq_pull.1 hk'
  rw [gw_sqIso w r y j k hj₀ hk₀, gw_sqIso w r y j' k' hj₀' hk₀', gm_sq_g M (r ≫ p) y j j' hj₀ hj₀',
    gm_sq_pull_g L f r y k k' hk₀ hk₀']
  have e := hw Y r y (j 0) (j' 0) (fun _ => k PUnit.unit 0) (fun _ => k' PUnit.unit 0) hj₀ hj₀'
    (mem_pull.2 hk₀) (mem_pull.2 hk₀')
  rw [gm_pull_g L f r y _ _ (mem_pull.2 hk₀) (mem_pull.2 hk₀')] at e
  rw [e, mul_pow, mul_pow, inv_pow]

end GlobalTheory.SqLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareIsoRespectsSymmetryPointwise
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareIsoRespectsSymmetryPointwise
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqSym

open GlobalTheory.SqLevel

variable {X Y Z : Scheme.{0}} {K : Type} [Fintype K]

theorem sq_chart_le (L : LB X) (φ : K → (Y ⟶ X)) (j : K → Fin 1 → L.ι) :
    LB.wchart (sqLB L) φ j ≤ LB.wchart L φ (fun k => j k 0) :=
  fun _ hy => Set.mem_iInter.2 fun k => mem_sq.1 (Set.mem_iInter.1 hy k)

def sqGen (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) :
    LB.Gen (LB.LinComb (sqLB L) φ ε) :=
  ⟨fun j => res (sq_chart_le L φ j) (t.s (fun k => j k 0)) ^ 2⟩

theorem gm_sqGen {L : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    (j : K → Fin 1 → L.ι) (h : r z ∈ LB.wchart (sqLB L) φ j) :
    gm r z _ ((sqGen L φ ε t).s j) = gm r z _ (t.s (fun k => j k 0)) ^ 2 := by
  exact (map_pow _ _ _).trans (congrArg (· ^ 2) (gm_res r z _ h _))

theorem sqGen_isGen {L : LB X} (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (ht : t.IsGen) : (sqGen L φ ε t).IsGen := by
  intro (i : K → Fin 1 → L.ι) (j : K → Fin 1 → L.ι)
  apply unit_ext
  intro y hy
  have hi := sq_chart_le L φ i hy.1
  have hj := sq_chart_le L φ j hy.2
  rw [gm_res (𝟙 _) y _ hy, map_mul, gm_res (𝟙 _) y _ hy, gm_sqGen t (𝟙 Y) y i hy.1, gm_sqGen t (𝟙 Y) y j hy.2]
  refine (congrArg (· ^ 2) (gen_trans ht (𝟙 _) y hi hj)).trans ?_
  refine (mul_pow _ _ 2).trans (congrArg (· * _) ?_)
  refine Eq.trans ?_ (gm_linComb (sqLB L) φ ε (𝟙 _) y i j hy.1 hy.2).symm
  rw [trF, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [gm_sq_g L (𝟙 _ ≫ φ k) y (i k) (j k) (by simpa using Set.mem_iInter.1 hi k)
    (by simpa using Set.mem_iInter.1 hj k), ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem val_sqGen {L : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) {z : Z}
    {J : (Z ⟶ X) → Fin 1 → L.ι} (hJ : Good (sqLB L) z J) (r : Z ⟶ Y) :
    val (sqGen L φ ε t) r z J = val t r z (fun ψ => J ψ 0) ^ 2 :=
  gm_sqGen t r z _ (hJ.mem φ r)

theorem good_of_sq {L : LB X} {z : Z} {J : (Z ⟶ X) → Fin 1 → L.ι} (hJ : Good (sqLB L) z J) :
    Good L z (fun ψ => J ψ 0) := fun ψ => mem_sq.1 (hJ ψ)

end GlobalTheory.SqSym

namespace GlobalTheory


open RigidIsoCube SqSym SqLevel in
theorem sq_iso_respects_symmetry_pointwise : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U.symG r z N ^ 2 =
        (∏ k : Fin 2, gv wL (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k) z
          (fun _ => N (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k))
          (fun _ => N' (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
        val (L := U'.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U'.symG r z N' ^ 2 := by
  intro hG R _ _ _ I _ D D' A A' G _ _ _ U U' wL hw Z r z N N' hN hN'
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have hL : (sqLB U.LG.L).IsLB := DVR.linComb_isLB _ U.LG.isLB _ _
  have hL' : (sqLB U'.LG.L).IsLB := DVR.linComb_isLB _ U'.LG.isLB _ _
  have pg := isoPullId_pgen hw (rfl : 𝟙 G.left = 𝟙 G.left)
  have oi : eSec G ≫ (ι[G]).left = eSec G := by
    have : η[G] ≫ ι[G] = η[G] := by simp
    exact congrArg (fun q => q.left) this
  have key := pmaps_of_section pg hL hL' (φ' := ![(ι[G]).left, 𝟙 G.left]) (φ := ![(ι[G]).left, 𝟙 G.left])
    (ε := ![1, -1]) (sqGen _ _ _ U'.symG) (sqGen_isGen U'.LG.isLB U'.symG_gen) (sqGen _ _ _ U.symG)
    (sqGen_isGen U.LG.isLB U.symG_gen) (fun _ => Category.comp_id _) G.hom (eSec G) (Over.w η[G]) s₁
    fun y J J' hJ hJ' => by
      have a := val_corr (good_of_sq hJ) U.symG_rig (𝟙 _)
      rw [val_pull (good_of_sq hJ), val_one, Category.id_comp] at a
      have b := val_corr (good_of_sq hJ') U'.symG_rig (𝟙 _)
      rw [val_pull (good_of_sq hJ'), val_one, Category.id_comp] at b
      rw [val_sqGen _ hJ, val_sqGen _ hJ', a, b, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, oi, Category.comp_id]
      simp
  set φ : Fin 2 → (G.left ⟶ G.left) := ![(ι[G]).left, 𝟙 G.left] with hφ
  have m1 : ∀ k, (r ≫ φ k) z ∈ (sqLB U.LG.L).U (fun _ => N (r ≫ φ k)) := fun k => mem_sq.2 (hN _)
  have m2 : ∀ k, (r ≫ φ k) z ∈ (sqLB U'.LG.L).U (fun _ => N' (r ≫ φ k)) := fun k => mem_sq.2 (hN' _)
  have e := key Z r z (fun k _ => N (r ≫ φ k)) (fun k _ => N' (r ≫ φ k)) (fun k => by simpa using m1 k)
    (fun k => by simpa using m2 k)
  have h1 : (r ≫ 𝟙 G.left) z ∈ LB.wchart (sqLB U.LG.L) φ (fun k _ => N (r ≫ φ k)) :=
    Set.mem_iInter.2 fun k => by simpa using m1 k
  have h2 : r z ∈ LB.wchart (sqLB U'.LG.L) φ (fun k _ => N' (r ≫ φ k)) :=
    Set.mem_iInter.2 fun k => by simpa using m2 k
  have e1 := gm_sqGen U.symG (r ≫ 𝟙 G.left) z _ h1
  have e2 := gm_sqGen U'.symG r z _ h2
  simp only [Category.comp_id] at e1 e
  exact e1.symm.trans (e.trans (congrArg₂ (· * ·)
    (Finset.prod_congr rfl fun k _ => by rw [gw_isoPullId wL rfl _ z _ _ (m1 k) (m2 k)]) e2))
end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareIsoRespectsSymmetryPointwiseStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_iso_respects_symmetry_pointwise : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U.symG r z N ^ 2 =
        (∏ k : Fin 2, gv wL (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k) z
          (fun _ => N (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k))
          (fun _ => N' (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
        val (L := U'.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U'.symG r z N' ^ 2 := by
  first | exact @GlobalTheory.sq_iso_respects_symmetry_pointwise | exact GlobalTheory.sq_iso_respects_symmetry_pointwise | (intros; apply GlobalTheory.sq_iso_respects_symmetry_pointwise <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareIsoCarriesSquareCubical
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareIsoCarriesSquareCubical
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqLevel

variable {X Y : Scheme.{0}} {K : Type} [Fintype K]

theorem sqGen_le (L₀ : LB X) (φ : K → (Y ⟶ X)) (j : K → Fin 1 → L₀.ι) :
    LB.wchart (sqLB L₀) φ j ≤ LB.wchart L₀ φ (fun k => j k 0) :=
  fun _ hy => Set.mem_iInter.2 fun k => mem_sq.1 (Set.mem_iInter.1 hy k)

def sqGen {L₀ : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L₀ φ ε)) :
    LB.Gen (LB.LinComb (sqLB L₀) φ ε) :=
  ⟨fun j => res (sqGen_le L₀ φ j) (t.s (fun k => j k 0)) ^ 2⟩

theorem gm_sqGen {Z : Scheme.{0}} {L₀ : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L₀ φ ε))
    (r : Z ⟶ Y) (z : Z) (j : K → Fin 1 → L₀.ι) (hj : r z ∈ LB.wchart (sqLB L₀) φ j) :
    gm r z _ ((sqGen t).s j) = gm r z _ (t.s (fun k => j k 0)) ^ 2 :=
  (map_pow _ _ _).trans (congrArg (· ^ 2) (gm_res r z _ hj _))

theorem sqGen_isGen {L₀ : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L₀ φ ε)} (ht : t.IsGen) :
    (sqGen t).IsGen := by
  intro j j'
  apply unit_ext
  intro x hx
  have hj := sqGen_le L₀ φ j hx.1
  have hj' := sqGen_le L₀ φ j' hx.2
  have hm : (𝟙 Y) x ∈ (LB.LinComb L₀ φ ε).U (fun k => j k 0) ⊓ (LB.LinComb L₀ φ ε).U (fun k => j' k 0) := ⟨hj, hj'⟩
  have e := congrArg (gm (𝟙 Y) x _) (ht (fun k => j k 0) (fun k => j' k 0))
  rw [gm_res (𝟙 Y) x _ hm, map_mul, gm_res (𝟙 Y) x _ hm] at e
  erw [gm_linComb L₀ φ ε (𝟙 Y) x _ _ hj hj'] at e
  rw [gm_res _ x _ hx, map_mul, gm_res _ x _ hx, gm_sqGen t (𝟙 Y) x j hx.1, gm_sqGen t (𝟙 Y) x j' hx.2]
  erw [gm_linComb (sqLB L₀) φ ε (𝟙 Y) x j j' hx.1 hx.2]
  rw [e, mul_pow]
  congr 1
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  have a₁ : (𝟙 Y ≫ φ k) x ∈ L₀.U (j k 0) := Set.mem_iInter.1 hj k
  have a₂ : (𝟙 Y ≫ φ k) x ∈ L₀.U (j' k 0) := Set.mem_iInter.1 hj' k
  rw [gm_sq_g L₀ (𝟙 Y ≫ φ k) x (j k) (j' k) a₁ a₂, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
    mul_comm]

theorem val_sqGen {Z : Scheme.{0}} {L₀ : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L₀ φ ε))
    {z : Z} {J : (Z ⟶ X) → Fin 1 → L₀.ι} (hJ : Good (sqLB L₀) z J) (r : Z ⟶ Y) :
    val (sqGen t) r z J = val t r z (fun ψ => J ψ 0) ^ 2 :=
  gm_sqGen t r z _ (hJ.mem φ r)

theorem good_sq {Z : Scheme.{0}} {L₀ : LB X} {z : Z} {J : (Z ⟶ X) → Fin 1 → L₀.ι} (hJ : Good (sqLB L₀) z J) :
    Good L₀ z (fun ψ => J ψ 0) :=
  fun ψ => mem_sq.1 (hJ ψ)

end GlobalTheory.SqLevel

namespace GlobalTheory


open RigidIsoCube SqLevel in
theorem sq_iso_carries_sq_cube : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 G).left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t r z N ^ 2 =
        (∏ k : thK.{0}, gv wL (r ≫ thφ G (x3 G) k) z (fun _ => N (r ≫ thφ G (x3 G) k))
          (fun _ => N' (r ≫ thφ G (x3 G) k)) ^ thε k) *
        val (L := U'.LG.L) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t r z N' ^ 2 := by
  intro hG R _ _ _ I _ D D' A A' G _ _ _ U U' wL hw Z r z N N' hN hN'
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  have sj : Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom :=
    surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _)
      (surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _) s₁)
  have hL := DVR.linComb_isLB U.LG.L U.LG.isLB (fun _ : Fin 1 => 𝟙 G.left) (fun _ => 2)
  have hL' := DVR.linComb_isLB U'.LG.L U'.LG.isLB (fun _ : Fin 1 => 𝟙 G.left) (fun _ => 2)
  have pg : PGen (isoPullId wL (rfl : 𝟙 G.left = 𝟙 G.left)) := isoPullId_pgen hw rfl
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 G := lift 1 (lift 1 1)
  have he : e.left ≫ (snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have PM := pmaps_of_section pg hL hL' (φ' := thφ G (x3 G)) (φ := thφ G (x3 G)) (ε := thε)
    (sqGen U'.cubG.t) (sqGen_isGen U'.cubG.isGen) (sqGen U.cubG.t) (sqGen_isGen U.cubG.isGen)
    (fun _ => Category.comp_id _) _ e.left he sj fun y J J' hJ hJ' => by
      refine (val_sqGen _ hJ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_sqGen _ hJ' _)).symm)
      have c₁ : val U.cubG.t e.left y (fun ψ => J ψ 0) = 1 := (isCub_cubV U.cubG (good_sq hJ)).face 1 1
      have c₂ : val U'.cubG.t e.left y (fun ψ => J' ψ 0) = 1 := (isCub_cubV U'.cubG (good_sq hJ')).face 1 1
      have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G) 1 1
        (fun q => gw (isoPullId wL (rfl : 𝟙 G.left = 𝟙 G.left)) q y (J (q ≫ 𝟙 _)) (J' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine (congrArg (· ^ 2) c₁).trans (Eq.trans ?_ (congrArg₂ (· * ·) p (congrArg (· ^ 2) c₂)).symm)
      simp
  have hp : ∀ k, (r ≫ thφ G (x3 G) k) z ∈ (sqLB U.LG.L).U (fun _ => N (r ≫ thφ G (x3 G) k)) :=
    fun k => mem_sq.2 (hN _)
  have hq : ∀ k, (r ≫ thφ G (x3 G) k) z ∈ (sqLB U'.LG.L).U (fun _ => N' (r ≫ thφ G (x3 G) k)) :=
    fun k => mem_sq.2 (hN' _)
  have v := PM Z r z (fun k _ => N (r ≫ thφ G (x3 G) k)) (fun k _ => N' (r ≫ thφ G (x3 G) k)) hp hq
  rw [Category.comp_id] at v
  refine (gm_sqGen U.cubG.t r z (fun k _ => N (r ≫ thφ G (x3 G) k)) (Set.mem_iInter.2 hp)).symm.trans
    (v.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_)
      (gm_sqGen U'.cubG.t r z (fun k _ => N' (r ≫ thφ G (x3 G) k)) (Set.mem_iInter.2 hq))))
  exact congrArg (· ^ thε k) (gw_isoPullId wL rfl _ z _ _ (hp k) (hq k))

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareIsoCarriesSquareCubicalStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_iso_carries_square_cubical : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 G).left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t r z N ^ 2 =
        (∏ k : thK.{0}, gv wL (r ≫ thφ G (x3 G) k) z (fun _ => N (r ≫ thφ G (x3 G) k))
          (fun _ => N' (r ≫ thφ G (x3 G) k)) ^ thε k) *
        val (L := U'.LG.L) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t r z N' ^ 2 := by
  first | exact @GlobalTheory.sq_iso_carries_sq_cube | exact GlobalTheory.sq_iso_carries_sq_cube | (intros; apply GlobalTheory.sq_iso_carries_sq_cube <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareComparisonTorusInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareComparisonTorusInvariant
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace TorusInvarianceSq

open TorusInvariance SqLevel

theorem sq_cube_alg {V K : Type} [CommGroup V] [Fintype K] (ε : K → ℤ) (W W' B a : K → V) (c c' : V)
    (hc : c ^ 2 = (∏ k, B k ^ ε k) * c' ^ 2) (h : ∀ k, a k * W' k ^ 2 = W k ^ 2 * B k) :
    ((∏ k, W k ^ ε k) * c) ^ 2 = (∏ k, a k ^ ε k) * ((∏ k, W' k ^ ε k) * c') ^ 2 := by
  have hk : ∏ k, ((W k ^ ε k) ^ 2 * B k ^ ε k) = ∏ k, (a k ^ ε k * (W' k ^ ε k) ^ 2) :=
    Finset.prod_congr rfl fun k _ => by
      have := congrArg (· ^ ε k) (h k)
      simp only [mul_zpow] at this
      have p : ∀ X : V, (X ^ ε k) ^ 2 = (X ^ 2) ^ ε k := fun X => by rw [sq, sq, mul_zpow]
      rw [p, p]
      exact this.symm
  calc ((∏ k, W k ^ ε k) * c) ^ 2 = (∏ k, (W k ^ ε k) ^ 2) * ((∏ k, B k ^ ε k) * c' ^ 2) := by
        rw [mul_pow, Finset.prod_pow, hc]
    _ = (∏ k, ((W k ^ ε k) ^ 2 * B k ^ ε k)) * c' ^ 2 := by
        rw [Finset.prod_mul_distrib, _root_.mul_assoc]
    _ = (∏ k, (a k ^ ε k * (W' k ^ ε k) ^ 2)) * c' ^ 2 := by rw [hk]
    _ = (∏ k, a k ^ ε k) * ((∏ k, W' k ^ ε k) * c') ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow, mul_pow, _root_.mul_assoc]

section Level

open WCub EvenPull

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] {e : ℕ}
variable {D D' : DegData R I} {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {U : UnifPre I D A G}
  {U' : UnifPre I D' A' G}
  (u : LB.Iso ((sqLB D'.toPre.P.L).pull (U'.gt e).pG.left) ((sqLB D.toPre.P.L).pull (U.gt e).pG.left))

def aVal {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
    (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι) (r : Z ⟶ (thickObj R I e G).left) : (Z.presheaf.stalk z)ˣ :=
  gw u r z (fun _ => J (r ≫ (U.gt e).pG.left)) (fun _ _ => J' (r ≫ (U'.gt e).pG.left))

variable {wL : LB.Iso (sqLB U'.LG.L) (sqLB U.LG.L)}
  (sq : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
    (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM →
    (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL →
    (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
    gw u r z (fun _ => jM) (fun _ _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 =
      gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG I e G).left) z (fun _ => jL) (fun _ => jL'))
include sq

theorem cube_aVal (hc : ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 G).left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t r z N ^ 2 =
        (∏ k : thK.{0}, gv wL (r ≫ thφ G (x3 G) k) z (fun _ => N (r ≫ thφ G (x3 G) k))
          (fun _ => N' (r ≫ thφ G (x3 G) k)) ^ thε k) *
        val (L := U'.LG.L) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t r z N' ^ 2)
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x : Fin 3 → (T ⟶ thickObj R I e G))
    {z : T.left} {J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L z J) (hJ' : Good D'.toPre.P.L z J') :
    val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        (tri (thick R I e) (U.gt e).pG x) z J ^ 2 =
      (∏ k : thK.{0}, aVal u z J J' (psum (thickObj R I e G) x k.down).left ^ thε k) *
        val (L := D'.toPre.P.L) (φ := thφ D'.toPre.P.A (x3 D'.toPre.P.A)) (ε := thε) D'.toPre.cub.t
          (tri (thick R I e) (U'.gt e).pG x) z J' ^ 2 := by
  choose N hN using fun χ : T.left ⟶ G.left => exists_chart U.LG.isLB (χ z)
  choose N' hN' using fun χ : T.left ⟶ G.left => exists_chart U'.LG.isLB (χ z)
  have f₃ := tri_thφ (thick R I e) (fstG I e G) x (𝟙 _) (Category.id_comp _).symm
  have e₁ := cube_val U x hJ hN
  have e₂ := cube_val U' x hJ' hN'
  have e₃ := hc _ (tri (thick R I e) (fstG I e G) x) z N N' hN hN'
  have e₄ : val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t (tri (thick R I e) (fstG I e G) x) z N ^ 2 =
      (∏ k : thK.{0}, gv wL ((psum (thickObj R I e G) x k.down).left ≫ (fstG I e G).left) z
        (fun _ => N ((psum (thickObj R I e G) x k.down).left ≫ (fstG I e G).left))
        (fun _ => N' ((psum (thickObj R I e G) x k.down).left ≫ (fstG I e G).left)) ^ thε k) *
      val (L := U'.LG.L) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t (tri (thick R I e) (fstG I e G) x) z N' ^ 2 :=
    e₃.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => by rw [f₃ k]) rfl)
  rw [e₁, e₂]
  exact sq_cube_alg thε _ _ _ _ _ _ e₄ fun k => sq _ _ z _ _ _ _ (hJ _) (hJ' _) (hN _) (hN' _)

theorem even_aVal (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U.symG r z N ^ 2 =
        (∏ k : Fin 2, gv wL (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k) z
          (fun _ => N (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k))
          (fun _ => N' (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
        val (L := U'.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U'.symG r z N' ^ 2)
    {Z : Scheme.{0}} (r : Z ⟶ (thickObj R I e G).left) {z : Z}
    {J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι} {J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L z J) (hJ' : Good D'.toPre.P.L z J') :
    val D.toPre.sym (r ≫ (U.gt e).pG.left) z J ^ 2 * aVal u z J J' r =
      aVal u z J J' (r ≫ (ι[thickObj R I e G]).left) * val D'.toPre.sym (r ≫ (U'.gt e).pG.left) z J' ^ 2 := by
  choose N hN using fun χ : Z ⟶ G.left => exists_chart U.LG.isLB (χ z)
  choose N' hN' using fun χ : Z ⟶ G.left => exists_chart U'.LG.isLB (χ z)
  have iF : (ι[thickObj R I e G]).left ≫ (fstG I e G).left = (fstG I e G).left ≫ (ι[G]).left := inv_fst _ G
  have e₁ := even_val U r hJ hN
  have e₂ := even_val U' r hJ' hN'
  have e₃ := hs _ (r ≫ (fstG I e G).left) z N N' hN hN'
  rw [Fin.prod_univ_two] at e₃
  let d := fun s : Z ⟶ G.left => gv wL s z (fun _ => N s) (fun _ => N' s)
  have e₄ : val U.symG (r ≫ (fstG I e G).left) z N ^ 2 =
      d ((r ≫ (ι[thickObj R I e G]).left) ≫ (fstG I e G).left) * (d (r ≫ (fstG I e G).left))⁻¹ *
        val U'.symG (r ≫ (fstG I e G).left) z N' ^ 2 := by
    refine e₃.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) ((zpow_one _).trans (congrArg d ?_))
      ((zpow_neg_one _).trans (congrArg (fun s => (d s)⁻¹) (Category.comp_id _)))) rfl)
    rw [Category.assoc r (ι[thickObj R I e G]).left, iF, Category.assoc]; rfl
  have e₅ : ∀ s : Z ⟶ (thickObj R I e G).left, aVal u z J J' s * wVal U' e z J' N' s ^ 2 =
      wVal U e z J N s ^ 2 * d (s ≫ (fstG I e G).left) := fun s => sq _ s z _ _ _ _ (hJ _) (hJ' _) (hN _) (hN' _)
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  have a₄ := congrArg Additive.ofMul e₄
  have a₅ := congrArg Additive.ofMul (e₅ r)
  have a₆ := congrArg Additive.ofMul (e₅ (r ≫ (ι[thickObj R I e G]).left))
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at a₁ a₂ a₄ a₅ a₆ ⊢
  linear_combination (norm := abel) 2 • a₁ - 2 • a₂ + a₄ + a₅ - a₆

end Level

end TorusInvarianceSq


open ReciprocityTheory.ChartRestriction.G.DVR TorusInvariance TorusInvarianceSq SqLevel in
set_option maxHeartbeats 400000 in
theorem comparison_sq_torus_invariant : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 G).left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t r z N ^ 2 =
        (∏ k : thK.{0}, gv wL (r ≫ thφ G (x3 G) k) z (fun _ => N (r ≫ thφ G (x3 G) k))
          (fun _ => N' (r ≫ thφ G (x3 G) k)) ^ thε k) *
        val (L := U'.LG.L) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t r z N' ^ 2) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U.symG r z N ^ 2 =
        (∏ k : Fin 2, gv wL (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k) z
          (fun _ => N (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k))
          (fun _ => N' (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
        val (L := U'.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U'.symG r z N' ^ 2) →
    ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom →
    (U'.gt e).q ≫ β.hom = (U.gt e).q →
    ∀ u : LB.Iso ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull (U'.gt e).pG.left)
      ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull (U.gt e).pG.left), u.IsGen →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
      (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
      gw u r z (fun _ => jM) (fun _ _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 =
        gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG I e G).left) z (fun _ => jL) (fun _ => jL')) →
    ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.toPre.X) (y : Z ⟶ thickObj R I e G)
      (z : Z.left) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι),
      (U.gt e).pG.left (y.left z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (y.left z) ∈ D'.toPre.P.L.U jM' →
      gw u ((τ ≫ (U.gt e).i) * y).left z (fun _ => jM) (fun _ _ => jM') = gw u y.left z (fun _ => jM) (fun _ _ => jM') := by
  intro _ R _ _ _ I _ D D' A A' G _ _ hG U U' wL _ hc hs e β _ hβ u hu sq Z₀ τ₀ y₀ z₀ jM jM' m m'
  have := (U.gt e).q_hom
  have := (U'.gt e).q_hom
  have := (U.gt e).i_hom
  have := hG.geomConnected
  have := connectedSpace_spec_quotient (I ^ (e + 1)) (Z₀.hom z₀)
  have : GeometricallyConnected (thickObj R I e G).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (thick R I e)))
  have : ConnectedSpace (thickObj R I e G).left :=
    GroupConn.connectedSpace_of_section (thickObj R I e G).hom (η : 𝟙_ _ ⟶ thickObj R I e G).left (Over.w _)
  have hq : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.toPre.X),
      (τ ≫ (U.gt e).i) ≫ (U.gt e).q = (1 : Z ⟶ thickObj R I e G) ≫ (U.gt e).q := fun τ => by
    rw [Category.assoc, (U.gt e).isKernel.w, MonObj.one_comp, ← Category.assoc, comp_toUnit, Hom.one_def]
  have hq' : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.toPre.X),
      (τ ≫ (U.gt e).i) ≫ (U'.gt e).q = (1 : Z ⟶ thickObj R I e G) ≫ (U'.gt e).q := fun τ => by
    rw [← cancel_mono β.hom, Category.assoc _ _ β.hom, Category.assoc _ _ β.hom, hβ]
    exact hq τ
  have hp : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.toPre.X)
      (y : Z ⟶ thickObj R I e G), ((τ ≫ (U.gt e).i) * y).left ≫ (U.gt e).pG.left = y.left ≫ (U.gt e).pG.left :=
    fun τ y => pG_congr _ (by rw [MonObj.mul_comp, hq, ← MonObj.mul_comp, _root_.one_mul])
  have hp' : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.toPre.X)
      (y : Z ⟶ thickObj R I e G), ((τ ≫ (U.gt e).i) * y).left ≫ (U'.gt e).pG.left = y.left ≫ (U'.gt e).pG.left :=
    fun τ y => pG_congr _ (by rw [MonObj.mul_comp, hq', ← MonObj.mul_comp, _root_.one_mul])
  obtain ⟨ρ, key⟩ := exists_ratio_translate (U.gt e).i (linComb_isLB _ D.toPre.P.isLB _ _)
    (linComb_isLB _ D'.toPre.P.isLB _ _) u hu (fun _ => hp) (fun _ => hp')
  have triv := ratio_eq_one (U.gt e).i ρ (fun Z z => by
    choose J hJ using fun χ : Z.left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ z)
    choose J' hJ' using fun χ : Z.left ⟶ D'.toPre.P.A.left => exists_chart D'.toPre.P.isLB (χ z)
    refine ⟨aVal u z J J', fun t y => ?_, fun t t' y => ?_, fun t => ?_⟩
    · rw [aVal, aVal, hp, hp']
      exact key Z t y z _ _ (mem_sq.2 (hJ _)) (mem_sq.2 (hJ' _))
    · have a := cube_aVal u sq hc ![t ≫ (U.gt e).i, t' ≫ (U.gt e).i, y] hJ hJ'
      have b := cube_aVal u sq hc ![1, 1, y] hJ hJ'
      rw [tri_congr (U.gt e) y (hq t) (hq t'), tri_congr (U'.gt e) y (hq' t) (hq' t')] at a
      exact mul_right_cancel (a.symm.trans b)
    · have a := even_aVal u sq hs (t ≫ (U.gt e).i).left hJ hJ'
      have b := even_aVal u sq hs (1 : Z ⟶ thickObj R I e G).left hJ hJ'
      rw [pG_congr (U.gt e) (hq t), pG_congr (U'.gt e) (hq' t)] at a
      exact cancel_even a b)
  rw [key Z₀ τ₀ y₀ z₀ (fun _ => jM) (fun _ => jM') (mem_sq.2 m) (mem_sq.2 m'), triv, map_one, _root_.one_mul]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareComparisonTorusInvariantStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_comparison_torus_invariant : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 G).left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t r z N ^ 2 =
        (∏ k : thK.{0}, gv wL (r ≫ thφ G (x3 G) k) z (fun _ => N (r ≫ thφ G (x3 G) k))
          (fun _ => N' (r ≫ thφ G (x3 G) k)) ^ thε k) *
        val (L := U'.LG.L) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t r z N' ^ 2) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U.symG r z N ^ 2 =
        (∏ k : Fin 2, gv wL (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k) z
          (fun _ => N (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k))
          (fun _ => N' (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
        val (L := U'.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U'.symG r z N' ^ 2) →
    ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom →
    (U'.gt e).q ≫ β.hom = (U.gt e).q →
    ∀ u : LB.Iso ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull (U'.gt e).pG.left)
      ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull (U.gt e).pG.left), u.IsGen →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
      (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
      gw u r z (fun _ => jM) (fun _ _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 =
        gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG I e G).left) z (fun _ => jL) (fun _ => jL')) →
    ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.toPre.X) (y : Z ⟶ thickObj R I e G)
      (z : Z.left) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι),
      (U.gt e).pG.left (y.left z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (y.left z) ∈ D'.toPre.P.L.U jM' →
      gw u ((τ ≫ (U.gt e).i) * y).left z (fun _ => jM) (fun _ _ => jM') = gw u y.left z (fun _ => jM) (fun _ _ => jM') := by
  first | exact @GlobalTheory.comparison_sq_torus_invariant | exact GlobalTheory.comparison_sq_torus_invariant | (intros; apply GlobalTheory.comparison_sq_torus_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationSquaresAgreeAtEachThickening
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory


open SqLevel in
set_option maxHeartbeats 400000 in
theorem polarisation_squares_agree_at_level : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      eSec G (r z) ∈ U.LG.L.U jL → eSec G (r z) ∈ U'.LG.L.U jL' →
      gm r z _ (U.LG.rig.s (fun _ => jL)) ^ 2 =
        gv wL (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z _ (U'.LG.rig.s (fun _ => jL')) ^ 2) →
    ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom →
    (U'.gt e).q ≫ β.hom = (U.gt e).q →
    ∃ v : LB.Iso ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
        (fstG I e D'.toPre.P.A).left)
      ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
        (β.hom.left ≫ (fstG I e D.toPre.P.A).left)), v.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
      (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
      gw v (r ≫ (U'.gt e).q.left) z (fun _ => jM) (fun _ => fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 =
        gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG I e G).left) z (fun _ => jL) (fun _ => jL') := by
  intro hG R _ _ _ I hI D D' A A' G _ _ hS U U' wL hwL hrig e β hβ hq
  have hM := DVR.linComb_isLB D.toPre.P.L D.toPre.P.isLB (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)
  have hM' := DVR.linComb_isLB D'.toPre.P.L D'.toPre.P.isLB (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)
  have hL := DVR.linComb_isLB U.LG.L U.LG.isLB (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)
  have hL' := DVR.linComb_isLB U'.LG.L U'.LG.isLB (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)
  have hwL' : (isoPullId wL (rfl : 𝟙 G.left = 𝟙 G.left)).IsGen := (isGen_iff _).2 (isoPullId_pgen hwL rfl)
  obtain ⟨u, hu, hu'⟩ := LevelComparison.exists_comparison hM hM' hL hL' (sqIso_isGen (U.w_gen e))
    (sqIso_isGen (U'.w_gen e)) hwL'
  have sqrel : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι)
      (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
      gw u r z (fun _ => jM) (fun _ _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 =
        gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG I e G).left) z (fun _ => jL) (fun _ => jL') := by
    intro Z r z jM jM' jL jL' a₁ a₂ a₃ a₄
    have h := hu' Z r z (fun _ => jM) (fun _ => jM') (fun _ => jL) (fun _ => jL') (mem_sq.2 a₁) (mem_sq.2 a₂)
      (mem_sq.2 a₃) (mem_sq.2 a₄)
    rw [gw_sqIso (U'.w e) r z (fun _ => jM') (fun _ _ => jL') a₂ a₄,
      gw_sqIso (U.w e) r z (fun _ => jM) (fun _ _ => jL) a₁ a₃,
      gw_isoPullId wL rfl _ z (fun _ => jL) (fun _ => jL') (mem_sq.2 a₃) (mem_sq.2 a₄)] at h
    exact h
  have inv := GlobalTheory.T.square_comparison_torus_invariant hG R I hI D D' A A' G hS U U' wL hwL (GlobalTheory.T.square_iso_carries_square_cubical hG R I hI D D' A A' G hS U U' wL hwL)
    (GlobalTheory.T.square_iso_respects_symmetry_pointwise hG R I hI D D' A A' G hS U U' wL hwL) e β hβ hq u hu sqrel
  haveI := (U'.gt e).q_flat
  haveI := (U'.gt e).q_surj
  haveI := (U'.gt e).q_affine
  haveI := (U.gt e).q_hom
  have hql : (U'.gt e).q.left ≫ β.hom.left = (U.gt e).q.left := congrArg (·.left) hq
  obtain ⟨v, hv, hv'⟩ := LevelComparison.exists_iso_descend (U'.gt e).q.left (fstG I e D'.toPre.P.A).left
    (β.hom.left ≫ (fstG I e D.toPre.P.A).left) (p := (U.gt e).pG.left) (p' := (U'.gt e).pG.left)
    (by rw [← Category.assoc, hql]; rfl) rfl u hu (fun Z g₁ g₂ z j j' h a b => by
      obtain ⟨a₀, rfl⟩ : ∃ a₀, j = fun _ => a₀ := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim k 0)⟩
      obtain ⟨b₀, rfl⟩ : ∃ b₀, j' = fun _ => b₀ := ⟨j' 0, funext fun k => congrArg j' (Subsingleton.elim k 0)⟩
      let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (g₂ ≫ (thickObj R I e G).hom)
      let k₂ : Z' ⟶ thickObj R I e G := Over.homMk g₂ rfl
      let k₁ : Z' ⟶ thickObj R I e G := Over.homMk g₁ (by
        change g₁ ≫ (thickObj R I e G).hom = g₂ ≫ (thickObj R I e G).hom
        rw [← Over.w (U'.gt e).q, reassoc_of% h])
      have e₁ : k₁ ≫ (U'.gt e).q = k₂ ≫ (U'.gt e).q := Over.OverMorphism.ext h
      have e' : k₁ ≫ (U.gt e).q = k₂ ≫ (U.gt e).q := by rw [← hq, reassoc_of% e₁]
      have w : (k₁ * k₂⁻¹) ≫ (U.gt e).q = toUnit Z' ≫ η[thickObj R I e D.toPre.P.A] := by
        rw [MonObj.mul_comp, GrpObj.inv_comp, e', mul_inv_cancel]
        rfl
      have ht : ((U.gt e).isKernel.lift _ _ w ≫ (U.gt e).i) * k₂ = k₁ := by
        rw [(U.gt e).isKernel.lift_fst, inv_mul_cancel_right]
      have := inv Z' ((U.gt e).isKernel.lift _ _ w) k₂ z a₀ b₀ (mem_sq.1 a) (mem_sq.1 b)
      rw [ht] at this
      exact this)
  refine ⟨v, hv, fun Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  rw [hv' Z r z (fun _ => jM) (fun _ => jM') (mem_sq.2 a₁) (mem_sq.2 a₂)]
  exact sqrel Z r z jM jM' jL jL' a₁ a₂ a₃ a₄

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationSquaresAgreeAtEachThickeningStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_squares_agree_at_each_thickening : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      eSec G (r z) ∈ U.LG.L.U jL → eSec G (r z) ∈ U'.LG.L.U jL' →
      gm r z _ (U.LG.rig.s (fun _ => jL)) ^ 2 =
        gv wL (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z _ (U'.LG.rig.s (fun _ => jL')) ^ 2) →
    ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom →
    (U'.gt e).q ≫ β.hom = (U.gt e).q →
    ∃ v : LB.Iso ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
        (fstG I e D'.toPre.P.A).left)
      ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
        (β.hom.left ≫ (fstG I e D.toPre.P.A).left)), v.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
      (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
      gw v (r ≫ (U'.gt e).q.left) z (fun _ => jM) (fun _ => fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 =
        gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG I e G).left) z (fun _ => jL) (fun _ => jL') := by
  first | exact @GlobalTheory.polarisation_squares_agree_at_level | exact GlobalTheory.polarisation_squares_agree_at_level | (intros; apply GlobalTheory.polarisation_squares_agree_at_level <;> assumption)
end
