module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIntegralOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemSpreadOfLevelFractionField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLtBinomialBoundOfMulPowLt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfAssociated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrFactorPointPadicAlgClosure

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPrincipalPolarisationExtendsSemiAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenUnitMulSq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SquareNear

theorem stalk_props : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ x : G₁.left, IsDomain (G₁.left.presheaf.stalk x) ∧ IsNoetherianRing (G₁.left.presheaf.stalk x) ∧ IsIntegrallyClosed (G₁.left.presheaf.stalk x) := by
  intro R' _ _ _ hA G₁ _ _ hG x
  obtain ⟨_, -, _, -⟩ := hA
  haveI := hG.smooth
  have hS : GlobalTheory.IsNormalScheme (Sp R') := inferInstance
  have h := GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth G₁.hom
    ((GlobalTheory.isNormalScheme_iff _).mp hS) x
  haveI : IsLocallyNoetherian G₁.left := LocallyOfFiniteType.isLocallyNoetherian G₁.hom
  exact ⟨h.1, inferInstance, h.2⟩

end GlobalTheory.SquareNear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPolarisationClassGenericDiagonalDoubling
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPolarisationClassGenericDiagonalDoubling
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DiagPic

open GlobalTheory.CechPic

theorem pull_inv {K : Type} [Field K] (A : PolAV (Sp K)) :
    pull (GrpObj.inv : A.A ⟶ A.A).left (cls A.L A.isLB) = cls A.L A.isLB := by
  obtain ⟨U, hU, ht⟩ := A.sym (default : PrimeSpectrum K)
  have h := (cls_eq_zero_iff (LB.isLB_linComb A.isLB _ _)).2 ht
  rw [cls_linComb A.isLB, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, add_neg_eq_zero] at h
  have hr : Set.range (𝟙 A.A.left : A.A.left ⟶ A.A.left) ⊆ Set.range (A.A.hom ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    intro x _
    have e : A.A.hom x = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    show A.A.hom x ∈ U
    rw [e]
    exact hU
  have h' := congrArg (pull (IsOpenImmersion.lift (A.A.hom ⁻¹ᵁ U).ι (𝟙 _) hr)) h
  rwa [← pull_comp, ← pull_comp, IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac, Category.id_comp,
    pull_id] at h'

theorem pull_one {S : Scheme.{0}} (A : PolAV S) {T : Over S} :
    pull (1 : T ⟶ A.A).left (cls A.L A.isLB) = 0 := by
  have h := (cls_eq_zero_iff (pull_isLB A.isLB _)).2 A.rigid
  rw [cls_pull A.isLB] at h
  rw [Hom.one_def, Over.comp_left, pull_comp]
  exact (congrArg _ h).trans (map_zero _)

theorem lam_self {K : Type} [Field K] (A : PolAV (Sp K)) :
    lam (cls A.L A.isLB) (𝟙 A.A) (𝟙 A.A) = 2 • cls A.L A.isLB := by
  have h := lam_mul_left A.isLB (GlobalTheory.Moduli.cube_of_isLB _ A A.L A.isLB) (𝟙 A.A) (𝟙 A.A)⁻¹ (𝟙 A.A)
  rw [mul_inv_cancel, lam_one_left] at h
  have e : lam (cls A.L A.isLB) (𝟙 A.A)⁻¹ (𝟙 A.A) = -(2 • cls A.L A.isLB) := by
    rw [lam, inv_mul_cancel, pull_one, Hom.inv_def, Category.id_comp, pull_inv, Over.id_left, pull_id]
    abel
  rw [e] at h
  exact (add_neg_eq_zero.1 h.symm)

theorem pull_sq {K : Type} [Field K] (A : PolAV (Sp K)) :
    pull ((𝟙 A.A) ^ 2 : A.A ⟶ A.A).left (cls A.L A.isLB) = 4 • cls A.L A.isLB := by
  have h := lam_self A
  rw [lam, pull_one, Over.id_left, pull_id, add_zero, sub_sub, sub_eq_iff_eq_add] at h
  rw [pow_two, h]
  abel

end GlobalTheory.Mum.DiagPic

namespace GlobalTheory.Mum

open GlobalTheory.CechPic

theorem two_smul_cls_eq_pull_diag_and_pull_sq : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (c : GlobalTheory.CechPic.Pic (pullback G.hom (jK R))) (d : GlobalTheory.CechPic.Pic G.left) (hL : (A.L.pull gen.hom.left).IsLB) (hP : (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left).IsLB), c = GlobalTheory.CechPic.cls (A.L.pull gen.hom.left) hL → d = GlobalTheory.CechPic.cls (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left) hP → 2 • c = GlobalTheory.CechPic.pull (pullback.fst G.hom (jK R)) d ∧ ∃ φ : pullback G.hom (jK R) ⟶ pullback G.hom (jK R), φ ≫ pullback.fst G.hom (jK R) = pullback.fst G.hom (jK R) ≫ ((𝟙 G) ^ 2 : G ⟶ G).left ∧ GlobalTheory.CechPic.pull φ c = 4 • c := by
  intro R _ _ G _ _ A gen hgen PP hExt c d hL hP hc hd
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have hc' : c = pull gen.hom.left (cls A.L A.isLB) := hc
  refine ⟨?_, ((𝟙 ((Over.pullback (jK R)).obj G)) ^ 2 : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left, ?_, ?_⟩
  · obtain ⟨g₂, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _
      (isGrpPullback_pullback G (jK R))
    have h₁ := (cls_eq_iff (LB.isLB_linComb hL _ _) (pull_isLB hExt.1 g₂)).2 (hExt.2 g₂ hg₂)
    have h₂ := (cls_cube_two hL (fst _ _) (snd _ _) (LB.isLB_linComb hL _ _)).symm.trans h₁
    have h₃ := congrArg (pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G))).left) h₂
    have e : (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G))).left ≫ g₂ =
        pullback.fst G.hom (jK R) ≫ (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left := by
      apply pullback.hom_ext
      · show (_ ≫ g₂) ≫ (fst G G).left = (_ ≫ _) ≫ (fst G G).left
        rw [Category.assoc, hg₂.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
          lift_fst, Over.id_left, Over.id_left]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
      · show (_ ≫ g₂) ≫ (snd G G).left = (_ ≫ _) ≫ (snd G G).left
        rw [Category.assoc, hg₂.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
          lift_snd, Over.id_left, Over.id_left]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
    rw [pull_lam, lift_fst, lift_snd, cls_pull hExt.1, ← pull_comp, e, pull_comp, cls_pull A.isLB, lam_pull,
      Category.id_comp] at h₃
    have h₄ := pull_lam gen.hom (cls A.L A.isLB) (𝟙 _) (𝟙 _)
    rw [Category.comp_id, DiagPic.lam_self, map_nsmul] at h₄
    rw [hc', hd]
    exact h₄.trans h₃
  · have e : ((𝟙 ((Over.pullback (jK R)).obj G)) ^ 2 : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G) = (Over.pullback (jK R)).map ((𝟙 G) ^ 2) := by
      rw [pow_two, pow_two, Functor.map_mul, CategoryTheory.Functor.map_id]
    rw [e]
    exact pullback.lift_fst _ _ _
  · have e : ((𝟙 ((Over.pullback (jK R)).obj G)) ^ 2 : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G) ≫ gen.hom = gen.hom ≫ (𝟙 A.A) ^ 2 := by
      rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
    have h := congrArg (pull gen.hom.left) (DiagPic.pull_sq A)
    rw [← pull_comp, ← Over.comp_left, ← e, Over.comp_left, pull_comp, map_nsmul] at h
    rw [hc']
    exact h

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPolarisationClassGenericDiagonalDoublingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_smul_polarisation_class_generic_diagonal_doubling : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (c : GlobalTheory.CechPic.Pic (pullback G.hom (jK R))) (d : GlobalTheory.CechPic.Pic G.left) (hL : (A.L.pull gen.hom.left).IsLB) (hP : (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left).IsLB), c = GlobalTheory.CechPic.cls (A.L.pull gen.hom.left) hL → d = GlobalTheory.CechPic.cls (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left) hP → 2 • c = GlobalTheory.CechPic.pull (pullback.fst G.hom (jK R)) d ∧ ∃ φ : pullback G.hom (jK R) ⟶ pullback G.hom (jK R), φ ≫ pullback.fst G.hom (jK R) = pullback.fst G.hom (jK R) ≫ ((𝟙 G) ^ 2 : G ⟶ G).left ∧ GlobalTheory.CechPic.pull φ c = 4 • c := by
  first | exact @GlobalTheory.Mum.two_smul_cls_eq_pull_diag_and_pull_sq | exact GlobalTheory.Mum.two_smul_cls_eq_pull_diag_and_pull_sq | (intros; apply GlobalTheory.Mum.two_smul_cls_eq_pull_diag_and_pull_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfInfLeInfRight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.LocalEqGlue

noncomputable section

open TopologicalSpace Opposite

variable {X Y Z : Scheme.{0}}

theorem resU_resU {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (x : Γ(X, U)ˣ) :
    res k (res h x) = res (k.trans h) x := by
  ext
  change (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE k).op).hom x.val = _
  rw [← X.presheaf.map_comp]
  rfl

theorem resU_pullU_resU (f : Y ⟶ X) {U V : X.Opens} (k : V ≤ U) {W : Y.Opens}
    (h : W ≤ f ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    res h (pullU f V (res k x)) = res (h.trans (f.preimage_mono k)) (pullU f U x) := by
  ext
  change (X.presheaf.map (homOfLE k).op ≫ f.appLE V W h).hom x.val = (f.appLE U W _).hom x.val
  rw [Scheme.Hom.map_appLE]

theorem resU_pullU_congr {m m' : Y ⟶ X} (e : m = m') (U : X.Opens) {W : Y.Opens}
    (h : W ≤ m ⁻¹ᵁ U) (h' : W ≤ m' ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU m U x) = res h' (pullU m' U x) := by
  subst e
  rfl

theorem resU_pullU_square {P : Scheme.{0}} {g : Z ⟶ Y} {f : Y ⟶ X} {g' : Z ⟶ P} {f' : P ⟶ X}
    (e : g ≫ f = g' ≫ f') (U : X.Opens) {W : Z.Opens} (h : W ≤ g ⁻¹ᵁ f ⁻¹ᵁ U)
    (h' : W ≤ g' ⁻¹ᵁ f' ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU g _ (pullU f U x)) = res h' (pullU g' _ (pullU f' U x)) := by
  exact resU_pullU_congr e U h h' x

theorem rs_rs {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE k).op).hom ((X.presheaf.map (homOfLE h).op).hom x) =
      (X.presheaf.map (homOfLE (k.trans h)).op).hom x := by
  change (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE k).op).hom x = _
  rw [← X.presheaf.map_comp]
  rfl

theorem rs_app (f : Y ⟶ X) (U : X.Opens) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (x : Γ(X, U)) :
    (Y.presheaf.map (homOfLE h).op).hom ((f.app U).hom x) = (f.appLE U W h).hom x := rfl

theorem appLE_rs (f : Y ⟶ X) {U V : X.Opens} (k : V ≤ U) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ V)
    (x : Γ(X, U)) :
    (f.appLE V W h).hom ((X.presheaf.map (homOfLE k).op).hom x) =
      (f.appLE U W (h.trans (f.preimage_mono k))).hom x := by
  change (X.presheaf.map (homOfLE k).op ≫ f.appLE V W h).hom x = _
  rw [Scheme.Hom.map_appLE]

theorem rs_appLE (f : Y ⟶ X) (U : X.Opens) {V W : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) (k : W ≤ V)
    (x : Γ(X, U)) :
    (Y.presheaf.map (homOfLE k).op).hom ((f.appLE U V h).hom x) =
      (f.appLE U W (k.trans h)).hom x := by
  change (f.appLE U V h ≫ Y.presheaf.map (homOfLE k).op).hom x = _
  rw [Scheme.Hom.appLE_map]

theorem inf_inf_le_inf_left (A B C D : X.Opens) : (A ⊓ B) ⊓ (C ⊓ D) ≤ A ⊓ C :=
  fun _ hx => ⟨hx.1.1, hx.2.1⟩

theorem inf_inf_le_inf_right (A B C D : X.Opens) : (A ⊓ B) ⊓ (C ⊓ D) ≤ B ⊓ D :=
  fun _ hx => ⟨hx.1.2, hx.2.2⟩

theorem inf_preimage_le (f : Y ⟶ X) (A B : X.Opens) : f ⁻¹ᵁ A ⊓ f ⁻¹ᵁ B ≤ f ⁻¹ᵁ (A ⊓ B) :=
  fun _ hx => hx

theorem pull_g_eq (L : LB X) (f : Y ⟶ X) (i i' : (L.pull f).ι) :
    (L.pull f).g i i' = res (le_inf ((inf_le_left.trans (LB.wchart_le L (fun _ => f) i PUnit.unit)))
      (inf_le_right.trans (LB.wchart_le L (fun _ => f) i' PUnit.unit)))
      (pullU f _ (L.g (i PUnit.unit) (i' PUnit.unit))) := by
  exact (Fintype.prod_unique (fun _ : PUnit => _)).trans (zpow_one _)

theorem cancel_nzd {R : Type} [CommRing R] {x y r : R} (hr : r ∈ nonZeroDivisors R)
    (h : x * r = y * r) : x = y :=
  (mul_cancel_right_mem_nonZeroDivisors hr).mp h

theorem exists_lb_of_localEq : ∀ (X Y : Scheme.{0}) (j : Y ⟶ X) (L : LB Y) (θ : L.Sec) (Ix : Type) (V : Ix → X.Opens) (a : ∀ k, Γ(X, V k)), (∀ k (W : X.Opens) (hW : W ≤ V k), (X.presheaf.map (homOfLE hW).op).hom (a k) ∈ nonZeroDivisors Γ(X, W)) → (∀ k (W : Y.Opens) (hW : W ≤ j ⁻¹ᵁ V k), (Y.presheaf.map (homOfLE hW).op).hom ((j.app (V k)).hom (a k)) ∈ nonZeroDivisors Γ(Y, W)) → (∀ k l, ∃ c : Γ(X, V k ⊓ V l)ˣ, (X.presheaf.map (homOfLE inf_le_left).op).hom (a k) = (c : Γ(X, V k ⊓ V l)) * (X.presheaf.map (homOfLE inf_le_right).op).hom (a l)) → (∀ k i, ∃ w : Γ(Y, j ⁻¹ᵁ V k ⊓ L.U i)ˣ, (Y.presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) = (w : Γ(Y, j ⁻¹ᵁ V k ⊓ L.U i)) * (Y.presheaf.map (homOfLE inf_le_left).op).hom ((j.app (V k)).hom (a k))) → ∃ (O : X.Opens) (N : LB O.toScheme), (∀ k, V k ≤ O) ∧ N.IsLB ∧ LBIso (N.pull (pullback.fst O.ι j)) (L.pull (pullback.snd O.ι j)) := by
  intro X Y j L θ Ix V a ha hb hc hw
  choose c hc using hc
  choose w hw using hw
  have c_self : ∀ k, c k k = 1 := by
    intro k
    apply Units.ext
    have h' : (c k k : Γ(X, V k ⊓ V k)) *
        (X.presheaf.map (homOfLE (inf_le_left : V k ⊓ V k ≤ V k)).op).hom (a k) =
        1 * (X.presheaf.map (homOfLE (inf_le_left : V k ⊓ V k ≤ V k)).op).hom (a k) := by
      rw [_root_.one_mul]; exact (hc k k).symm
    exact cancel_nzd (ha k (V k ⊓ V k) inf_le_left) h'
  have c_cocycle : ∀ k l m,
      res (inf_le_left : V k ⊓ V l ⊓ V m ≤ V k ⊓ V l) (c k l) *
        res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          V k ⊓ V l ⊓ V m ≤ V l ⊓ V m) (c l m) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          V k ⊓ V l ⊓ V m ≤ V k ⊓ V m) (c k m) := by
    intro k l m
    apply Units.ext
    have e1 := congrArg (X.presheaf.map (homOfLE
      (inf_le_left : V k ⊓ V l ⊓ V m ≤ V k ⊓ V l)).op).hom (hc k l)
    have e2 := congrArg (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          V k ⊓ V l ⊓ V m ≤ V l ⊓ V m)).op).hom (hc l m)
    have e3 := congrArg (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          V k ⊓ V l ⊓ V m ≤ V k ⊓ V m)).op).hom (hc k m)
    simp only [map_mul, rs_rs] at e1 e2 e3
    apply cancel_nzd (ha m (V k ⊓ V l ⊓ V m) inf_le_right)
    simp only [res, Units.coe_map, MonoidHom.coe_coe, Units.val_mul]
    rw [_root_.mul_assoc, ← e2, ← e1, e3]
  have Y1 : ∀ k l i i',
      res (inf_inf_le_inf_left (j ⁻¹ᵁ V k) (j ⁻¹ᵁ V l) (L.U i) (L.U i')) (w k i) =
        res (inf_le_right : (j ⁻¹ᵁ V k ⊓ j ⁻¹ᵁ V l) ⊓ (L.U i ⊓ L.U i') ≤ L.U i ⊓ L.U i')
          (L.g i i') *
        (res ((inf_le_left : (j ⁻¹ᵁ V k ⊓ j ⁻¹ᵁ V l) ⊓ (L.U i ⊓ L.U i') ≤ _).trans
          (inf_preimage_le j (V k) (V l))) (pullU j _ (c k l)))⁻¹ *
        res (inf_inf_le_inf_right (j ⁻¹ᵁ V k) (j ⁻¹ᵁ V l) (L.U i) (L.U i')) (w l i') := by
    intro k l i i'
    have hWl : (j ⁻¹ᵁ V k ⊓ j ⁻¹ᵁ V l) ⊓ (L.U i ⊓ L.U i') ≤ j ⁻¹ᵁ V l := fun _ hx => hx.1.2
    have hWkl : (j ⁻¹ᵁ V k ⊓ j ⁻¹ᵁ V l) ⊓ (L.U i ⊓ L.U i') ≤ j ⁻¹ᵁ (V k ⊓ V l) := fun _ hx => hx.1
    have hW1 : (j ⁻¹ᵁ V k ⊓ j ⁻¹ᵁ V l) ⊓ (L.U i ⊓ L.U i') ≤ j ⁻¹ᵁ V k ⊓ L.U i :=
      fun _ hx => ⟨hx.1.1, hx.2.1⟩
    have hW2 : (j ⁻¹ᵁ V k ⊓ j ⁻¹ᵁ V l) ⊓ (L.U i ⊓ L.U i') ≤ j ⁻¹ᵁ V l ⊓ L.U i' :=
      fun _ hx => ⟨hx.1.2, hx.2.2⟩
    have hW3 : (j ⁻¹ᵁ V k ⊓ j ⁻¹ᵁ V l) ⊓ (L.U i ⊓ L.U i') ≤ L.U i ⊓ L.U i' := fun _ hx => hx.2
    have f1 := congrArg (Y.presheaf.map (homOfLE hW1).op).hom (hw k i)
    have f2 := congrArg (Y.presheaf.map (homOfLE hW2).op).hom (hw l i')
    have f3 := congrArg (Y.presheaf.map (homOfLE hW3).op).hom (θ.compat i i')
    have f4 := congrArg (j.appLE (V k ⊓ V l) _ hWkl).hom (hc k l)
    simp only [map_mul, rs_rs, rs_app, appLE_rs, rs_appLE] at f1 f2 f3 f4
    have Y1e : (Y.presheaf.map (homOfLE hW1).op).hom (w k i : Γ(Y, j ⁻¹ᵁ V k ⊓ L.U i)) *
        (j.appLE (V k ⊓ V l) _ hWkl).hom (c k l : Γ(X, V k ⊓ V l)) =
        (Y.presheaf.map (homOfLE hW3).op).hom (L.g i i' : Γ(Y, L.U i ⊓ L.U i')) *
        (Y.presheaf.map (homOfLE hW2).op).hom (w l i' : Γ(Y, j ⁻¹ᵁ V l ⊓ L.U i')) := by
      apply cancel_nzd (hb l _ hWl)
      simp only [rs_app]
      rw [_root_.mul_assoc, ← f4, ← f1, f3, f2, _root_.mul_assoc]
    rw [mul_right_comm, eq_mul_inv_iff_mul_eq]
    exact Units.ext Y1e
  let O : X.Opens := ⨆ k, V k
  have hVO : ∀ k, V k ≤ O := fun k => le_iSup V k
  have hinf3 : ∀ A B C : X.Opens,
      O.ι ⁻¹ᵁ A ⊓ O.ι ⁻¹ᵁ B ⊓ O.ι ⁻¹ᵁ C ≤ O.ι ⁻¹ᵁ (A ⊓ B ⊓ C) := fun _ _ _ _ hx => hx
  let N : LB O.toScheme := LB.mk Ix (fun k => O.ι ⁻¹ᵁ V k)
    (fun k l => res (inf_preimage_le O.ι (V k) (V l))
      (pullU O.ι _ (c k l)))
  have hN : N.IsLB := by
    refine ⟨?_, ?_, ?_⟩
    · refine eq_top_iff.mpr fun x _ => ?_
      have hx : O.ι x ∈ O := by
        first
          | exact x.2
          | exact (Scheme.Opens.range_ι O).le ⟨x, rfl⟩
          | simp [Scheme.Opens.ι_apply]
      rw [TopologicalSpace.Opens.mem_iSup] at hx ⊢
      exact hx
    · intro k
      show res _ (res _ (pullU O.ι _ (c k k))) = 1
      rw [c_self, map_one, map_one, map_one]
    · intro k l m
      show res _ (res _ (pullU O.ι _ (c k l))) * res _ (res _ (pullU O.ι _ (c l m))) =
        res _ (res _ (pullU O.ι _ (c k m)))
      have := congrArg (fun u => res (hinf3 (V k) (V l) (V m)) (pullU O.ι _ u))
        (c_cocycle k l m)
      simp only [map_mul, resU_pullU_resU] at this
      simp only [resU_resU]
      exact this
  refine ⟨O, N, hVO, hN, ?_⟩
  have hsq : pullback.fst O.ι j ≫ O.ι = pullback.snd O.ι j ≫ j := pullback.condition
  have hpt : ∀ x, O.ι.base ((pullback.fst O.ι j).base x) = j.base ((pullback.snd O.ι j).base x) :=
    fun x => by
      have := congrArg (fun f : pullback O.ι j ⟶ X => f.base x) hsq
      simpa using this
  have hle : ∀ p : (PUnit → L.ι) × (PUnit → Ix),
      (L.pull (pullback.snd O.ι j)).U p.1 ⊓ (N.pull (pullback.fst O.ι j)).U p.2 ≤
        pullback.snd O.ι j ⁻¹ᵁ (j ⁻¹ᵁ V (p.2 PUnit.unit) ⊓ L.U (p.1 PUnit.unit)) := by
    intro p x hx
    have h1 := LB.wchart_le L (fun _ => pullback.snd O.ι j) p.1 PUnit.unit hx.1
    have h2 := LB.wchart_le N (fun _ => pullback.fst O.ι j) p.2 PUnit.unit hx.2
    refine ⟨?_, h1⟩
    show j.base ((pullback.snd O.ι j).base x) ∈ V (p.2 PUnit.unit)
    rw [← hpt]
    exact h2
  let w' : LB.Iso (N.pull (pullback.fst O.ι j)) (L.pull (pullback.snd O.ι j)) :=
    ⟨fun p => res (hle p) (pullU (pullback.snd O.ι j) _ (w (p.2 PUnit.unit) (p.1 PUnit.unit)))⟩
  refine ⟨w', fun p q => ?_⟩
  have hQ : (LB.div (L.pull (pullback.snd O.ι j)) (N.pull (pullback.fst O.ι j))).U p ⊓
      (LB.div (L.pull (pullback.snd O.ι j)) (N.pull (pullback.fst O.ι j))).U q ≤
      pullback.snd O.ι j ⁻¹ᵁ ((j ⁻¹ᵁ V (p.2 PUnit.unit) ⊓ j ⁻¹ᵁ V (q.2 PUnit.unit)) ⊓
        (L.U (p.1 PUnit.unit) ⊓ L.U (q.1 PUnit.unit))) := fun x hx =>
    ⟨⟨(hle p hx.1).1, (hle q hx.2).1⟩, ⟨(hle p hx.1).2, (hle q hx.2).2⟩⟩
  have hQc : (LB.div (L.pull (pullback.snd O.ι j)) (N.pull (pullback.fst O.ι j))).U p ⊓
      (LB.div (L.pull (pullback.snd O.ι j)) (N.pull (pullback.fst O.ι j))).U q ≤
      pullback.fst O.ι j ⁻¹ᵁ O.ι ⁻¹ᵁ (V (p.2 PUnit.unit) ⊓ V (q.2 PUnit.unit)) := fun x hx =>
    ⟨LB.wchart_le N (fun _ => pullback.fst O.ι j) p.2 PUnit.unit hx.1.2,
      LB.wchart_le N (fun _ => pullback.fst O.ι j) q.2 PUnit.unit hx.2.2⟩
  have key := congrArg (fun u => res hQ (pullU (pullback.snd O.ι j) _ u))
    (Y1 (p.2 PUnit.unit) (q.2 PUnit.unit) (p.1 PUnit.unit) (q.1 PUnit.unit))
  simp only [map_mul, map_inv, resU_pullU_resU] at key
  rw [resU_pullU_square hsq.symm _ _ hQc] at key
  have goal' : res (inf_le_left : ((L.pull (pullback.snd O.ι j)).U p.1 ⊓ (N.pull (pullback.fst O.ι j)).U p.2) ⊓
        ((L.pull (pullback.snd O.ι j)).U q.1 ⊓ (N.pull (pullback.fst O.ι j)).U q.2) ≤ _)
        (res (hle p) (pullU (pullback.snd O.ι j) _ (w (p.2 PUnit.unit) (p.1 PUnit.unit)))) =
      (res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          ((L.pull (pullback.snd O.ι j)).U p.1 ⊓ (N.pull (pullback.fst O.ι j)).U p.2) ⊓
          ((L.pull (pullback.snd O.ι j)).U q.1 ⊓ (N.pull (pullback.fst O.ι j)).U q.2) ≤ _)
          ((L.pull (pullback.snd O.ι j)).g p.1 q.1) *
        (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          ((L.pull (pullback.snd O.ι j)).U p.1 ⊓ (N.pull (pullback.fst O.ι j)).U p.2) ⊓
          ((L.pull (pullback.snd O.ι j)).U q.1 ⊓ (N.pull (pullback.fst O.ι j)).U q.2) ≤ _)
          ((N.pull (pullback.fst O.ι j)).g p.2 q.2))⁻¹) *
      res (inf_le_right : ((L.pull (pullback.snd O.ι j)).U p.1 ⊓ (N.pull (pullback.fst O.ι j)).U p.2) ⊓
        ((L.pull (pullback.snd O.ι j)).U q.1 ⊓ (N.pull (pullback.fst O.ι j)).U q.2) ≤ _)
        (res (hle q) (pullU (pullback.snd O.ι j) _ (w (q.2 PUnit.unit) (q.1 PUnit.unit)))) := by
    have eL : res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          ((L.pull (pullback.snd O.ι j)).U p.1 ⊓ (N.pull (pullback.fst O.ι j)).U p.2) ⊓
          ((L.pull (pullback.snd O.ι j)).U q.1 ⊓ (N.pull (pullback.fst O.ι j)).U q.2) ≤ _)
          ((L.pull (pullback.snd O.ι j)).g p.1 q.1) =
        res (hQ.trans ((pullback.snd O.ι j).preimage_mono inf_le_right))
          (pullU (pullback.snd O.ι j) _ (L.g (p.1 PUnit.unit) (q.1 PUnit.unit))) := by
      rw [pull_g_eq]
      exact resU_resU _ _ _
    have eN : res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          ((L.pull (pullback.snd O.ι j)).U p.1 ⊓ (N.pull (pullback.fst O.ι j)).U p.2) ⊓
          ((L.pull (pullback.snd O.ι j)).U q.1 ⊓ (N.pull (pullback.fst O.ι j)).U q.2) ≤ _)
          ((N.pull (pullback.fst O.ι j)).g p.2 q.2) =
        res hQc (pullU (pullback.fst O.ι j) _
          (pullU O.ι _ (c (p.2 PUnit.unit) (q.2 PUnit.unit)))) := by
      rw [pull_g_eq, show N.g (p.2 PUnit.unit) (q.2 PUnit.unit) =
        res (inf_preimage_le O.ι (V (p.2 PUnit.unit)) (V (q.2 PUnit.unit)))
          (pullU O.ι _ (c (p.2 PUnit.unit) (q.2 PUnit.unit))) from rfl]
      refine (resU_resU _ _ _).trans ?_
      exact resU_pullU_resU (pullback.fst O.ι j) (inf_preimage_le O.ι _ _) _ _
    rw [eL, eN, resU_resU, resU_resU]
    exact key
  exact goal'

end

end GlobalTheory.LocalEqGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfNotNonempty
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.SqGlue

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom s) =
      (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem subsingleton_of_not_nonempty {X : Scheme.{0}} {W : X.Opens} (h : ¬ Nonempty W) : Subsingleton Γ(X, W) := by
  have e : W = ⊥ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => h ⟨⟨x, hx⟩⟩
  subst e
  infer_instance

theorem res_cancel {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (hW : W ≤ V) {a : Γ(X, V)} (ha : a ≠ 0)
    {b c : Γ(X, W)} (h : b * (X.presheaf.map (homOfLE hW).op).hom a = c * (X.presheaf.map (homOfLE hW).op).hom a) :
    b = c := by
  by_cases hn : Nonempty W
  · refine mul_right_cancel₀ (fun h0 => ha ?_) h
    apply map_injective_of_isIntegral X (homOfLE hW)
    rw [h0, map_zero]
  · exact (subsingleton_of_not_nonempty hn).elim _ _

theorem exists_unit_of_locally {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (hW : W ≤ V) (s : Γ(X, W))
    {t : Γ(X, V)} (ht : t ≠ 0)
    (h : ∀ x ∈ W, ∃ (O : X.Opens) (hO : O ≤ W), x ∈ O ∧ ∃ u : Γ(X, O)ˣ,
      (X.presheaf.map (homOfLE hO).op).hom s = (u : Γ(X, O)) * (X.presheaf.map (homOfLE (hO.trans hW)).op).hom t) :
    ∃ c : Γ(X, W)ˣ, s = (c : Γ(X, W)) * (X.presheaf.map (homOfLE hW).op).hom t := by
  choose O hO hx u hu using fun x : W => h x.1 x.2
  have hcov : W ≤ iSup O := fun x hxW => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxW⟩, hx _⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf O (fun x => (u x : Γ(X, O x))) := by
    intro x y
    refine res_cancel (W := O x ⊓ O y) (inf_le_left.trans ((hO x).trans hW)) ht ?_
    have e₁ := congrArg (X.presheaf.map (homOfLE (inf_le_left : O x ⊓ O y ≤ O x)).op).hom (hu x)
    have e₂ := congrArg (X.presheaf.map (homOfLE (inf_le_right : O x ⊓ O y ≤ O y)).op).hom (hu y)
    rw [map_mul, res_res, res_res] at e₁ e₂
    exact e₁.symm.trans e₂
  obtain ⟨c, hc, -⟩ := X.sheaf.existsUnique_gluing' O W (fun x => homOfLE (hO x)) hcov
    (fun x => (u x : Γ(X, O x))) hcomp
  have hc' : ∀ x, (X.presheaf.map (homOfLE (hO x)).op).hom c = (u x : Γ(X, O x)) := hc
  have hunit : IsUnit (c : Γ(X, W)) := by
    refine X.toRingedSpace.isUnit_of_isUnit_germ W c fun x hxW => ?_
    have e := X.presheaf.germ_res_apply (homOfLE (hO ⟨x, hxW⟩)) x (hx ⟨x, hxW⟩) c
    have e' := (u ⟨x, hxW⟩).isUnit.map (X.presheaf.germ (O ⟨x, hxW⟩) x (hx ⟨x, hxW⟩)).hom
    rw [← hc'] at e'
    exact e ▸ e'
  refine ⟨hunit.unit, ?_⟩
  refine X.sheaf.eq_of_locally_eq' O W (fun x => homOfLE (hO x)) hcov _ _ fun x => ?_
  change (X.presheaf.map (homOfLE (hO x)).op).hom s = (X.presheaf.map (homOfLE (hO x)).op).hom _
  rw [map_mul, res_res, IsUnit.unit_spec, hc', hu x]

theorem app_res {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} {O : X.Opens} (hU : U' ≤ U) (hO : O ≤ f ⁻¹ᵁ U')
    (s : Γ(Y, U)) :
    (X.presheaf.map (homOfLE (hO.trans (f.preimage_mono hU))).op).hom ((f.app U).hom s) =
      (X.presheaf.map (homOfLE hO).op).hom ((f.app U').hom ((Y.presheaf.map (homOfLE hU).op).hom s)) := by
  rw [← res_res (f.preimage_mono hU) hO]
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

def resU {X : Scheme.{0}} {A B : X.Opens} (h : B ≤ A) (u : Γ(X, A)ˣ) : Γ(X, B)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom u

@[simp] theorem coe_resU {X : Scheme.{0}} {A B : X.Opens} (h : B ≤ A) (u : Γ(X, A)ˣ) :
    (resU h u : Γ(X, B)) = (X.presheaf.map (homOfLE h).op).hom u := rfl

theorem pow_ne_zero' {X : Scheme.{0}} [IsIntegral X] {V : X.Opens} {a : Γ(X, V)} (ha : a ≠ 0) (n : ℕ) : a ^ n ≠ 0 := by
  by_cases hn : Nonempty V
  · exact pow_ne_zero n ha
  · exact (ha ((subsingleton_of_not_nonempty hn).elim _ _)).elim

end GlobalTheory.SqGlue


open GlobalTheory.SqGlue in
theorem GlobalTheory.SqGlue.main : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (L2 : LB G₁.left), L2.IsLB → ∀ (h : L2.Sec) (Lθ : LB (pullback G₁.hom (jK R'))) (θ : Lθ.Sec), (∀ j i, ∃ w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G₁.hom (jK R')).app (L2.U j)).hom (h.f j))) → ∀ (Ix : Type) (V : Ix → G₁.left.Opens) (a : ∀ k, Γ(G₁.left, V k)), (∀ k, a k ≠ 0) → (∀ k j, ∃ u : Γ(G₁.left, V k ⊓ L2.U j)ˣ, (G₁.left.presheaf.map (homOfLE inf_le_right).op).hom (h.f j) = (u : Γ(G₁.left, V k ⊓ L2.U j)) * (G₁.left.presheaf.map (homOfLE inf_le_left).op).hom (a k) ^ 2) → (∀ k l, ∃ c : Γ(G₁.left, V k ⊓ V l)ˣ, (G₁.left.presheaf.map (homOfLE inf_le_left).op).hom (a k) ^ 2 = (c : Γ(G₁.left, V k ⊓ V l)) * (G₁.left.presheaf.map (homOfLE inf_le_right).op).hom (a l) ^ 2) ∧ (∀ k i, ∃ w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ V k ⊓ Lθ.U i)ˣ, ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ V k ⊓ Lθ.U i)) * ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G₁.hom (jK R')).app (V k)).hom (a k)) ^ 2) := by
  intro R' _ _ _ _ G₁ _ _ hsemi L2 hL h Lθ θ hθ Ix V a hne hu
  haveI : Smooth G₁.hom := hsemi.smooth
  haveI : GeometricallyConnected G₁.hom := hsemi.geomConnected
  haveI : IsIntegral G₁.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G₁
  haveI : IsIntegral (pullback G₁.hom (jK R')) := GlobalTheory.isIntegral_pullback_of_smooth G₁.hom (jK R')
  have hcov : ∀ x : G₁.left, ∃ j, x ∈ L2.U j := fun x => by
    have : x ∈ (⊤ : G₁.left.Opens) := trivial
    rw [← hL.cover] at this
    exact TopologicalSpace.Opens.mem_iSup.1 this
  set f := pullback.fst G₁.hom (jK R') with hf
  refine ⟨fun k l => ?_, fun k i => ?_⟩
  · refine (exists_unit_of_locally inf_le_right
      ((G₁.left.presheaf.map (homOfLE (inf_le_left : V k ⊓ V l ≤ V k)).op).hom (a k) ^ 2)
      (pow_ne_zero' (hne l) 2) fun x hx => ?_).imp fun c hc => by rwa [map_pow] at hc
    obtain ⟨j, hj⟩ := hcov x
    obtain ⟨uk, huk⟩ := hu k j
    obtain ⟨ul, hul⟩ := hu l j
    have hk : V k ⊓ V l ⊓ L2.U j ≤ V k ⊓ L2.U j := inf_le_inf_right _ inf_le_left
    have hl : V k ⊓ V l ⊓ L2.U j ≤ V l ⊓ L2.U j := inf_le_inf_right _ inf_le_right
    have e1 := congrArg (G₁.left.presheaf.map (homOfLE hk).op).hom huk
    have e2 := congrArg (G₁.left.presheaf.map (homOfLE hl).op).hom hul
    rw [map_mul, map_pow, res_res, res_res] at e1 e2
    have e : (resU hk uk : Γ(G₁.left, V k ⊓ V l ⊓ L2.U j)) *
        (G₁.left.presheaf.map (homOfLE (hk.trans inf_le_left)).op).hom (a k) ^ 2 =
        (resU hl ul : Γ(G₁.left, V k ⊓ V l ⊓ L2.U j)) *
        (G₁.left.presheaf.map (homOfLE (hl.trans inf_le_left)).op).hom (a l) ^ 2 := by
      rw [coe_resU, coe_resU, ← e1, ← e2]
    refine ⟨V k ⊓ V l ⊓ L2.U j, inf_le_left, ⟨hx, hj⟩, (resU hk uk)⁻¹ * resU hl ul, ?_⟩
    rw [map_pow, res_res, map_pow, Units.val_mul, _root_.mul_assoc, ← e, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  · have ht : (f.app (V k)).hom (a k) ≠ 0 := fun h0 =>
      hne k (GlobalTheory.ExpInt.generic_app_injective G₁ (V k) (h0.trans (map_zero _).symm))
    refine (exists_unit_of_locally inf_le_left
      ((((pullback G₁.hom (jK R')).presheaf.map (homOfLE (inf_le_right : f ⁻¹ᵁ V k ⊓ Lθ.U i ≤ Lθ.U i)).op).hom
        (θ.f i)) ^ 2) (pow_ne_zero' ht 2) fun y hy => ?_).imp fun c hc => by rwa [map_pow] at hc
    obtain ⟨j, hj⟩ := hcov (f.base y)
    obtain ⟨uk, huk⟩ := hu k j
    obtain ⟨w, hw⟩ := hθ j i
    have hO₁ : f ⁻¹ᵁ (V k ⊓ L2.U j) ⊓ Lθ.U i ≤ f ⁻¹ᵁ L2.U j ⊓ Lθ.U i :=
      inf_le_inf_right _ (f.preimage_mono inf_le_right)
    have hO₂ : f ⁻¹ᵁ (V k ⊓ L2.U j) ⊓ Lθ.U i ≤ f ⁻¹ᵁ (V k ⊓ L2.U j) := inf_le_left
    have hO₃ : f ⁻¹ᵁ (V k ⊓ L2.U j) ⊓ Lθ.U i ≤ f ⁻¹ᵁ V k ⊓ Lθ.U i :=
      inf_le_inf_right _ (f.preimage_mono inf_le_left)
    have e1 := congrArg ((pullback G₁.hom (jK R')).presheaf.map (homOfLE hO₁).op).hom hw
    rw [map_mul, map_pow, res_res, res_res] at e1
    rw [app_res f (inf_le_right : V k ⊓ L2.U j ≤ L2.U j) hO₂, huk, map_mul, map_mul, map_pow, map_pow,
      ← app_res f (inf_le_left : V k ⊓ L2.U j ≤ V k) hO₂] at e1
    refine ⟨_, hO₃, ⟨⟨hy.1, hj⟩, hy.2⟩, resU hO₁ w * resU hO₂ (Units.map (f.app (V k ⊓ L2.U j)).hom.toMonoidHom uk), ?_⟩
    rw [map_pow, res_res, map_pow, e1, Units.val_mul, coe_resU, coe_resU, Units.coe_map, _root_.mul_assoc]
    rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqMulSqOfFaithfullyFlatHeightOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqMulSqOfFaithfullyFlatHeightOne
open IsLocalRing

namespace GlobalTheory.Mum

theorem exists_uniformiser_mul_eq_mul_pow_of_height_eq_one (O : Type) [CommRing O] [IsDomain O]
    [IsNoetherianRing O] [IsIntegrallyClosed O] (p : Ideal O) [hp : p.IsPrime] (h1 : p.height = 1)
    (h : O) (hh : h ≠ 0) :
    ∃ π ∈ p, π ≠ 0 ∧ (∀ y ∈ p, ∃ s ∉ p, π ∣ s * y) ∧
      ∃ (n : ℕ) (b c : O), b ∉ p ∧ c ∉ p ∧ b * h = c * π ^ n := by
  have := GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one O p h1
  let R := Localization.AtPrime p
  have hinj : Function.Injective (algebraMap O R) :=
    IsLocalization.injective R p.primeCompl_le_nonZeroDivisors
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨⟨π, s⟩, hs⟩ := IsLocalization.surj p.primeCompl ϖ
  have hsu : IsUnit (algebraMap O R s) := IsLocalization.map_units R s
  have hπ : Irreducible (algebraMap O R π) := by
    have e : algebraMap O R π = ϖ * algebraMap O R s := hs.symm
    rw [e]
    exact (irreducible_mul_isUnit hsu).2 hϖ
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπ
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff R p π, hmax]
    exact Ideal.mem_span_singleton_self _
  · rintro rfl
    exact hπ.ne_zero (map_zero _)
  · intro y hy
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff R p y, hmax, Ideal.mem_span_singleton] at hy
    obtain ⟨z, hz⟩ := hy
    obtain ⟨⟨t, r⟩, hr⟩ := IsLocalization.surj p.primeCompl z
    refine ⟨r, r.2, t, hinj ?_⟩
    have hr' : z * algebraMap O R r = algebraMap O R t := hr
    rw [map_mul, map_mul, hz, ← hr']
    ring
  · have hh' : algebraMap O R h ≠ 0 := fun h0 => hh (hinj (by rw [h0, map_zero]))
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hh' hπ
    obtain ⟨⟨c, b⟩, hb⟩ := IsLocalization.surj p.primeCompl (u : R)
    have hb' : (u : R) * algebraMap O R b = algebraMap O R c := hb
    refine ⟨n, b, c, b.2, ?_, hinj ?_⟩
    · have hcu : IsUnit (algebraMap O R c) := by
        rw [← hb']
        exact u.isUnit.mul (IsLocalization.map_units R b)
      exact (IsLocalization.AtPrime.isUnit_to_map_iff R p c).1 hcu
    · rw [map_mul, map_mul, map_pow, hu, ← hb']
      ring

theorem exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime : ∀ (O C : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CommRing C] [IsDomain C] [IsNoetherianRing C] [Algebra O C] [Module.FaithfullyFlat O C] (h : O), h ≠ 0 → (∃ (u : Cˣ) (g : C), algebraMap O C h = u * g ^ 2) → ∀ p : Ideal O, p.IsPrime → p.height = 1 → (Ideal.map (algebraMap O C) p).IsPrime → ∃ a b c : O, b ∉ p ∧ c ∉ p ∧ b * h = c * a ^ 2 := by
  intro O C _ _ _ _ _ _ _ _ _ h hh hsq p hp h1 hP
  obtain ⟨u, g, hg⟩ := hsq
  obtain ⟨π, hπp, hπ0, hgen, n, b, c, hb, hc, hbc⟩ :=
    exists_uniformiser_mul_eq_mul_pow_of_height_eq_one O p h1 h hh
  let P : Ideal C := Ideal.map (algebraMap O C) p
  let R := Localization.AtPrime P
  let φ : O →+* R := (algebraMap C R).comp (algebraMap O C)
  have hcomap : P.comap (algebraMap O C) = p := Ideal.comap_map_eq_self_of_faithfullyFlat p
  have hinjR : Function.Injective (algebraMap C R) :=
    IsLocalization.injective R P.primeCompl_le_nonZeroDivisors
  have hinjC : Function.Injective (algebraMap O C) := FaithfulSMul.algebraMap_injective O C
  have hinj : Function.Injective φ := hinjR.comp hinjC
  have hunit : ∀ s ∉ p, IsUnit (φ s) := by
    intro s hs
    refine (IsLocalization.AtPrime.isUnit_to_map_iff R P (algebraMap O C s)).2 ?_
    intro hm
    exact hs (hcomap ▸ (Ideal.mem_comap.2 hm))
  have hπR : φ π ≠ 0 := fun h0 => hπ0 (hinj (by rw [h0, map_zero]))
  have hmax : maximalIdeal R = Ideal.span {φ π} := by
    apply le_antisymm
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro y hy
      obtain ⟨s, hs, hd⟩ := hgen y hy
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      have hd' : φ π ∣ φ s * φ y := by rw [← map_mul]; exact map_dvd φ hd
      exact (hunit s hs).dvd_mul_left.1 hd'
    · rw [Ideal.span_singleton_le_iff_mem]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R P (algebraMap O C π)).2
        (Ideal.mem_map_of_mem _ hπp)
  have hnf : ¬ IsField R := by
    intro hf
    rw [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot] at hf
    exact hπR hf
  have hdvr : IsDiscreteValuationRing R :=
    ((IsDiscreteValuationRing.TFAE R hnf).out 5 1).1 (show (maximalIdeal R).IsPrincipal from ⟨⟨φ π, hmax⟩⟩)
  have hirr : Irreducible (φ π) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  have hhR : φ h = algebraMap C R u * algebraMap C R g ^ 2 := by
    show algebraMap C R (algebraMap O C h) = _
    rw [hg, map_mul, map_pow]
  have hg0 : algebraMap C R g ≠ 0 := by
    intro h0
    apply hh
    apply hinj
    rw [hhR, h0, map_zero]
    ring
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg0 hirr
  have huR : IsUnit (algebraMap C R u) := u.isUnit.map _
  have hnm : 2 * m = n := by
    refine IsDiscreteValuationRing.unit_mul_pow_congr_pow hirr hirr
      ((hunit b hb).unit * huR.unit * v ^ 2) (hunit c hc).unit _ _ ?_
    have e := congrArg φ hbc
    rw [map_mul, map_mul, map_pow, hhR, hv] at e
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    rw [← e]
    ring
  refine ⟨π ^ m, b, c, hb, hc, ?_⟩
  rw [hbc, ← hnm]
  ring

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqMulSqOfFaithfullyFlatHeightOneStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_eq_mul_sq_of_faithfullyFlat_height_one : ∀ (O C : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CommRing C] [IsDomain C] [IsNoetherianRing C] [Algebra O C] [Module.FaithfullyFlat O C] (h : O), h ≠ 0 → (∃ (u : Cˣ) (g : C), algebraMap O C h = u * g ^ 2) → ∀ p : Ideal O, p.IsPrime → p.height = 1 → (Ideal.map (algebraMap O C) p).IsPrime → ∃ a b c : O, b ∉ p ∧ c ∉ p ∧ b * h = c * a ^ 2 := by
  first | exact @GlobalTheory.Mum.exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime | exact GlobalTheory.Mum.exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime | (intros; apply GlobalTheory.Mum.exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPrincipalPolarisationExtendsSemiAbelian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SymExtend

open GlobalTheory.CechPic

theorem stalkMap_comp_base {R : Type} [CommRing R] {G : Over (Sp R)} (f : G ⟶ G) (x : G.left) :
    (f.left.stalkMap x).hom.comp ((G.left.presheaf.germ ⊤ (f.left x) trivial).hom.comp ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) =
      (G.left.presheaf.germ ⊤ x trivial).hom.comp ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) := by
  ext a
  have e := Scheme.Hom.germ_stalkMap_apply f.left ⊤ x trivial
    (G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
  refine e.trans ?_
  conv_rhs => rw [← Over.w f]
  rfl

theorem exists_open_unit_mul_sq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hA : AdmBase R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (L2 : LB G.left) (h2 : L2.IsLB) (h : L2.Sec)
    (Lθ : LB (pullback G.hom (jK R))) (hθ : Lθ.IsLB) (θ : Lθ.Sec) (hc : (∀ j i, ∃ w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G.hom (jK R)).app (L2.U j)).hom (h.f j)))) (hs : (∀ (x' : G.left) (k : L2.ι), ((𝟙 G) ^ 2 : G ⟶ G).left x' ∈ L2.U k → gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) ≠ 0 ∧ ∃ (u : (G.left.presheaf.stalk x')ˣ) (g : G.left.presheaf.stalk x'), gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) = u * g ^ 2))
    (x : G.left) (hx : G.hom x = closedPoint R) :
    ∃ V : G.left.Opens, x ∈ V ∧ ∃ a : Γ(G.left, V), a ≠ 0 ∧ ∀ j, ∃ u : Γ(G.left, V ⊓ L2.U j)ˣ, (G.left.presheaf.map (homOfLE inf_le_right).op).hom (h.f j) = (u : Γ(G.left, V ⊓ L2.U j)) * (G.left.presheaf.map (homOfLE inf_le_left).op).hom a ^ 2 := by
  have hfl := (GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow _ G hG 2 two_ne_zero).1
  have hsu := GlobalTheory.SemiAbSurj.surjective_pow _ G hG 2 two_ne_zero
  generalize ((𝟙 G) ^ 2 : G ⟶ G) = f at hs hfl hsu
  obtain ⟨x', rfl⟩ := f.left.surjective x
  have hx' : G.hom x' = closedPoint R := by
    rw [← hx, ← Scheme.Hom.comp_apply, Over.w f]
  obtain ⟨hD, hN, hIC⟩ := GlobalTheory.SquareNear.stalk_props R hA G hG (f.left x')
  obtain ⟨hD', hN', hIC'⟩ := GlobalTheory.SquareNear.stalk_props R hA G hG x'
  obtain ⟨k, hk⟩ := exists_chart h2 (f.left x')
  obtain ⟨hne, u, g, hug⟩ := hs x' k hk
  rw [gs_stalkMap _ _ _ hk, gs_eq (𝟙 G.left) (f.left x') _ hk] at hne hug
  let _ := (f.left.stalkMap x').hom.toAlgebra
  have : Module.Flat (G.left.presheaf.stalk (f.left x')) (G.left.presheaf.stalk x') := Flat.stalkMap f.left x'
  have : IsLocalHom (algebraMap (G.left.presheaf.stalk (f.left x')) (G.left.presheaf.stalk x')) :=
    inferInstanceAs (IsLocalHom (f.left.stalkMap x').hom)
  have : Module.FaithfullyFlat (G.left.presheaf.stalk (f.left x')) (G.left.presheaf.stalk x') :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hne₀ : (G.left.presheaf.germ (L2.U k) (f.left x') hk).hom (h.f k) ≠ 0 := fun e =>
    hne ((congrArg (f.left.stalkMap x').hom e).trans (map_zero _))
  have hsq : ∃ (u : (G.left.presheaf.stalk x')ˣ) (g : G.left.presheaf.stalk x'),
      algebraMap (G.left.presheaf.stalk (f.left x')) (G.left.presheaf.stalk x')
        ((G.left.presheaf.germ (L2.U k) (f.left x') hk).hom (h.f k)) = u * g ^ 2 := ⟨u, g, hug⟩
  have hinj := GlobalTheory.Mum.LocalInj.base_to_stalk_injective R hA G hG (f.left x')
  have hpr := GlobalTheory.Mum.ideal_map_stalk_isPrime_of_closedPoint R hA G hG (f.left x') hx
  have hpr' := GlobalTheory.Mum.ideal_map_stalk_isPrime_of_closedPoint R hA G hG x' hx'
  have hhor := GlobalTheory.SqHorizontal.horizontal R hA G hG L2 h Lθ hθ θ hc (f.left x') k hk
  rw [← stalkMap_comp_base f x'] at hpr'
  generalize ((G.left.presheaf.germ ⊤ (f.left x') trivial).hom.comp ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) = σ at hinj hpr hpr' hhor
  have Hp : ∀ p : Ideal (G.left.presheaf.stalk (f.left x')), p.IsPrime → p.height = 1 →
      ∃ a b c : G.left.presheaf.stalk (f.left x'), b ∉ p ∧ c ∉ p ∧
        b * (G.left.presheaf.germ (L2.U k) (f.left x') hk).hom (h.f k) = c * a ^ 2 := by
    intro p hp h1
    by_cases hq : Ideal.comap σ p = ⊥
    · exact hhor p hp hq
    · have hqp : (Ideal.comap σ p).IsPrime := Ideal.comap_isPrime _ p
      have hP := hpr _ hqp
      have heq : Ideal.map σ (Ideal.comap σ p) = p := by
        by_contra hne'
        have hlt := lt_of_le_of_ne (Ideal.map_comap_le (f := σ) (K := p)) hne'
        have h1' : (Ideal.map σ (Ideal.comap σ p)).height < 1 :=
          (Ideal.height_strict_mono_of_isPrime hlt).trans_le h1.le
        rw [ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1'
        exact hq ((Ideal.map_eq_bot_iff_of_injective hinj).1 h1')
      refine GlobalTheory.T.exists_mul_eq_mul_sq_of_faithfullyFlat_height_one _ _ _ hne₀ hsq p hp h1 ?_
      have := hpr' _ hqp
      rwa [← Ideal.map_map, heq] at this
  obtain ⟨u₀, a, hua⟩ := isUnit_mul_sq_of_faithfullyFlat _ (G.left.presheaf.stalk x') _ hne₀ hsq Hp
  have ha : a ≠ 0 := by
    rintro rfl
    apply hne₀
    rw [hua]
    simp
  exact GlobalTheory.Mum.unit_mul_sq_spread G.left L2 h (f.left x') k hk u₀ a ha hua

theorem exists_unit_mul_of_sq_sec {X : Scheme.{0}} [IsIntegral X] [GlobalTheory.IsNormalScheme X] (W : X.Opens)
    {s t : Γ(X, W)} (c : Γ(X, W)ˣ) (ht : Nonempty W → t ≠ 0) (h : s ^ 2 = c * t ^ 2) :
    ∃ w : Γ(X, W)ˣ, s = w * t := by
  by_cases hW : Nonempty W
  · have ht := ht hW
    have h1 : t ∣ s := (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 ⟨c, by rw [h, mul_comm]⟩
    have h2 : s ∣ t := (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1
      ⟨(c⁻¹ : Γ(X, W)ˣ), by rw [h, mul_right_comm, Units.mul_inv, _root_.one_mul]⟩
    obtain ⟨w, hw⟩ := associated_of_dvd_dvd h1 h2
    exact ⟨w, by rw [← hw, mul_comm]⟩
  · obtain rfl : W = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hW ⟨⟨x, hx⟩⟩
    exact ⟨1, Subsingleton.elim _ _⟩

theorem res_ne_zero {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (hW : W ≤ V) {a : Γ(X, V)} (ha : a ≠ 0)
    [Nonempty W] : (X.presheaf.map (homOfLE hW).op).hom a ≠ 0 := fun h0 =>
  ha (map_injective_of_isIntegral X (homOfLE hW) (h0.trans (map_zero _).symm))

theorem res_mem_nonZeroDivisors {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (hW : W ≤ V) {a : Γ(X, V)}
    (ha : a ≠ 0) : (X.presheaf.map (homOfLE hW).op).hom a ∈ nonZeroDivisors Γ(X, W) := by
  by_cases hn : Nonempty W
  · exact mem_nonZeroDivisors_of_ne_zero (res_ne_zero hW ha)
  · obtain rfl : W = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hn ⟨⟨x, hx⟩⟩
    rw [Subsingleton.elim ((X.presheaf.map (homOfLE hW).op).hom a) 1]
    exact Submonoid.one_mem _

theorem extends_near (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hA : AdmBase R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (L2 : LB G.left) (h2 : L2.IsLB) (h : L2.Sec)
    (Lθ : LB (pullback G.hom (jK R))) (hθ : Lθ.IsLB) (θ : Lθ.Sec) (hc : (∀ j i, ∃ w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G.hom (jK R)).app (L2.U j)).hom (h.f j)))) (hs : (∀ (x' : G.left) (k : L2.ι), ((𝟙 G) ^ 2 : G ⟶ G).left x' ∈ L2.U k → gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) ≠ 0 ∧ ∃ (u : (G.left.presheaf.stalk x')ˣ) (g : G.left.presheaf.stalk x'), gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) = u * g ^ 2)) :
    ∃ (O : G.left.Opens) (N : LB O.toScheme), (∀ g : G.left, G.hom g = closedPoint R → g ∈ O) ∧ N.IsLB ∧
      LBIso (N.pull (pullback.fst O.ι (pullback.fst G.hom (jK R)))) (Lθ.pull (pullback.snd O.ι (pullback.fst G.hom (jK R)))) := by
  have hY := fun (x : {x : G.left // G.hom x = closedPoint R}) =>
    exists_open_unit_mul_sq R hA G hG L2 h2 h Lθ hθ θ hc hs x.1 x.2
  choose V hxV a ha hu using hY
  obtain ⟨hsq, hθa⟩ := GlobalTheory.SqGlue.main R hA G hG L2 h2 h _ θ hc _ V a ha hu
  haveI : IsIntegrallyClosed R := hA.2.2.1
  haveI : IsNoetherianRing R := hA.1
  haveI : Smooth G.hom := hG.smooth
  haveI : GeometricallyConnected G.hom := hG.geomConnected
  haveI : IsIntegral G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G
  haveI : GlobalTheory.IsNormalScheme G.left := GlobalTheory.isNormalScheme_of_smooth G.hom
  haveI : IsIntegral (pullback G.hom (jK R)) := GlobalTheory.isIntegral_pullback_of_smooth G.hom (jK R)
  haveI : GlobalTheory.IsNormalScheme (pullback G.hom (jK R)) := GlobalTheory.isNormalScheme_of_smooth (pullback.snd G.hom (jK R))
  have hgen : ∀ k, ((pullback.fst G.hom (jK R)).app (V k)).hom (a k) ≠ 0 := fun k h0 =>
    ha k (GlobalTheory.ExpInt.generic_app_injective G (V k) (h0.trans (map_zero _).symm))
  obtain ⟨O, N, hO, hN, hiso⟩ := GlobalTheory.LocalEqGlue.exists_lb_of_localEq G.left _ (pullback.fst G.hom (jK R)) Lθ θ _ V a
    (fun k W hW => res_mem_nonZeroDivisors hW (ha k)) (fun k W hW => res_mem_nonZeroDivisors hW (hgen k))
    (fun k l => by
      obtain ⟨c, hc⟩ := hsq k l
      exact exists_unit_mul_of_sq_sec _ c (fun _ => res_ne_zero _ (ha l)) hc)
    (fun k i => by
      obtain ⟨w, hw⟩ := hθa k i
      exact exists_unit_mul_of_sq_sec _ w (fun _ => res_ne_zero _ (hgen k)) hw)
  exact ⟨O, N, fun g hg => hO ⟨g, hg⟩ (hxV ⟨g, hg⟩), hN, hiso⟩

theorem exists_odd_sec {X : Scheme.{0}} [Nonempty X] {L : LB X} (hL : GlobalTheory.IsAmpleLB L) :
    ∃ (t : ℕ) (θ : (lbPow L (2 * t + 1)).Sec) (i : (lbPow L (2 * t + 1)).ι), θ.f i ≠ 0 := by
  obtain ⟨t, ht⟩ := Filter.eventually_atTop.1 (GlobalTheory.CutOutSections.eventually_isGenerated_lbPow hL)
  obtain ⟨θ, hθ⟩ := (ht (2 * t + 1) (by omega)).exists_mem (Classical.arbitrary X)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hθ
  refine ⟨t, θ, i, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hi
  exact hi

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ L₁ : LB G.left, L₁.IsLB ∧ LBIso (L₁.pull (pullback.fst G.hom (jK R))) (A.L.pull gen.hom.left) := by
  intro R _ _ _ hA G _ _ hG A gen hgen PP hext
  have hL : (A.L.pull gen.hom.left).IsLB := LB.isLB_pull A.isLB _
  have hP : (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left).IsLB := LB.isLB_pull hext.1 _
  obtain ⟨h2c, φ, hφ, h4c⟩ := GlobalTheory.T.two_smul_polarisation_class_generic_diagonal_doubling R G A gen hgen PP hext _ _ hL hP rfl rfl
  haveI : Smooth G.hom := hG.smooth
  haveI : GeometricallyConnected G.hom := hG.geomConnected
  haveI : IsIntegral (pullback G.hom (jK R)) := GlobalTheory.isIntegral_pullback_of_smooth G.hom (jK R)
  haveI : IsIso gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map gen.hom))
  have hamp : GlobalTheory.IsAmpleLB (X := pullback G.hom (jK R)) (A.L.pull gen.hom.left) :=
    (GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A.A A.isLB A.ample).pull_of_isAffineHom gen.hom.left
  have hK : Function.Surjective (pullback.snd G.hom (jK R)).appTop.hom := by
    have e : pullback.snd G.hom (jK R) = gen.hom.left ≫ A.A.hom := (Over.w gen.hom).symm
    haveI : IsIso gen.hom.left.appTop := inferInstanceAs (IsIso (gen.hom.left.app ⊤))
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso gen.hom.left.appTop).2.comp (GlobalTheory.ExpansionTotal.globalFns _ A.A A.isAb).2
  obtain ⟨t, θ, hθ⟩ := exists_odd_sec hamp
  generalize (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left) = P at hP h2c
  have hLθ := GlobalTheory.isLB_lbPow hL (2 * t + 1)
  have hL2 := GlobalTheory.isLB_lbPow hP (2 * t + 1)
  have eθ := cls_lbPow hL (2 * t + 1) hLθ
  obtain ⟨h, hc, hs⟩ := exists_sec_sq_of_double R hA G hG hK _ hLθ θ hθ _ hL2
    (by rw [cls_lbPow hP, map_nsmul, ← h2c, smul_comm]; exact congrArg (2 • ·) eθ) φ hφ
    (by
      refine (congrArg (pull φ) eθ).trans (Eq.trans ?_ (congrArg (4 • ·) eθ).symm)
      rw [map_nsmul, smul_comm]
      exact congrArg ((2 * t + 1) • ·) h4c)
  obtain ⟨O, N, hO, hN, hiso⟩ := extends_near R hA G hG _ hL2 h _ hLθ θ hc hs
  obtain ⟨N', hN', eN'⟩ := cls_surj (cls N hN - t • pull O.ι (cls P hP))
  have e₁ := (cls_eq_iff (LB.isLB_pull hN _) (LB.isLB_pull hLθ _)).2 hiso
  rw [cls_pull hN, cls_pull hLθ] at e₁
  obtain ⟨L', hL', hI⟩ := GlobalTheory.Mum.lb_extends_of_extLam R hA G hG _ PP hL hext O hO N' hN'
    ((cls_eq_iff (LB.isLB_pull hN' _) (LB.isLB_pull hL _)).1 (by
      rw [cls_pull hN', eN', map_sub, e₁, map_nsmul, ← pull_comp, pullback.condition, pull_comp, ← h2c]
      refine Eq.trans ?_ (cls_pull hL _ _).symm
      refine (congrArg (fun z => pull (pullback.snd O.ι (pullback.fst G.hom (jK R))) z - _) eθ).trans ?_
      rw [map_nsmul, map_nsmul, smul_smul, add_smul, one_smul, mul_comm t 2, add_sub_cancel_left]))
  exact ⟨L', hL', hI.symm⟩

end GlobalTheory.SymExtend
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPrincipalPolarisationExtendsSemiAbelianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPrincipalPolarisation_extends_semiAbelian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ L₁ : LB G.left, L₁.IsLB ∧ LBIso (L₁.pull (pullback.fst G.hom (jK R))) (A.L.pull gen.hom.left) := by
  first | exact @GlobalTheory.SymExtend.main | exact GlobalTheory.SymExtend.main | (intros; apply GlobalTheory.SymExtend.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSymmBundleExtensionOnFactor
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finExt_lbExt_of_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ExtLam G (A.L.pull gen.hom.left) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ φ : R →+* W, Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R)), IsGrpPullback GW G (spMap φ) βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW → LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A.L.pull gen.hom.left).pull κ) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)) (L₁ : LB G₁.left), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β ∧ L₁.IsLB ∧ LBIso (L₁.pull (pullback.fst G₁.hom (jK R'))) ((A.L.pull gen.hom.left).pull κ₁) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hOL G _ _ hG inc pr hinc hpr h1 h2 A gen hgen hext W _ _ _ hW φ hφ hloc GW _ _ βW DW AW UW κ hpb hκ hiso
  obtain ⟨L₁, hL₁, hiso₁⟩ := GlobalTheory.T.symmetricPrincipalPolarisation_extends_semiAbelian R hR.1 G hG A gen hgen _ hext
  have hsp : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  have hL : (A.L.pull gen.hom.left).IsLB := LB.isLB_pull A.isLB _
  refine ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, G, inferInstance, inferInstance, 𝟙 _, 𝟙 _, L₁,
    ⟨hR.1, Function.injective_id, RingHom.Finite.id R⟩, ?_, by simp, hL₁, ?_⟩
  · haveI : IsMonHom (Iso.refl G).hom := (inferInstance : IsMonHom (𝟙 G))
    exact (isGrpPullback_of_iso (Iso.refl G)).congr hsp.symm rfl
  · exact LBIso.trans (LB.isLB_pull hL₁ _) hL (LB.isLB_pull hL _) hiso₁ (GlobalTheory.TInj.GenPull.pull_id_iso hL)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSymmBundleExtensionOnFactorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteExtension_symmBundle_extension_on_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ExtLam G (A.L.pull gen.hom.left) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ φ : R →+* W, Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R)), IsGrpPullback GW G (spMap φ) βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW → LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A.L.pull gen.hom.left).pull κ) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)) (L₁ : LB G₁.left), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β ∧ L₁.IsLB ∧ LBIso (L₁.pull (pullback.fst G₁.hom (jK R'))) ((A.L.pull gen.hom.left).pull κ₁) := by
  first | exact @GlobalTheory.Mum.exists_finExt_lbExt_of_factor | exact GlobalTheory.Mum.exists_finExt_lbExt_of_factor | (intros; apply GlobalTheory.Mum.exists_finExt_lbExt_of_factor <;> assumption)
end
