module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsFibreIso
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomGenericPoint
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmResPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactTermAfterTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalOfIsTwistPull

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.PsiRing

def FibNZ {Y S : Scheme.{0}} (p : Y ⟶ S) {M : LB Y} (s : LB.Sec M) : Prop :=
  ∀ y : S, ∃ z : Y, p z = y ∧ z ∈ nonzeroLocus s

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

def Mult (D : DegPre R) (th g : SecBT D (𝟙_ _) 1 0) (b : R) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
    sval g r z J = cst (r ≫ (𝟙_ _ ⊗ D.P.A).hom) z b * sval th r z J

def Coef (D : DegPre R) (χ : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (th : SecBT D (𝟙_ _) 1 0) (g : SecBT D (𝟙_ _) 1 χ) (b : R) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
    sval g (lift (toUnit T) y).left z J = cst T.hom z b * ((val u (toUnit T).left z J * rigV D z J).val *
      sval th (lift (toUnit T) (y * cT D T χ)).left z J)

def SecCmp (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β))
    (xe : D'.X ≃+ D.X) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (f' : ∀ α, SecBT D' (𝟙_ _) 1 α) : Prop :=
  ∀ (α : D'.X) (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ D'.P.A).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
    r ≫ (snd _ D.P.A).left = r' ≫ (snd _ D'.P.A).left ≫ β → ∀ z J J', Good D.P.L z J → Good D'.P.L z J' →
      sval (f (xe α)) r z J = (∏ i : Fin 4, gw v (r' ≫ famφT D' (𝟙_ _) α i) z (J (r' ≫ famφT D' (𝟙_ _) α i ≫ β))
        (J' (r' ≫ famφT D' (𝟙_ _) α i)) ^ DegPre.famε 1 i).val * sval (f' α) r' z J'

abbrev RigCmp (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left)
    (v : LB.Iso D'.P.L (D.P.L.pull β)) : Prop :=
  PMaps v (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap φ)

abbrev PsiCmp (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β))
    (xe : D'.X ≃+ D.X) (gam : (TK V).left ⟶ (TK R).left) : Prop :=
  ∀ x, PMaps v (K := PUnit) (fun _ => D'.xK x) (fun _ => D.xK (xe x)) (fun _ => -1) (D'.psi x) (D.psi (xe x)) gam

end GlobalTheory.PsiRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymBaseChange

variable {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [GrpObj G'] {f : B' ⟶ B} {φ : G'.left ⟶ G.left}

theorem pushPt_injective (h : IsGrpPullback G' G f φ) {T : Over B'} {x y : T ⟶ G'}
    (e : pushPt h.1.w x = pushPt h.1.w y) : x = y := by
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · exact congrArg (fun z => z.left) e
  · rw [Over.w, Over.w]

theorem exists_endo (h : IsGrpPullback G' G f φ) (w : G ⟶ G) [IsMonHom w] :
    ∃ w' : G' ⟶ G', IsMonHom w' ∧ ∀ {T : Over B'} (x : T ⟶ G'), pushPt h.1.w (x ≫ w') = pushPt h.1.w x ≫ w := by
  let w' : G' ⟶ G' := Over.homMk (h.1.lift (φ ≫ w.left) G'.hom (by rw [Category.assoc, Over.w, h.1.w]))
    (h.1.lift_snd _ _ _)
  have hw : w'.left ≫ φ = φ ≫ w.left := h.1.lift_fst _ _ _
  have pa : ∀ {T : Over B'} (x : T ⟶ G'), pushPt h.1.w (x ≫ w') = pushPt h.1.w x ≫ w := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
  have mul : ∀ (T : Over B') (x y : T ⟶ G'), (x * y) ≫ w' = (x ≫ w') * (y ≫ w') := by
    intro T x y
    apply pushPt_injective h
    have a : pushPt h.1.w (x * y) = pushPt h.1.w x * pushPt h.1.w y := map_mul (pushHom h T) x y
    have b : pushPt h.1.w ((x ≫ w') * (y ≫ w')) = pushPt h.1.w (x ≫ w') * pushPt h.1.w (y ≫ w') :=
      map_mul (pushHom h T) _ _
    rw [pa, a, b, pa, pa, MonObj.mul_comp]
  refine ⟨w', ⟨?_, ?_⟩, pa⟩
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over B') ⟶ G') ≫ w' = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul (G' ⊗ G') (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

theorem hypS_baseChange : ∀ (B B' : Scheme.{0}) (G : Over B) (G' : Over B') [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (f : B' ⟶ B) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → HypS G L → HypS G' L' := by
  intro B B' G G' _ _ _ _ f φ L L' hL hL' h hb ⟨w, wd, hw, hwd, hs, hp, ha⟩
  obtain ⟨w', hw', pa⟩ := exists_endo h w
  obtain ⟨wd', hwd', pd⟩ := exists_endo h wd
  have hB : (L.pull φ).IsLB := by
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (φ y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 G'.left) y _ hy, map_one, gm_pull_g L φ (𝟙 G'.left) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 G'.left) y _ hy, gm_res (𝟙 G'.left) y _ hy,
        gm_res (𝟙 G'.left) y _ hy, gm_pull_g L φ (𝟙 G'.left) y I J hy.1.1 hy.1.2,
        gm_pull_g L φ (𝟙 G'.left) y J K hy.1.2 hy.2, gm_pull_g L φ (𝟙 G'.left) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  refine ⟨w', wd', hw', hwd', ?_, ?_, ?_⟩
  · apply pushPt_injective h
    have b : pushPt h.1.w (w' * wd') = pushPt h.1.w w' * pushPt h.1.w wd' := map_mul (pushHom h G') _ _
    have c := pa (𝟙 G')
    have d := pd (𝟙 G')
    rw [Category.id_comp] at c d
    rw [b, c, d, ← MonObj.comp_mul, hs, Category.comp_id]
  · have h₁ : LBIso (L.pull φ) (cubeLB G' ![𝟙 G', w'] (L.pull φ)) := by
      let U := pushPt h.1.w (𝟙 G')
      refine LBIso.chartPull (chartPullPull L _ U.left (Category.id_comp _))
        (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => by
          fin_cases i
          · simp [U]
          · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _)) I.down) hp
    have h₂ : LBIso (cubeLB G' ![𝟙 G', w'] (L.pull φ)) (cubeLB G' ![𝟙 G', w'] L') :=
      GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _
    exact LBIso.trans hL' hB (DVR.linComb_isLB L' hL' _ _) hb
      (LBIso.trans hB (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _) h₁ h₂)
  · have h₁ : LBIso (cubeLB G' ![fst G' G' ≫ w', snd G' G'] (L.pull φ))
        (cubeLB G' ![fst G' G', snd G' G' ≫ wd'] (L.pull φ)) := by
      let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
      refine LBIso.chartPull (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => by
        fin_cases i
        · exact (pa _).trans (by simp [U])
        · simp [U]) I.down)
        (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => by
          fin_cases i
          · simp [U]
          · exact (pd _).trans (by simp [U])) I.down) ha
    exact LBIso.trans (DVR.linComb_isLB L' hL' _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _)
      (GlobalTheory.PowPrimitive.lbIso_linComb hb _ _)
      (LBIso.trans (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _) h₁
        (GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _))

end GlobalTheory.SymBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChangeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleSymmetry_hypothesis_base_change : ∀ (B B' : Scheme.{0}) (G : Over B) (G' : Over B') [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (f : B' ⟶ B) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → HypS G L → HypS G' L' := by
  first | exact @GlobalTheory.SymBaseChange.hypS_baseChange | exact GlobalTheory.SymBaseChange.hypS_baseChange | (intros; apply GlobalTheory.SymBaseChange.hypS_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.QkPullEquiv

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull GlobalTheory.TorusExt

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {F : Type} [Field F] [Algebra (FractionRing R) F]
  [Algebra (FractionRing R') F]

theorem weilQkIs_of_pull (hG : GlobalFnsSt) (hF : Compat φ F) {k : ℕ} {p q : QkPt D F k} {p' q' : QkPt D' F k}
    (hp : p'.y = hD.xe.symm p.y) (hpg : IsPullGtF φ hD F p.g p'.g) (hq : q'.y = hD.xe.symm q.y)
    (hqg : IsPullGtF φ hD F q.g q'.g) {ζ : F} (H : WeilQkIs D' F k p' q' ζ) : WeilQkIs D F k p q ζ := by
  intro w v hw hv s s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄ β
  obtain ⟨α, rfl⟩ := hD.xe.surjective β
  obtain ⟨κ, κ', hκ⟩ := exists_isFibreIso hD hF
  obtain ⟨w', hw', tw⟩ := phiRel_transport hG R R' φ D D' hD F hF κ hκ.fst hκ.snd.symm k p p' hp hpg w hw
  obtain ⟨v', hv', tv⟩ := phiRel_transport hG R R' φ D D' hD F hF κ hκ.fst hκ.snd.symm k q q' hq hqg v hv
  choose dn hdn using exists_fam_field_pull hG R R' φ D D' hD F hF κ hκ.fst hκ.snd.symm k
  have e := (isSmul_iff _ _ _).1 (H w' v' hw' hv' _ _ _ _ _ (tv _ _ _ _ (hdn s) (hdn s₁) r₁)
    (tw _ _ _ _ (hdn s₁) (hdn s₂) r₂) (tw _ _ _ _ (hdn s) (hdn s₃) r₃) (tv _ _ _ _ (hdn s₃) (hdn s₄) r₄))
  refine sec_ext_val D.P.isLB (s := s₂.s (hD.xe α)) (s' := (ζ • s₄).s (hD.xe α)) fun y J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB y
  have a := FamFieldPull.IsSecPull.val (hdn s₂ α) (hκ.fam α) κ' y hJ hJ'
  have b := FamFieldPull.IsSecPull.val (hdn s₄ α) (hκ.fam α) κ' y hJ hJ'
  have c : κ' ≫ (fst (TF (R := R') F) D'.P.A).left = 𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left := by
    rw [← hκ.fst, ← Category.assoc, hκ.inv_hom]
  rw [hκ.inv_hom] at a b
  rw [e, sval_smul _ _ _ _ y hJ', c, mul_left_comm, ← b] at a
  rw [sval_smul _ _ _ _ y hJ]
  exact a

variable (hG : GlobalFnsSt) (hF : Compat φ F) (hB : D.TauBimult) (hB' : D'.TauBimult) {k : ℕ}

theorem pullQk_injective : Function.Injective (pullQk hD hG hF hB hB' (k := k)) := fun _ _ h =>
  qk_ext (hD.xe.symm.injective (congrArg QkPt.y h)) (pullGt_injective hD hG hF (congrArg QkPt.g h))

theorem qkAdd_pullQk_iff (p q r : QkPt D F k) : QkAdd p q r ↔
    QkAdd (pullQk hD hG hF hB hB' p) (pullQk hD hG hF hB hB' q) (pullQk hD hG hF hB hB' r) :=
  ⟨qkAdd_pullQk hD hG hF hB hB', fun h => (qkAdd_iff hB _ _ _).2 ((equiv_pullQk hD hG hF hB hB' _ _).1
    ((qkAdd_iff_of_equiv hB' (qk_equiv_refl hB' _) (qk_equiv_refl hB' _)
      (qkAdd_pullQk hD hG hF hB hB' (qkAdd_qkAdd hB p q))).1 h))⟩

theorem weilQkIs_pullQk_iff (p q : QkPt D F k) (z : F) : WeilQkIs D F k p q z ↔
    WeilQkIs D' F k (pullQk hD hG hF hB hB' p) (pullQk hD hG hF hB hB' q) z := by
  obtain ⟨a₁, a₂⟩ := (eq_pullQk_iff hD hG hF hB hB' p _).1 rfl
  obtain ⟨b₁, b₂⟩ := (eq_pullQk_iff hD hG hF hB hB' q _).1 rfl
  exact ⟨weilQkIs_pull hD hF a₁ a₂ b₁ b₂, weilQkIs_of_pull hD hG hF a₁ a₂ b₁ b₂⟩

theorem comm_proj {f' : D'.P.A ⟶ D'.P.A} {f : D.P.A ⟶ D.P.A}
    (h : f' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map f) :
    f'.left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ f.left := by
  have e : f'.left ≫ hD.e.hom.left = hD.e.hom.left ≫ ((Over.pullback (specOf φ)).map f).left :=
    congrArg (fun q => q.left) h
  have g : ((Over.pullback (specOf φ)).map f).left ≫ pullback.fst D.P.A.hom (specOf φ) =
      pullback.fst D.P.A.hom (specOf φ) ≫ f.left := pullback.lift_fst _ _ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) g).trans (Category.assoc _ _ _).symm)))

theorem qkAct_pullQk_iff {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] {o : D.OAct O}
    {o' : D'.OAct O} (hx : ∀ (a : O) y, hD.xe (a • y) = a • hD.xe y)
    (ho : ∀ a, (o'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (o.onB.act a).left) (a : O)
    (p q : QkPt D F k) : QkAct o a p q ↔ QkAct o' a (pullQk hD hG hF hB hB' p) (pullQk hD hG hF hB hB' q) :=
  ⟨qkAct_pullQk hD hG hF hB hB' hx ho, fun h => (qkAct_iff hB hG o _ _ _).2
    ((equiv_pullQk hD hG hF hB hB' _ _).1 ((qkAct_iff_of_equiv hB' hG o' (qk_equiv_refl hB' _)
      (qkAct_pullQk hD hG hF hB hB' hx ho (qkAct_qkSmul hB hG o a p))).1 h))⟩

theorem exists_equiv_pullQk : ∃ τ : QkPt D F k ≃ QkPt D' F k, ⇑τ = pullQk hD hG hF hB hB' :=
  ⟨Equiv.ofBijective _ ⟨pullQk_injective hD hG hF hB hB', pullQk_surjective hD hG hF hB hB'⟩, rfl⟩

end GlobalTheory.QkPullEquiv

namespace GlobalTheory


open GlobalTheory.ArcPull GlobalTheory.TorusExt GlobalTheory.QkPullEquiv in
theorem exists_qk_pull_equiv : Laws → Laws2 → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D'), D.TauBimult → D'.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ k : ℕ, ∃ τ : QkPt D F k ≃ QkPt D' F k, (∀ p p', τ p = p' ↔ p'.y = hD.xe.symm p.y ∧ IsPullGtF φ hD F p.g p'.g) ∧ (∀ p q, QkPt.Equiv D F p q ↔ QkPt.Equiv D' F (τ p) (τ q)) ∧ (∀ p q r, QkAdd p q r ↔ QkAdd (τ p) (τ q) (τ r)) ∧ (∀ p q z, WeilQkIs D F k p q z ↔ WeilQkIs D' F k (τ p) (τ q) z) ∧ ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (o : D.OAct O) (o' : D'.OAct O), (∀ (a : O) y, hD.xe (a • y) = a • hD.xe y) → (∀ a, o'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (o.onB.act a)) → ∀ a p q, QkAct o a p q ↔ QkAct o' a (τ p) (τ q) := by
  intro hL _ R R' _ _ _ _ φ D D' hD hB hB' F _ _ _ hF k
  have hG := hL.globalFns
  obtain ⟨τ, hτ⟩ := exists_equiv_pullQk hD hG hF hB hB' (k := k)
  refine ⟨τ, ?_⟩
  rw [hτ]
  exact ⟨fun p p' => eq_comm.trans (eq_pullQk_iff hD hG hF hB hB' p p'),
    fun p q => (equiv_pullQk hD hG hF hB hB' p q).symm, qkAdd_pullQk_iff hD hG hF hB hB',
    weilQkIs_pullQk_iff hD hG hF hB hB',
    fun O _ _ _ _ o o' hx ho => qkAct_pullQk_iff hD hG hF hB hB' hx fun a => comm_proj hD (ho a)⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnPowerOfLocalBases
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnPowerOfLocalBases
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem resG_resG_apply {X : Scheme.{0}} {U V T : X.Opens} (h : V ≤ U) (h' : T ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem exists_secOn_glue {X : Scheme.{0}} (B : LB X) (V : X.Opens) {κ : Type} (T : κ → X.Opens)
    (hT : ∀ k, T k ≤ V) (hV : ∀ x ∈ V, ∃ k, x ∈ T k) (σ : ∀ k j, Γ(X, T k ⊓ B.U j))
    (hσ : ∀ k, σ k ∈ secOn B (T k))
    (hc : ∀ k k' j, resG X (inf_le_inf_right _ inf_le_left : (T k ⊓ T k') ⊓ B.U j ≤ T k ⊓ B.U j) (σ k j) =
      resG X (inf_le_inf_right _ inf_le_right : (T k ⊓ T k') ⊓ B.U j ≤ T k' ⊓ B.U j) (σ k' j)) :
    ∃ τ ∈ secOn B V, ∀ k j, resG X (inf_le_inf_right _ (hT k)) (τ j) = σ k j := by
  have H : ∀ j, ∃ τ : Γ(X, V ⊓ B.U j), ∀ k, resG X (inf_le_inf_right _ (hT k)) τ = σ k j := fun j => by
    obtain ⟨g, hg, -⟩ := X.sheaf.existsUnique_gluing' (fun k => T k ⊓ B.U j) (V ⊓ B.U j)
      (fun k => homOfLE (inf_le_inf_right _ (hT k)))
      (fun x hx => by
        obtain ⟨k, hk⟩ := hV x hx.1
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk, hx.2⟩) (fun k => σ k j) (fun k k' => by
        have e : (T k ⊓ B.U j) ⊓ (T k' ⊓ B.U j) ≤ (T k ⊓ T k') ⊓ B.U j :=
          fun x hx => ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
        have := congrArg (resG X e) (hc k k' j)
        rw [resG_resG_apply, resG_resG_apply] at this
        exact this)
    exact ⟨g, hg⟩
  choose τ hτ using H
  refine ⟨τ, fun i j => ?_, fun k j => hτ j k⟩
  refine X.sheaf.eq_of_locally_eq' (fun k => T k ⊓ B.U i ⊓ B.U j) (V ⊓ B.U i ⊓ B.U j)
    (fun k => homOfLE (inf_le_inf_right _ (inf_le_inf_right _ (hT k))))
    (fun x hx => by
      obtain ⟨k, hk⟩ := hV x hx.1.1
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, ⟨hk, hx.1.2⟩, hx.2⟩) _ _ fun k => ?_
  have h := hσ k i j
  rw [← hτ i k, ← hτ j k, resG_resG_apply, resG_resG_apply] at h
  change resG X (inf_le_inf_right _ (inf_le_inf_right _ (hT k))) _ =
    resG X (inf_le_inf_right _ (inf_le_inf_right _ (hT k))) _
  rw [map_mul, resG_resG_apply, resG_resG_apply, resG_resG_apply]
  exact h

theorem sum_mul_mem_secOn {X : Scheme.{0}} (B : LB X) (V : X.Opens) {I : Type} [Fintype I] (f : I → Γ(X, V))
    (σ : I → ∀ j, Γ(X, V ⊓ B.U j)) (hσ : ∀ i, σ i ∈ secOn B V) :
    (fun j => ∑ i, resG X inf_le_left (f i) * σ i j) ∈ secOn B V := fun j j' => by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finset.mul_sum, resG_resG_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hσ i j j', mul_left_comm]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

theorem ZHPre.genVal_res (k : ℤ) {I : Type} [Fintype I]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : I → Ω) {V V' : Q.G.left.Opens} (e : V' ≤ V)
    (σ : ∀ j, Γ(Q.G.left, V ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V σ) :
    GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V' (fun j => resG _ (inf_le_inf_right _ e) (σ j)) := by
  intro K _ β g r jP jL h1 h2 h3 h4 h5
  rw [h K β g r jP jL h1 h2 h3 h4 (h5.trans e)]
  congr 1
  have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (V' ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U (fun _ => jL)) :=
    fun w _ => ⟨h5 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
  exact (valR_res (g ≫ Q.φ) _ hU _).symm

theorem ZHPre.genVal_of_cover (k : ℤ) {I : Type} [Fintype I]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : I → Ω) {V : Q.G.left.Opens} {κ : Type}
    (T : κ → Q.G.left.Opens) (hT : ∀ a, T a ≤ V) (hV : ∀ x ∈ V, ∃ a, x ∈ T a)
    (σ : ∀ j, Γ(Q.G.left, V ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : ∀ a, GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c (T a)
      (fun j => resG _ (inf_le_inf_right _ (hT a)) (σ j))) :
    GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V σ := by
  intro K _ β g r jP jL h1 h2 h3 h4 h5
  obtain ⟨a, ha⟩ := hV _ (h5 ⟨IsLocalRing.closedPoint K, rfl⟩)
  have h6 : Set.range (g ≫ Q.φ) ⊆ T a := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum K) w (IsLocalRing.closedPoint K)]
    exact ha
  rw [h a K β g r jP jL h1 h2 h3 h4 h6]
  congr 1
  have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (T a ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U (fun _ => jL)) :=
    fun w _ => ⟨h6 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
  exact valR_res (g ≫ Q.φ) _ hU _

theorem ZHPre.genVal_sum (k : ℤ) {I J : Type} [Fintype I] [Fintype J]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : J → I → Ω) (W : M.Z.Opens)
    (hW : (W : Set M.Z).Nonempty) (f : J → Γ(M.Z, W))
    (σ : J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : ∀ i, GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t (c i) _ (σ i)) :
    GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t (fun l => ∑ i, valF M.pt W (f i) * c i l) _
      (fun j => ∑ i, resG _ inf_le_left ((Q.G.hom.appLE W _ le_rfl).hom (f i)) * σ i j) := by
  intro K _ β g r jP jL h1 h2 h3 h4 h5
  have hV : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ W) := fun w _ => h5 ⟨w, rfl⟩
  have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ W ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U (fun _ => jL)) :=
    fun w _ => ⟨h5 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
  have hp : (g ≫ Q.φ) ≫ Q.G.hom = spMap β ≫ M.pt := by
    rw [Category.assoc, Q.cart.1.w, ← h1]
    rfl
  have hf : ∀ i, (valMap (g ≫ Q.φ) _ hU).hom (resG _ inf_le_left ((Q.G.hom.appLE W _ le_rfl).hom (f i))) =
      β (valF M.pt W (f i)) := fun i => by
    rw [← valR_eq, valR_res _ _ hU, valR_appLE _ _ _ hV, hp, valR_spMap_comp β M.pt W (M.top_le_preimage_pt hW),
      valF_eq_valR]
  have hi := fun i => h i K β g r jP jL h1 h2 h3 h4 h5
  set_option synthInstance.maxHeartbeats 100000 in
    rw [valF_eq_valR (g ≫ Q.φ), valR_eq _ _ hU, map_sum, Finset.mul_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finset.sum_mul, hf]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, ← valR_eq, ← valF_eq_valR, ← hi i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => mul_assoc _ _ _

end GlobalTheory.ZH

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_secOn_genVal_of_bases : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀), (U₀ : Set M.Z).Nonempty → (∀ (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b)) → ∃ σ : S.J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))).U j), ∀ i, σ i ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) ∧ GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i)) → ∀ (W : M.Z.Opens) (x₀ : S.Gam) (v : S.J → Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ v ∈ EE.E z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => v l / S.th x₀) _ σ := by
  intro o Ω _ _ _ S ρ M U₀ EE Q hU hb W x₀ v hv
  have H : ∀ z : W, ∃ T : M.Z.Opens, z.1 ∈ T ∧ T ≤ W ∧
      ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ T),
        GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => v l / S.th x₀) _ σ := by
    rintro ⟨z, hz⟩
    obtain ⟨U, b, hzU, -, hE⟩ := EE.loc z
    have h1 := (hv z hz).2
    rw [hE z hzU] at h1
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (M.O z) (v := fun i l => b i l)).1 h1
    let T : M.Z.Opens := W ⊓ U ⊓ ⟨⋂ i, {z' | (a i : Ω) ∈ M.O z'},
      isOpen_iInter_of_finite fun i => M.isOpen_setOf_mem_O _⟩
    have hzT : z ∈ T := ⟨⟨hz, hzU⟩, Set.mem_iInter.2 fun i => (a i).2⟩
    have hne : (T : Set M.Z).Nonempty := ⟨z, hzT⟩
    have h2 : ∀ i, ∃ f : Γ(M.Z, T), valF M.pt T f = a i := fun i =>
      (RatModel.mem_ringOn_iff_exists hne).1 (RatModel.mem_ringOn.2 fun z' hz' => Set.mem_iInter.1 hz'.2 i)
    choose f hf using h2
    obtain ⟨σ, hσ⟩ := hb T x₀ b fun z' hz' => ⟨(hv z' hz'.1.1).1, hE z' hz'.1.2⟩
    refine ⟨T, hzT, inf_le_left.trans inf_le_left, _,
      sum_mul_mem_secOn _ _ (fun i => (Q.G.hom.appLE T _ le_rfl).hom (f i)) σ fun i => (hσ i).1, ?_⟩
    have h3 := Q.genVal_sum S.N ρ.s (fun i l => b i l / S.th x₀) T hne f σ fun i => (hσ i).2
    have h4 : (fun l => ∑ i, valF M.pt T (f i) * (b i l / S.th x₀)) = fun l => v l / S.th x₀ := by
      funext l
      rw [← ha, Finset.sum_apply, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hf, ← mul_div_assoc]
      rfl
    rw [h4] at h3
    exact h3
  choose T hz hT σ hσ hg using H
  have hle : ∀ z, Q.G.hom ⁻¹ᵁ T z ≤ Q.G.hom ⁻¹ᵁ W := fun z x hx => hT z hx
  have hcov : ∀ x ∈ Q.G.hom ⁻¹ᵁ W, ∃ z, x ∈ Q.G.hom ⁻¹ᵁ T z := fun x hx => ⟨⟨Q.G.hom x, hx⟩, hz _⟩
  obtain ⟨τ, hτ, hr⟩ := exists_secOn_glue _ (Q.G.hom ⁻¹ᵁ W) (fun z => Q.G.hom ⁻¹ᵁ T z) hle hcov σ hσ
    fun z z' j => congrFun (Q.eq_of_genVal hU _ _ _ _ _ _ (Q.genVal_res _ _ _ inf_le_left _ (hg z))
      (Q.genVal_res _ _ _ inf_le_right _ (hg z'))) j
  refine ⟨τ, hτ, Q.genVal_of_cover _ _ _ _ hle hcov τ fun z => ?_⟩
  have h5 := hg z
  rw [← funext (hr z)] at h5
  exact h5

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnPowerOfLocalBasesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_secOn_power_of_local_bases : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀), (U₀ : Set M.Z).Nonempty → (∀ (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b)) → ∃ σ : S.J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))).U j), ∀ i, σ i ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) ∧ GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i)) → ∀ (W : M.Z.Opens) (x₀ : S.Gam) (v : S.J → Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ v ∈ EE.E z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => v l / S.th x₀) _ σ := by
  first | exact @GlobalTheory.ZH.exists_secOn_genVal_of_bases | exact GlobalTheory.ZH.exists_secOn_genVal_of_bases | (intros; apply GlobalTheory.ZH.exists_secOn_genVal_of_bases <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericTrivialisationSectionAndPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericTrivialisationSectionAndPullback
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {H : LB M.Z} {d : H.ι → Ω}

theorem GenTriv.exists_sec_hasVal (h : M.GenTriv H d) (x : Ω) (hx : ∀ k, ∀ z ∈ H.U k, x / d k ∈ M.O z) :
    ∃ σ : H.Sec, M.HasVal d σ x := by
  have hf : ∀ k, ∃ f : Γ(M.Z, H.U k), (H.U k : Set M.Z).Nonempty → valF M.pt (H.U k) f = x / d k := fun k => by
    by_cases hk : (H.U k : Set M.Z).Nonempty
    · obtain ⟨f, hf⟩ := (mem_ringOn_iff_exists hk).1 (mem_ringOn.2 (hx k))
      exact ⟨f, fun _ => hf⟩
    · exact ⟨0, fun h => (hk h).elim⟩
  choose f hf using hf
  refine ⟨⟨f, fun i j => ?_⟩, hf⟩
  by_cases hij : ((H.U i ⊓ H.U j : M.Z.Opens) : Set M.Z).Nonempty
  · refine M.res_injective _ hij ?_
    have h1 := (M.res_apply _ hij _).trans ((M.valF_resG inf_le_left hij (f i)).trans
      (hf i (hij.mono (fun _ hz => (show _ ∈ H.U i ∧ _ ∈ H.U j from hz).1))))
    have h2 := (M.res_apply _ hij _).trans ((M.valF_resG inf_le_right hij (f j)).trans
      (hf j (hij.mono (fun _ hz => (show _ ∈ H.U i ∧ _ ∈ H.U j from hz).2))))
    have h3 := (M.res_apply _ hij _).trans (h.g_eq i j hij)
    rw [map_mul, h3]
    refine h1.trans (Eq.trans ?_ (congrArg (d j / d i * ·) h2.symm))
    have := h.ne i
    have := h.ne j
    field_simp
  · have e : (H.U i ⊓ H.U j : M.Z.Opens) = ⊥ :=
      SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hij)
    have : Subsingleton Γ(M.Z, H.U i ⊓ H.U j) := by
      rw [e]; infer_instance
    exact Subsingleton.elim _ _

theorem GenTriv.pull (h : M.GenTriv H d) {Ω' : Type} [Field Ω'] [Algebra o Ω'] {φ : Ω →ₐ[o] Ω'}
    {N : RatModel o Ω'} {a : N.Z ⟶ M.Z} (ha : M.IsHom N φ a) :
    N.GenTriv (H.pull a) fun k => φ (d (k PUnit.unit)) := by
  refine ⟨fun k => (map_ne_zero φ).2 (h.ne _), fun k k' hk => ?_⟩
  have hle : (H.pull a).U k ⊓ (H.pull a).U k' ≤ a ⁻¹ᵁ (H.U (k PUnit.unit) ⊓ H.U (k' PUnit.unit)) :=
    le_inf (inf_le_left.trans (LB.wchart_le H (fun _ => a) k PUnit.unit))
      (inf_le_right.trans (LB.wchart_le H (fun _ => a) k' PUnit.unit))
  have hne : ((H.U (k PUnit.unit) ⊓ H.U (k' PUnit.unit) : M.Z.Opens) : Set M.Z).Nonempty := by
    obtain ⟨z, hz⟩ := hk
    exact ⟨a z, hle hz⟩
  have e : ((H.pull a).g k k' : Γ(N.Z, (H.pull a).U k ⊓ (H.pull a).U k')) =
      resG N.Z hle (a.app _ (H.g (k PUnit.unit) (k' PUnit.unit) : Γ(M.Z, _))) := by
    have e0 : (H.pull a).g k k' = Semi.res hle (pullU a _ (H.g (k PUnit.unit) (k' PUnit.unit))) :=
      (Fintype.prod_unique (ι := PUnit) fun _ =>
        Semi.res hle (pullU a _ (H.g (k PUnit.unit) (k' PUnit.unit))) ^ (1 : ℤ)).trans (zpow_one _)
    exact congrArg Units.val e0
  rw [e, N.valF_resG hle hk, ha.valF_app hne, h.g_eq _ _ hne, map_div₀]

theorem genTriv_sec_and_pull : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z)
    (d : H.ι → Ω), M.GenTriv H d →
    (∀ x : Ω, (∀ k, ∀ z ∈ H.U k, x / d k ∈ M.O z) → ∃ σ : H.Sec, M.HasVal d σ x) ∧
    ∀ (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N : RatModel o Ω') (a : N.Z ⟶ M.Z),
      M.IsHom N φ a → N.GenTriv (H.pull a) fun k => φ (d (k PUnit.unit)) :=
  fun _ _ _ _ _ _ _ _ h => ⟨h.exists_sec_hasVal, fun _ _ _ _ _ _ ha => h.pull ha⟩

end GlobalTheory.ZH.RatModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericTrivialisationSectionAndPullbackStatement
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericTrivialisation_section_and_pullback : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z) (d : H.ι → Ω), M.GenTriv H d → (∀ x : Ω, (∀ k, ∀ z ∈ H.U k, x / d k ∈ M.O z) → ∃ σ : H.Sec, M.HasVal d σ x) ∧ ∀ (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N : RatModel o Ω') (a : N.Z ⟶ M.Z), M.IsHom N φ a → N.GenTriv (H.pull a) fun k => φ (d (k PUnit.unit)) := by
  first | exact @GlobalTheory.ZH.RatModel.genTriv_sec_and_pull | exact GlobalTheory.ZH.RatModel.genTriv_sec_and_pull | (intros; apply GlobalTheory.ZH.RatModel.genTriv_sec_and_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LePreimageOpenPartIffTestCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LePreimageOpenPartIffTestCoordinates
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.TestCrit

theorem exists_ne_zero_iff {O K k J : Type} [CommRing O] [Field K] [Algebra O K] [Field k] [Fintype J]
    [DecidableEq J] (hinj : Function.Injective (algebraMap O K)) (φ : O →+* k) (n A : Matrix J J O)
    (b : Matrix J J K) (hn : n.map (algebraMap O K) * b = 1) (I : Set J)
    (hs : Submodule.span O (b '' I) = Submodule.span O (Set.range fun i j => algebraMap O K (A i j)))
    (w : J → k) :
    (∃ i, ∑ j, φ (A i j) * (n.map φ).mulVec w j ≠ 0) ↔ ∃ i, i ∈ I ∧ w i ≠ 0 := by
  have hn' : b * n.map (algebraMap O K) = 1 := mul_eq_one_comm.1 hn
  have hb : ∀ i i', ∑ j, b i j * algebraMap O K (n j i') = (1 : Matrix J J K) i i' := fun i i' => by
    rw [← hn', Matrix.mul_apply]
    rfl
  have hsum : ∀ i, ∑ j, φ (A i j) * (n.map φ).mulVec w j = ∑ i', φ ((A * n) i i') * w i' := fun i => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul,
      Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
    exact Finset.sum_comm
  have hA : ∀ i i', algebraMap O K ((A * n) i i') = ∑ j, algebraMap O K (A i j) * algebraMap O K (n j i') :=
    fun i i' => by simp only [Matrix.mul_apply, map_sum, map_mul]
  simp only [hsum]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨i', -, hi'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    refine ⟨i', ?_, right_ne_zero_of_mul hi'⟩
    by_contra hI
    have h0 : ∀ a ∈ Submodule.span O (b '' I), ∑ j, a j * algebraMap O K (n j i') = 0 := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem _ h =>
        obtain ⟨i₀, hi₀, rfl⟩ := h
        rw [hb, Matrix.one_apply_ne]
        rintro rfl
        exact hI hi₀
      | zero => simp
      | add a a' _ _ ha ha' => simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ha, ha', add_zero]
      | smul c a _ ha =>
        simp only [Pi.smul_apply, smul_mul_assoc]
        rw [← Finset.smul_sum, ha, smul_zero]
    have h1 := h0 (fun j => algebraMap O K (A i j)) (hs ▸ Submodule.subset_span ⟨i, rfl⟩)
    rw [← hA, map_eq_zero_iff _ hinj] at h1
    exact hi' (by rw [h1, map_zero, zero_mul])
  · rintro ⟨i, hI, hw⟩
    by_contra hz
    push_neg at hz
    have hm : b i ∈ Submodule.span O (Set.range fun i j => algebraMap O K (A i j)) :=
      hs ▸ Submodule.subset_span ⟨i, hI, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hm
    have h1 : ∀ i', (1 : Matrix J J O) i i' = ∑ a, c a * (A * n) a i' := fun i' => hinj (by
      have : algebraMap O K ((1 : Matrix J J O) i i') = (1 : Matrix J J K) i i' := by
        simp only [Matrix.one_apply, apply_ite (algebraMap O K), map_one, map_zero]
      have hc' : ∀ j, b i j = ∑ a, algebraMap O K (c a) * algebraMap O K (A a j) := fun j => by
        rw [← hc]
        simp only [Finset.sum_apply, Pi.smul_apply]
        simp only [Algebra.smul_def]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, ← hb, map_sum]
      simp only [map_mul, hA, hc', Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
      exact Finset.sum_comm)
    apply hw
    calc w i = ∑ i', φ ((1 : Matrix J J O) i i') * w i' := by
          simp [Matrix.one_apply, apply_ite φ]
      _ = ∑ a, φ (c a) * ∑ i', φ ((A * n) a i') * w i' := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [h1, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
          exact Finset.sum_comm
      _ = 0 := by simp only [hz, mul_zero, Finset.sum_const_zero]

theorem le_preimage_G_iff_test : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ (x : Sp (kb p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W tm.l).toScheme) (w : S.J → kb p), x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y → Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l) x ((tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w) → (⊤ ≤ (x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⁻¹ᵁ Q.G ↔ ∃ i, t.cls i = 0 ∧ w i ≠ 0) := by
  intro o Ω _ _ _ hA S ρ M U₀ EE hB Q p _ y y₀ t c tm _ x w hx hw
  have := hA.ft
  obtain ⟨ψ, hψ⟩ : ∃ ψ : o →+* OO p, y ≫ M.s = spMap ψ :=
    ⟨(Spec.preimage (y ≫ M.s)).hom, (Spec.map_preimage _).symm⟩
  have hg : (gPt p ≫ y) ≫ M.s = spMap ((OO p).subtype.comp ψ) := by
    rw [Category.assoc, hψ, ← Spec.map_comp]
    rfl
  have hy₀ : ∀ a : o, y₀ (algebraMap o S.R a) = (ψ a : PadicAlgCl p) := fun a =>
    (c.at_ _).trans (RatModel.val_algebraMap hg a)
  have hgy : gPt p ≫ y = (spMap (algebraMap (FractionRing t.u.V) (PadicAlgCl p)) ≫ c.yK) ≫ U₀.ι := by
    refine (congrArg (gPt p ≫ ·) c.fac.symm).trans ?_
    beta_reduce
    rw [Category.assoc, c.yK_fac, ← Category.assoc, ← Category.assoc, ← Spec.map_comp]
    congr 1
    exact Spec.map_comp (CommRingCat.ofHom (algebraMap t.u.V (FractionRing t.u.V)))
      (CommRingCat.ofHom (algebraMap (FractionRing t.u.V) (PadicAlgCl p)))
  have hU : Set.range (gPt p ≫ y) ⊆ U₀ := by
    rw [hgy]
    rintro _ ⟨a, rfl⟩
    exact ((spMap (algebraMap (FractionRing t.u.V) (PadicAlgCl p)) ≫ c.yK) a).2
  have hcen : M.Cen U₀ (y (cPt p)) y := ⟨rfl, hU⟩
  have hcl := GlobalTheory.ZH.isClosed_centre o Ω M U₀ _ p y hcen
  obtain ⟨hker, -, hspan⟩ := GlobalTheory.T.span_rows_classZero_eq_invariant o Ω S ρ p y₀ t fun a => by
    rw [hy₀]
    exact (mem_OO_iff _).1 (ψ a).2
  have hT : S.TT M (y (cPt p)) = S.perp t.l.yy.ker := by
    rw [ThetaSys.TT, hB.atTest _ p y y₀ t.τ hcen c.at_, hker]
  have hW : ⊤ ≤ y ⁻¹ᵁ Q.W tm.l := (CrdCalc.top_le_iff y _).2 tm.mem
  have hrange : Set.range ((x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ≫ Q.P.hom) = {y (cPt p)} := by
    rw [Category.assoc, hx, RatModel.range_eq_singleton _ (IsLocalRing.closedPoint _)]
    congr 1
    exact congrArg y (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))
  have hs : (x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ≫ Q.P.hom ≫ M.s =
      spMap ((IsLocalRing.residue (OO p)).comp ψ) := by
    rw [← Category.assoc, Category.assoc x, hx, Category.assoc, hψ, ← Spec.map_comp]
    rfl
  have hcrd := Q.rel tm.l _ x _ hw
  rw [OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q _ _ _ _ _ hrange (Or.inl hcl) hs hcrd, hT, hx,
    Matrix.mulVec_mulVec]
  set C : Matrix S.J S.J (OO p) := (Q.c tm.l).map (valR y (Q.W tm.l)) with hC
  have hn : (Q.c tm.l).map (valR (rPt p ≫ y) (Q.W tm.l)) *
      (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)) =
      (C * tm.m.map t.u.j).map (IsLocalRing.residue (OO p)) := by
    rw [Matrix.map_mul]
    congr 1
    ext i j
    exact (CrdCalc.valR_spMap _ y _ hW).2 _
  rw [hn]
  obtain ⟨hWg, hvg⟩ := CrdCalc.valR_spMap (OO p).subtype y _ hW
  have hWg' : Set.range (gPt p ≫ y) ⊆ Q.W tm.l := (top_le_preimage_iff _ _).1 hWg
  set ξ := (gPt p ≫ y) (IsLocalRing.closedPoint _) with hξ
  have hr : Set.range (gPt p ≫ y) = {ξ} := RatModel.range_eq_singleton _ _
  have hξW : ξ ∈ Q.W tm.l := hWg' ⟨_, rfl⟩
  have hξU : ξ ∈ U₀ := hU ⟨_, rfl⟩
  have hBm : ∀ i j, Q.B tm.l i j ∈ M.O ξ := fun i => by
    have h1 : Q.B tm.l i ∈ EE.E ξ := by
      rw [Q.basis _ _ hξW]
      exact Submodule.subset_span ⟨i, rfl⟩
    rw [hB.ee.1 ξ hξU] at h1
    exact (RatModel.Lat.mem_const_iff M).1 h1
  have hinv : C.map (algebraMap (OO p) (PadicAlgCl p)) * (Q.B tm.l).map (M.val (gPt p ≫ y)) = 1 := by
    let c' : Matrix S.J S.J (M.O ξ) := fun i j => ⟨_, RatModel.valF_mem_O hξW (Q.c tm.l i j)⟩
    let B' : Matrix S.J S.J (M.O ξ) := fun i j => ⟨_, hBm i j⟩
    have h1 : c' * B' = 1 := by
      apply Matrix.map_injective (f := (M.O ξ).val.toRingHom) Subtype.val_injective
      beta_reduce
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact Q.c_inv tm.l
    have h2 := congrArg (fun N => N.map (RatModel.valHom _ _ hr)) h1
    beta_reduce at h2
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    rw [← h2]
    congr 1
    ext i j
    exact ((RatModel.val_valF hWg' _).trans (hvg _)).symm
  refine exists_ne_zero_iff Subtype.val_injective (IsLocalRing.residue (OO p)) _
    (fun i j => ψ (S.proj (S.perp t.l.yy.ker) 0 j i)) (t.b.map (algebraMap _ (PadicAlgCl p))) ?_
    {i | t.cls i = 0} ?_ w
  · rw [Matrix.map_mul, Matrix.mul_assoc, ← hinv, tm.m_eq]
    rfl
  · rw [hspan]
    simp only [hy₀]
    rfl

end GlobalTheory.ZH.TestCrit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LePreimageOpenPartIffTestCoordinatesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_preimage_openPart_iff_testCoordinates : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ (x : Sp (kb p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W tm.l).toScheme) (w : S.J → kb p), x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y → Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l) x ((tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w) → (⊤ ≤ (x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⁻¹ᵁ Q.G ↔ ∃ i, t.cls i = 0 ∧ w i ≠ 0) := by
  first | exact @GlobalTheory.ZH.TestCrit.le_preimage_G_iff_test | exact GlobalTheory.ZH.TestCrit.le_preimage_G_iff_test | (intros; apply GlobalTheory.ZH.TestCrit.le_preimage_G_iff_test <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsLBGenTrivOfRatios
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem eq_of_res_eq_of_nonempty {U : M.Z.Opens} {f g : Γ(M.Z, U)}
    (h : ∀ hU : (U : Set M.Z).Nonempty, M.res U hU f = M.res U hU g) : f = g := by
  by_cases hU : (U : Set M.Z).Nonempty
  · exact M.res_injective U hU (h hU)
  · obtain rfl : U = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hU)
    exact Subsingleton.elim _ _

theorem exists_unit_res_eq {U : M.Z.Opens} {x : Ω} (hx : x ≠ 0) (h : ∀ z ∈ U, x ∈ M.O z)
    (h' : ∀ z ∈ U, x⁻¹ ∈ M.O z) :
    ∃ g : Γ(M.Z, U)ˣ, ∀ hU : (U : Set M.Z).Nonempty, M.res U hU (g : Γ(M.Z, U)) = x := by
  by_cases hU : (U : Set M.Z).Nonempty
  · obtain ⟨a, ha⟩ := (mem_ringOn_iff_exists hU).1 (mem_ringOn.2 h)
    obtain ⟨b, hb⟩ := (mem_ringOn_iff_exists hU).1 (mem_ringOn.2 h')
    have hab : a * b = 1 := M.res_injective U hU (by
      rw [map_mul, map_one, res_apply, res_apply, ha, hb, mul_inv_cancel₀ hx])
    exact ⟨⟨a, b, hab, (mul_comm _ _).trans hab⟩, fun _ => (M.res_apply U hU a).trans ha⟩
  · exact ⟨1, fun h => (hU h).elim⟩

theorem exists_isLB_genTriv_of_ratios : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (ι : Type) (U : ι → M.Z.Opens) (d : ι → Ω), ⨆ k, U k = ⊤ → (∀ k, d k ≠ 0) → (∀ k k', ∀ z ∈ U k ⊓ U k', d k' / d k ∈ M.O z) → ∃ g : ∀ k k', Γ(M.Z, U k ⊓ U k')ˣ, (⟨ι, U, g⟩ : LB M.Z).IsLB ∧ M.GenTriv ⟨ι, U, g⟩ d := by
  intro o Ω _ _ _ M ι U d hU hd hr
  have key : ∀ k k', ∃ g : Γ(M.Z, U k ⊓ U k')ˣ, ∀ h : ((U k ⊓ U k' : M.Z.Opens) : Set M.Z).Nonempty,
      M.res _ h (g : Γ(M.Z, U k ⊓ U k')) = d k' / d k := fun k k' =>
    M.exists_unit_res_eq (div_ne_zero (hd k') (hd k)) (hr k k') fun z hz => by
      rw [inv_div]
      exact hr k' k z ⟨hz.2, hz.1⟩
  choose g hg using key
  have hres : ∀ k k' {V : M.Z.Opens} (h : V ≤ U k ⊓ U k') (hV : (V : Set M.Z).Nonempty),
      M.res V hV ((Semi.res h (g k k') : Γ(M.Z, V)ˣ) : Γ(M.Z, V)) = d k' / d k := fun k k' V h hV =>
    (M.res_resG h hV _).trans (hg k k' _)
  refine ⟨g, ⟨hU, fun i => Units.ext (M.eq_of_res_eq_of_nonempty fun hV => ?_),
    fun i j k => Units.ext (M.eq_of_res_eq_of_nonempty fun hV => ?_)⟩,
    ⟨hd, fun k k' h => (M.res_apply _ h _).symm.trans (hg k k' h)⟩⟩
  · refine (hres i i _ hV).trans ?_
    rw [div_self (hd i), Units.val_one, map_one]
  · rw [Units.val_mul, map_mul]
    refine (congrArg₂ (· * ·) (hres i j _ hV) (hres j k _ hV)).trans (Eq.trans ?_ (hres i k _ hV).symm)
    have := hd i
    have := hd j
    field_simp

end GlobalTheory.ZH.RatModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationChartValueFormsCorrespond
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationChartValueFormsCorrespond
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.PreForm

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ h) z U a = (r.stalkMap z).hom (gs h (r z) U a) := by
  rw [← gs_pull r h z U hU, gs_eq r z (h ⁻¹ᵁ U) hU, gs_eq h (r z) U hU]
  exact (Scheme.Hom.germ_stalkMap_apply r (h ⁻¹ᵁ U) z hU _).symm

theorem sval_comp_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval s (r ≫ h) z J = (r.stalkMap z).hom (sval s h (r z) (fun ψ => J (r ≫ ψ))) := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp_stalk r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem sval_eq_of_id {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y' ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (h : Y' ⟶ Y)
    (H : ∀ y J, Good L y J → sval s' (𝟙 Y') y J = sval s h y J)
    (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    sval s' r z J = sval s (r ≫ h) z J := by
  have e := sval_comp_stalk s' (𝟙 Y') r z hJ
  rw [Category.comp_id] at e
  rw [e, sval_comp_stalk s h r z hJ, H (r z) (fun ψ => J (r ≫ ψ)) (fun ψ => hJ (r ≫ ψ))]

theorem under_iff_match {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : PreU I D.toPre A G) (U₀ : UnifPre I D A G) : Under U U₀ ↔ Match U U₀ :=
  ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm⟩,
    fun ⟨a, b, c, d, e, f⟩ => ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm⟩⟩

theorem under_exists_and_expands : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∀ U₀ : UnifPre I D A G, ∃ U : PreU I D.toPre A G, Under U U₀) ∧ (∀ U : PreU I D.toPre A G, ∃ U₀ : UnifPre I D A G, Under U U₀) ∧ ∀ (U : PreU I D.toPre A G) (U₀ : UnifPre I D A G), Under U U₀ → ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D.toPre (𝟙_ _) k α) (σ₀ : H0 U₀.LG.L k) (f₀ : ∀ α, D.toPre.SecB k α), (∀ σ₁ : H0 U.P.L.L k, HEq σ₁ σ₀ → ∀ z J, Good U.P.L.L z J → sval σ (𝟙 _) z J = sval σ₁ (snd (𝟙_ _) G).left z J) → (∀ α z J, Good D.toPre.P.L z J → sval (f α) (𝟙 _) z J = sval (f₀ α) (snd (𝟙_ _) D.toPre.P.A).left z J) → (U.ExpT (𝟙_ _) k σ f ↔ ∀ e, U₀.ExpandsAt e k σ₀ f₀) := by
  intro hL _ R _ _ I D A G _ _ hG
  refine ⟨fun U₀ => ?_, fun U => ?_, fun U U₀ hU k σ f σ₀ f₀ hσ hf => ?_⟩
  · obtain ⟨w, hw⟩ := U₀.ext
    obtain ⟨U, hU, -⟩ := GlobalTheory.ValueForm.exists_preU_match hL.globalFns R I D A G U₀ hG w hw
    exact ⟨U, (under_iff_match U U₀).2 hU⟩
  · obtain ⟨U₀, hU⟩ := GlobalTheory.UU.ToChart.exists_match R I D A G U
    exact ⟨U₀, (under_iff_match U U₀).2 hU⟩
  · have hM := (under_iff_match U U₀).1 hU
    have ht : H0 U₀.LG.L k = H0 U.P.L.L k := by rw [hM.LG]
    have hc : HEq (cast ht σ₀) σ₀ := cast_heq ht σ₀
    have sG : SameG (cast ht σ₀) σ := fun Z r z J hJ => sval_eq_of_id _ _ _ (hσ _ hc) Z r z J hJ
    have sB : SameB f₀ f := fun α Z r z J hJ => sval_eq_of_id _ _ _ (hf α) Z r z J hJ
    exact ⟨expandsAt_of_expT R I D A G U U₀ hM k σ₀ _ σ f₀ f hc.symm sG sB,
      expT_of_expandsAt R I D A G U U₀ hM k σ₀ _ σ f₀ f hc.symm sG sB⟩

end GlobalTheory.LN.PreForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationChartValueFormsCorrespondStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_chart_value_forms_correspond : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∀ U₀ : UnifPre I D A G, ∃ U : PreU I D.toPre A G, Under U U₀) ∧ (∀ U : PreU I D.toPre A G, ∃ U₀ : UnifPre I D A G, Under U U₀) ∧ ∀ (U : PreU I D.toPre A G) (U₀ : UnifPre I D A G), Under U U₀ → ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D.toPre (𝟙_ _) k α) (σ₀ : H0 U₀.LG.L k) (f₀ : ∀ α, D.toPre.SecB k α), (∀ σ₁ : H0 U.P.L.L k, HEq σ₁ σ₀ → ∀ z J, Good U.P.L.L z J → sval σ (𝟙 _) z J = sval σ₁ (snd (𝟙_ _) G).left z J) → (∀ α z J, Good D.toPre.P.L z J → sval (f α) (𝟙 _) z J = sval (f₀ α) (snd (𝟙_ _) D.toPre.P.A).left z J) → (U.ExpT (𝟙_ _) k σ f ↔ ∀ e, U₀.ExpandsAt e k σ₀ f₀) := by
  first | exact @GlobalTheory.LN.PreForm.under_exists_and_expands | exact GlobalTheory.LN.PreForm.under_exists_and_expands | (intros; apply GlobalTheory.LN.PreForm.under_exists_and_expands <;> assumption)
end
end
