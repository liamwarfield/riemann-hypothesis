module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TautologicalModel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOpenConditionSmoothProject
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LamPull

theorem exists_isSquare {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (w : φ ≫ G.hom = G'.hom ≫ f) :
    IsSquare φ (lift (pushPt w (fst G' G')) (pushPt w (snd G' G'))).left :=
  ⟨congrArg (fun z => z.left) (lift_fst (pushPt w (fst G' G')) (pushPt w (snd G' G'))),
    congrArg (fun z => z.left) (lift_snd (pushPt w (fst G' G')) (pushPt w (snd G' G')))⟩

theorem isSquare_unique {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ b) : a = b := by
  apply pullback.hom_ext
  · exact ha.1.trans hb.1.symm
  · exact ha.2.trans hb.2.symm

theorem lbIso_lam_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left}
    {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (H : LBIso L' (L.pull φ))
    {φ₂ : (G2 G').left ⟶ (G2 G).left} (hφ : IsSquare φ φ₂) : LBIso (abelian₂ G' L') ((abelian₂ G L).pull φ₂) := by
  obtain rfl := isSquare_unique hφ (exists_isSquare h.1.w)
  have hΛ : (abelian₂ G L).IsLB := DVR.linComb_isLB L hL _ _
  have h₁ : LBIso (abelian₂ G' L') (abelian₂ G' (L.pull φ)) := by
    obtain ⟨w, hw⟩ := H
    exact ⟨LB.linCombIso w _ _, DVR.linCombIso_isGen w hw _ _⟩
  let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
  have h₂ : LBIso (abelian₂ G' (L.pull φ)) ((abelian₂ G L).pull U.left) := by
    refine LBIso.chartPull
      (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (Geo.Tor.chartPullPull (abelian₂ G L) _ U.left rfl) ⟨idIso _, idIso_isGen hΛ⟩
    fin_cases i <;> simp [U, x2]
  exact LBIso.trans (DVR.linComb_isLB L' hL' _ _) (DVR.linComb_isLB _ (LB.isLB_pull hL φ) _ _) (LB.isLB_pull hΛ _) h₁ h₂

theorem lam_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S), (∀ φ : t'.G.left ⟶ t.G.left, φ ≫ t.G.hom = t'.G.hom ≫ f → ∃ φ₂ : (G2 t'.G).left ⟶ (G2 t.G).left, IsSquare φ φ₂) ∧ ∀ (ν : SABMap t' t f) (φ₂ : (G2 t'.G).left ⟶ (G2 t.G).left), IsSquare ν.φ φ₂ → LBIso (abelian₂ t'.G t'.PP.L) ((abelian₂ t.G t.PP.L).pull φ₂) := by
  intro E _ _ _ H S S' t t' f
  refine ⟨fun φ w => ⟨_, exists_isSquare w⟩, fun ν φ₂ hφ => ?_⟩
  obtain ⟨w, hw, -⟩ := ν.lin
  exact lbIso_lam_pull ν.cart t.PP.isLB t'.PP.isLB ⟨w, hw⟩ hφ

end GlobalTheory.LamPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelOfPolarised

open PrimNorm

section Bundle

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem prod_lam {T : Over S} (x y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h ((lift x y).left ≫ (psum A (x2 A) I.down).left) ^
      ((-1 : ℤ) ^ (2 - I.down.card)) = diff₂ (fun q : T ⟶ A => h q.left) x y :=
  (prod_square (lift x y) (fst A A) (snd A A) h).trans (by rw [lift_fst, lift_snd])

theorem hasGen_lam_pull (hL : L.IsLB) {T : Over S} (x y : T ⟶ A) (h : diff₂ (ptCls L T) x y = 1) :
    ∃ t : ((abelian₂ A L).pull (lift x y).left).Gen, t.IsGen :=
  hasGen_nested hL _ _ _ _ (by
    rw [Fintype.prod_unique, zpow_one]
    exact (prod_lam x y (cls L)).trans h)

theorem lbIso_lam_pull (hL : L.IsLB) (x y : A ⊗ A ⟶ A)
    (h : diff₂ (ptCls L _) x y = diff₂ (ptCls L _) (fst A A) (snd A A)) :
    LBIso (abelian₂ A L) ((abelian₂ A L).pull (lift x y).left) :=
  LBIso.symm (lbIso_nested hL _ _ _ _ _ _ (by
    rw [Fintype.prod_unique, zpow_one]
    exact (prod_lam x y (cls L)).trans (h.trans (prod_square_id _ _ (cls L)).symm)))

theorem eq_one_of_lam (hL : L.IsLB) (hK : Out.KTriv A L) {T : Over S} (x : T ⟶ A)
    (h : ∃ t : ((abelian₂ A L).pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) : x = 1 := by
  have H := ((KerPow.pull_iff _ _ _).1 h).pull (β_ T A).hom.left
    (φ' := fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T A ≫ x) (snd T A)).left ≫ (psum A (x2 A) I.down).left)
    (fun I => by
      rw [← Category.assoc, ← Over.comp_left, comp_lift, braiding_hom_snd_assoc, braiding_hom_fst])
  have H₁ : KerPow.LocGen L (fst T A).left
      (fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T A ≫ x) (snd T A)).left ≫ (psum A (x2 A) I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) := fun p => ⟨⊤, trivial, H.pull _ fun _ => rfl⟩
  have H₂ := BoxKernel.locGen_base hL (fst T A).left (K := Fin 2) ![(1 : T ⟶ A).left, x.left] ![1, -1]
  refine KerPow.eq_one_of_locGen hK x (H₁.comb hL H₂ fun U _ g => ?_)
  rw [prod_lam, Fin.prod_univ_two, Fin.prod_univ_two]
  show _ * (g (fst T A ≫ (1 : T ⟶ A)).left ^ (1 : ℤ) * g (fst T A ≫ x).left ^ (-1 : ℤ))⁻¹ =
    g ((fst T A ≫ x) * snd T A).left ^ (1 : ℤ) * g (snd T A).left ^ (-1 : ℤ)
  rw [MonObj.comp_one, diff₂]
  apply Additive.ofMul.injective
  simp only [zpow_neg, zpow_one, ofMul_mul, ofMul_inv]
  abel

end Bundle

theorem lbIso_diag (hL : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) :
    LBIso (lbPow P.L 2) ((abelian₂ P.A P.L).pull (lift (𝟙 P.A) (𝟙 P.A)).left) := by
  refine LBIso.symm (lbIso_nested P.isLB _ _ _ _ _ _ ?_)
  rw [Fintype.prod_unique, zpow_one]
  refine (prod_lam _ _ (cls P.L)).trans ?_
  rw [Fintype.prod_unique]
  have a := (hasGen_iff P.isLB _ _).1 (hL.mulPull S P 2)
  have b := (hasGen_iff P.isLB _ _).1 (MulPull.HasGen.pull (K := PUnit) P.rigid (toUnit P.A).left)
  rw [Fin.prod_univ_two] at a
  rw [Fintype.prod_unique, zpow_one] at b
  have a' : cls P.L (𝟙 P.A.left) ^ (4 : ℤ) * cls P.L (𝟙 P.A ^ 2).left ^ (-1 : ℤ) = 1 := a
  have b' : cls P.L (1 : P.A ⟶ P.A).left = 1 := b
  rw [pow_two, zpow_neg, zpow_one, mul_inv_eq_one] at a'
  show cls P.L (𝟙 P.A * 𝟙 P.A).left * (cls P.L (𝟙 P.A.left))⁻¹ * (cls P.L (𝟙 P.A.left))⁻¹ *
    cls P.L (1 : P.A ⟶ P.A).left = cls P.L (𝟙 P.A.left) ^ (2 : ℤ)
  rw [← a', b']
  group

theorem weilIs_of_lbIso_pow (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L N : LB A.left} (hL : L.IsLB) (hN : N.IsLB) {d : ℕ} (hw : LBIso (lbPow L d) N) {n : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs A L n x y c) : Out.WeilIs A N n x y (c ^ d) := by
  have e : CechPic.cls N hN = d • CechPic.cls L hL :=
    ((CechPic.cls_eq_iff (LB.isLB_linComb hL _ _) hN).2 hw).symm.trans (CechPic.cls_lbPow hL d _)
  have up : ∀ {Z : Over S} (θ : Out.ThetaGrp A L n Z), ∃ θ' : Out.ThetaGrp A N n Z, θ'.pt = θ.pt := fun {Z} θ => by
    have z := (CechPic.cls_eq_zero_iff (N := Out.thetaLB A L n θ.pt) (LB.isLB_linComb hL _ _)).2 ⟨θ.φ, θ.isGen⟩
    have z' := (CechPic.cls_linComb hL _ _ _).symm.trans z
    obtain ⟨t, ht⟩ := (CechPic.cls_eq_zero_iff (N := Out.thetaLB A N n θ.pt) (LB.isLB_linComb hN _ _)).1
      ((CechPic.cls_linComb hN _ _ _).trans (by
        simp only [e, map_nsmul, smul_comm _ d]
        rw [← Finset.smul_sum, z', smul_zero]))
    exact ⟨⟨θ.pt, t, ht⟩, rfl⟩
  obtain ⟨c', hc'⟩ := CommutatorPairing.exists_weilIs (k := n) (x := x) (y := y) hG hA hN
    (fun p => by
      obtain ⟨V, hV, ⟨θ, -, eθ, -⟩, -⟩ := h p
      obtain ⟨θ', e'⟩ := up θ
      exact ⟨V, hV, θ', e'.trans eθ⟩)
    (fun p => by
      obtain ⟨V, hV, ⟨θ₀, θ, -, eθ⟩, -⟩ := h p
      obtain ⟨θ', e'⟩ := up θ
      exact ⟨V, hV, θ', e'.trans eθ⟩)
  have hw' : LBIso (lbPow L d) (N.pull (𝟙 A : A ⟶ A).left) :=
    (CechPic.cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hN _ _)).1
      (((CechPic.cls_eq_iff _ hN).2 hw).trans (CechPic.pull_id _).symm)
  have := (weilIs_along_hom hG S A A (𝟙 A) L N d n T x y c c' hA hA hL hN inferInstance hw'
    (by rwa [Category.comp_id, Category.comp_id])).2 h
  rwa [← this]

theorem unitOn_inj {k : Type} [CommRing k] : Function.Injective (unitOn (R := k)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).1 (congrArg Units.val h))

theorem exists_smul_of_dvd {h k : ℕ} {a : Fin h ⊕ Fin h → ℤ} (H : ∀ b, (k : ℤ) ∣ omegaStd a b) : ∃ b, a = k • b := by
  have d : ∀ i, (k : ℤ) ∣ a i := by
    rintro (i | i)
    · simpa [omegaStd, Pi.single_apply] using H (Pi.single (.inr i) 1)
    · simpa [omegaStd, Pi.single_apply] using H (Pi.single (.inl i) 1)
  choose b hb using d
  exact ⟨b, funext fun i => by simpa using hb i⟩

theorem onto_torsion {I G : Type} [Fintype I] [Group G] {k : ℕ} (hk : k ≠ 0) (f : (I → ℤ) → G)
    (add : ∀ a b, f (a + b) = f a * f b) (tors : ∀ a, f a ^ k = 1) (ker : ∀ a, f a = 1 → ∃ b, a = k • b)
    (card : Nat.card {g : G // g ^ k = 1} = k ^ Fintype.card I) (g : G) (hg : g ^ k = 1) : ∃ a, f a = g := by
  haveI : NeZero k := ⟨hk⟩
  let F : (I → ZMod k) → {g : G // g ^ k = 1} := fun c => ⟨f fun i => (c i).val, tors _⟩
  have hF : Function.Injective F := fun c c' e => by
    have e₁ : f (fun i => (c i).val) = f fun i => (c' i).val := congrArg Subtype.val e
    have e₂ := add ((fun i => ((c i).val : ℤ)) - fun i => ((c' i).val : ℤ)) fun i => (c' i).val
    rw [sub_add_cancel, e₁] at e₂
    obtain ⟨b, hb⟩ := ker _ (mul_eq_right.1 e₂.symm)
    funext i
    have := congrArg (fun z : ℤ => (z : ZMod k)) (congrFun hb i)
    simpa [sub_eq_zero] using this
  have : Finite {g : G // g ^ k = 1} := Nat.finite_of_card_ne_zero (by rw [card]; exact pow_ne_zero _ hk)
  obtain ⟨c, hc⟩ := (hF.bijective_of_nat_card_le (by rw [card, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card])).2 ⟨g, hg⟩
  exact ⟨_, congrArg Subtype.val hc⟩

end GlobalTheory.SiegelOfPolarised

namespace GlobalTheory


open SiegelOfPolarised PrimNorm in
theorem exists_siegPre_of_polAV : Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (K : Type) [Field K] (em : o →+* K) (h k : ℕ) (ζ : o) (ze : Kˣ) (P : Out.PolAV (Sp K)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp K)) ⟶ P.A)), P.g = h → (k : K) ≠ 0 → (ze : K) = em ζ → IsPrimitiveRoot ze k → (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ k = 1) → (∀ x y, Out.WeilIs P.A P.L k (lev x) (lev y) (unitOn (ze ^ omegaStd x y))) → ∃ (c : SiegPre h k ζ (spMap em)) (φ : c.A ≅ P.A), IsMonHom φ.hom ∧ c.Principal ∧ LBIso c.P ((abelian₂ P.A P.L).pull (lift (fst c.A c.A ≫ φ.hom) (snd c.A c.A ≫ φ.hom)).left) ∧ ∀ x, c.lev x ≫ φ.hom = lev x := by
  intro hL _ o _ K _ em h k ζ ze P lev hg hk hze hprim add tors weil
  have lam : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have dg : ((abelian₂ P.A P.L).pull (lift (𝟙 P.A) (𝟙 P.A)).left).IsLB := LB.isLB_linComb lam _ _
  have lev0 : lev 0 = 1 := mul_eq_left.1 ((add 0 0).symm.trans (by rw [add_zero]))
  let c : SiegPre h k ζ (spMap em) :=
    { A := P.A
      ab := P.isAb
      P := abelian₂ P.A P.L
      isLB := lam
      rig₁ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
      rig₂ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
      symm := lbIso_lam_pull P.isLB _ _ (diff₂_comm _ _)
      lev := lev
      lev_add := add
      lev_tors := tors
      geom := by
        intro k' _ _ x β z hx hz
        obtain ⟨φ₀, rfl⟩ := Spec.map_surjective x
        let φ : K →+* k' := φ₀.hom
        have hβ : φ.comp em = β := by
          have : CommRingCat.ofHom em ≫ φ₀ = CommRingCat.ofHom β := by
            rw [← Spec.map_inj, Spec.map_comp]; exact hx
          exact congrArg (fun q => q.hom) this
        obtain rfl : z = Units.map φ.toMonoidHom ze := Units.ext (by rw [hz, ← hβ]; simp [hze])
        have hz' : IsPrimitiveRoot (Units.map φ.toMonoidHom ze) k :=
          hprim.map_of_injective (Units.map_injective φ.injective)
        have hk' : (k : k') ≠ 0 := by rw [← map_natCast φ]; exact (map_ne_zero φ).2 hk
        have hk₀ : k ≠ 0 := fun e => hk (by simp [e])
        have W : ∀ a b, Out.WeilIs P.A P.L k (toUnit (Over.mk (Spec.map φ₀)) ≫ lev a) (toUnit _ ≫ lev b)
            (unitOn (Units.map φ.toMonoidHom ze ^ omegaStd a b)) := fun a b => by
          have H := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (toUnit (Over.mk (Spec.map φ₀))) (weil a b)
          have e : Units.map (toUnit (Over.mk (Spec.map φ₀))).left.appTop.hom.toMonoidHom
              (unitOn (ze ^ omegaStd a b)) = unitOn (Units.map φ.toMonoidHom (ze ^ omegaStd a b)) :=
            Units.ext (congrArg (fun q => q.hom (ze ^ omegaStd a b).val) (Scheme.ΓSpecIso_inv_naturality φ₀)).symm
          rw [e, map_zpow] at H
          exact H
        have ker : ∀ a, toUnit (Over.mk (Spec.map φ₀)) ≫ lev a = 1 → ∃ b, a = k • b := fun a ha =>
          exists_smul_of_dvd fun b => by
            have w₁ := W a b
            have w₀ := W 0 b
            rw [ha] at w₁
            rw [lev0, MonObj.comp_one] at w₀
            have e := unitOn_inj (CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB w₁ w₀)
            rw [show omegaStd 0 b = 0 by simp [omegaStd], zpow_zero] at e
            exact (hz'.zpow_eq_one_iff_dvd _).1 e
        refine ⟨fun a => ⟨ker a, ?_⟩, onto_torsion hk₀ _ (fun a b => by rw [add, MonObj.comp_mul])
          (fun a => by rw [← MonObj.comp_pow, tors, MonObj.comp_one]) ker ?_, fun a b => ?_⟩
        · rintro ⟨b, rfl⟩
          have pw : ∀ n : ℕ, lev (n • b) = lev b ^ n := fun n => by
            induction n with
            | zero => rw [zero_smul, pow_zero, lev0]
            | succ n ih => rw [succ_nsmul, add, ih, pow_succ]
          rw [pw, tors, MonObj.comp_one]
        · rw [(hL.mulN _ P k (Nat.pos_of_ne_zero hk₀)).2.2.2.2 k' _ hk', hg]
          simp [two_mul]
        · have H := weilIs_of_lbIso_pow hL.globalFns P.isAb P.isLB dg (lbIso_diag hL P) (W a b)
          have e : unitOn (Units.map φ.toMonoidHom ze ^ (2 * omegaStd a b)) =
              unitOn (Units.map φ.toMonoidHom ze ^ omegaStd a b) ^ 2 := by
            rw [mul_comm, zpow_mul, zpow_ofNat]
            exact map_pow _ _ _
          rw [e]
          exact H }
  refine ⟨c, Iso.refl _, inferInstanceAs (IsMonHom (𝟙 P.A)), ⟨?_, fun T x hx => eq_one_of_lam P.isLB P.ktriv x hx⟩,
    lbIso_lam_pull P.isLB _ _ (congrArg₂ _ (Category.comp_id _) (Category.comp_id _)), fun x => Category.comp_id _⟩
  have R := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) P.L 2 two_pos P.isAb P.isAb P.isLB (inferInstanceAs (IsFinite (𝟙 P.A.left)))
  have R' := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) (lbPow P.L 2) 2 two_pos P.isAb P.isAb
    (LB.isLB_linComb P.isLB _ _) (inferInstanceAs (IsFinite (𝟙 P.A.left)))
  exact R'.2.2.2 _ dg (lbIso_diag hL P) (R.2.1.2 P.ample)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAVStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegPre_iso_of_polAV : Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (K : Type) [Field K] (em : o →+* K) (h k : ℕ) (ζ : o) (ze : Kˣ) (P : Out.PolAV (Sp K)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp K)) ⟶ P.A)), P.g = h → (k : K) ≠ 0 → (ze : K) = em ζ → IsPrimitiveRoot ze k → (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ k = 1) → (∀ x y, Out.WeilIs P.A P.L k (lev x) (lev y) (unitOn (ze ^ omegaStd x y))) → ∃ (c : SiegPre h k ζ (spMap em)) (φ : c.A ≅ P.A), IsMonHom φ.hom ∧ c.Principal ∧ LBIso c.P ((abelian₂ P.A P.L).pull (lift (fst c.A c.A ≫ φ.hom) (snd c.A c.A ≫ φ.hom)).left) ∧ ∀ x, c.lev x ≫ φ.hom = lev x := by
  first | exact @GlobalTheory.exists_siegPre_of_polAV | exact GlobalTheory.exists_siegPre_of_polAV | (intros; apply GlobalTheory.exists_siegPre_of_polAV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open CechPic

theorem CechPic.lam_pull_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' T' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (c : Pic G.left) (x y : T' ⟶ G') :
    lam (pull φ c) x y = lam c (pushHom h T' x) (pushHom h T' y) := by
  rw [lam, lam, ← map_mul, ← map_one (pushHom h T')]
  simp only [← pull_comp]
  rfl

theorem adjoint_cubeLB_of_dense_fibres : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (u v : A ⟶ A), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → IsMonHom u → IsMonHom v → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (_ : IsCommMonObj G) (φ : G.left ⟶ A.left) (L' : LB G.left) (u' v' : G ⟶ G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ L'.IsLB ∧ LBIso L' (L.pull φ) ∧ u'.left ≫ φ = φ ≫ u.left ∧ v'.left ≫ φ = φ ≫ v.left ∧ LBIso (cubeLB G ![fst G G ≫ u', snd G G] L') (cubeLB G ![fst G G, snd G G ≫ v'] L')} → LBIso (cubeLB A ![fst A A ≫ u, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ v] L) := by
  intro hG S _ A _ _ L u v hA hL hamp hu hv hd
  have := hA.smooth
  have : IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  have hp : IsPullback (snd A A).left (fst A A).left A.hom A.hom :=
    (IsPullback.of_hasPullback A.hom A.hom).flip
  have h₁ : (cubeLB A ![fst A A ≫ u, snd A A] L).IsLB := LB.isLB_linComb hL _ _
  have h₂ : (cubeLB A ![fst A A, snd A A ≫ v] L).IsLB := LB.isLB_linComb hL _ _
  have hN := LB.isLB_div h₂ h₁
  refine GlobalTheory.T.seesaw_reduced_base_abelianScheme_of_dense_fibres hG S A L hA hL hamp A.left (A ⊗ A).left A.hom (snd A A).left (fst A A).left _ hp hN
    ((hd.preimage A.hom.isOpenMap).mono ?_) (lift (𝟙 A) (1 : A ⟶ A)).left ?_ ?_
  · rintro a ⟨K, _, x, G, _, _, φ, L', u', v', ⟨q, hq⟩, h, hL', hiso, hu', hv', H⟩
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback h.1 a q hq.symm
    let U : Over.mk ((G ⊗ G).hom ≫ x) ⟶ A ⊗ A := lift (pushHom h _ (fst G G)) (pushHom h _ (snd G G))
    have e₁ : U.left ≫ (fst A A).left = (fst G G).left ≫ φ :=
      congrArg (fun q => q.left) (lift_fst (pushHom h _ (fst G G)) (pushHom h _ (snd G G)))
    have e₂ : U.left ≫ (snd A A).left = (snd G G).left ≫ φ :=
      congrArg (fun q => q.left) (lift_snd (pushHom h _ (fst G G)) (pushHom h _ (snd G G)))
    have P : IsPullback U.left (fst G G).left (fst A A).left φ := by
      have B := (IsPullback.of_hasPullback G.hom G.hom).flip.paste_horiz h.1
      refine IsPullback.of_right ?_ e₁ hp
      rw [e₂, h.1.w]
      exact B
    have push : ∀ {w' : G ⟶ G} {w : A ⟶ A}, w'.left ≫ φ = φ ≫ w.left → ∀ y : G ⊗ G ⟶ G,
        pushHom h _ (y ≫ w') = pushHom h _ y ≫ w := fun hw y => Over.OverMorphism.ext (by
      show (y.left ≫ _) ≫ _ = (y.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
    refine ⟨G.left.residueField z, inferInstance, G.left.fromSpecResidueField z ≫ φ,
      pullback (fst G G).left (G.left.fromSpecResidueField z), pullback.fst _ _ ≫ U.left,
      pullback.snd _ _, ⟨IsLocalRing.closedPoint (G.left.residueField z), ?_⟩,
      (IsPullback.of_hasPullback _ _).paste_horiz P, ?_⟩
    · rw [← hz]
      exact congrArg φ (Scheme.fromSpecResidueField_apply z _)
    · have h₁' : (cubeLB G ![fst G G ≫ u', snd G G] L').IsLB := LB.isLB_linComb hL' _ _
      have h₂' : (cubeLB G ![fst G G, snd G G ≫ v'] L').IsLB := LB.isLB_linComb hL' _ _
      have H' := (cls_eq_iff h₁' h₂').2 H
      rw [cls_cube_two hL', cls_cube_two hL', (cls_eq_iff hL' (pull_isLB hL φ)).2 hiso, cls_pull hL,
        lam_pull_of_isGrpPullback h, lam_pull_of_isGrpPullback h, push hu', push hv'] at H'
      have j : pull U.left (cls _ h₂ - cls _ h₁) = 0 := by
        rw [cls_cube_two hL, cls_cube_two hL, map_sub, pull_lam, pull_lam, lift_fst,
          lift_snd, lift_fst_assoc, lift_snd_assoc]
        exact sub_eq_zero.2 H'.symm
      refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
      rw [cls_pull hN, cls_div h₂ h₁]
      exact (pull_comp _ _ _).trans ((congrArg _ j).trans (map_zero _))
  · rw [← Over.comp_left, lift_fst, Over.id_left]
  · refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
    rw [cls_pull hN, cls_div h₂ h₁, cls_cube_two hL, cls_cube_two hL, map_sub, pull_lam, pull_lam, lift_fst,
      lift_snd, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, lam_one_right, lam_one_right, sub_self]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_endomorphisms_cubeLB_of_dense_fibres : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (u v : A ⟶ A), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → IsMonHom u → IsMonHom v → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (_ : IsCommMonObj G) (φ : G.left ⟶ A.left) (L' : LB G.left) (u' v' : G ⟶ G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ L'.IsLB ∧ LBIso L' (L.pull φ) ∧ u'.left ≫ φ = φ ≫ u.left ∧ v'.left ≫ φ = φ ≫ v.left ∧ LBIso (cubeLB G ![fst G G ≫ u', snd G G] L') (cubeLB G ![fst G G, snd G G ≫ v'] L')} → LBIso (cubeLB A ![fst A A ≫ u, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ v] L) := by
  first | exact @GlobalTheory.adjoint_cubeLB_of_dense_fibres | exact GlobalTheory.adjoint_cubeLB_of_dense_fibres | (intros; apply GlobalTheory.adjoint_cubeLB_of_dense_fibres <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFieldExtensionBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFieldExtensionBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AmpleDescent

theorem relAmple_of_fieldExtension : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left) (L₀ : LB A₀.left) (L : LB A.left), IsAbelianScheme A₀ → IsGrpPullback A A₀ (spMap i) φ → L₀.IsLB → L.IsLB → LBIso L (L₀.pull φ) → Out.RelAmple A L → Out.RelAmple A₀ L₀ := by
  intro K₀ K _ _ i A₀ A _ _ φ L₀ L hab hpb hL₀ hL hiso hA

  have : IsProper A₀.hom := hab.proper
  have hP : IsPullback φ A.hom A₀.hom (spMap i) := hpb.1
  have : IsProper A.hom := MorphismProperty.of_isPullback (P := @IsProper) hP this

  have h1 : IsAmpleLB (L₀.pull φ) :=
    (GlobalTheory.isAmpleLB_congr hL (pull_isLB hL₀ φ) hiso).1 ((GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hL).1 hA)

  have : CompactSpace A₀.left := QuasiCompact.compactSpace_of_compactSpace A₀.hom
  have : QuasiSeparatedSpace A₀.left := quasiSeparatedSpace_of_quasiSeparated A₀.hom

  exact (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A₀ hL₀).2 (GlobalTheory.AmpleDescent.isAmpleLB_of_pull i hP hL₀ h1)

end GlobalTheory.AmpleDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFieldExtensionBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.relAmple_of_fieldExtension_baseChange : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left) (L₀ : LB A₀.left) (L : LB A.left), IsAbelianScheme A₀ → IsGrpPullback A A₀ (spMap i) φ → L₀.IsLB → L.IsLB → LBIso L (L₀.pull φ) → Out.RelAmple A L → Out.RelAmple A₀ L₀ := by
  first | exact @GlobalTheory.AmpleDescent.relAmple_of_fieldExtension | exact GlobalTheory.AmpleDescent.relAmple_of_fieldExtension | (intros; apply GlobalTheory.AmpleDescent.relAmple_of_fieldExtension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsJoinNormalProjectiveModels
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsJoinNormalProjectiveModels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.JoinModels

theorem isNormalScheme_of_flat_preimmersion {U X : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U := by
  intro x
  obtain ⟨h1, h2⟩ := h (j x)
  have hf : (j.stalkMap x).hom.Flat := Flat.stalkMap j x
  have hs : Function.Surjective (j.stalkMap x).hom := j.stalkMap_surjective x
  have hi : Function.Injective (j.stalkMap x).hom := by
    letI := (j.stalkMap x).hom.toAlgebra
    have : Module.Flat (X.presheaf.stalk (j x)) (U.presheaf.stalk x) := hf
    have : IsLocalHom (algebraMap (X.presheaf.stalk (j x)) (U.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (j.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (j x))
      (B := U.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j x)) (U.presheaf.stalk x)
  let e := RingEquiv.ofBijective (j.stalkMap x).hom ⟨hi, hs⟩
  have h3 : IsDomain (U.presheaf.stalk x) := e.symm.toMulEquiv.isDomain _
  exact ⟨h3, IsIntegrallyClosed.of_equiv e⟩

theorem isPullback_toImage_comp {U P Z : Scheme.{0}} (j : U ⟶ P) (q : P ⟶ Z) (v : U ⟶ Z)
    (h : j ≫ q = v) [QuasiCompact j] [IsSeparated q] [Flat v] [Mono v] :
    IsPullback (𝟙 U) j.toImage v (j.imageι ≫ q) := by
  have Hu := IsPullback.of_hasPullback v q
  have : Mono (pullback.snd v q) := inferInstance
  let c : U ⟶ pullback v q := pullback.lift (𝟙 U) j (by simpa using h.symm)
  have hc₁ : c ≫ pullback.fst _ _ = 𝟙 U := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd _ _ = j := pullback.lift_snd _ _ _
  have : IsClosedImmersion (c ≫ pullback.fst _ _) := by rw [hc₁]; infer_instance
  have : IsClosedImmersion c := .of_comp c (pullback.fst _ _)
  have H := (GlobalTheory.isPullback_toImage_of_isClosedImmersion j c _ hc₂).paste_horiz Hu
  rwa [hc₁] at H

theorem exists_common_projective {O : Type} [CommRing O] {U : Scheme.{0}} (σ : U ⟶ Sp O) {I : Type}
    [Finite I] [Nonempty I] (X : I → Scheme.{0}) (s : ∀ i, X i ⟶ Sp O) (hs : ∀ i, IsProjOver (s i))
    (u : ∀ i, U ⟶ X i) (hu : ∀ i, u i ≫ s i = σ) :
    ∃ (P : Scheme.{0}) (r : P ⟶ Sp O) (j : U ⟶ P) (p : ∀ i, P ⟶ X i), IsProjOver r ∧ j ≫ r = σ ∧
      ∀ i, p i ≫ s i = r ∧ j ≫ p i = u i := by
  classical
  have key : ∀ S : Finset I, ∃ (P : Scheme.{0}) (r : P ⟶ Sp O) (j : U ⟶ P), IsProjOver r ∧ j ≫ r = σ ∧
      ∀ i ∈ S, ∃ p : P ⟶ X i, p ≫ s i = r ∧ j ≫ p = u i := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      obtain ⟨i⟩ := ‹Nonempty I›
      exact ⟨X i, s i, u i, hs i, hu i, by simp⟩
    | insert k S _ ih =>
      obtain ⟨P, r, j, h1, h2, h3⟩ := ih
      refine ⟨pullback r (s k), pullback.fst _ _ ≫ r, pullback.lift j (u k) (h2.trans (hu k).symm),
        GlobalTheory.ProjSpace.isProjOver_pullback h1 (hs k), by rw [pullback.lift_fst_assoc, h2], fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ⟨pullback.snd _ _, pullback.condition.symm, pullback.lift_snd _ _ _⟩
      · obtain ⟨p, hp1, hp2⟩ := h3 i hi
        exact ⟨pullback.fst _ _ ≫ p, by rw [Category.assoc, hp1], by rw [pullback.lift_fst_assoc, hp2]⟩
  have := Fintype.ofFinite I
  obtain ⟨P, r, j, h1, h2, h3⟩ := key Finset.univ
  choose p hp using fun i => h3 i (Finset.mem_univ i)
  exact ⟨P, r, j, p, h1, h2, hp⟩

theorem isProper_of_proj {O : Type} [CommRing O] {X : Scheme.{0}} {s : X ⟶ Sp O} (h : IsProjOver s) :
    IsProper s := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str O N
  infer_instance

theorem exists_join {O : Type} [CommRing O] {U : Scheme.{0}} (σ : U ⟶ Sp O) {I : Type}
    [Finite I] [Nonempty I] (X : I → Scheme.{0}) (s : ∀ i, X i ⟶ Sp O) (hs : ∀ i, IsProjOver (s i))
    (u : ∀ i, U ⟶ X i) (hu : ∀ i, u i ≫ s i = σ) [∀ i, Flat (u i)] [∀ i, Mono (u i)]
    [∀ i, QuasiCompact (u i)] :
    ∃ (P : Scheme.{0}) (r : P ⟶ Sp O) (j : U ⟶ P) (p : ∀ i, P ⟶ X i), IsProjOver r ∧ j ≫ r = σ ∧
      ∀ i, p i ≫ s i = r ∧ IsPullback (𝟙 U) j (u i) (p i) := by
  obtain ⟨P, r, j, p, h1, h2, h3⟩ := exists_common_projective σ X s hs u hu
  have := isProper_of_proj h1
  have hsep : ∀ i, IsSeparated (p i) := fun i => by
    have : IsSeparated (p i ≫ s i) := by rw [(h3 i).1]; infer_instance
    exact IsSeparated.of_comp (p i) (s i)
  have : QuasiCompact j := by
    obtain ⟨i⟩ := ‹Nonempty I›
    have : QuasiCompact (j ≫ p i) := by rw [(h3 i).2]; infer_instance
    exact QuasiCompact.of_comp j (p i)
  obtain ⟨N, e, he, hr⟩ := h1
  refine ⟨j.image, j.imageι ≫ r, j.toImage, fun i => j.imageι ≫ p i,
    ⟨N, j.imageι ≫ e, inferInstance, by rw [Category.assoc, hr]⟩, by simpa using h2, fun i => ⟨?_, ?_⟩⟩
  · rw [Category.assoc, (h3 i).1]
  · exact isPullback_toImage_comp j (p i) (u i) (h3 i).2

theorem exists_join_scheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → CharZero O → ∃ (X : Scheme.{0}) (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap β)) (f : ∀ i, pullback s (spMap (b i)) ⟶ (C i).X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X ∧ IsProjOver s ∧ Flat s ∧ jQ ≫ pullback.snd _ _ = c ∧ IsOpenImmersion jQ ∧ Dense (Set.range jQ) ∧ ∀ i, f i ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback s (spMap (b i)), g ≫ pullback.fst _ _ = jQ ≫ pullback.fst _ _ → g ≫ f i = (C i).j) ∧ ∀ x : ↥(pullback s (spMap (b i))), f i x ∈ Set.range (C i).j → pullback.fst s (spMap (b i)) x ∈ Set.range (jQ ≫ pullback.fst s (spMap β)) := by
  intro E _ _ _ H U F O _ _ c t β I _ _ R _ a b ω C hβ hR _ _
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hβ
  letI := β.toAlgebra
  have hβ : algebraMap O F = β := rfl
  have hcl : ∀ i, ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp O) (κ : (C i).X ⟶ X'), IsProjOver s' ∧
      IsPullback κ (C i).s s' (spMap (b i)) := fun i => by
    letI := (b i).toAlgebra
    have := (hR i).2.2
    exact GlobalTheory.ProjClosure.exists_projective_closure O (R i) (a i) (C i).X (C i).s (C i).proj
  choose X' s' κ hs' hk using hcl
  have hbo : ∀ i, IsOpenImmersion (spMap (b i)) := fun i => by
    letI := (b i).toAlgebra
    have := (hR i).2.2
    exact IsOpenImmersion.of_isLocalization (a i)
  have hko : ∀ i, IsOpenImmersion (κ i) := fun i => MorphismProperty.of_isPullback (hk i).flip (hbo i)
  have hj : ∀ i, IsPreimmersion (C i).j ∧ Flat (C i).j ∧ QuasiCompact (C i).j ∧ QuasiCompact (κ i) :=
    fun i => by
      obtain ⟨⟨⟨_, _⟩, _, hfr⟩, _, _⟩ := hR i
      letI := (ω i).toAlgebra
      obtain ⟨-, -, -, h1, h2, -, h3⟩ := GlobalTheory.genericPart_dense_proOpen (R i) F (C i).X U (C i).s (C i).jQ
        (C i).flat (C i).proj (C i).jQ_open (C i).jQ_dense
      exact ⟨h1, h2, h3, MorphismProperty.of_isPullback (hk i).flip inferInstance⟩
  have hωb : ∀ i, spMap (ω i) ≫ spMap (b i) = spMap β := fun i => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, (hR i).2.1]
  have hjs : ∀ i, (C i).j ≫ (C i).s = c ≫ spMap (ω i) := fun i => by
    rw [Cpt.j, Category.assoc, pullback.condition, reassoc_of% (C i).jQ_over]
  have h1 := fun i => (hj i).1
  have h2 := fun i => (hj i).2.1
  have h3 := fun i => (hj i).2.2.1
  have h4 := fun i => (hj i).2.2.2
  obtain ⟨P, r, j, p, hr, hjr, hp⟩ := exists_join (c ≫ spMap β) X' s' hs' (fun i => (C i).j ≫ κ i)
    (fun i => by rw [Category.assoc, (hk i).w, reassoc_of% (hjs i), hωb])
  have hjp : ∀ i, j ≫ p i = (C i).j ≫ κ i := fun i => by simpa using (hp i).2.w.symm
  let jP : U ⟶ pullback r (spMap β) := pullback.lift j c hjr
  have hjP₁ : jP ≫ pullback.fst _ _ = j := pullback.lift_fst _ _ _
  have hjP₂ : jP ≫ pullback.snd _ _ = c := pullback.lift_snd _ _ _
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hU : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U :=
    isNormalScheme_of_flat_preimmersion (C i₀).j (C i₀).normal
  have hjPo : IsOpenImmersion jP := by
    have G := (IsPullback.of_hasPullback (C i₀).s (spMap (ω i₀))).flip.paste_vert (hk i₀).flip
    rw [hωb] at G
    let ρ : pullback r (spMap β) ⟶ pullback (C i₀).s (spMap (ω i₀)) :=
      G.lift (pullback.snd _ _) (pullback.fst _ _ ≫ p i₀)
        (by rw [Category.assoc, (hp i₀).1, pullback.condition])
    have hρ₁ : ρ ≫ pullback.snd _ _ = pullback.snd _ _ := G.lift_fst _ _ _
    have hρ₂ : ρ ≫ pullback.fst _ _ ≫ κ i₀ = pullback.fst _ _ ≫ p i₀ := G.lift_snd _ _ _
    have A : IsPullback ρ (pullback.fst r (spMap β)) (pullback.fst _ _ ≫ κ i₀) (p i₀) := by
      refine IsPullback.of_right (h₁₂ := pullback.snd _ _) (h₂₂ := s' i₀) (v₁₃ := spMap β) ?_ hρ₂ G
      rw [hρ₁, (hp i₀).1]
      exact (IsPullback.of_hasPullback _ _).flip
    have B : IsPullback (𝟙 U) jP (C i₀).jQ ρ := by
      refine IsPullback.of_bot (v₂₁ := pullback.fst _ _) (v₂₂ := pullback.fst _ _ ≫ κ i₀) (h₃₁ := p i₀)
        ?_ ?_ A
      · rw [hjP₁, ← Category.assoc]
        exact (hp i₀).2
      · refine G.hom_ext ?_ ?_
        · rw [Category.id_comp, Category.assoc, hρ₁, hjP₂, (C i₀).jQ_over]
        · rw [Category.id_comp, Category.assoc, hρ₂, reassoc_of% hjP₁, hjp, Cpt.j, Category.assoc]
    exact MorphismProperty.of_isPullback B (C i₀).jQ_open
  obtain ⟨Y, π, jQ, -, hY, hproj, hflat, hq₁, hq₂, hqo, hqd, hqr⟩ :=
    GlobalTheory.exists_normal_finite_model_of_finite_over_open O F P U r c j jP.opensRange jP.isoOpensRange.hom hr hU inferInstance
      (by rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]; exact hjP₁)
      (by rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]; exact hjP₂)
  let f : ∀ i, pullback (π ≫ r) (spMap (b i)) ⟶ (C i).X := fun i =>
    (hk i).lift (pullback.fst _ _ ≫ π ≫ p i) (pullback.snd _ _)
      (by rw [Category.assoc, Category.assoc, (hp i).1, pullback.condition])
  have hf : ∀ i, f i ≫ κ i = pullback.fst _ _ ≫ π ≫ p i := fun i => (hk i).lift_fst _ _ _
  refine ⟨Y, π ≫ r, jQ, f, hY, hproj, hflat, hq₁, hqo, hqd, fun i => ⟨(hk i).lift_snd _ _ _, ?_, ?_⟩⟩
  · intro g hg
    have hq₂' : jQ ≫ pullback.fst (π ≫ r) (spMap β) ≫ π = j := hq₂
    rw [← cancel_mono (κ i), Category.assoc, hf, reassoc_of% hg, reassoc_of% hq₂', hjp]
  · rintro x ⟨y, hy⟩
    have e1 : p i (π (pullback.fst (π ≫ r) (spMap (b i)) x)) = ((C i).j ≫ κ i) y := by
      rw [Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply (f i), hf]
      simp only [Scheme.Hom.comp_apply]
    obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback (hp i).2 y _ e1.symm
    obtain ⟨w, hw⟩ : pullback.fst (π ≫ r) (spMap (b i)) x ∈ Set.range (pullback.fst (π ≫ r) (spMap β)) := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨c z, ?_⟩
      rw [Scheme.Hom.comp_apply π r, ← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hjr]
    obtain ⟨v, hv⟩ := (hqr w).mpr ⟨jP.isoOpensRange.hom z, by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.isoOpensRange_hom_ι_assoc]
      exact (congrArg (fun m : U ⟶ P => m z) hjP₁).trans (hz.trans (congrArg π hw.symm))⟩
    exact ⟨v, by rw [Scheme.Hom.comp_apply, ← hw]; exact congrArg _ hv⟩

end GlobalTheory.JoinModels
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsJoinNormalProjectiveModelsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_join_normal_projective_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → CharZero O → ∃ (X : Scheme.{0}) (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap β)) (f : ∀ i, pullback s (spMap (b i)) ⟶ (C i).X), IsNormalScheme X ∧ IsProjOver s ∧ Flat s ∧ jQ ≫ pullback.snd _ _ = c ∧ IsOpenImmersion jQ ∧ Dense (Set.range jQ) ∧ ∀ i, f i ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback s (spMap (b i)), g ≫ pullback.fst _ _ = jQ ≫ pullback.fst _ _ → g ≫ f i = (C i).j) ∧ ∀ x : ↥(pullback s (spMap (b i))), f i x ∈ Set.range (C i).j → pullback.fst s (spMap (b i)) x ∈ Set.range (jQ ≫ pullback.fst s (spMap β)) := by
  first | exact @GlobalTheory.JoinModels.exists_join_scheme | exact GlobalTheory.JoinModels.exists_join_scheme | (intros; apply GlobalTheory.JoinModels.exists_join_scheme <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubeProjectiveAbelianSchemeAffineBase
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubeProjectiveAbelianSchemeAffineBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AbLaw.CubeAffine

theorem triv_theta_of_isProjBy :
    Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ M : LB A.left, M.IsLB → Triv (Theta A M) :=
  fun hL R _ A _ _ hA hp M hM => CubeProj.exists_gen_theta_of_isProjBy hL.globalFns R A hA hp M hM

end GlobalTheory.AbLaw.CubeAffine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubeProjectiveAbelianSchemeAffineBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theorem_of_cube_projective_abelianScheme_affineBase : Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ M : LB A.left, M.IsLB → Triv (Theta A M) := by
  first | exact @GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy | exact GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy | (intros; apply GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalModelAboveFiniteCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalModelAboveFiniteCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem Cpt.exists_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (C : Cpt c t β) (b : O →+* O') (k : F →+* F') (r : U' ⟶ U) (hr : r ≫ c = c' ≫ spMap k) (ν : SABMap t' t r), IsDedFrac β → IsDedFrac β' → β'.comp b = k.comp β → Geo.Tor.IsNormalScheme U' → IsFinite (pullback.lift r c' hr) → ∃ C' : Cpt c' t' β', Nonempty (C'.Above C b r ν) := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' C b k r hr ν _ hD hβ hN hfin
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hD
  let _ := β'.toAlgebra
  have hsq : spMap β' ≫ spMap b = spMap k ≫ spMap β := by rw [← spMap_comp, ← spMap_comp, hβ]
  have hjs : C.j ≫ C.s = c ≫ spMap β := by
    rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]
  have hopen := C.jQ_open
  let s₁ := pullback.snd C.s (spMap b)
  let q : pullback s₁ (spMap β') ⟶ pullback C.s (spMap β) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ spMap k) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hsq,
        Category.assoc])
  have q₁ : q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
  have q₂ : q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap k := pullback.lift_snd _ _ _
  have hq : IsPullback q (pullback.snd s₁ (spMap β')) (pullback.snd C.s (spMap β)) (spMap k) := by
    refine IsPullback.of_right ?_ q₂ (IsPullback.of_hasPullback C.s (spMap β))
    rw [q₁, ← hsq]
    exact (IsPullback.of_hasPullback s₁ (spMap β')).paste_horiz (IsPullback.of_hasPullback C.s (spMap b))
  let f : U' ⟶ pullback C.s (spMap b) := pullback.lift (r ≫ C.j) (c' ≫ spMap β') (by
    rw [Category.assoc, hjs, ← Category.assoc, hr, Category.assoc, Category.assoc, hsq])
  have f₁ : f ≫ pullback.fst _ _ = r ≫ C.j := pullback.lift_fst _ _ _
  let u : U' ⟶ pullback s₁ (spMap β') := pullback.lift f c' (pullback.lift_snd _ _ _)
  have u₁ : u ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have u₂ : u ≫ pullback.snd _ _ = c' := pullback.lift_snd _ _ _
  have hu : r ≫ C.jQ = u ≫ q := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, q₁, ← Category.assoc u, u₁, f₁, Cpt.j]
    · rw [Category.assoc, Category.assoc, q₂, ← Category.assoc u, u₂, C.jQ_over, hr]
  let g := pullback.snd C.jQ q
  let v : U' ⟶ pullback C.jQ q := pullback.lift r u hu
  have v₁ : v ≫ pullback.fst _ _ = r := pullback.lift_fst _ _ _
  have v₂ : v ≫ g = u := pullback.lift_snd _ _ _
  have hp : IsPullback (pullback.fst C.jQ q) (g ≫ pullback.snd _ _) c (spMap k) := by
    have := (IsPullback.of_hasPullback C.jQ q).paste_vert hq
    rwa [C.jQ_over] at this
  have hv : IsFinite v := by
    have e : v = pullback.lift r c' hr ≫ hp.isoPullback.inv := by
      rw [Iso.eq_comp_inv]
      apply pullback.hom_ext
      · rw [Category.assoc, hp.isoPullback_hom_fst, v₁, pullback.lift_fst]
      · rw [Category.assoc, hp.isoPullback_hom_snd, ← Category.assoc, v₂, u₂, pullback.lift_snd]
    rw [e]; infer_instance
  have hW : (v ≫ g.isoOpensRange.hom) ≫ g.opensRange.ι = u := by
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, v₂]
  obtain ⟨Y, π, jQ, hπ, hY, hproj, hflat, j₂, j₁, jo, jd, jr⟩ :=
    GlobalTheory.exists_normal_finite_model_of_finite_over_open O' F' _ U' s₁ c' f g.opensRange (v ≫ g.isoOpensRange.hom)
      (GlobalTheory.ProjSpace.isProjOver_pullback_snd b C.proj) hN inferInstance
      (by rw [← Category.assoc]; exact (congrArg (· ≫ _) hW).trans u₁)
      (by rw [← Category.assoc]; exact (congrArg (· ≫ _) hW).trans u₂)
  obtain ⟨pp, cub, sym, adj, prim, mu, hmu⟩ := sabPull Out.CubePf.cubePull (π ≫ pullback.fst C.s (spMap b)) C.t
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m ν
  have hj : (jQ ≫ pullback.fst (π ≫ s₁) (spMap β')) ≫ π ≫ pullback.fst C.s (spMap b) =
      r ≫ C.jQ ≫ pullback.fst _ _ := by
    refine Eq.trans ?_ f₁
    rw [← j₁]
    simp only [Category.assoc]
  obtain ⟨n', hn'⟩ : ∃ n' : SABMap t' C.t ((jQ ≫ pullback.fst (π ≫ s₁) (spMap β')) ≫ π ≫ pullback.fst C.s (spMap b)),
      n'.φ = ν.φ ≫ C.m.φ := by
    rw [hj]; exact ⟨n, hn⟩
  obtain ⟨m, hm⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mu n'
  have hg : ∀ p, p ∈ g.opensRange ↔ pullback.fst C.s (spMap b) (pullback.fst s₁ (spMap β') p) ∈ abLocus C.t.G := by
    intro p
    have e : pullback.fst C.s (spMap b) (pullback.fst s₁ (spMap β') p) = pullback.fst C.s (spMap β) (q p) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, q₁]
    rw [e]
    change p ∈ Set.range (pullback.snd C.jQ q) ↔ q p ∈ pullback.fst C.s (spMap β) ⁻¹' abLocus C.t.G
    rw [C.ab_gen, Scheme.Pullback.range_snd]
    rfl
  refine ⟨⟨Y, π ≫ s₁, hY, hproj, hflat, jQ, j₂, jo, jd, _, m, ?_⟩,
    ⟨⟨π ≫ pullback.fst _ _, ?_, ?_, mu, hj, hm.symm.trans hn'⟩⟩⟩
  · ext y
    refine Iff.trans ?_ (jr y).symm
    rw [Set.mem_preimage, ← abLocus_pullback abLocusOne C.t.semi mu.cart.1, Scheme.Hom.comp_apply]
    constructor
    · intro h
      let w : pullback (π ≫ s₁) (spMap β') ⟶ pullback s₁ (spMap β') :=
        pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
      have hw : pullback.fst s₁ (spMap β') (w y) = π (pullback.fst (π ≫ s₁) (spMap β') y) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
      refine ⟨⟨w y, (hg _).2 (by rw [hw]; exact h)⟩, ?_⟩
      exact (Scheme.Hom.comp_apply _ _ _).trans hw
    · rintro ⟨p, hp⟩
      replace hp := (Scheme.Hom.comp_apply _ _ _).symm.trans hp
      have := (hg p.1).1 p.2
      exact (congrArg (fun z => pullback.fst C.s (spMap b) z ∈ abLocus C.t.G) hp).mp this
  · simp only [Category.assoc, s₁, pullback.condition]
  · have key : ∀ h, IsFinite (pullback.lift (π ≫ pullback.fst C.s (spMap b)) (π ≫ s₁) h) := fun h => by
      have e : pullback.lift (π ≫ pullback.fst C.s (spMap b)) (π ≫ s₁) h = π := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
        · rw [pullback.lift_snd]
      rw [e]; exact hπ
    exact key _

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalModelAboveFiniteCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_model_above_finite_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (C : Cpt c t β) (b : O →+* O') (k : F →+* F') (r : U' ⟶ U) (hr : r ≫ c = c' ≫ spMap k) (ν : SABMap t' t r), IsDedFrac β → IsDedFrac β' → β'.comp b = k.comp β → IsNormalScheme U' → IsFinite (pullback.lift r c' hr) → ∃ C' : Cpt c' t' β', Nonempty (C'.Above C b r ν) := by
  first | exact @GlobalTheory.Models.Cpt.exists_above | exact GlobalTheory.Models.Cpt.exists_above | (intros; apply GlobalTheory.Models.Cpt.exists_above <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperOfCompleteDVRLiftGeneric
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperOfCompleteDVRLiftGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.ValuativeGeneric

theorem exists_lift_of_surjectiveOnStalks {X Z : Scheme.{0}} (j : X ⟶ Z) [SurjectiveOnStalks j]
    (K : Type) [Field K] (t : Spec (.of K) ⟶ Z) (x : X)
    (hx : t (IsLocalRing.closedPoint K) = j x) :
    ∃ u : Spec (.of K) ⟶ X, u ≫ j = t ∧ ∀ p, u p = x := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Z).symm.surjective t
  obtain rfl : z = j x := (Scheme.fromSpecResidueField_apply z
    (Spec.map φ (IsLocalRing.closedPoint K))).symm.trans hx
  have : IsIso (j.residueFieldMap x) := by
    refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(j.residueFieldMap x).hom.injective, ?_⟩
    intro a
    obtain ⟨b, rfl⟩ := X.residue_surjective x a
    obtain ⟨c, rfl⟩ := j.stalkMap_surjective x b
    refine ⟨Z.residue _ c, ?_⟩
    rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap]
    rfl
  refine ⟨Spec.map (inv (j.residueFieldMap x) ≫ φ) ≫ X.fromSpecResidueField x, ?_, fun p => by simp⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc]
  rfl

theorem isClosedImmersion_of_lift {X Z : Scheme.{0}} [IsLocallyNoetherian Z] [Z.IsSeparated]
    (j : X ⟶ Z) [IsPreimmersion j] [QuasiCompact j]
    (h : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K]
      (x : Sp K ⟶ X) (y : Sp V ⟶ Z), Set.range x ⊆ genericPoints X →
      x ≫ j = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) :
    IsClosedImmersion j := by
  refine .of_isPreimmersion j (IsClosedMap.isClosed_range ?_)
  rw [isClosedMap_iff_specializingMap]
  refine j.isEmbedding.isInducing.specializingMap ?_
  rintro _ z hz ⟨x, rfl⟩
  obtain ⟨x₀, hx₀, hs⟩ := exists_mem_genericPoints_specializes x
  have hs' : j x₀ ⤳ z := (hs.map j.continuous).trans hz
  by_cases hne : j x₀ = z
  · exact ⟨x₀, hne⟩
  obtain ⟨O, _, _, _, g, hg₀, hg₁⟩ := exists_complete_discreteValuationRing_of_specializes hs' hne
  have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective _ _
  have hpt : (spMap (algebraMap O (FractionRing O)) ≫ g)
      (IsLocalRing.closedPoint (FractionRing O)) = j x₀ := by
    refine Eq.trans (congrArg g (PrimeSpectrum.ext ?_)) hg₀
    change Ideal.comap (algebraMap O (FractionRing O)) (IsLocalRing.maximalIdeal _) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ hinj
  obtain ⟨u, hu, hux⟩ := exists_lift_of_surjectiveOnStalks j (FractionRing O) _ x₀ hpt
  obtain ⟨x', hx'⟩ := h O (FractionRing O) u g (by rintro _ ⟨p, rfl⟩; rw [hux]; exact hx₀) hu
  have : IsDominant (spMap (algebraMap O (FractionRing O))) := by
    refine ⟨?_⟩
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_
    exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
  have e : x' ≫ j = g :=
    ext_of_isDominant (spMap (algebraMap O (FractionRing O))) (by rw [← Category.assoc, hx', hu])
  exact ⟨x' (IsLocalRing.closedPoint O), by rw [← hg₁, ← e]; rfl⟩

theorem isProper_of_lift_generic : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (f : X ⟶ Y) (s : Y ⟶ Sp R), IsSeparated s → IsQProjOver (f ≫ s) → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Y), Set.range x ⊆ genericPoints X → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  intro R _ _ X Y _ f s hs ⟨N, i, hi, hq, e⟩ h
  have := isProper_str R N
  let j : X ⟶ pullback s (PSpace.str R N) := pullback.lift f i e.symm
  have hj₁ : j ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have hj₂ : j ≫ pullback.snd _ _ = i := pullback.lift_snd _ _ _
  have : IsImmersion (j ≫ pullback.snd _ _) := hj₂ ▸ hi
  have : QuasiCompact (j ≫ pullback.snd _ _) := hj₂ ▸ hq
  have : IsImmersion j := IsImmersion.of_comp j (pullback.snd _ _)
  have : QuasiCompact j := QuasiCompact.of_comp j (pullback.snd _ _)
  have : IsLocallyNoetherian (pullback s (PSpace.str R N)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst _ _)
  have : (pullback s (PSpace.str R N)).IsSeparated := by
    refine ⟨?_⟩
    rw [← terminal.comp_from (pullback.fst s (PSpace.str R N) ≫ s)]
    infer_instance
  have : IsClosedImmersion j := isClosedImmersion_of_lift j fun V K _ _ _ _ _ _ _ x y hx hy =>
    h V K x (y ≫ pullback.fst _ _) hx (by rw [← hj₁, ← Category.assoc, hy, Category.assoc])
  rw [← hj₁]
  infer_instance

end GlobalTheory.ValuativeGeneric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperOfCompleteDVRLiftGenericStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_completeDVR_lift_generic : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (f : X ⟶ Y) (s : Y ⟶ Sp R), IsSeparated s → IsQProjOver (f ≫ s) → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Y), Set.range x ⊆ genericPoints X → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  first | exact @GlobalTheory.ValuativeGeneric.isProper_of_lift_generic | exact GlobalTheory.ValuativeGeneric.isProper_of_lift_generic | (intros; apply GlobalTheory.ValuativeGeneric.isProper_of_lift_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeOfExistsRelAmple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem cube_of_exists_relAmple {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {H₀ : LB B.left} (hH : H₀.IsLB) (hamp : Out.RelAmple B H₀)
    {M : LB B.left} (hM : M.IsLB) : ∃ t : LB.Gen (Theta B M), t.IsGen := by
  have hG := GlobalTheory.laws_without_cohomology.1
  exact GlobalTheory.Biadditive.triv_of_faces hG hB hH hamp hM (thφ B (x3 B)) thε
    (fun r i b h => GlobalTheory.AbLaw.CubeGen.trivAt_of_formal hM r (GlobalTheory.AbLaw.CubeGen.prod_face r i b h))
    (fun r b h U _ k => GlobalTheory.AbLaw.CubeGen.prod_face r 0 b h U k)

theorem cube_of_relAmple :
    ∀ (S : Scheme.{0}) [IsReduced S] (B : Over S) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∃ t : LB.Gen (Theta B M), t.IsGen := fun _ _ _ _ _ _ hB hM hamp => cube_of_exists_relAmple hB hM hamp hM

end GlobalTheory.HkFam
end
