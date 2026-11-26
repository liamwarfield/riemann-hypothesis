module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwo

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftCompPG
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp.LevelCmp

theorem lift_comp_pG {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A)
    (hab : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ b.left)
    {A₂ : PolAV (Sp (FractionRing R))} {D₂ : DegData R (maximalIdeal R)} (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (β : D₂.toPre.P.A ≅ D.toPre.P.A) (hβ : ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left)
    (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left) (hh' : h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left) :
    h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom b 0 := by
  classical
  haveI := GlobalTheory.TorsionTranslate.mono_fst (I := maximalIdeal R) e G
  have hs : (thick R (maximalIdeal R) e ≫ a.left) ≫ G.hom = 𝟙 (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))).left ≫ thick R (maximalIdeal R) e := by
    rw [Category.assoc, Over.w a]; simp
  let ae : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶ thickObj R (maximalIdeal R) e G :=
    Over.homMk (pullback.lift (thick R (maximalIdeal R) e ≫ a.left) (𝟙 (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))).left) hs) (pullback.lift_snd _ _ _)
  have hae : ae.left ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left := pullback.lift_fst _ _ _
  have heq : h = (GlobalTheory.MumCmp.Transl.tr ae).left :=
    (cancel_mono (fstG (maximalIdeal R) e G).left).1 (by rw [hh', GlobalTheory.MumCmp.Transl.tr_fst hae])
  have h₁ := GlobalTheory.TorusCoord.im_mul (U.gt e) (toUnit (thickObj R (maximalIdeal R) e G) ≫ ae) (𝟙 (thickObj R (maximalIdeal R) e G))
  have h₂ : GlobalTheory.TorusCoord.im (U.gt e) (toUnit (thickObj R (maximalIdeal R) e G) ≫ ae) = toUnit _ ≫ b := by
    ext
    have := hab e ae.left (Over.w ae) hae
    simp [GlobalTheory.TorusCoord.im] at this ⊢
    rw [this]
  have h₃ : GlobalTheory.TorusCoord.im (U.gt e) (𝟙 (thickObj R (maximalIdeal R) e G)) = (U₂.gt e).pG ≫ β.hom := by
    ext
    have := (hβ e).symm
    simp [GlobalTheory.TorusCoord.im] at this ⊢
    exact this
  have h₅ : GlobalTheory.TorusCoord.im (U.gt e) (GlobalTheory.MumCmp.Transl.tr ae) = (U₂.gt e).pG ≫ (β.hom * (toUnit D₂.toPre.P.A ≫ b)) := by
    rw [GlobalTheory.MumCmp.Transl.tr, h₁, h₂, h₃, comp_mul, comp_toUnit_assoc, mul_comm]
  rw [heq]
  exact congrArg Over.Hom.left h₅

end GlobalTheory.MumCmp.LevelCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorRatioTranslationTwistIsos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorRatioTranslationTwistIsos
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TwRatio

theorem exists_ratio_gen {X A : Scheme.{0}} {M : LB X} {L₀ : LB A} (hM : M.IsLB) (hL₀ : L₀.IsLB)
    {K : Type} [Fintype K] (φ : K → (A ⟶ X)) (ε : K → ℤ) (F : A ⟶ X)
    (w : LB.Iso L₀ (LB.LinComb M φ ε)) (hw : w.IsGen) (W : LB.Iso L₀ (M.pull F)) (hW : W.IsGen) :
    ∃ τ : LB.Gen (LB.LinComb M (Sum.elim φ (fun _ : PUnit => F)) (Sum.elim ε (fun _ => -1))), τ.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) (J : (Z ⟶ X) → M.ι) (j' : L₀.ι), Good M z J → r z ∈ L₀.U j' →
        val τ r z J = gv w r z (fun k => J (r ≫ φ k)) j' * (gw W r z (J (r ≫ F)) j')⁻¹ := by
  classical
  have pW := (isGen_iff W).1 hW
  have l1 : ∀ (j : K ⊕ PUnit → M.ι) k, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k ≤
      (LB.LinComb M φ ε).U (j ∘ Sum.inl) ⊓ L₀.U k := fun j k y hy =>
    ⟨Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy.1 (Sum.inl i), hy.2⟩
  have l2 : ∀ (j : K ⊕ PUnit → M.ι) k, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k ≤
      (M.pull F).U (fun _ => j (Sum.inr PUnit.unit)) ⊓ L₀.U k := fun j k y hy =>
    ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 (Sum.inr PUnit.unit), hy.2⟩
  let u : ∀ (j : K ⊕ PUnit → M.ι) k, Γ(A, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k)ˣ := fun j k =>
    res (l1 j k) (w.s (j ∘ Sum.inl, k)) * (res (l2 j k) (W.s (fun _ => j (Sum.inr PUnit.unit), k)))⁻¹
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) j k, r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k →
      gm r z _ (u j k) = gv w r z (j ∘ Sum.inl) k * (gw W r z (j (Sum.inr PUnit.unit)) k)⁻¹ :=
    fun Z r z j k hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _)
      ((map_inv _ _).trans (congrArg _ (gm_res r z _ hz _))))
  have rel : ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) (j j' : K ⊕ PUnit → M.ι) (k k' : L₀.ι),
      r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j → r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j' →
      r z ∈ L₀.U k → r z ∈ L₀.U k' →
      gv w r z (j ∘ Sum.inl) k * (gw W r z (j (Sum.inr PUnit.unit)) k)⁻¹ =
        trF (Sum.elim φ (fun _ : PUnit => F)) (Sum.elim ε (fun _ => -1)) r z j j' *
          (gv w r z (j' ∘ Sum.inl) k' * (gw W r z (j' (Sum.inr PUnit.unit)) k')⁻¹) := by
    intro Z r z j j' k k' hj hj' hk hk'
    have key : ∀ {G : Type} [CommGroup G] (a c d x y : G), a * c⁻¹ * x * (d * c⁻¹ * y)⁻¹ = a * d⁻¹ * (x * y⁻¹) :=
      fun a c d x y => by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
    have a₁ : r z ∈ (LB.LinComb M φ ε).U (j ∘ Sum.inl) := Set.mem_iInter.2 fun i => Set.mem_iInter.1 hj (Sum.inl i)
    have a₂ : r z ∈ (LB.LinComb M φ ε).U (j' ∘ Sum.inl) := Set.mem_iInter.2 fun i => Set.mem_iInter.1 hj' (Sum.inl i)
    have b₁ : F (r z) ∈ M.U (j (Sum.inr PUnit.unit)) := Set.mem_iInter.1 hj (Sum.inr PUnit.unit)
    have b₂ : F (r z) ∈ M.U (j' (Sum.inr PUnit.unit)) := Set.mem_iInter.1 hj' (Sum.inr PUnit.unit)
    have e := gm_linComb M φ ε r z _ _ a₁ a₂
    rw [gm_isGen hw r z _ _ k k' a₁ a₂ hk hk', pW Z r z _ _ k k' b₁ b₂ hk hk']
    erw [e]
    rw [trF, Fintype.prod_sum_type]
    simp only [Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, zpow_neg, zpow_one]
    exact key _ _ _ _ _
  have glue : ∀ j : K ⊕ PUnit → M.ι, ∃ s : Γ(A, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j)ˣ,
      ∀ k, res (inf_le_left : LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k ≤ _) s = u j k := fun j =>
    glue_unit _ (fun k => LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k) (fun _ => inf_le_left)
      (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL₀ y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩) (u j)
      (fun k k' y hy => by
        rw [hu _ _ y j k hy.1, hu _ _ y j k' hy.2, rel _ (𝟙 A) y j j k k' hy.1.1 hy.1.1 hy.1.2 hy.2.2,
          trF_self hM _ _ (𝟙 A) y hy.1.1, _root_.one_mul])
  choose s hs using glue
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) j k, r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j →
      r z ∈ L₀.U k → gm r z _ (s j) = gv w r z (j ∘ Sum.inl) k * (gw W r z (j (Sum.inr PUnit.unit)) k)⁻¹ :=
    fun Z r z j k hj hk => (gm_res r z _ (show r z ∈ _ ⊓ L₀.U k from ⟨hj, hk⟩) (s j)).symm.trans
      ((congrArg (gm r z _) (hs j k)).trans (hu Z r z j k ⟨hj, hk⟩))
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z J j' hJ hj' => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL₀ y
    exact (hv _ (𝟙 A) y j k hj hk).trans ((rel _ (𝟙 A) y j j' k k hj hj' hk hk).trans
      (congrArg _ (hv _ (𝟙 A) y j' k hj' hk).symm))
  · exact hv Z r z _ j' (hJ.mem _ r) hj'

end GlobalTheory.MumCmp.TwRatio

namespace GlobalTheory.MumCmp.TwRatio

theorem exists_twist_ratio : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A) (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (w : LB.Iso D₀.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₀ D β b) GlobalTheory.MumCmp.twε)) (hw : w.IsGen)
    (W : LB.Iso D₀.P.L (D.P.L.pull (GlobalTheory.MumCmp.twφ D₀ D β b 0))) (hW : W.IsGen),
    ∃ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![b.left, η[D.P.A].left] ![-1, 1]), ν.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D₀.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (j' : D₀.P.L.ι),
        Geo.Tor.Good D.P.L z J → r z ∈ D₀.P.L.U j' →
        Geo.Tor.gv w r z (fun i => J (r ≫ GlobalTheory.MumCmp.twφ D₀ D β b i)) j' =
          Geo.Tor.gw W r z (J (r ≫ GlobalTheory.MumCmp.twφ D₀ D β b 0)) j' * Geo.Tor.val ν (r ≫ D₀.P.A.hom) z J := by
  intro R _ _ _ D₀ D β b w hw W hW
  classical
  obtain ⟨τ, hτ, vτ⟩ := exists_ratio_gen D.P.isLB D₀.P.isLB (GlobalTheory.MumCmp.twφ D₀ D β b) GlobalTheory.MumCmp.twε
    (GlobalTheory.MumCmp.twφ D₀ D β b 0) w hw W hW
  obtain ⟨t₀, ht₀⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (K := Fin 2) ![b.left, η[D.P.A].left] ![-1, 1]
  have hF : FormEq (Sum.elim (GlobalTheory.MumCmp.twφ D₀ D β b) (fun _ : PUnit => GlobalTheory.MumCmp.twφ D₀ D β b 0))
      (Sum.elim GlobalTheory.MumCmp.twε (fun _ => -1))
      (fun k => D₀.P.A.hom ≫ (![b.left, η[D.P.A].left] : Fin 2 → ((𝟙_ (Over (Sp R))).left ⟶ D.P.A.left)) k)
      ![-1, 1] := by
    intro U _ h
    have e1 : GlobalTheory.MumCmp.twφ D₀ D β b 1 = D₀.P.A.hom ≫ b.left := rfl
    have e2 : GlobalTheory.MumCmp.twφ D₀ D β b 2 = D₀.P.A.hom ≫ η[D.P.A].left := rfl
    rw [Fintype.prod_sum_type, Fin.prod_univ_three, Fin.prod_univ_two]
    simp only [Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, e1, e2, GlobalTheory.MumCmp.twε, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨τ', hτ', vτ'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen D.P.isLB hF τ hτ
  obtain ⟨a, ha⟩ := GlobalTheory.AbPackage.exists_unit_ratio D.P.isLB hτ' (DVR.pullGen_isGen _ _ _ t₀ ht₀ D₀.P.A.hom)
  have hG := GlobalTheory.globalFns_holds _ D₀.P.A D₀.P.isAb
  obtain ⟨c, hc⟩ := hG.2 a.val
  obtain ⟨c', hc'⟩ := hG.2 (a⁻¹).val
  have hcc : c * c' = 1 := hG.1 (by rw [map_mul, hc, hc', Units.mul_inv, map_one])
  let cu : Γ(Sp R, ⊤)ˣ := ⟨c, c', hcc, (mul_comm c' c).trans hcc⟩
  have hcu : pullU D₀.P.A.hom ⊤ cu = a := Units.ext hc
  obtain ⟨ν, hν, vν⟩ := GlobalTheory.TorsionTranslate.exists_scale t₀ ht₀ cu
  refine ⟨ν, hν, fun Z r z J j' hJ hj' => ?_⟩
  have e1 := vτ Z r z J j' hJ hj'
  have e2 := vτ' Z r z J hJ
  have e3 := ha Z r z J hJ
  have e4 := val_pull hJ t₀ D₀.P.A.hom r
  have e5 := vν Z (r ≫ D₀.P.A.hom) z J hJ
  have e6 : gm r z ⊤ a = gm (r ≫ D₀.P.A.hom) z ⊤ cu := by
    rw [← hcu]; exact gm_pull r D₀.P.A.hom z ⊤ trivial cu
  rw [e5, ← e6, ← e4, ← e3, e2, e1, mul_left_comm, mul_inv_cancel, _root_.mul_one]

end GlobalTheory.MumCmp.TwRatio
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorRatioTranslationTwistIsosStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_ratio_translationTwist_isos : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A) (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (w : LB.Iso D₀.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₀ D β b) GlobalTheory.MumCmp.twε)) (hw : w.IsGen)
    (W : LB.Iso D₀.P.L (D.P.L.pull (GlobalTheory.MumCmp.twφ D₀ D β b 0))) (hW : W.IsGen),
    ∃ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![b.left, η[D.P.A].left] ![-1, 1]), ν.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D₀.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (j' : D₀.P.L.ι),
        Geo.Tor.Good D.P.L z J → r z ∈ D₀.P.L.U j' →
        Geo.Tor.gv w r z (fun i => J (r ≫ GlobalTheory.MumCmp.twφ D₀ D β b i)) j' =
          Geo.Tor.gw W r z (J (r ≫ GlobalTheory.MumCmp.twφ D₀ D β b 0)) j' * Geo.Tor.val ν (r ≫ D₀.P.A.hom) z J := by
  first | exact @GlobalTheory.MumCmp.TwRatio.exists_twist_ratio | exact GlobalTheory.MumCmp.TwRatio.exists_twist_ratio | (intros; apply GlobalTheory.MumCmp.TwRatio.exists_twist_ratio <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalIsoTranslatedBundleLevelComparison
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalIsoTranslatedBundleLevelComparison
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TranslLev

open GlobalTheory.MumCmp.Transl UnifCompare

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G]


set_option maxHeartbeats 800000 in
theorem exists_iso_translate_levels [IsLocalRing R] (hR : AdmBase R I) (hG : IsSemiAbelian G) {D D' : DegData R I}
    {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (a : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G) (ha : a ^ 2 = 1) (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.toPre.P.A)
    (hab : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left),
      ae ≫ (thickObj R I e G).hom = 𝟙 _ → ae ≫ (fstG I e G).left = thick R I e ≫ a.left →
      ae ≫ (U.gt e).pG.left = thick R I e ≫ b.left)
    (wL : LB.Iso U'.LG.L (U.LG.L.pull (tr a).left)) (hw : wL.IsGen) (β : D'.toPre.P.A ≅ D.toPre.P.A)
    (hβ : ∀ e, (U'.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) :
    ∃ w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull (padd D.toPre.P.A β.hom (toUnit D'.toPre.P.A ≫ b)).left),
      w.IsGen ∧ ∀ (e : ℕ) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left),
        h ≫ (fstG I e G).left = (fstG I e G).left ≫ (tr a).left →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
          (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
        (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
        (tr a).left ((fstG I e G).left (r z)) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
        gw w (r ≫ (U'.gt e).pG.left) z jM jM' * gw (U'.w e) r z jM' (fun _ => jL') =
          gw (U.w e) (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL' := by
  rw [isGen_iff] at hw
  obtain ⟨hf, hs⟩ := surjective_appTop U
  obtain ⟨ae, hae⟩ : ∃ ae : ∀ e, 𝟙_ _ ⟶ thickObj R I e G,
      ∀ e, (ae e).left ≫ (fstG I e G).left = thick R I e ≫ a.left :=
    ⟨fun e => Over.homMk (pullback.lift (thick R I e ≫ a.left) (𝟙 _) (by
      rw [Category.assoc, Over.w a]; exact (Category.comp_id _).trans (Category.id_comp _).symm))
      (pullback.lift_snd _ _ _), fun e => pullback.lift_fst _ _ _⟩
  let Φ : D'.toPre.P.A ≅ D.toPre.P.A :=
    { hom := β.hom * (toUnit _ ≫ b)
      inv := (𝟙 _ * (toUnit _ ≫ b)⁻¹) ≫ β.inv
      hom_inv_id := by
        rw [← Category.assoc, MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, ← Category.assoc, comp_toUnit,
          mul_inv_cancel_right, β.hom_inv_id]
      inv_hom_id := by
        rw [MonObj.comp_mul, Category.assoc, β.inv_hom_id, Category.comp_id, ← Category.assoc, comp_toUnit,
          inv_mul_cancel_right] }
  let βe : ∀ e, thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A := fun e =>
    (Over.pullback (thick R I e)).mapIso Φ
  have hβe : ∀ e, (βe e).hom.left ≫ (fstG I e D.toPre.P.A).left = (fstG I e D'.toPre.P.A).left ≫ Φ.hom.left :=
    fun e => pullback.lift_fst _ _ _
  have hb : ∀ e, (tr (ae e)).left ≫ (U.gt e).pG.left =
      (U'.gt e).q.left ≫ (βe e).hom.left ≫ (fstG I e D.toPre.P.A).left := fun e => by
    have h₁ := TorusCoord.im_mul (U.gt e) (toUnit _ ≫ ae e) (𝟙 (thickObj R I e G))
    have h₂ : TorusCoord.im (U.gt e) (toUnit (thickObj R I e G) ≫ ae e) = toUnit _ ≫ b := by
      apply Over.OverMorphism.ext
      show ((thickObj R I e G).hom ≫ (ae e).left) ≫ (U.gt e).pG.left = ((thickObj R I e G).hom ≫ thick R I e) ≫ b.left
      rw [Category.assoc, Category.assoc]
      exact congrArg ((thickObj R I e G).hom ≫ ·) (hab e _ (Over.w (ae e)) (hae e))
    have h₃ : TorusCoord.im (U.gt e) (𝟙 (thickObj R I e G)) = (U'.gt e).pG ≫ β.hom :=
      Over.OverMorphism.ext ((Category.id_comp _).trans (hβ e).symm)
    have h₄ : (U'.gt e).pG ≫ Φ.hom = ((U'.gt e).pG ≫ β.hom) * (toUnit _ ≫ b) := by
      show (U'.gt e).pG ≫ (β.hom * (toUnit _ ≫ b)) = _
      rw [MonObj.comp_mul, ← Category.assoc _ (toUnit _), comp_toUnit]
    rw [h₂, h₃, _root_.mul_comm (toUnit _ ≫ b), ← h₄] at h₁
    rw [hβe]
    exact (congrArg (fun q => q.left) h₁).trans (Category.assoc (U'.gt e).q.left _ _)
  choose v hvg hv using fun e => exists_level (hae e) hw hG ha hf hs β.hom (hβ e) _ (hb e)
  have hc : ∀ e, thickMap R I e D'.toPre.P.A ≫ (βe (e + 1)).hom.left =
      (βe e).hom.left ≫ thickMap R I e D.toPre.P.A := fun e => thickMap_comm e _ _ _ (hβe e) (hβe (e + 1))
  have ht : ∀ e, thickMap R I e G ≫ (tr (ae (e + 1))).left = (tr (ae e)).left ≫ thickMap R I e G := fun e =>
    thickMap_comm e _ _ _ (tr_fst (hae e)) (tr_fst (hae (e + 1)))
  obtain ⟨hN, -, -, hC⟩ := hR
  obtain ⟨Ψ, w, hwg, H⟩ := exists_iso_of_compatible_thickenings GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    GlobalTheory.abelianSchemeLaws_all.1.ample R I D.toPre.P D'.toPre.P βe v hvg hc (by
    intro e Z r z j j' hj hj'
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have hm : ∀ y : (thickObj R I e D'.toPre.P.A).left,
        y ∈ (D.toPre.P.L.pull ((βe e).hom.left ≫ (fstG I e D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left).U (fun _ => j') →
        thickMap R I e D'.toPre.P.A y ∈
          (D.toPre.P.L.pull ((βe (e + 1)).hom.left ≫ (fstG I (e + 1) D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I (e + 1) D'.toPre.P.A).left).U (fun _ => j') := by
      intro y hy
      have k : thickMap R I e D'.toPre.P.A ≫ (βe (e + 1)).hom.left ≫ (fstG I (e + 1) D.toPre.P.A).left =
          (βe e).hom.left ≫ (fstG I e D.toPre.P.A).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I (e + 1) D.toPre.P.A).left) (hc e)).trans
          ((Category.assoc _ _ _).trans (congrArg ((βe e).hom.left ≫ ·) (trans_comp_proj e _))))
      exact ⟨mem_pull.2 ((congrArg (fun g => g y ∈ D.toPre.P.L.U j) k).mpr (mem_pull.1 hy.1)),
        mem_pull.2 ((congrArg (fun g => g y ∈ D'.toPre.P.L.U j') (trans_comp_proj e _)).mpr
          (mem_pull.1 hy.2))⟩
    have hz : r z ∈ (D.toPre.P.L.pull ((βe e).hom.left ≫ (fstG I e D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left).U (fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    refine (gm_pull r _ z _ (hm _ hz) _).symm.trans
      (gm_eq_of_flat_surjective (U'.gt e).q.left _ _ (fun x _ hx => ?_) r z (hm _ hz) hz)
    refine (gm_pull _ _ x _ (hm _ hx) _).trans ?_
    obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB ((tr a).left ((fstG I e G).left x))
    obtain ⟨jL', hL'⟩ := exists_chart U'.LG.isLB ((fstG I e G).left x)
    have hM : (U.gt e).pG.left ((tr (ae e)).left x) ∈ D.toPre.P.L.U j :=
      (congrArg (fun g => g x ∈ D.toPre.P.L.U j) (hb e)).mpr (mem_pull.1 hx.1)
    have hM' : (U'.gt e).pG.left x ∈ D'.toPre.P.L.U j' := mem_pull.1 hx.2
    have k₁ : (thickMap R I e G ≫ (tr (ae (e + 1))).left) ≫ (U.gt (e + 1)).pG.left =
        (tr (ae e)).left ≫ (U.gt e).pG.left :=
      (congrArg (· ≫ (U.gt (e + 1)).pG.left) (ht e)).trans ((Category.assoc _ _ _).trans
        (congrArg ((tr (ae e)).left ≫ ·) (U.gt_q e)))
    have h₀ := hv e _ (𝟙 _) x j j' jL jL' hM hM' hL hL'
    have h₁ := hv (e + 1) _ (thickMap R I e G) x j j' jL jL'
      ((congrArg (fun g => g x ∈ D.toPre.P.L.U j) k₁).mpr hM)
      ((congrArg (fun g => g x ∈ D'.toPre.P.L.U j') (U'.gt_q e)).mpr hM')
      ((congrArg (fun g => (tr a).left (g x) ∈ U.LG.L.U jL) (trans_comp_proj e G)).mpr hL)
      ((congrArg (fun g => g x ∈ U'.LG.L.U jL') (trans_comp_proj e G)).mpr hL')
    rw [gw_trans U' e x j' jL' hM' hL', ht, gw_trans' U e (tr (ae e)).left x j jL hM
      ((congrArg (fun g => g x ∈ U.LG.L.U jL) (tr_fst (hae e))).mpr hL), trans_comp_q, trans_comp_proj] at h₁
    rw [Category.id_comp, Category.id_comp, Category.id_comp] at h₀
    exact mul_right_cancel (h₁.trans h₀.symm))
  have := D'.toPre.P.isAb.proper
  have := D.toPre.P.isAb.proper
  have eΨ : Ψ.hom = padd D.toPre.P.A β.hom (toUnit D'.toPre.P.A ≫ b) :=
    hom_eq_of_thickenings_of_isProper R I (IsAdicComplete.le_jacobson_bot I) _ _ Ψ.hom Φ.hom
      fun e => (H e).1.trans (hβe e)
  have eΨ' : (padd D.toPre.P.A β.hom (toUnit D'.toPre.P.A ≫ b)).left = Ψ.hom.left := by rw [eΨ]
  rw [eΨ']
  refine ⟨w, hwg, fun e h hh Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  haveI := GlobalTheory.TorsionTranslate.mono_fst (I := I) e G
  have heq : h = (tr (ae e)).left := (cancel_mono (fstG I e G).left).1 (by rw [hh, tr_fst (hae e)])
  subst heq
  have hq : (U'.gt e).pG.left = (U'.gt e).q.left ≫ (fstG I e D'.toPre.P.A).left := rfl
  have m₁ : (fstG I e D.toPre.P.A).left ((βe e).hom.left ((r ≫ (U'.gt e).q.left) z)) ∈ D.toPre.P.L.U jM :=
    (congrArg (fun g => g (r z) ∈ D.toPre.P.L.U jM) (hb e)).mp a₁
  have m₂ : (fstG I e D'.toPre.P.A).left ((r ≫ (U'.gt e).q.left) z) ∈ D'.toPre.P.L.U jM' :=
    (congrArg (fun g => g (r z) ∈ D'.toPre.P.L.U jM') hq).mp a₂
  have k := (H e).2 Z (r ≫ (U'.gt e).q.left) z jM jM' m₁ m₂
  have k' : gw w (r ≫ (U'.gt e).pG.left) z jM jM' = gw (v e) (r ≫ (U'.gt e).q.left) z jM (fun _ => jM') :=
    (congrArg (fun g => gw w g z jM jM') (show r ≫ (U'.gt e).pG.left =
      (r ≫ (U'.gt e).q.left) ≫ (fstG I e D'.toPre.P.A).left by rw [hq, Category.assoc])).trans k
  rw [← hv e Z r z jM jM' jL jL' a₁ a₂ a₃ a₄, k']

end GlobalTheory.MumCmp.TranslLev

theorem GlobalTheory.MumCmp.TranslLev.exists_iso_translate_global : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (ha : a ^ 2 = 1) (b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A)
    (hab : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ b.left)
    {A₂ : PolAV (Sp (FractionRing R))} {D₂ : DegData R (maximalIdeal R)} (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)) (hwL : wL.IsGen) (β : D₂.toPre.P.A ≅ D.toPre.P.A) (hβ : ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left),
    ∃ W : LB.Iso D₂.toPre.P.L (D.toPre.P.L.pull (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom b 0)), W.IsGen ∧
      ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D₂.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U₂.LG.L.ι),
        (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U jM → (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U jM' →
        ((toUnit G ≫ a) * 𝟙 G).left ((fstG (maximalIdeal R) e G).left (r z)) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U₂.LG.L.U jL' →
        Geo.Tor.gw W (r ≫ (U₂.gt e).pG.left) z jM jM' * Geo.Tor.gw (U₂.w e) r z jM' (fun _ => jL') =
          Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG (maximalIdeal R) e G).left) z jL jL' := by
  intro R _ _ _ hR D A G _ _ hG U a ha b hab A₂ D₂ U₂ wL hwL β hβ
  obtain ⟨W, hW, hv⟩ := GlobalTheory.MumCmp.TranslLev.exists_iso_translate_levels hR.1 hG U.toUnifPre U₂.toUnifPre a ha b
    hab wL hwL β hβ
  exact ⟨W, hW, fun e h _ hh Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => hv e h hh Z r z jM jM' jL jL' a₁ a₂ a₃ a₄⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalIsoTranslatedBundleLevelComparisonStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_iso_translated_bundle_levelComparison : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (ha : a ^ 2 = 1) (b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A)
    (hab : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ b.left)
    {A₂ : PolAV (Sp (FractionRing R))} {D₂ : DegData R (maximalIdeal R)} (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)) (hwL : wL.IsGen) (β : D₂.toPre.P.A ≅ D.toPre.P.A) (hβ : ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left),
    ∃ W : LB.Iso D₂.toPre.P.L (D.toPre.P.L.pull (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom b 0)), W.IsGen ∧
      ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D₂.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U₂.LG.L.ι),
        (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U jM → (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U jM' →
        ((toUnit G ≫ a) * 𝟙 G).left ((fstG (maximalIdeal R) e G).left (r z)) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U₂.LG.L.U jL' →
        Geo.Tor.gw W (r ≫ (U₂.gt e).pG.left) z jM jM' * Geo.Tor.gw (U₂.w e) r z jM' (fun _ => jL') =
          Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG (maximalIdeal R) e G).left) z jL jL' := by
  first | exact @GlobalTheory.MumCmp.TranslLev.exists_iso_translate_global | exact GlobalTheory.MumCmp.TranslLev.exists_iso_translate_global | (intros; apply GlobalTheory.MumCmp.TranslLev.exists_iso_translate_global <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelComparisonGeneratorOfUniformisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp.LevelCmp

theorem exists_level_gen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)), wL.IsGen → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∃ ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1]), ν.IsGen ∧ ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.gv w (r ≫ (U₂.gt e).pG.left) z (fun i => J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ (U₂.gt e).pG.left)) * Geo.Tor.gw (U₂.w e) r z (J' (r ≫ (U₂.gt e).pG.left)) (fun _ => N' (r ≫ (fstG (maximalIdeal R) e G).left)) = Geo.Tor.gw (U.w e) (r ≫ h) z (J (r ≫ h ≫ (U.gt e).pG.left)) (fun _ => N (r ≫ h ≫ (fstG (maximalIdeal R) e G).left)) * Geo.Tor.gw wL (r ≫ (fstG (maximalIdeal R) e G).left) z (N (r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' (r ≫ (fstG (maximalIdeal R) e G).left)) * Geo.Tor.val ν (r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e) z J := by
  intro R _ _ _ hR D A G _ _ hG U g hg a ha hab A₂ D₂ U₂ wL hwL β hβm hβ w hw
  have hab' : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left :=
    fun e ae h1 h2 => (hab e ae h1 h2).1
  obtain ⟨W, hW, HW⟩ := GlobalTheory.T.exists_global_iso_translated_bundle_levelComparison hR hG U a ha g.b hab' U₂ wL hwL β hβ
  obtain ⟨ν, hν, Hν⟩ := GlobalTheory.T.exists_generator_ratio_translationTwist_isos D₂.toPre D.toPre β.hom g.b w hw W hW
  refine ⟨ν, hν, ?_⟩
  intro e h hh hh' Z r z J J' N N' hJ hJ' hN hN'
  have k0 := lift_comp_pG U a g.b hab' U₂ β hβ e h hh'
  have hm : r ≫ h ≫ (U.gt e).pG.left = (r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0 := by
    rw [k0, Category.assoc]
  have hf : r ≫ h ≫ (fstG (maximalIdeal R) e G).left = r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left := by
    rw [hh']
  have hs : (r ≫ (U₂.gt e).pG.left) ≫ D₂.toPre.P.A.hom = r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e := by
    rw [Category.assoc, Over.w]; rfl
  have k2 := Hν Z (r ≫ (U₂.gt e).pG.left) z J (J' (r ≫ (U₂.gt e).pG.left)) hJ (hJ' _)
  have m1 : (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U (J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0)) := by
    have m1' : (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U (J (r ≫ h ≫ (U.gt e).pG.left)) := by
      simpa using hJ (r ≫ h ≫ (U.gt e).pG.left)
    rw [hm] at m1'
    exact m1'
  have m2 : (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U (J' (r ≫ (U₂.gt e).pG.left)) := by
    simpa using hJ' (r ≫ (U₂.gt e).pG.left)
  have m3 : ((toUnit G ≫ a) * 𝟙 G).left ((fstG (maximalIdeal R) e G).left (r z)) ∈ U.LG.L.U (N (r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) := by
    simpa using hN (r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)
  have m4 : (fstG (maximalIdeal R) e G).left (r z) ∈ U₂.LG.L.U (N' (r ≫ (fstG (maximalIdeal R) e G).left)) := by
    simpa using hN' (r ≫ (fstG (maximalIdeal R) e G).left)
  have k1 := HW e h hh hh' Z r z _ _ _ _ m1 m2 m3 m4
  rw [k2, hs, mul_right_comm, k1, hm, hf]

end GlobalTheory.MumCmp.LevelCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelComparisonGeneratorOfUniformisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelComparison_generator_of_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)), wL.IsGen → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∃ ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1]), ν.IsGen ∧ ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.gv w (r ≫ (U₂.gt e).pG.left) z (fun i => J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ (U₂.gt e).pG.left)) * Geo.Tor.gw (U₂.w e) r z (J' (r ≫ (U₂.gt e).pG.left)) (fun _ => N' (r ≫ (fstG (maximalIdeal R) e G).left)) = Geo.Tor.gw (U.w e) (r ≫ h) z (J (r ≫ h ≫ (U.gt e).pG.left)) (fun _ => N (r ≫ h ≫ (fstG (maximalIdeal R) e G).left)) * Geo.Tor.gw wL (r ≫ (fstG (maximalIdeal R) e G).left) z (N (r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' (r ≫ (fstG (maximalIdeal R) e G).left)) * Geo.Tor.val ν (r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e) z J := by
  first | exact @GlobalTheory.MumCmp.LevelCmp.exists_level_gen | exact GlobalTheory.MumCmp.LevelCmp.exists_level_gen | (intros; apply GlobalTheory.MumCmp.LevelCmp.exists_level_gen <;> assumption)
end
