module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleTjCorrespondencePInvertible

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingMumfordBundlePrincipalPolarisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionMumfordBundlePolarisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalPolarisationMumfordBundleAlgClosu
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipal
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PrincipalOfPairing

open GlobalTheory.CechPic

theorem lbIso_sq_diag {k : Type} [Field k] [IsAlgClosed k] {B : Over (Sp k)} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {L : LB B.left} (hL : L.IsLB) (hs : Out.Sym B L) {P : LB (G2 B).left} (hP : P.IsLB)
    (hiso : LBIso (abelian₂ B L) P) : LBIso (lbPow L 2) (P.pull (lift (𝟙 B) (𝟙 B) : B ⟶ G2 B).left) := by
  have hlam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hPow : (lbPow L 2).IsLB := LB.isLB_linComb hL _ _
  have hΘ := exists_gen_theta_of_isAbelianScheme k B hB L hL
  have h₀ : pull (1 : B ⟶ B).left (cls L hL) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    obtain ⟨N, hN, e⟩ := cls_surj (pull (η[B]).left (cls L hL))
    have z : cls N hN = 0 := (cls_eq_zero_iff hN).2 (DVR.exists_gen_of_isLB_local (V := k) N hN)
    rw [← e, z, map_zero]
  have h₁ : cls _ hlam = lam (cls L hL) (fst B B) (snd B B) := cls_cube_two hL _ _ hlam
  have h₂ := lam_mul_left hL hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)
  rw [mul_inv_cancel, lam_one_left, lam.eq_1 _ (𝟙 B)⁻¹, inv_mul_cancel, h₀] at h₂
  have h₃ := exists_gen_neg_of_sym GlobalTheory.lawsAndExpansions.1.1.globalFns hB hL hs
  rw [← cls_eq_zero_iff (LB.isLB_linComb hL _ _), cls_linComb hL] at h₃
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id] at h₃
  have einv : GrpObj.inv (X := B) = (𝟙 B)⁻¹ := by simp [Hom.inv_def]
  rw [einv, add_neg_eq_zero] at h₃
  rw [h₃, Over.id_left, pull_id] at h₂
  refine (cls_eq_iff hPow (pull_isLB hP _)).1 ?_
  rw [cls_lbPow hL 2 hPow, cls_pull hP, ← (cls_eq_iff hlam hP).2 hiso, h₁, pull_lam, lift_fst, lift_snd,
    eq_neg_of_add_eq_zero_left h₂.symm, two_smul]
  abel

theorem exists_principal : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → Out.RelAmple A (PP.pull (lift (𝟙 A) (𝟙 A) : A ⟶ G2 A).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : LB.Gen (PP.pull (lift (snd A T ≫ x) (fst A T) : A ⊗ T ⟶ G2 A).left), t.IsGen) → x = toUnit T ≫ η[A]) → ∃ L : LB A.left, L.IsLB ∧ Out.Sym A L ∧ LBIso (abelian₂ A L) PP ∧ Out.RelAmple A L ∧ Out.KTriv A L := by
  intro K _ _ _ A _ _ hA P hP hs hb ha hk
  obtain ⟨L, hL, sL, iL⟩ := GlobalTheory.SymBiextHalf.exists_sym_lam K A hA P hP hs hb
  refine ⟨L, hL, sL, iL, ?_, GlobalTheory.KTrivOfLam.kTriv_of_lam_iso _ A hA P hP hk L hL iL⟩
  have := hA.proper
  have hMa := isAmpleLB_of_relAmple_of_isAffine A (pull_isLB hP _) ha
  have h2 : IsAmpleLB (lbPow L 2) := hMa.of_lbIso (isLB_lbPow hL 2) (lbIso_sq_diag hA hL sL hP iL)
  have hLa : IsAmpleLB L := (isAmpleLB_pow_iff hL (by norm_num)).1 h2
  refine relAmple_of_isAmpleLB A hL fun U hU => ?_
  have : CompactSpace (A.hom ⁻¹ᵁ U) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := A.hom) _ U.isOpen hU.isCompact)
  exact hLa.pull_of_isOpenImmersion _

end GlobalTheory.PrincipalOfPairing

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalPolarisationMumfordBundleAlgClosu
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PrincipalBaseChange

variable {S S' : Scheme.{0}} {A : Over S} [GrpObj A] {f : S' ⟶ S}

theorem lift_comp_sq (w : pullback.fst A.hom f ≫ A.hom = ((Over.pullback f).obj A).hom ≫ f)
    {X : Over S'} (a b : X ⟶ (Over.pullback f).obj A) :
    (lift a b).left ≫ (lift (pushPt w (fst ((Over.pullback f).obj A) ((Over.pullback f).obj A)))
        (pushPt w (snd ((Over.pullback f).obj A) ((Over.pullback f).obj A)))).left =
      (lift (pushPt w a) (pushPt w b)).left := by
  apply pullback.hom_ext
  · change _ ≫ _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [← Over.comp_left, lift_fst, ← Over.comp_left, lift_fst]
    show (lift a b).left ≫ ((fst ((Over.pullback f).obj A) ((Over.pullback f).obj A)).left ≫ pullback.fst A.hom f) = a.left ≫ pullback.fst A.hom f
    rw [← Category.assoc, ← Over.comp_left, lift_fst]
  · change _ ≫ _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [← Over.comp_left, lift_snd, ← Over.comp_left, lift_snd]
    show (lift a b).left ≫ ((snd ((Over.pullback f).obj A) ((Over.pullback f).obj A)).left ≫ pullback.fst A.hom f) = b.left ≫ pullback.fst A.hom f
    rw [← Category.assoc, ← Over.comp_left, lift_snd]

theorem lift_comp_sq' (w : pullback.fst A.hom f ≫ A.hom = ((Over.pullback f).obj A).hom ≫ f)
    {X : Over S'} {Y : Over S} (U : Over.mk (X.hom ≫ f) ⟶ Y) (a b : X ⟶ (Over.pullback f).obj A) (c d : Y ⟶ A)
    (ha : pushPt w a = U ≫ c) (hb : pushPt w b = U ≫ d) :
    (lift a b).left ≫ (lift (pushPt w (fst ((Over.pullback f).obj A) ((Over.pullback f).obj A)))
        (pushPt w (snd ((Over.pullback f).obj A) ((Over.pullback f).obj A)))).left =
      U.left ≫ (lift c d).left := by
  rw [lift_comp_sq, ← Over.comp_left, comp_lift, ha, hb]

end GlobalTheory.PrincipalBaseChange

namespace GlobalTheory.PrincipalBaseChange

theorem exists_principal_algClosure : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → Out.RelAmple A (PP.pull (lift (𝟙 A) (𝟙 A) : A ⟶ G2 A).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : LB.Gen (PP.pull (lift (snd A T ≫ x) (fst A T) : A ⊗ T ⟶ G2 A).left), t.IsGen) → x = toUnit T ≫ η[A]) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] (κ : (G2 ((Over.pullback (spMap (algebraMap K Ω))).obj A)).left ⟶ (G2 A).left), Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K Ω))) κ → ∃ L : LB ((Over.pullback (spMap (algebraMap K Ω))).obj A).left, L.IsLB ∧ Out.Sym ((Over.pullback (spMap (algebraMap K Ω))).obj A) L ∧ LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K Ω))).obj A) L) (PP.pull κ) ∧ Out.RelAmple ((Over.pullback (spMap (algebraMap K Ω))).obj A) L ∧ Out.KTriv ((Over.pullback (spMap (algebraMap K Ω))).obj A) L := by
  intro K _ _ A _ _ hA PP hP hs hb ha hk Ω _ _ _ κ hκ
  set f := spMap (algebraMap K Ω) with hf
  set AΩ := (Over.pullback f).obj A with hAΩ
  have h := isGrpPullback_pullback A f
  have w := h.1.w
  obtain rfl := GlobalTheory.LamPull.isSquare_unique hκ (GlobalTheory.LamPull.exists_isSquare w)
  have hAΩab : IsAbelianScheme AΩ := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hP' := pull_isLB hP (lift (pushPt w (fst AΩ AΩ)) (pushPt w (snd AΩ AΩ))).left
  have pmul : ∀ {T : Over (Sp Ω)} (x y : T ⟶ AΩ), pushPt w (x * y) = pushPt w x * pushPt w y :=
    fun x y => map_mul (pushHom h _) x y
  refine GlobalTheory.PrincipalOfPairing.exists_principal Ω AΩ hAΩab _ hP' ?_ ?_ ?_ ?_
  · obtain ⟨u, hu⟩ := hs
    refine gen_chartPull (chartPullLinComb PP _ _ _ _ (lift (pushPt w (fst AΩ AΩ)) (pushPt w (snd AΩ AΩ))).left fun k => ?_) u hu
    fin_cases k
    · exact lift_comp_sq' w _ (snd AΩ AΩ) (fst AΩ AΩ) (snd A A) (fst A A) (lift_snd _ _).symm (lift_fst _ _).symm
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · obtain ⟨u, hu⟩ := hb
    let U3 : Over.mk ((AΩ ⊗ (AΩ ⊗ AΩ)).hom ≫ f) ⟶ A ⊗ (A ⊗ A) :=
      lift (pushPt w (fst AΩ (AΩ ⊗ AΩ)))
        (lift (pushPt w (snd AΩ (AΩ ⊗ AΩ) ≫ fst AΩ AΩ)) (pushPt w (snd AΩ (AΩ ⊗ AΩ) ≫ snd AΩ AΩ)))
    refine gen_chartPull (chartPullLinComb PP _ _ _ _ U3.left fun k => ?_) u hu
    fin_cases k
    · refine lift_comp_sq' w U3 _ _ _ _ ?_ (by simp [U3])
      rw [comp_mul, pmul]
      simp [U3]
    · exact lift_comp_sq' w U3 _ _ _ _ (by simp [U3]) (by simp [U3])
    · have e1 : snd AΩ (AΩ ⊗ AΩ) = lift (snd AΩ (AΩ ⊗ AΩ) ≫ fst AΩ AΩ) (snd AΩ (AΩ ⊗ AΩ) ≫ snd AΩ AΩ) := by simp
      have e2 : snd A (A ⊗ A) = lift (snd A (A ⊗ A) ≫ fst A A) (snd A (A ⊗ A) ≫ snd A A) := by simp
      show (snd AΩ (AΩ ⊗ AΩ)).left ≫ _ = U3.left ≫ (snd A (A ⊗ A)).left
      rw [e1, e2]
      exact lift_comp_sq' w U3 _ _ _ _ (by simp [U3]) (by simp [U3])
  · have e : (lift (𝟙 AΩ) (𝟙 AΩ)).left ≫ (lift (pushPt w (fst AΩ AΩ)) (pushPt w (snd AΩ AΩ))).left =
        pullback.fst A.hom f ≫ (lift (𝟙 A) (𝟙 A)).left := by
      rw [lift_comp_sq' w (pushPt w (𝟙 AΩ)) _ _ (𝟙 A) (𝟙 A) (by simp) (by simp)]
      simp [pushPt]
    refine GlobalTheory.AmpleLocalBase.relAmple_baseChange h.1 (pull_isLB hP _) (pull_isLB hP' _) ?_ ha
    refine LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _)
      (GlobalTheory.Mum.lbIso_pull_pull_comp hP _ _) ?_
    rw [e]
    exact (GlobalTheory.Mum.lbIso_pull_pull_comp hP _ _).symm
  · intro T x ⟨t, ht⟩
    let T₀ : Over (Sp K) := Over.mk (T.hom ≫ f)
    let x₀ : T₀ ⟶ A := pushPt w x
    let sT : Over.mk ((AΩ ⊗ T).hom ≫ f) ⟶ T₀ := Over.homMk (snd AΩ T).left (by
      show (snd AΩ T).left ≫ T.hom ≫ f = (AΩ ⊗ T).hom ≫ f
      rw [← Category.assoc, Over.w (snd AΩ T)])
    let V0 : Over.mk ((AΩ ⊗ T).hom ≫ f) ⟶ A ⊗ T₀ := lift (pushPt w (fst AΩ T)) sT
    have e : (lift (snd AΩ T ≫ x) (fst AΩ T)).left ≫ (lift (pushPt w (fst AΩ AΩ)) (pushPt w (snd AΩ AΩ))).left =
        V0.left ≫ (lift (snd A T₀ ≫ x₀) (fst A T₀)).left := by
      refine lift_comp_sq' w V0 _ _ _ _ ?_ (by simp [V0])
      rw [lift_snd_assoc]
      exact Over.OverMorphism.ext (by simp [pushPt, sT, x₀])
    have hV : IsIso V0.left := by
      have e3 : V0.left = (pullbackLeftPullbackSndIso A.hom f T.hom).hom := by
        apply pullback.hom_ext
        · change V0.left ≫ pullback.fst A.hom (T.hom ≫ f) =
            (pullbackLeftPullbackSndIso A.hom f T.hom).hom ≫ pullback.fst A.hom (T.hom ≫ f)
          rw [pullbackLeftPullbackSndIso_hom_fst]
          change V0.left ≫ (fst A T₀).left = _
          rw [← Over.comp_left, lift_fst]
          rfl
        · change V0.left ≫ pullback.snd A.hom (T.hom ≫ f) =
            (pullbackLeftPullbackSndIso A.hom f T.hom).hom ≫ pullback.snd A.hom (T.hom ≫ f)
          rw [pullbackLeftPullbackSndIso_hom_snd]
          change V0.left ≫ (snd A T₀).left = _
          rw [← Over.comp_left, lift_snd]
          rfl
      rw [e3]
      infer_instance
    have g1 := (exists_gen_pull_pull_iff hP _ _).1 ⟨t, ht⟩
    rw [e] at g1
    obtain ⟨t1, ht1⟩ := g1
    obtain ⟨t2, ht2⟩ := gen_chartPull (chartPullPull (PP.pull (V0.left ≫ (lift (snd A T₀ ≫ x₀) (fst A T₀)).left))
      (inv V0.left)) t1 ht1
    have g3 := (exists_gen_pull_pull_iff hP _ (inv V0.left)).1 ⟨t2, ht2⟩
    rw [IsIso.inv_hom_id_assoc] at g3
    have hx0 : x₀ = toUnit T₀ ≫ η[A] := hk T₀ x₀ g3
    have e1 : pushPt w (toUnit T ≫ η[AΩ]) = toUnit T₀ ≫ η[A] := by
      rw [← Hom.one_def, ← Hom.one_def]
      exact map_one (pushHom h T)
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · change x₀.left = (pushPt w (toUnit T ≫ η[AΩ])).left
      rw [hx0, e1]
    · rw [Over.w x, Over.w (toUnit T ≫ η[AΩ])]

end GlobalTheory.PrincipalBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalPolarisationMumfordBundleAlgClosuStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalPolarisation_mumfordBundle_algClosure : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → Out.RelAmple A (PP.pull (lift (𝟙 A) (𝟙 A) : A ⟶ G2 A).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : LB.Gen (PP.pull (lift (snd A T ≫ x) (fst A T) : A ⊗ T ⟶ G2 A).left), t.IsGen) → x = toUnit T ≫ η[A]) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] (κ : (G2 ((Over.pullback (spMap (algebraMap K Ω))).obj A)).left ⟶ (G2 A).left), Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K Ω))) κ → ∃ L : LB ((Over.pullback (spMap (algebraMap K Ω))).obj A).left, L.IsLB ∧ Out.Sym ((Over.pullback (spMap (algebraMap K Ω))).obj A) L ∧ LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K Ω))).obj A) L) (PP.pull κ) ∧ Out.RelAmple ((Over.pullback (spMap (algebraMap K Ω))).obj A) L ∧ Out.KTriv ((Over.pullback (spMap (algebraMap K Ω))).obj A) L := by
  first | exact @GlobalTheory.PrincipalBaseChange.exists_principal_algClosure | exact GlobalTheory.PrincipalBaseChange.exists_principal_algClosure | (intros; apply GlobalTheory.PrincipalBaseChange.exists_principal_algClosure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteLocalExtensionFractionRingOfGalois
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteLocalExtensionFractionRingOfGalois
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

theorem exists_finExt_fractionRing_of_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [Algebra (FractionRing R) E], FiniteDimensional (FractionRing R) E → IsGalois (FractionRing R) E → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (t : E →+* FractionRing R'), FinExt ρ ∧ ∀ r : R, t (algebraMap (FractionRing R) E (algebraMap R (FractionRing R) r)) = algebraMap R' (FractionRing R') (ρ r) := by
  intro R _ _ _ hR E _ _ hfd hgal
  letI := hfd
  letI := hgal
  obtain ⟨hloc, hfe⟩ := finExt_integralClosure (E := E) hR
  letI : Algebra R E := (baseMap R E).toAlgebra
  haveI : IsScalarTower R (FractionRing R) E := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsIntegrallyClosed R := hR.1.2.2.1
  haveI : CharZero R := hR.2
  set R₂ := integralClosure R E
  haveI : IsFractionRing R₂ E := integralClosure.isFractionRing_of_finite_extension (FractionRing R) E
  let t : E ≃ₐ[R₂] FractionRing R₂ := IsLocalization.algEquiv (nonZeroDivisors R₂) E (FractionRing R₂)
  refine ⟨R₂, inferInstance, inferInstance, hloc, algebraMap R R₂, t.toRingEquiv.toRingHom, hfe, ?_⟩
  intro r
  have h1 : algebraMap (FractionRing R) E (algebraMap R (FractionRing R) r) = algebraMap R₂ E (algebraMap R R₂ r) := rfl
  rw [h1]
  change t (algebraMap R₂ E _) = _
  rw [AlgEquiv.commutes]

end GlobalTheory.GalClosure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteLocalExtensionFractionRingOfGaloisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteLocalExtension_fractionRing_of_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [Algebra (FractionRing R) E], FiniteDimensional (FractionRing R) E → IsGalois (FractionRing R) E → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (t : E →+* FractionRing R'), FinExt ρ ∧ ∀ r : R, t (algebraMap (FractionRing R) E (algebraMap R (FractionRing R) r)) = algebraMap R' (FractionRing R') (ρ r) := by
  first | exact @GlobalTheory.GalClosure.exists_finExt_fractionRing_of_galois | exact GlobalTheory.GalClosure.exists_finExt_fractionRing_of_galois | (intros; apply GlobalTheory.GalClosure.exists_finExt_fractionRing_of_galois <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGaloisDescentPrincipalPolarisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGaloisDescentPrincipalPolarisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumDescent

theorem qc_qs_tensor {S : Scheme.{0}} (A : Over S) [IsProper A.hom] :
    QuasiCompact (A ⊗ A).hom ∧ QuasiSeparated (A ⊗ A).hom := by
  have e : (A ⊗ A).hom = pullback.fst A.hom A.hom ≫ A.hom := rfl
  rw [e]; exact ⟨inferInstance, inferInstance⟩

theorem exists_galois_polAV : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] (κ : (G2 ((Over.pullback (spMap (algebraMap K Ω))).obj A)).left ⟶ (G2 A).left), Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K Ω))) κ → ∀ L : LB ((Over.pullback (spMap (algebraMap K Ω))).obj A).left, L.IsLB → Out.Sym ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K Ω))).obj A) L) (PP.pull κ) → Out.RelAmple ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → Out.KTriv ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → ∃ (E : Type) (_ : Field E) (_ : Algebra K E), FiniteDimensional K E ∧ IsGalois K E ∧ ∃ (A₁ : PolAV (Sp E)) (gen : (Over.pullback (spMap (algebraMap K E))).obj A ≅ A₁.A), IsMonHom gen.hom ∧ ∀ κ : (G2 ((Over.pullback (spMap (algebraMap K E))).obj A)).left ⟶ (G2 A).left, Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K E))) κ → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K E))).obj A) (A₁.L.pull gen.hom.left)) (PP.pull κ) := by
  intro K _ _ A _ _ hA PP hPP Ω _ _ _ _ κ hκ L hL hS hΛ hAmp hKT
  haveI := hA.proper
  haveI := hA.smooth
  let σΩ : K →+* Ω := algebraMap K Ω
  let AΩ := (Over.pullback (spMap σΩ)).obj A
  have hAΩ : IsAbelianScheme AΩ := isAbelianScheme_pullback_obj _ A hA
  have hpΩ : IsGrpPullback AΩ A (spMap σΩ) (pullback.fst A.hom (spMap σΩ)) := isGrpPullback_pullback A _

  obtain ⟨F, hF, H⟩ := GlobalTheory.LBDescent.exists_finite_subextension_cls K Ω A.left AΩ.left A.hom AΩ.hom
    (pullback.fst A.hom (spMap σΩ)) hpΩ.1 L hL
  let f : Sp F ⟶ Sp K := spMap (algebraMap K F)
  let AF := (Over.pullback f).obj A
  have hAF : IsAbelianScheme AF := isAbelianScheme_pullback_obj f A hA
  have hpF : IsGrpPullback AF A f (pullback.fst A.hom f) := isGrpPullback_pullback A f
  have hcomp : spMap (algebraMap F Ω) ≫ f = spMap σΩ := by
    simp only [f, σΩ, spMap]
    rw [← Spec.map_comp]
    congr 1
  have w : pullback.fst A.hom (spMap σΩ) ≫ A.hom = (AΩ.hom ≫ spMap (algebraMap F Ω)) ≫ f := by
    rw [Category.assoc, hcomp]
    exact hpΩ.1.w
  let jm : AΩ.left ⟶ AF.left := pullback.lift (pullback.fst A.hom (spMap σΩ)) (AΩ.hom ≫ spMap (algebraMap F Ω)) w
  have hjf : jm ≫ pullback.fst A.hom f = pullback.fst A.hom (spMap σΩ) := pullback.lift_fst _ _ _
  have hjs : jm ≫ AF.hom = AΩ.hom ≫ spMap (algebraMap F Ω) := pullback.lift_snd _ _ _
  have hj : IsGrpPullback AΩ AF (spMap (algebraMap F Ω)) jm :=
    IsGrpPullback.cancel hpF (hpΩ.congr hcomp.symm hjf.symm) hjs
  obtain ⟨x, hx⟩ := H AF.left AF.hom (pullback.fst A.hom f) (IsPullback.of_hasPullback _ _) jm hjf hjs
  obtain ⟨L₁, hL₁, rfl⟩ := CechPic.cls_surj x
  have hw : LBIso L (L₁.pull jm) := by
    rw [← CechPic.cls_eq_iff hL (pull_isLB hL₁ jm), CechPic.cls_pull hL₁ jm (pull_isLB hL₁ jm)]
    exact hx.symm

  have hPPlb : PP.IsLB := hPP
  obtain ⟨κF, hκF⟩ : ∃ κF : (G2 AF).left ⟶ (G2 A).left, IsSquare (pullback.fst A.hom f) κF :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hpF.1.w⟩
  obtain ⟨jm₂, hjm₂⟩ : ∃ jm₂ : (G2 AΩ).left ⟶ (G2 AF).left, IsSquare jm jm₂ :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hj.1.w⟩
  have hΛF : (abelian₂ AF L₁).IsLB := DVR.linComb_isLB _ hL₁ _ _
  have hΛΩ : (abelian₂ AΩ L).IsLB := DVR.linComb_isLB _ hL _ _
  have hNF : (PP.pull κF).IsLB := pull_isLB hPPlb κF
  have eΩ : κ = jm₂ ≫ κF := by
    have h := GlobalTheory.ZM.SiegPull.isSquare_comp hjm₂ hκF
    rw [hjf] at h
    exact GlobalTheory.LamPull.isSquare_unique hκ h
  have isoΩ : LBIso ((abelian₂ AF L₁).pull jm₂) ((PP.pull κF).pull jm₂) :=
    LBIso.trans (pull_isLB hΛF _) hΛΩ (pull_isLB hNF _)
      (GlobalTheory.LamPull.lbIso_lam_pull hj hL₁ hL hw hjm₂).symm
      (LBIso.trans hΛΩ (pull_isLB hPPlb _) (pull_isLB hNF _) hΛ
        (GlobalTheory.ArcDataDescent.lbIso_pull_pull hPPlb κF jm₂ eΩ).symm)
  haveI := hAF.proper
  haveI := hAF.smooth
  have hqq := qc_qs_tensor AF
  obtain ⟨s, hs⟩ := GlobalTheory.lbIso_descends_to_subfield_containing_finset F Ω (algebraMap F Ω) (G2 AF) (G2 AΩ) jm₂
    (abelian₂ AF L₁) (PP.pull κF) (GlobalTheory.SiegelDescent.isPullback_square hj.1 jm₂ hjm₂) hqq.1 hqq.2 hΛF hNF isoΩ

  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let F' : IntermediateField K Ω := F ⊔ IntermediateField.adjoin K (s : Set Ω)
  haveI : FiniteDimensional K (IntermediateField.adjoin K (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  haveI : FiniteDimensional K F' := IntermediateField.finiteDimensional_sup _ _
  let E : IntermediateField K Ω := IntermediateField.normalClosure K F' Ω
  haveI hEf : FiniteDimensional K E := normalClosure.is_finiteDimensional K F' Ω
  haveI hEg : IsGalois K E := by
    haveI : Normal K E := inferInstance
    exact IsGalois.mk
  have hFE : F ≤ E := le_sup_left.trans F'.le_normalClosure
  have hsE : (s : Set Ω) ⊆ E := fun y hy =>
    F'.le_normalClosure (le_sup_right (a := F) (IntermediateField.subset_adjoin K _ hy))
  let α : F →+* E := (IntermediateField.inclusion hFE).toRingHom
  let e : Sp E ⟶ Sp K := spMap (algebraMap K E)
  let AE := (Over.pullback e).obj A
  have hAE : IsAbelianScheme AE := isAbelianScheme_pullback_obj e A hA
  have hpE : IsGrpPullback AE A e (pullback.fst A.hom e) := isGrpPullback_pullback A e
  have hcα : spMap α ≫ f = e := by
    simp only [f, e, α, spMap]
    rw [← Spec.map_comp]
    congr 1
  have wE : pullback.fst A.hom e ≫ A.hom = (AE.hom ≫ spMap α) ≫ f := by
    rw [Category.assoc, hcα]
    exact hpE.1.w
  let χ : AE.left ⟶ AF.left := pullback.lift (pullback.fst A.hom e) (AE.hom ≫ spMap α) wE
  have hχf : χ ≫ pullback.fst A.hom f = pullback.fst A.hom e := pullback.lift_fst _ _ _
  have hχs : χ ≫ AF.hom = AE.hom ≫ spMap α := pullback.lift_snd _ _ _
  have hχ : IsGrpPullback AE AF (spMap α) χ := IsGrpPullback.cancel hpF (hpE.congr hcα.symm hχf.symm) hχs
  obtain ⟨χ₂, hχ₂⟩ : ∃ χ₂ : (G2 AE).left ⟶ (G2 AF).left, IsSquare χ χ₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hχ.1.w⟩
  have isoE : LBIso ((abelian₂ AF L₁).pull χ₂) ((PP.pull κF).pull χ₂) :=
    hs E α (algebraMap E Ω) (RingHom.ext fun _ => rfl) (fun y hy => ⟨⟨y, hsE hy⟩, rfl⟩) (G2 AE) χ₂
      (GlobalTheory.SiegelDescent.isPullback_square hχ.1 χ₂ hχ₂)

  let LE : LB AE.left := L₁.pull χ
  have hLE : LE.IsLB := pull_isLB hL₁ χ
  have hcE : spMap (algebraMap E Ω) ≫ e = spMap σΩ := by
    simp only [e, σΩ, spMap]
    rw [← Spec.map_comp]
    congr 1
  have wΩ : pullback.fst A.hom (spMap σΩ) ≫ A.hom = (AΩ.hom ≫ spMap (algebraMap E Ω)) ≫ e := by
    rw [Category.assoc, hcE]
    exact hpΩ.1.w
  let jE : AΩ.left ⟶ AE.left := pullback.lift (pullback.fst A.hom (spMap σΩ)) (AΩ.hom ≫ spMap (algebraMap E Ω)) wΩ
  have hjEf : jE ≫ pullback.fst A.hom e = pullback.fst A.hom (spMap σΩ) := pullback.lift_fst _ _ _
  have hjEs : jE ≫ AE.hom = AΩ.hom ≫ spMap (algebraMap E Ω) := pullback.lift_snd _ _ _
  have hjE : IsGrpPullback AΩ AE (spMap (algebraMap E Ω)) jE :=
    IsGrpPullback.cancel hpE (hpΩ.congr hcE.symm hjEf.symm) hjEs
  have hαΩ : spMap (algebraMap E Ω) ≫ spMap α = spMap (algebraMap F Ω) := by
    simp only [α, spMap]
    rw [← Spec.map_comp]
    congr 1
  have ejm : jm = jE ≫ χ := by
    apply pullback.hom_ext
    · rw [hjf, Category.assoc, hχf, hjEf]
    · show jm ≫ AF.hom = (jE ≫ χ) ≫ AF.hom
      rw [hjs, Category.assoc, hχs, ← Category.assoc, hjEs, Category.assoc, hαΩ]
  have hwE : LBIso L (LE.pull jE) :=
    LBIso.trans hL (pull_isLB hL₁ jm) (pull_isLB hLE jE) hw
      (GlobalTheory.ArcDataDescent.lbIso_pull_pull hL₁ χ jE ejm).symm
  have hd := GlobalTheory.PolDescent.rigidified_sym_kTriv_descend E Ω (algebraMap E Ω) AE AΩ jE LE L hAE hjE hLE hL hwE
  haveI := hAE.proper
  haveI := hAE.smooth
  have ha := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension E Ω (algebraMap E Ω) AE AΩ jE hjE LE L hLE hL
    hwE hAΩ.proper hAmp hKT
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim E AE hAE
  have hrig : Out.Rigidified AE LE := by
    have : Subsingleton (𝟙_ (Over (Sp E))).left := inferInstanceAs (Subsingleton (PrimeSpectrum E))
    exact GlobalTheory.PolDescent.exists_gen_of_unique (default : PrimeSpectrum E) (pull_isLB hLE _)
  let A₁ : Out.PolAV (Sp E) :=
    { A := AE, isAb := hAE, g := g, smoothDim := hg, L := LE, isLB := hLE, rigid := hrig,
      sym := hd.2.1 hS, ample := ha.2.1, ktriv := ha.2.2 }
  refine ⟨E, inferInstance, inferInstance, hEf, hEg, A₁, Iso.refl _, ?_, fun κ' hκ' => ?_⟩
  · show IsMonHom (𝟙 AE); infer_instance
  have e' : κ' = χ₂ ≫ κF := by
    have h := GlobalTheory.ZM.SiegPull.isSquare_comp hχ₂ hκF
    rw [hχf] at h
    exact GlobalTheory.LamPull.isSquare_unique hκ' h
  have hLE' : (LE.pull (𝟙 AE.left)).IsLB := pull_isLB hLE _
  have k₁ : LBIso (abelian₂ AE (LE.pull (𝟙 AE.left))) ((abelian₂ AF L₁).pull χ₂) :=
    GlobalTheory.LamPull.lbIso_lam_pull hχ hL₁ hLE' (GlobalTheory.ArcDataDescent.lbIso_pull_pull hL₁ χ (𝟙 _) (Category.id_comp χ).symm) hχ₂
  have k₂ : LBIso ((PP.pull κF).pull χ₂) (PP.pull κ') := GlobalTheory.ArcDataDescent.lbIso_pull_pull hPPlb κF χ₂ e'
  exact LBIso.trans (DVR.linComb_isLB _ hLE' _ _) (pull_isLB hΛF _) (pull_isLB hPPlb _) k₁
    (LBIso.trans (pull_isLB hΛF _) (pull_isLB hNF _) (pull_isLB hPPlb _) isoE k₂)

end GlobalTheory.MumDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGaloisDescentPrincipalPolarisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_galois_descent_principal_polarisation : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] (κ : (G2 ((Over.pullback (spMap (algebraMap K Ω))).obj A)).left ⟶ (G2 A).left), Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K Ω))) κ → ∀ L : LB ((Over.pullback (spMap (algebraMap K Ω))).obj A).left, L.IsLB → Out.Sym ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K Ω))).obj A) L) (PP.pull κ) → Out.RelAmple ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → Out.KTriv ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → ∃ (E : Type) (_ : Field E) (_ : Algebra K E), FiniteDimensional K E ∧ IsGalois K E ∧ ∃ (A₁ : PolAV (Sp E)) (gen : (Over.pullback (spMap (algebraMap K E))).obj A ≅ A₁.A), IsMonHom gen.hom ∧ ∀ κ : (G2 ((Over.pullback (spMap (algebraMap K E))).obj A)).left ⟶ (G2 A).left, Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K E))) κ → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K E))).obj A) (A₁.L.pull gen.hom.left)) (PP.pull κ) := by
  first | exact @GlobalTheory.MumDescent.exists_galois_polAV | exact GlobalTheory.MumDescent.exists_galois_polAV | (intros; apply GlobalTheory.MumDescent.exists_galois_polAV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionMumfordBundlePolarisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumDesc


set_option maxHeartbeats 1000000 in
theorem exists_polAV_field : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → Out.RelAmple A (PP.pull (lift (𝟙 A) (𝟙 A) : A ⟶ G2 A).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : LB.Gen (PP.pull (lift (snd A T ≫ x) (fst A T) : A ⊗ T ⟶ G2 A).left), t.IsGen) → x = toUnit T ≫ η[A]) → ∃ (E : Type) (_ : Field E) (_ : Algebra K E), FiniteDimensional K E ∧ IsGalois K E ∧ ∃ (A₁ : PolAV (Sp E)) (gen : (Over.pullback (spMap (algebraMap K E))).obj A ≅ A₁.A), IsMonHom gen.hom ∧ ∀ κ : (G2 ((Over.pullback (spMap (algebraMap K E))).obj A)).left ⟶ (G2 A).left, Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K E))) κ → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K E))).obj A) (A₁.L.pull gen.hom.left)) (PP.pull κ) := by
  intro K _ _ A _ _ hA PP hPP hs ha hm hk
  obtain ⟨κ, hκ⟩ : ∃ κ : (G2 ((Over.pullback (spMap (algebraMap K (AlgebraicClosure K)))).obj A)).left ⟶ (G2 A).left,
      Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K (AlgebraicClosure K)))) κ :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare (isGrpPullback_pullback A _).1.w⟩
  obtain ⟨L, hL, hS, hI, hM, hT⟩ := GlobalTheory.T.exists_principalPolarisation_mumfordBundle_algClosure K A hA PP hPP hs ha hm hk (AlgebraicClosure K) κ hκ
  exact GlobalTheory.T.exists_finite_galois_descent_principal_polarisation K A hA PP hPP (AlgebraicClosure K) κ hκ L hL hS hI hM hT


set_option maxHeartbeats 1000000 in
theorem exists_extLam_finExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ PP : LB (G2 G).left, PP.IsLB → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (PP.pull κ₀) (K := Fin 2) ![(lift (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : G2 ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, 𝟙 (G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1]), u.IsGen) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (PP.pull κ₀) (K := Fin 3) ![(lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) * (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1, -1]), u.IsGen) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → Out.RelAmple ((Over.pullback (jK R)).obj G) ((PP.pull κ₀).pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left)) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((PP.pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → x = toUnit T ≫ η[((Over.pullback (jK R)).obj G)]) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ ExtLam G₁ (A₁.L.pull gen₁.hom.left) (PP.pull β₂) := by
  intro R _ _ _ hR G _ _ hab PP hPP hsym hadd hamp hker
  have hp := isGrpPullback_pullback G (jK R)
  obtain ⟨κ₀, hκ₀⟩ : ∃ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left,
      Geo.Tor.IsSquare (pullback.fst G.hom (jK R)) κ₀ := ⟨_, GlobalTheory.LamPull.exists_isSquare hp.1.w⟩
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨E, _, _, hfd, hgal, A₁, gen, hgen, hLam⟩ :=
    exists_polAV_field (FractionRing R) ((Over.pullback (jK R)).obj G) hab (PP.pull κ₀) (pull_isLB hPP κ₀)
      (hsym κ₀ hκ₀) (hadd κ₀ hκ₀) (hamp κ₀ hκ₀) (hker κ₀ hκ₀)
  obtain ⟨R', _, _, _, ρ, t, hρ, ht⟩ := GlobalTheory.T.exists_finiteLocalExtension_fractionRing_of_galois R hR E hfd hgal
  haveI := hgen
  have hsq : (spMap t) ≫ (spMap (algebraMap (FractionRing R) E)) ≫ jK R = jK R' ≫ spMap ρ := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact ht r
  have hE := isGrpPullback_pullback ((Over.pullback (jK R)).obj G) (spMap (algebraMap (FractionRing R) E))
  have hβ := isGrpPullback_pullback G (spMap ρ)
  have hp₁ := isGrpPullback_pullback ((Over.pullback (spMap ρ)).obj G) (jK R')
  have hc := (hp₁.comp hβ).congr hsq.symm rfl
  have hAEG := hE.comp hp
  have w1 : (pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ)) ≫ G.hom =
      (((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).hom ≫ (spMap t) ≫ (spMap (algebraMap (FractionRing R) E))) ≫ jK R := by
    simpa only [Category.assoc] using hc.1.w
  let a : ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).left ⟶
      ((Over.pullback (jK R)).obj G).left := pullback.lift _ _ w1
  have w2 : a ≫ ((Over.pullback (jK R)).obj G).hom =
      (((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).hom ≫ (spMap t)) ≫ (spMap (algebraMap (FractionRing R) E)) := by
    exact (pullback.lift_snd _ _ w1).trans (Category.assoc _ _ _).symm
  let φ₁ : ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).left ⟶
      ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G)).left := pullback.lift _ _ w2
  have hφ₁fst : φ₁ ≫ pullback.fst ((Over.pullback (jK R)).obj G).hom (spMap (algebraMap (FractionRing R) E)) ≫ pullback.fst G.hom (jK R) =
      pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ) := by
    simp only [φ₁, a, pullback.lift_fst_assoc, pullback.lift_fst]
  have hφ₁w : φ₁ ≫ ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G)).hom =
      ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).hom ≫ (spMap t) := pullback.lift_snd _ _ _
  have hφ := hAEG.cancel (hc.congr rfl hφ₁fst.symm) hφ₁w
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨A₀, g, hg, hgL⟩ := GlobalTheory.ArcDataDescent.exists_polPull hL.polBaseChange (spMap t) A₁
  have h1 := (hφ.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl
  obtain ⟨e, he, heg⟩ := grpPullback_iso h1 hg
  obtain ⟨β₂, hβ₂⟩ : ∃ β₂ : (G2 ((Over.pullback (spMap ρ)).obj G)).left ⟶ (G2 G).left,
      Geo.Tor.IsSquare (pullback.fst G.hom (spMap ρ)) β₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hβ.1.w⟩
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, (Over.pullback (spMap ρ)).obj G, inferInstance, inferInstance,
    pullback.fst G.hom (spMap ρ), β₂, A₀, e, ?_, ?_, ?_, ?_, ?_⟩
  · exact hρ
  · exact hβ
  · exact hβ₂
  · exact he
  refine ⟨pull_isLB hPP β₂, fun κ₂' hκ₂' => ?_⟩
  have hL1 : (A₁.L.pull gen.hom.left).IsLB := pull_isLB A₁.isLB _
  have hL0 : (A₀.L.pull e.hom.left).IsLB := pull_isLB A₀.isLB _
  have hNL : LBIso (A₀.L.pull e.hom.left) ((A₁.L.pull gen.hom.left).pull φ₁) :=
    LBIso.trans hL0 (pull_isLB A₁.isLB _) (pull_isLB hL1 φ₁)
      (GlobalTheory.ArcDataDescent.lbIso_pull hgL e.hom.left heg.symm)
      (GlobalTheory.ArcDataDescent.lbIso_pull_pull A₁.isLB gen.hom.left φ₁ rfl).symm
  obtain ⟨φ₂, hφ₂⟩ : ∃ φ₂, Geo.Tor.IsSquare φ₁ φ₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hφ.1.w⟩
  have h₁ := GlobalTheory.LamPull.lbIso_lam_pull hφ hL1 hL0 hNL hφ₂
  obtain ⟨κ, hκ⟩ : ∃ κ : (G2 ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G))).left ⟶ (G2 ((Over.pullback (jK R)).obj G)).left, Geo.Tor.IsSquare (pullback.fst ((Over.pullback (jK R)).obj G).hom (spMap (algebraMap (FractionRing R) E))) κ :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hE.1.w⟩
  have hΛ : (abelian₂ ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G)) (A₁.L.pull gen.hom.left)).IsLB :=
    DVR.linComb_isLB _ hL1 _ _
  have hLK : LBIso (abelian₂ ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G)) (A₁.L.pull gen.hom.left))
      (PP.pull (κ ≫ κ₀)) :=
    LBIso.trans hΛ (pull_isLB (pull_isLB hPP _) κ) (pull_isLB hPP _) (hLam κ hκ)
      (GlobalTheory.ArcDataDescent.lbIso_pull_pull hPP κ₀ κ rfl)
  have h₂ := GlobalTheory.ArcDataDescent.lbIso_pull hLK φ₂ (ψ := φ₂ ≫ κ ≫ κ₀) rfl
  have hsq2 : φ₂ ≫ κ ≫ κ₀ = κ₂' ≫ β₂ := by
    apply GlobalTheory.LamPull.isSquare_unique
      (φ := pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ))
    · constructor
      · simp only [Category.assoc, hκ₀.1, reassoc_of% hκ.1, reassoc_of% hφ₂.1, hφ₁fst]
      · simp only [Category.assoc, hκ₀.2, reassoc_of% hκ.2, reassoc_of% hφ₂.2, hφ₁fst]
    · constructor
      · simp only [Category.assoc, hβ₂.1, reassoc_of% hκ₂'.1]
      · simp only [Category.assoc, hβ₂.2, reassoc_of% hκ₂'.2]
  rw [hsq2] at h₂
  have h₃ : LBIso (PP.pull (κ₂' ≫ β₂)) ((PP.pull β₂).pull κ₂') :=
    (GlobalTheory.ArcDataDescent.lbIso_pull_pull hPP β₂ κ₂' rfl).symm
  exact LBIso.trans (DVR.linComb_isLB _ hL0 _ _) (pull_isLB hΛ φ₂) (pull_isLB (pull_isLB hPP β₂) κ₂') h₁
    (LBIso.trans (pull_isLB hΛ φ₂) (pull_isLB hPP _) (pull_isLB (pull_isLB hPP β₂) κ₂') h₂ h₃)

end GlobalTheory.MumDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionMumfordBundlePolarisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_mumford_bundle_polarisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ PP : LB (G2 G).left, PP.IsLB → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (PP.pull κ₀) (K := Fin 2) ![(lift (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : G2 ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, 𝟙 (G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1]), u.IsGen) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (PP.pull κ₀) (K := Fin 3) ![(lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) * (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1, -1]), u.IsGen) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → Out.RelAmple ((Over.pullback (jK R)).obj G) ((PP.pull κ₀).pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left)) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((PP.pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → x = toUnit T ≫ η[((Over.pullback (jK R)).obj G)]) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ ExtLam G₁ (A₁.L.pull gen₁.hom.left) (PP.pull β₂) := by
  first | exact @GlobalTheory.MumDesc.exists_extLam_finExt | exact GlobalTheory.MumDesc.exists_extLam_finExt | (intros; apply GlobalTheory.MumDesc.exists_extLam_finExt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingKernelTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiStarMulKillsPointOfTrivialPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiStarMulKillsPointOfTrivialPairing
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.CechPic

theorem lam_rosati_field (K : Type) [Field K] (P : PolAV (Sp K)) (O : Type) [Ring O] [StarRing O] (oA : P.OAct O)
    (o : O) {T' : Over (Sp K)} (x z : T' ⟶ P.A) :
    haveI := P.isAb.comm
    lam (cls P.L P.isLB) (x ≫ oA.act (star o)) z = lam (cls P.L P.isLB) x (z ≫ oA.act o) := by
  haveI := P.isAb.comm
  haveI := oA.hom (star o)
  haveI := oA.hom o
  have hr := oA.rosati (star o)
  rw [star_star] at hr
  obtain ⟨u, hu, -⟩ := exists_ros GlobalTheory.globalFns_holds P.isAb P.isLB _ _ hr
  have h := GlobalTheory.EndRosati.cls_of_rosati P.isLB u hu x z
  show _ - _ - _ + _ = _ - _ - _ + _
  rw [h]

theorem kill_of_lam_triv : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (O : Type) [Ring O] [StarRing O] (oA : P.OAct O) (e f : O) (H : Over (Sp K)) (a : H ⟶ P.A) (r : P.A ⟶ H), r ≫ a = oA.act e → ∀ (T : Over (Sp K)) (y : T ⟶ P.A), (∃ t : LB.Gen (letI := P.isAb.comm; (abelian₂ P.A P.L).pull (lift (snd H T ≫ y) (fst H T ≫ a ≫ oA.act f) : H ⊗ T ⟶ G2 P.A).left), t.IsGen) → y ≫ oA.act (star e * star f) = toUnit T ≫ η[P.A] := by
  intro K _ P O _ _ oA e f H a r hra T y ⟨t, ht⟩
  haveI := P.isAb.comm
  have h0 : lam (cls P.L P.isLB) (snd H T ≫ y) (fst H T ≫ a ≫ oA.act f) = 0 := by
    have := (cls_eq_zero_iff (pull_isLB (GlobalTheory.FullSiegel.isLB_lam P.isLB) _)).2 ⟨t, ht⟩
    rwa [GlobalTheory.FullSiegel.cls_lam_pull P.isLB] at this
  have h1 : lam (cls P.L P.isLB) (fst T P.A ≫ y) ((snd T P.A ≫ oA.act e) ≫ oA.act f) = 0 := by
    have := congrArg (pull (lift (snd T P.A ≫ r) (fst T P.A)).left) h0
    rw [pull_lam, map_zero, lift_snd_assoc, lift_fst_assoc, Category.assoc, reassoc_of% hra] at this
    rw [Category.assoc]
    exact this
  have h2 := (lam_rosati_field K P O oA f _ _).trans h1
  have h3 := (lam_rosati_field K P O oA e _ (snd T P.A)).trans h2
  have hb : ((fst T P.A ≫ y) ≫ oA.act (star f)) ≫ oA.act (star e) = fst T P.A ≫ y ≫ oA.act (star e * star f) := by
    rw [oA.map_mul]; simp only [Category.assoc]
  rw [hb] at h3
  have h4 := congrArg (pull (lift (snd P.A T) (fst P.A T)).left) h3
  rw [pull_lam, map_zero, lift_fst_assoc, lift_snd] at h4
  have hg : ∃ t : ((abelian₂ P.A P.L).pull (lift (snd P.A T ≫ y ≫ oA.act (star e * star f)) (fst P.A T)).left).Gen,
      t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB (GlobalTheory.FullSiegel.isLB_lam P.isLB) _)).1 ?_
    rw [GlobalTheory.FullSiegel.cls_lam_pull P.isLB]
    exact h4
  exact (GlobalTheory.FullSiegel.eq_one_of_lam_triv P.isLB P.rigid P.ktriv T _ hg).trans (Hom.one_def ..)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiStarMulKillsPointOfTrivialPairingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosati_star_mul_kills_point_of_trivial_pairing : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (O : Type) [Ring O] [StarRing O] (oA : P.OAct O) (e f : O) (H : Over (Sp K)) (a : H ⟶ P.A) (r : P.A ⟶ H), r ≫ a = oA.act e → ∀ (T : Over (Sp K)) (y : T ⟶ P.A), (∃ t : LB.Gen (letI := P.isAb.comm; (abelian₂ P.A P.L).pull (lift (snd H T ≫ y) (fst H T ≫ a ≫ oA.act f) : H ⊗ T ⟶ G2 P.A).left), t.IsGen) → y ≫ oA.act (star e * star f) = toUnit T ≫ η[P.A] := by
  first | exact @GlobalTheory.Mum.kill_of_lam_triv | exact GlobalTheory.Mum.kill_of_lam_triv | (intros; apply GlobalTheory.Mum.kill_of_lam_triv <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

theorem GlobalTheory.Mum.pairing_kernel_trivial : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → x = toUnit T ≫ η[((Over.pullback (jK R)).obj G)] := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi κ₀ hκ T x hx
  have h1 := GlobalTheory.T.pull_generator_factor_pairing_generic_mumfordBundle R D D' F A' G' U' oA oG hlin G inc hinc κ₀ hκ T x hx
  have hra : (U'.gen.inv ≫ (Over.pullback (jK R)).map pr) ≫ ((Over.pullback (jK R)).map inc ≫ U'.gen.hom) = oA.act F.e := by
    have e1 := hlin.ext F.e
    rw [← hpi, CategoryTheory.Functor.map_comp] at e1
    rw [Category.assoc, ← Category.assoc ((Over.pullback (jK R)).map pr), e1, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have h2 := GlobalTheory.T.rosati_star_mul_kills_point_of_trivial_pairing (FractionRing R) A' F.O oA F.e F.f ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).map inc ≫ U'.gen.hom) (U'.gen.inv ≫ (Over.pullback (jK R)).map pr) hra T (x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom) h1
  have hip' : (Over.pullback (jK R)).map inc ≫ (Over.pullback (jK R)).map pr = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id]
  have he : (x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom) ≫ oA.act F.e = x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom := by
    rw [← hra]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc ((Over.pullback (jK R)).map inc) ((Over.pullback (jK R)).map pr), hip', Category.id_comp]
  obtain ⟨-, hsym, g, hg⟩ := hF
  set y := x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom with hy
  have hu : y ≫ oA.act (Star.star F.e * F.f * F.e) = toUnit T ≫ η[A'.A] := by
    rw [hsym, oA.map_mul, ← Category.assoc, he, h2]
  have h3 : y = toUnit T ≫ η[A'.A] := by
    have : IsMonHom (oA.act g) := oA.hom g
    rw [← he, ← hg, oA.map_mul, ← Category.assoc, hu, Category.assoc, IsMonHom.one_hom]
  have hx' : x = y ≫ U'.gen.inv ≫ (Over.pullback (jK R)).map pr := by
    rw [hy]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hip', Category.comp_id]
  rw [hx', h3]
  have hη : η[A'.A] ≫ U'.gen.inv = η[(Over.pullback (jK R)).obj G'] := by
    have : IsMonHom U'.gen.hom := U'.gen_hom
    rw [← IsMonHom.one_hom U'.gen.hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : IsMonHom ((Over.pullback (jK R)).map pr) := inferInstance
  rw [Category.assoc, ← Category.assoc η[A'.A], hη, IsMonHom.one_hom]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamPush
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorSym

open GlobalTheory.CechPic GlobalTheory.EndRosati

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def genι (G : Over (Sp R)) : (Over.map (jK R)).obj ((Over.pullback (jK R)).obj G) ⟶ G :=
  Over.homMk (pullback.fst G.hom (jK R)) pullback.condition

theorem lam_push (U : UnifPre I D A G) {T : Over (Sp (FractionRing R))} (x y : T ⟶ (Over.pullback (jK R)).obj G) :
    @id (Pic T.left) (lam (T := (Over.map (jK R)).obj T) (cls _ U.LG.isLB) (push (genι G) x) (push (genι G) y)) =
      lam (cls _ A.isLB) (x ≫ U.gen.hom) (y ≫ U.gen.hom) := by
  have := U.gen_hom
  have e := (cls_eq_iff (LB.isLB_pull A.isLB _) (LB.isLB_pull U.LG.isLB _)).2 U.ext
  rw [cls_pull A.isLB, cls_pull U.LG.isLB] at e
  have hm : ∀ x y : T ⟶ (Over.pullback (jK R)).obj G, push (genι G) (x * y) = push (genι G) x * push (genι G) y :=
    fun x y => push_mul (genι G) (𝟙 _) (Category.id_comp _).symm x y
  have h1 : push (genι G) (1 : T ⟶ (Over.pullback (jK R)).obj G) = 1 := by
    have := hm 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have hp : ∀ x : T ⟶ (Over.pullback (jK R)).obj G,
      @id (Pic T.left) (pull (push (genι G) x).left (cls _ U.LG.isLB)) =
        pull x.left (pull U.gen.hom.left (cls _ A.isLB)) := fun x => by
    rw [e, ← pull_comp]; rfl
  rw [← lam_pull U.gen.hom, lam, lam, ← hm, ← h1, ← hp, ← hp, ← hp, ← hp]
  rfl

theorem lam_act (U : UnifPre I D A G) {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X] {o : D.OAct O}
    {oA : A.OAct O} {oG : RingAct G O} (h : U.OLinear O o oA oG) (a : O) {T : Over (Sp (FractionRing R))}
    (x y : (Over.map (jK R)).obj T ⟶ G) :
    lam (cls _ U.LG.isLB) (x ≫ oG.act a) y = lam (cls _ U.LG.isLB) x (y ≫ oG.act (star a)) := by
  have sj : ∀ x : (Over.map (jK R)).obj T ⟶ G, ∃ x' : T ⟶ (Over.pullback (jK R)).obj G, push (genι G) x' = x :=
    fun x => ⟨Over.homMk (pullback.lift x.left T.hom (Over.w x)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  obtain ⟨x, rfl⟩ := sj x
  obtain ⟨y, rfl⟩ := sj y
  have e' : ∀ f : G ⟶ G, push (genι G) ((Over.pullback (jK R)).map f) = genι G ≫ f := fun f =>
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  rw [← push_comp _ (e' _), ← push_comp _ (e' _)]
  refine (lam_push U _ _).trans (Eq.trans ?_ (lam_push U _ _).symm)
  obtain ⟨t, ht⟩ := GlobalTheory.RosatiDescent.exists_gen_of_rosatiAdj (oA.rosati a)
  have := cls_of_rosati A.isLB t ht (x ≫ U.gen.hom) (y ≫ U.gen.hom)
  rw [Category.assoc, Category.assoc, h.ext, h.ext, ← Category.assoc, ← Category.assoc, lam, lam, this]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀) (K := Fin 2) ![(lift (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : G2 ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, 𝟙 (G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1]), u.IsGen := by
  intro R _ _ _ _ D D' F hF A' G' _ _ _ U' oA oG hlin G _ _ _ inc pr _ _ hip hpi κ₀ hκ
  have hs : oG.act (star F.e * F.f * F.e) = oG.act (star F.e * star F.f * F.e) :=
    congrArg oG.act hF.2.1
  have hi : inc ≫ oG.act F.e = inc := by rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  let GK := (Over.pullback (jK R)).obj G
  have hL := U'.LG.isLB
  have sy : ∀ x y : (Over.map (jK R)).obj (G2 GK) ⟶ G,
      lam (cls _ hL) (x ≫ inc) (y ≫ inc ≫ oG.act F.f) = lam (cls _ hL) (y ≫ inc) (x ≫ inc ≫ oG.act F.f) := fun x y => by
    have e₁ := lam_act U'.toUnifPre hlin F.e (x ≫ inc) (y ≫ inc ≫ oG.act F.f)
    have e₂ := lam_act U'.toUnifPre hlin F.f (x ≫ inc) (y ≫ inc)
    have e₃ := lam_act U'.toUnifPre hlin F.e (x ≫ inc) (y ≫ inc ≫ oG.act (star F.f))
    have e₄ : inc ≫ oG.act F.f ≫ oG.act (star F.e) = inc ≫ oG.act (star F.f) ≫ oG.act (star F.e) := by
      have := congrArg (inc ≫ ·) hs
      simpa only [oG.map_mul, reassoc_of% hi] using this
    simp only [Category.assoc, hi] at e₁ e₂ e₃
    rw [e₁, e₄, ← e₃, ← e₂, lam_comm]
  have hP := pull_isLB (GlobalTheory.FullSiegel.isLB_lam hL)
    (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left
  refine (gen_iff_sum (pull_isLB hP κ₀) _ _).2 ?_
  rw [cls_pull hP, GlobalTheory.FullSiegel.cls_lam_pull hL, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id, ← pull_comp]
  let X : (Over.map (jK R)).obj (G2 GK) ⟶ G := push (genι G) (fst GK GK)
  let Y : (Over.map (jK R)).obj (G2 GK) ⟶ G := push (genι G) (snd GK GK)
  have k₁ : κ₀ = (lift X Y).left := by
    refine pullback.hom_ext (hκ.1.trans ?_) (hκ.2.trans ?_)
    · exact (congrArg (·.left) (lift_fst X Y)).symm
    · exact (congrArg (·.left) (lift_snd X Y)).symm
  have k₂ : (lift (snd GK GK) (fst GK GK)).left ≫ κ₀ = (lift Y X).left := by
    rw [k₁]; exact lift_push (genι G) _ _
  have p₁ := pull_lam (lift X Y) (cls _ hL) (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f)
  have p₂ := pull_lam (lift Y X) (cls _ hL) (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f)
  rw [lift_fst_assoc, lift_snd_assoc] at p₁ p₂
  rw [← k₁] at p₁
  rw [← k₂] at p₂
  exact add_neg_eq_zero.2 (p₂.trans ((sy Y X).trans p₁.symm))

end GlobalTheory.Mum.FactorSym
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingMumfordBundlePrincipalPolarisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem pairing_factor_mumford : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂) := by
  intro R _ _ _ hR D D' F hA A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi
  exact GlobalTheory.T.exists_finite_extension_mumford_bundle_polarisation R hR G
    (RetractGeneric.isAbelianScheme_generic R A' G' hG' U'.gen G hG inc pr hinc hpr hip) _
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb U'.LG.isLB _ _) _)
    (FactorSym.main R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)
    (factorPairing_add R hR D D' F A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)
    (factorPairing_diag_relAmple R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)
    (pairing_kernel_trivial R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingMumfordBundlePrincipalPolarisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorPairing_mumfordBundle_principal_polarisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂) := by
  first | exact @GlobalTheory.Mum.pairing_factor_mumford | exact GlobalTheory.Mum.pairing_factor_mumford | (intros; apply GlobalTheory.Mum.pairing_factor_mumford <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinExtCubicalSymmetricEvenFactor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finExt_cp_factor_even : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (A₀ : PolAV (Sp (FractionRing R₀))) (gen₀ : (Over.pullback (jK R₀)).obj G₀ ≅ A₀.A), FinExt ρ₀ ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P ∧ IsMonHom gen₀.hom ∧ LBIso (A₀.L.pull gen₀.hom.left) (P.L.L.pull (pullback.fst G₀.hom (jK R₀))) := by
  intro R _ _ _ hR D D' F hA A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi
  obtain ⟨R₁, _, _, _, ρ₁, G₁, _, _, β₁, β₁₂, A₁, gen₁, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.T.factorPairing_mumfordBundle_principal_polarisation R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi
  exact GlobalTheory.T.exists_evenCubicalStructure_of_idempotentFactor_biextension R hR D D' F A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi R₁ ρ₁ G₁ β₁ β₁₂ A₁ gen₁
    h1 h2 h3 h4 h5

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinExtCubicalSymmetricEvenFactorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finExt_cubicalSymmetric_even_factor : (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (A₀ : PolAV (Sp (FractionRing R₀))) (gen₀ : (Over.pullback (jK R₀)).obj G₀ ≅ A₀.A), FinExt ρ₀ ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P ∧ IsMonHom gen₀.hom ∧ LBIso (A₀.L.pull gen₀.hom.left) (P.L.L.pull (pullback.fst G₀.hom (jK R₀)))) := by
  first | exact @GlobalTheory.Mum.exists_finExt_cp_factor_even | exact GlobalTheory.Mum.exists_finExt_cp_factor_even | (intros; apply GlobalTheory.Mum.exists_finExt_cp_factor_even <;> assumption)
end
