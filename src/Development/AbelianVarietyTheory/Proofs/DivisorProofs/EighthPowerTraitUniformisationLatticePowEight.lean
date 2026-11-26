module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationEighthPowerExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpOfVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsEighthPowerProjections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsTauCoord
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrFactorPointPadicAlgClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeClsPullHom

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixActsOnTorsionLabels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerEndomorphismLatticeAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerEndomorphismLatticeAdjoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.E8Endomorphism

open GlobalTheory.Poinc.Sep.EndCompat

theorem lattice_of_charMap {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (S a a' : Matrix (Fin 8) (Fin 8) ℤ)
    (hS : S.transpose = S) (hSa : S * a' = a.transpose * S) (c : Fin 8 → (X →+ Y)) (e : Y ≃+ (Fin 8 → X))
    (hT : ∀ y, ∑ v, c v (∑ u, S v u • e y u) = y) (h : Y →+ Y) (hh : ∀ u χ, h (c u χ) = ∑ v, a' u v • c v χ)
    (y : Y) : e (h y) = fun u => ∑ v, a u v • e y v := by
  have hM' : a'.transpose * S = S * a := by
    have := congrArg Matrix.transpose hSa
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hS] at this
  have hM : ∀ w u, ∑ v, a' v w * S v u = ∑ x, S w x * a x u := fun w u => by
    have := congrFun (congrFun hM' w) u
    simpa [Matrix.mul_apply] using this
  have key : ∀ x : Fin 8 → X, ∑ v, c v (∑ u, S v u • x u) = e.symm x := by
    intro x
    conv_rhs => rw [← hT (e.symm x)]
    simp
  apply e.symm.injective
  rw [AddEquiv.symm_apply_apply, ← key]
  conv_lhs => rw [← hT y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, hh, Finset.smul_sum, smul_smul]
  have L : ∀ f : Fin 8 → Fin 8 → Fin 8 → Y, ∑ v, ∑ u, ∑ w, f v u w = ∑ w, ∑ u, ∑ v, f v u w := fun f => by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun u _ => Finset.sum_comm]
    rw [Finset.sum_comm]
  calc ∑ v, ∑ u, ∑ w, (S v u * a' v w) • c w (e y u)
      = ∑ w, ∑ u, ∑ v, (S v u * a' v w) • c w (e y u) := L (fun v u w => (S v u * a' v w) • c w (e y u))
    _ = ∑ w, ∑ u, (∑ v, a' v w * S v u) • c w (e y u) := by
        refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun v _ => by rw [mul_comm]
    _ = ∑ w, ∑ u, (∑ x, S w x * a x u) • c w (e y u) := by simp only [hM]
    _ = ∑ w, ∑ x, ∑ u, (S w x * a x u) • c w (e y u) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_smul

theorem endU_lattice_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (a a' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ E' : GlobalTheory.UT.EndU U'.toUnifPre, (∀ u, E'.aA ≫ pr u = (List.ofFn fun v => pr v ^ a' u v).prod) → ∀ y, e (E'.h y) = fun u => ∑ v, a u v • e y v := by
  intro R _ _ _ hB hDVR G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniqA hL pG hpG hpGc c hc e he a a' haa' E' hE' y
  have hCN : GlobalTheory.TorRef.IsCN R := ⟨hB.1.1, hB.1.2.2.1, hB.1.2.2.2, hB.2⟩
  haveI : IsNoetherianRing R := hCN.1
  haveI : IsIntegrallyClosed R := hCN.2.1
  haveI := E'.homG
  haveI := U.gen_hom
  have hstep : ∀ u, E'.aG ≫ pG u = (List.ofFn fun v => pG v ^ a' u v).prod := by
    intro u
    haveI := hpG u
    have hR : IsMonHom (List.ofFn fun v => pG v ^ a' u v).prod := by
      refine isMonHom_of_mul _ fun T x z => ?_
      have key : ∀ w : T ⟶ G', w ≫ (List.ofFn fun v => pG v ^ a' u v).prod = ∏ v, (w ≫ pG v) ^ a' u v := fun w => by
        rw [← List.prod_ofFn]
        exact map_ofFn_prod (preH w) pG (a' u)
      rw [key, key, key, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      haveI := hpG v
      rw [MonObj.mul_comp, mul_zpow]
    obtain ⟨F0, -, huniq⟩ := GlobalTheory.semiAbelianHomExtension_holds.fractionField R (FractionRing R) G' G hG' hG
      ((Over.pullback (jK R)).map (E'.aG ≫ pG u))
    refine (huniq _ ⟨inferInstance, rfl⟩).trans (huniq _ ⟨hR, ?_⟩).symm
    rw [← cancel_mono U.gen.hom]
    have e1 : (Over.pullback (jK R)).map (E'.aG ≫ pG u) ≫ U.gen.hom =
        U'.gen.hom ≫ (List.ofFn fun v => pr v ^ a' u v).prod := by
      rw [Functor.map_comp, Category.assoc, hpGc u, ← Category.assoc, E'.ext, Category.assoc, hE' u]
    rw [e1]
    calc (Over.pullback (jK R)).map (List.ofFn fun v => pG v ^ a' u v).prod ≫ U.gen.hom
        = ((postH U.gen.hom U.gen_hom).comp (pullH (jK R) G' G)) (List.ofFn fun v => pG v ^ a' u v).prod := rfl
      _ = (List.ofFn fun v => ((postH U.gen.hom U.gen_hom).comp (pullH (jK R) G' G)) (pG v) ^ a' u v).prod :=
          map_ofFn_prod _ pG (a' u)
      _ = (List.ofFn fun v => preH U'.gen.hom (pr v) ^ a' u v).prod :=
          congrArg (fun z : Fin 8 → _ => (List.ofFn fun v => z v ^ a' u v).prod) (funext hpGc)
      _ = preH U'.gen.hom (List.ofFn fun v => pr v ^ a' u v).prod := (map_ofFn_prod _ pr (a' u)).symm
      _ = U'.gen.hom ≫ (List.ofFn fun v => pr v ^ a' u v).prod := rfl
  have hEC := GlobalTheory.Poinc.Eq8.endChar_endU R hCN D' A' G' hG' U' E'
  have hh := GlobalTheory.T.characterMap_of_integral_matrix_action R hCN D A G hG U D' A' G' hG' U' pG hpG c hc a' E'.aG E'.h E'.homG hEC hstep
  exact lattice_of_charMap (W + W.transpose) a a' (by rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm])
    haa' c e he E'.h hh y

end GlobalTheory.Poinc.E8Endomorphism
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerEndomorphismLatticeAdjointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighth_power_endomorphism_lattice_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (a a' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ E' : GlobalTheory.UT.EndU U'.toUnifPre, (∀ u, E'.aA ≫ pr u = (List.ofFn fun v => pr v ^ a' u v).prod) → ∀ y, e (E'.h y) = fun u => ∑ v, a u v • e y v := by
  first | exact @GlobalTheory.Poinc.E8Endomorphism.endU_lattice_adjoint | exact GlobalTheory.Poinc.E8Endomorphism.endU_lattice_adjoint | (intros; apply GlobalTheory.Poinc.E8Endomorphism.endU_lattice_adjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleAdjointOfGenericAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleAdjointOfGenericAdjoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.PoincAdj

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend GlobalTheory.UT GlobalTheory.Mum.Two

theorem lbIso_adj_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB A.A ![fst A.A A.A ≫ E.aA, snd A.A A.A] A.L) (cubeLB A.A ![fst A.A A.A, snd A.A A.A ≫ E'.aA] A.L) → LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) := by
  intro R _ _ _ hB G _ _ hS D A U E E' hA
  have hR : AdmBase R (maximalIdeal R) := hB.1
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  haveI := hS.smooth
  haveI := hS.geomConnected
  haveI := GlobalTheory.smooth_tensorObj_hom G G
  haveI := GlobalTheory.geometricallyIntegral_tensorObj_hom G G
  let U₁ := U.toUnifPre
  let δ := CartesianMonoidalCategory.prodComparison (Over.pullback (jK R)) G G
  let u := lift (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U₁.gen.hom)
    (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U₁.gen.hom)
  have hL := U₁.LG.isLB
  have hAL := A.isLB
  have hgen := U₁.gen_hom
  have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U₁.LG.L hL) =
      CechPic.pull U₁.gen.hom.left (cls A.L hAL) := by
    obtain ⟨w, hw⟩ := U₁.ext
    rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hAL _ (pull_isLB hAL _)]
    exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
  have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
      ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
    fun q => pullback.lift_fst _ _ _
  have hu : u.left ≫ (A.A ⊗ A.A).hom =
      ((Over.pullback (jK R)).obj G ⊗ (Over.pullback (jK R)).obj G).hom ≫ 𝟙 _ := by
    rw [Category.comp_id]; exact Over.w u
  have key : ∀ (x y : G ⟶ G) (cx cy : A.A ⟶ A.A), Gen₀ U₁ U₁ x cx → Gen₀ U₁ U₁ y cy →
      CechPic.pull (pullback.fst (G ⊗ G).hom (jK R)) (cubeCls G ![fst G G ≫ x, snd G G ≫ y] (cls U₁.LG.L hL)) =
        CechPic.pull δ.left (CechPic.pull u.left
          (cubeCls A.A ![fst A.A A.A ≫ cx, snd A.A A.A ≫ cy] (cls A.L hAL))) := by
    intro x y cx cy hx hy
    have e' := push_cubeCls (isGrpPullback_pullback G (jK R)) (T' := (Over.pullback (jK R)).obj (G ⊗ G))
      (T := G ⊗ G) (fun i => (Over.pullback (jK R)).map (![fst G G ≫ x, snd G G ≫ y] i))
      ![fst G G ≫ x, snd G G ≫ y] (pullback.fst (G ⊗ G).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U₁.LG.L hL)
    refine e'.trans ((pull_cubeCls _ ![fst _ _ ≫ (Over.pullback (jK R)).map x,
      snd _ _ ≫ (Over.pullback (jK R)).map y] _ δ (fun i => ?_) _).symm.trans ?_)
    · fin_cases i <;> simp [δ]
    rw [hc']
    refine congrArg (CechPic.pull δ.left) (push_cubeCls (isGrpPullback_of_iso U₁.gen) _ _ u.left hu (fun i => ?_) _).symm
    fin_cases i
    · show ((fst _ _ ≫ (Over.pullback (jK R)).map x) ≫ U₁.gen.hom).left = (u ≫ fst A.A A.A ≫ cx).left
      congr 1
      simp only [u, Category.assoc, lift_fst_assoc]
      rw [hx]
    · show ((snd _ _ ≫ (Over.pullback (jK R)).map y) ≫ U₁.gen.hom).left = (u ≫ snd A.A A.A ≫ cy).left
      congr 1
      simp only [u, Category.assoc, lift_snd_assoc]
      rw [hy]
  have g₁ : Gen₀ U₁ U₁ (𝟙 G) (𝟙 A.A) := by
    unfold Gen₀; rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have k₁ := key E.aG (𝟙 G) E.aA (𝟙 A.A) E.ext g₁
  have k₂ := key (𝟙 G) E'.aG (𝟙 A.A) E'.aA g₁ E'.ext
  simp only [Category.comp_id] at k₁ k₂
  have eA : cubeCls A.A ![fst A.A A.A ≫ E.aA, snd A.A A.A] (cls _ hAL) =
      cubeCls A.A ![fst A.A A.A, snd A.A A.A ≫ E'.aA] (cls _ hAL) :=
    (cls_cubeLB A.A _ hAL).symm.trans (((cls_eq_iff _ _).2 hA).trans (cls_cubeLB A.A _ hAL))
  refine GlobalTheory.Mum.lbIso_of_generic_local R (G ⊗ G) (η[G ⊗ G]).left (Over.w _) _ _ (LB.isLB_linComb hL _ _)
    (LB.isLB_linComb hL _ _) ?_
  refine (cls_eq_iff (pull_isLB (LB.isLB_linComb hL _ _) _) (pull_isLB (LB.isLB_linComb hL _ _) _)).1 ?_
  rw [cls_pull (LB.isLB_linComb hL _ _) _ (pull_isLB (LB.isLB_linComb hL _ _) _),
    cls_pull (LB.isLB_linComb hL _ _) _ (pull_isLB (LB.isLB_linComb hL _ _) _)]
  refine (congrArg (CechPic.pull _) (cls_cubeLB G ![fst G G ≫ E.aG, snd G G] hL)).trans ?_
  refine Eq.trans ?_ (congrArg (CechPic.pull _) (cls_cubeLB G ![fst G G, snd G G ≫ E'.aG] hL)).symm
  rw [k₁, k₂, eA]

end GlobalTheory.PoincAdj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleAdjointOfGenericAdjointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_adjoint_of_generic_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB A.A ![fst A.A A.A ≫ E.aA, snd A.A A.A] A.L) (cubeLB A.A ![fst A.A A.A, snd A.A A.A ≫ E'.aA] A.L) → LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) := by
  first | exact @GlobalTheory.PoincAdj.lbIso_adj_of_generic | exact GlobalTheory.PoincAdj.lbIso_adj_of_generic | (intros; apply GlobalTheory.PoincAdj.lbIso_adj_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismMovesTorsionLatticeByAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismMovesTorsionLatticeByAdjoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.EndLattice

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem congMod_y_of_end : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (m : ℕ) (pk pk' : QkPt D.toPre K m) (x : TFK (R := R) K ⟶ A.A), 1 ≤ m → QkToAkU U.toUnifPre K m pk x → QkToAkU U.toUnifPre K m pk' (x ≫ E.aA) → CongMod m pk'.y (E'.h pk.y) := by
  intro R _ _ _ hBase G _ _ hG D A U E E' hE K _ _ _ m pk pk' x hm h1 h2
  haveI : CharZero R := hBase.2
  have hAdm := hBase.1
  obtain ⟨-, hFE⟩ := GlobalTheory.UT.functorial_of_unif R (maximalIdeal R) hAdm D A G hG U
  obtain ⟨-, hK⟩ := hFE E E' hE
  obtain ⟨hex, hiota, hmap⟩ := hK K
  have hcalc := (GlobalTheory.EndCalc.end_calculus GlobalTheory.firstFiveLaws R (maximalIdeal R) hAdm D A G hG U K E E E).2.1
  choose φ hφ using fun g => (hex g).exists
  have hadd : ∀ g g' : GtPtF D.toPre K, φ (g + g') = φ g + φ g' := fun g g' =>
    (isAdd_iff_eq _ _ _).1 (hcalc g g' (g + g') _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (hφ g) (hφ g') (hφ _))
  let φh : GtPtF D.toPre K →+ GtPtF D.toPre K :=
    AddMonoidHom.mk' φ hadd
  obtain ⟨h, hns, hio⟩ := pk.eq
  have hh : h = m • pk.g := (isNsmul_iff_eq _ _ _).1 hns
  let p' : QkPt D.toPre K m :=
    ⟨E'.h pk.y, φ pk.g, φ h, (isNsmul_iff_eq _ _ _).2 (by rw [hh]; exact map_nsmul φh m pk.g), hiota _ _ _ hio (hφ h)⟩
  have h3 : QkToAkU U.toUnifPre K m p' (x ≫ E.aA) := hmap m hm pk p' x rfl (hφ pk.g) h1
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hAdm D A G hG U K m hm
  have e : f p' = f pk' := ((hf.1 _ _).1 h3).symm.trans ((hf.1 _ _).1 h2)
  obtain ⟨z, hz, -⟩ := (hf.2.2.1 _ _).1 e
  exact ⟨z, hz⟩

end GlobalTheory.EndLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismMovesTorsionLatticeByAdjointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endomorphism_moves_torsionLattice_by_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (m : ℕ) (pk pk' : QkPt D.toPre K m) (x : TFK (R := R) K ⟶ A.A), 1 ≤ m → QkToAkU U.toUnifPre K m pk x → QkToAkU U.toUnifPre K m pk' (x ≫ E.aA) → CongMod m pk'.y (E'.h pk.y) := by
  first | exact @GlobalTheory.EndLattice.congMod_y_of_end | exact GlobalTheory.EndLattice.congMod_y_of_end | (intros; apply GlobalTheory.EndLattice.congMod_y_of_end <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFormBundleMatricesAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFormBundleMatricesAdjoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.E8AdjointPairing

open GlobalTheory.CechPic

section Pairing

variable {S : Scheme.{0}} {G G' T : Over S} [GrpObj G] [GrpObj G']

def lamC (x y : T ⟶ G) : Pic G.left →+ Pic T.left where
  toFun c := lam c x y
  map_zero' := by simp only [lam, map_zero]; abel
  map_add' c d := by simp only [lam, map_add (f := _)]; abel

theorem lamC_apply (c : Pic G.left) (x y : T ⟶ G) : lamC x y c = lam c x y := rfl

theorem lam_pull_of (g : G' ⟶ G) (c : Pic G.left) (u v : T ⟶ G')
    (hm : (u * v) ≫ g = (u ≫ g) * (v ≫ g)) (h1 : (1 : T ⟶ G') ≫ g = 1) :
    lam (pull g.left c) u v = lam c (u ≫ g) (v ≫ g) := by
  simp only [lam, ← pull_comp, ← Over.comp_left, hm, h1]

end Pairing

end GlobalTheory.E8AdjointPairing

namespace GlobalTheory.E8AdjointPairing

open GlobalTheory.CechPic

section Bilinear

variable {S : Scheme.{0}} {G G' T : Over S} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
  {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen)
include hΘ

theorem lam_mul_right' (x y z : T ⟶ G) :
    lam (cls L hL) x (y * z) = lam (cls L hL) x y + lam (cls L hL) x z := by
  rw [lam_comm, lam_mul_left hL hΘ, lam_comm, lam_comm _ z]

def lamHom (z : T ⟶ G) : (T ⟶ G) →* Multiplicative (Pic T.left) where
  toFun x := Multiplicative.ofAdd (lam (cls L hL) x z)
  map_one' := by rw [lam_one_left]; rfl
  map_mul' x y := by rw [lam_mul_left hL hΘ]; rfl

theorem lam_zpow_left (x z : T ⟶ G) (k : ℤ) :
    lam (cls L hL) (x ^ k) z = k • lam (cls L hL) x z := by
  have h := map_zpow (lamHom hL hΘ z) x k
  exact congrArg Multiplicative.toAdd h

theorem lam_prod_left : ∀ (n : ℕ) (x : Fin n → (T ⟶ G)) (e : Fin n → ℤ) (z : T ⟶ G),
    lam (cls L hL) (List.ofFn fun v => x v ^ e v).prod z = ∑ v, e v • lam (cls L hL) (x v) z
  | 0, x, e, z => by simp [lam_one_left]
  | n + 1, x, e, z => by
    rw [List.ofFn_succ, List.prod_cons, lam_mul_left hL hΘ, lam_zpow_left hL hΘ,
      lam_prod_left n (fun v => x v.succ) (fun v => e v.succ) z, Fin.sum_univ_succ]

theorem lam_prod_right (n : ℕ) (x : Fin n → (T ⟶ G)) (e : Fin n → ℤ) (z : T ⟶ G) :
    lam (cls L hL) z (List.ofFn fun v => x v ^ e v).prod = ∑ v, e v • lam (cls L hL) z (x v) := by
  rw [lam_comm, lam_prod_left hL hΘ]
  simp only [lam_comm _ z]

theorem lam_lam (p q : G' ⟶ G) [IsMonHom p] [IsMonHom q] (u v : T ⟶ G') :
    lam (lam (cls L hL) p q) u v = lam (cls L hL) (u ≫ p) (v ≫ q) + lam (cls L hL) (u ≫ q) (v ≫ p) := by
  have e : lam (lam (cls L hL) p q) u v = lamC u v (lam (cls L hL) p q) := rfl
  rw [e, show lam (cls L hL) p q = pull (p * q).left (cls L hL) - pull p.left (cls L hL) - pull q.left (cls L hL)
      + pull (1 : G' ⟶ G).left (cls L hL) from rfl, map_add, map_sub, map_sub]
  simp only [lamC_apply]
  rw [lam_pull_of (p * q) _ u v (by rw [MonObj.comp_mul, MonObj.mul_comp, MonObj.mul_comp, MonObj.comp_mul,
      MonObj.comp_mul, _root_.mul_mul_mul_comm]) (by rw [MonObj.comp_mul, MonObj.one_comp, MonObj.one_comp, _root_.mul_one]),
    lam_pull_of p _ u v (MonObj.mul_comp _ _ _) (MonObj.one_comp _),
    lam_pull_of q _ u v (MonObj.mul_comp _ _ _) (MonObj.one_comp _),
    lam_pull_of (1 : G' ⟶ G) _ u v (by rw [MonObj.comp_one, MonObj.comp_one, MonObj.comp_one, _root_.mul_one])
      (MonObj.comp_one _)]
  rw [MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_one, MonObj.comp_one, lam_one_left,
    lam_mul_left hL hΘ, lam_mul_right' hL hΘ, lam_mul_right' hL hΘ]
  abel

end Bilinear

end GlobalTheory.E8AdjointPairing

namespace GlobalTheory.E8AdjointPairing

open GlobalTheory.CechPic

theorem alg_left {M : Type*} [AddCommGroup M] (S a : Matrix (Fin 8) (Fin 8) ℤ) (B : Fin 8 → Fin 8 → M) :
    ∑ i, ∑ j, S i j • ∑ v, a i v • B v j = ∑ v, ∑ j, (a.transpose * S) v j • B v j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  simp_rw [smul_comm (S _ _) (a _ _)]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

theorem alg_right {M : Type*} [AddCommGroup M] (S a' : Matrix (Fin 8) (Fin 8) ℤ) (B : Fin 8 → Fin 8 → M) :
    ∑ i, ∑ j, S i j • ∑ v, a' j v • B i v = ∑ i, ∑ v, (S * a') i v • B i v := by
  simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_comm

def precomp {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (h : T ⟶ T') : (T' ⟶ G) →* (T ⟶ G) where
  toFun y := h ≫ y
  map_one' := MonObj.comp_one h
  map_mul' := MonObj.comp_mul h

theorem comp_prod {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (h : T ⟶ T') :
    ∀ (n : ℕ) (x : Fin n → (T' ⟶ G)) (e : Fin n → ℤ),
      h ≫ (List.ofFn fun v => x v ^ e v).prod = (List.ofFn fun v => (h ≫ x v) ^ e v).prod
  | 0, x, e => by simp [MonObj.comp_one]
  | n + 1, x, e => by
    rw [List.ofFn_succ, List.prod_cons, MonObj.comp_mul, comp_prod h n, List.ofFn_succ, List.prod_cons]
    congr 1
    exact map_zpow (precomp (G := G) h) (x 0) (e 0)

theorem lbIso_cubeLB_adjoint : ∀ (K : Type) [Field K] (A A' : PolAV (Sp K)) (W : Matrix (Fin 8) (Fin 8) ℤ) (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (a a' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ (f f' : A'.A ⟶ A'.A), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → (∀ u, f' ≫ pr u = (List.ofFn fun v => pr v ^ a' u v).prod) → LBIso (cubeLB A'.A ![fst A'.A A'.A ≫ f, snd A'.A A'.A] A'.L) (cubeLB A'.A ![fst A'.A A'.A, snd A'.A A'.A ≫ f'] A'.L) := by
  intro K _ A A' W pr hpr hiso a a' hS f f' hf hf'
  have := A.isAb.comm
  obtain ⟨r, hr⟩ := A.rigid
  obtain ⟨cs⟩ := (GlobalTheory.firstFiveLaws.1.cube (Sp K) A ⟨A.L, r, A.isLB, hr⟩ rfl).1
  have hΘ : ∃ t : LB.Gen (Theta A.A A.L), t.IsGen := ⟨cs.t, cs.isGen⟩
  have hL := A.isLB
  have hL' := A'.isLB
  have hLam : (abelian₂ A.A A.L).IsLB := LB.isLB_linComb hL _ _
  have hLC := LB.isLB_linComb hLam (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
    (fun ab => W ab.1 ab.2)
  have hcA : cls A'.L hL' = ∑ ab : Fin 8 × Fin 8, W ab.1 ab.2 • lam (cls A.L hL) (pr ab.1) (pr ab.2) := by
    rw [(cls_eq_iff hL' hLC).2 hiso, cls_linComb hLam]
    refine Finset.sum_congr rfl fun ab _ => ?_
    congr 1
    rw [show cls (abelian₂ A.A A.L) hLam = lam (cls A.L hL) (fst A.A A.A) (snd A.A A.A) from cls_cube_two hL _ _ _,
      pull_lam, lift_fst, lift_snd]
  have key : ∀ {T : Over (Sp K)} (u v : T ⟶ A'.A), lam (cls A'.L hL') u v =
      ∑ i, ∑ j, (W + W.transpose) i j • lam (cls A.L hL) (u ≫ pr i) (v ≫ pr j) := by
    intro T u v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← lamC_apply, hcA, map_sum]
    simp only [map_zsmul, lamC_apply, lam_lam hL hΘ, smul_add, Finset.sum_add_distrib, Matrix.add_apply,
      Matrix.transpose_apply, add_smul]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    congr 1
    exact Finset.sum_comm
  have h₁ : (cubeLB A'.A ![fst A'.A A'.A ≫ f, snd A'.A A'.A] A'.L).IsLB := LB.isLB_linComb hL' _ _
  have h₂ : (cubeLB A'.A ![fst A'.A A'.A, snd A'.A A'.A ≫ f'] A'.L).IsLB := LB.isLB_linComb hL' _ _
  refine (cls_eq_iff h₁ h₂).1 ?_
  rw [cls_cube_two hL', cls_cube_two hL', key, key]
  simp only [Category.assoc, hf, hf', comp_prod, lam_prod_left hL hΘ, lam_prod_right hL hΘ]
  refine (alg_left (W + W.transpose) a
    (fun v j => lam (cls A.L hL) (fst A'.A A'.A ≫ pr v) (snd A'.A A'.A ≫ pr j))).trans ?_
  rw [← hS]
  exact (alg_right (W + W.transpose) a'
    (fun i v => lam (cls A.L hL) (fst A'.A A'.A ≫ pr i) (snd A'.A A'.A ≫ pr v))).symm

end GlobalTheory.E8AdjointPairing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFormBundleMatricesAdjointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_formBundle_matrices_adjoint : ∀ (K : Type) [Field K] (A A' : PolAV (Sp K)) (W : Matrix (Fin 8) (Fin 8) ℤ) (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (a a' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ (f f' : A'.A ⟶ A'.A), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → (∀ u, f' ≫ pr u = (List.ofFn fun v => pr v ^ a' u v).prod) → LBIso (cubeLB A'.A ![fst A'.A A'.A ≫ f, snd A'.A A'.A] A'.L) (cubeLB A'.A ![fst A'.A A'.A, snd A'.A A'.A ≫ f'] A'.L) := by
  first | exact @GlobalTheory.E8AdjointPairing.lbIso_cubeLB_adjoint | exact GlobalTheory.E8AdjointPairing.lbIso_cubeLB_adjoint | (intros; apply GlobalTheory.E8AdjointPairing.lbIso_cubeLB_adjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixActsOnTorsionLabels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.MatTors

theorem endU_exists (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hadm : AdmBase R (maximalIdeal R))
    (D : DegData R (maximalIdeal R)) (P : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D P G) (aA : P.A ⟶ P.A) (haA : IsMonHom aA) :
    ∃ E : GlobalTheory.UT.EndU U.toUnifPre, E.aA = aA := by
  haveI := hadm.1
  haveI := hadm.2.2.1
  have := U.gen_hom
  have hinv : IsMonHom U.gen.inv := inferInstance
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds R
    (FractionRing R) G G hG hG (U.gen.hom ≫ aA ≫ U.gen.inv)
  obtain ⟨E, -, hE⟩ := GlobalTheory.UT.exists_degenerationEndomorphism_of_admissibleBase R (maximalIdeal R) hadm D P G hG U F aA hF haA
    (by rw [hF']; simp)
  exact ⟨E, hE⟩

theorem isMonHom_matrix (S : Scheme.{0}) (X Y : Over S) [GrpObj X] [GrpObj Y] [IsCommMonObj Y] (pr : Fin 8 → (X ⟶ Y))
    (hpr : ∀ a, IsMonHom (pr a))
    (hu : ∀ (T' : Over S) (y' : Fin 8 → (T' ⟶ Y)), ∃! x : T' ⟶ X, ∀ a, x ≫ pr a = y' a) (f : X ⟶ X)
    (a : Matrix (Fin 8) (Fin 8) ℤ) (hf : ∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) : IsMonHom f := by
  haveI : ∀ v, IsMonHom (pr v) := hpr
  refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul f fun T x y => ?_
  have hz : ∀ (z : T ⟶ X) (u : Fin 8), z ≫ f ≫ pr u = ∏ v, (z ≫ pr v) ^ a u v := by
    intro z u
    let φz : (X ⟶ Y) →* (T ⟶ Y) := ⟨⟨(z ≫ ·), MonObj.comp_one z⟩, MonObj.comp_mul z⟩
    rw [hf u, List.prod_ofFn]
    exact (map_prod φz _ _).trans (Finset.prod_congr rfl fun v _ => map_zpow φz _ _)
  refine (hu T fun u => ((x * y) ≫ f) ≫ pr u).unique (fun u => rfl) (fun u => ?_)
  rw [MonObj.mul_comp, Category.assoc, Category.assoc, Category.assoc, hz, hz, hz]
  simp only [MonObj.mul_comp, mul_zpow, Finset.prod_mul_distrib]

theorem exists_adjoint (S a : Matrix (Fin 8) (Fin 8) ℤ) (hS : S.det = 1) : ∃ a', S * a' = a.transpose * S :=
  ⟨S⁻¹ * (a.transpose * S), Matrix.mul_nonsing_inv_cancel_left S _ (hS ▸ isUnit_one)⟩

theorem matrix_acts_on_torsion_labels : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (f : A'.A ⟶ A'.A), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x : TFK (R := R) K ⟶ A'.A), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' (x ≫ f) → CongMod m (e pk'.y) (fun u => ∑ v, a u v • e pk.y v) := by
  intro R _ _ _ hB hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr hpu hL pG hpG hext c hc e he a f hf K _ _ _ m pk pk' x
    hm hx hx'
  obtain ⟨a', ha⟩ := exists_adjoint (W + W.transpose) a hW.2
  obtain ⟨f', hf', -⟩ := hpu A'.A (fun u => (List.ofFn fun v => pr v ^ a' u v).prod)
  obtain ⟨E, hE⟩ := endU_exists R hB.1 D' A' G' hG' U' f (isMonHom_matrix _ A'.A A.A pr hpr hpu f a hf)
  obtain ⟨E', hE'⟩ := endU_exists R hB.1 D' A' G' hG' U' f' (isMonHom_matrix _ A'.A A.A pr hpr hpu f' a' hf')
  subst hE hE'
  have h₁ := GlobalTheory.T.eighthPower_formBundle_matrices_adjoint _ A A' W pr hpr hL a a' ha E.aA E'.aA hf hf'
  have h₂ := GlobalTheory.T.mumfordBundle_adjoint_of_generic_adjoint R hB G' hG' D' A' U' E E' h₁
  obtain ⟨w, hw⟩ := GlobalTheory.T.endomorphism_moves_torsionLattice_by_adjoint R hB G' hG' D' A' U' E E' h₂ K m pk pk' x hm hx hx'
  have h₃ := GlobalTheory.T.eighth_power_endomorphism_lattice_adjoint R hB hdvr G hG D A U G' hG' D' A' U' W hW pr hpr hpu hL pG hpG hext c hc e he a a' ha E' hf' pk.y
  exact ⟨e w, by rw [hw, map_add (f := _), map_nsmul, h₃]⟩

end GlobalTheory.Poinc.Eq8.MatTors
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixActsOnTorsionLabelsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_acts_on_torsion_labels_alt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (f : A'.A ⟶ A'.A), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x : TFK (R := R) K ⟶ A'.A), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' (x ≫ f) → CongMod m (e pk'.y) (fun u => ∑ v, a u v • e pk.y v) := by
  first | exact @GlobalTheory.Poinc.Eq8.MatTors.matrix_acts_on_torsion_labels | exact GlobalTheory.Poinc.Eq8.MatTors.matrix_acts_on_torsion_labels | (intros; apply GlobalTheory.Poinc.Eq8.MatTors.matrix_acts_on_torsion_labels <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsExtendUniformisedGroups
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsExtendUniformisedGroups
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

def matAddEquiv {M : Type*} [AddCommGroup M] (S : Matrix (Fin 8) (Fin 8) ℤ) (hS : S.det = 1) :
    (Fin 8 → M) ≃+ (Fin 8 → M) where
  toFun w v := ∑ u, S v u • w u
  invFun w v := ∑ u, S.adjugate v u • w u
  left_inv w := by
    funext v
    have h : S.adjugate * S = 1 := by rw [Matrix.adjugate_mul, hS, one_smul]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  right_inv w := by
    funext v
    have h : S * S.adjugate = 1 := by rw [Matrix.mul_adjugate, hS, one_smul]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  map_add' x y := by
    funext v
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

def sumChars {X X' : Type*} [AddCommGroup X] [AddCommGroup X'] (c : Fin 8 → (X →+ X')) : (Fin 8 → X) →+ X' where
  toFun y := ∑ v, c v (y v)
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

theorem e8data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∃ (pG : Fin 8 → (G' ⟶ G)) (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)) (e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X)), (∀ v, IsMonHom (pG v)) ∧ (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) ∧ (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) ∧ ∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y := by
  intro R _ _ _ hR hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniv hL
  haveI := hdvr
  haveI := U.gen_hom
  haveI := U'.gen_hom
  have hpG : ∀ v, ∃ F : G' ⟶ G, IsMonHom F ∧
      (Over.pullback (jK R)).map F = U'.gen.hom ≫ pr v ≫ U.gen.inv := by
    intro v
    haveI := hpr v
    obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) G' G hG' hG
      (U'.gen.hom ≫ pr v ≫ U.gen.inv) inferInstance
    exact ⟨F, hF, hF'⟩
  choose pG hpGm hpGg using hpG
  have hgen : ∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v := by
    intro v
    rw [hpGg v]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  choose c hc using fun v =>
    GlobalTheory.Poinc.HomTor.exists_torMatch R hR G hG D A U G' hG' D' A' U' (pG v) (hpGm v)
  have hbij := (characters_eighthPower_elementaryMatrices R hR hdvr G hG D A U G' hG' D' A' U' W hW pr hpr huniv hL pG hpGm hgen c hc).1
  let Φ := AddEquiv.ofBijective (sumChars c) hbij
  let Sm := matAddEquiv (M := D.toPre.X) (W + W.transpose) hW.2
  refine ⟨pG, c, Φ.symm.trans Sm.symm, hpGm, hgen, hc, fun y => ?_⟩
  have h1 : Sm ((Φ.symm.trans Sm.symm) y) = Φ.symm y := by simp
  have h2 : Φ (Φ.symm y) = y := Φ.apply_symm_apply y
  rw [← h1] at h2
  exact h2

end GlobalTheory.Poinc.Eq8
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsExtendUniformisedGroupsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_projections_extend_uniformisedGroups : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∃ (pG : Fin 8 → (G' ⟶ G)) (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)) (e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X)), (∀ v, IsMonHom (pG v)) ∧ (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) ∧ (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) ∧ ∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y := by
  first | exact @GlobalTheory.Poinc.Eq8.e8data | exact GlobalTheory.Poinc.Eq8.e8data | (intros; apply GlobalTheory.Poinc.Eq8.e8data <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerPsiOrdersProjectionLatticeCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerPsiOrdersProjectionLatticeCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.E8Lattice

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (ϖ : R) (β : LinearMap.BilinForm ℤ D.toPre.X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → (∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) ϖ ^ (β a b')) → ∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W β (e y) ∧ Associated r (ϖ ^ (qW W β (e y)).toNat) := by
  intro R _ _ _ hRb hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniv hL pG hpG hgen c hc e hsum ϖ β hs hp hτ y r hr
  refine GlobalTheory.Poinc.E8Order.main R hdvr D.toPre D'.toPre D'.tau_bimult D'.psi_even D.tau_bimult W hW ϖ β hs hp hτ c e hsum
    ?_ y r hr
  intro v a' b x x' hx hx'
  exact GlobalTheory.TauFormHom.main R hRb hdvr G hG D A U G' hG' D' A' U' (pG v) (hpG v) (c v)
    ((Pi.evalAddMonoidHom (fun _ : Fin 8 => D.toPre.X) v).comp e.toAddMonoidHom) (hc v)
    (GlobalTheory.T.torsionLabels_eighthPower_projections R hRb hdvr G hG D A U G' hG' D' A' U' W hW pr hpr huniv hL pG hpG hgen c hc e hsum v)
    a' b x x' hx hx'

end GlobalTheory.Poinc.E8Lattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerPsiOrdersProjectionLatticeCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_psiOrders_projectionLatticeCoordinates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (ϖ : R) (β : LinearMap.BilinForm ℤ D.toPre.X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → (∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) ϖ ^ (β a b')) → ∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W β (e y) ∧ Associated r (ϖ ^ (qW W β (e y)).toNat) := by
  first | exact @GlobalTheory.Poinc.E8Lattice.main | exact GlobalTheory.Poinc.E8Lattice.main | (intros; apply GlobalTheory.Poinc.E8Lattice.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerTraitUniformisationLatticePowEight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.EighthTorsion
open MonObj

def postcomp {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f] :
    (T ⟶ G) →* (T ⟶ H) where
  toFun g := g ≫ f
  map_one' := by simp
  map_mul' a b := by simp [MonObj.mul_comp]

theorem prod_comp {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f]
    (l : List (T ⟶ G)) : l.prod ≫ f = (l.map (· ≫ f)).prod :=
  (map_list_prod (postcomp (T := T) f) l)

theorem zpow_comp' {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f]
    (g : T ⟶ G) (n : ℤ) : (g ^ n) ≫ f = (g ≫ f) ^ n :=
  map_zpow (postcomp (T := T) f) g n

theorem ident_pow {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T : Trait F)
    (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (hD : IsDiagEnd F W P T.y ε)
    (A8 : PolAV (Sp (FractionRing T.V))) (pA : IsPowPolAV A8 T.A 8) :
    ∃ φ : P.A ≅ A8.A, IsMonHom φ.hom ∧
      LBIso P.L (LB.LinComb (abelian₂ T.A.A T.A.L) (K := Fin 8 × Fin 8)
        (fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left) (fun ab => W ab.1 ab.2)) ∧
      ∀ E a, ε E ≫ φ.hom ≫ pA.pr a = ((List.finRange 8).map fun b => (φ.hom ≫ pA.pr b) ^ E a b).prod := by
  obtain ⟨c, ⟨φc, φ₂, hc, hsq, ⟨w, hw⟩, -⟩, pr, hpr, huniv, hL, hε⟩ := hD
  obtain ⟨e, he, hee⟩ := grpPullback_iso hc T.cart
  let p : IsPowGrp P.A T.A.A 8 :=
    { pr := fun a => pr a ≫ e.hom
      hom := fun a => by have := hpr a; infer_instance
      lim := Fan.IsLimit.mk _ (fun s => (huniv s.pt fun a => s.proj a ≫ e.inv).choose)
        (fun s a => by
          have h := (huniv s.pt fun a => s.proj a ≫ e.inv).choose_spec.1 a
          change _ ≫ pr a ≫ e.hom = _
          rw [← Category.assoc, h, Category.assoc, e.inv_hom_id, Category.comp_id])
        (fun s m hm => (huniv s.pt fun a => s.proj a ≫ e.inv).choose_spec.2 m fun a => by
          have h : m ≫ pr a ≫ e.hom = s.proj a := hm a
          rw [← h, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]) }
  obtain ⟨φ, hφ, hφp⟩ := GlobalTheory.PowerExamples.pow_unique p pA.toIsPowGrp
  have hφp' : ∀ a, φ.hom ≫ pA.pr a = pr a ≫ e.hom := hφp
  refine ⟨φ, hφ, ?_, ?_⟩
  · have hpt : ∀ a, (pr a).left ≫ φc = (φ.hom ≫ pA.pr a).left ≫ T.α := fun a => by
      rw [hφp' a, Over.comp_left, Category.assoc, hee]
    have hΛ : (abelian₂ T.A.A T.A.L).IsLB := LB.isLB_linComb T.A.isLB _ _
    obtain ⟨w', hw'⟩ := T.lb
    have i₁ := iso_linComb ((isGen_iff w).1 hw) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
      (fun ab => W ab.1 ab.2)
    have i₂ := iso_linComb ((isGen_iff w').1 hw') (K := Fin 8 × Fin 8)
      (fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left) (fun ab => W ab.1 ab.2)
    have hm : (fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left ≫ φ₂) =
        fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left ≫ T.α₂ :=
      funext fun ab => GlobalTheory.Poinc.SharpIdent.lift_comp_square hsq T.sq _ _ _ _ (hpt ab.1) (hpt ab.2)
    rw [hm] at i₁
    exact LBIso.trans P.isLB (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb hΛ _ _) hL
      (LBIso.trans (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb F.univ.isLB _ _) (LB.isLB_linComb hΛ _ _) i₁ i₂.symm)
  · intro E a
    haveI := he
    rw [hφp' a, ← Category.assoc, hε E a, prod_comp, List.map_map]
    congr 1
    refine List.map_congr_left fun b _ => ?_
    simp only [Function.comp_apply, hφp' b]
    exact zpow_comp' e.hom (pr b) (E a b)

theorem exists_proj {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T : Trait F)
    (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (hD : IsDiagEnd F W P T.y ε) :
    ∃ pr : Fin 8 → (P.A ⟶ T.A.A), (∀ a, IsMonHom (pr a)) ∧
      (∀ (T' : Over (Sp (FractionRing T.V))) (y : Fin 8 → (T' ⟶ T.A.A)), ∃! z : T' ⟶ P.A, ∀ a, z ≫ pr a = y a) ∧
      LBIso P.L (LB.LinComb (abelian₂ T.A.A T.A.L) (K := Fin 8 × Fin 8)
        (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) ∧
      ∀ E a, ε E ≫ pr a = (List.ofFn fun b => pr b ^ E a b).prod := by
  obtain ⟨A8, pA, -⟩ := GlobalTheory.exists_powPolAV _ T.A 8
  obtain ⟨φ, hφ, hL, hε⟩ := ident_pow F W T P ε hD A8 pA
  refine ⟨fun a => φ.hom ≫ pA.pr a, fun a => by have := pA.hom a; infer_instance, fun T' y => ?_, hL,
    fun E a => by rw [List.ofFn_eq_map]; exact hε E a⟩
  refine ⟨pA.lim.lift (Fan.mk T' y) ≫ φ.inv, fun a => ?_, fun z hz => ?_⟩
  · rw [Category.assoc, φ.inv_hom_id_assoc]
    exact pA.lim.fac (Fan.mk T' y) ⟨a⟩
  · rw [Iso.eq_comp_inv]
    exact pA.lim.uniq (Fan.mk T' y) _ fun a => (Category.assoc _ _ _).trans (hz a.as)

theorem tau_coord {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} (T : Trait F) (a b' : T.D.toPre.X)
    (x : (FractionRing T.V)ˣ) (hx : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord T.D.toPre a b' x) :
    ∃ u : T.Vˣ, (x : FractionRing T.V) =
      algebraMap T.V (FractionRing T.V) (u : T.V) * algebraMap T.V (FractionRing T.V) T.ϖ ^ (T.β a b') := by
  obtain ⟨x₁, h₁⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord T.D.toPre (a + b')
  obtain ⟨x₂, h₂⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord T.D.toPre a
  obtain ⟨x₃, h₃⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord T.D.toPre b'
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.TauCoordQuot.main T.V T.D.toPre a b' x x₁ x₂ x₃ hx h₁ h₂ h₃
  obtain ⟨r₁, c₁, e₁⟩ :=
    GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top T.D _) h₁
  obtain ⟨r₂, c₂, e₂⟩ :=
    GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top T.D _) h₂
  obtain ⟨r₃, c₃, e₃⟩ :=
    GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top T.D _) h₃
  obtain ⟨u, hu⟩ := T.mono.tau (fun i y z => by fin_cases i; exact T.symm y z)
    (Fin.forall_fin_one.2 T.irr.ne_zero) c₂ c₃ c₁
  simp only [Fin.prod_univ_one, Matrix.cons_val_zero] at hu
  refine ⟨u₀ * u, ?_⟩
  have key : algebraMap T.V (FractionRing T.V) (u₀ : T.V) * algebraMap T.V (FractionRing T.V) r₁ *
      (algebraMap T.V (FractionRing T.V) r₂)⁻¹ * (algebraMap T.V (FractionRing T.V) r₃)⁻¹ =
      algebraMap T.V (FractionRing T.V) (u₀ : T.V) * (algebraMap T.V (FractionRing T.V) r₁ /
        (algebraMap T.V (FractionRing T.V) r₂ * algebraMap T.V (FractionRing T.V) r₃)) := by
    rw [div_eq_mul_inv, mul_inv]; ring
  rw [hu₀, e₁, e₂, e₃, key, hu]
  simp only [Units.val_mul, map_mul]
  ring

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (T : Trait F) (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)), IsDiagEnd F W P T.y ε → ∃ (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G'), IsSemiAbelian G' ∧ ∃ (D' : DegData T.V (maximalIdeal T.V)) (U' : Unif (maximalIdeal T.V) D' P G') (j : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ y, ∃ v : T.Vˣ, PsiCoord D'.toPre y (v * T.ϖ ^ (qW W T.β (j y)).toNat)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing T.V) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x x' : TFK (R := T.V) K ⟶ P.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' x' → x' = x ≫ ε E → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b) := by
  intro g n F W hW T P ε hD
  have hCN : GlobalTheory.TorRef.IsCN T.V := ⟨inferInstance, inferInstance, T.complete, T.char⟩
  have hB : GlobalTheory.Mum.Base T.V := ⟨⟨inferInstance, inferInstance, inferInstance, T.complete⟩, T.char⟩
  have hS : SharpOver F W P T.y := by
    obtain ⟨c, hc, pr, h₁, h₂, h₃, -⟩ := hD
    exact ⟨c, hc, pr, h₁, h₂, h₃⟩
  haveI : IsCommMonObj (powObj T.G 8) := GlobalTheory.PowerExamples.comm_of_pow (powIsPowGrp T.G 8)
  have hG' : IsSemiAbelian (powObj T.G 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ T.G 8 (powIsPowGrp T.G 8) T.semi
  obtain ⟨D', ⟨U'⟩⟩ := GlobalTheory.PowE8.exists_unif_pow8 g n _ _ F W hW T.V hCN T.D T.G T.A T.U T.y T.α T.α₂ T.semi T.cart
    T.sq T.lb P hS
  obtain ⟨pr, hpr, huniv, hL, hε⟩ := exists_proj F W T P ε hD
  obtain ⟨pG, c, e, hpG, hgen, hc, he⟩ := GlobalTheory.T.eighthPower_projections_extend_uniformisedGroups T.V hB T.dvr T.G T.semi T.D T.A T.U _ hG' D' P U' W hW pr hpr
    huniv hL
  have hnn : ∀ a, 0 ≤ T.β a a := fun a => by
    by_cases ha : a = 0
    · simp [ha]
    · exact (GlobalTheory.Poinc.Trait.beta_pos g n _ _ F T a ha).le
  refine ⟨powObj T.G 8, inferInstance, inferInstance, hG', D', U', e, fun y => ?_, ?_⟩
  · obtain ⟨r, hr⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff _ y).2 (GlobalTheory.PeriodFormCompare.psiIn_top D' y)
    obtain ⟨-, h⟩ := GlobalTheory.T.eighthPower_psiOrders_projectionLatticeCoordinates T.V hB T.dvr T.G T.semi T.D T.A T.U _ hG' D' P U' W hW pr hpr huniv hL pG hpG hgen c hc
      e he T.ϖ T.β T.symm hnn (tau_coord T) y r hr
    obtain ⟨v, hv⟩ := h.symm
    exact ⟨v, by rw [mul_comm, hv]; exact hr⟩
  · rintro K _ _ _ m pk pk' x x' E hm h h' rfl
    exact GlobalTheory.T.matrix_acts_on_torsion_labels_alt T.V hB T.dvr T.G T.semi T.D T.A T.U _ hG' D' P U' W hW pr hpr huniv hL pG hpG hgen c hc e he E (ε E)
      (hε E) K m pk pk' x hm h h'

end GlobalTheory.EighthTorsion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerTraitUniformisationLatticePowEightStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_trait_uniformisation_lattice_pow_eight : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (T : Trait F) (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)), IsDiagEnd F W P T.y ε → ∃ (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G'), IsSemiAbelian G' ∧ ∃ (D' : DegData T.V (maximalIdeal T.V)) (U' : Unif (maximalIdeal T.V) D' P G') (j : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ y, ∃ v : T.Vˣ, PsiCoord D'.toPre y (v * T.ϖ ^ (qW W T.β (j y)).toNat)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing T.V) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x x' : TFK (R := T.V) K ⟶ P.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' x' → x' = x ≫ ε E → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b)) := by
  first | exact @GlobalTheory.EighthTorsion.main | exact GlobalTheory.EighthTorsion.main | (intros; apply GlobalTheory.EighthTorsion.main <;> assumption)
end
