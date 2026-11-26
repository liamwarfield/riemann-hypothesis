module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RankAndGOfIsPowDeg
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RosatiAdjPow
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CubBoxVal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowUnif

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig GlobalTheory.WCub

theorem tri_map {S S' : Scheme.{0}} {G G' : Over S} (f : S' ⟶ S) {E E' T : Over S'} (p : (Over.map f).obj E ⟶ G)
    (p' : (Over.map f).obj E' ⟶ G') (x : Fin 3 → (T ⟶ E')) (ρ : E' ⟶ E) (π : G' ⟶ G)
    (h : p'.left ≫ π.left = ρ.left ≫ p.left) :
    (∀ a, ((Over.map f).map (x a) ≫ p') ≫ π = (Over.map f).map (x a ≫ ρ) ≫ p) ∧
      tri f p' x ≫ (π ⊗ₘ π ⊗ₘ π).left = tri f p (fun a => x a ≫ ρ) := by
  have e : ∀ a, ((Over.map f).map (x a) ≫ p') ≫ π = (Over.map f).map (x a ≫ ρ) ≫ p := fun a =>
    Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg ((x a).left ≫ ·) h).trans
      (Category.assoc _ _ _).symm))
  refine ⟨e, ?_⟩
  show (lift _ (lift _ _) ≫ (π ⊗ₘ π ⊗ₘ π)).left = _
  rw [lift_map, lift_map, e, e, e]

theorem psum_comp {S : Scheme.{0}} {E E' T : Over S} [GrpObj E] [IsCommMonObj E] [GrpObj E'] [IsCommMonObj E']
    (x : Fin 3 → (T ⟶ E')) (ρ : E' ⟶ E) [IsMonHom ρ] (k : Finset (Fin 3)) :
    (psum E' x k).left ≫ ρ.left = (psum E (fun a => x a ≫ ρ) k).left :=
  congrArg (fun z => z.left) (psum_hom (MonoidHom.mk' (fun z : T ⟶ E' => z ≫ ρ) fun a b => MonObj.mul_comp a b ρ) x k)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem w_cub_val (U : UnifPre I D A G) (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (x : Fin 3 → (T ⟶ thickObj R I e G)) (y : T.left) {J N} (hJ : Good D.toPre.P.L y J) (hN : Good U.LG.L y N) :
    val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        (tri (thick R I e) (U.gt e).pG x) y J =
      (∏ k : thK, Geo.Tor.gw (U.w e) (psum (thickObj R I e G) x k.down).left y
        (J (tri (thick R I e) (U.gt e).pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k))
        (fun _ => N (tri (thick R I e) (fstG I e G) x ≫ thφ G (x3 G) k)) ^ thε k) *
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t (tri (thick R I e) (fstG I e G) x) y N := by
  have := (U.gt e).q_hom
  have f₃ := tri_thφ (thick R I e) (fstG I e G) x (𝟙 _) (Category.id_comp _).symm
  have f₄ := tri_thφ (thick R I e) (U.gt e).pG x (U.gt e).q rfl
  exact (clause_iff (tri (thick R I e) (U.gt e).pG x) (tri (thick R I e) (fstG I e G) x)
    (fun k : thK => (psum (thickObj R I e G) x k.down).left) _ _ _ (D.toPre.cub.t.s _) (U.cubG.t.s _)
    (fun k => (U.w e).s (fun _ => J (tri (thick R I e) (U.gt e).pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k),
      fun _ => N (tri (thick R I e) (fstG I e G) x ≫ thφ G (x3 G) k))) thε).1
    (U.w_cub e T x _ _ (fun a b e => congrArg N e) (fun a b e => congrArg J e)) y
    (hJ.mem _ _) (hN.mem _ _) (fun k => ⟨mem_pull.2 (pt_of_eq (f₄ k) y ▸
      hJ (tri (thick R I e) (U.gt e).pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k)),
      mem_pull.2 (pt_of_eq (f₃ k) y ▸ hN (tri (thick R I e) (fstG I e G) x ≫ thφ G (x3 G) k))⟩)

theorem cub_box_val (hG : GlobalFnsSt) (pD : IsPowDeg D'.toPre D.toPre j) (e : ℕ)
    {E E' T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (p : (Over.map (thick R I e)).obj E ⟶ D.toPre.P.A)
    (p' : (Over.map (thick R I e)).obj E' ⟶ D'.toPre.P.A) (x : Fin 3 → (T ⟶ E')) (ρ : Fin j → (E' ⟶ E))
    (h : ∀ i, p'.left ≫ (pD.pw.pr i).left = (ρ i).left ≫ p.left) (y : T.left) (J J')
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') :
    (∏ k : thK, om (pr := fun i => (pD.pw.pr i).left) pD.w y J J'
        (tri (thick R I e) p' x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) ^ thε k) *
      val (L := D'.toPre.P.L) (φ := thφ D'.toPre.P.A (x3 D'.toPre.P.A)) (ε := thε) D'.toPre.cub.t
        (tri (thick R I e) p' x) y J' =
      ∏ i, val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        (tri (thick R I e) p (fun a => x a ≫ ρ i)) y J := by
  have c := GlobalTheory.CubBox.cubV_box hG R j D.toPre D'.toPre pD ((Over.map (thick R I e)).obj T) y J J' hJ hJ'
    ((Over.map (thick R I e)).map (x 0) ≫ p') ((Over.map (thick R I e)).map (x 1) ≫ p')
    ((Over.map (thick R I e)).map (x 2) ≫ p')
  have q := prod_cub ((Over.map (thick R I e)).map (x 0) ≫ p') ((Over.map (thick R I e)).map (x 1) ≫ p')
    ((Over.map (thick R I e)).map (x 2) ≫ p') (om (pr := fun i => (pD.pw.pr i).left) pD.w y J J')
  refine (congrArg₂ (· * ·) q rfl).trans ((mul_comm _ _).trans (c.trans (Finset.prod_congr rfl fun i _ => ?_)))
  have t := (tri_map (thick R I e) p p' x (ρ i) (pD.pw.pr i) (h i)).1
  rw [t, t, t]
  rfl

theorem cub_box (hG : GlobalFnsSt) (pD : IsPowDeg D'.toPre D.toPre j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G)
    (e : ℕ) (g' : GtCoord I D'.toPre e G')
    (hq : ∀ i, g'.pG.left ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ (U.gt e).pG.left)
    (w' : LB.Iso ((boxLB U.LG.L pG.pr).pull (fstG I e G').left) (D'.toPre.P.L.pull g'.pG.left))
    (Q : BoxSquare (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) pD.w (U.w e) w' (rhoE I pG e))
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x : Fin 3 → (T ⟶ thickObj R I e G'))
    (jL : thK → Fin j → U.LG.L.ι) (jM : thK → D'.toPre.P.L.ι)
    (cM : LB.Coh D'.toPre.P.L (fun k => tri (thick R I e) g'.pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) jM)
    (y : T.left) (hB : tri (thick R I e) g'.pG x y ∈ LB.wchart D'.toPre.P.L (thφ D'.toPre.P.A (x3 D'.toPre.P.A)) jM)
    (hL : tri (thick R I e) (fstG I e G') x y ∈ LB.wchart (boxLB U.LG.L pG.pr) (thφ G' (x3 G')) jL) :
    gm (tri (thick R I e) g'.pG x) y (LB.wchart D'.toPre.P.L (thφ D'.toPre.P.A (x3 D'.toPre.P.A)) jM)
        (D'.toPre.cub.t.s jM) =
      (∏ k : thK, Geo.Tor.gw w' (psum (thickObj R I e G') x k.down).left y (jM k) (fun _ => jL k) ^ thε k) *
      gm (tri (thick R I e) (fstG I e G') x) y (LB.wchart (boxLB U.LG.L pG.pr) (thφ G' (x3 G')) jL)
        ((boxCub pG U.LG.L U.cubG.t).s jL) := by
  have := g'.q_hom
  have := (U.gt e).q_hom
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  let ρ : Fin j → (thickObj R I e G' ⟶ thickObj R I e G) := fun i => (Over.pullback (thick R I e)).map (pG.pr i)
  have ps : ∀ i (k : thK), (psum (thickObj R I e G') x k.down).left ≫ rhoE I pG e i =
      (psum (thickObj R I e G) (fun a => x a ≫ ρ i) k.down).left := fun i k => by
    have := pG.hom i
    exact psum_comp x (ρ i) k.down
  have f₂ := tri_thφ (thick R I e) g'.pG x g'.q rfl
  have f₃ := fun i => tri_thφ (thick R I e) (fstG I e G) (fun a => x a ≫ ρ i) (𝟙 _) (Category.id_comp _).symm
  have f₄ := fun i => tri_thφ (thick R I e) (U.gt e).pG (fun a => x a ≫ ρ i) (U.gt e).q rfl
  have hψ : ∀ i a, thφ G' (x3 G') a ≫ (pG.pr i).left = (pG.pr i ⊗ₘ pG.pr i ⊗ₘ pG.pr i).left ≫ thφ G (x3 G) a :=
    fun i a => letI := pG.hom i; (CubeMap.ofHom (pG.pr i)).psum_comm a.down
  have t := fun i => (tri_map (thick R I e) (fstG I e G) (fstG I e G') x (ρ i) (pG.pr i) (hρ i).symm).2
  have key := rel_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) D.toPre.P.isLB D'.toPre.P.isLB
    U.LG.isLB (U.w_gen e) Q hρ hq (K := thK) (ε := thε) y (fun k => (psum (thickObj R I e G') x k.down).left)
    (φ := thφ G (x3 G)) (ψ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ψ' := thφ D'.toPre.P.A (x3 D'.toPre.P.A))
    U.cubG.isGen D.toPre.cub.t D'.toPre.cub.t (tri (thick R I e) g'.pG x)
    (fun i => tri (thick R I e) (U.gt e).pG (fun a => x a ≫ ρ i))
    (fun i => tri (thick R I e) (fstG I e G) (fun a => x a ≫ ρ i))
    (fun i k => (congrArg (· ≫ fGl I G e) (ps i k)).trans (f₃ i k).symm) (fun k => (f₂ k).symm)
    (fun i k => (congrArg (· ≫ pGl U e) (ps i k)).trans (f₄ i k).symm)
    (cub_box_val hG pD e (U.gt e).pG g'.pG x ρ hq y)
    (fun i J N hJ hN => (w_cub_val U e T (fun a => x a ≫ ρ i) y hJ hN).trans (congrArg₂ (· * ·)
      (Finset.prod_congr rfl fun k _ => by rw [ps i k]) rfl))
    jL jM cM (Set.mem_iInter.1 hB) (fun k i => by
      have a : ((tri (thick R I e) (fstG I e G') x ≫ thφ G' (x3 G') k) ≫ (pG.pr i).left) y ∈ U.LG.L.U (jL k i) :=
        Set.mem_iInter.1 (Set.mem_iInter.1 hL k) i
      rw [Category.assoc, hψ, ← Category.assoc, t] at a
      exact a)
  refine key.trans (congrArg₂ (· * ·) rfl (Eq.trans (Finset.prod_congr rfl fun i _ => ?_)
    (gm_box_pull U.LG.L (fun i => (pG.pr i).left) _ hψ (fun _ => U.cubG.t) _ y jL hL).symm))
  rw [t]

end GlobalTheory.PowUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NuGeIffOfIsActOfOfPowEqOne
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaNu

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

private theorem units_mul_eq_mul_of_eq_mul {R : Type*} [CommRing R] (a b c : Rˣ) (x y : R) (h : x = y * c) :
    (a : R) * x = ((a * b⁻¹ * c : Rˣ) : R) * ((b : R) * y) := by
  rw [h, Units.val_mul, Units.val_mul]
  have hb : ((b⁻¹ : Rˣ) : R) * b = 1 := Units.inv_mul b
  linear_combination (-((a : R) * c * y)) * hb

theorem isActOf_of_sval {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S} {θ : ThetaGrp A L k T}
    {s s' : LB.Sec (LPow A L k T)}
    (h : ∀ y J, Good L y J → sval (L := L) s' (𝟙 _) y J =
      sval (L := L) s (𝟙 _ ≫ (translT A θ.pt).left) y J * (val (L := L) θ.φ (𝟙 _) y J).val) :
    IsActOf A L k θ s s' := by
  have hcomp : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left]
    unfold translT
    simp
  intro j
  refine fn_ext fun x hx => ?_
  obtain ⟨J, hJ, -⟩ := exists_good L hL x (K := Empty) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
    (fun e => e.elim)
  have hx0 : x ∈ L.wchart (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0) :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx 0
  have hx1 : (𝟙 _ ≫ (translT A θ.pt).left) x ∈ L.wchart (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1) := by
    refine Set.mem_iInter.2 fun _ => ?_
    have h1 := Set.mem_iInter.1 hx 1
    simpa [← hcomp] using h1
  have e1 := sec_trans s' (𝟙 _) x hx0 (hJ.mem _ (𝟙 _))
  have e2 := sec_trans s (𝟙 _ ≫ (translT A θ.pt).left) x hx1 (hJ.mem _ _)
  have e3 := gen_trans θ.isGen (𝟙 _) x hx (hJ.mem _ (𝟙 _))
  have key := h x J hJ
  unfold sval val at key
  refine (gs_res (𝟙 _) x _ hx _).trans (e1.trans ?_)
  refine Eq.trans ?_ (gs_mul (𝟙 _) x _ hx _ _).symm
  refine Eq.trans ?_ (congrArg₂ (· * ·) (gs_unit (𝟙 _) x _ hx _)
    ((gs_res (𝟙 _) x _ hx _).trans (gs_pull _ _ x _ hx1 _))).symm
  rw [e2, e3]
  have htr : trF ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] (𝟙 _) x j
        (fun i => J (𝟙 _ ≫ ![(snd T A).left, (translPt A θ.pt).left] i)) =
      trF (fun _ : Fin 1 => (snd T A).left) (fun _ => k) (𝟙 _) x (fun _ => j 0) (fun _ => J (𝟙 _ ≫ (snd T A).left)) *
        (trF (fun _ : Fin 1 => (snd T A).left) (fun _ => k) (𝟙 _ ≫ (translT A θ.pt).left) x (fun _ => j 1)
          (fun _ => J ((𝟙 _ ≫ (translT A θ.pt).left) ≫ (snd T A).left)))⁻¹ := by
    simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      zpow_neg, Category.assoc, hcomp]
    rw [show J ((𝟙 _ ≫ (translT A θ.pt).left) ≫ (snd T A).left) = J (𝟙 _ ≫ (translPt A θ.pt).left) by
      rw [Category.assoc, hcomp]]
    rfl
  rw [htr]
  exact units_mul_eq_mul_of_eq_mul _ _ _ _ _ key

theorem exists_isActOf {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T)
    (s : LB.Sec (LPow A L k T)) : ∃ s', IsActOf A L k θ s s' := by
  have hcomp : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left]
    unfold translT
    simp
  have hform : FormEq (Sum.elim (fun _ : Fin 1 => (translT A θ.pt).left ≫ (snd T A).left)
      ![(snd T A).left, (translPt A θ.pt).left]) (Sum.elim (fun _ => k) ![k, -k])
      (fun _ : Fin 1 => (snd T A).left) (fun _ => k) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Finset.univ_unique, Finset.prod_singleton, Sum.elim_inl, Sum.elim_inr,
      Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, hcomp]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨s₁, hs₁⟩ := exists_sec hL hform (pullMulSec s (translT A θ.pt).left θ.φ θ.isGen)
  refine ⟨s₁, isActOf_of_sval hL fun y J hJ => ?_⟩
  rw [hs₁ _ _ y J hJ]
  exact sval_pullMulSec _ _ _ _ _ _ hJ

end GlobalTheory.ThetaNu

namespace GlobalTheory


open ThetaNu in
theorem nuGe_iff_of_isActOf_of_pow_eq_one : Laws → TWStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t₀ : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t₀), P.TorsionIso → Geo.Tor.ExpBijF P.U.toUnifPre → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (k : ℕ), 1 ≤ k → ∀ (w : LB.Iso (P.A.L.pull P.U.gen.hom.left) (P.U.LG.L.pull (pullback.fst t₀.G.hom (jK V)))), w.IsGen → ∀ (θ : ThetaGrp P.A.A P.A.L (k : ℤ) (TFK (R := V) F)) (n : ℕ), 1 ≤ n → θ.pt ^ k = 1 → θ.pt ^ n = 1 → LB.Gen.Corr P.A.L _ _ _ _ (Out.powGen P.A.A P.A.L (k : ℤ) θ n) (LB.oneGen P.A.L) → ∀ (t t' : LB.Sec (LPow P.A.A P.A.L (k : ℤ) (TFK (R := V) F))) (s s' : Fam P.D.toPre F k), P.U.ExpandsF F k w t s → P.U.ExpandsF F k w t' s' → IsActOf P.A.A P.A.L (k : ℤ) θ t t' → ∀ r : ℚ, NuGe P.D Q F v k s r ↔ NuGe P.D Q F v k s' r := by
  intro hLaws hTW V _ _ _ ϖ hϖ E _ _ _ H t₀ P hTI hEB Q hQ F _ _ _ v hv k hk w hw θ n hn hθk hθn hc t t' s s' hs hs'
    hact r

  obtain ⟨f, hf, hsurj, -⟩ := hTI F k hk
  obtain ⟨p, hp⟩ := hsurj θ.pt hθk
  have hpt := (hf p θ.pt).2 hp.symm
  unfold Geo.Tor.PELUnif.ToA QkToAkU QkToAk at hpt
  obtain ⟨w₁, hw₁, hΦ⟩ := (hpt w hw).2 θ rfl

  obtain ⟨c, hTWc⟩ := hTW V ϖ hϖ P.D Q hQ F v hv k hk p w₁ hw₁ 1 one_ne_zero
  have step : ∀ (u u' : LB.Sec (LPow P.A.A P.A.L (k : ℤ) (TFK (R := V) F))) (e e' : Fam P.D.toPre F k),
      P.U.ExpandsF F k w u e → P.U.ExpandsF F k w u' e' → IsActOf P.A.A P.A.L (k : ℤ) θ u u' →
      ∀ q : ℚ, NuGe P.D Q F v k e q ↔ NuGe P.D Q F v k e' (q + c) := fun u u' e e' he he' ha q =>
    hTWc e e' e' (hΦ u u' e e' he he' ha) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff 1 e' e').2 (one_smul F e').symm) q

  have hL : P.A.L.IsLB := P.A.isLB
  choose g hg using fun u => exists_isActOf hL θ u
  have horb : ∀ m : ℕ, IsActOf P.A.A P.A.L (k : ℤ) θ (g^[m] t) (g^[m + 1] t) := fun m => by
    rw [Function.iterate_succ_apply']
    exact hg _
  have hexp := hEB F k hk w hw
  choose e he using fun m : ℕ => (hexp.1 (g^[m] t)).exists
  have hshift : ∀ (m : ℕ) (q : ℚ), NuGe P.D Q F v k (e 0) q ↔ NuGe P.D Q F v k (e m) (q + m * c) := by
    intro m
    induction m with
    | zero => intro q; simp
    | succ m ih =>
      intro q
      rw [ih q, step _ _ _ _ (he m) (he (m + 1)) (horb m)]
      push_cast
      ring_nf

  have hback : g^[n] t = t := by
    have hf := thetaGrp_act_iterate_eq_of_pow_eq_one _ P.A.A P.A.L hL (k : ℤ) (TFK (R := V) F) θ n hθn hc
      (fun i => g^[i] t) (fun i => by simpa using horb i)
    generalize hu : g^[n] t = u at hf
    simp only [Fin.val_last, Fin.val_zero, hu, Function.iterate_zero, id] at hf
    obtain ⟨uf, uc⟩ := u
    obtain ⟨tf, tc⟩ := t
    obtain rfl : uf = tf := funext hf
    rfl
  have he0 : e 0 = s := (hexp.1 t).unique (he 0) hs
  have hen : e n = s := (hexp.1 t).unique (by rw [← hback]; exact he n) hs
  have hper : ∀ q : ℚ, NuGe P.D Q F v k s q ↔ NuGe P.D Q F v k s (q + n * c) := by
    intro q
    rw [← he0, hshift n q, he0, hen]

  have hmono : ∀ q q' : ℚ, q' ≤ q → NuGe P.D Q F v k s q → NuGe P.D Q F v k s q' := by
    intro q q' hqq h χ
    obtain ⟨m, a, σ, σF, h1, h2, h3⟩ := h χ
    exact ⟨m, a, σ, σF, h1, fun i => le_trans (WithTop.coe_le_coe.2 (by linarith)) (h2 i), h3⟩
  have hs's : NuGe P.D Q F v k s (r - c) ↔ NuGe P.D Q F v k s' r := by
    simpa using step t t' s s' hs hs' hact (r - c)
  rw [← hs's]
  by_cases hc0 : c = 0
  · simp [hc0]
  · have hd : (n : ℚ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast (show n ≠ 0 by omega)) hc0
    exact ⟨fun h => PeriodicValuation.all_of_periodic hmono hd hper r _ h, fun h => PeriodicValuation.all_of_periodic hmono hd hper _ r h⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProductUniformizationTorusIsPower
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProductUniformizationTorusIsPower
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowTorus

section Box

variable {X X' Y Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

private theorem units_map_stalkMap_gm_eq_gm_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (s : Y ⟶ X) (z : Z) (U : X.Opens)
    (a : Γ(X, U)ˣ) :
    Units.map ((r.stalkMap z).hom : Y.presheaf.stalk (r z) →* Z.presheaf.stalk z) (gm s (r z) U a) =
      gm (r ≫ s) z U a := by
  unfold gm
  by_cases h : s (r z) ∈ U
  · have h' : (r ≫ s) z ∈ U := h
    rw [dite_eq_left h, dite_eq_left h']
    apply Units.ext
    simp only [Units.coe_map, MonoidHom.coe_coe]
    unfold pullU
    simp only [Units.coe_map, MonoidHom.coe_coe, MonoidHom.comp_apply]
    have key := congrArg (fun φ => φ.hom ((s.app U).hom a.val)) (Scheme.Hom.germ_stalkMap r (s ⁻¹ᵁ U) z h)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at key
    exact key
  · have h' : ¬ (r ≫ s) z ∈ U := h
    rw [dite_eq_right h, dite_eq_right h']
    simp

private theorem units_map_stalkMap_bw_eq_bw_comp {X X' Y Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
    (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (r : Z ⟶ Y) (ψ : Y ⟶ X') (z : Z) (jN : Fin j → M.ι) (k : M'.ι) :
    Units.map ((r.stalkMap z).hom : Y.presheaf.stalk (r z) →* Z.presheaf.stalk z) (bw w ψ (r z) jN k) =
      bw w (r ≫ ψ) z jN k := by
  unfold bw
  exact units_map_stalkMap_gm_eq_gm_comp r ψ z _ _

private theorem units_map_stalkMap_val_eq_val_comp {X Y Y₁ Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y₁ ⟶ X)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (s : Y ⟶ Y₁) (z : Z) (J : (Z ⟶ X) → L.ι) :
    Units.map ((r.stalkMap z).hom : Y.presheaf.stalk (r z) →* Z.presheaf.stalk z)
        (val t s (r z) (fun ψ => J (r ≫ ψ))) = val t (r ≫ s) z J := by
  rw [val_of t (r ≫ s) z J (fun k => J (r ≫ s ≫ φ k)) (fun k => by rw [Category.assoc]),
    val_of t s (r z) _ (fun k => J (r ≫ s ≫ φ k)) (fun k => rfl)]
  exact units_map_stalkMap_gm_eq_gm_comp r s z _ _

theorem box_gen_val_along (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {Y₀ : Scheme.{0}}
    {φ' : K → (Y ⟶ X')} {φ : Fin j → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε))
    (H : LB.Gen.Maps (LB.linCombIso w φ' ε) t'
      (GeneratorPullback.boxGen M pr φ' ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))))
    (r : Z ⟶ Y) (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, bw w (r ≫ φ' a) y (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r y J' =
      ∏ i, val (t i) (r ≫ ρ i) y J := by
  have E := box_gen_val w hψ t' t H (r y) (J := fun ψ => J (r ≫ ψ)) (J' := fun ψ => J' (r ≫ ψ))
    (fun ψ => hJ (r ≫ ψ)) (fun ψ => hJ' (r ≫ ψ))
  have E2 := congrArg (Units.map ((r.stalkMap y).hom : Y.presheaf.stalk (r y) →* Z.presheaf.stalk y)) E
  rw [map_mul, map_prod, map_prod] at E2
  simp only [map_zpow, units_map_stalkMap_bw_eq_bw_comp, units_map_stalkMap_val_eq_val_comp, Category.comp_id] at E2
  simp only [Category.assoc]
  exact E2

end Box

section Coord

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem val_on_torus {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (χ : D.X) {z : Z.left}
    {J : (Z.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (τ : Z ⟶ splitTorus _ D.X) :
    val (g.t χ) (τ ≫ g.i).left z J = gm τ.left z ⊤ (charUnit _ D.X χ) := by
  have h1 := GlobalTheory.TorusCoord.val_torus g χ hJ τ 1
  rw [_root_.mul_one] at h1
  rw [h1, GlobalTheory.TorusCoord.val_unit g χ hJ, _root_.mul_one]

theorem prod_on_torus (χ : D.X) {V : Type} [CommGroup V]
    (f : ((splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left ⟶ D.P.A.left) → V) :
    ∏ k, f (g.i.left ≫ D.Oφ g.pG χ k) ^ Oinvε k = 1 := by
  have k0 : g.i ≫ g.q = (1 : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ thickObj R I e G) ≫ g.q := by
    have := g.q_hom
    rw [g.isKernel.w, MonObj.one_comp]
    rfl
  have k1 : (Over.map (thick R I e)).map g.i ≫ g.pG = 1 := by
    have h := GlobalTheory.TorusCoord.im_congr g k0
    rw [GlobalTheory.TorusCoord.im_one] at h
    exact h
  have e0 : g.i.left ≫ (padd D.P.A g.pG (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ D.c χ)).left =
      g.i.left ≫ (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ D.c χ).left := by
    change ((Over.map (thick R I e)).map g.i ≫ _).left = ((Over.map (thick R I e)).map g.i ≫ _).left
    have hp : padd D.P.A g.pG (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ D.c χ) =
        g.pG * (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ D.c χ) := rfl
    rw [hp, MonObj.comp_mul, k1, _root_.one_mul]
  have e2 : g.i.left ≫ g.pG.left = g.i.left ≫ (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ η).left := by
    change ((Over.map (thick R I e)).map g.i ≫ _).left = ((Over.map (thick R I e)).map g.i ≫ _).left
    rw [k1, ← Category.assoc, toUnit_unique ((Over.map (thick R I e)).map g.i ≫ toUnit _) (toUnit _)]
    rfl
  simp only [Fin.prod_univ_four, Oinvε, DegPre.Oφ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  erw [e0, e2]
  group

end Coord

theorem gm_char_zero {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X)
    (z : Z.left) : gm τ.left z ⊤ (charUnit S X 0) = 1 := by
  have h := GlobalTheory.splitTorusPointsEquiv_val S X (splitTorus S X) (𝟙 _) 0
  rw [ofAdd_zero, map_one, Units.val_one] at h
  have h2 : charUnit S X 0 = 1 := by
    ext
    rw [Units.val_one, h]
    simp
  rw [h2, map_one]

theorem torus_ext {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ τ' : Z ⟶ splitTorus S X)
    (h : ∀ χ z, gm τ.left z ⊤ (charUnit S X χ) = gm τ'.left z ⊤ (charUnit S X χ)) : τ = τ' := by
  apply (splitTorusPointsEquiv S X Z).injective
  refine MonoidHom.ext fun χ => Units.ext ?_
  obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective χ
  rw [GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.splitTorusPointsEquiv_val]
  exact GlobalTheory.TorusCoord.appTop_eq_of_gm _ _ _ (h x)

section Pow

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}

theorem exists_factor (P : UnifPowOf3 pD pA pG U' U) (e : ℕ) (i : Fin j) :
    ∃ h : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X,
      h ≫ (U.gt e).i = (U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i) := by
  have hk := (U.gt e).isKernel
  have hη : (η : 𝟙_ _ ⟶ thickObj R I e D'.toPre.P.A) ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = η := by
    have hm := pD.pw.hom i
    change (_ ≫ _) ≫ _ = _ ≫ _
    rw [Category.assoc, ← Functor.map_comp, hm.one_hom]
  have hc : ((U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i)) ≫ (U.gt e).q =
      toUnit _ ≫ η := by
    rw [Category.assoc, ← P.q_pr e i, ← Category.assoc, (U'.gt e).isKernel.w, Category.assoc, hη]
  exact ⟨hk.lift _ _ hc, hk.lift_fst _ _ hc⟩


set_option maxHeartbeats 800000 in
theorem char_prod (P : UnifPowOf3 pD pA pG U' U) (e : ℕ)
    (h : Fin j → (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X))
    (hh : ∀ i, h i ≫ (U.gt e).i = (U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i))
    (x : D'.toPre.X) (z : (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X).left) :
    gm (𝟙 _) z ⊤ (charUnit _ D'.toPre.X x) = ∏ i, gm (h i).left z ⊤ (charUnit _ D.toPre.X (pD.xe x i)) := by
  obtain ⟨J, hJ, -⟩ := exists_good D.toPre.P.L D.toPre.P.isLB z (K := PEmpty) (fun k => k.elim)
    (fun k => k.elim) (fun a => a.elim) (fun k => k.elim)
  obtain ⟨J', hJ', -⟩ := exists_good D'.toPre.P.L D'.toPre.P.isLB z (K := PEmpty) (fun k => k.elim)
    (fun k => k.elim) (fun a => a.elim) (fun k => k.elim)
  obtain ⟨hψ, H⟩ := P.t_pr e x
  have B := box_gen_val_along pD.w hψ ((U'.gt e).t x) (fun i => (U.gt e).t (pD.xe x i)) H
    (U'.gt e).i.left z hJ hJ'
  have hP := prod_on_torus (U'.gt e) x (fun ψ => bw pD.w ψ z (fun i => J (ψ ≫ (pD.pw.pr i).left)) (J' ψ))
  rw [hP, _root_.one_mul] at B
  have L1 := val_on_torus (U'.gt e) x hJ' (𝟙 _)
  rw [Category.id_comp] at L1
  rw [L1] at B
  refine B.trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [← val_on_torus (U.gt e) (pD.xe x i) hJ (h i), hh i]
  rfl

end Pow

theorem torus_isPow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) (P : UnifPowOf3 pD pA pG U' U) (e : ℕ), ∃ pT : IsPowGrp (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X) (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X) j, (∀ i, (U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i) = pT.pr i ≫ (U.gt e).i) ∧ ∀ (i : Fin j) (χ : D.toPre.X), res (fun x _ => show (pT.pr i).left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial) (pullU (pT.pr i).left ⊤ (charUnit _ D.toPre.X χ)) = charUnit _ D'.toPre.X (pD.xe.symm (Pi.single i χ)) := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U P e
  obtain ⟨p, hp⟩ := GlobalTheory.exists_isPowGrp_splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X
    D'.toPre.X j pD.xe
  choose h hh using fun i => exists_factor P e i
  refine ⟨p, fun i => ?_, hp⟩
  have key : h i = p.pr i := by
    apply torus_ext
    intro χ z
    have c := char_prod P e h hh (pD.xe.symm (Pi.single i χ)) z
    rw [Finset.prod_eq_single i] at c
    · rw [AddEquiv.apply_symm_apply, Pi.single_eq_same] at c
      rw [← c]
      have hz := (gm_rp₁ (p.pr i).left z ⊤ ⊤ _ trivial (charUnit _ D.toPre.X χ)).symm.trans
        (congrArg (gm (𝟙 _) z ⊤) (hp i χ))
      exact hz.symm
    · intro b _ hb
      rw [AddEquiv.apply_symm_apply, Pi.single_eq_of_ne hb, gm_char_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [← hh i, key]

end GlobalTheory.PowTorus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProductUniformizationTorusIsPowerStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.productUniformization_torus_isPower : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) (P : UnifPowOf3 pD pA pG U' U) (e : ℕ), ∃ pT : IsPowGrp (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X) (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X) j, (∀ i, (U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i) = pT.pr i ≫ (U.gt e).i) ∧ ∀ (i : Fin j) (χ : D.toPre.X), res (fun x _ => show (pT.pr i).left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial) (pullU (pT.pr i).left ⊤ (charUnit _ D.toPre.X χ)) = charUnit _ D'.toPre.X (pD.xe.symm (Pi.single i χ)) := by
  first | exact @GlobalTheory.PowTorus.torus_isPow | exact GlobalTheory.PowTorus.torus_isPow | (intros; apply GlobalTheory.PowTorus.torus_isPow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymBox
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PsiEvenBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily

theorem sym_box (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D D' : DegPre R}
    (pD : IsPowDeg D' D j) {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) (y : Z) {J J'} (hJ : Good D.P.L y J)
    (hJ' : Good D'.P.L y J') :
    om pD.w y J J' (r ≫ (ι[D'.P.A]).left) * (om pD.w y J J' r)⁻¹ * val D'.sym r y J' =
      ∏ i, val D.sym (r ≫ (pD.pw.pr i).left) y J := by
  have hψ : ∀ (i : Fin j) (a : Fin 2), (![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] : Fin 2 → _) a ≫ (pD.pw.pr i).left =
      (pD.pw.pr i).left ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) a := by
    intro i a
    have := pD.pw.hom i
    fin_cases a
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]
    · simp
  have he : eSec D'.P.A ≫ D'.P.A.hom = 𝟙 _ := Over.w η[D'.P.A]
  have hp : Function.Surjective D'.P.A.hom.appTop.hom := (hG _ D'.P.A D'.P.isAb).2
  have hinv : eSec D'.P.A ≫ (ι[D'.P.A]).left = eSec D'.P.A := by
    unfold eSec
    rw [← Over.comp_left, GrpObj.one_inv]
  have hpr : ∀ i, eSec D'.P.A ≫ (pD.pw.pr i).left = eSec D.P.A := fun i => by
    have := pD.pw.hom i
    unfold eSec
    rw [← Over.comp_left, IsMonHom.one_hom]
  have hone : ∀ (E : DegPre R) (z : ↥(𝟙_ (Over (Spec (CommRingCat.of R)))).left)
      (K : ((𝟙_ (Over (Spec (CommRingCat.of R)))).left ⟶ E.P.A.left) → E.P.L.ι), Good E.P.L z K →
      val E.sym (eSec E.P.A) z K = 1 := by
    intro E z K hK
    have h := val_corr hK E.sym_rig (𝟙 _)
    rw [val_pull hK, Category.id_comp, val_one] at h
    exact h
  have key := GlobalTheory.CubBox.box_unique (φ' := ![(ι[D'.P.A]).left, 𝟙 D'.P.A.left]) (φ := ![(ι[D.P.A]).left, 𝟙 D.P.A.left])
    (ε := ![1, -1]) (ρ := fun i => (pD.pw.pr i).left) D.P.isLB D'.P.isLB pD.w pD.w_gen hψ D'.sym_gen D.sym_gen
    D'.P.A.hom (eSec D'.P.A) he hp
  specialize key (by
    intro z K K' hK hK'
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg_one,
      Category.comp_id, hinv, hpr, mul_inv_cancel]
    rw [hone D' z K' hK', hone D z K hK, Finset.prod_const_one, _root_.mul_one]) Z r y J J' hJ hJ'
  rw [Fin.prod_univ_two] at key
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg_one,
    Category.comp_id] at key
  exact key

private theorem mul_mul_eq_mul_mul_mul_inv_mul {G : Type*} [CommGroup G] (a b c s : G) :
    b * c * s = a * (c * (b * a⁻¹ * s)) := by
  rw [← mul_inv_cancel_left a (b * c * s)]
  ac_rfl

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j), D.PsiEven → D'.PsiEven := by
  intro hG R _ _ j D D' pD hE χ
  refine corr_of_val D'.P.isLB (fun y J' hJ' => ?_)
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
  have ha : D'.xK (-χ) = D'.xK χ ≫ (ι[D'.P.A]).left := by
    show ptK (D'.c (-χ)) = ptK (D'.c χ) ≫ (ι[D'.P.A]).left
    rw [GlobalTheory.PsiEvenPull.c_neg]
    unfold ptK
    rw [← Over.comp_left, Category.assoc]
  have hb : ∀ i, D'.xK χ ≫ (pD.pw.pr i).left = D.xK (pD.xe χ i) := by
    intro i
    have h := cPoint_pr pD (TK R) χ i
    unfold cP at h
    show ptK (D'.c χ) ≫ (pD.pw.pr i).left = ptK (D.c (pD.xe χ i))
    unfold ptK
    rw [← Over.comp_left, h]
  have hc : ∀ i, pD.xe (-χ) i = -pD.xe χ i := fun i => by
    rw [map_neg, Pi.neg_apply]
  have h4 : ∀ i, val (D.psi (pD.xe (-χ) i)) (𝟙 _) y J * val D.sym (D'.xK χ ≫ (pD.pw.pr i).left) y J =
      val (D.psi (pD.xe χ i)) (𝟙 _) y J := fun i => by
    have h := val_corr hJ (hE (pD.xe χ i)) (𝟙 _)
    rw [val_mul hJ, val_pull hJ, Category.id_comp] at h
    rw [hc, hb]
    exact h
  have h1 := psi_val pD hJ hJ' χ (𝟙 _)
  have h2 := psi_val pD hJ hJ' (-χ) (𝟙 _)
  have h3 := sym_box hG pD (D'.xK χ) y hJ hJ'
  rw [Category.id_comp, inv_mul_eq_iff_eq_mul] at h1 h2
  rw [ha] at h2
  rw [val_mul hJ', val_pull hJ', Category.id_comp, h1, h2]
  simp only [← h4, Finset.prod_mul_distrib]
  rw [← h3]
  exact mul_mul_eq_mul_mul_mul_inv_mul _ _ _ _

end GlobalTheory.PsiEvenBox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsoOfIsPowGrp
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
noncomputable def chartPullPullLinComb {X X' Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (pr : K → (X' ⟶ X)) (ε : K → ℤ) (F : Y ⟶ X') (g : Z ⟶ X) (p : K → (Y ⟶ Z))
    (hc : ∀ k, p k ≫ g = F ≫ pr k) :
    ChartPull ((LB.LinComb L pr ε).pull F) (LB.LinComb (L.pull g) p ε) (𝟙 Y) :=
  have le : ∀ J : PUnit → K → L.ι, ((LB.LinComb L pr ε).pull F).U J ≤
      LB.wchart (L.pull g) p (fun k _ => J PUnit.unit k) := fun J y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => by
      have h1 : (F ≫ pr k) y ∈ L.U (J PUnit.unit k) :=
        Set.mem_iInter.1 (Set.mem_iInter.1 hy PUnit.unit) k
      rw [← hc k] at h1
      exact h1
  { idx := fun J k _ => J PUnit.unit k
    le := le
    g := fun y J J' hj hj' => by
      refine (gm_pull_g (LB.LinComb L pr ε) F (𝟙 Y) y J J' hj hj').trans ?_
      refine (gm_linComb L pr ε (𝟙 Y ≫ F) y _ _ (Set.mem_iInter.1 hj PUnit.unit)
        (Set.mem_iInter.1 hj' PUnit.unit)).trans
        (Eq.trans (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
          (gm_linComb (L.pull g) p ε (𝟙 Y) y _ _ (le J hj) (le J' hj')).symm)
      refine Eq.trans ?_ (gm_pull_g L g (𝟙 Y ≫ p k) y _ _ (Set.mem_iInter.1 (le J hj) k)
        (Set.mem_iInter.1 (le J' hj') k)).symm
      rw [Category.assoc, Category.assoc, hc] }

theorem isMonHom_of_isPowGrp {S : Scheme.{0}} {H G' G : Over S} [GrpObj H] [GrpObj G'] [GrpObj G]
    {j : ℕ} (p : IsPowGrp G' G j) (f : H ⟶ G') (hf : ∀ i, IsMonHom (f ≫ p.pr i)) : IsMonHom f := by
  have ext : ∀ (a b : H ⊗ H ⟶ G'), (∀ i, a ≫ p.pr i = b ≫ p.pr i) → a = b :=
    fun a b h => Fan.IsLimit.hom_ext p.lim a b h
  have ext1 : ∀ (a b : 𝟙_ (Over S) ⟶ G'), (∀ i, a ≫ p.pr i = b ≫ p.pr i) → a = b :=
    fun a b h => Fan.IsLimit.hom_ext p.lim a b h
  constructor
  · refine ext1 _ _ fun i => ?_
    rw [Category.assoc, (hf i).one_hom, (p.hom i).one_hom]
  · refine ext _ _ fun i => ?_
    rw [Category.assoc, (hf i).mul_hom, Category.assoc, (p.hom i).mul_hom, ← Category.assoc (f ⊗ₘ f),
      tensorHom_comp_tensorHom]

theorem exists_iso_of_isPowGrp {S : Scheme.{0}} {H' H G' G : Over S} [GrpObj H'] [GrpObj H]
    [GrpObj G'] [GrpObj G] {j : ℕ} (q : IsPowGrp H' H j) (p : IsPowGrp G' G j) (e : H ≅ G)
    [IsMonHom e.hom] :
    ∃ e' : H' ≅ G', IsMonHom e'.hom ∧ ∀ i, e'.hom ≫ p.pr i = q.pr i ≫ e.hom := by
  let u : H' ⟶ G' := Fan.IsLimit.lift p.lim fun i => q.pr i ≫ e.hom
  let v : G' ⟶ H' := Fan.IsLimit.lift q.lim fun i => p.pr i ≫ e.inv
  have hu : ∀ i, u ≫ p.pr i = q.pr i ≫ e.hom := fun i => Fan.IsLimit.fac p.lim _ i
  have hv : ∀ i, v ≫ q.pr i = p.pr i ≫ e.inv := fun i => Fan.IsLimit.fac q.lim _ i
  have huv : u ≫ v = 𝟙 H' := Fan.IsLimit.hom_ext q.lim _ _ fun i => by
    change (u ≫ v) ≫ q.pr i = 𝟙 H' ≫ q.pr i
    rw [Category.assoc, hv i, ← Category.assoc, hu i, Category.assoc, e.hom_inv_id, Category.comp_id,
      Category.id_comp]
  have hvu : v ≫ u = 𝟙 G' := Fan.IsLimit.hom_ext p.lim _ _ fun i => by
    change (v ≫ u) ≫ p.pr i = 𝟙 G' ≫ p.pr i
    rw [Category.assoc, hu i, ← Category.assoc, hv i, Category.assoc, e.inv_hom_id, Category.comp_id,
      Category.id_comp]
  refine ⟨⟨u, v, huv, hvu⟩, ?_, hu⟩
  refine isMonHom_of_isPowGrp p _ fun i => ?_
  have : IsMonHom (q.pr i) := q.hom i
  change IsMonHom (u ≫ p.pr i)
  rw [hu i]
  infer_instance


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_gen_pow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G), ∃ gen' : (Over.pullback (jK R)).obj G' ≅ A'.A, IsMonHom gen'.hom ∧ (∀ i, gen'.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ ∃ w : LB.Iso (A'.L.pull gen'.hom.left) ((boxLB U.LG.L pG.pr).pull (pullback.fst G'.hom (jK R))), w.IsGen := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U
  have : IsMonHom U.gen.hom := U.gen_hom
  obtain ⟨p', hp'⟩ := isPowGrp_baseChange _ _ (jK R) G' G j pG
  obtain ⟨e', he', hc⟩ := exists_iso_of_isPowGrp p' pA.toIsPowGrp U.gen
  refine ⟨e', he', fun i => by rw [hc i, hp' i], ?_⟩
  obtain ⟨w0, hw0⟩ := U.ext
  have pullCP : ∀ {X Y : Scheme.{0}} (L : LB X) (F : Y ⟶ X), ChartPull (L.pull F) L F := fun L F =>
    { idx := fun J => J PUnit.unit
      le := fun J y hy => (mem_pull (L := L) (F := F) (x := y) (J := J)).1 hy
      g := fun y J J' hj hj' => (gm_pull_g L F (𝟙 _) y J J' hj hj').trans (by rw [Category.id_comp]) }
  have hcA : ∀ k, (p'.pr k).left ≫ U.gen.hom.left = e'.hom.left ≫ (pA.pr k).left := fun k => by
    simpa using (congrArg (fun m => m.left) (hc k)).symm
  have hcG : ∀ k, (p'.pr k).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R) ≫ (pG.pr k).left := fun k => by
    rw [hp' k]
    simp
  have H34 : LBIso (LB.LinComb (A.L.pull U.gen.hom.left) (fun k => (p'.pr k).left) (fun _ => 1))
      (LB.LinComb (U.LG.L.pull (pullback.fst G.hom (jK R))) (fun k => (p'.pr k).left) (fun _ => 1)) :=
    ⟨LB.linCombIso w0 _ _, linCombIso_isGen w0 hw0 _ _⟩
  have HB : LBIso ((boxLB A.L pA.pr).pull e'.hom.left)
      ((boxLB U.LG.L pG.pr).pull (pullback.fst G'.hom (jK R))) :=
    LBIso.chartPull
      (chartPullPullLinComb A.L (fun k => (pA.pr k).left) (fun _ => 1) e'.hom.left U.gen.hom.left
        (fun k => (p'.pr k).left) hcA)
      (chartPullPullLinComb U.LG.L (fun k => (pG.pr k).left) (fun _ => 1) (pullback.fst G'.hom (jK R))
        (pullback.fst G.hom (jK R)) (fun k => (p'.pr k).left) hcG) H34
  have HA : LBIso (A'.L.pull e'.hom.left) ((boxLB A.L pA.pr).pull e'.hom.left) :=
    LBIso.chartPull (pullCP A'.L e'.hom.left) (pullCP _ e'.hom.left) ⟨pA.w, pA.w_gen⟩
  exact LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (linComb_isLB _ A.isLB _ _) _)
    (pull_isLB (linComb_isLB _ U.LG.isLB _ _) _) HA HB

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LinOfSval
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.NuBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Generic

variable {X Y Y' Z : Scheme.{0}}

theorem lin_of_sval {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {s : LB.Sec (LB.LinComb L φ ε)} {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε))
    (H : ∀ (y : Y) J, Good L y J → sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (b i) * sval (t i) (𝟙 Y) y J)
    (j : K → L.ι) :
    s.f j = ∑ i, resTop (LB.wchart L φ j) (b i) * (show Γ(Y, LB.wchart L φ j) from (t i).f j) := by
  unfold resTop
  dsimp only
  refine fn_ext fun y hy0 => ?_
  have hy : (𝟙 Y) y ∈ LB.wchart L φ j := hy0
  show gs (𝟙 Y) y (LB.wchart L φ j) (s.f j) = gs (𝟙 Y) y (LB.wchart L φ j) _
  obtain ⟨J, hJ, hs⟩ := sval_trans hL s y j hy
  have hy' := hJ.mem φ (𝟙 Y)
  have e : ∀ i, gs (𝟙 Y) y (LB.wchart L φ j) ((t i).f j) =
      (trF φ ε (𝟙 Y) y j (fun k => J (𝟙 Y ≫ φ k))).val * sval (t i) (𝟙 Y) y J := fun i =>
    (sec_trans (t i) (𝟙 Y) y hy hy').trans (congrArg _ (sval_of (t i) (𝟙 Y) y J _ fun _ => rfl).symm)
  rw [hs, H y J hJ, Finset.mul_sum, gs_fsum _ _ _ hy]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Eq.trans ?_ (gs_mul (𝟙 Y) y (LB.wchart L φ j) hy _ ((t i).f j)).symm
  rw [gs_res (𝟙 Y) y le_top hy (b i), e i]
  ring

theorem gs_one (r : Z ⟶ Y) (z : Z) : gs r z ⊤ (1 : Γ(Y, ⊤)) = 1 := by
  rw [gs_eq r z ⊤ trivial, map_one, map_one]

end Generic

theorem le_val_prod {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {T : Type} (S : Finset T)
    (a : T → F) (q : T → ℚ) (h : ∀ i, ((q i : ℚ) : WithTop ℚ) ≤ v (a i)) :
    ((∑ i ∈ S, q i : ℚ) : WithTop ℚ) ≤ v (∏ i ∈ S, a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx, v.map_mul, WithTop.coe_add]
    exact add_le_add (h x) ih


set_option maxHeartbeats 1600000 in
theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (k : ℕ) (Fs : Fin j → Fam D.toPre F k) (F' : Fam D'.toPre F k), IsBoxFam pD F k F' Fs → ∀ r : Fin j → ℚ, (∀ i, NuGe D Q F v k (Fs i) (r i)) → NuGe D' (fun x => ∑ i, Q (pD.xe x i)) F v k F' (∑ i, r i) := by
  intro V _ _ _ ϖ hϖ j D D' pD Q hQ F _ _ v k Fs F' hB r hr
  unfold IsBoxFam at hB
  unfold NuGe at hr ⊢
  intro α'
  have hBα := hB α'
  clear hB
  obtain ⟨hφ, hB⟩ := hBα
  unfold VGe at hr ⊢
  choose n a σ σF hsc hv he using fun i => hr i (pD.xe α' i)
  clear hr
  have hM := D.toPre.P.isLB
  have hM' := D'.toPre.P.isLB

  choose σB hσB using fun m : (∀ i, Fin (n i)) =>
    exists_boxSec_val hM hM' pD.w pD.w_gen (D'.toPre.famφB α') (DegPre.famε k)
      (fun i => (pD.pw.pr i).left) (fun i => D.toPre.famφB (pD.xe α' i)) (famφB_pr pD α')
      (fun i => σ i (m i))

  choose σFB hσFB using fun m : (∀ i, Fin (n i)) =>
    exists_boxSec_val hM hM' pD.w pD.w_gen (D'.toPre.famφ F α') (DegPre.famε k)
      (prB pD F) (fun i => D.toPre.famφ F (pD.xe α' i)) hφ (fun i => σF i (m i))
  have hpr : ∀ i, (DegPre.prB D'.toPre F).left ≫ (pD.pw.pr i).left =
      prB pD F i ≫ (DegPre.prB D.toPre F).left := by
    intro i
    unfold prB
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    unfold DegPre.prB
    simp
  have hsc' : ∀ m : (∀ i, Fin (n i)), GeneratorPullback.SecScal D'.toPre.P.L (D'.toPre.famφ F α') (DegPre.famε k) (σFB m)
      (D'.toPre.famφB α') (DegPre.famε k) (σB m) (DegPre.prB D'.toPre F).left 1 := fun m =>
    BoxFamScalar.secScal_box hM hM' pD.w (GC.famφ_eq D'.toPre F α') hpr (σFB m) (fun i => σF i (m i)) (σB m)
      (fun i => σ i (m i))
      (fun y J J' hJ hJ' => hσFB m _ (𝟙 _) y J J' hJ hJ')
      (fun y J J' hJ hJ' => hσB m _ (DegPre.prB D'.toPre F).left y J J' hJ hJ')
      (fun _ => 1) 1 (fun y => by rw [Finset.prod_eq_one fun i _ => gs_one _ _, gs_one])
      (fun i => hsc i (m i))
  let e := Fintype.equivFin (∀ i, Fin (n i))
  refine ⟨Fintype.card (∀ i, Fin (n i)), fun l => ∏ i, a i (e.symm l i), fun l => σB (e.symm l),
    fun l => σFB (e.symm l), fun l => hsc' _, fun l => ?_, fun jM => ?_⟩
  · refine le_trans (le_of_eq ?_) (le_val_prod v Finset.univ _ _ fun i => hv i (e.symm l i))
    congr 1
    simp only [Finset.sum_add_distrib, Finset.sum_div, Int.cast_sum]
  ·
    have H : ∀ (y : (D'.toPre.BF F).left) (J' : ((D'.toPre.BF F).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι),
        Good D'.toPre.P.L y J' → sval (F'.s α') (𝟙 _) y J' =
          ∑ l, gs (𝟙 _) y ⊤ (((fst (TF (R := V) F) D'.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (∏ i, a i (e.symm l i)))) * sval (σFB (e.symm l)) (𝟙 _) y J' := by
      intro y J' hJ'
      obtain ⟨J, hJ, -⟩ := exists_good _ hM y (K := Empty) Empty.elim Empty.elim (fun x => x.elim)
        (fun x => x.elim)
      have hle : ∀ (jN : Fin 4 → Fin j → D.toPre.P.L.ι) (jM : Fin 4 → D'.toPre.P.L.ι) (i : Fin j),
          LB.wchart (LB.LinComb D.toPre.P.L (fun i => (pD.pw.pr i).left) (fun _ => 1)) (D'.toPre.famφ F α') jN ⊓
            LB.wchart D'.toPre.P.L (D'.toPre.famφ F α') jM ≤
              prB pD F i ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφ F (pD.xe α' i)) (fun a => jN a i) :=
        fun jN jM i => inf_le_left.trans (box_le_of_comp D.toPre.P.L (fun i => (pD.pw.pr i).left)
          (D'.toPre.famφ F α') (D.toPre.famφ F (pD.xe α' i)) (prB pD F i) i (hφ i) jN)
      have hF := BoxFamScalar.box_sval pD.w hφ (F'.s α') (fun i => (Fs i).s (pD.xe α' i)) hle hB (𝟙 _) y hJ hJ'
      have hfac : ∀ i, sval ((Fs i).s (pD.xe α' i)) (𝟙 _ ≫ prB pD F i) y J =
          ∑ l, gs (𝟙 _ ≫ prB pD F i) y ⊤ (((fst (TF (R := V) F) D.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i l))) * sval (σF i l) (𝟙 _ ≫ prB pD F i) y J := by
        intro i
        have hm := hJ.mem (D.toPre.famφ F (pD.xe α' i)) (𝟙 _ ≫ prB pD F i)
        unfold sval
        refine (congrArg (gs (𝟙 _ ≫ prB pD F i) y _) (he i _)).trans ?_
        refine (gs_fsum _ y _ hm _ _).trans (Finset.sum_congr rfl fun l _ => ?_)
        refine (gs_mul _ y _ hm _ _).trans ?_
        unfold DegPre.constBF
        exact congrArg (· * _) (gs_res _ y le_top hm _)
      have hcst : ∀ m : (∀ i, Fin (n i)), ∏ i, gs (𝟙 _ ≫ prB pD F i) y ⊤ (((fst (TF (R := V) F) D.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i (m i)))) =
          gs (𝟙 _) y ⊤ (((fst (TF (R := V) F) D'.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (∏ i, a i (m i)))) := by
        intro m
        refine BoxFamScalar.gs_scal_prod (fst (TF (R := V) F) D.toPre.P.A).left
          (fst (TF (R := V) F) D'.toPre.P.A).left (prB pD F) (fun i => ?_) y (fun i => a i (m i))
        unfold prB
        rw [← Over.comp_left]
        simp
      refine (Units.mul_right_inj (∏ a, bw pD.w (𝟙 _ ≫ D'.toPre.famφ F α' a) y (fun i => J ((𝟙 _ ≫ D'.toPre.famφ F α' a) ≫ (pD.pw.pr i).left)) (J' (𝟙 _ ≫ D'.toPre.famφ F α' a)) ^ DegPre.famε k a)).1 ?_
      refine hF.trans ?_
      rw [Finset.mul_sum]
      simp only [hfac]
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      rw [Equiv.sum_comp e.symm (fun m => ((∏ a, bw pD.w (𝟙 _ ≫ D'.toPre.famφ F α' a) y (fun i => J ((𝟙 _ ≫ D'.toPre.famφ F α' a) ≫ (pD.pw.pr i).left)) (J' (𝟙 _ ≫ D'.toPre.famφ F α' a)) ^ DegPre.famε k a) : _) * (gs (𝟙 _) y ⊤ (((fst (TF (R := V) F) D'.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (∏ i, a i (m i)))) * sval (σFB m) (𝟙 _) y J'))]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.prod_mul_distrib, hcst m, ← hσFB m _ (𝟙 _) y J J' hJ hJ']
      ring
    have key := lin_of_sval hM' _ (fun l => σFB (e.symm l)) H jM
    unfold resTop at key
    unfold DegPre.constBF
    exact key

end GlobalTheory.NuBox
end
end
