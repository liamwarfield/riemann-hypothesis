module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
public import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankHostDivTwo
public import Formalism.LocalToGlobal.ProjectiveLattices.LieFreePf
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NumberFieldFinitePlaceCompletionEmbedding

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndep
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndep
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.LiftUnique

theorem cube_rig_comp {S S' S'' : Scheme.{0}} {G'' : Over S''} {G' : Over S'} {G : Over S} [GrpObj G'']
    [IsCommMonObj G''] [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (m : CubeMap G' G)
    (m' : CubeMap G'' G') (n : CubeMap G'' G) (hF : n.F = m'.F ≫ m.F) (he : n.e = m'.e ≫ m.e)
    (L'' : RigLB G'') (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F))
    (w' : LB.Iso L''.L (L'.L.pull m'.F))
    (hw : w.IsGen ∧ LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig
      (m.rigPull L.L L.rig))
    (hw' : w'.IsGen ∧ LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec G'') (fun _ => 1)) L''.rig
      (m'.rigPull L'.L L'.rig)) :
    ∃ w'' : LB.Iso L''.L (L.L.pull n.F),
      (w''.IsGen ∧ LB.Gen.Maps (LB.linCombIso w'' (K := PUnit) (fun _ => eSec G'') (fun _ => 1)) L''.rig
        (n.rigPull L.L L.rig)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ G''.left) (z : Z) (j : L.L.ι) (i : L'.L.ι) (k : L''.L.ι),
        n.F (r z) ∈ L.L.U j → m'.F (r z) ∈ L'.L.U i → r z ∈ L''.L.U k →
        gw w'' r z j k = gw w (r ≫ m'.F) z j i * gw w' r z i k := by
  obtain ⟨Fn, F3, e, hec, hp⟩ := n
  dsimp only at hF he
  subst hF he
  have g := (isGen_iff w).1 hw.1
  have g' := (isGen_iff w').1 hw'.1
  have r := (maps_iff w _ (fun _ => eSec G) _ L'.rig L.rig m.e _ (rigPull_le m.F m.e m.e_comm L.L)
    (fun _ => rfl)).1 hw.2
  have r' := (maps_iff w' _ (fun _ => eSec G') _ L''.rig L'.rig m'.e _ (rigPull_le m'.F m'.e m'.e_comm L'.L)
    (fun _ => rfl)).1 hw'.2
  obtain ⟨w'', T⟩ := exists_comp L'.isLB w w' g g' L.isLB L''.isLB
  exact ⟨w'', ⟨(isGen_iff w'').2 (T.pgen_comp L'.isLB g g'),
    (maps_iff w'' _ (fun _ => eSec G) _ L''.rig L.rig (m'.e ≫ m.e) _ (rigPull_le _ _ hec L.L) (fun _ => rfl)).2
      (T.pmaps_comp L'.isLB (fun _ => m'.e_comm) r r')⟩, T⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rig_comp {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f : S' ⟶ S} (m : SABMap t₁ t f)
    (m' : SABMap t₂ t₁ (𝟙 S')) (n : SABMap t₂ t f) (hF : n.φ = m'.φ ≫ m.φ)
    (w : LB.Iso t₁.PP.L (t.PP.L.pull m.φ)) (w' : LB.Iso t₂.PP.L (t₁.PP.L.pull m'.φ)) (hw : RigIso m w)
    (hw' : RigIso m' w') :
    ∃ w'' : LB.Iso t₂.PP.L (t.PP.L.pull n.φ), RigIso n w'' ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ t₂.G.left) (z : Z) (j : t.PP.L.ι) (i : t₁.PP.L.ι) (k : t₂.PP.L.ι),
        n.φ (r z) ∈ t.PP.L.U j → m'.φ (r z) ∈ t₁.PP.L.U i → r z ∈ t₂.PP.L.U k →
        gw w'' r z j k = gw w (r ≫ m'.φ) z j i * gw w' r z i k :=
  cube_rig_comp m.cm m'.cm n.cm hF (by rw [n.base, m.base, m'.base]; exact (Category.id_comp f).symm) _ _ _ w w' hw hw'

theorem exists_over_id {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f f' : S' ⟶ S} (e : f' = 𝟙 _ ≫ f)
    (m : SABMap t₁ t f) (n : SABMap t₂ t f') : ∃ m' : SABMap t₂ t₁ (𝟙 S'), n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ t t₁ t₂ f (𝟙 _) m n

theorem exists_hom {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f f' : S' ⟶ S} (e : f' = f)
    (m : SABMap t₁ t f) (n : SABMap t₂ t f') : ∃ ψ : t₁.G ⟶ t₂.G, IsMonHom ψ ∧ ψ.left ≫ n.φ = m.φ := by
  subst e
  obtain ⟨ψ, h₁, h₂, -⟩ := sabMap_iso m n rfl rfl
  exact ⟨ψ.hom, h₁, h₂⟩

theorem lieComb_map {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G'] (ψ : G ⟶ G') [IsMonHom ψ]
    {n : ℕ} {c : Fin n → R} {v : Fin n → (epsR R ⟶ G)} {w : epsR R ⟶ G} (h : IsLieComb c v w) :
    IsLieComb c (fun j => v j ≫ ψ) (w ≫ ψ) := by
  obtain ⟨u, hu, rfl⟩ := h
  have hL : ∀ L : List (epsR R ⟶ G), (L.map (· ≫ ψ)).prod = L.prod ≫ ψ := by
    intro L
    induction L with
    | nil => simp [MonObj.one_comp]
    | cons a L ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih, MonObj.mul_comp]
  refine ⟨fun j => u j ≫ ψ, fun j => ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left, hu j, Category.assoc]
  · rw [← hL, List.map_ofFn]
    rfl

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {M : MChart Y} {R : Type} [CommRing R] [Algebra c.F R] {f : Γ(Y.X, M.U) →+* R}
  {x : Sp R ⟶ Xo.X}

theorem xF_eq (Λ Λ' : M.Lift f x) : Λ'.xF = Λ.xF := by
  apply pullback.hom_ext
  · exact Λ'.xF_fst.trans Λ.xF_fst.symm
  · exact Λ'.xF_snd.trans Λ.xF_snd.symm

theorem vec (Λ Λ' : M.Lift f x) (cv : Fin M.n → R) (w : Sp (DualNumber R) ⟶ Xo.univ.t.G.left) (h : Λ.Vec cv w) :
    Λ'.Vec cv w := by
  obtain ⟨ψ, hψ, e⟩ := exists_hom (xF_eq Λ Λ') Λ.m' Λ'.m'
  obtain ⟨v', u', h₁, h₂, h₃⟩ := h
  have e₁ : ψ.left ≫ Λ'.m1.φ = Λ.m1.φ := by rw [Λ'.liftedChartMap_eq, Λ.liftedChartMap_eq, ← Category.assoc, e]
  have e₂ : ψ.left ≫ Λ'.m2.φ = Λ.m2.φ := by rw [Λ'.matrix_two_by_two_congr, Λ.matrix_two_by_two_congr, ← Category.assoc, e]
  refine ⟨fun j => v' j ≫ ψ, u' ≫ ψ, fun j => ?_, lieComb_map ψ h₂, ?_⟩
  · rw [Over.comp_left, Category.assoc, e₂, h₁ j]
  · rw [Over.comp_left, Category.assoc, e₁, h₃]

theorem thTie (Λ Λ' : M.Lift f x) (s : LB.Sec (PPx x)) (h : Λ.ThTie s) : Λ'.ThTie s := by
  obtain ⟨n, e⟩ := exists_over_id ((xF_eq Λ Λ').trans (Category.id_comp _).symm) Λ.m' Λ'.m'
  have e₁ : Λ'.m1.φ = n.φ ≫ Λ.m1.φ := by rw [Λ'.liftedChartMap_eq, Λ.liftedChartMap_eq, ← Category.assoc, e]
  have e₂ : Λ'.m2.φ = n.φ ≫ Λ.m2.φ := by rw [Λ'.matrix_two_by_two_congr, Λ.matrix_two_by_two_congr, ← Category.assoc, e]
  obtain ⟨w1, w2, σ, s1, r1, r2, i1, c2, c1⟩ := h
  obtain ⟨w0, g0, r0, -⟩ := n.lin
  obtain ⟨w1', r1', T1⟩ := rig_comp Λ.m1 n Λ'.m1 e₁ w1 w0 r1 ⟨g0, r0⟩
  obtain ⟨w2', r2', T2⟩ := rig_comp Λ.m2 n Λ'.m2 e₂ w2 w0 r2 ⟨g0, r0⟩
  have hL := Λ.t'.PP.isLB
  have hL' := Λ'.t'.PP.isLB
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w0).1 g0) hL hL' σ
  obtain ⟨s1', hs1⟩ := thf_secUp ((isGen_iff w1').1 r1'.1) Xo.univ.t.PP.isLB hL' σ'
  refine ⟨w1', w2', σ', s1', r1', r2', fun (i : PUnit → Xo.univ.t.PP.L.ι) k => fn_ext fun y hy => ?_,
    fun j k W h₁ h₂ => fn_ext fun y hy => ?_, fun g hs hf (j : PUnit → Xo.univ.t.PP.L.ι) hj => fn_ext fun y hy => ?_⟩
  · exact (gs_res _ y _ hy _).trans ((hs1 _ (𝟙 _) y i k hy.1 hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _)))))
  · obtain ⟨i, hi⟩ := exists_chart hL (n.φ y)
    have hm : Λ.m2.φ (n.φ y) ∈ Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j :=
      (congrArg (fun q => q y ∈ Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) e₂).mp (h₁ hy)
    have hz : (𝟙 _ ≫ n.φ) y ∈ Λ.m2.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) ⊓
        ((Y.t.PP.L.pull Λ.m2.φ).U (fun _ => j) ⊓ Λ.t'.PP.L.U i) := ⟨hm, mem_pull.2 hm.2, hi⟩
    have a := congrArg (gs (𝟙 _ ≫ n.φ) y _) (c2 j i _ inf_le_left inf_le_right)
    have a' : gs ((𝟙 _ ≫ n.φ) ≫ Λ.m2.φ) y _ (M.θ j) =
        (gw w2 (𝟙 _ ≫ n.φ) y j i).val * gs (𝟙 _ ≫ n.φ) y _ (σ.f i) :=
      (gs_appLE Λ.m2.φ _ _ _ _ y hz _).symm.trans (a.trans ((gs_mul _ y _ hz _ _).trans
        (congrArg₂ (· * ·) ((gs_res _ y _ hz _).trans (gs_unit _ y _ hz.2 _)) (gs_res _ y _ hz _))))
    have b := hσ' _ (𝟙 _) y i k hi (h₂ hy).2
    have t := T2 _ (𝟙 _) y j i k (h₁ hy).2 hi (h₂ hy).2
    refine (gs_appLE Λ'.m2.φ _ _ h₁ (𝟙 _) y hy _).trans ?_
    refine (congrArg (fun q => gs q y _ (M.θ j))
      (show 𝟙 _ ≫ Λ'.m2.φ = (𝟙 _ ≫ n.φ) ≫ Λ.m2.φ by rw [e₂, Category.assoc])).trans (a'.trans ?_)
    refine Eq.symm ((gs_mul _ y _ hy _ _).trans ((congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_unit _ y _ (h₂ hy) _).trans (congrArg Units.val t))) (gs_res _ y _ hy _)).trans ?_))
    rw [Units.val_mul, _root_.mul_assoc]
    exact congrArg _ b.symm
  · let A := Xo.univ.t.G
    let a0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk Λ.t'.G.hom rfl
    let b0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ A := Over.homMk Λ.m1.φ Λ.m1.cart.1.w
    let q : Λ.t'.G.left ⟶ Gx x := (lift a0 b0).left
    have qf : q ≫ (fst (Over.mk x) A).left = Λ.t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
    have qs : q ≫ (snd (Over.mk x) A).left = Λ.m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
    have hq : n.φ ≫ q = g := by
      apply pullback.hom_ext
      · rw [Category.assoc]
        show n.φ ≫ q ≫ (fst (Over.mk x) A).left = g ≫ (fst (Over.mk x) A).left
        rw [qf, hf]
        exact n.cart.1.w.trans (Category.comp_id _)
      · rw [Category.assoc]
        show n.φ ≫ q ≫ (snd (Over.mk x) A).left = g ≫ (snd (Over.mk x) A).left
        rw [qs, hs, e₁]
    have le : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ q ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit) := fun z hz =>
      Set.mem_iInter.2 fun _ => (congrArg (fun p => p z ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) qs).mpr (mem_pull.1 hz)
    obtain ⟨i, hi⟩ := exists_chart hL (n.φ y)
    obtain ⟨k, hk⟩ := exists_chart hL' y
    have hm : Λ.m1.φ (n.φ y) ∈ Xo.univ.t.PP.L.U (j PUnit.unit) :=
      (congrArg (fun p => p y ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) e₁).mp (mem_pull.1 hy)
    have hz : (𝟙 _ ≫ n.φ) y ∈ (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ⊓ Λ.t'.PP.L.U i := ⟨mem_pull.2 hm, hi⟩
    have a := congrArg (gs (𝟙 _ ≫ n.φ) y _) (i1 j i)
    have a' : gs (𝟙 _ ≫ n.φ) y _ (s1.f j) =
        (gw w1 (𝟙 _ ≫ n.φ) y (j PUnit.unit) i).val * gs (𝟙 _ ≫ n.φ) y _ (σ.f i) :=
      (gs_res _ y _ hz _).symm.trans (a.trans ((gs_mul _ y _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ y _ hz _) (gs_res _ y _ hz _))))
    have b := hσ' _ (𝟙 _) y i k hi hk
    have t := T1 _ (𝟙 _) y (j PUnit.unit) i k (mem_pull.1 hy) hi hk
    have d : gs (𝟙 _ ≫ n.φ) y _ (s1.f j) = gs (𝟙 _ ≫ g) y _ (s.f (fun _ => j PUnit.unit)) :=
      (congrArg (gs (𝟙 _ ≫ n.φ) y _) (c1 q qs qf j le)).trans ((gs_appLE q _ _ le _ y hz.1 _).trans
        (congrArg (fun p => gs p y _ (s.f (fun _ => j PUnit.unit))) (by rw [Category.assoc, hq])))
    refine (hs1 _ (𝟙 _) y j k hy hk).trans (Eq.trans ?_ (a'.symm.trans (d.trans (gs_appLE g _ _ hj (𝟙 _) y hy _).symm)))
    rw [t, Units.val_mul, _root_.mul_assoc]
    exact congrArg _ b.symm

theorem lift_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ Λ' : M.Lift f x, (∀ cv w, Λ.Vec cv w → Λ'.Vec cv w) ∧ ∀ s, Λ.ThTie s → Λ'.ThTie s := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ Λ'
  exact ⟨vec Λ Λ', thTie Λ Λ'⟩

end GlobalTheory.Reg.LiftUnique
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndepStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelChartLift_coords_generator_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ Λ' : M.Lift f x, (∀ cv w, Λ.Vec cv w → Λ'.Vec cv w) ∧ ∀ s, Λ.ThTie s → Λ'.ThTie s := by
  first | exact @GlobalTheory.Reg.LiftUnique.lift_indep | exact GlobalTheory.Reg.LiftUnique.lift_indep | (intros; apply GlobalTheory.Reg.LiftUnique.lift_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralGeneratorOfChartPointCdvr
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.SecGeneratesOfNeZeroOnClosedFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory
namespace SecLineGen

theorem constFn_mul' {V : Type} [CommRing V] {X : Scheme.{0}} (π : X ⟶ Sp V) (U : X.Opens)
    (a b : V) : constFn π U (a * b) = constFn π U a * constFn π U b := by
  first
  | exact map_mul _ a b
  | (unfold constFn; exact map_mul _ a b)
  | (simp only [constFn, map_mul])
  | (unfold constFn; simp)
  | (unfold constFn Sp; done)

theorem apply_mem_basicOpen_of_mem {V : Type} [CommRing V] {X : Scheme.{0}} (π : X ⟶ Sp V)
    (U : X.Opens) (a : V) (g : X) (hg : g ∈ X.basicOpen (constFn π U a)) :
    π g ∈ PrimeSpectrum.basicOpen a := by
  unfold constFn at hg
  have h0 := Scheme.basicOpen_appLE π U ⊤ (fun _ _ => trivial)
    ((Scheme.ΓSpecIso (CommRingCat.of V)).inv a)
  have hg' : g ∈ U ⊓ π ⁻¹ᵁ ((Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv a)) := by
    rw [← h0]
    exact hg
  have h2 : π g ∈ (Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv a) := hg'.2
  have h3 := AlgebraicGeometry.basicOpen_eq_of_affine (R := CommRingCat.of V) a
  first
  | (rw [h3] at h2; exact h2)
  | (unfold Sp at h2; rw [h3] at h2; exact h2)
  | exact h3 ▸ h2
  | (unfold Sp at h2; done)

end SecLineGen


open SecLineGen in
theorem sec_generates_of_ne_zero_on_closed_fibre :
    ∀ (V : Type) [CommRing V] [IsLocalRing V] (X : Scheme.{0}) (π : X ⟶ Sp V) (L : LB X) (θ θ' : LB.Sec L), (∀ σ : LB.Sec L, ∃! a : V, ∀ i, σ.f i = constFn π _ a * θ.f i) → (∃ (g : X) (i : L.ι), π g = IsLocalRing.closedPoint V ∧ g ∈ X.basicOpen (θ'.f i)) → (∃ u : Vˣ, ∀ i, θ'.f i = constFn π _ (u : V) * θ.f i) ∧ ∀ σ : LB.Sec L, ∃! a : V, ∀ i, σ.f i = constFn π _ a * θ'.f i := by
  intro V _ _ X π L θ θ' hθ hpt
  obtain ⟨g, i, hgc, hgi⟩ := hpt
  obtain ⟨a, ha, -⟩ := hθ θ'

  have hmem : g ∈ X.basicOpen (constFn π (L.U i) a) := by
    have h := hgi
    rw [ha i, Scheme.basicOpen_mul] at h
    exact h.1

  have hu : IsUnit a := by
    by_contra hna
    have h1 := SecLineGen.apply_mem_basicOpen_of_mem π _ a g hmem
    rw [hgc] at h1
    have h2 : a ∉ (IsLocalRing.closedPoint V).asIdeal := (PrimeSpectrum.mem_basicOpen _ _).1 h1
    have hmax : a ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal a).2 hna
    first | exact h2 hmax | exact h2 (by simpa using hmax)
  obtain ⟨u, rfl⟩ := hu
  refine ⟨⟨u, fun j => ha j⟩, ?_⟩
  intro σ
  obtain ⟨b, hb, hbu⟩ := hθ σ
  refine ⟨b * ↑u⁻¹, ?_, ?_⟩
  · intro j
    rw [hb j, ha j, ← _root_.mul_assoc, ← SecLineGen.constFn_mul', _root_.mul_assoc b, Units.inv_mul, _root_.mul_one]
  · intro c hc
    have key : c * ↑u = b := hbu (c * ↑u) (fun j => by
      rw [hc j, ha j, ← _root_.mul_assoc, ← SecLineGen.constFn_mul'])
    rw [← key, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralGeneratorOfChartPointCdvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.TieIntegral

theorem isRigIso_iff {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F)) :
    IsRigIso m L' L w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig m.e :=
  and_congr (isGen_iff w)
    (maps_iff w _ (fun _ => eSec G) _ L'.rig L.rig m.e _ (rigPull_le m.F m.e m.e_comm L.L) (fun _ => rfl))

theorem exists_rigIso_cancel {S S' S'' : Scheme.{0}} {G'' : Over S''} {G' : Over S'} {G : Over S} [GrpObj G'']
    [IsCommMonObj G''] [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (m : CubeMap G' G)
    (m' : CubeMap G'' G') (n : CubeMap G'' G) (hF : n.F = m'.F ≫ m.F) (he : n.e = m'.e ≫ m.e)
    (L'' : RigLB G'') (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F))
    (w'' : LB.Iso L''.L (L.L.pull n.F)) (hw : IsRigIso m L' L w) (hw'' : IsRigIso n L'' L w'') :
    ∃ w' : LB.Iso L''.L (L'.L.pull m'.F), IsRigIso m' L'' L' w' ∧
      ∀ (Y : Scheme.{0}) (f : Y ⟶ G''.left) (y : Y) (j : L.L.ι) (i : L'.L.ι) (k : L''.L.ι),
        m.F (m'.F (f y)) ∈ L.L.U j → m'.F (f y) ∈ L'.L.U i → f y ∈ L''.L.U k →
        gw w'' f y j k = gw w (f ≫ m'.F) y j i * gw w' f y i k := by
  obtain ⟨Fn, F3, e, hec, hp⟩ := n
  dsimp only at hF he
  subst hF he
  rw [isRigIso_iff] at hw hw''
  obtain ⟨g, r⟩ := hw
  obtain ⟨g'', r''⟩ := hw''
  obtain ⟨w', T⟩ := exists_cancel L.isLB w w'' g g'' L'.isLB L''.isLB
  exact ⟨w', (isRigIso_iff _ _ _ _).2 ⟨T.pgen_cancel L.isLB g g'',
    T.pmaps_cancel L.isLB (fun _ => m'.e_comm) r r''⟩, T⟩

theorem gs_of_formula {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (U : X.Opens) (θ : ∀ i, Γ(X, U ⊓ L.U i)) (σ : LB.Sec L')
    (h : ∀ (j : L.ι) (k : L'.ι) (W : X'.Opens) (h₁ : W ≤ F ⁻¹ᵁ (U ⊓ L.U j))
      (h₂ : W ≤ (L.pull F).U (fun _ => j) ⊓ L'.U k),
      (F.appLE _ _ h₁).hom (θ j) = resG _ h₂ (w.s (fun _ => j, k)).val * resG _ (h₂.trans inf_le_right) (σ.f k))
    {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) (hU : F (r z) ∈ U) (hj : F (r z) ∈ L.U j)
    (hk : r z ∈ L'.U k) :
    gs (r ≫ F) z _ (θ j) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  let W : X'.Opens := F ⁻¹ᵁ (U ⊓ L.U j) ⊓ L'.U k
  have h₁ : W ≤ F ⁻¹ᵁ (U ⊓ L.U j) := inf_le_left
  have h₂ : W ≤ (L.pull F).U (fun _ => j) ⊓ L'.U k := fun y hy => ⟨mem_pull.2 hy.1.2, hy.2⟩
  have hz : r z ∈ W := ⟨⟨hU, hj⟩, hk⟩
  have e := congrArg (gs r z W) (h j k W h₁ h₂)
  refine (gs_appLE F _ _ h₁ r z hz _).symm.trans (e.trans ((gs_mul r z _ hz _ _).trans ?_))
  exact congrArg₂ (· * ·) ((gs_res r z h₂ hz _).trans (gs_unit r z _ (h₂ hz) _)) (gs_res r z _ hz _)

end GlobalTheory.Reg.TieIntegral

namespace GlobalTheory.Reg


open TieIntegral in
theorem exists_generator_of_thTie :
    ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V), letI := io.toAlgebra; ∀ (x : Sp T.Fr ⟶ Xo.X) (s : LB.Sec (PPx x)) (Λ : M.Lift ((algebraMap T.V T.Fr).comp f₀) x), Λ.ThTie s → ∀ (G : SAB H (Sp T.V)) (m : SABMap G Y.t (spMap f₀ ≫ M.hU.fromSpec)) (m2 : SABMap Λ.t' G (spMap (algebraMap T.V T.Fr))), m2.φ ≫ m.φ = Λ.m2.φ → ∃ θ : LB.Sec G.PP.L, (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left (le_top : G.PP.L.U i ≤ ⊤) ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧ ∃ (w1 : LB.Iso Λ.t'.PP.L (Xo.univ.t.PP.L.pull Λ.m1.φ)) (w2 : LB.Iso Λ.t'.PP.L (G.PP.L.pull m2.φ)) (σ : LB.Sec Λ.t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull Λ.m1.φ)) (θ2 : LB.Sec (G.PP.L.pull m2.φ)), RigIso Λ.m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧ ∀ g : Λ.t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = Λ.m1.φ → g ≫ (fst (Over.mk x) Xo.univ.t.G).left = Λ.t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit)) := by
  intro hT E _ _ _ H Dw l Xo c O _ β Y M hPI T io f₀
  let _ := io.toAlgebra
  intro x s Λ hTie G m m2 hφ
  obtain ⟨w1, wΛ, σ, s1, r1, rΛ, hI1, hform, hg⟩ := hTie
  have hcomp : spMap ((algebraMap T.V T.Fr).comp f₀) = spMap (algebraMap T.V T.Fr) ≫ spMap f₀ := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hz : Λ.xF ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ (spMap f₀ ≫ M.hU.fromSpec) := by
    rw [Λ.xF_j, hcomp]; exact Category.assoc _ _ _
  obtain ⟨θ₀, hθ₀, -⟩ := thetaCore_of hT E H Dw l Xo c O β Y hPI T.V _ Λ.xF hz G m Λ.t' m2
  have hU : ⊤ ≤ (spMap f₀ ≫ M.hU.fromSpec) ⁻¹ᵁ M.U := fun y _ => by
    have : M.hU.fromSpec (spMap f₀ y) ∈ Set.range M.hU.fromSpec := ⟨_, rfl⟩
    rw [M.hU.range_fromSpec] at this
    exact this
  obtain ⟨w, θ, rw', hθ, hne⟩ := exists_sec_pull_nonzero_on_fibres E H _ _ Y.t G _ m M.U hU M.θ M.θ_mem M.θ_ne
  have hgen := (sec_generates_of_ne_zero_on_closed_fibre T.V _ G.G.hom G.PP.L θ₀ θ hθ₀ (hne _)).2
  have he : Λ.m2.cm.e = m2.cm.e ≫ m.cm.e := by
    rw [Λ.m2.base, m2.base, m.base, hcomp]; exact Category.assoc _ _ _
  obtain ⟨w2, r2, tri⟩ := exists_rigIso_cancel m.cm m2.cm Λ.m2.cm hφ.symm he Λ.t'.PP G.PP Y.t.PP w wΛ rw' rΛ
  refine ⟨θ, hgen, w1, w2, σ, s1, thfPull G.PP.L m2.φ θ, r1, r2, hI1,
    fun (i : PUnit → G.PP.L.ι) k => fn_ext fun y hy => ?_, fun j hj => rfl, hg⟩
  have hi : m2.φ y ∈ G.PP.L.U (i PUnit.unit) := mem_pull.1 hy.1
  obtain ⟨j, hj⟩ := exists_chart Y.t.PP.isLB (m.φ (m2.φ y))
  have hyU : m.φ (m2.φ y) ∈ Y.t.G.hom ⁻¹ᵁ M.U := (congrArg (fun q => q (m2.φ y) ∈ M.U) m.cart.1.w).mpr
    (hU (show G.G.hom (m2.φ y) ∈ (⊤ : (Sp T.V).Opens) from trivial))
  have pt : Λ.m2.φ y = m.φ (m2.φ y) := congrArg (fun q => q y) hφ.symm
  have e1 := gs_of_formula w _ M.θ θ hθ (𝟙 _ ≫ m2.φ) y j (i PUnit.unit) hyU hj hi
  have e2 := gs_of_formula wΛ _ M.θ σ hform (𝟙 _) y j k (pt ▸ hyU) (pt ▸ hj) hy.2
  have e3 := tri _ (𝟙 _) y j (i PUnit.unit) k hj hi hy.2
  have e4 : (𝟙 _ ≫ m2.φ) ≫ m.φ = 𝟙 _ ≫ Λ.m2.φ := by rw [Category.assoc, hφ]
  rw [e4, e2, e3, Units.val_mul, _root_.mul_assoc, Units.mul_right_inj] at e1
  refine (gs_res _ y _ hy _).trans ((gs_appLE m2.φ _ _ _ (𝟙 _) y hy.1 _).trans (e1.symm.trans ?_))
  refine Eq.symm ((gs_mul _ y _ hy _ _).trans ?_)
  exact congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _)

end GlobalTheory.Reg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralGeneratorOfChartPointCdvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralGenerator_of_chartPoint_cdvr : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V), letI := io.toAlgebra; ∀ (x : Sp T.Fr ⟶ Xo.X) (s : LB.Sec (PPx x)) (Λ : M.Lift ((algebraMap T.V T.Fr).comp f₀) x), Λ.ThTie s → ∀ (G : SAB H (Sp T.V)) (m : SABMap G Y.t (spMap f₀ ≫ M.hU.fromSpec)) (m2 : SABMap Λ.t' G (spMap (algebraMap T.V T.Fr))), m2.φ ≫ m.φ = Λ.m2.φ → ∃ θ : LB.Sec G.PP.L, (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left (le_top : G.PP.L.U i ≤ ⊤) ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧ ∃ (w1 : LB.Iso Λ.t'.PP.L (Xo.univ.t.PP.L.pull Λ.m1.φ)) (w2 : LB.Iso Λ.t'.PP.L (G.PP.L.pull m2.φ)) (σ : LB.Sec Λ.t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull Λ.m1.φ)) (θ2 : LB.Sec (G.PP.L.pull m2.φ)), RigIso Λ.m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧ ∀ g : Λ.t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = Λ.m1.φ → g ≫ (fst (Over.mk x) Xo.univ.t.G).left = Λ.t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit)) := by
  first | exact @GlobalTheory.Reg.exists_generator_of_thTie | exact GlobalTheory.Reg.exists_generator_of_thTie | (intros; apply GlobalTheory.Reg.exists_generator_of_thTie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.LiftBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.LiftBaseChange
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.LiftBaseChange

section Bundles

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'} {F'' : X'' ⟶ X}

def IsCompIso (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (w'' : LB.Iso L'' (L.pull F'')) : Prop :=
  ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (j : L.ι) (i : L'.ι) (k : L''.ι), F (F' (f y)) ∈ L.U j → F' (f y) ∈ L'.U i →
    f y ∈ L''.U k → gw w'' f y j k = gw w (f ≫ F') y j i * gw w' f y i k

theorem tie_comp (hL' : L'.IsLB) (e : F'' = F' ≫ F) {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')}
    {w'' : LB.Iso L'' (L.pull F'')} (T : IsCompIso w w' w'') (V : X.Opens) (θ : ∀ j, Γ(X, V ⊓ L.U j))
    (σ : LB.Sec L') (σ' : LB.Sec L'')
    (hσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ X'') (z : Z) j k, F' (r z) ∈ L'.U j → r z ∈ L''.U k →
      gs (r ≫ F') z _ (σ.f j) = (gw w' r z j k).val * gs r z _ (σ'.f k))
    (h : ∀ (j : L.ι) (k : L'.ι) (W : X'.Opens) (h₁ : W ≤ F ⁻¹ᵁ (V ⊓ L.U j))
      (h₂ : W ≤ (L.pull F).U (fun _ => j) ⊓ L'.U k),
      (F.appLE _ _ h₁).hom (θ j) = resG _ h₂ (w.s (fun _ => j, k)).val * resG _ (h₂.trans inf_le_right) (σ.f k))
    (j : L.ι) (k : L''.ι) (W : X''.Opens) (h₁ : W ≤ F'' ⁻¹ᵁ (V ⊓ L.U j))
    (h₂ : W ≤ (L.pull F'').U (fun _ => j) ⊓ L''.U k) :
    (F''.appLE _ _ h₁).hom (θ j) = resG _ h₂ (w''.s (fun _ => j, k)).val * resG _ (h₂.trans inf_le_right) (σ'.f k) := by
  subst e
  refine fn_ext fun y hy => ?_
  obtain ⟨i, hi⟩ := exists_chart hL' (F' y)
  have hj : F (F' y) ∈ V ⊓ L.U j := h₁ hy
  have hk : y ∈ L''.U k := (h₂ hy).2
  let W₀ : X'.Opens := F ⁻¹ᵁ (V ⊓ L.U j) ⊓ ((L.pull F).U (fun _ => j) ⊓ L'.U i)
  have hW : (𝟙 X'' ≫ F') y ∈ W₀ := ⟨hj, mem_pull.2 hj.2, hi⟩
  have e₀ := congrArg (gs (𝟙 X'' ≫ F') y W₀) (h j i W₀ inf_le_left inf_le_right)
  have e₁ : gs ((𝟙 X'' ≫ F') ≫ F) y _ (θ j) = (gw w (𝟙 X'' ≫ F') y j i).val * gs (𝟙 X'' ≫ F') y _ (σ.f i) :=
    (gs_appLE F _ _ _ _ y hW _).symm.trans (e₀.trans ((gs_mul _ y _ hW _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hW _).trans (gs_unit _ y _ hW.2 _)) (gs_res _ y _ hW _))))
  have e₂ := hσ _ (𝟙 X'') y i k hi hk
  have e₃ := T _ (𝟙 X'') y j i k hj.2 hi hk
  refine (gs_appLE _ _ _ h₁ (𝟙 _) y hy _).trans (Eq.trans ?_ (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y h₂ hy _).trans (gs_unit _ y _ (h₂ hy) _)) (gs_res _ y _ hy _)))))
  rw [← Category.assoc, e₁, e₂, ← _root_.mul_assoc, ← Units.val_mul, ← e₃]
  rfl

theorem isoMaps_comp (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB) (e : F'' = F' ≫ F) {w : LB.Iso L' (L.pull F)}
    {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull F'')} (T : IsCompIso w w' w'') (g : w''.IsGen)
    (σ : LB.Sec L') (σ' : LB.Sec L'')
    (hσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ X'') (z : Z) j k, F' (r z) ∈ L'.U j → r z ∈ L''.U k →
      gs (r ≫ F') z _ (σ.f j) = (gw w' r z j k).val * gs r z _ (σ'.f k))
    (s : LB.Sec (L.pull F)) (hs : IsoMaps w σ s) :
    ∃ s' : LB.Sec (L.pull F''), IsoMaps w'' σ' s' ∧ ∀ (J : PUnit → L.ι) (y : X''), y ∈ (L.pull F'').U J →
      gs (𝟙 X'') y _ (s'.f J) = gs (𝟙 X'' ≫ F') y _ (s.f J) := by
  subst e
  obtain ⟨s', hs'⟩ := thf_secUp ((isGen_iff w'').1 g) hL hL'' σ'
  refine ⟨s', fun (i : PUnit → L.ι) k => fn_ext fun y hy => ?_, fun J y hy => ?_⟩
  · exact (gs_res _ y _ hy _).trans ((hs' _ (𝟙 _) y i k hy.1 hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _)))))
  · obtain ⟨i, hi⟩ := exists_chart hL' (F' y)
    obtain ⟨k, hk⟩ := exists_chart hL'' y
    have hj : F (F' y) ∈ L.U (J PUnit.unit) := mem_pull₂.1 hy
    have hW : (𝟙 X'' ≫ F') y ∈ (L.pull F).U J ⊓ L'.U i := ⟨mem_pull.2 hj, hi⟩
    have e₀ := congrArg (gs (𝟙 X'' ≫ F') y _) (hs J i)
    have e₁ : gs (𝟙 X'' ≫ F') y _ (s.f J) =
        (gw w (𝟙 X'' ≫ F') y (J PUnit.unit) i).val * gs (𝟙 X'' ≫ F') y _ (σ.f i) :=
      (gs_res _ y _ hW _).symm.trans (e₀.trans ((gs_mul _ y _ hW _ _).trans (congrArg₂ (· * ·)
        (gs_unit _ y _ hW _) (gs_res _ y _ hW _))))
    rw [e₁, hσ _ (𝟙 X'') y i k hi hk, ← _root_.mul_assoc, ← Units.val_mul, ← T _ (𝟙 X'') y _ i k hj hi hk]
    exact hs' _ (𝟙 _) y J k hy hk

end Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rigIso_iff {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) :
    RigIso m w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec t'.G) (fun _ => eSec t.G) (fun _ => 1) t'.PP.rig t.PP.rig m.cm.e :=
  and_congr (isGen_iff w)
    (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig m.cm.e _ (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L)
      (fun _ => rfl))

theorem rigIso_comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (m : SABMap t' t f) (m' : SABMap t'' t' g) (n : SABMap t'' t h) (eh : h = g ≫ f)
    (eφ : n.φ = m'.φ ≫ m.φ) {w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} {w' : LB.Iso t''.PP.L (t'.PP.L.pull m'.φ)}
    (hw : RigIso m w) (hw' : RigIso m' w') :
    ∃ w'' : LB.Iso t''.PP.L (t.PP.L.pull n.φ), RigIso n w'' ∧ IsCompIso w w' w'' := by
  have ee : n.cm.e = m'.cm.e ≫ m.cm.e := by rw [n.base, m'.base, m.base, eh]
  simp only [rigIso_iff] at hw hw' ⊢
  obtain ⟨⟨F, F3, e, he, hp⟩, c, b, a, li⟩ := n
  dsimp only [SABMap.φ] at ee eφ
  subst ee eφ
  obtain ⟨w'', T⟩ := exists_comp t'.PP.isLB w w' hw.1 hw'.1 t.PP.isLB t''.PP.isLB
  exact ⟨w'', ⟨T.pgen_comp t'.PP.isLB hw.1 hw'.1, T.pmaps_comp t'.PP.isLB (fun _ => m'.cm.e_comm) hw.2 hw'.2⟩, T⟩

theorem exists_comp' {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    (m : SABMap t' t f) (m' : SABMap t'' t' g) (h : S'' ⟶ S) (eh : h = g ≫ f) :
    ∃ n : SABMap t'' t h, n.φ = m'.φ ≫ m.φ := by
  subst eh
  exact sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m'

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMapR_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Chart.dualMapR (g.comp f) = (Chart.dualMapR g).comp (Chart.dualMapR f) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [Chart.dualMapR]

theorem exists_vec_lift {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) {G : Over (Sp R)} {G' : Over (Sp S)}
    {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom (spMap ψ)) (v : epsR R ⟶ G) :
    ∃ v' : epsR S ⟶ G', v'.left ≫ φ = spMap (Chart.dualMapR ψ) ≫ v.left := by
  have w : (spMap (Chart.dualMapR ψ) ≫ v.left) ≫ G.hom = (epsR S).hom ≫ spMap ψ := by
    rw [Category.assoc, Over.w v]
    exact LieCombBaseChange.dualMap_over ψ
  exact ⟨Over.homMk (h.lift _ _ w) (h.lift_snd _ _ w), h.lift_fst _ _ w⟩

end GlobalTheory.LiftBaseChange

namespace GlobalTheory

open LiftBaseChange


set_option maxHeartbeats 1000000 in
theorem lift_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (S : Type) [CommRing S] [Algebra c.F S] (ψ : R →ₐ[c.F] S), ∃ Λ' : M.Lift (ψ.toRingHom.comp f) (spMap ψ.toRingHom ≫ x), (∀ cv w, Λ.Vec cv w → Λ'.Vec (fun j => ψ (cv j)) (spMap (dualMap ψ.toRingHom) ≫ w)) ∧ ∀ (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx (spMap ψ.toRingHom ≫ x))) (pm : Gx (spMap ψ.toRingHom ≫ x) ⟶ Gx x), pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left → pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left ≫ spMap ψ.toRingHom → (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx (spMap ψ.toRingHom ≫ x)).U i ≤ pm ⁻¹ᵁ (PPx x).U i), (pm.appLE _ _ h).hom (s.f i) = s'.f i) → Λ.ThTie s → Λ'.ThTie s' := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ S _ _ ψ
  obtain ⟨t'', p⟩ : ∃ t'' : SAB H (Sp S), Nonempty (SABMap t'' Λ.t' (spMap ψ.toRingHom)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap ψ.toRingHom) Λ.t'
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨p⟩ := p
  have e2 : spMap (ψ.toRingHom.comp f) ≫ M.hU.fromSpec = spMap ψ.toRingHom ≫ spMap f ≫ M.hU.fromSpec := by
    rw [spMap_comp', Category.assoc]
  obtain ⟨n', hn'⟩ := exists_comp' Λ.m' p _ rfl
  obtain ⟨n1, hn1⟩ := exists_comp' Λ.m1 p _ rfl
  obtain ⟨n2, hn2⟩ := exists_comp' Λ.m2 p _ e2
  refine ⟨⟨spMap ψ.toRingHom ≫ Λ.xF, by rw [Category.assoc, Λ.xF_fst], ?_, by rw [Category.assoc, Λ.xF_j, e2],
    t'', n', n1, n2, by rw [hn1, hn', Λ.liftedChartMap_eq, Category.assoc], by rw [hn2, hn', Λ.matrix_two_by_two_congr, Category.assoc]⟩, ?_, ?_⟩
  · rw [Category.assoc, Λ.xF_snd, ← spMap_comp']
    exact congrArg spMap ψ.comp_algebraMap
  · rintro cv w ⟨v, u, hv, hc, hu⟩
    choose v' hv' using fun j => exists_vec_lift ψ.toRingHom p.cart.1 (v j)
    obtain ⟨u', hu'⟩ := exists_vec_lift ψ.toRingHom p.cart.1 u
    refine ⟨v', u', fun j => ?_, (lieComb_baseChange R S ψ.toRingHom _ _ _ p.cart _ v u cv v' u' hv' hc).1 hu', ?_⟩
    · show (v' j).left ≫ n2.φ = _
      rw [hn2, ← Category.assoc, dualMapR_comp, spMap_comp', Category.assoc (spMap _), ← hv j]
      exact (congrArg (· ≫ Λ.m2.φ) (hv' j)).trans (Category.assoc _ _ _)
    · show u'.left ≫ n1.φ = _
      rw [hn1, ← Category.assoc, ← hu]
      exact (congrArg (· ≫ Λ.m1.φ) hu').trans (Category.assoc _ _ _)
  · rintro s s' pm hp₁ hp₂ hps ⟨w1, w2, σ, s1, r1, r2, hI, hθ, hg⟩
    obtain ⟨w0, g0, r0, -⟩ := p.lin
    have R0 : RigIso p w0 := ⟨g0, r0⟩
    obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w0).1 g0) Λ.t'.PP.isLB t''.PP.isLB σ
    obtain ⟨w1', r1', T1⟩ := rigIso_comp Λ.m1 p n1 rfl hn1 r1 R0
    obtain ⟨w2', r2', T2⟩ := rigIso_comp Λ.m2 p n2 e2 hn2 r2 R0
    obtain ⟨s1', hI', hs1'⟩ := isoMaps_comp Xo.univ.t.PP.isLB Λ.t'.PP.isLB t''.PP.isLB hn1 T1 r1'.1 σ σ' hσ' s1 hI
    refine ⟨w1', w2', σ', s1', r1', r2', hI', tie_comp Λ.t'.PP.isLB hn2 T2 _ M.θ σ σ' hσ' hθ, ?_⟩
    intro g' e₁ e₂ (j : PUnit → Xo.univ.t.PP.L.ι) hj
    have e₁' : g' ≫ (snd (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left = n1.φ := e₁
    have e₂' : g' ≫ (fst (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left = t''.G.hom := e₂
    let A := Xo.univ.t.G
    let a0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk Λ.t'.G.hom rfl
    let b0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ A := Over.homMk Λ.m1.φ Λ.m1.cart.1.w
    let g : Λ.t'.G.left ⟶ Gx x := (lift a0 b0).left
    have gf : g ≫ (fst (Over.mk x) A).left = Λ.t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
    have gs' : g ≫ (snd (Over.mk x) A).left = Λ.m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
    have sq : p.φ ≫ g = g' ≫ pm := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc]
        show p.φ ≫ g ≫ (fst (Over.mk x) A).left = g' ≫ pm ≫ (fst (Over.mk x) A).left
        rw [gf, hp₂, ← Category.assoc, e₂']
        exact p.cart.1.w
      · rw [Category.assoc, Category.assoc]
        show p.φ ≫ g ≫ (snd (Over.mk x) A).left = g' ≫ pm ≫ (snd (Over.mk x) A).left
        rw [gs', hp₁, e₁', hn1]
    have le₁ : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit) := fun y hy =>
      Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) gs').mpr (mem_pull.1 hy)
    have le₂ : (PPx (spMap ψ.toRingHom ≫ x)).U (fun _ => j PUnit.unit) ≤ pm ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit) :=
      fun y hy => Set.mem_iInter.2 fun _ =>
        (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) hp₁).mpr (Set.mem_iInter.1 hy 0)
    refine fn_ext fun y hy => ?_
    have hy₁ : (𝟙 _ ≫ p.φ) y ∈ (Xo.univ.t.PP.L.pull Λ.m1.φ).U j :=
      mem_pull.2 ((congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) hn1).mp (mem_pull.1 hy))
    have c₁ : (𝟙 _ ≫ p.φ) ≫ g = (𝟙 _ ≫ g') ≫ pm := by rw [Category.id_comp, Category.id_comp, sq]
    refine (hs1' j y hy).trans ((congrArg (gs (𝟙 _ ≫ p.φ) y _) (hg g gs' gf j le₁)).trans
      ((gs_appLE g _ _ le₁ _ y hy₁ _).trans ((congrArg (fun q => gs q y _ (s.f (fun _ => j PUnit.unit))) c₁).trans ?_)))
    exact (gs_appLE pm _ _ le₂ (𝟙 _ ≫ g') y (hj hy) _).symm.trans
      ((congrArg (gs (𝟙 _ ≫ g') y _) (hps _ le₂)).trans (gs_appLE g' _ _ hj (𝟙 _) y hy _).symm)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.LiftBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_baseChange_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (S : Type) [CommRing S] [Algebra c.F S] (ψ : R →ₐ[c.F] S), ∃ Λ' : M.Lift (ψ.toRingHom.comp f) (spMap ψ.toRingHom ≫ x), (∀ cv w, Λ.Vec cv w → Λ'.Vec (fun j => ψ (cv j)) (spMap (dualMap ψ.toRingHom) ≫ w)) ∧ ∀ (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx (spMap ψ.toRingHom ≫ x))) (pm : Gx (spMap ψ.toRingHom ≫ x) ⟶ Gx x), pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left → pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left ≫ spMap ψ.toRingHom → (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx (spMap ψ.toRingHom ≫ x)).U i ≤ pm ⁻¹ᵁ (PPx x).U i), (pm.appLE _ _ h).hom (s.f i) = s'.f i) → Λ.ThTie s → Λ'.ThTie s' := by
  first | exact @GlobalTheory.lift_baseChange | exact GlobalTheory.lift_baseChange | (intros; apply GlobalTheory.lift_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NoCommonZeroOfFiniteValues
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NoCommonZeroOfFiniteValues
set_option synthInstance.maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_valuationSubring_hom_of_overLa {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) (T : CDVR) (io : K →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e) :
    ∃ b : (la.valuation K).valuationSubring →+* T.V,
      (algebraMap T.V T.Fr).comp b = io.comp (la.valuation K).valuationSubring.subtype := by
  have hmem : ∀ a : (la.valuation K).valuationSubring, io a ∈ (algebraMap T.V T.Fr).range := by
    intro a
    apply Formalism.L2.PjFree.mem_range_of_vV_nonneg
    rw [ho.2]
    refine mul_nonneg (by positivity) ?_
    by_cases ha : (a : K) = 0
    · simp [vLa, ha]
    · have hv : la.valuation K (a : K) ≤ 1 := a.2
      have hn : la.valuation K (a : K) ≠ 0 := (la.valuation K).ne_zero_iff.2 ha
      have := (WithZero.log_le_log hn one_ne_zero).2 hv
      simp only [WithZero.log_one] at this
      simp only [vLa]; omega
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  let eq : T.V ≃+* (algebraMap T.V T.Fr).range :=
    RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
      ⟨fun x y h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  refine ⟨eq.symm.toRingHom.comp
    ((io.comp (la.valuation K).valuationSubring.subtype).codRestrict _ hmem), ?_⟩
  ext a
  exact congrArg Subtype.val (eq.apply_symm_apply ⟨io a, hmem a⟩)

theorem noCommonZero_of_finite_values : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ la : HeightOneSpectrum (𝓞 c.F), ModelAt Xo c la → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → (∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la, ∃ i, v (ws i) ≠ ⊤) → Formalism.L2.PjFree.NoCommonZero Xo c ws := by
  intro hST E _ _ _ H Dw l Xo c hL la hM a n m ws hws hv k _ _ _ y
  by_contra hcon
  push Not at hcon
  obtain ⟨p, φ, y', hy'⟩ := hL.test k y
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  have hker : ∀ i, evR Xo c (ws i) y' ∈ RingHom.ker φ.toRingHom := by
    intro i
    have := GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n (ws i) (hws i) p.R k φ y' y hy'
    rw [hcon i] at this
    exact this.symm
  obtain ⟨M, hMmax, hle⟩ := Ideal.exists_le_maximal _ (RingHom.ker_ne_top φ.toRingHom)
  let _ : Field (p.R ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite c.F (p.R ⧸ M) := finite_of_finite_type_of_isJacobsonRing c.F (p.R ⧸ M)
  have : NumberField (p.R ⧸ M) := NumberField.of_module_finite c.F (p.R ⧸ M)
  obtain ⟨T, κ, e, ho, hfin⟩ := GlobalTheory.locFld c.F (p.R ⧸ M) (algebraMap c.F (p.R ⧸ M)) la
  set io : c.F →+* T.Fr := κ.comp (algebraMap c.F (p.R ⧸ M)) with hio
  let _ : Algebra c.F T.Fr := io.toAlgebra
  let ψ : p.R →ₐ[c.F] T.Fr := { κ.comp (Ideal.Quotient.mk M) with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := hL.bc p.R T.Fr ψ y'
  have hz0 : ∀ i, evR Xo c (ws i) z = 0 := by
    intro i
    rw [GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n (ws i) (hws i) p.R T.Fr ψ y' z hz]
    show κ (Ideal.Quotient.mk M _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (hle (hker i)), map_zero]
  obtain ⟨Y, hPI⟩ := hM
  obtain ⟨b, hb⟩ := exists_valuationSubring_hom_of_overLa la T io e ho
  have hIF : IntFramesSt Xo c :=
    intFrames Xo c Out.CubePf.cubePull (lieFree Xo c) (thetaFrame_of Xo c hST) (fun S _ _ y => hL.test S y)
  obtain ⟨w, t, hw⟩ := intFr_of_model hIF T io Y hPI b hb z
  obtain ⟨i, hi⟩ := hv _ ⟨PtV.mk la ho w hfin () trivial, rfl⟩
  apply hi
  show nval T.V e (evI w (ws i)) = ⊤
  have h0 : evI w (ws i) = 0 := by
    have := hL.wt a n (ws i) (hws i) T.Fr t z w.1 ⟨p, ψ, y', hz⟩ w.2.1 hw
    rw [hz0 i, mul_zero] at this
    exact this
  rw [h0, nval_zero]

end GlobalTheory.Reg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NoCommonZeroOfFiniteValuesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noCommonZero_of_exists_finite_value : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ la : HeightOneSpectrum (𝓞 c.F), ModelAt Xo c la → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → (∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la, ∃ i, v (ws i) ≠ ⊤) → Formalism.L2.PjFree.NoCommonZero Xo c ws := by
  first | exact @GlobalTheory.Reg.noCommonZero_of_finite_values | exact GlobalTheory.Reg.noCommonZero_of_finite_values | (intros; apply GlobalTheory.Reg.noCommonZero_of_finite_values <;> assumption)
end
end
