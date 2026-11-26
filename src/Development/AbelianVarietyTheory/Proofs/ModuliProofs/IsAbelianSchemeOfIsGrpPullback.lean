module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PolPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'}
  {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left}

theorem isCommMonObj_of_isGrpPullback [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    (h : IsGrpPullback G' G f φ) : IsCommMonObj G' := by
  rw [isCommMonObj_iff_isMulCommutative]
  intro T
  refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
  rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
    ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]

theorem isAbelianScheme_of_isGrpPullback [GrpObj G] [GrpObj G'] (hG : IsAbelianScheme G)
    (h : IsGrpPullback G' G f φ) : IsAbelianScheme G' := by
  have := hG.comm
  exact
    { comm := isCommMonObj_of_isGrpPullback h
      smooth := MorphismProperty.of_isPullback (P := @Smooth) h.1 hG.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) h.1 hG.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hG.geomConnected }

theorem relAmple_restrict (h : IsPullback φ G'.hom G.hom f) (hL : L.IsLB) (hL' : L'.IsLB)
    (e : LBIso L' (L.pull φ)) (hA : Out.RelAmple G L) (V : S.Opens) (hV : IsAffineOpen V) :
    Out.RelAmple (Over.mk (G'.hom ∣_ (f ⁻¹ᵁ V))) (L'.pull (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι) := by
  have H : IsPullback ((G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ) (G'.hom ∣_ (f ⁻¹ᵁ V)) G.hom ((f ⁻¹ᵁ V).ι ≫ f) :=
    (isPullback_morphismRestrict G'.hom (f ⁻¹ᵁ V)).flip.paste_horiz h
  obtain ⟨w, hw⟩ : LBIso (L'.pull (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι) (L.pull ((G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ)) :=
    LBIso.chartPull (chartPullPull L' _ _ rfl)
      (chartPullSame L (fun _ : PUnit => (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ) (fun _ => φ) (fun _ => 1) _ fun _ => rfl) e
  let i := (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
  have hPull : (L'.pull i).IsLB := by
    refine ⟨top_le_iff.1 ?_, ?_, ?_⟩
    · intro y _
      obtain ⟨j, hj⟩ := exists_chart hL' (i y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => j, mem_pull.2 hj⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 _) y _ hy, map_one, gm_pull_g L' i (𝟙 _) y J J hy hy]
      exact gm_self hL' i y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy,
        gm_pull_g L' i (𝟙 _) y I J hy.1.1 hy.1.2,
        gm_pull_g L' i (𝟙 _) y J K hy.1.2 hy.2,
        gm_pull_g L' i (𝟙 _) y I K hy.1.1 hy.2]
      exact gm_cocycle hL' i y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  exact relAmple_pull (A' := Over.mk (G'.hom ∣_ (f ⁻¹ᵁ V))) H hL hPull
    ((isGen_iff w).1 hw) V hV (fun y => y.2) hA

theorem pol_pull_of_relAmple_local
    (hloc : ∀ (S : Scheme.{0}) (A : Over S) (L : LB A.left), L.IsLB → QuasiCompact A.hom → QuasiSeparated A.hom →
      (∀ s : S, ∃ (U : S.Opens) (_ : s ∈ U),
        Out.RelAmple (Over.mk (A.hom ∣_ U)) (L.pull (A.hom ⁻¹ᵁ U).ι)) → Out.RelAmple A L) :
    ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsAbelianScheme G → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → IsAbelianScheme G' ∧ (Out.RelAmple G L → Out.RelAmple G' L') ∧ (Out.KTriv G L → Out.KTriv G' L') := by
  intro S S' G G' _ _ f φ L L' hL hL' hG h e
  have hG' := isAbelianScheme_of_isGrpPullback hG h
  have := hG'.proper
  refine ⟨hG', fun hA => hloc S' G' L' hL' inferInstance inferInstance fun s => ?_, fun hK => ?_⟩
  · obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := f s) trivial
    exact ⟨f ⁻¹ᵁ V, hs, relAmple_restrict h.1 hL hL' e hA V hV⟩
  · obtain ⟨w, hw⟩ := e
    exact kTriv_pull h hL hL' ((isGen_iff w).1 hw) hK

end GlobalTheory.PolPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ZM.SiegPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem lbIso_pull_comp {X Y Y' : Scheme.{0}} {L : LB X} {A : LB Y} {F : Y ⟶ X} (H : LBIso A (L.pull F))
    (h : Y' ⟶ Y) : LBIso (A.pull h) (L.pull (h ≫ F)) := by
  refine LBIso.chartPull (chartPullPull A h h rfl) ⟨id, fun J x hx => ?_, fun y J J' hJ hJ' => ?_⟩ H
  · have hx' := (mem_pull (F := h ≫ F)).1 hx
    exact (mem_pull (F := F)).2 hx'
  · have a1 := (mem_pull (F := h ≫ F)).1 hJ
    have a2 := (mem_pull (F := h ≫ F)).1 hJ'
    rw [gm_pull_g L (h ≫ F) (𝟙 Y') y J J' hJ hJ', Category.id_comp]
    exact (gm_pull_g L F h y J J' ((mem_pull (F := F)).2 a1) ((mem_pull (F := F)).2 a2)).symm

theorem exists_isSquare {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left} (w : φ ≫ G.hom = G'.hom ≫ f) :
    ∃ φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left, IsSquare φ φ₂ := by
  let T : Over S := Over.mk ((G' ⊗ G').hom ≫ f)
  have w₁ : ((fst G' G').left ≫ φ) ≫ G.hom = T.hom := by
    rw [Category.assoc, w, ← Category.assoc, Over.w (fst G' G')]
    rfl
  have w₂ : ((snd G' G').left ≫ φ) ≫ G.hom = T.hom := by
    rw [Category.assoc, w, ← Category.assoc, Over.w (snd G' G')]
    rfl
  let x : T ⟶ G := Over.homMk ((fst G' G').left ≫ φ) w₁
  let y : T ⟶ G := Over.homMk ((snd G' G').left ≫ φ) w₂
  refine ⟨(lift x y).left, ?_, ?_⟩
  · rw [← Over.comp_left, lift_fst]
    rfl
  · rw [← Over.comp_left, lift_snd]
    rfl

theorem isSquare_tensor {G G' : Over S} (φ : G' ⟶ G) : IsSquare φ.left (φ ⊗ₘ φ).left := by
  constructor
  · rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
  · rw [← Over.comp_left, tensorHom_snd, Over.comp_left]

theorem isSquare_comp {S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {ψ : G''.left ⟶ G'.left} {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare ψ ψ₂) (h : IsSquare φ φ₂) : IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) := by
  constructor
  · rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc]
  · rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]

theorem isSquare_unique {G : Over S} {G' : Over S'} {φ φ' : G'.left ⟶ G.left}
    {φ₂ φ₂' : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h : IsSquare φ φ₂) (h' : IsSquare φ' φ₂') (e : φ = φ') : φ₂ = φ₂' := by
  subst e
  have w : φ₂' ≫ (G ⊗ G).hom = φ₂ ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), ← Category.assoc, h'.1, ← Category.assoc, h.1]
  let a : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂ rfl
  let b : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂' w
  have hab : a = b := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      change φ₂ ≫ (fst G G).left = φ₂' ≫ (fst G G).left
      rw [h.1, h'.1]
    · apply Over.OverMorphism.ext
      change φ₂ ≫ (snd G G).left = φ₂' ≫ (snd G G).left
      rw [h.2, h'.2]
  exact congrArg (fun m => m.left) hab

theorem lbIso_lam_pull {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (h : IsGrpPullback G' G f φ)
    (hw : LBIso L' (L.pull φ)) {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (hs : IsSquare φ φ₂) :
    LBIso (abelian₂ G' L') ((abelian₂ G L).pull φ₂) := by
  obtain ⟨w, hw'⟩ := hw
  have hP : PGen w := by
    unfold PGen gw
    intro Y g y j j' k k' h1 h2 h3 h4
    have m1 : g y ∈ (L.pull φ).U (fun _ => j) := (mem_pull (F := φ)).2 h1
    have m2 : g y ∈ (L.pull φ).U (fun _ => j') := (mem_pull (F := φ)).2 h2
    have hV : g y ∈ (L.pull φ).U (fun _ => j) ⊓ L'.U k ⊓ ((L.pull φ).U (fun _ => j') ⊓ L'.U k') :=
      ⟨⟨m1, h3⟩, ⟨m2, h4⟩⟩
    have e := congrArg (gm g y _) (hw' (fun _ => j, k) (fun _ => j', k'))
    unfold LB.div at e
    simp only [map_mul, map_inv] at e
    simp only [gm_res g y _ hV] at e
    rw [gm_pull_g L φ g y (fun _ => j) (fun _ => j') m1 m2] at e
    exact e
  have e : ∀ I : ULift (Finset (Fin 2)),
      (psum G' (x2 G') I.down).left ≫ φ = φ₂ ≫ (psum G (x2 G) I.down).left := by
    let T : Over S' := G' ⊗ G'
    have hj : φ₂ ≫ (G ⊗ G).hom = T.hom ≫ f := by
      rw [← Over.w (fst G G), ← Category.assoc, hs.1, Category.assoc, h.1.w, ← Category.assoc,
        Over.w (fst G' G')]
    let U : Over S := Over.mk (T.hom ≫ f)
    let j : U ⟶ G ⊗ G := Over.homMk φ₂ hj
    have hΦ : ∀ u : T ⟶ G', (u.left ≫ φ) ≫ G.hom = U.hom := fun u => by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w u]
      rfl
    let Φ : (T ⟶ G') → (U ⟶ G) := fun u => Over.homMk (u.left ≫ φ) (hΦ u)
    have Φmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y =>
      Over.OverMorphism.ext (h.2 T x y (Φ x) (Φ y) rfl rfl).symm
    let Φh : (T ⟶ G') →* (U ⟶ G) := MonoidHom.mk' Φ Φmul
    have key : ∀ (u : T ⟶ G') (v : G ⊗ G ⟶ G), Φ u = j ≫ v → u.left ≫ φ = φ₂ ≫ v.left :=
      fun u v hh => congrArg (fun m => m.left) hh
    have key' : ∀ (u : T ⟶ G') (v : G ⊗ G ⟶ G), u.left ≫ φ = φ₂ ≫ v.left → Φ u = j ≫ v :=
      fun u v hh => Over.OverMorphism.ext (by exact hh)
    have base : ∀ k : Fin 2, Φ (x2 G' k) = j ≫ x2 G k := by
      intro k
      fin_cases k
      · exact key' _ _ hs.1.symm
      · exact key' _ _ hs.2.symm
    have fold : ∀ l : List (Fin 2),
        Φ (List.foldr (fun k acc => padd G' (x2 G' k) acc) (pzero G' (G2 G')) l) =
          j ≫ List.foldr (fun k acc => padd G (x2 G k) acc) (pzero G (G2 G)) l := by
      intro l
      induction l with
      | nil =>
        change Φh 1 = j ≫ 1
        rw [map_one, comp_one]
      | cons k l ih =>
        change Φ (x2 G' k * _) = j ≫ (x2 G k * _)
        rw [Φmul, comp_mul, base k, ih]
    intro I
    exact key _ _ (fold _)
  exact LBIso.chartPull (chartPullId _) (chartPullOut L _ _ φ₂ _ e) (iso_linComb hP _ _)

end GlobalTheory.ZM.SiegPull


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.DlogPol

section Germs
variable {X Y Z : Scheme.{0}}

theorem gs_rsT (r : Z ⟶ Y) (z : Z) {O₀ O : Y.Opens} (h : O ≤ O₀) (hz : r z ∈ O) (s : Γ(Y, O₀)) :
    gs r z O (rsT s O) = gs r z O₀ s := by
  rw [rsT, dif_pos h]
  exact gs_res r z h hz s

theorem gs_pbT (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) {O₀ : X.Opens} {O : Y.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (hz : r z ∈ O)
    (s : Γ(X, O₀)) : gs r z O (pbT f s O) = gs (r ≫ f) z O₀ s := by
  rw [pbT, dif_pos h]
  exact (gs_res r z h hz ((f.app O₀).hom s)).trans (gs_pull r f z O₀ (h hz) s)

theorem gs_one (r : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : r z ∈ O) : gs r z O 1 = 1 := by
  simp only [gs_eq r z O hz, map_one]

theorem gs_sub (r : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : r z ∈ O) (a b : Γ(Y, O)) :
    gs r z O (a - b) = gs r z O a - gs r z O b := by
  simp only [gs_eq r z O hz, map_sub]

theorem gs_constFn {R : Type} [CommRing R] (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : r z ∈ O) (a : R) :
    gs r z O (constFn p O a) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) :=
  (gs_res r z (show O ≤ p ⁻¹ᵁ ⊤ from fun _ _ => trivial) hz ((p.app ⊤).hom _)).trans (gs_pull r p z ⊤ trivial _)

theorem eps_sq {K : Type} [Field K] (p : X ⟶ Sp (DualNumber K)) (U : X.Opens) :
    constFn p U DualNumber.eps * constFn p U DualNumber.eps = 0 := by
  unfold constFn
  rw [← map_mul, ← map_mul, DualNumber.eps_mul_eps, map_zero, map_zero]

end Germs

theorem exists_gen {K : Type} [Field K] {X Y Y' : Scheme.{0}} (π : Y' ⟶ Sp (DualNumber K)) (τ ρ : Y' ⟶ Y)
    (hτ : ∀ (y : Y') (W : Y.Opens), τ y ∈ W → ρ y ∈ W) (m : Y ⟶ X) (L : LB X) (hL : L.IsLB)
    (k : C1 (fun i => m ⁻¹ᵁ L.U i))
    (hk : ∀ i j (y : Y'), m (τ y) ∈ L.U i → m (τ y) ∈ L.U j →
      gs (τ ≫ m) y _ (L.g i j).val = gs (ρ ≫ m) y _ (L.g i j).val *
        (1 + gs π y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom DualNumber.eps) *
          gs ρ y _ (k i j)))
    (hc : IsCob _ k) :
    ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) (fun n => ![τ, ρ] n ≫ m) ![1, -1]), t.IsGen := by
  obtain ⟨b, hb⟩ := hc
  let φ : Fin 2 → (Y' ⟶ X) := fun n => ![τ, ρ] n ≫ m
  have h₀ : ∀ (J : Fin 2 → L.ι) (y : Y'), y ∈ LB.wchart L φ J → m (τ y) ∈ L.U (J 0) := fun J y hy =>
    Set.mem_iInter.1 hy 0
  have h₀' : ∀ (J : Fin 2 → L.ι) (y : Y'), y ∈ LB.wchart L φ J → m (ρ y) ∈ L.U (J 0) := fun J y hy =>
    hτ y (m ⁻¹ᵁ L.U (J 0)) (h₀ J y hy)
  have h₁ : ∀ (J : Fin 2 → L.ι) (y : Y'), y ∈ LB.wchart L φ J → m (ρ y) ∈ L.U (J 1) := fun J y hy =>
    Set.mem_iInter.1 hy 1
  have le : ∀ J : Fin 2 → L.ι, LB.wchart L φ J ≤ (ρ ≫ m) ⁻¹ᵁ (L.U (J 0) ⊓ L.U (J 1)) := fun J y hy =>
    ⟨h₀' J y hy, h₁ J y hy⟩
  let u : ∀ J : Fin 2 → L.ι, Γ(Y', LB.wchart L φ J)ˣ := fun J =>
    ⟨1 - constFn π _ DualNumber.eps * pbT ρ (b (J 0)) _, 1 + constFn π _ DualNumber.eps * pbT ρ (b (J 0)) _,
      by linear_combination (-(pbT ρ (b (J 0)) (LB.wchart L φ J)) ^ 2) * eps_sq π (LB.wchart L φ J),
      by linear_combination (-(pbT ρ (b (J 0)) (LB.wchart L φ J)) ^ 2) * eps_sq π (LB.wchart L φ J)⟩
  refine ⟨⟨fun J => res (le J) (pullU (ρ ≫ m) _ (L.g (J 0) (J 1))) * u J⟩, isGen_of_gm _ fun y J J' hJ hJ' => ?_⟩
  set e := gs π y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom DualNumber.eps) with he
  have ee : e * e = 0 := by
    rw [he, ← gs_mul π y ⊤ trivial, ← map_mul, DualNumber.eps_mul_eps, map_zero, gs_eq π y ⊤ trivial, map_zero, map_zero]
  have val : ∀ J : Fin 2 → L.ι, y ∈ LB.wchart L φ J →
      (gm (𝟙 Y') y (LB.wchart L φ J) (res (le J) (pullU (ρ ≫ m) _ (L.g (J 0) (J 1))) * u J)).val =
        (gm (ρ ≫ m) y _ (L.g (J 0) (J 1))).val * (1 - e * gs ρ y _ (b (J 0))) := fun J hJ => by
    rw [map_mul, Units.val_mul, gm_res (𝟙 Y') y (le J) hJ, gm_pull (𝟙 Y') (ρ ≫ m) y _ (le J hJ), Category.id_comp,
      ← gs_unit (𝟙 Y') y _ hJ]
    congr 1
    change gs (𝟙 Y') y _ (1 - constFn π _ DualNumber.eps * pbT ρ (b (J 0)) _) = _
    rw [gs_sub _ _ _ hJ, gs_one _ _ _ hJ, gs_mul _ _ _ hJ, gs_constFn _ _ _ _ hJ,
      gs_pbT (𝟙 Y') ρ y (O₀ := m ⁻¹ᵁ L.U (J 0)) (fun y hy => h₀' J y hy) hJ, Category.id_comp, Category.id_comp]
  have tr : trF φ ![1, -1] (𝟙 Y') y J J' =
      gm (τ ≫ m) y _ (L.g (J 0) (J' 0)) * (gm (ρ ≫ m) y _ (L.g (J 1) (J' 1)))⁻¹ := by
    rw [trF, Fin.prod_univ_two]
    simp only [Category.id_comp]
    simp [φ]
  have c₁ := gm_cocycle hL (ρ ≫ m) y (h₀' J y hJ) (h₀' J' y hJ') (h₁ J' y hJ')
  have c₂ := gm_cocycle hL (ρ ≫ m) y (h₀' J y hJ) (h₁ J y hJ) (h₁ J' y hJ')
  have k₁ := hk _ _ y (h₀ J y hJ) (h₀ J' y hJ')
  have m₀ : ρ y ∈ m ⁻¹ᵁ L.U (J 0) ⊓ m ⁻¹ᵁ L.U (J' 0) := ⟨h₀' J y hJ, h₀' J' y hJ'⟩
  rw [hb, gs_sub _ _ _ m₀, gs_rsT _ _ inf_le_right m₀, gs_rsT _ _ inf_le_left m₀,
    gs_unit (τ ≫ m) y (L.U (J 0) ⊓ L.U (J' 0)) ⟨h₀ J y hJ, h₀ J' y hJ'⟩, gs_unit (ρ ≫ m) y (L.U (J 0) ⊓ L.U (J' 0)) m₀, ← he] at k₁
  change gm (𝟙 Y') y (LB.wchart L φ J) _ = trF φ ![1, -1] (𝟙 Y') y J J' * gm (𝟙 Y') y (LB.wchart L φ J') _
  rw [tr, _root_.mul_assoc, mul_left_comm, eq_inv_mul_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val J hJ, val J' hJ', k₁]
  have d := congrArg Units.val (c₁.trans c₂.symm)
  rw [Units.val_mul, Units.val_mul] at d
  linear_combination (-(1 - e * gs ρ y _ (b (J 0)))) * d +
    ((gm (ρ ≫ m) y _ (L.g (J 0) (J' 0))).val * (gm (ρ ≫ m) y _ (L.g (J' 0) (J' 1))).val *
      (gs ρ y _ (b (J' 0)) - gs ρ y _ (b (J 0))) * gs ρ y _ (b (J' 0))) * ee

theorem isUnit_pbT {X Y : Scheme.{0}} (m : Y ⟶ X) (L : LB X) (i j : L.ι) :
    IsUnit (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j)) := by
  rw [pbT, dif_pos (show m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j ≤ m ⁻¹ᵁ (L.U i ⊓ L.U j) from fun _ h => h)]
  exact (L.g i j).isUnit.map _

theorem isCoc_dlog {X Y : Scheme.{0}} (m : Y ⟶ X) (L : LB X) (hL : L.IsLB)
    (d : ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)) (hmul : ∀ W f f', d W (f * f') = f * d W f' + f' * d W f)
    (hres : ∀ W W' (f : Γ(Y, W)), W' ≤ W → d W' (rsT f W') = rsT (d W f) W')
    (φ : C1 (fun i => m ⁻¹ᵁ L.U i))
    (hφ : ∀ i j, pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) * φ i j =
      d _ (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j))) : IsCoc _ φ := by
  intro i j k
  set O : Y.Opens := m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j ⊓ m ⁻¹ᵁ L.U k with hO
  let G : L.ι → L.ι → Γ(Y, O) := fun a b => rsT (pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b)) O
  have hd : ∀ a b, O ≤ m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b → d O (G a b) = G a b * rsT (φ a b) O := fun a b h => by
    rw [hres _ _ _ h, ← hφ]
    simp only [G, rsT, dif_pos h, map_mul]
  have hg : ∀ a b, O ≤ m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b → ∀ y ∈ O,
      gs (𝟙 Y) y O (G a b) = (gm m y _ (L.g a b)).val := fun a b h y hy => by
    rw [gs_rsT _ _ h hy, gs_pbT (𝟙 Y) m y (O₀ := L.U a ⊓ L.U b) (O := m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b) (fun _ h => h) (h hy), Category.id_comp,
      gs_unit m y (L.U a ⊓ L.U b) (h hy)]
  have l₁ : O ≤ m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j := inf_le_left
  have l₂ : O ≤ m ⁻¹ᵁ L.U j ⊓ m ⁻¹ᵁ L.U k := fun _ h => ⟨h.1.2, h.2⟩
  have l₃ : O ≤ m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U k := fun _ h => ⟨h.1.1, h.2⟩
  have co : G i j * G j k = G i k := fn_ext fun y hy => by
    rw [gs_mul _ _ _ hy, hg _ _ l₁ y hy, hg _ _ l₂ y hy, hg _ _ l₃ y hy, ← Units.val_mul,
      gm_cocycle hL m y hy.1.1 hy.1.2 hy.2]
  have un : IsUnit (G i k) := by
    simp only [G, rsT, dif_pos l₃]
    exact (isUnit_pbT m L i k).map _
  have e := hmul O (G i j) (G j k)
  rw [co, hd _ _ l₁, hd _ _ l₂, hd _ _ l₃] at e
  refine un.mul_left_cancel ?_
  change G i k * (rsT (φ i j) O + rsT (φ j k) O) = G i k * rsT (φ i k) O
  linear_combination (-1 : Γ(Y, O)) * e - (rsT (φ i j) O + rsT (φ j k) O) * co

theorem preimage_transl {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] (w : epsR K ⟶ A) (hw : IsTangent w)
    (W : A.left.Opens) :
    ((fst (epsR K) A ≫ w) * snd (epsR K) A).left ⁻¹ᵁ W = (snd (epsR K) A).left ⁻¹ᵁ W := by
  let z : 𝟙_ (Over (Sp K)) ⟶ epsR K := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)
  have hz : z ≫ w = η[A] := Over.OverMorphism.ext hw
  let j : A ⟶ epsR K ⊗ A := lift (toUnit A ≫ z) (𝟙 A)
  have j₁ : j ≫ snd (epsR K) A = 𝟙 A := lift_snd _ _
  have j₂ : j ≫ ((fst (epsR K) A ≫ w) * snd (epsR K) A) = 𝟙 A := by
    rw [MonObj.comp_mul, j₁, lift_fst_assoc, Category.assoc, hz, ← Hom.one_def, _root_.one_mul]
  have j₃ : j.left ≫ (fst (epsR K) A).left = A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom := by
    have := congrArg (fun q => q.left) (lift_fst (toUnit A ≫ z) (𝟙 A))
    refine this.trans ?_
    change (toUnit A).left ≫ _ = _
    congr 1
  have h := (GlobalTheory.ConstThickening.structure_dualNumber K A.left (epsR K ⊗ A).left A.hom (fst (epsR K) A).left (snd (epsR K) A).left j.left
    (IsPullback.of_hasPullback (epsR K).hom A.hom).flip (congrArg (fun q => q.left) j₁) j₃).1
    (((fst (epsR K) A ≫ w) * snd (epsR K) A).left ⁻¹ᵁ W)
  rw [← h, ← Scheme.Hom.comp_preimage j.left, ← Over.comp_left, j₂]
  rfl

theorem dlog_independent : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (X : Scheme.{0}) (m : P₀.A.left ⟶ X) (L : LB X), L.IsLB → LBIso P₀.L (L.pull m) → (∃ φ, IsDlog m L dd φ) ∧ ∀ φ, IsDlog m L dd φ → (∀ a, IsCoc _ (φ a)) ∧ ∀ c, IsCob _ (lc P₀.A.hom c φ) → c = 0 := by
  intro K _ P g v dd hv hdd X m L hL ⟨u, hu⟩
  refine ⟨⟨fun a i j => ((isUnit_pbT m L i j).unit⁻¹ : _ˣ).val * dd a _ (pbT m (L.g i j).val _), fun a i j => ?_⟩,
    fun φ hφ => ⟨fun a => ?_, fun c hc => ?_⟩⟩
  · rw [← _root_.mul_assoc, IsUnit.mul_val_inv, _root_.one_mul]
  · obtain ⟨-, h₁, h₂, -⟩ := (GlobalTheory.KS.InvField.main K P.A (v a) (hv.1 a)).2 _ (hdd a)
    exact isCoc_dlog m L hL (dd a) h₁ h₂ (φ a) (hφ a)
  have := P.isAb.comm
  obtain ⟨a₁, a₂, a₃, -⟩ := GlobalTheory.LieComb.lieComb_algebra K P.A g v hv.1
  obtain ⟨w, hw, -⟩ := a₁ c
  have tw := a₂ c w hw
  obtain ⟨dw, hdw⟩ := (GlobalTheory.KS.InvField.main K P.A w tw).1
  have hsum : ∀ (W : P.A.left.Opens) (h : Γ(P.A.left, W)), dw W h = ∑ a, constFn P.A.hom _ (c a) * dd a W h :=
    GlobalTheory.KS.InvHom.invDer_along_hom K P.A P.A (𝟙 _) g v dd w dw c inferInstance hv.1 tw hdd hdw (by rwa [Category.comp_id])
  have pre := preimage_transl w tw
  set τ := ((fst (epsR K) P.A ≫ w) * snd (epsR K) P.A).left with hτ
  set ρ := (snd (epsR K) P.A).left with hρ
  obtain ⟨t, ht⟩ := exists_gen (fst (epsR K) P.A).left τ ρ (fun y W hy => (pre W).le hy) m L hL _ (fun i j y hi hj => by
    have hy : y ∈ ρ ⁻¹ᵁ (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) := (pre _).le ⟨hi, hj⟩
    have e := congrArg (gs (𝟙 _) y _) (hdw (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) (pbT m (L.g i j).val _))
    have e₂ : dw _ (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j)) =
        pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) * lc P.A.hom c φ i j := by
      rw [hsum, lc, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [← hφ a i j, mul_left_comm]
    rw [e₂, gs_add _ _ _ hy, gs_mul _ _ _ hy, gs_constFn _ _ _ _ hy, gs_pbT _ _ _ (pre _).ge hy,
      gs_pbT _ _ _ le_rfl hy, gs_pbT _ _ _ le_rfl hy, Category.id_comp, Category.id_comp, Category.id_comp,
      gs_mul _ _ _ hy, gs_pbT _ m y (O₀ := L.U i ⊓ L.U j) (O := m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) (fun _ h => h) ⟨hi, hj⟩,
      gs_pbT _ m y (O₀ := L.U i ⊓ L.U j) (O := m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) (fun _ h => h) hy] at e
    refine e.trans ?_
    ring) hc
  obtain ⟨s, hs⟩ := exists_down ((isGen_iff u).1 hu) hL P.isLB t ht
  have w1 : w = 1 := P.ktriv (DualNumber K) _ w fun p =>
    ⟨⊤, trivial, gen_chartPull (chartPullPull (Out.translDiff P.A P.L w) _ _ rfl) s hs⟩
  have h0 : IsLieComb 0 v w := by
    have := a₃ 0 Fin.elim0 Fin.elim0 Fin.elim0 w (fun i => i.elim0) ⟨Fin.elim0, fun i => i.elim0, by rw [w1]; rfl⟩
    simpa using this
  exact (hv.2 w tw).unique hw h0

end GlobalTheory.KS.DlogPol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.logDerivative_principalPolarisation_independent : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (X : Scheme.{0}) (m : P₀.A.left ⟶ X) (L : LB X), L.IsLB → LBIso P₀.L (L.pull m) → (∃ φ, IsDlog m L dd φ) ∧ ∀ φ, IsDlog m L dd φ → (∀ a, IsCoc _ (φ a)) ∧ ∀ c, IsCob _ (lc P₀.A.hom c φ) → c = 0 := by
  first | exact @GlobalTheory.KS.DlogPol.dlog_independent | exact GlobalTheory.KS.DlogPol.dlog_independent | (intros; apply GlobalTheory.KS.DlogPol.dlog_independent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExt
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExt
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PolDescent

theorem exists_gen_of_unique {Y : Scheme.{0}} [Subsingleton Y] (y₀ : Y) {M : LB Y} (hM : M.IsLB) :
    ∃ t : LB.Gen M, t.IsGen := by
  obtain ⟨i₀, hi₀⟩ := exists_chart hM y₀
  have h : ∀ y, y ∈ M.U i₀ := fun y => by rwa [Subsingleton.elim y y₀]
  have le : ∀ i, M.U i ≤ M.U i ⊓ M.U i₀ := fun i => le_inf le_rfl fun y _ => h y
  refine ⟨⟨fun i => res (le i) (M.g i i₀)⟩, fun i j => unit_ext fun y hy => ?_⟩
  refine ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.1 _)).trans (Eq.symm ((map_mul _ _ _).trans ?_))
  refine (congrArg _ ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _))).trans ?_
  exact gm_cocycle hM _ y hy.1 hy.2 (h y)

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}

theorem inv_left_comp (h : IsGrpPullback A' A f φ) :
    (GrpObj.inv : A' ⟶ A').left ≫ φ = φ ≫ (GrpObj.inv : A ⟶ A).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h A') (𝟙 A'))
  simp only [Hom.inv_def, Category.id_comp] at e
  exact e.trans (congrArg (· ≫ _) (Category.id_comp φ))

theorem kTriv_of_pullback [Flat f] [Surjective f] [IsAffineHom f] (h : IsGrpPullback A' A f φ) (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : Out.KTriv A' L') : Out.KTriv A L := by
  obtain ⟨w, hw⟩ := hw
  intro R _ t x hx
  have : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)
  let R' : Type := Γ(pullback t f, ⊤)
  let e : Spec (CommRingCat.of R') ⟶ pullback t f := (pullback t f).isoSpec.inv
  have : IsIso e := inferInstanceAs (IsIso (pullback t f).isoSpec.inv)
  have : Epi (pullback.fst t f) := Flat.epi_of_flat_of_surjective _
  obtain ⟨q, t', hq, sq⟩ : ∃ (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
      (t' : Spec (CommRingCat.of R') ⟶ S'), Epi q ∧ q ≫ t = t' ≫ f :=
    ⟨e ≫ pullback.fst t f, e ≫ pullback.snd t f, inferInstance, by
      rw [Category.assoc, Category.assoc, pullback.condition]⟩
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  have sx : (q ≫ x.left) ≫ A.hom = t' ≫ f := by rw [Category.assoc, Over.w x]; exact sq
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ sx) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = q ≫ x.left := h.1.lift_fst _ _ _
  have main : x' = toUnit _ ≫ η[A'] := by
    refine hK R' t' x' fun p => ?_
    obtain ⟨V, hV, c, hc⟩ := hx (q p)
    refine ⟨q ⁻¹ᵁ V, hV, ?_⟩
    let a : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk ((fst T' A').left ≫ q)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) (Over.w (fst T' A'))))))
    let b : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ A := pushPt h.1.w (snd T' A')
    have k₁ : (lift a b).left ≫ (fst T A).left = (fst T' A').left ≫ q :=
      congrArg (fun q => q.left) (lift_fst a b)
    have k₂ : (snd T' A').left ≫ φ = (lift a b).left ≫ (snd T A).left :=
      (congrArg (fun q => q.left) (lift_snd a b)).symm
    have k₃ : ((fst T' A' ≫ x') * snd T' A').left ≫ φ = (lift a b).left ≫ ((fst T A ≫ x) * snd T A).left := by
      have e₀ : lift a b ≫ ((fst T A ≫ x) * snd T A) = (a ≫ x) * b := by
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
      have e₁ := h.2 (T' ⊗ A') (fst T' A' ≫ x') (snd T' A') (a ≫ x) b
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hx'.symm).trans (Category.assoc _ _ _).symm)) rfl
      rw [← e₀] at e₁
      exact e₁.symm
    obtain ⟨n, hn⟩ : ∃ n : ((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme ⟶ ((fst T A).left ⁻¹ᵁ V).toScheme,
        n ≫ ((fst T A).left ⁻¹ᵁ V).ι = ((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫ (lift a b).left :=
      ⟨IsOpenImmersion.lift _ (((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫ (lift a b).left) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y.1 ∈ V) k₁).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
    let ψ : Fin 2 → (((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme ⟶ A'.left) := fun k =>
      ((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫
        ![(lift (fst T' A' ≫ x') (snd T' A') ≫ μ[A']).left, (snd T' A').left] k
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame L (fun k => ψ k ≫ φ) _ _ n fun k => by
      rw [← Category.assoc n, hn, Category.assoc, Category.assoc]
      fin_cases k
      exacts [congrArg (_ ≫ ·) k₃, congrArg (_ ≫ ·) k₂]) c₁ h₁
    obtain ⟨c₃, h₃⟩ := exists_down ((isGen_iff w).1 hw) hL hL' c₂ h₂
    exact gen_chartPull (chartPullOut L' _ _ _ ψ fun _ => rfl) c₃ h₃
  let a : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk q sq
  have e₁ : pushPt h.1.w x' = 1 := (congrArg _ main).trans (map_one (pushHom h T'))
  have e₂ : a ≫ x = a ≫ (1 : T ⟶ A) :=
    (Over.OverMorphism.ext hx'.symm : a ≫ x = pushPt h.1.w x').trans (e₁.trans (MonObj.comp_one a).symm)
  exact Over.OverMorphism.ext ((cancel_epi q).1 (congrArg (fun z => z.left) e₂))

theorem sym_of_pullback [Subsingleton S'] (s' : S') (h : IsGrpPullback A' A f φ) (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    (desc : ∀ M : LB A.left, M.IsLB → (∃ t : (M.pull φ).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen)
    (hS : Out.Sym A' L') : Out.Sym A L := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨U, hU, c, hc⟩ := hS s'
  obtain ⟨e, he⟩ : ∃ e : A'.left ⟶ (A'.hom ⁻¹ᵁ U).toScheme, e ≫ (A'.hom ⁻¹ᵁ U).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      show A'.hom y ∈ U
      rwa [Subsingleton.elim (A'.hom y) s']), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullSame L' ![(GrpObj.inv : A' ⟶ A').left, 𝟙 _] _ _ e fun k => by
    fin_cases k
    · exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) he).trans (Category.id_comp _))).symm
    · exact he.symm) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up ((isGen_iff w).1 hw) hL hL' c₁ h₁
  obtain ⟨c₃, h₃⟩ := desc _ (DVR.linComb_isLB L hL ![(GrpObj.inv : A ⟶ A).left, 𝟙 _] ![1, -1])
    (gen_chartPull (chartPullOut L _ _ φ _ fun k => by
      fin_cases k
      · exact inv_left_comp h
      · exact (Category.id_comp φ).trans (Category.comp_id φ).symm) c₂ h₂)
  intro s
  refine ⟨⊤, trivial, gen_chartPull (chartPullSame L _ _ _ (A.hom ⁻¹ᵁ ⊤).ι fun k => ?_) c₃ h₃⟩
  fin_cases k
  · rfl
  · exact (Category.comp_id _).symm

theorem rigidified_sym_kTriv_descend : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left) (L₀ : LB A₀.left) (L : LB A.left), IsAbelianScheme A₀ → IsGrpPullback A A₀ (spMap i) φ → L₀.IsLB → L.IsLB → LBIso L (L₀.pull φ) → (Out.Rigidified A L → Out.Rigidified A₀ L₀) ∧ (Out.Sym A L → Out.Sym A₀ L₀) ∧ (Out.KTriv A L → Out.KTriv A₀ L₀) := by
  intro K₀ K _ _ i A₀ A _ _ φ L₀ L hA h hL₀ hL hw
  refine ⟨fun _ => ?_, fun hS => ?_, fun hK => ?_⟩
  · have : Subsingleton (𝟙_ (Over (Sp K₀))).left := inferInstanceAs (Subsingleton (PrimeSpectrum K₀))
    exact exists_gen_of_unique (default : PrimeSpectrum K₀) (pull_isLB hL₀ _)
  · have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    exact sym_of_pullback (default : PrimeSpectrum K) h hL₀ hL hw
      (GlobalTheory.T.lineBundle_trivial_iso_descend_field K₀ K i _ _ A₀.hom A.hom φ hA.smooth hA.proper hA.geomConnected h.1).1 hS
  · have := GlobalTheory.FieldBaseChange.flat_spMap i
    have := GlobalTheory.FieldBaseChange.surjective_spMap i
    exact kTriv_of_pullback h hL₀ hL hw hK

end GlobalTheory.PolDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidified_symmetric_kernelTrivial_descend_fieldExt : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left) (L₀ : LB A₀.left) (L : LB A.left), IsAbelianScheme A₀ → IsGrpPullback A A₀ (spMap i) φ → L₀.IsLB → L.IsLB → LBIso L (L₀.pull φ) → (Out.Rigidified A L → Out.Rigidified A₀ L₀) ∧ (Out.Sym A L → Out.Sym A₀ L₀) ∧ (Out.KTriv A L → Out.KTriv A₀ L₀) := by
  first | exact @GlobalTheory.PolDescent.rigidified_sym_kTriv_descend | exact GlobalTheory.PolDescent.rigidified_sym_kTriv_descend | (intros; apply GlobalTheory.PolDescent.rigidified_sym_kTriv_descend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescentSmoothDimension
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescentSmoothDimension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FieldDescentAb

set_option backward.isDefEq.respectTransparency.types false

theorem fpqc_spMap {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (spMap i) := by
  refine ⟨⟨⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩, ?_⟩, inferInstance⟩
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.Flat.of_isField (Field.toIsField K₀) _

theorem isSeparated_of_isPullback {X Y S T : Scheme.{0}} {f : T ⟶ S} {g : Y ⟶ X}
    {p : X ⟶ S} {q : Y ⟶ T} (H : IsPullback g q p f)
    (hf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) f)
    [IsSeparated q] : IsSeparated p := by
  have h : (MorphismProperty.diagonal @UniversallyClosed) p :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.diagonal @UniversallyClosed) H.flip hf
      (show UniversallyClosed (pullback.diagonal q) from inferInstance)
  have h' : UniversallyClosed (pullback.diagonal p) := h
  exact ⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal p).isClosedMap.isClosed_range⟩

theorem geometricallyConnected_of_isPullback {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K)
    {X Y : Scheme.{0}} {g : Y ⟶ X} {p : X ⟶ Sp K₀} {q : Y ⟶ Sp K}
    (H : IsPullback g q p (spMap i)) [hq : GeometricallyConnected q] :
    GeometricallyConnected p := by
  refine ⟨fun K' _ y Z fst snd h => ?_⟩
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective y
  obtain ⟨Ω, _, _, j, j', e⟩ := GlobalTheory.exists_algClosed_join_of_two_field_extensions K₀ K K' i ψ.hom
  have e' : spMap j ≫ spMap i = spMap j' ≫ Spec.map ψ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext e
  have h₁ : IsPullback (pullback.fst snd (spMap j') ≫ fst) (pullback.snd snd (spMap j')) p
      (spMap j ≫ spMap i) := by
    rw [e']
    exact (IsPullback.of_hasPullback snd (spMap j')).paste_horiz h
  have h₂ : IsPullback (H.lift (pullback.fst snd (spMap j') ≫ fst)
      (pullback.snd snd (spMap j') ≫ spMap j) (by rw [h₁.w, Category.assoc]))
      (pullback.snd snd (spMap j')) q (spMap j) :=
    IsPullback.of_right (by rw [H.lift_fst]; exact h₁) (H.lift_snd _ _ _) H
  have hc : ConnectedSpace ↥(pullback snd (spMap j')) :=
    hq.geometrically_connectedSpace _ _ _ h₂
  have : Surjective (spMap j') := (fpqc_spMap j').1.1
  exact (pullback.fst snd (spMap j')).surjective.connectedSpace
    (pullback.fst snd (spMap j')).continuous

theorem isCommMonObj_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} (A₀ : Over S)
    (A : Over S') [GrpObj A₀] [GrpObj A] {φ : A.left ⟶ A₀.left} (H : IsGrpPullback A A₀ f φ)
    [Flat f] [Surjective f] [IsCommMonObj A] : IsCommMonObj A₀ := by
  have key : ∀ (T₀ : Over S) (x₀ y₀ : T₀ ⟶ A₀), x₀ * y₀ = y₀ * x₀ := by
    intro T₀ x₀ y₀
    let T : Over S' := Over.mk (pullback.snd T₀.hom f)
    let r : Over.mk (T.hom ≫ f) ⟶ T₀ :=
      Over.homMk (pullback.fst T₀.hom f) pullback.condition
    let up : (T₀ ⟶ A₀) → (T ⟶ A) := fun x => Over.homMk
      (H.1.lift (pullback.fst T₀.hom f ≫ x.left) (pullback.snd T₀.hom f)
        (by rw [Category.assoc, Over.w x, pullback.condition])) (H.1.lift_snd _ _ _)
    have hup : ∀ x : T₀ ⟶ A₀, (r ≫ x).left = (up x).left ≫ φ := fun x =>
      (H.1.lift_fst _ _ _).symm
    have h₁ := H.2 T (up x₀) (up y₀) _ _ (hup x₀) (hup y₀)
    have h₂ := H.2 T (up y₀) (up x₀) _ _ (hup y₀) (hup x₀)
    rw [mul_comm (up y₀), ← h₁, ← MonObj.comp_mul, ← MonObj.comp_mul] at h₂
    have : Epi (pullback.fst T₀.hom f) := Flat.epi_of_flat_of_surjective _
    ext1
    rw [← cancel_epi (pullback.fst T₀.hom f)]
    exact h₂.symm
  constructor
  have := key _ (fst A₀ A₀) (snd A₀ A₀)
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, lift_snd_fst] at this
  exact this.symm

theorem isAbelianScheme_and_relDim_descend : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap i) φ → IsAbelianScheme A → IsAbelianScheme A₀ ∧ ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g A₀.hom := by
  intro K₀ K _ _ i A₀ A _ _ φ H hA
  have hf := fpqc_spMap i
  have := hf.1.1
  have := hf.1.2
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hsep : IsSeparated A₀.hom := isSeparated_of_isPullback H.1 hf
  have huc : UniversallyClosed A₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) H.1.flip hf
      inferInstance
  have hsm : Smooth A₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) H.1.flip hf inferInstance
  have h₀ : IsAbelianScheme A₀ :=
    { comm := isCommMonObj_of_isGrpPullback A₀ A H
      smooth := hsm
      proper := {}
      geomConnected := geometricallyConnected_of_isPullback i H.1 }
  refine ⟨h₀, fun g hg => ?_⟩
  obtain ⟨g', hg'⟩ := GlobalTheory.AbelianDim.exists_relDim K₀ A₀ h₀
  have h' : SmoothOfRelativeDimension g' A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback H.1 hg'
  obtain ⟨x, -⟩ := A.hom.surjective (Nonempty.some inferInstance)
  rw [ReciprocityTheory.ChartRestriction.G.H1.dim_unique A.hom hg h' x]
  exact hg'

end GlobalTheory.FieldDescentAb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescentSmoothDimensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.abelian_scheme_descent_smooth_dimension : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap i) φ → IsAbelianScheme A → IsAbelianScheme A₀ ∧ ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g A₀.hom := by
  first | exact @GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend | exact GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend | (intros; apply GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullCubicalOfIso
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

open TopologicalSpace

theorem exists_unit_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (a b : LB.Gen (LB.LinComb L φ ε)) (ha : a.IsGen) (hb : b.IsGen) :
    ∃ u : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (q : K → L.ι), r z ∈ LB.wchart L φ q →
      gm r z (LB.wchart L φ q) (a.s q) = gm r z ⊤ u * gm r z (LB.wchart L φ q) (b.s q) := by
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (q : K → L.ι),
      gm r z (LB.wchart L φ q) (a.s q * (b.s q)⁻¹) =
        gm r z (LB.wchart L φ q) (a.s q) * (gm r z (LB.wchart L φ q) (b.s q))⁻¹ := fun Z r z q =>
    (map_mul _ _ _).trans (congrArg _ (map_inv _ _))
  obtain ⟨u, hu⟩ := glue_unit ⊤ (LB.wchart L φ) (fun _ => le_top) (fun y _ => by
      choose q hq using fun k => exists_chart hL (φ k y)
      exact Opens.mem_iSup.2 ⟨q, Set.mem_iInter.2 hq⟩) (fun q => a.s q * (b.s q)⁻¹) (fun q q' y hy => by
      refine (v _ _ y q).trans (Eq.trans ?_ (v _ _ y q').symm)
      rw [gen_trans ha (𝟙 Y) y hy.1 hy.2, gen_trans hb (𝟙 Y) y hy.1 hy.2, mul_inv, _root_.mul_mul_mul_comm,
        mul_inv_cancel, _root_.one_mul])
  refine ⟨u, fun Z r z q hq => ?_⟩
  rw [← gm_res r z (le_top : LB.wchart L φ q ≤ ⊤) hq u, hu q]
  exact ((congrArg (· * _) (v Z r z q)).trans (inv_mul_cancel_right _ _)).symm

theorem isPullCubical_of_iso (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G']
    [GrpObj G] [IsCommMonObj G] (hA : IsAbelianScheme G') (α : G' ⟶ G) [IsMonHom α] {L' : RigLB G'} {L : RigLB G}
    (c' : CubicalStr G' L') (c : CubicalStr G L) (h : LBIso L'.L (L.L.pull α.left)) :
    (CubeMap.ofHom α).IsPullCubical c' c := by
  obtain ⟨w, hw⟩ := h
  have hw' := (isGen_iff w).1 hw
  obtain ⟨a, ha, hm⟩ := DegPull.exists_pmaps (K := PUnit) hw' L.isLB L'.isLB (φ' := fun _ => eSec G')
    (φ := fun _ => eSec G) (ε := fun _ => 1) (𝟙 _) (fun _ => (CubeMap.ofHom α).e_comm) L.rig L.rigGen
  obtain ⟨u, hu⟩ := exists_unit_ratio L'.isLB a L'.rig ha L'.rigGen
  let w₁ : LB.Iso L'.L (L.L.pull α.left) :=
    ⟨fun p => w.s p * res (U := G'.hom ⁻¹ᵁ ⊤) (fun _ _ => trivial) (pullU G'.hom ⊤ u)⟩
  have g₁ : ∀ (Y : Scheme.{0}) (f : Y ⟶ G'.left) (y : Y) j k, α.left (f y) ∈ L.L.U j → f y ∈ L'.L.U k →
      gw w₁ f y j k = gw w f y j k * gm (f ≫ G'.hom) y ⊤ u := fun Y f y j k hj hk =>
    (map_mul _ _ _).trans (congrArg _ ((gm_res f y _ (show f y ∈ (L.L.pull α.left).U (fun _ => j) ⊓ L'.L.U k from
      ⟨mem_pull.2 hj, hk⟩) _).trans (gm_pull f G'.hom y ⊤ trivial u)))
  have hw₁ : PGen w₁ := fun Y f y j j' k k' hj hj' hk hk' => by
    rw [g₁ Y f y j k hj hk, g₁ Y f y j' k' hj' hk', hw' Y f y j j' k k' hj hj' hk hk', _root_.mul_assoc]
  refine (isPullCubical_iff _ c c').2 ⟨w₁, hw₁, fun Z r z p q hp hq => ?_, ?_⟩
  · refine (hm Z r z p q hp hq).trans ?_
    have e : (r ≫ eSec G') ≫ G'.hom = r := by
      rw [Category.assoc, show eSec G' ≫ G'.hom = 𝟙 _ from Over.w η[G'], Category.comp_id]
    have e₂ := g₁ Z (r ≫ eSec G') z _ _ (hp default) (hq default)
    rw [e] at e₂
    rw [hu Z r z q (Set.mem_iInter.2 hq), Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one]
    exact (_root_.mul_assoc _ _ _).symm.trans (congrArg (· * _) e₂.symm)
  · let e : 𝟙_ (Over S) ⟶ G3 G' := lift 1 (lift 1 1)
    have s₁ := (hG _ _ hA).2
    have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ α.left = (CubeMap.ofHom α).F3 ≫ thφ G (x3 G) I :=
      fun I => (CubeMap.ofHom α).psum_comm I.down
    refine EvenPull.pmaps_of_section (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε) hw₁ L.isLB L'.isLB
      (CubeMap.ofHom α).F3 hψ c'.t c'.isGen
      c.t c.isGen (G3 G').hom e.left (Over.w e) (AbLaw.Cube.surj_tensor hG hA (AbLaw.Cube.surj_tensor hG hA s₁))
      (fun y J J' hJ hJ' => ?_)
    have a₁ : e.left ≫ (CubeMap.ofHom α).F3 = (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left := by
      show (e ≫ (α ⊗ₘ α ⊗ₘ α)).left = _
      simp only [e, lift_map, MonObj.one_comp]
    have b₁ : val c.t (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left y J = 1 := by
      have v := val_corr hJ (c.face 0) (lift (1 : 𝟙_ (Over S) ⟶ G) 1).left
      rw [val_one] at v
      have vp := val_pull (φ := thφ G (x3 G)) (ε := thε) hJ c.t (faceMap G 0).left (lift (1 : 𝟙_ (Over S) ⟶ G) 1).left
      rw [vp] at v
      have eq : (lift (1 : 𝟙_ (Over S) ⟶ G) 1) ≫ faceMap G 0 = lift 1 (lift 1 1) := by
        simp [faceMap, x2, pzero, comp_lift, Hom.one_def]
      rw [← Over.comp_left, eq] at v
      exact v
    have b₂ : val c'.t (lift (1 : 𝟙_ (Over S) ⟶ G') (lift 1 1)).left y J' = 1 := by
      have v := val_corr hJ' (c'.face 0) (lift (1 : 𝟙_ (Over S) ⟶ G') 1).left
      rw [val_one] at v
      have vp := val_pull (φ := thφ G' (x3 G')) (ε := thε) hJ' c'.t (faceMap G' 0).left (lift (1 : 𝟙_ (Over S) ⟶ G') 1).left
      rw [vp] at v
      have eq : (lift (1 : 𝟙_ (Over S) ⟶ G') 1) ≫ faceMap G' 0 = lift 1 (lift 1 1) := by
        simp [faceMap, x2, pzero, comp_lift, Hom.one_def]
      rw [← Over.comp_left, eq] at v
      exact v
    have b₃ := prod_cub (1 : 𝟙_ (Over S) ⟶ G') 1 1 (fun ψ => gw w₁ ψ y (J (ψ ≫ α.left)) (J' ψ))
    refine Eq.trans ((congrArg (fun q => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t q y J) a₁).trans b₁)
      (Eq.symm ?_)
    refine (congrArg₂ (· * ·) b₃ b₂).trans ?_
    simp

theorem mono_of_kTriv {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] (α : G' ⟶ G) [IsMonHom α]
    {L' : LB G'.left} {L : LB G.left} (hL' : L'.IsLB) (hL : L.IsLB) (h : LBIso L' (L.pull α.left))
    (hK : Out.KTriv G' L') : Mono α.left := by
  obtain ⟨w, hw⟩ := h
  have key : ∀ (R : Type) [CommRing R] (t : Sp R ⟶ S) (x : Over.mk t ⟶ G'), x ≫ α = 1 → x = 1 := by
    intro R _ t x hx
    refine hK R t x fun p => ⟨⊤, trivial, ?_⟩
    let φ' : Fin 2 → ((Over.mk t ⊗ G').left ⟶ G'.left) :=
      ![(lift (fst (Over.mk t) G' ≫ x) (snd (Over.mk t) G') ≫ μ[G']).left, (snd (Over.mk t) G').left]
    have e : φ' 0 ≫ α.left = φ' 1 ≫ α.left := by
      show (((fst (Over.mk t) G' ≫ x) * snd (Over.mk t) G') ≫ α).left = (snd (Over.mk t) G' ≫ α).left
      rw [MonObj.mul_comp, Category.assoc, hx, MonObj.comp_one, _root_.one_mul]
    obtain ⟨t₁, h₁, -⟩ := exists_gen hL (φ' := fun k => φ' k ≫ α.left) (ε' := ![1, -1]) (fun U _ k => by
      rw [Fin.prod_univ_two]; simp [e]) (LB.oneGen L (Y := (Over.mk t ⊗ G').left)) AbLaw.Cube.oneGen_isGen
    obtain ⟨t₂, h₂⟩ := exists_down ((isGen_iff w).1 hw) hL hL' t₁ h₁
    exact gen_chartPull (chartPullPull _ _ _ rfl) t₂ h₂
  refine ⟨fun {Z} f g hfg => ?_⟩
  refine Scheme.Cover.hom_ext Z.affineCover _ _ fun i => ?_
  have hs : g ≫ G'.hom = f ≫ G'.hom := by rw [← Over.w α, reassoc_of% hfg]
  let j : Spec (CommRingCat.of (Z.affineOpenCover.X i)) ⟶ Z := Z.affineCover.f i
  let x : Over.mk (j ≫ f ≫ G'.hom) ⟶ G' := Over.homMk (j ≫ f) (Category.assoc _ _ _)
  let y : Over.mk (j ≫ f ≫ G'.hom) ⟶ G' := Over.homMk (j ≫ g) (by rw [Category.assoc, hs]; rfl)
  have e : x ≫ α = y ≫ α := Over.OverMorphism.ext (by
    show (j ≫ f) ≫ _ = (j ≫ g) ≫ _
    rw [Category.assoc, hfg, Category.assoc])
  have := key _ _ (x * y⁻¹) (by rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel])
  exact congrArg (fun q => q.left) (mul_inv_eq_one.1 this)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem iso_of_lam {S : Scheme.{0}} (t' t : SAB H S) (α : t'.G ⟶ t.G) [IsMonHom α]
    (hact : ∀ a, t'.act.act a ≫ α = α ≫ t.act.act a)
    (h : LBIso (abelian₂ t'.G (lbPow t'.PP.L 1)) (abelian₂ t'.G (t.PP.L.pull α.left))) :
    LBIso t'.PP.L (t.PP.L.pull α.left) := by
  let U : t'.G ⟶ G2 t'.G := lift (𝟙 _) (t'.act.act H.w0)
  have ps : ∀ I : Finset (Fin 2), U ≫ psum t'.G (x2 t'.G) I = psum t'.G ![𝟙 _, t'.act.act H.w0] I := fun I =>
    (psum_hom (preHom U) (x2 t'.G) I).trans (congrArg (fun q => psum t'.G q I) (funext fun i => by
      fin_cases i <;> simp [preHom, U, x2]))
  have pa : ∀ I : Finset (Fin 2), psum t'.G ![𝟙 _, t'.act.act H.w0] I ≫ α = α ≫ psum t.G ![𝟙 _, t.act.act H.w0] I :=
    fun I => (psum_hom (MonoidHom.mk' (fun z : t'.G ⟶ t'.G => z ≫ α) fun a b => MonObj.mul_comp a b α) _ I).trans
      ((congrArg (fun q => psum t.G q I) (funext fun i => by
        fin_cases i <;> simp [preHom, hact])).trans (psum_hom (preHom α) ![𝟙 _, t.act.act H.w0] I).symm)
  have h₁ : LBIso (cubeLB t'.G ![𝟙 _, t'.act.act H.w0] (lbPow t'.PP.L 1))
      (cubeLB t'.G ![𝟙 _, t'.act.act H.w0] (t.PP.L.pull α.left)) :=
    LBIso.chartPull (chartPullSame _ _ _ _ U.left fun I => congrArg (fun q => q.left) (ps I.down).symm)
      (chartPullSame _ _ _ _ U.left fun I => congrArg (fun q => q.left) (ps I.down).symm) h
  have h₂ : LBIso (t'.PP.L.pull (𝟙 _)) (cubeLB t'.G ![𝟙 _, t'.act.act H.w0] (t'.PP.L.pull (𝟙 _))) :=
    LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullLinComb _ _ _ _ _ (𝟙 _) fun I => by simp) t'.prim
  have h₃ : LBIso (t.PP.L.pull α.left) (cubeLB t'.G ![𝟙 _, t'.act.act H.w0] (t.PP.L.pull α.left)) :=
    LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullLinComb _ _ _ _ _ α.left fun I =>
      congrArg (fun q => q.left) (pa I.down)) t.prim
  have i₁ : (t'.PP.L.pull (𝟙 _)).IsLB := DVR.linComb_isLB _ t'.PP.isLB _ _
  have i₂ : (t.PP.L.pull α.left).IsLB := DVR.linComb_isLB _ t.PP.isLB _ _
  have h₄ := LBIso.trans i₁ (DVR.linComb_isLB _ i₂ _ _) i₂
    (LBIso.trans i₁ (DVR.linComb_isLB _ i₁ _ _) (DVR.linComb_isLB _ i₂ _ _) h₂ h₁) h₃.symm
  exact LBIso.chartPull (chartPullUnpull _ _ rfl) (chartPullId _) h₄

theorem pow_eq_one_of_weilIs (hK : Out.KerPowSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S)
    {T : Over S} [Unique T.left] {n : ℕ} (hn : 0 < n) {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs P.A P.L n x y c) : x ^ n = 1 ∧ y ^ n = 1 := by
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, -⟩ := h default
  have key : ∀ θ : Out.ThetaGrp P.A P.L n (Out.overRes V), θ.pt ^ n = 1 := fun θ =>
    (hK S P n hn _ θ.pt).1 fun p => ⟨⊤, trivial, gen_chartPull (chartPullPull _ _ _ rfl) θ.φ θ.isGen⟩
  have hs : Surjective V.ι := ⟨fun z => ⟨⟨default, hV⟩, Subsingleton.elim _ _⟩⟩
  have he : Epi V.ι := Flat.epi_of_flat_of_surjective _
  have key₂ : ∀ z : T ⟶ P.A, (Out.overResι V ≫ z) ^ n = 1 → z ^ n = 1 := fun z hz => by
    rw [← MonObj.comp_pow, ← MonObj.comp_one (Out.overResι V)] at hz
    exact Over.OverMorphism.ext ((cancel_epi V.ι).1 (congrArg (fun q => q.left) hz))
  exact ⟨key₂ x (hx ▸ key θx), key₂ y (hy ▸ key θy)⟩

end GlobalTheory.HeckePoint
end
end
