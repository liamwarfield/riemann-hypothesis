module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CubBoxVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GmCharPow
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LcgLinCombEqProd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SquareRes
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowUnif

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig

variable {B B' G G' T T' S₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {j : ℕ}
  {pr : Fin j → (B' ⟶ B)} {prG : Fin j → (G' ⟶ G)} {p : T ⟶ B} {p' : T' ⟶ B'} {f : T ⟶ G} {f' : T' ⟶ G'}

private theorem sec_res_comp_algebraMap {X : Scheme.{0}} {U V W : X.Opens} (h₁ : U ≤ V) (h₂ : V ≤ W)
    (x : Γ(X, W)ˣ) : res h₁ (res h₂ x) = res (h₁.trans h₂) x := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private theorem res_self_lemma {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (x : Γ(X, U)ˣ) : res h x = x := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  have e : homOfLE h = 𝟙 U := rfl
  rw [e, op_id, CategoryTheory.Functor.map_id]
  rfl

private theorem linComb_comp_U_le_linComb_linComb_U {eG' : S₀ ⟶ G'} (jN : Fin j → L.ι) :
    (LB.LinComb L (fun i => eG' ≫ prG i) (fun _ => 1)).U jN ≤
      (LB.LinComb (LB.LinComb L prG (fun _ => 1)) (K := PUnit) (fun _ => eG') (fun _ => 1)).U (fun _ => jN) := by
  intro x hx
  simp only [LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage,
    SetLike.mem_coe] at hx ⊢
  intro _ k
  simpa using hx k

private theorem linComb_unit_U_le {X Y : Scheme.{0}} (N : LB X) (e : Y ⟶ X) (a b : N.ι) :
    (LB.LinComb N (K := PUnit) (fun _ => e) (fun _ => 1)).U (fun _ => a) ⊓
      (LB.LinComb N (K := PUnit) (fun _ => e) (fun _ => 1)).U (fun _ => b) ≤ e ⁻¹ᵁ (N.U a ⊓ N.U b) := by
  intro x hx
  simp only [LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage,
    SetLike.mem_coe, Scheme.Hom.mem_preimage, TopologicalSpace.Opens.mem_inf] at hx ⊢
  exact ⟨hx.1 PUnit.unit, hx.2 PUnit.unit⟩

private theorem linComb_unit_g_eq {X Y : Scheme.{0}} (N : LB X) (e : Y ⟶ X) (a b : N.ι) :
    (LB.LinComb N (K := PUnit) (fun _ => e) (fun _ => 1)).g (fun _ => a) (fun _ => b) =
      res (linComb_unit_U_le N e a b) (pullU e (N.U a ⊓ N.U b) (N.g a b)) := by
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one, pow_one]
  rfl

private theorem res_pullU_id_eq_res'' {X : Scheme.{0}} {U V : X.Opens} (x : Γ(X, U)ˣ) (h : V ≤ (𝟙 X) ⁻¹ᵁ U) :
    res h (pullU (𝟙 X) U x) = res (fun y hy => h hy) x := by
  apply Units.ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rfl

private theorem res_congr_of_index_eq {X : Scheme.{0}} {Idx : Type*} {U : Idx → X.Opens} (s : ∀ a, Γ(X, U a)ˣ) {V : X.Opens}
    {a b : Idx} (e : a = b) (h₁ : V ≤ U a) (h₂ : V ≤ U b) : res h₁ (s a) = res h₂ (s b) := by
  subst e
  rfl

theorem idIso_rig (hL : L.IsLB) {eG : S₀ ⟶ G} {eG' : S₀ ⟶ G'} (rL : LB.Gen (L.pull eG))
    (hG : ∀ (i : Fin j) (_ : PUnit), eG' ≫ prG i = 𝟙 S₀ ≫ eG)
    (hr : (GeneratorPullback.boxGen L prG (fun _ : PUnit => eG') (fun _ => 1)
      (fun i => GeneratorPullback.pullAlong L (prG i) (𝟙 S₀) (fun _ => eG) (fun _ => 1) (fun _ => eG') (hG i) rL)).IsGen) :
    ∃ b : LB.Gen (LB.LinComb L (K := Fin j) (fun i => eG' ≫ prG i) (fun _ => 1)),
      GeneratorPullback.MapsAt L (LB.LinComb L prG (fun _ => 1)) prG (idIso _) eG' 1
        (GeneratorPullback.boxGen L prG (fun _ : PUnit => eG') (fun _ => 1)
          (fun i => GeneratorPullback.pullAlong L (prG i) (𝟙 S₀) (fun _ => eG) (fun _ => 1) (fun _ => eG') (hG i) rL)) b ∧
      LB.Gen.Corr L _ _ _ _ b (GeneratorPullback.finProdGen L (J := Fin j) (fun _ _ => eG) (fun _ _ => 1) (fun _ => rL)) := by
  refine ⟨⟨fun jN => res (linComb_comp_U_le_linComb_linComb_U (prG := prG) (eG' := eG') jN) ((GeneratorPullback.boxGen L prG (fun _ : PUnit => eG') (fun _ => 1)
      (fun i => GeneratorPullback.pullAlong L (prG i) (𝟙 S₀) (fun _ => eG) (fun _ => 1) (fun _ => eG') (hG i) rL)).s fun _ => jN)⟩, ?_, ?_⟩
  · unfold GeneratorPullback.MapsAt
    intro jN jL
    have H := hr (fun _ => jN) (fun _ => jL)
    have hO : eG' ⁻¹ᵁ ((L.LinComb prG fun _ => 1).U jN ⊓ (L.LinComb prG fun _ => 1).U jL) ≤
        ((L.LinComb prG fun _ => 1).LinComb (K := PUnit) (fun _ => eG') (fun _ => 1)).U (fun _ => jN) ⊓
          ((L.LinComb prG fun _ => 1).LinComb (K := PUnit) (fun _ => eG') (fun _ => 1)).U (fun _ => jL) := by
      intro x hx
      simp only [LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage,
        SetLike.mem_coe, Scheme.Hom.mem_preimage, TopologicalSpace.Opens.mem_inf] at hx ⊢
      exact ⟨fun _ => hx.1, fun _ => hx.2⟩
    have H2 := congrArg (res hO) H
    erw [linComb_unit_g_eq] at H2
    simp only [map_mul, sec_res_comp_algebraMap, res_self_lemma] at H2
    dsimp only
    erw [sec_res_comp_algebraMap]
    simp only [pow_one, zpow_one]
    exact H2
  · unfold LB.Gen.Corr GeneratorPullback.finProdGen
    intro j₁ j' c₁ c₂ hj
    have hk : ∀ k, j₁ k = j' (k, PUnit.unit) := fun k => hj k (k, PUnit.unit) (by simpa using hG k PUnit.unit)
    clear hj c₁ c₂ hr
    dsimp only
    unfold GeneratorPullback.boxGen GeneratorPullback.pullAlong
    dsimp only
    erw [sec_res_comp_algebraMap, map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro i _
    erw [sec_res_comp_algebraMap]
    exact (sec_res_comp_algebraMap _ _ _).trans ((res_pullU_id_eq_res'' _ _).trans
      ((res_congr_of_index_eq rL.s (funext fun k => by cases k; exact hk i) _ _).trans (sec_res_comp_algebraMap _ _ _).symm))

private theorem pullU_res_eq_res_pullU'' {X Y : Scheme.{0}} (r : Y ⟶ X) {U U' : X.Opens} (h' : U' ≤ U)
    (hh : r ⁻¹ᵁ U' ≤ r ⁻¹ᵁ U) (x : Γ(X, U)ˣ) : pullU r U' (res h' x) = res hh (pullU r U x) := by
  apply Units.ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

private theorem div_g_eq_res_mul_res_inv {X : Scheme.{0}} (A B : LB X) (p q : A.ι × B.ι) :
    (A.div B).g p q = res (inf_le_inf inf_le_left inf_le_left) (A.g p.1 q.1) *
      (res (inf_le_inf inf_le_right inf_le_right) (B.g p.2 q.2))⁻¹ := rfl

private theorem pull_g_eq_res_pullU {X Y : Scheme.{0}} (N : LB X) (e : Y ⟶ X) (a b : N.ι) :
    (N.pull e).g (fun _ => a) (fun _ => b) = res (linComb_unit_U_le N e a b) (pullU e (N.U a ⊓ N.U b) (N.g a b)) :=
  linComb_unit_g_eq N e a b

private theorem res_mul_rings_of_integers {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (a b : Γ(X, U)ˣ) :
    res h (a * b) = res h a * res h b := map_mul _ _ _

private theorem res_inv' {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) :
    res h a⁻¹ = (res h a)⁻¹ := map_inv _ _

private theorem toFld_gm_res {X Y : Scheme.{0}} (r : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (hV : V ≤ r ⁻¹ᵁ U)
    (u : Γ(X, U)ˣ) (y : Y) (hy : y ∈ V) : gm (𝟙 Y) y V (res hV (pullU r U u)) = gm r y U u := by
  have hy' : r y ∈ U := hV hy
  have hy1 : (𝟙 Y : Y ⟶ Y) y ∈ V := hy
  unfold gm
  rw [dite_eq_left hy1, dite_eq_left hy']
  apply Units.ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, res, pullU]
  exact TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hV) y hy _

private theorem gm_id_res_eq' {Y : Scheme.{0}} {U V : Y.Opens} (hV : V ≤ U) (u : Γ(Y, U)ˣ) (y : Y) (hy : y ∈ V) :
    gm (𝟙 Y) y V (res hV u) = gm (𝟙 Y) y U u := by
  have hy1 : (𝟙 Y : Y ⟶ Y) y ∈ V := hy
  have hy2 : (𝟙 Y : Y ⟶ Y) y ∈ U := hV hy
  unfold gm
  rw [dite_eq_left hy1, dite_eq_left hy2]
  apply Units.ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, res, pullU]
  exact TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hV) y hy _

private theorem units_ext_of_gm_id_eq' {Y : Scheme.{0}} {V : Y.Opens} (a b : Γ(Y, V)ˣ)
    (H : ∀ y (hy : y ∈ V), gm (𝟙 Y) y V a = gm (𝟙 Y) y V b) : a = b := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext Y.sheaf V
  intro y hy
  have e := congrArg Units.val (H y hy)
  have hy1 : (𝟙 Y : Y ⟶ Y) y ∈ V := hy
  unfold gm at e
  rw [dite_eq_left hy1] at e
  exact e

theorem square_res (hM' : M'.IsLB)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull f) (M.pull p)}
    {we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f') (M'.pull p')} {h : Fin j → (T' ⟶ T)}
    (hwe : we'.IsGen) (Q : BoxSquare w we we' h) (jNM : Fin j → M.ι) (jM' : M'.ι) (jL' jNL : Fin j → L.ι)
    (V : T'.Opens) (h₁ : V ≤ p' ⁻¹ᵁ (LB.div (LB.LinComb M pr (fun _ => 1)) M').U (jNM, jM'))
    (h₂ : V ≤ (LB.div (M'.pull p') ((LB.LinComb L prG (fun _ => 1)).pull f')).U (fun _ => jM', fun _ => jL'))
    (h₃ : ∀ i, V ≤ h i ⁻¹ᵁ (LB.div (M.pull p) (L.pull f)).U (fun _ => jNM i, fun _ => jNL i))
    (h₄ : V ≤ f' ⁻¹ᵁ (LB.div (LB.LinComb L prG (fun _ => 1)) (LB.LinComb L prG (fun _ => 1))).U (jNL, jL')) :
    res h₁ (pullU p' _ (w.s (jNM, jM'))) * res h₂ (we'.s (fun _ => jM', fun _ => jL')) =
      (∏ i, res (h₃ i) (pullU (h i) _ (we.s (fun _ => jNM i, fun _ => jNL i)))) *
        res h₄ (pullU f' _ ((idIso (LB.LinComb L prG (fun _ => 1))).s (jNL, jL'))) := by
  have hw2 := hwe
  unfold LB.Gen.IsGen at hw2
  have hV1 : V ≤ ((M'.pull p').div ((L.LinComb prG fun _ => 1).pull f')).U (fun _ => jM', fun _ => jNL) ⊓
      ((M'.pull p').div ((L.LinComb prG fun _ => 1).pull f')).U (fun _ => jM', fun _ => jL') := by
    intro x hx
    have a2 := h₂ hx
    have a4 := h₄ hx
    clear h₁ h₃ Q hwe hw2 h₂ h₄ hx
    simp only [LB.div, LB.pull, LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_mk,
      TopologicalSpace.Opens.coe_mk, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, Scheme.Hom.mem_preimage, Set.mem_inter_iff] at a2 a4 ⊢
    refine ⟨⟨a2.1, ?_⟩, a2.1, ?_⟩
    · exact Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => a4.1 k
    · exact Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => a4.2 k
  have hg := congrArg (res hV1) (hw2 (fun _ => jM', fun _ => jNL) (fun _ => jM', fun _ => jL'))
  simp only [map_mul, sec_res_comp_algebraMap] at hg
  rw [div_g_eq_res_mul_res_inv] at hg
  dsimp only at hg
  rw [pull_g_eq_res_pullU] at hg
  erw [pull_g_eq_res_pullU] at hg
  simp only [map_mul, map_inv, sec_res_comp_algebraMap] at hg
  have hVp : V ≤ p' ⁻¹ᵁ M'.U jM' := fun y hy => (h₁ hy).2
  have hself : ∀ (k : V ≤ p' ⁻¹ᵁ (M'.U jM' ⊓ M'.U jM')),
      res k (pullU p' (M'.U jM' ⊓ M'.U jM') (M'.g jM' jM')) = 1 := by
    intro k
    have e1 := pullU_res_eq_res_pullU'' p' (le_inf le_rfl le_rfl : M'.U jM' ≤ M'.U jM' ⊓ M'.U jM') (fun y hy => ⟨hy, hy⟩)
      (M'.g jM' jM')
    rw [hM'.g_self jM', map_one] at e1
    exact (sec_res_comp_algebraMap hVp (show p' ⁻¹ᵁ M'.U jM' ≤ p' ⁻¹ᵁ (M'.U jM' ⊓ M'.U jM') from fun y hy => ⟨hy, hy⟩) _).symm.trans
      (by rw [← e1, map_one])
  have hX : ∀ k, res hV1 (res k (pullU p' (M'.U jM' ⊓ M'.U jM') (M'.g jM' jM'))) = 1 :=
    fun k => (sec_res_comp_algebraMap _ _ _).trans (hself _)
  erw [res_mul_rings_of_integers, res_inv'] at hg
  erw [hX] at hg
  rw [_root_.one_mul, eq_inv_mul_iff_mul_eq] at hg
  rw [← hg]
  refine (mul_left_comm _ _ _).trans ((mul_comm _ _).trans ?_)
  refine congrArg₂ (· * ·) ?_ ((sec_res_comp_algebraMap _ _ _).trans rfl)
  apply units_ext_of_gm_id_eq'
  intro y hy
  have c1 : ∀ i, pr i (p' ((𝟙 T' : T' ⟶ T') y)) ∈ M.U (jNM i) := fun i => Set.mem_iInter.1 (h₁ hy).1 i
  have c2 : p' ((𝟙 T' : T' ⟶ T') y) ∈ M'.U jM' := (h₁ hy).2
  have c3 : ∀ i, prG i (f' ((𝟙 T' : T' ⟶ T') y)) ∈ L.U (jNL i) := fun i => Set.mem_iInter.1 (h₄ hy).1 i
  have q := Q T' (𝟙 T') y jNM jM' jNL c1 c2 c3
  simp only [bw, Geo.Tor.gw, Category.id_comp] at q
  rw [map_mul, map_prod, toFld_gm_res _ _ _ _ hy, gm_id_res_eq' _ _ _ hy,
    Finset.prod_congr rfl (fun i _ => toFld_gm_res (h i) (h₃ i) _ y hy)]
  exact q

end GlobalTheory.PowUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvenAlong
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowUnif

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig

variable {B B' G G' T T' S S₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {j : ℕ}
  {pr : Fin j → (B' ⟶ B)} {prG : Fin j → (G' ⟶ G)} {p : T ⟶ B} {p' : T' ⟶ B'} {f : T ⟶ G} {f' : T' ⟶ G'}

theorem rig_box (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull f) (M.pull p)}
    {we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f') (M'.pull p')} {h : Fin j → (T' ⟶ T)}
    (hwe : we.IsGen) (Q : BoxSquare w we we' h)
    (hF : ∀ i, h i ≫ f = f' ≫ prG i) (hE : ∀ i, p' ≫ pr i = h i ≫ p)
    {u : S ⟶ T} {u' : S ⟶ T'} {s : S ⟶ S₀} {eG : S₀ ⟶ G} {eA : S₀ ⟶ B} {eG' : S₀ ⟶ G'} {eA' : S₀ ⟶ B'}
    {rL : LB.Gen (L.pull eG)} (hrL : rL.IsGen) {rM : LB.Gen (M.pull eA)} {rM' : LB.Gen (M'.pull eA')}
    (H : RigAlong we u s rL rM) (hu : ∀ i, u' ≫ h i = u) (hf : u ≫ f = s ≫ eG) (hp : u ≫ p = s ≫ eA)
    (hp' : u' ≫ p' = s ≫ eA') (hG : ∀ (i : Fin j) (_ : PUnit), eG' ≫ prG i = 𝟙 S₀ ≫ eG)
    (b : LB.Gen (LB.LinComb M (K := Fin j) (fun i => eA' ≫ pr i) (fun _ => 1)))
    (b₁ : GeneratorPullback.MapsAt M M' pr w eA' 1 rM' b)
    (b₂ : LB.Gen.Corr M _ _ _ _ b (GeneratorPullback.finProdGen M (J := Fin j) (fun _ _ => eA) (fun _ _ => 1) (fun _ => rM))) :
    RigAlong we' u' s (GeneratorPullback.boxGen L prG (fun _ : PUnit => eG') (fun _ => 1)
      (fun i => GeneratorPullback.pullAlong L (prG i) (𝟙 S₀) (fun _ => eG) (fun _ => 1) (fun _ => eG') (hG i) rL)) rM' := by
  rintro ⟨qM, qL⟩ V a₁ a₂ a₃
  refine unit_ext fun y hy => ?_
  have key := rel_box hM hM' hL hwe Q hF hE (K := PUnit) (ε := fun _ => 1) y (fun _ => u') hrL rM rM' s
    (fun _ => s) (fun _ => s) (fun i _ => by rw [hu, hf]) (fun _ => hp') (fun i _ => by rw [hu, hp])
    (fun J J' hJ hJ' => (congrArg₂ (· * ·) (Fintype.prod_unique _) rfl).trans
      ((mapsAt_val w eA' 1 rM' b b₁ s y hJ hJ').symm.trans ((val_corr hJ b₂ s).trans (val_finProd _ _ _ s y hJ))))
    (fun i J N hJ hN => by
      have e := H.stalk hf hp (𝟙 S) y (J (s ≫ eA)) (N (s ≫ eG)) ((pt_of_eq hp y).symm ▸ hJ (s ≫ eA))
        ((pt_of_eq hf y).symm ▸ hN (s ≫ eG))
      rw [Category.id_comp, Category.id_comp] at e
      rw [Fintype.prod_unique, zpow_one, hu]
      exact e.symm)
    qL qM (fun a b _ => congrArg qM (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 (a₃ hy) k)
    (fun k i => (pt_of_eq (hG i k) (s y)) ▸ Set.mem_iInter.1 (Set.mem_iInter.1 (a₂ hy) k) i)
  rw [Fintype.prod_unique, zpow_one] at key
  have e := gm_box_pull L prG (fun _ => 𝟙 S₀) hG (fun _ => rL) s y qL (a₂ hy)
  rw [Category.comp_id] at e
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res_pull _ u' y a₁ hy _)
    (gm_res_pull _ s y a₂ hy _)).trans (Eq.trans ?_ (gm_res_pull _ s y a₃ hy _).symm))
  rw [Category.id_comp, Category.id_comp]
  exact (congrArg₂ (· * ·) rfl e).trans key.symm

def EvenAlong (we : LB.Iso (L.pull f) (M.pull p)) (iT : T ⟶ T) {iG : G ⟶ G} {iB : B ⟶ B}
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]))
    (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1])) : Prop :=
  ∀ (jS : Fin 2 → L.ι) (jT : Fin 2 → M.ι),
    LB.Coh L (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS →
    LB.Coh M (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT →
    ∀ (V : T.Opens) (h₁ : V ≤ p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT)
      (h₂ : V ≤ (M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1))
      (h₃ : V ≤ iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)))
      (h₄ : V ≤ f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS),
      res h₁ (pullU p _ (σ.s jT)) * res h₂ (we.s (fun _ => jT 1, fun _ => jS 1)) =
        res h₃ (pullU iT _ (we.s (fun _ => jT 0, fun _ => jS 0))) * res h₄ (pullU f _ (s.s jS))

theorem EvenAlong.stalk {we : LB.Iso (L.pull f) (M.pull p)} {iT : T ⟶ T} {iG : G ⟶ G} {iB : B ⟶ B}
    {s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1])}
    {σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1])} (ev : EvenAlong we iT s σ)
    (iF : iT ≫ f = f ≫ iG) (iP : iT ≫ p = p ≫ iB) {Z : Scheme.{0}} (r : Z ⟶ T) (z : Z)
    (jS : Fin 2 → L.ι) (jT : Fin 2 → M.ι) (cS : LB.Coh L (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS)
    (cT : LB.Coh M (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT)
    (hS : ∀ k, (![iG, 𝟙 G] : Fin 2 → (G ⟶ G)) k (f (r z)) ∈ L.U (jS k))
    (hT : ∀ k, (![iB, 𝟙 B] : Fin 2 → (B ⟶ B)) k (p (r z)) ∈ M.U (jT k)) :
    gm (r ≫ p) z (LB.wchart M (K := Fin 2) ![iB, 𝟙 B] jT) (σ.s jT) =
      (∏ k, Geo.Tor.gw we ((![r ≫ iT, r] : Fin 2 → _) k) z (jT k) (fun _ => jS k) ^ (![1, -1] : Fin 2 → ℤ) k) *
        gm (r ≫ f) z (LB.wchart L (K := Fin 2) ![iG, 𝟙 G] jS) (s.s jS) := by
  have S0 : f (iT (r z)) ∈ L.U (jS 0) := (pt_of_eq iF (r z)).symm ▸ hS 0
  have T0 : p (iT (r z)) ∈ M.U (jT 0) := (pt_of_eq iP (r z)).symm ▸ hT 0
  have S1 : f (r z) ∈ L.U (jS 1) := hS 1
  have T1 : p (r z) ∈ M.U (jT 1) := hT 1
  let W : T.Opens := p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT ⊓
    ((M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1)) ⊓
    iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)) ⊓
    f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS
  have hW : r z ∈ W := ⟨⟨⟨Set.mem_iInter.2 hT, mem_pull.2 T1, mem_pull.2 S1⟩, mem_pull.2 T0, mem_pull.2 S0⟩,
    Set.mem_iInter.2 hS⟩
  have l₁ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have l₂ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have l₃ : W ≤ _ := inf_le_left.trans inf_le_right
  have l₄ : W ≤ _ := inf_le_right
  obtain ⟨n₁, n₂⟩ := GlobalTheory.EvenPull.even_stalk we s σ jS jT W l₁ l₂ l₃ l₄ r z hW
  have E := n₁.symm.trans ((congrArg (gm r z W) (ev jS jT cS cT W l₁ l₂ l₃ l₄)).trans n₂)
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg]
  rw [← mul_right_comm, ← E, mul_inv_cancel_right]

theorem even_box (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull f) (M.pull p)}
    {we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f') (M'.pull p')} {h : Fin j → (T' ⟶ T)}
    (hwe : we.IsGen) (Q : BoxSquare w we we' h)
    (hF : ∀ i, h i ≫ f = f' ≫ prG i) (hE : ∀ i, p' ≫ pr i = h i ≫ p)
    {iT : T ⟶ T} {iG : G ⟶ G} {iB : B ⟶ B} {iT' : T' ⟶ T'} {iG' : G' ⟶ G'} {iB' : B' ⟶ B'}
    (ih : ∀ i, iT' ≫ h i = h i ≫ iT) (iF : iT ≫ f = f ≫ iG) (iP : iT ≫ p = p ≫ iB) (iP' : iT' ≫ p' = p' ≫ iB')
    (hG : ∀ i k, (![iG', 𝟙 G'] : Fin 2 → _) k ≫ prG i = prG i ≫ (![iG, 𝟙 G] : Fin 2 → _) k)
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1])) (hs : s.IsGen)
    (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]))
    (σ' : LB.Gen (LB.LinComb M' (K := Fin 2) ![iB', 𝟙 B'] ![1, -1]))
    (hσ : ∀ (y : T') J J', Good M y J → Good M' y J' →
      om w y J J' (p' ≫ iB') * (om w y J J' p')⁻¹ * val σ' p' y J' = ∏ i, val σ (p' ≫ pr i) y J)
    (ev : EvenAlong we iT s σ) :
    EvenAlong we' iT' (GeneratorPullback.boxGen L prG _ _ (fun i => GeneratorPullback.pullAlong L (prG i) (prG i) _ _ _ (hG i) s)) σ' := by
  intro jS' jT' _ cT V h₁ h₂ h₃ h₄
  refine unit_ext fun z hz => ?_
  obtain ⟨k₁, k₂⟩ := GlobalTheory.EvenPull.even_stalk we'
    (GeneratorPullback.boxGen L prG _ _ (fun i => GeneratorPullback.pullAlong L (prG i) (prG i) _ _ _ (hG i) s)) σ' jS' jT' V h₁ h₂ h₃ h₄
    (𝟙 T') z hz
  refine k₁.trans (Eq.trans ?_ k₂.symm)
  clear k₁ k₂
  have c₀ : ∀ i k, (![iT', 𝟙 T'] : Fin 2 → _) k ≫ h i = (![h i ≫ iT, h i] : Fin 2 → _) k :=
    fun i => Fin.forall_fin_two.2 ⟨ih i, Category.id_comp _⟩
  have c₁ : ∀ i k, ((![iT', 𝟙 T'] : Fin 2 → _) k ≫ h i) ≫ f = (h i ≫ f) ≫ (![iG, 𝟙 G] : Fin 2 → _) k :=
    fun i => Fin.forall_fin_two.2 ⟨by
      show (iT' ≫ h i) ≫ f = (h i ≫ f) ≫ iG
      rw [ih, Category.assoc, iF, Category.assoc], by
      show (𝟙 T' ≫ h i) ≫ f = (h i ≫ f) ≫ 𝟙 G
      rw [Category.id_comp, Category.comp_id]⟩
  have c₃ : ∀ i k, ((![iT', 𝟙 T'] : Fin 2 → _) k ≫ h i) ≫ p = (h i ≫ p) ≫ (![iB, 𝟙 B] : Fin 2 → _) k :=
    fun i => Fin.forall_fin_two.2 ⟨by
      show (iT' ≫ h i) ≫ p = (h i ≫ p) ≫ iB
      rw [ih, Category.assoc, iP, Category.assoc], by
      show (𝟙 T' ≫ h i) ≫ p = (h i ≫ p) ≫ 𝟙 B
      rw [Category.id_comp, Category.comp_id]⟩
  have mL : ∀ k i, (![iG, 𝟙 G] : Fin 2 → (G ⟶ G)) k ((h i ≫ f) z) ∈ L.U (jS' k i) := fun k i => by
    have a : ((f' ≫ (![iG', 𝟙 G'] : Fin 2 → (G' ⟶ G')) k) ≫ prG i) z ∈ L.U (jS' k i) :=
      Set.mem_iInter.1 (Set.mem_iInter.1 (h₄ hz) k) i
    rw [Category.assoc, hG, ← Category.assoc, ← hF] at a
    exact a
  have HM : ∀ J J', Good M z J → Good M' z J' →
      (∏ k, om w z J J' (p' ≫ (![iB', 𝟙 B'] : Fin 2 → _) k) ^ (![1, -1] : Fin 2 → ℤ) k) * val σ' p' z J' =
        ∏ i, val σ (h i ≫ p) z J := fun J J' hJ hJ' => by
    have e := hσ z J J' hJ hJ'
    simp only [hE] at e
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, zpow_one, zpow_neg]
    exact e
  have HU : ∀ i J N, Good M z J → Good L z N → val σ (h i ≫ p) z J =
      (∏ k, Geo.Tor.gw we ((![iT', 𝟙 T'] : Fin 2 → _) k ≫ h i) z (J ((h i ≫ p) ≫ (![iB, 𝟙 B] : Fin 2 → _) k))
        (fun _ => N ((h i ≫ f) ≫ (![iG, 𝟙 G] : Fin 2 → _) k)) ^ (![1, -1] : Fin 2 → ℤ) k) * val s (h i ≫ f) z N :=
    fun i J N hJ hN => by
      simp only [c₀]
      exact ev.stalk iF iP (h i) z _ _
        (fun a b e => congrArg N ((Category.assoc _ _ _).trans ((congrArg (h i ≫ ·) e).trans
          (Category.assoc _ _ _).symm)))
        (fun a b e => congrArg J ((Category.assoc _ _ _).trans ((congrArg (h i ≫ ·) e).trans
          (Category.assoc _ _ _).symm)))
        (fun k => hN ((h i ≫ f) ≫ (![iG, 𝟙 G] : Fin 2 → _) k)) (fun k => hJ ((h i ≫ p) ≫ (![iB, 𝟙 B] : Fin 2 → _) k))
  have key := rel_box hM hM' hL hwe Q hF hE (K := Fin 2) (ε := ![1, -1]) z ![iT', 𝟙 T'] hs σ σ' p'
    (fun i => h i ≫ p) (fun i => h i ≫ f) c₁
    (Fin.forall_fin_two.2 ⟨iP', (Category.id_comp _).trans (Category.comp_id _).symm⟩) c₃ HM HU
    jS' jT' cT (fun k => Set.mem_iInter.1 (h₁ hz) k) mL
  have e := gm_box_pull L prG prG hG (fun _ => s) f' z jS' (h₄ hz)
  rw [Fin.prod_univ_two] at key
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg, hF] at key
  rw [Category.id_comp, Category.id_comp, Category.id_comp]
  refine Eq.trans ?_ (congrArg₂ (· * ·) rfl e).symm
  rw [key, mul_right_comm, inv_mul_cancel_right]

end GlobalTheory.PowUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxIso
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowerThickIso

section General

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_res gm_pull gm_div gm_linComb gm_pull_g gm_self mem_pull PGen isGen_iff glue_unit
  exists_chart)

variable {B B' G G' Ge Ge' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {j : ℕ}
  {pr : Fin j → (B' ⟶ B)} {prG : Fin j → (G' ⟶ G)} {pG : Ge ⟶ B} {pG' : Ge' ⟶ B'} {fG : Ge ⟶ G} {fG' : Ge' ⟶ G'}
  {h : Fin j → (Ge' ⟶ Ge)}

theorem gm_box_g {Z : Scheme.{0}} (ψ : Z ⟶ B') (z : Z) (a b : Fin j → M.ι) (ha : ∀ i, pr i (ψ z) ∈ M.U (a i))
    (hb : ∀ i, pr i (ψ z) ∈ M.U (b i)) :
    gm ψ z (LB.wchart M pr a ⊓ LB.wchart M pr b) ((LB.LinComb M pr (fun _ => 1)).g a b) =
      ∏ i, gm (ψ ≫ pr i) z (M.U (a i) ⊓ M.U (b i)) (M.g (a i) (b i)) :=
  (gm_linComb M pr (fun _ => 1) ψ z a b (Set.mem_iInter.2 ha) (Set.mem_iInter.2 hb)).trans
    (Finset.prod_congr rfl fun _ _ => zpow_one _)

theorem bw_change {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} (hw : w.IsGen) {Z : Scheme.{0}} (ψ : Z ⟶ B') (z : Z)
    (a b : Fin j → M.ι) (k k' : M'.ι) (ha : ∀ i, pr i (ψ z) ∈ M.U (a i)) (hb : ∀ i, pr i (ψ z) ∈ M.U (b i))
    (hk : ψ z ∈ M'.U k) (hk' : ψ z ∈ M'.U k') :
    bw w ψ z a k = (∏ i, gm (ψ ≫ pr i) z (M.U (a i) ⊓ M.U (b i)) (M.g (a i) (b i))) *
      (gm ψ z _ (M'.g k k'))⁻¹ * bw w ψ z b k' := by
  have hm : ψ z ∈ LB.wchart M pr a ⊓ M'.U k ⊓ (LB.wchart M pr b ⊓ M'.U k') :=
    ⟨⟨Set.mem_iInter.2 ha, hk⟩, Set.mem_iInter.2 hb, hk'⟩
  have e := congrArg (gm ψ z (LB.wchart M pr a ⊓ M'.U k ⊓ (LB.wchart M pr b ⊓ M'.U k'))) (hw (a, k) (b, k'))
  have e' := (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div M' (LB.LinComb M pr (fun _ => 1)) ψ z (a, k) (b, k') hm) (gm_res ψ z _ hm _))))
  rw [← gm_box_g ψ z a b ha hb]
  exact e'

def germ (pG' : Ge' ⟶ B') (h : Fin j → (Ge' ⟶ Ge)) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1)))
    (we : LB.Iso (L.pull fG) (M.pull pG)) {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι) (jM' : M'.ι)
    (jL : Fin j → L.ι) : (Z.presheaf.stalk z)ˣ :=
  (bw w (r ≫ pG') z jM jM')⁻¹ * ∏ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i)

theorem germ_change (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : w.IsGen) (hwe : PGen we)
    {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM kM : Fin j → M.ι) (jM' kM' : M'.ι) (jL kL : Fin j → L.ι)
    (a₁ : ∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) (a₂ : pG' (r z) ∈ M'.U jM') (a₃ : ∀ i, prG i (fG' (r z)) ∈ L.U (jL i))
    (b₁ : ∀ i, pr i (pG' (r z)) ∈ M.U (kM i)) (b₂ : pG' (r z) ∈ M'.U kM') (b₃ : ∀ i, prG i (fG' (r z)) ∈ L.U (kL i)) :
    germ pG' h w we r z jM jM' jL =
      gm (r ≫ pG') z _ (M'.g jM' kM') *
        (∏ i, gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i)))⁻¹ *
        germ pG' h w we r z kM kM' kL := by
  have p₁ : ∀ i, pG (h i (r z)) = pr i (pG' (r z)) := fun i => congrArg (fun g => g (r z)) (e₁ i).symm
  have p₂ : ∀ i, fG (h i (r z)) = prG i (fG' (r z)) := fun i => congrArg (fun g => g (r z)) (e₂ i)
  have a := bw_change hw (r ≫ pG') z jM kM jM' kM' a₁ b₁ a₂ b₂
  have c : ∀ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i) =
      gm ((r ≫ pG') ≫ pr i) z (M.U (jM i) ⊓ M.U (kM i)) (M.g (jM i) (kM i)) *
        (gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i)))⁻¹ *
        Geo.Tor.gw we (r ≫ h i) z (kM i) (fun _ => kL i) := fun i => by
    have c₃ : fG (h i (r z)) ∈ L.U (jL i) := p₂ i ▸ a₃ i
    have d₃ : fG (h i (r z)) ∈ L.U (kL i) := p₂ i ▸ b₃ i
    have c₁ : pG (h i (r z)) ∈ M.U (jM i) := p₁ i ▸ a₁ i
    have d₁ : pG (h i (r z)) ∈ M.U (kM i) := p₁ i ▸ b₁ i
    have c := hwe Z (r ≫ h i) z (jM i) (kM i) (fun _ => jL i) (fun _ => kL i) c₁ d₁ (mem_pull.2 c₃) (mem_pull.2 d₃)
    rw [gm_pull_g L fG (r ≫ h i) z (fun _ => jL i) (fun _ => kL i) (mem_pull.2 c₃) (mem_pull.2 d₃),
      Category.assoc, Category.assoc, ← e₁, e₂] at c
    rw [Category.assoc, Category.assoc]
    exact c
  unfold germ
  rw [a, Finset.prod_congr rfl fun i _ => c i, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  generalize (∏ i, gm ((r ≫ pG') ≫ pr i) z (M.U (jM i) ⊓ M.U (kM i)) (M.g (jM i) (kM i))) = A
  generalize (∏ i, gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i))) = C
  generalize gm (r ≫ pG') z _ (M'.g jM' kM') = A'
  generalize bw w (r ≫ pG') z kM kM' = P
  generalize (∏ i, Geo.Tor.gw we (r ≫ h i) z (kM i) (fun _ => kL i)) = R
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_unit (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : w.IsGen) (hwe : PGen we)
    (jM' : M'.ι) (jL : Fin j → L.ι) :
    ∃ s : Γ(Ge', (M'.pull pG').U (fun _ => jM') ⊓ ((LB.LinComb L prG (fun _ => 1)).pull fG').U (fun _ => jL))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι), (∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) →
        pG' (r z) ∈ M'.U jM' → (∀ i, prG i (fG' (r z)) ∈ L.U (jL i)) →
        gm r z _ s = germ pG' h w we r z jM jM' jL := by
  have p₁ : ∀ i x, pG (h i x) = pr i (pG' x) := fun i x => congrArg (fun g => g x) (e₁ i).symm
  have p₂ : ∀ i x, fG (h i x) = prG i (fG' x) := fun i x => congrArg (fun g => g x) (e₂ i)
  obtain ⟨W, hW⟩ : ∃ W : (Fin j → M.ι) → Ge'.Opens, ∀ a x, x ∈ W a ↔
      (∀ i, pr i (pG' x) ∈ M.U (a i)) ∧ pG' x ∈ M'.U jM' ∧ ∀ i, prG i (fG' x) ∈ L.U (jL i) :=
    ⟨fun a => pG' ⁻¹ᵁ LB.wchart M pr a ⊓ (pG' ⁻¹ᵁ M'.U jM' ⊓ fG' ⁻¹ᵁ LB.wchart L prG jL),
      fun _ _ => and_congr Set.mem_iInter (and_congr Iff.rfl Set.mem_iInter)⟩
  have l₀ : ∀ a, W a ≤ (M'.pull pG').U (fun _ => jM') ⊓ ((LB.LinComb L prG (fun _ => 1)).pull fG').U (fun _ => jL) :=
    fun a x hx => ⟨mem_pull.2 ((hW a x).1 hx).2.1, mem_pull.2 (Set.mem_iInter.2 ((hW a x).1 hx).2.2)⟩
  have l₁ : ∀ a, W a ≤ pG' ⁻¹ᵁ (LB.wchart M pr a ⊓ M'.U jM') := fun a x hx =>
    ⟨Set.mem_iInter.2 ((hW a x).1 hx).1, ((hW a x).1 hx).2.1⟩
  have l₂ : ∀ a i, W a ≤ h i ⁻¹ᵁ ((M.pull pG).U (fun _ => a i) ⊓ (L.pull fG).U (fun _ => jL i)) := fun a i x hx =>
    ⟨mem_pull.2 ((p₁ i x).symm ▸ ((hW a x).1 hx).1 i), mem_pull.2 ((p₂ i x).symm ▸ ((hW a x).1 hx).2.2 i)⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ a, Γ(Ge', W a)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (a : Fin j → M.ι), r z ∈ W a →
      gm r z (W a) (u a) = germ pG' h w we r z a jM' jL :=
    ⟨fun a => (res (l₁ a) (pullU pG' _ (w.s (a, jM'))))⁻¹ *
        ∏ i, res (l₂ a i) (pullU (h i) _ (we.s (fun _ => a i, fun _ => jL i))),
      fun Z r z a hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹)
        ((gm_res r z (l₁ a) hz _).trans (gm_pull r pG' z _ (l₁ a hz) _)))) ((map_prod _ _ _).trans
          (Finset.prod_congr rfl fun i _ =>
            (gm_res r z (l₂ a i) hz _).trans (gm_pull r (h i) z _ (l₂ a i hz) _))))⟩
  obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
      choose a ha using fun i => exists_chart hM (pr i (pG' x))
      exact TopologicalSpace.Opens.mem_iSup.2
        ⟨a, (hW a x).2 ⟨ha, mem_pull.1 hx.1, Set.mem_iInter.1 (mem_pull.1 hx.2)⟩⟩) u
    (fun a a' x hx => by
      have h₁ := (hW a x).1 hx.1
      have h₂ := (hW a' x).1 hx.2
      have k := germ_change e₁ e₂ hw hwe (𝟙 Ge') x a a' jM' jM' jL jL h₁.1 h₁.2.1 h₁.2.2 h₂.1 h₂.2.1 h₂.2.2
      rw [gm_self hM' (𝟙 Ge' ≫ pG') x h₁.2.1, Finset.prod_eq_one fun i _ =>
        gm_self hL ((𝟙 Ge' ≫ fG') ≫ prG i) x (h₁.2.2 i), inv_one, _root_.one_mul, _root_.one_mul] at k
      exact (hu _ (𝟙 Ge') x a hx.1).trans (k.trans (hu _ (𝟙 Ge') x a' hx.2).symm))
  refine ⟨s, fun Z r z jM a₁ a₂ a₃ => ?_⟩
  have hz := (hW jM (r z)).2 ⟨a₁, a₂, a₃⟩
  exact (gm_res r z (l₀ jM) hz s).symm.trans ((congrArg (gm r z (W jM)) (hs jM)).trans (hu Z r z jM hz))

theorem exists_box_iso (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (we : LB.Iso (L.pull fG) (M.pull pG)) (hw : w.IsGen)
    (hwe : we.IsGen) :
    ∃ we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull fG') (M'.pull pG'), we'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι) (jM' : M'.ι) (jL : Fin j → L.ι),
        (∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) → pG' (r z) ∈ M'.U jM' → (∀ i, prG i (fG' (r z)) ∈ L.U (jL i)) →
        bw w (r ≫ pG') z jM jM' * Geo.Tor.gw we' r z jM' (fun _ => jL) =
          ∏ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i) := by
  rw [isGen_iff] at hwe
  choose s hs using exists_unit hM hM' hL e₁ e₂ hw hwe
  refine ⟨⟨fun p => s (p.1 PUnit.unit) (p.2 PUnit.unit)⟩, (isGen_iff _).2 ?_, fun Z r z jM jM' jL a₁ a₂ a₃ => ?_⟩
  · intro Z r z l l' k k' a₂ b₂ a₄ b₄
    choose a ha using fun i => exists_chart hM (pr i (pG' (r z)))
    have a₄' : ∀ i, prG i (fG' (r z)) ∈ L.U (k PUnit.unit i) := Set.mem_iInter.1 (mem_pull.1 a₄)
    have b₄' : ∀ i, prG i (fG' (r z)) ∈ L.U (k' PUnit.unit i) := Set.mem_iInter.1 (mem_pull.1 b₄)
    have c := germ_change e₁ e₂ hw hwe r z a a l l' _ _ ha a₂ a₄' ha b₂ b₄'
    rw [← hs l _ Z r z a ha a₂ a₄', ← hs l' _ Z r z a ha b₂ b₄', ← gm_box_g (r ≫ fG') z _ _ a₄' b₄'] at c
    rw [gm_pull_g (LB.LinComb L prG (fun _ => 1)) fG' r z k k' a₄ b₄]
    exact c
  · exact (congrArg (bw w (r ≫ pG') z jM jM' * ·) (hs jM' jL Z r z jM a₁ a₂ a₃)).trans
      (mul_inv_cancel_left _ _)

end General

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (e : ℕ) (g : GtCoord I D.toPre e G) (g' : GtCoord I D'.toPre e G'), (∀ i, g'.pG.left ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ g.pG.left) → ∀ (L : LB G.left), L.IsLB → ∀ w : LB.Iso (L.pull (fstG I e G).left) (D.toPre.P.L.pull g.pG.left), w.IsGen → ∃ w' : LB.Iso ((boxLB L pG.pr).pull (fstG I e G').left) (D'.toPre.P.L.pull g'.pG.left), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : Fin j → L.ι), (∀ i, (pD.pw.pr i).left (g'.pG.left (r z)) ∈ D.toPre.P.L.U (jM i)) → g'.pG.left (r z) ∈ D'.toPre.P.L.U jM' → (∀ i, (pG.pr i).left ((fstG I e G').left (r z)) ∈ L.U (jL i)) → bw pD.w (r ≫ g'.pG.left) z jM jM' * Geo.Tor.gw w' r z jM' (fun _ => jL) = ∏ i, Geo.Tor.gw w (r ≫ ((Over.pullback (thick R I e)).map (pG.pr i)).left) z (jM i) (fun _ => jL i) := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG e g g' hq L hL w hw
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  exact exists_box_iso (Ge := (thickObj R I e G).left) (Ge' := (thickObj R I e G').left) (h := rhoE I pG e)
    (pG := g.pG.left) (pG' := g'.pG.left) (fG := fGl I G e) (fG' := fGl I G' e)
    D.toPre.P.isLB D'.toPre.P.isLB hL hq hρ pD.w w pD.w_gen hw

end GlobalTheory.PowerThickIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UniformisationPowerWithoutExpansion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowUnif

section Level

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig GlobalTheory.WCub

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

omit [IsDomain R] [IsCommMonObj G] [IsCommMonObj G'] in
theorem rho_fst (pG : IsPowGrp G' G j) (e : ℕ) (i : Fin j) :
    rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := pullback.lift_fst _ _ _

omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem thickMap_rho (pG : IsPowGrp G' G j) (e : ℕ) (i : Fin j) :
    thickMap R I e G' ≫ rhoE I pG (e + 1) i = rhoE I pG e i ≫ thickMap R I e G := by
  have : Mono (fGl I G (e + 1)) := mono_fstG I (e + 1) G
  have a : thickMap R I e G ≫ fGl I G (e + 1) = fGl I G e := thickMap_fstG I e G
  have a' : thickMap R I e G' ≫ fGl I G' (e + 1) = fGl I G' e := thickMap_fstG I e G'
  rw [← cancel_mono (fGl I G (e + 1)), Category.assoc, Category.assoc, rho_fst, a, rho_fst, ← Category.assoc, a']

theorem thickMap_pG (pD : IsPowDeg D'.toPre D.toPre j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G) (e : ℕ)
    (g₀ : GtCoord I D'.toPre e G') (g₁ : GtCoord I D'.toPre (e + 1) G')
    (h₀ : ∀ i, g₀.pG.left ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ (U.gt e).pG.left)
    (h₁ : ∀ i, g₁.pG.left ≫ (pD.pw.pr i).left = rhoE I pG (e + 1) i ≫ (U.gt (e + 1)).pG.left) :
    thickMap R I e G' ≫ g₁.pG.left = g₀.pG.left := by
  have h : LevelCompat.thickMapOver I e G' ≫ g₁.pG = g₀.pG := pD.pw.lim.hom_ext fun ⟨i⟩ =>
    Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg (thickMap R I e G' ≫ ·) (h₁ i)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (U.gt (e + 1)).pG.left) (thickMap_rho pG e i)).trans
        ((Category.assoc _ _ _).trans ((congrArg (rhoE I pG e i ≫ ·) (U.gt_q e)).trans (h₀ i).symm))))))
  exact congrArg (fun z => z.left) h

variable (pD : IsPowDeg D'.toPre D.toPre j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G)
    (e : ℕ) (g' : GtCoord I D'.toPre e G')
    (hq : ∀ i, g'.pG.left ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ (U.gt e).pG.left)
    (w' : LB.Iso ((boxLB U.LG.L pG.pr).pull (fstG I e G').left) (D'.toPre.P.L.pull g'.pG.left))
    (Q : BoxSquare (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) pD.w (U.w e) w' (rhoE I pG e))
include hq Q

theorem rig_level : RigAlong (T := (thickObj R I e G').left) w' (eSec (thickObj R I e G')) (thick R I e)
    (boxRig pG U.LG.L U.LG.rig) D'.toPre.rig := by
  obtain ⟨b, b₁, b₂⟩ := pD.w_rig
  exact rig_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) D.toPre.P.isLB D'.toPre.P.isLB
    U.LG.isLB (U.w_gen e) Q (rho_fst pG e) hq U.LG.rigGen (U.w_rig e)
    (fun i => by
      have := pG.hom i
      exact BoxSymmetry.eSec_comp_hom ((Over.pullback (thick R I e)).map (pG.pr i)))
    (eSec_fstG I e G) (eSec_pG I (U.gt e)) (eSec_pG I g')
    (fun i _ => letI := pG.hom i; (CubeMap.ofHom (pG.pr i)).e_comm) b b₁ b₂

theorem even_level (hG : GlobalFnsSt) : EvenAlong (T := (thickObj R I e G').left) w' (ι[thickObj R I e G']).left
    (boxSym pG U.LG.L U.symG) D'.toPre.sym := by
  have := g'.q_hom
  have := (U.gt e).q_hom
  exact even_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) D.toPre.P.isLB D'.toPre.P.isLB
    U.LG.isLB (U.w_gen e) Q (rho_fst pG e) hq
    (fun i => by
      have := pG.hom i
      exact EvenPull.inv_left_comp ((Over.pullback (thick R I e)).map (pG.pr i)))
    (EvenPull.inv_fst _ G) (EvenPull.inv_hom_fst _ _ (U.gt e).q) (EvenPull.inv_hom_fst _ _ g'.q) (inv_pr pG)
    U.symG U.symG_gen D.toPre.sym D'.toPre.sym
    (fun y J J' hJ hJ' => PsiEvenBox.sym_box hG pD g'.pG.left y hJ hJ') (U.w_even e)

end Level


open GlobalTheory.WCub in
set_option maxHeartbeats 1600000 in
theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G), ∃ (U' : UnifPre I D' A' G') (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)), (∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ wL.IsGen ∧ (∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j) (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)), GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧ LB.Gen.Corr U.LG.L _ _ _ _ b (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))) ∧ (∀ (e : ℕ) (i : Fin j), (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q) ∧ (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i))))) ∧ (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL')))) := by
  intro hG R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U
  obtain ⟨gen, gen_hom, gen_pr, ext⟩ := exists_gen_pow R I j D D' A A' G G' pD pA pG U
  choose gt q_pr t_pr using fun e => GlobalTheory.PowTorusCoord.main hG R I j D D' A A' G G' pD pA pG e (U.gt e)
  have hq : ∀ e i, (gt e).pG.left ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ (U.gt e).pG.left :=
    fun e i => (t_pr e 0).choose i 2
  choose w w_gen Q using fun e => PowerThickIso.main R I j D D' A A' G G' pD pA pG e (U.gt e) (gt e) (hq e)
    U.LG.L U.LG.isLB (U.w e) (U.w_gen e)
  have hL := boxIsLB _ G' G j pG U.LG.L U.LG.isLB
  have hr := boxRigIsGen _ G' G j pG U.LG.L U.LG.rig U.LG.isLB U.LG.rigGen
  obtain ⟨c, hc⟩ := boxCubical _ G' G j pG U.LG U.cubG hL hr
  obtain ⟨s₁, s₂⟩ := boxSym_isSymmetry _ G' G j pG U.LG.L U.symG U.LG.isLB U.symG_gen U.symG_rig
  have gq := fun e => thickMap_pG pD pG U e (gt e) (gt (e + 1)) (hq e) (hq (e + 1))
  refine ⟨{
      smooth := (PowGrp.powers _ G' G j pG).1 U.smooth
      separated := (PowGrp.powers _ G' G j pG).2.1 U.separated
      gen := gen
      gen_hom := gen_hom
      LG := ⟨boxLB U.LG.L pG.pr, boxRig pG U.LG.L U.LG.rig, hL, hr⟩
      cubG := c
      symG := boxSym pG U.LG.L U.symG
      symG_gen := s₁
      symG_rig := s₂
      ext := ext
      gt := gt
      gt_q := gq
      gt_t := fun e χ => corr_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left)
        (T₁ := (thickObj R I (e + 1) G).left) (T₁' := (thickObj R I (e + 1) G').left)
        D.toPre.P.isLB D'.toPre.P.isLB pD.w (thickMap_rho pG e) (t_pr e χ).choose
        (t_pr (e + 1) χ).choose (LevelCompat.thickMap_Oφ (gt e) (gt (e + 1)) (gq e) χ) (t_pr e χ).choose_spec
        (t_pr (e + 1) χ).choose_spec (fun i => U.gt_t e _)
      w := w
      w_gen := w_gen
      w_rig := fun e => rig_level pD pG U e (gt e) (hq e) (w e) (Q e)
      w_even := fun e => even_level pD pG U e (gt e) (hq e) (w e) (Q e) hG
      w_cub := fun e T x jL jM _ cM => (clause_iff (tri (thick R I e) (gt e).pG x) (tri (thick R I e) (fstG I e G') x)
        (fun k : thK => (psum (thickObj R I e G') x k.down).left) _ _ _ (D'.toPre.cub.t.s jM) (c.t.s jL)
        (fun k => (w e).s (fun _ => jM k, fun _ => jL k)) thε).2 fun y hB hL _ => by
          rw [hc]
          exact cub_box hG pD pG U e (gt e) (hq e) (w e) (Q e) T x jL jM cM y hB hL
      w_compat := fun e => compat_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left)
        (T₁ := (thickObj R I (e + 1) G).left) (T₁' := (thickObj R I (e + 1) G').left)
        D.toPre.P.isLB (Q e) (Q (e + 1)) (U.w_compat e) (UnifPullRig.thickMap_fstG I e G) (U.gt_q e)
        (UnifPullRig.thickMap_fstG I e G') (gq e) (rho_fst pG e) (hq e) (thickMap_rho pG e) },
    Geo.Tor.idIso _, gen_pr, Geo.Tor.idIso_isGen hL, ?_, q_pr, t_pr, fun e jNM jM' jL' jNL => ?_⟩
  · exact idIso_rig U.LG.isLB U.LG.rig (fun i _ => letI := pG.hom i; (CubeMap.ofHom (pG.pr i)).e_comm) hr
  · exact square_res (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) D'.toPre.P.isLB (w_gen e) (Q e)
      jNM jM' jL' jNL _ _ _ _ _

end GlobalTheory.PowUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UniformisationPowerWithoutExpansionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.uniformisation_power_without_expansion : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G), ∃ (U' : UnifPre I D' A' G') (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)), (∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ wL.IsGen ∧ (∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j) (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)), GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧ LB.Gen.Corr U.LG.L _ _ _ _ b (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))) ∧ (∀ (e : ℕ) (i : Fin j), (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q) ∧ (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i))))) ∧ (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL')))) := by
  first | exact @GlobalTheory.PowUnif.main | exact GlobalTheory.PowUnif.main | (intros; apply GlobalTheory.PowUnif.main <;> assumption)
end
