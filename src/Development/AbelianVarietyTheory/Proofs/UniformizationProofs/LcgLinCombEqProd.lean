module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LcgLinCombEqProd
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

lemma boxGen_overlap_le {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (a b : K → (LB.LinComb L F (fun _ => 1)).ι) (i : J) :
    LB.wchart (LB.LinComb L F (fun _ => 1)) φ a ⊓ LB.wchart (LB.LinComb L F (fun _ => 1)) φ b ≤
      LB.wchart (L.pull (F i)) φ (fun k _ => a k i) ⊓
        LB.wchart (L.pull (F i)) φ (fun k _ => b k i) := by
  have key : ∀ c : K → (LB.LinComb L F (fun _ => 1)).ι,
      LB.wchart (LB.LinComb L F (fun _ => 1)) φ c ≤ LB.wchart (L.pull (F i)) φ (fun k _ => c k i) := by
    intro c y hy
    simp only [LB.wchart, LB.pull, LB.LinComb, TopologicalSpace.Opens.mem_mk, Set.mem_iInter,
      Set.mem_preimage, SetLike.mem_coe] at hy ⊢
    intro k _
    exact hy k i
  exact inf_le_inf (key a) (key b)

lemma lcg_linComb_eq_prod {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (a b : K → (LB.LinComb L F (fun _ => 1)).ι) :
    LB.lcg (LB.LinComb L F (fun _ => 1)) φ ε a b =
      ∏ i, res (boxGen_overlap_le L F φ a b i)
        (LB.lcg (L.pull (F i)) φ ε (fun k _ => a k i) (fun k _ => b k i)) := by
  show (∏ k, (res _ (pullU (φ k) (LB.wchart L F (a k) ⊓ LB.wchart L F (b k))
      (LB.lcg L F (fun _ => 1) (a k) (b k)))) ^ ε k) =
    ∏ i, res _ (∏ k, (res _ (pullU (φ k)
      (LB.wchart L (fun _ : PUnit => F i) (fun _ => a k i) ⊓ LB.wchart L (fun _ : PUnit => F i) (fun _ => b k i))
      (LB.lcg L (fun _ : PUnit => F i) (fun _ => 1) (fun _ => a k i) (fun _ => b k i)))) ^ ε k)
  simp only [LB.lcg, map_prod, map_zpow, zpow_one, Finset.univ_unique, Finset.prod_singleton,
    ReciprocityTheory.ChartRestriction.G.DVR.pullU_res, ← Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_
  congr 1
  repeat erw [ReciprocityTheory.ChartRestriction.G.DVR.res_res']

private lemma res_res_eq {Z : Scheme.{0}} {U V V' W : Z.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (h₃ : V' ≤ U)
    (h₄ : W ≤ V') (x : Γ(Z, U)ˣ) : res h₂ (res h₁ x) = res h₄ (res h₃ x) := by
  rw [ReciprocityTheory.ChartRestriction.G.DVR.res_res', ReciprocityTheory.ChartRestriction.G.DVR.res_res']

theorem isGen_boxGen {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (ht : ∀ i, (t i).IsGen) :
    (GeneratorPullback.boxGen L F φ ε t).IsGen := by
  intro a b
  have hg : ((LB.LinComb L F (fun _ => 1)).LinComb φ ε).g a b = _ := lcg_linComb_eq_prod L F φ ε a b
  rw [hg]
  show res (U := LB.wchart (LB.LinComb L F (fun _ => 1)) φ a)
      (V := LB.wchart (LB.LinComb L F (fun _ => 1)) φ a ⊓ LB.wchart (LB.LinComb L F (fun _ => 1)) φ b) _
      (∏ i, res (V := LB.wchart (LB.LinComb L F (fun _ => 1)) φ a) _ ((t i).s fun k _ => a k i)) =
    (∏ i, res (boxGen_overlap_le L F φ a b i)
      (LB.lcg (L.pull (F i)) φ ε (fun k _ => a k i) (fun k _ => b k i))) *
      res (U := LB.wchart (LB.LinComb L F (fun _ => 1)) φ b)
        (V := LB.wchart (LB.LinComb L F (fun _ => 1)) φ a ⊓ LB.wchart (LB.LinComb L F (fun _ => 1)) φ b) _
        (∏ i, res (V := LB.wchart (LB.LinComb L F (fun _ => 1)) φ b) _ ((t i).s fun k _ => b k i))
  simp only [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e := (congrArg (res (boxGen_overlap_le L F φ a b i))
    ((ht i) (fun k _ => a k i) (fun k _ => b k i))).trans (map_mul _ _ _)
  refine (res_res_eq _ _ _ _ _).trans (e.trans ?_)
  congr 1
  exact res_res_eq _ _ _ _ _

theorem boxIsLB (S : Scheme.{0}) : BoxIsLBSt (S := S) := by
  intro G' G _ _ j p L hL
  exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB L hL _ _

theorem boxRigIsGen (S : Scheme.{0}) : BoxRigIsGenSt (S := S) := by
  intro G' G _ _ _ _ j p L r hL hr
  refine isGen_boxGen _ _ _ _ _ (fun i => ?_)
  have := p.hom i
  exact LBxP.isGen_pullAlong L (p.pr i).left (𝟙 _) (fun _ : PUnit => eSec G)
    (fun _ => 1) (fun _ => eSec G') (fun _ => (CubeMap.ofHom (p.pr i)).e_comm) r hr

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourthSide
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.FourthSide

theorem gm_pull_g {X X' Y : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (f : Y ⟶ X') (y : Y) (j j' : L.ι)
    (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j') :
    gm f y ((L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j')) ((L.pull F).g (fun _ => j) (fun _ => j')) =
      gm (f ≫ F) y _ (L.g j j') := by
  have hp : f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j') := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g j j'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f F y (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _)

variable {B B' G G' Ge Ge' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {L' : LB G'}
  {Φ : B' ⟶ B} {Ψ : G' ⟶ G} {pG : Ge ⟶ B} {pG' : Ge' ⟶ B'} {fG : Ge ⟶ G} {fG' : Ge' ⟶ G'} {h : Ge' ⟶ Ge}

def germ (pG' : Ge' ⟶ B') (fG' : Ge' ⟶ G') (h : Ge' ⟶ Ge) (w : LB.Iso M' (M.pull Φ)) (wL : LB.Iso L' (L.pull Ψ))
    (we : LB.Iso (L.pull fG) (M.pull pG)) {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι)
    (jL' : L'.ι) : (Z.presheaf.stalk z)ˣ :=
  (gw w (r ≫ pG') z jM jM')⁻¹ * (gw we (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ fG') z jL jL')

theorem germ_change (e₁ : pG' ≫ Φ = h ≫ pG) (e₂ : h ≫ fG = fG' ≫ Ψ) {w : LB.Iso M' (M.pull Φ)}
    {wL : LB.Iso L' (L.pull Ψ)} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : PGen w) (hwL : PGen wL) (hwe : PGen we)
    {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM kM : M.ι) (jM' kM' : M'.ι) (jL kL : L.ι) (jL' kL' : L'.ι)
    (a₁ : Φ (pG' (r z)) ∈ M.U jM) (a₂ : pG' (r z) ∈ M'.U jM') (a₃ : Ψ (fG' (r z)) ∈ L.U jL)
    (a₄ : fG' (r z) ∈ L'.U jL') (b₁ : Φ (pG' (r z)) ∈ M.U kM) (b₂ : pG' (r z) ∈ M'.U kM')
    (b₃ : Ψ (fG' (r z)) ∈ L.U kL) (b₄ : fG' (r z) ∈ L'.U kL') :
    germ pG' fG' h w wL we r z jM jM' jL jL' =
      gm (r ≫ pG') z _ (M'.g jM' kM') * (gm (r ≫ fG') z _ (L'.g jL' kL'))⁻¹ *
        germ pG' fG' h w wL we r z kM kM' kL kL' := by
  have p₁ : pG (h (r z)) = Φ (pG' (r z)) := congrArg (fun g => g (r z)) e₁.symm
  have p₂ : fG (h (r z)) = Ψ (fG' (r z)) := congrArg (fun g => g (r z)) e₂
  have c₃ : fG (h (r z)) ∈ L.U jL := p₂ ▸ a₃
  have d₃ : fG (h (r z)) ∈ L.U kL := p₂ ▸ b₃
  have c₁ : pG (h (r z)) ∈ M.U jM := p₁ ▸ a₁
  have d₁ : pG (h (r z)) ∈ M.U kM := p₁ ▸ b₁
  have a := hw Z (r ≫ pG') z jM kM jM' kM' a₁ b₁ a₂ b₂
  have b := hwL Z (r ≫ fG') z jL kL jL' kL' a₃ b₃ a₄ b₄
  have c := hwe Z (r ≫ h) z jM kM (fun _ => jL) (fun _ => kL) c₁ d₁ (mem_pull.2 c₃) (mem_pull.2 d₃)
  rw [gm_pull_g L fG (r ≫ h) z jL kL c₃ d₃, Category.assoc, Category.assoc, ← e₁, e₂] at c
  rw [Category.assoc] at a b
  unfold germ
  rw [a, b, c]
  generalize gm (r ≫ pG' ≫ Φ) z _ (M.g jM kM) = A
  generalize gm (r ≫ fG' ≫ Ψ) z _ (L.g jL kL) = C
  generalize gm (r ≫ pG') z _ (M'.g jM' kM') = A'
  generalize gm (r ≫ fG') z _ (L'.g jL' kL') = C'
  generalize gw w (r ≫ pG') z kM kM' = P
  generalize gw wL (r ≫ fG') z kL kL' = Q
  generalize gw we (r ≫ h) z kM (fun _ => kL) = R
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_unit (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB)
    (e₁ : pG' ≫ Φ = h ≫ pG) (e₂ : h ≫ fG = fG' ≫ Ψ) {w : LB.Iso M' (M.pull Φ)}
    {wL : LB.Iso L' (L.pull Ψ)} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : PGen w) (hwL : PGen wL) (hwe : PGen we)
    (jM' : M'.ι) (jL' : L'.ι) :
    ∃ s : Γ(Ge', (M'.pull pG').U (fun _ => jM') ⊓ (L'.pull fG').U (fun _ => jL'))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jL : L.ι), Φ (pG' (r z)) ∈ M.U jM →
        pG' (r z) ∈ M'.U jM' → Ψ (fG' (r z)) ∈ L.U jL → fG' (r z) ∈ L'.U jL' →
        gm r z _ s = germ pG' fG' h w wL we r z jM jM' jL jL' := by
  have p₁ : ∀ x, pG (h x) = Φ (pG' x) := fun x => congrArg (fun g => g x) e₁.symm
  have p₂ : ∀ x, fG (h x) = Ψ (fG' x) := fun x => congrArg (fun g => g x) e₂
  obtain ⟨W, hW⟩ : ∃ W : M.ι × L.ι → Ge'.Opens, ∀ i x, x ∈ W i ↔
      Φ (pG' x) ∈ M.U i.1 ∧ pG' x ∈ M'.U jM' ∧ Ψ (fG' x) ∈ L.U i.2 ∧ fG' x ∈ L'.U jL' :=
    ⟨fun i => pG' ⁻¹ᵁ (Φ ⁻¹ᵁ M.U i.1) ⊓ (pG' ⁻¹ᵁ M'.U jM' ⊓ (fG' ⁻¹ᵁ (Ψ ⁻¹ᵁ L.U i.2) ⊓ fG' ⁻¹ᵁ L'.U jL')),
      fun _ _ => Iff.rfl⟩
  have l₀ : ∀ i, W i ≤ (M'.pull pG').U (fun _ => jM') ⊓ (L'.pull fG').U (fun _ => jL') := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).2.1, mem_pull.2 ((hW i x).1 hx).2.2.2⟩
  have l₁ : ∀ i, W i ≤ pG' ⁻¹ᵁ ((M.pull Φ).U (fun _ => i.1) ⊓ M'.U jM') := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.1⟩
  have l₂ : ∀ i, W i ≤ h ⁻¹ᵁ ((M.pull pG).U (fun _ => i.1) ⊓ (L.pull fG).U (fun _ => i.2)) := fun i x hx =>
    ⟨mem_pull.2 ((p₁ x).symm ▸ ((hW i x).1 hx).1), mem_pull.2 ((p₂ x).symm ▸ ((hW i x).1 hx).2.2.1)⟩
  have l₃ : ∀ i, W i ≤ fG' ⁻¹ᵁ ((L.pull Ψ).U (fun _ => i.2) ⊓ L'.U jL') := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).2.2.1, ((hW i x).1 hx).2.2.2⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(Ge', W i)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (i : M.ι × L.ι), r z ∈ W i →
      gm r z (W i) (u i) = germ pG' fG' h w wL we r z i.1 jM' i.2 jL' :=
    ⟨fun i => (res (l₁ i) (pullU pG' _ (w.s (fun _ => i.1, jM'))))⁻¹ *
        (res (l₂ i) (pullU h _ (we.s (fun _ => i.1, fun _ => i.2))) *
          res (l₃ i) (pullU fG' _ (wL.s (fun _ => i.2, jL')))),
      fun Z r z i hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹)
        ((gm_res r z (l₁ i) hz _).trans (gm_pull r pG' z _ (l₁ i hz) _)))) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res r z (l₂ i) hz _).trans (gm_pull r h z _ (l₂ i hz) _))
          ((gm_res r z (l₃ i) hz _).trans (gm_pull r fG' z _ (l₃ i hz) _)))))⟩
  obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hM (Φ (pG' x))
      obtain ⟨j, hj⟩ := exists_chart hL (Ψ (fG' x))
      exact Opens.mem_iSup.2 ⟨(i, j), (hW (i, j) x).2 ⟨hi, mem_pull.1 hx.1, hj, mem_pull.1 hx.2⟩⟩) u
    (fun i i' x hx => by
      have h₁ := (hW i x).1 hx.1
      have h₂ := (hW i' x).1 hx.2
      have k := germ_change e₁ e₂ hw hwL hwe (𝟙 Ge') x i.1 i'.1 jM' jM' i.2 i'.2 jL' jL' h₁.1 h₁.2.1 h₁.2.2.1
        h₁.2.2.2 h₂.1 h₂.2.1 h₂.2.2.1 h₂.2.2.2
      rw [gm_self hM' (𝟙 Ge' ≫ pG') x h₁.2.1, gm_self hL' (𝟙 Ge' ≫ fG') x h₁.2.2.2, inv_one, one_mul, one_mul] at k
      exact (hu _ (𝟙 Ge') x i hx.1).trans (k.trans (hu _ (𝟙 Ge') x i' hx.2).symm))
  refine ⟨s, fun Z r z jM jL a₁ a₂ a₃ a₄ => ?_⟩
  have hz := (hW (jM, jL) (r z)).2 ⟨a₁, a₂, a₃, a₄⟩
  exact (gm_res r z (l₀ (jM, jL)) hz s).symm.trans
    ((congrArg (gm r z (W (jM, jL))) (hs (jM, jL))).trans (hu Z r z (jM, jL) hz))

theorem exists_fourth_side (B B' G G' Ge Ge' : Scheme.{0}) (M : LB B) (M' : LB B') (L : LB G) (L' : LB G')
    (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB) (Φ : B' ⟶ B) (Ψ : G' ⟶ G) (pG : Ge ⟶ B)
    (pG' : Ge' ⟶ B') (fG : Ge ⟶ G) (fG' : Ge' ⟶ G') (h : Ge' ⟶ Ge) (e₁ : pG' ≫ Φ = h ≫ pG)
    (e₂ : h ≫ fG = fG' ≫ Ψ) (w : LB.Iso M' (M.pull Φ)) (wL : LB.Iso L' (L.pull Ψ))
    (we : LB.Iso (L.pull fG) (M.pull pG)) (hw : w.IsGen) (hwL : wL.IsGen) (hwe : we.IsGen) :
    ∃ we' : LB.Iso (L'.pull fG') (M'.pull pG'), we'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
        Φ (pG' (r z)) ∈ M.U jM → pG' (r z) ∈ M'.U jM' → Ψ (fG' (r z)) ∈ L.U jL → fG' (r z) ∈ L'.U jL' →
        gw w (r ≫ pG') z jM jM' * gw we' r z jM' (fun _ => jL') =
          gw we (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ fG') z jL jL' := by
  rw [isGen_iff] at hw hwL hwe
  choose s hs using exists_unit hM hM' hL hL' e₁ e₂ hw hwL hwe
  refine ⟨⟨fun p => s (p.1 PUnit.unit) (p.2 PUnit.unit)⟩, (isGen_iff _).2 ?_, fun Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  · intro Z r z j j' k k' a₂ b₂ a₄ b₄
    obtain ⟨i, hi⟩ := exists_chart hM (Φ (pG' (r z)))
    obtain ⟨l, hl⟩ := exists_chart hL (Ψ (fG' (r z)))
    have a₄' := mem_pull.1 a₄
    have b₄' := mem_pull.1 b₄
    have c := germ_change e₁ e₂ hw hwL hwe r z i i j j' l l _ _ hi a₂ hl a₄' hi b₂ hl b₄'
    rw [← hs j _ Z r z i l hi a₂ hl a₄', ← hs j' _ Z r z i l hi b₂ hl b₄',
      ← gm_pull_g L' fG' r z _ _ a₄' b₄'] at c
    exact c
  · exact (congrArg (gw w (r ≫ pG') z jM jM' * ·) (hs jM' jL' Z r z jM jL a₁ a₂ a₃ a₄)).trans
      (mul_inv_cancel_left _ _)

end GlobalTheory.FourthSide
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullGenBoxGen
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxCubical

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_res)

section Box

variable {X X' Y Z : Scheme.{0}} (L : LB X) {J K K' : Type} [Fintype J] [Fintype K] [Fintype K']

lemma gU_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε))
    (jj : K → (LB.LinComb L F (fun _ => 1)).ι) (y : Y)
    (hy : y ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) φ jj) :
    gU y hy ((GeneratorPullback.boxGen L F φ ε t).s jj) =
      ∏ i, gU y (GeneratorPullback.box_le L F φ jj i hy) ((t i).s (fun k _ => jj k i)) := by
  show gU y hy (∏ i, _) = _
  exact (map_prod (gU y hy) _ _).trans (Finset.prod_congr rfl fun i _ => gU_res _ _ _ _)

lemma gU_pullGen (M : LB X') (φ : K → (Y ⟶ X')) (ε : K → ℤ) (t : LB.Gen (LB.LinComb M φ ε))
    (a : Z ⟶ Y) (j : K → M.ι) (z : Z) (hz : z ∈ LB.wchart M (fun k => a ≫ φ k) j) :
    gU z hz ((LB.pullGen M φ ε t a).s j) =
      Units.map (RingHom.toMonoidHom (a.stalkMap z).hom)
        (gU (a.base z) (LBxP.wpl M φ a j hz) (t.s j)) :=
  (gU_res _ _ _ _).trans (gU_pullU a _ z _ _)

lemma pullGen_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (a : Z ⟶ Y) :
    LB.pullGen (LB.LinComb L F (fun _ => 1)) φ ε (GeneratorPullback.boxGen L F φ ε t) a =
      GeneratorPullback.boxGen L F (fun k => a ≫ φ k) ε (fun i => LB.pullGen (L.pull (F i)) φ ε (t i) a) := by
  apply LBxP.gen_ext
  intro jj z hz
  refine (gU_pullGen _ φ ε _ a jj z hz).trans ?_
  refine Eq.trans ?_ (gU_boxGen L F (fun k => a ≫ φ k) ε _ jj z hz).symm
  refine (congrArg (Units.map (RingHom.toMonoidHom (a.stalkMap z).hom))
    (gU_boxGen L F φ ε t jj (a.base z) _)).trans ?_
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  exact (gU_pullGen (L.pull (F i)) φ ε (t i) a _ z _).symm

lemma mulGen_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε))
    (t' : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ' ε')) :
    LB.mulGen (LB.LinComb L F (fun _ => 1)) φ ε φ' ε' (GeneratorPullback.boxGen L F φ ε t)
        (GeneratorPullback.boxGen L F φ' ε' t') =
      GeneratorPullback.boxGen L F (Sum.elim φ φ') (Sum.elim ε ε')
        (fun i => LB.mulGen (L.pull (F i)) φ ε φ' ε' (t i) (t' i)) := by
  apply LBxP.gen_ext
  intro jj y hy
  refine (LBxP.gU_mulGen _ φ ε φ' ε' _ _ jj y hy).trans ?_
  refine Eq.trans ?_ (gU_boxGen L F (Sum.elim φ φ') (Sum.elim ε ε') _ jj y hy).symm
  refine (congrArg₂ (· * ·) (gU_boxGen L F φ ε t _ y _) (gU_boxGen L F φ' ε' t' _ y _)).trans ?_
  refine Finset.prod_mul_distrib.symm.trans (Finset.prod_congr rfl fun i _ => ?_)
  exact (LBxP.gU_mulGen (L.pull (F i)) φ ε φ' ε' (t i) (t' i) (fun k _ => jj k i) y _).symm

lemma oneGen_boxGen (F : J → (X' ⟶ X)) :
    LB.oneGen (Y := Y) (LB.LinComb L F (fun _ => 1)) =
      GeneratorPullback.boxGen L F PEmpty.elim PEmpty.elim (fun i => LB.oneGen (L.pull (F i))) := by
  apply LBxP.gen_ext
  intro jj y hy
  refine Eq.trans ?_ (gU_boxGen L F PEmpty.elim PEmpty.elim _ jj y hy).symm
  refine (map_one (gU y hy)).trans (Finset.prod_eq_one fun i _ => ?_).symm
  exact map_one (gU y _)

lemma corr_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε))
    (t' : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ' ε'))
    (h : ∀ i, LB.Gen.Corr (L.pull (F i)) φ ε φ' ε' (t i) (t' i)) :
    LB.Gen.Corr (LB.LinComb L F (fun _ => 1)) φ ε φ' ε' (GeneratorPullback.boxGen L F φ ε t)
      (GeneratorPullback.boxGen L F φ' ε' t') := by
  intro jj jj' h1 h2 h12
  apply unit_ext
  intro y hy
  refine ((gU_res _ y hy _).trans (gU_boxGen L F φ ε t jj y hy.1)).trans ?_
  refine Eq.trans ?_ ((gU_res _ y hy _).trans (gU_boxGen L F φ' ε' t' jj' y hy.2)).symm
  refine Finset.prod_congr rfl fun i _ => ?_
  have H := h i (fun k _ => jj k i) (fun k _ => jj' k i)
    (fun k₁ k₂ e => funext fun _ => congrFun (h1 k₁ k₂ e) i)
    (fun k₁ k₂ e => funext fun _ => congrFun (h2 k₁ k₂ e) i)
    (fun k₁ k₂ e => funext fun _ => congrFun (h12 k₁ k₂ e) i)
  have hy' : y ∈ LB.wchart (L.pull (F i)) φ (fun k _ => jj k i) ⊓
      LB.wchart (L.pull (F i)) φ' (fun k _ => jj' k i) :=
    ⟨GeneratorPullback.box_le L F φ jj i hy.1, GeneratorPullback.box_le L F φ' jj' i hy.2⟩
  exact (gU_res _ y hy' _).symm.trans ((congrArg (gU y hy') H).trans (gU_res _ y hy' _))

lemma gU_pull_lcg (F : J → (X' ⟶ X)) (δ : J → ℤ) (a : Y ⟶ X') (i j : J → L.ι) (y : Y)
    (hy : y ∈ a ⁻¹ᵁ ((LB.LinComb L F δ).U i ⊓ (LB.LinComb L F δ).U j)) :
    gU y hy (pullU a _ ((LB.LinComb L F δ).g i j)) =
      ∏ n, (gU y (show y ∈ (a ≫ F n) ⁻¹ᵁ (L.U (i n) ⊓ L.U (j n)) from
        ⟨LB.wchart_le L F i n hy.1, LB.wchart_le L F j n hy.2⟩)
        (pullU (a ≫ F n) _ (L.g (i n) (j n)))) ^ δ n := by
  refine (gU_pullU a _ y hy _).trans ?_
  refine (congrArg (Units.map (RingHom.toMonoidHom (a.stalkMap y).hom))
    (LBxP.gU_lcg L F δ i j (a.base y) hy)).trans ?_
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun n _ => ?_)
  refine (map_zpow _ _ _).trans (congrArg (· ^ δ n) ?_)
  refine (gU_pullU a _ y _ _).symm.trans ?_
  exact LBxP.gU_pullU_comp a (F n) _ _ y _ _

lemma isGen_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (h : ∀ i, (t i).IsGen) :
    (GeneratorPullback.boxGen L F φ ε t).IsGen := by
  intro jj jj'
  apply unit_ext
  intro y hy
  have hy' : ∀ i, y ∈ (LB.LinComb (L.pull (F i)) φ ε).U (fun k _ => jj k i) ⊓
      (LB.LinComb (L.pull (F i)) φ ε).U (fun k _ => jj' k i) := fun i =>
    ⟨GeneratorPullback.box_le L F φ jj i hy.1, GeneratorPullback.box_le L F φ jj' i hy.2⟩
  have hg : gU y hy ((LB.LinComb (LB.LinComb L F (fun _ => 1)) φ ε).g jj jj') =
      ∏ i, gU y (hy' i) ((LB.LinComb (L.pull (F i)) φ ε).g (fun k _ => jj k i)
        (fun k _ => jj' k i)) := by
    refine (LBxP.gU_lcg _ φ ε jj jj' y hy).trans ?_
    refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ =>
      LBxP.gU_lcg (L.pull (F i)) φ ε _ _ y (hy' i)).symm
    refine Eq.trans ?_ Finset.prod_comm
    refine Finset.prod_congr rfl fun k _ => ?_
    refine Eq.trans ?_ (Finset.prod_zpow _ _ _).symm
    refine congrArg (· ^ ε k) ?_
    refine (gU_pull_lcg L F (fun _ => 1) (φ k) (jj k) (jj' k) y _).trans ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    refine (zpow_one _).trans ?_
    exact (LBxP.gU_pull_g L (F i) (φ k) (fun _ => jj k i) (fun _ => jj' k i) y _ _).symm
  refine ((gU_res _ y hy _).trans (gU_boxGen L F φ ε t jj y hy.1)).trans ?_
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) hg
    ((gU_res _ y hy _).trans (gU_boxGen L F φ ε t jj' y hy.2)))).symm
  refine Eq.trans ?_ Finset.prod_mul_distrib
  refine Finset.prod_congr rfl fun i _ => ?_
  have H := congrArg (gU y (hy' i)) (h i (fun k _ => jj k i) (fun k _ => jj' k i))
  exact (gU_res _ y (hy' i) _).symm.trans (H.trans ((map_mul _ _ _).trans
    (congrArg (_ * ·) (gU_res _ y (hy' i) _))))

end Box

section Cub

variable {S : Scheme.{0}} {G' : Over S} [GrpObj G'] [IsCommMonObj G'] {X : Scheme.{0}}
  {J : Type} [Fintype J]

def prodCubical (L : LB X) (F : J → (G'.left ⟶ X))
    (r : ∀ i, LB.Gen ((L.pull (F i)).pull (eSec G'))) (hL : ∀ i, (L.pull (F i)).IsLB)
    (hr : ∀ i, (r i).IsGen) (c : ∀ i, CubicalStr G' ⟨L.pull (F i), r i, hL i, hr i⟩)
    (r' : LB.Gen ((LB.LinComb L F (fun _ => 1)).pull (eSec G')))
    (hL' : (LB.LinComb L F (fun _ => 1)).IsLB) (hr' : r'.IsGen) :
    CubicalStr G' ⟨LB.LinComb L F (fun _ => 1), r', hL', hr'⟩ where
  t := GeneratorPullback.boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t)
  isGen := isGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) (fun i => (c i).isGen)
  face := fun n =>
    LBxP.corr_of_eq (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)
      (oneGen_boxGen L F) (corr_boxGen L F _ _ _ _ _ _ (fun i => (c i).face n))
  cubeSymmetric_swap_first :=
    LBxP.corr_of_eq rfl (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)
      (corr_boxGen L F (thφ G' (x3 G')) thε _ _ (fun i => (c i).t) _ (fun i => (c i).cubeSymmetric_swap_first))
  cubeSymmetric_swap_last :=
    LBxP.corr_of_eq rfl (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)
      (corr_boxGen L F (thφ G' (x3 G')) thε _ _ (fun i => (c i).t) _ (fun i => (c i).cubeSymmetric_swap_last))
  cocycle :=
    LBxP.corr_of_eq
      ((congrArg₂ (LB.mulGen (LB.LinComb L F (fun _ => 1)) _ _ _ _)
        (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)
        (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)).trans
        (mulGen_boxGen L F _ _ _ _ _ _))
      ((congrArg₂ (LB.mulGen (LB.LinComb L F (fun _ => 1)) _ _ _ _)
        (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)
        (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)).trans
        (mulGen_boxGen L F _ _ _ _ _ _))
      (corr_boxGen L F _ _ _ _ _ _ (fun i => (c i).cocycle))

end Cub

end GlobalTheory.BoxCubical

namespace GlobalTheory

theorem boxCubical : ∀ S : Scheme.{0}, BoxCubicalSt (S := S) := by
  intro S G' G _ _ _ _ j p L c hL hr
  let m : Fin j → CubeMap G' G := fun i => letI := p.hom i; CubeMap.ofHom (p.pr i)
  have hLi : ∀ i, (L.L.pull (m i).F).IsLB := fun i => LB.isLB_pull L.isLB (m i).F
  have hri : ∀ i, ((m i).rigPull L.L L.rig).IsGen := fun i =>
    LBxP.isGen_pullAlong L.L (m i).F (m i).e (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec G') (fun _ => (m i).e_comm) L.rig L.rigGen
  exact ⟨BoxCubical.prodCubical L.L (fun i => (p.pr i).left) (fun i => (m i).rigPull L.L L.rig)
    hLi hri (fun i => CubePf.cubical (m i) L c (hLi i) (hri i)) _ hL hr, rfl⟩

end GlobalTheory
end
end
