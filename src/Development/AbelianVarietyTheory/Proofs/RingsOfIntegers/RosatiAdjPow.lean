module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RosatiAdjPow
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.RosatiPower

variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G]

private theorem padd_comp_eq_padd_comp_of_isMonHom {T H K : Over S} [GrpObj H] [GrpObj K] (q : H ⟶ K) [IsMonHom q]
    (a b : T ⟶ H) : padd H a b ≫ q = padd K (a ≫ q) (b ≫ q) := by
  unfold padd
  simp [IsMonHom.mul_hom]

private theorem comp_padd_eq_padd_comp {T T' H : Over S} [GrpObj H] (x : T ⟶ T') (a b : T' ⟶ H) :
    x ≫ padd H a b = padd H (x ≫ a) (x ≫ b) := by
  unfold padd
  first
  | simp
  | simp [Hom.mul_def]
  | simp [comp_lift_assoc]

theorem rosatiφ_comp (q : G' ⟶ G) [IsMonHom q] {f g : G ⟶ G} {f' g' : G' ⟶ G'}
    (hf : f' ≫ q = q ≫ f) (hg : g' ≫ q = q ≫ g) (k : Fin 6) :
    rosatiφ G' f' g' k ≫ q.left = (q ⊗ₘ q).left ≫ rosatiφ G f g k := by
  have e1 : (q ⊗ₘ q) ≫ fst G G = fst G' G' ≫ q := by simp
  have e2 : (q ⊗ₘ q) ≫ snd G G = snd G' G' ≫ q := by simp
  have key : ∀ (a : G' ⊗ G' ⟶ G') (b : G ⊗ G ⟶ G), a ≫ q = (q ⊗ₘ q) ≫ b →
      a.left ≫ q.left = (q ⊗ₘ q).left ≫ b.left := by
    intro a b h
    rw [← Over.comp_left, h, Over.comp_left]
  fin_cases k <;> refine key _ _ ?_ <;>
    simp only [padd_comp_eq_padd_comp_of_isMonHom, comp_padd_eq_padd_comp, Category.assoc, hf, hg, reassoc_of% e1, reassoc_of% e2, e1, e2]

theorem exists_restrict {A B : Over S} (q : A ⟶ B) (U : S.Opens) :
    ∃ n : (A.hom ⁻¹ᵁ U).toScheme ⟶ (B.hom ⁻¹ᵁ U).toScheme,
      n ≫ (B.hom ⁻¹ᵁ U).ι = (A.hom ⁻¹ᵁ U).ι ≫ q.left := by
  refine ⟨q.left.resLE (B.hom ⁻¹ᵁ U) (A.hom ⁻¹ᵁ U) ?_, Scheme.Hom.resLE_comp_ι _ _⟩
  intro x hx
  rw [← Over.w q] at hx
  exact hx

private theorem exists_isGen_of_isGen_iso_of_isGen {X : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB)
    (u : LB.Iso A B) (hu : u.IsGen) (t : LB.Gen B) (ht : t.IsGen) : ∃ t' : LB.Gen A, t'.IsGen := by
  classical
  let tS : LB.Sec B := ⟨fun b => (t.s b : Γ(X, B.U b)), fun i j => by
    have e := congrArg Units.val (ht i j)
    simpa [res] using e⟩
  have hunit : ∀ a, IsUnit ((secOfIso tS hu hA hB).f a) := by
    intro a
    apply RingedSpace.isUnit_of_isUnit_germ X.toRingedSpace
    intro x hx
    have hc := cover_inf hB a hx
    rw [TopologicalSpace.Opens.mem_iSup] at hc
    obtain ⟨b, hb⟩ := hc
    have hsp := secOfIso_spec tS hu hA hB a b
    have e1 : X.presheaf.germ (A.U a) x hx ((secOfIso tS hu hA hB).f a) =
        X.presheaf.germ (A.U a ⊓ B.U b) x hb (rs inf_le_left ((secOfIso tS hu hA hB).f a)) := by
      simp only [rs, TopCat.Presheaf.germ_res_apply]
    change IsUnit (X.presheaf.germ (A.U a) x hx ((secOfIso tS hu hA hB).f a))
    rw [e1, hsp, isoCand, map_mul]
    refine IsUnit.mul ((Units.isUnit _).map _) ?_
    simp only [rs, TopCat.Presheaf.germ_res_apply]
    exact (Units.isUnit (t.s b)).map _
  refine ⟨⟨fun a => (hunit a).unit⟩, fun i j => ?_⟩
  apply Units.ext
  have e := (secOfIso tS hu hA hB).compat i j
  simpa [res] using e

end GlobalTheory.RosatiPower


open GlobalTheory.RosatiPower in
theorem GlobalTheory.rosatiAdj_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → Geo.Tor.LBIso L' (boxLB L p.pr) → ∀ (f g : G ⟶ G) (f' g' : G' ⟶ G'), (∀ i, f' ≫ p.pr i = p.pr i ≫ f) → (∀ i, g' ≫ p.pr i = p.pr i ≫ g) → RosatiAdj G L f g → RosatiAdj G' L' f' g' := by
  intro S G' G _ _ _ _ j p L L' hL hL' hiso f g f' g' hf hg hr
  have hm : ∀ i, IsMonHom (p.pr i) := p.hom
  unfold RosatiAdj at hr ⊢
  unfold boxLB at hiso
  intro s
  obtain ⟨U, hsU, t, ht⟩ := hr s
  refine ⟨U, hsU, ?_⟩
  obtain ⟨w, hw⟩ := hiso
  have hn : ∀ i, ∃ n : ((G' ⊗ G').hom ⁻¹ᵁ U).toScheme ⟶ ((G ⊗ G).hom ⁻¹ᵁ U).toScheme,
      n ≫ ((G ⊗ G).hom ⁻¹ᵁ U).ι = ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ (p.pr i ⊗ₘ p.pr i).left :=
    fun i => exists_restrict (p.pr i ⊗ₘ p.pr i) U
  choose n hn using hn
  have hc : ∀ i k, (((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) ≫ (p.pr i).left =
      n i ≫ ((G ⊗ G).hom ⁻¹ᵁ U).ι ≫ rosatiφ G f g k := by
    intro i k
    rw [Category.assoc, rosatiφ_comp (p.pr i) (hf i) (hg i) k, ← Category.assoc, ← hn i, Category.assoc]
  let t' : ∀ i, ((L.pull (p.pr i).left).LinComb
      (fun k => ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) rosatiε).Gen :=
    fun i => GeneratorPullback.pullAlong L (p.pr i).left (n i) _ rosatiε _ (hc i) t
  have ht' : ∀ i, (t' i).IsGen := by
    intro i
    exact LBxP.isGen_pullAlong L (Over.Hom.left (p.pr i)) (n i) _ rosatiε _ (hc i) t ht
  have hb := GlobalTheory.BoxSymmetry.isGen_boxGen L (fun i => (p.pr i).left) _ rosatiε t' ht'
  have hwi := linCombIso_isGen w hw (fun k => ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) rosatiε
  exact exists_isGen_of_isGen_iso_of_isGen (linComb_isLB _ hL' _ _) (linComb_isLB _ (linComb_isLB _ hL _ _) _ _) _ hwi _ hb

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RatioTrans
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CubBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

section Box

variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem bw_trans {Z : Scheme.{0}} (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen) (ψ : Z ⟶ X') (z : Z)
    {jN jN' : Fin j → M.ι} {k k' : M'.ι} (h₁ : ψ z ∈ LB.wchart M pr jN) (h₁' : ψ z ∈ LB.wchart M pr jN')
    (h₂ : ψ z ∈ M'.U k) (h₂' : ψ z ∈ M'.U k') :
    bw w ψ z jN k = (∏ i, gm (ψ ≫ pr i) z (M.U (jN i) ⊓ M.U (jN' i)) (M.g (jN i) (jN' i))) *
      (gm ψ z (M'.U k ⊓ M'.U k') (M'.g k k'))⁻¹ * bw w ψ z jN' k' := by
  have hm : ψ z ∈ LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k') := ⟨⟨h₁, h₂⟩, h₁', h₂'⟩
  have e := congrArg (gm ψ z (LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k'))) (hw (jN, k) (jN', k'))
  have d := gm_div M' (LB.LinComb M pr (fun _ => 1)) ψ z (jN, k) (jN', k') hm
  have l := gm_linComb M pr (fun _ => 1) ψ z jN jN' h₁ h₁'
  simp only [zpow_one] at l
  refine (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (d.trans (congrArg₂ (· * ·) l rfl)) (gm_res ψ z _ hm _))))

variable {K : Type} [Fintype K]

def ratio (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ}
    (ρ : Fin j → (Y ⟶ Y₀)) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ ε))
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (jN : K → Fin j → M.ι) (jM : K → M'.ι) : (Z.presheaf.stalk z)ˣ :=
  (∏ a, bw w (r ≫ φ' a) z (jN a) (jM a) ^ ε a) * gm r z (LB.wchart M' φ' jM) (t'.s jM) *
    (∏ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => jN a i)) (t.s (fun a => jN a i)))⁻¹

theorem chart_le {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a) (jN : K → Fin j → M.ι) (i : Fin j) :
    LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ≤ ρ i ⁻¹ᵁ LB.wchart M φ (fun a => jN a i) := fun y hy =>
  Set.mem_iInter.2 fun a => (congrArg (fun g : Y ⟶ X => g y ∈ M.U (jN a i)) (hψ i a)).mp
    (Set.mem_iInter.1 (Set.mem_iInter.1 hy a) i)

theorem ratio_trans (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)} (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {jN jN' : K → Fin j → M.ι} {jM jM' : K → M'.ι}
    (h : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)
    (h' : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN' ⊓ LB.wchart M' φ' jM') :
    ratio w ρ t' t r z jN jM = ratio w ρ t' t r z jN' jM' := by
  have e₁ : ∀ a, bw w (r ≫ φ' a) z (jN a) (jM a) = _ := fun a => bw_trans w hw (r ≫ φ' a) z (jN' := jN' a) (k' := jM' a)
    (Set.mem_iInter.1 h.1 a) (Set.mem_iInter.1 h'.1 a) (Set.mem_iInter.1 h.2 a) (Set.mem_iInter.1 h'.2 a)
  have e₂ := gen_trans ht' r z h.2 h'.2
  have e₃ : ∀ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => jN a i)) (t.s (fun a => jN a i)) = _ := fun i =>
    gen_trans ht (r ≫ ρ i) z (j' := fun a => jN' a i) (chart_le hψ jN i h.1) (chart_le hψ jN' i h'.1)
  have e₄ : ∏ i, trF (L := M) φ ε (r ≫ ρ i) z (fun a => jN a i) (fun a => jN' a i) =
      ∏ a, (∏ i, gm ((r ≫ φ' a) ≫ pr i) z (M.U (jN a i) ⊓ M.U (jN' a i)) (M.g (jN a i) (jN' a i))) ^ ε a := by
    unfold trF
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Category.assoc, Category.assoc, hψ]
  unfold ratio
  rw [Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) (e₁ a), e₂, Finset.prod_congr rfl fun i _ => e₃ i,
    Finset.prod_mul_distrib, e₄]
  simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, trF]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_ratio (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)} (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ ε)) (jN : K → Fin j → M.ι) (jM : K → M'.ι) :
    ∃ u : Γ(Y, LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
        r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM →
        gm r z _ u = ratio w ρ t' t r z jN jM := by
  refine ⟨@id (Γ(Y, LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ)
      ((LB.linCombIso w φ' ε).s (jN, jM)) * res inf_le_right (t'.s jM) *
      (∏ i, res (inf_le_left.trans (chart_le hψ jN i)) (pullU (ρ i) _ (t.s (fun a => jN a i))))⁻¹,
    fun Z r z hz => ?_⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linCombIso w φ' ε r z jN jM hz) (gm_res r z _ hz _))) ((map_inv _ _).trans (congrArg (·⁻¹)
      ((map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => ?_)))))
  exact (gm_res r z _ hz _).trans (gm_pull r (ρ i) z _ (chart_le hψ jN i hz.1) _)

theorem box_unique {S₀ : Scheme.{0}} (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1)))
    (hw : w.IsGen) {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen)
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (h : ∀ y J J', Good M y J → Good M' y J' →
      (∏ a, bw w (e ≫ φ' a) y (fun i => J ((e ≫ φ' a) ≫ pr i)) (J' (e ≫ φ' a)) ^ ε a) * val t' e y J' =
        ∏ i, val t (e ≫ ρ i) y J)
    (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J') (hJ : Good M z J) (hJ' : Good M' z J') :
    (∏ a, bw w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' =
      ∏ i, val t (r ≫ ρ i) z J := by
  choose u hu using fun q : (K → Fin j → M.ι) × (K → M'.ι) => exists_ratio w hψ t' t q.1 q.2
  obtain ⟨s, hs⟩ := glue_unit (⊤ : Y.Opens)
    (fun q : (K → Fin j → M.ι) × (K → M'.ι) =>
      LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' q.1 ⊓ LB.wchart M' φ' q.2) (fun _ => le_top)
    (fun y _ => by
      choose a ha using fun k i => exists_chart hM (pr i (φ' k y))
      choose b hb using fun k => exists_chart hM' (φ' k y)
      exact Opens.mem_iSup.2 ⟨(a, b), Set.mem_iInter.2 fun k => Set.mem_iInter.2 (ha k), Set.mem_iInter.2 hb⟩) u
    (fun q q' y hy => (hu q _ (𝟙 Y) y hy.1).trans ((ratio_trans w hw hψ ht' ht (𝟙 Y) y hy.1 hy.2).trans
      (hu q' _ (𝟙 Y) y hy.2).symm))
  obtain ⟨a, ha⟩ := hp s.val
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J'), Good M z J → Good M' z J' →
      ((∏ a, bw w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' *
        (∏ i, val t (r ≫ ρ i) z J)⁻¹).val = gs (r ≫ p) z ⊤ a := by
    intro Z r z J J' hJ hJ'
    have hm : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) ⊓
        LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) :=
      ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((r ≫ φ' a) ≫ pr i), hJ'.mem _ r⟩
    have v : ∏ i, val t (r ≫ ρ i) z J = ∏ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => J ((r ≫ φ' a) ≫ pr i)))
        (t.s (fun a => J ((r ≫ φ' a) ≫ pr i))) := Finset.prod_congr rfl fun i _ =>
      val_of t _ z J _ (fun a => by rw [Category.assoc, Category.assoc, hψ])
    rw [v]
    have w₁ := (hu (fun a i => J ((r ≫ φ' a) ≫ pr i), fun a => J' (r ≫ φ' a)) Z r z hm).symm.trans
      ((congrArg (gm r z _) (hs _).symm).trans (gm_res r z le_top hm s))
    exact (congrArg Units.val w₁).trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  have a1 : a = 1 := fn_ext fun y _ => by
    choose I hI using fun χ : S₀ ⟶ X => exists_chart hM (χ y)
    choose I' hI' using fun χ : S₀ ⟶ X' => exists_chart hM' (χ y)
    have := key _ e y I I' hI hI'
    rw [h y I I' hI hI', mul_inv_cancel, he] at this
    rw [← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
  have := key Z r z J J' hJ hJ'
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

end Box

theorem cubV_box : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (T : Over (Spec (CommRingCat.of R))) (z : T.left) (J J'), Geo.Tor.Good D.P.L z J → Geo.Tor.Good D'.P.L z J' → ∀ x x' y : T ⟶ D'.P.A, (let om := fun p : T ⟶ D'.P.A => bw pD.w p.left z (fun i => J (p.left ≫ (pD.pw.pr i).left)) (J' p.left); Geo.Tor.cubV D'.cub z J' x x' y * (om (x * x' * y) * (om (x * x'))⁻¹ * (om (x * y))⁻¹ * (om (x' * y))⁻¹ * om x * om x' * om y * (om 1)⁻¹) = ∏ i, Geo.Tor.cubV D.cub z J (x ≫ pD.pw.pr i) (x' ≫ pD.pw.pr i) (y ≫ pD.pw.pr i)) := by
  intro hG R _ _ j D D' pD T z J J' hJ hJ' x x' y om
  let ρ : Fin j → ((G3 D'.P.A).left ⟶ (G3 D.P.A).left) := fun i => (pD.pw.pr i ⊗ₘ pD.pw.pr i ⊗ₘ pD.pw.pr i).left
  have hψ : ∀ i a, thφ D'.P.A (x3 D'.P.A) a ≫ (pD.pw.pr i).left = ρ i ≫ thφ D.P.A (x3 D.P.A) a := fun i a =>
    letI := pD.pw.hom i
    (CubeMap.ofHom (pD.pw.pr i)).psum_comm a.down
  have hρ : ∀ {T : Over (Spec (CommRingCat.of R))} (a b c : T ⟶ D'.P.A) i, (lift a (lift b c)).left ≫ ρ i =
      (lift (a ≫ pD.pw.pr i) (lift (b ≫ pD.pw.pr i) (c ≫ pD.pw.pr i))).left := fun a b c i => by
    show (lift a (lift b c) ≫ (pD.pw.pr i ⊗ₘ pD.pw.pr i ⊗ₘ pD.pw.pr i)).left = _
    rw [lift_map, lift_map]
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D'.P.A := lift 1 (lift 1 1)
  have sj : Function.Surjective
      ((snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2)
  have he : e.left ≫ (snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := box_unique (pr := fun i => (pD.pw.pr i).left) D.P.isLB D'.P.isLB pD.w pD.w_gen (ε := thε) hψ
    D'.cub.isGen D.cub.isGen _ e.left he sj (fun s I I' hI hI' => by
      have C' : IsCub (cubV D'.cub s I') := isCub_cubV D'.cub hI'
      have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) s I) := isCub_cubV D.cub hI
      have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) 1 1
        (fun q => bw pD.w q s (fun i => I (q ≫ (pD.pw.pr i).left)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine (congrArg₂ (· * ·) p (C'.face 1 1)).trans (Eq.trans (by simp) (Finset.prod_eq_one fun i _ => ?_).symm)
      have := pD.pw.hom i
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) ≫ pD.pw.pr i = 1 := by simp [Hom.one_def]
      rw [show e.left ≫ ρ i = _ from hρ 1 1 1 i, o]
      exact C.face 1 1) _ (lift x (lift x' y)).left z J J' hJ hJ'
  have p := prod_cub x x' y (fun q => bw pD.w q z (fun i => J (q ≫ (pD.pw.pr i).left)) (J' q))
  refine (mul_comm _ _).trans ((congrArg₂ (· * ·) p rfl).symm.trans (key.trans (Finset.prod_congr rfl fun i _ => ?_)))
  rw [hρ]; rfl

end GlobalTheory.CubBox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValFinProdGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.QBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

def kap (ξ : Spec (CommRingCat.of (FractionRing V))) :
    FractionRing V →+* (Spec (CommRingCat.of (FractionRing V))).presheaf.stalk ξ :=
  ((Spec (CommRingCat.of (FractionRing V))).presheaf.germ ⊤ ξ trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom

omit [IsDiscreteValuationRing V] in
theorem gs_scal (ξ : Spec (CommRingCat.of (FractionRing V))) (c : FractionRing V) :
    gs (𝟙 _) ξ ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) = kap ξ c := by
  rw [gs_eq _ ξ ⊤ trivial]
  rfl

def SV (ϖ : V) (ξ : Spec (CommRingCat.of (FractionRing V)))
    (s : ((Spec (CommRingCat.of (FractionRing V))).presheaf.stalk ξ)ˣ) (n : ℤ) : Prop :=
  ∃ c, HasVal ϖ c n ∧ s.val = kap ξ c

theorem SV.mul (hϖ : Irreducible ϖ) {ξ : Spec (CommRingCat.of (FractionRing V))} {s t} {n m : ℤ}
    (hs : SV ϖ ξ s n) (ht : SV ϖ ξ t m) : SV ϖ ξ (s * t) (n + m) := by
  obtain ⟨c, ⟨u, hu⟩, hc⟩ := hs
  obtain ⟨d, ⟨v, hv⟩, hd⟩ := ht
  refine ⟨c * d, ⟨u * v, ?_⟩, by rw [Units.val_mul, hc, hd, map_mul]⟩
  rw [hu, hv, zpow_add₀ ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2
      hϖ.ne_zero), Units.val_mul, map_mul]; ring

theorem SV.prod (hϖ : Irreducible ϖ) {ξ : Spec (CommRingCat.of (FractionRing V))} {T : Type} (S : Finset T)
    {s : T → _} {n : T → ℤ} (hs : ∀ i, SV ϖ ξ (s i) (n i)) : SV ϖ ξ (∏ i ∈ S, s i) (∑ i ∈ S, n i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, ⟨1, by simp⟩, by simp⟩
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha]; exact (hs a).mul hϖ ih

theorem SV.unique (hϖ : Irreducible ϖ) {ξ : Spec (CommRingCat.of (FractionRing V))} {s} {n m : ℤ}
    (hs : SV ϖ ξ s n) (ht : SV ϖ ξ s m) : n = m := by
  obtain ⟨c, hc, e⟩ := hs
  obtain ⟨d, hd, e'⟩ := ht
  have : c = d := (kap ξ).injective (e.symm.trans e')
  exact hasVal_unique hϖ hc (this ▸ hd)

theorem sv_unit (ξ : Spec (CommRingCat.of (FractionRing V))) (U : (Spec (CommRingCat.of V)).Opens)
    (hU : (closedPoint V : Spec (CommRingCat.of V)) ∈ U) (a : Γ(Spec (CommRingCat.of V), U)ˣ) :
    SV ϖ ξ (gm (jK V) ξ U a) 0 := by
  obtain rfl := eq_top_of_closedPoint_mem U hU
  refine ⟨algebraMap V _ ((Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom a : Vˣ) : V),
    ⟨_, by rw [zpow_zero, _root_.one_mul]⟩, ?_⟩
  rw [gm_val _ ξ ⊤ trivial]
  have hnat := congrArg (fun f => (CommRingCat.Hom.hom f) ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a.val))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  refine congrArg ((Spec (CommRingCat.of (FractionRing V))).presheaf.germ ⊤ ξ trivial).hom
    (Eq.trans ?_ hnat.symm)
  rw [Iso.hom_inv_id_apply]
  rfl

theorem sv_unit' (ξ : Spec (CommRingCat.of (FractionRing V))) {X : Scheme.{0}} (p : Spec (CommRingCat.of V) ⟶ X)
    (U : X.Opens) (hU : p (closedPoint V) ∈ U) (a : Γ(X, U)ˣ) :
    SV ϖ ξ (gm (jK V ≫ p) ξ U a) 0 := by
  have h : p (jK V ξ) ∈ U := by
    have := eq_top_of_closedPoint_mem (p ⁻¹ᵁ U) hU
    have h2 : jK V ξ ∈ p ⁻¹ᵁ U := by rw [this]; trivial
    exact h2
  rw [← gm_pull (jK V) p ξ U h]
  exact sv_unit ξ _ hU _

theorem sv_gen (hϖ : Irreducible ϖ) (ξ : Spec (CommRingCat.of (FractionRing V))) {X : Scheme.{0}} {L : LB X}
    {Ix : Type} [Fintype Ix]
    {φ : Ix → (Spec (CommRingCat.of V) ⟶ X)} {φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    {hφ : ∀ k, φ' k = jK V ≫ φ k} {ε : Ix → ℤ} {t : LB.Gen (LB.LinComb L φ' ε)} {n : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) {J} (hJ : Good L ξ J)
    (hc : ∀ k, φ k (closedPoint V) ∈ L.U (J (jK V ≫ φ k))) : SV ϖ ξ (val t (𝟙 _) ξ J) n := by
  obtain ⟨e, c, -, hcv, H⟩ := SectionScalarValuation.exists_val_genHasVal hn
  have H1 := H _ (𝟙 _) ξ J hJ
  rw [gs_scal, Category.id_comp] at H1
  obtain ⟨d, ⟨u, hu⟩, hd⟩ : SV ϖ ξ (val e (jK V) ξ J) 0 :=
    sv_unit ξ _ (Set.mem_iInter.2 hc) _
  refine ⟨c * d, ?_, by rw [H1, hd, map_mul]⟩
  rw [hu, zpow_zero, _root_.one_mul]
  exact hasVal_mul_unit hcv u

theorem exists_goodV (ξ : Spec (CommRingCat.of (FractionRing V))) {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (s : X ⟶ Spec (CommRingCat.of V)) [IsSeparated s] :
    ∃ J, Good L ξ J ∧ ∀ p : Spec (CommRingCat.of V) ⟶ X, p ≫ s = 𝟙 _ →
      p (closedPoint V) ∈ L.U (J (jK V ≫ p)) := by
  haveI : IsDominant (jK V) := isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of V) ⟶ X => exists_chart hL (p (closedPoint V))
  obtain ⟨J, hJ, e⟩ := exists_good L hL ξ (K := {p : Spec (CommRingCat.of V) ⟶ X // p ≫ s = 𝟙 _})
    (fun p => jK V ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated s (a.2.trans b.2.symm) (jK V) h))
    (fun p => by
      have := eq_top_of_closedPoint_mem (p.1 ⁻¹ᵁ L.U (pick p.1)) (hpk p.1)
      have h2 : jK V ξ ∈ p.1 ⁻¹ᵁ L.U (pick p.1) := by rw [this]; trivial
      exact h2)
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

section Box

variable {X X' Y : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem mapsAt_val (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (p : Y ⟶ X') (n : ℤ)
    (a : LB.Gen (LB.LinComb M' (K := PUnit) (fun _ => p) (fun _ => n)))
    (b : LB.Gen (LB.LinComb M (K := Fin j) (fun i => p ≫ pr i) (fun _ => n)))
    (H : GeneratorPullback.MapsAt M M' pr w p n a b) (y : Y) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    val b (𝟙 _) y J = bw w p y (fun i => J (p ≫ pr i)) (J' p) ^ n * val a (𝟙 _) y J' := by
  have hm' : p y ∈ LB.wchart M pr (fun i => J (p ≫ pr i)) ⊓ M'.U (J' p) :=
    ⟨Set.mem_iInter.2 fun i => hJ (p ≫ pr i), hJ' p⟩
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ p ⁻¹ᵁ (LB.div (LB.LinComb M pr (fun _ => 1)) M').U (fun i => J (p ≫ pr i), J' p) := hm'
  have E := congrArg (gm (𝟙 Y) y _) (H (fun i => J (p ≫ pr i)) (J' p))
  rw [val_of b _ y J (fun i => J (p ≫ pr i)) (fun i => by rw [Category.id_comp]),
    val_of a _ y J' (fun _ => J' p) (fun i => by rw [Category.id_comp])]
  refine (gm_res _ y _ hm _).symm.trans (E.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans (congrArg (· ^ n) ?_)) (gm_res _ y _ hm _))))
  exact gm_pull (𝟙 Y) p y _ hm' _

theorem val_finProdGen {K I : Type} [Fintype K] [Fintype I] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb M (φ i) (ε i))) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good M z J) :
    val (GeneratorPullback.finProdGen M φ ε t) r z J = ∏ i, val (t i) r z J :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

end Box

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → QForm.IsQ D'.toPre ϖ (fun x => ∑ i, Q (pD.xe x i)) := by
  intro V _ _ _ ϖ hϖ j D D' pD Q hQ x
  obtain ⟨m, hm⟩ := QForm.exists_QVal hϖ D' x
  suffices h : m = ∑ i, Q (pD.xe x i) by rw [h] at hm; exact hm
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing V))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_goodV ξ D.toPre.P.isLB D.toPre.P.A.hom
  obtain ⟨J', hJ', hJc'⟩ := exists_goodV ξ D'.toPre.P.isLB D'.toPre.P.A.hom
  obtain ⟨b, hb, hcorr⟩ := pD.w_psi x
  have e1 := mapsAt_val pD.w _ _ _ b hb ξ hJ hJ'
  have e2 := (val_corr hJ hcorr (𝟙 _)).trans (val_finProdGen _ _ _ _ _ hJ)
  have s1 : SV ϖ ξ (val (D'.toPre.psi x) (𝟙 _) ξ J') m :=
    sv_gen hϖ ξ hm hJ' fun _ => hJc' _ (Over.w _)
  have s2 := SV.prod hϖ Finset.univ fun i : Fin j =>
    sv_gen hϖ ξ (hQ (pD.xe x i)) hJ fun _ => hJc _ (Over.w _)
  have hx : D'.toPre.xK x = jK V ≫ (D'.toPre.c x).left := QForm.ptK_eq _ x
  have s3 : SV ϖ ξ (bw pD.w (D'.toPre.xK x) ξ (fun i => J (D'.toPre.xK x ≫ (pD.pw.pr i).left))
      (J' (D'.toPre.xK x))) 0 := by
    rw [hx]
    refine sv_unit' ξ _ _ ?_ _
    refine ⟨Set.mem_iInter.2 fun i => ?_, hJc' _ (Over.w _)⟩
    exact hJc ((D'.toPre.c x).left ≫ (pD.pw.pr i).left) (QForm.over_sec _ _)
  have s4 := s3.mul hϖ s2
  rw [← e2, zero_add] at s4
  have e3 := e1
  rw [zpow_neg_one, eq_inv_mul_iff_mul_eq] at e3
  exact s1.unique hϖ (e3 ▸ s4)

end GlobalTheory.QBox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalOfPointwise
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxFamScalar

section Generic

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X X' Y Y' W W' Z : Scheme.{0}}

theorem sval_of_secScal {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  unfold GeneratorPullback.SecScal resTop at H
  have hV : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have hW : h (r z) ∈ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hV.2 k
  have hc : LB.Coh L (Sum.elim φ₁ fun k => h ≫ φ₂ k)
      (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k))) := by
    rintro (a | a) (b | b) e <;> simp only [Sum.elim_inl, Sum.elim_inr] at e ⊢ <;> rw [e]
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc]),
    sval_of s₁ r z J (fun k => J (r ≫ φ₁ k)) (fun k => rfl)]
  calc _ = _ := (gs_pull r h z _ hW _).symm
    _ = _ := (gs_res r z _ hV _).symm
    _ = _ := congrArg (gs r z _) (H _ _ hc)
    _ = _ := gs_mul r z _ hV _ _
    _ = _ := congrArg₂ (· * ·) (gs_res r z _ hV _) (gs_res r z _ hV _)

theorem secScal_of_pointwise {L : LB X} (hL : L.IsLB) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ}
    {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : ∀ (y : Y') (J : (Y' ⟶ X) → L.ι), Good L y J →
      sval s₂ (𝟙 Y' ≫ h) y J = gs (𝟙 Y') y ⊤ c * sval s₁ (𝟙 Y') y J) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c := by
  unfold GeneratorPullback.SecScal resTop
  intro j₁ j₂ hc
  apply fn_ext
  intro y hy
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL y (Sum.elim φ₁ fun k => h ≫ φ₂ k) (Sum.elim j₁ j₂) hc (by
    rintro (k | k)
    · exact Set.mem_iInter.1 hy.1 k
    · exact Set.mem_iInter.1 hy.2 k)
  have hW : h y ∈ LB.wchart L φ₂ j₂ := Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k
  have e := H y J hJ
  rw [sval_of s₂ (𝟙 Y' ≫ h) y J j₂ (fun k => by simpa using hJj (Sum.inr k)),
    sval_of s₁ (𝟙 Y') y J j₁ (fun k => by simpa using hJj (Sum.inl k))] at e
  calc _ = _ := gs_res _ y _ hy _
    _ = _ := gs_pull _ h y _ hW _
    _ = _ := e
    _ = _ := (congrArg₂ (· * ·) (gs_res _ y _ hy _) (gs_res _ y _ hy _)).symm
    _ = _ := (gs_mul _ y _ hy _ _).symm

variable {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem box_sval (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')}
    {φ : Fin j → K → (Y ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y' ⟶ Y)}
    (hφ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (s' : LB.Sec (LB.LinComb M' φ' ε))
    (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε))
    (hle : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι) i,
      LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM ≤
        ρ i ⁻¹ᵁ LB.wchart M (φ i) (fun a => jN a i))
    (H : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι),
      (@id (Γ(Y', LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ)
        ((LB.linCombIso w φ' ε).s (jN, jM))).val * rs inf_le_right (s'.f jM) =
        ∏ i, rs (hle jN jM i) (((ρ i).app _).hom ((s i).f (fun a => jN a i))))
    (q : Z ⟶ Y') (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, bw w (q ≫ φ' a) y (fun i => J ((q ≫ φ' a) ≫ pr i)) (J' (q ≫ φ' a)) ^ ε a).val * sval s' q y J' =
      ∏ i, sval (s i) (q ≫ ρ i) y J := by
  have hq : q y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((q ≫ φ' a) ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (q ≫ φ' a)) :=
    ⟨Good.mem (L := LB.LinComb M pr (fun _ => 1)) (J := fun ψ i => J (ψ ≫ pr i)) (fun ψ => hJ.mem pr ψ) φ' q,
      hJ'.mem φ' q⟩
  have key := congrArg (gs q y _) (H (fun a i => J ((q ≫ φ' a) ≫ pr i)) (fun a => J' (q ≫ φ' a)))
  calc _ = _ := congrArg (fun u => (∏ a, bw w (q ≫ φ' a) y (fun i => J ((q ≫ φ' a) ≫ pr i)) (J' (q ≫ φ' a)) ^ ε a).val * u)
          ((sval_of s' q y J' _ (fun a => rfl)).trans (gs_res q y _ hq _).symm)
    _ = _ := congrArg (· * _) (congrArg Units.val (gm_linCombIso w φ' ε q y _ _ hq).symm)
    _ = _ := congrArg (· * _) (gs_unit q y _ hq _).symm
    _ = _ := (gs_mul q y _ hq _ _).symm
    _ = _ := key
    _ = _ := gs_prod q y _ hq Finset.univ _
    _ = _ := Finset.prod_congr rfl fun i _ =>
          ((gs_res q y _ hq _).trans (gs_pull q (ρ i) y _ (hle _ _ i hq) _)).trans
            (sval_of (s i) (q ≫ ρ i) y J _ (fun a => by simp only [Category.assoc, hφ])).symm

theorem gs_scal {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (c : R) :
    gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  unfold scal
  have e := gs_pull (𝟙 Z) r z ⊤ trivial ((Scheme.Hom.appTop p).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))
  rw [Category.id_comp] at e
  rw [← e, Scheme.Hom.comp_appTop]
  rfl

theorem gs_scal_prod {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (p' : Y' ⟶ Spec (CommRingCat.of R))
    (ρ : Fin j → (Y' ⟶ Y)) (hρ : ∀ i, ρ i ≫ p = p') (y : Y') (r : Fin j → R) :
    ∏ i, gs (𝟙 _ ≫ ρ i) y ⊤ (scal p (r i)) = gs (𝟙 _) y ⊤ (scal p' (∏ i, r i)) := by
  have hsc : (∏ i, scal p' (r i)) = scal p' (∏ i, r i) := by
    simp only [scal, map_prod]
  rw [← hsc, gs_prod (𝟙 _) y ⊤ trivial Finset.univ]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gs_scal, Category.id_comp, hρ]

theorem secScal_box (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1)))
    {K : Type} [Fintype K] {ε : K → ℤ}
    {φ' : K → (Y' ⟶ X')} {φ : Fin j → K → (Y ⟶ X)} {ρ : Fin j → (Y' ⟶ Y)}
    {ψ' : K → (W' ⟶ X')} {ψ : Fin j → K → (W ⟶ X)} {σ : Fin j → (W' ⟶ W)}
    {h' : Y' ⟶ W'} {h : Y ⟶ W} (e' : ∀ a, φ' a = h' ≫ ψ' a) (e : ∀ i, h' ≫ σ i = ρ i ≫ h)
    (s' : LB.Sec (LB.LinComb M' φ' ε)) (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε))
    (t' : LB.Sec (LB.LinComb M' ψ' ε)) (t : ∀ i, LB.Sec (LB.LinComb M (ψ i) ε))
    (Hs : ∀ (y : Y') J J', Good M y J → Good M' y J' →
      (∏ a, bw w (𝟙 Y' ≫ φ' a) y (fun i => J ((𝟙 Y' ≫ φ' a) ≫ pr i)) (J' (𝟙 Y' ≫ φ' a)) ^ ε a).val *
        sval s' (𝟙 Y') y J' = ∏ i, sval (s i) (𝟙 Y' ≫ ρ i) y J)
    (Ht : ∀ (y : Y') J J', Good M y J → Good M' y J' →
      (∏ a, bw w (h' ≫ ψ' a) y (fun i => J ((h' ≫ ψ' a) ≫ pr i)) (J' (h' ≫ ψ' a)) ^ ε a).val *
        sval t' h' y J' = ∏ i, sval (t i) (h' ≫ σ i) y J)
    (c : Fin j → Γ(Y, ⊤)) (c' : Γ(Y', ⊤))
    (hc : ∀ y : Y', ∏ i, gs (𝟙 _ ≫ ρ i) y ⊤ (c i) = gs (𝟙 _) y ⊤ c')
    (H : ∀ i, GeneratorPullback.SecScal M (φ i) ε (s i) (ψ i) ε (t i) h (c i)) :
    GeneratorPullback.SecScal M' φ' ε s' ψ' ε t' h' c' := by
  apply secScal_of_pointwise hM'
  intro y J' hJ'
  obtain ⟨J, hJ, -⟩ := exists_good M hM y (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun a => a.elim)
  have hs := Hs y J J' hJ hJ'
  have ht := Ht y J J' hJ hJ'
  have hci := hc y
  have hH : ∀ i, sval (t i) (h' ≫ σ i) y J = gs (𝟙 Y' ≫ ρ i) y ⊤ (c i) * sval (s i) (𝟙 Y' ≫ ρ i) y J :=
    fun i => by rw [← sval_of_secScal (H i) (𝟙 Y' ≫ ρ i) y hJ, Category.id_comp, ← e i]
  simp only [Category.id_comp] at hs hH hci ⊢
  simp only [← e'] at ht
  refine (Units.isUnit (∏ a, bw w (φ' a) y (fun i => J (φ' a ≫ pr i)) (J' (φ' a)) ^ ε a)).mul_left_cancel ?_
  rw [ht, Finset.prod_congr rfl (fun i _ => hH i), Finset.prod_mul_distrib, hci, ← hs, mul_left_comm]

end Generic


set_option maxHeartbeats 800000 in
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (pD : IsPowDeg D'.toPre D.toPre j) (k : ℕ) (Fs : Fin j → Fam D.toPre (FractionRing R) k) (f : Fin j → ∀ α : D.toPre.X, D.toPre.SecB k α) (r : Fin j → R), (∀ i α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((Fs i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom (r i))) → ∀ (F' : Fam D'.toPre (FractionRing R) k), IsBoxFam pD (FractionRing R) k F' Fs → ∀ α' : D'.toPre.X, GeneratorPullback.SecScal D'.toPre.P.L (DegPre.famφ D'.toPre (FractionRing R) α') (DegPre.famε k) (F'.s α') (D'.toPre.famφB α') (DegPre.famε k) (boxFamB pD k f α') (DegPre.prB D'.toPre (FractionRing R)).left (scal (DegPre.BF D'.toPre (FractionRing R)).hom (∏ i, r i)) := by
  intro R _ _ I j D D' pD k Fs f r hF F' hB α'
  have e1 : ∀ i, (D'.toPre.prB (FractionRing R)).left ≫ (pD.pw.pr i).left =
      prB pD (FractionRing R) i ≫ (D.toPre.prB (FractionRing R)).left := by
    intro i
    unfold prB DegPre.prB
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  have e2 : ∀ i, prB pD (FractionRing R) i ≫ (D.toPre.BF (FractionRing R)).hom =
      (D'.toPre.BF (FractionRing R)).hom := fun i => Over.w (TF (FractionRing R) ◁ pD.pw.pr i)
  obtain ⟨hφ, hBα⟩ := hB α'
  obtain ⟨hφB, hBB⟩ := isBoxFamB_boxFamB pD k f α'
  exact secScal_box D.toPre.P.isLB D'.toPre.P.isLB pD.w
    (ρ := fun i => prB pD (FractionRing R) i) (σ := fun i => (pD.pw.pr i).left)
    (h' := (D'.toPre.prB (FractionRing R)).left) (h := (D.toPre.prB (FractionRing R)).left)
    (fun a => GC.famφ_eq D'.toPre (FractionRing R) α' a) e1
    (F'.s α') (fun i => (Fs i).s (pD.xe α' i)) (boxFamB pD k f α') (fun i => f i (pD.xe α' i))
    (fun y J J' hJ hJ' => box_sval pD.w hφ (F'.s α') _
      (fun jN _ i => inf_le_left.trans (box_le_of_comp _ _ _ _ _ i (hφ i) jN)) hBα (𝟙 _) y hJ hJ')
    (fun y J J' hJ hJ' => box_sval pD.w hφB (boxFamB pD k f α') _
      (fun jN _ i => inf_le_left.trans (box_le_of_comp _ _ _ _ _ i (hφB i) jN)) hBB _ y hJ hJ')
    (fun i => scal (D.toPre.BF (FractionRing R)).hom (r i)) _
    (fun y => gs_scal_prod _ _ _ e2 y r)
    (fun i => hF i (pD.xe α' i))

end GlobalTheory.BoxFamScalar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxProductLinearIndependent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace BoxIndep

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_tensor_pow (F O : Type) [Field F] [CommRing O] [Algebra F O] {m : ℕ} (β : Fin m → O)
    (hβ : LinearIndependent F β) (j : ℕ) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra F B) (em : Fin j → (O →ₐ[F] B)),
      LinearIndependent F (fun a : Fin j → Fin m => ∏ i, em i (β (a i))) := by
  induction j with
  | zero =>
    refine ⟨F, inferInstance, inferInstance, fun i => i.elim0, ?_⟩
    rw [linearIndependent_unique_iff]
    simp
  | succ j ih =>
    obtain ⟨B, _, _, em, h⟩ := ih
    refine ⟨TensorProduct F O B, inferInstance, inferInstance,
      Fin.cons Algebra.TensorProduct.includeLeft
        (fun i => (Algebra.TensorProduct.includeRight).comp (em i)), ?_⟩
    have h2 := (hβ.tmul_of_isDomain h).comp (Fin.consEquiv (fun _ : Fin (j+1) => Fin m)).symm
      (Equiv.injective _)
    refine (congrArg (fun v : (Fin (j + 1) → Fin m) → TensorProduct F O B => LinearIndependent F v) (funext fun a => ?_)).mpr h2
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, AlgHom.comp_apply, Function.comp_apply]
    rw [← map_prod, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    rfl

variable {X Z : Scheme.{0}}

noncomputable def germOf {B : CommRingCat.{0}} (r : Z ⟶ Spec B) (z : Z) : B →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ ⊤) z trivial).hom.comp ((r.app ⊤).hom.comp (Scheme.ΓSpecIso B).inv.hom)

theorem germOf_apply {B : CommRingCat.{0}} (r : Z ⟶ Spec B) (z : Z) (a : B) :
    germOf r z a = gs r z ⊤ ((Scheme.ΓSpecIso B).inv.hom a) := (gs_eq r z ⊤ trivial _).symm

theorem germOf_map {B C : CommRingCat.{0}} (r : Z ⟶ Spec C) (φ : B ⟶ C) (z : Z) (a : B) :
    germOf (r ≫ Spec.map φ) z a = germOf r z (φ.hom a) := by
  rw [germOf_apply, germOf_apply, ← gs_pull r (Spec.map φ) z ⊤ trivial]
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality φ)
  exact congrArg (gs r z ⊤) e.symm

theorem eq_zero_of_germOf {B : CommRingCat.{0}} (a : B) (h : ∀ z, germOf (𝟙 (Spec B)) z a = 0) : a = 0 := by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv).1
  refine fn_ext fun z hz => ?_
  rw [map_zero, gs_zero _ _ _ hz]
  exact (germOf_apply _ _ _).symm.trans (h z)

theorem fromSpecStalk_mem (x : X) {U : X.Opens} (hx : x ∈ U) (y : Spec (X.presheaf.stalk x)) :
    X.fromSpecStalk x y ∈ U := by
  have : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y, rfl⟩
  rw [Scheme.range_fromSpecStalk] at this
  exact Specializes.mem_open this U.isOpen hx

theorem gs_fromSpecStalk (x : X) {U : X.Opens} (hx : x ∈ U) (r : Z ⟶ Spec (X.presheaf.stalk x)) (z : Z)
    (a : Γ(X, U)) : gs (r ≫ X.fromSpecStalk x) z U a = germOf r z (gs (𝟙 X) x U a) := by
  have hm := fromSpecStalk_mem x hx (r z)
  rw [← gs_pull r _ z U hm, Scheme.fromSpecStalk_app hx, germOf_apply, gs_eq (𝟙 X) x U hx]
  exact gs_res r z le_top hm _

theorem fromSpecStalk_comp {B : CommRingCat.{0}} (p : X ⟶ Spec B) (x : X) :
    X.fromSpecStalk x ≫ p = Spec.map (CommRingCat.ofHom (germOf p x)) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_epi (Scheme.ΓSpecIso B).inv,
    ← Scheme.ΓSpecIso_inv_naturality]
  ext a
  have e : CommRingCat.ofHom (germOf p x) =
      (Scheme.ΓSpecIso B).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ x trivial := rfl
  simp [e]

theorem exists_test {F : Type} [Field F] (p : X ⟶ Spec (CommRingCat.of F)) (x : X) {U : X.Opens} (hx : x ∈ U) {m : ℕ}
    (s : Fin m → Γ(X, U))
    (hs : ∀ c : Fin m → F, ∑ l, germOf p x (c l) * gs (𝟙 X) x U (s l) = 0 → c = 0) (j : ℕ) :
    ∃ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Fin j → (Z ⟶ X)), (∀ i, r i ≫ p = q) ∧
      (∀ i z, r i z ∈ U) ∧ ∀ c : (Fin j → Fin m) → F,
        (∀ z, ∑ a, germOf q z (c a) * ∏ i, gs (r i) z U (s (a i)) = 0) → c = 0 := by
  let : Algebra F (X.presheaf.stalk x) := (germOf p x).toAlgebra
  have hβ : LinearIndependent F (fun l => gs (𝟙 X) x U (s l)) :=
    Fintype.linearIndependent_iff.2 fun c hc => congrFun (hs c (by simp only [Algebra.smul_def] at hc; exact hc))
  obtain ⟨B, _, _, em, h⟩ := exists_tensor_pow F _ _ hβ j
  refine ⟨Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap F B)),
    fun i => (Spec.map (CommRingCat.ofHom (em i).toRingHom) : _ ⟶ Spec (X.presheaf.stalk x)) ≫ X.fromSpecStalk x,
    fun i => ?_, fun i z => fromSpecStalk_mem x hx _, fun c hc => ?_⟩
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact (em i).commutes a
  · funext a
    refine Fintype.linearIndependent_iff.1 h c (eq_zero_of_germOf (B := CommRingCat.of B) _ fun z => ?_) a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc z, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, map_mul, map_prod]
    congr 1
    · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [gs_fromSpecStalk x hx]
      exact (germOf_map (B := X.presheaf.stalk x) (𝟙 _) (CommRingCat.ofHom (em i).toRingHom) z _).symm

theorem gs_liftFun {S : Scheme.{0}} (A : Over S) {B : CommRingCat.{0}} (t : Spec B ⟶ S)
    (W : (Over.mk t ⊗ A).left.Opens) (r : Z ⟶ (Over.mk t ⊗ A).left) (z : Z) (hz : r z ∈ W) (a : B) :
    gs r z W (liftFun A (T := Over.mk t) W ((Scheme.ΓSpecIso B).inv.hom a)) =
      germOf (B := B) (r ≫ (fst (Over.mk t) A).left) z a :=
  (gs_res r z le_top hz _).trans ((gs_pull r (fst (Over.mk t) A).left z ⊤ trivial _).trans (germOf_apply _ _ _).symm)

theorem gs_comb {S : Scheme.{0}} (A : Over S) {B : CommRingCat.{0}} (t : Spec B ⟶ S)
    (W : (Over.mk t ⊗ A).left.Opens) (r : Z ⟶ (Over.mk t ⊗ A).left) (z : Z) (hz : r z ∈ W) {K : Type} [Fintype K]
    (c : K → B) (f : K → Γ((Over.mk t ⊗ A).left, W)) :
    gs r z W (∑ l, liftFun A (T := Over.mk t) W ((Scheme.ΓSpecIso B).inv.hom (c l)) * f l) =
      ∑ l, germOf (B := B) (r ≫ (fst (Over.mk t) A).left) z (c l) * gs r z W (f l) := by
  rw [gs_fsum r z W hz]
  exact Finset.sum_congr rfl fun l _ => by rw [gs_mul r z W hz, gs_liftFun A t W r z hz]

theorem box_indep {S : Scheme.{0}} (j : ℕ) (A A' : PolAV S) (pA : IsPowPolAV A' A j) (F : Type) [Field F]
    (t : Spec (CommRingCat.of F) ⟶ S) (k m : ℕ)
    (b : Fin m → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (Over.mk t) A.A).left) (fun _ => (k : ℤ))))
    (hb : ∀ c : Fin m → F,
      (∀ jj, ∑ l, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) * (b l).f jj = 0) → c = 0)
    (t' : (Fin j → Fin m) →
      LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (Over.mk t) A'.A).left) (fun _ => (k : ℤ))))
    (ht : ∀ a, (∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.mk t) ⊗ A'.A).left) (z : Z) (J J'), Good A.L z J → Good A'.L z J' →
      (bw pA.w (r ≫ (snd (Over.mk t) A'.A).left) z (fun i => J ((r ≫ (snd (Over.mk t) A'.A).left) ≫ (pA.pr i).left))
        (J' (r ≫ (snd (Over.mk t) A'.A).left)) ^ k).val * sval (t' a) r z J' =
        ∏ i, sval (b (a i)) (r ≫ ((Over.mk t) ◁ pA.pr i).left) z J))
    (c : (Fin j → Fin m) → F)
    (hc : ∀ jj, ∑ a, liftFun A'.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c a)) * (t' a).f jj = 0) :
    c = 0 := by
  have := A.isAb.smooth
  have := A.isAb.geomConnected
  have hg := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres A.A.hom
  have hint : IsIntegral (Over.mk t ⊗ A.A).left :=
    hg.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t A.A.hom).flip
  obtain ⟨j₀, hj₀⟩ := exists_chart A.isLB ((snd (Over.mk t) A.A).left (genericPoint (Over.mk t ⊗ A.A).left))
  have hx : genericPoint (Over.mk t ⊗ A.A).left ∈
      LB.wchart A.L (fun _ : Fin 1 => (snd (Over.mk t) A.A).left) (fun _ => j₀) := Set.mem_iInter.2 fun _ => hj₀
  obtain ⟨Z, q, r, hq, hr, H⟩ := exists_test (F := F) (fst (Over.mk t) A.A).left _ hx (fun l => (b l).f (fun _ => j₀))
    (fun c hc => hb c fun jj => by
      refine fn_ext fun y hy => congrArg _ ?_
      have hy' : genericPoint (Over.mk t ⊗ A.A).left ∈
          LB.wchart A.L (fun _ : Fin 1 => (snd (Over.mk t) A.A).left) jj :=
        ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr ⟨y, trivial, hy⟩
      apply germ_injective_of_isIntegral _ _ hy'
      refine (gs_eq (𝟙 _) _ _ hy' _).symm.trans (Eq.trans ?_ (map_zero _).symm)
      refine (gs_comb A.A t _ (𝟙 _) _ hy' c _).trans ?_
      simp only [fun l => sec_trans (b l) (𝟙 _) _ hy' hx, Category.id_comp, mul_left_comm _ (Units.val _)]
      rw [← Finset.mul_sum]
      exact (congrArg _ hc).trans (mul_zero _)) j
  let T : Over S := Over.mk (q ≫ t)
  let q' : T ⟶ Over.mk t := Over.homMk q rfl
  let r' : Fin j → (T ⟶ Over.mk t ⊗ A.A) := fun i => Over.homMk (r i) (by
    rw [← Over.w (fst (Over.mk t) A.A), ← Category.assoc, hq]; rfl)
  let ρ : T ⟶ Over.mk t ⊗ A'.A := lift q' (Fan.IsLimit.lift pA.lim fun i => r' i ≫ snd _ _)
  have hρ : ∀ i, ρ ≫ Over.mk t ◁ pA.pr i = r' i := fun i => by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      exact Over.OverMorphism.ext (hq i).symm
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact Fan.IsLimit.fac pA.lim _ i
  have hρ' : ∀ i, (ρ.left : Z ⟶ _) ≫ (Over.mk t ◁ pA.pr i).left = r i := fun i => congrArg (fun g => g.left) (hρ i)
  have hρq : (ρ.left : Z ⟶ _) ≫ (fst (Over.mk t) A'.A).left = q :=
    congrArg (fun g => g.left) (lift_fst q' (Fan.IsLimit.lift pA.lim fun i => r' i ≫ snd _ _))
  refine H c fun z => ?_
  obtain ⟨J, hJ, eJ⟩ := exists_good A.L A.isLB z (fun i => r i ≫ (snd (Over.mk t) A.A).left) (fun _ => j₀)
    (fun _ _ _ => rfl) (fun i => Set.mem_iInter.1 (hr i z) 0)
  choose J' hJ' using fun ψ : Z ⟶ A'.A.left => exists_chart A'.isLB (ψ z)
  have hJ' : Good A'.L z J' := hJ'
  have hm := hJ'.mem (fun _ : Fin 1 => (snd (Over.mk t) A'.A).left) (ρ.left : Z ⟶ _)
  have E := (gs_comb A'.A t _ (ρ.left : Z ⟶ _) z hm c _).symm.trans
    ((congrArg _ (hc _)).trans (gs_zero _ _ _ hm))
  have E' := fun a => ht a Z ρ.left z J J' hJ hJ'
  simp only [hρ'] at E'
  rw [hρq] at E
  obtain ⟨u, hu⟩ : ∃ u : Z.presheaf.stalk z, ∀ a, u * sval (Z := Z) (t' a) ρ.left z J' =
      ∏ i, sval (b (a i)) (r i) z J := ⟨_, E'⟩
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) ((Finset.mul_sum _ _ u).symm.trans
    ((congrArg _ E).trans (mul_zero _)))
  refine Eq.trans (congrArg _ ((Finset.prod_congr rfl fun i _ =>
    (sval_of (b (a i)) (r i) z J (fun _ => j₀) (fun _ => eJ i)).symm).trans (hu a).symm)) ?_
  exact mul_left_comm _ _ _

end BoxIndep

theorem boxProduct_linearIndependent : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (m : ℕ) (b : Fin m → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))), (∀ c : Fin m → F, (∀ jj, ∑ l, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) * (b l).f jj = 0) → c = 0) → ∀ t' : (Fin j → Fin m) → LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ))), (∀ a, (∀ (Z : Scheme.{0}) (r : Z ⟶ ((TFK (R := R) F) ⊗ A'.A).left) (z : Z) (J J'), Geo.Tor.Good A.L z J → Geo.Tor.Good A'.L z J' → (bw pA.w (r ≫ (snd (TFK (R := R) F) A'.A).left) z (fun i => J ((r ≫ (snd (TFK (R := R) F) A'.A).left) ≫ (pA.pr i).left)) (J' (r ≫ (snd (TFK (R := R) F) A'.A).left)) ^ k).val * Geo.Tor.sval (t' a) r z J' = ∏ i, Geo.Tor.sval (b (a i)) (r ≫ ((TFK (R := R) F) ◁ pA.pr i).left) z J)) → ∀ c : (Fin j → Fin m) → F, (∀ jj, ∑ a, liftFun A'.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c a)) * (t' a).f jj = 0) → c = 0 :=
  fun R _ _ j A A' pA F _ _ k m b hb t' ht c hc =>
    BoxIndep.box_indep j A A' pA F (jFK (R := R) F) k m b hb t' ht c hc

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpBijFOfAdmissibleBase
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem expBijF_of_admissible_base : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I →
    ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
      [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), Geo.Tor.ExpBijF U.toUnifPre :=
  fun hL _ R _ _ I _ D A G _ _ U => expansion_bijective_over_fields hL.globalFns R I D A G U

end GlobalTheory
end
