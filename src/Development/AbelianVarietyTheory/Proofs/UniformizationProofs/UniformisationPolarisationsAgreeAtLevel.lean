module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LcgLinCombEqProd
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisationsAgreeAtLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisationsAgreeAtLevel
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevelComparison

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Compare

variable {B B' G E : Scheme.{0}} {M : LB B} {M' : LB B'} {L L' : LB G} {p : E ⟶ B} {p' : E ⟶ B'} {f : E ⟶ G}

def germ (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f) (M'.pull p')) (wL : LB.Iso L' (L.pull (𝟙 G)))
    {Z : Scheme.{0}} (r : Z ⟶ E) (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gw w r z jM (fun _ => jL) * gw wL (r ≫ f) z jL jL' * (gw w' r z jM' (fun _ => jL'))⁻¹

theorem germ_change {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f) (M'.pull p')}
    {wL : LB.Iso L' (L.pull (𝟙 G))} (hw : PGen w) (hw' : PGen w') (hwL : PGen wL)
    {Z : Scheme.{0}} (r : Z ⟶ E) (z : Z) (jM kM : M.ι) (jM' kM' : M'.ι) (jL kL : L.ι) (jL' kL' : L'.ι)
    (a₁ : p (r z) ∈ M.U jM) (a₂ : p' (r z) ∈ M'.U jM') (a₃ : f (r z) ∈ L.U jL)
    (a₄ : f (r z) ∈ L'.U jL') (b₁ : p (r z) ∈ M.U kM) (b₂ : p' (r z) ∈ M'.U kM')
    (b₃ : f (r z) ∈ L.U kL) (b₄ : f (r z) ∈ L'.U kL') :
    germ w w' wL r z jM jM' jL jL' =
      gm (r ≫ p) z _ (M.g jM kM) * (gm (r ≫ p') z _ (M'.g jM' kM'))⁻¹ * germ w w' wL r z kM kM' kL kL' := by
  have a := hw Z r z jM kM (fun _ => jL) (fun _ => kL) a₁ b₁ (mem_pull.2 a₃) (mem_pull.2 b₃)
  have b := hwL Z (r ≫ f) z jL kL jL' kL' a₃ b₃ a₄ b₄
  have c := hw' Z r z jM' kM' (fun _ => jL') (fun _ => kL') a₂ b₂ (mem_pull.2 a₄) (mem_pull.2 b₄)
  rw [FourthSide.gm_pull_g L f r z jL kL a₃ b₃] at a
  rw [FourthSide.gm_pull_g L' f r z jL' kL' a₄ b₄] at c
  rw [Category.comp_id] at b
  unfold germ
  rw [a, b, c]
  generalize gm (r ≫ p) z _ (M.g jM kM) = A
  generalize gm (r ≫ f) z _ (L.g jL kL) = C
  generalize gm (r ≫ p') z _ (M'.g jM' kM') = A'
  generalize gm (r ≫ f) z _ (L'.g jL' kL') = C'
  generalize gw w r z kM (fun _ => kL) = P
  generalize gw wL (r ≫ f) z kL kL' = Q
  generalize gw w' r z kM' (fun _ => kL') = R
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_unit (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f) (M'.pull p')}
    {wL : LB.Iso L' (L.pull (𝟙 G))} (hw : PGen w) (hw' : PGen w') (hwL : PGen wL) (jM : M.ι) (jM' : M'.ι) :
    ∃ s : Γ(E, (M.pull p).U (fun _ => jM) ⊓ (M'.pull p').U (fun _ => jM'))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ E) (z : Z) (jL : L.ι) (jL' : L'.ι), p (r z) ∈ M.U jM →
        p' (r z) ∈ M'.U jM' → f (r z) ∈ L.U jL → f (r z) ∈ L'.U jL' →
        gm r z _ s = germ w w' wL r z jM jM' jL jL' := by
  obtain ⟨W, hW⟩ : ∃ W : L.ι × L'.ι → E.Opens, ∀ i x, x ∈ W i ↔
      p x ∈ M.U jM ∧ p' x ∈ M'.U jM' ∧ f x ∈ L.U i.1 ∧ f x ∈ L'.U i.2 :=
    ⟨fun i => p ⁻¹ᵁ M.U jM ⊓ (p' ⁻¹ᵁ M'.U jM' ⊓ (f ⁻¹ᵁ L.U i.1 ⊓ f ⁻¹ᵁ L'.U i.2)), fun _ _ => Iff.rfl⟩
  have l₀ : ∀ i, W i ≤ (M.pull p).U (fun _ => jM) ⊓ (M'.pull p').U (fun _ => jM') := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).1, mem_pull.2 ((hW i x).1 hx).2.1⟩
  have l₁ : ∀ i, W i ≤ (M.pull p).U (fun _ => jM) ⊓ (L.pull f).U (fun _ => i.1) := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).1, mem_pull.2 ((hW i x).1 hx).2.2.1⟩
  have l₂ : ∀ i, W i ≤ f ⁻¹ᵁ ((L.pull (𝟙 G)).U (fun _ => i.1) ⊓ L'.U i.2) := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).2.2.1, ((hW i x).1 hx).2.2.2⟩
  have l₃ : ∀ i, W i ≤ (M'.pull p').U (fun _ => jM') ⊓ (L'.pull f).U (fun _ => i.2) := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).2.1, mem_pull.2 ((hW i x).1 hx).2.2.2⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(E, W i)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ E) (z : Z) (i : L.ι × L'.ι), r z ∈ W i →
      gm r z (W i) (u i) = germ w w' wL r z jM jM' i.1 i.2 :=
    ⟨fun i => res (l₁ i) (w.s (fun _ => jM, fun _ => i.1)) *
        res (l₂ i) (pullU f _ (wL.s (fun _ => i.1, i.2))) * (res (l₃ i) (w'.s (fun _ => jM', fun _ => i.2)))⁻¹,
      fun Z r z i hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        (gm_res r z (l₁ i) hz _) ((gm_res r z (l₂ i) hz _).trans (gm_pull r f z _ (l₂ i hz) _))))
        ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z (l₃ i) hz _))))⟩
  obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hL (f x)
      obtain ⟨j, hj⟩ := exists_chart hL' (f x)
      exact Opens.mem_iSup.2 ⟨(i, j), (hW (i, j) x).2 ⟨mem_pull.1 hx.1, mem_pull.1 hx.2, hi, hj⟩⟩) u
    (fun i i' x hx => by
      have h₁ := (hW i x).1 hx.1
      have h₂ := (hW i' x).1 hx.2
      have k := germ_change hw hw' hwL (𝟙 E) x jM jM jM' jM' i.1 i'.1 i.2 i'.2 h₁.1 h₁.2.1 h₁.2.2.1
        h₁.2.2.2 h₂.1 h₂.2.1 h₂.2.2.1 h₂.2.2.2
      rw [gm_self hM (𝟙 E ≫ p) x h₁.1, gm_self hM' (𝟙 E ≫ p') x h₁.2.1, inv_one, _root_.one_mul,
        _root_.one_mul] at k
      exact (hu _ (𝟙 E) x i hx.1).trans (k.trans (hu _ (𝟙 E) x i' hx.2).symm))
  refine ⟨s, fun Z r z jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  have hz := (hW (jL, jL') (r z)).2 ⟨a₁, a₂, a₃, a₄⟩
  exact (gm_res r z (l₀ (jL, jL')) hz s).symm.trans
    ((congrArg (gm r z (W (jL, jL'))) (hs (jL, jL'))).trans (hu Z r z (jL, jL') hz))

theorem exists_comparison (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f) (M'.pull p')}
    {wL : LB.Iso L' (L.pull (𝟙 G))} (hw : w.IsGen) (hw' : w'.IsGen) (hwL : wL.IsGen) :
    ∃ u : LB.Iso (M'.pull p') (M.pull p), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ E) (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
        p (r z) ∈ M.U jM → p' (r z) ∈ M'.U jM' → f (r z) ∈ L.U jL → f (r z) ∈ L'.U jL' →
        gw u r z jM (fun _ => jM') * gw w' r z jM' (fun _ => jL') =
          gw w r z jM (fun _ => jL) * gw wL (r ≫ f) z jL jL' := by
  rw [isGen_iff] at hw hw' hwL
  choose s hs using exists_unit hM hM' hL hL' hw hw' hwL
  refine ⟨⟨fun q => s (q.1 PUnit.unit) (q.2 PUnit.unit)⟩, (isGen_iff _).2 ?_,
    fun Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  · intro Z r z j j' k k' a₁ b₁ a₂ b₂
    obtain ⟨i, hi⟩ := exists_chart hL (f (r z))
    obtain ⟨l, hl⟩ := exists_chart hL' (f (r z))
    have a₂' := mem_pull.1 a₂
    have b₂' := mem_pull.1 b₂
    have c := germ_change hw hw' hwL r z j j' _ _ i i l l a₁ a₂' hi hl b₁ b₂' hi hl
    rw [← hs j _ Z r z i l a₁ a₂' hi hl, ← hs j' _ Z r z i l b₁ b₂' hi hl,
      ← FourthSide.gm_pull_g M' p' r z _ _ a₂' b₂'] at c
    exact c
  · exact (congrArg (· * gw w' r z jM' (fun _ => jL')) (hs jM jM' Z r z jL jL' a₁ a₂ a₃ a₄)).trans
      (inv_mul_cancel_right _ _)

end Compare

section Descend

variable {X Y : Scheme.{0}} (q : X ⟶ Y) [Flat q] [Surjective q]

theorem unit_ext_of_flat {V : Y.Opens} {a b : Γ(Y, V)ˣ} (h : ∀ x, q x ∈ V → gm q x V a = gm q x V b) : a = b := by
  apply Units.ext
  apply FunDescent.app_injective q V
  have : pullU q V a = pullU q V b := unit_ext fun x hx =>
    (gm_pull (𝟙 X) q x V hx a).trans (Eq.trans (by rw [Category.id_comp]; exact h x hx)
      (gm_pull (𝟙 X) q x V hx b).symm)
  exact congrArg Units.val this

theorem exists_unit_descend [QuasiCompact q] (V : Y.Opens) (W : X.Opens) (hW : q ⁻¹ᵁ V ≤ W) (s : Γ(X, W)ˣ)
    (hs : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X) (z : Z), g₁ ≫ q = g₂ ≫ q → q (g₂ z) ∈ V →
      gm g₁ z W s = gm g₂ z W s) :
    ∃ t : Γ(Y, V)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z), q (r z) ∈ V → gm (r ≫ q) z V t = gm r z W s := by
  obtain ⟨a, ha⟩ := FunDescent.exists_app_eq q V (res hW s).val (fun Z g₁ g₂ h₁ h₂ e => by
    have k : ∀ (g : Z ⟶ X) (h : ⊤ ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V)) (z : Z),
        gm (𝟙 Z) z ⊤ (res h (pullU g _ (res hW s))) = gm g z W s := fun g h z =>
      (gm_res (𝟙 Z) z h trivial _).trans ((gm_pull (𝟙 Z) g z _ (h trivial) _).trans (by
        rw [Category.id_comp]; exact gm_res g z hW (h trivial) s))
    have : res h₁ (pullU g₁ _ (res hW s)) = res h₂ (pullU g₂ _ (res hW s)) := unit_ext fun z _ =>
      (k g₁ h₁ z).trans ((hs Z g₁ g₂ z e (h₂ trivial)).trans (k g₂ h₂ z).symm)
    exact congrArg Units.val this)
  obtain ⟨t, rfl⟩ := FunDescent.isUnit_of_isUnit_app q V a (ha ▸ (res hW s).isUnit)
  refine ⟨t, fun Z r z hz => ?_⟩
  have : pullU q V t = res hW s := Units.ext ha
  rw [← gm_pull r q z V hz, this]
  exact gm_res r z hW hz s

theorem exists_iso_descend [QuasiCompact q] {B B' : Scheme.{0}} {M : LB B} {M' : LB B'} (a : Y ⟶ B') (b : Y ⟶ B)
    {p : X ⟶ B} {p' : X ⟶ B'} (hp : p = q ≫ b) (hp' : p' = q ≫ a) (u : LB.Iso (M'.pull p') (M.pull p))
    (hu : u.IsGen)
    (hinv : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X) (z : Z) (j : M.ι) (j' : M'.ι), g₁ ≫ q = g₂ ≫ q →
      p (g₂ z) ∈ M.U j → p' (g₂ z) ∈ M'.U j' → gw u g₁ z j (fun _ => j') = gw u g₂ z j (fun _ => j')) :
    ∃ v : LB.Iso (M'.pull a) (M.pull b), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (j : M.ι) (j' : M'.ι), p (r z) ∈ M.U j → p' (r z) ∈ M'.U j' →
        gw v (r ≫ q) z j (fun _ => j') = gw u r z j (fun _ => j') := by
  subst hp hp'
  rw [isGen_iff] at hu
  have key : ∀ (j : M.ι) (j' : M'.ι), ∃ t : Γ(Y, (M.pull b).U (fun _ => j) ⊓ (M'.pull a).U (fun _ => j'))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z), q (r z) ∈ (M.pull b).U (fun _ => j) ⊓ (M'.pull a).U (fun _ => j') →
        gm (r ≫ q) z _ t = gw u r z j (fun _ => j') := fun j j' =>
    exists_unit_descend q ((M.pull b).U (fun _ => j) ⊓ (M'.pull a).U (fun _ => j'))
      ((M.pull (q ≫ b)).U (fun _ => j) ⊓ (M'.pull (q ≫ a)).U (fun _ => j'))
      (fun x hx => ⟨mem_pull₂.2 (mem_pull.1 hx.1), mem_pull₂.2 (mem_pull.1 hx.2)⟩)
      (u.s (fun _ => j, fun _ => j'))
      (fun Z g₁ g₂ z e hz => hinv Z g₁ g₂ z j j' e (mem_pull.1 hz.1) (mem_pull.1 hz.2))
  choose t ht using key
  refine ⟨⟨fun k => t (k.1 PUnit.unit) (k.2 PUnit.unit)⟩, ?_,
    fun Z r z j j' h h' => ht j j' Z r z ⟨mem_pull.2 h, mem_pull.2 h'⟩⟩
  rintro ⟨J, K⟩ ⟨J', K'⟩
  apply unit_ext_of_flat q
  intro x hx
  have hj := mem_pull.1 hx.1.1
  have hj' := mem_pull.1 hx.2.1
  have hk := mem_pull.1 hx.1.2
  have hk' := mem_pull.1 hx.2.2
  have c := hu _ (𝟙 X) x (J PUnit.unit) (J' PUnit.unit) (fun _ => K PUnit.unit) (fun _ => K' PUnit.unit) hj hj'
    (mem_pull₂.2 hk) (mem_pull₂.2 hk')
  have t₁ := ht (J PUnit.unit) (K PUnit.unit) X (𝟙 X) x ⟨mem_pull.2 hj, mem_pull.2 hk⟩
  have t₂ := ht (J' PUnit.unit) (K' PUnit.unit) X (𝟙 X) x ⟨mem_pull.2 hj', mem_pull.2 hk'⟩
  have g₁ := FourthSide.gm_pull_g M' (q ≫ a) (𝟙 X) x _ _ hk hk'
  have g₂ := FourthSide.gm_pull_g M' a q x _ _ hk hk'
  have g₃ := gm_div_g (L := M) (L' := M'.pull a) (F := b) q x (J PUnit.unit) (J' PUnit.unit)
    (fun _ => K PUnit.unit) (fun _ => K' PUnit.unit) hj hj' (mem_pull.2 hk) (mem_pull.2 hk')
  rw [Category.id_comp] at t₁ t₂ g₁ c
  rw [← t₁, ← t₂, g₁, ← g₂, ← g₃] at c
  exact (gm_res _ x _ hx _).trans (c.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)

end Descend

end GlobalTheory.LevelComparison

namespace GlobalTheory

theorem polarisations_agree_at_level : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom → (U'.gt e).q ≫ β.hom = (U.gt e).q → ∃ v : LB.Iso (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left) (D.toPre.P.L.pull (β.hom.left ≫ (fstG I e D.toPre.P.A).left)), v.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw v (r ≫ (U'.gt e).q.left) z jM (fun _ => jM') * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL') := by
  intro hG R _ _ _ I hI D D' A A' G _ _ hS U U' wL he hwL hrig e β hβ hq
  obtain ⟨u, hu, hu'⟩ := LevelComparison.exists_comparison D.toPre.P.isLB D'.toPre.P.isLB U.LG.isLB U'.LG.isLB
    (U.w_gen e) (U'.w_gen e) hwL
  have inv := GlobalTheory.T.genMaps_linCombIso_of_semiAbelian hG R I hI D D' A A' G hS U U' wL he hwL hrig
    (rigidified_iso_respects_cube_and_symmetry hG R I hI D D' A A' G hS U U' wL he hwL hrig) e β hβ hq u hu hu'
  haveI := (U'.gt e).q_flat
  haveI := (U'.gt e).q_surj
  haveI := (U'.gt e).q_affine
  haveI := (U.gt e).q_hom
  have hql : (U'.gt e).q.left ≫ β.hom.left = (U.gt e).q.left := congrArg (·.left) hq
  obtain ⟨v, hv, hv'⟩ := LevelComparison.exists_iso_descend (U'.gt e).q.left (fstG I e D'.toPre.P.A).left
    (β.hom.left ≫ (fstG I e D.toPre.P.A).left) (p := (U.gt e).pG.left) (p' := (U'.gt e).pG.left)
    (by rw [← Category.assoc, hql]; rfl) rfl u hu (fun Z g₁ g₂ z j j' h a b => by
      let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (g₂ ≫ (thickObj R I e G).hom)
      let k₂ : Z' ⟶ thickObj R I e G := Over.homMk g₂ rfl
      let k₁ : Z' ⟶ thickObj R I e G := Over.homMk g₁ (by
        change g₁ ≫ (thickObj R I e G).hom = g₂ ≫ (thickObj R I e G).hom
        rw [← Over.w (U'.gt e).q, reassoc_of% h])
      have e₁ : k₁ ≫ (U'.gt e).q = k₂ ≫ (U'.gt e).q := Over.OverMorphism.ext h
      have e' : k₁ ≫ (U.gt e).q = k₂ ≫ (U.gt e).q := by rw [← hq, reassoc_of% e₁]
      have w : (k₁ * k₂⁻¹) ≫ (U.gt e).q = toUnit Z' ≫ η[thickObj R I e D.toPre.P.A] := by
        rw [MonObj.mul_comp, GrpObj.inv_comp, e', mul_inv_cancel]
        rfl
      have ht : ((U.gt e).isKernel.lift _ _ w ≫ (U.gt e).i) * k₂ = k₁ := by
        rw [(U.gt e).isKernel.lift_fst, inv_mul_cancel_right]
      have := inv Z' ((U.gt e).isKernel.lift _ _ w) k₂ z j j' a b
      rw [ht] at this
      exact this)
  refine ⟨v, hv, fun Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  rw [← hu' Z r z jM jM' jL jL' a₁ a₂ a₃ a₄]
  exact congrArg (· * _) (hv' Z r z jM jM' a₁ a₂)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisationsAgreeAtLevelStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.uniformisation_polarisations_agree_at_level : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom → (U'.gt e).q ≫ β.hom = (U.gt e).q → ∃ v : LB.Iso (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left) (D.toPre.P.L.pull (β.hom.left ≫ (fstG I e D.toPre.P.A).left)), v.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw v (r ≫ (U'.gt e).q.left) z jM (fun _ => jM') * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL') := by
  first | exact @GlobalTheory.polarisations_agree_at_level | exact GlobalTheory.polarisations_agree_at_level | (intros; apply GlobalTheory.polarisations_agree_at_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqClosedPointOfNotMemRange
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericExt

universe u

theorem flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  change Flat (Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec)
  have : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have h₂ : IsOpenImmersion (IsAffineOpen.fromSpec hU) := IsAffineOpen.isOpenImmersion_fromSpec hU
  have h₃ : Flat (IsAffineOpen.fromSpec hU) := inferInstance
  exact MorphismProperty.comp_mem @Flat _ _ this h₃

theorem exists_hom_specStalk {W Y T X : Scheme.{u}} (j : W ⟶ Y) [IsSchemeTheoreticallyDominant j]
    [QuasiCompact j] [X.IsSeparated] (F : W ⟶ X) (g' : T ⟶ Y) [Flat g'] (g : T ⟶ X)
    (H : ∀ (Z : Scheme.{u}) (ρ : Z ⟶ T) (r : Z ⟶ W), r ≫ j = ρ ≫ g' → r ≫ F = ρ ≫ g) (p : T) :
    ∃ φ : Spec (Y.presheaf.stalk (g' p)) ⟶ X, ∀ (Z : Scheme.{u})
      (ρ : Z ⟶ Spec (Y.presheaf.stalk (g' p))) (r : Z ⟶ W),
      r ≫ j = ρ ≫ Y.fromSpecStalk (g' p) → r ≫ F = ρ ≫ φ := by
  let h := Spec.map (g'.stalkMap p)
  obtain ⟨h₁, h₂⟩ : Flat h ∧ Surjective h :=
    (flat_and_surjective_SpecMap_iff _).2 (faithfullyFlat_stalkMap_of_flat g' p)
  have hh : h ≫ Y.fromSpecStalk (g' p) = T.fromSpecStalk p ≫ g' :=
    Scheme.SpecMap_stalkMap_fromSpecStalk g'
  have := flat_fromSpecStalk Y (g' p)
  have key : pullback.fst h h ≫ T.fromSpecStalk p ≫ g = pullback.snd h h ≫ T.fromSpecStalk p ≫ g := by
    let q := pullback.fst h h ≫ h ≫ Y.fromSpecStalk (g' p)
    have hq : Flat q := inferInstance
    refine hom_ext_of_isSchemeTheoreticallyDominant (pullback.fst q j) (terminal.from X) ?_
      (terminal.hom_ext _ _)
    have e₁ := H _ (pullback.fst q j ≫ pullback.fst h h ≫ T.fromSpecStalk p) (pullback.snd q j) (by
      rw [← pullback.condition]; simp only [q, Category.assoc, hh])
    have e₂ := H _ (pullback.fst q j ≫ pullback.snd h h ≫ T.fromSpecStalk p) (pullback.snd q j) (by
      rw [← pullback.condition]
      simp only [q, Category.assoc, ← hh, pullback.condition_assoc])
    simpa only [Category.assoc] using e₁.symm.trans e₂
  let φ := EffectiveEpi.desc h (T.fromSpecStalk p ≫ g) (fun a b hab => by
    have := congrArg (pullback.lift a b hab ≫ ·) key
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this)
  have hφ : h ≫ φ = T.fromSpecStalk p ≫ g := EffectiveEpi.fac _ _ _
  refine ⟨φ, fun Z ρ r hr => ?_⟩
  rw [← cancel_epi (pullback.fst ρ h), pullback.condition_assoc, hφ]
  have := H _ (pullback.snd ρ h ≫ T.fromSpecStalk p) (pullback.fst ρ h ≫ r) (by
    rw [Category.assoc, hr, pullback.condition_assoc, hh, Category.assoc])
  simpa only [Category.assoc] using this

theorem exists_extension {W Y X S : Scheme.{u}} (j : W ⟶ Y) [IsOpenImmersion j] [IsDominant j]
    [QuasiCompact j] [IsIntegral Y] [S.IsSeparated] (sY : Y ⟶ S) (sX : X ⟶ S) [IsSeparated sX]
    [LocallyOfFiniteType sX] (F : W ⟶ X) (hF : F ≫ sX = j ≫ sY)
    (H : ∀ y : Y, y ∉ Set.range j → ∃ (T : Scheme.{u}) (g' : T ⟶ Y) (g : T ⟶ X), Flat g' ∧ y ∈ Set.range g' ∧
      ∀ (Z : Scheme.{u}) (ρ : Z ⟶ T) (r : Z ⟶ W), r ≫ j = ρ ≫ g' → r ≫ F = ρ ≫ g) :
    ∃ ψ : Y ⟶ X, j ≫ ψ = F ∧ ψ ≫ sX = sY := by
  have hX : X.IsSeparated := ⟨by rw [← terminal.comp_from sX]; infer_instance⟩
  have : IsSchemeTheoreticallyDominant j := .of_isDominant j
  let e₀ := Y.fromSpecStalk (genericPoint Y)
  have : IsDominant e₀ := isDominant_fromSpecStalk_genericPoint Y
  have hr : Set.range e₀ ⊆ Set.range j := by
    rw [Scheme.range_fromSpecStalk]
    intro z hz
    have hg : genericPoint Y ∈ Set.range j :=
      (genericPoint_spec Y).mem_open_set_iff j.isOpenEmbedding.isOpen_range |>.2
        (by simpa [Set.range_nonempty_iff_nonempty] using j.denseRange.nonempty)
    exact Specializes.mem_open hz j.isOpenEmbedding.isOpen_range hg
  let e := IsOpenImmersion.lift j e₀ hr
  have he : e ≫ j = e₀ := IsOpenImmersion.lift_fac _ _ _
  have loc : ∀ y : Y, ∃ (U : Scheme.{u}) (k : U ⟶ Y) (_ : IsOpenImmersion k) (ψ : U ⟶ X)
      (l : Spec (Y.presheaf.stalk (genericPoint Y)) ⟶ U),
      y ∈ Set.range k ∧ l ≫ k = e₀ ∧ l ≫ ψ = e ≫ F := by
    intro y
    by_cases hy : y ∈ Set.range j
    · exact ⟨W, j, inferInstance, F, e, hy, he, rfl⟩
    obtain ⟨T, g', g, hg', ⟨p, rfl⟩, hT⟩ := H y hy
    obtain ⟨φ, hφ⟩ := exists_hom_specStalk j F g' g hT p
    have := flat_fromSpecStalk Y (g' p)
    have hover : φ ≫ sX = Y.fromSpecStalk (g' p) ≫ sY := by
      refine hom_ext_of_isSchemeTheoreticallyDominant (pullback.fst (Y.fromSpecStalk (g' p)) j)
        (terminal.from S) ?_ (terminal.hom_ext _ _)
      rw [← reassoc_of% (hφ _ _ _ pullback.condition.symm), hF, pullback.condition_assoc]
    obtain ⟨U, hU, ψ, h₁, -⟩ := spread_out_of_isGermInjective' sY sX φ hover
    let m := Spec.map (Y.presheaf.stalkSpecializes (genericPoint_specializes (g' p)))
    have hm : m ≫ Y.fromSpecStalk (g' p) = e₀ := Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
    refine ⟨U, U.ι, inferInstance, ψ, m ≫ U.fromSpecStalkOfMem _ hU, ⟨⟨_, hU⟩, rfl⟩, ?_, ?_⟩
    · rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hm]
    · rw [Category.assoc, ← h₁]
      exact (hφ _ m e (he.trans hm.symm)).symm
  choose U k hk ψ l hy hl hψ using loc
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y U k (fun y => ⟨y, hy y⟩) hk
  have hc : ∀ a b : Y, pullback.fst (k a) (k b) ≫ ψ a = pullback.snd (k a) (k b) ≫ ψ b := by
    intro a b
    let m := pullback.lift (l a) (l b) ((hl a).trans (hl b).symm)
    have : IsReduced (pullback (k a) (k b)) := isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ k a)
    have : IsDominant (m ≫ pullback.fst _ _ ≫ k a) := by
      rw [pullback.lift_fst_assoc, hl]
      infer_instance
    have : IsDominant m := .of_comp_of_isOpenImmersion m (pullback.fst _ _ ≫ k a)
    refine ext_of_isDominant m ?_
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hψ, hψ]
  have hι : ∀ a : Y, k a ≫ 𝒰.glueMorphisms ψ hc = ψ a := fun a => 𝒰.ι_glueMorphisms ψ hc a
  have h1 : j ≫ 𝒰.glueMorphisms ψ hc = F := by
    have : IsReduced W := isReduced_of_isOpenImmersion j
    have : IsDominant (e ≫ j) := by rw [he]; infer_instance
    have : IsDominant e := .of_comp_of_isOpenImmersion e j
    refine ext_of_isDominant e ?_
    rw [reassoc_of% he, ← hl (genericPoint Y), Category.assoc, hι, hψ]
  refine ⟨_, h1, ext_of_isDominant j ?_⟩
  rw [reassoc_of% h1, hF]

theorem isOpenImmersion_jK (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsOpenImmersion (jK R) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away ϖ (FractionRing R) := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ)
      (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero)
      fun a ha => ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero ha) hϖ
    exact ⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩
  exact IsOpenImmersion.of_isLocalization ϖ

theorem eq_closedPoint_of_not_mem_range (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (s : Spec (CommRingCat.of R)) (hs : s ∉ Set.range (jK R)) : s = IsLocalRing.closedPoint R := by
  by_cases h : s.asIdeal = ⊥
  · refine (hs ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩).elim
    rw [h]
    exact Ideal.comap_bot_of_injective (algebraMap R (FractionRing R)) (IsFractionRing.injective R _)
  · exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (s.isPrime.isMaximal h))

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X' X : Over (Spec (CommRingCat.of R))) [Flat X'.hom] [IsIntegral X'.left] [IsSeparated X.hom] [LocallyOfFiniteType X.hom] (f : (Over.pullback (jK R)).obj X' ⟶ (Over.pullback (jK R)).obj X), (∀ x : X'.left, X'.hom x = IsLocalRing.closedPoint R → ∃ (T : Scheme.{0}) (g' : T ⟶ X'.left) (g : T ⟶ X.left), Flat g' ∧ x ∈ Set.range g' ∧ ∀ (Z : Scheme.{0}) (ρ : Z ⟶ T) (r : Z ⟶ ((Over.pullback (jK R)).obj X').left), r ≫ pullback.fst X'.hom (jK R) = ρ ≫ g' → r ≫ f.left ≫ pullback.fst X.hom (jK R) = ρ ≫ g) → ∃ ψ : X' ⟶ X, (Over.pullback (jK R)).map ψ = f := by
  intro R _ _ _ X' X _ _ _ _ f H
  have := isOpenImmersion_jK R
  have : IsDominant (jK R) := DVR.isDominant_jK
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsDominant (pullback.fst X'.hom (jK R)) := inferInstance
  have hf : f.left ≫ pullback.snd X.hom (jK R) = pullback.snd X'.hom (jK R) := Over.w f
  obtain ⟨ψ, h₁, h₂⟩ := exists_extension (pullback.fst X'.hom (jK R)) X'.hom X.hom
    (f.left ≫ pullback.fst X.hom (jK R))
    (by rw [Category.assoc, pullback.condition, pullback.condition, ← Category.assoc]; congr 1)
    (fun y hy => H y (eq_closedPoint_of_not_mem_range R _ fun h => hy (by
      rw [Scheme.Pullback.range_fst]; exact h)))
  refine ⟨Over.homMk ψ h₂, Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)⟩
  · exact (pullback.lift_fst _ _ _).trans h₁
  · exact (Over.w _).trans hf.symm

end GlobalTheory.GenericExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOfGen
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.KerPair

theorem exists_pow_gen {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℕ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => ε k * n)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J ^ n := by
  induction n with
  | zero =>
    obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := φ) (ε' := fun k => ε k * (0 : ℕ))
      (fun U _ h => by simp) (LB.oneGen L (Y := Y))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨t', ht', fun Z r z J hJ => (hv _ _ z J hJ).trans ((val_one _).trans (pow_zero _).symm)⟩
  | succ n ih =>
    obtain ⟨s, hs, hv⟩ := ih
    obtain ⟨t', ht', hv'⟩ := exists_gen hL (φ' := φ) (ε' := fun k => ε k * (n + 1 : ℕ)) (fun U _ h => by
        refine (Fintype.prod_sum_type _).trans ?_
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [← zpow_add]
        congr 1
        push_cast
        ring)
      (LB.mulGen L _ _ _ _ s t) (DVR.mulGen_isGen _ _ _ _ _ _ _ hs ht)
    refine ⟨t', ht', fun Z r z J hJ => (hv' _ _ z J hJ).trans ((val_mul hJ _ _ _).trans ?_)⟩
    rw [hv Z r z J hJ, pow_succ]

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : RigLB B} (c : CubicalStr B L)
  {T : Over S} {x : T ⟶ B}

abbrev trφ (x : T ⟶ B) : Fin 2 → ((T ⊗ B).left ⟶ B.left) := ![((fst T B ≫ x) * snd T B).left, (snd T B).left]


omit [IsCommMonObj B] in
theorem prod_tr {T' : Over S} (ρ : T' ⟶ T) (b : T' ⟶ B) {U : Type} [CommGroup U] (h : (T'.left ⟶ B.left) → U) (m : ℤ) :
    ∏ k : Fin 2, h ((lift ρ b).left ≫ trφ x k) ^ ((![1, -1] : Fin 2 → ℤ) k * m) =
      h ((ρ ≫ x) * b).left ^ m * h b.left ^ (-m) := by
  have e₀ : (lift ρ b).left ≫ trφ x 0 = ((ρ ≫ x) * b).left := by
    show (lift ρ b ≫ ((fst T B ≫ x) * snd T B)).left = _
    rw [MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst]
  have e₁ : (lift ρ b).left ≫ trφ x 1 = b.left := by
    show (lift ρ b ≫ snd T B).left = _
    rw [lift_snd]
  rw [Fin.prod_univ_two, e₀, e₁]
  simp


omit [IsCommMonObj B] in
theorem prod_tr_one {T' : Over S} (ρ : T' ⟶ T) (b : T' ⟶ B) {U : Type} [CommGroup U] (h : (T'.left ⟶ B.left) → U) :
    ∏ k : Fin 2, h ((lift ρ b).left ≫ trφ x k) ^ (![1, -1] : Fin 2 → ℤ) k =
      h ((ρ ≫ x) * b).left * (h b.left)⁻¹ := by
  simpa using prod_tr (x := x) ρ b h 1

theorem val_mul_pt (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (u : LB.Gen (LB.LinComb L.L (trφ x) ![1, -1]))
    (hu : u.IsGen) (a b : T ⟶ B) (z : T.left) (J) (hJ : Good L.L z J) :
    val u (lift (𝟙 T) (a * b)).left z J * val u (lift (𝟙 T) (1 : T ⟶ B)).left z J =
      cubV c z J x a b * val u (lift (𝟙 T) a).left z J * val u (lift (𝟙 T) b).left z J := by
  let p := fst T B
  let q := snd T B
  let uu := fun w : T ⊗ B ⟶ B => LB.pullGen L.L _ _ u (lift p w).left
  have gu : ∀ w, (uu w).IsGen := fun w => DVR.pullGen_isGen _ _ _ _ hu _
  have vu : ∀ {T' : Over S} (σ : T' ⟶ T ⊗ B) {z : T'.left} {J}, Good L.L z J → ∀ w,
      val (uu w) σ.left z J = val u (lift (σ ≫ p) (σ ≫ w)).left z J := fun σ z J hJ w =>
    (val_pull hJ _ _ _).trans (by rw [← Over.comp_left, comp_lift])
  let t₁ := LB.mulGen L.L _ _ _ _ (uu ((p ≫ a) * q)) (uu 1)
  let t₂ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ B (x3 B)) thε c.t (lift (p ≫ x) (lift (p ≫ a) q)).left) (uu (p ≫ a))) (uu q)
  have ev : ∀ (w : T ⟶ B) {z : T.left} {J}, Good L.L z J →
      val t₁ (lift (𝟙 T) w).left z J =
        val u (lift (𝟙 T) (a * w)).left z J * val u (lift (𝟙 T) (1 : T ⟶ B)).left z J ∧
      val t₂ (lift (𝟙 T) w).left z J =
        cubV c z J x a w * val u (lift (𝟙 T) a).left z J * val u (lift (𝟙 T) w).left z J := fun w z J hJ => by
    have hp : lift (𝟙 T) w ≫ p = 𝟙 T := lift_fst _ _
    have hq : lift (𝟙 T) w ≫ q = w := lift_snd _ _
    have hp' : ∀ v : T ⟶ B, lift (𝟙 T) w ≫ p ≫ v = v := fun v => by rw [← Category.assoc, hp, Category.id_comp]
    constructor
    · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vu _ hJ _) (vu _ hJ _))).trans ?_
      rw [MonObj.comp_mul, MonObj.comp_one, hp, hq, hp']
    · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (val_cub c _ hJ _ _ _) (vu _ hJ _))) (vu _ hJ _))).trans ?_
      rw [hp, hq, hp', hp']
  refine (ev b hJ).1.symm.trans (Eq.trans ?_ (ev b hJ).2)
  refine gen_unique' L.isLB (fun V _ k => ?_) p.left (lift (𝟙 T) (1 : T ⟶ B)).left
    (by rw [← Over.comp_left, lift_fst, Over.id_left]) (WeilCube.surj_fst hG hB T)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (gu _) (gu _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _) (gu _)) (gu _))
    (fun y I hI => ?_) _ _ z J hJ
  · refine (DVR.prod_sum₂ (K := thK ⊕ Fin 2) (K' := Fin 2) (U := V) _
      (DVR.prod_sum₂ (K := thK) (K' := Fin 2) (U := V) _ (prod_cub (p ≫ x) (p ≫ a) q k) (prod_tr_one p (p ≫ a) k))
      (prod_tr_one p q k)).trans (Eq.trans ?_
      (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_tr_one p ((p ≫ a) * q) k) (prod_tr_one p 1 k)).symm)
    rw [_root_.mul_one, ← _root_.mul_assoc (p ≫ x)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · refine (ev 1 hI).1.trans (Eq.trans ?_ (ev 1 hI).2.symm)
    rw [_root_.mul_one, (isCub_cubV c (T := T) hI).face₃, _root_.one_mul]

theorem val_pow_pt (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (u : LB.Gen (LB.LinComb L.L (trφ x) ![1, -1]))
    (hu : u.IsGen) {N : ℕ} (hx : x ^ N = 1) (b : T ⟶ B) (z : T.left) (J) (hJ : Good L.L z J) :
    cubN (cubV c z J) N 1 x b * val u (lift (𝟙 T) b).left z J ^ N = val u (lift (𝟙 T) (1 : T ⟶ B)).left z J ^ N := by
  let p := fst T B
  let q := snd T B
  have hx' : (p ≫ x) ^ N = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨t, ht, hv⟩ := WeilCube.exists_gen_torsion c N (p ≫ x) q hx'
  obtain ⟨s, hs, hsv⟩ := exists_pow_gen L.isLB u hu N
  let uu := fun w : T ⊗ B ⟶ B => LB.pullGen L.L _ _ s (lift p w).left
  have gu : ∀ w, (uu w).IsGen := fun w => DVR.pullGen_isGen _ _ _ _ hs _
  have vu : ∀ {T' : Over S} (σ : T' ⟶ T ⊗ B) {z : T'.left} {J}, Good L.L z J → ∀ w,
      val (uu w) σ.left z J = val u (lift (σ ≫ p) (σ ≫ w)).left z J ^ N := fun σ z J hJ w =>
    (val_pull hJ _ _ _).trans ((hsv _ _ z J hJ).trans (by rw [← Over.comp_left, comp_lift]))
  let t₁ := LB.mulGen L.L _ _ _ _ t (uu q)
  have ev : ∀ (w : T ⟶ B) {z : T.left} {J}, Good L.L z J →
      val t₁ (lift (𝟙 T) w).left z J = cubN (cubV c z J) N 1 x w * val u (lift (𝟙 T) w).left z J ^ N ∧
      val (uu 1) (lift (𝟙 T) w).left z J = val u (lift (𝟙 T) (1 : T ⟶ B)).left z J ^ N := fun w z J hJ => by
    have hp : lift (𝟙 T) w ≫ p = 𝟙 T := lift_fst _ _
    have hq : lift (𝟙 T) w ≫ q = w := lift_snd _ _
    have hp' : ∀ v : T ⟶ B, lift (𝟙 T) w ≫ p ≫ v = v := fun v => by rw [← Category.assoc, hp, Category.id_comp]
    constructor
    · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _ _ z J hJ) (vu _ hJ _))).trans ?_
      rw [hp, hq, hp']
    · refine (vu _ hJ _).trans ?_
      rw [MonObj.comp_one, hp]
  refine (ev b hJ).1.symm.trans (Eq.trans ?_ (ev b hJ).2)
  refine gen_unique' L.isLB (fun V _ k => ?_) p.left (lift (𝟙 T) (1 : T ⟶ B)).left
    (by rw [← Over.comp_left, lift_fst, Over.id_left]) (WeilCube.surj_fst hG hB T)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (gu _)) (gu _) (fun y I hI => ?_) _ _ z J hJ
  · refine (prod_tr p 1 k N).trans (Eq.trans ?_
      (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 2) (U := V) _ rfl (prod_tr p q k N)).symm)
    rw [_root_.mul_one]
    simp only [Fin.prod_univ_succ, Sum.elim_inl, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.prod_univ_zero]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    module
  · refine (ev 1 hI).1.trans (Eq.trans ?_ (ev 1 hI).2.symm)
    rw [(isCub_cubV c (T := T) hI).N_one, _root_.one_mul]

theorem cubWeil_of_gen : (GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (c : CubicalStr B L) (N : ℕ) (T : Over S) (x y : T ⟶ B), x ^ N = 1 → y ^ N = 1 → (∃ u : LB.Gen (translDiff B L.L x), u.IsGen) → CubWeil c N x y 1) := by
  intro hG S B _ _ hB L c N T x y hx hy ⟨u, hu⟩
  refine ⟨hx, hy, fun z J hJ => ?_⟩
  have C := isCub_cubV c hJ
  obtain ⟨U, hU⟩ : ∃ U : (T ⟶ B) → (T.left.presheaf.stalk z)ˣ,
      ∀ b, U b = val (L := L.L) (φ := trφ x) (ε := ![1, -1]) u (lift (𝟙 T) b).left z J := ⟨_, fun _ => rfl⟩
  have m : ∀ a b, U (a * b) * U 1 = cubV c z J x a b * U a * U b := fun a b => by
    simp only [hU]; exact val_mul_pt c hG hB u hu a b z J hJ
  have k : cubN (cubV c z J) N 1 x y * U y ^ N = U 1 ^ N := by
    simp only [hU]; exact val_pow_pt c hG hB u hu hx y z J hJ
  have b : ∀ n : ℕ, U (y ^ n) * U 1 ^ n = U 1 * (cubN (cubV c z J) n 1 y x * U y ^ n) := fun n => by
    induction n with
    | zero => simp [cubN]
    | succ n ih =>
      have e := m (y ^ n) y
      rw [C.s01, C.s12] at e
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
      rw [pow_succ, pow_succ, pow_succ]
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul e
      have ih' := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at e' ih' ⊢
      linear_combination (norm := abel) e' + ih'
  have b' := b N
  rw [hy] at b'
  rw [(gm (𝟙 T.left) z ⊤).map_one, _root_.one_mul]
  exact mul_right_cancel (k.trans (mul_left_cancel b'))

end GlobalTheory.UU.KerPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAffineWeightUnits
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem TQ.exists_affine_weight_units [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X)
    (b : Q.B.left) : ∃ V : Q.B.left.Opens, IsAffineOpen V ∧ b ∈ V ∧
      ∃ u : Multiplicative X →* Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ, ∀ χ : X, IsWt Q.i _ (u (Multiplicative.ofAdd χ)).val χ := by
  let e := Module.Free.chooseBasis ℤ X
  choose W hW v hv using fun k => Q.loc b (e k)
  have ho : IsOpen (⋂ k, (W k : Set Q.B.left)) := isOpen_iInter_of_finite fun k => (W k).isOpen
  obtain ⟨V, hV, hbV, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Q.B.left.isBasis_affineOpens
    (show b ∈ (⟨_, ho⟩ : Q.B.left.Opens) from Set.mem_iInter.2 hW)
  have hk : ∀ k, Q.q.left ⁻¹ᵁ V ≤ Q.q.left ⁻¹ᵁ W k := fun k =>
    Q.q.left.preimage_mono fun x hx => Set.mem_iInter.1 (hle hx) k
  let w : _ → Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ := fun k =>
    Units.map (G.left.presheaf.map (homOfLE (hk k)).op).hom.toMonoidHom (v k)
  let l : X →ₗ[ℤ] Additive Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ := e.constr ℤ fun k => Additive.ofMul (w k)
  let H : AddSubgroup X :=
    { carrier := {χ | IsWt Q.i _ (Additive.toMul (l χ)).val χ}
      zero_mem' := by
        show IsWt Q.i _ (Additive.toMul (l 0)).val 0
        rw [map_zero]; exact isWt_one
      add_mem' := fun {a c} ha hc => by
        show IsWt Q.i _ (Additive.toMul (l (a + c))).val (a + c)
        rw [map_add (f := _)]; exact IsWt.mul ha hc
      neg_mem' := fun {a} ha => by
        show IsWt Q.i _ (Additive.toMul (l (-a))).val (-a)
        rw [map_neg]; exact IsWt.inv ha }
  have hH : Submodule.span ℤ (Set.range e) ≤ H.toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show IsWt Q.i _ (Additive.toMul (l (e k))).val (e k)
    rw [Module.Basis.constr_basis]
    exact (hv k).res (hk k)
  refine ⟨V, hV, hbV, AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom, fun χ => ?_⟩
  exact hH (e.mem_span χ)

theorem TQ.exists_local_section [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X)
    (b : Q.B.left) : ∃ (V : Q.B.left.Opens) (hV : IsAffineOpen V), b ∈ V ∧
      ∃ s : Spec Γ(Q.B.left, V) ⟶ G.left, s ≫ Q.q.left = hV.fromSpec := by
  obtain ⟨V, hV, hb, u, hu⟩ := Q.exists_affine_weight_units b
  have := Q.q_affine
  obtain ⟨hU, hbij⟩ := isAffineOpen_and_bijective_of_weight_units S X G Q.B Q.q Q.i Q.q_hom Q.i_hom Q.q_flat Q.q_surj
    inferInstance Q.isKernel V hV u hu
  let φ := RingEquiv.ofBijective _ hbij
  let ε : AddMonoidAlgebra Γ(Q.B.left, V) X →+* Γ(Q.B.left, V) :=
    (AddMonoidAlgebra.lift Γ(Q.B.left, V) Γ(Q.B.left, V) X 1).toRingHom
  let r : Γ(G.left, Q.q.left ⁻¹ᵁ V) ⟶ Γ(Q.B.left, V) := CommRingCat.ofHom (ε.comp φ.symm.toRingHom)
  have hr : Q.q.left.appLE V _ le_rfl ≫ r = 𝟙 _ := by
    rw [← Scheme.Hom.app_eq_appLE]
    ext a
    have h : φ (AddMonoidAlgebra.single 0 a) = (Q.q.left.app V).hom a :=
      (AddMonoidAlgebra.liftNC_single _ _ 0 a).trans
        ((congrArg (_ * ·) (((Units.coeHom _).comp u).map_one)).trans (_root_.mul_one _))
    change ε (φ.symm ((Q.q.left.app V).hom a)) = a
    rw [← h, RingEquiv.symm_apply_apply]
    simp [ε]
  refine ⟨V, hV, hb, Spec.map r ≫ hU.fromSpec, ?_⟩
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec Q.q.left hV hU le_rfl, ← Category.assoc,
    ← Spec.map_comp, hr, Spec.map_id, Category.id_comp]

theorem TQ.exists_lift [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X)
    {A : Type} [CommRing A] [IsLocalRing A] {p : Spec (CommRingCat.of A) ⟶ S} (b : Over.mk p ⟶ Q.B) :
    ∃ g : Over.mk p ⟶ G, g ≫ Q.q = b := by
  let b' : Spec (CommRingCat.of A) ⟶ Q.B.left := b.left
  obtain ⟨V, hV, hb, s, hs⟩ := Q.exists_local_section (b' (IsLocalRing.closedPoint A))
  have hr : Set.range b' ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of A) b' hb).ge (Set.mem_univ y)
  have h : (IsOpenImmersion.lift hV.fromSpec b' hr ≫ s) ≫ Q.q.left = b' := by
    rw [Category.assoc, hs, IsOpenImmersion.lift_fac]
  refine ⟨Over.homMk (IsOpenImmersion.lift hV.fromSpec b' hr ≫ s) ?_, Over.OverMorphism.ext h⟩
  rw [← Over.w Q.q, ← Category.assoc]
  exact (congrArg (· ≫ Q.B.hom) h).trans (Over.w b)

theorem exists_pow_eq_splitTorus [Module.Free ℤ X] {Z : Over S} {N : ℕ}
    (h : ∀ a : Γ(Z.left, ⊤)ˣ, ∃ r, r ^ N = a) (t : Z ⟶ splitTorus S X) : ∃ t' : Z ⟶ splitTorus S X, t' ^ N = t := by
  let e := Module.Free.chooseBasis ℤ X
  let E := splitTorusPointsEquiv S X Z
  choose r hr using h
  let l : X →ₗ[ℤ] Additive Γ(Z.left, ⊤)ˣ := e.constr ℤ fun k => Additive.ofMul (r (chV t (e k)))
  let m : X →ₗ[ℤ] Additive Γ(Z.left, ⊤)ˣ := (MonoidHom.toAdditiveRight (E t)).toIntLinearMap
  have hl : N • l = m := e.ext fun k => by
    rw [LinearMap.smul_apply, Module.Basis.constr_basis]
    exact congrArg Additive.ofMul (hr _)
  refine ⟨E.symm (AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom), E.injective ?_⟩
  rw [map_pow, MulEquiv.apply_symm_apply]
  exact MonoidHom.ext fun χ => congrArg Additive.toMul (LinearMap.congr_fun hl (Multiplicative.toAdd χ))

theorem torusQuotient_points_lift :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G]
      [IsCommMonObj G] (Q : TQ G X) (A : Type) [CommRing A] [IsLocalRing A] (p : Spec (CommRingCat.of A) ⟶ S),
      (∀ b : Over.mk p ⟶ Q.B, ∃ g : Over.mk p ⟶ G, g ≫ Q.q = b) ∧
      ∀ N : ℕ, (∀ a : Aˣ, ∃ r : Aˣ, r ^ N = a) → ∀ b : Over.mk p ⟶ Q.B, b ^ N = 1 →
        ∃ g : Over.mk p ⟶ G, g ^ N = 1 ∧ g ≫ Q.q = b := by
  intro S X _ _ _ G _ _ Q A _ _ p
  refine ⟨Q.exists_lift, fun N hN b hb => ?_⟩
  have := Q.q_hom
  have := Q.i_hom
  obtain ⟨g, rfl⟩ := Q.exists_lift b
  have h₁ : (g ^ N) ≫ Q.q = toUnit _ ≫ η[Q.B] := by rw [MonObj.pow_comp, hb, Hom.one_def]
  let e : Aˣ ≃* Γ(Spec (CommRingCat.of A), ⊤)ˣ :=
    Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.toMulEquiv
  obtain ⟨t, ht⟩ := exists_pow_eq_splitTorus (Z := Over.mk p) (N := N) (fun a => by
    obtain ⟨r, hr⟩ := hN (e.symm a)
    exact ⟨e r, (map_pow e r N).symm.trans ((congrArg e hr).trans (e.apply_symm_apply a))⟩)
    (Q.isKernel.lift _ _ h₁)
  have h₂ : (t ≫ Q.i) ^ N = g ^ N := by rw [← MonObj.pow_comp, ht, IsPullback.lift_fst]
  have h₃ : (t ≫ Q.i) ≫ Q.q = 1 := by
    rw [Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (t ≫ toUnit _) (toUnit _)]
  refine ⟨(t ≫ Q.i)⁻¹ * g, ?_, ?_⟩
  · rw [mul_pow, inv_pow, h₂, inv_mul_cancel]
  · rw [MonObj.mul_comp, GrpObj.inv_comp, h₃, inv_one, _root_.one_mul]

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothProjOfFree
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem TQ.smooth_proj_of_free {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {G : Over S} [GrpObj G] (Q : TQ G X) : Smooth Q.q.left := by
  have := Q.q_hom
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  have := (H1.torus_dim S X).smooth
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ((H1.torsor_pullback Q.i Q.q Q.isKernel).map (Over.forget _)).flip
    ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact Q.q.left)⟩ ?_
  exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this

theorem TQ.dim_eq_add_finrank :
    (∀ (S : Scheme.{0}) [Nonempty S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] (Q : TQ G X) (g g' : ℕ), SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g' Q.B.hom → g = g' + Module.finrank ℤ X) := by
  intro S hS X _ _ _ G _ Q g g' dG dB
  obtain ⟨y⟩ := hS
  have := Q.i_hom
  have := Q.smooth_proj_of_free
  obtain ⟨m, W, hW, d₁⟩ := H1.exists_dim Q.q.left (eSec G y)
  have g₂ : m = Module.finrank ℤ X := H1.dim_base (Q.isKernel.map (Over.forget _)) d₁ (H1.torus_dim S X) (eSec _ y)
    ((congrArg (fun k => k.left y ∈ W) (IsMonHom.one_hom Q.i)).mpr hW)
  have d₂ : SmoothOfRelativeDimension (m + g') (W.ι ≫ G.hom) := by
    rw [← Over.w Q.q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom) := inferInstance
  have := H1.dim_unique _ d₂ d₃ ⟨_, hW⟩
  omega

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompRedIff
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.RingPoint

theorem toSpec_appTop {Z : Scheme.{0}} {D : Type} [CommRing D] (θ : D →+* Γ(Z, ⊤)) (a : Γ(Spec (CommRingCat.of D), ⊤)) :
    (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop.hom a = θ ((Scheme.ΓSpecIso (CommRingCat.of D)).hom.hom a) := by
  have h : (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of D)).hom ≫ CommRingCat.ofHom θ := by
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom θ : CommRingCat.of D ⟶ Γ(Z, ⊤))
  exact congrArg (fun q => q.hom a) h

theorem exists_ringPoint {S : Scheme.{0}} (Y : Over S) [IsAffine Y.left] (D : Type) [CommRing D]
    (κ : Γ(Y.left, ⊤) →+* D) : ∃ (U : Over S) (y₀ : U ⟶ Y) (e : Γ(U.left, ⊤) ≃+* D), IsAffine U.left ∧
      (∀ b, e (y₀.left.appTop.hom b) = κ b) ∧
      ∀ (Z : Over S) (y : Z ⟶ Y) (θ : D →+* Γ(Z.left, ⊤)), (∀ b, θ (κ b) = y.left.appTop.hom b) →
        ∃ σ : Z ⟶ U, σ ≫ y₀ = y ∧ ∀ a, σ.left.appTop.hom a = θ (e a) := by
  let p : Spec (CommRingCat.of D) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom κ : Γ(Y.left, ⊤) ⟶ CommRingCat.of D) ≫ Y.left.isoSpec.inv
  have hp : ∀ b, (Scheme.ΓSpecIso (CommRingCat.of D)).hom.hom (p.appTop.hom b) = κ b := fun b => by
    have h : p.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of D)).hom = CommRingCat.ofHom κ := by
      rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc,
        ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop]
      simp
    exact congrArg (fun q => q.hom b) h
  refine ⟨Over.mk (p ≫ Y.hom), Over.homMk p rfl, (Scheme.ΓSpecIso (CommRingCat.of D)).commRingCatIsoToRingEquiv,
    inferInstanceAs (IsAffine (Spec _)), hp, fun Z y θ hθ => ?_⟩
  have h : (Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) ≫ p = y.left := by
    refine ext_of_isAffine ?_
    ext b
    rw [Scheme.Hom.comp_appTop]
    exact (toSpec_appTop θ _).trans ((congrArg θ (hp b)).trans (hθ b))
  refine ⟨Over.homMk (Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) ?_, Over.OverMorphism.ext h, toSpec_appTop θ⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Y.hom) h).trans (Over.w y))

def strMap {A : Type} [CommRing A] (Z : Over (Spec (CommRingCat.of A))) : A →+* Γ(Z.left, ⊤) :=
  Z.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem appTop_strMap {A : Type} [CommRing A] {Z Y : Over (Spec (CommRingCat.of A))} (y : Z ⟶ Y) (a : A) :
    y.left.appTop.hom (strMap Y a) = strMap Z a := by
  rw [strMap, strMap, ← Over.w y, Scheme.Hom.comp_appTop]; rfl

theorem exists_comp_red_iff {A : Type} [CommRing A] (J : Ideal A) (Z : Over (Spec (CommRingCat.of A))) :
    (∃ s, s ≫ red J = Z.hom) ↔ ∀ a ∈ J, strMap Z a = 0 := by
  have nat : ∀ a, (red J).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ J))).inv.hom (Ideal.Quotient.mk J a) := fun a =>
    congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk J) : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ J))).symm
  constructor
  · rintro ⟨s, hs⟩ a ha
    rw [strMap, ← hs, Scheme.Hom.comp_appTop]
    change s.appTop.hom ((red J).appTop.hom _) = 0
    rw [nat, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero, map_zero]
  · intro h
    refine ⟨Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J (strMap Z) h)), ext_of_isAffine ?_⟩
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of A)).inv]
    ext a
    rw [Scheme.Hom.comp_appTop]
    refine (congrArg _ (nat a)).trans ((toSpec_appTop _ _).trans ?_)
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
    rfl

end GlobalTheory.UU.RingPoint
end
end
