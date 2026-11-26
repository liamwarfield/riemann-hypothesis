module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsogenyPullbackHeckeModuliObject
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismOfMultiplicativeSectionFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingAutOfRelAmple
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_iso_of_sectionRing_aut_of_relAmple : ∀ (K : Type) [CommRing K] (X : Over (Spec (CommRingCat.of K))) [IsProper X.hom] (L : LB X.left), L.IsLB → RelAmple X L → ∀ θ : ∀ n : ℕ, 1 ≤ n → (H0 L n ≃ H0 L n), (∀ (n : ℕ) (hn : 1 ≤ n) (c : K) (a b d : H0 L n), (∀ j, d.f j = a.f j + resTop _ (scal X.hom c) * b.f j) → ∀ j, (θ n hn d).f j = (θ n hn a).f j + resTop _ (scal X.hom c) * (θ n hn b).f j) → (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 L n) (b : H0 L m) (d : H0 L (n + m)), (∀ j : Fin 1 → L.ι, (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from d.f j) = (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from a.f j) * (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from b.f j)) → ∀ j : Fin 1 → L.ι, (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) = (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ n hn a).f j) * (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ m hm b).f j)) → ∃ Φ₀ : X ≅ X, ∃ w : LB.Iso L (L.pull Φ₀.hom.left), w.IsGen ∧ ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 L n), (∀ (Z : Scheme.{0}) (r : Z ⟶ X.left) (z : Z) (p : Fin 1 → L.ι) (q : Fin 1 → L.ι), (∀ κ, (Φ₀.hom.left) ((fun _ : Fin 1 => 𝟙 X.left) κ (r z)) ∈ L.U (p κ)) → (∀ κ, (fun _ : Fin 1 => 𝟙 X.left) κ (r z) ∈ L.U (q κ)) → Geo.Tor.gs (r ≫ Φ₀.hom.left) z (LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) p) ((θ n hn a).f p) = (∏ κ, Geo.Tor.gw w (r ≫ (fun _ : Fin 1 => 𝟙 X.left) κ) z (p κ) (q κ) ^ (fun _ : Fin 1 => (n : ℤ)) κ).val * Geo.Tor.gs r z (LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) q) ((a).f q)) := by
  intro K _ X _ L hL hA θ hlin hmul
  have h := isAmpleLB_of_relAmple_of_isAffine X hL hA
  have := h.compactSpace
  have := h.quasiSeparatedSpace
  obtain ⟨-, m, hm, M, s, hs⟩ := isAffineOpen_nonzeroLocus_of_relAmple K X L hL hA 1 le_rfl
  have hN : 1 ≤ 1 * m := by omega
  have haff := (isAffineOpen_nonzeroLocus_of_relAmple K X L hL hA (1 * m) hN).1
  obtain ⟨Φ, hΦ⟩ := exists_iso_of_sectionRing_equiv K X X L L hL hL θ hlin hmul
    ⟨1 * m, hN, H0 L (1 * m), id,
      top_le_iff.1 (hs.ge.trans (iSup_le fun i => le_iSup (fun a : H0 L (1 * m) => nonzeroLocus a) (s i))),
      top_le_iff.1 (hs.ge.trans (iSup_le fun i => le_iSup_of_le ((θ (1 * m) hN).symm (s i))
        (congrArg nonzeroLocus ((θ (1 * m) hN).apply_symm_apply (s i))).ge)),
      fun a => ⟨haff _, haff _⟩⟩
  exact ⟨Φ, exists_iso_of_sectionRing K X X L L hL hL θ hlin hmul Φ.hom.left hΦ
    (exists_sec_succ_of_relAmple K X L hL hA)⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperAndRelAmpleLPow
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isProper_and_relAmple_lPow :
    ∀ (F : Type) [CommRing F] (S : Scheme.{0}) (P : PolAV S) (t : Spec (CommRingCat.of F) ⟶ S) [IsLocalRing F] (N : ℕ), 1 ≤ N → IsProper (fst (Over.mk t) P.A).left ∧ RelAmple (S := Spec (CommRingCat.of F)) (Over.mk (fst (Over.mk t) P.A).left) (LPow P.A P.L (N : ℤ) (Over.mk t)) := by
  intro F _ S P t _ N hN
  have hP := P.isAb.proper
  have H : IsPullback (snd (Over.mk t) P.A).left (fst (Over.mk t) P.A).left P.A.hom t :=
    (IsPullback.of_hasPullback t P.A.hom).flip
  have hp : IsProper (fst (Over.mk t) P.A).left := MorphismProperty.of_isPullback (P := @IsProper) H hP
  refine ⟨hp, ?_⟩
  have hp' : IsProper (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left).hom := hp
  have hL := LB.isLB_pull P.isLB (snd (Over.mk t) P.A).left
  have hM : (LPow P.A P.L (N : ℤ) (Over.mk t)).IsLB := LB.isLB_linComb P.isLB _ _
  have h₁ := (relAmple_iff_isAmpleLB_of_isAffine
    (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left) hL).1
    (AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample H)
  refine (relAmple_iff_isAmpleLB_of_isAffine
    (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left) hM).2
    (((isAmpleLB_pow_iff hL hN).2 h₁).of_lbIso hM ?_)
  exact LBIso.chartPull (CoprimeTorsion.chartPullLPow P.A P.L (Over.mk t) N) (chartPullPowPull P.L _ N)
    (lbIso_refl (isLB_lbPow P.isLB N))

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEquivPow
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PowSections

variable {Y : Scheme.{0}}

theorem sec_ext {M : LB Y} {s t : LB.Sec M} (h : ∀ i, s.f i = t.f i) : s = t := by
  cases s; cases t
  congr 1
  exact funext h

def refine {M M' : LB Y} (σ : M'.ι → M.ι) (hU : ∀ i, M'.U i ≤ M.U (σ i))
    (hg : ∀ i j y, y ∈ M'.U i → y ∈ M'.U j →
      gm (𝟙 Y) y _ (M'.g i j) = gm (𝟙 Y) y _ (M.g (σ i) (σ j))) (s : LB.Sec M) : LB.Sec M' where
  f i := (Y.presheaf.map (homOfLE (hU i)).op).hom (s.f (σ i))
  compat i j := fn_ext fun y hy => by
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ M.U (σ i) ⊓ M.U (σ j) := ⟨hU i hy.1, hU j hy.2⟩
    have e := congrArg (gs (𝟙 Y) y _) (s.compat (σ i) (σ j))
    rw [gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_unit _ y _ hm] at e
    rw [gs_mul _ y _ hy, gs_res _ y inf_le_left hy, gs_res _ y inf_le_right hy, gs_unit _ y _ hy, gs_res _ y (hU i) hy.1,
      gs_res _ y (hU j) hy.2, hg i j y hy.1 hy.2]
    exact e

theorem gs_refine {M M' : LB Y} (σ : M'.ι → M.ι) (hU : ∀ i, M'.U i ≤ M.U (σ i))
    (hg : ∀ i j y, y ∈ M'.U i → y ∈ M'.U j →
      gm (𝟙 Y) y _ (M'.g i j) = gm (𝟙 Y) y _ (M.g (σ i) (σ j))) (s : LB.Sec M) (i : M'.ι) (y : Y)
    (hy : y ∈ M'.U i) :
    gs (𝟙 Y) y _ ((refine σ hU hg s).f i) = gs (𝟙 Y) y _ (s.f (σ i)) :=
  gs_res (𝟙 Y) y (hU i) hy _

def secEquiv {M M' : LB Y} (σ : M'.ι ≃ M.ι) (hU : ∀ i, M'.U i = M.U (σ i))
    (hg : ∀ i j y, y ∈ M'.U i → y ∈ M'.U j →
      gm (𝟙 Y) y _ (M'.g i j) = gm (𝟙 Y) y _ (M.g (σ i) (σ j))) : LB.Sec M ≃ LB.Sec M' :=
  have hU' : ∀ i, M.U i ≤ M'.U (σ.symm i) := fun i => by rw [hU, σ.apply_symm_apply]
  have hg' : ∀ i j y, y ∈ M.U i → y ∈ M.U j →
      gm (𝟙 Y) y _ (M.g i j) = gm (𝟙 Y) y _ (M'.g (σ.symm i) (σ.symm j)) := fun i j y hi hj => by
    rw [hg _ _ y (hU' i hi) (hU' j hj)]
    obtain ⟨i, rfl⟩ := σ.surjective i
    obtain ⟨j, rfl⟩ := σ.surjective j
    rw [σ.apply_symm_apply, σ.apply_symm_apply]
  { toFun := refine σ (fun i => (hU i).le) hg
    invFun := refine σ.symm hU' hg'
    left_inv := fun s => sec_ext fun i => fn_ext fun y hy => by
      rw [gs_refine _ _ _ _ _ y hy, gs_refine _ _ _ _ _ y (hU' i hy), σ.apply_symm_apply]
    right_inv := fun s => sec_ext fun i => fn_ext fun y hy => by
      rw [gs_refine _ _ _ _ _ y hy, gs_refine _ _ _ _ _ y ((hU i).le hy), σ.symm_apply_apply] }

theorem gs_secEquiv {M M' : LB Y} (σ : M'.ι ≃ M.ι) (hU : ∀ i, M'.U i = M.U (σ i))
    (hg : ∀ i j y, y ∈ M'.U i → y ∈ M'.U j →
      gm (𝟙 Y) y _ (M'.g i j) = gm (𝟙 Y) y _ (M.g (σ i) (σ j))) (s : LB.Sec M) (i : M'.ι) (y : Y)
    (hy : y ∈ M'.U i) :
    gs (𝟙 Y) y _ ((secEquiv σ hU hg s).f i) = gs (𝟙 Y) y _ (s.f (σ i)) :=
  gs_res (𝟙 Y) y (hU i).le hy _

theorem exists_equiv_pow (M : LB Y) (n : ℕ) (g : ∀ i j, Γ(Y, M.U i ⊓ M.U j)ˣ)
    (hg : ∀ i j y, y ∈ M.U i → y ∈ M.U j →
      gm (𝟙 Y) y _ (g i j) = gm (𝟙 Y) y _ (M.g i j) ^ (n : ℤ)) :
    ∃ E : H0 M n ≃ LB.Sec (⟨M.ι, M.U, g⟩ : LB Y),
      ∀ a (j : M.ι) (y : Y), y ∈ M.U j →
        gs (𝟙 _) y _ ((E a).f j) = gs (𝟙 _) y _ (a.f (fun _ => j)) := by
  have m₁ : ∀ (j : M.ι) (y : Y), y ∈ M.U j →
      y ∈ LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => j) := fun j y hy => Set.mem_iInter.2 fun _ => hy
  let σ : M.ι ≃ (Fin 1 → M.ι) :=
    ⟨fun j _ => j, fun J => J 0, fun _ => rfl, fun J => funext fun k => by rw [Subsingleton.elim k 0]⟩
  have hU : ∀ j : M.ι, M.U j = LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => j) :=
    fun j => le_antisymm (fun y hy => m₁ j y hy) (fun y hy => Set.mem_iInter.1 hy 0)
  have hg' : ∀ i j y, y ∈ M.U i → y ∈ M.U j → gm (𝟙 Y) y _ (g i j) = gm (𝟙 Y) y _
      ((LB.LinComb M (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (n : ℤ))).g (fun _ => i) (fun _ => j)) := by
    intro i j y hi hj
    have e := gm_linComb M (fun _ : Fin 1 => 𝟙 Y) (fun _ => (n : ℤ)) (𝟙 Y) y (fun _ => i) (fun _ => j)
      (m₁ i y hi) (m₁ j y hj)
    rw [Fin.prod_univ_one, Category.id_comp] at e
    rw [hg i j y hi hj]
    exact e.symm
  exact ⟨secEquiv (M := LB.LinComb M (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (n : ℤ)))
    (M' := ⟨M.ι, M.U, g⟩) σ hU hg',
    fun a j y hy => gs_secEquiv (M := LB.LinComb M (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (n : ℤ)))
      (M' := ⟨M.ι, M.U, g⟩) σ hU hg' a j y hy⟩

theorem exists_equiv {X : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N n : ℕ) :
    ∃ E : H0 (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (N : ℤ))) n ≃
        LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => ((N * n : ℕ) : ℤ))),
      ∀ a (j : Fin 1 → L.ι) (y : Y), p y ∈ L.U (j 0) →
        gs (𝟙 _) y _ ((E a).f j) = gs (𝟙 _) y _ (a.f (fun _ => j)) := by
  obtain ⟨E, hE⟩ := exists_equiv_pow (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (N : ℤ))) n
    (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => ((N * n : ℕ) : ℤ))).g (fun i j y hi hj => by
      have e := gm_linComb L (fun _ : Fin 1 => p) (fun _ => (N : ℤ)) (𝟙 Y) y i j hi hj
      have e' := gm_linComb L (fun _ : Fin 1 => p) (fun _ => ((N * n : ℕ) : ℤ)) (𝟙 Y) y i j hi hj
      rw [Fin.prod_univ_one] at e e'
      refine e'.trans (Eq.trans ?_ (congrArg (· ^ (n : ℤ)) e.symm))
      rw [Nat.cast_mul, zpow_mul])
  refine ⟨E, fun a j y hy => hE a j y (Set.mem_iInter.2 fun k => ?_)⟩
  obtain rfl : k = 0 := Subsingleton.elim _ _
  exact hy

end PowSections

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismOfMultiplicativeSectionFamily
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SectionAut

abbrev PP {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (a : ℤ) : LB Y :=
  LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => a)

theorem mem_one {X Y : Scheme.{0}} {L : LB X} {p : Y ⟶ X} {j : Fin 1 → L.ι} {y : Y} :
    y ∈ LB.wchart L (fun _ : Fin 1 => p) j ↔ p y ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem exists_equiv {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N n : ℕ) :
    ∃ E : H0 (PP L p N) n ≃ LB.Sec (PP L p ((N * n : ℕ) : ℤ)),
      ∀ a (j : Fin 1 → L.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ LB.wchart L (fun _ : Fin 1 => p) j →
        gs r z (LB.wchart L (fun _ : Fin 1 => p) j) ((E a).f j) =
          gs r z (LB.wchart (PP L p N) (fun _ : Fin 1 => 𝟙 Y) (fun _ => j)) (a.f (fun _ => j)) := by
  obtain ⟨E, hE⟩ := PowSections.exists_equiv L p N n
  refine ⟨E, fun a j Z r z hz => ?_⟩
  have le : LB.wchart L (fun _ : Fin 1 => p) j ≤ LB.wchart (PP L p N) (fun _ : Fin 1 => 𝟙 Y) (fun _ => j) :=
    fun y hy => Set.mem_iInter.2 fun _ => hy
  have e : (E a).f j = (Y.presheaf.map (homOfLE le).op).hom (a.f (fun _ => j)) :=
    fn_ext fun y hy => (hE a j y (mem_one.1 hy)).trans (gs_res (𝟙 Y) y le hy _).symm
  exact (congrArg (gs r z _) e).trans (gs_res r z le hz _)

theorem exists_gen_of_iso {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N n : ℕ) (F ψ : Y ⟶ Y) (hψ : ψ ≫ F = 𝟙 Y)
    (m : Y ⟶ X) (hm : ψ ≫ p = m) (w : LB.Iso (PP L p N) ((PP L p N).pull F)) (hw : w.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![p, m] ![((N * n : ℕ) : ℤ), -((N * n : ℕ) : ℤ)]), α.IsGen ∧
      ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![p, m] j →
        gm (𝟙 Y) y (LB.wchart L ![p, m] j) (α.s j) = Geo.Tor.gw w ψ y (fun _ => j 0) (fun _ => j 1) ^ (n : ℤ) := by
  subst hm
  have hF : ∀ y, F (ψ y) = y := fun y => by
    rw [← Scheme.Hom.comp_apply, hψ]; rfl
  have h0 : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![p, ψ ≫ p] j →
      F (ψ y) ∈ (PP L p N).U (fun _ => j 0) := fun j y hy => by
    rw [hF]; exact mem_one.2 (Set.mem_iInter.1 hy 0)
  have h1 : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![p, ψ ≫ p] j →
      ψ y ∈ (PP L p N).U (fun _ => j 1) := fun j y hy => mem_one.2 (Set.mem_iInter.1 hy 1)
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L ![p, ψ ≫ p] j ≤
      ψ ⁻¹ᵁ (((PP L p N).pull F).U (fun _ _ => j 0) ⊓ (PP L p N).U (fun _ => j 1)) := fun j y hy =>
    ⟨mem_pull.2 (h0 j y hy), h1 j y hy⟩
  let α : LB.Gen (LB.LinComb L (K := Fin 2) ![p, ψ ≫ p] ![((N * n : ℕ) : ℤ), -((N * n : ℕ) : ℤ)]) :=
    ⟨fun j => res (le j) (pullU ψ _ (w.s (fun _ _ => j 0, fun _ => j 1))) ^ (n : ℤ)⟩
  have hα : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![p, ψ ≫ p] j →
      gm (𝟙 Y) y (LB.wchart L ![p, ψ ≫ p] j) (α.s j) =
        Geo.Tor.gw w ψ y (fun _ => j 0) (fun _ => j 1) ^ (n : ℤ) := fun j y hy =>
    (map_zpow _ _ _).trans (congrArg (· ^ (n : ℤ))
      ((gm_res (𝟙 Y) y (le j) hy _).trans (gm_pull (𝟙 Y) ψ y (((PP L p N).pull F).U (fun _ _ => j 0) ⊓ (PP L p N).U (fun _ => j 1)) (le j hy) _)))
  refine ⟨α, isGen_of_gm α fun y j j' hj hj' => ?_, hα⟩
  have e := (isGen_iff w).1 hw Y ψ y _ _ _ _ (h0 j y hj) (h0 j' y hj') (h1 j y hj) (h1 j' y hj')
  have e0 := gm_linComb L (fun _ : Fin 1 => p) (fun _ => (N : ℤ)) (ψ ≫ F) y (fun _ => j 0) (fun _ => j' 0)
    (h0 j y hj) (h0 j' y hj')
  have e1 := gm_linComb L (fun _ : Fin 1 => p) (fun _ => (N : ℤ)) ψ y (fun _ => j 1) (fun _ => j' 1)
    (h1 j y hj) (h1 j' y hj')
  rw [Fin.prod_univ_one] at e0 e1
  have e' := e.trans (congrArg₂ (fun a b => a * b⁻¹ * _) e0 e1)
  rw [hα j y hj, hα j' y hj', e', trF, Fin.prod_univ_two, hψ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp, mul_zpow, inv_zpow, ← zpow_mul,
    Nat.cast_mul, zpow_neg]

theorem chart_le {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N : ℤ) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => p) j ≤ LB.wchart (PP L p N) (fun _ : Fin 1 => 𝟙 Y) (fun _ => j) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy

def rho {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N : ℤ) (j : Fin 1 → L.ι) :
    Γ(Y, LB.wchart (PP L p N) (fun _ : Fin 1 => 𝟙 Y) (fun _ => j)) →+* Γ(Y, LB.wchart L (fun _ : Fin 1 => p) j) :=
  (Y.presheaf.map (homOfLE (chart_le L p N j)).op).hom

theorem rho_injective {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N : ℤ) (j : Fin 1 → L.ι) :
    Function.Injective (rho L p N j) := fun a b h => fn_ext fun y hy => by
  have hy' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : Fin 1 => p) j := Set.mem_iInter.1 hy 0
  exact (gs_res (𝟙 Y) y (chart_le L p N j) hy' a).symm.trans ((congrArg (gs (𝟙 Y) y _) h).trans
    (gs_res (𝟙 Y) y (chart_le L p N j) hy' b))

theorem rho_resTop {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N : ℤ) (j : Fin 1 → L.ι) (c : Γ(Y, ⊤)) :
    rho L p N j (resTop _ c) = resTop _ c := fn_ext fun y hy =>
  (gs_res (𝟙 Y) y (chart_le L p N j) hy _).trans ((gs_res (𝟙 Y) y le_top (chart_le L p N j hy) c).trans
    (gs_res (𝟙 Y) y le_top hy c).symm)

theorem exists_iso {K : Type} [CommRing K] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    (Y : Over (Spec (CommRingCat.of K))) [IsProper Y.hom] (p : Y.left ⟶ X) (N : ℕ) (hA : RelAmple Y (PP L p N))
    (Φ : ∀ n : ℕ, 1 ≤ n → LB.Sec (PP L p ((N * n : ℕ) : ℤ)) ≃ LB.Sec (PP L p ((N * n : ℕ) : ℤ)))
    (hlin : ∀ n hn (c : K) (s s' s'' : LB.Sec (PP L p ((N * n : ℕ) : ℤ))),
      (∀ j, s''.f j = resTop _ (scal Y.hom c) * s.f j + s'.f j) →
      ∀ j, (Φ n hn s'').f j = resTop _ (scal Y.hom c) * (Φ n hn s).f j + (Φ n hn s').f j)
    (hmul : ∀ n m hn hm hnm (s : LB.Sec (PP L p ((N * n : ℕ) : ℤ))) (s' : LB.Sec (PP L p ((N * m : ℕ) : ℤ)))
      (s'' : LB.Sec (PP L p ((N * (n + m) : ℕ) : ℤ))),
      (∀ j, @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) (s''.f j) =
        @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) (s.f j) *
          @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) (s'.f j)) →
      ∀ j, @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((Φ (n + m) hnm s'').f j) =
        @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((Φ n hn s).f j) *
          @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((Φ m hm s').f j)) :
    ∃ ψ : Y ≅ Y, ∀ (m : Y.left ⟶ X), ψ.hom.left ≫ p = m → ∀ n hn,
      ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![p, m] ![((N * n : ℕ) : ℤ), -((N * n : ℕ) : ℤ)]), α.IsGen ∧
        ∀ s (j : Fin 2 → L.ι) (y : Y.left), y ∈ LB.wchart L ![p, m] j →
          gs (𝟙 _) y (LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 0)) ((Φ n hn s).f (fun _ => j 0)) =
            (gm (𝟙 _) y (LB.wchart L ![p, m] j) (α.s j)).val *
              gs ψ.hom.left y (LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 1)) (s.f (fun _ => j 1)) := by
  choose E hE using fun n => exists_equiv L p N n
  have hE' : ∀ n a j, @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((E n a).f j) =
      rho L p N j (a.f (fun _ => j)) := fun n a j =>
    fn_ext fun y hy => (hE n a j _ (𝟙 _) y hy).trans (gs_res (𝟙 _) y (chart_le L p N j) hy _).symm
  let θ : ∀ n : ℕ, 1 ≤ n → (H0 (PP L p N) n ≃ H0 (PP L p N) n) := fun n hn => (E n).trans ((Φ n hn).trans (E n).symm)
  have hθE : ∀ n hn a, E n (θ n hn a) = Φ n hn (E n a) := fun n hn a => (E n).apply_symm_apply _
  have hθ : ∀ n hn a j, rho L p N j ((θ n hn a).f (fun _ => j)) =
      @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((Φ n hn (E n a)).f j) := fun n hn a j => by
    rw [← hE', hθE]
  have one : ∀ j : Fin 1 → (PP L p N).ι, ∃ i, j = fun _ => i := fun j =>
    ⟨j 0, funext fun k => by rw [Subsingleton.elim k 0]⟩
  obtain ⟨Φ₀, w, hw, H⟩ := exists_iso_of_sectionRing_aut_of_relAmple K Y (PP L p N) (LB.isLB_linComb hL _ _) hA θ
    (fun n hn c a b d h j => by
      obtain ⟨i, rfl⟩ := one j
      apply rho_injective L p N i
      have e := hlin n hn c (E n b) (E n a) (E n d) (fun j => (hE' n d j).trans ((congrArg (rho L p N j) (h _)).trans
        ((map_add _ _ _).trans ((add_comm _ _).trans (congrArg₂ (· + ·) ((map_mul _ _ _).trans
          (congrArg₂ (· * ·) (rho_resTop L p N j _) (hE' n b j).symm)) (hE' n a j).symm))))) i
      exact (hθ n hn d i).trans (e.trans ((map_add _ _ _).trans ((add_comm _ _).trans (congrArg₂ (· + ·)
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) (rho_resTop L p N i _) (hθ n hn b i))) (hθ n hn a i)))).symm))
    (fun n m hn hm a b d h j => by
      obtain ⟨i, rfl⟩ := one j
      apply rho_injective L p N i
      have e := hmul n m hn hm (hn.trans (Nat.le_add_right n m)) (E n a) (E m b) (E (n + m) d)
        (fun j => (hE' _ d j).trans ((congrArg (rho L p N j) (h _)).trans
          ((map_mul _ _ _).trans (congrArg₂ (· * ·) (hE' n a j).symm (hE' m b j).symm)))) i
      exact (hθ _ _ d i).trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (hθ n hn a i) (hθ m hm b i))).symm))
  have hψ : Φ₀.inv.left ≫ Φ₀.hom.left = 𝟙 _ := by rw [← Over.comp_left, Φ₀.inv_hom_id, Over.id_left]
  refine ⟨Φ₀.symm, fun m hm n hn => ?_⟩
  obtain ⟨α, hα, hv⟩ := exists_gen_of_iso L p N n Φ₀.hom.left Φ₀.inv.left hψ m hm w hw
  refine ⟨α, hα, fun s j y hy => ?_⟩
  obtain ⟨a, rfl⟩ := (E n).surjective s
  have hF : Φ₀.hom.left (Φ₀.inv.left y) = y := by
    rw [← Scheme.Hom.comp_apply, hψ]; rfl
  have h0 : y ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 0) := mem_one.2 (Set.mem_iInter.1 hy 0)
  have h1 : Φ₀.inv.left y ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 1) := by
    subst hm; exact mem_one.2 (Set.mem_iInter.1 hy 1)
  have e := H n hn a _ Φ₀.inv.left y (fun _ _ => j 0) (fun _ _ => j 1)
    (fun _ => (congrArg (· ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 0)) hF).mpr h0) (fun _ => h1)
  rw [hψ, Fin.prod_univ_one, Category.comp_id] at e
  rw [← hθE, hE n _ _ _ (𝟙 _) y h0, hv j y hy]
  exact e.trans (congrArg _ (hE n a _ _ Φ₀.inv.left y h1).symm)

end SectionAut

theorem exists_iso_of_multiplicative_section_family : ∀ (F : Type) [Field F] (S : Scheme.{0}) (P : PolAV S) (t : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), 1 ≤ N → ∀ Φ : ∀ k : ℕ, LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)) ≃ LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)), (∀ k (s s' s'' : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t))) (c : Γ((Over.mk t).left, ⊤)), (∀ j, s''.f j = liftFun P.A _ c * s.f j + s'.f j) → ∀ j, (Φ k s'').f j = liftFun P.A _ c * (Φ k s).f j + (Φ k s').f j) → (∀ k l (s : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t))) (s' : LB.Sec (LPow P.A P.L ((N * (l + 1) : ℕ) : ℤ) (Over.mk t))) (s'' : LB.Sec (LPow P.A P.L ((N * (k + l + 1 + 1) : ℕ) : ℤ) (Over.mk t))), (∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s''.f j) = @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s.f j) * @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s'.f j)) → ∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ (k + l + 1) s'').f j) = @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ k s).f j) * @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ l s').f j)) → ∃ (ψ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P.A) (_ : ψ.hom ≫ fst _ _ = fst _ _), ∀ k, ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (Over.mk t) P.A).left, (ψ.hom ≫ snd _ _).left] ![((N * (k + 1) : ℕ) : ℤ), -((N * (k + 1) : ℕ) : ℤ)]), α.IsGen ∧ ∀ s, IsTwistPull P.A P.L ψ.hom (ψ.hom ≫ snd _ _) rfl _ _ α s (Φ k s) := by
  intro F _ S P t N hN Φ hlin hmul
  obtain ⟨hp, hA⟩ := isProper_and_relAmple_lPow F S P t N hN
  have hp' : IsProper (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left).hom := hp
  have hmul' : ∀ k l m (_ : m = k + l + 1) (s : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)))
      (s' : LB.Sec (LPow P.A P.L ((N * (l + 1) : ℕ) : ℤ) (Over.mk t)))
      (s'' : LB.Sec (LPow P.A P.L ((N * (m + 1) : ℕ) : ℤ) (Over.mk t))),
      (∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s''.f j) =
        @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s.f j) *
        @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s'.f j)) →
      ∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ m s'').f j) =
        @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ k s).f j) *
        @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ l s').f j) := by
    rintro k l _ rfl
    exact hmul k l
  obtain ⟨ψ₀, H⟩ := SectionAut.exists_iso P.L P.isLB
    (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left) (snd (Over.mk t) P.A).left N hA
    (fun n hn => match n, hn with | k + 1, _ => Φ k)
    (fun n hn c => match n, hn with
      | k + 1, _ => fun s s' s'' => hlin k s s' s'' ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c))
    (fun n m hn hm _ => match n, m, hn, hm with
      | k + 1, l + 1, _, _ => hmul' k l (k + 1 + l) (by omega))
  have w₀ : ψ₀.hom.left ≫ (fst (Over.mk t) P.A).left = (fst (Over.mk t) P.A).left := Over.w ψ₀.hom
  let ψ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P.A := Over.isoMk ((Over.forget _).mapIso ψ₀) (by
    have e : (fst (Over.mk t) P.A).left ≫ t = (Over.mk t ⊗ P.A).hom := Over.w (fst (Over.mk t) P.A)
    show ψ₀.hom.left ≫ (Over.mk t ⊗ P.A).hom = (Over.mk t ⊗ P.A).hom
    rw [← e, ← Category.assoc, w₀])
  refine ⟨ψ, Over.OverMorphism.ext w₀, fun k => ?_⟩
  obtain ⟨α, hα, hv⟩ := H (ψ.hom ≫ snd _ _).left rfl (k + 1) (Nat.succ_pos k)
  refine ⟨α, hα, fun s j => fn_ext fun y hy => ?_⟩
  have l₀ := chart_le_zero P.A P.L (ψ.hom ≫ snd _ _) j
  have l₁ := chart_le_pull P.A P.L ψ.hom (ψ.hom ≫ snd _ _) rfl j
  exact (gs_res (𝟙 _) y l₀ hy _).trans ((hv s j y hy).trans ((gs_mul (𝟙 _) y _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) ((gs_res (𝟙 _) y l₁ hy _).trans
      (gs_pull (𝟙 _) ψ.hom.left y
        (LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) (fun _ => j 1)) (l₁ hy) _)))).symm)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismOfMultiplicativeSectionFamilyStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_automorphism_of_multiplicative_section_family : ∀ (F : Type) [Field F] (S : Scheme.{0}) (P : PolAV S) (t : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), 1 ≤ N → ∀ Φ : ∀ k : ℕ, LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)) ≃ LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)), (∀ k (s s' s'' : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t))) (c : Γ((Over.mk t).left, ⊤)), (∀ j, s''.f j = liftFun P.A _ c * s.f j + s'.f j) → ∀ j, (Φ k s'').f j = liftFun P.A _ c * (Φ k s).f j + (Φ k s').f j) → (∀ k l (s : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t))) (s' : LB.Sec (LPow P.A P.L ((N * (l + 1) : ℕ) : ℤ) (Over.mk t))) (s'' : LB.Sec (LPow P.A P.L ((N * (k + l + 1 + 1) : ℕ) : ℤ) (Over.mk t))), (∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s''.f j) = @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s.f j) * @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s'.f j)) → ∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ (k + l + 1) s'').f j) = @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ k s).f j) * @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ l s').f j)) → ∃ (ψ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P.A) (_ : ψ.hom ≫ fst _ _ = fst _ _), ∀ k, ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (Over.mk t) P.A).left, (ψ.hom ≫ snd _ _).left] ![((N * (k + 1) : ℕ) : ℤ), -((N * (k + 1) : ℕ) : ℤ)]), α.IsGen ∧ ∀ s, IsTwistPull P.A P.L ψ.hom (ψ.hom ≫ snd _ _) rfl _ _ α s (Φ k s) := by
  first | exact @GlobalTheory.exists_iso_of_multiplicative_section_family | exact GlobalTheory.exists_iso_of_multiplicative_section_family | (intros; apply GlobalTheory.exists_iso_of_multiplicative_section_family <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismInducingFrobeniusAllDegrees
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.InducingAut

open GlobalTheory.FieldBaseChange

theorem exists_const_ratio {K : Type} [CommRing K] {Y : Scheme.{0}} {N : LB Y} (hN : ∀ y : Y, ∃ i, y ∈ N.U i)
    (p : Y ⟶ Spec (CommRingCat.of K)) (hp : Function.Surjective p.appTop.hom)
    {t₁ t₂ : LB.Gen N} (h₁ : t₁.IsGen) (h₂ : t₂.IsGen) :
    ∃ c : K, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : N.ι), r z ∈ N.U i →
      (gm r z (N.U i) (t₁.s i)).val = constVal (r ≫ p) z c * (gm r z (N.U i) (t₂.s i)).val := by
  have tr : ∀ {t : LB.Gen N}, t.IsGen → ∀ (i j : N.ι) (x : Y), x ∈ N.U i ⊓ N.U j →
      gm (𝟙 Y) x (N.U i) (t.s i) = gm (𝟙 Y) x (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Y) x (N.U j) (t.s j) := by
    intro t ht i j x hx
    have := congrArg (gm (𝟙 Y) x (N.U i ⊓ N.U j)) (ht i j)
    rwa [map_mul, gm_res _ x _ hx, gm_res _ x _ hx] at this
  obtain ⟨u, hu⟩ := glue_unit ⊤ N.U (fun _ => le_top) (fun y _ => TopologicalSpace.Opens.mem_iSup.2 (hN y))
    (fun i => t₁.s i * (t₂.s i)⁻¹) (fun i j x hx => by
      rw [map_mul, map_mul, map_inv, map_inv, tr h₁ i j x hx, tr h₂ i j x hx, mul_inv, _root_.mul_mul_mul_comm,
        mul_inv_cancel, _root_.one_mul])
  obtain ⟨a, ha⟩ := hp u.val
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 a
  refine ⟨c, fun Z r z i hi => ?_⟩
  have key : (gm r z (N.U i) (t₁.s i) * (gm r z (N.U i) (t₂.s i))⁻¹).val = constVal (r ≫ p) z c := by
    rw [← map_inv, ← map_mul, ← hu i, gm_res r z _ hi]
    exact (gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial _))
  rw [← key, ← Units.val_mul, inv_mul_cancel_right]

theorem constVal_pow {K : Type} [CommRing K] {Z : Scheme.{0}} (π : Z ⟶ Spec (CommRingCat.of K)) (z : Z) (c : K)
    (k : ℕ) : constVal π z (c ^ k) = constVal π z c ^ k := by
  simp only [constVal, gs_eq π z ⊤ trivial, map_pow]

theorem isoRelM_change {Y Y' X₁ X₂ Z₁ Z₂ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {w w' : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {m : Y' ⟶ Y} {k : ℕ} {g₁ : Z₁ ⟶ X₁} {h₁ : Y' ⟶ Z₁}
    {g₂ : Z₂ ⟶ X₂} {h₂ : Y' ⟶ Z₂}
    {S : Type} [CommRing S] {π₁ : Z₁ ⟶ Spec (CommRingCat.of S)} (c : S)
    (hc : ∀ (y : Y') i₂ i₁, f₂ (m y) ∈ L₂.U i₂ → f₁ (m y) ∈ L₁.U i₁ →
      (isoVal w' (𝟙 Y' ≫ m) y i₂ i₁).val =
        constVal ((𝟙 Y' ≫ h₁) ≫ π₁) y c * (isoVal w (𝟙 Y' ≫ m) y i₂ i₁).val)
    {a : SecOver π₁ (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ)))}
    {b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => (k : ℤ)))}
    (h : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w' m k g₁ h₁ a g₂ h₂ b) :
    GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ (c ^ k • a : SecOver π₁ _) g₂ h₂ b := by
  refine (isoRelM_iff w m k h₁ h.1 _ h.2.1 _ _).2 fun y i₂ i₁ a₂ a₁ => ?_
  have b₁ : g₁ ((𝟙 Y' ≫ h₁) y) ∈ L₁.U i₁ :=
    (congrArg (fun q : Y' ⟶ X₁ => q y) h.1 : g₁ (h₁ y) = f₁ (m y)).symm ▸ a₁
  rw [powVal_smul _ _ _ y b₁, (isoRelM_iff w' m k h₁ h.1 _ h.2.1 _ _).1 h _ (𝟙 _) y i₂ i₁ a₂ a₁,
    zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hc y i₂ i₁ a₂ a₁,
    constVal_pow]
  ring

theorem mul_chart_iff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (g : Y ⟶ X) {a b c : ℤ}
    (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => g) (fun _ => a)))
    (s' : LB.Sec (LB.LinComb L (fun _ : Fin 1 => g) (fun _ => b)))
    (s'' : LB.Sec (LB.LinComb L (fun _ : Fin 1 => g) (fun _ => c))) :
    (∀ j, @id Γ(Y, LB.wchart L (fun _ : Fin 1 => g) j) (s''.f j) =
      @id Γ(Y, LB.wchart L (fun _ : Fin 1 => g) j) (s.f j) * @id Γ(Y, LB.wchart L (fun _ : Fin 1 => g) j) (s'.f j)) ↔
    ∀ y J, Good L y J → sval s'' (𝟙 Y) y J = sval s (𝟙 Y) y J * sval s' (𝟙 Y) y J := by
  constructor
  · intro h y J hJ
    exact (congrArg (gs (𝟙 Y) y _) (h _)).trans (gs_mul _ y _ (hJ.mem (fun _ : Fin 1 => g) (𝟙 Y)) _ _)
  · intro h j
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun _ : Fin 1 => 𝟙 Y ≫ g) j
      (fun a b _ => congrArg j (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 hy k)
    have := h y J hJ
    rw [sval_of s _ y J j e, sval_of s' _ y J j e, sval_of s'' _ y J j e] at this
    exact this.trans (gs_mul _ y _ hy _ _).symm

section Frames

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem exists_frame (k : ℕ) (b : TF (R := R) F ⟶ D.P.A) : ∃ w : Frm D F k b, w.IsGen :=
  exists_gen_of_local (V := F) D.P.L D.P.isLB _ _


variable {D F} in
theorem exists_frame_pow {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} (w : Frm D F k b) (hw : w.IsGen) (n : ℕ) :
    ∃ ω : Frm D F (k * n) b, ω.IsGen ∧ ∀ z J, Good D.P.L z J → val ω (𝟙 _) z J = val w (𝟙 _) z J ^ n := by
  obtain ⟨ω, h, v⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε (k * n))
    (fun U _ h => Finset.prod_congr rfl fun i _ => congrArg _ (by
      fin_cases i <;> simp [DegPre.lineε, mul_comm]))
    (GeneratorPullback.powGen D.P.L _ _ w n) (powGen_isGen _ _ _ w hw n)
  exact ⟨ω, h, fun z J hJ => (v _ _ z J hJ).trans (map_pow _ _ _)⟩

end Frames

section Unif

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem expandsF_change (hG : GlobalFnsSt) (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (k : ℕ) {w w' : W0 U} (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ c : F, ∀ (t : SecOver (abelianBase A F) (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s : Fam D.toPre F k),
      U.ExpandsF F k w' t s → U.ExpandsF F k w (c • t : SecOver (abelianBase A F) _) s := by
  have : IsIso U.gen.hom.left := ⟨⟨U.gen.inv.left, by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]⟩⟩
  have hp : Function.Surjective (U.gen.hom.left ≫ A.A.hom).appTop.hom := by
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    have : IsIso U.gen.hom.left.appTop := inferInstanceAs (IsIso (U.gen.hom.left.app ⊤))
    exact (ConcreteCategory.bijective_of_isIso U.gen.hom.left.appTop).2.comp (hG _ _ A.isAb).2
  obtain ⟨c, hc⟩ := exists_const_ratio (K := FractionRing R) (fun y => by
    obtain ⟨i, hi⟩ := exists_chart A.isLB (U.gen.hom.left y)
    obtain ⟨j, hj⟩ := exists_chart U.LG.isLB (pullback.fst G.hom (jK R) y)
    exact ⟨(fun _ => j, fun _ => i), mem_pull.2 hj, mem_pull.2 hi⟩) (U.gen.hom.left ≫ A.A.hom) hp hw' hw
  refine ⟨algebraMap (FractionRing R) F c ^ k, ?_⟩
  rintro t s ⟨v, a, b⟩
  refine ⟨v, isoRelM_change (π₁ := abelianBase A F) _ (fun y i₂ i₁ a₂ a₁ => ?_) a, b⟩
  refine (hc _ _ y (fun _ => i₂, fun _ => i₁) ⟨mem_pull.2 a₂, mem_pull.2 a₁⟩).trans (congrArg (· * _) ?_)
  refine Eq.trans (congrArg (fun q => constVal q y c) ?_) (constVal_specMap _ (algebraMap (FractionRing R) F) y c)
  have hπ : (U.genF F).left ≫ abelianBase A F = groupBase G F :=
    congrArg (fun q => q.left) (lift_fst _ _ : U.genF F ≫ fst _ _ = _)
  have e : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
  simp only [Category.id_comp]
  rw [hπ, e]
  exact (isPullback_groupBase F).w

theorem exists_transport (hG : GlobalFnsSt) (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {N : ℕ} (hN : 1 ≤ N) {w₀ : W0 U.toUnifPre} (hw₀ : w₀.IsGen) (Φ : Fam D.toPre F N →ₗ[F] Fam D.toPre F N)
    (hΦ : Function.Bijective Φ) :
    ∃ Ψ : SecA A F N ≃ SecA A F N,
      (∀ (s s' s'' : SecA A F N) (c : Γ((TFK (R := R) F).left, ⊤)),
        (∀ j, s''.f j = liftFun A.A _ c * s.f j + s'.f j) →
          ∀ j, (Ψ s'').f j = liftFun A.A _ c * (Ψ s).f j + (Ψ s').f j) ∧
      (∀ t, ∃ s, U.ExpandsF F N w₀ t s ∧ U.ExpandsF F N w₀ (Ψ t) (Φ s)) ∧
      ∀ w₁ : W0 U.toUnifPre, w₁.IsGen → ∀ t s s', U.ExpandsF F N w₁ t s → U.ExpandsF F N w₁ (Ψ t) s' →
        s' = Φ s := by
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
  let Ψ := (e.trans (LinearEquiv.ofBijective Φ hΦ)).trans e.symm
  have hΨ : ∀ t, e (Ψ t) = Φ (e t) := fun t => e.apply_symm_apply _
  refine ⟨Ψ.toEquiv, fun s s' s'' c h j => ?_, fun t => ⟨e t, (he _ _).2 rfl, (he _ _).2 (hΨ t)⟩,
    fun w₁ hw₁ t s s' h h' => ?_⟩
  · obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 c
    let t : SecOver (abelianBase A F) (LPow A.A A.L (N : ℤ) (TFK (R := R) F)) := s
    let t' : SecOver (abelianBase A F) (LPow A.A A.L (N : ℤ) (TFK (R := R) F)) := s'
    let t'' : SecOver (abelianBase A F) (LPow A.A A.L (N : ℤ) (TFK (R := R) F)) := s''
    have e₁ : t'' = c • t + t' := SecOver.ext _ _ fun j => (h j).trans rfl
    have e₂ : Ψ t'' = c • Ψ t + Ψ t' := by rw [e₁, map_add (f := _), map_smul]
    exact (congrArg (chartFun _ _ j) e₂).trans rfl
  · obtain ⟨c, hc⟩ := expandsF_change hG U.toUnifPre F N hw₀ hw₁
    have a := (he _ _).1 (hc t s h)
    have a' := (he _ _).1 (hc (Ψ t) s' h')
    exact a'.symm.trans ((e.map_smul c _).trans ((congrArg (c • ·) (hΨ t)).trans
      ((Φ.map_smul c _).symm.trans (congrArg Φ ((e.map_smul c t).symm.trans a)))))

end Unif


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem exists_qk_mul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (p : QkPt D F k) (n : ℕ) :
    ∃ h : GtPtF D F, GtPtF.IsNsmul (k * n) p.g h ∧ GtPtF.IsIota (n • p.y) h :=
  (GlobalTheory.TorusExt.qkMk hB (k := k * n) (n • p.y) p.g (by
    rw [map_nsmul, ← GlobalTheory.TorusExt.qk_nsmul hB p, mul_nsmul])).eq

theorem exists_aut : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, ∃ ψ : (TFK (R := R) F ⊗ A.A) ≅ (TFK (R := R) F ⊗ A.A), ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ q : QkPt D.toPre F N, q.y = n • p.y → q.g = p.g → IndAt U.toUnifPre F N q ψ.hom := by
  intro hL R _ _ _ I hI D A G _ _ hS U F _ _ _ k hk p
  have hG := hL.1.globalFns
  have hN : ∀ n, 1 ≤ k * (n + 1) := fun n => Nat.mul_pos hk n.succ_pos
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨w, hw⟩ := exists_frame D.toPre F k p.g.b
  choose ω hω vω using fun n => exists_frame_pow w hw (n + 1)
  let q : ∀ n, QkPt D.toPre F (k * (n + 1)) := fun n =>
    ⟨(n + 1) • p.y, p.g, exists_qk_mul D.tau_bimult p (n + 1)⟩
  choose Φ hΦ using fun n => GlobalTheory.T.thetaOperators_projective_representation hL R I hI D F (k * (n + 1)) (hN n)
  have hΦ' := fun n => (hΦ n).1 (q n) (ω n) (hω n)
  choose Ψ lin ex un using fun n => exists_transport hG U F (hN n) hw₀ _ (hΦ' n).1
  have mul : ∀ m : Fin 3 → ℕ, m 2 = m 0 + m 1 + 1 → ∀ t : ∀ i, SecA A F (k * (m i + 1)),
      (∀ z J, Good A.L z J → sA (t 2) (𝟙 _) z J = sA (t 0) (𝟙 _) z J * sA (t 1) (𝟙 _) z J) →
      ∀ z J, Good A.L z J → sA (Ψ _ (t 2)) (𝟙 _) z J = sA (Ψ _ (t 0)) (𝟙 _) z J * sA (Ψ _ (t 1)) (𝟙 _) z J := by
    intro m hm t
    choose s hs hs' using fun i => ex (m i) (t i)
    exact GlobalTheory.T.heckeOperator_multiplicative_on_section_products hL R I hI D A G hS U F w₀ hw₀ k hk p w hw (fun i => m i + 1) (fun i => k * (m i + 1))
      (fun i => ⟨Nat.succ_pos _, rfl⟩) (by show m 2 + 1 = m 0 + 1 + (m 1 + 1); omega) (fun i => q (m i))
      (fun i => ω (m i)) (fun i => ⟨rfl, rfl, hω _, vω _⟩) t (fun i => Ψ _ (t i)) s _
      (fun i => ⟨hs i, hs' i, ((hΦ' _).2 _ _).2 rfl⟩)
  obtain ⟨ψ, hψ, hα⟩ := GlobalTheory.T.exists_automorphism_of_multiplicative_section_family F _ A (jFK (R := R) F) k hk Ψ lin (fun a b s s' s'' h =>
    (mul_chart_iff A.isLB _ _ _ _).2 (mul ![a, b, a + b + 1] rfl
      (Fin.cons s (Fin.cons s' (Fin.cons s'' finZeroElim))) ((mul_chart_iff A.isLB _ _ _ _).1 h)))
  refine ⟨ψ, fun n N hn hN' q' hy hg => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hN'
  obtain rfl : q' = q n := GlobalTheory.TorusExt.qk_ext hy hg
  obtain ⟨α, hα, tw⟩ := hα n
  refine ⟨hψ, fun w₁ hw₁ => ⟨α, ω n, hα, hω n, fun t t' s s' h h' H => ?_⟩⟩
  obtain rfl : t' = Ψ n t := sec_ext' A.isLB fun y J hJ =>
    (GlobalTheory.ThetaLin.sval_of_isTwistPull A.A H (𝟙 _) y hJ).trans
      (GlobalTheory.ThetaLin.sval_of_isTwistPull A.A (tw t) (𝟙 _) y hJ).symm
  exact ((hΦ' n).2 _ _).2 (un n w₁ hw₁ t s s' h h')

end GlobalTheory.InducingAut

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismInducingFrobeniusAllDegreesStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_automorphism_inducing_frobenius_all_degrees : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, ∃ ψ : (TFK (R := R) F ⊗ A.A) ≅ (TFK (R := R) F ⊗ A.A), ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ q : QkPt D.toPre F N, q.y = n • p.y → q.g = p.g → IndAt U.toUnifPre F N q ψ.hom := by
  first | exact @GlobalTheory.InducingAut.exists_aut | exact GlobalTheory.InducingAut.exists_aut | (intros; apply GlobalTheory.InducingAut.exists_aut <;> assumption)
end
