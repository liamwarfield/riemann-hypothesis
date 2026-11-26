module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionsProductBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedUniversalHomMatrixScheme

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoLBCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixUniq

open GlobalTheory.HomFixMat

theorem psi_unique {Rg : Type} [CommRing Rg] {A : Over (Sp Rg)} [GrpObj A] {X : Scheme.{0}} (ψ ψ₂ : X ⟶ (topS Rg ⊗ A).left)
    (h : ψ ≫ (snd (topS Rg) A).left = ψ₂ ≫ (snd (topS Rg) A).left) : ψ = ψ₂ := by
  haveI : Mono (topS Rg).hom := by
    show Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
  have e : ψ ≫ (fst (topS Rg) A).left = ψ₂ ≫ (fst (topS Rg) A).left := by
    rw [← cancel_mono (topS Rg).hom]
    simp only [Category.assoc, Over.w]
    rw [← Over.w (snd (topS Rg) A), ← Category.assoc, h, Category.assoc]
  exact pullback.hom_ext e h

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B]


variable (L : LB A.left) (M : LB B.left) in
def RigEq (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) {R : Type} [CommRing R]
    (t : Sp R ⟶ Sp Rg) {A' B' : Over (Sp R)} [GrpObj A'] [GrpObj B'] (Φ' : A' ⟶ B')
    (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left)
    (α : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)) : Prop :=
  ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (α.s p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k

theorem isoLB_cover {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left}
    {M : LB B.left} (hL : L.IsLB) (hM : M.IsLB) (k : ℕ) {R : Type} [CommRing R] {A' B' : Over (Sp R)}
    (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (x : A'.left) :
    ∃ p, x ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p := by
  have hc : ∀ {X : Scheme.{0}} (N : LB X), N.IsLB → ∀ y : X, ∃ i, y ∈ N.U i := fun N hN y =>
    TopologicalSpace.Opens.mem_iSup.1 (by rw [hN.cover]; trivial)
  obtain ⟨iM, hiM⟩ := hc M hM ((((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left)).base x)
  obtain ⟨iL, hiL⟩ := hc L hL (((ψA ≫ (snd (topS Rg) A).left)).base x)
  exact ⟨(fun _ => iM, fun _ => iL), Set.mem_iInter.2 fun _ => hiM, Set.mem_iInter.2 fun _ => hiL⟩

end GlobalTheory.HomFixUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismsSameMatrixIsomorphicTestData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProportionalGermsSectionsEmbedProjectively
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProportionalGermsSectionsEmbedProjectively
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HomFixGerm

open GlobalTheory.AmpleSpan

theorem eq_of_germs {X Y Z : Scheme.{0}} (π : Y ⟶ Z) {N : LB Y} {κ : Type} (s : κ → LB.Sec N)
    (hs : EmbedsBy π s) (f₁ f₂ : X ⟶ Y) (hπ : f₁ ≫ π = f₂ ≫ π)
    (h : ∀ x : X, ∃ σ : κ → X.presheaf.stalk x,
      (∃ p, f₁ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₁ x (N.U p) ((s l).f p) = u * σ l) ∧
      (∃ p, f₂ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₂ x (N.U p) ((s l).f p) = u * σ l)) :
    f₁ = f₂ := by
  have mem : ∀ x l, f₁ x ∈ nonzeroLocus (s l) ↔ f₂ x ∈ nonzeroLocus (s l) := by
    intro x l
    obtain ⟨σ, ⟨p₁, hp₁, u₁, e₁⟩, ⟨p₂, hp₂, u₂, e₂⟩⟩ := h x
    rw [mem_nonzeroLocus_iff_gs (s l) f₁ x hp₁, mem_nonzeroLocus_iff_gs (s l) f₂ x hp₂, e₁ l, e₂ l,
      Units.isUnit_units_mul, Units.isUnit_units_mul]
  have rat : ∀ (l : κ) (r : κ → Γ(Y, nonzeroLocus (s l))), (∀ j, IsRatio (s j) (s l) (r j)) →
      ∀ x j, f₁ x ∈ nonzeroLocus (s l) → gs f₁ x _ (r j) = gs f₂ x _ (r j) := by
    intro l r hr x j hx
    have hx₂ := (mem x l).1 hx
    obtain ⟨σ, ⟨p₁, hp₁, u₁, e₁⟩, ⟨p₂, hp₂, u₂, e₂⟩⟩ := h x
    have a₁ := (hr j).gs f₁ x hx hp₁
    have a₂ := (hr j).gs f₂ x hx₂ hp₂
    rw [e₁ j, e₁ l] at a₁
    rw [e₂ j, e₂ l] at a₂
    have hσ : IsUnit (σ l) := by
      have := (mem_nonzeroLocus_iff_gs (s l) f₁ x hp₁).1 hx
      rwa [e₁ l, Units.isUnit_units_mul] at this
    have b₁ : σ j = gs f₁ x _ (r j) * σ l := by
      apply u₁.isUnit.mul_left_cancel
      rw [a₁]; ring
    have b₂ : σ j = gs f₂ x _ (r j) * σ l := by
      apply u₂.isUnit.mul_left_cancel
      rw [a₂]; ring
    exact hσ.mul_right_cancel (b₁.symm.trans b₂)
  have loc : ∀ l, (f₁ ⁻¹ᵁ nonzeroLocus (s l)).ι ≫ f₁ = (f₁ ⁻¹ᵁ nonzeroLocus (s l)).ι ≫ f₂ := by
    intro l
    obtain ⟨haff, r, hr, hsurj⟩ := hs.2 l
    have hV : f₁ ⁻¹ᵁ nonzeroLocus (s l) ≤ f₂ ⁻¹ᵁ nonzeroLocus (s l) := fun x hx => (mem x l).1 hx
    have happ : f₁.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) le_rfl =
        f₂.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) hV := by
      have hcomp : (f₁.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) le_rfl).hom.comp
            (MvPolynomial.eval₂Hom (π.appLE ⊤ (nonzeroLocus (s l)) le_top).hom r) =
          (f₂.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) hV).hom.comp
            (MvPolynomial.eval₂Hom (π.appLE ⊤ (nonzeroLocus (s l)) le_top).hom r) := by
        refine MvPolynomial.ringHom_ext (fun b => ?_) (fun j => ?_)
        · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
          refine fn_ext fun x hx => ?_
          rw [gs_appLE f₁ _ _ le_rfl (𝟙 X) x hx, gs_appLE f₂ _ _ hV (𝟙 X) x hx, Category.id_comp,
            Category.id_comp, gs_appLE π ⊤ _ le_top f₁ x hx, gs_appLE π ⊤ _ le_top f₂ x (hV hx), hπ]
        · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
          refine fn_ext fun x hx => ?_
          rw [gs_appLE f₁ _ _ le_rfl (𝟙 X) x hx, gs_appLE f₂ _ _ hV (𝟙 X) x hx, Category.id_comp,
            Category.id_comp]
          exact rat l r hr x j hx
      ext a
      obtain ⟨P, rfl⟩ := hsurj a
      exact congrArg (fun φ : MvPolynomial κ Γ(Z, ⊤) →+* _ => φ P) hcomp
    haveI : IsAffine (nonzeroLocus (s l)) := haff
    have hres : f₁.resLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) le_rfl =
        f₂.resLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) hV := by
      refine ext_of_isAffine ?_
      simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, happ]
    rw [← Scheme.Hom.resLE_comp_ι f₁ (le_rfl : f₁ ⁻¹ᵁ nonzeroLocus (s l) ≤ _),
      ← Scheme.Hom.resLE_comp_ι f₂ hV, hres]
  have hcov : TopologicalSpace.IsOpenCover (fun l => f₁ ⁻¹ᵁ nonzeroLocus (s l)) := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show f₁ x ∈ ⨆ l, nonzeroLocus (s l) by rw [hs.1]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hl⟩
  exact Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _ hcov) f₁ f₂ fun l => loc l

end GlobalTheory.HomFixGerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProportionalGermsSectionsEmbedProjectivelyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_proportional_germs_sectionsEmbedProjectively : ∀ {X Y Z : Scheme.{0}} (π : Y ⟶ Z) {N : LB Y} {κ : Type} (s : κ → LB.Sec N), GlobalTheory.AmpleSpan.EmbedsBy π s → ∀ (f₁ f₂ : X ⟶ Y), f₁ ≫ π = f₂ ≫ π → (∀ x : X, ∃ σ : κ → X.presheaf.stalk x, (∃ p, f₁ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₁ x (N.U p) ((s l).f p) = u * σ l) ∧ (∃ p, f₂ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₂ x (N.U p) ((s l).f p) = u * σ l)) → f₁ = f₂ := by
  first | (exact @GlobalTheory.HomFixGerm.eq_of_germs) | (exact GlobalTheory.HomFixGerm.eq_of_germs) | (intros; apply GlobalTheory.HomFixGerm.eq_of_germs  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMatrixIdentityGermPullbackChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMatrixIdentityGermPullbackChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

theorem pullbackGerm_finset_sum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {K : Type} (s : Finset K)
    (a : K → Γ(X, U)) : gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

theorem isMat_germ : ∀ {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left} {k : ℕ} {mA mB : ℕ} {bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))} {bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))} {eA : LB.Gen (L.pull (eSec A))} {eB : LB.Gen (M.pull (eSec B))} {R : Type} [CommRing R] {t : Sp R ⟶ Sp Rg} {A' B' : Over (Sp R)} [GrpObj A'] [GrpObj B'] {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {c : Fin mA → Fin mB → Γ(Sp R, ⊤)}, IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → ∃ (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left), ψA ≫ (snd (topS Rg) A).left = φA' ∧ ψB ≫ (snd (topS Rg) B).left = φB' ∧ ∀ (Z : Scheme.{0}) (e : Z ⟶ A'.left) (z : Z) (pM : Fin 1 → M.ι) (q : Fin 1 → L.ι), (e ≫ Φ'.left ≫ ψB) z ∈ (LPow B M (k : ℤ) (topS Rg)).U pM → (e ≫ ψA) z ∈ (LPow A L (k : ℤ) (topS Rg)).U q → ∃ u : (Z.presheaf.stalk z)ˣ, ∀ j, gs (e ≫ Φ'.left ≫ ψB) z _ ((bB j).f pM) = u * ∑ i, gs (e ≫ A'.hom) z ⊤ (c i j) * gs (e ≫ ψA) z _ ((bA i).f q) := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB R _ t A' B' _ _ φA' φB' Φ' c h
  obtain ⟨ψA, ψB, α, h1, h2, -, -, hch⟩ := h
  refine ⟨ψA, ψB, h1, h2, ?_⟩
  intro Z e z pM q hM hA
  have hz : e z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U (pM, q) := by
    refine ⟨?_, ?_⟩
    · refine Set.mem_iInter.2 fun i => ?_
      have := Set.mem_iInter.1 hM i
      simpa using this
    · refine Set.mem_iInter.2 fun i => ?_
      have := Set.mem_iInter.1 hA i
      simpa using this
  refine ⟨gm e z _ (α.s (pM, q)), fun j => ?_⟩
  have E := congrArg (gs e z ((isoLB (L := L) (M := M) k Φ' ψA ψB).U (pM, q))) (hch j (pM, q))
  erw [gs_mul _ _ _ hz] at E
  erw [gs_unit _ _ _ hz, pullbackGerm_finset_sum _ _ _ hz, gs_appLE _ _ _ _ _ _ hz] at E
  refine E.trans (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
  erw [gs_mul _ _ _ hz, gs_appLE _ _ _ _ _ _ hz, gs_appLE _ _ _ _ _ _ hz]
  rfl

end GlobalTheory.HomFixMat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMatrixIdentityGermPullbackChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMatrixIdentity_germ_pullback_chart : ∀ {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left} {k : ℕ} {mA mB : ℕ} {bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))} {bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))} {eA : LB.Gen (L.pull (eSec A))} {eB : LB.Gen (M.pull (eSec B))} {R : Type} [CommRing R] {t : Sp R ⟶ Sp Rg} {A' B' : Over (Sp R)} [GrpObj A'] [GrpObj B'] {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {c : Fin mA → Fin mB → Γ(Sp R, ⊤)}, IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → ∃ (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left), ψA ≫ (snd (topS Rg) A).left = φA' ∧ ψB ≫ (snd (topS Rg) B).left = φB' ∧ ∀ (Z : Scheme.{0}) (e : Z ⟶ A'.left) (z : Z) (pM : Fin 1 → M.ι) (q : Fin 1 → L.ι), (e ≫ Φ'.left ≫ ψB) z ∈ (LPow B M (k : ℤ) (topS Rg)).U pM → (e ≫ ψA) z ∈ (LPow A L (k : ℤ) (topS Rg)).U q → ∃ u : (Z.presheaf.stalk z)ˣ, ∀ j, gs (e ≫ Φ'.left ≫ ψB) z _ ((bB j).f pM) = u * ∑ i, gs (e ≫ A'.hom) z ⊤ (c i j) * gs (e ≫ ψA) z _ ((bA i).f q) := by
  first | (exact @GlobalTheory.HomFixMat.isMat_germ) | (exact GlobalTheory.HomFixMat.isMat_germ) | (intros; apply GlobalTheory.HomFixMat.isMat_germ  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsAfterBaseChangeSpecTopOpenOfStableBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsAfterBaseChangeSpecTopOpenOfStableBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat.EmbedsBC
theorem embeds_bc : ∀ {Rg : Type} [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] (M : LB B.left) (k : ℕ) {mB : ℕ} (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))), IsAbelianScheme B → M.IsLB → VeryAmpleAt B M k → IsBCBasis B M k bB → ∃ (x : Sp Rg ⟶ (topS Rg).left) (b' : Fin mB → LB.Sec (LPow B M (k : ℤ) (baseAt x))), IsIso x ∧ (∀ i, IsPullSec B M (k : ℤ) (homAt x ▷ B) (whiskerRight_snd (homAt x) B) (bB i) (b' i)) ∧ GlobalTheory.AmpleSpan.EmbedsBy (fst (baseAt x) B).left b' := by
  intro Rg _ B _ M k mB bB hAb hM hVA hBC
  have : UniversallyClosed B.hom := by
    have := hAb.proper
    infer_instance
  let x : Sp Rg ⟶ (topS Rg).left := (Sp Rg).topIso.inv
  have hx : IsIso x := inferInstanceAs (IsIso (Sp Rg).topIso.inv)
  choose b' hb' using fun i => ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_isPullSec B M (k : ℤ) (homAt x ▷ B) (whiskerRight_snd (homAt x) B) (bB i)
  refine ⟨x, b', hx, hb', ?_⟩
  have hsp := (hBC Rg x b' hb').2
  exact GlobalTheory.AmpleSpan.embedsBy_baseAt B hM hVA (isAffineOpen_top (Sp Rg)) x b' hsp
end GlobalTheory.HomFixMat.EmbedsBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsAfterBaseChangeSpecTopOpenOfStableBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeds_after_baseChange_specTopOpen_of_stable_basis : ∀ {Rg : Type} [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] (M : LB B.left) (k : ℕ) {mB : ℕ} (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))), IsAbelianScheme B → M.IsLB → VeryAmpleAt B M k → IsBCBasis B M k bB → ∃ (x : Sp Rg ⟶ (topS Rg).left) (b' : Fin mB → LB.Sec (LPow B M (k : ℤ) (baseAt x))), IsIso x ∧ (∀ i, IsPullSec B M (k : ℤ) (homAt x ▷ B) (whiskerRight_snd (homAt x) B) (bB i) (b' i)) ∧ GlobalTheory.AmpleSpan.EmbedsBy (fst (baseAt x) B).left b' := by
  first | (exact @GlobalTheory.HomFixMat.EmbedsBC.embeds_bc) | (exact GlobalTheory.HomFixMat.EmbedsBC.embeds_bc) | (intros; apply GlobalTheory.HomFixMat.EmbedsBC.embeds_bc  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismsSameMatrixIsomorphicTestData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixMat

private theorem topS_tensor_left_ext {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) {Z : Scheme.{0}}
    (f g : Z ⟶ (topS Rg ⊗ A).left) (h : f ≫ (snd (topS Rg) A).left = g ≫ (snd (topS Rg) A).left) : f = g := by
  have P := IsPullback.of_hasPullback (topS Rg).hom A.hom
  have h' : f ≫ pullback.snd (topS Rg).hom A.hom = g ≫ pullback.snd (topS Rg).hom A.hom := h
  apply P.hom_ext
  · have hm : Mono (topS Rg).hom := by
      change Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
    rw [← cancel_mono (topS Rg).hom, Category.assoc, Category.assoc, P.w, ← Category.assoc, h', Category.assoc]
  · exact h'

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

theorem mat_determines : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A₁ B₁ : Over (Sp R)) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁) (A₂ B₂ : Over (Sp R)) [GrpObj A₂] [GrpObj B₂] (φA₂ : A₂.left ⟶ A.left) (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A₁ B₁ φA₁ φB₁ Φ₁ → IsTest A B L M t A₂ B₂ φA₂ φB₂ Φ₂ → IsMat L M k bA bB eA eB t A₁ B₁ φA₁ φB₁ Φ₁ c → IsMat L M k bA bB eA eB t A₂ B₂ φA₂ φB₂ Φ₂ c → IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ (𝟙 (Sp R)) := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH R _ t A₁ B₁ _ _ φA₁ φB₁ Φ₁ A₂ B₂ _ _ φA₂ φB₂ Φ₂ c T₁ T₂ M₁ M₂
  obtain ⟨-, hBab, hL, hM, -, -, -, -, hva, -, hbc⟩ := hH
  let ψA : A₂.left ⟶ A₁.left := T₁.1.1.lift φA₂ A₂.hom T₂.1.1.w
  let ψB : B₂.left ⟶ B₁.left := T₁.2.1.1.lift φB₂ B₂.hom T₂.2.1.1.w
  have hψA1 : ψA ≫ φA₁ = φA₂ := T₁.1.1.lift_fst _ _ _
  have hψA2 : ψA ≫ A₁.hom = A₂.hom := T₁.1.1.lift_snd _ _ _
  have hψB1 : ψB ≫ φB₁ = φB₂ := T₁.2.1.1.lift_fst _ _ _
  have hψB2 : ψB ≫ B₁.hom = B₂.hom := T₁.2.1.1.lift_snd _ _ _
  have gA : IsGrpPullback A₂ A₁ (𝟙 _) ψA :=
    IsGrpPullback.cancel T₁.1 (by rw [Category.id_comp, hψA1]; exact T₂.1) (by rw [hψA2, Category.comp_id])
  have gB : IsGrpPullback B₂ B₁ (𝟙 _) ψB :=
    IsGrpPullback.cancel T₁.2.1 (by rw [Category.id_comp, hψB1]; exact T₂.2.1) (by rw [hψB2, Category.comp_id])
  refine ⟨ψA, ψB, gA, gB, hψA1, hψB1, ?_⟩
  suffices key : Φ₂.left ≫ φB₂ = ψA ≫ Φ₁.left ≫ φB₁ by
    apply T₁.2.1.1.hom_ext
    · rw [Category.assoc, hψB1, key, Category.assoc]
    · rw [Category.assoc, hψB2, Over.w Φ₂, Category.assoc, Over.w Φ₁, hψA2]

  obtain ⟨ψA₁, ψB₁, eA₁, eB₁, g₁⟩ := GlobalTheory.T.isMatrixIdentity_germ_pullback_chart M₁
  obtain ⟨ψA₂, ψB₂, eA₂, eB₂, g₂⟩ := GlobalTheory.T.isMatrixIdentity_germ_pullback_chart M₂
  obtain ⟨x, b', hx, hb', hemb⟩ := GlobalTheory.T.embeds_after_baseChange_specTopOpen_of_stable_basis B M k bB hBab hM hva hbc
  have hG : ψA ≫ ψA₁ = ψA₂ := topS_tensor_left_ext A _ _ (by rw [Category.assoc, eA₁, eA₂, hψA1])
  let H : (baseAt x ⊗ B).left ⟶ (topS Rg ⊗ B).left := (homAt x ▷ B).left
  have hHi : IsIso (homAt x) := by
    have : IsIso ((Over.forget _).map (homAt x)) := hx
    exact isIso_of_reflects_iso (homAt x) (Over.forget _)
  have hH : IsIso H := (inferInstance : IsIso ((Over.forget _).map (homAt x ▷ B)))
  have hHs : H ≫ (snd (topS Rg) B).left = (snd (baseAt x) B).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  let F₁ : A₂.left ⟶ (topS Rg ⊗ B).left := ψA ≫ Φ₁.left ≫ ψB₁
  let F₂ : A₂.left ⟶ (topS Rg ⊗ B).left := Φ₂.left ≫ ψB₂
  suffices hF : F₂ ≫ inv H = F₁ ≫ inv H by
    have e1 : F₂ = F₁ := by simpa using congrArg (· ≫ H) hF
    have e2 : F₂ ≫ (snd (topS Rg) B).left = F₁ ≫ (snd (topS Rg) B).left := by rw [e1]
    simp only [F₁, F₂, Category.assoc] at e2
    rwa [eB₁, eB₂] at e2

  have memw : ∀ {P Q : Scheme.{0}} (W : LB Q) (φ : P ⟶ Q) (j : Fin 1 → W.ι) (y : P), φ y ∈ W.U (j 0) →
      y ∈ LB.wchart W (fun _ : Fin 1 => φ) j := fun W φ j y h =>
    Set.mem_iInter.2 fun i => by rw [Subsingleton.elim i 0]; exact h
  have hsx : (snd (topS Rg) B).left = inv H ≫ (snd (baseAt x) B).left := by
    rw [← hHs, IsIso.inv_hom_id_assoc]
  have hbase : ∀ (Z : Scheme.{0}) (r : Z ⟶ (baseAt x ⊗ B).left) (z : Z) (pM : Fin 1 → M.ι) (j : Fin mB),
      r z ∈ (LPow B M (k : ℤ) (baseAt x)).U pM →
      gs r z _ ((b' j).f pM) = gs (r ≫ H) z _ ((bB j).f pM) := by
    intro Z r z pM j hz
    rw [hb' j pM, gs_res _ _ _ hz, gs_pull]
    exact chart_le_res B M (homAt x ▷ B) (whiskerRight_snd (homAt x) B) (k : ℤ) pM hz
  have hmono : Mono (baseAt x).hom := by
    have : Mono (topS Rg).hom := by
      change Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
    change Mono (x ≫ (topS Rg).hom); infer_instance
  have hπ : ∀ F : A₂.left ⟶ (topS Rg ⊗ B).left, F ≫ inv H ≫ (fst (baseAt x) B).left ≫ (baseAt x).hom =
      F ≫ (snd (topS Rg) B).left ≫ B.hom := by
    intro F
    have w : (fst (baseAt x) B).left ≫ (baseAt x).hom = (snd (baseAt x) B).left ≫ B.hom :=
      pullback.condition
    rw [w, hsx]; simp only [Category.assoc]
  refine GlobalTheory.T.eq_of_proportional_germs_sectionsEmbedProjectively (fst (baseAt x) B).left b' hemb _ _ ?_ ?_
  · rw [← cancel_mono (baseAt x).hom]
    simp only [Category.assoc]
    rw [hπ, hπ]
    simp only [F₁, F₂, Category.assoc]
    rw [reassoc_of% eB₁, reassoc_of% eB₂, T₁.2.1.1.w, T₂.2.1.1.w, reassoc_of% (Over.w Φ₂), reassoc_of% (Over.w Φ₁),
      reassoc_of% hψA2]
  · intro z
    obtain ⟨q0, hq0⟩ := exists_chart hL (φA₂ z)
    obtain ⟨p₁, hp₁⟩ := exists_chart hM ((ψA ≫ Φ₁.left ≫ φB₁) z)
    obtain ⟨p₂, hp₂⟩ := exists_chart hM ((Φ₂.left ≫ φB₂) z)
    have mA₂ : (𝟙 A₂.left ≫ ψA₂) z ∈ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => q0) := by
      refine memw L _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.id_comp, eA₂]; exact hq0
    have mA₁ : (ψA ≫ ψA₁) z ∈ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => q0) := by
      rw [hG]; simpa using mA₂
    have mB₂ : (𝟙 A₂.left ≫ Φ₂.left ≫ ψB₂) z ∈ (LPow B M (k : ℤ) (topS Rg)).U (fun _ => p₂) := by
      refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.id_comp, Category.assoc, eB₂]; exact hp₂
    have mB₁ : (ψA ≫ Φ₁.left ≫ ψB₁) z ∈ (LPow B M (k : ℤ) (topS Rg)).U (fun _ => p₁) := by
      refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, eB₁]; exact hp₁
    obtain ⟨u₂, hu₂⟩ := g₂ A₂.left (𝟙 _) z _ _ mB₂ mA₂
    obtain ⟨u₁, hu₁⟩ := g₁ A₂.left ψA z _ _ mB₁ mA₁
    simp only [Category.id_comp] at hu₂
    rw [hψA2, hG] at hu₁
    refine ⟨fun j => ∑ i, gs A₂.hom z ⊤ (c i j) * gs ψA₂ z _ ((bA i).f (fun _ => q0)), ⟨fun _ => p₂, ?_, u₂, fun l => ?_⟩,
      ⟨fun _ => p₁, ?_, u₁, fun l => ?_⟩⟩
    · refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₂, Category.assoc]; rw [eB₂]; exact hp₂
    · rw [hbase _ _ _ _ _ (memw M _ _ _ (by rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₂, Category.assoc]; rw [eB₂]; exact hp₂)),
        Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      exact hu₂ l
    · refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₁, Category.assoc]; rw [eB₁]; exact hp₁
    · rw [hbase _ _ _ _ _ (memw M _ _ _ (by rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₁, Category.assoc]; rw [eB₁]; exact hp₁)),
        Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      exact hu₁ l

end GlobalTheory.HomFixMat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismsSameMatrixIsomorphicTestDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homomorphisms_same_matrix_isomorphic_test_data : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A₁ B₁ : Over (Sp R)) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁) (A₂ B₂ : Over (Sp R)) [GrpObj A₂] [GrpObj B₂] (φA₂ : A₂.left ⟶ A.left) (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A₁ B₁ φA₁ φB₁ Φ₁ → IsTest A B L M t A₂ B₂ φA₂ φB₂ Φ₂ → IsMat L M k bA bB eA eB t A₁ B₁ φA₁ φB₁ Φ₁ c → IsMat L M k bA bB eA eB t A₂ B₂ φA₂ φB₂ Φ₂ c → IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ (𝟙 (Sp R)) := by
  first | exact @GlobalTheory.HomFixMat.mat_determines | exact GlobalTheory.HomFixMat.mat_determines | (intros; apply GlobalTheory.HomFixMat.mat_determines <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismMatrixUniqueFixedPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSectionsGroupScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSectionsGroupScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

noncomputable section

namespace GlobalTheory.HomFixIndep

theorem eq_zero_of_locally {X : Scheme.{0}} {U : X.Opens} (s : Γ(X, U))
    (h : ∀ x ∈ U, ∃ (W : X.Opens) (hW : W ≤ U), x ∈ W ∧ (X.presheaf.map (homOfLE hW).op).hom s = 0) :
    s = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf U s 0 fun x hx => ?_
  obtain ⟨W, hW, hxW, h0⟩ := h x hx
  have e1 := X.presheaf.germ_res_apply (homOfLE hW) x hxW s
  change (X.presheaf.germ U x hx).hom s = (X.presheaf.germ U x hx).hom 0
  rw [← e1, h0, map_zero, map_zero]

theorem appLE_eq {X Y : Scheme.{0}} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f₁ ⁻¹ᵁ U) (a : Γ(Y, U)) :
    (f₁.appLE U V e).hom a = (f₂.appLE U V (h ▸ e)).hom a := by
  subst h; rfl

theorem res_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V W : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (h : W ≤ V)
    (a : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom a) = (f.appLE U W (h.trans e)).hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_appLE {X Y Z : Scheme.{0}} (g : X ⟶ Y) (f : Y ⟶ Z) (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : W ≤ g ⁻¹ᵁ V) (a : Γ(Z, U)) :
    (g.appLE V W e₂).hom ((f.appLE U V e₁).hom a) =
      ((g ≫ f).appLE U W (fun _ hx => e₁ (e₂ hx))).hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

end GlobalTheory.HomFixIndep


open GlobalTheory.HomFixIndep in
theorem GlobalTheory.HomFixIndep.pulled_basis_indep : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k mA : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))), IsBCBasis A L k bA → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) [GrpObj A'] (φA' : A'.left ⟶ A.left) (ψA : A'.left ⟶ (topS Rg ⊗ A).left), IsGrpPullback A' A t φA' → ψA ≫ (snd (topS Rg) A).left = φA' → ∀ (d : Fin mA → Γ(Sp R, ⊤)), (∀ (j : Fin 1 → L.ι) (x : A'.left), x ∈ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j → ∃ (W : A'.left.Opens) (hW : W ≤ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j), x ∈ W ∧ ∑ i, (A'.hom.appLE ⊤ W (by simp)).hom (d i) * (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j) W (hW.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j))).hom ((bA i).f j) = 0) → d = 0 := by
  intro Rg _ A _ L k mA bA hB R _ t A' _ φA' ψA hT hψ d hloc
  let t'' : Spec (CommRingCat.of R) ⟶ (topS Rg).left :=
    IsOpenImmersion.lift (⊤ : (Sp Rg).Opens).ι t (by rw [Scheme.Opens.range_ι]; exact fun _ _ => trivial)
  have ht'' : (baseAt t'').hom = t := by simp [t'', baseAt, topS, overRes, baseOver]
  set T := baseAt t'' with hTdef
  have hw : (snd T A).left ≫ A.hom = (fst T A).left ≫ t := by
    rw [← ht'', Over.w (snd T A), Over.w (fst T A)]
  let g : (T ⊗ A).left ⟶ A'.left := hT.1.lift (snd T A).left (fst T A).left hw
  have hg1 : g ≫ φA' = (snd T A).left := hT.1.lift_fst _ _ _
  have hg2 : g ≫ A'.hom = (fst T A).left := hT.1.lift_snd _ _ _
  have hgψ : g ≫ ψA = (homAt t'' ▷ A).left := by
    apply psi_unique
    rw [Category.assoc, hψ, hg1, ← Over.comp_left, whiskerRight_snd]
  let b' : Fin mA → LB.Sec (LPow A L (k : ℤ) T) := fun i =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.pullSecLP A L (k : ℤ) (homAt t'' ▷ A) (whiskerRight_snd (homAt t'') A) (bA i)
  obtain ⟨hli, -⟩ := hB R t'' b' (fun i => ReciprocityTheory.ChartRestriction.G.PullbackSections.isPullSec_pullSecLP A L (k : ℤ) _ _ (bA i))
  rw [Fintype.linearIndependent_iff] at hli
  funext i
  refine hli d ?_ i
  apply Subtype.ext
  funext j
  have hD : (LPow A L (k : ℤ) T).U j ≤ g ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j := by
    intro y hy
    have e : g ≫ ψA ≫ (snd (topS Rg) A).left = (snd T A).left := by
      rw [← Category.assoc, hgψ, ← Over.comp_left, whiskerRight_snd]
    have h1 : (g ≫ ψA ≫ (snd (topS Rg) A).left).base y ∈ (L.U (j 0) : Set A.left) := by
      rw [e]; exact Set.mem_iInter.1 hy 0
    exact Set.mem_iInter.2 fun i => by rw [Subsingleton.elim i 0]; exact h1
  have hF : (∑ i, (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j) (by simp)).hom (d i) *
      (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j)
        (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j)
        (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j)).hom ((bA i).f j)) = 0 := by
    refine eq_zero_of_locally _ fun x hx => ?_
    obtain ⟨W, hW, hxW, h0⟩ := hloc j x hx
    refine ⟨W, hW, hxW, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans h0
    rw [map_mul]
    exact congrArg₂ (· * ·) (res_appLE _ _ _ _ _ _ _) (res_appLE _ _ _ _ _ _ _)
  calc (∑ i, d i • SecM.ofSec A (b' i)).val j
      = ∑ i, ((fst T A).left.appLE ⊤ ((LPow A L (k : ℤ) T).U j) (by simp)).hom (d i) *
          ((homAt t'' ▷ A).left.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j)
            ((LPow A L (k : ℤ) T).U j) (chart_le_res A L _ (whiskerRight_snd (homAt t'') A) _ j)).hom ((bA i).f j) := by
        rw [Submodule.coe_sum, Finset.sum_apply]
        rfl
    _ = (g.appLE _ _ hD).hom (∑ i, (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j) (by simp)).hom (d i) *
      (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j)
        (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j)
        (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j)).hom ((bA i).f j)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        exact congrArg₂ (· * ·) (((appLE_appLE _ _ _ _ _ _ _ _).trans (appLE_eq hg2 _ _ _ _)).symm)
          (((appLE_appLE _ _ _ _ _ _ _ _).trans (appLE_eq hgψ _ _ _ _)).symm)
    _ = _ := by rw [hF, map_zero]; rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSectionsGroupSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_sections_group_scheme : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k mA : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))), IsBCBasis A L k bA → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) [GrpObj A'] (φA' : A'.left ⟶ A.left) (ψA : A'.left ⟶ (topS Rg ⊗ A).left), IsGrpPullback A' A t φA' → ψA ≫ (snd (topS Rg) A).left = φA' → ∀ (d : Fin mA → Γ(Sp R, ⊤)), (∀ (j : Fin 1 → L.ι) (x : A'.left), x ∈ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j → ∃ (W : A'.left.Opens) (hW : W ≤ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j), x ∈ W ∧ ∑ i, (A'.hom.appLE ⊤ W (by simp)).hom (d i) * (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j) W (hW.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j))).hom ((bA i).f j) = 0) → d = 0 := by
  first | (exact @GlobalTheory.HomFixIndep.pulled_basis_indep) | (exact GlobalTheory.HomFixIndep.pulled_basis_indep) | (intros; apply GlobalTheory.HomFixIndep.pulled_basis_indep  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedIsoPowerBundleRatioUnitEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedIsoPowerBundleRatioUnitEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

noncomputable section

namespace GlobalTheory.HomFixUnit

theorem ratio_unit_eq_one : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), IsAbelianScheme A → L.IsLB → M.IsLB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (α α₂ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)) (v : Γ(A'.left, ⊤)ˣ), IsTest A B L M t A' B' φA' φB' Φ' → ψA ≫ (snd (topS Rg) A).left = φA' → ψB ≫ (snd (topS Rg) B).left = φB' → (∀ p, α.s p = res (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤) v * α₂.s p) → RigEq L M k eA eB t Φ' ψA ψB α → RigEq L M k eA eB t Φ' ψA ψB α₂ → v = 1 := by
  intro Rg _ A B _ _ L M k eA eB hA hL hM R _ t A' B' _ _ φA' φB' Φ' ψA ψB α α₂ v hT hψA hψB hv hα hα₂
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hT.1
  refine Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA.unit_eq_one_of_eSec GlobalTheory.globalFns_holds A' hA' v ?_
  show (zeroPt A').appTop.hom v.val = 1
  let W : ((Fin 1 → M.ι) × (Fin 1 → L.ι)) → (Sp R).Opens := fun p =>
    (zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
      t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
      t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0)
  have hloc : ∀ p, ((Sp R).presheaf.map (homOfLE (le_top : W p ≤ ⊤)).op).hom
      ((zeroPt A').appTop.hom v.val) = 1 := by
    intro p
    have h1 := hα p
    have h2 := hα₂ p
    rw [hv p, Units.val_mul, map_mul] at h1
    have hres : (Scheme.Hom.appLE (zeroPt A') ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (W p)
        (inf_le_left.trans inf_le_left)).hom
          ((res (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤) v : Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)ˣ) : Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)) =
        ((Sp R).presheaf.map (homOfLE (le_top : W p ≤ ⊤)).op).hom ((zeroPt A').appTop.hom v.val) := by
      show (A'.left.presheaf.map (homOfLE (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤)).op ≫
        Scheme.Hom.appLE (zeroPt A') ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (W p)
          (inf_le_left.trans inf_le_left)).hom v.val = _
      rw [Scheme.Hom.map_appLE]
      rfl
    rw [hres] at h1
    have key := h1.trans h2.symm
    rw [_root_.mul_assoc] at key
    exact (IsUnit.mul_left_inj (IsUnit.mul ((α₂.s p).isUnit.map _) (((eA.s _).isUnit.map _).pow k))).1
      (key.trans (_root_.one_mul _).symm)
  have hcov : (⊤ : (Sp R).Opens) ≤ iSup W := by
    rintro x -
    have hc : ∀ {X : Scheme.{0}} (N : LB X), N.IsLB → ∀ y : X, ∃ i, y ∈ N.U i := fun N hN y =>
      TopologicalSpace.Opens.mem_iSup.1 (by rw [hN.cover]; trivial)
    obtain ⟨iL, hiL⟩ := hc L hL ((eSec A) (t x))
    obtain ⟨iM, hiM⟩ := hc M hM ((eSec B) (t x))
    haveI := hT.2.2.1
    have eA' : zeroPt A' ≫ ψA ≫ (snd (topS Rg) A).left = t ≫ eSec A := by
      rw [hψA]; exact GlobalTheory.UU.eSec_comp_of_isGrpPullback hT.1
    have eB' : zeroPt A' ≫ (Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left = t ≫ eSec B := by
      have h0 : zeroPt A' ≫ Φ'.left = zeroPt B' := congrArg Over.Hom.left (IsMonHom.one_hom Φ')
      rw [Category.assoc, hψB, ← Category.assoc, h0]
      exact GlobalTheory.UU.eSec_comp_of_isGrpPullback hT.2.1
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => iM, fun _ => iL), ?_⟩
    refine ⟨⟨⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩, Set.mem_iInter.2 fun _ => hiL⟩,
      Set.mem_iInter.2 fun _ => hiM⟩
    · show ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (zeroPt A' x) ∈ M.U iM
      rw [← Scheme.Hom.comp_apply, eB', Scheme.Hom.comp_apply]
      exact hiM
    · show (ψA ≫ (snd (topS Rg) A).left) (zeroPt A' x) ∈ L.U iL
      rw [← Scheme.Hom.comp_apply, eA', Scheme.Hom.comp_apply]
      exact hiL
  exact TopCat.Sheaf.eq_of_locally_eq' (Sp R).sheaf W ⊤ (fun p => homOfLE le_top) hcov _ 1
    (fun p => (hloc p).trans (map_one ((Sp R).presheaf.map (homOfLE le_top : W p ⟶ ⊤).op).hom).symm)

end GlobalTheory.HomFixUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedIsoPowerBundleRatioUnitEqOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalised_isoPowerBundle_ratio_unit_eq_one : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), IsAbelianScheme A → L.IsLB → M.IsLB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (α α₂ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)) (v : Γ(A'.left, ⊤)ˣ), IsTest A B L M t A' B' φA' φB' Φ' → ψA ≫ (snd (topS Rg) A).left = φA' → ψB ≫ (snd (topS Rg) B).left = φB' → (∀ p, α.s p = res (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤) v * α₂.s p) → RigEq L M k eA eB t Φ' ψA ψB α → RigEq L M k eA eB t Φ' ψA ψB α₂ → v = 1 := by
  first | (exact @GlobalTheory.HomFixUnit.ratio_unit_eq_one) | (exact GlobalTheory.HomFixUnit.ratio_unit_eq_one) | (intros; apply GlobalTheory.HomFixUnit.ratio_unit_eq_one  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismMatrixUniqueFixedPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

noncomputable section

namespace GlobalTheory.HomFixUniq

theorem mat_unique : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c c' : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c' → c = c' := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH R _ t A' B' _ _ φA' φB' Φ' c c' hT h₁ h₂
  obtain ⟨hAab, -, hL, hM, -, -, -, -, -, hbA, -⟩ := hH
  obtain ⟨ψA, ψB, α, hψA, hψB, hα, hrig, hmat⟩ := h₁
  obtain ⟨ψA₂, ψB₂, α₂, hψA₂, hψB₂, hα₂, hrig₂, hmat₂⟩ := h₂
  obtain rfl : ψA₂ = ψA := psi_unique _ _ (hψA₂.trans hψA.symm)
  obtain rfl : ψB₂ = ψB := psi_unique _ _ (hψB₂.trans hψB.symm)
  obtain ⟨v, hv⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA.exists_ratio_gen
    (isoLB_cover (L := L) (M := M) hL hM k Φ' ψA₂ ψB₂) hα hα₂
  have v1 : v = 1 := GlobalTheory.T.normalised_isoPowerBundle_ratio_unit_eq_one Rg A B L M k eA eB hAab hL hM R t A' B' φA' φB' Φ' ψA₂ ψB₂ α α₂ v hT hψA hψB hv hrig hrig₂
  have hαe : ∀ p, α.s p = α₂.s p := fun p => by rw [hv p, v1, map_one, _root_.one_mul]
  funext i j
  have hd := GlobalTheory.T.pullback_sections_group_scheme Rg A L k mA bA hbA R t A' φA' ψA₂ hT.1 hψA₂ (fun i => c i j - c' i j) (fun jL x hx => by
    obtain ⟨iM, hiM⟩ : ∃ iM, ((((Φ'.left ≫ ψB₂) ≫ (snd (topS Rg) B).left)).base x) ∈ M.U iM :=
      TopologicalSpace.Opens.mem_iSup.1 (by rw [hM.cover]; trivial)
    refine ⟨(isoLB (L := L) (M := M) k Φ' ψA₂ ψB₂).U (fun _ => iM, jL), inf_le_right,
      ⟨Set.mem_iInter.2 fun _ => hiM, hx⟩, ?_⟩
    have e := (hmat j (fun _ => iM, jL)).symm.trans (hmat₂ j (fun _ => iM, jL))
    have e1 := congrArg Units.val (hαe (fun _ => iM, jL))
    erw [e1] at e
    have e2 := (α₂.s (fun _ => iM, jL)).isUnit.mul_left_cancel e
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 e2)
  exact sub_eq_zero.1 (congrFun hd i)

end GlobalTheory.HomFixUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismMatrixUniqueFixedPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homomorphism_matrix_unique_fixed_pullback : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c c' : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c' → c = c' := by
  first | exact @GlobalTheory.HomFixUniq.mat_unique | exact GlobalTheory.HomFixUniq.mat_unique | (intros; apply GlobalTheory.HomFixUniq.mat_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixRepOfUniversal
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open Opposite

namespace GlobalTheory.EndLoc.HomFixGlue

theorem pullPull_mem {X Y Z Y' Z' : Scheme.{0}} (M : LB X) (F : Y ⟶ X) (G : Z ⟶ Y) (F' : Y' ⟶ X) (G' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (hc : G' ≫ F' = h ≫ G ≫ F) (J : PUnit → PUnit → M.ι) (y : Z')
    (hy : y ∈ ((M.pull F').pull G').U J) :
    h y ∈ ((M.pull F).pull G).U (fun _ => fun _ => J PUnit.unit PUnit.unit) := by
  have h1 := mem_pull.1 (mem_pull.1 hy)
  have e : F (G (h y)) = F' (G' y) := by
    have := congrArg (fun k => k y) hc
    simpa using this.symm
  exact mem_pull.2 (mem_pull.2 (by rw [e]; exact h1))

def chartPullPullPull {X Y Z Y' Z' : Scheme.{0}} (M : LB X) (F : Y ⟶ X) (G : Z ⟶ Y) (F' : Y' ⟶ X) (G' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (hc : G' ≫ F' = h ≫ G ≫ F) : ChartPull ((M.pull F').pull G') ((M.pull F).pull G) h where
  idx J := fun _ => fun _ => J PUnit.unit PUnit.unit
  le J y hy := pullPull_mem M F G F' G' h hc J y hy
  g y J J' hj hj' := by
    have a1 := gm_pull_g (M.pull F') G' (𝟙 _) y J J' hj hj'
    have a2 := gm_pull_g M F' (𝟙 _ ≫ G') y (J PUnit.unit) (J' PUnit.unit) (mem_pull.1 hj) (mem_pull.1 hj')
    have m1 := pullPull_mem M F G F' G' h hc J y hj
    have m2 := pullPull_mem M F G F' G' h hc J' y hj'
    have b1 := gm_pull_g (M.pull F) G h y _ _ m1 m2
    have b2 := gm_pull_g M F (h ≫ G) y (fun _ => J PUnit.unit PUnit.unit) (fun _ => J' PUnit.unit PUnit.unit)
      (mem_pull.1 m1) (mem_pull.1 m2)
    rw [a1, a2, b1, b2]
    have e : (𝟙 _ ≫ G') ≫ F' = (h ≫ G) ≫ F := by simp [hc]
    rw [e]

section
variable {S : Scheme.{0}}

variable (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)

end

end GlobalTheory.EndLoc.HomFixGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixMat

theorem isTest_pullback : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (T T' : Scheme.{0}) (t : T ⟶ Sp Rg) (h : T' ⟶ T) (A₁ B₁ : Over T) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁), IsTest A B L M t A₁ B₁ φA₁ φB₁ Φ₁ → ∃ (A₂ : Over T') (_ : GrpObj A₂) (B₂ : Over T') (_ : GrpObj B₂) (φA₂ : A₂.left ⟶ A.left) (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂), IsTest A B L M (h ≫ t) A₂ B₂ φA₂ φB₂ Φ₂ ∧ IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ h := by
  intro Rg _ A B _ _ L M T T' t h A₁ B₁ _ _ φA₁ φB₁ Φ₁ hT
  obtain ⟨hA, hB, hm, hl⟩ := hT
  haveI : IsMonHom Φ₁ := hm
  have eΦ : ((Over.pullback h).map Φ₁).left ≫ pullback.fst B₁.hom h = pullback.fst A₁.hom h ≫ Φ₁.left :=
    pullback.lift_fst _ _ _
  have gA := isGrpPullback_pullback A₁ h
  have gB := isGrpPullback_pullback B₁ h
  refine ⟨(Over.pullback h).obj A₁, inferInstance, (Over.pullback h).obj B₁, inferInstance,
    pullback.fst A₁.hom h ≫ φA₁, pullback.fst B₁.hom h ≫ φB₁, (Over.pullback h).map Φ₁,
    ⟨gA.comp hA, gB.comp hB, PullGtPf.isMonHom_of_grpPullback gA gB Φ₁ _ eΦ, ?_⟩,
    pullback.fst A₁.hom h, pullback.fst B₁.hom h, gA, gB, rfl, rfl, eΦ⟩
  exact LBIso.chartPull
    (chartPullSame L (fun _ => pullback.fst A₁.hom h ≫ φA₁) (fun _ => φA₁) (fun _ => 1) (pullback.fst A₁.hom h)
      (fun _ => rfl))
    (HomFixGlue.chartPullPullPull M _ _ _ _ (pullback.fst A₁.hom h)
      (by rw [← Category.assoc, eΦ, Category.assoc])) hl

end GlobalTheory.HomFixMat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isTest_comp_isPullD_of_isTest : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (T T' : Scheme.{0}) (t : T ⟶ Sp Rg) (h : T' ⟶ T) (A₁ B₁ : Over T) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁), IsTest A B L M t A₁ B₁ φA₁ φB₁ Φ₁ → ∃ (A₂ : Over T') (_ : GrpObj A₂) (B₂ : Over T') (_ : GrpObj B₂) (φA₂ : A₂.left ⟶ A.left) (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂), IsTest A B L M (h ≫ t) A₂ B₂ φA₂ φB₂ Φ₂ ∧ IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ h := by
  first | (exact @GlobalTheory.HomFixMat.isTest_pullback) | (exact GlobalTheory.HomFixMat.isTest_pullback) | (intros; apply GlobalTheory.HomFixMat.isTest_pullback  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedRepresentsFixedPullbackHoms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixMat

theorem exists_locClosed_homFix : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ (N : ℕ) (X : Scheme.{0}) (c : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (H : Scheme.{0}) (i : H ⟶ X)
    (AH : Over H) (_ : GrpObj AH) (BH : Over H) (_ : GrpObj BH) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left)
    (Φ : AH ⟶ BH), IsClosedImmersion c ∧ IsOpenImmersion i ∧
    IsGrpPullback AH A (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φA ∧ IsGrpPullback BH B (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φB ∧ IsMonHom Φ ∧
    LBIso (L.pull φA) ((M.pull φB).pull Φ.left) ∧
    ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg))) = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  intro Rg _ _ A B _ _ _ _ L M k hA hB hL hM hrA hrB hamp hk hva hbasA hbasB
  obtain ⟨eA, heA⟩ := hrA
  obtain ⟨eB, heB⟩ := hrB
  obtain ⟨mA, bA, hbA⟩ := hbasA
  obtain ⟨mB, bB, hbB⟩ := hbasB
  have hyp : Hyps L M k bA bB eA eB := ⟨hA, hB, hL, hM, heA, heB, hamp, hk, hva, hbA, hbB⟩

  obtain ⟨X, cE, H, i, AH, gA, BH, gB, φA, φB, Φ, hc, hi, htest, hex, hmat⟩ :=
    GlobalTheory.T.exists_locallyClosed_universal_hom_matrix_scheme Rg A B L M k mA mB bA bB eA eB hyp
  refine ⟨mA * mB, X, cE, H, i, AH, gA, BH, gB, φA, φB, Φ, hc, hi, htest.1, htest.2.1, htest.2.2.1,
    htest.2.2.2, ?_⟩
  intro R _ t A' B' _ _ φA' φB' Φ' h1 h2 h3 h4
  have ht : IsTest A B L M t A' B' φA' φB' Φ' := ⟨h1, h2, h3, h4⟩

  obtain ⟨c, hc'⟩ := GlobalTheory.T.line_bundle_sections_product_base_change Rg A B L M k mA mB bA bB eA eB hyp R t A' B' φA' φB' Φ' ht
  obtain ⟨h, hh, hmatc⟩ := hex R t A' B' φA' φB' Φ' c ht hc'

  obtain ⟨A₂, g₂, B₂, g₂', φA₂, φB₂, Φ₂, ht₂, hp₂⟩ :=
    GlobalTheory.T.exists_isTest_comp_isPullD_of_isTest Rg A B L M H (Sp R) (i ≫ cE ≫ affπ Rg (mA * mB)) h AH BH φA φB Φ htest
  have hm₂ := hmat R h A₂ B₂ φA₂ φB₂ Φ₂ ht₂ hp₂
  rw [hh, hmatc] at hm₂
  rw [hh] at ht₂

  have hpd := GlobalTheory.T.homomorphisms_same_matrix_isomorphic_test_data Rg A B L M k mA mB bA bB eA eB hyp R t A₂ B₂ φA₂ φB₂ Φ₂ A' B' φA' φB' Φ' c
    ht₂ ht hm₂ hc'
  have hfin := IsPullD.comp hp₂ hpd
  rw [Category.id_comp] at hfin
  refine ⟨h, ⟨hh, hfin⟩, ?_⟩

  rintro h' ⟨hh', hpd'⟩
  have ht' : IsTest A B L M (h' ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' := by
    rw [hh']; exact ht
  have hm' := hmat R h' A' B' φA' φB' Φ' ht' hpd'
  rw [hh'] at hm'
  have heq : matOf (h' ≫ i ≫ cE) = c :=
    GlobalTheory.T.homomorphism_matrix_unique_fixed_pullback Rg A B L M k mA mB bA bB eA eB hyp R t A' B' φA' φB' Φ' _ _ ht hm' hc'
  have hg : h' ≫ i ≫ cE = h ≫ i ≫ cE := by
    apply hom_ext_affine
    · simp only [Category.assoc]
      rw [hh', hh]
    · intro n
      obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective n
      exact congrFun (congrFun (heq.trans hmatc.symm) p.1) p.2
  have hg' : h' ≫ i = h ≫ i := by
    rw [← cancel_mono cE]
    simpa only [Category.assoc] using hg
  exact (cancel_mono i).1 hg'

end GlobalTheory.HomFixMat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedRepresentsFixedPullbackHomsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_locallyClosed_represents_fixedPullback_homs : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ (N : ℕ) (X : Scheme.{0}) (c : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (H : Scheme.{0}) (i : H ⟶ X)
    (AH : Over H) (_ : GrpObj AH) (BH : Over H) (_ : GrpObj BH) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left)
    (Φ : AH ⟶ BH), IsClosedImmersion c ∧ IsOpenImmersion i ∧
    IsGrpPullback AH A (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φA ∧ IsGrpPullback BH B (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φB ∧ IsMonHom Φ ∧
    LBIso (L.pull φA) ((M.pull φB).pull Φ.left) ∧
    ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg))) = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  first | (exact @GlobalTheory.HomFixMat.exists_locClosed_homFix) | (exact GlobalTheory.HomFixMat.exists_locClosed_homFix) | (intros; apply GlobalTheory.HomFixMat.exists_locClosed_homFix  <;> assumption)
end
