module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechDifferentialOneInclusion
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TerminalRes
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeSite
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ}

def wch (i : X ⟶ PSpace K N) (j : Fin (N + 1)) : X.Opens := i ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)

def uy (i : X ⟶ PSpace K N) {m : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (k : Fin m) : X.Opens :=
  i ⁻¹ᵁ Proj.basicOpen _ (y k)

def wK (q : X ⟶ Spec (CommRingCat.of K)) (i : X ⟶ PSpace K N) {m : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K)
    (s : ℕ) (k : Fin m) : ObjectProperty (Thick (smFun X q)) :=
  St (TF 1 s) (Set.range fun j => uy i y k ⊓ wch i j)

def wU (q : X ⟶ Spec (CommRingCat.of K)) (i : X ⟶ PSpace K N) {m : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K)
    (s : ℕ) : ObjectProperty (Thick (smFun X q)) :=
  fun T => ∃ k, wK q i y s k T

def yQ {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (k k' : Fin m) :
    Γ(PSpace K N, Proj.basicOpen _ (y k')) :=
  (Proj.awayToSection _ (y k')).hom
    (HomogeneousLocalization.Away.mk _ ((MvPolynomial.mem_homogeneousSubmodule e (y k')).2 (hy k')) 1 (y k)
      (by simpa using (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)))

end CrystallineSemistableComparison.Pb
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ZeroC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

def addC (Q : ObjectProperty (Thick (smFun X q))) (ĝ : ∀ T : Q.FullSubcategory, T.obj.B) : CH.Cn (CH.modF (sP Q).A) 1 :=
  fun σ => (show (σ.obj (Fin.last 1)).obj.B from
    ĝ (σ.obj (Fin.last 1)) - (σ.map (homOfLE (Fin.zero_le (Fin.last 1)))).hom.φ (ĝ (σ.obj 0)))

def zeroC (Q : ObjectProperty (Thick (smFun X q))) (ĝ : ∀ T : Q.FullSubcategory, T.obj.B) : CH.Cn (CH.modF (sP Q).A) 0 :=
  fun σ => (show (σ.obj (Fin.last 0)).obj.B from ĝ (σ.obj (Fin.last 0)))

def xdtC (s : ℕ) (V : X.Opens) {d : ℕ} (t : Fin d → Γ(X, V)) (x : Γ(X, V)) : CH.Cn (CH.modF (sP (KS q s {V})).A) d :=
  (CH.mulP (sP (KS q s {V})).A).cupC (Nat.zero_add d)
    (zeroC _ fun T => liftV T.obj (ks_in q s V T.obj T.property) x)
    (cupListC (sP (KS q s {V})).A fun k => addC _ fun T => liftV T.obj (ks_in q s V T.obj T.property) (t k))

end CrystallineSemistableComparison.Pb
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.PowKPull
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

theorem powK_pull {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {C : Type 1} [Category.{0} C]
    (g : C ⥤ Thick (smFun X q)) (c : HdR q 2) (z : CH.Cn (CH.modF (g ⋙ thA (smFun X q))) 2) (hz : CH.d _ 2 z = 0)
    (hcz : (CH.cx _).cls z hz = (CH.Mor.restrict (O (smFun X q)) g).pull 2 c) (k : ℕ) :
    ∃ h, (CH.cx _).cls (cupPowC (g ⋙ thA (smFun X q)) z k) h = (CH.Mor.restrict (O (smFun X q)) g).pull (2 * k) (powK q c k) := by
  induction k with
  | zero =>
    change ∃ h : CH.d (CH.modF (g ⋙ thA (smFun X q))) 0 (cupPowC (g ⋙ thA (smFun X q)) z 0) = 0,
      (CH.cx (CH.modF (g ⋙ thA (smFun X q)))).cls (n := 0) (cupPowC (g ⋙ thA (smFun X q)) z 0) h =
        (CH.Mor.restrict (O (smFun X q)) g).hom.mapH 0 (CH.oneH (thA (smFun X q)))
    have h0 : CH.d (CH.modF (g ⋙ thA (smFun X q))) 0 (cupPowC (g ⋙ thA (smFun X q)) z 0) = 0 := by
      funext s
      simp only [CH.d, cupPowC, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_two]
      simp [CH.modF]
      change (((thA (smFun X q)).map (g.map (GlobalTheory.CatH.toLast 0 s))).hom 1) +
        -(((thA (smFun X q)).map (g.map (GlobalTheory.CatH.toLast 1 s))).hom 1) = 0
      simp only [map_one, add_neg_cancel]
    refine ⟨h0, ?_⟩
    unfold CH.oneH
    exact (CrystallineSemistableComparison.P.mapH_cls (CH.Mor.restrict (O (smFun X q)) g).hom 0
      (fun s => (1 : (thA (smFun X q)).obj (s.obj (Fin.last 0)))) _ (by exact h0)).symm
  | succ k ih =>
    obtain ⟨hk, ek⟩ := ih
    obtain ⟨hc, ec⟩ := CrystallineSemistableComparison.P.cup_cls (CH.mulP (g ⋙ thA (smFun X q))) (show 2 * k + 2 = 2 * (k + 1) by omega)
      (cupPowC (g ⋙ thA (smFun X q)) z k) z hk hz
    refine ⟨hc, ?_⟩
    have key := CrystallineSemistableComparison.P.cup_pull (CH.mulP (thA (smFun X q))) (CH.mulP (g ⋙ thA (smFun X q))) g
      (fun _ => LinearMap.id) (fun _ => LinearMap.id) (fun _ => LinearMap.id)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
      (show 2 * k + 2 = 2 * (k + 1) by omega) (powK q c k) c
    change _ = (CH.Mor.restrict (O (smFun X q)) g).pull (2 * (k + 1))
      ((CH.mulP (thA (smFun X q))).cup (show 2 * k + 2 = 2 * (k + 1) by omega) (powK q c k) c)
    refine (ec.symm.trans ?_).trans key.symm
    rw [ek, hcz]
    rfl

end CrystallineSemistableComparison.Pb
end
end
