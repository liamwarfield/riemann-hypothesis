module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsTautologicalLineAt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

def CLiftK.precomp {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}
    (Λ : CLiftK g D) (h : C' ⥤ C) : CLiftK (h ⋙ g) D where
  p c := Λ.p (h.obj c)
  hp c := Λ.hp (h.obj c)
  w φ := Λ.w (h.map φ)
  hw φ hh := Λ.hw (h.map φ) hh

def zK {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (s : ℕ) :
    CH.Cn (g ⋙ O (smFun X q)) 2 :=
  fun σ => (show (g.obj (σ.obj (Fin.last 2))).B from
    plogK (g.obj (σ.obj (Fin.last 2))).δ s ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1))

def 𝒱D (D : E.LineData X) : Set X.Opens := {V | ∃ σ : (V : Scheme.{0}) ⟶ D.Y, σ ≫ D.f = V.ι}

end CrystallineSemistableComparison.Pb
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

def liftV {V : X.Opens} (T : Thick (smFun X q)) (h : InU V T) (g : Γ(X, V)) : T.B :=
  Classical.choose (Ideal.Quotient.mk_surjective (ev T h g))

def dlogC (Q : ObjectProperty (Thick (smFun X q))) (s : ℕ) (ĝ : ∀ T : Q.FullSubcategory, T.obj.B) :
    CH.Cn (CH.modF (sP Q).A) 1 :=
  fun σ => (show (σ.obj (Fin.last 1)).obj.B from
    plogK (σ.obj (Fin.last 1)).obj.δ s (ĝ (σ.obj (Fin.last 1)) *
      Ring.inverse ((σ.map (homOfLE (Fin.zero_le (Fin.last 1)))).hom.φ (ĝ (σ.obj 0))) - 1))

def jacSpan {V V' : X.Opens} (h : V ≤ V') {A : Type} [CommRing A] (ι : Γ(X, V) →+* A) {d m : ℕ}
    (D : Fin d → Γ(X, V) → A) (κ : Fin m → Fin d) : AddSubgroup A :=
  AddSubgroup.closure {y | ∃ (b : Γ(X, V')) (bs : Fin m → Γ(X, V')),
    y = ι (rs h b) * (Matrix.of fun k l => D (κ k) (rs h (bs l))).det}

section KS
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem inU_mono {V V' : X.Opens} (h : V ≤ V') {T : Thick (smFun X q)} (hT : InU V T) : InU V' T :=
  fun x hx => h (hT hx)

theorem ks_le (s : ℕ) {V V' : X.Opens} (h : V ≤ V') : KS q s {V} ≤ KS q s {V'} := by
  rintro T ⟨hT, W, hW, hTW⟩
  rw [Set.mem_singleton_iff] at hW
  subst hW
  exact ⟨hT, V', rfl, inU_mono q h hTW⟩

theorem ks_in (s : ℕ) (V : X.Opens) : ∀ T, KS q s {V} T → InU V T := by
  rintro T ⟨-, W, hW, hTW⟩
  rw [Set.mem_singleton_iff] at hW
  exact hW ▸ hTW

def resKS (s : ℕ) {V V' : X.Opens} (h : V ≤ V') (r r' : ℤ) (j : ℕ) :
    HQ (KS q s {V'}) r r' j →ₗ[K] HQ (KS q s {V}) r r' j :=
  ((incl (ks_le q s h)).sq (incl_fil _ r) (incl_fil _ r')).pull j

end KS

end CrystallineSemistableComparison.Pb
end
end
