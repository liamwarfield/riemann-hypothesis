module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrSt
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def ChartPrimTrSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (wPT : PrimTyG I.G),
    IsPrimG I.G wPT →
    letI := io.toAlgebra
    ∃ wP : PrimTy H Xo, IsPrim wP ∧
      ∃ wP' : LB.Gen (LB.LinComb I.t'.PP.L (primφ I.t') primε), wP'.IsGen ∧
        (∃ c₂ : LB.Gen (LB.LinComb I.G.PP.L (fun k => primφ I.t' k ≫ I.m2.φ) primε),
          LB.Gen.Corr I.G.PP.L _ _ _ _ c₂ (LB.pullGen I.G.PP.L _ _ wPT I.m2.φ) ∧
          LB.Gen.Maps (LB.linCombIso I.w2 (primφ I.t') primε) wP' (flatGen I.G.PP.L I.m2.φ _ _ c₂)) ∧
        ∃ c₁ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (fun k => primφ I.t' k ≫ I.m1.φ) primε),
          LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ c₁ (LB.pullGen Xo.univ.t.PP.L _ _ wP I.m1.φ) ∧
          LB.Gen.Maps (LB.linCombIso I.w1 (primφ I.t') primε) wP' (flatGen Xo.univ.t.PP.L I.m1.φ _ _ c₁)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem primφ_comm {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (k : Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) : primφ t' k ≫ m.φ = m.φ ≫ primφ t k := by
  rcases k with k | I
  · simp [primφ]
  · show (psum t'.G ![𝟙 t'.G, t'.act.act H.w0] I.down).left ≫ m.cm.F =
      m.cm.F ≫ (psum t.G ![𝟙 t.G, t.act.act H.w0] I.down).left
    refine (psum_push m.cart ![𝟙 t'.G, t'.act.act H.w0] ![𝟙 t.G, t.act.act H.w0] (pushPt m.cart.1.w (𝟙 t'.G))
      (fun i => ?_) I.down).trans ?_
    · fin_cases i
      · simp
      · exact Over.OverMorphism.ext (by simp [pushPt, m.act H.w0])
    · simp [pushPt]

variable {X Y : Scheme.{0}} {K : Type} [Fintype K]

theorem corr_self (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) :
    LB.Gen.Corr L φ ε φ ε c c := by
  intro j j' _ _ h
  obtain rfl : j = j' := funext fun k => h k k rfl
  rfl

theorem exists_reindex (L : LB X) {φ φ' : K → (Y ⟶ X)} (h : φ' = φ) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen) :
    ∃ c' : LB.Gen (LB.LinComb L φ' ε), c'.IsGen ∧ LB.Gen.Corr L φ' ε φ ε c' c := by
  subst h
  exact ⟨c, hc, corr_self L _ ε c⟩

theorem maps_flat {X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε))
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε))
    (R : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
        gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) = pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q)) :
    LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε t) := by
  refine (maps_iff w φ' (fun k => φ' k ≫ F) ε a t (𝟙 Y) (flatGen L F φ' ε t)
    (fun j x hx => wchart_pull_le L F φ' j hx) (fun j => ?_)).2 ?_
  · refine unit_ext fun y hy => ?_
    have hyV : (𝟙 Y : Y ⟶ Y) y ∈ ((L.pull F).LinComb φ' ε).U j := hy
    have hyU : (𝟙 Y : Y ⟶ Y) ((𝟙 Y : Y ⟶ Y) y) ∈ LB.wchart L (fun k => φ' k ≫ F) (fun k => j k ⟨⟩) :=
      wchart_pull_le L F φ' j hy
    refine (gm_res (𝟙 Y) y _ hyV _).trans ?_
    refine Eq.trans ?_ (gm_res (𝟙 Y) y _ hyV _).symm
    have e := gm_pull (𝟙 Y) (𝟙 Y) y _ hyU (t.s fun k => j k ⟨⟩)
    rw [Category.comp_id] at e
    exact e.symm
  · intro Z r z p q hp hq
    rw [Category.comp_id]
    exact R Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)

end Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf
