module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing

section Gen

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

theorem gs_sum (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) {n : ℕ} (a : Fin n → Γ(Y, U)) :
    gs f z U (∑ i, a i) = ∑ i, gs f z U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [gs_eq f z U h, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => (gs_eq f z U h (a i)).symm

theorem secScal_sval {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = sval s₁ r z J := by
  have hj : ∀ k, (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) : K₁ ⊕ K₂ → L.ι) k =
      J (r ≫ Sum.elim φ₁ (fun k => h ≫ φ₂ k) k) := by
    intro k; cases k <;> rfl
  have hcoh : LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k)) (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k))) := fun k₁ k₂ hk => by
    rw [hj, hj, hk]
  have H' := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) hcoh
  have hm1 : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) :=
    show r.base z ∈ (⋂ k, ((φ₁ k).base ⁻¹' (L.U (J (r ≫ φ₁ k)) : Set X))) from
      Set.mem_iInter.2 fun k => hJ (r ≫ φ₁ k)
  have hm2 : r z ∈ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    show r.base z ∈ (⋂ k, ((h ≫ φ₂ k).base ⁻¹' (L.U (J (r ≫ h ≫ φ₂ k)) : Set X))) from
      Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ₂ k)
  have hm : r z ∈ (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) := ⟨hm1, hm2⟩
  have hle2 : (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) ≤ h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) := inf_le_right.trans (wchart_comp_le φ₂ h (fun k => J (r ≫ h ≫ φ₂ k)))
  have hle1 : (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) ≤ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) := inf_le_left
  have l1 : gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) ((Y'.presheaf.map (homOfLE hle2).op).hom ((h.app _).hom (s₂.f (fun k => J (r ≫ h ≫ φ₂ k))))) =
      gs (r ≫ h) z (LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k))) (s₂.f (fun k => J (r ≫ h ≫ φ₂ k))) :=
    (gs_res r z hle2 hm _).trans (gs_pull r h z _ (hle2 hm) _)
  have l2 : gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) (resTop (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) 1 * (Y'.presheaf.map (homOfLE hle1).op).hom (s₁.f (fun k => J (r ≫ φ₁ k)))) =
      gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k))) (s₁.f (fun k => J (r ≫ φ₁ k))) := by
    simp only [resTop, map_one]
    rw [_root_.one_mul]
    exact gs_res r z hle1 hm _
  have key := congrArg (gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)))) H'
  have e : (fun k => J ((r ≫ h) ≫ φ₂ k)) = (fun k => J (r ≫ h ≫ φ₂ k)) := by
    funext k; rw [Category.assoc]
  show gs (r ≫ h) z (LB.wchart L φ₂ (fun k => J ((r ≫ h) ≫ φ₂ k)))
      (s₂.f (fun k => J ((r ≫ h) ≫ φ₂ k))) = gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k))) (s₁.f (fun k => J (r ≫ φ₁ k)))
  rw [e]
  exact l1.symm.trans (key.trans l2)

theorem secScal_of_sval (hL : L.IsLB) {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ}
    {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    (H : ∀ (y : Y') (J : (Y' ⟶ X) → L.ι), Good L y J → sval s₂ (𝟙 Y' ≫ h) y J = sval s₁ (𝟙 Y') y J) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1 := by
  intro j₁ j₂ hc
  simp only [resTop, map_one, _root_.one_mul]
  refine fn_ext fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := exists_good L hL y _ _ hc (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hy.1 a, Set.mem_iInter.1 hy.2 a])
  have := H y J hJ
  rw [sval_of s₁ _ y J j₁ (fun k => by rw [Category.id_comp]; exact e (.inl k)),
    sval_of s₂ _ y J j₂ (fun k => by rw [Category.id_comp]; exact e (.inr k))] at this
  have le : LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤ h ⁻¹ᵁ LB.wchart L φ₂ j₂ :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  exact ((gs_res _ y _ hy _).trans (gs_pull _ h y _ (le hy.2) _)).trans (this.trans (gs_res _ y _ hy _).symm)

theorem sval_lin {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)}
    {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε))
    (hs : ∀ j : K → L.ι, s.f j = ∑ i, resTop (LB.wchart L φ j) (b i) * (show Γ(Y, LB.wchart L φ j) from (t i).f j)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s r z J = ∑ i, gs r z ⊤ (b i) * sval (t i) r z J := by
  have hmem : r z ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := by
    show r.base z ∈ (⋂ k, ((φ k).base ⁻¹' (L.U (J (r ≫ φ k)) : Set X)))
    exact Set.mem_iInter.2 fun k => hJ (r ≫ φ k)
  show gs r z (LB.wchart L φ (fun k => J (r ≫ φ k))) (s.f (fun k => J (r ≫ φ k))) = _
  rw [hs, gs_sum r z _ hmem]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul _ z _ hmem]
  congr 1
  exact gs_res r z le_top hmem (b i)

theorem sval_pullSec {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval (pullSec L φ ε s h) r z J = sval s (r ≫ h) z J := by
  have hmem : r z ∈ LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) := by
    show r.base z ∈ (⋂ k, ((h ≫ φ k).base ⁻¹' (L.U (J (r ≫ h ≫ φ k)) : Set X)))
    exact Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)
  calc sval (pullSec L φ ε s h) r z J
      = gs r z (LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)))
          ((Y'.presheaf.map (homOfLE (wchart_comp_le φ h (fun k => J (r ≫ h ≫ φ k)))).op).hom
            ((h.app _).hom (s.f (fun k => J (r ≫ h ≫ φ k))))) := rfl
    _ = gs r z (h ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)))
          ((h.app _).hom (s.f (fun k => J (r ≫ h ≫ φ k)))) :=
        gs_res r z (wchart_comp_le φ h _) hmem _
    _ = gs (r ≫ h) z (LB.wchart L φ (fun k => J (r ≫ h ≫ φ k))) (s.f (fun k => J (r ≫ h ≫ φ k))) :=
        gs_pull r h z _ (wchart_comp_le φ h _ hmem) _
    _ = sval s (r ≫ h) z J := by
        have e : (fun k => J ((r ≫ h) ≫ φ k)) = fun k => J (r ≫ h ≫ φ k) := by
          funext k; rw [Category.assoc]
        show _ = gs (r ≫ h) z (LB.wchart L φ (fun k => J ((r ≫ h) ≫ φ k)))
          (s.f (fun k => J ((r ≫ h) ≫ φ k)))
        rw [e]

end Gen

section Move

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem gs_gF_comp {h : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left}
    (hf : h ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left)
    (y : (DegPre.BF D.toPre F).left) (ζ : F) :
    gs h y ⊤ (gF D.toPre F ζ) = gs (𝟙 _) y ⊤ (gF D.toPre F ζ) := by
  calc gs h y ⊤ (gF D.toPre F ζ)
      = gs (h ≫ (fst (TF (R := V) F) D.toPre.P.A).left) y ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) :=
        gs_pull h (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ (by simp) _
    _ = gs (𝟙 _ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) y ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) := by rw [hf, Category.id_comp]
    _ = gs (𝟙 _) y ⊤ (gF D.toPre F ζ) :=
        (gs_pull (𝟙 _) (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ (by simp) _).symm

theorem vge_move {k : ℕ} {α χ : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))}
    {s' : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))}
    {h : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left}
    (hfst : h ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left)
    {TB : D.toPre.P.A.left ⟶ D.toPre.P.A.left}
    (hh : h ≫ (DegPre.prB D.toPre F).left = (DegPre.prB D.toPre F).left ≫ TB)
    {K₃ K₄ : Type} [Fintype K₃] [Fintype K₄]
    {φ₃ : K₃ → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb D.toPre.P.L φ₃ ε₃))
    (hrel : GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) s'
      (DegPre.famφ D.toPre F α) (DegPre.famε k) s h φ₃ ε₃ u)
    {ψ : K₄ → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)} {δ : K₄ → ℤ}
    (eB : LB.Gen (LB.LinComb D.toPre.P.L ψ δ)) (heB : eB.IsGen)
    (hform : FormEq (Sum.elim (fun i => TB ≫ D.toPre.famφB α i) ψ) (Sum.elim (DegPre.famε k) δ)
      (D.toPre.famφB χ) (DegPre.famε k))
    (c : F)
    (hc : ∀ (y : (DegPre.BF D.toPre F).left) (J : ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
      Good D.toPre.P.L y J →
      (val u (𝟙 _) y J).val = gs (𝟙 _) y ⊤ (gF D.toPre F c) * (val eB (DegPre.prB D.toPre F).left y J).val)
    {r q : ℚ} (hq : ((q : ℚ) : WithTop ℚ) ≤ v c) (hs : VGe D F v k α s r) : VGe D F v k χ s' (r + q) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := hs
  have e1 : ∀ i, ∃ t : D.toPre.SecB k χ, ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D.toPre.P.A.left) (z : Z) (J),
      Good D.toPre.P.L z J → sval t ρ z J = sval (σ i) (ρ ≫ TB) z J * (val eB ρ z J).val := fun i => by
    obtain ⟨t, ht⟩ := exists_sec hL hform (pullMulSec (σ i) TB eB heB)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullMulSec _ _ _ heB ρ z hJ)⟩
  choose σ' hσ' using e1
  have hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB χ i) (DegPre.famε k)
      (DegPre.famφ D.toPre F χ) (DegPre.famε k) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  have e2 : ∀ i, ∃ t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval t ρ z J = sval (σ' i) (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun i => by
    obtain ⟨t, ht⟩ := exists_sec hL hformF (pullSec D.toPre.P.L _ _ (σ' i) (DegPre.prB D.toPre F).left)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullSec _ _ _ _ ρ z hJ)⟩
  choose σ'F hσ'F using e2
  refine ⟨n, fun i => c * a i, σ', σ'F, fun i => ?_, fun i => ?_, fun j => ?_⟩
  · exact secScal_of_sval hL fun y J hJ => (hσ'F i _ (𝟙 _) y J hJ).symm
  · rw [AddValuation.map_mul, WithTop.coe_add, add_comm ((r : ℚ) : WithTop ℚ)]
    exact add_le_add hq (hva i)
  · show s'.f j = ∑ i, resTop _ (gF D.toPre F (c * a i)) * (σ'F i).f j
    refine fn_ext fun y hy => ?_
    choose I hI using fun ψ : (DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left =>
      Geo.Tor.exists_chart hL (ψ y)
    have hIy : Good D.toPre.P.L y I := hI
    have m := hIy.mem (DegPre.famφ D.toPre F χ) (𝟙 _)
    have hy' : y ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j := hy
    have T0 := sec_trans s' (𝟙 _) y hy' m
    set τ := (Geo.Tor.trF (DegPre.famφ D.toPre F χ) (DegPre.famε k) (𝟙 _) y j
      (fun k => I (𝟙 _ ≫ DegPre.famφ D.toPre F χ k))).val with hτ
    have Ti : ∀ i, gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
        (resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (c * a i)) *
          (show Γ((DegPre.BF D.toPre F).left, LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) from (σ'F i).f j)) =
        τ * (gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) * sval (σ'F i) (𝟙 _) y I) := fun i => by
      have S1 : gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
          (resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (c * a i))) =
          gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) := gs_res _ y le_top hy' _
      rw [gs_mul _ y _ hy', S1, sec_trans (σ'F i) (𝟙 _) y hy' m, hτ]
      exact mul_left_comm _ _ _
    have RHS : gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
        (∑ i, resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (c * a i)) *
          (show Γ((DegPre.BF D.toPre F).left, LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) from (σ'F i).f j)) =
        τ * ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) * sval (σ'F i) (𝟙 _) y I := by
      rw [gs_sum _ y _ hy', Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Ti i
    have CORE : sval s' (𝟙 _) y I = ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) * sval (σ'F i) (𝟙 _) y I := by
      have H1 := (secRel_iff hL _ _ s' _ _ s h _ _ u).1 hrel _ (𝟙 _) y I hIy
      have H2 := sval_lin (fun i => gF D.toPre F (a i)) σF (fun j => hsum j) (𝟙 _ ≫ h) y hIy
      rw [H1, H2, hc y I hIy, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have A1 : gs (𝟙 _ ≫ h) y ⊤ (gF D.toPre F (a i)) = gs (𝟙 _) y ⊤ (gF D.toPre F (a i)) := by
        rw [Category.id_comp]; exact gs_gF_comp hfst y (a i)
      have A2 : sval (σF i) (𝟙 _ ≫ h) y I = sval (σ i) ((DegPre.prB D.toPre F).left ≫ TB) y I := by
        rw [← secScal_sval (hscal i) (𝟙 _ ≫ h) y hIy, Category.assoc, hh, Category.id_comp]
      have A3 : sval (σ'F i) (𝟙 _) y I = sval (σ i) ((DegPre.prB D.toPre F).left ≫ TB) y I *
          (val eB (DegPre.prB D.toPre F).left y I).val := by
        rw [hσ'F i _ (𝟙 _) y I hIy, Category.id_comp, hσ' i _ _ y I hIy]
      rw [A1, A2, A3, map_mul, gs_mul _ y ⊤ (by trivial)]
      ring
    exact T0.trans ((congrArg (fun x => τ * x) CORE).trans RHS.symm)

end Move

end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

section Flat

variable {Y X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)

lemma flat_le {K : Type} [Fintype K] (p : (K → L₁.ι) × (K → L₂.ι)) (k : K) :
    LB.wchart L₁ (fun _ : K => f₁) p.1 ⊓ LB.wchart L₂ (fun _ : K => f₂) p.2 ≤
      (L₂.pull f₂).U (fun _ => p.2 k) ⊓ (L₁.pull f₁).U (fun _ => p.1 k) := by
  intro x hx
  simp only [LB.pull, LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_mk,
    Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe] at hx ⊢
  exact ⟨fun _ => hx.2 k, fun _ => hx.1 k⟩

def flatIso (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) {K : Type} [Fintype K] (ε : K → ℤ) :
    LB.Iso (LB.LinComb L₂ (fun _ : K => f₂) ε) (LB.LinComb L₁ (fun _ : K => f₁) ε) :=
  ⟨fun p => ∏ k, res (flat_le L₁ L₂ f₁ f₂ p k) (w.s (fun _ => p.2 k, fun _ => p.1 k)) ^ (-ε k)⟩

lemma comm_alg {M : Type*} [CommGroup M] (a b c : M) (n : ℤ) :
    (a * b⁻¹ * c) ^ (-n) = b ^ n * (a ^ n)⁻¹ * c ^ (-n) := by
  rw [mul_zpow, mul_zpow, zpow_neg a, inv_zpow', neg_neg, mul_comm ((a ^ n)⁻¹) (b ^ n)]

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
lemma gm_pull_g' {Z : Scheme.{0}} {X : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (r : Z ⟶ Y) (z : Z) (a b : L.ι)
    (ha : f (r z) ∈ L.U a) (hb : f (r z) ∈ L.U b) :
    gm r z ((L.pull f).U (fun _ => a) ⊓ (L.pull f).U (fun _ => b)) ((L.pull f).g (fun _ => a) (fun _ => b)) =
      gm (r ≫ f) z (L.U a ⊓ L.U b) (L.g a b) := by
  exact (gm_linComb L (fun _ : PUnit => f) (fun _ => 1) r z (fun _ => a) (fun _ => b)
    (Set.mem_iInter.2 fun _ => ha) (Set.mem_iInter.2 fun _ => hb)).trans (by simp)

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
set_option maxHeartbeats 1000000 in
theorem flatIso_isGen (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) {K : Type} [Fintype K] (ε : K → ℤ) :
    (flatIso L₁ L₂ f₁ f₂ w ε).IsGen := by
  have hP := (isGen_iff w).1 hw
  intro (p : (K → L₁.ι) × (K → L₂.ι)) (q : (K → L₁.ι) × (K → L₂.ι))
  apply unit_ext
  intro y hy
  have hp : y ∈ LB.wchart L₁ (fun _ : K => f₁) p.1 ⊓ LB.wchart L₂ (fun _ : K => f₂) p.2 := hy.1
  have hq : y ∈ LB.wchart L₁ (fun _ : K => f₁) q.1 ⊓ LB.wchart L₂ (fun _ : K => f₂) q.2 := hy.2
  show gm (𝟙 Y) y _ (res _ (∏ k, res (flat_le L₁ L₂ f₁ f₂ p k) (w.s (fun _ => p.2 k, fun _ => p.1 k)) ^ (-ε k))) =
    gm (𝟙 Y) y _ ((res _ ((LB.LinComb L₁ (fun _ : K => f₁) ε).g p.1 q.1) *
      (res _ ((LB.LinComb L₂ (fun _ : K => f₂) ε).g p.2 q.2))⁻¹) *
      res _ (∏ k, res (flat_le L₁ L₂ f₁ f₂ q k) (w.s (fun _ => q.2 k, fun _ => q.1 k)) ^ (-ε k)))
  erw [map_mul, map_mul, map_inv, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy,
    gm_linComb L₁ _ ε (𝟙 Y) y p.1 q.1 hp.1 hq.1, gm_linComb L₂ _ ε (𝟙 Y) y p.2 q.2 hp.2 hq.2]
  erw [map_prod, map_prod]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h1 : f₁ y ∈ L₁.U (p.1 k) := Set.mem_iInter.1 hp.1 k
  have h1' : f₁ y ∈ L₁.U (q.1 k) := Set.mem_iInter.1 hq.1 k
  have h2 : f₂ y ∈ L₂.U (p.2 k) := Set.mem_iInter.1 hp.2 k
  have h2' : f₂ y ∈ L₂.U (q.2 k) := Set.mem_iInter.1 hq.2 k
  have e := hP Y (𝟙 Y) y (p.2 k) (q.2 k) (fun _ => p.1 k) (fun _ => q.1 k) (by simpa using h2) (by simpa using h2')
    (Set.mem_iInter.2 fun _ => by simpa using h1) (Set.mem_iInter.2 fun _ => by simpa using h1')
  rw [gm_pull_g' L₁ f₁ (𝟙 Y) y (p.1 k) (q.1 k) (by simpa using h1) (by simpa using h1')] at e
  rw [map_zpow, map_zpow]
  erw [gm_res _ y _ hp, gm_res _ y _ hq]
  change ReciprocityTheory.ChartRestriction.G.Geo.Tor.gw w (𝟙 Y) y (p.2 k) (fun _ => p.1 k) ^ (-ε k) =
    _ * _ * ReciprocityTheory.ChartRestriction.G.Geo.Tor.gw w (𝟙 Y) y (q.2 k) (fun _ => q.1 k) ^ (-ε k)
  rw [e]
  simp only [Category.id_comp]
  exact comm_alg _ _ _ _

end Flat

section NZ

variable {Y : Scheme.{0}}

lemma mem_nonzeroLocus {M : LB Y} (s : LB.Sec M) (y : Y) :
    y ∈ nonzeroLocus s ↔ ∃ j, y ∈ Y.basicOpen (s.f j) := by
  rw [nonzeroLocus, TopologicalSpace.Opens.mem_iSup]

theorem nonzeroLocus_secOfIso {A B : LB Y} (u : LB.Iso A B) (t : LB.Sec B) (hu : u.IsGen) (hA : A.IsLB)
    (hB : B.IsLB) : nonzeroLocus t ≤ nonzeroLocus (secOfIso (u := u) t hu hA hB) := by
  intro y hy
  obtain ⟨b, hb⟩ := (mem_nonzeroLocus t y).1 hy
  have hyb : y ∈ B.U b := Y.basicOpen_le _ hb
  obtain ⟨a, ha⟩ : ∃ a, y ∈ A.U a := by
    have : y ∈ (⨆ a, A.U a : Y.Opens) := by rw [hA.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  refine (mem_nonzeroLocus _ y).2 ⟨a, ?_⟩
  have e := secOfIso_spec (u := u) t hu hA hB a b
  have e2 := congrArg Y.basicOpen e
  rw [isoCand, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (Units.isUnit _), Scheme.basicOpen_res,
    Scheme.basicOpen_res] at e2
  have hmem : y ∈ (A.U a ⊓ B.U b) ⊓ ((A.U a ⊓ B.U b) ⊓ Y.basicOpen (t.f b)) := ⟨⟨ha, hyb⟩, ⟨ha, hyb⟩, hb⟩
  rw [← e2] at hmem
  exact hmem.2

end NZ

section Main

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

end Main

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.MemFinsetInf
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

def subSec {Y : Scheme.{0}} {M : LB Y} (s s' : LB.Sec M) : LB.Sec M where
  f j := s.f j - s'.f j
  compat i j := by rw [map_sub, map_sub, s.compat, s'.compat, mul_sub]

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

lemma fstG_act {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) {G : Over (Spec (CommRingCat.of R))}
    (f : G ⟶ G) :
    ((Over.pullback (thick R I e)).map f).left ≫ (fstG I e G).left = (fstG I e G).left ≫ f.left := by
  simp only [fstG]
  simp
  all_goals first
    | exact pullback.lift_fst _ _ _
    | erw [pullback.lift_fst]

lemma pG_act {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) {O : Type} [Ring O] [StarRing O]
    [Module O D.toPre.X] {ιD : D.OAct O} {ιA : A.OAct O} {ιG : RingAct G O} (hlin : U.OLinear O ιD ιA ιG)
    (e : ℕ) (a : O) :
    ((Over.pullback (thick R I e)).map (ιG.act a)).left ≫ (U.gt e).pG.left =
      (U.gt e).pG.left ≫ (ιD.onB.act a).left := by
  have hq := congrArg (fun φ => φ.left) (hlin.q_lin e a)
  simp only [Over.comp_left] at hq
  unfold GtCoord.pG
  simp only [Over.comp_left, Over.map_map_left, Category.assoc]
  rw [← Category.assoc, hq, Category.assoc]
  congr 1
  first
    | exact fstG_act I e (ιD.onB.act a)
    | (unfold DegPre.prBe; simp; done)
    | (unfold DegPre.prBe; simp; exact pullback.lift_fst _ _ _)

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsAtScale
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

section Scale

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma const_pull' {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (pY : Y ⟶ Spec (CommRingCat.of R)) (pZ : Z ⟶ Spec (CommRingCat.of R))
    (hφ : φ ≫ pZ = pY) (r : R) {U : Z.Opens} {W : Y.Opens} (h : W ≤ φ ⁻¹ᵁ U) :
    (Y.presheaf.map (homOfLE h).op).hom ((φ.app U).hom (resTop U (scal pZ r))) = resTop W (scal pY r) := by
  subst hφ
  simp only [rs, resTop, scal, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have key := congrArg (fun f => (CommRingCat.Hom.hom f) ((pZ.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))
    (φ.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.comp_apply] at key
  rw [key, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem expandsAt_scale (U : UnifPre I D A G) (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (r : R) (h : U.ExpandsAt e k σ f) :
    U.ExpandsAt e k (SecOps.secScale (scal G.hom r) σ)
      (fun α => SecOps.secScale (scal D.toPre.P.A.hom r) (f α)) := by
  obtain ⟨S, hvan, hid⟩ := h
  refine ⟨S, fun α hα j => ?_, fun p j₁ jf jt h1 hcoh => ?_⟩
  · show ((U.gt e).pG.left.app _).hom (resTop _ (scal D.toPre.P.A.hom r) * (f α).f j) = 0
    rw [map_mul, hvan α hα j, mul_zero]
  · have e0 := hid p j₁ jf jt h1 hcoh
    set W := U.expW e p j₁ S jf jt
    have hG : (fstG I e G).left ≫ G.hom = ((Over.map (thick R I e)).obj (thickObj R I e G)).hom := Over.w _
    have hB : (U.gt e).pG.left ≫ D.toPre.P.A.hom = ((Over.map (thick R I e)).obj (thickObj R I e G)).hom :=
      Over.w _
    have e1 := congrArg (fun x => resTop W (scal ((Over.map (thick R I e)).obj (thickObj R I e G)).hom r) * x) e0
    simp only [Finset.mul_sum] at e1
    convert e1 using 1
    · simp only [SecOps.secScale]
      erw [map_mul, map_mul, const_pull' (fstG I e G).left _ G.hom (Over.w _) r (U := U.LG.L.wchart (fun _ => 𝟙 G.left) j₁)]
      exact mul_left_comm _ _ _
    · refine Finset.sum_congr rfl (fun α _ => ?_)
      simp only [SecOps.secScale]
      erw [map_mul, map_mul, const_pull' (U.gt e).pG.left _ D.toPre.P.A.hom (Over.w _) r (U := D.toPre.P.L.wchart (D.toPre.famφB α.1) (jf α.1))]
      exact mul_assoc _ _ _

end Scale

lemma scal_mul {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of V)) (r r' : V) : scal p (r * r') = scal p r * scal p r' := by
  simp only [scal, map_mul]

lemma resTop_mul {Y : Scheme.{0}} (W : Y.Opens) (c c' : Γ(Y, ⊤)) : resTop W (c * c') = resTop W c * resTop W c' :=
  map_mul _ _ _

lemma app_resTop {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (U : Z.Opens) {W : Y.Opens} (h : W ≤ φ ⁻¹ᵁ U) (c : Γ(Z, ⊤)) :
    (Y.presheaf.map (homOfLE h).op).hom ((φ.app U).hom (resTop U c)) = resTop W (φ.appTop.hom c) := by
  simp only [resTop]
  have key := congrArg (fun f => (CommRingCat.Hom.hom f) c) (φ.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.comp_apply] at key
  rw [key, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma secScal_scale {X Y Y' : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (hs : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (c' : Γ(Y, ⊤)) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ (SecOps.secScale c' s₂) h (h.appTop.hom c' * c) := by
  intro j₁ j₂ hj
  have e := hs j₁ j₂ hj
  show _ = _ * _
  erw [map_mul, map_mul, e, app_resTop, resTop_mul]
  exact (_root_.mul_assoc _ _ _).symm

section BackK

variable {G : Over (Spec (CommRingCat.of V))}

lemma rs_resTop {Y : Scheme.{0}} {W W' : Y.Opens} (h : W' ≤ W) (c : Γ(Y, ⊤)) : rs h (resTop W c) = resTop W' c :=
  SecOps.resTop_res h c

end BackK

section Integral

variable (D : DegData V (maximalIdeal V)) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

end Integral

end ReciprocityTheory.ChartRestriction.G.DVR
end
end
