module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExpDerivativeLie
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.TwoClsEMap

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmpleB
section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.IsFiniteMapG4map
section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.IsFiniteMapTensorHom
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar.XB

variable {S : Scheme.{0}}

def pr8 (A : Over S) : Fin 8 → (G4 (A ⊗ A) ⟶ A)
  | 0 => prj (A ⊗ A) 0 ≫ fst A A
  | 1 => prj (A ⊗ A) 0 ≫ snd A A
  | 2 => prj (A ⊗ A) 1 ≫ fst A A
  | 3 => prj (A ⊗ A) 1 ≫ snd A A
  | 4 => prj (A ⊗ A) 2 ≫ fst A A
  | 5 => prj (A ⊗ A) 2 ≫ snd A A
  | 6 => prj (A ⊗ A) 3 ≫ fst A A
  | 7 => prj (A ⊗ A) 3 ≫ snd A A

def lim8 (A : Over S) : IsLimit (Fan.mk (G4 (A ⊗ A)) (pr8 A)) :=
  mkFanLimit _ (fun s => fourfoldProductLift ![lift (s.proj 0) (s.proj 1), lift (s.proj 2) (s.proj 3),
      lift (s.proj 4) (s.proj 5), lift (s.proj 6) (s.proj 7)])
    (fun s k => by fin_cases k <;> simp [pr8, fourfoldProductLift, prj])
    (fun s m hm => by
      have h0 : m ≫ pr8 A 0 = s.proj 0 := hm 0
      have h1 : m ≫ pr8 A 1 = s.proj 1 := hm 1
      have h2 : m ≫ pr8 A 2 = s.proj 2 := hm 2
      have h3 : m ≫ pr8 A 3 = s.proj 3 := hm 3
      have h4 : m ≫ pr8 A 4 = s.proj 4 := hm 4
      have h5 : m ≫ pr8 A 5 = s.proj 5 := hm 5
      have h6 : m ≫ pr8 A 6 = s.proj 6 := hm 6
      have h7 : m ≫ pr8 A 7 = s.proj 7 := hm 7
      simp only [pr8, prj, ← Category.assoc] at h0 h1 h2 h3 h4 h5 h6 h7
      refine CartesianMonoidalCategory.hom_ext _ _ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)
        (CartesianMonoidalCategory.hom_ext _ _ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)
          (CartesianMonoidalCategory.hom_ext _ _ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)
            (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_))) <;>
        simp [fourfoldProductLift, ← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7])

variable {T : Scheme.{0}} (s : T ⟶ S)

theorem isFinite_map_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    (hf : IsFinite ((Over.pullback s).map f).left) (hg : IsFinite ((Over.pullback s).map g).left) :
    IsFinite ((Over.pullback s).map (f ⊗ₘ g)).left := by
  set F := Over.pullback s
  have he : F.map (f ⊗ₘ g) =
      CartesianMonoidalCategory.prodComparison F X X' ≫ (F.map f ⊗ₘ F.map g) ≫
        inv (CartesianMonoidalCategory.prodComparison F Y Y') := by
    rw [← Category.assoc, ← CartesianMonoidalCategory.prodComparison_natural, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  have ht : IsFinite (Over.Hom.left (F.map f ⊗ₘ F.map g)) :=
    GlobalTheory.TensorFinite.isFinite_tensorHom _ _ hf hg
  haveI : IsIso (CartesianMonoidalCategory.prodComparison F X X') :=
    CartesianMonoidalCategory.isIso_prodComparison_of_preservesLimit_pair F X X'
  haveI : IsIso (CartesianMonoidalCategory.prodComparison F Y Y') :=
    CartesianMonoidalCategory.isIso_prodComparison_of_preservesLimit_pair F Y Y'
  haveI : IsIso (Over.Hom.left (CartesianMonoidalCategory.prodComparison F X X')) :=
    (Over.forget T).map_isIso (CartesianMonoidalCategory.prodComparison F X X')
  haveI : IsIso (Over.Hom.left (inv (CartesianMonoidalCategory.prodComparison F Y Y'))) :=
    (Over.forget T).map_isIso (inv (CartesianMonoidalCategory.prodComparison F Y Y'))
  have h1 : IsFinite (Over.Hom.left (CartesianMonoidalCategory.prodComparison F X X')) := inferInstance
  have h2 : IsFinite (Over.Hom.left (inv (CartesianMonoidalCategory.prodComparison F Y Y'))) :=
    inferInstance
  rw [he, Over.comp_left, Over.comp_left]
  exact MorphismProperty.comp_mem @IsFinite _ _ h1 (MorphismProperty.comp_mem @IsFinite _ _ ht h2)

end PositivityTheory.PrwZar.XB
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar.XB

variable {S : Scheme.{0}}

def fourfoldProductMap {G H : Over S} (h : G ⟶ H) : G4 G ⟶ G4 H := h ⊗ₘ (h ⊗ₘ (h ⊗ₘ h))

theorem isFinite_map_g4map {T : Scheme.{0}} (s : T ⟶ S) {G H : Over S} (h : G ⟶ H)
    (hh : IsFinite ((Over.pullback s).map h).left) : IsFinite ((Over.pullback s).map (fourfoldProductMap h)).left :=
  isFinite_map_tensorHom s _ _ hh (isFinite_map_tensorHom s _ _ hh (isFinite_map_tensorHom s _ _ hh hh))

variable {Ω : Type} [Field Ω]

theorem isIso_inv_left {G : Over (Sp Ω)} [GrpObj G] [IsCommMonObj G] : IsIso ((𝟙 G)⁻¹ : G ⟶ G).left := by
  have e : ((𝟙 G)⁻¹ : G ⟶ G) ≫ (𝟙 G)⁻¹ = 𝟙 G := by
    rw [GrpObj.comp_inv, Category.comp_id, inv_inv]
  haveI : IsIso ((𝟙 G)⁻¹ : G ⟶ G) := ⟨⟨(𝟙 G)⁻¹, e, e⟩⟩
  exact (Over.forget (Sp Ω)).map_isIso ((𝟙 G)⁻¹ : G ⟶ G)

theorem relAmple_sym {G : Over (Sp Ω)} [GrpObj G] [IsCommMonObj G] [IsProper G.hom] {L : LB G.left} (hL : L.IsLB)
    (ha : Out.RelAmple G L) :
    Out.RelAmple G (LB.LinComb L (K := Fin 2) ![𝟙 G.left, ((𝟙 G)⁻¹ : G ⟶ G).left] ![1, 1]) := by
  haveI : IsIso ((𝟙 G)⁻¹ : G ⟶ G).left := isIso_inv_left
  haveI : IsAffineHom ((𝟙 G)⁻¹ : G ⟶ G).left := inferInstance
  have hLi : Out.RelAmple G (L.pull ((𝟙 G)⁻¹ : G ⟶ G).left) :=
    GlobalTheory.PosDefAmple.relAmple_pull_of_isAffineHom _ hL ha
  have hN := LB.isLB_linComb (K := Fin 2) hL ![𝟙 G.left, ((𝟙 G)⁻¹ : G ⟶ G).left] ![1, 1]
  refine GlobalTheory.relAmple_of_isAmpleLB G hN (fun U hU => ?_)
  have hP := LB.isLB_pull hL ((𝟙 G)⁻¹ : G ⟶ G).left
  have h1 := GlobalTheory.isAmpleLB_of_relAmple G hL ha U hU
  have h2 := GlobalTheory.isAmpleLB_of_relAmple G hP hLi U hU
  have a1 := LB.isLB_pull hN (G.hom ⁻¹ᵁ U).ι
  have a2 := LB.isLB_pull hL (G.hom ⁻¹ᵁ U).ι
  have a3 := LB.isLB_pull hP (G.hom ⁻¹ᵁ U).ι
  have a4 := LB.isLB_div a1 a2
  have a5 := LB.isLB_div a4 a3
  refine GlobalTheory.IsAmpleLB.tensor h1 h2 a1 ?_
  rw [← cls_eq_zero_iff a5, cls_div a4 a3 a5, cls_div a1 a2 a4, cls_pull hN _ a1, cls_pull hL _ a2,
    cls_pull hP _ a3, cls_pull hL _ hP, cls_linComb hL _ _ hN]
  simp [Fin.sum_univ_two, pull_id]

end PositivityTheory.PrwZar.XB
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]


set_option maxHeartbeats 400000 in
theorem relAmple_lPart (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (mu : B ⟶ A) [IsMonHom mu]
    (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (ha : Out.RelAmple ((Over.pullback s).obj A) L) (hmu : IsFinite ((Over.pullback s).map mu).left) :
    Out.RelAmple ((Over.pullback s).obj (G4 (A ⊗ B))) (lPart mu s L) := by
  have hGA : IsAbelianScheme ((Over.pullback s).obj A) := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  haveI : IsProper ((Over.pullback s).obj A).hom := hGA.proper
  have hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hAB : IsAbelianScheme (A ⊗ B) := AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have h4A : IsAbelianScheme (G4 (A ⊗ A)) :=
    AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAA
      (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAA (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAA hAA))
  have h4B : IsAbelianScheme (G4 (A ⊗ B)) :=
    AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB
      (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB hAB))
  have hY : IsAbelianScheme ((Over.pullback s).obj (G4 (A ⊗ A))) := GlobalTheory.isAbelianScheme_pullback_obj s _ h4A
  have hG : IsAbelianScheme ((Over.pullback s).obj (G4 (A ⊗ B))) := GlobalTheory.isAbelianScheme_pullback_obj s _ h4B
  haveI : IsProper ((Over.pullback s).obj (G4 (A ⊗ A))).hom := hY.proper
  haveI : IsProper ((Over.pullback s).obj (G4 (A ⊗ B))).hom := hG.proper
  have hL' : (L.LinComb ![𝟙 _, Over.Hom.left (𝟙 ((Over.pullback s).obj A))⁻¹] ![1, 1]).IsLB :=
    LB.isLB_linComb hL _ _
  have ha' := XB.relAmple_sym hL ha
  haveI hpr : ∀ j, IsMonHom (XB.pr8 A j) := by
    intro j
    fin_cases j <;> simp only [XB.pr8] <;> infer_instance
  let p : Out.IsPowGrp ((Over.pullback s).obj (G4 (A ⊗ A))) ((Over.pullback s).obj A) 8 :=
    { pr := fun j => (Over.pullback s).map (XB.pr8 A j)
      hom := fun j => inferInstance
      lim := (isLimitMapConeFanMkEquiv (Over.pullback s) _ _).1 (isLimitOfPreserves _ (XB.lim8 A)) }
  have hbox := GlobalTheory.relAmple_boxLB _ _ _ 8 p _ hL' ha'
  have hboxLB : (Out.boxLB (L.LinComb ![𝟙 _, Over.Hom.left (𝟙 ((Over.pullback s).obj A))⁻¹] ![1, 1])
      p.pr).IsLB := LB.isLB_linComb hL' _ _
  have hid : IsFinite ((Over.pullback s).map (𝟙 A)).left := by
    have e1 : (Over.pullback s).map (𝟙 A) = 𝟙 _ := (Over.pullback s).map_id A
    rw [e1, Over.id_left]
    infer_instance
  have hΦ : IsFinite ((Over.pullback s).map (XB.fourfoldProductMap (𝟙 A ⊗ₘ mu))).left :=
    XB.isFinite_map_g4map s _ (XB.isFinite_map_tensorHom s _ _ hid hmu)
  haveI := hΦ
  have h2 := GlobalTheory.PosDefAmple.relAmple_pull_of_isAffineHom ((Over.pullback s).map (XB.fourfoldProductMap (𝟙 A ⊗ₘ mu)))
    hboxLB hbox
  have hlpLB : (lPart mu s L).IsLB := LB.isLB_linComb hL _ _
  have hq : ∀ i : Fin 4, XB.fourfoldProductMap (𝟙 A ⊗ₘ mu) ≫ prj (A ⊗ A) i = prj (A ⊗ B) i ≫ (𝟙 A ⊗ₘ mu) := by
    intro i
    fin_cases i <;> simp [XB.fourfoldProductMap, prj]
  have hinv : ∀ {X : Over (Sp Ω)} (f : X ⟶ (Over.pullback s).obj A),
      (pull (Over.Hom.left f⁻¹)) (cls L hL) =
        (pull (Over.Hom.left f)) ((pull (Over.Hom.left (𝟙 ((Over.pullback s).obj A))⁻¹)) (cls L hL)) := by
    intro X f
    rw [← pull_comp, ← Over.comp_left, GrpObj.comp_inv, Category.comp_id]
  refine GlobalTheory.PosDefAmple.relAmple_of_nsmul hlpLB (LB.isLB_pull hboxLB _) le_rfl ?_ h2
  rw [one_smul, cls_pull hboxLB, GlobalTheory.PosDefAmple.pull_cls_boxLB p.pr hL']
  simp only [lPart]
  simp only [cls_linComb hL, Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_eight, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, map_add, Over.id_left, pull_id]
  simp only [p, ← Functor.map_comp, XB.pr8]
  simp only [← Category.assoc, hq]
  simp only [Category.assoc, tensorHom_fst, tensorHom_snd, Category.comp_id, phiL]
  simp only [hinv (pA s 0), hinv (pA s 1), hinv (pA s 2), hinv (pA s 3), hinv (pM mu s 0), hinv (pM mu s 1),
    hinv (pM mu s 2), hinv (pM mu s 3)]
  simp only [pA, pM]
  abel

end PositivityTheory.PrwZar
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FinSurjOfQuasiInverse
section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.IsFiniteMuFibre
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar.Z2

theorem isAbelianScheme_pb {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A]
    (h : IsAbelianScheme A) : IsAbelianScheme ((Over.pullback f).obj A) := by
  have := h.comm
  have := h.smooth
  have := h.proper
  have := h.geomConnected
  exact
    { comm := inferInstance
      smooth := (inferInstance : Smooth (pullback.snd A.hom f))
      proper := (inferInstance : IsProper (pullback.snd A.hom f))
      geomConnected := (inferInstance : GeometricallyConnected (pullback.snd A.hom f)) }

theorem pb_map_id_pow {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Over S) [GrpObj B] (m : ℕ) :
    (Over.pullback f).map (𝟙 B ^ m) = 𝟙 ((Over.pullback f).obj B) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero]; exact CategoryTheory.Functor.map_one _
  | succ n ih => rw [pow_succ, pow_succ, CategoryTheory.Functor.map_mul, ih, CategoryTheory.Functor.map_id]

theorem fin_surj_core {Ω : Type} [Field Ω] {As Bs : Over (Sp Ω)} [GrpObj As] [GrpObj Bs]
    (hA : IsAbelianScheme As) (hB : IsAbelianScheme Bs) (ls : As ⟶ Bs) (mus : Bs ⟶ As) (m : ℕ) (hm : 1 ≤ m)
    (h₁ : ls ≫ mus = 𝟙 As ^ m) (h₂ : mus ≫ ls = 𝟙 Bs ^ m) {L : LB As.left} (hL : L.IsLB)
    (ha : Out.RelAmple As L) :
    IsFinite ls.left ∧ Surjective ls.left ∧ IsFinite mus.left ∧ Surjective mus.left := by
  have := hA.comm
  have := hA.proper
  have := hB.proper
  have hfin : IsFinite ((𝟙 As) ^ m : As ⟶ As).left :=
    ((GlobalTheory.T.cube_trivial_and_finite_flat_surjective_mul_abelianScheme Ω As L (L.pull (fst As As).left) hA hL ha (LB.isLB_pull hL _)).2 m hm).1
  have hsB : Surjective ((𝟙 Bs) ^ m : Bs ⟶ Bs).left := GlobalTheory.T.abelianScheme_nsmul_surjective Ω Bs hB m (by omega)
  have hsA : Surjective ((𝟙 As) ^ m : As ⟶ As).left := GlobalTheory.T.abelianScheme_nsmul_surjective Ω As hA m (by omega)
  have e₁ : ls.left ≫ mus.left = ((𝟙 As) ^ m : As ⟶ As).left := by rw [← Over.comp_left, h₁]
  have e₂ : mus.left ≫ ls.left = ((𝟙 Bs) ^ m : Bs ⟶ Bs).left := by rw [← Over.comp_left, h₂]
  have hsl : Surjective ls.left := by
    have : Surjective (mus.left ≫ ls.left) := by rw [e₂]; exact hsB
    exact AlgebraicGeometry.Surjective.of_comp (f := mus.left) (g := ls.left)
  have hsm : Surjective mus.left := by
    have : Surjective (ls.left ≫ mus.left) := by rw [e₁]; exact hsA
    exact AlgebraicGeometry.Surjective.of_comp (f := ls.left) (g := mus.left)
  have hpm : IsProper mus.left := by
    have : IsProper (mus.left ≫ As.hom) := by rw [Over.w]; infer_instance
    exact IsProper.of_comp _ As.hom
  have hfl : IsFinite ls.left := by
    have : IsFinite (ls.left ≫ mus.left) := by rw [e₁]; exact hfin
    exact MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) ls.left mus.left inferInstance this
  have hqm : LocallyQuasiFinite mus.left := by
    rw [locallyQuasiFinite_iff_finite_preimage_singleton]
    intro a
    have hq : LocallyQuasiFinite (ls.left ≫ mus.left) := by rw [e₁]; infer_instance
    have h0 : ((ls.left ≫ mus.left) ⁻¹' {a}).Finite :=
      (locallyQuasiFinite_iff_finite_preimage_singleton.1 hq) a
    refine (h0.image ls.left).subset ?_
    intro x hx
    obtain ⟨y, rfl⟩ := hsl.surj x
    refine ⟨y, ?_, rfl⟩
    simpa using hx
  exact ⟨hfl, hsl, IsFinite.of_isProper_of_locallyQuasiFinite mus.left, hsm⟩

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem isFinite_mu_fibre (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (g : ℕ)
    (hgA : SmoothOfRelativeDimension g A.hom) (hgB : SmoothOfRelativeDimension g B.hom) (l : A ⟶ B) [IsMonHom l]
    (mu : B ⟶ A) [IsMonHom mu] (m : ℕ) (hm : 1 ≤ m) (h₁ : l ≫ mu = 𝟙 A ^ m) (h₂ : mu ≫ l = 𝟙 B ^ m)
    (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (ha : Out.RelAmple ((Over.pullback s).obj A) L) : IsFinite ((Over.pullback s).map mu).left := by
  have e₁ : (Over.pullback s).map l ≫ (Over.pullback s).map mu = 𝟙 ((Over.pullback s).obj A) ^ m := by
    rw [← Functor.map_comp, h₁, pb_map_id_pow]
  have e₂ : (Over.pullback s).map mu ≫ (Over.pullback s).map l = 𝟙 ((Over.pullback s).obj B) ^ m := by
    rw [← Functor.map_comp, h₂, pb_map_id_pow]
  exact (fin_surj_core (isAbelianScheme_pb s A hA) (isAbelianScheme_pb s B hB) _ _ m hm e₁ e₂ hL ha).2.2.1

end PositivityTheory.PrwZar.Z2
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem isFinite_mu_fibre (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (g : ℕ)
    (hgA : SmoothOfRelativeDimension g A.hom) (hgB : SmoothOfRelativeDimension g B.hom) (l : A ⟶ B) [IsMonHom l]
    (mu : B ⟶ A) [IsMonHom mu] (m : ℕ) (hm : 1 ≤ m) (h₁ : l ≫ mu = 𝟙 A ^ m) (h₂ : mu ≫ l = 𝟙 B ^ m)
    (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (ha : Out.RelAmple ((Over.pullback s).obj A) L) : IsFinite ((Over.pullback s).map mu).left :=
  Z2.isFinite_mu_fibre hA hB g hgA hgB l mu m hm h₁ h₂ s L hL ha

end PositivityTheory.PrwZar
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.RelAmpleOfTwoSmul
section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.RelAmpleOfTwoSmulAlt
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar.Z2

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem relAmple_of_two_smul {G : Over (Sp Ω)} [GrpObj G] (hG : IsAbelianScheme G) {M N : LB G.left}
    (hM : M.IsLB) (hN : N.IsLB) (d : ℕ) (hd : 1 ≤ d) (e : d • cls M hM = d • cls N hN) (h : Out.RelAmple G N) :
    Out.RelAmple G M := by
  haveI : IsProper G.hom := hG.proper
  have hK := GlobalTheory.isLB_lbPow hN d
  have hcls : d • cls M hM = cls (lbPow N d) hK := by
    rw [cls_lbPow hN d hK, e]
  refine GlobalTheory.PosDefAmple.relAmple_of_nsmul hM hK hd hcls ?_
  refine GlobalTheory.relAmple_of_isAmpleLB G hK fun U hU => ?_
  have hNU := GlobalTheory.isAmpleLB_of_relAmple G hN h U hU
  have hpk : ∀ k : ℕ, ((lbPow N k).pull (G.hom ⁻¹ᵁ U).ι).IsLB :=
    fun k => pull_isLB (GlobalTheory.isLB_lbPow hN k) _
  have hN1 : (N.pull (G.hom ⁻¹ᵁ U).ι).IsLB := pull_isLB hN _
  have hc : ∀ k : ℕ, cls _ (hpk k) = k • cls _ hN1 := fun k => by
    rw [cls_pull (GlobalTheory.isLB_lbPow hN k), cls_lbPow hN k, map_nsmul, cls_pull hN]
  have key : ∀ k : ℕ, 1 ≤ k → GlobalTheory.IsAmpleLB ((lbPow N k).pull (G.hom ⁻¹ᵁ U).ι) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      exact GlobalTheory.IsAmpleLB.of_lbIso hNU (hpk 1) ((cls_eq_iff (hpk 1) hN1).1 (by rw [hc, one_smul]))
    | succ k hk ih =>
      refine GlobalTheory.IsAmpleLB.tensor ih hNU (hpk (k + 1)) ?_
      have h1 := LB.isLB_div (hpk (k + 1)) (hpk k)
      have h2 := LB.isLB_div h1 hN1
      refine (cls_eq_zero_iff h2).1 ?_
      rw [cls_div h1 hN1, cls_div (hpk (k + 1)) (hpk k), hc, hc, succ_nsmul]
      abel
  exact key d hd

end PositivityTheory.PrwZar.Z2
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem relAmple_of_two_smul {G : Over (Sp Ω)} [GrpObj G] (hG : IsAbelianScheme G) {M N : LB G.left}
    (hM : M.IsLB) (hN : N.IsLB) (d : ℕ) (hd : 1 ≤ d) (e : d • cls M hM = d • cls N hN) (h : Out.RelAmple G N) :
    Out.RelAmple G M :=
  Z2.relAmple_of_two_smul hG hM hN d hd e h

end PositivityTheory.PrwZar
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.RelAmpleOfLbPow
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem relAmple_of_lbPow {G : Over (Sp Ω)} [GrpObj G] (hG : IsAbelianScheme G) {M : LB G.left} (hM : M.IsLB)
    (n : ℕ) (hn : 1 ≤ n) (h : Out.RelAmple G (lbPow M n)) : Out.RelAmple G M := by
  haveI : IsProper G.hom := hG.proper
  have hP : (lbPow M n).IsLB := GlobalTheory.isLB_lbPow hM n
  exact GlobalTheory.PosDefAmple.relAmple_of_nsmul hM hP hn (cls_lbPow hM n hP).symm h

end PositivityTheory.PrwZar
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

private theorem eMap_comp_eMap'_eq_id_pow [IsCommMonObj A] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    (m : ℕ) : eMap mu α m ≫ eMap' mu α m = 𝟙 (G4 (A ⊗ B)) ^ (2 * m) := by
  apply fourfold_product_ext
  intro i
  rw [Category.assoc, eMap', g4lift_prj]
  ext1
  · rw [Category.assoc, lift_fst, Category.assoc, pow_comp', Category.id_comp, MonObj.comp_mul, comp_pow',
      comp_prod_zpow]
    simp only [← Category.assoc, eMap, g4lift_prj, lift_fst, lift_snd]
    simp only [pow_comp']
    have key : ∀ j : Fin 4, (((prj (A ⊗ B) j ≫ snd A B) ≫ mu) ^ (2 * m)) ^ α i j =
        (((prj (A ⊗ B) j ≫ snd A B) ≫ mu) ^ α i j) ^ (2 * m) := by
      intro j
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    simp only [key, Finset.prod_pow, mul_pow, inv_pow, inv_mul_cancel_right]
  · rw [Category.assoc, lift_snd, Category.assoc, pow_comp', Category.id_comp, ← Category.assoc, eMap,
      g4lift_prj, lift_snd]

theorem relAmple_zb (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    (ha : Out.RelAmple ((Over.pullback s).obj A) L) (g : ℕ) (hgA : SmoothOfRelativeDimension g A.hom)
    (hgB : SmoothOfRelativeDimension g B.hom)
    (m : ℕ) (hm : 1 ≤ m) (h₁ : l ≫ mu = 𝟙 A ^ m) (h₂ : mu ≫ l = 𝟙 B ^ m)
    (hα : α.transpose * α = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hα' : α * α.transpose = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    Out.RelAmple ((Over.pullback s).obj (G4 (A ⊗ B))) (zb mu α s P L) := by
  haveI : IsCommMonObj A := hA.comm
  haveI : IsCommMonObj B := hB.comm
  have hP : P.IsLB := hD.isLB
  have hAB : IsAbelianScheme (A ⊗ B) := AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have h4 : IsAbelianScheme (G4 (A ⊗ B)) :=
    AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB
      (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB hAB))
  have hG : IsAbelianScheme ((Over.pullback s).obj (G4 (A ⊗ B))) := Z2.isAbelianScheme_pb s _ h4
  have hfin := isFinite_mu_fibre hA hB g hgA hgB l mu m hm h₁ h₂ s L hL ha
  have hlp := relAmple_lPart hA hB mu s L hL ha hfin
  have hlpLB : (lPart mu s L).IsLB := LB.isLB_linComb hL _ _
  have hzb : (zb mu α s P L).IsLB := isLB_zb mu α s hP hL
  have c1 : (Over.pullback s).map (eMap' mu α m) ≫ (Over.pullback s).map (eMap mu α m) =
      𝟙 _ ^ (2 * m) := by
    rw [← Functor.map_comp, eMap'_comp_eMap, Z2.pb_map_id_pow]
  have c2 : (Over.pullback s).map (eMap mu α m) ≫ (Over.pullback s).map (eMap' mu α m) =
      𝟙 _ ^ (2 * m) := by
    rw [← Functor.map_comp, eMap_comp_eMap'_eq_id_pow, Z2.pb_map_id_pow]
  have hE1 : ((zb mu α s P L).pull (Over.Hom.left ((Over.pullback s).map (eMap mu α m)))).IsLB :=
    LB.isLB_pull hzb _
  have hE := two_cls_eMap hA hB hD hD' l mu α s L hL e m hm h₁ h₂ hα hα' hE1 hlpLB
  have hEa := relAmple_of_two_smul hG hE1 hlpLB 2 (by norm_num) hE hlp
  obtain ⟨hE'fin, -, -, -⟩ := Z2.fin_surj_core hG hG ((Over.pullback s).map (eMap' mu α m))
    ((Over.pullback s).map (eMap mu α m)) (2 * m) (by omega) c1 c2 hlpLB hlp
  haveI := hE'fin
  haveI : IsProper ((Over.pullback s).obj (G4 (A ⊗ B))).hom := hG.proper
  have h2 := GlobalTheory.PosDefAmple.relAmple_pull_of_isAffineHom ((Over.pullback s).map (eMap' mu α m)) hE1 hEa
  have hNLB := LB.isLB_pull hE1 (Over.Hom.left ((Over.pullback s).map (eMap' mu α m)))
  have hP2 : ((zb mu α s P L).pull (Over.Hom.left (𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))) ^ (2 * m)))).IsLB :=
    LB.isLB_pull hzb _
  have hpow := Z2.two_cls_pow hA hB hD hD' l mu α s L hL e (2 * m) hP2
  have hN : cls _ hNLB = cls _ hP2 := by
    rw [cls_pull hE1, cls_pull hzb, cls_pull hzb, ← pull_comp, ← Over.comp_left, c1]
  have hM : (lbPow (zb mu α s P L) ((2 * m) ^ 2)).IsLB := GlobalTheory.isLB_lbPow hzb _
  have key : 2 • cls _ hM = 2 • cls _ hNLB := by
    rw [hN, hpow, cls_lbPow hzb, smul_smul]
  have h3 := relAmple_of_two_smul hG hM hNLB 2 (by norm_num) key h2
  exact relAmple_of_lbPow hG hzb ((2 * m) ^ 2) (Nat.one_le_pow _ _ (by omega)) h3

end PositivityTheory.PrwZar
