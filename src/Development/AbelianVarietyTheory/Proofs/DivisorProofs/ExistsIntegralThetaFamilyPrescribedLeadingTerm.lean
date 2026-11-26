module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEvenCubicalValuesNotMemMaximalIdealPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTranslatedMembersLeadingTimesIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicIntegralReadingOfTrivialisations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicIntegralReadingOfTrivialisations
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ThFamRead

section
variable {R : Type} [CommRing R] [IsDomain R]

theorem gm_eq_unitAt {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z)
    (W : (Spec (CommRingCat.of (FractionRing R))).Opens) (hW : W = ⊤)
    (a : Γ(Spec (CommRingCat.of (FractionRing R)), W)ˣ) :
    gm r z W a = GlobalTheory.ThFam.unitAt r z (Units.map (DVR.GC.evalTop W hW).toMonoidHom a) := by
  subst hW
  apply Units.ext
  rw [gm_val r z ⊤ trivial]
  have e : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) ≤ ⊤)).op = 𝟙 _ :=
    Subsingleton.elim _ _
  simp only [GlobalTheory.ThFam.unitAt, DVR.GC.evalTop, Units.coe_map, RingHom.comp_apply, e,
    CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, Iso.hom_inv_id_apply]
  rfl

theorem gm_jK_eq_unitAt {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z)
    (W : (Spec (CommRingCat.of R)).Opens) (hW : W = ⊤) (b : Γ(Spec (CommRingCat.of R), W)ˣ) :
    gm (r ≫ jK R) z W b = GlobalTheory.ThFam.unitAt r z
      (Units.map (algebraMap R (FractionRing R)).toMonoidHom (Units.map (DVR.GC.evalTop W hW).toMonoidHom b)) := by
  have hW' : jK R ⁻¹ᵁ W = ⊤ := by subst hW; rfl
  rw [← gm_pull r (jK R) z W (by rw [hW]; trivial) b, gm_eq_unitAt r z _ hW']
  congr 1
  apply Units.ext
  exact DVR.GC.evalTop_specMap (algebraMap R (FractionRing R)) W hW hW' b.val

theorem commGroup_mul_eq_mul_mul_div {G : Type} [CommGroup G] (T A B : G) : T * A = A * B⁻¹ * (T * B) := by
  rw [_root_.mul_comm T B, ← _root_.mul_assoc, inv_mul_cancel_right, _root_.mul_comm]

variable [IsLocalRing R] (D : DegPre R)

def ch (χ : D.X) : PUnit → D.P.L.ι :=
  (DVR.exists_chart_top D.P.L D.P.isLB (fun _ : PUnit => GlobalTheory.ThFam.ptR D χ) (fun _ => (-1 : ℤ))).choose

theorem ch_top (χ : D.X) : LB.wchart D.P.L (fun _ : PUnit => GlobalTheory.ThFam.ptR D χ) (ch D χ) = ⊤ :=
  (DVR.exists_chart_top D.P.L D.P.isLB (fun _ : PUnit => GlobalTheory.ThFam.ptR D χ) (fun _ => (-1 : ℤ))).choose_spec

def gen (χ : D.X) : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => GlobalTheory.ThFam.ptR D χ) (fun _ => -1)) :=
  (DVR.exists_gen_of_local D.P.L D.P.isLB (fun _ : PUnit => GlobalTheory.ThFam.ptR D χ) (fun _ => (-1 : ℤ))).choose

theorem gen_isGen (χ : D.X) : (gen D χ).IsGen :=
  (DVR.exists_gen_of_local D.P.L D.P.isLB (fun _ : PUnit => GlobalTheory.ThFam.ptR D χ) (fun _ => (-1 : ℤ))).choose_spec

theorem xK_eq (χ : D.X) : D.xK χ = jK R ≫ GlobalTheory.ThFam.ptR D χ := by
  simp [ptK, GlobalTheory.ThFam.ptR]

theorem chK_top (χ : D.X) : LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (ch D χ) = ⊤ := by
  refine eq_top_iff.2 fun y _ => Set.mem_iInter.2 fun k => ?_
  have h1 := (ch_top D χ).ge (show jK R y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
  have h2 := Set.mem_iInter.1 h1 k
  rw [← DegPre.xK, xK_eq]
  exact h2

def kap (χ : D.X) : (FractionRing R)ˣ :=
  Units.map (DVR.GC.evalTop _ (chK_top D χ)).toMonoidHom ((D.psi χ).s (ch D χ)) *
    (Units.map (algebraMap R (FractionRing R)).toMonoidHom
      (Units.map (DVR.GC.evalTop _ (ch_top D χ)).toMonoidHom ((gen D χ).s (ch D χ))))⁻¹

theorem reads' (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z)
    (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J) :
    val (D.psi χ) r z J = GlobalTheory.ThFam.unitAt r z (kap D χ) * val (gen D χ) (r ≫ jK R) z J := by
  have hx : r ≫ D.xK χ = (r ≫ jK R) ≫ GlobalTheory.ThFam.ptR D χ := by rw [xK_eq, Category.assoc]
  have m1 := hJ.mem (K := PUnit) (fun _ => D.xK χ) r
  have m0 : r z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (ch D χ) := by rw [chK_top]; trivial
  have t1 := gen_trans (D.psi_gen χ) r z m1 m0
  have m1' := hJ.mem (K := PUnit) (fun _ => GlobalTheory.ThFam.ptR D χ) (r ≫ jK R)
  have m0' : (r ≫ jK R) z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => GlobalTheory.ThFam.ptR D χ) (ch D χ) := by
    rw [ch_top]; trivial
  have t2 := gen_trans (gen_isGen D χ) (r ≫ jK R) z m1' m0'
  have htr : trF (L := D.P.L) (K := PUnit) (fun _ => D.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ D.xK χ)) (ch D χ) =
      trF (L := D.P.L) (K := PUnit) (fun _ => GlobalTheory.ThFam.ptR D χ) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ GlobalTheory.ThFam.ptR D χ)) (ch D χ) := by
    simp only [trF]
    rw [hx]
  show gm r z _ _ = _ * gm (r ≫ jK R) z _ _
  rw [t1, t2, htr]
  erw [gm_eq_unitAt r z _ (chK_top D χ), gm_jK_eq_unitAt r z _ (ch_top D χ)]
  rw [kap, map_mul, map_inv]
  exact commGroup_mul_eq_mul_mul_div _ _ _

theorem reads : GlobalTheory.ThFam.Reads D (kap D) := ⟨gen D, gen_isGen D, reads' D⟩

end

end GlobalTheory.ThFamRead

namespace GlobalTheory.ThFamRead

section
variable {R : Type} [CommRing R] [IsDomain R]

theorem unitAt_inj (z : (TK R).left) :
    Function.Injective (GlobalTheory.ThFam.unitAt (R := R) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z) := fun a b h =>
  Units.ext (RingHom.injective _ (congrArg Units.val h))

theorem toGen_unit (z : (TK R).left) (u : Rˣ) :
    Units.map (GlobalTheory.BetaAdd.toGen z).toMonoidHom u = GlobalTheory.ThFam.unitAt (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z
      (Units.map (algebraMap R (FractionRing R)).toMonoidHom u) := by
  have h := gm_jK_eq_unitAt (R := R) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z ⊤ rfl
    (Units.map (DegPre.toOpen (R := R) ⊤).toMonoidHom u)
  have e1 : Units.map (DVR.GC.evalTop (⊤ : (Spec (CommRingCat.of R)).Opens) rfl).toMonoidHom
      (Units.map (DegPre.toOpen (R := R) ⊤).toMonoidHom u) = u := by
    apply Units.ext
    have e : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤)).op = 𝟙 _ := Subsingleton.elim _ _
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, DVR.GC.evalTop, GlobalTheory.BetaAdd.toOpen_top,
      RingHom.comp_apply, e, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply, Iso.inv_hom_id_apply]
  rw [e1, Category.id_comp] at h
  rw [← h]
  apply Units.ext
  show GlobalTheory.BetaAdd.toGen z u = _
  rw [GlobalTheory.BetaAdd.toGen_eq]
  exact gs_unit (jK R) z ⊤ trivial (Units.map (DegPre.toOpen (R := R) ⊤).toMonoidHom u)

theorem mem_intU {z : (TK R).left} {x : ((TK R).left.presheaf.stalk z)ˣ} (hx : x ∈ GlobalTheory.BetaAdd.intU z) :
    ∃ u : Rˣ, x = GlobalTheory.ThFam.unitAt (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z
      (Units.map (algebraMap R (FractionRing R)).toMonoidHom u) := by
  obtain ⟨u, rfl⟩ := hx
  exact ⟨u, toGen_unit z u⟩

variable [IsLocalRing R] (D : DegPre R)

theorem ptR_eq (χ : D.X) : GlobalTheory.ThFam.ptR D χ = (D.c χ).left := by
  simp [GlobalTheory.ThFam.ptR]

theorem psi_val {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
    (hI : ∀ x : Spec (CommRingCat.of R) ⟶ D.P.A.left, x ≫ D.P.A.hom = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ D.P.L.U (J (jK R ≫ x)))
    (χ : D.X) : ∃ u : Rˣ, val (D.psi χ) (𝟙 _) z J = GlobalTheory.ThFam.unitAt (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z
      (kap D χ * Units.map (algebraMap R (FractionRing R)).toMonoidHom u) := by
  have h1 := reads' D χ (TK R).left (𝟙 (TK R).left) z J hJ
  have hm := GlobalTheory.BetaAdd.val_mem (z := z) hI (gen D χ) (𝟙 _) (fun _ => by rw [Category.id_comp]; exact Over.w _)
    ((𝟙 (TK R).left) ≫ jK R) (by rw [Category.id_comp, Category.comp_id])
  obtain ⟨u, hu⟩ := mem_intU hm
  exact ⟨u, h1.trans (by rw [hu, map_mul]; rfl)⟩

theorem ne0 (u : Rˣ) : algebraMap R (FractionRing R) (u : R) ≠ 0 :=
  (u.isUnit.map (algebraMap R (FractionRing R))).ne_zero

theorem even (hE : D.PsiEven) (χ : D.X) : ∃ u : Rˣ, ((kap D (-χ) : (FractionRing R)ˣ) : FractionRing R) =
    (kap D χ : FractionRing R) * algebraMap R (FractionRing R) (u : R) := by
  obtain ⟨z⟩ : Nonempty (TK R).left := ⟨IsLocalRing.closedPoint (FractionRing R)⟩
  obtain ⟨J, hJ, hI⟩ := GlobalTheory.BetaAdd.exists_good_int D z
  have e := (val_mul hJ _ _ (𝟙 _)).symm.trans (val_corr hJ (hE χ) (𝟙 _))
  rw [val_pull hJ] at e
  obtain ⟨u1, h1⟩ := psi_val D hJ hI (-χ)
  obtain ⟨u2, h2⟩ := psi_val D hJ hI χ
  obtain ⟨u3, h3⟩ := mem_intU (GlobalTheory.BetaAdd.val_mem hI D.sym (GlobalTheory.ThFam.ptR D χ)
    (fun k => by fin_cases k <;> simp [Over.w]) (𝟙 (TK R).left ≫ D.xK χ) (by rw [Category.id_comp, xK_eq]))
  rw [h1, h2, h3, ← map_mul] at e
  have e' := congrArg Units.val (unitAt_inj z e)
  simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at e'
  refine ⟨u2 * u1⁻¹ * u3⁻¹, ?_⟩
  simp only [Units.val_mul, map_mul, map_units_inv]
  have n1 := ne0 u1
  have n3 := ne0 u3
  field_simp
  linear_combination e'

theorem tau_val {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (x y : D.X) :
    val (D.tau x y) (𝟙 _) z J = val (D.psi (x + y)) (𝟙 _) z J * (val (D.psi x) (𝟙 _) z J)⁻¹ *
      (val (D.psi y) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem cube (hB : D.TauBimult) (a a' b : D.X) : ∃ u : Rˣ,
    ((kap D (a + a' + b) * kap D a * kap D a' * kap D b : (FractionRing R)ˣ) : FractionRing R) =
      ((kap D (a + a') * kap D (a + b) * kap D (a' + b) : (FractionRing R)ˣ) : FractionRing R) *
        algebraMap R (FractionRing R) (u : R) := by
  obtain ⟨z⟩ : Nonempty (TK R).left := ⟨IsLocalRing.closedPoint (FractionRing R)⟩
  obtain ⟨J, hJ, hI⟩ := GlobalTheory.BetaAdd.exists_good_int D z
  have e := (val_mul hJ _ _ (𝟙 _)).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
  rw [tau_val D hJ, tau_val D hJ, tau_val D hJ] at e
  have hc := val_pull hJ D.cub.t (D.pt3 a a' b) (𝟙 (TK R).left)
  erw [hc] at e
  have hr : val D.rigK (𝟙 (TK R).left) z J = val D.rig (𝟙 (TK R).left ≫ (toUnit (TK R)).left) z J := val_pull hJ _ _ _
  obtain ⟨ur, hur⟩ := mem_intU (GlobalTheory.BetaAdd.val_mem (z := z) hI D.rig (𝟙 _)
    (fun _ => by rw [Category.id_comp]; exact Over.w _) (𝟙 (TK R).left ≫ (toUnit (TK R)).left)
    (by rw [Category.id_comp, Category.comp_id]; simpa using Over.w (toUnit (TK R))))
  obtain ⟨uc, huc⟩ := mem_intU (GlobalTheory.BetaAdd.val_mem (z := z) hI D.cub.t
    (lift (D.c a) (lift (D.c a') (D.c b))).left
    (fun k => (Category.assoc _ _ _).trans ((congrArg (fun f => _ ≫ f) (Over.w (psum D.P.A (x3 D.P.A) k.down))).trans (Over.w _))) (𝟙 (TK R).left ≫ D.pt3 a a' b)
    (by simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]))
  obtain ⟨u1, h1⟩ := psi_val D hJ hI (a + a' + b)
  obtain ⟨u2, h2⟩ := psi_val D hJ hI (a + a')
  obtain ⟨u3, h3⟩ := psi_val D hJ hI b
  obtain ⟨u4, h4⟩ := psi_val D hJ hI (a + b)
  obtain ⟨u5, h5⟩ := psi_val D hJ hI a
  obtain ⟨u6, h6⟩ := psi_val D hJ hI (a' + b)
  obtain ⟨u7, h7⟩ := psi_val D hJ hI a'
  rw [hr, hur, huc, h1, h2, h3, h4, h5, h6, h7] at e
  simp only [← map_inv, ← map_mul] at e
  have e' := congrArg Units.val (unitAt_inj z e)
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, map_units_inv] at e'
  clear h1 h2 h3 h4 h5 h6 h7 hr hur huc hc e hI hJ
  refine ⟨u2 * u4 * u6 * (u1 * u5 * u7 * u3 * ur * uc)⁻¹, ?_⟩
  simp only [Units.val_mul, map_mul, map_units_inv]
  have := ne0 u1; have := ne0 u2; have := ne0 u3; have := ne0 u4; have := ne0 u5; have := ne0 u6; have := ne0 u7
  have := ne0 ur; have := ne0 uc
  have := (kap D (a + a' + b)).ne_zero; have := (kap D (a + a')).ne_zero; have := (kap D b).ne_zero
  have := (kap D (a + b)).ne_zero; have := (kap D a).ne_zero; have := (kap D (a' + b)).ne_zero
  have := (kap D a').ne_zero
  field_simp at e' ⊢
  linear_combination e'

theorem psiIn_mem (I : Ideal R) (χ : D.X) (h : D.PsiIn χ I) :
    ∃ s ∈ I, ((kap D χ : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s := by
  have hle : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (ch D χ PUnit.unit) := by
    intro y _
    have h1 := Set.mem_iInter.1
      ((ch_top D χ).ge (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)) PUnit.unit
    rw [ptR_eq] at h1
    exact h1
  have hh : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (ch D χ) :=
    fun y _ => (chK_top D χ).ge trivial
  obtain ⟨r, hr, e⟩ := h (ch D χ) ⊤ (isAffineOpen_top _) hle hh
  obtain ⟨s, hs, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ GlobalTheory.BetaAdd.toOpen_bij.2).1 hr
  have key : DVR.GC.evalTop _ (chK_top D χ) ((D.psi χ).s (ch D χ)).val = algebraMap R (FractionRing R) s := by
    have e0 : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤)).op = 𝟙 _ := Subsingleton.elim _ _
    calc DVR.GC.evalTop _ (chK_top D χ) ((D.psi χ).s (ch D χ)).val
        = DVR.GC.evalTop (jK R ⁻¹ᵁ ⊤) rfl
            (((Spec (CommRingCat.of (FractionRing R))).presheaf.map (homOfLE hh).op).hom ((D.psi χ).s (ch D χ)).val) :=
          (DVR.GC.evalTop_res hh (chK_top D χ) rfl _).symm
      _ = DVR.GC.evalTop (jK R ⁻¹ᵁ ⊤) rfl (((jK R).app ⊤).hom (DegPre.toOpen ⊤ s)) := congrArg _ e.symm
      _ = algebraMap R (FractionRing R) (DVR.GC.evalTop ⊤ rfl (DegPre.toOpen ⊤ s)) :=
          DVR.GC.evalTop_specMap (algebraMap R (FractionRing R)) ⊤ rfl rfl _
      _ = algebraMap R (FractionRing R) s := by
          congr 1
          simp only [DVR.GC.evalTop, GlobalTheory.BetaAdd.toOpen_top, RingHom.comp_apply, e0, CategoryTheory.Functor.map_id,
            CommRingCat.hom_id, RingHom.id_apply, Iso.inv_hom_id_apply]
  refine ⟨s * ((Units.map (DVR.GC.evalTop _ (ch_top D χ)).toMonoidHom ((gen D χ).s (ch D χ)))⁻¹ : Rˣ),
    I.mul_mem_right _ hs, ?_⟩
  simp only [kap, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_mul, map_units_inv,
    Units.val_inv_eq_inv_val, key]
  exact congrArg (· * _) key

end

theorem exists_reading : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∃ κ : D.toPre.X → (FractionRing R)ˣ, GlobalTheory.ThFam.Reads D.toPre κ ∧ (∀ a, ∃ u : Rˣ, ((κ (-a) : (FractionRing R)ˣ) : FractionRing R) = (κ a : FractionRing R) * algebraMap R (FractionRing R) (u : R)) ∧ (∀ a a' b, ∃ u : Rˣ, ((κ (a + a' + b) * κ a * κ a' * κ b : (FractionRing R)ˣ) : FractionRing R) = ((κ (a + a') * κ (a + b) * κ (a' + b) : (FractionRing R)ˣ) : FractionRing R) * algebraMap R (FractionRing R) (u : R)) ∧ (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R (FractionRing R) s) ∧ ∀ n : ℕ, {a | ¬ ∃ s ∈ maximalIdeal R ^ n, (κ a : FractionRing R) = algebraMap R (FractionRing R) s}.Finite := by
  intro R _ _ _ _ D
  refine ⟨kap D.toPre, reads D.toPre, even D.toPre D.psi_even, cube D.toPre D.tau_bimult,
    fun a ha => psiIn_mem D.toPre _ a (D.psi_pos a ha), fun n => (D.psi_tendsto n).subset ?_⟩
  intro χ hχ h
  exact hχ (psiIn_mem D.toPre _ χ h)

end GlobalTheory.ThFamRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicIntegralReadingOfTrivialisationsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_cubic_integral_reading_of_trivialisations : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∃ κ : D.toPre.X → (FractionRing R)ˣ, GlobalTheory.ThFam.Reads D.toPre κ ∧ (∀ a, ∃ u : Rˣ, ((κ (-a) : (FractionRing R)ˣ) : FractionRing R) = (κ a : FractionRing R) * algebraMap R (FractionRing R) (u : R)) ∧ (∀ a a' b, ∃ u : Rˣ, ((κ (a + a' + b) * κ a * κ a' * κ b : (FractionRing R)ˣ) : FractionRing R) = ((κ (a + a') * κ (a + b) * κ (a' + b) : (FractionRing R)ˣ) : FractionRing R) * algebraMap R (FractionRing R) (u : R)) ∧ (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R (FractionRing R) s) ∧ ∀ n : ℕ, {a | ¬ ∃ s ∈ maximalIdeal R ^ n, (κ a : FractionRing R) = algebraMap R (FractionRing R) s}.Finite := by
  first | exact @GlobalTheory.ThFamRead.exists_reading | exact GlobalTheory.ThFamRead.exists_reading | (intros; apply GlobalTheory.ThFamRead.exists_reading <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalEvenCharacterLeadingTermsMemMaximalIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalEvenCharacterLeadingTermsMemMaximalIdeal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.LeadTerm

theorem int_bound {X : Type} [AddCommGroup X] (q : X → ℤ) (h0 : ∀ x, 0 ≤ q x) (hz : q 0 = 0)
    (hneg : ∀ a, q (-a) = q a)
    (hcub : ∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b))
    (m α : X) (j : ℕ) (hj : q α ≤ j) : q α ≤ j * q m + q (m + α) := by
  have hlin : ∀ (n : ℕ) (y : X),
      q (n • m + y) = q (n • m) + q y + n * (q (m + y) - q m - q y) := by
    intro n y
    induction n with
    | zero => simp [hz]
    | succ n ih =>
      have h := hcub (n • m) m y
      rw [succ_nsmul]
      push_cast
      linarith
  have h2 : q (m + m) = 4 * q m := by
    have h := hcub m m (-m)
    simp only [add_neg_cancel_right, add_neg_cancel, hneg, hz] at h
    linarith
  have hsq : ∀ n : ℕ, q (n • m) = (n : ℤ) ^ 2 * q m := by
    intro n
    induction n with
    | zero => simp [hz]
    | succ n ih =>
      have h := hlin n m
      rw [succ_nsmul, h, ih, h2]
      push_cast
      ring
  rcases (h0 m).lt_or_eq with hm | hm
  · have : (j : ℤ) ≤ j * q m := by nlinarith
    linarith [h0 (m + α)]
  · have hB : q α ≤ q (m + α) := by
      by_contra hlt
      push_neg at hlt
      set n : ℕ := (q α).toNat + 1 with hn
      have hnz : (n : ℤ) = q α + 1 := by
        rw [hn]; push_cast; rw [Int.toNat_of_nonneg (h0 α)]
      have h := hlin n α
      rw [hsq n, ← hm] at h
      have hpos := h0 (n • m + α)
      rw [hnz] at h
      nlinarith
    rw [← hm]
    linarith

theorem exists_mul_eq_of_addVal_le {R : Type} [CommRing R] [IsDomain R] (P : Ideal R) [P.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime P)] (x y : R)
    (h : IsDiscreteValuationRing.addVal (Localization.AtPrime P) (algebraMap R _ y) ≤
      IsDiscreteValuationRing.addVal (Localization.AtPrime P) (algebraMap R _ x)) :
    ∃ s ∉ P, ∃ a : R, s * x = a * y := by
  obtain ⟨c, hc⟩ := (IsDiscreteValuationRing.addVal_le_iff_dvd).mp h
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
  have hinj := IsLocalization.injective (Localization.AtPrime P)
    (Ideal.primeCompl_le_nonZeroDivisors P)
  refine ⟨s, s.2, a, hinj ?_⟩
  have hs := IsLocalization.mk'_spec (Localization.AtPrime P) a s
  rw [map_mul, map_mul, hc, ← hs]
  ring

theorem lead_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (κ : X → (FractionRing R)ˣ), (∀ a, κ (-a) = κ a) → (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) → (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R _ s) → ∀ α : X, ∃ k₀ : ℕ, ∀ k ≥ k₀, (∀ m, m ≠ 0 → ∃ s ∈ maximalIdeal R, ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s) ∧ ∀ n : ℕ, {m | ¬ ∃ s ∈ maximalIdeal R ^ n, ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s}.Finite := by
  intro R _ _ _ _ _ X _ _ κ hneg hcub hmax α
  set K := FractionRing R
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  have hκ0 : κ 0 = 1 := by
    have h := hcub 0 0 0
    simp only [add_zero] at h
    exact mul_right_cancel (b := κ 0 * κ 0 * κ 0)
      (by simpa only [_root_.mul_assoc, _root_.one_mul] using h)

  have hr : ∀ x, ∃ s : R, (κ x : K) = algebraMap R K s := by
    intro x
    by_cases hx : x = 0
    · exact ⟨1, by simp [hx, hκ0]⟩
    · obtain ⟨s, -, hs⟩ := hmax x hx
      exact ⟨s, hs⟩
  choose r hr using hr
  have hr0 : ∀ x, r x ≠ 0 := by
    intro x h
    have := hr x
    rw [h, map_zero] at this
    exact (κ x).ne_zero this
  have hrneg : ∀ a, r (-a) = r a := by
    intro a; apply hinjK; rw [← hr, ← hr, hneg]
  have hrz : r 0 = 1 := by
    apply hinjK; rw [← hr, hκ0]; simp
  have hrcub : ∀ a a' b, r (a + a' + b) * r a * r a' * r b = r (a + a') * r (a + b) * r (a' + b) := by
    intro a a' b
    apply hinjK
    simp only [map_mul, ← hr]
    exact_mod_cast congrArg Units.val (hcub a a' b)

  have hZ : ∀ (j : ℕ) (m : X), ((κ m ^ (j + 1) * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : Kˣ) : K) =
      algebraMap R K (r m ^ j * r (m + α)) / algebraMap R K (r α) := by
    intro j m
    have hm0 : algebraMap R K (r m) ≠ 0 := by rw [← hr]; exact (κ m).ne_zero
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hr, map_mul, map_pow]
    field_simp
    ring

  set Φ : Ideal R → ℕ → Prop := fun P j => ∀ m, ∃ s ∉ P, ∃ a : R, s * (r m ^ j * r (m + α)) = a * r α
  have hloc : ∀ P : Ideal R, ∀ hP : P.IsPrime, P.height = 1 →
      ∃ J : ℕ, (r α ∉ P → J = 0) ∧ ∀ j ≥ J, Φ P j := by
    intro P hP h1
    haveI := GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one R P h1
    set D := Localization.AtPrime P
    have hne : ∀ x, IsDiscreteValuationRing.addVal D (algebraMap R D (r x)) ≠ ⊤ := by
      intro x h
      rw [IsDiscreteValuationRing.addVal_eq_top_iff] at h
      exact hr0 x (IsLocalization.injective D (Ideal.primeCompl_le_nonZeroDivisors P)
        (by rw [h, map_zero]))
    set v : X → ℕ := fun x => (IsDiscreteValuationRing.addVal D (algebraMap R D (r x))).toNat
    have he : ∀ x, IsDiscreteValuationRing.addVal D (algebraMap R D (r x)) = (v x : ℕ∞) :=
      fun x => (ENat.coe_toNat (hne x)).symm
    have hvz : v 0 = 0 := by
      have := he 0
      rw [hrz, map_one, IsDiscreteValuationRing.addVal_one] at this
      exact_mod_cast this.symm
    have hvneg : ∀ a, v (-a) = v a := by intro a; simp only [v, hrneg]
    have hvcub : ∀ a a' b, v (a + a' + b) + v a + v a' + v b = v (a + a') + v (a + b) + v (a' + b) := by
      intro a a' b
      have := congrArg (fun t => IsDiscreteValuationRing.addVal D (algebraMap R D t)) (hrcub a a' b)
      simp only [map_mul, IsDiscreteValuationRing.addVal_mul, he] at this
      exact_mod_cast this
    refine ⟨v α, fun hα => ?_, fun j hj m => ?_⟩
    · have hu : IsUnit (algebraMap R D (r α)) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff D P (r α)).mpr hα
      have := he α
      rw [← hu.unit_spec, IsDiscreteValuationRing.addVal_eq_zero_of_unit] at this
      exact_mod_cast this.symm
    · have hb := int_bound (fun x => (v x : ℤ)) (fun x => by positivity) (by simp [hvz])
        (fun a => by simp [hvneg]) (fun a a' b => by exact_mod_cast hvcub a a' b) m α j
        (by exact_mod_cast hj)
      have hb' : v α ≤ j * v m + v (m + α) := by exact_mod_cast hb
      apply exists_mul_eq_of_addVal_le P
      rw [map_mul, map_pow, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
        he, he, he, nsmul_eq_mul]
      exact_mod_cast hb'

  have hfin := ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.finite_height_one (hr0 α)
  have hev : ∀ P ∈ {P : Ideal R | P.IsPrime ∧ P.height = 1 ∧ r α ∈ P},
      ∀ᶠ j in Filter.atTop, Φ P j := by
    rintro P ⟨hP, h1, -⟩
    obtain ⟨J, -, hJ⟩ := hloc P hP h1
    exact Filter.eventually_atTop.mpr ⟨J, hJ⟩
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp ((Filter.eventually_all_finite hfin).mpr hev)
  have hall : ∀ j ≥ J, ∀ P : Ideal R, P.IsPrime → P.height = 1 → Φ P j := by
    intro j hj P hP h1
    by_cases hα : r α ∈ P
    · exact hJ j hj P ⟨hP, h1, hα⟩
    · obtain ⟨J', hJ'0, hJ'⟩ := hloc P hP h1
      exact hJ' j (by rw [hJ'0 hα]; exact Nat.zero_le _)

  have hint : ∀ j ≥ J, ∀ m, ∃ c : R,
      algebraMap R K c = ((κ m ^ (j + 1) * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : Kˣ) : K) := by
    intro j hj m
    rw [hZ]
    have hα0 : algebraMap R K (r α) ≠ 0 := by rw [← hr]; exact (κ α).ne_zero
    obtain ⟨c, hc⟩ := ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := R) (K := K)
      (algebraMap R K (r m ^ j * r (m + α)) / algebraMap R K (r α)) (by
        intro P hP h1
        obtain ⟨s, hs, a, ha⟩ := hall j hj P hP h1 m
        refine ⟨s, hs, a, ?_⟩
        rw [mul_div_assoc', ← map_mul, ha, map_mul, mul_div_cancel_right₀ _ hα0])
    exact ⟨c, hc⟩

  have hstep : ∀ k ≥ J + 2, ∀ m, ∃ c : R,
      ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : Kˣ) : K) = algebraMap R K (r m * c) := by
    intro k hk m
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    obtain ⟨c, hc⟩ := hint (i - 1) (by omega) m
    refine ⟨c, ?_⟩
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at hc
    rw [pow_succ', _root_.mul_assoc, Units.val_mul, ← hc, map_mul, hr]
  refine ⟨J + 2, fun k hk => ⟨fun m hm => ?_, fun n => ?_⟩⟩
  · obtain ⟨c, hc⟩ := hstep k hk m
    obtain ⟨s, hs, hsκ⟩ := hmax m hm
    have : r m = s := hinjK (by rw [← hr, hsκ])
    exact ⟨r m * c, by rw [this]; exact Ideal.mul_mem_right c _ hs, hc⟩
  · refine (GlobalTheory.T.finite_even_cubical_values_not_mem_maximalIdeal_pow R X κ hneg hcub hmax n).subset ?_
    intro m hm hm'
    apply hm
    obtain ⟨s, hs, hsκ⟩ := hm'
    obtain ⟨c, hc⟩ := hstep k hk m
    have : r m = s := hinjK (by rw [← hr, hsκ])
    exact ⟨r m * c, by rw [this]; exact Ideal.mul_mem_right c _ hs, hc⟩

end GlobalTheory.LeadTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalEvenCharacterLeadingTermsMemMaximalIdealStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_even_character_leading_terms_mem_maximalIdeal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (κ : X → (FractionRing R)ˣ), (∀ a, κ (-a) = κ a) → (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) → (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R _ s) → ∀ α : X, ∃ k₀ : ℕ, ∀ k ≥ k₀, (∀ m, m ≠ 0 → ∃ s ∈ maximalIdeal R, ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s) ∧ ∀ n : ℕ, {m | ¬ ∃ s ∈ maximalIdeal R ^ n, ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s}.Finite := by
  first | exact @GlobalTheory.LeadTerm.lead_mem | exact GlobalTheory.LeadTerm.lead_mem | (intros; apply GlobalTheory.LeadTerm.lead_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicUnitMultipleFractionRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicUnitMultipleFractionRing
namespace GlobalTheory
namespace EvenCubicNorm

open Finset

theorem eq_zero_of_even_cubic {ι X G : Type*} [AddCommGroup X] [AddCommGroup G]
    (b : Module.Basis ι ℤ X) (f : X → G) (hev : ∀ a, f (-a) = f a)
    (hcub : ∀ a a' c, f (a + a' + c) + f a + f a' + f c = f (a + a') + f (a + c) + f (a' + c))
    (h1 : ∀ i, f (b i) = 0) (h2 : ∀ i j, i ≠ j → f (b i + b j) = 0) : ∀ a, f a = 0 := by
  have hext : ∀ g : X →+ G, (∀ i, g (b i) = 0) → ∀ a, g a = 0 := by
    intro g hg a
    have : g.toIntLinearMap = 0 := b.ext (fun i => by simpa using hg i)
    simpa using LinearMap.congr_fun this a
  have h0 : f 0 = 0 := by simpa using hcub 0 0 0
  let B : X → X →+ G := fun c =>
    { toFun := fun a => f (a + c) - f a - f c
      map_zero' := by simp [h0]
      map_add' := by
        intro a a'
        have h := hcub a a' c
        have e : f (a + a' + c) - f (a + a') - f c - (f (a + c) - f a - f c + (f (a' + c) - f a' - f c))
            = (f (a + a' + c) + f a + f a' + f c) - (f (a + a') + f (a + c) + f (a' + c)) := by abel
        rw [← sub_eq_zero, e, h, sub_self] }
  have hBapp : ∀ c a, B c a = f (a + c) - f a - f c := fun _ _ => rfl
  have hdiag : ∀ i, B (b i) (b i) = 0 := by
    intro i
    have h := (B (b i)).map_add (b i) (-(b i))
    rw [add_neg_cancel, map_zero, hBapp (b i) (-(b i)), neg_add_cancel, hev, h0, h1] at h
    simpa using h.symm
  have hA : ∀ j a, B (b j) a = 0 := by
    intro j
    apply hext
    intro i
    by_cases hij : i = j
    · subst hij; exact hdiag i
    · rw [hBapp, h2 i j hij, h1, h1]; simp
  have hAll : ∀ a c, B c a = 0 := by
    intro a c
    have h := hext (B a) (fun j => by rw [hBapp, add_comm (b j) a, ← hA j a, hBapp]; abel) c
    rw [hBapp] at h ⊢
    rw [add_comm c a] at h
    rw [← h]; abel
  let F : X →+ G :=
    { toFun := f
      map_zero' := h0
      map_add' := by
        intro a c
        have h := hAll a c
        rw [hBapp, sub_sub, sub_eq_zero] at h
        exact h }
  intro a
  exact hext F h1 a

section Quadratic

variable {M : Type*} [CommGroup M] {ι : Type*} [Fintype ι]

def prodPow (z : ι → ι → M) (e : ι → ι → ℤ) : M := ∏ i, ∏ j, z i j ^ e i j

theorem prodPow_add (z : ι → ι → M) (e e' : ι → ι → ℤ) :
    prodPow z e * prodPow z e' = prodPow z (fun i j => e i j + e' i j) := by
  simp only [prodPow, zpow_add, Finset.prod_mul_distrib]

theorem prodPow_single [DecidableEq ι] (z : ι → ι → M) (k l : ι) :
    prodPow z (fun i j => if i = k ∧ j = l then 1 else 0) = z k l := by
  unfold prodPow
  rw [Finset.prod_eq_single k, Finset.prod_eq_single l]
  · simp
  · intro j _ hj; simp [hj]
  · simp
  · intro i _ hi
    apply Finset.prod_eq_one
    intro j _; simp [hi]
  · simp

end Quadratic

theorem indicator_sum_mul {ι : Type*} [DecidableEq ι] (i j k l : ι) (hkl : k ≠ l) :
    (((if i = k then 1 else 0) + (if i = l then 1 else 0)) * ((if j = k then 1 else 0) + (if j = l then 1 else 0)) : ℤ) =
      (if i = k ∧ j = k then 1 else 0) + (if i = l ∧ j = l then 1 else 0) +
        (if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0) := by
  by_cases hik : i = k <;> by_cases hil : i = l <;> by_cases hjk : j = k <;> by_cases hjl : j = l <;>
    simp_all

theorem exists_even_cubic_unit_multiple (R : Type) [CommRing R] [IsDomain R] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (κ₀ : X → (FractionRing R)ˣ)
    (hev : ∀ a, ∃ u : Rˣ, ((κ₀ (-a) : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R))
    (hcub : ∀ a a' b, ∃ u : Rˣ, ((κ₀ (a + a' + b) * κ₀ a * κ₀ a' * κ₀ b : (FractionRing R)ˣ) : FractionRing R) = ((κ₀ (a + a') * κ₀ (a + b) * κ₀ (a' + b) : (FractionRing R)ˣ) : FractionRing R) * algebraMap R (FractionRing R) (u : R)) :
    ∃ κ : X → (FractionRing R)ˣ, (∀ a, κ (-a) = κ a) ∧
      (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) ∧
      ∀ a, ∃ u : Rˣ, ((κ a : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R) := by
  classical
  set K := FractionRing R
  let φ : Rˣ →* Kˣ := Units.map (algebraMap R K).toMonoidHom
  have hφ : ∀ u : Rˣ, ((φ u : Kˣ) : K) = algebraMap R K (u : R) := fun u => rfl
  let H : Subgroup Kˣ := φ.range
  let ψ : Kˣ → Additive (Kˣ ⧸ H) := fun x => Additive.ofMul (QuotientGroup.mk x)
  have ψmul : ∀ x y, ψ (x * y) = ψ x + ψ y := fun x y => rfl
  have ψφ : ∀ x u, ψ (x * φ u) = ψ x := by
    intro x u
    rw [ψmul]
    have : ψ (φ u) = 0 := by
      show Additive.ofMul (QuotientGroup.mk (φ u) : Kˣ ⧸ H) = 0
      rw [(QuotientGroup.eq_one_iff (φ u)).mpr (MonoidHom.mem_range.mpr ⟨u, rfl⟩)]; rfl
    rw [this, add_zero]
  have ψeq : ∀ x y, ψ x = ψ y → ∃ u : Rˣ, y = x * φ u := by
    intro x y h
    have h' : (QuotientGroup.mk x : Kˣ ⧸ H) = QuotientGroup.mk y := h
    obtain ⟨u, hu⟩ := QuotientGroup.eq.mp h'
    exact ⟨u, by rw [hu]; group⟩
  let b := (Module.Free.chooseBasis ℤ X).reindex (Fintype.equivFin _)
  set r := Fintype.card (Module.Free.ChooseBasisIndex ℤ X)
  let n : Fin r → X → ℤ := fun i a => b.repr a i
  let z : Fin r → Fin r → Kˣ := fun i j =>
    if i = j then κ₀ (b i) else if i < j then κ₀ (b i + b j) * (κ₀ (b i))⁻¹ * (κ₀ (b j))⁻¹ else 1
  let E : X → Fin r → Fin r → ℤ := fun a i j => n i a * n j a
  let κ : X → Kˣ := fun a => prodPow z (E a)
  have hκ : ∀ a, κ a = prodPow z (E a) := fun _ => rfl
  have κev : ∀ a, κ (-a) = κ a := by
    intro a; simp only [hκ]; congr 1; funext i j; simp [E, n]
  have κcub : ∀ a a' c, κ (a + a' + c) * κ a * κ a' * κ c = κ (a + a') * κ (a + c) * κ (a' + c) := by
    intro a a' c
    simp only [hκ, prodPow_add]
    congr 1; funext i j; simp only [E, n, map_add (f := _), Finsupp.add_apply]; ring
  have nb : ∀ i k, n i (b k) = if i = k then 1 else 0 := by
    intro i k; simp [n, Finsupp.single_apply, eq_comm]
  have κb : ∀ k, κ (b k) = κ₀ (b k) := by
    intro k
    have : E (b k) = fun i j => if i = k ∧ j = k then 1 else 0 := by
      funext i j; simp only [E, nb]; split_ifs <;> simp_all
    rw [hκ, this, prodPow_single]; simp [z]
  have κbb : ∀ k l, k < l → κ (b k + b l) = κ₀ (b k + b l) := by
    intro k l hkl
    have hne : k ≠ l := ne_of_lt hkl
    have hsplit : prodPow z (E (b k + b l)) =
        prodPow z (fun i j => if i = k ∧ j = k then 1 else 0) * prodPow z (fun i j => if i = l ∧ j = l then 1 else 0) *
        prodPow z (fun i j => if i = k ∧ j = l then 1 else 0) * prodPow z (fun i j => if i = l ∧ j = k then 1 else 0) := by
      simp only [prodPow_add]
      congr 1; funext i j; simp only [E, n, map_add (f := _), Finsupp.add_apply]
      have h1 := nb i k; have h2 := nb i l; have h3 := nb j k; have h4 := nb j l
      simp only [n] at h1 h2 h3 h4
      rw [h1, h2, h3, h4]
      exact indicator_sum_mul i j k l hne
    rw [hκ, hsplit, prodPow_single, prodPow_single, prodPow_single, prodPow_single]
    have hzk : z k k = κ₀ (b k) := by simp only [z]; exact if_pos trivial
    have hzl : z l l = κ₀ (b l) := by simp only [z]; exact if_pos trivial
    have hzkl : z k l = κ₀ (b k + b l) * (κ₀ (b k))⁻¹ * (κ₀ (b l))⁻¹ := by
      simp only [z]; rw [if_neg hne, if_pos hkl]
    have hzlk : z l k = 1 := by simp only [z]; rw [if_neg hne.symm, if_neg (not_lt_of_gt hkl)]
    rw [hzk, hzl, hzkl, hzlk, mul_one, mul_comm (κ₀ (b k) * κ₀ (b l)), mul_assoc, mul_assoc,
      ← mul_assoc (κ₀ (b k))⁻¹, ← mul_inv, inv_mul_cancel, mul_one]
  have κbb' : ∀ k l, k ≠ l → κ (b k + b l) = κ₀ (b k + b l) := by
    intro k l hkl
    rcases lt_or_gt_of_ne hkl with h | h
    · exact κbb k l h
    · rw [add_comm]; exact κbb l k h

  have κ₀ev : ∀ a, ψ (κ₀ (-a)) = ψ (κ₀ a) := by
    intro a
    obtain ⟨u, hu⟩ := hev a
    have : κ₀ (-a) = κ₀ a * φ u := Units.ext (by rw [Units.val_mul, hφ]; exact hu)
    rw [this, ψφ]
  have κ₀cub : ∀ a a' c, ψ (κ₀ (a + a' + c)) + ψ (κ₀ a) + ψ (κ₀ a') + ψ (κ₀ c) =
      ψ (κ₀ (a + a')) + ψ (κ₀ (a + c)) + ψ (κ₀ (a' + c)) := by
    intro a a' c
    obtain ⟨u, hu⟩ := hcub a a' c
    have : κ₀ (a + a' + c) * κ₀ a * κ₀ a' * κ₀ c = κ₀ (a + a') * κ₀ (a + c) * κ₀ (a' + c) * φ u :=
      Units.ext (by rw [Units.val_mul _ (φ u), hφ]; exact hu)
    have h := congrArg ψ this
    rw [ψφ] at h
    simpa only [ψmul] using h
  let f : X → Additive (Kˣ ⧸ H) := fun a => ψ (κ (a)) - ψ (κ₀ a)
  have hf : ∀ a, f a = 0 := by
    refine EvenCubicNorm.eq_zero_of_even_cubic b f ?_ ?_ ?_ ?_
    · intro a; simp only [f]; rw [κev, κ₀ev]
    · intro a a' c
      have h1 := κ₀cub a a' c
      have h2 := congrArg ψ (κcub a a' c)
      simp only [ψmul] at h2
      simp only [f]
      have e : ψ (κ (a + a' + c)) - ψ (κ₀ (a + a' + c)) + (ψ (κ a) - ψ (κ₀ a)) + (ψ (κ a') - ψ (κ₀ a')) +
            (ψ (κ c) - ψ (κ₀ c)) - (ψ (κ (a + a')) - ψ (κ₀ (a + a')) + (ψ (κ (a + c)) - ψ (κ₀ (a + c))) +
            (ψ (κ (a' + c)) - ψ (κ₀ (a' + c)))) =
          (ψ (κ (a + a' + c)) + ψ (κ a) + ψ (κ a') + ψ (κ c) - (ψ (κ (a + a')) + ψ (κ (a + c)) + ψ (κ (a' + c)))) -
          (ψ (κ₀ (a + a' + c)) + ψ (κ₀ a) + ψ (κ₀ a') + ψ (κ₀ c) -
            (ψ (κ₀ (a + a')) + ψ (κ₀ (a + c)) + ψ (κ₀ (a' + c)))) := by abel
      rw [← sub_eq_zero, e, h1, h2, sub_self, sub_self, sub_self]
    · intro i; simp only [f]; rw [κb, sub_self]
    · intro i j hij; simp only [f]; rw [κbb' i j hij, sub_self]
  refine ⟨κ, κev, κcub, fun a => ?_⟩
  have h := hf a
  simp only [f, sub_eq_zero] at h
  obtain ⟨u, hu⟩ := ψeq _ _ h.symm
  exact ⟨u, by rw [hu, Units.val_mul, hφ]⟩

end EvenCubicNorm
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicUnitMultipleFractionRingStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_cubic_unit_multiple_fractionRing : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (κ₀ : X → (FractionRing R)ˣ), (∀ a, ∃ u : Rˣ, ((κ₀ (-a) : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R)) → (∀ a a' b, ∃ u : Rˣ, ((κ₀ (a + a' + b) * κ₀ a * κ₀ a' * κ₀ b : (FractionRing R)ˣ) : FractionRing R) = ((κ₀ (a + a') * κ₀ (a + b) * κ₀ (a' + b) : (FractionRing R)ˣ) : FractionRing R) * algebraMap R (FractionRing R) (u : R)) → ∃ κ : X → (FractionRing R)ˣ, (∀ a, κ (-a) = κ a) ∧ (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) ∧ ∀ a, ∃ u : Rˣ, ((κ a : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R) := by
  first | exact @GlobalTheory.EvenCubicNorm.exists_even_cubic_unit_multiple | exact GlobalTheory.EvenCubicNorm.exists_even_cubic_unit_multiple | (intros; apply GlobalTheory.EvenCubicNorm.exists_even_cubic_unit_multiple <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaFamilyPrescribedLeadingTerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ThFam

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem gs_scal_one {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (y : Y) : gs (𝟙 Y) y ⊤ (scal p 1) = 1 := by
  have h : scal p (1 : R) = 1 := by simp [scal]
  rw [h, gs_eq _ y ⊤ trivial, map_one, map_one]

theorem secScal_generic (D : DegData R (maximalIdeal R)) (k : ℕ) (α : D.toPre.X) (b : D.toPre.SecB k α) :
    GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k)
      (GlobalTheory.FieldBaseChange.genericTerm D k α b) (D.toPre.famφB α) (DegPre.famε k) b
      (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) := by
  refine (GlobalTheory.FieldBaseChange.secScal_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_
  exact (GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).symm.trans
    ((_root_.one_mul _).symm.trans (congrArg (· * _) (gs_scal_one _ y).symm))

theorem lead_units {X : Type} [AddCommGroup X] (κ κ' : X → (FractionRing R)ˣ) (u : X → Rˣ)
    (hu : ∀ a, ((κ' a : (FractionRing R)ˣ) : FractionRing R) = (κ a : FractionRing R) * algebraMap R (FractionRing R) (u a : R))
    (k : ℕ) (α mu : X) :
    ((lead κ k α mu : (FractionRing R)ˣ) : FractionRing R) = (lead κ' k α mu : FractionRing R) *
      algebraMap R (FractionRing R) (((u mu ^ k * (u (mu + α) * (u mu)⁻¹ * (u α)⁻¹))⁻¹ : Rˣ) : R) := by
  have e : ∀ x : Rˣ, algebraMap R (FractionRing R) ((x⁻¹ : Rˣ) : R) = (algebraMap R (FractionRing R) (x : R))⁻¹ :=
    fun x => map_units_inv (algebraMap R (FractionRing R) : R →* FractionRing R) x
  have ne : ∀ x : Rˣ, algebraMap R (FractionRing R) (x : R) ≠ 0 := fun x =>
    (x.isUnit.map (algebraMap R (FractionRing R))).ne_zero
  have h₁ := ne (u mu); have h₂ := ne (u (mu + α)); have h₃ := ne (u α)
  have h₄ := (κ mu).ne_zero; have h₅ := (κ (mu + α)).ne_zero; have h₆ := (κ α).ne_zero
  simp only [lead, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hu, e, map_mul, map_pow]
  field_simp
  ring

theorem core (hR : Base R) (D : DegData R (maximalIdeal R)) (κ : D.toPre.X → (FractionRing R)ˣ)
    (hκ : Reads D.toPre κ) (κ' : D.toPre.X → (FractionRing R)ˣ)
    (hu : ∀ a, ∃ u : Rˣ, ((κ' a : (FractionRing R)ˣ) : FractionRing R) =
      (κ a : FractionRing R) * algebraMap R (FractionRing R) (u : R))
    (k : ℕ) (hk : 1 ≤ k) (α : D.toPre.X)
    (h1 : ∀ mu, mu ≠ 0 → ∃ s ∈ maximalIdeal R,
      ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s)
    (h2 : ∀ n : ℕ, {mu | ¬ ∃ s ∈ maximalIdeal R ^ n,
      ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s}.Finite)
    (b : D.toPre.SecB k α) : ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead α b := by
  classical
  choose u hu using hu
  have inj := IsFractionRing.injective R (FractionRing R)
  have h1' : ∀ mu, ∃ s : R, mu ≠ 0 → s ∈ maximalIdeal R ∧
      ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s := fun mu => by
    by_cases h : mu = 0
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨s, hs, e⟩ := h1 mu h
      exact ⟨s, fun _ => ⟨hs, e⟩⟩
  choose s hs using h1'
  let w : D.toPre.X → R := fun mu => (((u mu ^ k * (u (mu + α) * (u mu)⁻¹ * (u α)⁻¹))⁻¹ : Rˣ) : R)
  let r : D.toPre.X → R := fun mu => s mu * w mu
  have hr : ∀ mu, mu ≠ 0 → algebraMap R (FractionRing R) (r mu) =
      ((lead κ k α mu : (FractionRing R)ˣ) : FractionRing R) ∧ r mu ∈ maximalIdeal R := fun mu h =>
    ⟨by rw [lead_units κ κ' u hu k α mu, (hs mu h).2, map_mul], Ideal.mul_mem_right _ _ (hs mu h).1⟩
  have key : ∀ mu, mu ≠ 0 → ∀ e : ℕ, r mu ∉ maximalIdeal R ^ (e + 1) → ¬ ∃ s' ∈ maximalIdeal R ^ (e + 1),
      ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s' := by
    rintro mu h e hn ⟨s', hs'm, hs'e⟩
    have : s mu = s' := inj ((hs mu h).2.symm.trans hs'e)
    exact hn (Ideal.mul_mem_right _ _ (this ▸ hs'm))
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  have hcls : ∀ a c : D.toPre.X, α + k • a = α + k • c → a = c := fun a c h => by
    have h' : (k : ℤ) • a = (k : ℤ) • c := by simpa using add_left_cancel h
    exact smul_right_injective D.toPre.X (show (k : ℤ) ≠ 0 by omega) h'
  obtain ⟨F, hFα, hF0⟩ := ReciprocityTheory.ChartRestriction.G.DVR.UUA.exists_fam_rep (F := FractionRing R) hG D.tau_bimult k α hcls
    (GlobalTheory.FieldBaseChange.genericTerm D k α b)
  have hb : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α)
      (D.toPre.famφB α) (DegPre.famε k) b (DegPre.prB D.toPre (FractionRing R)).left
      (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) := by
    rw [hFα]; exact secScal_generic D k α b
  have hex : ∀ β : D.toPre.X, ∃ g : D.toPre.SecB k β, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) β)
      (DegPre.famε k) (F.s β) (D.toPre.famφB β) (DegPre.famε k) g (DegPre.prB D.toPre (FractionRing R)).left
      (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) ∧ (β ≠ α → VanMod (maximalIdeal R) g 0 ∧
        ∀ e : ℕ, ¬ VanMod (maximalIdeal R) g e → ∃ mu, α + k • mu = β ∧ ¬ ∃ s' ∈ maximalIdeal R ^ (e + 1),
          ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s') := by
    intro β
    by_cases hβ : β = α
    · subst hβ
      exact ⟨b, hb, fun h => absurd rfl h⟩
    by_cases hc : ∃ mu, α + k • mu = β
    · obtain ⟨mu, rfl⟩ := hc
      have hmu : mu ≠ 0 := by
        rintro rfl
        exact hβ (by simp)
      obtain ⟨f, hf1, hf2⟩ := GlobalTheory.T.thetaFamily_translatedMembers_leading_times_integral R hR D κ hκ k hk α b F hb mu (r mu) (hr mu hmu).1
      refine ⟨f, hf1, fun _ => ⟨hf2 0 (by simpa using (hr mu hmu).2), fun e he => ⟨mu, rfl, ?_⟩⟩⟩
      exact key mu hmu e (fun h => he (hf2 e h))
    · push_neg at hc
      refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secZero, ?_, fun _ => ⟨fun j => map_zero _, fun e he => absurd (fun j => map_zero _) he⟩⟩
      refine (GlobalTheory.FieldBaseChange.secScal_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_
      rw [ReciprocityTheory.ChartRestriction.G.DVR.UUA.sval_zero_of (fun j => rfl) _ y J (hJ.mem _ _),
        ReciprocityTheory.ChartRestriction.G.DVR.UUA.sval_zero_of (hF0 β hc) _ y J (hJ.mem _ _), mul_zero]
  choose g hg using hex
  refine ⟨⟨F, Function.update g α b, fun β => ?_, fun e => ?_⟩, Function.update_self α b g, fun β hβ => ?_⟩
  · by_cases h : β = α
    · subst h
      rw [Function.update_self]
      exact hb
    · rw [Function.update_of_ne h]
      exact (hg β).1
  · refine (((h2 (e + 1)).image (fun mu => α + k • mu)).insert α).subset fun β hβ => ?_
    by_cases h : β = α
    · exact Or.inl h
    · right
      have hβ' : ¬ VanMod (maximalIdeal R) (g β) e := by
        have := hβ
        simp only [Set.mem_setOf_eq] at this
        rwa [Function.update_of_ne h] at this
      obtain ⟨mu, hmu, hn⟩ := ((hg β).2 h).2 e hβ'
      exact ⟨mu, hn, hmu⟩
  · show VanMod (maximalIdeal R) (Function.update g α b β) 0
    rw [Function.update_of_ne hβ]
    exact ((hg β).2 hβ).1

theorem exists_intFam_lead : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)), (∀ α : D.toPre.X, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ b : D.toPre.SecB k α,
      ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead α b) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ b : D.toPre.SecB k 0, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead 0 b := by
  intro R _ _ _ hR D
  haveI := hR.1.1
  haveI := hR.1.2.2.1
  obtain ⟨κ, hκ, hev, hcub, hpos, htend⟩ := GlobalTheory.T.exists_even_cubic_integral_reading_of_trivialisations R hR D
  obtain ⟨κ', hev', hcub', hu⟩ := GlobalTheory.T.exists_even_cubic_unit_multiple_fractionRing R D.toPre.X κ hev hcub
  have hu0 := hu
  choose u hu' using hu0
  have hpos' : ∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, ((κ' a : (FractionRing R)ˣ) : FractionRing R) =
      algebraMap R (FractionRing R) s := fun a ha => by
    obtain ⟨s, hs, e⟩ := hpos a ha
    exact ⟨s * u a, Ideal.mul_mem_right _ _ hs, by rw [hu' a, e, map_mul]⟩
  have h0 : κ' 0 = 1 := by
    have := hcub' 0 0 0
    simp only [add_zero] at this
    exact mul_eq_left.1 this
  refine ⟨fun α => ?_, fun k hk b => ?_⟩
  · obtain ⟨k₁, H⟩ := GlobalTheory.T.cubical_even_character_leading_terms_mem_maximalIdeal R D.toPre.X κ' hev' hcub' hpos' α
    exact ⟨max k₁ 1, fun k hk b => core hR D κ hκ κ' hu k (le_of_max_le_right hk) α
      (H k (le_of_max_le_left hk)).1 (H k (le_of_max_le_left hk)).2 b⟩
  · have hl : ∀ mu, lead κ' k 0 mu = κ' mu ^ k := fun mu => by
      simp [lead, h0]
    refine core hR D κ hκ κ' hu k hk 0 (fun mu hmu => ?_) (fun n => ?_) b
    · obtain ⟨s, hs, e⟩ := hpos' mu hmu
      exact ⟨s ^ k, Ideal.pow_mem_of_mem _ hs k (by omega), by rw [hl, Units.val_pow_eq_pow_val, e, map_pow]⟩
    · refine (htend n).subset fun mu hmu h => hmu ?_
      obtain ⟨s, hs, e⟩ := h
      refine ⟨(s * u mu) ^ k, Ideal.pow_mem_of_mem _ (Ideal.mul_mem_right _ _ hs) k (by omega), ?_⟩
      rw [hl, Units.val_pow_eq_pow_val, hu' mu, e, ← map_mul, ← map_pow]

end GlobalTheory.ThFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaFamilyPrescribedLeadingTermStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralThetaFamily_prescribed_leadingTerm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), (∀ α : D.toPre.X, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ b : D.toPre.SecB k α, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead α b) ∧ ∀ k : ℕ, 1 ≤ k → ∀ b : D.toPre.SecB k 0, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead 0 b := by
  first | exact @GlobalTheory.ThFam.exists_intFam_lead | exact GlobalTheory.ThFam.exists_intFam_lead | (intros; apply GlobalTheory.ThFam.exists_intFam_lead <;> assumption)
end
