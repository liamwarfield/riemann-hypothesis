module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.OneTmulNeZeroOfDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPullDeg
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PsiInPull

theorem gs_injective {Y Z : Scheme.{0}} [IsReduced Y] (f : Z ⟶ Y) (z : Z)
    (hz : ∀ U : Y.Opens, U ≠ ⊥ → f z ∈ U) (U : Y.Opens) (hU : f z ∈ U) {a b : Γ(Y, U)}
    (h : gs f z U a = gs f z U b) : a = b := by
  rw [gs_eq f z U hU, gs_eq f z U hU, ← sub_eq_zero, ← map_sub, ← map_sub] at h
  by_contra hne
  have h1 : f z ∈ Y.basicOpen (a - b) := hz _ (by
    rw [Ne, basicOpen_eq_bot_iff]; exact sub_ne_zero.2 hne)
  have h2 : z ∈ Z.basicOpen ((f.app U).hom (a - b)) := by
    rw [← Scheme.preimage_basicOpen]; exact h1
  have h3 := (Z.mem_basicOpen _ z hU).1 h2
  rw [h] at h3
  exact not_isUnit_zero h3

theorem jK_mem {R : Type} [CommRing R] [IsDomain R] (z : Spec (CommRingCat.of (FractionRing R)))
    (U : (Spec (CommRingCat.of R)).Opens) (hU : U ≠ ⊥) : jK R z ∈ U := by
  obtain ⟨v, hv⟩ : ∃ v, v ∈ U := by
    by_contra hc
    exact hU (eq_bot_iff.2 fun v hv => hc ⟨v, hv⟩)
  have hs : jK R z ⤳ v := by
    refine (PrimeSpectrum.le_iff_specializes (jK R z) v).1 ?_
    intro a ha
    have ha' : algebraMap R (FractionRing R) a ∈ (PrimeSpectrum.asIdeal z) := ha
    have hb : PrimeSpectrum.asIdeal z = ⊥ := Ideal.eq_bot_of_prime _ (h := z.isPrime)
    rw [hb, Ideal.mem_bot, IsFractionRing.to_map_eq_zero_iff] at ha'
    rw [ha']; exact Ideal.zero_mem _
  exact hs.mem_open U.isOpen hv

theorem res_toOpen {R : Type} [CommRing R] {U V : (Spec (CommRingCat.of R)).Opens} (h : U ≤ V) (a : R) :
    ((Spec (CommRingCat.of R)).presheaf.map (homOfLE h).op).hom (DegPre.toOpen V a) = DegPre.toOpen U a := by
  simp only [DegPre.toOpen, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem app_toOpen {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (V : (Spec (CommRingCat.of R)).Opens) (a : R) :
    ((specOf φ).app V).hom (DegPre.toOpen V a) = DegPre.toOpen (specOf φ ⁻¹ᵁ V) (φ a) := by
  have nat := congrArg (fun g => g.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  have e := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    ((specOf φ).naturality (homOfLE (le_top : V ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  simp only [DegPre.toOpen, RingHom.comp_apply]
  rw [e, nat]
  rfl

theorem exists_of_locally {R : Type} [CommRing R] [IsDomain R] (J : Ideal R)
    (z : Spec (CommRingCat.of (FractionRing R))) (t : (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk z)
    (V : (Spec (CommRingCat.of R)).Opens) (hV : IsAffineOpen V) (hz : jK R z ∈ V)
    (H : ∀ v ∈ V, ∃ U : (Spec (CommRingCat.of R)).Opens, U ≤ V ∧ v ∈ U ∧
      ∃ s ∈ J.map (DegPre.toOpen U), gs (jK R) z U s = t) :
    ∃ r ∈ J.map (DegPre.toOpen V), gs (jK R) z V r = t := by
  let θ : Γ(Spec (CommRingCat.of R), V) →+* (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk z :=
    ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ (jK R ⁻¹ᵁ V) z hz).hom.comp ((jK R).app V).hom
  have hθ : ∀ a, gs (jK R) z V a = θ a := fun a => gs_eq _ _ _ hz a
  let Q : Ideal Γ(Spec (CommRingCat.of R), V) :=
    { carrier := {a | ∃ b ∈ J.map (DegPre.toOpen V), θ b = θ a * t}
      zero_mem' := ⟨0, Ideal.zero_mem _, by simp⟩
      add_mem' := by
        rintro a a' ⟨b, hb, e⟩ ⟨b', hb', e'⟩
        exact ⟨b + b', Ideal.add_mem _ hb hb', by rw [map_add (f := _), map_add (f := _), e, e', add_mul]⟩
      smul_mem' := by
        rintro c a ⟨b, hb, e⟩
        exact ⟨c * b, Ideal.mul_mem_left _ _ hb, by rw [smul_eq_mul, map_mul, map_mul, e, _root_.mul_assoc]⟩ }
  have key : ∀ v ∈ V, ∃ f ∈ Q, v ∈ (Spec (CommRingCat.of R)).basicOpen f := by
    intro v hv
    obtain ⟨U, hUV, hvU, s, hs, e⟩ := H v hv
    obtain ⟨f, hfU, hvf⟩ := hV.exists_basicOpen_le (V := U) ⟨v, hvU⟩ hv
    have hzf : jK R z ∈ (Spec (CommRingCat.of R)).basicOpen f :=
      jK_mem z _ (fun h0 => by rw [h0] at hvf; exact hvf)
    have := hV.isLocalization_basicOpen f
    have hs' : ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hfU).op).hom s ∈
        (J.map (DegPre.toOpen V)).map
          (algebraMap Γ(Spec (CommRingCat.of R), V) Γ(Spec (CommRingCat.of R), (Spec (CommRingCat.of R)).basicOpen f)) := by
      have h1 := Ideal.mem_map_of_mem ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hfU).op).hom hs
      rw [Ideal.map_map] at h1 ⊢
      convert h1 using 2
      ext a
      exact (res_toOpen ((Spec (CommRingCat.of R)).basicOpen_le f) a).trans (res_toOpen hfU a).symm
    obtain ⟨⟨⟨b, hb⟩, ⟨_, n, rfl⟩⟩, e2⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) _).1 hs'
    have e3 := congrArg (gs (jK R) z ((Spec (CommRingCat.of R)).basicOpen f)) e2
    rw [gs_mul _ _ _ hzf, gs_res _ _ hfU hzf, e] at e3
    have e4 : ∀ a, gs (jK R) z ((Spec (CommRingCat.of R)).basicOpen f)
        (algebraMap Γ(Spec (CommRingCat.of R), V) _ a) = θ a := fun a =>
      (gs_res _ _ ((Spec (CommRingCat.of R)).basicOpen_le f) hzf a).trans (hθ a)
    rw [e4, e4] at e3
    refine ⟨f ^ n * f, Ideal.mul_mem_right _ _ ⟨b, hb, e3.symm.trans (_root_.mul_comm _ _)⟩, ?_⟩
    rw [← pow_succ, Scheme.basicOpen_pow _ _ (Nat.succ_pos n)]
    exact hvf
  have hQ : Ideal.span (Q : Set Γ(Spec (CommRingCat.of R), V)) = ⊤ := by
    refine (hV.self_le_iSup_basicOpen_iff).1 fun v hv => ?_
    obtain ⟨f, hf, hvf⟩ := key v hv
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hvf⟩
  rw [Ideal.span_eq] at hQ
  obtain ⟨b, hb, e⟩ : (1 : Γ(Spec (CommRingCat.of R), V)) ∈ Q := hQ ▸ Submodule.mem_top
  exact ⟨b, hb, by rw [hθ, e, map_one, _root_.one_mul]⟩

theorem mem_wchart {Y B : Scheme.{0}} (M : LB B) (φ : Y ⟶ B) (y : Y) (j : M.ι) (h : φ y ∈ M.U j) :
    y ∈ LB.wchart M (fun _ : PUnit => φ) (fun _ => j) := Set.mem_iInter.2 fun _ => h

theorem psiOn_val {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}
    (ψ : PsiOn D W) (χ : D.X) (p : D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens)
    (hVp : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U p)
    (h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (fun _ => p))
    (r : Γ(Spec (CommRingCat.of R), V))
    (hr : ((jK R).app V).hom r = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s (fun _ => p)).val)
    {Z : Scheme.{0}} (g : Z ⟶ W.toScheme) (z : Z) (hz : W.ι (g z) ∈ V) :
    (gm g z (LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c χ).left) (fun _ => p))
      ((ψ.psi χ).s (fun _ => p))).val = gs (g ≫ W.ι) z V r := by
  have hc : (toUnit (TW W) ≫ D.c χ).left = W.ι ≫ (D.c χ).left := rfl
  have hle : W.ι ⁻¹ᵁ V ≤ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c χ).left) (fun _ => p) :=
    fun y hy => mem_wchart _ _ _ _ (hVp hy)
  obtain ⟨z₀⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have hW : jK R z₀ ∈ W := jK_mem z₀ W (fun h0 => by
    have : (g z).1 ∈ W := (g z).2
    exact (h0.le this : (g z).1 ∈ (⊥ : (Spec (CommRingCat.of R)).Opens)))
  have hV : jK R z₀ ∈ V := jK_mem z₀ V (fun h0 => by rw [h0] at hz; exact hz)
  let z₁ : (jK R ⁻¹ᵁ W).toScheme := ⟨z₀, hW⟩
  have hι : (jK R ∣_ W) ≫ W.ι = (jK R ⁻¹ᵁ W).ι ≫ jK R := morphismRestrict_ι _ _
  have hpt : W.ι ((jK R ∣_ W) z₁) = jK R z₀ := congrArg (fun q => q z₁) hι
  have hm : (jK R ∣_ W) z₁ ∈ W.ι ⁻¹ᵁ V := by
    show W.ι ((jK R ∣_ W) z₁) ∈ V
    rw [hpt]; exact hV
  have hdense : ∀ U : W.toScheme.Opens, U ≠ ⊥ → (jK R ∣_ W) z₁ ∈ U := by
    intro U hU
    have h1 : jK R z₀ ∈ W.ι ''ᵁ U := jK_mem z₀ _ (fun h0 => hU (by
      rw [← W.ι.preimage_image_eq U, h0]; rfl))
    rw [← hpt] at h1
    rw [← W.ι.preimage_image_eq U]; exact h1
  have n₂ : (jK R ⁻¹ᵁ W).ι z₁ ∈ jK R ⁻¹ᵁ V := hV
  have e₃ := (gm_pullGen D.P.L _ _ (ψ.psi χ) (jK R ∣_ W) (𝟙 _) z₁ (fun _ => p) (mem_wchart _ _ _ _ (hVp hm))).symm.trans
    ((gm_corr D.P.L (ψ.psi_eq χ) (𝟙 _) z₁ p (mem_wchart _ _ _ _ (hVp hm)) (mem_wchart _ _ _ _ (hVp hV))).trans
      (gm_pullGen D.P.L _ _ (D.psi χ) (jK R ⁻¹ᵁ W).ι (𝟙 _) z₁ (fun _ => p) (mem_wchart _ _ _ _ (hVp hV))))
  rw [Category.id_comp, Category.id_comp] at e₃
  have e : (W.toScheme.presheaf.map (homOfLE hle).op).hom ((ψ.psi χ).s (fun _ => p)).val = (W.ι.app V).hom r := by
    refine gs_injective (jK R ∣_ W) z₁ hdense (W.ι ⁻¹ᵁ V) hm ?_
    refine ((gs_res _ _ hle hm _).trans ((gs_unit _ _ _ (hle hm) _).trans (congrArg Units.val e₃))).trans ?_
    refine Eq.trans ?_ (gs_pull (jK R ∣_ W) W.ι z₁ V hm r).symm
    rw [hι]
    refine Eq.trans ?_ (gs_pull (jK R ⁻¹ᵁ W).ι (jK R) z₁ V n₂ r)
    rw [hr]
    exact ((gs_res _ _ h n₂ _).trans (gs_unit _ _ _ (h n₂) _)).symm
  exact (gs_unit g z _ (hle hz) _).symm.trans ((gs_res g z hle hz _).symm.trans
    ((congrArg (gs g z (W.ι ⁻¹ᵁ V)) e).trans (gs_pull g W.ι z V hz r)))

end PsiInPull


open PsiInPull in
theorem psiIn_of_isPullDeg (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R')
    (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (x : D'.X) (J : Ideal R) (J' : Ideal R')
    (hJ : J.map φ ≤ J') (H : D.PsiIn (hD.xe x) J) : D'.PsiIn x J' := by
  intro j' V' hV' hle' h'
  obtain ⟨q, rfl⟩ : ∃ q, j' = fun _ => q := ⟨j' PUnit.unit, rfl⟩
  have hss : Subsingleton (Spec (CommRingCat.of (FractionRing R'))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R')))
  by_cases hne : ∃ z, jK R' z ∈ V'
  swap
  · exact ⟨0, Ideal.zero_mem _, fn_ext fun z hz => (hne ⟨z, hz⟩).elim⟩
  obtain ⟨z, hz⟩ := hne
  obtain ⟨b, hb, hcorr⟩ := hD.psi_pr x
  set Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) with hΦ
  have hcp : (D'.c x).left ≫ Φ = specOf φ ≫ (D.c (hD.xe x)).left := hD.c_pr x
  have hxK : D'.xK x = jK R' ≫ (D'.c x).left := rfl
  have cW : hD.g ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left = D'.xK x ≫ Φ := by
    rw [hxK, Category.assoc, hcp, ← Category.assoc (jK R'), ← hD.g_comm, Category.assoc]; rfl
  obtain ⟨r', hr', e'⟩ := exists_of_locally J' z
    (gm (𝟙 _) z (LB.wchart D'.P.L (fun _ : PUnit => D'.xK x) (fun _ => q)) ((D'.psi x).s (fun _ => q))).val
    V' hV' hz (by
    intro v hv
    obtain ⟨p, hp⟩ := exists_chart D.P.isLB ((D.c (hD.xe x)).left (specOf φ v))
    obtain ⟨_, ⟨V, hV, rfl⟩, hvV, hVp⟩ := (Spec (CommRingCat.of R)).isBasis_affineOpens.exists_subset_of_mem_open
      (show specOf φ v ∈ ((D.c (hD.xe x)).left ⁻¹ᵁ D.P.L.U p : (Spec (CommRingCat.of R)).Opens) from hp)
      ((D.c (hD.xe x)).left ⁻¹ᵁ D.P.L.U p).isOpen
    have h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK (hD.xe x)) (fun _ => -1)).U (fun _ => p) :=
      fun y hy => mem_wchart _ _ _ _ (hVp hy)
    obtain ⟨r, hrJ, hr⟩ := H (fun _ => p) V hV hVp h
    have hzU : jK R' z ∈ V' ⊓ specOf φ ⁻¹ᵁ V := jK_mem z _ (fun h0 =>
      (h0.le (show v ∈ V' ⊓ specOf φ ⁻¹ᵁ V from ⟨hv, hvV⟩) : v ∈ (⊥ : (Spec (CommRingCat.of R')).Opens)))
    have hU : V' ⊓ specOf φ ⁻¹ᵁ V ≤ (D'.c x).left ⁻¹ᵁ ((D.P.L.pull Φ).U (fun _ => p) ⊓ D'.P.L.U q) := fun y hy =>
      ⟨mem_pull.2 ((congrArg (fun m => m y ∈ D.P.L.U p) hcp).mpr (hVp hy.2)), hle' hy.1⟩
    have m₁ : (𝟙 (TK R').left : (TK R').left ⟶ (TK R').left) z ∈
        D'.xK x ⁻¹ᵁ ((D.P.L.pull Φ).U (fun _ => p) ⊓ D'.P.L.U q) := hU hzU
    have mp : Φ (D'.xK x z) ∈ D.P.L.U p := mem_pull.1 m₁.1
    have mW : (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left (hD.g z) ∈ D.P.L.U p :=
      (congrArg (fun m => m z ∈ D.P.L.U p) cW).mpr mp
    have e₁ := congrArg (gm (𝟙 (TK R').left) z (D'.xK x ⁻¹ᵁ ((D.P.L.pull Φ).U (fun _ => p) ⊓ D'.P.L.U q)))
      (hb (fun _ => p) q)
    have e₁' := (gm_res _ z _ m₁ _).symm.trans (e₁.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ (D'.xK x) z
        ((D.P.L.pull Φ).U (fun _ => p) ⊓ D'.P.L.U q) m₁ _))) (gm_res _ z _ m₁ _))))
    have e₂ := (gm_corr D.P.L hcorr (𝟙 (TK R').left) z p (mem_wchart _ _ _ _ mp) (mem_wchart _ _ _ _ mW)).trans
      (gm_pullGen D.P.L _ _ _ hD.g (𝟙 (TK R').left) z _ (mem_wchart _ _ _ _ mW))
    have hgz : hD.W.ι (hD.g z) ∈ V := (congrArg (fun m => m z ∈ V) hD.g_comm).mpr hzU.2
    have e₃ := psiOn_val hD.psiW (hD.xe x) p V hVp h r hr hD.g z hgz
    have e₄ := e₂.symm.trans e₁'
    rw [Category.id_comp, zpow_neg_one, eq_inv_mul_iff_mul_eq] at e₄
    erw [Category.id_comp] at e₄
    refine ⟨V' ⊓ specOf φ ⁻¹ᵁ V, inf_le_left, ⟨hv, hvV⟩,
      ((Spec (CommRingCat.of R')).presheaf.map (homOfLE hU).op).hom
        (((D'.c x).left.app _).hom (hD.w.s (fun _ => p, q)).val) *
      ((Spec (CommRingCat.of R')).presheaf.map (homOfLE (inf_le_right : V' ⊓ specOf φ ⁻¹ᵁ V ≤ _)).op).hom
        (((specOf φ).app V).hom r), Ideal.mul_mem_left _ _ ?_, ?_⟩
    · have h1 := Ideal.mem_map_of_mem (((Spec (CommRingCat.of R')).presheaf.map
        (homOfLE (inf_le_right : V' ⊓ specOf φ ⁻¹ᵁ V ≤ _)).op).hom.comp ((specOf φ).app V).hom) hrJ
      rw [Ideal.map_map] at h1
      refine Ideal.map_mono (f := DegPre.toOpen (V' ⊓ specOf φ ⁻¹ᵁ V)) hJ ?_
      rw [Ideal.map_map]
      have e5 : (DegPre.toOpen (V' ⊓ specOf φ ⁻¹ᵁ V)).comp φ = (((Spec (CommRingCat.of R')).presheaf.map
          (homOfLE (inf_le_right : V' ⊓ specOf φ ⁻¹ᵁ V ≤ _)).op).hom.comp ((specOf φ).app V).hom).comp
          (DegPre.toOpen V) :=
        RingHom.ext fun a => ((congrArg _ (app_toOpen φ V a)).trans (res_toOpen inf_le_right _)).symm
      rw [e5]
      exact h1
    · refine Eq.trans ?_ (congrArg Units.val e₄)
      refine (gs_mul _ _ _ hzU _ _).trans (congrArg₂ (· * ·) ?_ ?_)
      · exact (gs_res _ _ hU hzU _).trans ((gs_pull (jK R') (D'.c x).left z _ m₁ _).trans (gs_unit (D'.xK x) z ((D.P.L.pull Φ).U (fun _ => p) ⊓ D'.P.L.U q) m₁ _))
      · refine (gs_res _ _ _ hzU _).trans ((gs_pull (jK R') (specOf φ) z V hzU.2 r).trans ?_)
        exact (congrArg (fun m => gs m z V r) hD.g_comm).symm.trans e₃.symm)
  refine ⟨r', hr', fn_ext fun y hy => ?_⟩
  obtain rfl : y = z := Subsingleton.elim (α := Spec (CommRingCat.of (FractionRing R'))) y z
  exact (gs_pull (𝟙 _) (jK R') y V' hz r').trans (e'.trans
    ((gs_res (𝟙 _) y h' hy _).trans (gs_unit _ _ _ (h' hy) _)).symm)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HeisenbergWeightSpaceIrreducible
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem heisenberg_weightSpace_irreducible : ∀ (F : Type) [Field F] [IsAlgClosed F] (A : Type) [CommGroup A] [Finite A] (E : Type) [AddCommGroup E] [Module F E] [FiniteDimensional F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E)), (Nat.card A : F) ≠ 0 → Module.finrank F E ^ 2 = Nat.card A → (∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v)) → (∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) → (∀ a, (∀ b, e a b = 1) → a = 1) → ∀ (T : Subgroup A) (lam : T →* (E ≃ₗ[F] E)), (∀ t : T, ∃ c : Fˣ, ∀ v, lam t v = (c : F) • Φ t v) → ∀ Wt : (T →* Fˣ) → Submodule F E, (∀ χ v, v ∈ Wt χ ↔ ∀ t, lam t v = (χ t : F) • v) → ∀ (χ : T →* Fˣ) (U : Submodule F E), U ≤ Wt χ → (∀ h : A, (∀ t : T, e t h = 1) → ∀ v ∈ U, Φ h v ∈ U) → U = ⊥ ∨ U = Wt χ := by
  classical
  intro F _ _ A _ _ E _ _ _ e Φ hcard hdim hmul hcomm hnd T lam hlam Wt hWt χ U hU hstab
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  haveI : Nontrivial E := ⟨⟨u, 0, hu0⟩⟩

  have hel : ∀ a b c, e (a * b) c = e a c * e b c := by
    intro a b c
    obtain ⟨k, hk⟩ := hmul a b
    have h1 := hcomm (a * b) c u
    rw [hk, hk, hcomm b c u, map_smul, hcomm a c, map_smul, smul_smul, smul_smul, smul_smul] at h1
    have h2 : Φ c (Φ a (Φ b u)) ≠ 0 := fun h => hu0 (by simpa using h)
    have h3 := smul_left_injective F h2 h1
    apply Units.ext
    have hk0 : (k : F) ≠ 0 := k.ne_zero
    apply mul_left_cancel₀ hk0
    rw [Units.val_mul]
    linear_combination -h3
  have he1 : ∀ c, e 1 c = 1 := by
    intro c
    have := hel 1 1 c
    rw [_root_.mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hinj : Function.Injective fun a b => (e a b : F) := by
    intro a a' h
    have : a * a'⁻¹ = 1 := by
      apply hnd
      intro b
      have hb : e a b = e a' b := Units.ext (congrFun h b)
      rw [hel, hb, ← hel, mul_inv_cancel, he1]
    exact mul_inv_eq_one.mp this
  have hli : LinearIndependent F fun a => (Φ a : E →ₗ[F] E) :=
    linearIndependent_of_comm_smul _ _ (fun a => (Φ a).injective) (fun a b v => hcomm a b v) hinj
  haveI := Fintype.ofFinite A
  have hspan : Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [Module.finrank_linearMap, ← sq, hdim, Nat.card_eq_fintype_card]
  refine le_antisymm hU fun v hv => ?_
  obtain ⟨f, hf⟩ : ∃ f : E →ₗ[F] E, f u = v := by
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hu0
    exact ⟨φ.smulRight v, by simp [hφ]⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp
    (hspan ▸ Submodule.mem_top : f ∈ Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)))
  have hvs : v = ∑ a, c a • Φ a u := by
    rw [← hf, ← hc]; simp
  have hu := (hWt χ u).mp (hU huU)
  have hv' := (hWt χ v).mp hv
  have hlamΦ : ∀ (t : T) a, lam t (Φ a u) = ((χ t : F) * (e t a : F)) • Φ a u := by
    intro t a
    obtain ⟨k, hk⟩ := hlam t
    rw [hk, hcomm, smul_comm, ← map_smul, ← hk, hu, map_smul, smul_smul, mul_comm]
  have hvt : ∀ t : T, v = ∑ a, (c a * (e t a : F)) • Φ a u := by
    intro t
    have h1 := hv' t
    have h0 : (χ t : F) ≠ 0 := (χ t).ne_zero
    apply smul_right_injective E h0
    simp only
    rw [← h1]
    conv_lhs => rw [hvs]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hlamΦ, smul_smul, smul_smul]
    congr 1; ring
  have hT : (Fintype.card T : F) ≠ 0 := by
    intro h
    apply hcard
    rw [← Subgroup.card_mul_index T, Nat.cast_mul, Nat.card_eq_fintype_card, h, zero_mul]
  have hsum : (Fintype.card T : F) • v = ∑ a, (c a * ∑ t : T, (e t a : F)) • Φ a u := by
    have : (Fintype.card T : F) • v = ∑ _t : T, v := by
      rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [this, Finset.sum_congr rfl fun t _ => hvt t, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.sum_smul]
  rw [← U.smul_mem_iff hT, hsum]
  refine U.sum_mem fun a _ => ?_
  by_cases ha : ∀ t : T, e t a = 1
  · exact U.smul_mem _ (hstab a ha u huU)
  · let ψ : T →* F :=
      { toFun := fun t => (e t a : F)
        map_one' := by simp [he1]
        map_mul' := fun s t => by simp [hel] }
    have hψ : ψ ≠ 1 := by
      intro h
      apply ha
      intro t
      apply Units.ext
      exact DFunLike.congr_fun h t
    have := sum_hom_units_eq_zero ψ hψ
    have h2 : ∑ t : T, (e t a : F) = 0 := this
    rw [h2, mul_zero, zero_smul]
    exact U.zero_mem

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSmoothAtOfSmoothQuotientPow
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothLimit

section Ring
open TensorProduct IsLocalRing

variable {V A S C : Type} [CommRing V] [CommRing A] [CommRing S] [CommRing C] [Algebra V A]
  [Algebra A S] [Algebra V S] [IsScalarTower V A S] [Algebra V C]

theorem flat_and_formallySmooth_tensor (M : Submonoid A) [IsLocalization M S]
    [Algebra.Smooth C (C ⊗[V] A)] :
    Module.Flat C (C ⊗[V] S) ∧ Algebra.FormallySmooth C (C ⊗[V] S) := by
  let φ : C ⊗[V] A →ₐ[C] C ⊗[V] S :=
    Algebra.TensorProduct.map (AlgHom.id C C) (IsScalarTower.toAlgHom V A S)
  letI := φ.toRingHom.toAlgebra
  haveI : IsScalarTower C (C ⊗[V] A) (C ⊗[V] S) :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  haveI := IsLocalization.tensorProduct_tensorProduct_right V C M S (by
    ext a; simp [RingHom.algebraMap_toAlgebra, φ])
  haveI : Module.Flat (C ⊗[V] A) (C ⊗[V] S) :=
    IsLocalization.flat _ (M.map (Algebra.TensorProduct.includeRight (R := V) (A := C)))
  haveI : Algebra.FormallySmooth (C ⊗[V] A) (C ⊗[V] S) :=
    .of_isLocalization (M.map (Algebra.TensorProduct.includeRight (R := V) (A := C)))
  exact ⟨.trans C (C ⊗[V] A) _, .comp C (C ⊗[V] A) _⟩

theorem isSmoothAt_of_smooth_quotient_pow [IsLocalRing V] [IsNoetherianRing V]
    [Algebra.FiniteType V A]
    (h : ∀ e : ℕ, Algebra.Smooth (V ⧸ maximalIdeal V ^ (e + 1))
      ((V ⧸ maximalIdeal V ^ (e + 1)) ⊗[V] A))
    (q : Ideal A) [q.IsPrime] (hq : q.comap (algebraMap V A) = maximalIdeal V) :
    Algebra.IsSmoothAt V q := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing V A
  haveI : Algebra.FinitePresentation V A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let S := Localization.AtPrime q
  have hle : (maximalIdeal V).map (algebraMap V S) ≤ maximalIdeal S := by
    rw [Ideal.map_le_iff_le_comap, IsScalarTower.algebraMap_eq V A S, ← Ideal.comap_comap,
      show (maximalIdeal S).comap (algebraMap A S) = q from
        Localization.AtPrime.under_maximalIdeal, hq]
  haveI : IsLocalHom (algebraMap V S) :=
    ((IsLocalRing.local_hom_tfae (algebraMap V S)).out 3 1).mp hle
  haveI : Module.Flat V S := by
    refine LocalFlat.flat_of_relationsLift S (I := maximalIdeal V)
      (hle.trans (IsLocalRing.maximalIdeal_le_jacobson _)) fun n => ?_
    rcases n with _ | e
    · intro F _ _ f x _
      exact LocalFlat.range_lTensor_le LinearMap.id _ (by simp) ⟨x, by simp⟩
    · haveI := h e
      haveI := (flat_and_formallySmooth_tensor (V := V) (S := S)
        (C := V ⧸ maximalIdeal V ^ (e + 1)) q.primeCompl).1
      refine LocalFlat.relationsLift_of_flat (C := V ⧸ maximalIdeal V ^ (e + 1))
        Ideal.Quotient.mk_surjective Ideal.mk_ker
        (TensorProduct.mk V (V ⧸ maximalIdeal V ^ (e + 1)) S 1)
        (TensorProduct.mk_surjective _ _ _ Ideal.Quotient.mk_surjective) ?_
      exact LinearMap.ker_tensorProductMk _
  haveI : Algebra.Smooth (ResidueField V) (ResidueField V ⊗[V] A) := by
    haveI := h 0
    let C := V ⧸ maximalIdeal V ^ (0 + 1)
    letI : Algebra C (ResidueField V) :=
      (Ideal.Quotient.factor (S := maximalIdeal V ^ (0 + 1)) (T := maximalIdeal V)
        (by simp)).toAlgebra
    haveI : IsScalarTower V C (ResidueField V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact .of_equiv (Algebra.TensorProduct.cancelBaseChange V C (ResidueField V) (ResidueField V) A)
  haveI := (flat_and_formallySmooth_tensor (V := V) (S := S)
        (C := ResidueField V) q.primeCompl).2
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (R := V) (S := S) (P := A)
    q.primeCompl

end Ring

theorem mem_smoothLocus {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [LocallyOfFinitePresentation f]
    (h : ∀ e, Smooth (pullback.snd f (thick V (IsLocalRing.maximalIdeal V) e)))
    (x : X) (hx : f x = IsLocalRing.closedPoint V) : x ∈ f.smoothLocus := by
  wlog hX : ∃ S, X = Spec S generalizing f X
  · obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
    have H := this (X.affineCover.f i ≫ f) (fun e => by
      haveI := h e
      rw [← pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance) y (by simpa using hx) ⟨_, rfl⟩
    rwa [← Scheme.Hom.preimage_smoothLocus_eq] at H
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  letI := φ.hom.toAlgebra
  haveI : Algebra.FinitePresentation V S :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation) (φ := φ)).mp ‹_›
  have hs (e : ℕ) : Algebra.Smooth (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1))
      (TensorProduct V (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) S) := by
    have H := isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct V (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) S)
    have e1 := H.flip.isoPullback_hom_snd
    have h1 : Smooth (H.flip.isoPullback.hom ≫ pullback.snd _ _) := by
      haveI : Smooth (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap V S)))
        (Spec.map (CommRingCat.ofHom
          (algebraMap V (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)))))) := h e
      infer_instance
    rw [e1, HasRingHomProperty.Spec_iff (P := @Smooth)] at h1
    exact RingHom.smooth_algebraMap.mp h1
  haveI : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  haveI := isSmoothAt_of_smooth_quotient_pow hs x.asIdeal (congrArg PrimeSpectrum.asIdeal hx)
  obtain ⟨g, hg, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth V x.asIdeal
  let j : Spec (CommRingCat.of (Localization.Away g)) ⟶ Spec S :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))
  haveI : IsOpenImmersion j := IsOpenImmersion.of_isLocalization g
  haveI : Smooth (j ≫ Spec.map φ) := by
    rw [← Spec.map_comp, HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hsm
  obtain ⟨y, rfl⟩ : x ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ g]
    exact hg
  have := (j ≫ Spec.map φ).smoothLocus_eq_top.ge (Set.mem_univ y)
  rwa [← Scheme.Hom.preimage_smoothLocus_eq] at this

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (B : Over (Spec (CommRingCat.of V))) [IsProper B.hom], (∀ e, Smooth (thickObj V (IsLocalRing.maximalIdeal V) e B).hom) → Smooth B.hom := by
  intro V _ _ _ _ B _ h
  haveI : LocallyOfFinitePresentation B.hom := inferInstance
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  intro x _
  by_contra hx
  have hc : IsClosed (B.hom '' (B.hom.smoothLocus : Set B.left)ᶜ) :=
    B.hom.isClosedMap _ B.hom.smoothLocus.2.isClosed_compl
  obtain ⟨y, hy, hy'⟩ := (IsLocalRing.specializes_closedPoint (R := V) (B.hom x)).mem_closed hc ⟨x, hx, rfl⟩
  exact hy (mem_smoothLocus B.hom h y hy')

end GlobalTheory.SmoothLimit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PerfectPairingOrthogonalOfCard
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerfectPairingCount

variable {F : Type} [Field F]

theorem linearIndependent_unitsChar (G : Type) [Group G] :
    LinearIndependent F (fun (f : G →* Fˣ) => (fun g => ((f g : Fˣ) : F) : G → F)) := by
  have h := linearIndependent_monoidHom G F
  have hinj : Function.Injective (fun f : G →* Fˣ => (Units.coeHom F).comp f) := by
    intro f g hfg
    ext x
    exact DFunLike.congr_fun hfg x
  exact h.comp _ hinj

theorem finite_unitsChar (G : Type) [Group G] [Finite G] : Finite (G →* Fˣ) :=
  (linearIndependent_unitsChar (F := F) G).finite

theorem card_unitsChar_le (G : Type) [Group G] [Finite G] :
    Nat.card (G →* Fˣ) ≤ Nat.card G := by
  classical
  haveI := finite_unitsChar (F := F) G
  haveI := Fintype.ofFinite (G →* Fˣ)
  haveI := Fintype.ofFinite G
  have h := (linearIndependent_unitsChar (F := F) G).fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h
  simpa [Nat.card_eq_fintype_card] using h

variable {A : Type} [CommGroup A] [Finite A]

theorem card_ker_mul_le (E : A →* (A →* Fˣ)) (hE : ∀ a, (∀ b, E a b = 1) → a = 1)
    (H K : Subgroup A) (hK : ∀ k ∈ K, ∀ h ∈ H, E k h = 1) :
    Nat.card K * Nat.card H ≤ Nat.card A := by
  haveI := finite_unitsChar (F := F) (A ⧸ H)
  let φ : K → (A ⧸ H →* Fˣ) := fun k =>
    QuotientGroup.lift H (E k) (fun h hh => hK k k.2 h hh)
  have hφ : Function.Injective φ := by
    intro k k' hkk
    have h1 : E k = E k' := by
      apply MonoidHom.ext
      intro b
      have := DFunLike.congr_fun hkk (QuotientGroup.mk b)
      exact this
    have h2 : (k : A) * (k' : A)⁻¹ = 1 := by
      apply hE
      intro b
      rw [map_mul, map_inv, h1, mul_inv_cancel]
      rfl
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  have h3 : Nat.card K ≤ Nat.card (A ⧸ H) :=
    (Nat.card_le_card_of_injective φ hφ).trans (card_unitsChar_le _)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H]
  exact Nat.mul_le_mul_right _ h3

theorem right_nondegenerate (E : A →* (A →* Fˣ)) (hE : ∀ a, (∀ b, E a b = 1) → a = 1)
    (b : A) (hb : ∀ a, E a b = 1) : b = 1 := by
  have h := card_ker_mul_le E hE E.flip.ker ⊤ (fun k _ h hh => by
    have := DFunLike.congr_fun (MonoidHom.mem_ker.mp hh) k
    simpa using this)
  rw [Subgroup.card_top] at h
  have hpos : 0 < Nat.card A := Nat.card_pos
  have h1 : Nat.card E.flip.ker ≤ 1 := by
    have : Nat.card A * Nat.card E.flip.ker ≤ Nat.card A * 1 := by simpa using h
    exact Nat.le_of_mul_le_mul_left this hpos
  have h2 : E.flip.ker = ⊥ := Subgroup.card_le_one_iff_eq_bot _ |>.mp h1
  have h3 : b ∈ E.flip.ker := by
    rw [MonoidHom.mem_ker]
    apply MonoidHom.ext
    intro a
    simpa using hb a
  rw [h2] at h3
  exact Subgroup.mem_bot.mp h3

theorem one_side (E : A →* (A →* Fˣ)) (hE : ∀ a, (∀ b, E a b = 1) → a = 1)
    (T H : Subgroup A) (hTH : ∀ t ∈ T, ∀ h ∈ H, E t h = 1)
    (hc : Nat.card T * Nat.card H = Nat.card A) :
    (∀ x, (∀ h ∈ H, E x h = 1) ↔ x ∈ T) ∧ (∀ χ : H →* Fˣ, ∃ x, ∀ h : H, E x h = χ h) := by
  let R : A →* (H →* Fˣ) :=
    { toFun := fun a => (E a).comp H.subtype
      map_one' := by apply MonoidHom.ext; intro h; simp
      map_mul' := by intro a a'; apply MonoidHom.ext; intro h; simp }
  have hR : ∀ x, x ∈ R.ker ↔ ∀ h ∈ H, E x h = 1 := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx h hh
      exact DFunLike.congr_fun hx ⟨h, hh⟩
    · intro hx
      apply MonoidHom.ext
      intro h
      exact hx h h.2
  have hle : T ≤ R.ker := fun t ht => (hR t).mpr (hTH t ht)
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hcard : Nat.card R.ker ≤ Nat.card T := by
    have := card_ker_mul_le E hE H R.ker (fun k hk => (hR k).mp hk)
    rw [← hc] at this
    exact Nat.le_of_mul_le_mul_right this hHpos
  have heq : T = R.ker := Subgroup.eq_of_le_of_card_ge hle hcard
  refine ⟨fun x => by rw [← hR, heq], ?_⟩
  haveI := finite_unitsChar (F := F) H
  have hrange : Nat.card R.range = Nat.card H := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup R.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange R).toEquiv, ← heq, ← hc,
      mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_right hTpos h1).symm
  have htop : R.range = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [Subgroup.card_top, hrange]
    exact card_unitsChar_le _
  intro χ
  have : χ ∈ R.range := by rw [htop]; trivial
  obtain ⟨x, hx⟩ := this
  exact ⟨x, fun h => DFunLike.congr_fun hx h⟩

end GlobalTheory.PerfectPairingCount

namespace GlobalTheory

theorem perfectPairing_orthogonal_of_card :
    ∀ (F : Type) [Field F] (A : Type) [CommGroup A] [Finite A] (e : A → A → Fˣ), (∀ a a' b, e (a * a') b = e a b * e a' b) → (∀ a b b', e a (b * b') = e a b * e a b') → (∀ a, (∀ b, e a b = 1) → a = 1) → ∀ T H : Subgroup A, (∀ t ∈ T, ∀ h ∈ H, e t h = 1) → Nat.card T * Nat.card H = Nat.card A → (∀ x, (∀ h ∈ H, e x h = 1) ↔ x ∈ T) ∧ (∀ x, (∀ t ∈ T, e t x = 1) ↔ x ∈ H) ∧ (∀ χ : H →* Fˣ, ∃ x, ∀ h : H, e x h = χ h) ∧ (∀ χ : T →* Fˣ, ∃ x, ∀ t : T, e t x = χ t) := by
  intro F _ A _ _ e h1 h2 h3 T H hTH hc
  let E : A →* (A →* Fˣ) :=
    MonoidHom.mk' (fun a => MonoidHom.mk' (e a) (h2 a)) (fun a a' => by
      apply MonoidHom.ext
      intro b
      exact h1 a a' b)
  have hE : ∀ a, (∀ b, E a b = 1) → a = 1 := h3
  have hE' : ∀ b, (∀ a, E.flip b a = 1) → b = 1 :=
    fun b hb => PerfectPairingCount.right_nondegenerate E hE b hb
  obtain ⟨a1, a2⟩ := PerfectPairingCount.one_side E hE T H hTH hc
  obtain ⟨b1, b2⟩ := PerfectPairingCount.one_side E.flip hE' H T
    (fun h hh t ht => hTH t ht h hh) (by rw [mul_comm, hc])
  exact ⟨a1, b1, a2, b2⟩

end GlobalTheory
end
