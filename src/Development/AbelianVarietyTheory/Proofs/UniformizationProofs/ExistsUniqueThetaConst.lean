module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalOfIsTwistPull
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RosatiAdjPow
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIntegralTensorLeftOfSmoothGrpObj
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.JKAppTopInjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BiTrivLiftOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationLiftNilpotent
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDescendThrough
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapDescends

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.NormTheta

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem rigT_isGen {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (k : ℤ) : (rigT A L ρ T k).IsGen := by
  intro i j
  refine unit_ext fun y hy => ?_
  have v : ∀ i : Fin 1 → L.ι, y ∈ LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i →
      gm (𝟙 T.left) y (LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i) ((rigT A L ρ T k).s i) =
        gm T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => i 0)) (ρ.s fun _ => i 0) ^ k := fun i hi =>
    (map_zpow _ _ _).trans (congrArg (· ^ k) (gm_rp₁ T.hom y _ _ (rigT_le A L i) hi _))
  have e := gen_trans (L := L) (φ := fun _ : PUnit.{1} => eSec A) (ε := fun _ => 1) hρ T.hom y
    (j := fun _ => i 0) (j' := fun _ => j 0) (rigT_le A L (T := T) i hy.1) (rigT_le A L (T := T) j hy.2)
  rw [trF, Fintype.prod_unique, zpow_one] at e
  refine ((gm_res (𝟙 _) y _ hy _).trans (v i hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb L (fun _ : Fin 1 => T.hom ≫ eSec A) (fun _ => k) (𝟙 _) y i j hy.1 hy.2)
    ((gm_res (𝟙 _) y _ hy _).trans (v j hy.2)))).symm)
  rw [Fin.prod_univ_one, Category.id_comp, ← mul_zpow]
  exact congrArg (· ^ k) e

theorem ptSec_fst : (ptSecT A (1 : T ⟶ A)).left ≫ (fst T A).left = 𝟙 T.left := by
  rw [← Over.comp_left, ptSecT, lift_fst]; rfl

theorem one_left : (1 : T ⟶ A).left = T.hom ≫ eSec A := rfl

theorem ptSec_snd : (ptSecT A (1 : T ⟶ A)).left ≫ (snd T A).left = T.hom ≫ eSec A := by
  rw [← Over.comp_left, ptSecT, lift_snd, one_left]

theorem ptSec_snd_pow (m : ℕ) : (ptSecT A (1 : T ⟶ A)).left ≫ (snd T A ^ m).left = T.hom ≫ eSec A := by
  rw [← Over.comp_left, MonObj.comp_pow, ptSecT, lift_snd, one_pow, one_left]

theorem exists_normalised (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : ℕ) (a b c : ℤ)
    (hc : c = a - b)
    (α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b])) (h₀ : α₀.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b]), α.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT A 1).left) (rigT A L ρ T c) := by
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ m).left]) (ε' := ![a, -b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, ptSec_snd, ptSec_snd_pow, hc]
      rw [← zpow_add, ← zpow_add, show -a + - -b + (a - b) = 0 by ring, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (ptSecT A 1).left)) (rigT A L ρ T c)) (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ _)) (rigT_isGen hρ c)) _))
  refine ⟨α, hα, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, ptSec_fst, Category.comp_id,
    val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]

theorem exists_value (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (k : ℤ)
    (t : LB.Sec (LPow A L k T)) : ∃ c : Γ(T.left, ⊤), ∀ z J, Good L z J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) t (ptSecT A 1).left z J =
        gs (𝟙 _) z ⊤ c * (val (rigT A L ρ T k) (𝟙 _) z J).val := by
  obtain ⟨s, hs⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ f => by
      refine Eq.trans ?_ (Fintype.prod_empty _).symm
      simp only [Fintype.prod_sum_type, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr, ptSec_snd, zpow_neg,
        mul_inv_cancel])
    (pullMulSec (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) t (ptSecT A 1).left
      (LB.invGen L _ _ (rigT A L ρ T k)) (DVR.invGen_isGen _ _ _ _ (rigT_isGen hρ k)))
  have le : (⊤ : T.left.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (T.left ⟶ A.left)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(T.left.presheaf.map (homOfLE le).op).hom (s.f PEmpty.elim), fun z J hJ => ?_⟩
  have e := (hs _ (𝟙 _) z J hJ).trans (sval_pullMulSec _ _ _ _ _ z hJ)
  rw [val_inv, Category.id_comp,
    sval_of s (𝟙 _) z J PEmpty.elim (fun k => k.elim)] at e
  exact (Units.inv_mul_cancel_right _ _).symm.trans
    (congrArg (· * _) ((gs_res (𝟙 _) z le trivial _).trans e).symm)

theorem sec_ext {Y : Scheme.{0}} {M : LB Y} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  congr
  exact funext h

end General

end GlobalTheory.NormTheta

namespace GlobalTheory


open NormTheta in
theorem existsUnique_thetaConst : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m : ℕ), Odd m → ∀ (th : SecA A F 1) (x : TFK (R := R) F ⟶ A.A), x ^ (m ^ 2) = 1 → (∃! q : SecA A F (m ^ 2) × F, ThC A ρ m th x q.1 q.2) := by
  intro hLL R _ _ _ A F _ _ ρ hρ m hm th x hx
  have hLaw : Laws := hLL.1
  have hL := A.isLB
  let T := TFK (R := R) F
  have : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain ⟨p⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    refine (IsUnit.mk0 _ ?_).map e
    rw [← map_natCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2
      (Nat.cast_ne_zero.2 (pow_ne_zero 2 hm.pos.ne'))
  obtain ⟨hex, huniq⟩ := hLaw.symLift _ A (m ^ 2) hm.pow hu T x hx
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨α₀, hα₀⟩ := hLaw.mulPull _ A m
    have e₁ : (snd T A.A).left ≫ (mulA A.A m).left = (snd T A.A ^ m).left := by
      rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
    obtain ⟨α₁, hα₁, -⟩ := exists_gen hL (φ' := ![(snd T A.A).left, (snd T A.A ^ m).left])
      (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
      (fun U _ f => by
        refine Finset.prod_congr rfl fun i _ => ?_
        fin_cases i
        · exact congrArg₂ (fun q n => f q ^ n) (Category.comp_id _) (Nat.cast_pow m 2).symm
        · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
      (LB.pullGen A.L ![𝟙 A.A.left, (mulA A.A m).left] ![(m : ℤ) ^ 2, -1] α₀ (snd T A.A).left)
      (DVR.pullGen_isGen _ _ _ _ hα₀ _)
    obtain ⟨α, hα, hn⟩ := exists_normalised hL hρ m _ _ (((m ^ 2 : ℕ) : ℤ) - 1) rfl α₁ hα₁
    obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT A.A T m) (snd T A.A ^ m) (lift_snd _ _)
      ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
    obtain ⟨V, hV, θ₀, hθ₀⟩ := hex p
    obtain ⟨h, hh⟩ := GlobalLift.exists_section (T := T) hV
    obtain ⟨θ, hθ⟩ := GlobalLift.exists_symLift_pull hL h hθ₀
    rw [← Category.assoc, hh, Category.id_comp] at hθ
    obtain ⟨t, ht⟩ := ThetaPtExist.exists_isTwistPull hL (translT A.A θ.pt) (translPt A.A θ.pt) (lift_snd _ _)
      ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) θ.φ θ.isGen s₁
    obtain ⟨c₀, hc₀⟩ := exists_value hL hρ _ t
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 c₀
    exact ⟨(t, c), α, s₁, θ, hα, hn, hs₁, hθ, ht, hc₀⟩
  · rintro ⟨t, c⟩ ⟨t', c'⟩ ⟨α, s₁, θ, hα, hn, hs₁, hθ, ht, hc⟩ ⟨α', s₁', θ', hα', hn', hs₁', hθ', ht', hc'⟩
    have ea := gen_unique hL (fst T A.A).left (ptSecT A.A 1).left ptSec_fst
      (CommPairing.surj_fst hLaw.globalFns A.isAb T) hα hα' (fun y J hJ => by
        have a := (val_corr hJ hn (𝟙 _)).trans (val_corr hJ hn' (𝟙 _)).symm
        rwa [val_pull hJ, val_pull hJ, Category.id_comp] at a)
    obtain rfl : s₁ = s₁' := sec_ext (sec_ext_val hL fun y J hJ =>
      (ThetaLin.sval_of_isTwistPull A.A hs₁ _ y hJ).trans
        (Eq.trans (by rw [ea _ _ y J hJ]) (ThetaLin.sval_of_isTwistPull A.A hs₁' _ y hJ).symm))
    have eθ := huniq θ θ' hθ hθ'
    have ept : θ.pt = θ'.pt := hθ.pt_eq.trans hθ'.pt_eq.symm
    obtain rfl : t = t' := sec_ext (sec_ext_val hL fun y J hJ =>
      (ThetaLin.sval_of_isTwistPull A.A ht _ y hJ).trans
        (Eq.trans (by rw [val_corr hJ eθ, ept]) (ThetaLin.sval_of_isTwistPull A.A ht' _ y hJ).symm))
    refine Prod.ext rfl ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).1
      (fn_ext (V := ⊤) fun y _ => ?_))
    choose J hJ using fun χ : T.left ⟶ A.A.left => exists_chart hL (χ y)
    exact (Units.mul_left_inj _).1 ((hc y J hJ).symm.trans (hc' y J hJ))

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConstStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.existsUnique_theta_const_of_odd : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m : ℕ), Odd m → ∀ (th : SecA A F 1) (x : TFK (R := R) F ⟶ A.A), x ^ (m ^ 2) = 1 → (∃! q : SecA A F (m ^ 2) × F, ThC A ρ m th x q.1 q.2) := by
  first | exact @GlobalTheory.existsUnique_thetaConst | exact GlobalTheory.existsUnique_thetaConst | (intros; apply GlobalTheory.existsUnique_thetaConst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalBundleOfSymmetricSemiAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalBundleOfSymmetricSemiAbelian
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_cp_of_isSymmetric :
    Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (L : RigLB G) (c : CubicalStr G L), L.IsSymmetric → ∃ P : CP G, P.L = L ∧ HEq P.c c := by
  intro hL R _ _ _ A G _ _ hS gen _ L c hsym
  obtain ⟨s, hs, hr⟩ := GlobalTheory.SymmetricBundle.gen_of_isSymmetric L hsym
  have := hS.smooth
  have : Flat (G3 G).hom := by
    show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom)
    infer_instance
  exact ⟨⟨L, c, s, hs, hr, GlobalTheory.ValueForm.sym_cub_of_baseChange (jK R) (GlobalTheory.ValueForm.app_generic_injective _)
    (GlobalTheory.ValueForm.surjective_cube_baseChange hL.globalFns _ A.isAb gen) c s hs hr⟩, rfl, HEq.rfl⟩

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalBundleOfSymmetricSemiAbelianStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.exists_cubical_bundle_of_symmetric_semiAbelian : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (L : RigLB G) (c : CubicalStr G L), L.IsSymmetric → ∃ P : CP G, P.L = L ∧ HEq P.c c := by
  first | exact @GlobalTheory.UU.exists_cp_of_isSymmetric | exact GlobalTheory.UU.exists_cp_of_isSymmetric | (intros; apply GlobalTheory.UU.exists_cp_of_isSymmetric <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPowDeg
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PsiInPow

open PsiInPull

variable {R : Type} [CommRing R] [IsDomain R]

theorem psiIn_of_gs (D : DegPre R) (χ : D.X) (J : Ideal R)
    (H : ∀ (q : D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens), IsAffineOpen V →
      V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q → ∀ z : Spec (CommRingCat.of (FractionRing R)), jK R z ∈ V →
      ∃ r ∈ J.map (DegPre.toOpen V), gs (jK R) z V r =
        (gm (𝟙 _) z (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => q)) ((D.psi χ).s (fun _ => q))).val) :
    D.PsiIn χ J := by
  intro j' V hV hle h'
  obtain ⟨q, rfl⟩ : ∃ q, j' = fun _ => q := ⟨j' PUnit.unit, rfl⟩
  have hss : Subsingleton (Spec (CommRingCat.of (FractionRing R))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  by_cases hne : ∃ z, jK R z ∈ V
  swap
  · exact ⟨0, Ideal.zero_mem _, fn_ext fun z hz => (hne ⟨z, hz⟩).elim⟩
  obtain ⟨z, hz⟩ := hne
  obtain ⟨r', hr', e'⟩ := H q V hV hle z hz
  refine ⟨r', hr', fn_ext fun y hy => ?_⟩
  obtain rfl : y = z := Subsingleton.elim (α := Spec (CommRingCat.of (FractionRing R))) y z
  exact (gs_pull (𝟙 _) (jK R) y V hz r').trans (e'.trans
    ((gs_res (𝟙 _) y h' hy _).trans (gs_unit _ _ _ (h' hy) _)).symm)

theorem gs_of_psiIn (D : DegPre R) (χ : D.X) (J : Ideal R) (H : D.PsiIn χ J)
    (q : D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens) (hV : IsAffineOpen V)
    (hle : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q) (z : Spec (CommRingCat.of (FractionRing R))) (hz : jK R z ∈ V) :
    ∃ r ∈ J.map (DegPre.toOpen V), gs (jK R) z V r =
      (gm (𝟙 _) z (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => q)) ((D.psi χ).s (fun _ => q))).val := by
  have h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (fun _ => q) :=
    fun y hy => mem_wchart _ _ _ _ (hle hy)
  obtain ⟨r, hrJ, hr⟩ := H (fun _ => q) V hV hle h
  refine ⟨r, hrJ, ?_⟩
  exact (gs_pull (𝟙 _) (jK R) z V hz r).symm.trans ((congrArg (gs (𝟙 _) z _) hr).trans
    ((gs_res (𝟙 _) z h hz _).trans (gs_unit _ _ _ (h hz) _)))

theorem val_psi_zero (D : DegPre R) (hB : D.TauBimult) {y : (TK R).left} {J} (hJ : Good D.P.L y J) :
    val (D.psi 0) (𝟙 _) y J = (val D.rigK (𝟙 _) y J)⁻¹ := by
  have C : IsCub (cubV D.cub (T := TK R) y J) := isCub_cubV D.cub hJ
  have t := tauK_mul hJ hB 0 0 0
  have z0 : val (D.tau (0 + 0) 0) (𝟙 _) y J = val (D.tau 0 0) (𝟙 _) y J :=
    congrArg (fun a => val (D.tau a 0) (𝟙 _) y J) (add_zero 0)
  rw [z0, cPoint_zero, C.face, _root_.mul_one] at t
  have t0 : val (D.tau 0 0) (𝟙 _) y J = 1 := mul_eq_left.1 t.symm
  have e : val (D.tau 0 0) (𝟙 _) y J = val (D.psi (0 + 0)) (𝟙 _) y J * (val (D.psi 0) (𝟙 _) y J)⁻¹ *
      (val (D.psi 0) (𝟙 _) y J)⁻¹ * (val D.rigK (𝟙 _) y J)⁻¹ :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  rw [t0, add_zero, mul_inv_cancel, _root_.one_mul] at e
  exact (inv_mul_eq_one.1 e.symm)

end PsiInPow

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPsiThetaExpansionPsiRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPsiThetaExpansionPsiRelation
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.PsiExists

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem cT_zero (T : Over (Spec (CommRingCat.of R))) : cT D T 0 = 1 := by
  have h := DVR.cPoint_add D T 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem comp_famφT {T T₀ : Over (Spec (CommRingCat.of R))} (r : T ⟶ T₀ ⊗ D.P.A) (α : D.X) (k : Fin 4) :
    r.left ≫ famφT D T₀ α k = ![(r ≫ snd T₀ D.P.A).left, ((r ≫ snd T₀ D.P.A) * cT D T α).left, (cT D T α).left,
      (1 : T ⟶ D.P.A).left] k := by
  have c : r ≫ cT D _ α = cT D T α := by rw [← Category.assoc, comp_toUnit]
  fin_cases k
  · rfl
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul r (snd T₀ D.P.A) (cT D _ α)).trans (congrArg _ c))
  · exact congrArg (fun q => q.left) c
  · exact congrArg (fun q => q.left) (MonObj.comp_one (M := D.P.A) r)

theorem famφT_eq (T₀ : Over (Spec (CommRingCat.of R))) (α : D.X) :
    famφT D T₀ α = ![(snd T₀ D.P.A).left, (snd T₀ D.P.A * cT D _ α).left, (cT D _ α).left,
      (1 : T₀ ⊗ D.P.A ⟶ D.P.A).left] := rfl

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem exists_pullB {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ) (f : ∀ α, SecBT D T k α) :
    ∃ s : Raw D F k, PullB D F φ k f s := by
  have H : ∀ α, FormEq (Sum.elim (fun i => (φ ▷ D.P.A).left ≫ famφT D T α i)
      (fun e : PEmpty => (e.elim : (DegPre.BF D F).left ⟶ D.P.A.left))) (Sum.elim (DegPre.famε k) fun e => e.elim)
      (DegPre.famφ D F α) (DegPre.famε k) := by
    intro α U _ h
    have e : (fun i => (φ ▷ D.P.A).left ≫ famφT D T α i) = DegPre.famφ D F α := by
      funext i
      rw [comp_famφT, whiskerRight_snd]; rfl
    rw [e, Fintype.prod_sum_type]
    simp
  choose s hs using fun α => exists_sec D.P.isLB (H α)
    (pullMulSec (f α) (φ ▷ D.P.A).left (LB.oneGen D.P.L) (oneGen_isGen _))
  refine ⟨s, fun α z J hJ => ?_⟩
  refine (hs α _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ _ hJ).trans ?_)
  rw [val_one, Units.val_one, _root_.mul_one, Category.id_comp]

theorem isIso_trF (χ : D.X) : IsIso (DegPre.trF D F χ) := by
  have key : ∀ a b : D.X, a + b = 0 → DegPre.trF D F a ≫ DegPre.trF D F b = 𝟙 _ := by
    intro a b hab
    have c : DegPre.trF D F a ≫ cT D _ b = cT D _ b := by rw [← Category.assoc, comp_toUnit]
    have e : DegPre.trF D F a ≫ (snd (TF (R := R) F) D.P.A * cT D _ b) = snd _ _ := by
      rw [MonObj.comp_mul, c, show DegPre.trF D F a ≫ snd _ _ = snd (TF (R := R) F) D.P.A * cT D _ a from lift_snd _ _,
        _root_.mul_assoc]
      have := (DVR.cPoint_add D (DegPre.BF D F) a b).symm
      rw [hab] at this
      rw [show cT D (DegPre.BF D F) a * cT D _ b = 1 from this.trans (cT_zero D _), _root_.mul_one]
    have e' : DegPre.trF D F a ≫ fst _ _ = fst _ _ := lift_fst _ _
    exact (comp_lift _ _ _).trans ((congrArg₂ lift e' e).trans lift_fst_snd)
  exact ⟨DegPre.trF D F (-χ), key _ _ (add_neg_cancel χ), key _ _ (neg_add_cancel χ)⟩

theorem exists_translate (χ : D.X) (s₀ : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F 0) (DegPre.famε 1))) :
    ∃ h : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε 1)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
        sval h r z J = sval s₀ (r ≫ (DegPre.trF D F χ).left) z J *
          (val (D.psi χ) (r ≫ (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) z J *
            val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
              (r ≫ (DegPre.BF D F).hom) z J).val := by
  let κ : DegPre.BF D F ⟶ TK R := Over.homMk ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F)
    ((Category.assoc _ _ _).trans (Over.w (fst (TF (R := R) F) D.P.A)))
  have H : FormEq (Sum.elim (fun i => (DegPre.trF D F χ).left ≫ DegPre.famφ D F 0 i)
      (Sum.elim (fun _ : PUnit => κ.left ≫ ptK (D.c χ)) (fun _ : PUnit => (DegPre.BF D F).hom ≫ eSec D.P.A)))
      (Sum.elim (DegPre.famε 1) (Sum.elim (fun _ => -1) (fun _ => 1))) (DegPre.famφ D F χ) (DegPre.famε 1) := by
    intro U _ h
    have e₁ : (fun i => (DegPre.trF D F χ).left ≫ DegPre.famφ D F 0 i) =
        ![(snd (TF (R := R) F) D.P.A * cT D _ χ).left, (snd (TF (R := R) F) D.P.A * cT D _ χ).left,
          (1 : DegPre.BF D F ⟶ D.P.A).left, (1 : DegPre.BF D F ⟶ D.P.A).left] := by
      funext i
      refine (comp_famφT D (DegPre.trF D F χ) 0 i).trans ?_
      rw [cT_zero, _root_.mul_one,
        show DegPre.trF D F χ ≫ snd _ _ = snd (TF (R := R) F) D.P.A * cT D _ χ from lift_snd _ _]
    have e₂ : κ.left ≫ ptK (D.c χ) = (cT D (DegPre.BF D F) χ).left :=
      congrArg (fun q => q.left) (show κ ≫ cT D _ χ = cT D _ χ by rw [← Category.assoc, comp_toUnit])
    have e₃ : (DegPre.BF D F).hom ≫ eSec D.P.A = (1 : DegPre.BF D F ⟶ D.P.A).left := rfl
    rw [e₁, e₂, e₃, show DegPre.famφ D F χ = _ from famφT_eq D (TF (R := R) F) χ, Fintype.prod_sum_type,
      Fintype.prod_sum_type]
    simp [Fin.prod_univ_four, DegPre.famε, _root_.mul_assoc]
  obtain ⟨h, hh⟩ := exists_sec D.P.isLB H (pullMulSec s₀ (DegPre.trF D F χ).left
    (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (D.psi χ) κ.left)
      (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (DegPre.BF D F).hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (D.psi_gen χ) _) (DVR.pullGen_isGen _ _ _ _ D.rig_gen _)))
  refine ⟨h, fun Z r z J hJ => (hh Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ _ _ hJ).trans ?_)⟩
  exact congrArg (fun u : (Z.presheaf.stalk z)ˣ => sval s₀ (r ≫ (DegPre.trF D F χ).left) z J * u.val)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_pull hJ _ _ _)))

def constVal {F : Type} [Field F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) : F →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)

theorem constVal_eq {F : Type} [Field F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (c : F) :
    constVal p z c = gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) := (gs_eq p z ⊤ trivial _).symm

theorem exists_ratio (h₁ : Laws) (h₂ : Laws2) (χ : D.X)
    (s t : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε 1))) (hs : ∃ j, s.f j ≠ 0) (ht : ∃ j, t.f j ≠ 0) :
    ∃ a : Fˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval s r z J = constVal (r ≫ (fst (TF (R := R) F) D.P.A).left) z a.val * sval t r z J := by
  obtain ⟨b, hb⟩ := exists_basis_twist_field h₁ h₂ R D F 1 le_rfl χ
  have : Subsingleton (Fin (1 ^ D.P.g)) := by rw [one_pow]; infer_instance
  let i₀ : Fin (1 ^ D.P.g) := ⟨0, by simp⟩
  have key : ∀ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε 1)), (∃ j, s.f j ≠ 0) →
      ∃ c : F, c ≠ 0 ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
        sval s r z J = constVal (r ≫ (fst (TF (R := R) F) D.P.A).left) z c * sval (b i₀) r z J := by
    rintro s ⟨j, hj⟩
    obtain ⟨c, hc, -⟩ := hb s
    have hc' : ∀ j, s.f j = DegPre.constBF D F (c i₀) _ * (b i₀).f j := fun j =>
      (hc j).trans (Fintype.sum_subsingleton _ i₀)
    refine ⟨c i₀, fun h0 => hj ?_, fun Z r z J hJ => ?_⟩
    · rw [hc', h0, DegPre.constBF, map_zero, map_zero, map_zero, zero_mul]
    · rw [constVal_eq]
      exact (congrArg (gs r z _) (hc' _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·)
        ((gs_res r z le_top (hJ.mem _ r) _).trans (gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _)) rfl))
  obtain ⟨c, hc0, hc⟩ := key s hs
  obtain ⟨d, hd0, hd⟩ := key t ht
  refine ⟨Units.mk0 (c / d) (div_ne_zero hc0 hd0), fun Z r z J hJ => ?_⟩
  rw [hc Z r z J hJ, hd Z r z J hJ, ← _root_.mul_assoc, ← map_mul, Units.val_mk0, div_mul_cancel₀ c hd0]

theorem exists_psi_of_section (h₁ : Laws) (h₂ : Laws2) (i : (TK R).left ⟶ Spec (CommRingCat.of F))
    (hi : i ≫ jFK (R := R) F = 𝟙 _) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (hf : ∀ α, ∃ j, (f α).f j ≠ 0) :
    ∃ ψ : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1)),
      (∀ χ, (ψ χ).IsGen) ∧ ∀ (χ : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ 𝟙_ _) (κ : T ⟶ TK R)
        (y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → sval (f χ) (lift ρ y).left z J =
          (val (ψ χ) κ.left z J * rigV D z J).val * sval (f 0) (lift ρ (y * cT D T χ)).left z J := by
  obtain ⟨s, hs⟩ := exists_pullB D F (toUnit _) 1 f
  have hs0 := fun α => (pullB_ne_zero_iff R D F 1 f s hs α).2 (hf α)
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (DegPre.BF D F).left := isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  choose h hh using fun χ => exists_translate D F χ (s 0)
  have hh0 : ∀ χ, ∃ j, (h χ).f j ≠ 0 := fun χ => by
    obtain ⟨J, hJ⟩ := exists_good_pt (Z := (DegPre.BF D F).left) D.P.isLB (genericPoint _)
    have := isIso_trF D F χ
    have : IsIso (DegPre.trF D F χ).left := inferInstanceAs (IsIso ((Over.forget _).map (DegPre.trF D F χ)))
    rw [exists_ne_zero_iff_sval_ne_zero _ hJ, hh χ _ _ _ J hJ, Category.id_comp]
    exact mul_ne_zero (sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s 0) (hs0 0) _ _ _ J hJ) (Units.ne_zero _)
  choose a ha using fun χ => exists_ratio D F h₁ h₂ χ (s χ) (h χ) (hs0 χ) (hh0 χ)
  let u : D.X → Γ((TK R).left, ⊤)ˣ := fun χ => Units.map (i.app ⊤).hom.toMonoidHom (unitOn (a χ))
  refine ⟨fun χ => GlobalTheory.UU.scaleGen (u χ) (D.psi χ), fun χ => GlobalTheory.UU.scaleGen_isGen _ (D.psi_gen χ), ?_⟩
  intro χ T ρ κ y z J hJ
  have hκ : (κ.left ≫ i) ≫ jFK (R := R) F = κ.left := by rw [Category.assoc, hi, Category.comp_id]
  let κ' : T ⟶ TF (R := R) F := Over.homMk (κ.left ≫ i)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) hκ).trans (Over.w κ)))
  have hρ : κ' ≫ toUnit _ = ρ := toUnit_unique _ _
  have v₁ := pullB_values R D _ _ _ 1 f s hs χ T κ' y z J hJ
  have v₂ := pullB_values R D _ _ _ 1 f s hs 0 T κ' (y * cT D T χ) z J hJ
  rw [hρ] at v₁ v₂
  have a₁ : (lift κ' y).left ≫ (fst (TF (R := R) F) D.P.A).left = κ.left ≫ i :=
    congrArg (fun q => q.left) (lift_fst κ' y)
  have a₂ : (lift κ' y).left ≫ (DegPre.trF D F χ).left = (lift κ' (y * cT D T χ)).left := by
    refine congrArg (fun q => q.left) (?_ : lift κ' y ≫ DegPre.trF D F χ = _)
    refine (comp_lift _ _ _).trans (congrArg₂ lift (lift_fst _ _) ?_)
    refine (MonObj.comp_mul (lift κ' y) (snd _ D.P.A) (cT D _ χ)).trans ?_
    rw [lift_snd, ← Category.assoc, comp_toUnit]
  have a₃ : (lift κ' y).left ≫ (DegPre.BF D F).hom = T.hom := Over.w _
  have a₄ : (lift κ' y).left ≫ (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F = κ.left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jFK (R := R) F) a₁).trans hκ)
  have w₁ := ha χ _ (lift κ' y).left z J hJ
  have w₂ := hh χ _ (lift κ' y).left z J hJ
  rw [a₂, a₃, a₄] at w₂
  rw [a₁] at w₁
  have w₃ := GlobalTheory.UU.val_scaleGen (u χ) (D.psi χ) κ.left hJ
  have w₄ : (gm κ.left z ⊤ (u χ)).val = constVal (κ.left ≫ i) z (a χ).val :=
    (gs_unit κ.left z ⊤ trivial _).symm.trans ((gs_pull κ.left i z ⊤ trivial _).trans (constVal_eq _ _ _).symm)
  have alg : ∀ (A : Type) [CommRing A] (x₁ x₂ s₁ s₂ t c : A) (p q u v : Aˣ), s₁ = x₁ → s₂ = x₂ → s₁ = c * t →
      t = s₂ * (p * q).val → v = u * p → u.val = c → x₁ = (v * q).val * x₂ := by
    intro A _ x₁ x₂ s₁ s₂ t c p q u v e₁ e₂ e₃ e₄ e₅ e₆
    rw [← e₁, ← e₂, e₃, e₄, e₅, ← e₆]
    simp only [Units.val_mul]
    ring
  exact alg _ _ _ _ _ _ _ _ _ _ _ v₁ v₂ w₁ w₂ w₃ w₄

end GlobalTheory.PsiExists

namespace GlobalTheory

theorem exists_psi_psiRel : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (f : ∀ α, SecBT D (𝟙_ _) 1 α), (∀ α, ∃ j, (f α).f j ≠ 0) → ∃ ψ h, PsiRel (setPsi D ψ h) (𝟙_ _) f := by
  intro h₁ h₂ R _ _ D f hf
  obtain ⟨ψ, h, H⟩ := PsiExists.exists_psi_of_section D (FractionRing R) h₁ h₂ (𝟙 _)
    ((Category.id_comp _).trans (Spec.map_id _)) f hf
  exact ⟨ψ, h, H⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPsiThetaExpansionPsiRelationStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.exists_psi_thetaExpansionPsiRelation : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (f : ∀ α, SecBT D (𝟙_ _) 1 α), (∀ α, ∃ j, (f α).f j ≠ 0) → ∃ ψ h, PsiRel (setPsi D ψ h) (𝟙_ _) f := by
  first | exact @GlobalTheory.exists_psi_psiRel | exact GlobalTheory.exists_psi_psiRel | (intros; apply GlobalTheory.exists_psi_psiRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenPull
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BiTrivLiftOfIsNilpotentStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_biTriv_of_nonempty_biTriv_reduction : (∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] [IsCommMonObj G₀] [ConnectedSpace G₀.left] (F : G₀.left ⟶ G.left) (hw), IsGrpPullback G₀ G (red J) F → ∀ (P : CP G) (P₀ : CP G₀) (w), IsCPMap P₀ P (red J) F hw w → ∀ (i : splitTorus _ X ⟶ G) (i₀ : splitTorus _ X ⟶ G₀), IsMonHom i → IsMonHom i₀ → TorusCompat (red J) F i₀ i → Nonempty (BiTriv P₀.c i₀) → Nonempty (BiTriv P.c i)) := by
  first | exact @GlobalTheory.UU.biTriv_lift_of_isNilpotent | exact GlobalTheory.UU.biTriv_lift_of_isNilpotent | (intros; apply GlobalTheory.UU.biTriv_lift_of_isNilpotent <;> assumption)
end

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.TowerEx

theorem toBase_mul {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) (hw : F ≫ G.hom = G'.hom ≫ f) (T : Over S') (x y : T ⟶ G') :
    toBase hw (x * y) = toBase hw x * toBase hw y :=
  Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

theorem exists_congr {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {P : CP G} {P' : CP G'} {f f' : S' ⟶ S} {F F' : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) (e : f = f') (e' : F = F') (hw') : ∃ w', IsCPMap P' P f' F' hw' w' := by
  subst e e'
  exact ⟨w, h⟩

theorem exists_cancel {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] {P : CP G} {P' : CP G'} {P'' : CP G''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {f'' : S'' ⟶ S} {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left} {F'' : G''.left ⟶ G.left}
    {hw w hw'' w''} (h : IsCPMap P' P f F hw w) (h'' : IsCPMap P'' P f'' F'' hw'' w'')
    (hF : IsGrpPullback G'' G' f' F') (e : f' ≫ f = f'') (e' : F' ≫ F = F'') :
    ∃ w', IsCPMap P'' P' f' F' hF.1.w w' := by
  subst e e'
  exact ((isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF.1.w _ h).2 (toBase_mul hF _) _ h'').imp fun _ => And.left

theorem exists_even_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {P : CP G} {P' : CP G'} {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'}
    [IsMonHom i'] (hi : TorusCompat f F i' i) (σ : CubTriv P.c i) (hσ : σ.Even) :
    ∃ σ' : CubTriv P'.c i', σ'.Even := by
  have hE := SplitTorus.isGrpPullback_bcMap f X
  rw [torusCompat_iff] at hi
  have hc : ∀ k : Fin 2, ![i'.left, (1 : splitTorus S' X ⟶ G').left] k ≫ F =
      SplitTorus.bcMap f X ≫ ![i.left, (1 : splitTorus S X ⟶ G).left] k := fun k => by
    fin_cases k
    · exact hi.symm
    · show (1 : splitTorus S' X ⟶ G').left ≫ F = SplitTorus.bcMap f X ≫ (1 : splitTorus S X ⟶ G).left
      rw [one_left_comp h.mul, one_left, ← Category.assoc, hE.1.w]
  obtain ⟨s, hs, Hs⟩ := CubTransport.exists_pmaps ((isGen_iff w).1 h.gen) P.L.isLB P'.L.isLB _ hc σ.s σ.gen
  let β := toBaseHom (toBase_mul hE hE.1.w)
  have hβ : ∀ {T : Over S'} (t : T ⟶ splitTorus S' X), β T t ≫ i = toBase hw (t ≫ i') := fun t =>
    Over.OverMorphism.ext (by
      show (t.left ≫ SplitTorus.bcMap f X) ≫ i.left = (t.left ≫ i'.left) ≫ F
      rw [Category.assoc, hi, Category.assoc])
  have vs : ∀ (T : Over S') (z : T.left) (J') (J), Good P'.L.L z J' → Good P.L.L z J →
      ∀ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left)) →
      ∀ t : T ⟶ splitTorus S' X, @id (T.left.presheaf.stalk z)ˣ (val σ.s (β T t).left z J) =
        W (t ≫ i') * (W 1)⁻¹ * val s t.left z J' := by
    intro T z J' J hJ' hJ W hW t
    refine (CubTransport.val_pmaps hc Hs t.left hJ hJ').trans (congrArg₂ (· * ·) ?_ rfl)
    rw [hW, hW]
    exact CubTrivTorus.prod_cubTriv i' t (fun q => gw w q z (J (q ≫ F)) (J' q))
  refine ⟨⟨s, hs, fun T x y u z J' hJ' => ?_⟩, fun T x z J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left) := ⟨_, fun _ => rfl⟩
    have a := (h.vals T z J' J hJ' hJ W hW).2.2 (x ≫ i') (y ≫ i') (u ≫ i')
    obtain ⟨Z, hZ⟩ : ∃ Z : (T ⟶ splitTorus S' X) → (T.left.presheaf.stalk z)ˣ,
      ∀ t, Z t = val σ.s (β T t).left z J := ⟨_, fun _ => rfl⟩
    have b := σ.cub _ (β T x) (β T y) (β T u) z J hJ
    simp only [← map_mul, hβ] at b
    have b' : Z (x * y * u) * Z x * Z y * Z u = @id (T.left.presheaf.stalk z)ˣ
        (cubV P.c (T := Over.mk (T.hom ≫ f)) z J (toBase hw (x ≫ i')) (toBase hw (y ≫ i')) (toBase hw (u ≫ i'))) *
        Z (x * y) * Z (x * u) * Z (y * u) := by
      simp only [hZ]; exact b
    have v : ∀ t, Z t = W (t ≫ i') * (W 1)⁻¹ * val s t.left z J' := fun t => (hZ t).trans (vs T z J' J hJ' hJ W hW t)
    generalize @id (T.left.presheaf.stalk z)ˣ
        (cubV P.c (T := Over.mk (T.hom ≫ f)) z J (toBase hw (x ≫ i')) (toBase hw (y ≫ i')) (toBase hw (u ≫ i'))) = C
      at a b'
    simp only [v, MonObj.mul_comp] at b'
    apply Additive.ofMul.injective
    have a' := congrArg Additive.ofMul a
    have b'' := congrArg Additive.ofMul b'
    simp only [ofMul_mul, ofMul_inv] at a' b'' ⊢
    linear_combination (norm := abel) a' + b''
  · obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left) := ⟨_, fun _ => rfl⟩
    have a := (h.vals T z J' J hJ' hJ W hW).2.1 (x ≫ i')
    have b := hσ _ (β T x) z J hJ
    rw [← map_inv, hβ] at b
    have b' : W (x⁻¹ ≫ i') * (W 1)⁻¹ * val s (x⁻¹).left z J' =
        val P.sym ((x ≫ i').left ≫ F) z J * (W (x ≫ i') * (W 1)⁻¹ * val s x.left z J') := by
      rw [← vs T z J' J hJ' hJ W hW, ← vs T z J' J hJ' hJ W hW]; exact b
    rw [GrpObj.inv_comp] at b'
    show val s _ z J' = _ * val s _ z J'
    apply Additive.ofMul.injective
    have a' := congrArg Additive.ofMul a
    have b'' := congrArg Additive.ofMul b'
    simp only [ofMul_mul, ofMul_inv] at a' b'' ⊢
    linear_combination (norm := abel) a' + b''

theorem nonempty_biTriv (A : Type) [CommRing A] [IsLocalRing A] (hA : IsNilpotent (IsLocalRing.maximalIdeal A))
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (P : CP G) (i : splitTorus _ X ⟶ G)
    (hi : IsMonHom i) : Nonempty (BiTriv P.c i) := by
  letI : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  let f := red (IsLocalRing.maximalIdeal A)
  have hF := isGrpPullback_pullback G f
  have : Smooth ((Over.pullback f).obj G).hom := by show Smooth (pullback.snd G.hom f); infer_instance
  have : GeometricallyConnected ((Over.pullback f).obj G).hom := by
    show GeometricallyConnected (pullback.snd G.hom f); infer_instance
  have : ConnectedSpace (Spec (CommRingCat.of (A ⧸ IsLocalRing.maximalIdeal A))) :=
    SplitTorus.connectedSpace_of_isLocalRing _
  have := (GroupConn.connectedSpace_group _ ((Over.pullback f).obj G)).1
  obtain ⟨i₀, h₀, -⟩ := existsUnique_torusCompat (G' := (Over.pullback f).obj G) hF.1 i
  obtain ⟨_, _, _, _, _, _, _, hP⟩ := exists_isCPMap P (toBase_mul hF hF.1.w) _ (pull_isLB P.L.isLB _) _
    (pullIso_isGen P.L.isLB _)
  exact T.nonempty_biTriv_of_nonempty_biTriv_reduction A _ hA X G _ _ _ hF P _ _ hP i i₀ hi (h₀.isMonHom hF) h₀
    (BiextTriv.main _ X _ _ _ i₀ (h₀.isMonHom hF))

theorem nonempty_desc (A : Type) [CommRing A] [IsLocalRing A] (hA : IsNilpotent (IsLocalRing.maximalIdeal A))
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (P : CP G) (Q : TQ G X)
    (h : ∃ σ : CubTriv P.c Q.i, σ.Even) : Nonempty (Q.Desc P) := by
  have : ConnectedSpace (Spec (CommRingCat.of A)) := SplitTorus.connectedSpace_of_isLocalRing _
  have := (GroupConn.connectedSpace_group _ G).1
  exact UU.nonempty_desc _ X G Q P (nonempty_biTriv A hA G P Q.i Q.i_hom) h

theorem exists_lift {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [Nontrivial A']
    (hA : IsNilpotent (IsLocalRing.maximalIdeal A)) (φ : A →+* A') (hφ : Function.Surjective φ)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (G' : Over (Spec (CommRingCat.of A'))) [GrpObj G']
    [IsCommMonObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom φ)) F)
    {P : CP G} {P' : CP G'} {hw} {w} (hP : IsCPMap P' P (Spec.map (CommRingCat.ofHom φ)) F hw w) (Q' : TQ G' X)
    (h : ∃ σ : CubTriv P'.c Q'.i, σ.Even) :
    ∃ Q : TQ G X, TorusCompat (Spec.map (CommRingCat.ofHom φ)) F Q'.i Q.i ∧ ∃ σ : CubTriv P.c Q.i, σ.Even := by
  have hJ : RingHom.ker φ ≠ ⊤ := RingHom.ker_ne_top φ
  have hN : IsNilpotent (RingHom.ker φ) := by
    obtain ⟨n, hn⟩ := hA
    exact ⟨n, le_bot_iff.1 ((Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hJ) n).trans hn.le)⟩
  let e := (RingHom.quotientKerEquivOfSurjective hφ).symm
  let g : Spec (CommRingCat.of (A ⧸ RingHom.ker φ)) ⟶ Spec (CommRingCat.of A') := Spec.map e.toCommRingCatIso.hom
  have hg : g ≫ Spec.map (CommRingCat.ofHom φ) = red (RingHom.ker φ) := by
    rw [← Spec.map_comp]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
    exact (RingHom.quotientKerEquivOfSurjective hφ).symm_apply_eq.2 rfl
  have hG := isGrpPullback_pullback G' g
  have hF₀ := (hG.comp hF).congr hg rfl
  obtain ⟨Q₀, h₀⟩ := exists_tq_baseChange _ _ g X G' _ _ hG Q'
  obtain ⟨Q, hQ⟩ := TorusQuotLift.main A _ hN X G _ _ hF₀ Q₀
  refine ⟨Q, ?_, ?_⟩
  · have : IsIso (SplitTorus.bcMap g X) := (SplitTorus.isGrpPullback_bcMap g X).1.isIso_fst_of_isIso
    rw [torusCompat_iff] at h₀ hQ ⊢
    rw [← cancel_epi (SplitTorus.bcMap g X), ← Category.assoc, ← bcMap_comp, hg, hQ, ← Category.assoc, ← h₀,
      Category.assoc]
  · obtain ⟨_, _, _, _, _, _, _, hP₀⟩ := exists_isCPMap P' (toBase_mul hG hG.1.w) _ (pull_isLB P'.L.isLB _) _
      (pullIso_isGen P'.L.isLB _)
    obtain ⟨_, -, h₁⟩ := hP.exists_comp hP₀ (hG.comp hF).1.w
    obtain ⟨_, h₂⟩ := exists_congr h₁ hg rfl hF₀.1.w
    obtain ⟨σ, hσ⟩ := h
    have := Q₀.i_hom
    exact T.exists_even_cubicalTrivialisation_lift_nilpotent A _ hN hJ X G _ _ _ hF₀ P _ _ h₂ Q.i Q₀.i Q.i_hom Q₀.i_hom hQ
      (nonempty_biTriv A hA G P Q.i Q.i_hom) (exists_even_pull hP₀ h₀ σ hσ)

theorem exists_transition {S S' : Scheme.{0}} [ConnectedSpace S'] {f : S' ⟶ S} {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    [ConnectedSpace G'.left] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {P : CP G} {P' : CP G'} {hw} {w}
    (hP : IsCPMap P' P f F hw w) {Q : TQ G X} {Q' : TQ G' X} (h : TorusCompat f F Q'.i Q.i) (D : Q.Desc P)
    (D' : Q'.Desc P') :
    ∃ β : Q'.B.left ⟶ Q.B.left, IsCPPullback D'.M D.M f β ∧ Q'.q.left ≫ β = F ≫ Q.q.left := by
  obtain ⟨β, hq, hβ⟩ := TQ.exists_isGrpPullback _ _ f X G G' F hF Q Q' h
  obtain ⟨_, -, h₁⟩ := D.map.exists_comp hP (by rw [Category.assoc, Over.w, Category.comp_id, hw])
  obtain ⟨_, h₂⟩ := exists_congr h₁ (Category.comp_id f) hq.symm (by
    rw [Category.assoc, hβ.1.w, ← Category.assoc, Over.w])
  exact ⟨β, ⟨hβ, isCPMap_descends _ _ f X G' Q' P' D' Q.B D.M β hβ.1.w _ _ (toBase_mul hβ _) h₂⟩, hq⟩

end GlobalTheory.UU.TowerEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardQuotientKTorsionPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardQuotientKTorsionPairs
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT
open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem card_qk_eq_mul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {k : ℕ} (hk : k ≠ 0)
    (hd : ∀ y : D.X, ∃ g : GtPtF D F, k • g = iota hB F y) :
    Nat.card (Quot (QkPt.Equiv D F (k := k))) = k ^ D.rank * Nat.card {g : GtPtF D F // k • g = 0} := by
  choose r hr using hd
  let K : AddSubgroup D.X := (nsmulAddMonoidHom k : D.X →+ D.X).range
  have hK : Nat.card (D.X ⧸ K) = k ^ D.rank := AddSubgroup.index_range_nsmul D.X k
  let f : (D.X ⧸ K) × {g : GtPtF D F // k • g = 0} → Quot (QkPt.Equiv D F (k := k)) := fun x =>
    Quot.mk _ (qkMk hB x.1.out (r x.1.out + x.2.1) (by rw [nsmul_add, hr, x.2.2, add_zero]))
  rw [← hK, ← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · rintro ⟨c, t⟩ ⟨c', t'⟩ h
    obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 ((equiv_equivalence hB).eqvGen_iff.1 (Quot.eqvGen_exact h))
    simp only [qkMk_y, qkMk_g] at hy hg
    obtain rfl : c = c' := by
      rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', QuotientAddGroup.eq]
      exact ⟨z, by rw [hy, neg_add_cancel_left]; rfl⟩
    have hz : z = 0 := by
      have h0 : (k : ℤ) • z = 0 := by rw [natCast_zsmul]; exact left_eq_add.1 hy
      exact (smul_eq_zero.1 h0).resolve_left (by exact_mod_cast hk)
    rw [hz, map_zero, add_zero, add_right_inj] at hg
    exact Prod.ext rfl (Subtype.ext hg.symm)
  · rintro ⟨p⟩
    obtain ⟨z, hz⟩ : -p.y + (QuotientAddGroup.mk p.y : D.X ⧸ K).out ∈ K := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
    have hy : (QuotientAddGroup.mk p.y : D.X ⧸ K).out = p.y + k • z := by
      rw [show k • z = _ from hz, add_neg_cancel_left]
    refine ⟨⟨QuotientAddGroup.mk p.y, p.g + iota hB F z - r (QuotientAddGroup.mk p.y : D.X ⧸ K).out, ?_⟩,
      (Quot.sound ((equiv_iff hB _ _).2 ⟨z, hy, ?_⟩)).symm⟩
    · rw [nsmul_sub, hr, hy, nsmul_add, qk_nsmul hB, map_add (f := _), map_nsmul, sub_self]
    · exact add_sub_cancel _ _

theorem card_qk : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → Nat.card (Quot (QkPt.Equiv D.toPre F (k := k))) = k ^ (2 * (D.toPre.rank + D.toPre.P.g)) := by
  intro hL R _ _ _ I hA D F _ _ _ k hk
  have : IsNoetherianRing R := hA.1
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  have h₁ := (GlobalTheory.GtCount.card_gtTors hL.1 hL.2.1 R D.toPre F k (Nat.cast_ne_zero.2 (by omega))).1
  simp only [GlobalTheory.GtCount.gtTors_iff] at h₁
  have h₂ := (gt_onto_divisible_kernel hL R I hA D F).2.1 k hk
  rw [card_qk_eq_mul D.tau_bimult (by omega) fun y => (h₂ _).imp fun _ e => ((isNsmul_iff_eq _ _ _).1 e).symm, h₁,
    ← pow_add]
  congr 1
  ring

end GlobalTheory.UT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardQuotientKTorsionPairsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.card_quotient_kTorsion_pairs : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → Nat.card (Quot (QkPt.Equiv D.toPre F (k := k))) = k ^ (2 * (D.toPre.rank + D.toPre.P.g)) := by
  first | exact @GlobalTheory.UT.card_qk | exact GlobalTheory.UT.card_qk | (intros; apply GlobalTheory.UT.card_qk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSectionsIrreducibleThetaGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSectionsIrreducibleThetaGroup
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ThetaIrred

theorem irreducible_of_ringEquiv (F : Type) [Field F] [IsAlgClosed F] (R : Type) [CommRing R] (σ : F ≃+* R)
    (A : Type) [CommGroup A] (V : Type) [AddCommGroup V] [Module R V] (E : Type) [AddCommGroup E] [Module F E]
    (j : V ≃+ E) (hj : ∀ (c : F) v, j (σ c • v) = c • j v) (e : A → A → Rˣ) (Φ : A → (V ≃ₗ[R] V))
    (hcard : (Nat.card A : F) ≠ 0) (hdim : Module.finrank R V ^ 2 = Nat.card A)
    (hmul : ∀ a b, ∃ c : Rˣ, ∀ v, Φ (a * b) v = (c : R) • Φ a (Φ b v))
    (hcomm : ∀ a b v, Φ a (Φ b v) = (e a b : R) • Φ b (Φ a v)) (hnd : ∀ a, (∀ b, e a b = 1) → a = 1)
    (U : Submodule F E) (hU : ∀ a v, j v ∈ U → j (Φ a v) ∈ U) : U = ⊥ ∨ U = ⊤ := by
  letI := (MulEquiv.isField (Field.toIsField F) σ.symm.toMulEquiv).toField
  haveI : IsAlgClosed R := IsAlgClosed.of_ringEquiv F R σ
  have h0 : Nat.card A ≠ 0 := fun h => hcard (by rw [h, Nat.cast_zero])
  haveI : Finite A := Nat.finite_of_card_ne_zero h0
  haveI : Module.Finite R V := Module.finite_of_finrank_pos
    (Nat.pos_of_ne_zero fun h => h0 (by rw [← hdim, h]; rfl))
  have hc : (Nat.card A : R) ≠ 0 := fun h => hcard (σ.injective (by rw [map_natCast, h, map_zero]))
  let W : Submodule R V :=
    { carrier := {v | j v ∈ U}
      add_mem' := fun {a b} ha hb => by
        show j (a + b) ∈ U
        rw [map_add (f := _)]; exact U.add_mem ha hb
      zero_mem' := by
        show j 0 ∈ U
        rw [map_zero]; exact U.zero_mem
      smul_mem' := fun c v hv => by
        show j (c • v) ∈ U
        rw [← σ.apply_symm_apply c, hj]; exact U.smul_mem _ hv }
  have hone : ∃ c : Rˣ, ∀ v, (1 : V ≃ₗ[R] V) v = (c : R) • Φ 1 v := by
    obtain ⟨c, hc⟩ := hmul 1 1
    refine ⟨c, fun v => (Φ 1).injective ?_⟩
    rw [map_smul, ← hc, _root_.mul_one]; rfl
  have key := GlobalTheory.heisenberg_weightSpace_irreducible R A V e Φ hc hdim hmul hcomm hnd ⊥ 1
    (fun t => by
      obtain rfl : t = 1 := Subsingleton.elim _ _
      exact hone)
    (fun _ => ⊤)
    (fun χ v => ⟨fun _ t => by
      obtain rfl : t = 1 := Subsingleton.elim _ _
      rw [map_one, map_one, Units.val_one, one_smul]; rfl, fun _ => trivial⟩)
    1 W le_top (fun h _ v hv => hU h v hv)
  refine key.imp (fun h => ?_) (fun h => ?_)
  · refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    obtain ⟨v, rfl⟩ := j.surjective x
    have hv : v ∈ W := hx
    rw [h, Submodule.mem_bot] at hv
    rw [hv, map_zero]
  · refine Submodule.eq_top_iff'.2 fun x => ?_
    obtain ⟨v, rfl⟩ := j.surjective x
    exact (h ▸ Submodule.mem_top : v ∈ W)

theorem main : Laws → Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), (N : F) ≠ 0 → (∀ x : Over.mk p ⟶ P.A, x ^ N = 1 → ∃ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt = x) ∧ ∀ U : Submodule F (EA P p N), (∀ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt ^ N = 1 → ∀ v v' : EA P p N, IsActOf P.A P.L (N : ℤ) θ v.sec v'.sec → v ∈ U → v' ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro hL hL2 S _ P F _ _ p N hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 fun e => hN (by rw [e, Nat.cast_zero])
  obtain ⟨Φ, e, hdim, hact, hmul, hcomm, hnd⟩ := GlobalTheory.ThetaRep.exists_projective_rep hL hL2 S P F p N hN
  refine ⟨fun x hx => (hact ⟨x, hx⟩).imp fun θ h => h.1, fun U hU => ?_⟩
  let G : Subgroup (Over.mk p ⟶ P.A) := (powMonoidHom N).ker
  have hcard : Nat.card G = N ^ (2 * P.g) := (hL.mulN _ P N hN1).2.2.2.2 F p hN
  let j : SecM P.A P.L N (Over.mk p) ≃+ EA P p N :=
    { toFun := fun v => SecMod.mk _ (SecM.toSec P.A v)
      invFun := fun v => SecM.ofSec P.A v.sec
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  refine irreducible_of_ringEquiv F Γ((Over.mk p).left, ⊤)
    (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv G _ _ j (fun c v => rfl)
    (fun a b => e ⟨a.1, a.2⟩ ⟨b.1, b.2⟩) (fun a => Φ ⟨a.1, a.2⟩) ?_ ?_ (fun a b => hmul _ _ _ rfl)
    (fun a b => (hcomm _ _).2) (fun a h => Subtype.ext (hnd ⟨a.1, a.2⟩ fun b => h ⟨b.1, b.2⟩)) U fun a v hv => ?_
  · rw [hcard, Nat.cast_pow]; exact pow_ne_zero _ hN
  · rw [hdim, hcard, ← pow_mul, mul_comm]
  · obtain ⟨θ, h₁, h₂⟩ := hact ⟨a.1, a.2⟩
    exact hU θ (by rw [h₁]; exact a.2) (j v) _ (h₂ v) hv

end GlobalTheory.ThetaIrred
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSectionsIrreducibleThetaGroupStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.abelian_sections_irreducible_theta_group : Laws → Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), (N : F) ≠ 0 → (∀ x : Over.mk p ⟶ P.A, x ^ N = 1 → ∃ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt = x) ∧ ∀ U : Submodule F (EA P p N), (∀ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt ^ N = 1 → ∀ v v' : EA P p N, IsActOf P.A P.L (N : ℤ) θ v.sec v'.sec → v ∈ U → v' ∈ U) → U = ⊥ ∨ U = ⊤ := by
  first | exact @GlobalTheory.ThetaIrred.main | exact GlobalTheory.ThetaIrred.main | (intros; apply GlobalTheory.ThetaIrred.main <;> assumption)
end
end
