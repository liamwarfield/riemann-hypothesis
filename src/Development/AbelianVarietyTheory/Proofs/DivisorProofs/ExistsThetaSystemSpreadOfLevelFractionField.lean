module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemSpreadOfLevelFractionField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPullCongr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.MBDesc

theorem lbIso_pullComp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y) :
    LBIso (L.pull (g ≫ f)) ((L.pull f).pull g) :=
  ClosedPol.lbIso_pull_comp hL f g (g ≫ f) rfl

theorem lbIso_pull_congr {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {f g : Y ⟶ X} (h : f = g) :
    LBIso (L.pull f) (L.pull g) :=
  h ▸ RigidBundleGlue.LBIso.pull (GlobalTheory.lbIso_refl hL) f

end GlobalTheory.MBDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemSpreadOfLevelFractionField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SS

noncomputable section

namespace GlobalTheory.SpreadTheta

open GlobalTheory.ThetaDescent GlobalTheory.SymLevelDescent

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl


open NumberField in
theorem exists_base (R₁ : Type) [CommRing R₁] [IsDomain R₁] [CharZero R₁] (n m : ℕ) [NeZero n] [NeZero m]
    (hu : IsUnit (n : R₁)) (ζ : R₁) (hζ : IsPrimitiveRoot ζ m) :
    ∃ (o : Type) (_ : CommRing o) (b : o →+* R₁) (ze : oˣ), IsDedekindDomain o ∧ Algebra.FiniteType ℤ o ∧
      Function.Injective b ∧ IsUnit (n : o) ∧ b ze = ζ := by
  let K := CyclotomicField m ℚ
  haveI : IsCyclotomicExtension {m} ℚ K := CyclotomicField.isCyclotomicExtension m ℚ
  have hK := IsCyclotomicExtension.zeta_spec m ℚ K
  let pb := hK.integralPowerBasis
  have hmin : Polynomial.aeval ζ (minpoly ℤ pb.gen) = 0 := by
    have e₁ : minpoly ℤ pb.gen = Polynomial.cyclotomic m ℤ := by
      rw [IsPrimitiveRoot.integralPowerBasis_gen, Polynomial.cyclotomic_eq_minpoly hK (NeZero.pos m)]
      exact (minpoly.algebraMap_eq RingOfIntegers.coe_injective hK.toInteger).symm
    rw [e₁, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζ.isRoot_cyclotomic (NeZero.pos m)
  let σ : 𝓞 K →+* R₁ := (pb.lift ζ hmin).toRingHom
  have hσg : σ hK.toInteger = ζ := by
    have := pb.lift_gen ζ hmin
    rwa [IsPrimitiveRoot.integralPowerBasis_gen] at this
  have hσ : Function.Injective σ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have hb : RingHom.ker σ = ⊥ := by
      refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
      refine eq_bot_iff.2 fun a ha => ?_
      have : σ (algebraMap ℤ (𝓞 K) a) = 0 := ha
      rw [eq_intCast (algebraMap ℤ (𝓞 K)), map_intCast] at this
      exact (Ideal.mem_bot).2 (Int.cast_eq_zero.1 this)
    exact (RingHom.injective_iff_ker_eq_bot σ).2 hb |>.eq_iff.1 (hx.trans (map_zero σ).symm)
  have hun : IsUnit (σ (n : 𝓞 K)) := by rwa [map_natCast]
  let b : GlobalTheory.ZH.AwayBase K n →+* R₁ := IsLocalization.Away.lift (n : 𝓞 K) hun
  have hb : ∀ a, b (algebraMap (𝓞 K) _ a) = σ a := fun a => IsLocalization.Away.lift_eq _ hun a
  let z : GlobalTheory.ZH.AwayBase K n := algebraMap (𝓞 K) _ hK.toInteger
  have hz : IsPrimitiveRoot z m :=
    hK.toInteger_isPrimitiveRoot.map_of_injective (GlobalTheory.ZH.AwayBase.injective K n)
  refine ⟨GlobalTheory.ZH.AwayBase K n, inferInstance, b, (hz.isUnit (NeZero.ne m)).unit, inferInstance,
    by convert GlobalTheory.ZH.AwayBase.finiteType K n using 1 <;> first | rfl | exact Subsingleton.elim _ _, ?_, GlobalTheory.ZH.AwayBase.isUnit_natCast K n, ?_⟩
  · set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨k, a, e⟩ := IsLocalization.Away.surj (n : 𝓞 K) x
    have h := congrArg b e
    rw [map_mul, hx, zero_mul, hb] at h
    rw [(map_eq_zero_iff σ hσ).1 h.symm, map_zero] at e
    exact ((IsLocalization.Away.algebraMap_isUnit (n : 𝓞 K)).pow k).mul_left_eq_zero.1 e
  · show b z = ζ
    rw [hb, hσg]

theorem descends_to_fg_field_lb : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Q : Out.PolAV (Sp Ω)) (M : ℕ) (ze : oˣ), (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) → Nonempty (Out.Level Q M (unitOn (Units.map (algebraMap o Ω).toMonoidHom ze))) → ∃ (Ω₀ : Type) (_ : Field Ω₀) (_ : Algebra o Ω₀) (j : Ω₀ →ₐ[o] Ω) (R₀ : Subalgebra o Ω₀) (Q₀ : Out.PolAV (Sp Ω₀)) (φ : Q.A.left ⟶ Q₀.A.left), R₀.FG ∧ (∀ x : Ω₀, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b) ∧ Q₀.g = Q.g ∧ IsGrpPullback Q.A Q₀.A (spMap j.toRingHom) φ ∧ (letI := Q₀.isAb.comm; GlobalTheory.ZH.HypS Q₀.A Q₀.L) ∧ Nonempty (Out.Level Q₀ M (unitOn (Units.map (algebraMap o Ω₀).toMonoidHom ze))) ∧ LBIso Q.L (Q₀.L.pull φ) := by
  intro o K _ _ _ t M ze ⟨w, wd, hw, hwd, hsum, hpol, hadj⟩ ⟨lev⟩
  classical
  let β : o →+* K := algebraMap o K
  let act : Bool → (t.A ⟶ t.A) := fun j => cond j w wd
  obtain ⟨s₀, H₀⟩ := GlobalTheory.T.exists_finset_isProjOver_descends_to_subfield K (gen β ∅) t.A.left t.A.hom (GlobalTheory.ProjSpace.isProjOver_of_relAmple t.ample)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ (gen β s₀) (gen_mono β (Finset.empty_subset _)) (subset_gen β le_rfl)
  have : IsProper p₀ := isProper_of_isProjOver hp₀
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := GlobalTheory.grpObj_descends_to_large_subfield K (gen β s₀) (Over.mk p₀) t.A φ sq
  obtain ⟨s₂, H₂⟩ := GlobalTheory.T.exists_lineBundle_descent_to_subfield K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ t.L t.isLB sq
  obtain ⟨s₃, H₃⟩ := GlobalTheory.T.exists_descent_of_morphisms_to_subfield K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ X₀ p₀ Bool (fun j => (act j).left ≫ φ) sq
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, Over.w])
  obtain ⟨s₄, H₄⟩ := GlobalTheory.T.exists_descent_of_morphisms_to_subfield K (gen β s₀) (Sp (gen β s₀)) (Sp K) (𝟙 _) (𝟙 _) (spMap (gen β s₀).subtype) X₀ p₀
    (Fin (2 * t.g)) (fun a => (lev.pt a).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩)
    (fun a => by
      have e : (lev.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (lev.pt a)
      rw [Category.assoc, sq.w, ← Category.assoc, e]; simp)
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃ ∪ s₄
  have h : gen β s₀ ≤ gen β s := gen_mono β (fun x hx => by simp [s, hx])
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp (gen β s)) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : t.A.left ⟶ A₁.left := sq₁.lift φ (t.A.hom ≫ spMap (gen β s).subtype)
    (by rw [Category.assoc, spMap_subtype h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = t.A.hom ≫ spMap (gen β s).subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hL⟩ := H₂ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨f₁, hf₁⟩ := H₃ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨x₁, hx₁⟩ := H₄ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) (Sp (gen β s)) (𝟙 _) inc
    (spMap (gen β s).subtype) (IsPullback.of_vert_isIso ⟨by simp [inc]⟩) (spMap_subtype h) (by simp)
  let act₁ : Bool → (A₁ ⟶ A₁) := fun j =>
    Over.homMk (sq₁.lift (f₁ j) A₁.hom (by rw [(hf₁ j).2, sq₁.w])) (sq₁.lift_snd _ _ _)
  let pt₁ : Fin (2 * t.g) → (Out.baseOver (Sp (gen β s)) ⟶ A₁) := fun a =>
    Over.homMk (sq₁.lift (x₁ a) (𝟙 _) (by rw [(hx₁ a).2]; simp)) (sq₁.lift_snd _ _ _)
  have hpt : ∀ a, (lev.pt a).left ≫ ψ = spMap (gen β s).subtype ≫ (pt₁ a).left := fun a => by
    have e : (lev.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (lev.pt a)
    have e₁ : (pt₁ a).left ≫ φ₁ = x₁ a := sq₁.lift_fst _ _ _
    have e₂ : (pt₁ a).left ≫ A₁.hom = 𝟙 _ := sq₁.lift_snd _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁]
      exact ((hx₁ a).1.symm.trans (congrArg _ e₁.symm)).trans (Category.assoc _ _ _).symm
    · rw [Category.assoc, hψ₂, ← Category.assoc, e]
      refine (Category.id_comp _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      exact ((congrArg _ e₂).trans (Category.comp_id _)).symm
  have hact : ∀ j, (act j).left ≫ ψ = ψ ≫ (act₁ j).left := fun j => by
    have e₁ : (act₁ j).left ≫ φ₁ = f₁ j := sq₁.lift_fst _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁, Category.assoc, e₁, (hf₁ j).1]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hψ₂]
  obtain ⟨hab, hdim⟩ := GlobalTheory.T.abelian_scheme_descent_smooth_dimension _ K (gen β s).subtype A₁ t.A ψ hG t.isAb
  obtain ⟨hr, hs, hk⟩ := GlobalTheory.T.rigidified_symmetric_kernelTrivial_descend_fieldExt _ K (gen β s).subtype A₁ t.A ψ L₁ t.L hab hG hL₁ t.isLB hL
  have hamp := GlobalTheory.AmpleDescent.relAmple_of_fieldExtension _ K (gen β s).subtype A₁ t.A ψ L₁ t.L hab hG hL₁ t.isLB hL
    t.ample
  letI : Algebra o (gen β s) := (β.codRestrict _ (mem_gen β s)).toAlgebra
  obtain ⟨R₀, hfg, hfrac⟩ := exists_fg_subalgebra β s
  refine ⟨gen β s, inferInstance, inferInstance, ⟨(gen β s).subtype, fun _ => rfl⟩, R₀,
    ⟨A₁, hab, t.g, hdim _ t.smoothDim, L₁, hL₁, hr t.rigid, hs t.sym, hamp, hk t.ktriv⟩, ψ, hfg, hfrac, rfl, hG, ?_, ?_, hL⟩
  · have := t.isAb.comm
    have := hab.comm
    exact hypS_descend (gen β s).subtype hab hG hL₁ t.isLB hL (hact true).symm (hact false).symm hw hwd hsum hpol hadj
  · exact level_descend (gen β s).subtype t A₁ hab _ L₁ hL₁ _ _ _ _ hG hL M _ lev pt₁ hpt

end GlobalTheory.SpreadTheta

namespace GlobalTheory.Mum

theorem exists_thetaSys_spread : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [CharZero R₁] (A₁ : PolAV (Sp (FractionRing R₁))), (letI := A₁.isAb.comm; GlobalTheory.ZH.HypS A₁.A A₁.L) → ∀ (n k j : ℕ), n.Prime → Odd n → 2 ≤ k → 1 ≤ j → IsUnit (n : R₁) → ∀ (ζ : R₁ˣ), ReciprocityTheory.ChartRestriction.G.Out.Level A₁ ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap R₁ (FractionRing R₁)).toMonoidHom ζ)) → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : GlobalTheory.ZH.ArithBase o Ω) (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (b : o →+* R₁) (e : Ω →+* FractionRing R₁) (φ : A₁.A.left ⟶ ρS.P.A.left), S.g = A₁.g ∧ S.N = (n ^ k) ^ 2 ∧ S.r = n ^ j ∧ (∀ x : o, e (algebraMap o Ω x) = algebraMap R₁ (FractionRing R₁) (b x)) ∧ IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ ∧ LBIso A₁.L (ρS.P.L.pull φ) := by
  intro R₁ _ _ _ A₁ hS n k j hn ho hk hj hu ζ lev
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  haveI : NeZero n := ⟨hn.ne_zero⟩
  haveI : NeZero ((n ^ j * (n ^ k) ^ 2) ^ 2) := ⟨by have := hn.pos; positivity⟩
  let F := FractionRing R₁
  have hζ : IsPrimitiveRoot (ζ : R₁) ((n ^ j * (n ^ k) ^ 2) ^ 2) :=
    (IsPrimitiveRoot.map_iff_of_injective (f := algebraMap R₁ F) (IsFractionRing.injective R₁ F)).1
      (IsPrimitiveRoot.coe_units_iff.2 ((GlobalTheory.SymLevelDescent.isPrimitiveRoot_unitOn_iff _ _).1 lev.prim))
  obtain ⟨o, _, b, ze, hded, hft, hbi, hun, hbz⟩ := GlobalTheory.SpreadTheta.exists_base R₁ n _ hu ζ hζ
  letI : Algebra o F := ((algebraMap R₁ F).comp b).toAlgebra
  have hze : Units.map (algebraMap R₁ F).toMonoidHom ζ = Units.map (algebraMap o F).toMonoidHom ze :=
    Units.ext (by show algebraMap R₁ F ζ = algebraMap R₁ F (b ze); rw [hbz])
  have lev₀ : Nonempty (Out.Level A₁ ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap o F).toMonoidHom ze))) :=
    ⟨hze ▸ lev⟩
  obtain ⟨Ω₀, _, _, jj, R₀, Q₀, ψ, hR₀, hfr, hg, hψ, hS₀, ⟨lev₁⟩, hLψ⟩ :=
    GlobalTheory.SpreadTheta.descends_to_fg_field_lb o F A₁ _ ze hS lev₀
  have hcomp : ∀ x : o, jj (algebraMap o Ω₀ x) = algebraMap R₁ F (b x) := fun x => jj.commutes x
  haveI : CharZero Ω₀ := RingHom.charZero jj.toRingHom
  haveI : GlobalTheory.ZH.ArithBase o Ω₀ := ⟨hded, hft, inferInstance, fun x y hxy =>
    hbi (IsFractionRing.injective R₁ F (by rw [← hcomp, ← hcomp, hxy]))⟩
  have hM : IsUnit (((n ^ j * (n ^ k) ^ 2) ^ 2 : ℕ) : o) := by
    push_cast
    exact ((hun.pow _).mul ((hun.pow _).pow _)).pow _
  obtain ⟨R, P', φ₁, lev', hle, hR, hg', hS', hp₁, hl₁, -⟩ :=
    GlobalTheory.GenSpread.polAV_spreads_out o Ω₀ R₀ hR₀ hfr Q₀ _ ze hM hS₀ lev₁ hL
  have hfr' : ∀ x : Ω₀, ∃ a ∈ R, ∃ c ∈ R, x = a / c := fun x => by
    obtain ⟨a, ha, c, hc, e⟩ := hfr x
    exact ⟨a, hle ha, c, hle hc, e⟩
  obtain ⟨S, ρ, h, φ₂, -, hN, hr, hgS, hp₂, hl₂, -⟩ :=
    GlobalTheory.ThetaReal.exists_thetaSys_real hL hL₂ o Ω₀ R hR hfr' P' n k j ze hn ho hk hj hun hS' lev'
  have e : spMap S.R.val.toRingHom ≫ spMap (Subalgebra.inclusion h).toRingHom = spMap R.val.toRingHom :=
    GlobalTheory.SpreadTheta.spMap_comp_spMap _ _
  have w : φ₁ ≫ P'.A.hom = (Q₀.A.hom ≫ spMap S.R.val.toRingHom) ≫ spMap (Subalgebra.inclusion h).toRingHom := by
    rw [hp₁.1.w, Category.assoc, e]
  let χ := hp₂.1.lift φ₁ (Q₀.A.hom ≫ spMap S.R.val.toRingHom) w
  have hχ₁ : χ ≫ φ₂ = φ₁ := hp₂.1.lift_fst _ _ _
  have hχ₂ : χ ≫ ρ.P.A.hom = Q₀.A.hom ≫ spMap S.R.val.toRingHom := hp₂.1.lift_snd _ _ _
  have hχ : IsGrpPullback Q₀.A ρ.P.A (spMap S.R.val.toRingHom) χ :=
    IsGrpPullback.cancel hp₂ (hp₁.congr e.symm hχ₁.symm) hχ₂
  have hP := P'.isLB
  have c₁ : LBIso A₁.L ((P'.L.pull φ₁).pull ψ) :=
    LBIso.trans A₁.isLB (pull_isLB Q₀.isLB _) (pull_isLB (pull_isLB hP _) _) hLψ
      (GlobalTheory.RigidBundleGlue.LBIso.pull hl₁ ψ)
  have c₂ : LBIso ((P'.L.pull φ₁).pull ψ) (P'.L.pull ((ψ ≫ χ) ≫ φ₂)) :=
    LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB hP _)
      (GlobalTheory.MBDesc.lbIso_pullComp hP φ₁ ψ).symm
      (GlobalTheory.MBDesc.lbIso_pull_congr hP (by rw [Category.assoc, hχ₁]))
  have c₃ : LBIso (P'.L.pull ((ψ ≫ χ) ≫ φ₂)) (ρ.P.L.pull (ψ ≫ χ)) :=
    LBIso.trans (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) (pull_isLB ρ.P.isLB _)
      (GlobalTheory.MBDesc.lbIso_pullComp hP φ₂ (ψ ≫ χ)) (GlobalTheory.RigidBundleGlue.LBIso.pull hl₂.symm (ψ ≫ χ))
  refine ⟨o, Ω₀, inferInstance, inferInstance, inferInstance, inferInstance, S, ρ, b, jj.toRingHom, ψ ≫ χ,
    hgS.trans (hg'.trans hg), hN, hr, hcomp, (hψ.comp hχ).congr (GlobalTheory.SpreadTheta.spMap_comp_spMap _ _) rfl, ?_⟩
  exact LBIso.trans A₁.isLB (pull_isLB (pull_isLB hP _) _) (pull_isLB ρ.P.isLB _) c₁
    (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB ρ.P.isLB _) c₂ c₃)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemSpreadOfLevelFractionFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaSystem_spread_of_level_fractionField : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [CharZero R₁] (A₁ : PolAV (Sp (FractionRing R₁))), (letI := A₁.isAb.comm; GlobalTheory.ZH.HypS A₁.A A₁.L) → ∀ (n k j : ℕ), n.Prime → Odd n → 2 ≤ k → 1 ≤ j → IsUnit (n : R₁) → ∀ (ζ : R₁ˣ), ReciprocityTheory.ChartRestriction.G.Out.Level A₁ ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap R₁ (FractionRing R₁)).toMonoidHom ζ)) → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : GlobalTheory.ZH.ArithBase o Ω) (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (b : o →+* R₁) (e : Ω →+* FractionRing R₁) (φ : A₁.A.left ⟶ ρS.P.A.left), S.g = A₁.g ∧ S.N = (n ^ k) ^ 2 ∧ S.r = n ^ j ∧ (∀ x : o, e (algebraMap o Ω x) = algebraMap R₁ (FractionRing R₁) (b x)) ∧ IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ ∧ LBIso A₁.L (ρS.P.L.pull φ) := by
  first | exact @GlobalTheory.Mum.exists_thetaSys_spread | exact GlobalTheory.Mum.exists_thetaSys_spread | (intros; apply GlobalTheory.Mum.exists_thetaSys_spread <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourthPowerUnderIsogeny
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourthPowerUnderIsogeny
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaShift

section Reindex

variable {X : Scheme.{0}}

theorem res_res {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (h3 : W ≤ U) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom x) =
      (X.presheaf.map (homOfLE h3).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem unitsRes_res {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (h3 : W ≤ U) (x : Γ(X, U)ˣ) :
    res h2 (res h1 x) = res h3 x :=
  Units.ext (res_res h1 h2 h3 (x : Γ(X, U)))

theorem chart_le (L : LB X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) :=
  fun _ hx => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx 0

theorem chart_ge (L : LB X) (k : PUnit → L.ι) :
    LB.wchart L (fun _ : PUnit => 𝟙 X) k ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k PUnit.unit) :=
  fun _ hx => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx PUnit.unit

end Reindex

section Reindex2

variable {X : Scheme.{0}}

theorem basicOpen_res' {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) :
    X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) = V ⊓ X.basicOpen f :=
  Scheme.basicOpen_res X f (homOfLE h).op

theorem g_finOne (L : LB X) (n : ℕ) (i j : Fin 1 → L.ι) :
    (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ))).g i j =
      res (inf_le_inf (chart_le L i) (chart_le L j)) ((lbPow L n).g (fun _ => i 0) (fun _ => j 0)) := by
  simp only [lbPow, LB.LinComb, Fin.prod_univ_one, Finset.univ_unique, Finset.prod_singleton, map_zpow]
  congr 1
  exact (unitsRes_res _ _ _ _).symm

def secFinOne {L : LB X} {n : ℕ} (s : (lbPow L n).Sec) : Out.H0 L n where
  f j := (X.presheaf.map (homOfLE (chart_le L j)).op).hom (s.f (fun _ => j 0))
  compat i j := by
    have K := inf_le_inf (chart_le L i) (chart_le L j)
    have hc := congrArg (X.presheaf.map (homOfLE K).op).hom (s.compat (fun _ => i 0) (fun _ => j 0))
    have hl : LB.wchart L (fun _ : Fin 1 => 𝟙 X) i ⊓ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤
        LB.wchart L (fun _ : Fin 1 => 𝟙 X) i := inf_le_left
    have hr : LB.wchart L (fun _ : Fin 1 => 𝟙 X) i ⊓ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤
        LB.wchart L (fun _ : Fin 1 => 𝟙 X) j := inf_le_right
    have hl0 : LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => i 0) ⊓ LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) ≤
        LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => i 0) := inf_le_left
    have hr0 : LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => i 0) ⊓ LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) ≤
        LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) := inf_le_right
    have e1 := res_res (chart_le L i) hl (K.trans hl0) (s.f (fun _ => i 0))
    have e2 := res_res hl0 K (K.trans hl0) (s.f (fun _ => i 0))
    have e3 := res_res (chart_le L j) hr (K.trans hr0) (s.f (fun _ => j 0))
    have e4 := res_res hr0 K (K.trans hr0) (s.f (fun _ => j 0))
    have e5 := RingHom.map_mul (X.presheaf.map (homOfLE K).op).hom
      ((lbPow L n).g (fun _ => i 0) (fun _ => j 0)).val ((X.presheaf.map (homOfLE hr0).op).hom (s.f (fun _ => j 0)))
    have e6 := congrArg Units.val (g_finOne L n i j)
    exact e1.trans (e2.symm.trans (hc.trans (e5.trans (congrArg₂ (· * ·) e6.symm (e4.trans e3.symm)))))

theorem nonzeroLocus_secFinOne {L : LB X} {n : ℕ} (s : (lbPow L n).Sec) :
    Out.nonzeroLocus (secFinOne s) = Out.nonzeroLocus s := by
  apply le_antisymm
  · refine iSup_le fun (j : Fin 1 → L.ι) => ?_
    exact (basicOpen_res' (chart_le L j) _).le.trans (inf_le_right.trans (le_iSup (fun k => X.basicOpen (s.f k)) _))
  · refine iSup_le fun (k : PUnit → L.ι) => ?_
    refine le_trans ?_ (le_iSup (fun j => X.basicOpen ((secFinOne s).f j)) (fun _ => k PUnit.unit))
    exact (le_inf ((X.basicOpen_le _).trans (chart_ge L k)) le_rfl).trans (basicOpen_res' (chart_le L _) _).ge

end Reindex2

section Theta

variable {A : Over (Sp ℂ)} [GrpObj A] {M : LB A.left} {A' : Over (Sp ℂ)} [GrpObj A'] {M' : LB A'.left} {g : ℕ}

theorem differentiable_hermForm_left (Hm : Matrix (Fin g) (Fin g) ℂ) (a : Fin g → ℂ) :
    Differentiable ℂ (fun z : Fin g → ℂ => hermForm Hm z a) := by
  simp only [hermForm, dotProduct]
  fun_prop

theorem isThetaFn_shift (u : HolUnif A M g) (u' : HolUnif A' M' g) {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hH : Hm.IsHermitian) {χ : u.Λ → ℂ} {χ' : u'.Λ → ℂ} (h : u.Λ ≤ u'.Λ) (a : Fin g → ℂ)
    (hχ : ∀ l : u.Λ, χ l = χ' (Submodule.inclusion h l) *
      Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm a l).im))
    {θ : (Fin g → ℂ) → ℂ} (hθ : u'.IsThetaFn Hm χ' 4 θ) :
    u.IsThetaFn Hm χ 4 (fun z => θ (z + a) * Complex.exp (-(4 * Real.pi) * hermForm Hm z a)) := by
  refine ⟨(hθ.1.comp (differentiable_id.add_const a)).mul
    (((differentiable_hermForm_left Hm a).const_mul _).cexp), fun l z => ?_⟩
  have hl : z + (l : Fin g → ℂ) + a = (z + a) + ((Submodule.inclusion h l : u'.Λ) : Fin g → ℂ) := by
    simp only [Submodule.coe_inclusion]; abel
  have e1 : hermForm Hm (z + a) ((Submodule.inclusion h l : u'.Λ) : Fin g → ℂ) =
      hermForm Hm z l + hermForm Hm a l := by
    simp [hermForm, add_dotProduct]
  have e2 : hermForm Hm (z + l) a = hermForm Hm z a + hermForm Hm l a := by
    simp [hermForm, add_dotProduct]
  have e3 : hermForm Hm ((Submodule.inclusion h l : u'.Λ) : Fin g → ℂ) ((Submodule.inclusion h l : u'.Λ) : Fin g → ℂ) =
      hermForm Hm l l := rfl
  have e4 : hermForm Hm l a = (starRingEnd ℂ) (hermForm Hm a l) := GlobalTheory.LatticeHom.hermForm_swap_of_isHermitian hH a l
  have hw : (starRingEnd ℂ) (hermForm Hm a l) = hermForm Hm a l - 2 * Complex.I * ((hermForm Hm a l).im : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  show θ (z + (l : Fin g → ℂ) + a) * _ = _ * (θ (z + a) * _)
  rw [hl, hθ.2, e1, e3, e2, e4, hw, hχ l]
  have key : Complex.exp (Real.pi * (hermForm Hm z l + hermForm Hm a l) + Real.pi / 2 * hermForm Hm l l) ^ 4 *
      Complex.exp (-(4 * Real.pi) * (hermForm Hm z a + (hermForm Hm a l - 2 * Complex.I * ((hermForm Hm a l).im : ℂ)))) =
      Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm a l).im) ^ 4 *
      Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) ^ 4 *
      Complex.exp (-(4 * Real.pi) * hermForm Hm z a) := by
    simp only [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [mul_pow, mul_pow, mul_pow]
  linear_combination (χ' (Submodule.inclusion h l) ^ 4 * θ (z + a)) * key

end Theta


open GlobalTheory.LatticeHom in
theorem exists_morphism_affine_cover : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → (∀ θ, u.IsThetaFn Hm χ 4 θ → ∃ s, u.IsFnPow 4 s θ) →
    ∀ (P : Out.PolAV (Sp ℂ)) (u' : HolUnif P.A P.L g) (χ' : u'.Λ → ℂ) (h : u.Λ ≤ u'.Λ) (a : Fin g → ℂ),
    P.g = g → u'.IsAH Hm χ' →
    (∀ l : u.Λ, χ l = χ' (Submodule.inclusion h l) *
      Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm a l).im)) →
    ∃ ψ : A.left ⟶ P.A.left, ψ ≫ P.A.hom = A.hom ∧ (∀ z, (u.ex z).left ≫ ψ = (u'.ex (z + a)).left) ∧
      ∀ x : A.left, ∃ (s : Out.H0 M 4) (V : P.A.left.Opens), x ∈ Out.nonzeroLocus s ∧ IsAffineOpen V ∧
        Out.nonzeroLocus s = ψ ⁻¹ᵁ V := by
  intro g A _ hA M u Hm χ hM hAH hsec P u' χ' h a hg hAH' hχ
  subst hg
  have hsm : Smooth A.hom := hA.smooth
  have hred : IsReduced A.left := isReduced_of_smooth_complex _ A.hom hsm
  obtain ⟨-, -, -, -, -, -, -, hsecfn, -⟩ := AnyAppellHumbert.isAH_properties abelianSchemeLaws_all.1
    abelianSchemeLaws_all.2 (fun S P M hM => AbLaw.CubeAssembly.cube_gen S P M hM) thetaUnifAV_all P u' Hm χ' hAH'
  obtain ⟨m, t, hcov, hD⟩ := veryAmple_lbPow abelianSchemeLaws_all.1.ample ℂ P 4 le_rfl
  choose θ hθ hθt using fun j => ((hsecfn 4).1 (t j)).exists
  have hG : ∀ z, Complex.exp (-(4 * Real.pi) * hermForm Hm z a) ≠ 0 := fun z => Complex.exp_ne_zero _
  choose s hs using fun j => hsec _ (isThetaFn_shift u u' hAH'.1 h a hχ (hθ j))
  let Φ : (𝟙_ (Over (Sp ℂ)) ⟶ A) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    fun y => u'.ex (Function.surjInv u.ex_onto y + a)
  have hΦ : ∀ z, Φ (u.ex z) = u'.ex (z + a) := fun z => by
    have h1 : Function.surjInv u.ex_onto (u.ex z) - z ∈ u.Λ := by
      rw [← u.ker]
      have := u.ex_add (Function.surjInv u.ex_onto (u.ex z) - z) z
      rw [sub_add_cancel, Function.surjInv_eq u.ex_onto] at this
      exact mul_eq_right.1 this.symm
    have := SectionTheta.ex_add_lattice u' (z + a) ⟨_, h h1⟩
    rw [← this]
    show u'.ex _ = u'.ex _
    congr 1
    simp only
    abel
  have hmem : ∀ j z, ⊤ ≤ (u'.ex z).left ⁻¹ᵁ Out.nonzeroLocus (t j) ↔ θ j z ≠ 0 :=
    fun j => le_preimage_nonzeroLocus_iff u' P.isLB (hθt j)
  have hmemA : ∀ j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Out.nonzeroLocus (s j) ↔
      θ j (z + a) * Complex.exp (-(4 * Real.pi) * hermForm Hm z a) ≠ 0 :=
    fun j => le_preimage_nonzeroLocus_iff u hM (hs j)
  obtain ⟨f, hf, -⟩ := existsUnique_hom_of_locally_regular existsUnique_point_of_ringHom
      (eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom) P.A A hred inferInstance Φ fun y => by
    obtain ⟨z₀, rfl⟩ := u.ex_onto y
    obtain ⟨i, hi⟩ := TorusEnd.exists_top_le_preimage_of_iSup_eq_top (u'.ex (z₀ + a)).left _ hcov
    obtain ⟨haff, r, hrr, hgen⟩ := hD i
    obtain ⟨U, ρ, hU0, hU⟩ := exists_regular_quotients u hM hs i (mul_ne_zero ((hmem i _).1 hi) (hG z₀))
    refine ⟨U, _, hU0, haff, fun y' hy' => ?_, fun φ => ?_⟩
    · obtain ⟨z, rfl⟩ := u.ex_onto y'
      rw [hΦ]
      exact (hmem i _).2 (left_ne_zero_of_mul (hU z hy').1)
    · obtain ⟨Q, rfl⟩ := hgen φ
      refine ⟨MvPolynomial.eval₂ (RingHom.comp (A.hom.appLE ⊤ _ le_top).hom
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) ρ Q, fun y' hy' => ?_⟩
      obtain ⟨z, rfl⟩ := u.ex_onto y'
      have h1 := left_ne_zero_of_mul (hU z hy').1
      have h2 := right_ne_zero_of_mul (hU z hy').1
      rw [hΦ, TorusEnd.valAt'_eval₂ _ _ hy', TorusEnd.valAt'_eval₂ _ _ ((hmem i _).2 h1)]
      congr 2
      funext j
      rw [(hU z hy').2 j, valAt'_eq_div_of_mul u' P.isLB (hθt i) (hθt j) (r j) (hrr j) h1,
        mul_div_mul_right _ _ h2]
  have hfe : ∀ z, (u.ex z).left ≫ f.left = (u'.ex (z + a)).left := fun z => by
    rw [← Over.comp_left, hf, hΦ]
  have heq : ∀ j, Out.nonzeroLocus (s j) = f.left ⁻¹ᵁ Out.nonzeroLocus (t j) := fun j => by
    have hpt : ∀ x' : Sp ℂ ⟶ A.left, x' ≫ A.hom = 𝟙 _ → (⊤ ≤ x' ⁻¹ᵁ Out.nonzeroLocus (s j) ↔
        ⊤ ≤ (x' ≫ f.left) ⁻¹ᵁ Out.nonzeroLocus (t j)) := by
      intro x' hx'
      obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x' hx')
      have hz' : (u.ex z).left = x' := by rw [hz]; rfl
      rw [← hz', hfe, hmemA, hmem]
      exact ⟨left_ne_zero_of_mul, fun h0 => mul_ne_zero h0 (hG z)⟩
    exact le_antisymm (ComplexPoints.opens_le_of_complexPoints A.hom _ _ fun x' hx' => (hpt x' hx').1)
      (ComplexPoints.opens_le_of_complexPoints A.hom _ _ fun x' hx' => (hpt x' hx').2)
  refine ⟨f.left, Over.w f, hfe, fun x => ?_⟩
  have hx : x ∈ f.left ⁻¹ᵁ (⨆ j, Out.nonzeroLocus (t j)) := by rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  refine ⟨secFinOne (s j), Out.nonzeroLocus (t j), ?_, (hD j).1, ?_⟩
  · rw [nonzeroLocus_secFinOne, heq]
    exact hj
  · rw [nonzeroLocus_secFinOne, heq]

end GlobalTheory.ThetaShift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourthPowerUnderIsogenyStatement
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_fourth_power_under_isogeny : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → (∀ θ, u.IsThetaFn Hm χ 4 θ → ∃ s, u.IsFnPow 4 s θ) →
    ∀ (P : Out.PolAV (Sp ℂ)) (u' : HolUnif P.A P.L g) (χ' : u'.Λ → ℂ) (h : u.Λ ≤ u'.Λ) (a : Fin g → ℂ),
    P.g = g → u'.IsAH Hm χ' →
    (∀ l : u.Λ, χ l = χ' (Submodule.inclusion h l) *
      Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm a l).im)) →
    ∃ ψ : A.left ⟶ P.A.left, ψ ≫ P.A.hom = A.hom ∧ (∀ z, (u.ex z).left ≫ ψ = (u'.ex (z + a)).left) ∧
      ∀ x : A.left, ∃ (s : Out.H0 M 4) (V : P.A.left.Opens), x ∈ Out.nonzeroLocus s ∧ IsAffineOpen V ∧
        Out.nonzeroLocus s = ψ ⁻¹ᵁ V := by
  first | exact @GlobalTheory.ThetaShift.exists_morphism_affine_cover | exact GlobalTheory.ThetaShift.exists_morphism_affine_cover | (intros; apply GlobalTheory.ThetaShift.exists_morphism_affine_cover <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymLam
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SymBiextHalf

open GlobalTheory.CechPic GlobalTheory.SymLin GlobalTheory.LamOfDouble


open FreeAbelianGroup in
set_option maxHeartbeats 1000000 in
theorem exists_lin {K : Type} [Field K] [IsAlgClosed K] (hG : Out.GlobalFnsSt) {A : Over (Sp K)} [GrpObj A]
    [IsCommMonObj A] (hA : IsAbelianScheme A) {M : LB A.left} (hM : M.IsLB)
    (H : ∀ T : Over (Sp K),
      (∀ x y : T ⟶ A, y * y = 1 → pull (y * x).left (cls _ hM) = pull x.left (cls _ hM) + pull y.left (cls _ hM)) ∧
      (∀ y : T ⟶ A, y * y = 1 → pull y.left (cls _ hM) + pull y.left (cls _ hM) = 0) ∧
      ∀ x : T ⟶ A, pull (x⁻¹).left (cls _ hM) = pull x.left (cls _ hM))
    {n : ℕ} (i : (Multiplicative (Fin n → ZMod 2)) →* (𝟙_ (Over (Sp K)) ⟶ A)) (L : LB A.left) (hLe : L = lbPow M 2) :
    ∃ (u : ∀ c, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ((toUnit A ≫ i c) * 𝟙 A).left] ![1, -1]))
      (j : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![1, -1])),
      (∀ c, (u c).IsGen) ∧ (∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
        (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') ((toUnit A ≫ i c) * 𝟙 A).left))) ∧ j.IsGen ∧
      ∀ c (T : Over (Sp K)) (x : T ⟶ A) (z : T.left) (J), Good L z J →
        val (u c) x.left z J * val j ((toUnit T ≫ i c) * x).left z J =
          val j x.left z J * val (u c⁻¹) (x⁻¹).left z J := by
  obtain ⟨v, j, a, rv, rj, h₁, h₂, h₃⟩ := core hG hA hM H
    (fun n => i (bas n)) (fun n => by rw [← map_mul, mul_self_eq, map_one])
  subst hLe
  have hb' : ∀ m, ∃ b : Γ(Sp K, ⊤)ˣ, b * b = a m := fun m => by
    obtain ⟨b, e⟩ := IsAlgClosed.exists_pow_nat_eq ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (a m).val : K) two_pos
    have e' : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom b * (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom b =
        (a m).val := by
      rw [← map_mul, ← pow_two, e]
      exact Iso.hom_inv_id_apply _ _
    have hu := isUnit_of_mul_isUnit_left (e' ▸ Units.isUnit _)
    exact ⟨hu.unit, Units.ext e'⟩
  choose b hb' using hb'
  let ρ : Multiplicative (Fin n → ZMod 2) →* Monoid.End (Vals M A.left) :=
    { toFun := fun q => pl (tr (i q)).left
      map_one' := MonoidHom.ext fun f => by rw [map_one, tr_one]; exact pl_id f
      map_mul' := fun q q' => MonoidHom.ext fun f => by
        show _ = pl (tr (i q)).left (pl (tr (i q')).left f)
        rw [pl_pl, ← Over.comp_left, tr_tr, mul_comm q, map_mul] }
  have ρe : ∀ q f, ρ q f = pl (tr (i q)).left f := fun _ _ => rfl
  have ρb : ∀ (x : A ⟶ A) (f : Vals M (Sp K)), pl x.left (pl A.hom f) = pl A.hom f := fun x f => by
    rw [pl_pl, Over.w]
  have ii : ∀ q, i q * i q = 1 := fun q => by rw [← map_mul, mul_self_eq, map_one]
  obtain ⟨u, hu, hu'⟩ := exists_cocycle ρ (fun q f =>
      Rep M (of (𝟙 _) + of (𝟙 _) - of (tr (i q)).left - of (tr (i q)).left) f ∧
      f * ρ q j = j * pl (GrpObj.inv : A ⟶ A).left f)
    ⟨(map_one (uv M A.left) ▸ rep_uv 1).form (by rw [map_one, tr_one, Over.id_left]; abel),
      by simp⟩
    (fun q q' f f' hf hf' => ⟨(hf.1.mul (hf'.1.pull (tr (i q)).left)).form (by
        simp only [map_add (f := _), map_sub, map_of_apply, Category.comp_id]
        rw [← Over.comp_left, tr_tr, mul_comm q, map_mul]; abel), by
      have e : pl (GrpObj.inv : A ⟶ A).left (ρ q f') = ρ q (pl (GrpObj.inv : A ⟶ A).left f') := by
        rw [ρe, ρe, pl_pl, pl_pl, ← Over.comp_left, ← Over.comp_left, tr_inv (ii q)]
      rw [map_mul ρ, Monoid.End.coe_mul, Function.comp_apply, _root_.mul_assoc, ← map_mul, hf'.2, map_mul,
        ← _root_.mul_assoc, hf.2, map_mul, e, _root_.mul_assoc]⟩)
    (fun n => v n * pl A.hom (uv _ _ (b n)⁻¹))
    (fun n => ⟨((rv n).mul ((rep_uv _).pull A.hom)).form (by
        simp only [map_zero, add_zero]), by
      rw [ρe, map_mul, ρb, mul_right_comm, h₃, _root_.mul_assoc]⟩)
    (fun n => by
      rw [ρe, map_mul, ρb, _root_.mul_mul_mul_comm, h₁, ← hb',
        ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← mul_inv, mul_inv_cancel, map_one, map_one])
    (fun n m => by
      rw [ρe, ρe, map_mul, map_mul, ρb, ρb, _root_.mul_mul_mul_comm, h₂]
      ac_rfl)
  have hL' : (lbPow M 2).IsLB := LB.isLB_linComb hM _ _
  let D : Vals (lbPow M 2) A.left →* Vals M A.left := dn M (𝟙 _) ((2 : ℕ) : ℤ) A.left
  have Dpl : ∀ (x : A.left ⟶ A.left) f, D (pl x f) = pl x (D f) := fun _ _ => rfl
  have Dinj : ∀ {E} {f f'}, Rep (lbPow M 2) E f → Rep (lbPow M 2) E f' → D f = D f' →
      f = f' := fun {E f f'} hf hf' e => by
    obtain ⟨a, ha⟩ := ((hf.mul hf'.inv).form (add_neg_cancel _)).zero hL'
    have : uv M A.left a = 1 := by
      have := congrArg D ha
      rw [map_mul, map_inv, e, mul_inv_cancel] at this
      exact this.symm
    exact mul_inv_eq_one.1 (ha.trans (uv_eq_one hM _ this))
  have down : ∀ (x : A.left ⟶ A.left) f, Rep M (of (𝟙 _) + of (𝟙 _) - of x - of x) f →
      ∃ t : LB.Gen (LB.LinComb (lbPow M 2) (K := Fin 2) ![𝟙 A.left, x] ![1, -1]), t.IsGen ∧
        D (vals t) = f := fun x f hf =>
    Rep.down hM (𝟙 _) ((2 : ℕ) : ℤ) (K := Fin 2) ![𝟙 A.left, x] ![1, -1] (hf.form (by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id]; module))
  choose U hU eU using fun q => down _ _ (hu q).1
  obtain ⟨J₀, hJ₀, eJ⟩ := down (GrpObj.inv : A ⟶ A).left j rj
  have r₂ : ∀ {x : A.left ⟶ A.left} {t : LB.Gen (LB.LinComb (lbPow M 2) (K := Fin 2) ![𝟙 A.left, x] ![1, -1])},
      t.IsGen → ∀ y : A.left ⟶ A.left, Rep _ (of y - of (y ≫ x)) (pl y (vals t)) := fun ht y =>
    ((rep_vals ht).pull y).form (by simp [Fin.sum_univ_two, sub_eq_add_neg])
  have r₁ := fun q => pl_id (M := lbPow M 2) _ ▸ r₂ (hU q) (𝟙 _)
  have r₃ := pl_id (M := lbPow M 2) _ ▸ r₂ hJ₀ (𝟙 _)
  simp only [Category.id_comp] at r₁ r₃
  refine ⟨U, J₀, hU, fun q q' => corr_of_val hL' fun y J hJ => ?_, hJ₀, fun q T x z J hJ => ?_⟩
  · have e := Dinj (r₁ (q * q')) (((r₁ q).mul (r₂ (hU q') (tr (i q)).left)).form (by
      rw [← Over.comp_left, tr_tr, mul_comm q, map_mul]; abel)) (by rw [map_mul D, Dpl, eU, eU, eU, hu', ρe])
    rw [val_mul hJ, val_pull hJ]
    exact congrFun (congrFun (congrFun (congrFun e _) (𝟙 _)) y) ⟨J, hJ⟩
  · have e := Dinj ((r₁ q).mul (r₂ hJ₀ (tr (i q)).left)) ((r₃.mul (r₂ (hU q) (GrpObj.inv : A ⟶ A).left)).form (by
      rw [← Over.comp_left, ← Over.comp_left, tr_inv (ii q)]; abel)) (by
        rw [map_mul D, map_mul D, Dpl, Dpl, eU, eJ, ← ρe, (hu q).2])
    rw [inv_eq_of_mul_eq_one_right (mul_self_eq q), ← comp_tr x (i q), ← comp_inv' x, Over.comp_left, Over.comp_left]
    exact congrFun (congrFun (congrFun (congrFun e _) x.left) z) ⟨J, hJ⟩

theorem lam_iso (hL : Out.Laws) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {H : LB A.left} (hH : H.IsLB) (ha : Out.RelAmple A H) {P : LB (G2 A).left} (hP : P.IsLB)
    (bP : Biadd (cls P hP)) (sy : ∀ (T : Over (Sp R)) (x y : T ⟶ A), ev (cls P hP) x y = ev (cls P hP) y x)
    {L : LB A.left} (hLB : L.IsLB)
    (hiso : LBIso (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) 2) (L.pull ((𝟙 A) ^ 2 : A ⟶ A).left)) :
    LBIso (abelian₂ A L) P := by
  have hM : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hΛ : (abelian₂ A L).IsLB := LB.isLB_linComb hLB _ _
  have hN : (LB.div (abelian₂ A L) P).IsLB := LB.isLB_div hΛ hP
  have hPow : (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) 2).IsLB := LB.isLB_linComb hM _ _
  set l := cls L hLB with hl
  set p := cls P hP with hp
  have eΛ : cls _ hΛ = lam l (fst A A) (snd A A) := cls_cube_two hLB _ _ hΛ
  have eN : ∀ (T : Over (Sp R)) (x y : T ⟶ A), ev (cls _ hN) x y = lam l x y - ev p x y := by
    intro T x y
    rw [cls_div hΛ hP, eΛ, ev, map_sub, pull_lam, lift_fst, lift_snd]
    rfl
  have r₁ : ∀ (T : Over (Sp R)) (y : T ⟶ A), ev p 1 y = 0 := fun T y => by
    have := (bP T 1 1 y).1
    rw [_root_.mul_one] at this
    exact left_eq_add.1 this
  have n₁ : ∃ t : ((LB.div (abelian₂ A L) P).pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 ((eN _ _ _).trans ?_)
    rw [r₁, lam_one_left, sub_zero]
  have n₂ : ∃ t : ((LB.div (abelian₂ A L) P).pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 ((eN _ _ _).trans ?_)
    rw [sy, r₁, lam_one_right, sub_zero]
  have bN := biadd_of_axes hL.globalFns hA _ hH ha _ hN n₁ n₂
  have dbl : ∀ (T : Over (Sp R)) (x : T ⟶ A), pull (x * x).left l = ev p x x + ev p x x := by
    intro T x
    have e : 2 • ev p (𝟙 A) (𝟙 A) = pull ((𝟙 A) ^ 2 : A ⟶ A).left l :=
      (cls_lbPow hM 2 hPow).symm.trans ((cls_eq_iff hPow (pull_isLB hLB _)).2 hiso)
    have e' := congrArg (pull x.left) e
    rw [map_nsmul, pull_ev, ← pull_comp, ← Over.comp_left, pow_two, MonObj.comp_mul, Category.comp_id,
      two_smul] at e'
    exact e'.symm
  have z : ∀ (T : Over (Sp R)) (x y : T ⟶ A), ev (cls _ hN) (x ^ 4) y = 0 := by
    intro T x y
    have a : ev (cls _ hN) (x * x) (y * y) = 0 := by
      have o₂ := dbl T 1
      rw [_root_.mul_one, r₁] at o₂
      rw [eN, lam, _root_.mul_mul_mul_comm, dbl, dbl, dbl, o₂]
      simp only [(bP T _ _ _).1, (bP T _ _ _).2, sy T y x]
      abel
    rw [show x ^ 4 = x * x * (x * x) by rw [← pow_two, ← pow_two, ← pow_mul]]
    simp only [(bN T _ _ _).1, (bN T _ _ _).2] at a ⊢
    exact a
  have fin := triv_of_pull_pow hL A hA _ hH ha 4 (by norm_num) _ hN n₂ (by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 (Eq.trans ?_ (z _ (fst A A) (snd A A)))
    have e : ((𝟙 A) ^ 4 : A ⟶ A) ▷ A = lift (fst A A ^ 4) (snd A A) := by
      ext
      · rw [whiskerRight_fst, lift_fst, MonObj.comp_pow, Category.comp_id]
      · rw [whiskerRight_snd, lift_snd]
    rw [e]
    rfl)
  rw [← cls_eq_zero_iff hN, cls_div hΛ hP, sub_eq_zero] at fin
  exact (cls_eq_iff hΛ hP).1 fin

theorem exists_labels {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) :
    ∃ (n : ℕ) (i : Multiplicative (Fin n → ZMod 2) →* (𝟙_ (Over (Sp K)) ⟶ A)),
      ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp K),
        (∀ x : Over.mk t ⟶ A, x ^ 2 = 1 ↔ ∃ c, x = toUnit _ ≫ i c) ∧ ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1 := by
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim K A hA
  have hn : IsUnit ((2 : ℕ) : Γ(Sp K, ⊤)) := by
    have := (IsUnit.mk0 ((2 : ℕ) : K) (by norm_num)).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨v, hv, hfree⟩ := TorsionCover.exists_free (G := 𝟙_ (Over (Sp K)) ⟶ A) (r := 2 * g) (n := 2) two_ne_zero
    fun d hd => TorsionCover.card_torsion A hA hg (𝟙 (Sp K)) (by
      rintro h
      rw [Nat.cast_eq_zero] at h
      subst h
      simp at hd)
  let i := TorsionCover.combHom v hv
  refine ⟨2 * g, i, fun k _ _ t => ?_⟩
  have hinj : ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1 := fun c hc => by
    obtain ⟨C, -, hC⟩ := TorsionCover.exists_clopen_eq_one A hA hn (i c) (TorsionCover.hom_pow_eq_one i c)
    have h1 := (hC _ _).1 hc
    have h2 : 𝟙 _ ≫ i c = 1 := (hC _ (𝟙 _)).2 (by
      rintro y -
      obtain ⟨w⟩ : Nonempty (Sp k) := inferInstance
      have := h1 ⟨w, rfl⟩
      rwa [Subsingleton.elim (α := Sp K) y _])
    rw [Category.id_comp] at h2
    exact Multiplicative.toAdd.injective (hfree _ h2)
  exact ⟨TorsionCover.pow_eq_one_iff_of_card (r := 2 * g)
    (TorsionCover.card_torsion A hA hg t (TorsionCover.natCast_ne_zero hn t)) ((preHom (toUnit _)).comp i) hinj, hinj⟩

theorem exists_sym_lam : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → ∃ L : LB A.left, L.IsLB ∧ Out.Sym A L ∧ LBIso (abelian₂ A L) PP := by
  rintro K _ _ _ A _ _ hA P hP hs hb
  have hL : Out.Laws := GlobalTheory.lawsAndExpansions.1.1
  obtain ⟨H, hH, ha⟩ := GlobalTheory.ProjFinite.exists_relAmple_of_isProjBy
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme K A hA)
  rw [← cls_eq_zero_iff (LB.isLB_linComb hP _ _), cls_linComb hP] at hs hb
  simp only [Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    one_smul, neg_smul] at hs hb
  set p := cls P hP with hp
  have sy : ∀ (T : Over (Sp K)) (x y : T ⟶ A), ev p x y = ev p y x := fun T x y => by
    have e := congrArg (pull (lift y x).left) hs
    rw [map_add (f := _), map_neg, map_zero, pull_id, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd,
      add_neg_eq_zero] at e
    exact e
  have b₁ : ∀ (T : Over (Sp K)) (x x' y : T ⟶ A), ev p (x * x') y = ev p x y + ev p x' y := fun T x x' y => by
    have e := congrArg (pull (lift x (lift x' y)).left) hb
    simp only [map_add (f := _), map_neg, map_zero, ← pull_comp, ← Over.comp_left, comp_lift, MonObj.comp_mul, lift_fst,
      lift_snd, lift_snd_assoc] at e
    unfold ev
    rw [← sub_eq_zero, ← e]
    abel
  have bP : Biadd p := fun T x x' y => ⟨b₁ T x x' y, by rw [sy, b₁, sy T x, sy T x']⟩
  have hM : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hm : ∀ (T : Over (Sp K)) (x : T ⟶ A), pull x.left (cls _ hM) = ev p x x := fun T x =>
    (pull_ev x p (𝟙 A) (𝟙 A)).trans (by rw [Category.comp_id])
  have h1 : ∀ (T : Over (Sp K)) (y : T ⟶ A), ev p 1 y = 0 := fun T y => by simpa using b₁ T 1 1 y
  have hi : ∀ (T : Over (Sp K)) (x y : T ⟶ A), ev p x⁻¹ y = -ev p x y := fun T x y =>
    eq_neg_of_add_eq_zero_left (by rw [← b₁, inv_mul_cancel, h1])
  have h2 : ∀ (T : Over (Sp K)) (y x : T ⟶ A), y * y = 1 → ev p y x + ev p y x = 0 := fun T y x hy => by
    rw [← b₁, hy, h1]
  obtain ⟨n, i, li⟩ := exists_labels A hA
  obtain ⟨u, j, huj⟩ := exists_lin hL.globalFns hA hM (fun T => by
    simp only [hm]
    refine ⟨fun x y hy => ?_, fun y hy => h2 T y y hy, fun x => by rw [hi, sy, hi, neg_neg]⟩
    rw [b₁, sy T y, sy T x, b₁, b₁, sy T x y]
    linear_combination (norm := abel) h2 T y x hy) i _ rfl
  have hn : IsUnit ((2 : ℕ) : Γ(Sp K, ⊤)) := by
    have := (IsUnit.mk0 ((2 : ℕ) : K) (by norm_num)).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨p₁, p₂, p₃, p₄⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective _ A 2 hA hn
  have hψ : ∀ {T : Over (Sp K)} (x : T ⟶ A), x ≫ ((𝟙 A) ^ 2 : A ⟶ A) = x ^ 2 := fun x => by
    rw [MonObj.comp_pow, Category.comp_id]
  obtain ⟨L, hLB, iM, sM⟩ := GlobalTheory.LinDescent.exists_descent_symmetric _ A A ((𝟙 A) ^ 2) _ i _
    (LB.isLB_linComb hM _ _) p₁ p₂ p₃ p₄ (fun a => by rw [hψ, TorsionCover.hom_pow_eq_one])
    (fun k _ _ t => ⟨fun x => by rw [hψ]; exact (li k t).1 x, (li k t).2⟩) u j huj
  refine ⟨L, hLB, fun s => ⟨⊤, trivial, ?_⟩, lam_iso hL hA hH ha hP bP sy hLB iM⟩
  have e : cls L hLB = pull (GrpObj.inv : A ⟶ A).left (cls L hLB) := (cls_eq_iff hLB (pull_isLB hLB _)).2 sM
  rw [← cls_eq_zero_iff (LB.isLB_linComb hLB _ _), cls_linComb hLB]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
  rw [pull_comp, ← e, add_neg_cancel]

end GlobalTheory.SymBiextHalf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGermPrimeIdealMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem ideal_map_stalk_isPrime_of_closedPoint : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ x : G₁.left, G₁.hom x = closedPoint R' → ∀ q : Ideal R', q.IsPrime → (Ideal.map ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) q).IsPrime := by
  intro R' _ _ _ _ G₁ _ _ hG x hx q hq
  have := hG.smooth
  have := hG.geomConnected
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp G₁.left.isBasis_affineOpens
    (show x ∈ (⊤ : G₁.left.Opens) from trivial)
  replace hU : IsAffineOpen U := hU
  let A := Γ(G₁.left, U)
  let ψ : R' →+* A := (G₁.left.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom.comp
    ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)
  have hφ : (G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom) = (G₁.left.presheaf.germ U x hxU).hom.comp ψ := by
    ext r
    rw [← TopCat.Presheaf.germ_res G₁.left.presheaf (homOfLE le_top : U ⟶ ⊤) x hxU]
    rfl
  rw [hφ, ← Ideal.map_map]
  letI : Algebra R' A := ψ.toAlgebra

  have hnu : ∀ r ∈ q, ¬ IsUnit ((G₁.left.presheaf.germ U x hxU).hom (ψ r)) := by
    intro r hr hu
    have key := DFunLike.congr_fun hφ r
    simp only [RingHom.comp_apply] at key
    rw [← key] at hu
    have hu := (Scheme.mem_basicOpen G₁.left _ x (show x ∈ (⊤ : G₁.left.Opens) from trivial)).mpr hu
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at hu
    change G₁.hom x ∈ PrimeSpectrum.basicOpen r at hu
    rw [hx] at hu
    exact hu (IsLocalRing.le_maximalIdeal hq.ne_top hr)
  set P := hU.primeIdealOf ⟨x, hxU⟩
  letI : Algebra A (G₁.left.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk G₁.left.presheaf ⟨x, hxU⟩
  haveI := hU.isLocalization_stalk ⟨x, hxU⟩
  have hle : Ideal.map ψ q ≤ P.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, ← IsLocalization.AtPrime.to_map_mem_maximal_iff (G₁.left.presheaf.stalk x) P.asIdeal]
    exact hnu r hr
  have hI : (Ideal.map ψ q).IsPrime := by
    haveI := hq
    have hne : Ideal.map ψ q ≠ ⊤ := fun h => P.isPrime.ne_top (top_le_iff.mp (h ▸ hle))
    let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := R') A q
    haveI : Nontrivial (A ⧸ Ideal.map (algebraMap R' A) q) := Ideal.Quotient.nontrivial_iff.mpr hne
    haveI : Nontrivial (TensorProduct R' A (R' ⧸ q)) := e.symm.toEquiv.nontrivial
    have eSp : Spec.map (CommRingCat.ofHom (algebraMap R' A)) = hU.fromSpec ≫ G₁.hom := by
      apply ext_of_isAffine
      have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R' A))
      rw [← Iso.eq_comp_inv] at h1
      rw [h1, Scheme.Hom.comp_appTop]
      change _ = _ ≫ hU.fromSpec.app ⊤
      rw [IsAffineOpen.fromSpec_app_of_le hU ⊤ le_top]
      rw [show (homOfLE le_top : hU.fromSpec ⁻¹ᵁ ⊤ ⟶ ⊤) = 𝟙 _ from rfl]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
      ext r
      simp [ψ, RingHom.algebraMap_toAlgebra]
    haveI : IsIntegral (Spec (CommRingCat.of (R' ⧸ q))) :=
      (affine_isIntegral_iff _).mpr (inferInstanceAs (IsDomain (R' ⧸ q)))
    haveI : IsIntegral (pullback G₁.hom (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⧸ q))))) :=
      GlobalTheory.isIntegral_pullback_of_smooth _ _
    let j := (pullbackSpecIso R' A (R' ⧸ q)).inv ≫ (pullback.congrHom eSp rfl).hom ≫
      (pullbackRightPullbackFstIso G₁.hom _ hU.fromSpec).inv ≫ pullback.snd _ _
    haveI : Nonempty (Spec (CommRingCat.of (TensorProduct R' A (R' ⧸ q)))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum _))
    haveI := isIntegral_of_isOpenImmersion j
    haveI hdom := (affine_isIntegral_iff _).mp this
    haveI : IsDomain (A ⧸ Ideal.map (algebraMap R' A) q) := MulEquiv.isDomain _ e.toRingEquiv.toMulEquiv
    exact (Ideal.Quotient.isDomain_iff_prime _).mp this
  exact IsLocalization.isPrime_of_isPrime_disjoint P.asIdeal.primeCompl _ _ hI
    (Set.disjoint_left.mpr fun a ha h => ha (hle h))

end GlobalTheory.Mum
end
