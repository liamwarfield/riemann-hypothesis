module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelSmoothOfRelativeDimensionCharZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDescentSymmetricLinearisedBundle
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricLinearisationSquareDiagonalBundle
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LamIsoOfDoublingPullbackEqDiagonalSq
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRulePowComplex
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubrings
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleExistsOfAlgebraicInvariants

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricSqrtPrincipalSiegelFiniteEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricSqrtPrincipalSiegelFiniteEtale
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.SiegelSqrt
open GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

private theorem pull_isLB {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) : (L.pull F).IsLB := by
  refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
  · intro y _
    obtain ⟨i, hi⟩ := exists_chart hL (F y)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
  · intro J
    refine unit_ext fun y hy => ?_
    rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
    exact gm_self hL _ y (mem_pull.1 hy)
  · intro I J K
    refine unit_ext fun y hy => ?_
    rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
      gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
    exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)


section Transfer
variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}

def Labels {C : Type} [Group C] (A : Over S) [GrpObj A] (n : ℕ) (i : C →* (𝟙_ (Over S) ⟶ A)) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S),
    (∀ x : Over.mk t ⟶ A, x ^ n = 1 ↔ ∃ c, x = toUnit _ ≫ i c) ∧ ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1

theorem exists_pull_labels (h : IsGrpPullback A' A f φ) {C : Type} [Group C] (n : ℕ)
    (i : C →* (𝟙_ (Over S) ⟶ A)) (hi : Labels A n i) :
    ∃ i' : C →* (𝟙_ (Over S') ⟶ A'), (∀ c, (i' c).left ≫ φ = f ≫ (i c).left) ∧ Labels A' n i' := by
  have hmul : ∀ x y : 𝟙_ (Over S) ⟶ A, GlobalTheory.SiegelPull.secPull h (x * y) =
      GlobalTheory.SiegelPull.secPull h x * GlobalTheory.SiegelPull.secPull h y := by
    intro x y
    apply GlobalTheory.SiegelPull.push_injective h (𝟙_ (Over S'))
    rw [map_mul, GlobalTheory.SiegelPull.push_secPull', GlobalTheory.SiegelPull.push_secPull', GlobalTheory.SiegelPull.push_secPull',
      MonObj.comp_mul]
  refine ⟨MonoidHom.mk' (fun c => GlobalTheory.SiegelPull.secPull h (i c)) (fun a b => by rw [map_mul]; exact hmul _ _),
    fun c => GlobalTheory.SiegelPull.secPull_left h (i c), ?_⟩
  intro k _ _ t
  have hp := hi k (t ≫ f)
  have hinj := GlobalTheory.SiegelPull.push_injective h (Over.mk t)
  have key : ∀ c, pushHom h (Over.mk t) (toUnit (Over.mk t) ≫ GlobalTheory.SiegelPull.secPull h (i c)) =
      toUnit (Over.mk (t ≫ f)) ≫ i c := fun c => GlobalTheory.SiegelPull.push_secPull h (i c) (Over.mk t)
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun c hc => hp.2 c ?_⟩
  · have hpx : pushHom h (Over.mk t) x ^ n = 1 := by rw [← map_pow, hx, map_one]
    obtain ⟨c, hc⟩ := (hp.1 (pushHom h (Over.mk t) x)).1 hpx
    exact ⟨c, hinj ((key c).symm ▸ hc)⟩
  · rintro ⟨c, rfl⟩
    apply hinj
    rw [map_pow, map_one]
    exact (hp.1 _).2 ⟨c, key c⟩
  · rw [← key c]
    have hc' : toUnit (Over.mk t) ≫ GlobalTheory.SiegelPull.secPull h (i c) = 1 := hc
    rw [hc', map_one]

end Transfer

section Sieg
variable {h k : ℕ} {o o' : Type} [CommRing o] [CommRing o'] {ζ : o} {ζ' : o'} {S S' S'' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o'}

theorem diag_isLB (c : SiegPre h k ζ s) : c.diag.IsLB := by
  unfold SiegPre.diag
  exact pull_isLB c.isLB _

theorem diag_iso {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} {φ : c'.A.left ⟶ c.A.left}
    {φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left} (hs : IsSquare φ φ₂) (hw : LBIso c'.P (c.P.pull φ₂)) :
    LBIso c'.diag (c.diag.pull φ) := by
  unfold SiegPre.diag
  exact GlobalTheory.SiegelPull.diag_iso hs hw

theorem sqOf_of_pb {o₁ : Type} [CommRing o₁] {ζ₁ : o₁} {s₁ : S' ⟶ Sp o₁} {c₁ : SiegPre h k ζ₁ s₁}
    {c : SiegPre h k ζ s} {f : S' ⟶ S} {g : S'' ⟶ S'} {P : Out.PolAV S''} {φ : P.A.left ⟶ c₁.A.left}
    (hP : SqOf P c₁ g φ) (hc : SiegPB c₁ c f) : ∃ ψ, SqOf P c (g ≫ f) ψ := by
  have hLam : (abelian₂ P.A P.L).IsLB := by
    unfold abelian₂ cubeLB
    exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ P.isLB _ _
  obtain ⟨hPb, hg, φ₂', hsq', hiso'⟩ := hP
  obtain ⟨φ₁, φ₂, hpb₁, hsq₁, hiso₁, -⟩ := hc
  refine ⟨φ ≫ φ₁, hPb.comp hpb₁, hg, φ₂' ≫ φ₂, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hsq₁.1, ← Category.assoc, hsq'.1, Category.assoc]
  · rw [Category.assoc, hsq₁.2, ← Category.assoc, hsq'.2, Category.assoc]
  · exact LBIso.trans hLam (pull_isLB c₁.isLB _) (pull_isLB c.isLB _) hiso'
      (LBIso.trans (pull_isLB c₁.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _)
        (GlobalTheory.SiegelPullComp.iso_pull φ₂' hiso₁) (GlobalTheory.SiegelPullComp.iso_pull_pull c.isLB φ₂ φ₂'))

end Sieg

theorem pull_sieg {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S S' : Scheme.{0}} {s : S ⟶ Sp o} (s' : S' ⟶ Sp o)
    (f : S' ⟶ S) (hf : f ≫ s = s') (c : SiegPre h k ζ s) (hc : c.Principal) :
    ∃ c' : SiegPre h k ζ s', SiegPB c' c f ∧ c'.Principal := by
  obtain ⟨⟨c', hc'⟩, hpr⟩ := GlobalTheory.siegPre_pullback h k o ζ S S' s s' f c hf
  exact ⟨c', hc', hpr c' hc' hc⟩

theorem isUnit_two_sections (R : Type) [CommRing R] [Algebra ℚ R] : IsUnit ((2 : ℕ) : Γ(Sp R, ⊤)) := by
  have h2 : IsUnit ((2 : ℕ) : R) := by
    have hq : IsUnit ((2 : ℕ) : ℚ) := isUnit_iff_ne_zero.mpr (by norm_num)
    have := hq.map (algebraMap ℚ R)
    rwa [map_natCast] at this
  have := h2.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  rwa [map_natCast] at this

private theorem exists_ringHom_spMap_eq {R o : Type} [CommRing R] [CommRing o] (g : Sp R ⟶ Sp o) :
    ∃ β : o →+* R, spMap β = g :=
  ⟨(Spec.preimage g).hom, by unfold spMap; simp⟩

private theorem spMap_comp_var {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem exists_sqrt : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] (S : Scheme.{0}) (s : S ⟶ Sp o) (c : SiegPre h k ζ s) (f : Sp R ⟶ S), 2 ≤ k → IsUnit ζ → c.Principal → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (P : Out.PolAV (Sp R₁)) (φ : P.A.left ⟶ c.A.left), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) ∧ SqOf P c (spMap (algebraMap R R₁) ≫ f) φ ∧ TorsConst P.A 2 := by
  intro hL h k o _ ζ R _ _ _ S s c f hk hζ hc
  have two : ∀ (T : Type) [CommRing T] [Algebra ℚ T], IsUnit ((2 : ℕ) : T) := fun T _ _ => by
    have hq : IsUnit ((2 : ℕ) : ℚ) := isUnit_iff_ne_zero.mpr (by norm_num)
    have := hq.map (algebraMap ℚ T)
    rwa [map_natCast] at this
  have sq2 : ∀ x : Multiplicative (Fin (2 * h) → ZMod 2), x ^ 2 = 1 := fun x => by
    apply Multiplicative.toAdd.injective
    funext j
    rw [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat,
      show (2 : ZMod 2) = 0 from rfl, zero_mul]

  obtain ⟨β, hβ⟩ := exists_ringHom_spMap_eq (f ≫ s)
  obtain ⟨c₁, hpb₁, hc₁⟩ := pull_sieg (spMap β) f hβ.symm c hc
  have sm₁ := GlobalTheory.T.siegel_smoothOfRelativeDimension_charZero hL h k o ζ R β c₁ hk hζ

  obtain ⟨R₁, _, _, ⟨fin₁, et₁, ff₁⟩, lab₁⟩ := GlobalTheory.T.exists_finiteEtale_cover_constant_torsion R c₁.A h 2 c₁.ab sm₁ (two R)
  haveI : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R R₁
  letI : Algebra ℚ R₁ := ((algebraMap R R₁).comp (algebraMap ℚ R)).toAlgebra
  obtain ⟨c₂, hpb₂, hc₂⟩ := pull_sieg (spMap ((algebraMap R R₁).comp β)) (spMap (algebraMap R R₁))
    (spMap_comp_var β (algebraMap R R₁)).symm c₁ hc₁
  obtain ⟨φ₂, φ₂₂, hg₂, hsq₂, hiso₂, hlev₂⟩ := hpb₂
  obtain ⟨i, hi⟩ := lab₁ c₂.A φ₂ hg₂

  obtain ⟨R₂, _, _, ⟨fin₂, et₂, ff₂⟩, H91⟩ := GlobalTheory.T.exists_symmetric_linearisation_square_diagonalBundle hL h k o ζ R₁ ((algebraMap R R₁).comp β) c₂ h i hc₂
  haveI : IsNoetherianRing R₂ := Algebra.FiniteType.isNoetherianRing R₁ R₂
  letI : Algebra ℚ R₂ := ((algebraMap R₁ R₂).comp (algebraMap ℚ R₁)).toAlgebra
  obtain ⟨c₃, hpb₃, hc₃⟩ := pull_sieg (spMap ((algebraMap R₁ R₂).comp ((algebraMap R R₁).comp β)))
    (spMap (algebraMap R₁ R₂))
    (spMap_comp_var ((algebraMap R R₁).comp β) (algebraMap R₁ R₂)).symm c₂ hc₂
  obtain ⟨φ₃, φ₃₂, hg₃, hsq₃, hiso₃, hlev₃⟩ := hpb₃
  obtain ⟨i₃, hi₃l, hi₃⟩ := exists_pull_labels hg₃ 2 i hi
  have hLlb : (lbPow (c₂.diag.pull φ₃) 2).IsLB := isLB_lbPow (pull_isLB (diag_isLB c₂) _) 2
  obtain ⟨u, j, hu⟩ := H91 c₃.A φ₃ i₃ _ hg₃ hi₃l rfl

  obtain ⟨hmon, hfin, het, hsurj⟩ :=
    GlobalTheory.abelianScheme_id_pow_finite_etale_surjective (Sp R₂) c₃.A 2 c₃.ab (isUnit_two_sections R₂)
  obtain ⟨M, hM, hLM, hMinv⟩ := GlobalTheory.T.exists_descent_symmetric_linearised_bundle (Sp R₂) c₃.A c₃.A ((𝟙 c₃.A) ^ 2) _ i₃ _ hLlb hmon hfin het hsurj
    (fun x => by rw [MonObj.comp_pow, Category.comp_id, ← map_pow, sq2, map_one])
    (fun k _ _ t => ⟨fun x => by rw [MonObj.comp_pow, Category.comp_id]; exact (hi₃ k t).1 x, (hi₃ k t).2⟩) u j hu
  have hLam := GlobalTheory.T.lam_iso_of_doubling_pullback_eq_diagonal_sq hL h k o ζ R₂ _ c₃ M hc₃ hM
    (LBIso.trans (isLB_lbPow (diag_isLB c₃) 2) hLlb (pull_isLB hM _) (lbIso_lbPow (diag_iso hsq₃ hiso₃) 2) hLM)
  obtain ⟨P, φP, hP⟩ := GlobalTheory.T.exists_principalPolarization_symmetric_squareRoot hL h k o ζ R₂ _ c₃ M hc₃ (GlobalTheory.T.siegel_smoothOfRelativeDimension_charZero hL h k o ζ R₂ _ c₃ hk hζ) hM hLam hMinv

  obtain ⟨ψ₂, hψ₂⟩ := sqOf_of_pb hP ⟨φ₃, φ₃₂, hg₃, hsq₃, hiso₃, hlev₃⟩
  obtain ⟨ψ₁, hψ₁⟩ := sqOf_of_pb hψ₂ ⟨φ₂, φ₂₂, hg₂, hsq₂, hiso₂, hlev₂⟩
  obtain ⟨ψ₀, hψ₀⟩ := sqOf_of_pb hψ₁ hpb₁
  obtain ⟨iP, -, hiP⟩ := exists_pull_labels hP.1 2 i₃ hi₃
  letI : Algebra R R₂ := ((algebraMap R₁ R₂).comp (algebraMap R R₁)).toAlgebra
  haveI : IsScalarTower R R₁ R₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨R₂, inferInstance, inferInstance, P, ψ₀, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · first | exact Module.Finite.trans R₁ R₂ | infer_instance
  · first | exact Algebra.Etale.comp R R₁ R₂ | infer_instance
  · first | exact Module.FaithfullyFlat.trans R R₁ R₂ | infer_instance
  · have e : spMap (algebraMap R R₂) ≫ f =
        ((𝟙 _ ≫ spMap (algebraMap R₁ R₂)) ≫ spMap (algebraMap R R₁)) ≫ f := by
      rw [Category.id_comp, ← spMap_comp_var]
    rw [e]
    exact hψ₀
  · intro K _ _ x y hy
    obtain ⟨a, rfl⟩ := ((hiP K x).1 y).1 hy
    exact ⟨iP a, by rw [← map_pow, sq2, map_one], rfl⟩

end GlobalTheory.SiegelSqrt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricSqrtPrincipalSiegelFiniteEtaleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_sqrt_principal_siegel_finite_etale : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] (S : Scheme.{0}) (s : S ⟶ Sp o) (c : SiegPre h k ζ s) (f : Sp R ⟶ S), 2 ≤ k → IsUnit ζ → c.Principal → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (P : Out.PolAV (Sp R₁)) (φ : P.A.left ⟶ c.A.left), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) ∧ SqOf P c (spMap (algebraMap R R₁) ≫ f) φ ∧ TorsConst P.A 2 := by
  first | exact @GlobalTheory.SiegelSqrt.exists_sqrt | exact GlobalTheory.SiegelSqrt.exists_sqrt | (intros; apply GlobalTheory.SiegelSqrt.exists_sqrt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NonemptyRingHomComplex
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.KeyPow

namespace GlobalTheory.KeyRuleUnique

set_option autoImplicit false in
open Cardinal in
theorem _root_.GlobalTheory.KeyRuleUnique.nonempty_ringHom_complex (K : Type) [Field K] [CharZero K]
    [Countable K] : Nonempty (K →+* ℂ) := by
  let F := FractionRing (MvPolynomial ℝ K)
  let L := AlgebraicClosure F
  let i : K →+* L := (algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)
  haveI : CharZero L := (RingHom.charZero_iff i.injective).1 inferInstance
  have hK : #K ≤ 𝔠 := mk_le_aleph0.trans aleph0_le_continuum
  have hP : #(MvPolynomial ℝ K) = 𝔠 := by
    rw [MvPolynomial.cardinalMk_eq_max_lift]
    simp only [lift_id, mk_real]
    rw [max_eq_right hK, max_eq_left aleph0_le_continuum]
  have hF : #F = 𝔠 := by rw [FractionRing.cardinalMk, hP]
  have hL : #L = 𝔠 := by
    apply le_antisymm
    · calc #L ≤ max #F ℵ₀ := Algebra.IsAlgebraic.cardinalMk_le_max F L
        _ = 𝔠 := by rw [hF, max_eq_left aleph0_le_continuum]
    · rw [← hF]
      exact mk_le_of_injective (algebraMap F L).injective
  have hlt : ℵ₀ < #L := hL ▸ aleph0_lt_continuum
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_char_eq (K := L) (L := ℂ) 0 hlt
    (Cardinal.eq.1 (hL.trans mk_complex.symm))
  exact ⟨e.toRingHom.comp i⟩

end GlobalTheory.KeyRuleUnique
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RulePow
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyCl

theorem rule_pow : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → ThetaOne κ → ∀ (K : Type) [Field K] [CharZero K]
    (x y : KeyIn K) (j : ℕ), GlobalTheory.KeyPow.IsKeyPow y x j → κ K y = κ K x ^ j := by
  intro κ hH hF hT K _ _ x y j hp
  have hj : 1 ≤ j := by
    obtain ⟨_, hg, -⟩ := hp
    have := y.g_pos
    rcases Nat.eq_zero_or_pos j with rfl | h
    · omega
    · exact h
  obtain ⟨K₀, x₀, hK₀, hx₀⟩ := (GlobalTheory.T.keyData_descend_countable_subrings GlobalTheory.firstFiveLaws.1).2 K x
  obtain ⟨σ⟩ := GlobalTheory.KeyHouse.nonempty_ringHom_complex K₀
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.KeyPow.exists_isKeyPow _ x₀ j hj
  obtain ⟨x₁, hx₁⟩ := GlobalTheory.KeyPow.exists_keyPB_ring x₀ σ
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.KeyPow.exists_isKeyPow _ x₁ j hj
  have e₀ := GlobalTheory.KeyPow.keyPB_of_isKeyPow _ _ _ x₀ y₀ x y j hx₀ hy₀ hp
  have e₁ := GlobalTheory.KeyPow.keyPB_of_isKeyPow _ _ _ x₀ y₀ x₁ y₁ j hx₁ hy₀ hy₁
  have e := congrArg Units.val (GlobalTheory.T.thetaKeyRule_pow_complex κ hH hT x₁ y₁ j hy₁)
  rw [Units.val_pow_eq_pow_val, hF _ _ σ y₀ y₁ e₁, hF _ _ σ x₀ x₁ hx₁, ← map_pow] at e
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hF _ _ _ y₀ y e₀, hF _ _ _ x₀ x hx₀, ← map_pow, σ.injective e]

end GlobalTheory.KeyCl
end
