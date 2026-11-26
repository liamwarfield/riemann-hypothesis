module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTrivialOfSamePolarization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelDiagonalRestrictionOfSymmetricTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelDiagonalRestrictionOfSymmetricTrivial
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AbDual

theorem memKL_diag_of_triv_ev_of_symm : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) → GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) a := by
  intro R _ _ G _ hA P hP h0l h0r hsym T a ha
  have hs : (swap P).IsLB := pull_isLB hP _
  have hadd := (isAdditive_iff hP).1 (CubeNoeth.isAdditive_of_triv_axes hA hA hP h0l h0r)
  have hadd' := (isAdditive_iff hs).1 (CubeNoeth.isAdditive_swap_of_triv_axes hA hA hP h0l h0r)
  have hadd2 : ∀ (Y : Over (Sp R)) (u v w : Y ⟶ G), evc hP u (v * w) = evc hP u v + evc hP u w := by
    intro Y u v w
    rw [← evc_swap hP hs, ← evc_swap hP hs, ← evc_swap hP hs]
    exact hadd' Y v w u
  have hc : cls P hP = cls (swap P) hs := (cls_eq_iff hP hs).2 hsym
  have hsymm : ∀ (Y : Over (Sp R)) (u v : Y ⟶ G), evc hP u v = evc hP v u := by
    intro Y u v
    rw [← evc_swap hP hs u v]
    simp only [evc, hc]
  have hL : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  have hcL : ∀ (Y : Over (Sp R)) (u : Y ⟶ G), CechPic.pull u.left (cls _ hL) = evc hP u u := by
    intro Y u
    rw [cls_ev hP, pull_evc, Category.comp_id]
  have hx0 : evc hP (fst T G ≫ a) (snd T G) = 0 := by
    have e := congrArg (CechPic.pull (lift (snd T G) (fst T G)).left) ((triv_ev_iff hP _ _).1 ha)
    rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e
  have hD : (Out.translDiff G _ a).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc'⟩ := exists_pull_eq_zero (evc hP a a) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  have e₁ := pull_translDiff hL a hD (fst T G) (snd T G)
  rw [lift_fst_snd, Over.id_left, pull_id, hcL, hcL] at e₁
  have e₂ : cls _ hD = CechPic.pull (fst T G).left (evc hP a a) := by
    rw [e₁, pull_evc, hadd, hadd2, hadd2, hsymm _ (snd T G) (fst T G ≫ a), hx0]
    abel
  rw [cls_pull hD, e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T G).left ⁻¹ᵁ V).ι ≫ (fst T G).left) (fun z ↦ z.2) hc'

end GlobalTheory.AbDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelDiagonalRestrictionOfSymmetricTrivialStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_kernel_diagonal_restriction_of_symmetric_trivial : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) → GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) a := by
  first | exact @GlobalTheory.AbDual.memKL_diag_of_triv_ev_of_symm | exact GlobalTheory.AbDual.memKL_diag_of_triv_ev_of_symm | (intros; apply GlobalTheory.AbDual.memKL_diag_of_triv_ev_of_symm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionWithRangeInOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionWithRangeInOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.HenselLift

theorem exists_lift_mem_open (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R']
    (hc : IsAdicComplete (maximalIdeal R') R') (ρ : R →+* R') (U : Over (Sp R)) (hU : Smooth U.hom)
    (x₀ : Sp (ResidueField R') ⟶ U.left) (hx : x₀ ≫ U.hom = spMap ((residue R').comp ρ))
    (O : U.left.Opens) (hO : Set.range x₀ ⊆ O) :
    ∃ a : Sp R' ⟶ U.left, a ≫ U.hom = spMap ρ ∧ Set.range a ⊆ O := by
  obtain ⟨y, hy⟩ : ∃ y, x₀ (closedPoint (ResidueField R')) = y := ⟨_, rfl⟩
  obtain ⟨α, hs, hα⟩ := GlobalTheory.HenselZero.exists_formallySmooth_stalk (O := CommRingCat.of R) U.hom y
  obtain ⟨χ₀, hχ₀⟩ := GlobalTheory.HenselZero.exists_factor_stalk (T := CommRingCat.of (ResidueField R')) x₀ (y := y) hy
  letI := α.hom.toAlgebra
  letI := ρ.toAlgebra
  haveI : Algebra.FormallySmooth R (U.left.presheaf.stalk y) := hs
  haveI := hc
  have e₁ : α ≫ χ₀ = CommRingCat.ofHom ((residue R').comp ρ) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, reassoc_of% hχ₀, hx]
  let f : U.left.presheaf.stalk y →ₐ[R] R' ⧸ maximalIdeal R' :=
    { χ₀.hom with commutes' := fun r => congrArg (fun g => g.hom r) e₁ }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := maximalIdeal R') f
  have hg' : CommRingCat.ofHom g.toRingHom ≫ CommRingCat.ofHom (residue R') = χ₀ := by
    ext a
    exact congr($hg a)
  refine ⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y, ?_, ?_⟩
  · rw [Category.assoc, ← hα, ← Spec.map_comp]
    congr 1
    ext r
    exact g.commutes r
  · have hcl : (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y) (closedPoint R') = y := by
      have h1 : Spec.map (CommRingCat.ofHom (residue R')) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
          U.left.fromSpecStalk y = x₀ := by
        rw [← Spec.map_comp_assoc, hg', hχ₀]
      have h2 := congrArg (fun h => h (closedPoint (ResidueField R'))) h1
      simp only [Scheme.Hom.comp_apply] at h2
      rw [hy] at h2
      refine Eq.trans ?_ h2
      exact congrArg (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y)
        (comap_closedPoint (residue R')).symm
    rintro _ ⟨p, rfl⟩
    refine Specializes.mem_open ((specializes_closedPoint p).map (Scheme.Hom.continuous _)) O.isOpen ?_
    rw [hcl]
    exact hO ⟨_, hy⟩

end GlobalTheory.HenselLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionWithRangeInOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_residueFieldPoint_smooth_completeLocal : ∀ (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'], IsAdicComplete (maximalIdeal R') R' → ∀ (ρ : R →+* R') (U : Over (Sp R)), Smooth U.hom → ∀ (x₀ : Sp (ResidueField R') ⟶ U.left), x₀ ≫ U.hom = spMap ((residue R').comp ρ) → ∀ O : U.left.Opens, Set.range x₀ ⊆ O → ∃ a : Sp R' ⟶ U.left, a ≫ U.hom = spMap ρ ∧ Set.range a ⊆ O := by
  first | exact @GlobalTheory.HenselLift.exists_lift_mem_open | exact GlobalTheory.HenselLift.exists_lift_mem_open | (intros; apply GlobalTheory.HenselLift.exists_lift_mem_open <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimSys
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.TateCompare

variable {p : ℕ} [Fact p.Prime] {D : Datum p}
variable {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_zsmul (I : TateIsoO D k Q act e) (n : ℕ) (c : ℤ) (x : D.La) : I.ev n (c • x) = I.ev n x ^ c := by
  let φ : Multiplicative D.La →* Q := MonoidHom.mk' (fun y => I.ev n y.toAdd) (fun a b => I.add n _ _)
  exact map_zpow φ (Multiplicative.ofAdd x) c

theorem ev_eq_iff (I : TateIsoO D k Q act e) {n : ℕ} (hn : 0 < n) (hc : n.Coprime p) {x y : D.La} :
    I.ev n x = I.ev n y ↔ ∃ z, x = y + n • z := by
  constructor
  · intro h
    have h₁ : I.ev n y * I.ev n (x - y) = I.ev n y * 1 := by
      rw [← I.add, add_sub_cancel, h, _root_.mul_one]
    obtain ⟨z, hz⟩ := (I.ker n hn hc _).1 (mul_left_cancel h₁)
    exact ⟨z, by rw [← hz, add_sub_cancel]⟩
  · rintro ⟨z, rfl⟩
    exact I.ev_add_nsmul hn hc _ _

theorem exists_lift (I₁ I₂ : TateIsoO D k Q act e) (n : ℕ) :
    ∃ g : D.La →+ D.La, 0 < n → n.Coprime p → ∀ y, I₁.ev n (g y) = I₂.ev n y := by
  by_cases h : 0 < n ∧ n.Coprime p
  swap
  · exact ⟨0, fun h₁ h₂ => (h ⟨h₁, h₂⟩).elim⟩
  obtain ⟨hn, hc⟩ := h
  have := D.freeLa
  let b := Module.Free.chooseBasis ℤ D.La
  have hpre : ∀ y, ∃ x, I₁.ev n x = I₂.ev n y := fun y =>
    (I₁.onto n hn hc _).1 ((I₂.onto n hn hc _).2 ⟨y, rfl⟩)
  choose f hf using hpre
  let g : D.La →ₗ[ℤ] D.La := b.constr ℤ (fun i => f (b i))
  refine ⟨g.toAddMonoidHom, fun _ _ y => ?_⟩
  show I₁.ev n (g y) = I₂.ev n y
  have hy : y ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simp only [g, Module.Basis.constr_basis, hf]
  | zero =>
    rw [map_zero, (I₁.ker n hn hc 0).2 ⟨0, (smul_zero _).symm⟩, (I₂.ker n hn hc 0).2 ⟨0, (smul_zero _).symm⟩]
  | add x y _ _ hx hy => rw [map_add (f := _), I₁.add, I₂.add, hx, hy]
  | smul c x _ hx => rw [map_zsmul, ev_zsmul, ev_zsmul, hx]

theorem exists_mult (I₁ I₂ : TateIsoO D k Q act e) (n : ℕ) :
    ∃ u : ℕ, 0 < n → n.Coprime p → I₁.ζ n ^ u = I₂.ζ n := by
  by_cases h : 0 < n ∧ n.Coprime p
  swap
  · exact ⟨0, fun h₁ h₂ => (h ⟨h₁, h₂⟩).elim⟩
  obtain ⟨hn, hc⟩ := h
  have : NeZero n := ⟨hn.ne'⟩
  have h₁ : IsPrimitiveRoot ((I₁.ζ n : kˣ) : k) n := IsPrimitiveRoot.coe_units_iff.2 (I₁.ζ_prim n hn hc)
  have h₂ : ((I₂.ζ n : kˣ) : k) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, (I₂.ζ_prim n hn hc).pow_eq_one, Units.val_one]
  obtain ⟨u, -, hu⟩ := h₁.eq_pow_of_pow_eq_one h₂
  exact ⟨u, fun _ _ => Units.ext (by rw [Units.val_pow_eq_pow_val, hu])⟩

end GlobalTheory.UPel.HT.TateCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendAdicCompletionLocalization
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendAdicCompletionLocalization
open IsLocalRing TensorProduct

noncomputable section

namespace GlobalTheory

def intDerivationOfLeibniz {A M : Type} [CommRing A] [AddCommGroup M] {instZA : Algebra ℤ A}
    {_ : Module A M} {instZM : Module ℤ M} (f : A →+ M) (h : ∀ a b, f (a * b) = a • f b + b • f a) :
    Derivation ℤ A M :=
  { toFun := f
    map_add' := f.map_add
    map_smul' := fun c x => by
      simp only [RingHom.id_apply]
      obtain rfl : instZM = AddCommGroup.toIntModule M := Subsingleton.elim _ _
      obtain rfl : instZA = Ring.toIntAlgebra A := Subsingleton.elim _ _
      exact map_zsmul f c x
    map_one_eq_zero' := by
      have h1 := h 1 1
      rw [one_mul, one_smul] at h1
      simpa using h1
    leibniz' := h }

theorem derivation_extend_completion_localization_atPrime (S : Type) [CommRing S] (P : Ideal S)
    [P.IsPrime] (d : Derivation ℤ S S) :
    ∃ D : Derivation ℤ (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P))
      (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)),
      ∀ x, D (algebraMap S _ x) = algebraMap S _ (d x) := by
  obtain ⟨D', hD'⟩ := derivation_extend_localization_atPrime ℤ S (Localization.AtPrime P) P
    (intDerivationOfLeibniz
      ((algebraMap S (Localization.AtPrime P)).toAddMonoidHom.comp d.toLinearMap.toAddMonoidHom)
      (fun a b => by simp [d.leibniz, Algebra.smul_def]))
  have hadd : ∀ y z, BK.complDerFun (maximalIdeal (Localization.AtPrime P)) D' (y + z) =
      BK.complDerFun _ D' y + BK.complDerFun _ D' z := fun y z => by
    refine AdicCompletion.ext_evalₐ fun n => ?_
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime P)) (n + 1) y)
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime P)) (n + 1) z)
    rw [BK.evalₐ_complDerFun _ D' (r := r + t) (by rw [map_add (f := _), map_add (f := _), hr, ht]), map_add (f := _),
      map_add, map_add, BK.evalₐ_complDerFun _ D' hr.symm, BK.evalₐ_complDerFun _ D' ht.symm]
  refine ⟨intDerivationOfLeibniz
    { toFun := BK.complDerFun (maximalIdeal (Localization.AtPrime P)) D'
      map_zero' := by
        have h0 := hadd 0 0
        rw [add_zero] at h0
        simpa using h0
      map_add' := hadd }
    (fun a b => by simpa [smul_eq_mul] using BK.complDerFun_mul _ D' a b),
    fun x => ?_⟩
  have h2 := BK.complDerFun_algebraMap (maximalIdeal (Localization.AtPrime P)) D'
    (algebraMap S (Localization.AtPrime P) x)
  rw [hD'] at h2
  exact h2

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendAdicCompletionLocalizationStatement
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_extend_adicCompletion_localization : ∀ (S : Type) [CommRing S] (P : Ideal S) [P.IsPrime] (d : Derivation ℤ S S), ∃ D : Derivation ℤ (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)) (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)), ∀ x, D (algebraMap S _ x) = algebraMap S _ (d x) := by
  first | exact @GlobalTheory.derivation_extend_completion_localization_atPrime | exact GlobalTheory.derivation_extend_completion_localization_atPrime | (intros; apply GlobalTheory.derivation_extend_completion_localization_atPrime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsAddSwapUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsAddSwapUnique
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem mul_eq_zero_of_mem_map_sq {R : Type} [CommRing R] {I : Ideal R} (hI : I ^ 2 = 0) {B' : Type} [CommRing B']
    [Algebra R B'] {x y : B'} (hx : x ∈ I.map (algebraMap R B')) (hy : y ∈ I.map (algebraMap R B')) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← sq, map_sq hI B', Ideal.zero_eq_bot, Ideal.mem_bot] at h
  exact h

theorem isTheta_mul_eq {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (hI : I ^ 2 = 0) {B B₀ B' : Type}
    [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] [CommRing B'] [Algebra R B'] {p : B →+* B₀}
    {a b : B →ₐ[R] B'} {θ : Ω[B₀⁄R₀] →+ B'} (h : IsTheta I p a b θ) (x : B) {t : B'}
    (ht : t ∈ I.map (algebraMap R B')) : a x * t = b x * t := by
  have hd : (a x - b x) * t = 0 := by
    rw [← h.der x]; exact mul_eq_zero_of_mem_map_sq hI (h.mem _) ht
  rw [sub_mul, sub_eq_zero] at hd
  exact hd

theorem isTheta_add : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' : Type) [CommRing B'] [Algebra R B'] (a b c : B →ₐ[R] B') (θ θ' : Ω[B₀⁄R₀] →+ B'), IsTheta I p a b θ → (IsTheta I p b a (-θ) ∧ (IsTheta I p b c θ' → IsTheta I p a c (θ + θ')) ∧ (IsTheta I p a b θ' → θ = θ') ∧ (θ = 0 → a = b)) := by
  intro R R₀ _ _ I hI π hπ hk B B₀ _ _ _ _ p hs hp hker B' _ _ a b c θ θ' h
  refine ⟨⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩, fun h' ↦ ⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩, fun h' ↦ ?_,
    fun h0 ↦ ?_⟩
  · rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, h.smul, mul_neg, isTheta_mul_eq hI h x (h.mem w)]
  · rw [AddMonoidHom.neg_apply, h.der, neg_sub]
  · exact (Ideal.neg_mem_iff _).2 (h.mem w)
  · rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, h.smul, h'.smul, mul_add,
      isTheta_mul_eq hI h x (h'.mem w)]
  · rw [AddMonoidHom.add_apply, h.der, h'.der]; ring
  · exact Ideal.add_mem _ (h.mem w) (h'.mem w)
  · ext w
    have hw : w ∈ Submodule.span B₀ (Set.range (KaehlerDifferential.D R₀ B₀)) := by
      rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y, rfl⟩ := hy
      obtain ⟨x, rfl⟩ := hp y
      rw [h.der, h'.der]
    | zero => simp
    | add u v _ _ hu hv => rw [map_add (f := _), map_add (f := _), hu, hv]
    | smul r u _ hu =>
      obtain ⟨x, rfl⟩ := hp r
      rw [h.smul, h'.smul, hu]
  · ext x
    have := h.der x
    rw [h0, AddMonoidHom.zero_apply] at this
    exact (sub_eq_zero.1 this.symm)

end GlobalTheory.Obs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsAddSwapUniqueStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' : Type) [CommRing B'] [Algebra R B'] (a b c : B →ₐ[R] B') (θ θ' : Ω[B₀⁄R₀] →+ B'), IsTheta I p a b θ → (IsTheta I p b a (-θ) ∧ (IsTheta I p b c θ' → IsTheta I p a c (θ + θ')) ∧ (IsTheta I p a b θ' → θ = θ') ∧ (θ = 0 → a = b)) := by
  first | exact @GlobalTheory.Obs.isTheta_add | exact GlobalTheory.Obs.isTheta_add | (intros; apply GlobalTheory.Obs.isTheta_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomRescaledRealisationSameGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomRescaledRealisationSameGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.EndoHom

theorem isMonHom_of_prod_pow {S : Scheme.{0}} {A C : Over S} [GrpObj A] [GrpObj C] [IsCommMonObj C]
    (pr : Fin 8 → (A ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniq : ∀ (T' : Over S) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ A, ∀ a, x ≫ pr a = y a)
    (f : A ⟶ A) (e : Fin 8 → Fin 8 → ℤ)
    (hf : ∀ a, f ≫ pr a = ((List.finRange 8).map fun b => pr b ^ e a b).prod) : IsMonHom f := by
  refine isMonHom_of_mul f fun T x y => ?_
  obtain ⟨z, -, hu⟩ := huniq T (fun a => ((x * y) ≫ f) ≫ pr a)
  refine (hu ((x * y) ≫ f) fun a => rfl).trans (hu ((x ≫ f) * (y ≫ f)) fun a => ?_).symm
  have hpre : ∀ {T : Over S} (w : T ⟶ A) (a : Fin 8),
      w ≫ f ≫ pr a = ((List.finRange 8).map fun b => (w ≫ pr b) ^ e a b).prod := fun {T} w a => by
    let φ : (A ⟶ C) →* (T ⟶ C) := MonoidHom.mk' (w ≫ ·) fun g₁ g₂ => MonObj.comp_mul w g₁ g₂
    have h := map_list_prod φ ((List.finRange 8).map fun b => pr b ^ e a b)
    rw [List.map_map] at h
    rw [hf a]
    refine h.trans (congrArg List.prod (List.map_congr_left fun b _ => ?_))
    exact map_zpow φ (pr b) (e a b)
  have := hpr
  rw [MonObj.mul_comp, Category.assoc, Category.assoc, Category.assoc, hpre, hpre, hpre]
  simp only [MonObj.mul_comp, mul_zpow]
  exact (List.prod_map_mul).symm

theorem isMonHom_of_isGrpPullback_endo {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {b : S' ⟶ S} {φ : G'.left ⟶ G.left} (hg : IsGrpPullback G' G b φ) (f : G ⟶ G) (hf : IsMonHom f)
    (f₀ : G' ⟶ G') (h : f₀.left ≫ φ = φ ≫ f.left) : IsMonHom f₀ := by
  obtain ⟨f', hf', he⟩ := GlobalTheory.Ex.Arch.exists_pull_endo hg f hf
  have : f' = f₀ := Over.OverMorphism.ext (hg.1.hom_ext (he.trans h.symm) ((Over.w f').trans (Over.w f₀).symm))
  exact this ▸ hf'

end GlobalTheory.Poinc.EndoHom


open GlobalTheory.Poinc.EndoHom in
theorem GlobalTheory.Poinc.isMonHom_of_same_rechart : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) → ∀ E, IsMonHom (ε' E) := by
  intro g n F W Z i X ε hD c₀ hc R' fg frac hth hev ρ' ε' hS E
  obtain ⟨c, -, pr, hpr, huniq, -, hε⟩ := hD
  have hE : IsMonHom (ε E) := isMonHom_of_prod_pow pr hpr huniq (ε E) E (hε E)
  obtain ⟨P₀, a, a', ε₀, h₁, h₂, -, -, hε₀, -⟩ := hS
  have h₀ : IsMonHom (ε₀ E) := isMonHom_of_isGrpPullback_endo h₁ (ε E) hE (ε₀ E) (hε₀ E).1
  have : IsSchemeTheoreticallyDominant (spMap (X.S.rechart c₀ hc R' fg frac hth hev).R.val.toRingHom) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ Subtype.val_injective
  have := ρ'.P.isAb.smooth
  have := ρ'.P.isAb.proper
  exact GlobalTheory.ExtUnique.isMonHom_of_isGrpPullback h₂ h₂ (ε₀ E) (ε' E) (hε₀ E).2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomRescaledRealisationSameGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMonHom_rescaled_realisation_same_genericFibre : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) → ∀ E, IsMonHom (ε' E) := by
  first | exact @GlobalTheory.Poinc.isMonHom_of_same_rechart | exact GlobalTheory.Poinc.isMonHom_of_same_rechart | (intros; apply GlobalTheory.Poinc.isMonHom_of_same_rechart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedHomAlgebraMap
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InvForm

variable {R : Type} [CommRing R]

section Val

variable {B D : Type} [CommRing B] [Algebra R B] [CommRing D] [Algebra R D]

abbrev redHom (φ : B →ₐ[R] DualNumber D) : B →+* D :=
  (TrivSqZeroExt.fstHom R D D).toRingHom.comp φ.toRingHom

theorem redHom_algebraMap (φ : B →ₐ[R] DualNumber D) (r : R) :
    redHom φ (algebraMap R B r) = algebraMap R D r := by
  simp [redHom, TrivSqZeroExt.algebraMap_eq_inl']

def dVal (φ : B →ₐ[R] DualNumber D) : Ω[B⁄R] →ₗ[R] D :=
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  let d : Derivation R B D :=
    { toFun := fun b ↦ (φ b).snd
      map_add' := fun a b ↦ by simp
      map_smul' := fun r b ↦ by
        rw [map_smul, TrivSqZeroExt.snd_smul]
        rfl
      map_one_eq_zero' := by simp
      leibniz' := fun a b ↦ by
        change (φ (a * b)).snd = (φ a).fst * (φ b).snd + (φ b).fst * (φ a).snd
        rw [map_mul, TrivSqZeroExt.snd_mul]
        simp [MulOpposite.smul_eq_mul_unop]
        ring }
  d.liftKaehlerDifferential.restrictScalars R

theorem dVal_D (φ : B →ₐ[R] DualNumber D) (b : B) : dVal φ (KaehlerDifferential.D R B b) = (φ b).snd := by
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  exact Derivation.liftKaehlerDifferential_comp_D _ b

end Val

variable (A : Over (Sp R)) [GrpObj A]

def IsInv (w : GlobForm A.hom) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (U V : A.left.affineOpens)
    (φ : Sec A.hom U.1 →ₐ[R] DualNumber D) (ψ : Sec A.hom V.1 →ₐ[R] DualNumber D)
    (p q : Over.mk (spMap (algebraMap R (DualNumber D))) ⟶ A) (q₀ : Sp D ⟶ A.left),
    p.left = spMap (φ : Sec A.hom U.1 →+* DualNumber D) ≫ affPt A.hom U →
    q.left = spMap (algebraMap D (DualNumber D)) ≫ q₀ →
    (p * q).left = spMap (ψ : Sec A.hom V.1 →+* DualNumber D) ≫ affPt A.hom V →
    dVal φ (w.1 (op U)) = dVal ψ (w.1 (op V))

def InvForm : Submodule R (GlobForm A.hom) where
  carrier := {w | IsInv A w}
  add_mem' {w w'} hw hw' D _ _ U V φ ψ p q q₀ hp hq hpq := by
    change dVal φ (w.1 (op U) + w'.1 (op U)) = dVal ψ (w.1 (op V) + w'.1 (op V))
    rw [map_add (f := _), map_add (f := _), hw D U V φ ψ p q q₀ hp hq hpq, hw' D U V φ ψ p q q₀ hp hq hpq]
  zero_mem' D _ _ U V φ ψ p q q₀ _ _ _ := by
    change dVal φ 0 = dVal ψ 0
    rw [map_zero, map_zero]
  smul_mem' r w hw D _ _ U V φ ψ p q q₀ hp hq hpq := by
    change dVal φ (r • w.1 (op U)) = dVal ψ (r • w.1 (op V))
    rw [map_smul, map_smul, hw D U V φ ψ p q q₀ hp hq hpq]

end GlobalTheory.InvForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEvenCoordinatesNegDifferByUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEvenCoordinatesNegDifferByUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.PsiEvenCoordUnit

open GlobalTheory.PeriodBalance GlobalTheory.PsiTauCoordRel

theorem alg' {G : Type} [CommGroup G] (a b c x y : G) (h : b * y * c = a * x) : y = a * b⁻¹ * c⁻¹ * x := by
  rw [mul_right_comm (a * b⁻¹), mul_right_comm a, ← h, mul_right_comm (b * y), mul_right_comm b, mul_inv_cancel,
    _root_.one_mul, mul_inv_cancel_right]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), D.PsiEven →
    ∀ (y : D.X) (x x' : (FractionRing R)ˣ), IsPsiCoord D y x → IsPsiCoord D (-y) x' →
      ∃ u : Rˣ, (x' : FractionRing R) = algebraMap R (FractionRing R) u * x := by
  intro R _ _ _ D hE y x x' hx hx'
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  let cU : Rˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ := Units.map (cst ξ).toMonoidHom
  let kU : (FractionRing R)ˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    Units.map (kst ξ).toMonoidHom
  have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hE y) (𝟙 _))
  rw [val_pull hJ] at e
  obtain ⟨w, hw⟩ : ∃ w : Rˣ, val D.sym (𝟙 _ ≫ D.xK y) ξ J = cU w := by
    have : 𝟙 _ ≫ D.xK y = jK R ≫ (D.c y).left := by rw [Category.id_comp]; exact xK_eq D y
    rw [this]
    refine val_int ξ hJc D.sym (D.c y).left fun k => ?_
    obtain ⟨q, hq⟩ : ∃ q : D.P.A ⟶ D.P.A,
        (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k = q.left := by
      fin_cases k
      · exact ⟨_, rfl⟩
      · exact ⟨𝟙 _, rfl⟩
    rw [hq, Category.assoc, Over.w q, Over.w]; rfl
  obtain ⟨j, h, i1, rfl⟩ := hx
  obtain ⟨j', h', i1', rfl⟩ := hx'
  obtain ⟨c1, g1⟩ := val_psi_chart D ξ hJ hJc y j i1 (h trivial)
  obtain ⟨c2, g2⟩ := val_psi_chart D ξ hJ hJc (-y) j' i1' (h' trivial)
  have e1 : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.psi y).s j) = kU (genVal (D.psi y) j h) :=
    Units.ext (gm_genVal ξ (D.psi y) j h)
  have e2 : gm (𝟙 _) ξ (LB.wchart D.P.L _ j') ((D.psi (-y)).s j') = kU (genVal (D.psi (-y)) j' h') :=
    Units.ext (gm_genVal ξ (D.psi (-y)) j' h')
  have f : cU c2 * kU (genVal (D.psi (-y)) j' h') * cU w = cU c1 * kU (genVal (D.psi y) j h) :=
    (congrArg₂ (· * ·) (g2.trans (congrArg (cU c2 * ·) e2)) hw).symm.trans
      (e.trans (g1.trans (congrArg (cU c1 * ·) e1)))
  refine ⟨c1 * c2⁻¹ * w⁻¹, ?_⟩
  have k3 : genVal (D.psi (-y)) j' h' = Units.map (algebraMap R (FractionRing R)).toMonoidHom (c1 * c2⁻¹ * w⁻¹) *
      genVal (D.psi y) j h := by
    refine Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ) ?_
    rw [map_mul]
    change kU _ = cU (c1 * c2⁻¹ * w⁻¹) * kU _
    rw [map_mul, map_mul, map_inv, map_inv]
    exact alg' _ _ _ _ _ f
  exact congrArg Units.val k3

end GlobalTheory.PsiEvenCoordUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEvenCoordinatesNegDifferByUnitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiEven_coordinates_neg_differ_by_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), D.PsiEven →
    ∀ (y : D.X) (x x' : (FractionRing R)ˣ), IsPsiCoord D y x → IsPsiCoord D (-y) x' →
      ∃ u : Rˣ, (x' : FractionRing R) = algebraMap R (FractionRing R) u * x := by
  first | exact @GlobalTheory.PsiEvenCoordUnit.main | exact GlobalTheory.PsiEvenCoordUnit.main | (intros; apply GlobalTheory.PsiEvenCoordUnit.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelActionIsPullbackProdMapTorsor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelActionIsPullbackProdMapTorsor
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

namespace GlobalTheory.CharKer

variable {S : Scheme.{0}}

theorem comp_one_hom {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit X) (toUnit Y)]

theorem pmap_isPullback_actMap : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A'), IsMonHom i → IsMonHom q → IsPullback i (toUnit N) q η[A'] → IsPullback (prMap A N T) (actMap i T) (pmap q T) (pmap q T) := by
  intro S A A' N T _ _ _ i q hi hq hker
  have hiq : i ≫ q = 1 := by rw [hker.w, Hom.one_def]
  have hpf : pmap q T ≫ fst A' T = fst A T ≫ q := by simp [pmap]
  have hps : pmap q T ≫ snd A' T = snd A T := by simp [pmap]
  have hc : prMap A N T ≫ pmap q T = actMap i T ≫ pmap q T := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, hpf]
      simp only [prMap, actMap, lift_fst_assoc, mul_comp, Category.assoc, hiq]
      simp only [comp_one_hom, _root_.mul_one]
    · rw [Category.assoc, Category.assoc, hps]
      simp [prMap, actMap]
  have hfs : ∀ s : PullbackCone (pmap q T) (pmap q T), (s.fst ≫ fst A T) ≫ q = (s.snd ≫ fst A T) ≫ q := by
    intro s
    have h := congrArg (· ≫ fst A' T) s.condition
    simp only [Category.assoc, hpf] at h
    simpa only [Category.assoc] using h
  have hss : ∀ s : PullbackCone (pmap q T) (pmap q T), s.fst ≫ snd A T = s.snd ≫ snd A T := by
    intro s
    have h := congrArg (· ≫ snd A' T) s.condition
    simpa only [Category.assoc, hps] using h
  have hk : ∀ s : PullbackCone (pmap q T) (pmap q T),
      ((s.fst ≫ fst A T)⁻¹ * (s.snd ≫ fst A T)) ≫ q = toUnit s.pt ≫ η[A'] := by
    intro s
    rw [mul_comp, GrpObj.inv_comp, hfs s, _root_.inv_mul_cancel, Hom.one_def]
  refine ⟨⟨hc⟩, ⟨PullbackCone.IsLimit.mk hc
    (fun s => lift (s.fst ≫ fst A T)
      (lift (hker.lift ((s.fst ≫ fst A T)⁻¹ * (s.snd ≫ fst A T)) (toUnit _) (hk s)) (s.fst ≫ snd A T)))
    ?_ ?_ ?_⟩⟩
  · intro s
    apply CartesianMonoidalCategory.hom_ext <;> simp [prMap]
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simp only [actMap, Category.assoc, lift_fst, comp_mul, lift_fst_assoc, lift_snd_assoc, hker.lift_fst]
      exact _root_.mul_inv_cancel_left _ _
    · simp [actMap, hss]
  · intro s m h1 h2
    have ha : m ≫ fst A (N ⊗ T) = s.fst ≫ fst A T := by rw [← h1]; simp [prMap]
    have ht : m ≫ snd A (N ⊗ T) ≫ snd N T = s.fst ≫ snd A T := by rw [← h1]; simp [prMap]
    have hb : m ≫ fst A (N ⊗ T) * m ≫ snd A (N ⊗ T) ≫ fst N T ≫ i = s.snd ≫ fst A T := by
      rw [← h2]; simp [actMap, comp_mul]
    apply CartesianMonoidalCategory.hom_ext
    · simpa using ha
    · apply CartesianMonoidalCategory.hom_ext
      · apply hker.hom_ext
        · simp only [Category.assoc, lift_snd_assoc, lift_fst_assoc, hker.lift_fst]
          rw [← ha]
          exact eq_inv_mul_of_mul_eq hb
        · exact toUnit_unique _ _
      · simpa using ht

end GlobalTheory.CharKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelActionIsPullbackProdMapTorsorStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelAction_isPullback_prodMap_torsor : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A'), IsMonHom i → IsMonHom q → IsPullback i (toUnit N) q η[A'] → IsPullback (prMap A N T) (actMap i T) (pmap q T) (pmap q T) := by
  first | exact @GlobalTheory.CharKer.pmap_isPullback_actMap | exact GlobalTheory.CharKer.pmap_isPullback_actMap | (intros; apply GlobalTheory.CharKer.pmap_isPullback_actMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRValuationCompleteNormalLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRValuationCompleteNormalLocal
open IsLocalRing GlobalTheory.TorRef

namespace GlobalTheory.DivBound

theorem exists_cdvr_valuation_le : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ)), (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) → (∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1) → maximalIdeal V ≠ ⊥ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (k : FractionRing V →+* FractionRing V'), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ (∀ v : V, k (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (j v)) ∧ ∀ x y : FractionRing V, (∃ r : V', k x = algebraMap V' (FractionRing V') r * k y) → ν x ≤ ν y := by
  intro V _ _ _ hV ν h1 h2 hm
  obtain ⟨-, -, -, h0⟩ := hV
  obtain ⟨m, hmm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hmK : algebraMap V (FractionRing V) m ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hm0
  haveI : ν.IsNontrivial := ⟨algebraMap V (FractionRing V) m, (ν.ne_zero_iff).2 hmK, (h2 m hmm).ne⟩
  haveI : IsDiscreteValuationRing ν.valuationSubring := inferInstance
  haveI : CharZero (FractionRing V) :=
    charZero_of_injective_ringHom (IsFractionRing.injective V (FractionRing V))
  haveI : CharZero ν.valuationSubring :=
    RingHom.charZero (algebraMap ν.valuationSubring (FractionRing V))
  obtain ⟨W', _, _, _, g, hW', hg, hgl⟩ := GlobalTheory.LocalCompletion.exists_cDvr_embedding ν.valuationSubring
    inferInstance inferInstance (IsDiscreteValuationRing.ringKrullDim_eq_one _) inferInstance
  obtain ⟨hdvr, hc, hz⟩ := hW'

  let i : V →+* ν.valuationSubring := (algebraMap V (FractionRing V)).codRestrict ν.valuationSubring.toSubring (fun v => h1 v)
  have hi : ∀ v : V, ((i v : ν.valuationSubring) : FractionRing V) = algebraMap V (FractionRing V) v := fun _ => rfl
  have hiinj : Function.Injective i := fun a b h =>
    IsFractionRing.injective V (FractionRing V) (by rw [← hi, ← hi, h])

  have hnu : ∀ w : ν.valuationSubring, ν (w : FractionRing V) < 1 → ¬ IsUnit w := fun w hw hu =>
    hw.ne ((Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers ν)).mp hu)
  haveI hil : IsLocalHom i := ⟨fun a ha => by
    by_contra hna
    exact hnu (i a) (by rw [hi]; exact h2 a ((mem_maximalIdeal _).2 hna)) ha⟩
  haveI := hgl
  let g' : ν.valuationSubring →+* FractionRing W' := (algebraMap W' (FractionRing W')).comp g
  have hg' : Function.Injective g' :=
    (IsFractionRing.injective W' (FractionRing W')).comp hg
  let k : FractionRing V →+* FractionRing W' := IsFractionRing.lift (A := ν.valuationSubring) hg'
  have hk : ∀ w : ν.valuationSubring, k (w : FractionRing V) = algebraMap W' (FractionRing W') (g w) := fun w =>
    IsFractionRing.lift_algebraMap (A := ν.valuationSubring) hg' w
  refine ⟨W', inferInstance, inferInstance, inferInstance, hdvr, g.comp i, k, ⟨inferInstance, inferInstance, hc, hz⟩,
    hg.comp hiinj, inferInstance, fun v => by rw [← hi, hk]; rfl, ?_⟩
  rintro x y ⟨r, hr⟩
  by_cases hy : y = 0
  · have : k x = 0 := by rw [hr, hy, map_zero, mul_zero]
    rw [(map_eq_zero_iff k k.injective).1 this, hy]
  by_contra hxy
  rw [not_le] at hxy
  set z := x / y with hz'
  have hyν : ν y ≠ 0 := (ν.ne_zero_iff).2 hy
  have hz1 : 1 < ν z := by
    rw [hz', map_div₀]
    exact (one_lt_div₀ (zero_lt_iff.2 hyν)).2 hxy
  have hz0 : z ≠ 0 := by
    intro h; rw [h, map_zero] at hz1; exact not_lt_zero' hz1
  have hzi : ν z⁻¹ < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hz1
  let w : ν.valuationSubring := ⟨z⁻¹, hzi.le⟩
  have hkz : k z = algebraMap W' (FractionRing W') r := by
    rw [hz', map_div₀, hr, mul_div_assoc, div_self ((map_ne_zero k).2 hy), mul_one]
  have hkw : k (w : FractionRing V) = (k z)⁻¹ := by
    change k z⁻¹ = _
    rw [map_inv₀]
  rw [hk, hkz] at hkw
  have hunit : IsUnit (g w) := by
    have h : g w * r = 1 := by
      apply IsFractionRing.injective W' (FractionRing W')
      rw [map_mul, map_one, hkw, inv_mul_cancel₀]
      rw [← hkz]; exact (map_ne_zero k).2 hz0
    exact ⟨⟨g w, r, h, by rw [mul_comm]; exact h⟩, rfl⟩
  exact hnu w hzi (IsUnit.of_map g w hunit)

end GlobalTheory.DivBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRValuationCompleteNormalLocalStatement
open IsLocalRing GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_valuation_completeNormalLocal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ)), (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) → (∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1) → maximalIdeal V ≠ ⊥ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (k : FractionRing V →+* FractionRing V'), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ (∀ v : V, k (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (j v)) ∧ ∀ x y : FractionRing V, (∃ r : V', k x = algebraMap V' (FractionRing V') r * k y) → ν x ≤ ν y := by
  first | exact @GlobalTheory.DivBound.exists_cdvr_valuation_le | exact GlobalTheory.DivBound.exists_cdvr_valuation_le | (intros; apply GlobalTheory.DivBound.exists_cdvr_valuation_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianModelFiniteExtCompleteDVR
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianModelFiniteExtCompleteDVR
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.PolSemiAbModel

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem exists_model : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (P : PolAV (Sp (FractionRing W))),
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : W →+* V₁)
      (fK : FractionRing W →+* FractionRing V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
      (∀ a, fK (algebraMap W _ a) = algebraMap V₁ _ (f a)) ∧
      ∃ (A : PolAV (Sp (FractionRing V₁))) (β : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap fK) β ∧
        LBIso A.L (P.L.pull β) ∧
        ∃ (G : Over (Sp V₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
          IsSemiAbelian G ∧ IsMonHom gen.hom := by
  intro W _ _ _ hW P
  obtain ⟨hdvr, hcomp, hchar⟩ := (GlobalTheory.LN.cDvr_iff W).1 hW
  haveI : CharZero (FractionRing W) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective W (FractionRing W))
  obtain ⟨W', L, _, _, _, _, _, _, _, _, hsq, hfin, hloc, hcompl, G, _, ⟨e, he⟩, hG⟩ :=
    GlobalTheory.SS.potModel_isSemiAbelian W (FractionRing W) P.A P.isAb
  have hinj : Function.Injective (algebraMap W W') := by
    have h2 : Function.Injective ((algebraMap (FractionRing W) L).comp (algebraMap W (FractionRing W))) :=
      (algebraMap (FractionRing W) L).injective.comp (IsFractionRing.injective W (FractionRing W))
    rw [← hsq] at h2
    exact Function.Injective.of_comp h2
  haveI : CharZero W' := charZero_of_injective_algebraMap hinj
  let ε : FractionRing W' ≃ₐ[W'] L := IsLocalization.algEquiv (nonZeroDivisors W') (FractionRing W') L
  let fK : FractionRing W →+* FractionRing W' := (ε.symm : L →+* FractionRing W').comp (algebraMap (FractionRing W) L)
  have hε : (ε.symm : L →+* FractionRing W').comp (algebraMap W' L) = algebraMap W' (FractionRing W') := by
    ext x; exact ε.symm.commutes x
  obtain ⟨A, β, hpb, -, hLB⟩ := GlobalTheory.KeyFam.SameLam.exists_polPB P fK
  haveI : IsCommMonObj G := hG.comm
  refine ⟨W', inferInstance, inferInstance, inferInstance, algebraMap W W', fK,
    (GlobalTheory.LN.cDvr_iff W').2 ⟨inferInstance, hcompl, inferInstance⟩, hinj, hloc,
    RingHom.finite_algebraMap.2 hfin, ?_, A, β, hpb, hLB, ?_⟩
  · intro a
    show ε.symm (algebraMap (FractionRing W) L (algebraMap W _ a)) = _
    rw [← RingHom.comp_apply, ← hsq, RingHom.comp_apply]
    exact ε.symm.commutes _
  · let X := (Over.pullback (spMap (algebraMap W' L))).obj G
    let T := (Over.pullback (spMap (ε.symm : L →+* FractionRing W'))).obj X
    have h₁ := isGrpPullback_pullback G (jK W')
    have hTX := isGrpPullback_pullback X (spMap (ε.symm : L →+* FractionRing W'))
    have hXG := isGrpPullback_pullback G (spMap (algebraMap W' L))
    have hTG := (hTX.comp hXG).congr (by rw [spMap_comp', hε]) rfl
    obtain ⟨e₁, he₁, -⟩ := grpPullback_iso h₁ hTG
    have hXY := isGrpPullback_of_iso e
    have hYP := isGrpPullback_pullback P.A (spMap (algebraMap (FractionRing W) L))
    have hTP := (hTX.comp (hXY.comp hYP)).congr (by rw [Category.id_comp, spMap_comp']) rfl
    obtain ⟨e₂, he₂, -⟩ := grpPullback_iso hTP hpb
    exact ⟨G, inferInstance, inferInstance, e₁ ≪≫ e₂, hG, by simp only [Iso.trans_hom]; infer_instance⟩

end GlobalTheory.PolSemiAbModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianModelFiniteExtCompleteDVRStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelianModel_finiteExt_completeDVR : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (P : PolAV (Sp (FractionRing W))),
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : W →+* V₁)
      (fK : FractionRing W →+* FractionRing V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
      (∀ a, fK (algebraMap W _ a) = algebraMap V₁ _ (f a)) ∧
      ∃ (A : PolAV (Sp (FractionRing V₁))) (β : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap fK) β ∧
        LBIso A.L (P.L.pull β) ∧
        ∃ (G : Over (Sp V₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
          IsSemiAbelian G ∧ IsMonHom gen.hom := by
  first | exact @GlobalTheory.PolSemiAbModel.exists_model | exact GlobalTheory.PolSemiAbModel.exists_model | (intros; apply GlobalTheory.PolSemiAbModel.exists_model <;> assumption)
end
end
