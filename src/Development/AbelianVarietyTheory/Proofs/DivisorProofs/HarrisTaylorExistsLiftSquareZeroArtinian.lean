module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalProjectiveOverTensorRingOfIntegersStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftSummandLieResidueCharZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieConditionSummandResidueCharP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftLieOfHodgeSummandLie

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsIsotropicStableSummand
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveDeRham
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open GlobalTheory.AbDual GlobalTheory.AbLaw GlobalTheory.CechPic

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTPerf

theorem bijective_deRham (HR : GlobalTheory.Published.AbelianDeRham) (HD : GlobalTheory.Published.AbelianDualCrystal) {K : Type} [CommRing K]
    [IsNoetherianRing K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) (g : ℕ)
    (hg : SmoothOfRelativeDimension g A.hom) (P : LB (A ⊗ A).left) (hP : P.IsLB)
    (r₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (r₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (hsym : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    (amp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)) (e : ℕ) (he0 : 0 < e) (he : IsUnit (e : K))
    (hker : ∀ (T : Over (Sp K)) (x : T ⟶ A),
      (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1)
    (ψ : HdR A →ₗ[K] HdR A →ₗ[K] K) (hψ : IsCorrForm (dp0 K) (𝟙 _) A A P ψ) : Function.Bijective ψ := by

  have hsw : (swap P).IsLB := pull_isLB hP _
  have ec : cls P hP = cls _ hsw := (cls_eq_iff hP hsw).2 hsym
  have key : ∀ (Y : Over (Sp K)) (a b : Y ⟶ A), evc hP a b = evc hP b a := fun Y a b ↦ by
    rw [← evc_swap hP hsw a b]
    show CechPic.pull _ (cls P hP) = CechPic.pull _ (cls _ hsw)
    rw [ec]

  obtain ⟨B, _, Q, hB, hBg, hd, hd'⟩ := HD.1 (Sp K) A hA
  have hBg := hBg _ hg
  haveI : IsCommMonObj B := hB.comm

  have hL := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
  obtain ⟨H, hH, hamp⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod hA hA hL amp hL amp
  obtain ⟨a₁, a₂⟩ := GlobalTheory.BirigidLift.additive_of_triv hA hA hH hamp hP r₁ r₂
  obtain ⟨lam, hlam, hcls⟩ := GlobalTheory.BirigidLift.exists_hom hd hd'.additive hP a₁ a₂

  have hkerl : ∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ lam = 1 → x ^ e = 1 := by
    intro T x hx
    have tr : Triv (ev P (fst A T) (snd A T ≫ x)) := by
      rw [triv_ev_iff hP, GlobalTheory.BirigidLift.evc_of_cls hd.isLB hP hcls, Category.assoc, hx, comp_one]
      exact evc_one_right hd.isLB hd.zero _
    refine hker T x ((triv_ev_iff hP _ _).2 ?_)
    rw [key]
    exact (triv_ev_iff hP _ _).1 tr
  obtain ⟨μ', hμ', e₁, e₂⟩ := GlobalTheory.IsogenyQuasiInverse.exists_quasiInverse K A B g hA hB hg hBg lam hlam e he0 hkerl
  haveI := hlam
  haveI := hμ'
  have hpush : Function.Bijective (push (dp0 K) (𝟙 _) lam) := by
    have hmon (X : Over (Sp K)) [GrpObj X] [IsCommMonObj X] (n : ℕ) : IsMonHom ((𝟙 X) ^ n : X ⟶ X) := by
      induction n with
      | zero => rw [pow_zero]; exact isMonHom_one X X
      | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 X) ^ n) (𝟙 X) ≫ μ[X]))
    have hpow (X : Over (Sp K)) [GrpObj X] [IsCommMonObj X] (n : ℕ) :
        haveI := hmon X n
        push (dp0 K) (𝟙 _) ((𝟙 X) ^ n : X ⟶ X) = (n : K) • LinearMap.id := by
      induction n with
      | zero =>
        haveI := hmon X 0
        rw [push_congr (dp0 K) (𝟙 _) (pow_zero (𝟙 X)), push_one, Nat.cast_zero, zero_smul]
      | succ n ih =>
        haveI := hmon X n
        haveI := hmon X (n + 1)
        haveI : IsMonHom ((𝟙 X) ^ n * 𝟙 X) := inferInstanceAs (IsMonHom (lift ((𝟙 X) ^ n) (𝟙 X) ≫ μ[X]))
        rw [push_congr (dp0 K) (𝟙 _) (pow_succ (𝟙 X) n), push_mul, ih, push_id, Nat.cast_succ, add_smul, one_smul]
    haveI := hmon A e
    haveI := hmon B e
    have k₁ : ∀ x, push (dp0 K) (𝟙 _) μ' (push (dp0 K) (𝟙 _) lam x) = (e : K) • x := fun x ↦ by
      rw [← LinearMap.comp_apply, ← push_comp, push_congr (dp0 K) (𝟙 _) e₁, hpow]; rfl
    have k₂ : ∀ y, push (dp0 K) (𝟙 _) lam (push (dp0 K) (𝟙 _) μ' y) = (e : K) • y := fun y ↦ by
      rw [← LinearMap.comp_apply, ← push_comp, push_congr (dp0 K) (𝟙 _) e₂, hpow]; rfl
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨push (dp0 K) (𝟙 _) μ' ((↑he.unit⁻¹ : K) • y), ?_⟩⟩
    · have eq := congrArg (push (dp0 K) (𝟙 _) μ') hxy
      rw [k₁, k₁] at eq
      exact (he.smul_left_cancel).1 eq
    · rw [k₂, smul_smul, he.mul_val_inv, one_smul]

  obtain ⟨⟨φ, hφ, -⟩, hperf⟩ := GlobalTheory.Published.AbelianDualCrystal.duality HR hA hg hB hBg (hd.isPerfect hd')
  have C := cupSquare_of_free HR.1 (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_prod hg hg)
  have e' : LBIso (ev Q (fst A A) (snd A A ≫ lam)) (ev P (fst A A ≫ 𝟙 A) (snd A A)) := by
    refine (cls_eq_iff (pull_isLB hd.isLB _) (pull_isLB hP _)).1 ?_
    rw [cls_ev hd.isLB, cls_ev hP, GlobalTheory.BirigidLift.evc_of_cls hd.isLB hP hcls, Category.comp_id]
  have hadj : ∀ x y, φ x (push (dp0 K) (𝟙 _) lam y) = ψ x y := fun x y ↦ by
    have k := IsCorrForm.adjoint C hd.isLB hP hφ hψ (𝟙 A) lam e' x y
    rwa [push_id] at k
  haveI := (hperf φ hφ).1
  have hφb : Function.Bijective φ := LinearMap.IsPerfPair.bijective_left φ
  let E := LinearEquiv.ofBijective _ hpush
  have : ⇑ψ = ⇑E.dualMap ∘ ⇑φ := by
    funext x
    refine LinearMap.ext fun y ↦ ?_
    rw [Function.comp_apply, LinearEquiv.dualMap_apply, ← hadj]
    rfl
  rw [this]
  exact E.dualMap.bijective.comp hφb

end GlobalTheory.HTPerf

namespace GlobalTheory.HTPerf

open GlobalTheory.Published.GrothendieckMessing IsLocalRing


set_option maxHeartbeats 1600000 in
theorem skew_bijective : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → (∀ x y, φ x y = -φ y x) ∧ Function.Bijective φ := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ φ hφ
  have hI2 : RingHom.ker π ^ 2 = ⊥ := hsq
  haveI : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; simpa using Ideal.mul_mem_mul h1 h1
    rw [hI2] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  haveI : IsNoetherianRing C₀ := isNoetherianRing_of_surjective C C₀ π hπ
  let κ := divided₂ hsq
  have hκ : IsNilDP κ := isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  have GD : GlobalTheory.Published.GrothendieckDeformation :=
    GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.abelianDeRham GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers
  have hA₀ := o₀.ab
  have hP₀ := o₀.isLB
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.AbelianDim.exists_relDim C₀ o₀.A hA₀
  obtain ⟨A', _, i', h', hA'⟩ := GlobalTheory.UnobTop.abelianUnobstructed C (RingHom.ker π) hsq C₀ π hπ rfl o₀.A hA₀
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C A' hA'
  have Cs := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl hA' hg hA' hg h' h'

  have hsw : (swap o₀.P).IsLB := pull_isLB hP₀ _
  have hs : LBIso (swap o₀.P) o₀.P := (cls_eq_iff hsw hP₀).1 ((cls_eq_iff hP₀ hsw).2 o₀.symm).symm
  have skew : ∀ x y, φ x y = -φ y x := by
    have hswap : IsCorrForm κ (spMap π) o₀.A o₀.A (swap o₀.P) (-φ.flip) := by
      obtain ⟨n, a, b, hc, hφ⟩ := hφ
      have m : IsMor κ ((o₀.A ⊗ o₀.A).hom ≫ spMap π) κ ((o₀.A ⊗ o₀.A).hom ≫ spMap π) (RingHom.id C) (lift (snd o₀.A o₀.A) (fst o₀.A o₀.A)).left :=
        (homMor κ (spMap π) (lift (snd o₀.A o₀.A) (fst o₀.A o₀.A))).isMor
      have k := isChern_pull m hc
      rw [crystallinePull2_sum_cup] at k
      refine ⟨n, fun i ↦ -b i, a, ?_, fun x y ↦ ?_⟩
      · convert k using 2 with i
        rw [pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, Submodule.coe_neg, map_neg, map_neg,
          LinearMap.neg_apply, neg_eq_of_add_eq_zero_right (cup_add_cup _ _ _)]
      · simp only [LinearMap.neg_apply, LinearMap.flip_apply, hφ, map_neg, ← Finset.sum_neg_distrib, neg_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm]
    have hiso : IsCorrForm κ (spMap π) o₀.A o₀.A o₀.P (-φ.flip) := by
      obtain ⟨n, a, b, hc, hf⟩ := hswap
      exact ⟨n, a, b, (isChern_existsUnique_and_iso C _ κ _ _).2 _ _ hsw hP₀ hs _ hc, hf⟩
    intro x y
    exact LinearMap.congr_fun₂ (hφ.unique Cs hP₀ hiso) x y
  refine ⟨skew, ?_⟩

  have HC := (GD C (RingHom.ker π) κ hκ C₀ π hπ rfl).1
  obtain ⟨bij, -, -⟩ := HC g o₀.A A' i' h' hA' hg
  let e := LinearEquiv.ofBijective (crysToDR κ h') (HC.crysToDR_bijective h' hA' hg)
  have ee : ∀ xA, crysToDR κ h' (e.symm xA) = xA := e.apply_symm_apply
  letI : Algebra C C₀ := π.toAlgebra
  have hBC := (ADR.2.2.1 C A' g hA' hg C₀ o₀.A i' h').1
  obtain ⟨hfinA, hprojA, -⟩ := ADR.1.prim hA' hg
  haveI := hfinA
  haveI := hprojA
  haveI : Module.Finite C (Crys κ (spMap π) o₀.A) := Module.Finite.equiv e.symm
  haveI : Module.Projective C (Crys κ (spMap π) o₀.A) := Module.Projective.of_equiv e.symm

  let red : Crys κ (spMap π) o₀.A →ₛₗ[π] HdR o₀.A := hBC.bcMap.comp (crysToDR κ h')
  have hm : ∀ x, (crysRedMor κ rfl o₀.A).Corr x (red x) := fun x ↦
    (corr_crysToDR_iff rfl h' bij.2 x (red x)).1 (by exact hBC.corr_iff.2 rfl)
  have iso : LBIso (o₀.P.pull (Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A)))) o₀.P :=
    (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP₀ _) hP₀).1
      (by rw [GlobalTheory.CechPic.cls_pull hP₀, Over.id_left, GlobalTheory.CechPic.pull_id])
  obtain ⟨φ', hφ', e'⟩ := hφ.pull hP₀ (crysRedMor κ rfl o₀.A) (crysRedMor κ rfl o₀.A)
    (h := Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A))) (by simp) (by simp) hP₀ iso
  have hrel : ∀ x y, φ' (red x) (red y) = π (φ x y) := fun x y ↦ e' x (red x) y (red y) (hm x) (hm y)
  have hred : Function.Surjective red := by
    intro y
    let l : primDR A' →ₗ[C] C₀ :=
      { toFun c := y ((redMor h').pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨xA, hx⟩ := Module.projective_lifting_property (Algebra.linearMap C C₀) l hπ
    refine ⟨e.symm xA, ?_⟩
    show hBC.bcMap (crysToDR κ h' (e.symm xA)) = y
    rw [ee]
    exact hBC.corr_iff.1 fun c ↦ (LinearMap.congr_fun hx c).symm
  have hker : ∀ x, red x = 0 → x ∈ (RingHom.ker π) • (⊤ : Submodule C (Crys κ (spMap π) o₀.A)) := by
    intro x hx
    have hc := hBC.corr_iff.2 hx
    have hmem := GlobalTheory.BirigLift.mem_smul_top_of_forall_mem (RingHom.ker π) (crysToDR κ h' x) fun c ↦
      RingHom.mem_ker.2 ((hc c).symm.trans (LinearMap.zero_apply _))
    have := Submodule.mem_map_of_mem (f := e.symm.toLinearMap) hmem
    rw [Submodule.map_smul''] at this
    have ex : e.symm.toLinearMap (crysToDR κ h' x) = x := e.symm_apply_apply x
    rw [ex] at this
    exact Submodule.smul_mono le_rfl le_top this

  obtain ⟨k, hkp, hkerP⟩ := o₀.kerP
  have hk0 : 0 < k := by
    refine Nat.pos_of_ne_zero fun h0 ↦ ?_
    rw [h0, Nat.coprime_zero_left] at hkp
    exact (Fact.out : p.Prime).one_lt.ne' hkp
  have hku : IsUnit (k : C₀) := by
    have := (b.unit k hkp).map (π.comp tR)
    rwa [map_natCast] at this
  have hψb : Function.Bijective φ' :=
    bijective_deRham ADR ADC o₀.A hA₀ g₀ hg₀ o₀.P hP₀ o₀.rig₁ o₀.rig₂ o₀.symm o₀.ample k hk0 hku hkerP φ' hφ'
  have skew' : ∀ u v, φ' u v = -φ' v u := fun u v ↦ by
    obtain ⟨x, rfl⟩ := hred u
    obtain ⟨y, rfl⟩ := hred v
    rw [hrel, hrel, skew, map_neg]
  have hψf : Function.Surjective φ'.flip := fun l ↦ by
    obtain ⟨x, hx⟩ := hψb.2 (-l)
    exact ⟨x, LinearMap.ext fun y ↦ by rw [LinearMap.flip_apply, skew', hx, LinearMap.neg_apply, neg_neg]⟩
  have hperf := GlobalTheory.BirigLift.exists_perfect_mod π red φ φ' hπ hψf hred hker hrel

  have htop : (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C)) ≤ LinearMap.range φ.flip ⊔ RingHom.ker π • ⊤ := fun l _ ↦ by
    obtain ⟨z, hz⟩ := hperf l
    have hmem := GlobalTheory.BirigLift.mem_smul_top_of_forall_mem (RingHom.ker π) (l - φ.flip z) fun c ↦ by
      simpa only [LinearMap.sub_apply, LinearMap.flip_apply] using hz c
    exact Submodule.mem_sup.2 ⟨φ.flip z, ⟨z, rfl⟩, l - φ.flip z, hmem, add_sub_cancel _ _⟩
  have hIle : RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C)) ≤ LinearMap.range φ.flip := by
    calc RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C)) ≤ RingHom.ker π • (LinearMap.range φ.flip ⊔ RingHom.ker π • ⊤) :=
          Submodule.smul_mono le_rfl htop
      _ = RingHom.ker π • LinearMap.range φ.flip ⊔ RingHom.ker π • RingHom.ker π • ⊤ := Submodule.smul_sup _ _ _
      _ ≤ LinearMap.range φ.flip := by
          refine sup_le Submodule.smul_le_right ?_
          rw [← Submodule.mul_smul, ← pow_two, hI2, Submodule.bot_smul]
          exact bot_le
  have hsurj : Function.Surjective φ.flip :=
    LinearMap.range_eq_top.1 (top_le_iff.1 (htop.trans (sup_le le_rfl hIle)))
  haveI : Module.Free C (Crys (divided₂ hsq) (spMap π) o₀.A) := Module.free_of_flat_of_isLocalRing
  let bs := Module.finBasis C (Crys (divided₂ hsq) (spMap π) o₀.A)
  have hinj : Function.Injective φ.flip := by
    have hs' : Function.Surjective (bs.toDualEquiv.symm.toLinearMap ∘ₗ φ.flip) :=
      bs.toDualEquiv.symm.surjective.comp hsurj
    have hi := OrzechProperty.injective_of_surjective_endomorphism _ hs'
    exact fun x y hxy ↦ hi (by simp only [LinearMap.coe_comp, Function.comp_apply, hxy])
  have hneg : ∀ x, φ x = -φ.flip x := fun x ↦
    LinearMap.ext fun y ↦ by rw [LinearMap.neg_apply, LinearMap.flip_apply, skew]
  refine ⟨fun x x' hxx ↦ hinj (neg_injective ?_), fun l ↦ ?_⟩
  · rw [← hneg, ← hneg, hxx]
  · obtain ⟨z, hz⟩ := hsurj (-l)
    exact ⟨z, by rw [hneg, hz, neg_neg]⟩

end GlobalTheory.HTPerf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianLiftLieSquareZeroHarrisTaylor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianCompletionSupIdealSmulEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianCompletionSupIdealSmulEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

universe u

namespace GlobalTheory

open Submodule

theorem lagrangian_of_idempotent_split_univ :
 ∀ (R : Type) [CommRing R] (H : Type u) [AddCommGroup H] [Module R H] (O : Type) [Ring O] (ρ : O →+* Module.End R H) (bar : O → O) (φ : LinearMap.BilinForm R H) (e : Module.End R H), e * e = e → (∀ a, ρ a * e = e * ρ a) → (∀ a, bar (bar a) = a) → (∀ a x y, φ (ρ a x) y = φ x (ρ (bar a) y)) → (∀ x y, φ (e x) y = φ x (y - e y)) → Function.Bijective φ → φ.IsRefl → ∀ G M : Submodule R H, G ⊓ M = ⊥ → G ⊔ M = LinearMap.range e → (∀ a, ∀ x ∈ G, ρ a x ∈ G) → let E := G ⊔ (LinearMap.ker e ⊓ ⨅ x ∈ G, LinearMap.ker (φ x)); (∃ N : Submodule R H, IsCompl E N) ∧ E ⊓ LinearMap.range e = G ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ ∀ a, ∀ x ∈ E, ρ a x ∈ E := by
  intro R _ H _ _ O _ ρ bar φ e he hρe hbar hφρ hφe hbij hrefl G M hGM hGMr hGst E
  have hee : ∀ x, e (e x) = e x := fun x => by
    have := LinearMap.congr_fun he x
    simpa using this
  have hrange : ∀ r ∈ LinearMap.range e, e r = r := by
    rintro r ⟨y, rfl⟩; exact hee y
  have hG : ∀ g ∈ G, e g = g := fun g hg => hrange g (hGMr ▸ (le_sup_left : G ≤ G ⊔ M) hg)
  have hM : ∀ m ∈ M, e m = m := fun m hm => hrange m (hGMr ▸ (le_sup_right : M ≤ G ⊔ M) hm)
  have hrr : ∀ x y, φ (e x) (e y) = 0 := fun x y => by rw [hφe, hee, sub_self, map_zero]
  have hkk : ∀ k ∈ LinearMap.ker e, ∀ k' ∈ LinearMap.ker e, φ k k' = 0 := by
    intro k hk k' hk'
    rw [LinearMap.mem_ker] at hk hk'
    have := hφe k k'
    rw [hk, hk', sub_zero, map_zero, LinearMap.zero_apply] at this
    exact this.symm
  have memPerp : ∀ (S : Submodule R H) y, y ∈ (⨅ x ∈ S, LinearMap.ker (φ x)) ↔ ∀ x ∈ S, φ x y = 0 := by
    intro S y; simp [Submodule.mem_iInf]

  set S := LinearMap.range e with hS
  have hc : IsCompl (M.comap S.subtype) (G.comap S.subtype) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxM hxG
      have : (x : H) ∈ G ⊓ M := ⟨hxG, hxM⟩
      rw [hGM, Submodule.mem_bot] at this
      exact Subtype.ext this
    · rw [codisjoint_iff, Submodule.eq_top_iff']
      intro x
      have hx : (x : H) ∈ G ⊔ M := by rw [hGMr]; exact x.2
      obtain ⟨g, hg, m, hm, hgm⟩ := Submodule.mem_sup.1 hx
      have hgS : g ∈ S := hGMr ▸ (le_sup_left : G ≤ G ⊔ M) hg
      have hmS : m ∈ S := hGMr ▸ (le_sup_right : M ≤ G ⊔ M) hm
      have : x = ⟨m, hmS⟩ + ⟨g, hgS⟩ := Subtype.ext (by simp [← hgm, add_comm])
      rw [this]
      exact Submodule.add_mem_sup (by simpa using hm) (by simpa using hg)
  let P : H →ₗ[R] H := S.subtype ∘ₗ (M.comap S.subtype).subtype ∘ₗ
    (Submodule.linearProjOfIsCompl _ _ hc) ∘ₗ e.rangeRestrict
  have hPG : ∀ g ∈ G, P g = 0 := by
    intro g hg
    have h1 : e.rangeRestrict g ∈ G.comap S.subtype := by
      show e g ∈ G; rw [hG g hg]; exact hg
    simp only [P, LinearMap.coe_comp, Function.comp_apply]
    have h2 := Submodule.linearProjOfIsCompl_apply_right hc ⟨_, h1⟩
    erw [h2]
    simp
  have hPM : ∀ m ∈ M, P m = m := by
    intro m hm
    have h1 : e.rangeRestrict m ∈ M.comap S.subtype := by
      show e m ∈ M; rw [hM m hm]; exact hm
    simp only [P, LinearMap.coe_comp, Function.comp_apply]
    have h2 := Submodule.linearProjOfIsCompl_apply_left hc ⟨_, h1⟩
    erw [h2]
    simp [hM m hm]

  set K := LinearMap.ker e with hK
  have hker : ∀ x, x - e x ∈ K := fun x => by
    rw [hK, LinearMap.mem_ker, map_sub, hee, sub_self]

  have hdec : ∀ k ∈ K, ∃ k₂ ∈ K ⊓ (⨅ x ∈ G, LinearMap.ker (φ x)),
      k - k₂ ∈ K ⊓ (⨅ x ∈ M, LinearMap.ker (φ x)) := by
    intro k hk
    obtain ⟨x, hx⟩ := hbij.2 ((φ k).comp P)
    have hx' : ∀ r ∈ S, φ (x - e x) r = φ k (P r) := by
      intro r hr
      rw [map_sub, LinearMap.sub_apply, hφe, hrange r hr, sub_self, map_zero, sub_zero, hx]
      rfl
    refine ⟨x - e x, ⟨hker x, ?_⟩, ⟨K.sub_mem hk (hker x), ?_⟩⟩
    · refine (memPerp _ _).2 ?_
      intro g hg
      apply hrefl
      rw [hx' g (hGMr ▸ (le_sup_left : G ≤ G ⊔ M) hg), hPG g hg, map_zero]
    · refine (memPerp _ _).2 ?_
      intro m hm
      apply hrefl
      rw [map_sub, LinearMap.sub_apply, hx' m (hGMr ▸ (le_sup_right : M ≤ G ⊔ M) hm), hPM m hm,
        sub_self]
  have hzero : ∀ k ∈ K, k ∈ (⨅ x ∈ G, LinearMap.ker (φ x)) → k ∈ (⨅ x ∈ M, LinearMap.ker (φ x)) → k = 0 := by
    intro k hk hkG hkM
    rw [memPerp] at hkG hkM
    apply hbij.1
    rw [map_zero]
    ext y
    have hy : e y ∈ G ⊔ M := by rw [hGMr]; exact LinearMap.mem_range_self e y
    obtain ⟨g, hg, m, hm, hgm⟩ := Submodule.mem_sup.1 hy
    have : y = g + m + (y - e y) := by rw [hgm]; abel
    rw [this, map_add (f := _), map_add (f := _), hrefl _ _ (hkG g hg), hrefl _ _ (hkM m hm),
      hkk k hk _ (hker y)]
    simp
  refine ⟨⟨M ⊔ (K ⊓ ⨅ x ∈ M, LinearMap.ker (φ x)), ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxE hxN
    obtain ⟨g, hg, k₁, hk₁, rfl⟩ := Submodule.mem_sup.1 hxE
    obtain ⟨m, hm, k₂, hk₂, hmk⟩ := Submodule.mem_sup.1 hxN
    have he1 : e (g + k₁) = g := by rw [map_add (f := _), hG g hg, LinearMap.mem_ker.1 hk₁.1, add_zero]
    have he2 : e (m + k₂) = m := by rw [map_add (f := _), hM m hm, LinearMap.mem_ker.1 hk₂.1, add_zero]
    have hgm : g = m := by rw [← he1, ← he2, hmk]
    have hg0 : g = 0 := by
      have : g ∈ G ⊓ M := ⟨hg, hgm ▸ hm⟩
      rwa [hGM, Submodule.mem_bot] at this
    have hm0 : m = 0 := hgm ▸ hg0
    subst hg0; subst hm0
    rw [zero_add] at hmk ⊢
    rw [zero_add] at hmk
    exact hzero k₁ hk₁.1 hk₁.2 (hmk ▸ hk₂.2)
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro h
    have hy : e h ∈ G ⊔ M := by rw [hGMr]; exact LinearMap.mem_range_self e h
    obtain ⟨g, hg, m, hm, hgm⟩ := Submodule.mem_sup.1 hy
    obtain ⟨k₂, hk₂, hk₁⟩ := hdec (h - e h) (hker h)
    have : h = (g + k₂) + (m + (h - e h - k₂)) := by rw [← sub_eq_zero, ← hgm]; abel
    rw [this]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup hg hk₂) (Submodule.add_mem_sup hm hk₁)
  · apply le_antisymm
    · rintro x ⟨hxE, hxr⟩
      obtain ⟨g, hg, k₁, hk₁, rfl⟩ := Submodule.mem_sup.1 hxE
      have h1 := hrange _ hxr
      rw [map_add (f := _), hG g hg, LinearMap.mem_ker.1 hk₁.1, add_zero] at h1
      have : k₁ = 0 := by
        have := congrArg (· - g) h1
        simpa using this.symm
      rw [this, add_zero]; exact hg
    · exact le_inf le_sup_left (hGMr ▸ le_sup_left)
  · intro x hx y hy
    obtain ⟨g, hg, k, hk, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨g', hg', k', hk', rfl⟩ := Submodule.mem_sup.1 hy
    have hkG := (memPerp G k).1 hk.2
    have hk'G := (memPerp G k').1 hk'.2
    have h1 : φ g g' = 0 := by rw [← hG g hg, ← hG g' hg', hrr]
    have h2 : φ g k' = 0 := hk'G g hg
    have h3 : φ k g' = 0 := hrefl _ _ (hkG g' hg')
    have h4 : φ k k' = 0 := hkk k hk.1 k' hk'.1
    simp [h1, h2, h3, h4]
  · intro a x hx
    obtain ⟨g, hg, k, hk, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    refine Submodule.add_mem_sup (hGst a g hg) ⟨?_, ?_⟩
    · show e (ρ a k) = 0
      have := LinearMap.congr_fun (hρe a) k
      simp only [Module.End.mul_apply] at this
      rw [← this, LinearMap.mem_ker.1 hk.1, map_zero]
    · refine (memPerp _ _).2 ?_
      intro g' hg'
      have := hφρ (bar a) g' k
      rw [hbar] at this
      rw [← this]
      exact (memPerp G k).1 hk.2 _ (hGst _ g' hg')

theorem lagrangian_completion_sup_smul_eq : ∀ (C : Type) [CommRing C] (I : Ideal C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (O : Type) [Ring O] (ρ : O →+* Module.End C H) (bar : O → O) (φ : LinearMap.BilinForm C H) (e : Module.End C H), e * e = e → (∀ a, ρ a * e = e * ρ a) → (∀ x y, φ x y = -φ y x) → (∀ a, bar (bar a) = a) → (∀ a x y, φ (ρ a x) y = φ x (ρ (bar a) y)) → (∀ x y, φ (e x) y = φ x (y - e y)) → Function.Bijective φ → ∀ F : Submodule C H, I • ⊤ ≤ F → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → (∀ x, (∀ y ∈ F, φ x y ∈ I) → x ∈ F) → (∀ x ∈ F, e x ∈ F) → ∀ G M : Submodule C H, G ⊓ M = ⊥ → G ⊔ M = LinearMap.range e → (∀ a, ∀ x ∈ G, ρ a x ∈ G) → G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e → ∃ E : Submodule C H, (∃ N : Submodule C H, IsCompl E N) ∧ E ⊓ LinearMap.range e = G ∧ E ⊔ I • ⊤ = F ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ (∀ a, ∀ x ∈ E, ρ a x ∈ E) ∧ ∀ x ∈ E, e x ∈ E := by
  intro C _ I H _ _ _ _ O _ ρ bar φ e he hρe hskew hbar hφρ hφe hbij F hIF hFiso hFlag hFe G M hGM hGMr hGst hGF
  have hrefl : φ.IsRefl := fun x y h => by rw [hskew, h, neg_zero]
  have key := lagrangian_of_idempotent_split_univ C H O ρ bar φ e he hρe hbar hφρ hφe hbij hrefl G M hGM hGMr hGst
  dsimp only at key
  obtain ⟨hcompl, hEr, hiso, hEst⟩ := key
  have hee : ∀ x, e (e x) = e x := fun x => by
    have := LinearMap.congr_fun he x
    simpa using this
  have hker : ∀ x, e (x - e x) = 0 := fun x => by rw [map_sub, hee, sub_self]
  have hrange : ∀ r ∈ LinearMap.range e, e r = r := by
    rintro r ⟨y, rfl⟩; exact hee y
  have hGr : G ≤ LinearMap.range e := hGMr ▸ (le_sup_left : G ≤ G ⊔ M)
  have hG : ∀ g ∈ G, e g = g := fun g hg => hrange g (hGr hg)
  have hkk : ∀ k k', e k = 0 → e k' = 0 → φ k k' = 0 := by
    intro k k' hk hk'
    have := hφe k k'
    rw [hk, hk', sub_zero, map_zero, LinearMap.zero_apply] at this
    exact this.symm
  have hIfun : ∀ (f : H →ₗ[C] C), ∀ t ∈ (I • ⊤ : Submodule C H), f t ∈ I := by
    intro f t ht
    have hle : (I • ⊤ : Submodule C H) ≤ Submodule.comap f (show Submodule C C from I) := by
      refine Submodule.smul_le.2 ?_
      intro r hr n _
      show f (r • n) ∈ I
      rw [map_smul, smul_eq_mul]
      exact I.mul_mem_right _ hr
    exact hle ht
  have memPerp : ∀ y, y ∈ (⨅ x ∈ G, LinearMap.ker (φ x)) ↔ ∀ x ∈ G, φ x y = 0 := by
    intro y; simp [Submodule.mem_iInf]
  have hGF' : G ≤ F := le_trans le_sup_left (hGF.le.trans inf_le_left)
  have hdecomp : ∀ z ∈ F, ∃ g ∈ G, ∃ t ∈ (I • ⊤ : Submodule C H), g + t = e z := by
    intro z hz
    have h1 : e z ∈ F ⊓ LinearMap.range e := ⟨hFe z hz, LinearMap.mem_range_self e z⟩
    rw [← hGF] at h1
    obtain ⟨g, hg, t, ht, hgt⟩ := Submodule.mem_sup.1 h1
    exact ⟨g, hg, t, ht.1, hgt⟩

  set S := LinearMap.range e with hS
  have hc : IsCompl (G.comap S.subtype) (M.comap S.subtype) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxG hxM
      have : (x : H) ∈ G ⊓ M := ⟨hxG, hxM⟩
      rw [hGM, Submodule.mem_bot] at this
      exact Subtype.ext this
    · rw [codisjoint_iff, Submodule.eq_top_iff']
      intro x
      have hx : (x : H) ∈ G ⊔ M := by rw [hGMr]; exact x.2
      obtain ⟨g, hg, m, hm, hgm⟩ := Submodule.mem_sup.1 hx
      have hgS : g ∈ S := hGMr ▸ (le_sup_left : G ≤ G ⊔ M) hg
      have hmS : m ∈ S := hGMr ▸ (le_sup_right : M ≤ G ⊔ M) hm
      have : x = ⟨g, hgS⟩ + ⟨m, hmS⟩ := Subtype.ext (by simp [← hgm])
      rw [this]
      exact Submodule.add_mem_sup (by simpa using hg) (by simpa using hm)
  let P : H →ₗ[C] H := S.subtype ∘ₗ (G.comap S.subtype).subtype ∘ₗ
    (Submodule.linearProjOfIsCompl _ _ hc) ∘ₗ e.rangeRestrict
  have hPmem : ∀ x, P x ∈ G := fun x => (Submodule.linearProjOfIsCompl _ _ hc (e.rangeRestrict x)).2
  have hPG : ∀ g ∈ G, P g = g := by
    intro g hg
    have h1 : e.rangeRestrict g ∈ G.comap S.subtype := by
      show e g ∈ G; rw [hG g hg]; exact hg
    simp only [P, LinearMap.coe_comp, Function.comp_apply]
    have h2 := Submodule.linearProjOfIsCompl_apply_left hc ⟨_, h1⟩
    erw [h2]
    simp [hG g hg]

  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := C) (M := H)
  have hsurj : Function.Surjective (Fintype.linearCombination C v) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hv]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (Fintype.linearCombination C v) LinearMap.id hsurj
  have hexp : ∀ x, x = ∑ j, s x j • v j := by
    intro x
    have := LinearMap.congr_fun hs x
    rw [LinearMap.comp_apply, Fintype.linearCombination_apply] at this
    exact this.symm
  have hy : ∀ j : Fin n, ∃ y : H, ∀ x, φ x y = s x j := by
    intro j
    obtain ⟨x₀, hx₀⟩ := hbij.2 ((LinearMap.proj j) ∘ₗ s)
    refine ⟨-x₀, fun x => ?_⟩
    rw [map_neg, hskew, neg_neg, hx₀]
    rfl
  choose y hy using hy

  have hmain : ∀ k ∈ F, e k = 0 → ∃ t ∈ (I • ⊤ : Submodule C H), e t = 0 ∧ ∀ g ∈ G, φ g (k - t) = 0 := by
    intro k hkF hke
    let f : H →ₗ[C] C := (φ.flip k) ∘ₗ P
    have hf : ∀ x, f x = φ (P x) k := fun x => rfl
    have hfI : ∀ x, f x ∈ I := fun x => by rw [hf]; exact hFiso _ (hGF' (hPmem x)) _ hkF
    refine ⟨∑ j, f (v j) • (y j - e (y j)), ?_, ?_, ?_⟩
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hfI _) Submodule.mem_top
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [map_sum, map_smul, hker]
    · intro g hg
      have h1 : ∀ j, φ g (y j - e (y j)) = s g j := by
        intro j
        have := hφe g (y j)
        rw [hG g hg] at this
        rw [← this, hy]
      have h2 : f g = ∑ j, f (v j) * s g j := by
        conv_lhs => rw [hexp g]
        set_option synthInstance.maxHeartbeats 100000 in
          simp [map_sum, map_smul, mul_comm]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum]
      simp only [map_smul, h1, smul_eq_mul]
      rw [← h2, hf, hPG g hg, sub_self]
  refine ⟨G ⊔ (LinearMap.ker e ⊓ ⨅ x ∈ G, LinearMap.ker (φ x)), hcompl, hEr, ?_, hiso, hEst, ?_⟩
  · apply le_antisymm
    · refine sup_le (sup_le hGF' ?_) hIF
      rintro w ⟨hwk, hwp⟩
      replace hwk : e w = 0 := hwk
      have hwp' := (memPerp w).1 hwp
      apply hFlag w
      intro z hz
      obtain ⟨g, hg, t, ht, hgt⟩ := hdecomp z hz
      have hz' : z = g + t + (z - e z) := by rw [hgt]; abel
      rw [hz', map_add (f := _), map_add (f := _), hskew w g, hwp' g hg, neg_zero, zero_add,
        hkk w _ hwk (hker z), add_zero]
      exact hIfun (φ w) t ht
    · intro z hz
      obtain ⟨g, hg, t, ht, hgt⟩ := hdecomp z hz
      obtain ⟨t', ht', ht'e, ht'p⟩ := hmain (z - e z) (F.sub_mem hz (hFe z hz)) (hker z)
      have hz' : z = (g + (z - e z - t')) + (t + t') := by rw [← hgt]; abel
      rw [hz']
      refine Submodule.add_mem_sup (Submodule.add_mem_sup hg ⟨?_, ?_⟩) (Submodule.add_mem _ ht ht')
      · show e (z - e z - t') = 0
        rw [map_sub, hker, ht'e, sub_zero]
      · exact (memPerp _).2 ht'p
  · intro x hx
    obtain ⟨g, hg, k, hk, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _), hG g hg, LinearMap.mem_ker.1 hk.1, add_zero]
    exact le_sup_left (a := G) hg

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianCompletionSupIdealSmulEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangianCompletion_sup_ideal_smul_eq : ∀ (C : Type) [CommRing C] (I : Ideal C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (O : Type) [Ring O] (ρ : O →+* Module.End C H) (bar : O → O) (φ : LinearMap.BilinForm C H) (e : Module.End C H), e * e = e → (∀ a, ρ a * e = e * ρ a) → (∀ x y, φ x y = -φ y x) → (∀ a, bar (bar a) = a) → (∀ a x y, φ (ρ a x) y = φ x (ρ (bar a) y)) → (∀ x y, φ (e x) y = φ x (y - e y)) → Function.Bijective φ → ∀ F : Submodule C H, I • ⊤ ≤ F → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → (∀ x, (∀ y ∈ F, φ x y ∈ I) → x ∈ F) → (∀ x ∈ F, e x ∈ F) → ∀ G M : Submodule C H, G ⊓ M = ⊥ → G ⊔ M = LinearMap.range e → (∀ a, ∀ x ∈ G, ρ a x ∈ G) → G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e → ∃ E : Submodule C H, (∃ N : Submodule C H, IsCompl E N) ∧ E ⊓ LinearMap.range e = G ∧ E ⊔ I • ⊤ = F ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ (∀ a, ∀ x ∈ E, ρ a x ∈ E) ∧ ∀ x ∈ E, e x ∈ E := by
  first | (exact @GlobalTheory.lagrangian_completion_sup_smul_eq) | (exact GlobalTheory.lagrangian_completion_sup_smul_eq) | (intros; apply GlobalTheory.lagrangian_completion_sup_smul_eq  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentImaginaryQuadraticEigenCrystal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentImaginaryQuadraticEigenCrystal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.UPel.HT


open Polynomial in
theorem exists_idem_crys : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] (ρ : D.O →+* Module.End C H) (φ : LinearMap.BilinForm C H), (∀ (c : D.O) x y, φ (ρ c x) y = φ x (ρ (D.star c).unop y)) → ∃ e : Module.End C H, e * e = e ∧ (∀ c, ρ c * e = e * ρ c) ∧ (∀ x y, φ (e x) y = φ x (y - e y)) ∧ (∀ x, ρ (algebraMap (𝓞 D.F) D.O D.ω) (e x) = tR b.ρ • e x) ∧ (∃ v : C, IsUnit v ∧ ∀ x, e x = 0 → ρ (algebraMap (𝓞 D.F) D.O D.ω) x - tR b.ρ • x = v • x) ∧ ∀ N : Submodule C H, (∀ (c : D.O), ∀ x ∈ N, ρ c x ∈ N) → ∀ x ∈ N, e x ∈ N := by
  intro p _ D R _ b C _ tR H _ _ ρ φ hφ

  have hroot : tR b.ρ ^ 2 - (D.tr : C) * tR b.ρ + (D.nm : C) = 0 := by
    have := congrArg tR b.ρ_root
    simpa only [map_sub, map_add (f := _), map_mul, map_pow, map_intCast, map_zero] using this
  have hu2 : (tR b.ρ - ((D.tr : C) - tR b.ρ)) ^ 2 = ((D.tr ^ 2 - 4 * D.nm : ℤ) : C) := by
    push_cast; linear_combination 4 * hroot
  have hunit : IsUnit (tR b.ρ - ((D.tr : C) - tR b.ρ)) := by
    have hk : (D.tr ^ 2 - 4 * D.nm : ℤ) = -((D.tr ^ 2 - 4 * D.nm).natAbs : ℤ) := by
      rw [Int.ofNat_natAbs_of_nonpos (le_of_lt D.disc_neg)]; ring
    have hcop : (D.tr ^ 2 - 4 * D.nm).natAbs.Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]
      intro h; apply D.disc_p; exact Int.natCast_dvd.mpr h
    have h1 := (b.unit _ hcop).map tR
    have : IsUnit ((tR b.ρ - ((D.tr : C) - tR b.ρ)) ^ 2) := by
      rw [hu2, hk]; push_cast; simpa using h1.neg
    exact (isUnit_pow_iff two_ne_zero).mp this
  obtain ⟨uu, huu⟩ := hunit
  have hui : (↑uu⁻¹ : C) * (tR b.ρ - ((D.tr : C) - tR b.ρ)) = 1 := by rw [← huu]; exact uu.inv_mul

  set ui : C := (↑uu⁻¹ : C) with hui_def
  set r : C := tR b.ρ with hr_def
  set W : Module.End C H := ρ (algebraMap (𝓞 D.F) D.O D.ω) with hW_def

  have hωF : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    linear_combination D.ω * D.tr_eq - D.nm_eq
  have hWrel : W * W - (D.tr : Module.End C H) * W + (D.nm : Module.End C H) = 0 := by
    have := congrArg (fun z => ρ (algebraMap (𝓞 D.F) D.O z)) hωF
    simpa only [map_sub, map_add (f := _), map_mul, map_intCast, map_zero] using this
  have hWx : ∀ x, W (W x) = (D.tr : C) • W x - (D.nm : C) • x := by
    intro x
    have := congrArg (fun f : Module.End C H => f x) hWrel
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, Module.End.intCast_apply,
      LinearMap.zero_apply] at this
    rw [← Int.cast_smul_eq_zsmul C, ← Int.cast_smul_eq_zsmul C] at this
    rw [← sub_eq_zero, ← this]; abel

  have hcomm : ∀ c : D.O, ∀ x, ρ c (W x) = W (ρ c x) := by
    intro c x
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Algebra.commutes]
  have hbar : D.bar D.ω = (D.tr : 𝓞 D.F) - D.ω := by rw [← D.tr_eq]; ring
  have hWadj : ∀ x y, φ (W x) y = φ x ((D.tr : C) • y - W y) := by
    intro x y
    rw [hW_def, hφ, D.star_F, MulOpposite.unop_op, hbar, map_sub, map_intCast, map_sub, map_intCast,
      LinearMap.sub_apply, Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul C]
  refine ⟨ui • (W - ((D.tr : C) - r) • 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul,
      map_sub, hWx]
    match_scalars
    all_goals first | linear_combination ui * hui | linear_combination (-ui * ((D.tr:C) - r)) * hui - ui ^ 2 * hroot | linear_combination (ui * ((D.tr:C) - r)) * hui + ui ^ 2 * hroot | linear_combination (-ui * ((D.tr:C) - r)) * hui + ui ^ 2 * hroot | linear_combination (ui * ((D.tr:C) - r)) * hui - ui ^ 2 * hroot
  · intro c; ext x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul,
      map_sub, hcomm]
  · intro x y
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_sub,
      LinearMap.smul_apply, LinearMap.sub_apply, hWadj, smul_eq_mul]
    linear_combination (φ x y) * hui
  · intro x
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_sub, hWx]
    match_scalars
    all_goals first | linear_combination (0:C) | linear_combination ui * hroot | linear_combination -ui * hroot
  · refine ⟨-(r - ((D.tr : C) - r)), by rw [← huu]; exact (Units.isUnit uu).neg, ?_⟩
    intro x hx
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply] at hx
    have h2 : W x - ((D.tr : C) - r) • x = 0 := by
      have := congrArg (fun z => (↑uu : C) • z) hx
      simpa [smul_smul, hui_def] using this
    rw [sub_eq_zero] at h2
    rw [h2]
    match_scalars
    ring
  · intro N hN x hx
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
    exact N.smul_mem _ (N.sub_mem (hN _ x hx) (N.smul_mem _ hx))

end GlobalTheory.UPel.HT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentImaginaryQuadraticEigenCrystalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_imaginaryQuadratic_eigen_crystal : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] (ρ : D.O →+* Module.End C H) (φ : LinearMap.BilinForm C H), (∀ (c : D.O) x y, φ (ρ c x) y = φ x (ρ (D.star c).unop y)) → ∃ e : Module.End C H, e * e = e ∧ (∀ c, ρ c * e = e * ρ c) ∧ (∀ x y, φ (e x) y = φ x (y - e y)) ∧ (∀ x, ρ (algebraMap (𝓞 D.F) D.O D.ω) (e x) = tR b.ρ • e x) ∧ (∃ v : C, IsUnit v ∧ ∀ x, e x = 0 → ρ (algebraMap (𝓞 D.F) D.O D.ω) x - tR b.ρ • x = v • x) ∧ ∀ N : Submodule C H, (∀ (c : D.O), ∀ x ∈ N, ρ c x ∈ N) → ∀ x ∈ N, e x ∈ N := by
  first | (exact @GlobalTheory.UPel.HT.exists_idem_crys) | (exact GlobalTheory.UPel.HT.exists_idem_crys) | (intros; apply GlobalTheory.UPel.HT.exists_idem_crys  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianLiftLieSquareZeroHarrisTaylor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.HTSummand

theorem exists_lagrangian_lift_lie : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (φ : LinearMap.BilinForm C H), (∀ x y, φ x y = -φ y x) → Function.Bijective φ → (∀ (c : D.O) x y, φ (ρ c x) y = φ x (ρ (D.star c).unop y)) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → (∀ x, (∀ y ∈ F, φ x y ∈ I) → x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d, ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ F → ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ E : Submodule C H, (∃ M : Submodule C H, IsCompl E M) ∧ E ⊔ I • ⊤ = F ∧ (∀ (c : D.O), ∀ x ∈ E, ρ c x ∈ E) ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ ∀ d, ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ E → ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E := by
  intro p _ D R _ b C _ _ _ I hI tR H _ _ _ _ ρ hproj φ hskew hbij hadj F hIF hFO hFiso hFlag hE' hLie
  obtain ⟨e, he, hρe, hφe, hωe, ⟨v, hv, hωk⟩, hestab⟩ := GlobalTheory.T.exists_idempotent_imaginaryQuadratic_eigen_crystal p D R b C tR H ρ φ hadj
  have hFe := hestab F hFO
  have hLie' : ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F := by
    rintro d ⟨y, rfl⟩
    exact hLie _ (by rw [hωe, sub_self]; exact F.zero_mem)
  have hcore : ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : D.O), ∀ x ∈ G, ρ c x ∈ G) ∧ G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧ ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
    by_cases hp : IsUnit (p : C)
    · exact GlobalTheory.T.exists_liftSummand_lie_residueCharZero p D R b C I hI hp tR H ρ hproj e he hρe hωe F hIF hFO hFe hE' hLie'
    · exact GlobalTheory.T.exists_lieCondition_summand_residueCharP p D R b C I hI ((IsLocalRing.mem_maximalIdeal _).2 hp) tR H ρ hproj e he hρe hωe F hIF hFO hFe hE' hLie'
  obtain ⟨G, M, hGM, hGMr, hGO, hGF, hGLie⟩ := hcore
  obtain ⟨E, hEc, hEe, hEF, hEiso, hEO, hEst⟩ := GlobalTheory.T.lagrangianCompletion_sup_ideal_smul_eq C I H D.O ρ (fun a => (D.star a).unop) φ e he hρe hskew (fun a => D.star_star a) hadj hφe hbij F hIF hFiso hFlag hFe G M hGM hGMr hGO hGF
  refine ⟨E, hEc, hEF, hEO, hEiso, ?_⟩
  intro d hd
  have hGE : G ≤ E := hEe ▸ inf_le_left
  set k := d - e d with hkdef
  have hek : e k = 0 := by
    have := LinearMap.congr_fun he d
    simp only [Module.End.mul_apply] at this
    simp [hkdef, this]
  have hkE : k ∈ E := by
    set x := ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d with hx
    have h1 : x - e x ∈ E := E.sub_mem hd (hEst _ hd)
    have h2 : x - e x = ρ (algebraMap (𝓞 D.F) D.O D.ω) k - tR b.ρ • k := by
      have hc := LinearMap.congr_fun (hρe (algebraMap (𝓞 D.F) D.O D.ω)) d
      simp only [Module.End.mul_apply] at hc
      simp only [hx, hkdef, map_sub, LinearMap.map_smul, smul_sub, hc]
      abel
    rw [h2, hωk k hek] at h1
    obtain ⟨u, rfl⟩ := hv
    have := E.smul_mem (↑u⁻¹ : C) h1
    rwa [smul_smul, Units.inv_mul, one_smul] at this
  obtain ⟨w, hw, hdw⟩ := hGLie (e d) ⟨d, rfl⟩
  refine ⟨w, fun i c => hGE (hw i c), ?_⟩
  have : d - ∑ i, w i = (e d - ∑ i, w i) + k := by rw [hkdef]; abel
  rw [this]
  exact E.add_mem (hGE hdw) hkE

end GlobalTheory.HTSummand
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianLiftLieSquareZeroHarrisTaylorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lagrangian_lift_lie_squareZero_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (φ : LinearMap.BilinForm C H), (∀ x y, φ x y = -φ y x) → Function.Bijective φ → (∀ (c : D.O) x y, φ (ρ c x) y = φ x (ρ (D.star c).unop y)) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → (∀ x, (∀ y ∈ F, φ x y ∈ I) → x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d, ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ F → ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ E : Submodule C H, (∃ M : Submodule C H, IsCompl E M) ∧ E ⊔ I • ⊤ = F ∧ (∀ (c : D.O), ∀ x ∈ E, ρ c x ∈ E) ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ ∀ d, ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ E → ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E := by
  first | exact @GlobalTheory.HTSummand.exists_lagrangian_lift_lie | exact GlobalTheory.HTSummand.exists_lagrangian_lift_lie | (intros; apply GlobalTheory.HTSummand.exists_lagrangian_lift_lie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsIsotropicStableSummand
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.HTSummand

theorem exists_summand : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∃ E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E) ∧ (∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ E → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀
  obtain ⟨red, hfin, hproj, hsurj, hker, hcorr, hpush, E', M', hE'M', hE'⟩ :=
    GlobalTheory.CrysRed.exists_crysRed C C₀ π hπ hsq o₀.A o₀.ab D.O o₀.act
  haveI := hfin
  haveI := hproj
  obtain ⟨φ₀, hφ₀, huniq, hadj, φ', hφ', hrel⟩ := GlobalTheory.HTDefLift.exists_crysForm p D R b N C C₀ π hπ hsq tR o₀
  obtain ⟨hskew, hbij⟩ := GlobalTheory.HTPerf.skew_bijective p D R b N C C₀ π hπ hsq tR o₀ φ₀ hφ₀
  haveI : Nontrivial C₀ := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have ht : RingHom.ker π = ⊤ := eq_top_iff.2 fun x _ ↦ RingHom.mem_ker.2 (Subsingleton.elim _ _)
    rw [ht, ← Ideal.one_eq_top, one_pow] at hsq
    exact one_ne_zero hsq
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  have hlagr := GlobalTheory.HTLagr.fil_lagrangian p D R b N C₀ _ o₀ φ' (GlobalTheory.AbelianDim.exists_relDim C₀ o₀.A o₀.ab) hφ'
  have hlie := GlobalTheory.HTSummand.lie_mod_fil p D R b N C₀ (π.comp tR) _ (GlobalTheory.Cris.spMap_comp tR π).symm o₀
  have hprojF := GlobalTheory.T.crystal_projective_over_tensor_ringOfIntegers D.F C C₀ π hπ hsq o₀.A o₀.ab D.O o₀.act
  have hI2 : RingHom.ker π ^ 2 = ⊥ := hsq
  let F : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A) := (Fil o₀.A).comap red
  have hredI : ∀ x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)), red x = 0 := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr n _ ↦ ?_) (fun x y hx hy ↦ ?_)
    · rw [LinearMap.map_smulₛₗ, RingHom.mem_ker.1 hr, zero_smul]
    · rw [map_add (f := _), hx, hy, add_zero]
  have hIF : RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)) ≤ F := fun x hx ↦ by
    show red x ∈ Fil o₀.A
    rw [hredI x hx]; exact zero_mem _
  have hFstab : ∀ (c : D.O), ∀ x ∈ F, GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act c x ∈ F := by
    intro c x hx
    show red _ ∈ Fil o₀.A
    rw [hpush]
    haveI := o₀.act.hom c
    exact push_mem_Fil (o₀.act.act c) hx
  have hFiso : ∀ x ∈ F, ∀ y ∈ F, φ₀ x y ∈ RingHom.ker π := by
    intro x hx y hy
    rw [RingHom.mem_ker, ← hrel x (red x) y (red y) ((hcorr _ _).2 rfl) ((hcorr _ _).2 rfl)]
    exact hlagr.1 _ hx _ hy
  have hFlagr : ∀ x, (∀ y ∈ F, φ₀ x y ∈ RingHom.ker π) → x ∈ F := by
    intro x hx
    show red x ∈ Fil o₀.A
    refine hlagr.2 _ fun z hz ↦ ?_
    obtain ⟨y, rfl⟩ := hsurj z
    rw [hrel x (red x) y (red y) ((hcorr _ _).2 rfl) ((hcorr _ _).2 rfl)]
    exact RingHom.mem_ker.1 (hx y hz)
  have hE'F : E' ⊔ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)) = F := by
    refine le_antisymm (sup_le (fun d hd ↦ (hE' _).2 ⟨d, hd, rfl⟩) hIF) fun x hx ↦ ?_
    obtain ⟨d, hd, he⟩ := (hE' (red x)).1 hx
    have hx' : x = d + (x - d) := by abel
    rw [hx']
    exact Submodule.add_mem_sup hd (hker _ (by rw [map_sub, he, sub_self]))
  have hFlie : ∀ d, GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ F →
      ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F),
        GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧
        d - ∑ i, w i ∈ F := by
    intro d hd
    have hd' : red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d)
        ∈ Fil o₀.A := hd
    rw [map_sub, LinearMap.map_smulₛₗ, hpush] at hd'
    obtain ⟨w₀, hw₀, hsum⟩ := hlie (red d) hd'
    choose w hw using fun i ↦ hsurj (w₀ i)
    refine ⟨w, fun i c ↦ ?_, ?_⟩
    · show red _ ∈ Fil o₀.A
      rw [map_sub, LinearMap.map_smulₛₗ, hpush, hw]
      exact hw₀ i c
    · show red _ ∈ Fil o₀.A
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum]
      simp only [hw]
      exact hsum
  obtain ⟨E, ⟨M, hEM⟩, hEF, hstab, hiso, hlieE⟩ := GlobalTheory.T.exists_lagrangian_lift_lie_squareZero_harrisTaylor p D R b C (RingHom.ker π) hI2 tR
    (Crys (divided₂ hsq) (spMap π) o₀.A) (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act) hprojF φ₀ hskew hbij hadj
    F hIF hFstab hFiso hFlagr ⟨E', M', hE'M', hE'F⟩ hFlie
  refine ⟨E, ⟨M, hEM⟩, fun y ↦ ⟨fun hy ↦ ?_, fun ⟨d, hd, hc⟩ ↦ ?_⟩, fun c d hd ↦ hstab c d hd,
    fun φ hφ x hx y hy ↦ by rw [huniq φ hφ]; exact hiso x hx y hy, fun d hd ↦ hlieE d hd⟩
  · obtain ⟨x, rfl⟩ := hsurj y
    have hx : x ∈ F := hy
    rw [← hEF] at hx
    obtain ⟨d, hd, j, hj, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨d, hd, (hcorr _ _).2 (by rw [map_add (f := _), hredI j hj, add_zero])⟩
  · rw [← (hcorr d y).1 hc]
    have : d ∈ F := hEF ▸ Submodule.mem_sup_left hd
    exact this

end GlobalTheory.HTSummand
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsIsotropicStableSummandStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_exists_isotropic_stable_summand : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∃ E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E) ∧ (∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ E → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E) := by
  first | exact @GlobalTheory.HTSummand.exists_summand | exact GlobalTheory.HTSummand.exists_summand | (intros; apply GlobalTheory.HTSummand.exists_summand <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftSquareZeroArtinian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.UPel.HT

theorem exists_sqZero_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ t)), ∃ o : GlobalTheory.UPel.HT.Obj b N t, Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)) := by
  intro p _ D R _ b N hN C C₀ _ _ _ _ π hπ hsq' t o₀
  have hsq : RingHom.ker π ^ 2 = 0 := by rw [hsq']; rfl
  obtain ⟨tR, rfl⟩ : ∃ tR : R →+* C, t = spMap tR :=
    ⟨(Spec.preimage t).hom, by simp [spMap]⟩
  obtain ⟨E, hEc, hEf, hEs, hEi, hEl⟩ := GlobalTheory.T.harrisTaylor_exists_isotropic_stable_summand p D R b N C C₀ π hπ hsq tR o₀
  obtain ⟨A, _, i, h, act, hA, hE, hact⟩ := GlobalTheory.T.harrisTaylor_exists_lift_orderAction_hodge_summand p D R b N C C₀ π hπ hsq tR o₀ E hEc hEf hEs
  haveI : IsCommMonObj A := hA.comm
  subst hE
  obtain ⟨P, φ₂, hP, r1, r2, hsym, hamp, hker, hros, hsq2, hpol⟩ :=
    GlobalTheory.T.harrisTaylor_exists_polarisation_bundle_lift p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEi
  obtain ⟨eta, e1, e2, e3, e4, e5⟩ := GlobalTheory.T.harrisTaylor_primeToP_level_lift_squareZero p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hN P φ₂ hP hsq2 hpol
  exact ⟨{ A := A
           ab := hA
           act := act
           P := P
           isLB := hP
           rig₁ := r1
           rig₂ := r2
           symm := hsym
           ample := hamp
           kerP := hker
           rosati := hros
           lie := fun R' _ β x hx v hv => GlobalTheory.T.harrisTaylor_lift_lie_of_hodge_summand_lie p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEl R' β x hx v hv
           lieRank := fun k _ _ x β hx j => GlobalTheory.T.harrisTaylor_lieMultiplicity_squareZeroLift p D R b N C C₀ π hπ hsq tR o₀ A i h act hact k x β hx j
           eta := eta
           eta_add := e1
           eta_lin := e2
           eta_ker := e3
           geom := e4 },
    ⟨{ φ := i
       φ₂ := φ₂
       cart := h
       sq := hsq2
       act := hact
       pol := hpol
       eta := e5 }⟩⟩

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftSquareZeroArtinianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_exists_lift_squareZero_artinian : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ t)), ∃ o : GlobalTheory.UPel.HT.Obj b N t, Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)) := by
  first | (exact @GlobalTheory.UPel.HT.exists_sqZero_lift) | (exact GlobalTheory.UPel.HT.exists_sqZero_lift) | (intros; apply GlobalTheory.UPel.HT.exists_sqZero_lift <;> assumption)
end
