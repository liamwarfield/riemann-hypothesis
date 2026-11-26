module

public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackProdInjectiveBirigidifiedGaloisIsogeny
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPToLiftReal
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.ThetaPRead

theorem isThetaP_restrict {G' H' S' Si Tau Y ι : Type} [MeasurableSpace H'] [AddCommGroup Si] [Module ℂ Si]
    [AddCommGroup Tau] [Module ℂ Tau] [AddCommGroup Y] [Module ℂ Y]
    {M : ι → Type} [∀ ρ, AddCommGroup (M ρ)] [∀ ρ, Module ℂ (M ρ)] (low : ∀ ρ, Submodule ℂ (M ρ))
    {ν : Measure H'} {𝓕 : Set H'} {th : G' → H' → S' → ℂ} {pt : Si → S'}
    {io : (⨂[ℂ] ρ, low ρ) →ₗ[ℂ] Tau →ₗ[ℂ] Si} (L : Y →ₗ[ℂ] (H' → Tau)) (hL : Function.Injective L)
    (S : Submodule ℂ (H' → Tau)) (U : Y →ₗ[ℂ] ((∀ ρ, M ρ) →ₘₗ[ℂ] (G' → ℂ)))
    (h : ∃ thP, Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range L) thP ∧
      ∀ x (v : ∀ ρ, low ρ), U x (fun ρ => v ρ) = thP (L.rangeRestrict x) (PiTensorProduct.tprod ℂ v)) :
    Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range L ⊓ S)
      (LinearMap.lcomp ℂ (G' → ℂ) (PiTensorProduct.map fun ρ => (low ρ).subtype) ∘ₗ
        (PiTensorProduct.lift : ((∀ ρ, M ρ) →ₘₗ[ℂ] (G' → ℂ)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ U ∘ₗ
        (LinearEquiv.ofInjective L hL).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left) := by
  obtain ⟨thP, hP, hv⟩ := h
  have key : ∀ f : ↥(LinearMap.range L ⊓ S),
      (LinearMap.lcomp ℂ (G' → ℂ) (PiTensorProduct.map fun ρ => (low ρ).subtype) ∘ₗ
        (PiTensorProduct.lift : ((∀ ρ, M ρ) →ₘₗ[ℂ] (G' → ℂ)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ U ∘ₗ
        (LinearEquiv.ofInjective L hL).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left) f =
        thP (Submodule.inclusion inf_le_left f) := by
    intro f
    set x := (LinearEquiv.ofInjective L hL).symm (Submodule.inclusion inf_le_left f) with hx
    have h1 : L.rangeRestrict x = Submodule.inclusion inf_le_left f := by
      have := LinearEquiv.apply_symm_apply (LinearEquiv.ofInjective L hL) (Submodule.inclusion inf_le_left f)
      rw [← hx] at this
      rw [← this]
      rfl
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.lcomp_apply, LinearEquiv.coe_coe, PiTensorProduct.map_tprod, Submodule.coe_subtype,
      PiTensorProduct.lift.tprod]
    rw [← hx, hv x v, h1]
  refine ⟨fun f e g => ?_, fun f e g => ?_⟩
  · exact hP.integ (Submodule.inclusion inf_le_left f) e g
  · rw [key f]
    exact hP.eq _ e g

theorem isThetaP_toLiftReal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.thP_thF → ∀ μ i, Lift.IsThetaP ((RecTie.toLiftReal R F tupT hm hTop hinj).measV μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).fdV μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).thW μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).ptW μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).ioK i) ((RecTie.toLiftReal R F tupT hm hTop hinj).Amt μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).thC μ i) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj h μ i
  exact isThetaP_restrict _ _ _ _ _ (h i (tupT μ))

end GlobalTheory.ThetaPRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatedPairsSamePolarization
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatedPairsSamePolarization
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid.Pair

def innerAlgEquiv (R : Type) {A : Type} [CommRing R] [Ring A] [Algebra R A] (y : Aˣ) : A ≃ₐ[R] A :=
  GlobalTheory.InnerAutomorphism.innerAut R y

theorem rel_pol_c : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G), P.Rel Q → Q.pol = P.pol ∧ Q.c = P.c := by
  intro p _ G P Q ⟨y, s, _, hβ, hγ⟩
  refine ⟨?_, ?_⟩
  · have h := minpoly.algEquiv_eq (innerAlgEquiv G.F y) (P.γ : G.C)
    simp only [pol, hγ, Units.val_mul]
    exact h
  · have hsh : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
      intro a b; simp [sh]
    have hy : ∀ X : G.C, sh G (y : G.C) * (sh G ((y⁻¹ : G.Cˣ) : G.C) * X) = X := by
      intro X
      rw [← mul_assoc, ← hsh, Units.inv_mul, sh, map_one, MulOpposite.unop_one, one_mul]
    have core : (y : G.C) * P.γ * ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * P.β * sh G y) *
        (sh G ((y⁻¹ : G.Cˣ) : G.C) * (sh G P.γ * sh G y)) = (P.c : ℚ) • ((y : G.C) * P.β * sh G y) := by
      calc (y : G.C) * P.γ * ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * P.β * sh G y) *
            (sh G ((y⁻¹ : G.Cˣ) : G.C) * (sh G P.γ * sh G y))
          = y * (P.γ * P.β * sh G P.γ) * sh G y := by
            simp only [mul_assoc, Units.inv_mul_cancel_left, hy]
        _ = _ := by
            rw [P.sim, ← Algebra.smul_def]
            simp only [mul_smul_comm, smul_mul_assoc]
    have key : algebraMap ℚ G.C (Q.c : ℚ) * Q.β = algebraMap ℚ G.C (P.c : ℚ) * Q.β := by
      rw [← Q.sim, hγ, hβ]
      simp only [Units.val_mul, hsh, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
      rw [core, smul_comm]
    have hinj : Function.Injective (algebraMap ℚ G.C) := (algebraMap ℚ G.C).injective
    exact Units.ext (hinj ((Units.mul_left_inj Q.β).mp key))

end GlobalTheory.LKMid.Pair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatedPairsSamePolarizationStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.related_pairs_same_polarization : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G), P.Rel Q → Q.pol = P.pol ∧ Q.c = P.c := by
  first | (exact @GlobalTheory.LKMid.Pair.rel_pol_c) | (exact GlobalTheory.LKMid.Pair.rel_pol_c) | (intros; apply GlobalTheory.LKMid.Pair.rel_pol_c  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleSymmetric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleSymmetric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.HeckeSym

theorem grpSchemeSquareProductMap_comm_swap {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (ψ : A ⟶ A') :
    GlobalTheory.UPel.HT.Hecke.sq2 ψ ≫ (lift (snd A' A') (fst A' A')).left =
      (lift (snd A A) (fst A A)).left ≫ GlobalTheory.UPel.HT.Hecke.sq2 ψ := by
  unfold GlobalTheory.UPel.HT.Hecke.sq2
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp

theorem descended_symm : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ (m : ℕ) (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd A' A') (fst A' A')).left) := by
  intro p _ D R _ b M S s o A' _ _ ψ G hA' hψ hG m P' hP' H r₁ r₂
  set sw' := (lift (snd A' A') (fst A' A')).left with hsw'
  set sw := (lift (snd o.A o.A) (fst o.A o.A)).left with hsw
  set q := GlobalTheory.UPel.HT.Hecke.sq2 ψ with hq
  have hQ : (P'.pull sw').IsLB := pull_isLB hP' sw'

  have ax : ∀ (e₁ e₂ : A' ⟶ G2 A'), e₁ ≫ lift (snd A' A') (fst A' A') = e₂ →
      (∃ t : (P'.pull e₂.left).Gen, t.IsGen) → ∃ t : ((P'.pull sw').pull e₁.left).Gen, t.IsGen := by
    intro e₁ e₂ he ⟨t, ht⟩
    have hc : ∀ k : PUnit, (fun _ : PUnit => e₁.left) k ≫ sw' = 𝟙 _ ≫ (fun _ : PUnit => e₂.left) k := by
      intro _
      rw [Category.id_comp, hsw', ← Over.comp_left, he]
    have iso : LBIso ((P'.pull sw').pull e₁.left) (P'.pull e₂.left) :=
      LBIso.chartPull (chartPullLinComb P' sw' (fun _ => e₁.left) (fun _ => e₂.left) (fun _ => 1) (𝟙 _) hc)
        (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hP' _))
    exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hP' _) (pull_isLB hQ _) iso.symm t ht
  have a₁ := ax (lift (1 : A' ⟶ A') (𝟙 A')) (lift (𝟙 A') (1 : A' ⟶ A')) (by ext <;> simp) r₂
  have a₂ := ax (lift (𝟙 A') (1 : A' ⟶ A')) (lift (1 : A' ⟶ A') (𝟙 A')) (by ext <;> simp) r₁

  have E := grpSchemeSquareProductMap_comm_swap ψ
  have hPow : (GlobalTheory.UPel.HT.Hecke.lbPow o.P m).IsLB := DVR.linComb_isLB _ o.isLB _ _
  have step1 : LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m)
      (LB.LinComb (o.P.pull sw) (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1)) :=
    GlobalTheory.PowPrimitive.lbIso_linComb o.symm _ _
  have step2 : LBIso (LB.LinComb (o.P.pull sw) (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1))
      ((P'.pull sw').pull q) := by
    refine LBIso.chartPull (h := sw)
      (chartPullLinComb o.P sw (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) sw (fun _ => by simp))
      (chartPullLinComb P' sw' (fun _ : PUnit => q) (fun _ : PUnit => q) (fun _ => 1) sw (fun _ => E)) H
  have hmid : (LB.LinComb (o.P.pull sw) (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1)).IsLB :=
    DVR.linComb_isLB _ (pull_isLB o.isLB _) _ _
  have key : LBIso (P'.pull q) ((P'.pull sw').pull q) :=
    LBIso.trans (pull_isLB hP' q) hPow (pull_isLB hQ q) H.symm
      (LBIso.trans hPow hmid (pull_isLB hQ q) step1 step2)
  exact GlobalTheory.T.pullback_prod_injective_birigidified_galois_isogeny S o.A A' G ψ o.ab hA' hψ hG P' (P'.pull sw') hP' hQ r₁ r₂ a₁ a₂ key

end GlobalTheory.HeckeSym
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleSymmetricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_birigidified_bundle_symmetric : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ (m : ℕ) (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd A' A') (fst A' A')).left) := by
  first | exact @GlobalTheory.HeckeSym.descended_symm | exact GlobalTheory.HeckeSym.descended_symm | (intros; apply GlobalTheory.HeckeSym.descended_symm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionFiniteEtaleAbelianVarietyCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionFiniteEtaleAbelianVarietyCharZero
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OActFinEt

variable {S : Scheme.{0}} {O : Type} [CommRing O] {A : Over S} [GrpObj A]

theorem act_zero (act : OAct O A) : act.act 0 = 1 :=
  mul_left_cancel (a := act.act 0) (by rw [_root_.mul_one, ← act.add, add_zero])

theorem act_natCast (act : OAct O A) : ∀ n : ℕ, act.act (n : O) = 𝟙 A ^ n
  | 0 => by rw [Nat.cast_zero, act_zero, pow_zero]
  | n + 1 => by rw [Nat.cast_succ, act.add, act_natCast act n, act.one, pow_succ]

theorem exists_natCast_dvd {E : Type} [Field E] [NumberField E] (b : 𝓞 E) (hb : b ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ b ∣ (n : 𝓞 E) := by
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb
  · exact Ideal.mem_span_singleton.1 (Ideal.absNorm_mem _)

theorem finite_etale_act (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k]
    [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ) :
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ b : 𝓞 E, b ≠ 0 →
      IsFinite (act.act b).left ∧ Etale (act.act b).left ∧
        Finite {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act b = 1} := by
  intro hA hg b hb
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  obtain ⟨n, hn0, b', hb'⟩ := exists_natCast_dvd b hb
  have hnk : (n : k) ≠ 0 := Nat.cast_ne_zero.2 hn0
  have hu : IsUnit (n : Γ(Sp k, ⊤)) := by
    simpa using (Ne.isUnit hnk).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have h1 : act.act b ≫ act.act b' = 𝟙 A ^ n := by rw [← act.mul, ← hb', act_natCast]
  have h2 : act.act b' ≫ act.act b = 𝟙 A ^ n := by rw [← act.mul, mul_comm, ← hb', act_natCast]
  haveI := act.hom b
  haveI := act.hom b'
  haveI hF : IsFinite (𝟙 A ^ n).left := GrpTangent.isFinite_id_pow A hu
  haveI hE : Etale (𝟙 A ^ n).left := GrpTangent.etale_id_pow A hu
  haveI : IsSeparated A.hom := inferInstance
  have hsep : ∀ f : A ⟶ A, IsSeparated f.left := fun f => by
    have : IsSeparated (f.left ≫ A.hom) := by rw [Over.w f]; infer_instance
    exact IsSeparated.of_comp f.left A.hom
  haveI := hsep (act.act b')
  haveI : IsFinite ((act.act b).left ≫ (act.act b').left) := by rw [← Over.comp_left, h1]; exact hF
  haveI hfin : IsFinite (act.act b).left := IsFinite.of_comp _ (act.act b').left
  haveI : FormallyUnramified ((act.act b).left ≫ (act.act b').left) := by
    rw [← Over.comp_left, h1]; infer_instance
  haveI : FormallyUnramified (act.act b).left := FormallyUnramified.of_comp _ (act.act b').left
  haveI : Flat (act.act b).left :=
    (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected k A hA _ inferInstance
      hfin).1
  haveI : LocallyOfFinitePresentation ((act.act b).left ≫ A.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFinitePresentation (act.act b).left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp _ A.hom
  refine ⟨hfin, Etale.of_formallyUnramified_of_flat _, ?_⟩
  have hfinN := GlobalTheory.Published.AbMulNSt.finite GlobalTheory.abMulN_holds hA hg hnk
  refine Finite.of_injective (β := {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ n = 1})
    (fun x => ⟨x.1, ?_⟩) ?_
  · have := congrArg (· ≫ act.act b') x.2
    simp only [Category.assoc, h1, one_comp] at this
    rwa [comp_pow, Category.comp_id] at this
  · intro x y h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h

end GlobalTheory.OActFinEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionFiniteEtaleAbelianVarietyCharZeroStatement
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringAction_finite_etale_abelianVariety_charZero : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ b : 𝓞 E, b ≠ 0 → IsFinite (act.act b).left ∧ Etale (act.act b).left ∧ Finite {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act b = 1} := by
  first | exact @GlobalTheory.OActFinEt.finite_etale_act | exact GlobalTheory.OActFinEt.finite_etale_act | (intros; apply GlobalTheory.OActFinEt.finite_etale_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairRegularImageAtP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairRegularImageAtP
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

theorem charpoly_rho_eq_map_pol (G : HTGroup p) (P : Pair G) (w : Fin G.m) :
    (G.rho w (P.γ : G.C)).charpoly = P.pol.map (G.embW w) := by
  letI : Algebra G.F (G.Fw w) := (G.embW w).toAlgebra
  have hg : ∀ a, G.rho w (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) a :=
    fun a => by rw [G.rho_F, Matrix.algebraMap_eq_diagonal]; rfl
  let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) (G.Fw w) := { G.rho w with commutes' := hg }
  let L : G.Fw w ⊗[G.F] G.C →ₐ[G.Fw w] Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    Algebra.TensorProduct.lift (Algebra.ofId (G.Fw w) _) g (fun r _ => Algebra.commute_algebraMap_left r _)
  haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)
  have hL : ∀ x : G.C, L ((1 : G.Fw w) ⊗ₜ x) = G.rho w x := fun x => by
    show (Algebra.TensorProduct.lift _ g _) ((1 : G.Fw w) ⊗ₜ x) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  set γ : G.C := (P.γ : G.C) with hγ
  have hdeg : (minpoly G.F γ).natDegree = G.n := P.reg.1
  have hli : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hdeg] at this
    exact this
  have hT : LinearIndependent (G.Fw w) (fun i : Fin G.n => (1 : G.Fw w) ⊗ₜ[G.F] (γ ^ (i : ℕ))) := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact Module.Flat.linearIndependent_one_tmul hli
  have hM : LinearIndependent (G.Fw w) (fun i : Fin G.n => (G.rho w γ) ^ (i : ℕ)) := by
    have := hT.map' L.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
    have e : (fun i : Fin G.n => (G.rho w γ) ^ (i : ℕ)) =
        L.toLinearMap ∘ (fun i : Fin G.n => (1 : G.Fw w) ⊗ₜ[G.F] (γ ^ (i : ℕ))) := by
      funext i
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply]
      rw [hL, map_pow]
    rw [e]
    exact this
  have hint : IsIntegral (G.Fw w) (G.rho w γ) := Algebra.IsIntegral.isIntegral _
  set q := minpoly (G.Fw w) (G.rho w γ) with hq
  have hqm : q.Monic := minpoly.monic hint
  have hqdeg : G.n ≤ q.natDegree := by
    by_contra hlt
    push_neg at hlt
    have h0 : aeval (G.rho w γ) q = 0 := minpoly.aeval _ _
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at h0
    have h1 := Fintype.linearIndependent_iff.1 hM (fun i => q.coeff i) h0 ⟨q.natDegree, hlt⟩
    have h2 : q.coeff q.natDegree = 1 := hqm.coeff_natDegree
    rw [h2] at h1
    exact one_ne_zero h1
  have hpol : aeval (G.rho w γ) (P.pol.map (G.embW w)) = 0 := by
    have h : aeval (g γ) (minpoly G.F γ) = 0 := by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    change aeval (G.rho w γ) ((minpoly G.F γ).map (algebraMap G.F (G.Fw w))) = 0
    rw [Polynomial.aeval_map_algebraMap]
    exact h
  have hFint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hm1 : (P.pol.map (G.embW w)).Monic := (minpoly.monic hFint).map _
  have hn1 : (P.pol.map (G.embW w)).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact hdeg
  have e1 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hm1 (minpoly.dvd _ _ hpol)
    (by rw [hn1]; exact hqdeg)
  have e2 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm (Matrix.charpoly_monic _)
    (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hqdeg)
  rw [e2, e1]

theorem atP_regular : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G),
    (∀ w, (P.atP.2 w).val.charpoly = P.pol.map (G.embW w)) ∧ regular₂ G P.atP ∧
      ∀ y : P.cent, locC G y.1 ∈ Subgroup.centralizer {P.atP} := by
  intro p _ G P
  have h1 : ∀ w, (P.atP.2 w).val.charpoly = P.pol.map (G.embW w) := fun w => charpoly_rho_eq_map_pol G P w
  refine ⟨h1, fun w => ?_, fun y => ?_⟩
  · show (P.atP.2 w).val.charpoly.Separable
    rw [h1]
    exact P.reg.2.map
  · rw [Subgroup.mem_centralizer_singleton_iff]
    show locC G y.1 * locC G (P.γ, P.c) = locC G (P.γ, P.c) * locC G y.1
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext y.2.1 (mul_comm _ _)

end GlobalTheory.LKMid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairRegularImageAtPStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudePair_regular_image_at_p : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G), (∀ w, (P.atP.2 w).val.charpoly = P.pol.map (G.embW w)) ∧ regular₂ G P.atP ∧ ∀ y : P.cent, locC G y.1 ∈ Subgroup.centralizer {P.atP} := by
  first | (exact @GlobalTheory.LKMid.atP_regular) | (exact GlobalTheory.LKMid.atP_regular) | (intros; apply GlobalTheory.LKMid.atP_regular  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfMemAdjoinInv
open GlobalTheory.LN

namespace GlobalTheory.ValCrit


open Polynomial in
theorem _root_.GlobalTheory.ValCrit.isIntegral_of_mem_adjoin_inv {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (y : K) (hy : y ≠ 0)
    (h : y⁻¹ ∈ Algebra.adjoin R {y}) : IsIntegral R y⁻¹ := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h
  obtain ⟨p, hp⟩ := h
  letI : Invertible y := invertibleOfNonzero hy
  set n := p.natDegree
  have hrefl : (reflect n p).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_le_natDegree) ?_
    have : (reflect n p).natDegree ≤ n := natDegree_reflect_le.trans (by simp [n])
    exact_mod_cast Nat.lt_succ_of_le this
  refine ⟨X ^ (n + 1) - reflect n p, monic_X_pow_sub hrefl, ?_⟩
  have key := eval₂_reflect_mul_pow (algebraMap R K) y n p le_rfl
  rw [invOf_eq_inv] at key
  have hp' : eval₂ (algebraMap R K) y p = y⁻¹ := hp
  rw [hp'] at key
  have hval : eval₂ (algebraMap R K) y⁻¹ (reflect n p) = y⁻¹ ^ (n + 1) := by
    have hyn : y ^ n ≠ 0 := pow_ne_zero _ hy
    rw [← mul_inv_cancel_right₀ hyn (eval₂ (algebraMap R K) y⁻¹ (reflect n p)), key, pow_succ,
      inv_pow, mul_comm]
  rw [eval₂_sub, eval₂_X_pow, hval, sub_self]

private theorem maximalIdeal_map_sup_span_ne_univ_of_inv_not_mem_adjoin {R K : Type} [CommRing R]
    [IsLocalRing R] [Field K] [Algebra R K] (y : K) (hnot : y⁻¹ ∉ Algebra.adjoin R {y}) :
    (IsLocalRing.maximalIdeal R).map (algebraMap R (Algebra.adjoin R {y})) ⊔
      Ideal.span {(⟨y, Algebra.self_mem_adjoin_singleton R y⟩ : Algebra.adjoin R {y})} ≠ ⊤ := by
  set S := Algebra.adjoin R {y}
  set ys : S := ⟨y, Algebra.self_mem_adjoin_singleton R y⟩
  intro hJ
  set π := Ideal.Quotient.mk (Ideal.span {ys})
  have hsurj : Function.Surjective (π.comp (algebraMap R S)) := by
    intro s
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective s
    have hs2 : (s : K) ∈ (Polynomial.aeval (R := R) y).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact s.2
    obtain ⟨f, hf⟩ := hs2
    have hfs : Polynomial.aeval ys f = s :=
      Subtype.ext (by rw [← hf, Polynomial.aeval_subalgebra_coe]; rfl)
    refine ⟨f.coeff 0, ?_⟩
    rw [← hs, ← hfs, RingHom.comp_apply]
    conv_rhs => rw [← Polynomial.X_mul_divX_add f]
    rw [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_add (f := _), map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ys), zero_mul, zero_add]
  have htop : (IsLocalRing.maximalIdeal R).map (π.comp (algebraMap R S)) = ⊤ := by
    have := congrArg (Ideal.map π) hJ
    rwa [Ideal.map_sup, Ideal.map_map, Ideal.map_quotient_self, sup_bot_eq, Ideal.map_top] at this
  obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1
    (htop ▸ Submodule.mem_top : (1 : S ⧸ Ideal.span {ys}) ∈ _)
  have hmem : ys ∣ algebraMap R S (1 - a) := by
    rw [← Ideal.mem_span_singleton, map_sub, map_one, ← Ideal.Quotient.eq]
    exact ha1.symm
  have hunitA : IsUnit (algebraMap R S (1 - a)) :=
    (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits a
      ((IsLocalRing.mem_maximalIdeal a).1 ha)).map _
  obtain ⟨u, hu⟩ := isUnit_of_dvd_unit hmem hunitA
  apply hnot
  have h1 : ((u⁻¹ : Sˣ) : S) * ys = 1 := by rw [← hu, Units.inv_mul]
  have h2 : (((u⁻¹ : Sˣ) : S) : K) = y⁻¹ := eq_inv_of_mul_eq_one_left (congrArg Subtype.val h1)
  exact h2 ▸ ((u⁻¹ : Sˣ) : S).2

theorem _root_.GlobalTheory.ValCrit.dvd_of_forall_cdvr : ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (p q : R), q ≠ 0 →
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V),
      _root_.GlobalTheory.LN.CDvr V → Function.Injective φ →
      (IsLocalRing.maximalIdeal V).comap φ = IsLocalRing.maximalIdeal R → φ q ∣ φ p) →
    q ∣ p := by
  intro R _ _ _ _ _ _ p q hq H
  by_cases hp : p = 0
  · exact hp ▸ dvd_zero q
  by_contra hdvd
  set K := FractionRing R
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hpK : algebraMap R K p ≠ 0 := (map_ne_zero_iff _ hinjK).2 hp
  have hqK : algebraMap R K q ≠ 0 := (map_ne_zero_iff _ hinjK).2 hq
  set y : K := algebraMap R K q / algebraMap R K p with hy_def
  have hy : y ≠ 0 := div_ne_zero hqK hpK
  set S := Algebra.adjoin R {y}
  have hnot : y⁻¹ ∉ S := by
    intro hmem
    have hint := _root_.GlobalTheory.ValCrit.isIntegral_of_mem_adjoin_inv y hy hmem
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine hdvd ⟨r, hinjK ?_⟩
    rw [map_mul, hr, hy_def, inv_div, mul_comm, div_mul_cancel₀ _ hqK]
  let ys : S := ⟨y, Algebra.self_mem_adjoin_singleton R y⟩
  have hinjS : Function.Injective (algebraMap R S) := by
    intro a b hab
    exact hinjK (congrArg Subtype.val hab)
  haveI : Algebra.FiniteType R S := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton y)
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  haveI : CharZero S := charZero_of_injective_algebraMap hinjS
  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) ⊔ Ideal.span {ys}
  have hJ : J ≠ ⊤ := maximalIdeal_map_sup_span_ne_univ_of_inv_not_mem_adjoin y hnot
  obtain ⟨P, hPmax, hJP⟩ := Ideal.exists_le_maximal J hJ
  have hyP : ys ∈ P := hJP (Ideal.mem_sup_right (Ideal.mem_span_singleton_self ys))
  have hcomapP : P.comap (algebraMap R S) = IsLocalRing.maximalIdeal R := by
    refine ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le ?_ ?_).symm
    · exact (hPmax.isPrime.comap (algebraMap R S)).ne_top
    · exact Ideal.map_le_iff_le_comap.1 (le_trans le_sup_left hJP)
  obtain ⟨V, _, _, _, φ, hV, hφ, hcomap⟩ :=
    _root_.GlobalTheory.PrimeUnif.exists_cdvr S P
  have hψ : Function.Injective (φ.comp (algebraMap R S)) := hφ.comp hinjS
  have hψc : (IsLocalRing.maximalIdeal V).comap (φ.comp (algebraMap R S)) =
      IsLocalRing.maximalIdeal R := by
    rw [← Ideal.comap_comap, hcomap, hcomapP]
  obtain ⟨v, hv⟩ := H V (φ.comp (algebraMap R S)) hV hψ hψc
  have hrel : ys * algebraMap R S p = algebraMap R S q := by
    apply Subtype.ext
    change y * algebraMap R K p = algebraMap R K q
    rw [hy_def, div_mul_cancel₀ _ hpK]
  have hψp : φ (algebraMap R S p) ≠ 0 := by
    intro h0
    exact hp (hψ (by simpa using h0))
  have hone : φ ys * v = 1 := by
    apply mul_left_cancel₀ hψp
    simp only [RingHom.comp_apply] at hv
    rw [← hrel, map_mul] at hv
    calc φ (algebraMap R S p) * (φ ys * v) = φ ys * φ (algebraMap R S p) * v := by ring
      _ = φ (algebraMap R S p) := hv.symm
      _ = φ (algebraMap R S p) * 1 := (mul_one _).symm
  have hunit : IsUnit (φ ys) := isUnit_iff_exists_inv.2 ⟨v, hone⟩
  have hys : ys ∉ P := by
    rw [← hcomap, Ideal.mem_comap]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h hunit
  exact hys hyP

end GlobalTheory.ValCrit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairRelated
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid.PairConj

section Generic

variable {S : Type*} [Ring S]

theorem unop_mul_inv (σ : S →+* Sᵐᵒᵖ) (y : Sˣ) : (σ (y : S)).unop * (σ ((y⁻¹ : Sˣ) : S)).unop = 1 := by
  rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]

theorem unop_inv_mul (σ : S →+* Sᵐᵒᵖ) (y : Sˣ) : (σ ((y⁻¹ : Sˣ) : S)).unop * (σ (y : S)).unop = 1 := by
  rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]

theorem triv_conj (σ : S →+* Sᵐᵒᵖ) (b : S) (x y : Sˣ) :
    ((x * y⁻¹ : Sˣ) : S) * ((y : S) * b * (σ (y : S)).unop) * (σ ((x * y⁻¹ : Sˣ) : S)).unop =
      (x : S) * b * (σ (x : S)).unop := by
  have h := unop_mul_inv σ y
  calc ((x * y⁻¹ : Sˣ) : S) * ((y : S) * b * (σ (y : S)).unop) * (σ ((x * y⁻¹ : Sˣ) : S)).unop
      = (x : S) * (((y⁻¹ : Sˣ) : S) * y) * b * ((σ (y : S)).unop * (σ ((y⁻¹ : Sˣ) : S)).unop) *
          (σ (x : S)).unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = _ := by rw [Units.inv_mul, h, mul_one, mul_one]

end Generic

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

theorem sh_mul (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_sh (a : G.C) : sh G (sh G a) = a := G.star_star a

def shU (y : G.Cˣ) : G.Cˣ :=
  ⟨sh G y, sh G ((y⁻¹ : G.Cˣ) : G.C), unop_mul_inv G.star y, unop_inv_mul G.star y⟩

theorem shU_val (y : G.Cˣ) : ((shU G y : G.Cˣ) : G.C) = sh G y := rfl

def conjAlg (y : G.Cˣ) : G.C →ₐ[G.F] G.C where
  toFun a := y * a * ((y⁻¹ : G.Cˣ) : G.C)
  map_one' := by simp
  map_mul' a b := by
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  map_zero' := by simp
  map_add' a b := by simp [mul_add, add_mul]
  commutes' r := by
    show (y : G.C) * algebraMap G.F G.C r * ((y⁻¹ : G.Cˣ) : G.C) = algebraMap G.F G.C r
    rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

theorem conjAlg_injective (y : G.Cˣ) : Function.Injective (conjAlg G y) := by
  intro a b h
  have h' : (y : G.C) * a * ((y⁻¹ : G.Cˣ) : G.C) = y * b * ((y⁻¹ : G.Cˣ) : G.C) := h
  have := congrArg (fun z => ((y⁻¹ : G.Cˣ) : G.C) * z * (y : G.C)) h'
  simpa [mul_assoc] using this

variable {G} in
theorem inC_sh (R : Type) [CommRing R] [Algebra ℚ R] (a : G.C) :
    inC G R (sh G a) = (starT G.star R (inC G R a)).unop :=
  (starT_tmul G.star R 1 a).symm


variable {G} in
theorem triv_conj_unit (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C) (y : G.Cˣ)
    (x : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ) (hx : Triv G R β x t) :
    Triv G R ((y : G.C) * β * sh G y) (x * (Units.map (inC G R).toMonoidHom y)⁻¹) t := by
  unfold Triv at hx ⊢
  have e : inC G R ((y : G.C) * β * sh G y) =
      ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C) * inC G R β *
        (starT G.star R ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C)).unop := by
    rw [map_mul, map_mul, inC_sh]
    rfl
  rw [e, triv_conj, hx]

variable {G}

theorem conj_val (β y : G.Cˣ) : ((y * β * shU G y : G.Cˣ) : G.C) = (y : G.C) * β * sh G y := by
  rw [Units.val_mul, Units.val_mul, shU_val]

def conjPair (P : Pair G) (y : G.Cˣ) : Pair G where
  β := y * P.β * shU G y
  γ := y * P.γ * y⁻¹
  c := P.c
  sym := by
    simp only [Units.val_mul, shU_val, sh_mul, sh_sh, P.sym, mul_assoc]
  sim := by
    have hs := P.sim
    have h1 := unop_mul_inv G.star y
    simp only [Units.val_mul, shU_val, sh_mul]
    calc _ = (y : G.C) * (P.γ * (((y⁻¹ : G.Cˣ) : G.C) * y) * P.β * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) * sh G P.γ) *
            sh G y := by simp only [mul_assoc]
      _ = y * ((P.γ : G.C) * P.β * sh G P.γ) * sh G y := by
            rw [Units.inv_mul, show sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 from h1, mul_one, mul_one]
      _ = _ := by
            rw [hs, ← mul_assoc, ← mul_assoc, ← Algebra.commutes, mul_assoc _ (y : G.C), mul_assoc, mul_assoc]
  reg := by
    have e : ((y * P.γ * y⁻¹ : G.Cˣ) : G.C) = conjAlg G y P.γ := by simp [conjAlg]
    rw [e, minpoly.algHom_eq (conjAlg G y) (conjAlg_injective G y)]
    exact P.reg
  trivAf := by
    obtain ⟨x, t, hx⟩ := P.trivAf
    have h := triv_conj_unit (AfP p) (P.β : G.C) y x t hx
    rw [← conj_val] at h
    exact ⟨_, t, h⟩
  trivR := by
    obtain ⟨z, hz⟩ := P.trivR
    have h := triv_conj_unit ℝ (P.β : G.C) y z 1 hz
    rw [← conj_val] at h
    exact ⟨_, h⟩

theorem conjPair_β (P : Pair G) (y : G.Cˣ) :
    (((conjPair P y).β : G.Cˣ) : G.C) = (y : G.C) * P.β * sh G y := conj_val P.β y

end GlobalTheory.LKMid.PairConj


open GlobalTheory.LKMid.PairConj in
theorem GlobalTheory.LKMid.Pair.exists_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (y : G.Cˣ),
    ∃ P' : Pair G, P.Rel P' ∧ P'.γ = y * P.γ * y⁻¹ ∧ P'.c = P.c ∧
      ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t),
        ∃ (x' : (AfP p ⊗[ℚ] G.C)ˣ) (hx' : Triv G (AfP p) P'.β x' t),
          P'.toAf x' t hx' P'.self = P.toAf x t hx P.self := by
  intro p _ G P y
  refine ⟨conjPair P y, ⟨y, 1, one_pos, ?_, rfl⟩, rfl, rfl, ?_⟩
  · rw [map_one, one_mul, conjPair_β]
  · intro x t hx
    have h := triv_conj_unit (AfP p) (P.β : G.C) y x t hx
    rw [← conjPair_β] at h
    refine ⟨_, h, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · show (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹) *
          Units.map (inC G (AfP p)).toMonoidHom (y * P.γ * y⁻¹) *
          (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹)⁻¹ =
        x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹
      simp only [map_mul, map_inv]
      group
    · rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianCongrOfPositiveIndexEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianCongrOfPositiveIndexEq
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.HermCongruence

def signVec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) : Fin n → ℂ :=
  fun i => if 0 < hA.eigenvalues i then 1 else -1

theorem eigenvalues_ne_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hd : A.det ≠ 0)
    (i : Fin n) : hA.eigenvalues i ≠ 0 := by
  intro h
  apply hd
  rw [hA.det_eq_prod_eigenvalues]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])

theorem exists_congr_signVec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hd : A.det ≠ 0) :
    ∃ V : GL (Fin n) ℂ, (V : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * V = diagonal (signVec hA) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : Uᴴ * U = 1 := by
    have := hA.eigenvectorUnitary.2.1
    simpa [hU, Matrix.star_eq_conjTranspose] using this
  have hspec : A = U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have := hA.spectral_theorem
    simpa [hU, Matrix.star_eq_conjTranspose, Function.comp_def] using this
  set c : Fin n → ℂ := fun i => ((Real.sqrt |hA.eigenvalues i|)⁻¹ : ℝ) with hc
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i
    have h1 : 0 < |hA.eigenvalues i| := abs_pos.2 (eigenvalues_ne_zero hA hd i)
    simp [hc, Real.sqrt_eq_zero', not_le.2 h1, eigenvalues_ne_zero hA hd i]
  set V := U * diagonal c with hV
  have hVdet : V.det ≠ 0 := by
    rw [hV, det_mul, det_diagonal]
    refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun i _ => hc0 i)
    intro h
    have := congrArg det hUU
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  refine ⟨GeneralLinearGroup.mkOfDetNeZero V hVdet, ?_⟩
  show Vᴴ * A * V = _
  have hcs : (diagonal c)ᴴ = diagonal c := by
    rw [diagonal_conjTranspose]
    congr 1; funext i; simp [hc]
  rw [hV, conjTranspose_mul, hcs]
  conv_lhs => rw [hspec]
  have : diagonal c * Uᴴ * (U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ) * (U * diagonal c) =
      diagonal c * (Uᴴ * U) * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * (Uᴴ * U) * diagonal c := by
    simp only [Matrix.mul_assoc]
  rw [this, hUU, Matrix.mul_one, Matrix.mul_one, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  have hne := eigenvalues_ne_zero hA hd i
  have hpos : 0 < |hA.eigenvalues i| := abs_pos.2 hne
  have hsq : Real.sqrt |hA.eigenvalues i| * Real.sqrt |hA.eigenvalues i| = |hA.eigenvalues i| :=
    Real.mul_self_sqrt hpos.le
  have hs0 : Real.sqrt |hA.eigenvalues i| ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have key : (Real.sqrt |hA.eigenvalues i|)⁻¹ * hA.eigenvalues i * (Real.sqrt |hA.eigenvalues i|)⁻¹ =
      if 0 < hA.eigenvalues i then 1 else -1 := by
    rw [mul_comm, ← mul_assoc, ← mul_inv, hsq]
    split_ifs with h
    · rw [abs_of_pos h]; field_simp
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hne)]; field_simp
  simp only [signVec, hc]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, key]
  split_ifs <;> simp

end GlobalTheory.HermCongruence

namespace GlobalTheory.HermCongruence

theorem exists_equiv_pos {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : sigPosH hA = sigPosH hB) :
    ∃ e : Fin n ≃ Fin n, ∀ i, (0 < hA.eigenvalues (e i) ↔ 0 < hB.eigenvalues i) := by
  have h1 : Fintype.card {i // 0 < hB.eigenvalues i} = Fintype.card {i // 0 < hA.eigenvalues i} := h.symm
  have h2 : Fintype.card {i // ¬ 0 < hB.eigenvalues i} = Fintype.card {i // ¬ 0 < hA.eigenvalues i} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  refine ⟨Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2), fun i => ?_⟩
  by_cases hi : 0 < hB.eigenvalues i
  · have hx : Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2) i =
        ((Fintype.equivOfCardEq h1) ⟨i, hi⟩ : Fin n) := by
      simp [Equiv.subtypeCongr, hi]
    rw [hx]
    exact iff_of_true ((Fintype.equivOfCardEq h1) ⟨i, hi⟩).2 hi
  · have hx : Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2) i =
        ((Fintype.equivOfCardEq h2) ⟨i, hi⟩ : Fin n) := by
      simp [Equiv.subtypeCongr, hi]
    rw [hx]
    exact iff_of_false ((Fintype.equivOfCardEq h2) ⟨i, hi⟩).2 hi

theorem perm_congr {n : ℕ} (d : Fin n → ℂ) (e : Fin n ≃ Fin n) :
    ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e)ᴴ * diagonal d * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e =
      diagonal (d ∘ e) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  split_ifs with h <;> simp [h]

theorem congr_of_sigPosH_eq : ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian),
    A.det ≠ 0 → B.det ≠ 0 → sigPosH hA = sigPosH hB →
      ∃ Z : GL (Fin n) ℂ, B = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (Z : Matrix (Fin n) (Fin n) ℂ) := by
  intro n A B hA hB hdA hdB hs
  obtain ⟨VA, hVA⟩ := exists_congr_signVec hA hdA
  obtain ⟨VB, hVB⟩ := exists_congr_signVec hB hdB
  obtain ⟨e, he⟩ := exists_equiv_pos hA hB hs
  set P : Matrix (Fin n) (Fin n) ℂ := (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e with hP
  have hPP : P * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e.symm = 1 := by
    ext i j; simp [hP, Matrix.mul_apply, Matrix.one_apply]
  have hPdet : P.det ≠ 0 := by
    intro h
    have := congrArg det hPP
    rw [det_mul, h, zero_mul, det_one] at this
    exact zero_ne_one this
  have hsig : signVec hA ∘ e = signVec hB := by
    funext i
    simp only [Function.comp_apply, signVec]
    by_cases hi : 0 < hB.eigenvalues i
    · rw [if_pos hi, if_pos ((he i).2 hi)]
    · rw [if_neg hi, if_neg (fun h => hi ((he i).1 h))]
  refine ⟨VA * GeneralLinearGroup.mkOfDetNeZero P hPdet * VB⁻¹, ?_⟩
  set W : Matrix (Fin n) (Fin n) ℂ := ((VB⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hW
  have hVW : (VB : Matrix (Fin n) (Fin n) ℂ) * W = 1 := by
    rw [hW, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hWV : Wᴴ * (VB : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
    rw [← conjTranspose_mul, hVW, conjTranspose_one]
  have hP' : ((GeneralLinearGroup.mkOfDetNeZero P hPdet : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = P := rfl
  rw [Units.val_mul, Units.val_mul, hP', ← hW, conjTranspose_mul, conjTranspose_mul]
  have : Wᴴ * (Pᴴ * (VA : Matrix (Fin n) (Fin n) ℂ)ᴴ) * A * (VA * P * W) =
      Wᴴ * (Pᴴ * ((VA : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * VA) * P) * W := by
    simp only [Matrix.mul_assoc]
  rw [this, hVA, hP, perm_congr, hsig, ← hVB]
  have : Wᴴ * ((VB : Matrix (Fin n) (Fin n) ℂ)ᴴ * B * VB) * W =
      (Wᴴ * (VB : Matrix (Fin n) (Fin n) ℂ)ᴴ) * B * ((VB : Matrix (Fin n) (Fin n) ℂ) * W) := by
    simp only [Matrix.mul_assoc]
  rw [this, hWV, hVW, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.HermCongruence
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianCongrOfPositiveIndexEqStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_congr_of_positiveIndex_eq : ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian), A.det ≠ 0 → B.det ≠ 0 → sigPosH hA = sigPosH hB → ∃ Z : GL (Fin n) ℂ, B = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (Z : Matrix (Fin n) (Fin n) ℂ) := by
  first | exact @GlobalTheory.HermCongruence.congr_of_sigPosH_eq | exact GlobalTheory.HermCongruence.congr_of_sigPosH_eq | (intros; apply GlobalTheory.HermCongruence.congr_of_sigPosH_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHeckeTestFunctionSupportCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHeckeTestFunctionSupportCompact
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem isTest_support_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  intro p _ G L f hf
  obtain ⟨-, -, -, S, hS⟩ := hf
  have hK : IsCompact ((L.K.toSubgroup : Subgroup G.GAf) : Set G.GAf) := L.compact
  refine ⟨⋃ s ∈ S, (fun ab : G.GAf × G.GAf => ab.1 * s * ab.2) ''
      ((L.K.toSubgroup : Set G.GAf) ×ˢ (L.K.toSubgroup : Set G.GAf)), ?_, ?_⟩
  · refine S.isCompact_biUnion fun s _ => (hK.prod hK).image ?_
    fun_prop
  · intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
    exact Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHeckeTestFunctionSupportCompactStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedHeckeTestFunction_support_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  first | (exact @GlobalTheory.isTest_support_compact) | (exact GlobalTheory.isTest_support_compact) | (intros; apply GlobalTheory.isTest_support_compact  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjFrameMemUH
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicScalar

theorem conjFrame_mem_UH : ∀ (p q n : ℕ), p + q = n → ∀ (Gm : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), (Aᴴ * Formalism.UG.Jpq p q * A : Matrix (Fin n) (Fin n) ℂ) = Gm → IsUnit Gm.det → ∀ b : UpqT p q, conjFrame Gm A (UpqT.mat b) ∈ Formalism.QuantumDeterminants.UH Gm := by
  intro p q n hn Gm A hA hG b
  have hJ : (Formalism.UG.Jpq p q)ᴴ = Formalism.UG.Jpq p q := by simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]
  have h1 : Gm⁻¹ * Gm = 1 := Matrix.nonsing_inv_mul _ hG
  have hb : (UpqT.mat b)ᴴ * Formalism.UG.Jpq p q * UpqT.mat b = Formalism.UG.Jpq p q := b.2
  have hl : (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * A = 1 := by rw [Matrix.mul_assoc, hA, h1]
  have e : Fin n ≃ Fin p ⊕ Fin q := (finCongr hn.symm).trans finSumFinEquiv.symm
  have hr : A * (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hl
  have hc : A * conjFrame Gm A (UpqT.mat b) = UpqT.mat b * A := by
    have : A * conjFrame Gm A (UpqT.mat b) = A * (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * (UpqT.mat b * A) := by
      simp only [conjFrame, Matrix.mul_assoc]
    rw [this, hr, Matrix.one_mul]
  change (conjFrame Gm A (UpqT.mat b))ᴴ * Gm * conjFrame Gm A (UpqT.mat b) = Gm
  generalize conjFrame Gm A (UpqT.mat b) = C at hc
  calc Cᴴ * Gm * C = (A * C)ᴴ * Formalism.UG.Jpq p q * (A * C) := by
        rw [← hA]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Aᴴ * ((UpqT.mat b)ᴴ * Formalism.UG.Jpq p q * UpqT.mat b) * A := by
        rw [hc]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Gm := by rw [hb, hA]

end GlobalTheory.AdelicScalar
end
