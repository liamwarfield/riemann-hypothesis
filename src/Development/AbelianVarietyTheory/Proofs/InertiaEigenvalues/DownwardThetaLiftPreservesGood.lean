module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmRealProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinPullbackIsGoodTwistOfAnticyclotomicTame
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftPreservesGood
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanPOfGiven
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lowTNZ_holds {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) :
    Formalism.IndefR.Eqv.KerDiag.LowTNZ R := by
  intro i τ
  obtain ⟨w, hw, h0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.LowTypeRestriction.lowT_ne_bot (R.MW i (sg0 D A)) τ)
  exact ⟨⟨w, hw⟩, fun h => h0 (Subtype.ext h)⟩

theorem spanP_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    GlobalTheory.LiftRows.Given R F → Formalism.IndefR.Eqv.Act.SpanP R :=
  fun R _ _ => Formalism.IndefR.Eqv.KerDiag.spanP_of_lowTNZ R (lowTNZ_holds R)

end GlobalTheory.LiftRows

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftPreservesGood
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.GoodLift

theorem sum_translates {H X W ι : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] [Mul X] [Fintype ι]
    (E : H →ₗ[ℂ] (X → W)) (y : H) (yg : ι → H) (a c : ι → ℂ) (κ : ι → X)
    (hext : ∀ g h, E (yg g) h = (c g)⁻¹ • E y (h * κ g))
    (hy : ∀ (l : W →ₗ[ℂ] ℂ) h, ∑ g, a g * ((c g)⁻¹ * l (E y (h * κ g))) = l (E y h)) :
    E (∑ g, a g • yg g) = E y := by
  funext h
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, sub_eq_zero, ← hy l h, map_sum, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, Pi.smul_apply, map_smul, hext g h, map_smul, smul_eq_mul, smul_eq_mul]

theorem gaL_apply_choose {D : D7} {G : Type} [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (hk : ∀ g, ∃ κ, IsLevelLift V β L (eG g) κ)
    (F : GA D V → ℂ) (h : GA D V) :
    gaL V β L eG c F h = ∑ g, c g * ((levChi V β (flagL L) (hk g).choose)⁻¹ * F (h * (hk g).choose)) := by
  unfold gaL
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  show c g * actG0 V β L (eG g) F h = _
  unfold actG0
  rw [dite_eq_left (hk g)]

end GlobalTheory.GoodLift

namespace GlobalTheory.GoodLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

set_option maxHeartbeats 4000000 in
theorem liftsW_of_core (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) : LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
  obtain ⟨c, hc⟩ := hR.lev.βW i
  exact GlobalTheory.T.finite_group_lifts_to_parahoric_level _ _ _ _ _ hc rfl (GlobalTheory.T.typePlaces_not_pairwise_conjugate R.C.P R.Pg hR.lev.Pg)

set_option maxHeartbeats 4000000 in
theorem liftsV_of_core (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (g : G) :
    ∃ κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ := by
  obtain ⟨q, hq⟩ := (R.B.L i t).act_tie.red_surj g
  have h1 := hR.grp.red_L i t q
  obtain ⟨⟨_, h, rfl⟩, hq2⟩ := q
  obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (Vc D i)).1 h
  have e : finHom (Vc D i) (a * k) = finHom (Vc D i) k := by
    rw [map_mul, show finHom (Vc D i) a = 1 from ha, one_mul]
  refine ⟨k, hk, ?_, ?_⟩
  · rw [finE_eq, ← e]; exact hq2.1
  · rw [finE_eq, ← e, ← hq]; exact h1.symm

set_option maxHeartbeats 4000000 in
theorem translate_of_core (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) (κ : GA D (Vc D i))
    (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ) (y : (R.HV i t).H) :
    ∃ y' : (R.HV i t).H, (∀ h, (R.HV i t).e y' h = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ •
        (R.HV i t).e y (h * (finHom (Vc D i)).rangeRestrict κ)) ∧
      ∀ h, R.extV i t y' h = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ) := by
  obtain ⟨y', hy', -⟩ := GlobalTheory.RowClassSum.exists_translate (Vc D i) (R.βV i) (R.datVt i t) (R.cV i) (hR.models.cV i)
    (R.HV i t) _ (R.B.L i t).pres.reps (hR.models.HV i t) g0 κ hκ y
  have hc0 : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ ≠ 0 := levChi_ne_zero _ _
  refine ⟨y', hy', fun h => ?_⟩
  have e := GlobalTheory.ThetaProjEquiv.extV_shift R hR.models.cV i t κ hκ.1 _ hc0 y y' hy' h
  rw [LinearMap.map_smul, Pi.smul_apply] at e
  rw [← e, smul_smul, inv_mul_cancel₀ hc0, one_smul]

set_option maxHeartbeats 4000000 in
theorem thF_translate_low (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (g : G) (κ : GA D (Vc D i))
    (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ) (y y' : (R.HV i t).H)
    (hy : ∀ h, (R.HV i t).e y' h = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ •
        (R.HV i t).e y (h * (finHom (Vc D i)).rangeRestrict κ))
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    R.thF i t y' (fun ρ => v ρ) = actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (R.thF i t y (fun ρ => v ρ)) := by
  obtain ⟨κ', hκ'⟩ := liftsW_of_core R F hR i (R.eG g)
  funext x
  exact (GlobalTheory.ThetaProjEquiv.thF_shift_core R F hR i t (R.eG g) κ κ' hκ hκ'.1 y y' _ (levChi_ne_zero _ _)
    (GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hR.lev hR.models.inf hR.thP.ωP hR.thP.vP i t (R.eG g) κ κ' hκ hκ') hy v x).trans
    (GlobalTheory.ThetaProjEquiv.finiteGroup_acts_by_lift_translation_principalType R i (R.eG g) κ' hκ' _ (GlobalTheory.ThetaProjEquiv.thF_type R hR.thP.thF_mem i t y _) x).symm

set_option maxHeartbeats 4000000 in
theorem thF_low_eq (hP : R.IsThP) (i : Fin D.R.m) (t : T) (y z : (R.HV i t).H) (hz : R.extV i t z = R.extV i t y)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) : R.thF i t z (fun ρ => v ρ) = R.thF i t y (fun ρ => v ρ) := by
  obtain ⟨thP, hthP, hthF⟩ := hP.thF i t
  funext w
  refine ((congrFun (hthF _ v) w).trans (hthP.eq _ (PiTensorProduct.tprod ℂ v) w)).trans ?_
  refine Eq.trans ?_ ((congrFun (hthF y v) w).trans (hthP.eq _ (PiTensorProduct.tprod ℂ v) w)).symm
  have e1 : (((R.extV i t).rangeRestrict z : LinearMap.range (R.extV i t)) : GA D (Vc D i) → (R.cV i).W) =
      R.extV i t y := hz
  have e2 : (((R.extV i t).rangeRestrict y : LinearMap.range (R.extV i t)) : GA D (Vc D i) → (R.cV i).W) =
      R.extV i t y := rfl
  unfold Formalism.IndefR.Lift.thetaPInt
  rw [e1, e2]

set_option maxHeartbeats 4000000 in
theorem eWf_apply_sum (i : Fin D.R.m) (f : GA D (Wc D i) → ℂ) :
    R.eWf i (sg0 D A) f = ∑ g, RealDat.eC (A := A) (sg0 D A) g • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) f := by
  unfold RealDat.eWf gaL
  rw [LinearMap.sum_apply]
  rfl

end GlobalTheory.GoodLift

namespace GlobalTheory.GoodLift

set_option maxHeartbeats 8000000 in
theorem goodMem_of_given : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GoodMem R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t y hy
  have hR := hG.core
  have hLV := liftsV_of_core R F hR i t
  choose yg hyg hext using fun g : G => translate_of_core R F hR i t (R.eG g) _ (hLV g).choose_spec y
  have hz : R.extV i t (∑ g, RealDat.eC (A := A) (sg0 D A) g • yg g) = R.extV i t y :=
    sum_translates (R.extV i t) y yg _ _ (fun g => (hLV g).choose) hext
      (fun l h => (gaL_apply_choose (Vc D i) (R.βV i) (R.datVt i t) R.eG _ hLV _ h).symm.trans (congrFun (hy l) h))
  have hmem : (R.HW i (sg0 D A)).e (R.thG i t y) ∈ R.Wall i (sg0 D A) := by
    rw [← (hR.models.HW i (sg0 D A)).2.1]; exact ⟨_, rfl⟩
  refine sub_eq_zero.1 (GlobalTheory.LiftRows.spanP_of_given R F hG i _ (Submodule.sub_mem _ hmem (hR.thP.thF_mem i t y))
    fun v => ?_)
  refine sub_eq_zero.2 ?_
  rw [hR.thP.thG i t y]
  show R.eWf i (sg0 D A) (R.thF i t y (fun ρ => v ρ)) = _
  rw [eWf_apply_sum R i]
  calc ∑ g, RealDat.eC (A := A) (sg0 D A) g •
        actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (R.thF i t y (fun ρ => v ρ))
      = ∑ g, RealDat.eC (A := A) (sg0 D A) g • R.thF i t (yg g) (fun ρ => v ρ) :=
        Finset.sum_congr rfl fun g _ => by
          rw [thF_translate_low R F hR i t g _ (hLV g).choose_spec y (yg g) (hyg g) v]
    _ = R.thF i t (∑ g, RealDat.eC (A := A) (sg0 D A) g • yg g) (fun ρ => v ρ) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, MultilinearMap.sum_apply]
        simp only [map_smul, MultilinearMap.smul_apply]
    _ = R.thF i t y (fun ρ => v ρ) := thF_low_eq R hR.thP i t y _ hz v

end GlobalTheory.GoodLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftPreservesGoodStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downwardThetaLift_preserves_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GoodMem R i t := by
  first | exact @GlobalTheory.GoodLift.goodMem_of_given | exact GlobalTheory.GoodLift.goodMem_of_given | (intros; apply GlobalTheory.GoodLift.goodMem_of_given <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVecExistsUnique
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatVecExist

open GlobalTheory.PlaceModel

variable {D : D7}

theorem idemSum_split {e : AE D} {P Q : Finset (Pl D.host.E)} (he : IsIdemSum e (P ∪ Q)) (hd : Disjoint P Q) :
    ∃ eP eQ : AE D, IsIdemSum eP P ∧ IsIdemSum eQ Q ∧ eP * eQ = 0 ∧ eP * cA D eQ = 0 ∧ eQ * cA D eP = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, hc⟩ := he
  have h1 : ∀ i ∈ P ∪ Q, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hx := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es (P ∪ Q) h1 hc
  have hcr : ∀ A B : Finset (Pl D.host.E), A ⊆ P ∪ Q → B ⊆ P ∪ Q →
      (∑ i ∈ A, es i) * cA D (∑ j ∈ B, es j) = 0 := fun A B hA hB => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => hx i (hA hi) j (hB hj)
  have hP : P ⊆ P ∪ Q := Finset.subset_union_left
  have hQ : Q ⊆ P ∪ Q := Finset.subset_union_right
  refine ⟨∑ i ∈ P, es i, ∑ i ∈ Q, es i, ⟨⟨es, fun i hi => hes i (hP hi), rfl⟩, hcr P P hP hP⟩,
    ⟨⟨es, fun i hi => hes i (hQ hi), rfl⟩, hcr Q Q hQ hQ⟩, ?_, hcr P Q hP hQ, hcr Q P hQ hP⟩
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  exact GlobalTheory.PlaceDatum.idemAt_mul (hes i (hP hi)) (hes j (hQ hj)) (hx i (hP hi) j (hQ hj)) (hx j (hQ hj) i (hP hi))
    fun h => Finset.disjoint_left.1 hd hi (h ▸ hj)

theorem exists_model_of_fix {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {e : AE D} (he : GlobalTheory.PlaceModelSum.IsOrthSum e)
    (hec : e * cA D e = 0) {g : WO S T → ℂ}
    (hf : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, heisO ψ S T u g = g)
    (hf' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), heisO ψ S T u g = g) :
    ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 g Tm := by
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  refine exists_placeModel ψ hec _ (fun u hu y hy => (hdual u (he.infPart_half hu.2)).1 hu.1 y hy.1)
    (he.mem_of_dual hdual) (fun y hy h => ?_) (fun k hk => ?_) one_ne_zero g hf hf'
  · refine he.conj.mem_of_dual hdual y hy fun u hu => ?_
    rw [GlobalTheory.DualPairCheck.cA_cA] at hu
    rw [symplO_skew, AddChar.map_neg_eq_inv, h u hu, inv_one]
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, GlobalTheory.PlaceModelSum.idem_smul_half he.idem hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]

theorem omegaFlat_congr {a b : ℕ} (Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    {y y' : ∀ PP : Pl D.host.E, Matrix (Fin a) (Fin b) (kP PP)} (h : ∀ PP ∈ Q, y PP = y' PP) :
    GlobalTheory.ConjTwist.omegaFlat Q r ξ y = GlobalTheory.ConjTwist.omegaFlat Q r ξ y' := by
  have hiff : (∀ PP ∈ Q, IsUnit (topL r (y PP)).det) ↔ ∀ PP ∈ Q, IsUnit (topL r (y' PP)).det :=
    forall_congr' fun PP => forall_congr' fun hPP => by rw [h PP hPP]
  unfold GlobalTheory.ConjTwist.omegaFlat
  by_cases h1 : ∀ PP ∈ Q, IsUnit (topL r (y PP)).det
  · rw [dite_eq_left h1, dite_eq_left (hiff.1 h1)]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have e : (h1 PP.1 PP.2).unit = (hiff.1 h1 PP.1 PP.2).unit :=
      Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, h PP.1 PP.2])
    rw [e]
  · rw [dite_eq_right h1, dite_eq_right fun h2 => h1 (hiff.2 h2)]

theorem off_of_half {e c : AE D} (hc : e * c = 0) (hc' : cA D e * c = 0) {S T : HSp D} {u : WO S T} (hu : IsHalf c u) :
    ∀ a b, e * u a b = 0 ∧ cA D e * u a b = 0 := fun a b => by
  rw [← hu a b, ← mul_assoc, ← mul_assoc, hc, hc', zero_mul]
  exact ⟨rfl, rfl⟩

theorem flatVec_existsUnique : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), (∃ f, IsFlatVec R i t f) ∧ ∀ f f', IsFlatVec R i t f → IsFlatVec R i t f' → f = f' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR _ i t
  refine ⟨?_, ?_⟩
  · obtain ⟨hvac, e, he, -⟩ := hR.thP.vP i t
    have hψ := hvac.1
    have sV : IsSelfDualC (Vc D i) (R.ΛV i) :=
      GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βV i))
    have sW : IsSelfDualC (Wc D i) (R.ΛW i) :=
      GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βW i))
    have fullV := GlobalTheory.PlaceVec.selfDual_isFullLattice (Vc D i) (R.ΛV i) sV
    have fullW := GlobalTheory.PlaceVec.selfDual_isFullLattice (Wc D i) (R.ΛW i) sW
    obtain ⟨eg, eQ, hg, hq, h1, h2, h3⟩ := idemSum_split he (Formalism.IndefR.Fin.disjoint_Pg_Q R.toLevCh hR.lev t)
    have hinfg := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)
    obtain ⟨fg, hfg⟩ := GlobalTheory.PlaceVec.exists_isThetaAt hψ sV sW (a := cA D eg)
      (by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self hg]) hinfg
      (GlobalTheory.PlaceModelSum.placeModelExistsSum D R.ψ hψ _ _ _ _ sV sW _ eg hg _ hvac.2.theta hvac.2.lat).2
      (GlobalTheory.PlaceVec.isSBHalf_of_red fullV fullW hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
        (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _) R.Pg
        (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h)
    have hoQ := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hq
    have fix : ∀ u, (∀ a b, cA D eg * u a b = 0 ∧ eg * u a b = 0) →
        heisO R.ψ (Vc D i) (Wc D i) u (R.vacP i) = R.vacP i → heisO R.ψ (Vc D i) (Wc D i) u fg = fg :=
      fun u hu h0 => GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ (cA D eg) _ 1 _ _ fg hfg u
        (fun a b => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hu a b) h0
    have hPM := exists_model_of_fix hψ sV sW hoQ hq.2
      (fun u hu => fix u (fun a b => (off_of_half h1 (by rw [mul_comm, h3])
          ((isHalf_iff _ _).2 hu.2) a b).symm)
        (hoQ.heisO_eq (by rw [mul_comm, hq.2]) hvac.2.lat u hu))
      (fun u hu => fix u (fun a b => (off_of_half h2
          (by rw [← RingHom.map_mul, h1, map_zero]) ((isHalf_iff _ _).2 hu.2) a b).symm)
        (hoQ.conj.heisO_eq (by rw [GlobalTheory.DualPairCheck.cA_cA, hq.2]) hvac.2.lat u hu))
    have hinfQ := GlobalTheory.PlaceDatum.infPart_idemSum hq
    obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO fullV fullW (R.βV i) (R.βW i)
    obtain ⟨f, hf⟩ := GlobalTheory.PlaceDatum.exists_isThetaAt hψ sV sW (GlobalTheory.PlaceDatum.idemSum_mul_self hq) hinfQ hPM
      (GlobalTheory.PlaceDatum.isSBHalf_of_red eQ _ (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (GlobalTheory.PlaceDatum.frMapO_add _ _)
        (GlobalTheory.PlaceDatum.exists_den_frMapO sV.1.fg sW.1.fg _ _)
        ⟨K, hK, fun x hx => hC x (GlobalTheory.PlaceDatum.infPart_of_half hinfQ hx)⟩ (R.Q t)
        (fun y => GlobalTheory.ConjTwist.omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) y) fun y y' h => omegaFlat_congr _ _ _ h)
    exact ⟨f, eg, eQ, fg, hg, hq, hfg, hf⟩
  · rintro f f' ⟨eg, eQ, fg, hg, hq, hfg, hf⟩ ⟨eg', eQ', fg', hg', hq', hfg', hf'⟩
    obtain rfl := GlobalTheory.BaseKernelUniq.idemSum_unique (Vc D i) hg hg'
    obtain rfl := GlobalTheory.BaseKernelUniq.idemSum_unique (Vc D i) hq hq'
    obtain rfl : fg = fg' := by
      obtain ⟨⟨Tm, hTm⟩, hall⟩ := hfg
      rw [hall Tm hTm, hfg'.2 Tm hTm]
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
    rw [hall Tm hTm, hf'.2 Tm hTm]

end GlobalTheory.FlatVecExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGood
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGood
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistGood

theorem ramExactly_conj {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) {M : Type} [CommGroup M]
    (ψ : G D.host.E N.Om →* M) (Q : Set (Pl D.host.E)) (hA : AntiHom X.cc ψ) (hR : RamExactly ψ Q) :
    ∀ P ∈ Q, ∀ P' : Pl D.host.E, IsConjPl D.host P P' → P' ∈ Q := by
  intro P hP P' hPP
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x :=
    bridge_star_holds D.R D.host
  obtain ⟨⟨j, hj⟩, -⟩ := X.cc_cm
  have hκ : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    rw [← hst, ← hst, IsCMField.complexConj_apply_apply]
  have hc : ∀ x, X.cc (algebraMap D.host.E N.Om x) = algebraMap D.host.E N.Om (D.host.conj x) := fun x => by
    apply j.injective
    rw [hj, ← hst]
    exact (IsCMField.complexEmbedding_complexConj D.host.E (j.comp (algebraMap D.host.E N.Om)) x).symm
  have hs : ∀ x, X.cc.symm (algebraMap D.host.E N.Om x) = algebraMap D.host.E N.Om (D.host.conj x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  have hpl : IsPlaceOver (N.plOm.1 P) P := N.plOm.2 P
  obtain ⟨σ, hσ, hne⟩ := (hR P _ hpl).2 hP
  obtain ⟨σ', h1, h2⟩ := GlobalTheory.AntiRam.exists_conj_mem_Ine X.cc (fun x => D.host.conj x) hc hκ _ σ hσ
  refine (hR P' _ (fun y => ?_)).1 ⟨σ', h2, ?_⟩
  · have hint : IsIntegral ℤ (D.host.conj (y : D.host.E)) := by
      rw [← hst]
      exact (RingOfIntegers.isIntegral_coe y).map ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)
    rw [GlobalTheory.AntiRam.valuation_comap_lt_one, hs, ← hPP ⟨_, hint⟩ y (hκ _).symm]
    exact hpl ⟨_, hint⟩
  · rw [hA σ σ' h1]
    exact inv_ne_one.2 hne

theorem tw_good : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ), Formalism.MainNotions.IntegralHeckeForms.TwOK i k Q ψ → (ρ.tw i b k Q ψ).Good ∧ (ρ.B i j b).admitted (ρ.tw i b k Q ψ).Q ∧ ∀ x, ∃ u : (X.Ok i k)ˣ, (((ρ.tw i b k Q ψ).chi x : Circle) : ℂ) = ρ.eOk i b k u := by
  intro D N X ρ hρ i j b k Q ψ hψ
  classical
  obtain ⟨hsplit, hdisj, hopen, hanti, hzk, hram, -⟩ := hψ
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) Q) := GlobalTheory.T.chosenPlaces_admissible_goodSetup D N X ρ hρ i j b Q hsplit hdisj
  let g : (X.Ok i k)ˣ →* Circle := unitPart.comp (Units.map (ρ.eOk i b k).toMonoidHom)
  have hkey : charOf ρ.rc (ρ.eOk i b k) ψ = ρ.rc.pull (g.comp ψ) := by
    rw [Recip.pull_comp _ hopen]
    rfl
  have hz : X.zk i k ^ (X.l i ^ k) = 1 := Units.ext (by simpa using (X.zk_prim i k).pow_eq_one)
  have hpow : ∀ σ, ψ σ ^ (X.l i ^ k) = 1 := by
    intro σ
    obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  refine ⟨?_, hadm, ?_⟩
  · show (⟨half (ρ.ch i) Q, charOf ρ.rc (ρ.eOk i b k) ψ, resOf (charOf ρ.rc (ρ.eOk i b k) ψ)⟩ : Twist D Circle).Good
    rw [hkey]
    refine GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame D N X ρ.rc hρ.rc Circle (g.comp ψ) (X.l i) (X.lPrime i).out
      (fun σ => ⟨k, by rw [MonoidHom.comp_apply, ← map_pow, hpow, map_one]⟩) ?_ ?_ _ ?_ ?_ ?_
    · exact Subgroup.isOpen_mono (H₁ := ψ.ker) (fun x hx => by
        rw [MonoidHom.mem_ker] at hx ⊢
        rw [MonoidHom.comp_apply, hx, map_one]) hopen
    · intro x x' hx
      show g (ψ x') = (g (ψ x))⁻¹
      rw [hanti x x' hx, map_inv]
    · obtain ⟨P, -, h2, h3⟩ := hadm.1.split
      exact h3.mono (Finset.subset_union_right.trans h2)
    · intro P hP hl
      exact Finset.disjoint_left.1 hdisj (mem_half.1 hP).1 (X.twistExcludedPlaces_contains_residueChar i (show P ∈ placesOver D.host.E (X.l i) from hl))
    · intro v hv hnc B hB σ hσ
      have hvQ : v ∉ Q := by
        intro hvQ
        by_cases hc : v ∈ ρ.ch i
        · exact hv (mem_half.2 ⟨hvQ, hc⟩)
        · obtain ⟨v', hv'⟩ := GlobalTheory.TwistDet.exists_isConjPl v
          have hv'Q : v' ∈ Q := ramExactly_conj X ψ _ hanti hram v hvQ v' hv'
          have hne := ne_of_split (hsplit v hvQ) hv'
          have hv'c : v' ∈ ρ.ch i := by
            by_contra h
            exact hc (((hρ.ch i).pair v v' hv' hne).2 h)
          exact hnc v' (mem_half.2 ⟨hv'Q, hv'c⟩) (GlobalTheory.TwistDet.isConjPl_symm hv')
      have h1 : ψ σ = 1 := by
        by_contra h
        exact hvQ ((hram v B hB).1 ⟨σ, hσ, h⟩)
      rw [MonoidHom.comp_apply, h1, map_one]
  · intro x
    obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
    exact ⟨ψ σ, charOf_eq ρ.rc (ρ.eOk i b k) hopen hσ (pow_ne_zero _ (X.lPrime i).out.ne_zero) (hpow σ)⟩

end GlobalTheory.TwistGood

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGoodStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistingCharacter_admissibleGaloisTwist_good : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ), Formalism.MainNotions.IntegralHeckeForms.TwOK i k Q ψ → (ρ.tw i b k Q ψ).Good ∧ (ρ.B i j b).admitted (ρ.tw i b k Q ψ).Q ∧ ∀ x, ∃ u : (X.Ok i k)ˣ, (((ρ.tw i b k Q ψ).chi x : Circle) : ℂ) = ρ.eOk i b k u := by
  first | exact @GlobalTheory.TwistGood.tw_good | exact GlobalTheory.TwistGood.tw_good | (intros; apply GlobalTheory.TwistGood.tw_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowParamOfCuspidal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem rowParam_of_cuspParam : ∀ (D : D7) (Rw : RowSide D), GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → D.ntypes.cuspidal σ) → (∀ k v, IsSplitPl D.host (D.naut.plGw k v)) → RowParam D Rw := by
  intro D Rw hP hC hS j hj1 hj2 σ hσ hg
  obtain ⟨π, h⟩ := hP j hj1 hj2 σ hσ hg
  have hembb : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ = GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ true := fun τ => by
    ext x
    have e : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ true x = starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ false x) :=
      D.host.conjE_apply (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ false) x
    rw [e]
    rfl
  have hpar : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ) = (GlobalTheory.Triple.rowPar (D.hc τ)).map (fun p => ((p : ℚ) : ℂ)) := by
    intro τ
    simp [GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma, GlobalTheory.Triple.rowPar, Multiset.map_add (f := _), Multiset.map_map, Function.comp_def]
  refine ⟨π, ⟨h.1, h.2.1, fun τ => ?_, fun w hw => h.unr w hw, fun k v => ?_, hC j hj1 hj2 σ hσ hg⟩, h.2.2.1⟩
  · obtain ⟨a, b⟩ := h.2.2.2.2.2 τ
    refine ⟨?_, ?_⟩
    · rw [← hpar]; exact a
    · rw [← hembb, b, hpar, Multiset.map_map]
      refine Multiset.map_congr rfl fun p _ => ?_
      simp
  · rw [Rw.lab_eq k σ v, h.2.2.1 _ (hS k v)]
end GlobalTheory.TwInputs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistSecondStepKeptWithLocalisations
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistSecondStepKeptWithLocalisations
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.FitTw

noncomputable section

namespace GlobalTheory.TwInputs.SideBLoc

set_option maxHeartbeats 8000000 in
theorem exists_sideB_withLoc : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ (L : LocAll (lay0 D)) (ψ : (withLoc L).nd.Loc → NC.HC D.host.E), (∀ a, NC.ReadC (withLoc L).nd.plOm.1 ((withLoc L).ntw.psiL a) (NC.iotaC (withLoc L) a) (ψ a) 0) → ∃ Rw' : RowSide (withLoc L), HEq Rw'.locR Rw.locR ∧ ∃ Bs' : SideB (withLoc L) (cfL L cf) Rw' low Pq ({ S with } : RatDat (withLoc L).ntw) hL eig θ, HEq Bs'.rowS Bs.rowS := by
  intro D cf Rw low Pq S hL eig θ Bs L ψ hψ
  refine ⟨⟨Rw.locR, Rw.satR, Rw.lab_eq⟩, HEq.rfl, ?_⟩
  exact ⟨{ Bs with
    twF := twFL L Bs.twF
    tw := twTiedL L Bs.tw
    chiD := chiDL L Bs.chiD ψ
    chi := chiL L Bs.chi ψ hψ
    deltaRead := deltaReadL L Bs.deltaRead
    exp := expL L Bs.exp }, HEq.rfl⟩

end GlobalTheory.TwInputs.SideBLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistSecondStepKeptWithLocalisationsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_second_step_kept_with_localisations : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ (L : LocAll (lay0 D)) (ψ : (withLoc L).nd.Loc → NC.HC D.host.E), (∀ a, NC.ReadC (withLoc L).nd.plOm.1 ((withLoc L).ntw.psiL a) (NC.iotaC (withLoc L) a) (ψ a) 0) → ∃ Rw' : RowSide (withLoc L), HEq Rw'.locR Rw.locR ∧ ∃ Bs' : SideB (withLoc L) (cfL L cf) Rw' low Pq ({ S with } : RatDat (withLoc L).ntw) hL eig θ, HEq Bs'.rowS Bs.rowS := by
  first | exact @GlobalTheory.TwInputs.SideBLoc.exists_sideB_withLoc | exact GlobalTheory.TwInputs.SideBLoc.exists_sideB_withLoc | (intros; apply GlobalTheory.TwInputs.SideBLoc.exists_sideB_withLoc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartEigensystemIsTripleEigensystem
section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MeetsReferenceOfMeetsAll
noncomputable section

namespace GlobalTheory.TwInputs.EigModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.Triple (heckeVal satake muBase)

variable {D : D7}

variable {cf : CharFrame D} {Rw : RowSide D} {Sb : Finset (PlE D.host)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}

theorem sig_all_of (hN : NoFormsOff D) (hM : MeetsAll D) (hC : CommAll D)
    (hall : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b ev, GlobalTheory.EigTie.IsEigSys D.nexp i j b ev →
      ∃ s : D.ntw.Sig i, D.ntw.jS i s = j ∧ D.ntw.side i s = b ∧ ∀ k P, HkIdx i k P → GlobalTheory.EigTie.sigEv s k P = ev k P) :
    D.nexp.sig_all := by
  intro i j b x ev hx he hk
  by_cases hj : j ∈ Finset.Icc 1 D.R.m
  · let W : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
      Eigsp D.nexp i j b ev ⊓ LinearMap.ker (eG D.nexp i j b - LinearMap.id)
    have mW : ∀ y, y ∈ W ↔ (∀ k P, HkIdx i k P → D.nexp.hkF i j b k P y = ev k P • y) ∧ eG D.nexp i j b y = y := by
      intro y
      simp only [W, Eigsp, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    have hxW : x ∈ W := (mW x).2 ⟨fun k P h => hk k P h.1 h.2.1 h.2.2.1 h.2.2.2, he⟩
    have hst : GStable D.nexp i j b W := by
      intro g y hy
      obtain ⟨a, c⟩ := (mW y).1 hy
      refine (mW _).2 ⟨fun k P h => by rw [hC i j hj b k P h, a k P h, map_smul], ?_⟩
      have e := congrArg (MonoidAlgebra.lift (FractionRing (D.ntw.O i))
        (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)))
        (D.nexp.eAlg_central i b (MonoidAlgebra.of _ _ g))
      rw [map_mul, map_mul, MonoidAlgebra.lift_of] at e
      have e2 := LinearMap.congr_fun e y
      change eG D.nexp i j b (D.nexp.actG i j b g y) = D.nexp.actG i j b g (eG D.nexp i j b y) at e2
      rw [e2, c]
    obtain ⟨y, ⟨hy1, hy2⟩, hy0⟩ := (Submodule.ne_bot_iff _).1
      (hM i j b W ((Submodule.ne_bot_iff _).2 ⟨x, hxW, hx⟩) hst fun y hy => ((mW y).1 hy).2)
    obtain ⟨a, c⟩ := (mW y).1 hy1
    obtain ⟨s, e1, e2, e3⟩ := hall i j hj b ev ⟨y, ⟨y, hy2, c⟩, hy0, a⟩
    exact ⟨s, e1, e2, fun k P p q r t => e3 k P ⟨p, q, r, t⟩⟩
  · exact absurd ((hN i j hj b).elim x 0) hx

section Laws

open GlobalTheory.SupLaw.Model

variable (D) (A : ∀ (i : D.ntw.Tw) (j : ℕ), ℕ → PlE D.host → Module.End (KK D i) (Pt D j → KK D i))
  (s : ∀ i : D.ntw.Tw, ℕ → KK D i)

end Laws

end GlobalTheory.TwInputs.EigModel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartEigensystemIsTripleEigensystem
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.EigAll

theorem exists_smul_mem_of_mem_span {O K V : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (N : Submodule O V)
    {v : V} (hv : v ∈ Submodule.span K (N : Set V)) : ∃ d : O, d ≠ 0 ∧ d • v ∈ N := by
  let S : Submodule K V :=
    { carrier := {v | ∃ d : O, d ≠ 0 ∧ d • v ∈ N}
      add_mem' := by
        rintro a c ⟨d, hd, ha⟩ ⟨e, he, hc⟩
        refine ⟨d * e, mul_ne_zero hd he, ?_⟩
        rw [smul_add]
        refine N.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact N.smul_mem _ ha
        · rw [mul_smul]; exact N.smul_mem _ hc
      zero_mem' := ⟨1, one_ne_zero, by rw [smul_zero]; exact N.zero_mem⟩
      smul_mem' := by
        rintro c a ⟨d, hd, ha⟩
        obtain ⟨n, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := O) c
        have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
        have hmK : algebraMap O K m ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
        refine ⟨m * d, mul_ne_zero hm0 hd, ?_⟩
        have e1 : m • ((algebraMap O K n / algebraMap O K m) • a) = n • a := by
          rw [← algebraMap_smul K m, smul_smul, mul_div_cancel₀ _ hmK, algebraMap_smul]
        show (m * d) • ((algebraMap O K n / algebraMap O K m) • a) ∈ N
        rw [mul_comm, mul_smul, e1, smul_comm]
        exact N.smul_mem _ ha }
  have hle : Submodule.span K (N : Set V) ≤ S :=
    Submodule.span_le.2 fun x hx => ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  exact hle hv

theorem eq_zero_of_joint {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : ι → V →ₗ[K] V) (p : ι → Prop) (ev : ι → K) (M : Finset (ι → K)) :
    ∀ y : V, (∀ μ ∈ M, ∃ t, p t ∧ μ t ≠ ev t) → (∀ t, p t → T t y = ev t • y) →
      y ∈ Submodule.span K {z | ∃ μ ∈ M, ∀ t, p t → T t z = μ t • z} → y = 0 := by
  classical
  induction M using Finset.induction_on with
  | empty =>
    intro y _ _ hs
    have : {z : V | ∃ μ ∈ (∅ : Finset (ι → K)), ∀ t, p t → T t z = μ t • z} = ∅ := by
      ext z; simp
    rw [this, Submodule.span_empty, Submodule.mem_bot] at hs
    exact hs
  | insert μ0 M _ ih =>
    intro y hne hy hs
    obtain ⟨t0, hp0, hμ0⟩ := hne μ0 (Finset.mem_insert_self _ _)
    let L : V →ₗ[K] V := T t0 - μ0 t0 • LinearMap.id
    have hL : Submodule.span K {z | ∃ μ ∈ insert μ0 M, ∀ t, p t → T t z = μ t • z} ≤
        (Submodule.span K {z | ∃ μ ∈ M, ∀ t, p t → T t z = μ t • z}).comap L := by
      rw [Submodule.span_le]
      rintro z ⟨μ, hμ, hz⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      rcases Finset.mem_insert.1 hμ with rfl | hμ
      · have : L z = 0 := by
          simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hz t0 hp0, sub_self]
        rw [this]; exact Submodule.zero_mem _
      · have : L z = (μ t0 - μ0 t0) • z := by
          simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hz t0 hp0, sub_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, hμ, hz⟩)
    have hLy : L y = (ev t0 - μ0 t0) • y := by
      simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hy t0 hp0, sub_smul]
    have h0 := ih ((ev t0 - μ0 t0) • y) (fun μ hμ => hne μ (Finset.mem_insert_of_mem hμ))
      (fun t ht => by rw [map_smul, hy t ht, smul_comm]) (hLy ▸ hL hs)
    rcases smul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hμ0
    · exact h

variable {D : D7} {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
  {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
  {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}

open Classical in
def trEig (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Set (D.nexp.Fm i j b) :=
  {z | ∃ μ ∈ (Finset.univ.filter fun s : D.ntw.Sig i => D.ntw.jS i s = j ∧ D.ntw.side i s = b).image
      (fun s (t : ℕ × PlE D.host) => GlobalTheory.EigTie.sigEv s t.1 t.2),
    ∀ t : ℕ × PlE D.host, HkIdx i t.1 t.2 → D.nexp.hkF i j b t.1 t.2 z = μ t • z}

theorem good_part_le_span_triple_eigenvectors (Bs : SideB D cf Rw low Pq S hL eig θ) (hF : FullAll D) (i : D.ntw.Tw) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) :
    V0 D.nexp i j b ≤ Submodule.span (FractionRing (D.ntw.O i)) (trEig D i j b) := by
  classical
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  set K := FractionRing (D.ntw.O i)
  let Φ : K ⊗[D.ntw.O i] D.ntw.B i j b →ₗ[K] D.nexp.Fm i j b := (D.nexp.embB i j b).liftBaseChange K
  have hΦ : ∀ k P, HkIdx i k P → ∀ z, Φ (((D.ntw.hk i j b k P).baseChange K) z) = D.nexp.hkF i j b k P (Φ z) := by
    intro k P hP z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [Φ, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, map_smul]
      rw [Bs.hk_emb i j b k P x h1 h2 hP.2.2.2 hP.2.2.1 hP.2.1]
    | add z w hz hw => simp only [map_add (f := _), hz, hw]

  have hrange : ∀ x : D.ntw.B i j b, D.nexp.embB i j b x ∈ Submodule.span K (trEig D i j b) := by
    intro x
    have hx : (1 : K) ⊗ₜ[D.ntw.O i] x ∈ (⊤ : Submodule K (K ⊗[D.ntw.O i] D.ntw.B i j b)) := trivial
    rw [← Bs.sigSpan i j b h1 h2] at hx
    have hx' := Submodule.mem_map_of_mem (f := Φ) hx
    rw [Submodule.map_span] at hx'
    have e : Φ ((1 : K) ⊗ₜ[D.ntw.O i] x) = D.nexp.embB i j b x := by
      show (D.nexp.embB i j b).liftBaseChange K ((1 : K) ⊗ₜ[D.ntw.O i] x) = _
      rw [LinearMap.liftBaseChange_tmul, one_smul]
    rw [e] at hx'
    refine Submodule.span_mono ?_ hx'
    rintro _ ⟨z, ⟨s, hs1, hs2, hz⟩, rfl⟩
    refine ⟨fun t => GlobalTheory.EigTie.sigEv s t.1 t.2, Finset.mem_image.2 ⟨s, by simp [hs1, hs2], rfl⟩, ?_⟩
    intro t ht
    rw [← hΦ t.1 t.2 ht, hz t.1 t.2 ht.1 ht.2.1 ht.2.2.1 ht.2.2.2, map_smul]
    rfl
  intro v hv
  obtain ⟨d, hd, hdv⟩ := exists_smul_mem_of_mem_span (K := K) (D.nexp.Bsup i j b) (by rw [hF i j hj b]; trivial)
  have hdV : d • v ∈ V0 D.nexp i j b := by
    rw [← algebraMap_smul K d v]; exact Submodule.smul_mem _ _ hv
  have hmem : d • v ∈ LinearMap.range (D.nexp.embB i j b) := by
    rw [Bs.tw.B_range i j b]; exact ⟨hdv, hdV⟩
  obtain ⟨x, hx⟩ := hmem
  have hdK : algebraMap (D.ntw.O i) K d ≠ 0 := by
    intro h; exact hd (IsFractionRing.injective (D.ntw.O i) K (h.trans (map_zero _).symm))
  have : v = (algebraMap (D.ntw.O i) K d)⁻¹ • (d • v) := by
    rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hdK, one_smul]
  rw [this, ← hx]
  exact Submodule.smul_mem _ _ (hrange x)

theorem sig_all_of_sideB : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ),
    NoFormsOff D → MeetsAll D → CommAll D → FullAll D → D.nexp.sig_all := by
  intro D cf Rw low Pq S hL eig θ Bs hN hM hC hF
  classical
  refine EigModel.sig_all_of hN hM hC ?_
  rintro i j hj b ev ⟨y, hyV, hy0, hyE⟩
  by_contra hno
  push_neg at hno
  apply hy0
  refine eq_zero_of_joint (fun t : ℕ × PlE D.host => D.nexp.hkF i j b t.1 t.2) (fun t => HkIdx i t.1 t.2)
    (fun t => ev t.1 t.2) _ y ?_ (fun t ht => hyE t.1 t.2 ht) (good_part_le_span_triple_eigenvectors Bs hF i j hj b hyV)
  intro μ hμ
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hμ
  obtain ⟨hs1, hs2⟩ := (Finset.mem_filter.1 hs).2
  obtain ⟨k, P, hk, hne⟩ := hno s hs1 hs2
  exact ⟨(k, P), hk, hne⟩

end GlobalTheory.TwInputs.EigAll

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartEigensystemIsTripleEigensystemStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_part_eigensystem_is_triple_eigensystem : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), NoFormsOff D → MeetsAll D → CommAll D → FullAll D → D.nexp.sig_all := by
  first | exact @GlobalTheory.TwInputs.EigAll.sig_all_of_sideB | exact GlobalTheory.TwInputs.EigAll.sig_all_of_sideB | (intros; apply GlobalTheory.TwInputs.EigAll.sig_all_of_sideB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisAveragedSeriesOfClassSums
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisAveragedSeriesOfClassSums
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem exists_basisOf_of_classSum :
    ∀ (D : D7) (E : IntegralHeckeForms.XD D), IntegralHeckeForms.admT4 D.nexp E → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∃ S, BasisOf D.nexp i j b (SgJ D.nexp E i j b) S :=
  fun D E h i hi j hj b =>
    GlobalTheory.TwistChoice.exists_basisOf D.nexp i j b _ (GlobalTheory.TwistChoice.th_fg D.nexp E h i hi j hj b)

end GlobalTheory.TwInputs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisAveragedSeriesOfClassSumsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_averaged_series_of_class_sums : ∀ (D : D7) (E : IntegralHeckeForms.XD D), IntegralHeckeForms.admT4 D.nexp E → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∃ S, BasisOf D.nexp i j b (SgJ D.nexp E i j b) S := by
  first | exact @GlobalTheory.TwInputs.exists_basisOf_of_classSum | exact GlobalTheory.TwInputs.exists_basisOf_of_classSum | (intros; apply GlobalTheory.TwInputs.exists_basisOf_of_classSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBTies
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.SideTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fi
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def fiOf (R : RealDat3 D A3 Ks) (i' i : Fin D.R.m) (h : i' = i) : FormsIso (R.FW i') (R.FW i) := by
  subst h
  exact ⟨RingEquiv.refl _, fun _ => rfl, LinearEquiv.refl _ _, MulEquiv.refl _, fun _ => LinearIsometryEquiv.refl _ _,
    fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem fiOf_heq (R : RealDat3 D A3 Ks) (i' i : Fin D.R.m) (h : i' = i) (x : Fin (R.nW i') → D.what₂.LL) :
    HEq ((fiOf R i' i h).e x) x := by
  subst h; rfl

theorem fiOf_eG (R : RealDat3 D A3 Ks) (i' i : Fin D.R.m) (h : i' = i) (g : G) : (fiOf R i' i h).eG g = g := by
  subst h; rfl

end Fi

end GlobalTheory.TwInputs.SideTies
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LevelSeries

def flipElt {D : D7} (e : AE D) (m : ℕ) : AE D :=
  e * (m : AE D) + cA D e * incA D ((m : D.host.E)⁻¹) + (1 - e - cA D e)

theorem flipIdx_ne_zero {D : D7} (V W : HSp D) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) {m : ℕ} (hm : m ≠ 0) :
    flipIdx V W T m ≠ 0 := by
  unfold flipIdx
  rw [Finset.prod_ne_zero_iff]
  intro PP _
  refine pow_ne_zero _ ?_
  rw [Ne, Ideal.absNorm_eq_zero_iff, HeightOneSpectrum.maxPowDividing]
  exact pow_ne_zero _ PP.ne_bot

end GlobalTheory.LevelSeries

end
end
