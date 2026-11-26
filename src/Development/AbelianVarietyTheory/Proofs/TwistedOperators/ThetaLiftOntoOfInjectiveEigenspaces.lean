module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecOfEqIntertwiner

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftInjectiveGoodPartJointEigenspace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointApplyOfEigen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
namespace GlobalTheory.SplitEigen

theorem adjoint_apply_of_eigen {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (A : Module.End ℂ H) (hA : Commute A (LinearMap.adjoint A)) (v : H) (μ : ℂ) (hv : A v = μ • v) :
    LinearMap.adjoint A v = starRingEnd ℂ μ • v := by
  set B : Module.End ℂ H := A - μ • 1 with hBdef
  have hBadj : LinearMap.adjoint B = LinearMap.adjoint A - starRingEnd ℂ μ • 1 := by
    rw [hBdef, map_sub, map_smulₛₗ]
    congr 2
    exact LinearMap.adjoint_id
  have hBv : B v = 0 := by
    rw [hBdef, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hv, sub_self]
  have hc : Commute B (LinearMap.adjoint B) := by
    rw [hBadj, hBdef]
    exact (hA.sub_right ((Commute.one_right A).smul_right _)).sub_left ((Commute.one_left _).smul_left _)
  have h0 : LinearMap.adjoint B v = 0 := by
    have e : inner ℂ (LinearMap.adjoint B v) (LinearMap.adjoint B v) = (0 : ℂ) := by
      rw [LinearMap.adjoint_inner_left]
      have : B (LinearMap.adjoint B v) = LinearMap.adjoint B (B v) := by
        rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply]
      rw [this, hBv, map_zero, inner_zero_right]
    exact inner_self_eq_zero.1 e
  rw [hBadj, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h0
  exact h0

theorem adjoin_scalar {M : Type} [AddCommGroup M] [Module ℂ M] (S : Set (Module.End ℂ M)) (X : Set M)
    (hS : ∀ b ∈ S, ∃ μ : ℂ, ∀ u ∈ X, b u = μ • u) : ∀ b ∈ Algebra.adjoin ℂ S, ∃ μ : ℂ, ∀ u ∈ X, b u = μ • u := by
  intro b hb
  induction hb using Algebra.adjoin_induction with
  | mem b hb => exact hS b hb
  | algebraMap r => exact ⟨r, fun u _ => Module.algebraMap_end_apply ℂ ℂ M r u⟩
  | add b b' _ _ ihb ihb' =>
    obtain ⟨μ, hμ⟩ := ihb
    obtain ⟨μ', hμ'⟩ := ihb'
    exact ⟨μ + μ', fun u hu => by rw [LinearMap.add_apply, hμ u hu, hμ' u hu, add_smul]⟩
  | mul b b' _ _ ihb ihb' =>
    obtain ⟨μ, hμ⟩ := ihb
    obtain ⟨μ', hμ'⟩ := ihb'
    exact ⟨μ * μ', fun u hu => by rw [Module.End.mul_apply, hμ' u hu, map_smul, hμ u hu, smul_smul, mul_comm]⟩

end GlobalTheory.SplitEigen

namespace GlobalTheory.SplitEigen


set_option maxHeartbeats 40000000 in
theorem label_scalar_split : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ (j : Fin D.R.m) (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j A3.A.fam.μ0).H), GlobalTheory.Hk3.IsOpsV R.toRealDat j A3.A.fam.μ0 h → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0) h → ∀ (P : Pl D.host.E), GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P → conjPl P ≠ P → ∀ d, GlobalTheory.Hk3.IsLab (Vc D j) P d → ∃ a : ℂ, ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c, h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) = a • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _hOk hC hEx _hH _hGE j c h hh hN P hP hconj d _hd
  obtain ⟨hCoreF, -, -, hOnto, -, -, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have hCore := hCoreF hEx
  have hM := hCore.models
  obtain ⟨P0, hP0, rfl⟩ := (hOnto _ hP).2 hconj
  have hsplit := (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hCore.lev hCore.fam hM).2 j A3.A.fam.μ0 h hh ⟨P0, hP0⟩
  have hK := RealDat3.kFormL_of (R := R) (F := F) hM

  have hop : ∀ k, k ≤ (Vc D j).rank → (R.toCx3 F).opLC j A3.A.fam.μ0 (Sum.inl (Sum.inl (⟨P0, hP0⟩, k))) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1)) := by
    intro k hk
    refine LinearMap.ext_on_range (hK j A3.A.fam.μ0).2 fun b => ?_
    rw [← CxData.jL_opL _ hK]
    exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) (hsplit k hk _)

  have hT : ∀ k, k ≤ (Vc D j).rank → ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
      h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) =
        cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k))) • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
    intro k hk x hx
    have e1 := (U2.mem_eigPart.1 hx) (Sum.inl (⟨P0, hP0⟩, k))
    have e2 : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (U2.liftHeckeOperators A3 (R.toCx3 F) j (Sum.inl (⟨P0, hP0⟩, k)) x) =
        h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) := by
      exact (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j A3.A.fam.μ0).H)) (LinearMap.congr_fun (hop k hk) x)).trans rfl
    rw [← e2, e1]
    exact Tw.out_smul (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j A3.A.fam.μ0).H) _ _

  have hD : ∀ k, k ≤ (Vc D j).rank → ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
      h (R.pl P0) (Finsupp.single (dualLab (splitLab (Vc D j).rank k)) 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) =
        starRingEnd ℂ (cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k)))) •
          (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
    intro k hk x hx
    have ha : LinearMap.adjoint (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1)) =
        h (R.pl P0) (Finsupp.single (dualLab (splitLab (Vc D j).rank k)) 1) := by
      rw [hN.2 _ hP]
      congr 1
      rw [Finsupp.mapRange_single, star_one, GlobalTheory.Hk3.dualC, Finsupp.mapDomain_single]
    have hc : Commute (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1))
        (LinearMap.adjoint (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1))) :=
      ha.symm ▸ hN.1 _ _ hP hP _ _
    exact (LinearMap.congr_fun ha _).symm.trans (adjoint_apply_of_eigen _ hc _ _ (hT k hk x hx))

  obtain ⟨a, ha, hae⟩ := GlobalTheory.SplitGen.gen_split (Vc D j) (R.pl P0) hconj _
    (GlobalTheory.DefiniteOps.rtr (GlobalTheory.SplitHeckeAdj.fin (Vc D j)) (R.cV j).W) d
  have key := adjoin_scalar _ {u | ∃ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
      u = (R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x)} (by
    rintro b ⟨k, hk, rfl | rfl⟩
    · refine ⟨cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k))), ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (GlobalTheory.DefiniteOps.hkF_eq (Vc D j) (R.pl P0) _ _).symm.trans ((hh _ hP _ _).symm.trans
        ((congrArg (R.HV j A3.A.fam.μ0).e (hT k hk x hx)).trans (map_smul _ _ _)))
    · refine ⟨starRingEnd ℂ (cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k)))), ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (GlobalTheory.DefiniteOps.hkF_eq (Vc D j) (R.pl P0) _ _).symm.trans ((hh _ hP _ _).symm.trans
        ((congrArg (R.HV j A3.A.fam.μ0).e (hD k hk x hx)).trans (map_smul _ _ _)))) a ha
  obtain ⟨μ, hμ⟩ := key
  refine ⟨μ, fun x hx => (hM.HV j A3.A.fam.μ0).1 ?_⟩
  have hfix : ∀ k ∈ GlobalTheory.Hk3.hyp (Vc D j) (R.pl P0), GlobalTheory.DefiniteOps.rtr (GlobalTheory.SplitHeckeAdj.fin (Vc D j)) (R.cV j).W k
      ((R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x)) =
        (R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) := by
    obtain ⟨n, hn⟩ := hCore.lev.βV j
    have hn' : IsBaseFrame (Vc D j) (R.βV j) (R.ΛV j) 1 := (one_pow n : (1 : ℕ) ^ n = 1) ▸ hn
    refine GlobalTheory.DefiniteOps.fixed_of_mem (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j A3.A.fam.μ0) hn' (R.pl P0) hP (R.cV j).coef.ρ _ ?_
    have hm := LinearMap.mem_range_self (R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x)
    rw [(hM.HV j A3.A.fam.μ0).2.1] at hm
    exact hm
  exact (hh _ hP _ _).trans ((GlobalTheory.DefiniteOps.hkF_eq _ _ _ _).trans ((hae _ hfix).symm.trans
    ((hμ _ ⟨x, hx, rfl⟩).trans (map_smul _ _ _).symm)))

end GlobalTheory.SplitEigen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjIdealEqOfConjPl
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.InertEigScalar

theorem conjIdeal_eq_of_conjPl {D : D7} (P : Pl D.host.E) (hc : conjPl P = P) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal := by
  have h1 : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) := by
    unfold Formalism.HermitianLatticesTheory.conjIdeal
    show _ = Ideal.span _
    congr 1
    ext r
    constructor
    · rintro ⟨s, hs, hr⟩
      refine ⟨s, hs, ?_⟩
      apply RingOfIntegers.ext
      change _ = (algebraMap (𝓞 D.host.E) D.host.E r)
      rw [hr]
      rfl
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
  rw [h1]
  exact congrArg HeightOneSpectrum.asIdeal hc


set_option maxHeartbeats 1000000 in
theorem inert_label_scalar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ (j : Fin D.R.m) (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j A3.A.fam.μ0).H), GlobalTheory.Hk3.IsOpsV R.toRealDat j A3.A.fam.μ0 h → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0) h → ∀ (P : Pl D.host.E), GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P → conjPl P = P → ∀ d, GlobalTheory.Hk3.IsLab (Vc D j) P d → ∃ a : ℂ, ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c, h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) = a • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _hOk hC _hEx _hH _hPG j c h hh _hN P hP hc d hd
  have hlab := (GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing (Vc D j) P d).1 hd
  obtain ⟨s', hs2, hsp, hspos, rfl⟩ :=
    (GlobalTheory.Hk3.labIn_selfDual_iff (Vc D j).rank d).1 ⟨hlab.1, hlab.2.1, hlab.2.2 hc⟩
  have hPg : P ∉ R.Pg := fun hm => (hP P (Or.inl hm)).1 rfl
  have hPQ : P ∉ R.Q A3.A.fam.μ0 := fun hm => (hP P (Or.inr hm)).1 rfl
  have hfix := conjIdeal_eq_of_conjPl P hc
  have hSb : P ∉ R.Sb := by
    have e : R.Sb = R.Pg := hC.allPl
    rw [e]; exact hPg
  have hoff : Formalism.IndefR.Bridge.InertOff P (R.Sb : Set (Pl D.host.E)) := ⟨hfix, fun hm => hSb (Finset.mem_coe.1 hm)⟩
  have honto : R.in_onto := hC.inert.onto
  have hex : ∃ Q, R.plI Q = P := honto P hoff
  obtain ⟨Q, hQ⟩ := hex
  have hQok : Q ∈ A3.okI A3.A.fam.μ0 := by
    refine (hC.inert.tie.okI A3.A.fam.μ0 Q).2 ⟨?_, ?_⟩
    · rw [hQ]; exact hfix
    · rw [hQ, hC.allPl]
      simp only [Set.mem_union, Finset.mem_coe]
      tauto
  subst hQ
  have hLt : R.in_L := hC.inert.hL
  have hn := hLt j A3.A.fam.μ0
  obtain ⟨Comparison₂⟩ := hn
  let inR' : ↥(A3.okI A3.A.fam.μ0) × List ℕ → Prop :=
    fun k => Formalism.L2.Col.InertTypeOk (Vc D j).rank k.2 ∧ R.plI k.1 = R.plI Q
  let Tie' : Bridge.HeckeTie (Bridge.ratF (Vc D j)) (R.B.L j A3.A.fam.μ0).pres (A3.heckeLI j A3.A.fam.μ0) inR'
      (fun k => IsLabElt (Vc D j) (R.plI k.1) (GlobalTheory.Hk3.labIn (Vc D j).rank k.2))
      (fun k => IsLocElt (Vc D j) (R.plI k.1)) :=
    { hx := Comparison₂.hx, hA := Comparison₂.hA, hx_ok := fun i hi => Comparison₂.hx_ok i hi.1, hA_loc := fun i hi => Comparison₂.hA_loc i hi.1,
      chi_loc := fun i hi => Comparison₂.chi_loc i hi.1, hDC := fun i hi => Comparison₂.hDC i hi.1, op_eq := fun i hi => Comparison₂.op_eq i hi.1 }
  let k : ↥(A3.okI A3.A.fam.μ0) × List ℕ := (⟨Q, hQok⟩, s')
  have hk : inR' k := ⟨⟨hsp, hspos, hs2⟩, rfl⟩
  have hin : ∀ i, inR' i → GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 (R.plI i.1) ∧ conjPl (R.plI i.1) = R.plI i.1 ∧
      (GlobalTheory.Hk3.labIn (Vc D j).rank i.2).Pairwise (fun a b => b ≤ a) := by
    rintro ⟨Q', t'⟩ ⟨hty, hpl⟩
    simp only at hpl ⊢
    rw [hpl]
    exact ⟨hP, hc, ((GlobalTheory.Hk3.labIn_selfDual_iff _ _).2 ⟨t', hty.2.2, hty.1, hty.2.1, rfl⟩).2.1⟩
  have key := (GlobalTheory.InertHeckeLift.inert_lifts R.toRealDat F.lv2 hC.base.lev hC.base.fam hC.base.models j
    A3.A.fam.μ0 _ (fun k => R.plI k.1) (fun k => GlobalTheory.Hk3.labIn (Vc D j).rank k.2) (A3.heckeLI j A3.A.fam.μ0) inR'
    hin Tie' k hk).2.2.2 h hh
  have hK : (R.toCx3 F).KFormL := Formalism.IndefR.Links.RealDat3.kFormL_of (F := F) hC.base.models
  have hop : (R.toCx3 F).opLC j A3.A.fam.μ0 (Sum.inl (Sum.inr k)) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (h (R.plI Q) (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank s') 1)) := by
    apply LinearMap.ext_on_range (hK j A3.A.fam.μ0).2
    intro b
    rw [← Formalism.IndefR.Cx.CxData.jL_opL (R.toCx3 F) hK]
    show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.jV j A3.A.fam.μ0 (A3.heckeLI j A3.A.fam.μ0 k _)) =
      Tw.mk (twAt D.what₂.embLL A3.A.v0) (h (R.plI Q) _ (R.jV j A3.A.fam.μ0 _))
    exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) (key _)
  refine ⟨cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inr k)), fun x hx => ?_⟩
  have hx' : (R.toCx3 F).opLC j A3.A.fam.μ0 (Sum.inl (Sum.inr k)) x = c (Sum.inr k) • x :=
    (Formalism.IndefR.U2.mem_eigPart.1 hx) (Sum.inr k)
  rw [hop] at hx'
  exact congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0)) hx'

end GlobalTheory.InertEigScalar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftInjectiveGoodPartJointEigenspace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

set_option maxHeartbeats 1000000

namespace GlobalTheory.InjEigen

theorem label_eigensystem : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ), ∃ h, GlobalTheory.Hk3.IsOpsV R.toRealDat j A3.A.fam.μ0 h ∧ ∃ e : Eig D, ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c, ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P → GlobalTheory.Hk3.IsLab (Vc D j) P d → h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) = e P d • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hch hex hOk hpg j c
  obtain ⟨h, hops, hnf⟩ :=
    (GlobalTheory.DefiniteOps.definite_ops R.toRealDat F.lv2 hch.base.lev hch.base.fam hch.base.models).2 j A3.A.fam.μ0
  have key : ∀ P d, ∃ a : ℂ, GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P →
      GlobalTheory.Hk3.IsLab (Vc D j) P d → ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
        h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) =
          a • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
    intro P d
    by_cases hg : GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P
    · by_cases hl : GlobalTheory.Hk3.IsLab (Vc D j) P d
      · first
          | exact (Classical.em (Formalism.L2.DIV.conjPl P = P)).elim
              (fun hc => (GlobalTheory.InertEigScalar.inert_label_scalar R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
              (fun hc => (GlobalTheory.SplitEigen.label_scalar_split R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
          | exact (Classical.em (Formalism.DivisionValues.conjPl P = P)).elim
              (fun hc => (GlobalTheory.InertEigScalar.inert_label_scalar R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
              (fun hc => (GlobalTheory.SplitEigen.label_scalar_split R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
      · exact ⟨0, fun _ hl' => absurd hl' hl⟩
    · exact ⟨0, fun hg' => absurd hg' hg⟩
  choose e he using key
  exact ⟨h, hops, e, fun x hx P d hg hl => he P d hg hl x hx⟩

theorem inj_eig : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → LiftInj R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (x y : (R.toCx3 F).FLC j A3.A.fam.μ0), x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c → (R.toCx3 F).θ' j A3.A.fam.μ0 x ≠ 0 → y ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c ⊓ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j → (R.toCx3 F).θ' j A3.A.fam.μ0 y = 0 → y = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hch hex hinj hOk hpg j c x y hx hθx hy hθy
  obtain ⟨h, hops, e, he⟩ := label_eigensystem R F hok hch hex hOk hpg j c
  have hy' := Submodule.mem_inf.mp hy
  have hgood := GlobalTheory.goodV_of_goodL R F hok hch hex hOk hpg j y hy'.2
  clear hok hch hex hOk hpg hy
  have hθ : ∀ z : (R.toCx3 F).FLC j A3.A.fam.μ0, (R.toCx3 F).θ' j A3.A.fam.μ0 z =
      R.phs j • Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j A3.A.fam.μ0) z := fun z => rfl
  have hp : R.phs j ≠ 0 := by
    intro h0
    apply hθx
    rw [hθ, h0]
    exact zero_smul ℂ _
  have hcj : Formalism.IndefR.Links.cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) ≠ 0 := by
    intro h0
    apply hp
    rw [← Formalism.IndefR.Links.cj_cj (twAt D.what₂.embLL A3.A.v0) (R.phs j), h0, map_zero]
  have hx0 : R.thG j A3.A.fam.μ0 (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) ≠ 0 := by
    intro h0
    apply hθx
    rw [hθ]
    have h1 : Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j A3.A.fam.μ0) x = 0 := h0
    rw [h1]
    first
      | exact smul_zero (M := Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j _).H) (R.phs j)
      | exact smul_zero (M := Tw (twAt D.what₂.embLL A3.A.v0) _) (R.phs j)
      | (simp only [smul_zero]; rfl)
  have hy0 : R.thG j A3.A.fam.μ0 (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) = 0 := by
    have h2 : Formalism.IndefR.Links.cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j A3.A.fam.μ0 (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) = 0 := hθy
    exact (smul_eq_zero.mp h2).resolve_left hcj
  exact hinj j h hops e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) (fun P d hg hl => he x hx P d hg hl)
    (fun P d hg hl => he y hy'.1 P d hg hl) hx0 hgood hy0

end GlobalTheory.InjEigen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftInjectiveGoodPartJointEigenspaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_injective_goodPart_jointEigenspace : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → LiftInj R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (x y : (R.toCx3 F).FLC j A3.A.fam.μ0), x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c → (R.toCx3 F).θ' j A3.A.fam.μ0 x ≠ 0 → y ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c ⊓ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j → (R.toCx3 F).θ' j A3.A.fam.μ0 y = 0 → y = 0 := by
  first | exact @GlobalTheory.InjEigen.inj_eig | exact GlobalTheory.InjEigen.inj_eig | (intros; apply GlobalTheory.InjEigen.inj_eig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodFormsLeRangeThetaAdjointBaseTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodFormsLeRangeThetaAdjointBaseTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.LiftOntoGood

theorem mem_range_of_fixed {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y)
    (hsa : LinearMap.adjoint e = e) (hid : e * e = e) (hfix : ∀ y, e (th y) = th y)
    (hinj : ∀ v, e v = v → LinearMap.adjoint th v = 0 → v = 0) (x : Y) (hx : e x = x) : x ∈ LinearMap.range th := by
  have hcomp : e ∘ₗ th = th := LinearMap.ext hfix
  rw [← Submodule.orthogonal_orthogonal (LinearMap.range th)]
  intro v hv
  have hv0 : LinearMap.adjoint th v = 0 := by
    refine ext_inner_left ℂ fun z => ?_
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    exact hv _ (LinearMap.mem_range_self _ z)
  have h1 : LinearMap.adjoint th (e v) = 0 := by
    have e2 : LinearMap.adjoint th (e v) = LinearMap.adjoint (e ∘ₗ th) v := by
      rw [LinearMap.adjoint_comp, hsa, LinearMap.comp_apply]
    rw [e2, hcomp, hv0]
  have h2 : e (e v) = e v := by rw [← Module.End.mul_apply, hid]
  have h3 : e v = 0 := hinj (e v) h2 h1
  rw [← hx, ← LinearMap.adjoint_inner_left, hsa, h3, inner_zero_left]


set_option maxHeartbeats 1000000 in
theorem goodW_le_range : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → UpInjW R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → R.toRealDat.LUnif → ∀ j, U2.goodW A3 (R.toCx3 F) j ≤ LinearMap.range ((R.toCx3 F).θ' j A3.A.fam.μ0) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hUp _ _ hU j
  have hM : R.toRealDat.IsModels := hC.base.models
  have hC3 := RealDat3.characterisation_of_weak hC hEx
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hsa : LinearMap.adjoint (GlobalTheory.Hk3.eH R.toRealDat j) = GlobalTheory.Hk3.eH R.toRealDat j :=
    GlobalTheory.LiftScalarL.adjoint_eH R.toRealDat hM hX j
  have hc : ∀ g, ∑ a, RealDat.eC (A := A3.A) (sg0 D A3.A) a * RealDat.eC (A := A3.A) (sg0 D A3.A) (a⁻¹ * g) =
      RealDat.eC (A := A3.A) (sg0 D A3.A) g := fun g => GlobalTheory.Hk3.conv_map_idem _ (idemOf_mul_self A3.A.X hX) (sg0 D A3.A) g
  have hidem : GlobalTheory.Hk3.eH R.toRealDat j * GlobalTheory.Hk3.eH R.toRealDat j = GlobalTheory.Hk3.eH R.toRealDat j :=
    GlobalTheory.Hk3.sum_rep_idem _ _ hc
  have hinj := (hM.HW j (sg0 D A3.A)).1
  have hrange := (hM.HW j (sg0 D A3.A)).2.1
  have hfixth : ∀ y, GlobalTheory.Hk3.eH R.toRealDat j (R.thG j A3.A.μ0 y) = R.thG j A3.A.μ0 y := by
    intro y
    have hm := hC3.thP.thF_mem j A3.A.μ0 y
    rw [← hrange] at hm
    obtain ⟨x0, hx0⟩ := hm
    have e1 : R.thG j A3.A.μ0 y = GlobalTheory.Hk3.eH R.toRealDat j x0 := by
      apply hinj
      rw [hC3.thP.thG j A3.A.μ0 y, ← hx0, GlobalTheory.LiftScalarL.e_eH R.toRealDat hM j x0]
    rw [e1, ← Module.End.mul_apply, hidem]
  have key := mem_range_of_fixed (R.thG j A3.A.μ0) (GlobalTheory.Hk3.eH R.toRealDat j) hsa hidem hfixth (hUp j A3.A.μ0)
  intro w hw
  have hw' : w ∈ LinearMap.range ((R.toCx3 F).w0C false j) := hw
  rw [GlobalTheory.LevelRange.range_w0C_eq R F hOk hC hU false j] at hw'
  obtain ⟨x, rfl⟩ : ∃ x : (R.HW j (sg0 D A3.A)).H, Tw.mk (twAt D.what₂.embLL A3.A.v0) x = w := ⟨w, rfl⟩
  have hgood : (R.HW j (sg0 D A3.A)).e x ∈
      R.toRealDat.Wat j (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) := hw'
  have hfix : GlobalTheory.Hk3.eH R.toRealDat j x = x := by
    apply hinj
    rw [GlobalTheory.LiftScalarL.e_eH R.toRealDat hM j]
    exact GlobalTheory.LiftScalarCompare.postOn_of_good hgood
  obtain ⟨y, hy⟩ := key _ hfix
  have hne : cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) ≠ 0 := by
    intro h0
    have := congrArg norm h0
    rw [norm_cj, (hC.phase j).1, norm_zero] at this
    exact one_ne_zero this
  refine ⟨Tw.mk (twAt D.what₂.embLL A3.A.v0) ((cj (twAt D.what₂.embLL A3.A.v0) (R.phs j))⁻¹ • y), ?_⟩
  show cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j A3.A.μ0 ((cj (twAt D.what₂.embLL A3.A.v0) (R.phs j))⁻¹ • y) = x
  rw [map_smul, smul_inv_smul₀ hne, hy]

end GlobalTheory.LiftOntoGood
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodFormsLeRangeThetaAdjointBaseTupleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_forms_le_range_theta_adjoint_base_tuple : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → UpInjW R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → R.toRealDat.LUnif → ∀ j, U2.goodW A3 (R.toCx3 F) j ≤ LinearMap.range ((R.toCx3 F).θ' j A3.A.fam.μ0) := by
  exact @GlobalTheory.LiftOntoGood.goodW_le_range
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KernelProjectionPreservesGoodFormsBaseLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KernelProjectionPreservesGoodFormsBaseLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
open Formalism.IndefR.CxPass Formalism.IndefR.CxPass.LevelOperators

noncomputable section

namespace GlobalTheory.KerProjGood

theorem starProjection_comm {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (S : Submodule ℂ V) (T : V →ₗ[ℂ] V) (hT : ∀ u ∈ S, T u ∈ S) (hTa : ∀ u ∈ S, LinearMap.adjoint T u ∈ S) (z : V) :
    (S.starProjection (T z) : V) = T (S.starProjection z) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hT _ (Submodule.coe_mem _)) fun w hw => ?_
  rw [← map_sub, ← LinearMap.adjoint_inner_right]
  have h := Submodule.sub_starProjection_mem_orthogonal (K := S) z
  rw [inner_eq_zero_symm]
  exact h _ (hTa w hw)

end GlobalTheory.KerProjGood


open GlobalTheory.KerProjGood in
theorem GlobalTheory.kerProj_goodL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j, ∀ y ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j, ((LinearMap.ker ((R.toCx3 F).θ' j A3.A.fam.μ0)).starProjection y : (R.toCx3 F).FLC j A3.A.fam.μ0) ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hC _ _ hG j y hy
  have hM := hC.base.models
  have hK := RealDat3.kFormL_of (F := F) hM
  have hJ := RealDat3.jIsoL_of (F := F) hM
  set X := R.toCx3 F with hX
  set t := A3.A.fam.μ0
  have sp := lift_embeddings_span hK j t
  have jr : ∀ (g : G) x, X.jL j t ((A3.fam3.F.L j t).r g x) = X.opLC j t (Sum.inr g) (X.jL j t x) :=
    fun g x => X.jL_opL hK j t (Sum.inr g) x

  have hker : ∀ (g : G), ∀ u ∈ LinearMap.ker (X.θ' j t), X.opLC j t (Sum.inr g) u ∈ LinearMap.ker (X.θ' j t) := by
    intro g u hu
    rw [LinearMap.mem_ker] at hu ⊢
    have h := congrArg (fun f => f u) (theta_rho (r := (A3.fam3.F.L j t).r) (ρ := fun g => X.opLC j t (Sum.inr g))
      sp jr (fun g x => hG.2 j t g x) g)
    simp only [LinearMap.comp_apply] at h
    rw [h, hu, map_zero]
  have hadj : ∀ g : G, LinearMap.adjoint (X.opLC j t (Sum.inr g)) = X.opLC j t (Sum.inr g⁻¹) := fun g =>
    (X.opLC_adjoint hK F.cv hJ j t (Sum.inr g) (Sum.inr g⁻¹)
      fun f f' => csum_act_inv (hok.ok2.lifts j t).act g f f').symm
  have hcomm : ∀ (g : G) z, ((LinearMap.ker (X.θ' j t)).starProjection (X.opLC j t (Sum.inr g) z) : X.FLC j t) =
      X.opLC j t (Sum.inr g) ((LinearMap.ker (X.θ' j t)).starProjection z) := fun g z =>
    starProjection_comm _ _ (hker g) (fun u hu => by rw [hadj]; exact hker g⁻¹ u hu) z
  have hrange : U2.goodL A3 X F.P0 F.ψ0 F.P1 F.ψ1 j = LinearMap.range (opV A3.fam3.base3.v0.embedding
      (fun g => X.opLC j t (Sum.inr g)) (goodAt (A3.fam3.F.lvlA F.P0 F.ψ0).X (A3.fam3.F.lvlA F.P0 F.ψ0).P
        (A3.fam3.F.lvlA F.P0 F.ψ0).ψ)) := by
    show X.goodPartComplexPoints F.cv false j t = _
    unfold CxData.goodPartComplexPoints
    rw [show F.cv.v0L X.zs false j t = BlockGood.goodR (A3.fam3.F.L j t) (A3.fam3.F.lvlA F.P0 F.ψ0) from rfl, goodR_eq]
    conv_rhs => rw [LinearMap.range_eq_map, ← sp, Submodule.map_span]
    congr 1
    ext u
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨X.jL j t x, ⟨x, rfl⟩, (j_opF jr _ x).symm⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, j_opF jr _ x⟩
  rw [hrange] at hy ⊢
  obtain ⟨z, rfl⟩ := hy
  refine ⟨(LinearMap.ker (X.θ' j t)).starProjection z, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [opV, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hcomm]
  exact Finset.sum_congr rfl fun g _ => congrArg _ (hcomm g z).symm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KernelProjectionPreservesGoodFormsBaseLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelProjection_preserves_good_forms_base_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j, ∀ y ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j, ((LinearMap.ker ((R.toCx3 F).θ' j A3.A.fam.μ0)).starProjection y : (R.toCx3 F).FLC j A3.A.fam.μ0) ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j := by
  first | exact @GlobalTheory.kerProj_goodL | exact GlobalTheory.kerProj_goodL | (intros; apply GlobalTheory.kerProj_goodL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfMemBoth
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.OntoLinAlg

open Formalism.IndefR.U2

variable {I A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B]

theorem op_mem_ker {θ : A →ₗ[ℂ] B} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
    (hI : Intw θ op opB) (i : I) {k : A} (hk : k ∈ LinearMap.ker θ) : op i k ∈ LinearMap.ker θ := by
  rw [LinearMap.mem_ker] at hk ⊢
  rw [hI, hk, map_zero]

theorem op_mem_orth {θ : A →ₗ[ℂ] B} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
    (hI : Intw θ op opB) (hA : AdjClosed op) (i : I) {v : A} (hv : v ∈ (LinearMap.ker θ)ᗮ) :
    op i v ∈ (LinearMap.ker θ)ᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  obtain ⟨i', hi'⟩ := hA i
  rw [← LinearMap.adjoint_inner_left, ← hi']
  exact hv _ (op_mem_ker hI i' hu)

theorem eq_zero_of_mem_both {K : Submodule ℂ A} {z : A} (h1 : z ∈ K) (h2 : z ∈ Kᗮ) : z = 0 := by
  have := (Submodule.mem_orthogonal _ _).mp h2 z h1
  exact inner_self_eq_zero.mp this

theorem ontoParts_of {θ : A →ₗ[ℂ] B} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
    {good : Submodule ℂ A} {goodB : Submodule ℂ B} (Ix : Set (I → ℂ))
    (hI : Intw θ op opB) (hA : AdjClosed op) (hOnto : goodB ≤ LinearMap.range θ)
    (hPr : ∀ y ∈ good, ((LinearMap.ker θ).starProjection y : A) ∈ good)
    (hInj : ∀ (c : I → ℂ) (x y : A), x ∈ eigPart op c → θ x ≠ 0 → y ∈ eigPart op c ⊓ good → θ y = 0 → y = 0) :
    OntoParts (LinearMap.adjoint θ) op opB good goodB Ix := by
  intro c hc y hy
  set K := LinearMap.ker θ with hK
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc.2
  obtain ⟨x0, hx0⟩ := hOnto hw.2
  set x := x0 - K.starProjection x0 with hxdef
  have hxo : x ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal x0
  have hθx : θ x = w := by
    have : θ (K.starProjection x0) = 0 := LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem K x0)
    rw [hxdef, map_sub, this, sub_zero, hx0]
  have hxe : x ∈ eigPart op c := by
    rw [mem_eigPart]
    intro i
    have hz1 : op i x - c i • x ∈ Kᗮ := Submodule.sub_mem _ (op_mem_orth hI hA i hxo) (Submodule.smul_mem _ _ hxo)
    have hz2 : op i x - c i • x ∈ K := by
      rw [hK, LinearMap.mem_ker, map_sub, map_smul, hI, hθx, (mem_eigPart.mp hw.1) i, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_mem_both hz2 hz1)
  set y1 := K.starProjection y with hy1
  have hy1K : y1 ∈ K := Submodule.starProjection_apply_mem K y
  have hy2 : y - y1 ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal y
  have hy1e : y1 ∈ eigPart op c := by
    rw [mem_eigPart]
    intro i
    have hyi := (mem_eigPart.mp hy.1) i
    have e : op i y1 - c i • y1 = -(op i (y - y1) - c i • (y - y1)) := by
      rw [map_sub, smul_sub, hyi]; abel
    have hz1 : op i y1 - c i • y1 ∈ K := Submodule.sub_mem _ (op_mem_ker hI i hy1K) (Submodule.smul_mem _ _ hy1K)
    have hz2 : op i y1 - c i • y1 ∈ Kᗮ := by
      rw [e]
      exact Submodule.neg_mem _ (Submodule.sub_mem _ (op_mem_orth hI hA i hy2) (Submodule.smul_mem _ _ hy2))
    exact sub_eq_zero.mp (eq_zero_of_mem_both hz1 hz2)
  have hy10 : y1 = 0 := hInj c x y1 hxe (by rw [hθx]; exact hw0) ⟨hy1e, hPr y hy.2⟩ (LinearMap.mem_ker.mp hy1K)
  rw [← LinearMap.orthogonal_ker]
  have : y = y - y1 := by rw [hy10, sub_zero]
  rw [this]
  exact hy2

end GlobalTheory.OntoLinAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftOntoOfInjectiveEigenspaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.LiftOntoRed

theorem onto_red : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → LiftInj R.toRealDat → UpInjW R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → R.toRealDat.LUnif → ∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hC hEx hLI hUI hH hPG hLU hW hTh j
  exact GlobalTheory.OntoLinAlg.ontoParts_of _ (fun i x => hTh.intw j _ i x)
    (U2.adjoint_closed_lift_operators hH (RealDat3.kFormL_of hC.base.models) (RealDat3.jIsoL_of hC.base.models) j)
    (GlobalTheory.T.good_forms_le_range_theta_adjoint_base_tuple R F hok hC hEx hUI hH hPG hLU j) (GlobalTheory.T.kernelProjection_preserves_good_forms_base_level R F hok hC hEx hH hPG j)
    (GlobalTheory.T.thetaLift_injective_goodPart_jointEigenspace R F hok hC hEx hLI hH hPG j)

end GlobalTheory.LiftOntoRed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftOntoOfInjectiveEigenspacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_onto_of_injective_eigenspaces : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → LiftInj R.toRealDat → UpInjW R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → R.toRealDat.LUnif → ∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW := by
  first | exact @GlobalTheory.LiftOntoRed.onto_red | exact GlobalTheory.LiftOntoRed.onto_red | (intros; apply GlobalTheory.LiftOntoRed.onto_red <;> assumption)
end
