module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatakeParameterAtInertPlaceOfSpherical
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartsReadingStepMoveBasePointsOneOffLevelPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCanonicalModuleSuccessor
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowModCanon

open MeasureTheory _root_.Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.PeterssonHilbertSpace
open scoped InnerProductSpace

theorem ipM_smul_measure {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : DSModel V S)
    (hne : SmNonzero M) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)) {a : ℝ} (ha : 0 ≤ a) (T T' : MMap M)
    (h : ∃ c, IsMultIP M ν 𝓕 T T' c) :
    ipM M (ENNReal.ofReal a • ν) 𝓕 T T' = (a : ℂ) * ipM M ν 𝓕 T T' := by
  have h1 := ipM_spec M ν 𝓕 T T' h
  have h2 : IsMultIP M (ENNReal.ofReal a • ν) 𝓕 T T' ((a : ℂ) * ipM M ν 𝓕 T T') := by
    intro v v'
    obtain ⟨hi, he⟩ := h1 v v'
    refine ⟨?_, ?_⟩
    · rw [IntegrableOn, Measure.restrict_smul]
      exact hi.smul_measure ENNReal.ofReal_ne_top
    · rw [Measure.restrict_smul, integral_smul_measure, he, ENNReal.toReal_ofReal ha, Complex.real_smul, mul_assoc]
  have h3 := ipM_spec M _ 𝓕 T T' ⟨_, h2⟩
  choose w hw using hne
  have hw' : ∀ τ, (w τ : M.H τ) ≠ 0 := fun τ h => hw τ (Submodule.coe_eq_zero.1 h)
  have hv0 : ∏ τ, ⟪(w τ : M.H τ), (w τ : M.H τ)⟫_ℂ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 (hw' τ)
  exact hasPeterssonInner_unique M _ 𝓕 T T' w hv0 h3 h2

end GlobalTheory.RowModCanon

namespace GlobalTheory.RowModCanon

open MeasureTheory Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev
  Formalism.IndefR.Links Formalism.IndefR.RecTie


end GlobalTheory.RowModCanon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeNonzeroRecursionOfEigen
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TypeNZJoin

open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie


set_option maxHeartbeats 1000000 in
theorem inj_at {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (hT : ∀ j t, GlobalTheory.DownLift.TypeNZ X.R j t) (i : D.nd.Loc) (hS : GlobalTheory.NJoin.EigString X i)
    (hG : GlobalTheory.NJoin.EigGood X i) (hμ : Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (x : D.nd.X i) (hx : x ∈ ZgoodN D.nd D.naut i) (f : D.what₂.Mt (D.nd.mu i) (j.1 + 1))
    (hf : (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x)
    (h0 : D.what₂.thetaP (D.nd.mu i) (j.1 + 1) f = 0) : f = 0 := by
  have hC := X.given.core
  have hfm := (X.IL.jMt _ hμ j f).2
  obtain ⟨y, hy⟩ : ∃ y, (LinearEquiv.ofInjective _ (X.hinj j (X.tupT (D.nd.mu i)))).symm
      ⟨((X.IL.jMt _ hμ j f).1 : Formalism.L2.Theta.GA D (Vc D j) → (X.R.cV j).W), hfm.1⟩ = y := ⟨_, rfl⟩
  have hyf : X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f := by
    rw [← hy]
    exact congrArg Subtype.val ((LinearEquiv.ofInjective _ (X.hinj j (X.tupT (D.nd.mu i)))).apply_symm_apply _)
  have hthG : X.R.thG j (X.tupT (D.nd.mu i)) y = 0 := by
    have hM := GlobalTheory.ThetaLevelP.thF_mem_level X.R X.F hC.lev hC.models hC.thP X.R.hv0 false j (X.tupT (D.nd.mu i)) y
      (by rw [hyf]; exact hfm.2)
    obtain ⟨w, hw1, hw2, hw3⟩ := X.fire.2.1 (D.nd.mu i) hμ j f
    have hw' : PiTensorProduct.lift (X.R.thF j (X.tupT (D.nd.mu i)) y) ∘ₗ
        (toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj).embK j =
        (toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj).thC _ j (X.IL.jMt _ hμ j f) := by
      rw [← hy]; rfl
    have hwe : w = PiTensorProduct.lift (X.R.thF j (X.tupT (D.nd.mu i)) y) := by
      refine sub_eq_zero.1 (X.fire.2.2 j _ (sub_mem hw1 (Submodule.mem_map_of_mem hM)) ?_)
      exact (LinearMap.sub_comp _ _ _).trans (by rw [hw2]; exact sub_eq_zero.2 hw'.symm)
    have hth := X.recR.tied.lift.theta (D.nd.mu i) hμ j f w (X.fire.1 _ hμ j) hw1 hw2 hw3
    rw [h0, map_zero, ZeroMemClass.coe_zero, hwe] at hth
    have h2 : PiTensorProduct.lift (postOn _ (X.R.eWf j (sg0 D X.A)) (X.R.thF j (X.tupT (D.nd.mu i)) y)) = 0 := by
      rw [GlobalTheory.ThetaFireLift.lift_postOn]; exact hth.symm
    have h3 : (X.R.HW j (sg0 D X.A)).e (X.R.thG j (X.tupT (D.nd.mu i)) y) = 0 := by
      rw [hC.thP.thG]; exact (LinearEquiv.map_eq_zero_iff _).1 h2
    exact (hC.models.HW j _).1 (h3.trans (map_zero _).symm)
  have hy0 : y = 0 := by
    by_contra hne
    obtain ⟨h, hh⟩ := GlobalTheory.LiftOntoCompare.exists_opsV hC.lev hC.models j (X.tupT (D.nd.mu i))
    obtain ⟨s, hs1, hs2⟩ := hS hμ j hj x hx f hf y hyf hne h hh
    exact hne (hT j _ h hh s hs1 y hs2 (hG hμ j hj x hx f hf y hyf) hthG)
  have h4 : X.IL.jMt _ hμ j f = 0 := by
    apply Subtype.ext
    show X.fn hμ j f = 0
    rw [← hyf, hy0, map_zero]
  exact (LinearEquiv.map_eq_zero_iff _).1 h4

theorem of_cast {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (S : Submodule ℂ (D.what₂.Mt μ b))
    (H : ∀ f : D.what₂.Mt μ a, (h ▸ f : D.what₂.Mt μ b) ∈ S → D.what₂.thetaP μ a f = 0 → f = 0) :
    ∀ F ∈ S, D.what₂.thetaP μ b F = 0 → F = 0 := by
  subst h
  exact H

end GlobalTheory.TypeNZJoin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceOutsideBadSets
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.OffSQ

end GlobalTheory.OffSQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobenius
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.DenseInvFrob

theorem isSplitAt_of_inertiaDeg_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E]
    (w : HeightOneSpectrum (𝓞 E)) (hf : w.asIdeal.inertiaDeg ℤ = 1)
    (he : w.asIdeal.ramificationIdx ℤ = 1) : IsSplitAt w := by
  classical
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  set p : Ideal (𝓞 (maximalRealSubfield E)) := v.asIdeal with hp
  haveI : p.IsPrime := v.isPrime
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI hlo : w.asIdeal.LiesOver p := ⟨rfl⟩
  by_contra hns
  have hfin : (p.primesOver (𝓞 E)).Finite := Algebra.QuasiFinite.finite_primesOver p
  let _ : Fintype (p.primesOver (𝓞 E)) := hfin.fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  have hrank : Module.finrank (𝓞 (maximalRealSubfield E)) (𝓞 E) = 2 := by
    rw [← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]
    exact (IsFractionRing.finrank_eq (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) (𝓞 E) E).symm
  rw [hrank] at hsum
  have hf1 : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield E)) = 1 := by
    have := Ideal.inertiaDeg_tower (R := ℤ) p w.asIdeal
    rw [hf] at this
    exact Nat.eq_one_of_mul_eq_one_left this.symm
  have he1 : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
    have := Ideal.ramificationIdx_tower (R := ℤ) p w.asIdeal
    rw [he] at this
    exact Nat.eq_one_of_mul_eq_one_left this.symm
  have hPmem : w.asIdeal ∈ p.primesOver (𝓞 E) := ⟨inferInstance, hlo⟩
  have huniq : ∀ q : p.primesOver (𝓞 E), q = ⟨w.asIdeal, hPmem⟩ := by
    intro q
    have hq : q.1.IsPrime := q.2.1
    have hql : q.1.LiesOver p := q.2.2
    have hne : q.1 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q.1
    let u : HeightOneSpectrum (𝓞 E) := ⟨q.1, hq, hne⟩
    by_contra hqw
    apply hns
    refine ⟨u, fun h => hqw (Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)), ?_⟩
    ext1
    simp only [HeightOneSpectrum.under_asIdeal]
    exact hql.over.symm
  rw [Finset.sum_eq_single ⟨w.asIdeal, hPmem⟩ (fun b _ hb => absurd (huniq b) hb)
    (fun h => absurd (Finset.mem_univ _) h)] at hsum
  simp only [he1, hf1, mul_one] at hsum
  omega

end GlobalTheory.DenseInvFrob

namespace GlobalTheory.DenseInvFrob

end GlobalTheory.DenseInvFrob
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatSLatAdIff
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.LocCarry

theorem prV_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    (fun i => prV (E := E) v ((M *ᵥ w) i)) = M.map (prV (E := E) v) *ᵥ (fun i => prV (E := E) v (w i)) := by
  ext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem coe_bc_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    (((bc (prV (E := E) v) x)⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) :
      Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) =
      ((x⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _).map (prV (E := E) v) := by
  rw [← map_inv]
  rfl

theorem coe_bc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    ((bc (prV (E := E) v) x : GL (Fin N) (E ⊗[F] v.adicCompletion F)) :
      Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) =
      (x : Matrix (Fin N) (Fin N) _).map (prV (E := E) v) := rfl

theorem mem_latS_latAd_iff : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)),
    Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (z : Fin N → E ⊗[F] v.adicCompletion F),
      z ∈ latS (F := F) (v.adicCompletion F) (intV E v) (latAd x Lb) ↔
        (((bc (prV (E := E) v) x)⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈
          latS (F := F) (v.adicCompletion F) (intV E v) Lb := by
  intro F E _ _ _ _ _ _ N x Lb hfin hspan v z
  have hrec := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin N) Lb hfin hspan x
  have hpr : ∀ y : Fin N → E ⊗[F] v.adicCompletion F,
      (fun i => prV (E := E) v (Formalism.UG.P.afsplitIE v (y i))) = y := fun y => by
    ext i; exact Formalism.UG.P.afsplit_prV_IE v (y i)
  have hlat : Formalism.L2.PairingIndexBounds.F.latAd x Lb = Formalism.UG.CS.globLat x Lb := Submodule.span_eq (Formalism.UG.CS.globLat x Lb)
  rw [hlat]
  constructor
  · intro hz
    have h1 := Formalism.L2.Geo.Def.PN.IE_latS (Formalism.UG.CS.globLat x Lb) v hz
    have h2 := (hrec _).1 h1
    have h3 := Formalism.L2.Geo.Def.PN.prV_latS Lb v h2
    rw [prV_mulVec, hpr, ← coe_bc_inv] at h3
    exact h3
  · intro hz
    have h1 := Formalism.L2.Geo.Def.PN.IE_latS Lb v hz
    set u : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
      ((x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _) *ᵥ
        (fun i => Formalism.UG.P.afsplitIE v (((((bc (prV (E := E) v) x)⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) :
          Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ z) i)) with hu
    have h2 : u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.UG.CS.globLat x Lb) := by
      refine (hrec u).2 ?_
      rw [hu, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact h1
    have h3 := Formalism.L2.Geo.Def.PN.prV_latS (Formalism.UG.CS.globLat x Lb) v h2
    rw [hu, prV_mulVec, hpr, ← coe_bc, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h3
    exact h3

end GlobalTheory.LocCarry
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHeckeSplitPlaceSetIffDoubleCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHeckeSplitPlaceSetIffDoubleCoset
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TSetDoubleCoset

theorem trivOutside_mul {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GA L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro v hv
  have e : ((x * y : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) =
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [e, Matrix.map_mul, hx v hv, hy v hv, Matrix.mul_one]

theorem mem_GLint_of_entries {K : Type} [Field K] {n : ℕ} (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem loc_mem_GLint {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L)
    {k : GA L n} (hk : k ∈ Umax L n) :
    s.loc n k ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
  apply mem_GLint_of_entries
  · intro a b
    exact GlobalTheory.splitPlace_proj_mem_integers_of_integral s (hk a b)
  · intro a b
    rw [← map_inv]
    exact GlobalTheory.splitPlace_proj_mem_integers_of_integral s ((Umax L n).inv_mem hk a b)

theorem mem_tSet_iff : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (sp : SplitPlace L) (ϖ : (sp.v).adicCompletion (maximalRealSubfield L)) (k : ℕ), ∀ x₀ ∈ Formalism.AUTREP.tSet L n sp ϖ k, ∀ κ, κ ∈ Formalism.AUTREP.tSet L n sp ϖ k ↔ ∃ k₁, (k₁ ∈ Umax L n ∧ TrivOutside {sp.v} k₁) ∧ ∃ k₂, (k₂ ∈ Umax L n ∧ TrivOutside {sp.v} k₂) ∧ κ = k₁ * x₀ * k₂ := by
  intro L _ _ _ n sp ϖ k x₀ hx₀ κ
  obtain ⟨hx₀t, a₀, ha₀, b₀, hb₀, hx₀e⟩ := hx₀
  constructor
  · rintro ⟨hκt, a, ha, b, hb, hκe⟩
    obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc L n sp
    have hg : a * a₀⁻¹ ∈ Formalism.UG.GLint (Fin n) (sp.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring :=
      mul_mem ha (inv_mem ha₀)
    have hg' : b₀⁻¹ * b ∈ Formalism.UG.GLint (Fin n) (sp.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring :=
      mul_mem (inv_mem hb₀) hb
    refine ⟨e (a * a₀⁻¹), ⟨GlobalTheory.SplitHeckeComm.mem_Umax_of_loc sp _ (he1 _) (by rw [he2]; exact hg), he1 _⟩,
      e (b₀⁻¹ * b), ⟨GlobalTheory.SplitHeckeComm.mem_Umax_of_loc sp _ (he1 _) (by rw [he2]; exact hg'), he1 _⟩, ?_⟩
    apply GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq L n sp
    · exact hκt
    · exact trivOutside_mul (trivOutside_mul (he1 _) hx₀t) (he1 _)
    · rw [map_mul, map_mul, he2, he2]
      apply Units.ext
      simp only [Units.val_mul]
      rw [hκe, hx₀e]
      simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv_cancel_left]
  · rintro ⟨k₁, ⟨hk₁, hk₁t⟩, k₂, ⟨hk₂, hk₂t⟩, rfl⟩
    refine ⟨trivOutside_mul (trivOutside_mul hk₁t hx₀t) hk₂t, sp.loc n k₁ * a₀,
      mul_mem (loc_mem_GLint sp hk₁) ha₀, b₀ * sp.loc n k₂, mul_mem hb₀ (loc_mem_GLint sp hk₂), ?_⟩
    rw [map_mul, map_mul]
    simp only [Units.val_mul]
    rw [hx₀e]
    simp only [Matrix.mul_assoc]

end GlobalTheory.TSetDoubleCoset
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHeckeSplitPlaceSetIffDoubleCosetStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_heckeSplitPlaceSet_iff_doubleCoset : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (sp : SplitPlace L) (ϖ : (sp.v).adicCompletion (maximalRealSubfield L)) (k : ℕ), ∀ x₀ ∈ Formalism.AUTREP.tSet L n sp ϖ k, ∀ κ, κ ∈ Formalism.AUTREP.tSet L n sp ϖ k ↔ ∃ k₁, (k₁ ∈ Umax L n ∧ TrivOutside {sp.v} k₁) ∧ ∃ k₂, (k₂ ∈ Umax L n ∧ TrivOutside {sp.v} k₂) ∧ κ = k₁ * x₀ * k₂ := by
  exact GlobalTheory.TSetDoubleCoset.mem_tSet_iff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentMulEqSelfOfSupported
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentMulEqSelfOfSupported
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.PlaceSupp

theorem tensCast_tmul_one {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (v : HeightOneSpectrum (𝓞 F1)) (α : FiniteAdeleRing (𝓞 F1) F1) (h1 : α v = 1) (h0 : ∀ v', v' ≠ v → α v' = 0) :
    ∃ (w : HeightOneSpectrum (𝓞 F2)) (α' : FiniteAdeleRing (𝓞 F2) F2),
      GlobalTheory.NJoin.tensCast h (α ⊗ₜ[F1] (1 : E)) = (1 : E) ⊗ₜ[F2] α' ∧ α' w = 1 ∧ ∀ v', v' ≠ w → α' v' = 0 := by
  subst h
  exact ⟨v, α, rfl, h1, h0⟩


open Classical in
theorem equivFinsuppOfBasisRight_rTensor {K M N N' ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N']
    (b : Module.Basis ι K M) (f : N →ₗ[K] N') (x : N ⊗[K] M) (i : ι) :
    TensorProduct.equivFinsuppOfBasisRight b (LinearMap.rTensor M f x) i =
      f (TensorProduct.equivFinsuppOfBasisRight b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem rTensor_eq_zero {K M N P Q ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
    (b : Module.Basis ι K M) (f : N →ₗ[K] P) (g : N →ₗ[K] Q) (hfg : ∀ n, f n = 0 → g n = 0 → n = 0)
    (x : N ⊗[K] M) (h1 : LinearMap.rTensor M f x = 0) (h2 : LinearMap.rTensor M g x = 0) : x = 0 := by
  classical
  let e := TensorProduct.equivFinsuppOfBasisRight (M := N) b
  have hc : ∀ i, e x i = 0 := by
    intro i
    apply hfg
    · have := equivFinsuppOfBasisRight_rTensor b f x i
      rw [h1, map_zero, Finsupp.zero_apply] at this
      exact this.symm
    · have := equivFinsuppOfBasisRight_rTensor b g x i
      rw [h2, map_zero, Finsupp.zero_apply] at this
      exact this.symm
  have : e x = 0 := Finsupp.ext hc
  simpa using congrArg e.symm this

theorem AE_eq_zero (D : D7) (x : Formalism.L2.Theta.AE D) (h1 : Formalism.L2.Theta.infPart D x = 0)
    (h2 : Formalism.L2.Theta.finPart D x = 0) : x = 0 := by
  classical
  let b := Module.finBasis D.host.F D.host.E
  refine rTensor_eq_zero b (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F).toLinearMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F).toLinearMap
    (fun n hf hs => Prod.ext hf hs) x ?_ ?_
  · rw [← h1]; clear h1 h2
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy]
  · rw [← h2]; clear h1 h2
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy]


set_option maxHeartbeats 2000000 in
theorem idem_mul_eq_self : ∀ (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E) (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), (∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) → ∀ a : Formalism.L2.Theta.AE D, Formalism.L2.Theta.infPart D a = 0 → (∀ v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), v' ≠ s.v → ReciprocityTheory.Aut.compAt D.host.E v' (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)) = 0) → (p.e + Formalism.L2.Theta.cA D p.e) * a = a := by
  intro D s hF p c hπ a ha0 haf
  obtain ⟨he2, hec, v, ε, ⟨α, rfl, hα1, hα0⟩, hsum⟩ := p.split
  rw [hsum]
  have hι1 : p.ι 1 = p.e := by
    have := p.ι_π 1
    rwa [map_one, mul_one] at this
  have hπe : p.π p.e = 1 := by rw [← hι1, p.π_ι]
  have hee : p.e * algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α) = p.e := by
    rw [← hsum, mul_add, he2, hec, add_zero]
  have hfin : Formalism.L2.Theta.finPart D (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α)) = α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  obtain ⟨w, α', hT, hw1, hw0⟩ := tensCast_tmul_one hF v α hα1 hα0
  have hws : w = s.v := by
    by_contra hne
    have h0 : α' s.v = 0 := hw0 s.v (Ne.symm hne)
    have hz : p.π (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α)) = 0 := by
      rw [hπ, hfin, hT]
      have : s.proj ((1 : D.host.E) ⊗ₜ α') = 0 := by
        rw [SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        exact h0
      rw [this, map_zero]
    have := congrArg p.π hee
    rw [map_mul, hz, mul_zero, hπe] at this
    exact zero_ne_one this
  subst hws
  set x := algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α) with hx
  suffices hb : x * a - a = 0 from sub_eq_zero.mp hb
  apply AE_eq_zero D
  · rw [RingHom.map_sub, RingHom.map_mul, ha0, mul_zero, sub_zero]
  · have key : GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D (x * a - a)) = 0 := by
      apply GlobalTheory.AL_eq_zero_of_compAt
      intro v''
      rw [(Formalism.L2.Theta.finPart D).map_sub, (Formalism.L2.Theta.finPart D).map_mul, (GlobalTheory.NJoin.tensCast hF).map_sub,
        (GlobalTheory.NJoin.tensCast hF).map_mul, (compAt D.host.E v'').map_sub, (compAt D.host.E v'').map_mul, hfin, hT]
      by_cases hv : v'' = s.v
      · subst hv
        have : compAt D.host.E s.v ((1 : D.host.E) ⊗ₜ α') = 1 := by
          rw [compAt, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
          change (1 : D.host.E) ⊗ₜ (α' s.v) = 1
          rw [hw1]
          rfl
        rw [this, one_mul, sub_self]
      · rw [haf v'' hv, mul_zero, sub_zero]
    exact (GlobalTheory.NJoin.tensCast hF).map_eq_zero_iff.mp key

end GlobalTheory.PlaceSupp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentMulEqSelfOfSupportedStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceIdempotent_mul_eq_self_of_supported : ∀ (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E) (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), (∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) → ∀ a : Formalism.L2.Theta.AE D, Formalism.L2.Theta.infPart D a = 0 → (∀ v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), v' ≠ s.v → ReciprocityTheory.Aut.compAt D.host.E v' (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)) = 0) → (p.e + Formalism.L2.Theta.cA D p.e) * a = a := by
  first | exact @GlobalTheory.PlaceSupp.idem_mul_eq_self | exact GlobalTheory.PlaceSupp.idem_mul_eq_self | (intros; apply GlobalTheory.PlaceSupp.idem_mul_eq_self <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitLocalPlaceDataAtSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitLocalPlaceDataAtSplitPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitLocPlace

open GlobalTheory.FinPl GlobalTheory.FinPl.SplitPoint GlobalTheory.IdemModTwo GlobalTheory.SplitChart GlobalTheory.LocMod.SplitCompl _root_.Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem conjPl_ne {D : D7} (s : SplitPlace D.host.E) : Formalism.DivisionValues.conjPl s.w ≠ s.w := by
  intro h
  have hm : ∀ x : 𝓞 D.host.E, x ∈ (Formalism.DivisionValues.conjPl s.w).asIdeal ↔
      IsCMField.ringOfIntegersComplexConj D.host.E x ∈ s.w.asIdeal := by
    intro x
    show x ∈ Ideal.map (Formalism.DivisionValues.cO D.host.E) s.w.asIdeal ↔ _
    have e0 : (Formalism.DivisionValues.cO D.host.E).symm x = IsCMField.ringOfIntegersComplexConj D.host.E x := RingOfIntegers.ext rfl
    rw [Ideal.mem_map_of_equiv]
    refine ⟨fun ⟨y, hy, hxy⟩ => ?_, fun hx => ⟨_, hx, ?_⟩⟩
    · rw [← e0, ← hxy, RingEquiv.symm_apply_apply]; exact hy
    · rw [← e0, RingEquiv.apply_symm_apply]
  have hw : (GlobalTheory.SplitConjPlace.conjSP s).w = s.w := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    rw [GlobalTheory.SplitConjPlace.mem_conj_w, ← hm, h]
  have hv : ∀ x : D.host.E, Valued.v ((s.i.comp (IsCMField.complexConj D.host.E).toAlgHom).toRingHom x) =
      s.w.valuation D.host.E x := by
    intro x
    have h1 := PI.CompAtExist.muV_eq (GlobalTheory.SplitConjPlace.conjSP s) x
    rw [hw] at h1
    exact h1
  obtain ⟨φ, hφc, hφ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.w s.v _ hv
  obtain ⟨c, hc, -, hci⟩ := GlobalTheory.SplitCompl.exists_ringEquiv D.host.E s
  have hg : ∀ y, φ (c y) = y := by
    intro y
    refine (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield D.host.E) s.v).induction_on
      (p := fun y => φ (c y) = y) y (isClosed_eq (hφc.comp hc) continuous_id) fun a => ?_
    have e1 := s.i.commutes a
    rw [← e1, hci, hφ]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_algHom]
    rw [AlgEquiv.commutes]
  apply IsCMField.complexConj_ne_one D.host.E
  refine AlgEquiv.ext fun x => s.i.toRingHom.injective ?_
  have h2 := hg (s.i x)
  rw [hci, hφ] at h2
  exact h2

theorem exists_transport {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (v1 : HeightOneSpectrum (𝓞 F1)) (w : HeightOneSpectrum (𝓞 F2))
    (hv : ∀ a : F1, v1.valuation F1 a = w.valuation F2 ⟨a, h.le a.2⟩) :
    ∃ κ : v1.adicCompletion F1 →+* w.adicCompletion F2, Continuous κ ∧
      (∀ a : F1, κ (algebraMap F1 _ a) = algebraMap F2 (w.adicCompletion F2) ⟨a, h.le a.2⟩) ∧
      ∀ z : FiniteAdeleRing (𝓞 F1) F1, ∃ z' : FiniteAdeleRing (𝓞 F2) F2,
        Formalism.IndefR.principalLevelFrame.tensCastR h (z ⊗ₜ[F1] (1 : E)) = (1 : E) ⊗ₜ[F2] z' ∧ κ (z v1) = z' w := by
  subst h
  have hvw : v1 = w := by
    refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F1), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F1),
      hv]
  subst hvw
  exact ⟨RingHom.id _, continuous_id, fun a => rfl, fun z => ⟨z, rfl, rfl⟩⟩

theorem tensCastR_one_tmul {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) (x : E) :
    Formalism.IndefR.principalLevelFrame.tensCastR h ((1 : FiniteAdeleRing (𝓞 F1) F1) ⊗ₜ[F1] x) = x ⊗ₜ[F2] (1 : FiniteAdeleRing (𝓞 F2) F2) := by
  subst h
  rfl


set_option maxHeartbeats 1000000 in
theorem exists_place : ∀ (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E),
    ∃ (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E))
      (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E),
      Formalism.L2.JoinChr.IsPlIdem D p.e s.w ∧ Continuous c ∧
      (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧
      ∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a))) := by
  intro D s hF
  obtain ⟨e, he⟩ := GlobalTheory.Hk3.SplitMatch.exists_isIdemAt (conjPl_ne s)
  obtain ⟨-, -, v, ε, hε, hs⟩ := he.1
  have hsa : SplitAt D v e := splitAt_of he.1 hε hs
  have hP := splitPrime_emb hsa s.w he
  have hf : ∀ x : D.host.E, Valued.v ((emb hsa).toRingHom x) = s.w.valuation D.host.E x := by
    intro x
    rw [← hP]
    exact GlobalTheory.AdelicU.valued_apply_eq_valuation (emb hsa) x
  obtain ⟨φ, hφc, hφ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.w v _ hf
  let g : D.host.F →+* s.w.adicCompletion D.host.E :=
    (algebraMap D.host.E (s.w.adicCompletion D.host.E)).comp (algebraMap D.host.F D.host.E)
  have hg : ∀ a, Valued.v (g a) = v.valuation D.host.F a := by
    intro a
    simp only [g, RingHom.comp_apply]
    rw [GlobalTheory.Idele.valued_algebraMap, ← hf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
      GlobalTheory.Idele.valued_algebraMap]
  obtain ⟨ψ, hψc, hψ, -⟩ := GlobalTheory.DenseCompl.exists_extension v s.w g hg
  have hcomp : ∀ y, φ (ψ y) = y := by
    intro y
    refine (HeightOneSpectrum.denseRange_algebraMap D.host.F v).induction_on
      (p := fun y => φ (ψ y) = y) y (isClosed_eq (hφc.comp hψc) continuous_id) fun a => ?_
    rw [hψ]
    simp only [g, RingHom.comp_apply]
    rw [hφ]
    exact (emb hsa).commutes a
  let e0 := RingEquiv.ofBijective φ ⟨φ.injective, fun y => ⟨ψ y, hcomp y⟩⟩
  have he0 : ∀ y, e0.symm y = ψ y := fun y => e0.injective (by rw [e0.apply_symm_apply]; exact (hcomp y).symm)
  have hΦc : Continuous e0.symm := hψc.congr fun y => (he0 y).symm
  have hΦc' : Continuous e0 := hφc
  have hΦ : ∀ x : D.host.E, e0.symm (emb hsa x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x := by
    intro x
    have h1 := e0.symm_apply_apply (algebraMap D.host.E (s.w.adicCompletion D.host.E) x)
    exact (congrArg e0.symm (hφ x)).symm.trans h1
  obtain ⟨c, hc, -, hci⟩ := GlobalTheory.SplitCompl.exists_ringEquiv D.host.E s
  have hvv : ∀ a : D.host.F, v.valuation D.host.F a =
      s.v.valuation (maximalRealSubfield D.host.E) ⟨a, hF.le a.2⟩ := by
    intro a
    have h1 := hf (algebraMap D.host.F D.host.E a)
    have h2 := PI.CompAtExist.muV_eq s (algebraMap (maximalRealSubfield D.host.E) D.host.E ⟨a, hF.le a.2⟩)
    rw [← GlobalTheory.Idele.valued_algebraMap, ← GlobalTheory.Idele.valued_algebraMap, ← (emb hsa).commutes, ← s.i.commutes]
    exact h1.trans h2.symm
  obtain ⟨κ, hκc, hκa, hκz⟩ := exists_transport hF v s.v hvv
  have hΦκ : ∀ y, e0.symm y = c (κ y) := by
    intro y
    refine (HeightOneSpectrum.denseRange_algebraMap D.host.F v).induction_on
      (p := fun y => e0.symm y = c (κ y)) y (isClosed_eq hΦc (hc.comp hκc)) fun a => ?_
    have h1 : algebraMap D.host.F (v.adicCompletion D.host.F) a = emb hsa (algebraMap D.host.F D.host.E a) :=
      ((emb hsa).commutes a).symm
    have h2 : algebraMap (maximalRealSubfield D.host.E) (s.v.adicCompletion (maximalRealSubfield D.host.E))
        ⟨a, hF.le a.2⟩ = s.i (algebraMap (maximalRealSubfield D.host.E) D.host.E ⟨a, hF.le a.2⟩) :=
      (s.i.commutes _).symm
    rw [hκa]
    rw [h2]
    rw [hci]
    rw [h1]
    rw [hΦ]
  let p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E) :=
    { e := e
      split := he.1
      π := e0.symm.toRingHom.comp (comp hsa)
      ι := (sec D v e).comp e0.toRingHom.toAddMonoidHom
      π_ι := fun x => by
        show e0.symm (comp hsa (sec D v e (e0 x))) = x
        rw [comp_sec, RingEquiv.symm_apply_apply]
      ι_π := fun a => by
        show sec D v e (e0 (e0.symm (comp hsa a))) = e * a
        rw [RingEquiv.apply_symm_apply, sec_comp]
      cont_π := hΦc.comp (continuous_comp hsa)
      cont_ι := continuous_sec.comp hΦc' }
  refine ⟨p, c, ⟨he.1.1, ⟨v, ε, hε, Or.inl ⟨he.1.2.1, hs⟩⟩, he.2⟩, hc, hci, fun a => ?_⟩
  show e0.symm (comp hsa a) = _
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul y x =>
    have hyx : y ⊗ₜ[D.host.F] x = algebraMap (AF D.host.F) (AE D) y * incA D x := by
      show _ = (y ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hyx, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
    congr 1
    · rw [comp_algebraMap, hΦκ]
      obtain ⟨z', hz1, hz2⟩ := hκz y.2
      have e1 : Formalism.L2.Theta.finPart D (algebraMap (AF D.host.F) (AE D) y) = y.2 ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
      rw [e1]
      show _ = c (s.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF (y.2 ⊗ₜ[D.host.F] (1 : D.host.E))))
      rw [hz1]
      show c (κ (y.2 v)) = c (s.i 1 * z' s.v)
      rw [map_one, one_mul, hz2]
    · show e0.symm (emb hsa x) = _
      rw [hΦ]
      have e1 : Formalism.L2.Theta.finPart D (incA D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := rfl
      rw [e1]
      show _ = c (s.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF ((1 : Af D.host.F) ⊗ₜ[D.host.F] x)))
      rw [tensCastR_one_tmul]
      show _ = c (s.i x * ReciprocityTheory.Aut.evalAt D.host.E s.v 1)
      rw [map_one, mul_one, hci]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end GlobalTheory.SplitLocPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitLocalPlaceDataAtSplitPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitLocalPlaceData_at_splitPlace : ∀ (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E), ∃ (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), Formalism.L2.JoinChr.IsPlIdem D p.e s.w ∧ Continuous c ∧ (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧ ∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a))) := by
  first | exact @GlobalTheory.SplitLocPlace.exists_place | exact GlobalTheory.SplitLocPlace.exists_place | (intros; apply GlobalTheory.SplitLocPlace.exists_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceIsSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TieFrob

theorem xi_eq_of_heq {D : D7} {nch : NChoice D} {C C' : CharFrame D} (h : C = C') (Tp : TupTied D C nch)
    (Tp' : TupTied D C' nch) (e : HEq Tp Tp') : Tp.xi = Tp'.xi := by
  subst h; cases e; rfl

end GlobalTheory.TieFrob
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatakeParameterSphericalInertPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatakeParameterSphericalInertPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SatInertEx

theorem exists_satAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ Dv : InertDatum L n v w, π.SphAt v → ∃ α, NG.SatAt π Dv α := by
  intro L _ _ _ n π v w hw Dv hsph
  exact GlobalTheory.T.exists_satakeParameter_at_inertPlace_of_spherical L n π v w hw hsph Dv

end GlobalTheory.SatInertEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatakeParameterSphericalInertPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satakeParameter_spherical_inertPlace : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ Dv : InertDatum L n v w, π.SphAt v → ∃ α, NG.SatAt π Dv α := by
  first | exact @GlobalTheory.SatInertEx.exists_satAt | exact GlobalTheory.SatInertEx.exists_satAt | (intros; apply GlobalTheory.SatInertEx.exists_satAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceNotBadBelow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GoodOffBad

theorem conj_eq_complexConj (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

theorem isConjPl_conjPlE_left {D : D7} (P : PlE D.host) : IsConjPl D.host (GlobalTheory.SplitConjPlace.conjPlE P) P := by
  intro x y hxy
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
  have : IsCMField.ringOfIntegersComplexConj D.host.E x = y := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, hxy, conj_eq_complexConj]
  rw [this]

theorem conjPlE_mem_placesOver {D : D7} (P : PlE D.host) (p : ℕ) :
    GlobalTheory.SplitConjPlace.conjPlE P ∈ placesOver D.host.E p ↔ P ∈ placesOver D.host.E p := by
  show ((p : ℕ) : 𝓞 D.host.E) ∈ (GlobalTheory.SplitConjPlace.conjPlE P).asIdeal ↔ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE, map_natCast]

end GlobalTheory.GoodOffBad
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalCoordsConjUnitaryStandardForm
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalCoordsConjUnitaryStandardForm
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory

theorem unitary_conj_orthonormal : ∀ (D : D7) {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (crd γ : GL (Fin n) D.host.E), cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (crd : Matrix (Fin n) (Fin n) D.host.E) * (crd : Matrix (Fin n) (Fin n) D.host.E) = J → γ ∈ UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) J → cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) ((crd * γ * crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * ((crd * γ * crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  intro D n J crd γ hc hγ
  set σ : D.host.E →+* D.host.E := (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) with hσ
  have hg : cT σ (γ : Matrix (Fin n) (Fin n) D.host.E) * J * (γ : Matrix (Fin n) (Fin n) D.host.E) = J := hγ
  have h1 : (crd : Matrix (Fin n) (Fin n) D.host.E) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul]
  rw [cT_mul, cT_mul]
  calc cT σ ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * (cT σ (γ : Matrix (Fin n) (Fin n) D.host.E) * cT σ (crd : Matrix (Fin n) (Fin n) D.host.E)) *
        ((crd : Matrix (Fin n) (Fin n) D.host.E) * (γ : Matrix (Fin n) (Fin n) D.host.E) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E))
      = cT σ ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * (cT σ (γ : Matrix (Fin n) (Fin n) D.host.E) * (cT σ (crd : Matrix (Fin n) (Fin n) D.host.E) * (crd : Matrix (Fin n) (Fin n) D.host.E)) * (γ : Matrix (Fin n) (Fin n) D.host.E)) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) := by
        simp only [Matrix.mul_assoc]
    _ = cT σ ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * (cT σ (crd : Matrix (Fin n) (Fin n) D.host.E) * (crd : Matrix (Fin n) (Fin n) D.host.E)) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) := by
        rw [hc, hg, ← hc]
    _ = cT σ ((crd : Matrix (Fin n) (Fin n) D.host.E) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) * ((crd : Matrix (Fin n) (Fin n) D.host.E) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, cT_one, Matrix.one_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalCoordsConjUnitaryStandardFormStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalCoords_conj_unitary_standard_form : ∀ (D : D7) {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (crd γ : GL (Fin n) D.host.E), cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (crd : Matrix (Fin n) (Fin n) D.host.E) * (crd : Matrix (Fin n) (Fin n) D.host.E) = J → γ ∈ UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) J → cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) ((crd * γ * crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * ((crd * γ * crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  first | exact @GlobalTheory.unitary_conj_orthonormal | exact GlobalTheory.unitary_conj_orthonormal | (intros; apply GlobalTheory.unitary_conj_orthonormal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelFrameLiftUnitaryAutNearAdelicMatrixDepthOne
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelFrameLiftUnitaryAutNearAdelicMatrixDepthOne
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameRat

theorem nearAt_liftFr_smul : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) (w : SG) (g : UF X.E n), ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2 → ∀ (y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), NearAt (seamP s w.1) 1 y (seamGL s (d.1.liftFr w)) → NearAt (seamP s w.1) 1 (ratA D.host.F (seamGL s g.1) * y) (seamGL s (((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).1.liftFr w)) := by
  intro D X s n ST SG d w g hq y hy
  have hf := GlobalTheory.TopStep.liftFr_spec d.2 w
  have hf' : GlobalTheory.TopStep.IsLiftFr (d.1.act g.1 1) w (((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).1.liftFr w) := by
    have := GlobalTheory.TopStep.liftFr_spec ((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).2 w
    rwa [DecoSet.smul_val] at this
  set κ := GlobalTheory.TopStep.passFr g.1 1 hf hf' with hκ
  have hred : GlobalTheory.TopStep.redGL n w.1 κ = 1 := GlobalTheory.TopStep.redGL_passFr g.1 1 hf hf'
  have hred' : GlobalTheory.TopStep.redGL n w.1 κ⁻¹ = 1 := by rw [map_inv, hred, inv_one]
  have he : ((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).1.liftFr w = g.1 * d.1.liftFr w * (κ⁻¹).1 := by
    rw [InvMemClass.coe_inv, hκ]
    show _ = g.1 * d.1.liftFr w * ((((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).1.liftFr w)⁻¹ * g.1 * d.1.liftFr w)⁻¹
    group
  rw [he, map_mul, map_mul, mul_assoc, nearAt_rat_mul]
  exact GlobalTheory.CplPt.nearAt_mul 1 hy (GlobalTheory.CplPt.congAt_one_of_redGL s hq κ⁻¹ hred')

end GlobalTheory.FrameRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelFrameLiftUnitaryAutNearAdelicMatrixDepthOneStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFrameLift_unitaryAut_near_adelicMatrix_depth_one : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) (w : SG) (g : UF X.E n), ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2 → ∀ (y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), NearAt (seamP s w.1) 1 y (seamGL s (d.1.liftFr w)) → NearAt (seamP s w.1) 1 (ratA D.host.F (seamGL s g.1) * y) (seamGL s (((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).1.liftFr w)) := by
  first | exact @GlobalTheory.FrameRat.nearAt_liftFr_smul | exact GlobalTheory.FrameRat.nearAt_liftFr_smul | (intros; apply GlobalTheory.FrameRat.nearAt_liftFr_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalLatticeAut
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalLatticeAut
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory.TwU


set_option maxHeartbeats 1000000 in
theorem funMoved_ratA_act : ∀ {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : Formalism.L2.Forms.StepLevel D.host.F D.host.E (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D i hi) T D.R.f bad) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal) (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal) (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (d : Deco X.E (D.R.N i) ST SG) (g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) (hh : GLG (E := X.E) (n := D.R.N i) (SG := SG)), FunMoved s lev P v h ι x d → FunMoved s lev P v h ι (ratA D.host.F (seamGL s g) * x) (d.act g hh) := by
  intro D X s i hi T bad lev ST SG P v h ι x d g hh H w hw z hz
  have hw' : g.symm w ∈ d.N := (Formalism.L2.Col.mem_gmap g d.N w).1 hw
  have key : pullV (F := D.host.F) (ratA D.host.F (seamGL s g) * x) (fun a => s.iE (w a)) =
      pullV (F := D.host.F) x (fun a => s.iE (g.symm w a)) := by
    unfold pullV
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
    congr 1
    have e1 : (seamGL s g)⁻¹ = seamGL s g.symm := (map_inv (seamGL s) g).symm
    rw [← map_inv, e1]
    have := Formalism.MainNotions.G.KAat.bc_mulVec (F := D.host.F) (seamGL s g.symm) (fun a => s.iE (w a))
    rw [seamGL_mulVec] at this
    exact this
  show d.f P (g.symm w) = _
  exact H (g.symm w) hw' z (by rw [hz, key])

end GlobalTheory.TwU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalLatticeAutStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimeFunctionals_move_rational_lattice_aut : ∀ {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : Formalism.L2.Forms.StepLevel D.host.F D.host.E (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D i hi) T D.R.f bad) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal) (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal) (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (d : Deco X.E (D.R.N i) ST SG) (g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) (hh : GLG (E := X.E) (n := D.R.N i) (SG := SG)), FunMoved s lev P v h ι x d → FunMoved s lev P v h ι (ratA D.host.F (seamGL s g) * x) (d.act g hh) := by
  first | exact @GlobalTheory.TwU.funMoved_ratA_act | exact GlobalTheory.TwU.funMoved_ratA_act | (intros; apply GlobalTheory.TwU.funMoved_ratA_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartsRebasedOneOffLevelPrimeKilled
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartsRebasedOneOffLevelPrimeKilled
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.TwU.AtTrue.charts_funKilled_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K0 : Fam I l Z u a i hi bad chOf), I.ReadsK l Z u a i hi chOf K0 → (∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K0 β).lev.chi κ ^ n = 1) → ∃ Kc : Fam I l Z u a i hi bad chOf, ReadsOne I l Z u a i hi chOf Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K0 hK hfin
  obtain ⟨K', hK', hprop⟩ := TC.charts_funKilled I hI hP l Z u a i hi bad Ch chOf K0 hK
  obtain ⟨k, hk⟩ := GlobalTheory.T.chartsReadingStep_moveBasePoints_one_offLevelPrime I hI hP l Z u a i hi bad Ch chOf K' hK'
  refine ⟨fun β => moveChart (K' β) (k β), hk, fun β => ⟨(hprop β).1, ?_⟩⟩
  obtain ⟨hF, -, -, hU, hchi, -, -⟩ := hprop β
  obtain ⟨n, hn, hn'⟩ := hfin β
  refine ⟨n, hn, fun κ => ?_⟩
  have hm : (k β).1 * κ.1 * (k β).1⁻¹ ∈ (K0 β).lev.U := hU ▸ κ.2
  show ((K' β).lev.chi ⟨(k β).1 * κ.1 * (k β).1⁻¹, κ.2⟩) ^ n = 1
  have e := hchi ⟨(k β).1 * κ.1 * (k β).1⁻¹, κ.2⟩ ⟨_, hm⟩ rfl
  exact e.symm ▸ hn' _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartsRebasedOneOffLevelPrimeKilledStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charts_rebased_one_off_levelPrime_killed : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K0 : Fam I l Z u a i hi bad chOf), I.ReadsK l Z u a i hi chOf K0 → (∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K0 β).lev.chi κ ^ n = 1) → ∃ Kc : Fam I l Z u a i hi bad chOf, ReadsOne I l Z u a i hi chOf Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
  first | exact @GlobalTheory.TwU.AtTrue.charts_funKilled_one | exact GlobalTheory.TwU.AtTrue.charts_funKilled_one | (intros; apply GlobalTheory.TwU.AtTrue.charts_funKilled_one <;> assumption)
end
end
