module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemUJsetOfKset
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.CoreOfWeak

theorem core_of_weak : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → Core R.toRealDat F.lv2 ∧ IsSF R.toRealDat R.SF ∧ (∀ c, R.EEc c = EEc R.toRealDat R.SF c) ∧ ∀ i c, R.Wc' i c = Wcc R.toRealDat R.SF i c := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h e
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak h e
  refine ⟨⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩, ?_, fun c => rfl, fun i c => rfl⟩
  intro v
  rw [h.inert.SF v, h.allPl]

end GlobalTheory.CoreOfWeak
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.core_clauses_of_weak_characterisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → Core R.toRealDat F.lv2 ∧ IsSF R.toRealDat R.SF ∧ (∀ c, R.EEc c = EEc R.toRealDat R.SF c) ∧ ∀ i c, R.Wc' i c = Wcc R.toRealDat R.SF i c := by
  first | exact @GlobalTheory.CoreOfWeak.core_of_weak | exact GlobalTheory.CoreOfWeak.core_of_weak | (intros; apply GlobalTheory.CoreOfWeak.core_of_weak <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.GalLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Datum

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  (σ : D.what₂.LL →+* ℂ)

abbrev Comparison₂ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W)
    (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) : Prop :=
  Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
    (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L

abbrev ptAt (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f : WO (Vc D i) (Wc D i) → ℂ) :
    PolF D (Wc D i).rank (Vc D i).rank → (WO (Vc D i) (Wc D i) → ℂ) :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) B f

structure VecData (f₀ f : WO (Vc D i) (Wc D i) → ℂ)
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) : Prop where
  vec : IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      R.Pg ∅ (fun _ => 1) f₀ f
  onb : ∀ ρ, IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (B ρ) (pW D i ρ)
  theta : ∀ P, IsThetaFunO R.ψ (Vc D i) (Wc D i) (ptAt R i σ B f P)

def LiftData (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (H : HMod (Bridge.Gf (Vc D i) → c.W))
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ)
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))) : Prop :=
  IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω ∧ VecData R i σ f₀ f B ∧
    IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ B f) (deltaConj i σ) io ∧
    Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h φ => thetaKO ω h g φ) (ptAt R i σ B f) io
      (LinearMap.range (c.ext ∘ₗ H.e)) thP

def IsProjOf {c : CoefA (Vc D i)} {H : HMod (Bridge.Gf (Vc D i) → c.W)}
    (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ)))
    (th : H.H →ₗ[ℂ] (R.HW i σ).H) : Prop :=
  ∀ (x : H.H) (v : ∀ ρ, lowT (R.MW i σ) ρ),
    (R.HW i σ).e (th x) (fun ρ => v ρ) = R.eWf i σ (thP ((c.ext ∘ₗ H.e).rangeRestrict x) (PiTensorProduct.tprod ℂ v))

theorem isConjLift_iff (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (H : HMod (Bridge.Gf (Vc D i) → c.W))
    (th : H.H →ₗ[ℂ] (R.HW i σ).H) :
    IsConjLift R i σ μ' η' c H th ↔ ∃ ω f₀ f B io thP, LiftData R i σ μ' η' c H ω f₀ f B io thP ∧ IsProjOf R i σ thP th := by
  constructor
  · rintro ⟨ω, f₀, f, B, io, thP, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨ω, f₀, f, B, io, thP, ⟨h1, ⟨h2, h3, h4⟩, h5, h6⟩, h7⟩
  · rintro ⟨ω, f₀, f, B, io, thP, h, h7⟩
    exact ⟨ω, f₀, f, B, io, thP, h.1, h.2.1.vec, h.2.1.onb, h.2.1.theta, h.2.2.1, h.2.2.2, h7⟩

structure CoefAt (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) : Prop where
  coef : c.Is
  act : ∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE →
    ∀ v, c₁ (rhoVr (labLL D) (lamV D i) γE v) = c.ρ (γ : GA D (Vc D i)) (c₁ v)
  indep : LinearIndependent ℂ fun a => c₁ (bVV D.what₂.LL (lamV D i) a)
  span : Submodule.span ℂ (Set.range fun a => c₁ (bVV D.what₂.LL (lamV D i) a)) = ⊤
  pair : ∀ a b, inner ℂ (c₁ (bVV D.what₂.LL (lamV D i) a)) (c₁ (bVV D.what₂.LL (lamV D i) b)) =
    σ (pairVr (labLL D) (lamV D i) (gramV D i) (bVV D.what₂.LL (lamV D i) a) (bVV D.what₂.LL (lamV D i) b))

def PhaseFun (u : GA D (Wc D i) → ℂ) : Prop :=
  (∀ h, ‖u h‖ = 1) ∧ (∀ γ ∈ GQ (Wc D i), ∀ h, u (γ * h) = u h) ∧ (∀ g ∈ GinfC (Wc D i), ∀ h, u (h * g) = u h) ∧
    ∀ k ∈ levW R i, ∀ h, u (h * k) = u h

abbrev IsLiftW (g : G) (k : GA D (Wc D i)) : Prop := Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k

def EtaVals : Prop :=
  ∀ (P : Pl D.host.E) (e : AE D), Formalism.L2.JoinChr.IsPlIdem D e P → ∀ x : (AE D)ˣ,
    (x : AE D) = Formalism.L2.JoinChr.locE D e (Formalism.L2.Host.unif P : D.host.Eˣ) →
      ∃ y : D.what₂.LL, D.what₂.embLL y = ((R.eta x : Circle) : ℂ) * (((Real.sqrt (Nat.card (kP P) : ℝ))⁻¹ : ℝ) : ℂ)

end Datum

section Geo

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  (O : OMDat T.toCore R i Unit (fun _ => A.μ0))

def RepsAt (v₀ : (R.MW i (sg0 D A)).Vec) (h : O.Cl' () → GA D (Vc D i)) : Prop :=
  ∃ J' : Subgroup (Bridge.Gf (Vc D i)), RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ()) ∧
    PlaceEx R i A.μ0 h O.c0' ∧ ThAdIs R i A.μ0 h O.c0' v₀ (O.thAd ()) ∧
      ∀ x, O.Plc () x ↔ ∃ x₀, Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x

abbrev actG (g : G) : T.R ((i : ℕ) + 1) →ₗ[T.Q.c.F] T.R ((i : ℕ) + 1) := actLev T.Q.c O.lev2 g

variable (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))

def IsClassSum (h : O.Cl' () → GA D (Vc D i)) (x₀ : A.fam.amb.FL i A.μ0) {n : ℕ} (a : Fin n → D.what₂.LL)
    (f : Fin n → Cu T κ i) : Prop :=
  ∃ (x : O.Cl' () → VsV D i O.c'.F) (f' : Rul (T.Q.Xo ((i : ℕ) + 1)) O.c'),
    Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x ∧ f' ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA (κ i)) (Vc D i).rank ∧
    IsThClsD (T.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ ()) (O.w ()) (O.La ()) (O.Nc ()) (O.gam ()) (O.vol ()) (O.ep ()) O.io x f' ∧
    IsBC O.hle f' (fun k => O.jL (a k)) (fun k => (f k : T.R ((i : ℕ) + 1)))

def EquivBy (σ : D.what₂.LL →+* ℂ) (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (u : GA D (Wc D i) → ℂ) : Prop :=
  ∀ g k, IsLiftW R i g k → ∀ (f : Cu T κ i) (h : GA D (Wc D i)),
    u h * phiC T hV (wtA (κ i)) (actG O g (f : T.R ((i : ℕ) + 1))) h =
      σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) * (u (h * k) * phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) (h * k))

end Geo

end GlobalTheory.GalLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodingerHerm

theorem sesq_apply (D : D7) {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (x y : Fin k → D.host.E) :
    GlobalTheory.WeilSchrodinger.sesq D G x y = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [GlobalTheory.WeilSchrodinger.sesq, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply,
    smul_eq_mul, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem sesq_transpose_eq_form (D : D7) {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) (x y : Fin k → D.host.E) :
    GlobalTheory.WeilSchrodinger.sesq D Jᵀ y x = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig J x y := by
  rw [sesq_apply, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rfl

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) :
    M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let P : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Pᵀ * M * P.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg,
    Matrix.det_one, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0, mul_zero, zero_mul] at hd
  rw [Fintype.card_fin, one_mul, mul_one] at hd
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) hd.symm

variable (D : D7) (B : Base D.host.F D.host.E) {n : ℕ} (X : Spc D.host.F D.host.E n) {r s : ℕ}

theorem det_J_ne_zero (hX : X.IsHerm D.sp.cm.sig B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  intro h0
  apply h
  have hm : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det := (RingHom.map_det _ _).symm
  rw [hm, h0, map_zero]

theorem mem_one_iff (z : D.host.E) : z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨o, rfl⟩
    exact o.isIntegral_coe
  · intro h
    exact ⟨⟨z, h⟩, rfl⟩

theorem herm_nondeg_unimod (hX : X.IsHerm D.sp.cm.sig B r s) :
    (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).IsSymm ∧ (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).Nondegenerate ∧
      Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ) X.L := by
  have hdet : X.Jᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact det_J_ne_zero D B X hX
  refine ⟨⟨fun x y => ?_⟩, ⟨fun x hx => ?_, fun y hy => ?_⟩, ?_⟩
  ·
    have hs : ∀ i j, star (X.J i j) = X.J j i := fun i j => hX.herm j i
    simp only [sesq_apply, starRingEnd_apply, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star,
      Pi.star_apply, Matrix.transpose_apply, hs, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  ·
    have h1 : star x ᵥ* X.Jᵀ = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [← Matrix.dotProduct_mulVec, ← sesq_apply]
      exact hx v
    have h2 : star x = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
    simpa using congrArg star h2
  ·
    have h1 : X.Jᵀ *ᵥ y = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [dotProduct_comm]
      have := hy (star v)
      rwa [sesq_apply, star_star] at this
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet h1
  ·
    show Formalism.E.hdual _ X.L = X.L
    ext x
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
    rw [hX.dual x]
    refine forall₂_congr fun y _ => ?_
    rw [sesq_transpose_eq_form, mem_one_iff]

end GlobalTheory.WeilSchrodingerHerm

end

theorem GlobalTheory.WeilSchrodingerHerm.main : ∀ (D : D7) (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (n : ℕ) (X : Spc D.host.F D.host.E n) (r s : ℕ), X.IsHerm D.sp.cm.sig B r s →
      (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).IsSymm ∧ (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).Nondegenerate ∧
        Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ) X.L :=
  fun D B _ _ X _ _ hX => GlobalTheory.WeilSchrodingerHerm.herm_nondeg_unimod D B X hX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondegStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular : ∀ (D : D7) (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (n : ℕ) (X : Spc D.host.F D.host.E n) (r s : ℕ), X.IsHerm D.sp.cm.sig B r s →
      (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).IsSymm ∧ (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).Nondegenerate ∧
        Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ) X.L := by
  first | exact @GlobalTheory.WeilSchrodingerHerm.main | exact GlobalTheory.WeilSchrodingerHerm.main | (intros; apply GlobalTheory.WeilSchrodingerHerm.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.RealLift

open GlobalTheory.PointAtPlaceHom

variable {D : D7}

def prodAt (θ : InfFam D) (V : HSp D) (l : List D.what₂.Tau) (u : D.what₂.Tau → Mt V.rank) : GA D V :=
  (l.map fun τ => atTau θ V τ (u τ)).prod

theorem prodAt_mem (θ : InfFam D) (V : HSp D) (l : List D.what₂.Tau) (u : D.what₂.Tau → Mt V.rank) :
    prodAt θ V l u ∈ GinfC V := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
  exact atTau_mem V τ _

theorem infMat_prodAt {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) {u : D.what₂.Tau → Mt V.rank}
    (hu : u ∈ UG (gramAt D V)) (ρ : D.what₂.Tau) (l : List D.what₂.Tau) (hl : l.Nodup) :
    infMat D.sp.cm.sig V.gram (θ ρ) (prodAt θ V l u) = if ρ ∈ l then u ρ else 1 := by
  induction l with
  | nil => rw [if_neg List.not_mem_nil]; exact infMat_one V _
  | cons τ l ih =>
    have e : prodAt θ V (τ :: l) u = atTau θ V τ (u τ) * prodAt θ V l u := List.prod_cons
    have hs := atTau_spec hθ V τ (hu τ)
    rw [List.nodup_cons] at hl
    rw [e, infMat_mul, ih hl.2]
    by_cases c : ρ = τ
    · subst c
      rw [hs.2.1, if_neg hl.1, if_pos List.mem_cons_self, Matrix.mul_one]
    · rw [hs.2.2 ρ c, Matrix.one_mul]
      simp only [List.mem_cons, c, false_or]

theorem continuousOn_prodAt {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (l : List D.what₂.Tau) :
    ContinuousOn (prodAt θ V l) (UG (gramAt D V)) := by
  induction l with
  | nil => exact continuousOn_const
  | cons τ l ih =>
    have e : prodAt θ V (τ :: l) = fun u => atTau θ V τ (u τ) * prodAt θ V l u := funext fun _ => List.prod_cons
    have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
    have c : ContinuousOn (fun u : D.what₂.Tau → Mt V.rank => atTau θ V τ (u τ)) (UG (gramAt D V)) :=
      (continuousOn_atTau hθ V τ).comp (continuous_apply τ).continuousOn fun u hu => hu τ
    rw [e]
    exact c.mul ih

theorem archM_mem {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) :
    archM V (θ τ) g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  obtain ⟨θ₀, h₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  have e : θ = fun ρ => θ₀ (tauE D ρ) := (GlobalTheory.SmoothForms.RealPts.realPoints D).1 _ _ hθ fun ρ => h₀ _
  subst e
  exact (GlobalTheory.Member.Arch.unit_iff _ _ _).1 (((GlobalTheory.Member.Arch.archM_spec D V θ₀ h₀).1 _).2.2.2.2 g)

theorem exists_real_lift : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∃ L : (D.what₂.Tau → Mt V.rank) → GA D V, (∀ u ∈ UG (gramAt D V), L u ∈ GinfC V ∧ ∀ τ, archM V (θ τ) (L u) = u τ) ∧ (∀ u ∈ UG (gramAt D V), ∀ u' ∈ UG (gramAt D V), L (u * u') = L u * L u') ∧ ContinuousOn L (UG (gramAt D V)) ∧ (∀ g, (fun τ => archM V (θ τ) g) ∈ UG (gramAt D V)) ∧ (∀ u ∈ GinfC V, L (fun τ => archM V (θ τ) u) = u) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), atTau θ V τ g = L (Pi.mulSingle τ g)) ∧ (∀ g, ∃ a ∈ GfC V, ∃ u ∈ GinfC V, g = a * u) ∧ (∀ a ∈ GfC V, ∀ u ∈ GinfC V, a * u = u * a) ∧ ∀ τ, (gramAt D V τ).IsHermitian ∧ (gramAt D V τ).det ≠ 0 := by
  intro D θ V hθ
  obtain ⟨r1, -, r3, r4, -, r6, r7, -⟩ := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  let L : (D.what₂.Tau → Mt V.rank) → GA D V := prodAt θ V Finset.univ.toList
  have hm : ∀ u, L u ∈ GinfC V := prodAt_mem θ V _
  have hL : ∀ u ∈ UG (gramAt D V), ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) (L u) = u τ := fun u hu τ => by
    rw [infMat_prodAt hθ V hu τ _ (Finset.nodup_toList _), if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
  refine ⟨L, fun u hu => ⟨hm u, hL u hu⟩, fun u hu u' hu' => ?_, continuousOn_prodAt hθ V _,
    fun g τ => archM_mem hθ V g τ, fun u hu => ?_, fun τ g hg => ?_, r7, fun a ha u hu => (r6 u hu a ha).symm,
    fun τ => ⟨(r1 τ).1, (r1 τ).2.ne_zero⟩⟩
  · refine r3 _ (hm _) _ (mul_mem (hm _) (hm _)) fun τ => ?_
    rw [r4, hL u hu, hL u' hu', hL (u * u') fun ρ => mul_mem_UH (hu ρ) (hu' ρ)]
    rfl
  · exact r3 _ (hm _) _ hu fun τ => hL _ (fun ρ => archM_mem hθ V u ρ) τ
  · have hs := atTau_spec hθ V τ hg
    have hu : (Pi.mulSingle τ g : D.what₂.Tau → Mt V.rank) ∈ UG (gramAt D V) := fun ρ => by
      by_cases c : ρ = τ
      · subst c
        rwa [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne c]
        exact one_mem_UH _
    refine r3 _ hs.1 _ (hm _) fun ρ => ?_
    rw [hL _ hu]
    by_cases c : ρ = τ
    · subst c
      rw [Pi.mulSingle_eq_same, hs.2.1]
    · rw [Pi.mulSingle_eq_of_ne c, hs.2.2 ρ c]

end GlobalTheory.RealLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProductStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedean_lift_unitaryGroupProduct : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∃ L : (D.what₂.Tau → Mt V.rank) → GA D V, (∀ u ∈ UG (gramAt D V), L u ∈ GinfC V ∧ ∀ τ, archM V (θ τ) (L u) = u τ) ∧ (∀ u ∈ UG (gramAt D V), ∀ u' ∈ UG (gramAt D V), L (u * u') = L u * L u') ∧ ContinuousOn L (UG (gramAt D V)) ∧ (∀ g, (fun τ => archM V (θ τ) g) ∈ UG (gramAt D V)) ∧ (∀ u ∈ GinfC V, L (fun τ => archM V (θ τ) u) = u) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), atTau θ V τ g = L (Pi.mulSingle τ g)) ∧ (∀ g, ∃ a ∈ GfC V, ∃ u ∈ GinfC V, g = a * u) ∧ (∀ a ∈ GfC V, ∀ u ∈ GinfC V, a * u = u * a) ∧ ∀ τ, (gramAt D V τ).IsHermitian ∧ (gramAt D V τ).det ≠ 0 := by
  first | exact @GlobalTheory.RealLift.exists_real_lift | exact GlobalTheory.RealLift.exists_real_lift | (intros; apply GlobalTheory.RealLift.exists_real_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqLowKOfLeLowKSub
open Matrix Finset Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.LowHW

theorem height_root {n : ℕ} (a b : Fin n) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * Formalism.REAL.root a b i = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [Formalism.REAL.root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem height_sum {n : ℕ} (c : Fin n → Fin n → ℕ) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) i
      = ∑ a, ∑ b, (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
  simp only [← height_root, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring

theorem cdom_antisymm {n : ℕ} {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h1 : CDom ε μ Λ) (h2 : CDom ε Λ μ) :
    μ = Λ := by
  obtain ⟨c, hc, e1⟩ := h1
  obtain ⟨d, hd, e2⟩ := h2
  have key : ∀ (c : Fin n → Fin n → ℕ), (∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) → ∀ a b : Fin n,
      (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ -(c a b : ℝ) := by
    intro c hc a b
    by_cases h : c a b = 0
    · simp [h]
    · have h3 : (a : ℕ) + 1 ≤ b := (hc a b h).1
      have h4 : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast h3
      have h5 : (0 : ℝ) ≤ c a b := Nat.cast_nonneg _
      nlinarith
  have hs1 := height_sum c
  have hs2 := height_sum d
  rw [← e1] at hs1
  rw [← e2] at hs2
  have hz : ∑ i : Fin n, ((i : ℕ) : ℝ) * (Λ - μ) i + ∑ i : Fin n, ((i : ℕ) : ℝ) * (μ - Λ) i = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by simp only [Pi.sub_apply]; ring
  have l1 : ∑ a, ∑ b, (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ ∑ a, ∑ b, -(c a b : ℝ) :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => key c hc a b
  have l2 : ∑ a, ∑ b, (d a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 :=
    Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ =>
      (key d hd a b).trans (neg_nonpos.2 (Nat.cast_nonneg _))
  simp only [Finset.sum_neg_distrib] at l1
  have l3 : ∑ a, ∑ b, (c a b : ℝ) ≤ 0 := by linarith
  have hc0 : ∀ a b, (c a b : ℝ) = 0 := by
    intro a b
    refine le_antisymm (le_trans ?_ l3) (Nat.cast_nonneg _)
    calc (c a b : ℝ) ≤ ∑ b, (c a b : ℝ) :=
          Finset.single_le_sum (f := fun b => (c a b : ℝ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ b)
      _ ≤ _ := Finset.single_le_sum (f := fun a => ∑ b, (c a b : ℝ))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ a)
  simp only [hc0, zero_smul, Finset.sum_const_zero] at e1
  exact (sub_eq_zero.1 e1).symm

end GlobalTheory.LowHW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.ModelRep

section Conj

variable {n : ℕ} {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ}

theorem conj_mem (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) : P * g * P⁻¹ ∈ UJset ε := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have hg' : gᴴ * G * g = G := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        rw [hG, hg', ← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1]; simp

theorem conj_mem_inv (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : P⁻¹ * g * P ∈ Formalism.QuantumDeterminants.UH G := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  show (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P) = G
  calc (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P)
      = Pᴴ * (gᴴ * ((P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹)) * g) * P := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by
        rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hg', hG]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isURepOn_conj (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ) :
    IsURepOn (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  obtain ⟨⟨ha, hb⟩, hc, hd⟩ := hσ
  refine ⟨⟨?_, ?_⟩, fun g hg v => hc _ (conj_mem hP hG hg) v, fun v => ?_⟩
  · simpa only [Matrix.mul_one, h1] using ha
  · intro a ha' b hb'
    have e : P * (a * b) * P⁻¹ = (P * a * P⁻¹) * (P * b * P⁻¹) := by
      calc P * (a * b) * P⁻¹ = P * a * (P⁻¹ * P) * b * P⁻¹ := by rw [h2]; simp only [Matrix.mul_assoc, Matrix.one_mul]
        _ = _ := by simp only [Matrix.mul_assoc]
    show σ (P * (a * b) * P⁻¹) = _
    rw [e]
    exact hb _ (conj_mem hP hG ha') _ (conj_mem hP hG hb')
  · have hc : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact (hd v).comp hc.continuousOn fun g hg => conj_mem hP hG hg

theorem isIrredOn_conj (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsIrredOn (UJset ε) σ) :
    IsIrredOn (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  intro S hS h
  refine hσ S hS fun g hg v hv => ?_
  have := h _ (conj_mem_inv hP hG hg) v hv
  have e : P * (P⁻¹ * g * P) * P⁻¹ = g := by
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [h1]; simp
  simpa only [e] using this

theorem arr_injective {q : ℕ} (hq : q ≤ n) : Function.Injective (arr q : Fin n → Fin n) := by
  intro a b h
  have h' := congrArg Fin.val h
  have := a.2
  have := b.2
  apply Fin.ext
  unfold arr at h'
  split_ifs at h' <;> simp only at h' <;> omega

def arrEquiv {q : ℕ} (hq : q ≤ n) : Fin n ≃ Fin n :=
  Equiv.ofBijective (arr q) (Finite.injective_iff_bijective.1 (arr_injective hq))

theorem orth_sub (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (f : Fin n → Fin n) :
    ((P⁻¹).submatrix id f)ᴴ * G * (P⁻¹).submatrix id f = (Formalism.REAL.Jm ε).submatrix f f := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h3 : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    calc (P⁻¹)ᴴ * G * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  rw [← h3]
  rfl

theorem conj_single (hP : IsUnit P) (e : Fin n ≃ Fin n) (a c : Fin n) :
    (P⁻¹).submatrix id e * Matrix.single a c 1 * ((P⁻¹).submatrix id e)⁻¹ =
      P⁻¹ * Matrix.single (e a) (e c) 1 * P := by
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h3 : ((P⁻¹).submatrix id e)⁻¹ = P.submatrix e id := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.submatrix_mul_equiv, h2]
    rfl
  have h4 : (Matrix.single a c 1 : Matrix (Fin n) (Fin n) ℂ) = (Matrix.single (e a) (e c) 1).submatrix e e := by
    ext i j
    simp [Matrix.single_apply]
  rw [h3, h4, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rfl

end Conj

theorem model_rep : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), CompleteSpace (M.H τ) ∧ IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) ∧ IsIrredOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) ∧ (HolShape M → OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) ∧ ∀ a c, x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹ = (M.fr τ)⁻¹ * Matrix.single (arr (nNeg (M.ε τ)) a) (arr (nNeg (M.ε τ)) c) 1 * M.fr τ) := by
  intro D V S M τ
  obtain ⟨h1, -, h3, h4, -⟩ := M.ds τ
  refine ⟨h1, isURepOn_conj (M.fr_unit τ) (M.fr_gram τ) h3, isIrredOn_conj (M.fr_unit τ) (M.fr_gram τ) h4, fun hs => ⟨⟨nNeg_le _, ?_⟩, fun a c => ?_⟩⟩
  · obtain ⟨-, p, hp, h⟩ := hs τ
    have := orth_sub (M.fr_unit τ) (M.fr_gram τ) (arr (nNeg (M.ε τ)))
    refine this.trans ?_
    have hinj := arr_injective (nNeg_le (M.ε τ))
    unfold Formalism.REAL.Jm
    rw [Matrix.submatrix_diagonal _ _ hinj]
    congr 1
    funext a
    have := a.2
    simp only [Function.comp, h, nNeg_shape hp h, ReciprocityTheory.ChartRestriction.G.FD.sgn, arr, decide_eq_true_eq]
    split_ifs <;> first | (simp; done) | (exfalso; simp only at *; omega)
  · exact conj_single (M.fr_unit τ) (arrEquiv (nNeg_le (M.ε τ))) a c

end GlobalTheory.HolDict.ModelRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormalStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), CompleteSpace (M.H τ) ∧ IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) ∧ IsIrredOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) ∧ (HolShape M → OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) ∧ ∀ a c, x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹ = (M.fr τ)⁻¹ * Matrix.single (arr (nNeg (M.ε τ)) a) (arr (nNeg (M.ε τ)) c) 1 * M.fr τ) := by
  first | exact @GlobalTheory.HolDict.ModelRep.model_rep | exact GlobalTheory.HolDict.ModelRep.model_rep | (intros; apply GlobalTheory.HolDict.ModelRep.model_rep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess wd wdb bas)
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.FinChart
open scoped ContDiff ENNReal

namespace GlobalTheory

namespace FinChart

variable {D : ℕ}

theorem cHess_eq_hessC {f : V D → ℝ} {z : Fin D → ℂ} (hf : ContDiffAt ℝ 2 f (toV D z)) :
    cHess D (fun v => (f v : ℂ)) (toV D z) = hessC (f ∘ toV D) z := by
  set x := toV D z with hx
  set H := fderiv ℝ (fderiv ℝ f) x with hH
  have hD : HasFDerivAt (fderiv ℝ f) H x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have h₁ : fderiv ℝ (f ∘ toV D) =
      fun w => (fderiv ℝ f (toV D w)).comp (toV D).toContinuousLinearMap :=
    funext fun _ => (toV D).comp_right_fderiv
  have h₂ (u w : Fin D → ℂ) : fderiv ℝ (fderiv ℝ (f ∘ toV D)) z u w = H (toV D u) (toV D w) := by
    have := ((hD.comp z (toV D).hasFDerivAt).clm_comp
      (hasFDerivAt_const (toV D).toContinuousLinearMap z)).fderiv
    rw [h₁]
    erw [this]
    simp
  have hdiff := ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf
  set G : Fin D → V D → ℂ := fun l y => (2 : ℂ)⁻¹ *
    ((fderiv ℝ f y (bas D l) : ℂ) + Complex.I * (fderiv ℝ f y (Complex.I • bas D l) : ℂ))
  have hwdb (l) : wdb D l (fun y => (f y : ℂ)) =ᶠ[𝓝 x] G l := by
    filter_upwards [hdiff] with y hy
    simp only [wdb, G, ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply hy]
    ring
  have hGd (l e) : fderiv ℝ (G l) x e =
      ((H e (bas D l) : ℂ) + Complex.I * (H e (Complex.I • bas D l) : ℂ)) / 2 := by
    have ha (b : V D) : HasFDerivAt (fun y => ((fderiv ℝ f y b : ℝ) : ℂ))
        (Complex.ofRealCLM.comp ((fderiv ℝ f x).comp (0 : V D →L[ℝ] V D) + H.flip b)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x (hD.clm_apply (hasFDerivAt_const b x))
    have hG : HasFDerivAt (G l) _ x :=
      ((ha (bas D l)).add ((ha (Complex.I • bas D l)).const_mul Complex.I)).const_mul (2 : ℂ)⁻¹
    rw [hG.fderiv]
    simp
    ring
  ext j l
  have b₁ (a : Fin D) : toV D (Pi.single a 1) = bas D a := rfl
  have b₂ (a : Fin D) : toV D (Complex.I • Pi.single a 1) = Complex.I • bas D a := rfl
  simp only [cHess, Matrix.of_apply, wd, (hwdb l).fderiv_eq, hGd, hessC, h₂, b₁, b₂]
  push_cast
  linear_combination (-(H (Complex.I • bas D j) (Complex.I • bas D l) : ℂ) / 4) * Complex.I_mul_I

theorem measurePreserving_toV : MeasurePreserving (toV D) :=
  MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin D → ℂ)).symm
    (volume_preserving_ofLp_complex (Fin D))

end FinChart

section Abstract

variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem integrableOn_source_iff_of_density (c : OpenPartialHomeomorph X (Fin e → ℂ))
    {μ : Measure X} {w : (Fin e → ℂ) → ℝ} (hw : ContinuousOn w c.target)
    (hw0 : ∀ y ∈ c.target, 0 ≤ w y) (hμ : ∀ S, MeasurableSet S → S ⊆ c.source →
      μ S = ∫⁻ y in c.target ∩ c.symm ⁻¹' S, ENNReal.ofReal (w y))
    {g : X → ℝ} (hg : Measurable g) :
    (IntegrableOn g c.source μ ↔ IntegrableOn (fun y => g (c.symm y) * w y) c.target) ∧
      ∫ x in c.source, g x ∂μ = ∫ y in c.target, g (c.symm y) * w y := by
  have hT := c.open_target.measurableSet
  have key : μ.restrict c.source =
      ((volume.restrict c.target).withDensity fun y => ENNReal.ofReal (w y)).map c.symm := by
    ext S hS
    rw [Measure.restrict_apply hS, hμ _ (hS.inter c.open_source.measurableSet) inter_subset_right,
      Measure.map_apply_of_aemeasurable ((c.continuousOn_symm.aemeasurable hT).mono_ac
        (withDensity_absolutelyContinuous _ _)) hS, withDensity_apply',
      Measure.restrict_restrict' hT]
    congr 2
    ext y
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, c.map_target h.2⟩⟩
  rw [IntegrableOn, key]
  exact map_withDensity_integrable_integral c.open_target c.continuousOn_symm hw hw0 hg

theorem integrable_of_pieces (A : FinHolAtlas e X) (P : ChartPartition A) {μ : Measure X}
    {w : Fin A.n → (Fin e → ℂ) → ℝ} (hw : ∀ j, ContinuousOn (w j) (A.chart j).target)
    (hw0 : ∀ j, ∀ y ∈ (A.chart j).target, 0 ≤ w j y)
    (hμ : ∀ j S, MeasurableSet S → S ⊆ (A.chart j).source →
      μ S = ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' S, ENNReal.ofReal (w j y))
    {g : X → ℝ} (hg : Measurable g) (hi : ∀ j, IntegrableOn
      (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * w j y) (A.chart j).target) :
    Integrable g μ ∧ ∫ x, g x ∂μ = ∑ j, ∫ y in (A.chart j).target,
      P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * w j y := by
  have hc (j) : Continuous (P.χ j) := continuous_iff_continuousAt.2 fun x => by
    obtain ⟨l, hl⟩ := A.cover x
    have h₁ := ((P.smooth j l).continuousOn.mono fun y hy => ⟨hy, mem_univ _⟩).continuousAt
      ((A.chart l).open_target.mem_nhds ((A.chart l).map_source hl))
    refine (h₁.comp ((A.chart l).continuousAt hl)).congr ?_
    exact eventually_of_mem ((A.chart l).open_source.mem_nhds hl) fun z hz =>
      congrArg (P.χ j) ((A.chart l).left_inv hz)
  have key (j) := integrableOn_source_iff_of_density (A.chart j) (hw j) (hw0 j) (hμ j)
    ((hc j).measurable.mul hg)
  have h0 (j) (x) (hx : x ∉ (A.chart j).source) : P.χ j x * g x = 0 := by
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (P.tsupport_subset j h), zero_mul]
  have h₁ (j) : Integrable (fun x => P.χ j x * g x) μ :=
    ((key j).1.2 (hi j)).integrable_of_forall_notMem_eq_zero (h0 j)
  have e : g = fun x => ∑ j, P.χ j x * g x := funext fun x => by
    rw [← Finset.sum_mul, P.sum_eq_one, one_mul]
  refine ⟨e ▸ integrable_finsetSum _ fun j _ => h₁ j, ?_⟩
  conv_lhs => rw [e]
  rw [integral_finsetSum _ fun j _ => h₁ j]
  exact Finset.sum_congr rfl fun j _ =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero (h0 j)).symm.trans (key j).2

end Abstract

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB Y}
  {φ : Weight p σ B}

namespace Weight

theorem IsCInf.maDens_eq (h : φ.IsCInf) (c : AlgChart p σ D) {z : Fin D → ℂ}
    (hz : z ∈ c.finChart.target) :
    maDens (fun _ y => φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) z =
      c.chernDens φ (c.finChart.symm z) := by
  have hr : c.e (c.finChart.symm z) = toV D z := c.e.right_inv hz
  have hd := h.contDiffAt c (c.finChart.map_target hz) (mem_pick φ.isLB (c.finChart.symm z))
  rw [hr] at hd
  have e : (fun y => φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) = fun y => 2⁻¹ *
      ((fun v => φ.φ (pick φ.isLB (c.finChart.symm z)) (c.e.symm v)) ∘ toV D) y :=
    funext fun _ => div_eq_inv_mul _ _
  rw [maDens, ReciprocityTheory.AnForm.A.mdisc_const, e, hessC_const_mul', AlgChart.chernDens, AlgChart.hess,
    hr, cHess_eq_hessC hd, Matrix.det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Fintype.card_fin, ← mul_assoc, mul_assoc (D.factorial : ℝ), ← mul_pow, div_eq_mul_inv _ (_ ^ D),
    ← inv_pow]
  congr 3
  ring

variable {A : FinHolAtlas D (CxPts p σ)}

theorem IsCInf.locDens_eq (h : φ.IsCInf) (hA : IsAlgAtlas A) (j : Fin A.n) {z : Fin D → ℂ}
    (hz : z ∈ (A.chart j).target) : locDens A (fun _ => φ.locPot) j z =
      (hA.anRead.chart j).chernDens φ ((A.chart j).symm z) := by
  unfold locDens
  rw [hA.chart_eq j] at hz ⊢
  exact h.maDens_eq _ hz

theorem IsCInf.chernPart_eq [SecondCountableTopology (CxPts p σ)] (h : φ.IsCInf)
    (hA : IsAlgAtlas A) (ε : ℤˣ) (j : Fin A.n) (S : Set (CxPts p σ)) (hS : MeasurableSet S)
    (hs : S ⊆ (A.chart j).source) : φ.chernPart D ε S =
      ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' S,
        ENNReal.ofReal (max ((ε : ℤ) * locDens A (fun _ => φ.locPot) j y) 0) := by
  have hl (y) := h.locDens_eq hA j (z := y)
  generalize locDens A (fun _ => φ.locPot) j = d at hl ⊢
  rw [hA.chart_eq j] at hs hl ⊢
  set c := hA.anRead.chart j
  have hm := measurableSet_image c.e hS hs
  rw [chernPart_apply h ε c hS hs, ← measurePreserving_toV.setLIntegral_comp_preimage_emb
    (toV D).toHomeomorph.measurableEmbedding]
  have e : c.e '' S = c.e.target ∩ c.e.symm ⁻¹' S := by
    rw [← c.e.image_source_inter_eq', inter_eq_right.2 (show S ⊆ c.e.source from hs)]
  rw [e] at hm ⊢
  refine setLIntegral_congr_fun (hm.preimage (toV D).continuous.measurable) fun y hy => ?_
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, zero_le, max_eq_left, hl y hy.1]
  rfl

variable [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)]

theorem IsCInf.chernInt_eq_mInt_of_isAlgAtlas (h : φ.IsCInf) (hA : IsAlgAtlas A)
    {g : CxPts p σ → ℝ} (hg : Measurable g) :
    (φ.ChernIntegrableOn D univ g ↔ MIntegrable A (fun _ => φ.locPot) g) ∧
      (φ.ChernIntegrableOn D univ g → φ.chernInt D univ g = mInt A (fun _ => φ.locPot) g) := by
  have hne : Nonempty (ChartPartition A) := existsPartition A
  set P := hne.some
  set d := locDens A fun _ => φ.locPot with hd
  have hdc (j) : ContinuousOn (d j) (A.chart j).target := locDensCont A _
    (fun _ => ((isCInf_iff_isSmooth hA.anRead).1 h).isPotential hA) j
  let w (ε : ℤˣ) (j) (y) : ℝ := max ((ε : ℤ) * d j y) 0
  have hw (ε j) : ContinuousOn (w ε j) (A.chart j).target :=
    (continuous_id.max continuous_const).comp_continuousOn (continuousOn_const.mul (hdc j))
  have hw0 (ε j) : ∀ y ∈ (A.chart j).target, 0 ≤ w ε j y := fun _ _ => le_max_right _ _
  have hsub (j y) : w 1 j y - w (-1) j y = d j y := by
    simpa [w] using max_zero_sub_max_neg_zero_eq_self (d j y)
  have habs (ε j y) : |w ε j y| ≤ |d j y| := by
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ((le_abs_self _).trans_eq ?_) (abs_nonneg _)
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  have back (hm : MIntegrable A (fun _ => φ.locPot) g) (ε j) : IntegrableOn
      (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * w ε j y)
      (A.chart j).target := by
    obtain ⟨hKc, hKs⟩ := image_closed_compact (A.chart j) (isClosed_tsupport (P.χ j))
      (P.tsupport_subset j)
    refine integrableOn_target_of_closed (A.chart j) (Z := tsupport (P.χ j))
      (fun y _ hy => by simp [image_eq_zero_of_notMem_tsupport hy]) ?_
    have hcc := (chi_comp_continuousOn P j).mono hKs
    refine Integrable.mono ((hm j _ hKs hKc).continuousOn_mul hcc hKc) ?_ (.of_forall fun y => ?_)
    · exact (((hcc.aemeasurable hKc.measurableSet).mul (hg.comp_aemeasurable
        (((A.chart j).continuousOn_symm.mono hKs).aemeasurable hKc.measurableSet))).mul
        (((hw ε j).mono hKs).aemeasurable hKc.measurableSet)).aestronglyMeasurable
    · simp only [Real.norm_eq_abs, abs_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (habs ε j y) (by positivity)
  have pieces (hm : MIntegrable A (fun _ => φ.locPot) g) (ε) :=
    integrable_of_pieces A P (hw ε) (hw0 ε) (h.chernPart_eq hA ε) hg (back hm ε)
  have fwd (hi : φ.ChernIntegrableOn D univ g) : MIntegrable A (fun _ => φ.locPot) g :=
    fun j K hK _ => by
    have key (ε) := (integrableOn_source_iff_of_density (A.chart j) (hw ε j) (hw0 ε j)
      (h.chernPart_eq hA ε j) hg).1.1
    refine IntegrableOn.mono_set ?_ hK
    refine (Integrable.sub (key 1 (hi.1.mono_set (subset_univ _)))
      (key (-1) (hi.2.mono_set (subset_univ _)))).congr (.of_forall fun y => ?_)
    simp only [Pi.sub_apply, ← mul_sub, hsub, hd]
  refine ⟨⟨fwd, fun hm => ⟨(pieces hm 1).1.integrableOn, (pieces hm (-1)).1.integrableOn⟩⟩,
    fun hi => ?_⟩
  have hm := fwd hi
  rw [chernInt, Measure.restrict_univ, Measure.restrict_univ, (pieces hm 1).2, (pieces hm (-1)).2,
    mInt, dif_pos hne, integralWith, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_sub (back hm 1 j) (back hm (-1) j)]
  simp only [← mul_sub, hsub, hd, P]

theorem chernInt_eq_mInt (R : AnRead p σ D) (h : φ.IsCInf) {g : CxPts p σ → ℝ}
    (hg : Measurable g) :
    (φ.ChernIntegrableOn D univ g ↔ MIntegrable R.finAtlas (fun _ => φ.locPot) g) ∧
      (φ.ChernIntegrableOn D univ g →
        φ.chernInt D univ g = mInt R.finAtlas (fun _ => φ.locPot) g) :=
  h.chernInt_eq_mInt_of_isAlgAtlas R.isAlgAtlas_finAtlas hg

end Weight

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

variable {p : ℕ} [Fact p.Prime]

def IntC (G : HTGroup p) (w : AwayP p) (a : w.1.adicCompletion ℚ ⊗[ℚ] G.C) : Prop :=
  ∀ i, coordL G w a i ∈ w.1.adicCompletionIntegers ℚ

end GlobalTheory.FinClsLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PbEqOfPins
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PinsFixHalf

theorem pb_eq_of_pins : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → LawsJ T → (∀ i, OMPins T R κ v₀ O i) → T.pb = R.C.P.pb := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hR hT hO
  exact GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R hT.toLawsM hR
    ((hO ⟨0, lt_of_lt_of_le (by norm_num) D.R.two_le_m⟩).2.tuple ()).half

end GlobalTheory.PinsFixHalf
end
