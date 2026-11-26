module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.NormalizedHeckeData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.Per

export GlobalTheory.MemLoc (Core)

variable {l : ℕ} [Fact l.Prime]

def IsStd (P : LocPrime l) (AI : LocAinf l P) : Prop := Nonempty (LocTied l P AI)

theorem IsStd.of_tied {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) : IsStd P AI := ⟨T⟩

end GlobalTheory.Per

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem locAinf_actC {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (x : ℂ_[l]) :
    AI.actC g x = Per.σC g x := by
  have hc : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq hc (GlobalTheory.RingIface.sigC_cont l g)
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

theorem locAinf_actT {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (x : OCb l) :
    AI.actT g x = Per.σF g x := by
  refine Perfection.ext fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  obtain ⟨y₁, h₁, e₁⟩ := AI.actT_coeff g x n y hy.symm
  obtain ⟨y₂, h₂, e₂⟩ := coeff_galois_tilt l g x n y hy.symm
  have : y₁ = y₂ := Subtype.ext (by rw [h₁, h₂, locAinf_actC])
  exact e₁.trans (this ▸ e₂.symm)

theorem locAinf_actW {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (a : Ainf l) :
    AI.actW g a = Per.σA g a :=
  WittVector.ext fun n => (locAinf_actT AI g (a.coeff n)).trans (GlobalTheory.RingIface.sigA_coeff l g a n).symm

variable (l)

theorem isUnit_l_BdRp : IsUnit ((l : ℕ) : Per.BdRp l) := by
  have h := (GlobalTheory.RingBasics.isUnit_l l).map (algebraMap (Per.AinfP l) (Per.BdRp l))
  rwa [map_natCast] at h

theorem isUnit_l_Bcris : IsUnit ((l : ℕ) : Per.Bcris l) := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hne : e ≠ 1 := by
    rintro rfl
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    simp [rootT]
  obtain ⟨w, hw, -⟩ := exists_mu_pow_div l e he
  have hw' : ((l : ℕ) : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) ^ (l - 1) :=
    Subtype.ext (by simpa using hw)
  have hm : IsUnit (((algebraMap (Per.Acris l) (Per.Bcris l)).comp (algebraMap (Per.Acris0 l) (Per.Acris l)))
      (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e))) := by
    rw [RingHom.comp_apply, ← GlobalTheory.RingIface.tower]
    exact GlobalTheory.CrisLoc.unit_of_root l e he hne
  have h2 := congrArg
    ((algebraMap (Per.Acris l) (Per.Bcris l)).comp (algebraMap (Per.Acris0 l) (Per.Acris l))) hw'
  rw [map_mul, map_natCast, map_pow] at h2
  exact isUnit_of_mul_isUnit_left (h2 ▸ hm.pow (l - 1))

def BcrisP : Type := Localization.Away ((l : ℕ) : Per.Acris l)

instance : CommRing (BcrisP l) := inferInstanceAs (CommRing (Localization.Away ((l : ℕ) : Per.Acris l)))

instance : Algebra (Per.Acris l) (BcrisP l) :=
  inferInstanceAs (Algebra (Per.Acris l) (Localization.Away ((l : ℕ) : Per.Acris l)))

instance : IsLocalization.Away ((l : ℕ) : Per.Acris l) (BcrisP l) :=
  inferInstanceAs (IsLocalization.Away _ (Localization.Away ((l : ℕ) : Per.Acris l)))


variable {l} in
def plusLift {S : Type} [CommRing S] (f : Per.Acris l →+* S) (h : IsUnit ((l : ℕ) : S)) : BcrisP l →+* S :=
  IsLocalization.Away.lift ((l : ℕ) : Per.Acris l) (g := f) (by rwa [map_natCast])


variable {l} in
theorem plusLift_alg {S : Type} [CommRing S] (f : Per.Acris l →+* S) (h : IsUnit ((l : ℕ) : S))
    (x : Per.Acris l) : plusLift f h (algebraMap _ _ x) = f x :=
  IsLocalization.Away.lift_eq _ _ x

def plusToB : BcrisP l →+* Per.Bcris l :=
  plusLift (algebraMap (Per.Acris l) (Per.Bcris l)) (isUnit_l_Bcris l)

variable {l}

theorem plusToB_alg (x : Per.Acris l) :
    plusToB l (algebraMap _ _ x) = algebraMap (Per.Acris l) (Per.Bcris l) x := plusLift_alg _ _ x

theorem plus_ext {S : Type} [CommRing S] {f f' : BcrisP l →+* S}
    (h : ∀ x : Per.Acris l, f (algebraMap _ _ x) = f' (algebraMap _ _ x)) : f = f' :=
  IsLocalization.ringHom_ext (Submonoid.powers ((l : ℕ) : Per.Acris l)) (RingHom.ext h)

namespace Core

variable (C : Core l)

def jP : BcrisP l →+* Per.BdRp l := plusLift C.j (isUnit_l_BdRp l)

theorem jP_alg (x : Per.Acris l) : C.jP (algebraMap _ _ x) = C.j x := plusLift_alg _ _ x

theorem ι_plusToB (x : BcrisP l) :
    C.ι (plusToB l x) = algebraMap (Per.BdRp l) (Per.BdR l) (C.jP x) :=
  RingHom.congr_fun (plus_ext (f := C.ι.comp (plusToB l))
    (f' := (algebraMap (Per.BdRp l) (Per.BdR l)).comp C.jP) fun y => by
      rw [RingHom.comp_apply, RingHom.comp_apply, plusToB_alg, jP_alg, C.ι_j]) x

def oD : Om l →+* Per.BdR l := (algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o

def qB : ℚ_[l] →+* Per.Bcris l := C.u.comp (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))

def tB : Per.Bcris l := algebraMap (Per.Acris l) (Per.Bcris l) C.t

theorem ker_theta : RingHom.ker (Per.θ l) = Ideal.span {xi C.ε} := by
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact theta_eq_zero_iff_xi_dvd l C.ε (core_isEps l C) a

end Core


variable (l) in
theorem acris_torsionFree_complete : (∀ x : Per.Acris l, ((l : ℕ) : Per.Acris l) * x = 0 → x = 0) ∧
    IsAdicComplete (Ideal.span {((l : ℕ) : Per.Acris l)}) (Per.Acris l) :=
  ⟨(acris_basic l).2.1, (acris_basic l).1⟩


variable (l) in
theorem thetaD_onto_ker : Function.Surjective (Per.θD l) ∧ RingHom.ker (Per.θD l) = Per.FilP l 1 :=
  ⟨(thetaD_props l).1, Ideal.ext fun y => (thetaD_props l).2.1 y⟩

namespace Core

variable (C : Core l)

def DVR : Prop :=
  ∃ _ : IsDomain (Per.BdRp l), ∃ _ : IsDiscreteValuationRing (Per.BdRp l),
    IsLocalRing.maximalIdeal (Per.BdRp l) = Ideal.span {C.j C.t} ∧
    IsLocalRing.maximalIdeal (Per.BdRp l) = RingHom.ker (Per.θD l) ∧
    IsAdicComplete (IsLocalRing.maximalIdeal (Per.BdRp l)) (Per.BdRp l) ∧
    (∀ n : ℕ, Per.FilP l n = Ideal.span {C.j C.t ^ n}) ∧
    IsFractionRing (Per.BdRp l) (Per.BdR l)

def AwayT : Prop := IsLocalization.Away C.t (Per.Bcris l)

def PlusAwayT : Prop :=
  letI := (plusToB l).toAlgebra
  IsLocalization.Away (algebraMap (Per.Acris l) (BcrisP l) C.t) (Per.Bcris l)

def PlusInj : Prop := Function.Injective C.jP

def InvdR : Prop := ∀ (K : FinExt l) (b : Per.BdR l), (∀ g ∈ GK K, Per.σD g b = b) → ∃ x ∈ K.1, C.oD x = b

def InvB : Prop := ∀ (K : FinExt l) (b : Per.Bcris l), (∀ g ∈ GK K, Per.σB g b = b) →
  ∃ x : ↥(MaximalUnramifiedExtension l), (x : Om l) ∈ K.1 ∧ C.u x = b

def PhiInj (_C : Core l) : Prop := Function.Injective (Per.φB l)

def IotaInj : Prop := Function.Injective C.ι

def TensorInj : Prop := ∀ (m : ℕ) (x : Fin m → Om l), LinearIndependent ↥(MaximalUnramifiedExtension l) x →
  ∀ b : Fin m → Per.Bcris l, ∑ i, C.oD (x i) * C.ι (b i) = 0 → ∀ i, b i = 0

def Fund : Prop := ∀ b : Per.Bcris l, Per.φB l b = b → C.ι b ∈ Per.FilD l 0 → ∃ x : ℚ_[l], C.qB x = b

def FundOnto : Prop := ∀ w : Per.BdR l, ∃ b : Per.Bcris l, Per.φB l b = b ∧ C.ι b - w ∈ Per.FilD l 0

def OneSubPhiOnto (_C : Core l) : Prop := ∀ y : Per.Bcris l, ∃ x : Per.Bcris l, x - Per.φB l x = y

def Regular : Prop := ∀ (K : FinExt l) (b : Per.Bcris l), b ≠ 0 →
  (∀ g ∈ GK K, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) → IsUnit b

end Core

structure Fits {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (C : Core l) : Prop where

  ζ : C.ζ = P.ζQ

  ε : C.ε = AI.ε

  o : ∀ x : Om l, T.eD (algebraMap (Om l) P.R.BdR x) = C.oD x

  ι : ∀ b : P.R.B, T.eD (P.ιB b) = C.ι (T.eB b)

  u : ∀ c : ↥(MaximalUnramifiedExtension l), T.eB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = C.u c

  t : T.eB P.tB = C.tB

  χ : ∀ g : GQ l, ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = (((C.χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])

  σ : ∀ (K : FinExt l) (x : ↥(K0 K)) (c : ↥(MaximalUnramifiedExtension l)), (c : Om l) = (x : Om l) →
    (((P.PD K).σ x : ↥(K0 K)) : Om l) = ((C.σ c : ↥(MaximalUnramifiedExtension l)) : Om l)

end GlobalTheory.MemLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
noncomputable section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

def IsTheta {P : LocPrime l} (AI : LocAinf l P) (θ : Ainf l →+* OC l) : Prop :=
  (∀ (x : OCb l) (y : OC l),
    PreTilt.coeff 0 x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y →
      θ (WittVector.teichmuller l x) - y ∈ Ideal.span {((l : ℕ) : OC l)}) ∧
  Function.Surjective θ ∧
  (∀ (g : GQ l) (a : Ainf l), ((θ (AI.actW g a) : OC l) : PadicComplex l) =
    AI.actC g ((θ a : OC l) : PadicComplex l)) ∧
  (∀ a : Ainf l, θ a = 0 ↔ AI.ξ ∣ a) ∧
  ∀ j : ℕ, θ (WittVector.teichmuller l (AI.εroot j)) = AI.ζ j

def zC (x : ℤ_[l]) : PadicComplex l := algebraMap ℚ_[l] (PadicComplex l) (x : ℚ_[l])

def IsMat (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) {d : ℕ}
    (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) : Prop :=
  letI := zlMod LL T
  ∃ b : Module.Basis (Fin d) ℤ_[l] ↥T.L.T,
    (∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = zC (b.repr (actTZ LL T g (b j)) i)) ∧
    ∀ (a : ↥(OL LL)) (i j : Fin d), A a i j = zC (b.repr (⟨_, T.L.T.smul_mem a (b j).2⟩ : ↥T.L.T) i)

def IsDec (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l)
    (m : ℕ) {d : ℕ} (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (D : Matrix (Fin d) (Fin d) (PadicComplex l))
    (U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) : Prop :=
  IsUnit D.det ∧ (∀ a b, ‖D a b‖ ≤ 1) ∧ (∀ a b, ‖(l : PadicComplex l) * D⁻¹ a b‖ ≤ 1) ∧
    Frame χ K m U g ∧ ∀ σ ∈ Gj K m, D * U σ = M σ * D.map (act σ)

def ExpStar (LT : LocTheory) (G : Subgroup (GQ l)) (e : ℕ) (z : GQ l → ℚ_[l]) (α : Om l) : Prop :=
  CocOn G (fun σ y => (((LT l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z ∧
  ∃ b ∈ ((LT l).PD (botExt l)).Fil 0, ∀ σ ∈ G,
    algebraMap ℚ_[l] (LT l).R.BdR (z σ) -
      algebraMap ℚ_[l] (LT l).R.BdR ((logChi LT σ : ℤ_[l]) : ℚ_[l]) *
        (algebraMap (Om l) (LT l).R.BdR α * (LT l).ιB (LT l).tB ^ e) -
      (algebraMap ℚ_[l] (LT l).R.BdR (((LT l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) *
        (LT l).actQdR σ b - b) ∈ ((LT l).PD (botExt l)).Fil ((e : ℤ) + 1)

def betaE (l s e : ℕ) : ℤ :=
  if e = 0 then -1 else (s : ℤ) - 1 - e - padicValNat l (e - 1).factorial

def repQ {P : LocPrime l} (AI : LocAinf l P) (G : Subgroup (GQ l)) {T : Type} [AddCommGroup T]
    [Module ℤ_[l] T] (ρ : ↥G →* (T →ₗ[ℤ_[l]] T)) (a b : ℤ) :
    Representation ℤ_[l] ↥G (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b)) :=
  repX (act := AI.actWCbHom.comp G.subtype) ρ
    ⟨fun g x hx => (xiOK AI).1 (g : GQ l) x hx, (xiOK AI).2.1, fun g => (xiOK AI).2.2 (g : GQ l)⟩ a b

end GlobalTheory.Cyc
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
noncomputable section

namespace GlobalTheory.GLq

open Polynomial Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

abbrev Gn (g n : ℕ) : Type := GL (Fin n) (ZMod g)

abbrev Mt (g n : ℕ) : Type := Matrix (Fin n) (Fin n) (ZMod g)

def IsClass {G : Type} [Group G] (χ : G → ℂ) : Prop := ∀ x y : G, χ (y * x * y⁻¹) = χ x

def IsChar {G : Type} [Group G] (χ : G → ℂ) : Prop := ∃ V : FDRep ℂ G, ∀ x, V.character x = χ x

def IsIrr {G : Type} [Group G] (χ : G → ℂ) : Prop :=
  ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧ ∀ x, V.character x = χ x

def ip {G : Type} [Group G] [Fintype G] (α β : G → ℂ) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ x, α x * β x⁻¹

def tr {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ) : ℂ := ∑ x, a.coeff x * χ x

def zOf {G : Type} [Group G] [Fintype G] (χ : G → ℂ) : MonoidAlgebra ℂ G :=
  ∑ x, MonoidAlgebra.single x (χ 1 / (Fintype.card G : ℂ) * χ x⁻¹)

variable {g : ℕ} [Fact g.Prime]

def tl (a : ℕ) {n : ℕ} (M : Mt g n) : Mt g a := fun i j => entN M i j

def br (a b : ℕ) {n : ℕ} (M : Mt g n) : Mt g b := fun i j => entN M (a + i) (a + j)

def InPar (a : ℕ) {n : ℕ} (M : Mt g n) : Prop := ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0

def toG {n : ℕ} (M : Mt g n) : Gn g n := if h : IsUnit M then h.unit else 1

def hcT (a b : ℕ) (Φ : Gn g a → Gn g b → ℂ) (n : ℕ) : Gn g n → ℂ := fun x =>
  ((Finset.univ.filter fun p : Gn g n => InPar a (p : Mt g n)).card : ℂ)⁻¹ *
    ∑ y : Gn g n, if InPar a ((y⁻¹ * x * y : Gn g n) : Mt g n) then
      Φ (toG (tl a ((y⁻¹ * x * y : Gn g n) : Mt g n))) (toG (br a b ((y⁻¹ * x * y : Gn g n) : Mt g n))) else 0

def hc (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (n : ℕ) : Gn g n → ℂ := hcT a b (fun x y => α x * β y) n

def res (a b : ℕ) {n : ℕ} (χ : Gn g n → ℂ) : Gn g a → Gn g b → ℂ := fun h₁ h₂ =>
  ((g : ℂ) ^ (a * b))⁻¹ * ∑ x : Gn g n,
    if InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = (h₁ : Mt g a) ∧ br a b (x : Mt g n) = (h₂ : Mt g b) then χ x else 0

abbrev Pc (g : ℕ) : Type := Σ d : ℕ, Gn g d → ℂ

def degL (L : List (Pc g)) : ℕ := (L.map fun p => p.1).sum

def hcL (L : List (Pc g)) : (n : ℕ) → Gn g n → ℂ :=
  List.rec (motive := fun _ => (n : ℕ) → Gn g n → ℂ) (fun _ _ => 1)
    (fun p L ih n => hc p.1 (degL L) p.2 (ih (degL L)) n) L

theorem hcL_nil (n : ℕ) : hcL ([] : List (Pc g)) n = fun _ => 1 := rfl

theorem hcL_cons (p : Pc g) (L : List (Pc g)) (n : ℕ) :
    hcL (p :: L) n = hc p.1 (degL L) p.2 (hcL L (degL L)) n := rfl

def IsCusp {d : ℕ} (χ : Gn g d → ℂ) : Prop :=
  0 < d ∧ IsIrr χ ∧ ∀ a, 0 < a → a < d → res a (d - a) χ 1 1 = 0

def wh (ψ₀ : AddChar (ZMod g) ℂ) {n : ℕ} (χ : Gn g n → ℂ) : ℂ := tr (eU g n ψ₀) χ

def der (ψ₀ : AddChar (ZMod g) ℂ) (m : ℕ) {n : ℕ} (χ : Gn g n → ℂ) : Gn g m → ℂ := fun h =>
  wh ψ₀ (res m (n - m) χ h)

def gg (ψ₀ : AddChar (ZMod g) ℂ) (n : ℕ) : Gn g n → ℂ := fun x =>
  ((Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card : ℂ)⁻¹ *
    ∑ y : Gn g n, if IsUniUp ((y⁻¹ * x * y : Gn g n) : Mt g n) then
      ψ₀ (∑ i ∈ Finset.range (n - 1), entN ((y⁻¹ * x * y : Gn g n) : Mt g n) i (i + 1)) else 0

def eJ' (g N : ℕ) [NeZero g] (k : ℕ) (ψ₀ : AddChar (ZMod g) ℂ) : MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) :=
  eDat g N (fun M => IsUniUp M ∧ ∀ a, a < k → entN M a k = 0)
    (fun M => ∑ i ∈ Finset.range (N - 1), entN M i (i + 1)) ψ₀

structure LabelDatum (g : ℕ) [Fact g.Prime] where
  teich : Formalism.CyclotomicNorms.Fbar g →* ℂ
  teich_inj : ∀ x y, x ≠ 0 → y ≠ 0 → teich x = teich y → x = y
  gen : ℕ → Formalism.CyclotomicNorms.Fbar g
  gen_order : ∀ d, 0 < d → orderOf (gen d) = g ^ d - 1
  gen_norm : ∀ d e, 0 < d → 0 < e → gen (d * e) ^ ((g ^ (d * e) - 1) / (g ^ d - 1)) = gen d

def thetaOf (L : LabelDatum g) (d : ℕ) (x z : Formalism.CyclotomicNorms.Fbar g) : ℂ :=
  if h : ∃ n : ℕ, z = L.gen d ^ n then L.teich x ^ h.choose else 0

def IsPrimeLab (d : ℕ) (P : (ZMod g)[X]) : Prop := P.Monic ∧ Irreducible P ∧ P.coeff 0 ≠ 0 ∧ P.natDegree = d

def IsCuspOf (L : LabelDatum g) (P : (ZMod g)[X]) {d : ℕ} (χ : Gn g d → ℂ) : Prop :=
  IsPrimeLab d P ∧ IsCusp χ ∧ ∀ x ∈ Formalism.CyclotomicNorms.rootsBar P, ∀ y : Gn g d, Irreducible (y : Mt g d).charpoly →
    ∀ z ∈ Formalism.CyclotomicNorms.rootsBar (y : Mt g d).charpoly,
      χ y = (-1) ^ (d - 1) * ∑ i ∈ Finset.range d, thetaOf L d x (z ^ (g ^ i))

def HasLabel (L : LabelDatum g) {n : ℕ} (χ : Gn g n → ℂ) (f : (ZMod g)[X]) : Prop :=
  ∃ Q : List ((ZMod g)[X] × Pc g), (∀ p ∈ Q, IsCuspOf L p.1 p.2.2) ∧ degL (Q.map Prod.snd) = n ∧
    f = (Q.map Prod.fst).prod ∧ ip χ (hcL (Q.map Prod.snd) n) ≠ 0

def eSerC (L : LabelDatum g) (n : ℕ) (f : (ZMod g)[X]) : MonoidAlgebra ℂ (Gn g n) :=
  ∑ᶠ χ ∈ {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f}, zOf χ

def wtC (L : LabelDatum g) {n : ℕ} (a : MonoidAlgebra ℂ (Gn g n)) (f : (ZMod g)[X]) : ℝ :=
  ((a * eSerC L n f).coeff 1).re / (a.coeff 1).re

def Green : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (d : ℕ), 0 < d → ∃ τ : (ZMod g)[X] → Gn g d → ℂ,
    (∀ P, IsPrimeLab d P → IsCuspOf L P (τ P) ∧ τ P 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1)) ∧
    (∀ P P', IsPrimeLab d P → IsPrimeLab d P' → τ P = τ P' → P = P') ∧
    ∀ χ : Gn g d → ℂ, IsCusp χ → ∃ P, IsPrimeLab d P ∧ χ = τ P

def ESerTie (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ L : LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k ∧ ∀ f, D.ntypes.eSer k f = eSerC L D.R.r f

end GlobalTheory.GLq
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
noncomputable section

namespace GlobalTheory.Pass

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Polynomial Module TensorProduct

def lenModN {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (A H : Submodule O M) : ℕ∞ :=
  Module.length O (↥A ⧸ H.comap A.subtype)

section OnePD

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    (LL O : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

def DualJumpAt : Prop :=
  ∀ (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 PD A.ρ A'.ρ P → IsDR PD A.ρ →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD A'.ρ τ a ↔ IsJumpV PD A.ρ τ (-a - 1)

variable {LL O}

def IsSubFam {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (W : GRep G Qp LL O) : Prop :=
  ∃ (a : ℕ) (x : Fin a → ι) (p : Fin a → W.V →ₗ[LL] (Fin k → LL)),
    (∀ j g v, p j (W.ρ g v) = (Ms (x j) g).mulVec (p j v)) ∧ ∀ v, (∀ j, p j v = 0) → v = 0

def LiftFam {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (e : ℕ) : Prop :=
  ∀ W₁ W₂ : GRep G Qp LL O, IsSubFam Ms W₁ → IsSubFam Ms W₂ →
    ∀ (L₁ : Lattice (O := O) W₁.ρ) (L₂ : Lattice (O := O) W₂.ρ) (F : LatHom L₁ L₂), F.Onto → F.LiftF PD e

end OnePD

def DualJumpL (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), DualJumpAt ((LT l).PD K) ↥LL.1 ↥(OL LL)

def PotDRL (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
    IsCrys ((LT l).PD K') (A.ρ.comp (Subgroup.inclusion (GK_le h))) → IsDR ((LT l).PD K) A.ρ

def PcrisTensorL (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((LT l).PD K).actB g (algebraMap ↥(K0 K') (LT l).R.B c) = algebraMap ↥(K0 K') (LT l).R.B c')
    (A A' : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (Sig Sig' : Finset ((pc (LT l) h hN hF hS).Iner →* (↥LL.1)ˣ)),
    (pc (LT l) h hN hF hS).IsPotCrys A.ρ → (pc (LT l) h hN hF hS).InertiaThrough A.ρ Sig →
    (∀ (χ : ↥(GK K) →* (↥LL.1)ˣ) (c : (pc (LT l) h hN hF hS).Iner →* (↥LL.1)ˣ),
      IsTwistRep χ⁻¹ A.ρ A'.ρ → (pc (LT l) h hN hF hS).IsPotCrys (WeaklyAdmissibleFiltrations.charRep χ) →
      (pc (LT l) h hN hF hS).InertiaThrough (WeaklyAdmissibleFiltrations.charRep χ) {c} →
      (∀ b, b ∈ Sig' ↔ ∃ a ∈ Sig, b = a * c⁻¹) →
      (pc (LT l) h hN hF hS).IsPotCrys A'.ρ ∧ (pc (LT l) h hN hF hS).InertiaThrough A'.ρ Sig') ∧
    (∀ P : A.V →ₗ[↥LL.1] A'.V →ₗ[↥LL.1] ↥LL.1, IsDual1 ((LT l).PD K) A.ρ A'.ρ P →
      (∀ b, b ∈ Sig' ↔ ∃ a ∈ Sig, b = a⁻¹) →
      (pc (LT l) h hN hF hS).IsPotCrys A'.ρ ∧ (pc (LT l) h hN hF hS).InertiaThrough A'.ρ Sig')

variable {D : D7}

set_option synthInstance.maxHeartbeats 400000 in
def TieInePoly (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)),
    Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) →
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (r.comp (decS D.nd w))) →
    ∀ σ : Gw D.nd w, (σ : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) →
      ∀ p : (D.nd.O i)[X],
        p.map (iotaO D.nd D.naut i) =
          D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) r) w) (σ : GE D.nd) →
        ∀ d ∈ (pc (D.loc (D.nd.l i)) h hN hF hS).Dpcris ((D.nbr i w hw).rep (r.comp (decS D.nd w))),
          ∑ n ∈ Finset.range (p.natDegree + 1), (D.nbr i w hw).toLL (p.coeff n) •
            actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ((D.nbr i w hw).rep (r.comp (decS D.nd w)))
              ((D.nbr i w hw).e (σ ^ n)) d = 0

def InertEq (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.inert D.nbr i w hw = IK (D.nbr i w hw).Kw

section AtW

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def PotFam {ι : Type} {k : ℕ} (Ms : ι → (GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))) (n : ℕ) : Prop :=
  ∃ (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (Sig : Finset ((pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ)) (Fr : Br.G D.nbr i w hw),
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsFrob Fr ∧
    FrobStable (pc (D.loc (D.nd.l i)) h hN hF hS).Iner Fr Sig ∧ 1 ∈ Sig ∧ Sig.card ≤ n ∧
    ∀ x, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys (matRep (Br.loc D.nbr i w hw (Ms x))) ∧
      (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough (matRep (Br.loc D.nbr i w hw (Ms x))) Sig

def JumpFam {ι : Type} {k : ℕ} (Ms : ι → (GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))) (n a b : ℕ) : Prop :=
  ∃ U : Finset ℤ, (∀ u ∈ U, -(a : ℤ) ≤ u ∧ u ≤ b) ∧ (0 : ℤ) ∈ U ∧ U.card ≤ n + 1 ∧
    ∀ x τ, JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (Ms x))) τ (U : Set ℤ)

def LiftFamW {ι : Type} {k : ℕ} (Ms : ι → (GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))) (e : ℕ) : Prop :=
  LiftFam (O := Br.OLL D.nbr i w hw) (Br.PD D.loc D.nbr i w hw) (fun x => Br.loc D.nbr i w hw (Ms x)) e

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))

def cutCoc {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) :=
  {c | ∃ (a : ℕ) (x : Fin a → D.nd.X i) (_ : ∀ j, x j ∈ Xs) (E : Fin a → Fin D.R.nV → KK D.nd i)
      (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (_ : Y.FG)
      (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
        (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
      (hE : ∀ γ : GE D.nd,
        (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y)
      (φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k),
      (∀ (γ : GE D.nd) (y : ↥Y), φ ⟨_, hst γ y.1 y.2⟩ = WKG M γ (φ y)) ∧
      c = fun g => Br.phi (D.nbr i w hw) k
        (φ ⟨_, hE ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)⟩)}


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
def LocBound {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (e : ℕ) : Prop :=
  lenModN (Submodule.span (Br.OLL D.nbr i w hw) (cutCoc i w hw r Xs M))
      (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)) ≤
    (e : ℕ∞) * lenOl (Br.PD D.loc D.nbr i w hw) (O := Br.OLL D.nbr i w hw)


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
def HfChar : Prop :=
  (∀ c ∈ Finset.Icc 2 D.R.t,
    HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw (chiRatO D.nd i c)) ≤
      BD (Br.locLat D.nbr i w hw (chiRatO D.nd i c))) ∧
  HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) ≤
    Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw)

end AtW

def eMax (D : D7) (CT eta : ℕ) : ℕ :=
  CT * ((D.R.nV + 1) * ((D.R.nV + 1) ^ 2 / 4) + (eta + D.R.t + 1) * ((D.R.nV + 1) + (D.R.nV + 1) ^ 2 / 4))

def CentralIdemCoeff : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (e : MonoidAlgebra ℂ Γ), e * e = e → (∀ z, e * z = z * e) →
    ∀ ζ : ℂ, IsPrimitiveRoot ζ (Nat.card Γ) → ∀ h : Γ,
      (Nat.card Γ : ℂ) * e.coeff h ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)

def StepPotDual : Prop :=
  ∀ D : D7, PcrisTensorL D.loc → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ),
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → PotFam i w hw (fun x : ↥Xs => rDuO D.nd i r x) n

def SubTw {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))
    {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) : Prop :=
  (Continuous fun g => M g) ∧ ∃ x ∈ Xs, ∃ j : (Fin k → KK D.nd i) →ₗ[KK D.nd i] (Fin D.R.nV → KK D.nd i),
    Function.Injective j ∧ ∀ g v, j ((mapM (toK D.nd i) M g).mulVec v) =
      (mapM (toK D.nd i) (rTwO D.nd i r x) g).mulVec (j v)

def StepCont : Prop :=
  ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ x, (Continuous fun g => rTwO D.nd i r x g) ∧ Continuous fun g => rDuO D.nd i r x g

def ResSpan {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop :=
  Submodule.span (kk D.nd i) (Set.range (mapM (IsLocalRing.residue (D.nd.O i)) (rhoO D.nd i ρ π))) = ⊤

end GlobalTheory.Pass

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LiftToGlobalDescentData
noncomputable section

open Formalism.BasicNotions Formalism.L2

namespace GlobalTheory.HeightCounting

structure NTiedGPlaceholder (D : D7) : Type

end GlobalTheory.HeightCounting

end
end
