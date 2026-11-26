module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartAlgebraMapLiftV
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.MainNotions.N IsDedekindDomain NumberField
open Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NJoin

abbrev tensCast {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) :
    FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E ≃+* E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2 := Formalism.IndefR.principalLevelFrame.tensCastR h

abbrev StdFrame {D : D7} {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : RowPsi V n) : Prop :=
  Formalism.IndefR.principalLevelFrame.StdPsi hF P


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure RealAt (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) : Type 1 where
  G : Type
  [grp : Group G]
  [fin : Fintype G]
  Pl0 : Type
  T : Type
  A : FamIn D.what₂.LL G Pl0 T D.R.m
  Ks : Type
  [fKs : Field Ks]
  [nKs : NumberField Ks]
  [aKs : Algebra Ks D.what₂.LL]
  R : RealDat D A Ks
  F : Face D A
  tupT : D.what₂.Tup → T
  hm : 0 < D.R.m
  hTop : TopMultH R
  hinj : ∀ i t, Function.Injective (R.extV i t)
  X0 : BaseLevelRowSide D
  Ish : RowIds (RowSide.sharp D) (toChainReal R F tupT hm hTop) true
  I0 : RowIds X0.s (toChainReal R F tupT hm hTop) false
  IL : LiftIds (toLiftReal R F tupT hm hTop hinj)
  K : ColReal D
  Xd : DivX D
  E : EigIdx D Xd
  labPi : E.Pi → A.fam.base.Ix
  PY : RowPsi (Yc D 0) D.R.r
  PW : ∀ i, RowPsi (Wc D i) D.R.r
  eFT : D.what₂.FT ≃ FTR R.θ PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0)
  piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ
  ι : ∀ i, ↥(GfC (Yc D 0)) →* ↥(GfC (Wc D i))
  Tp : TupTied D R.C nch
  cfEq : R.C = cf
  tpEq : HEq Tp tp
  recR : RecReal R F tupT hm hTop hinj X0 Ish I0 IL K E labPi PY PW eFT piOf ι nch Tp
  given : GlobalTheory.LiftRows.Given R F
  full : R.FullP

attribute [instance] RealAt.grp RealAt.fin RealAt.fKs RealAt.nKs RealAt.aKs

variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : RealAt D cf nch tp)

theorem RealAt.fire : ThetaFireRow (toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj) X.IL :=
  ⟨fun μ _ i => GlobalTheory.ThetaPRead.isThetaP_toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj X.given.core.thP.thF μ i,
    GlobalTheory.ThetaFireLift.thetaFireL X.R X.F X.tupT X.hm X.hTop X.hinj X.given.core.lev X.given.core.grp X.given.core.models
      X.given.core.thP X.R.hv0 X.IL,
    GlobalTheory.LiftResInj.resInjL_toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj X.given.core.models.inf⟩

def RealAt.fn {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (x : D.what₂.Mt μ (j.1 + 1)) :
    GA D (Vc D j) → (X.R.cV j).W := (X.IL.jMt μ hμ j x).1

def RealAt.rep (σ : D.what₂.FT) : NG.FinTyp D.host.E D.R.r := rowRepR X.R.θ (X.eFT σ)

structure Agree (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) where
  hF : D.host.F = maximalRealSubfield D.host.E
  PV : ∀ j, RowPsi (Vc D j) D.R.nV
  stdV : ∀ j, StdFrame hF (PV j)
  stdW : ∀ j, StdFrame hF (X.PW j)
  a : Fin D.R.m → Formalism.AUTREP.GAf D.host.E D.R.nV
  rat : ∀ j h, h ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔
    ∃ γ ∈ Formalism.L2.Theta.GQ (Vc D j), finHom (Vc D j) γ = finHom (Vc D j) ((PV j).ψ ((a j)⁻¹ * h * a j))
  eW : ∀ μ, Used0 D μ → ∀ j : Fin D.R.m, (X.R.cV j).W ≃ₗ[ℂ] (M μ (j.1 + 1) (by omega) (by omega)).wt.W
  wt : ∀ μ hμ (j : Fin D.R.m) (h : ReciprocityTheory.Aut.GQ D.host.E D.R.nV), ∀ γ ∈ Formalism.L2.Theta.GQ (Vc D j),
    finHom (Vc D j) γ = finHom (Vc D j) ((PV j).ψ ((a j)⁻¹ * h * a j)) → ∀ v,
      eW μ hμ j ((X.R.cV j).ρ γ v) = (M μ (j.1 + 1) (by omega) (by omega)).wt.ρ h (eW μ hμ j v)
  real : ∀ μ hμ (j : Fin D.R.m) x h,
    (M μ (j.1 + 1) (by omega) (by omega)).real x h = eW μ hμ j (X.fn hμ j x ((PV j).ψ ((a j)⁻¹ * h)))
  rep_iso : RowRepTie rep X.R.θ X.PY (X.R.MY 0) (fun b => levS _ (X.R.βY 0) (X.R.dat0 (X.R.levR X.F b)))
    (fun b => levChi _ (X.R.βY 0) (X.R.dat0 (X.R.levR X.F b))) (fun _ => X.R.e0) X.eFT

def IsCanon {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (j : Fin D.R.m) {j' : ℕ} (hj : j.1 + 1 = j')
    (Y : GlobalTheory.NPin.RowMod D rep j') : Prop :=
  ∃ (e : Y.A →ₗ[ℂ] Mult.MMap (X.R.MW j (sg0 D X.A))) (c : ℝ), Function.Injective e ∧ 0 < c ∧
    Y.C.map e = Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)) ∧
    (∀ h x, e (Y.ρ h x) = actM (X.PW j) (X.R.MW j (sg0 D X.A)) h (e x)) ∧
    (∀ x ∈ Y.C, ∀ y ∈ Y.C, Y.B x y = (c : ℂ) * Mult.ipM (X.R.MW j (sg0 D X.A)) (X.R.νW j) (X.R.fdW j) (e x) (e y)) ∧
    ∀ y : D.what₂.Mj (j.1 + 1), PiTensorProduct.lift (e (Y.φ (hj ▸ y))) = (X.IL.jMj j y).1

def OnGood (i : D.nd.Loc) (p : ∀ (j : Fin D.R.m) (t : X.T), (X.R.HV j t).H → Prop) : Prop :=
  ∀ (hμ : Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i,
    ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x →
      ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → p j (X.tupT (D.nd.mu i)) y

def EigString (i : D.nd.Loc) : Prop :=
  OnGood X i fun j t y => y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j t h →
    ∃ s, GlobalTheory.DownLift.HasString X.R j t s ∧ GlobalTheory.DownLift.IsEigV X.R j t h s y

def EigGood (i : D.nd.Loc) : Prop := OnGood X i fun j t y => GlobalTheory.DownLift.GoodVt X.R j t y

theorem used_mu (i : D.nd.Loc) : Used0 D (D.nd.mu i) :=
  Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩

theorem RealAt.existsUnique_vec {μ} (hμ : Used0 D μ) (j : Fin D.R.m) (f : D.what₂.Mt μ (j.1 + 1)) :
    ∃! y, X.R.extV j (X.tupT μ) y = X.fn hμ j f := by
  have h : ∃ y, X.R.extV j (X.tupT μ) y = X.fn hμ j f := (X.IL.jMt μ hμ j f).2.1
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy, fun z hz => X.hinj _ _ (hz.trans hy.symm)⟩

end GlobalTheory.NJoin

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
noncomputable section

namespace GlobalTheory.TwU.WildChar

open _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker _root_.Formalism.UG _root_.Formalism.L2.Forms
open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

section Idele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)

end Idele

section Central

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} (t : KerEntTied ex) {u : D.what₂.Word} (μ : D.what₂.Tup)

variable {t μ} {St : ChainCharts D u μ} {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}


end Central

section Twist

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

end Twist

section Charts

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type}
  {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}


end Charts

section True

open GlobalTheory.TwU.AtTrue

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



end True

end GlobalTheory.TwU.WildChar

end

noncomputable section

namespace GlobalTheory.TwU.Rigid

open _root_.Formalism.UG _root_.Formalism.L2.Col _root_.Formalism.L2.PairingIndexBounds.F _root_.Formalism.MainNotions.G.KAat _root_.Formalism.L2.Forms _root_.Formalism.L2.Ker _root_.Formalism.L2.DIV
open NumberField IsDedekindDomain Matrix _root_.Formalism.BasicNotions _root_.Formalism.MainNotions _root_.Formalism.MainNotions.G
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}


end GlobalTheory.TwU.Rigid

end

noncomputable section

namespace GlobalTheory.TwU.Model

open NumberField IsDedekindDomain Matrix _root_.Formalism.BasicNotions _root_.Formalism.MainNotions _root_.Formalism.L2.Col _root_.Formalism.L2.Ker _root_.Formalism.L2.DIV _root_.Formalism.L2.Forms _root_.Formalism.UG
open scoped TensorProduct

section CongBasic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  have hi : ∀ x : 𝓞 E, iA F E (algebraMap (𝓞 E) E x) ∈ Formalism.L2.Herm.intAf F E := fun x => (toRInt F E x).2
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a + b) =
      iA F E (algebraMap (𝓞 E) E r) * (iA F E (algebraMap (𝓞 E) E s) * a) +
        iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact add_mem (mul_mem (hi r) h1) (mul_mem (hi s) h2)

theorem intAtA_mul {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a * b) =
      (iA F E (algebraMap (𝓞 E) E s) * a) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem h1 h2

theorem intAtA_int (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [map_one, map_one, one_mul]; exact (toRInt F E x).2⟩

theorem intAtA_sum {ι : Type} (s : Finset ι) (f : ι → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (h : ∀ i ∈ s, IntAtA (F := F) P (f i)) :
    IntAtA (F := F) P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using intAtA_int (F := F) (P := P) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intAtA_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end CongBasic

theorem sameCoset_equiv {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (P : rowSG Pr sel mu) :
    Equivalence (fun y y' : Sp X.E n => SameCoset sel mu cst P y y') := by
  constructor
  · intro y l
    rw [sub_self, Pi.zero_apply, mul_zero]
    exact ciIntAt_zero
  · intro y y' h l
    have h1 := ciIntAt_neg (h l)
    rwa [← mul_neg, ← Pi.neg_apply, neg_sub] at h1
  · intro x y z h h' l
    have h1 := (h l).add (h' l)
    rwa [← mul_add, ← Pi.add_apply, sub_add_sub_cancel] at h1

end GlobalTheory.TwU.Model

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWU4OfLimWU3
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.CongL

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def SeedWU4 (Rk : ℕ → Prop) (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (Wt : SeedWtU) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → Rk a → ∀ d : ℕ, FieldOK E l d →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    IsSplitAt v' → Apart v' w₀ → ∀ (U : Submodule ℂ (UA E a → ℂ)) (S Y : Finset (HeightOneSpectrum (𝓞 E))),
    ∃ Z₀ : Finset (HeightOneSpectrum (𝓞 E)),
      (∀ z ∈ Z₀, UsPl d z ∧ ((l : ℕ) : 𝓞 E) ∉ z.asIdeal ∧ Apart z w₀ ∧ ApartAll S z) ∧
      ∀ U' : Submodule ℂ (UA E a → ℂ), AutOffT T U' → Ty E l a w₀ U' → Wt E l a ι w₀ v' U U' → SphOffU w₀ S U' →
        (∃ B, SatU U' v' B) → (∀ z ∈ Z₀, GenAtU Gen U' z) →
      ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
        (∃ (V : Set (G E Ω)) (X : Finset (HeightOneSpectrum (𝓞 E))), IsOpen V ∧ Dense V ∧
          ∀ w, w ∉ X → UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ApartAll S w →
            ∀ B, SatU U' w B → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
              (∀ s ∈ Ine (F := E) A, r s = 1) ∧ ∀ s : G E Ω, IsFrob A (normV w) s → s ∈ V →
                ((r s⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
                  ((UpperTheory.V.Af.algSat a (normV w) B).map fun b => Polynomial.X - Polynomial.C b).prod) ∧
        (∀ w ∈ Y, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ApartAll S w →
          ∀ B, SatU U' w B → Gen a (normV w) B → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
        (∀ w ∈ Y, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ApartAll S w → CrysDRU U' ι r w) ∧
        (∀ w ∈ Y, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ApartAll S w → ∀ B, SatU U' w B → Gen a (normV w) B → PhiAt ι r w B)

def CongUW4 (Rk : ℕ → Prop) (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (Wt : SeedWtU) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → Rk a →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ U : Submodule ℂ (UA E a → ℂ), AutOffT T U →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    IsSplitAt v' → Apart v' w₀ →
    ∃ Kw : Levels E a, HasLevelOff w₀ v' Kw U ∧
      (∀ w, IsSplitAt w → Apart w w₀ → IsOpen (Kw w : Set (GL (Fin a) (w.adicCompletion E))) ∧
        IsCompact (Kw w : Set (GL (Fin a) (w.adicCompletion E)))) ∧
      (∀ w, IsSplitAt w → Apart w w₀ → Apart w v' → (∃ B, SatU U w B) → Kw w = GlobalTheory.LFun.KGL w (n := a)) ∧
      ∀ (Z W : Finset (HeightOneSpectrum (𝓞 E))),
        (∀ z ∈ Z, IsSplitAt z ∧ Apart z w₀ ∧ Apart z v' ∧ ∃ B, SatU U z B) →
        (∀ w ∈ W, IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∈ w.asIdeal ∧ Apart w w₀ ∧ Apart w v' ∧ ∃ B, SatU U w B) →
      ∃ c : HeightOneSpectrum (𝓞 E) → ℤ → ℂ, (∀ w n, c w n ≠ 0) ∧
      ∀ (J : Type) (O : LocOps l ι Kw J) (θ : J → Qbar l), IsSysU O U θ →
        PolyApprox (Sum.elim θ (fun p : ↥W × ℤ => ι.symm (c p.1 p.2 * PowSatU U p.1 p.2)))
          {ϑ | ∃ U' θ', AutOffT T U' ∧ HasLevelOff w₀ v' Kw U' ∧ (∃ B, SatU U' v' B) ∧ SameWtOff ι w₀ v' U U' ∧
            Wt E l a ι w₀ v' U U' ∧ Ty E l a w₀ U' ∧ (∀ z ∈ Z, GenAtU Gen U' z) ∧ (∀ w ∈ W, GenAtU Gen U' w) ∧ IsSysU O U' θ' ∧
            ϑ = Sum.elim θ' (fun p : ↥W × ℤ => ι.symm (c p.1 p.2 * PowSatU U' p.1 p.2))} ∧
        ((∀ j g, ∃ q : ℚ, O.f j g = q) → ∃ L : FinExt l, ∀ j, θ j ∈ L.1)

def LimWU4 (Rk : ℕ → Prop) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → Rk a → ∀ d : ℕ, FieldOK E l d →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ U : Submodule ℂ (UA E a → ℂ), AutOffT T U →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    IsSplitAt v' → Apart v' w₀ →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
      (∀ w, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, SatU U w B →
        UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → (∃ B, SatU U w B) → CrysDRU U ι r w) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ∀ B, SatU U w B →
        ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (hA : IsPlaceOver A w)
          (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
          (hBw : Pst.Induces Bw) (σ : Weil hA),
        ∃ (C : Set (G E Ω →* GL (Fin a) (Qbar l))) (J : (E →+* Qbar l) → Multiset ℤ),
          (∀ ρ ∈ C, Continuous ρ ∧ IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
            ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
              IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ (J τ)) ∧
          GlobalTheory.CongPhi.JointApprox r C (fun n => ι.symm (GlobalTheory.CongPhi.phiSum (GlobalTheory.RoadU.satWD hA a B) σ n))
            (fun ρ n => ι.symm (GlobalTheory.CongPhi.phiSum (wdAt P ι Bw hA hBw (ρ.comp (Dec (F := E) A).subtype)) σ n)))

def SeedFinOdd : Prop := SeedWU4 Odd GlobalTheory.CongW.TyEll (GlobalTheory.CongW.GenOf DGen) WtLac

def CongFinOdd : Prop := CongUW4 Odd GlobalTheory.CongW.TyEll (GlobalTheory.CongW.GenOf DGen) WtLac

def LimFinOdd : Prop := LimWU4 Odd

end GlobalTheory.CongL

end
end
