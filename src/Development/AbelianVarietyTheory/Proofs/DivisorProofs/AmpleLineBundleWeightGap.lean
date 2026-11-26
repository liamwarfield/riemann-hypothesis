module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BorelWeilFlagModelDetInverseIsAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightSectionsNonvanishingOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionExtensionToUniformisedSemiAbelia
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleFinitePlacesUnramOrSplitStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.HasPolChartOf
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

section Act

variable {R : Type} [CommRing R] [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R']

def IsPrim {S : Scheme.{0}} (P : PolAV S) (w : P.A ⟶ P.A) : Prop :=
  letI := P.isAb.comm
  ∃ u : LB.Gen (LB.LinComb P.L (K := Fin 4) ![(padd P.A (𝟙 _) w).left, 𝟙 P.A.left, w.left, (toUnit P.A ≫ η[P.A]).left]
    ![1, -2, -1, 2]), u.IsGen

end Act

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {o : Type} [CommRing o] {b : o →+* c.F}

end GlobalTheory.PolDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleWeightGap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsNsmulOfCommon
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp.AmpleTwist

private def commonRestr {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) : LB Y where
  ι := C.J
  U j := (B s).U (C.idx s j)
  g j j' := (B s).g (C.idx s j) (C.idx s j')

private theorem isLB_commonRestr {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    (commonRestr C s).IsLB := {
  cover := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨j, hj⟩ := C.cover y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (C.mem s j y).2 hj⟩
  g_self j := (C.isLB s).g_self (C.idx s j)
  cocycle i j k := (C.isLB s).cocycle (C.idx s i) (C.idx s j) (C.idx s k) }

private theorem commonRestr_iso {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    LBIso (commonRestr C s) (B s) :=
  iso_of_chart (C.isLB s)
    { idx := C.idx s
      le := fun _ _ h => h
      g := fun _ _ _ _ _ => rfl }

private theorem commonRestr_iso_tens {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    LBIso (commonRestr C (a + b)) (tens (B a) (B b)) :=
  iso_of_chart (isLB_tens (C.isLB a) (C.isLB b))
    { idx := fun j => (C.idx a j, C.idx b j)
      le := fun j y h => by
        have h' : y ∈ C.U j := (C.mem (a + b) j y).1 h
        exact ⟨(C.mem a j y).2 h', (C.mem b j y).2 h'⟩
      g := fun y j j' hj hj' => by
        have h₁ : y ∈ C.U j := (C.mem (a + b) j y).1 hj
        have h₂ : y ∈ C.U j' := (C.mem (a + b) j' y).1 hj'
        refine (C.add a b y j j' h₁ h₂).trans ?_
        exact (tr_tens (B a) (B b) y (a := (C.idx a j, C.idx b j)) (b := (C.idx a j', C.idx b j'))
          ⟨(C.mem a j y).2 h₁, (C.mem b j y).2 h₁⟩ ⟨(C.mem a j' y).2 h₂, (C.mem b j' y).2 h₂⟩).symm }

private theorem cls_common_add {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    cls (B (a + b)) (C.isLB (a + b)) = cls (B a) (C.isLB a) + cls (B b) (C.isLB b) := by
  have e₁ := (cls_eq_iff (isLB_commonRestr C (a + b)) (C.isLB (a + b))).2 (commonRestr_iso C (a + b))
  have e₂ := (cls_eq_iff (isLB_commonRestr C (a + b)) (isLB_tens (C.isLB a) (C.isLB b))).2
    (commonRestr_iso_tens C a b)
  rw [← e₁, e₂, cls_tens (C.isLB a) (C.isLB b)]

theorem cls_nsmul_of_common {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ)
    (a : Λ) : cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) := by
  induction n with
  | zero =>
    have h := cls_common_add C 0 0
    simp only [add_zero] at h
    simp only [zero_nsmul]
    exact left_eq_add.1 h
  | succ n ih => rw [succ_nsmul, cls_common_add C, ih, succ_nsmul]

theorem ampleAt_of_sec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (A : LB TF.Y.X), A.IsLB → ∀ (ρ χ : AllWt.Weight Dw) (n m : ℕ), IsAmpleLB (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)) → ∀ (y : Y₀ TF.X Z) (s : (LB.div (lbPow (L₀ TF.X Z χ) m) ((lbPow A n).pull (inc₀ TF.X Z ≫ TF.X.π))).Sec), y ∈ nonzeroLocus s → AmpleAt (L₀ TF.X Z (m • χ - ρ)) y := by
  intro E _ _ _ H Dw l Xo c TF Z A hA ρ χ n m hamp y s hs
  have hAg : (A.pull (inc₀ TF.X Z ≫ TF.X.π)).IsLB := pull_isLB hA _
  have hP : (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n).IsLB := isLB_lbPow hAg n
  have hρ := isLB_L₀ TF.X Z ρ
  have hB : (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)).IsLB := hamp.isLB
  have hN := isLB_L₀ TF.X Z (m • χ - ρ)
  have hN1 := isLB_lbPow hN 1
  have hD := LB.isLB_div hN1 hB
  have hχ := isLB_L₀ TF.X Z χ
  have hχm := isLB_lbPow hχ m
  have hAn := isLB_lbPow hA n
  have hAng : ((lbPow A n).pull (inc₀ TF.X Z ≫ TF.X.π)).IsLB := pull_isLB hAn _
  have hT := LB.isLB_div hχm hAng
  have hiso : LBIso (LB.div (lbPow (L₀ TF.X Z (m • χ - ρ)) 1)
      (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)))
      (LB.div (lbPow (L₀ TF.X Z χ) m) ((lbPow A n).pull (inc₀ TF.X Z ≫ TF.X.π))) := by
    refine (cls_eq_iff hD hT).1 ?_
    have e := cls_common_add (common₀ TF.X Z) (m • χ - ρ) ρ
    rw [sub_add_cancel] at e
    have e2 := cls_nsmul_of_common (common₀ TF.X Z) m χ
    rw [cls_div hN1 hB hD, cls_div hP hρ hB, cls_lbPow hN 1 hN1, cls_lbPow hAg n hP, cls_pull hA _ hAg,
      cls_div hχm hAng hT, cls_pull hAn _ hAng, cls_lbPow hA n hAn, cls_lbPow hχ m hχm, map_nsmul]
    have e3 : cls (L₀ TF.X Z (m • χ - ρ)) hN = m • cls (L₀ TF.X Z χ) hχ - cls (L₀ TF.X Z ρ) hρ := by
      rw [← e2, e, add_sub_cancel_right]
    rw [e3]
    abel
  obtain ⟨s', hs'⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hD hT hiso s
  refine ⟨1, LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ), s', one_pos, hB, hamp, ?_⟩
  rw [hs']
  exact hs

end GlobalTheory.HSApp.AmpleTwist
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

theorem _root_.GlobalTheory.HSApp.exists_dominant_sub {E : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
    (la ν : _root_.GlobalTheory.AllWt.Weight Dw) (hla : _root_.GlobalTheory.HSApp.GapGe (1 : ℤ) la) :
    ∃ mu : _root_.GlobalTheory.AllWt.Weight Dw, _root_.GlobalTheory.HSApp.GapGe (0 : ℤ) mu ∧
      ∃ m : ℕ, 0 < m ∧ m • la - mu = ν := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ τ : _root_.GlobalTheory.AllWt.Psi H, ∀ k : ℕ,
      k + 1 < Dw.p + Dw.q → _root_.GlobalTheory.CompHS.gap (ν τ) k ≤ M := by
    refine ⟨Finset.univ.sup fun p : _root_.GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q) =>
      (_root_.GlobalTheory.CompHS.gap (ν p.1) (p.2 : ℕ)).toNat, fun τ k hk => ?_⟩
    have h := Finset.le_sup (f := fun p : _root_.GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q) =>
      (_root_.GlobalTheory.CompHS.gap (ν p.1) (p.2 : ℕ)).toNat)
      (Finset.mem_univ (τ, (⟨k, by omega⟩ : Fin (Dw.p + Dw.q))))
    exact (Int.self_le_toNat _).trans (by exact_mod_cast h)
  refine ⟨(M + 1) • la - ν, ?_, M + 1, Nat.succ_pos M, sub_sub_cancel _ _⟩
  unfold _root_.GlobalTheory.HSApp.GapGe at hla ⊢
  intro τ k hk
  have h₁ := hla τ k hk
  have h₂ := hM τ k hk
  unfold _root_.GlobalTheory.CompHS.gap at h₁ h₂ ⊢
  rw [dite_eq_left hk] at h₁ h₂ ⊢
  have e : ∀ i, ((M + 1) • la - ν) τ i = ((M + 1 : ℕ) : ℤ) * la τ i - ν τ i := by
    intro i
    simp
  rw [e, e]
  push_cast
  nlinarith

end GlobalTheory.HSApp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigThetaKernelIntegrable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastNotMemOfCoprime
universe u_1

namespace GlobalTheory.CoprimeNatNotMem

theorem natCast_not_mem_of_coprime {Rg : Type u_1} [CommRing Rg] {P : Ideal Rg} (hP : P ≠ ⊤)
    {p n : ℕ} (h : Nat.Coprime p n) (hp : (p : Rg) ∈ P) : (n : Rg) ∉ P := by
  intro hn

  obtain ⟨u, v, huv⟩ : IsCoprime (p : Rg) (n : Rg) := by
    have hz : IsCoprime (p : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.mpr h
    simpa using hz.map (Int.castRingHom Rg)
  apply hP
  rw [Ideal.eq_top_iff_one, ← huv]
  exact P.add_mem (P.mul_mem_left u hp) (P.mul_mem_left v hn)

end GlobalTheory.CoprimeNatNotMem
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.SquareConv

theorem natCast_not_mem {Rg : Type*} [CommRing Rg] {P : Ideal Rg} (hP : P ≠ ⊤) {p n : ℕ} (hpn : Nat.Coprime p n)
    (hp : (p : Rg) ∈ P) : (n : Rg) ∉ P :=
  _root_.GlobalTheory.CoprimeNatNotMem.natCast_not_mem_of_coprime hP hpn hp

theorem standing {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {large₂ : SizeData₂ D}
    (hS : HidaSetting large₂ R F) (hx : 11 ≤ D.host.splitBound) {sc : Consts} (G : GridData R.toLevCh sc) (t : T) :
    SquareStanding G t := by
  classical
  obtain ⟨hq, hd, -⟩ := D.host.hyp
  have hcc : D.host.ccK = ⊤ := hS.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨P, -, -⟩, -⟩ := hS.size
  have lev : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_condN_of_splitK D.host hpp (P.level_split p hp)
  refine ⟨hx, fun w hw => ?_⟩
  have e1 : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) = ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) := by
    rw [hcc, Ideal.absNorm_top, mul_one]
  rw [e1]
  rcases Finset.mem_union.1 hw with hw | hw
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨p, hpv, hcop⟩ : ∃ p : ℕ, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∧ Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := by
      rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1
      · refine ⟨q0 D, G.pl.basePlace_over_qZero, ?_⟩
        have hs := (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
        have hM : Nat.Coprime (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) (q0 D) := by
          rw [Nat.Coprime, Nat.gcd_rec, hs, Nat.gcd_one_left]
        have hdv : D.host.QS * D.host.q * D.host.d ∣ Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D := by
          unfold LevelStarExponents.condE
          exact Dvd.dvd.mul_left dvd_rfl _
        exact (hM.coprime_dvd_left hdv).symm
      · rcases (S1_mem_OmF D).1 hv1 with h | h | h | h
        · exact ⟨_, h, lev _ (D.host.g_level 0) (D.host.g_prime 0)⟩
        · exact ⟨_, h, lev _ (D.host.g_level 1) (D.host.g_prime 1)⟩
        · exact ⟨_, h, lev _ D.host.pde_level.1 D.host.pde_prime⟩
        · exact ⟨_, h, lev _ D.host.pde_level.2 D.host.pde'_prime⟩
    have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal := by
      rw [← G.pl.under_w hv, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hpv
      exact hpv
    exact natCast_not_mem (G.pl.w v).isPrime.ne_top hcop hpw
  · intro hmem
    apply (hS.core.lev.Q_off t w hw).1
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem

theorem splitBound_ge {D : D7} {large₂ : SizeData₂ D} {ε : ℝ} (_he : large₂.sc.eps = ε) (_hx : (12 : ℝ) ^ (5 / ε) ≤ large₂.sc.x)
    {Γ : Type} {_ : Group Γ} {_ : Fintype Γ} {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} {_ : Field Ks} {_ : NumberField Ks} {_ : Algebra Ks D.what₂.LL} {R : RealDat D A Ks} {F : Face D A}
    (hS : HidaSetting large₂ R F := by assumption) : 11 ≤ D.host.splitBound :=
  hS.size.2.1.eleven_le

end GlobalTheory.SquareConv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpEqZeroOfHeisEigen
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.CosetOrth

section General

variable {E : Type} [Field E] [NumberField E]

def InHat (I : FractionalIdeal (𝓞 E)⁰ E) (x : FiniteAdeleRing (𝓞 E) E) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (x w) ≤ WithZero.exp (-(FractionalIdeal.count E w I))

theorem inHat_one_iff (x : FiniteAdeleRing (𝓞 E) E) : InHat 1 x ↔ ∀ w, Valued.v (x w) ≤ 1 := by
  simp only [InHat, FractionalIdeal.count_one, neg_zero, WithZero.exp_zero]

theorem inHat_zero (I : FractionalIdeal (𝓞 E)⁰ E) : InHat I 0 := fun w => by
  have : (0 : FiniteAdeleRing (𝓞 E) E) w = 0 := rfl
  rw [this, map_zero]; exact zero_le

theorem InHat.mul_left {I : FractionalIdeal (𝓞 E)⁰ E} {t x : FiniteAdeleRing (𝓞 E) E} (ht : InHat 1 t) (hx : InHat I x) :
    InHat I (t * x) := fun w => by
  have : (t * x) w = t w * x w := rfl
  rw [this, map_mul]
  exact (mul_le_of_le_one_left' ((inHat_one_iff t).1 ht w)).trans (hx w)

theorem InHat.add {I : FractionalIdeal (𝓞 E)⁰ E} {x y : FiniteAdeleRing (𝓞 E) E} (hx : InHat I x) (hy : InHat I y) :
    InHat I (x + y) := fun w => by
  have : (x + y) w = x w + y w := rfl
  rw [this]
  exact (Valued.v.map_add _ _).trans (max_le (hx w) (hy w))

theorem InHat.neg {I : FractionalIdeal (𝓞 E)⁰ E} {x : FiniteAdeleRing (𝓞 E) E} (hx : InHat I x) : InHat I (-x) := fun w => by
  have : (-x) w = -x w := rfl
  rw [this, Valuation.map_neg]
  exact hx w

end General

variable {D : D7}

abbrev FA (D : D7) : Type := FiniteAdeleRing (𝓞 D.host.E) D.host.E

def fe (D : D7) : AE D →+* FA D := (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp (finPart D)

theorem fe_apply (x : AE D) : fe D x = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D x) := rfl

def skewId (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
    ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)

def HatPt {S T : HSp D} (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (u : WO S T) : Prop :=
  u.map (infPart D) = 0 ∧ ∀ i j, InHat I (algebraMap D.host.E (FA D) r * fe D (u i j))

def finMat {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) : Matrix (Fin n) (Fin n) (FA D) :=
  ((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)).map (GlobalTheory.BotFormula.toFinE D)

theorem exists_fe (s : FA D) : ∃ σ : AE D, infPart D σ = 0 ∧ fe D σ = s := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm (0, (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s), ?_, ?_⟩
  · exact (he _).1.symm.trans (by rw [e.apply_symm_apply])
  · have : finPart D (e.symm (0, (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s)) =
        (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s := (he _).2.symm.trans (by rw [e.apply_symm_apply])
    rw [fe_apply, this, RingEquiv.apply_symm_apply]

theorem ip_eq_zero_of_heis_eigen {A B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ν : Measure (WO A B)} {𝓕 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓕) {f₁ f₂ : WO A B → ℂ}
    (h₁ : IsThetaFunO ψ A B f₁) (h₂ : IsThetaFunO ψ A B f₂) (v : WO A B) {α β : ℂ}
    (e₁ : heisO ψ A B v f₁ = α • f₁) (e₂ : heisO ψ A B v f₂ = β • f₂) (hβ : ‖β‖ = 1) (hne : α ≠ β) :
    ip A B ν 𝓕 f₁ f₂ = 0 := by
  have key := GlobalTheory.Size.ipO_heisO hψ hν.1 hν.2.1 h₁ h₂ v
  rw [e₁, e₂] at key
  have e : GlobalTheory.Ker.ipO ν 𝓕 (α • f₁) (β • f₂) = (α * starRingEnd ℂ β) * ip A B ν 𝓕 f₁ f₂ := by
    unfold GlobalTheory.Ker.ipO ip
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun w => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  have e' : GlobalTheory.Ker.ipO ν 𝓕 f₁ f₂ = ip A B ν 𝓕 f₁ f₂ := rfl
  rw [e, e'] at key
  have hb : starRingEnd ℂ β * β = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hβ]; simp
  have hne' : α * starRingEnd ℂ β ≠ 1 := fun h => hne (by
    have := congrArg (· * β) h
    simp only [one_mul, mul_assoc, hb, mul_one] at this
    exact this)
  have : (α * starRingEnd ℂ β - 1) * ip A B ν 𝓕 f₁ f₂ = 0 := by rw [sub_mul, key, one_mul, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne')

end GlobalTheory.CosetOrth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomDictionaryFramesExponentsKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleFirstFiniteDatumStandardIsVacuumDatu
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleFirstFiniteDatumStandardIsVacuumDatu
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotDict

theorem fst_isFinF : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (hA : X.rA.IsStd) (hW : X.rW.IsStd), X.Is ψ θ α β νH S → ∀ t, IsFinF ψ θ true (GlobalTheory.BotDict.stdFr A hA.1) (GlobalTheory.BotDict.stdFr WW hW.1) (X.f t) := by
  intro D T A A' WW X ψ θ α β νH S hA hW hX t
  have hv := hX.isVac
  have hν : Formalism.L2.Theta.IsHeckeChar D (α t / β t) := by
    have h := (hX.weil t).hecT
    rw [← inv_div]
    refine ⟨?_, fun x => ?_⟩
    · exact continuous_inv.comp h.1
    · show ((β t / α t) _)⁻¹ = 1
      rw [h.2 x, inv_one]
  have hI : X.ideal S t ≠ ⊥ := by
    unfold Tri.ideal
    rw [← Ideal.zero_eq_bot]
    refine Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_
    rw [Ideal.zero_eq_bot]
    exact w.ne_bot
  obtain ⟨f₁, h1, h1t⟩ := GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D ψ θ A WW X.rA X.rW (α t / β t) (X.e t) (S t) (X.ideal S t) X.vac
    hX.rigA hX.rigW hν (hX.idem t) hI hv
  have heq : X.f t = f₁ := by
    obtain ⟨⟨Tm, hT⟩, hall⟩ := hX.fst t
    rw [hall Tm hT, h1.2 Tm hT]
  have hft : IsThetaFunO ψ (GlobalTheory.Grid.neg A) WW (X.f t) := heq ▸ h1t
  refine ⟨hft, fun τ => ?_⟩
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.idem t)
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hv.1.1.1 hv.2.inf ho.infPart_eq ho.conj.infPart_eq
    (hX.fst t) hv.2.theta hft (hv.2.fock τ)
  rw [cart_frSgn_true_stdFr, cart_stdFr]
  have e1 : X.rA.s τ = 1 := (hA.2.2 τ).1
  have e2 : X.rW.s τ = 1 := (hW.2.2 τ).1
  simp only [e1, e2] at hF
  exact hF

end GlobalTheory.BotDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleFirstFiniteDatumStandardIsVacuumDatuStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesawTriple_firstFiniteDatum_standard_isVacuumDatum : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (hA : X.rA.IsStd) (hW : X.rW.IsStd), X.Is ψ θ α β νH S → ∀ t, IsFinF ψ θ true (GlobalTheory.BotDict.stdFr A hA.1) (GlobalTheory.BotDict.stdFr WW hW.1) (X.f t) := by
  first | exact @GlobalTheory.BotDict.fst_isFinF | exact GlobalTheory.BotDict.fst_isFinF | (intros; apply GlobalTheory.BotDict.fst_isFinF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRanksArithmeticLargeGrids
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRanksArithmeticLargeGrids
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotRankSize

theorem bot_arith (D : D7) (i j : ℕ) :
    Even (SqNum.botBig D i j + SqNum.botSmall D i j) ∧ SqNum.botSmall D i j + 2 < SqNum.botBig D i j ∧
      1 < SqNum.botSmall D i j := by
  have hk := D.R.k_even
  have hm := D.R.m_even
  have ht := D.R.t_odd
  have h3 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  rw [Nat.even_iff] at hk hm
  rw [Nat.odd_iff] at ht
  simp only [SqNum.botBig, SqNum.botSmall, rankV, sLen, Formalism.BasicNotions.Ranks.r]
  have e1 : (j + 1) * D.R.t = j * D.R.t + D.R.t := by ring
  have e2 : (i + 1) * (D.R.k + D.R.m - 1 + 6) = i * (D.R.k + D.R.m - 1 + 6) + (D.R.k + D.R.m - 1 + 6) := by ring
  rw [e1, e2]
  generalize j * D.R.t = A
  generalize i * (D.R.k + D.R.m - 1 + 6) = B
  rw [Nat.even_iff]
  omega

theorem bottom_ranks : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ i j : Fin D.R.m, Even (SqNum.botBig D i j + SqNum.botSmall D i j) ∧ SqNum.botSmall D i j + 2 < SqNum.botBig D i j ∧ 1 < SqNum.botSmall D i j := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro i j
  exact bot_arith D i j

end GlobalTheory.BotRankSize

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRanksArithmeticLargeGridsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomRanks_arithmetic_largeGrids : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ i j : Fin D.R.m, Even (SqNum.botBig D i j + SqNum.botSmall D i j) ∧ SqNum.botSmall D i j + 2 < SqNum.botBig D i j ∧ 1 < SqNum.botSmall D i j := by
  first | exact @GlobalTheory.BotRankSize.bottom_ranks | exact GlobalTheory.BotRankSize.bottom_ranks | (intros; apply GlobalTheory.BotRankSize.bottom_ranks <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleSecondFiniteDatumStandardIsVacuumDat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleSecondFiniteDatumStandardIsVacuumDat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotDict

theorem isFinF_snd_std : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (hA' : X.rA'.IsStd) (hW : X.rW.IsStd), X.Is ψ θ α β νH S → ∀ t, IsFinF ψ θ false (GlobalTheory.BotDict.stdFr A' hA'.1) (GlobalTheory.BotDict.stdFr WW hW.1) (X.f' t) := by
  intro D T A A' WW X ψ θ α β νH S hA' hW hI t
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hth : IsThetaFunO ψ A' WW (X.f' t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hI.isVac'.1 hI.isVac'.2.inf (hI.snd t) hI.isVac'.2.theta
  refine ⟨hth, fun τ => ?_⟩
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hI.isVac'.1.1.1 hI.isVac'.2.inf ho.conj.infPart_eq
    ho.conj.conj.infPart_eq (hI.snd t) hI.isVac'.2.theta hth (hI.isVac'.2.fock τ)
  rw [(hA'.2.2 τ).1, (hW.2.2 τ).1] at hF
  rw [cart_frSgn_false_stdFr, cart_stdFr]
  exact hF

end GlobalTheory.BotDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleSecondFiniteDatumStandardIsVacuumDatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesawTriple_secondFiniteDatum_standard_isVacuumDatum : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (hA' : X.rA'.IsStd) (hW : X.rW.IsStd), X.Is ψ θ α β νH S → ∀ t, IsFinF ψ θ false (GlobalTheory.BotDict.stdFr A' hA'.1) (GlobalTheory.BotDict.stdFr WW hW.1) (X.f' t) := by
  first | exact @GlobalTheory.BotDict.isFinF_snd_std | exact GlobalTheory.BotDict.isFinF_snd_std | (intros; apply GlobalTheory.BotDict.isFinF_snd_std <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomDictionaryFramesExponentsKernel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotDict

open GlobalTheory.ChainFr

theorem gBig_three {P Q R S : GP} (hP : GBig P) (hQ : GBig Q) (hR : GBig R)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → Q G μ₀ C x b → R G μ₀ C x b → S G μ₀ C x b) : GBig S := by
  obtain ⟨CF1, h1⟩ := hP
  obtain ⟨CF2, h2⟩ := hQ
  obtain ⟨CF3, h3⟩ := hR
  refine ⟨max CF1 (max CF2 CF3), fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, g1⟩ := h1 ε CF ((le_max_left _ _).trans hCF)
  obtain ⟨C2, x2, g2⟩ := h2 ε CF (((le_max_left _ _).trans (le_max_right _ _)).trans hCF)
  obtain ⟨C3, x3, g3⟩ := h3 ε CF (((le_max_right _ _).trans (le_max_right _ _)).trans hCF)
  refine ⟨max C1 (max C2 C3), max x1 (max x2 x3), fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ ?_ ?_ ?_⟩
  · exact g1 C ((le_max_left _ _).trans hC) D large₂ he ((le_max_left _ _).trans hx) hr T Lc μ₀ hμ G
  · exact g2 C (((le_max_left _ _).trans (le_max_right _ _)).trans hC) D large₂ he
      (((le_max_left _ _).trans (le_max_right _ _)).trans hx) hr T Lc μ₀ hμ G
  · exact g3 C (((le_max_right _ _).trans (le_max_right _ _)).trans hC) D large₂ he
      (((le_max_right _ _).trans (le_max_right _ _)).trans hx) hr T Lc μ₀ hμ G

theorem bottom_dictionary : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ), (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) ∧ (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0) ∧ (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) ∧ ∀ t : T, IsTriple A A' WW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧ (∀ τ, HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ)) ∧ IsFinF W.ψ W.θ true FA FW (X.f t) ∧ IsFinF W.ψ W.θ false FA' FW (X.f' t) ∧ (∀ P g h, thetaKO (X.ω t) g h (fockF W.ψ W.θ true FA FW (X.f t) P) = X.ker W.ψ W.θ t P h g) ∧ ∀ P g h, thetaKO (X.ω' t) g h (fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.ker' W.ψ W.θ t P h g := by
  refine gBig_three GlobalTheory.T.bottomRanks_arithmetic_largeGrids GlobalTheory.T.exists_bottomInfinityExponents_gap_largeGrids GlobalTheory.T.definiteBottomTriple_finitePlaces_unram_or_split ?_
  intro D T Lc sc G μ₀ C x b _ hsz hinf hram W i j A A' WW X hX
  obtain ⟨a, b, hab⟩ := hinf W i j
  have hs := hX.std
  have hs' := hX.std'
  have hw := hX.stdW
  have hr : WW.rank = SqNum.botBig D i j + SqNum.botSmall D i j := by rw [← hX.is.rank, hX.rank, hX.rank']
  refine ⟨stdFr A hs.1, stdFr A' hs'.1, stdFr WW hw.1, a, b, hasSignature_of_gram_eq_one hs.1,
    hasSignature_of_gram_eq_one hs'.1, hasSignature_of_gram_eq_one hw.1, fun t => ⟨?_, fun τ => ⟨(hab t τ).1, (hab t τ).2.1⟩,
    GlobalTheory.T.seesawTriple_firstFiniteDatum_standard_isVacuumDatum X _ _ _ _ _ _ hs hw hX.is t, GlobalTheory.T.seesawTriple_secondFiniteDatum_standard_isVacuumDatum X _ _ _ _ _ _ hs' hw hX.is t, ?_, ?_⟩⟩
  · refine
      { hecA := (hX.is.weil' t).hecS
        hecB := (hX.is.weil t).hecS
        resA := (hX.is.weil' t).resS
        resB := (hX.is.weil t).resS
        rank := hX.is.rank.symm
        even := by rw [hr]; exact (hsz i j).1
        sig := ⟨0, 0, fun τ => ⟨by simpa using hasSignature_of_gram_eq_one hs.1 τ, by simpa using hasSignature_of_gram_eq_one hs'.1 τ,
          by simpa using hasSignature_of_gram_eq_one hw.1 τ⟩, by rw [hX.rank, hX.rank']; have := (hsz i j).2; omega,
          by rw [hX.rank']; have := (hsz i j).2.2; omega⟩
        gap := fun τ => ⟨a τ, b τ, (hab t τ).1, (hab t τ).2.1, by rw [hr]; exact (hab t τ).2.2⟩
        ram := hram W i j A A' WW X hX t }
  · intro P g h
    have e1 : (GlobalTheory.SquareComm.frSgn true (stdFr A hs.1)).cart = fun τ => -X.rA.s τ :=
      funext fun τ => by rw [cart_frSgn_true_stdFr, (hs.2.2 τ).1]
    have e2 : (stdFr WW hw.1).cart = X.rW.s := funext fun τ => by rw [cart_stdFr, (hw.2.2 τ).1]
    have e3 : (stdFr A hs.1).onb = X.rA.B := funext fun τ => by rw [onb_stdFr, (hs.2.2 τ).2]
    have e4 : (stdFr WW hw.1).onb = X.rW.B := funext fun τ => by rw [onb_stdFr, (hw.2.2 τ).2]
    unfold GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker
    rw [e1, e2, e3, e4]
  · intro P g h
    have e1 : (GlobalTheory.SquareComm.frSgn false (stdFr A' hs'.1)).cart = X.rA'.s :=
      funext fun τ => by rw [cart_frSgn_false_stdFr, (hs'.2.2 τ).1]
    have e2 : (stdFr WW hw.1).cart = X.rW.s := funext fun τ => by rw [cart_stdFr, (hw.2.2 τ).1]
    have e3 : (stdFr A' hs'.1).onb = X.rA'.B := funext fun τ => by rw [onb_stdFr, (hs'.2.2 τ).2]
    have e4 : (stdFr WW hw.1).onb = X.rW.B := funext fun τ => by rw [onb_stdFr, (hw.2.2 τ).2]
    unfold GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker'
    rw [e1, e2, e3, e4]
    rfl

end GlobalTheory.BotDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomDictionaryFramesExponentsKernelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottom_dictionary_frames_exponents_kernel : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ), (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) ∧ (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0) ∧ (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) ∧ ∀ t : T, IsTriple A A' WW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧ (∀ τ, HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ)) ∧ IsFinF W.ψ W.θ true FA FW (X.f t) ∧ IsFinF W.ψ W.θ false FA' FW (X.f' t) ∧ (∀ P g h, thetaKO (X.ω t) g h (fockF W.ψ W.θ true FA FW (X.f t) P) = X.ker W.ψ W.θ t P h g) ∧ ∀ P g h, thetaKO (X.ω' t) g h (fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.ker' W.ψ W.θ t P h g := by
  first | exact @GlobalTheory.BotDict.bottom_dictionary | exact GlobalTheory.BotDict.bottom_dictionary | (intros; apply GlobalTheory.BotDict.bottom_dictionary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqNsmulOfActs
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo

theorem actG_mem_laHat {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N : ℕ} {g : G.GAf}
    (hg : g ∈ L.KN N) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) : L.actG g v ∈ LaHat D := by
  obtain ⟨w, hw, e⟩ := hg.1 v hv
  rw [e]
  exact add_mem hv (nsmul_mem hw N)

end GlobalTheory.LKGeo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroConstantFirst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotClassSumSmall

open scoped ComplexOrder


open GlobalTheory.DefiniteClassAvg in
theorem openCompact {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (hstd : X.rA'.IsStd) :
    IsOpen (((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) ∧
    IsCompact (((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
  have hJo : IsOpen (((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ A' X.rA'.β ∅] with κ h1
    exact h1.2.1
  have hV : ∀ φ : D.host.E →+* ℂ, (A'.gram.map φ).PosDef := fun φ => by
    rw [hstd.1, Matrix.map_one φ (map_zero φ) (map_one φ)]
    exact Matrix.PosDef.one
  let V' : HSp D := { A' with sig := fun _ => (A'.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC A' : Set (GA D A')) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  have hLc : IsCompact ((Lev.levA A' (Formalism.L2.DIV.St X.rA'.β) : Subgroup (GA D A')) : Set (GA D A')) := by
    obtain ⟨C, hC, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact A' X.rA'.β
    refine hC.of_isClosed_subset ((GlobalTheory.Ker.CongTop.isClosed_GfC A').inter
      (Subgroup.isClosed_of_isOpen _ hJo)) fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
    exact hCm k hk1 hk2
  refine ⟨hJo, (hLc.mul hGc).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hJo) ?_⟩
  intro k hk
  exact ⟨finPart A' k, finPart_mem_levA A' hk, realPart A' k, realPart_mem A' k, finPart_mul_realPart A' k⟩


end GlobalTheory.BotClassSumSmall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOnOpenCuspIso
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp.Sandwich

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {TF : TorFlag Xo c} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {P : WtPar Dw} (R : Choice TF.X Z U P)

theorem restr_mulPole (j : ℕ) (f : H0 R.str (R.adj j) ⊤) :
    H0.restr le_top (R.mulPole j ⊤ f) = R.mulPole j R.off (H0.restr le_top f) :=
  (ProdChart.restr_mul _ _ _ _).trans (by rw [H0.restr_ofSec]; rfl)

theorem mulPole_injective (h₁ : FreeOnOpen TF.X Z U P.u₁) (j : ℕ) : Function.Injective (R.mulPole j R.off) :=
  ((R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).mulEquiv (R.Δ₁.nowhereZero_pow R.str (R.notMem_support h₁) j)).injective

theorem nowhereZero_pow_zero : NowhereZero (H0.ofSec R.str ⊤ (R.Δ₁.pow 0)) := nowhereZero_of_exists fun y hy => by
  obtain ⟨i, hi⟩ := exists_chart R.Δ₁.isLB y
  exact ⟨fun _ => i, mem_zpow_U.2 hi, by rw [R.Δ₁.germ_pow R.str 0 i y hy hi, pow_zero]; exact isUnit_one⟩

end GlobalTheory.HSApp.Sandwich


open GlobalTheory.HSApp.Sandwich in
theorem GlobalTheory.HSApp.sandwich : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice TF.X Z U P)
    (ω : CanId R.toModif), FnAlgClosed (Xo := Xo) (c := c) → ∀ h₁ : FreeOnOpen TF.X Z U P.u₁,
    (∀ j, CuspIso TF.X Z U (P.wt j) → adjGlobal R j ≤ LinearMap.range (adjSec R ω h₁ j)) ∧
    (CuspIso TF.X Z U (P.wt 0) → LinearMap.range (adjSec R ω h₁ 0) ≤ adjGlobal R 0) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z r U P R ω hF h₁
  have key := fun (j : ℕ) m => GlobalTheory.T.canonical_ideal_weight_section hP hG E H Dw l Xo c TF Z hF R.toModif ω _ _ (P.kap_add j) m
  refine ⟨fun j hj => ?_, fun hj => ?_⟩
  · rintro _ ⟨f, rfl⟩
    let e := R.adjEquiv ω.ω ω.unit h₁ j (P.kap_add j)
    obtain ⟨m, hm⟩ := (R.bijective_pullOff (isLB_L₀ TF.X Z (P.wt j))).2 (e.symm (H0.restr le_top f))
    have hmul : H0.restr le_top (R.mulPole j ⊤ f) =
        (((common₀ TF.X Z).pull R.σ).canChart R.K.isLB (P.kap_add j)).mul ω.ω (R.pullOff m) := by
      rw [restr_mulPole, hm]
      have := R.mulPole_adjEquiv ω.ω ω.unit h₁ j (P.kap_add j) (e.symm (H0.restr le_top f))
      rw [LinearEquiv.apply_symm_apply] at this
      exact this
    obtain ⟨g, hg, hgm⟩ := (key j m).2 ⟨R.mulPole j ⊤ f, hmul⟩
    obtain ⟨c', hc'⟩ := hj.2 hg
    refine ⟨c', ?_⟩
    show e (R.pullOff (cuspSec TF.X Z U _ c')) = _
    rw [hc', hgm, hm, LinearEquiv.apply_symm_apply]
  · rintro _ ⟨c', rfl⟩
    obtain ⟨s, hs, hsr⟩ := hj.1 c'
    obtain ⟨g, hg⟩ := (key 0 _).1 ⟨s, hs, hsr⟩
    obtain ⟨f, hf⟩ := ((R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).mulEquiv (nowhereZero_pow_zero R)).surjective g
    refine ⟨f, mulPole_injective R h₁ 0 ?_⟩
    rw [← restr_mulPole, mulPole_adjSec]
    exact (congrArg (H0.restr le_top) hf).trans hg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupSixTermRelationToZpowForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AdjPolLocal
open GlobalTheory.MulPull GlobalTheory.PrimNorm GlobalTheory.PrimNormPol

theorem commGroup_sixTerm_relation_to_zpow_form {G : Type} [CommGroup G] {p q r s t u o : G}
    (h : p * q⁻¹ * r⁻¹ * o = s * t⁻¹ * u⁻¹ * o) :
    p ^ (1 : ℤ) * (q ^ (-1 : ℤ) * (r ^ (-1 : ℤ) * (s ^ (-1 : ℤ) * (t ^ (1 : ℤ) * u ^ (1 : ℤ))))) = 1 := by
  have h' := mul_right_cancel h
  have e : p ^ (1 : ℤ) * (q ^ (-1 : ℤ) * (r ^ (-1 : ℤ) * (s ^ (-1 : ℤ) * (t ^ (1 : ℤ) * u ^ (1 : ℤ))))) =
      (p * q⁻¹ * r⁻¹) * (s * t⁻¹ * u⁻¹)⁻¹ := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  rw [e, h', mul_inv_cancel]

theorem commGroup_sixTerm_zpow_form_to_relation {G : Type} [CommGroup G] {p q r s t u o : G}
    (h : p ^ (1 : ℤ) * (q ^ (-1 : ℤ) * (r ^ (-1 : ℤ) * (s ^ (-1 : ℤ) * (t ^ (1 : ℤ) * u ^ (1 : ℤ))))) = 1) :
    p * q⁻¹ * r⁻¹ * o = s * t⁻¹ * u⁻¹ * o := by
  congr 1
  have e : p ^ (1 : ℤ) * (q ^ (-1 : ℤ) * (r ^ (-1 : ℤ) * (s ^ (-1 : ℤ) * (t ^ (1 : ℤ) * u ^ (1 : ℤ))))) =
      (p * q⁻¹ * r⁻¹) * (s * t⁻¹ * u⁻¹)⁻¹ := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  rw [e, mul_inv_eq_one] at h
  exact h

theorem le_val_one_add_pow_sub {G : Type} [CommGroup G] {D a b : G} (h : 1 = D * (1 * a⁻¹ * b⁻¹ * 1)) : D = a * b := by
  rw [_root_.one_mul, _root_.mul_one, eq_comm, ← mul_inv, mul_inv_eq_one] at h
  exact h

theorem lbIso_of_rosatiAdj_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (f g : B ⟶ B), M.IsLB → RosatiAdj B M f g → LBIso (cubeLB B ![fst B B ≫ f, snd B B] M) (cubeLB B ![fst B B, snd B B ≫ g] M) := by
  intro R _ _ B _ _ M f g hM h
  obtain ⟨U, hU, t, ht⟩ := h (closedPoint R)
  have hall : ∀ p : Sp R, p ∈ U := fun p =>
    Specializes.mem_open ((PrimeSpectrum.le_iff_specializes p (closedPoint R)).1
      (le_maximalIdeal p.2.ne_top)) U.isOpen hU
  have H : KerPow.HasGen M (rosatiφ B f g) rosatiε :=
    KerPow.HasGen.of_range (W := (B ⊗ B).hom ⁻¹ᵁ U) ⟨t, ht⟩ (𝟙 _) (fun y => hall _) (fun k => Category.id_comp _)
  let φ := fun I : ULift (Finset (Fin 2)) => (psum B ![fst B B ≫ f, snd B B] I.down).left
  let ψ := fun I : ULift (Finset (Fin 2)) => (psum B ![fst B B, snd B B ≫ g] I.down).left
  let ε := fun I : ULift (Finset (Fin 2)) => (-1 : ℤ) ^ (2 - I.down.card)
  have hh' : MulPull.HasGen M (Sum.elim ψ φ) (Sum.elim ε fun i => -ε i) := by
    refine (MulPull.HasGen.inv H).of_formEq hM (fun U _ q => ?_)
    rw [Fin.prod_univ_six, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    dsimp [φ, ψ, ε]
    rw [GlobalTheory.NormRos.prod_square, GlobalTheory.NormRos.prod_square]
    dsimp [rosatiφ, rosatiε, padd]
    simp only [zpow_one, zpow_neg_one, inv_inv]
    change (q ((fst B B ≫ f) * snd B B).left)⁻¹ * q (fst B B ≫ f).left *
      q (snd B B).left * q (fst B B * (snd B B ≫ g)).left *
      (q (fst B B).left)⁻¹ * (q (snd B B ≫ g).left)⁻¹ =
      q (fst B B * (snd B B ≫ g)).left * (q (fst B B).left)⁻¹ *
      (q (snd B B ≫ g).left)⁻¹ * q (1 : (B ⊗ B) ⟶ B).left *
      (q ((fst B B ≫ f) * snd B B).left * (q (fst B B ≫ f).left)⁻¹ *
      (q (snd B B).left)⁻¹ * q (1 : (B ⊗ B) ⟶ B).left)⁻¹
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have chart : ChartPull (LB.div (LB.LinComb M ψ ε) (LB.LinComb M φ ε))
      (LB.LinComb M (Sum.elim ψ φ) (Sum.elim ε fun k => -ε k)) (𝟙 _) := by
    have le : ∀ p : (_ → M.ι) × (_ → M.ι), LB.wchart M ψ p.1 ⊓ LB.wchart M φ p.2 ≤
        LB.wchart M (Sum.elim ψ φ) (Sum.elim p.1 p.2) := fun p y hy => Set.mem_iInter.2 fun k => by
      rcases k with k | k
      exacts [Set.mem_iInter.1 hy.1 k, Set.mem_iInter.1 hy.2 k]
    refine { idx := fun p => Sum.elim p.1 p.2, le := le, g := ?_ }
    intro y p q hp hq
    refine (gm_div _ _ (𝟙 _) y p q ⟨hp, hq⟩).trans (Eq.trans ?_
      (gm_linComb M _ _ (𝟙 _) y _ _ (le p hp) (le q hq)).symm)
    refine (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb M ψ ε (𝟙 _) y p.1 q.1 hp.1 hq.1)
      (gm_linComb M φ ε (𝟙 _) y p.2 q.2 hp.2 hq.2)).trans ?_
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rfl
  obtain ⟨v, hv⟩ := hh'
  exact gen_chartPull chart v hv

theorem rosatiAdj_of_lbIso : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (f g : B ⟶ B), M.IsLB → LBIso (cubeLB B ![fst B B ≫ f, snd B B] M) (cubeLB B ![fst B B, snd B B ≫ g] M) → RosatiAdj B M f g := by
  intro S B _ _ M f g hM h
  have H := GlobalTheory.NormRos.exists_gen_rosati hM f g h
  intro s
  exact ⟨⊤, trivial, MulPull.HasGen.pull H ((B ⊗ B).hom ⁻¹ᵁ ⊤).ι⟩

end GlobalTheory.AdjPolLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePsiW0
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiRescale

open GlobalTheory.PsiWZeroPull (prod_four)

section Geometry

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

abbrev FourGen (L : LB A.left) (f : A ⟶ A) : Type :=
  LB.Gen (LB.LinComb L (K := Fin 4) ![(padd A (𝟙 _) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] ![1, -2, -1, 2])

theorem exists_normalised {L : LB A.left} (hL : L.IsLB) (f : A ⟶ A) [IsMonHom f] (u : FourGen L f) (hu : u.IsGen) :
    ∃ u' : FourGen L f, u'.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u' (eSec A)) (LB.oneGen L) := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL
    (φ' := (![(padd A (𝟙 _) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] : Fin 4 → _)) (ε' := ![1, -2, -1, 2])
    (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _ rfl
        (DVR.prod_neg _ _ (prod_four f (1 : A ⟶ A) k))) ?_
      rw [MonObj.one_comp, _root_.mul_one (1 : A ⟶ A)]
      refine mul_eq_left.2 (inv_eq_one.2 ?_)
      group)
    (LB.mulGen L _ _ _ _ u (LB.invGen L _ _ (LB.pullGen L _ _ u (1 : A ⟶ A).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _)))
  refine ⟨t, ht, corr_of_val hL fun y J hJ => ?_⟩
  have e : eSec A ≫ (1 : A ⟶ A).left = eSec A :=
    congrArg (fun q : 𝟙_ (Over S) ⟶ A => q.left) ((MonObj.comp_one (M := A) η[A]).trans (by simp [Hom.one_def]))
  rw [val_pull hJ, val_one, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, Category.assoc, e, mul_inv_cancel]

end Geometry

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

open DVR (cP cPoint_add)

end GlobalTheory.PsiRescale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacNormNeZero
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.NormRatio

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumNorm

theorem vacNorm_ne_zero : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ →
    Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) t0 → ∀ a d : ℕ, vacNorm D cc δ t0 a d ≠ 0 :=
  fun D cc δ t0 hc ht _ _ =>
    pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D (GlobalTheory.InducedType.induced_type D).1 cc δ t0 hc ht)

end GlobalTheory.VacuumNorm
end
