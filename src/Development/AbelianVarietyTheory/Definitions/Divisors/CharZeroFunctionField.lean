module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUnifOfParts
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Cartier

namespace GlobalTheory.VolBr

structure IsBallFam {G : Type} [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G) : Prop where

  subset : ∀ r, B r ⊆ Λ

  zero_mem : ∀ r, 0 ≤ r → (0 : G) ∈ B r

  sub_mem : ∀ r r' x y, x ∈ B r → y ∈ B r' → x - y ∈ B (r + r')

  nsmul_iff : ∀ (n : ℕ) (r : ℝ) (x : G), 0 < n → x ∈ Λ → (n • x ∈ B (n * r) ↔ x ∈ B r)

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

structure Pair (p : X ⟶ Sp k) where

  L : HermLB p

  A : HermLB p

  r : L.B.ι → X.functionFieldˣ

  r' : A.B.ι → X.functionFieldˣ

  hr : IsRatSec L.B r

  hr' : IsRatSec A.B r'

theorem exists_pair (L A : HermLB p) : ∃ P : Pair p, P.L = L ∧ P.A = A := by
  obtain ⟨r, hr⟩ := exists_isRatSec L.isLB
  obtain ⟨r', hr'⟩ := exists_isRatSec A.isLB
  exact ⟨⟨L, A, r, r', hr, hr'⟩, rfl, rfl⟩

namespace Pair

variable (P : Pair p)

def loc (a b : ℤ) (f : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) : X.functionField :=
  f * (P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b

def H (a b : ℤ) : AddSubgroup X.functionField where
  carrier := {f | ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → RegAt x (P.loc a b f i j)}
  zero_mem' x i j _ _ := ⟨0, by simp [loc]⟩
  add_mem' {f g} hf hg x i j hi hj := by
    obtain ⟨u, hu⟩ := hf x i j hi hj
    obtain ⟨v, hv⟩ := hg x i j hi hj
    exact ⟨u + v, by rw [map_add (f := _), hu, hv]; simp only [loc]; ring⟩
  neg_mem' {f} hf x i j hi hj := by
    obtain ⟨u, hu⟩ := hf x i j hi hj
    exact ⟨-u, by rw [map_neg, hu]; simp only [loc]; ring⟩

def nu (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : ℝ :=
  ‖ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y‖ *
    Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2)

def Bl (a b : ℤ) (R : ℝ) : Set X.functionField :=
  {f | f ∈ P.H a b ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y f ≤ R}

def lc (a b : ℤ) (R : ℝ) : ℝ := Real.log ((P.Bl a b R).ncard : ℝ)

def Rep (a b : ℤ) (M : HermLB p) : Prop :=
  ∃ ρ : M.B.ι → X.functionFieldˣ, IsRatSec M.B ρ ∧
    (∀ (x : X) c i j, x ∈ M.B.U c → x ∈ P.L.B.U i → x ∈ P.A.B.U j →
      UnitAt x ((ρ c : X.functionField) / P.loc a b 1 i j)) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ) c i j, y ∈ ptsIn p σ (M.B.U c) → y ∈ ptsIn p σ (P.L.B.U i) →
      y ∈ ptsIn p σ (P.A.B.U j) →
      Real.log ‖ratVal ((ρ c : X.functionField) / P.loc a b 1 i j) y‖ - (M.φ σ).φ c y / 2 =
        -(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2

structure Good (D : ℕ) (b : ℕ) (s t : X.functionField) : Prop where

  ample : IsAmpleLB P.A.B

  nef : P.A.IsNef D

  pos : 0 < b

  s_mem : s ∈ P.Bl 0 1 1

  s_ne : s ≠ 0

  t_mem : t ∈ P.Bl (-1) b 1

  t_ne : t ≠ 0

  reg : ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → ∀ g : X.functionField, RegAt x g →
    RegAt x (g * P.loc (-1) b t i j / P.loc 0 1 s i j) → RegAt x (g / P.loc 0 1 s i j)

end Pair

namespace IntExample

open GlobalTheory.Points GlobalTheory.CechPic

theorem ratVal_nat {σ : k →+* ℂ} (y : CxPts p σ) (n : ℕ) : ratVal (n : X.functionField) y = n := by
  have h : genericPoint X ∈ (⊤ : X.Opens) := trivial
  have e : (n : X.functionField) = fnOf ⊤ h (n : Γ(X, ⊤)) := (map_natCast _ n).symm
  rw [e, ratVal_fnOf mem_ptsIn_top h, ev_eq mem_ptsIn_top, map_natCast]

end IntExample

end GlobalTheory.VolBr
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArithBase GlobalTheory.CechPic

namespace GlobalTheory.ArInt.Model

variable {L M : HermLB (𝟙 (Sp ℤ))} {s t : ℝ}


open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in
private theorem lin_pow_eq_eval_sum_multinomial {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (m : ℕ) (r : ι → ℝ) :
    Ψ (_root_.GlobalTheory.ArInt.lin r ^ m) =
      MvPolynomial.eval r (∑ k ∈ (Finset.univ : Finset ι).piAntidiag m,
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k)
          ((Nat.multinomial Finset.univ k : ℝ) *
            Ψ (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) 1))) := by
  unfold _root_.GlobalTheory.ArInt.lin
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_pow_eq_sum_piAntidiag, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ∏ i, (MvPolynomial.C (r i) * MvPolynomial.X i) ^ k i =
      MvPolynomial.C (∏ i, r i ^ k i) *
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) (1 : ℝ) := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp [mul_pow, Finset.prod_mul_distrib, map_prod]
  rw [hk, MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [← mul_assoc, ← map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial ι ℝ), ← map_mul,
    ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
  simp
  ring

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in
private theorem eq_zero_of_isHomogeneous_of_forall_lin_pow_eq_zero {ι : Type} [Fintype ι]
    (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (m : ℕ)
    (hΨ : ∀ n : ι → ℤ, Ψ (_root_.GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ m) = 0)
    {P : MvPolynomial ι ℝ} (hP : P.IsHomogeneous m) : Ψ P = 0 := by
  classical
  set Q : MvPolynomial ι ℝ := ∑ k ∈ (Finset.univ : Finset ι).piAntidiag m,
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k)
      ((Nat.multinomial Finset.univ k : ℝ) *
        Ψ (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) 1)) with hQdef
  have hQ : Q = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → ℝ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective) fun x hx => ?_
    choose n hn using fun i => hx i (Set.mem_univ i)
    have hxn : x = fun i => (n i : ℝ) := funext fun i => (hn i).symm
    rw [map_zero, hxn, hQdef, ← lin_pow_eq_eval_sum_multinomial, hΨ]
  have hmon : ∀ d : ι →₀ ℕ, (Finsupp.weight 1) d = m →
      Ψ (MvPolynomial.monomial d 1) = 0 := by
    intro d hd
    have hmem : ⇑d ∈ (Finset.univ : Finset ι).piAntidiag m := by
      rw [Finset.mem_piAntidiag]
      refine ⟨?_, fun i _ => Finset.mem_univ i⟩
      rw [← hd, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
      simp
    have hc := congrArg (AddMonoidAlgebra.coeff · d) hQ
    rw [hQdef, MvPolynomial.coeff_sum, Finset.sum_eq_single (⇑d)] at hc
    · rw [Finsupp.equivFunOnFinite_symm_coe, MvPolynomial.coeff_monomial, if_pos rfl,
        MvPolynomial.coeff_zero] at hc
      have hne : (Nat.multinomial Finset.univ ⇑d : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.multinomial_pos _ _).ne'
      exact (mul_eq_zero.mp hc).resolve_left hne
    · intro b _ hb
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro heq
      apply hb
      rw [← heq]
      simp
    · intro h
      exact absurd hmem h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw := hP (MvPolynomial.mem_support_iff.mp hd)
  have hsm : MvPolynomial.monomial d (AddMonoidAlgebra.coeff P d) =
      AddMonoidAlgebra.coeff P d • MvPolynomial.monomial d (1 : ℝ) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul, hmon d hw, smul_zero]


open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in
theorem _root_.GlobalTheory.ArInt.Model.isArFun_unique {k : Type} [CommRing k] {X : Scheme.{0}}
    [IsIntegral X] {p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k} {D E : ℕ} (hX : _root_.GlobalTheory.IsArithVar p E)
    {ι : Type} [Fintype ι] {L : ι → _root_.GlobalTheory.HermLB p}
    {Φ Φ' : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (h : _root_.GlobalTheory.ArInt.IsArFun L D Φ)
    (h' : _root_.GlobalTheory.ArInt.IsArFun L D Φ') :
    Φ = Φ' := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have hpow : ∀ n : ι → ℤ,
      (Φ - Φ') (_root_.GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ (D + 1)) = 0 := by
    intro n
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact _root_.GlobalTheory.HermLB.IsSelfInter.unique hX
      (h1 n) (h1' n)
  have hhom : ∀ (P : MvPolynomial ι ℝ) (d : ℕ), P.IsHomogeneous d → Φ P = Φ' P := by
    intro P d hP
    by_cases hd : d = D + 1
    · subst hd
      exact sub_eq_zero.mp (eq_zero_of_isHomogeneous_of_forall_lin_pow_eq_zero (Φ - Φ') (D + 1) hpow hP)
    · rw [h2 P d hd hP, h2' P d hd hP]
  refine LinearMap.ext fun P => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPolynomial.sum_homogeneousComponent P, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ =>
    hhom _ j (MvPolynomial.homogeneousComponent_isHomogeneous j P)

end GlobalTheory.ArInt.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev DatFn (D : D7) (i : Fin D.R.m) : Type :=
  (∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) → ℂ

abbrev IsWeilTw (χ : (AE D)ˣ →* Circle) (ω : WeilRep D i) : Prop :=
  IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1
    (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ω


open Classical in
def VecOf (Q : Finset (Pl D.host.E)) (Ω : DatFn D i) (φ : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsVacO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.vacP i) ∧
    ∃ e : AE D, IsIdemSum e (R.Pg ∪ Q) ∧
      IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D e)
        (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i)
        (fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
          Ω (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) φ


open Classical in
def PhiOf (Q : Finset (Pl D.host.E)) (Ω : DatFn D i) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (N : Submodule (𝓞 D.host.E) La)
    (φ : (Fin (Vc D i).rank → La ⧸ N) → ℂ) : Prop :=
  ∃ e : AE D, IsIdemSum e (R.Pg ∪ Q) ∧ ∀ x : Fin (Vc D i).rank → La,
    IsIntM (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b)) ∧
    φ (fun b => Submodule.Quotient.mk (x b)) =
      Ω (fun PP => redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b)))

def ReadsOnly {i : Fin D.R.m} (S : Finset (Pl D.host.E)) (Ω : DatFn D i) : Prop :=
  ∀ y y', (∀ PP ∈ S, y PP = y' PP) → Ω y = Ω y'


open Classical in
def omegaFree (Q : Finset (Pl D.host.E)) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) : DatFn D i := fun y =>
  (if ∀ PP ∈ R.Pg, y PP = y₀ PP then 1 else 0) *
    if h : ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (y PP)).det then ∏ PP ∈ Q.attach, (((ξR PP.1 (h PP.1 PP.2).unit)⁻¹ : ℂˣ) : ℂ) else 0

structure KerDat (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ) : Prop where
  chr : ChrEq χ ξ
  fin : ∃ n : ℕ, 0 < n ∧ ξ.OrderDvd n
  triv : ξ.TrivOn D.host.F
  tame : ∀ v, ξ.TameAt v
  pl : IsTwistPlaces D.host.g Q
  off : ∀ PP ∈ Q, ((D.host.QS * D.host.q * D.host.d * D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal
  ram : ∀ PP, ¬ ξ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, Lev.IsConjPl PP' PP
  res : ∀ PP ∈ Q, IsRes ξ PP (ξR PP)
  weil : IsWeilTw R i χ ω
  vec : IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
    R.Pg Q ξR (R.vacP i) φ

variable {R i}

theorem KerDat.isKernel {ξ χ ξR Q ω φ} (h : KerDat R i ξ χ ξR Q ω φ) : IsKernel R i ξ Q ω φ :=
  ⟨χ, ξR, h.chr, h.res, h.weil, h.vec⟩

theorem KerDat.vecOf {ξ χ ξR Q ω φ} (h : KerDat R i ξ χ ξR Q ω φ) :
    VecOf R i Q (fun y => omegaK R.Pg y * omegaQ Q (Wc D i).rank ξR (-1) y) φ := h.vec

theorem kerDat_tuple (hL : R.toLevCh.Is A.μ0) (hP : R.IsThP) (t : T0) :
    KerDat R i (R.xiH t) (R.xi t) (R.xiR t) (R.Q t) (R.ωP i t) (R.vP i t) :=
  ⟨hL.xi t, hL.xi_fin t, hL.xi_triv t, hL.xi_tame t, hL.Q_pl t, fun PP h => (hL.Q_off t PP h).1, hL.Q_ram t, hL.xiR t,
    hP.ωP i t, hP.vP i t⟩

end GlobalTheory.OnCmp

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

variable (F : Type) [Field F] [NumberField F] [IsCMField F]

structure Datum where
  bar : 𝓞 F ≃+* 𝓞 F
  bar_eq : ∀ a : 𝓞 F, ((bar a : 𝓞 F) : F) = IsCMField.complexConj F (a : F)
  w : 𝓞 F
  w_add : w + bar w = 1
  La : Type
  [acg : AddCommGroup La]
  [mod : Module (𝓞 F) La]
  fin : Module.Finite (𝓞 F) La
  proj : Module.Projective (𝓞 F) La
  n : ℕ
  rank : Module.finrank (𝓞 F) La = n
  EF : LinearMap.BilinForm ℤ La
  alt : ∀ x, EF x x = 0
  unimod : Function.Bijective EF
  adj : ∀ (a : 𝓞 F) x y, EF (a • x) y = EF x (bar a • y)
  sig : (F →+* ℂ) → ℕ
  sig_conj : ∀ τ, sig τ + sig ((starRingEnd ℂ).comp τ) = n
  dom : ∃ J : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La, (∀ x, J (J x) = -x) ∧
    (∀ x y, EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < EF.baseChange ℝ (J x) x) ∧
    ∀ (a : 𝓞 F) (A : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La), (∀ x : La, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) →
      J ∘ₗ A = A ∘ₗ J ∧
      LinearMap.trace ℝ _ A = 2 * (∑ τ : F →+* ℂ, (sig τ : ℂ) * τ (a : F)).re ∧
      LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * (∑ τ : F →+* ℂ, (sig τ : ℂ) * τ (a : F)).im

attribute [instance] Datum.acg Datum.mod

variable {F}

def Datum.reflex (D : Datum F) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range fun a : F => ∑ τ : F →+* ℂ, (D.sig τ : ℂ) * τ a)

def Datum.OEp (D : Datum F) (p : ℕ) : Subring ℂ :=
  Subring.closure ({x | x ∈ D.reflex ∧ IsIntegral ℤ x} ∪ {x | ∃ m : ℕ, m.Coprime p ∧ x = (m : ℂ)⁻¹})

def ZbarP (p : ℕ) : Subring ℂ :=
  Subring.closure ({x : ℂ | IsIntegral ℤ x} ∪ {x | ∃ m : ℕ, m.Coprime p ∧ x = (m : ℂ)⁻¹})

theorem OEp_le (D : Datum F) (p : ℕ) : D.OEp p ≤ ZbarP p :=
  Subring.closure_mono (Set.union_subset_union (fun _ hx => hx.2) le_rfl)

def embP (p : ℕ) (τ : F →+* ℂ) (a : 𝓞 F) : ZbarP p :=
  ⟨τ (a : F), Subring.subset_closure (Or.inl ((NumberField.RingOfIntegers.isIntegral_coe a).map τ.toIntAlgHom))⟩

variable {S : Scheme.{0}}


open Classical in
def DetCondP (D : Datum F) (p : ℕ) {k : Type} [Field k] {G : Over S} [GrpObj G] (act : OAct (𝓞 F) G)
    (x : Sp k ⟶ S) (β : D.OEp p →+* k) : Prop :=
  ∃ β' : ZbarP p →+* k, (∀ y : D.OEp p, β' (Subring.inclusion (OEp_le D p) y) = β y) ∧
    ∀ σ : 𝓞 F →+* k, LieMult act x σ
      (∑ τ ∈ (Finset.univ.filter fun τ : F →+* ℂ => ∀ a, β' (embP p τ a) = σ a), D.sig τ)

structure TateIsoP (D : Datum F) (p : ℕ) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 F → Q → Q)
    (e : ℕ → Q → Q → kˣ → Prop) where
  ζ : ℕ → kˣ
  ζ_prim : ∀ n, 0 < n → n.Coprime p → IsPrimitiveRoot (ζ n) n
  ζ_pow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ζ (n * m) ^ m = ζ n
  ev : ℕ → D.La → Q
  add : ∀ n a b, ev n (a + b) = ev n a * ev n b
  lin : ∀ n (c : 𝓞 F) a, ev n (c • a) = act c (ev n a)
  ker : ∀ n, 0 < n → n.Coprime p → ∀ a, ev n a = 1 ↔ ∃ b, a = n • b
  onto : ∀ n, 0 < n → n.Coprime p → ∀ x, x ^ n = 1 ↔ ∃ a, ev n a = x
  tower : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ∀ a, ev (n * m) a ^ m = ev n a
  isom : ∀ n, 0 < n → n.Coprime p → ∀ a b, e n (ev n a) (ev n b) (ζ n ^ D.EF a b)

structure Obj (D : Datum F) (p N : ℕ) (s : S ⟶ Sp (D.OEp p)) where
  A : Over S
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  act : OAct (𝓞 F) A
  PP : RigLB A
  cub : CubicalStr A PP
  sym : PP.IsSymmetric
  adj : ∀ a, LBIso (cubeLB A ![fst A A ≫ act.act a, snd A A] PP.L)
    (cubeLB A ![fst A A, snd A A ≫ act.act (D.bar a)] PP.L)
  prim : LBIso PP.L (cubeLB A ![𝟙 A, act.act D.w] PP.L)
  ample : Out.RelAmple A PP.L
  ktriv : Out.KTriv A PP.L
  eta : D.La → (𝟙_ (Over S) ⟶ A)
  eta_add : ∀ a c, eta (a + c) = eta a * eta c
  eta_ker : ∀ a, eta (N • a) = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : D.OEp p →+* k), x ≫ s = spMap β →
    DetCondP D p act x β ∧
    ∃ I : TateIsoP D p k (Over.mk x ⟶ A) (fun a g => g ≫ act.act a)
        (fun n g g' c => Out.WeilIs A PP.L n g g' (unitOn c)),
      ∀ a, toUnit _ ≫ eta a = I.ev N a

attribute [instance] Obj.grp Obj.comm

structure ObjMap {D : Datum F} {p N : ℕ} {S' : Scheme.{0}} {s' : S' ⟶ Sp (D.OEp p)} {s : S ⟶ Sp (D.OEp p)}
    (o' : Obj D p N s') (o : Obj D p N s) (f : S' ⟶ S) where
  φ : o'.A.left ⟶ o.A.left
  cart : IsGrpPullback o'.A o.A f φ
  act : ∀ a, (o'.act.act a).left ≫ φ = φ ≫ (o.act.act a).left
  pol : LBIso o'.PP.L (o.PP.L.pull φ)
  eta : ∀ a, (o'.eta a).left ≫ φ = f ≫ (o.eta a).left

def Datum.dim (D : Datum F) : ℕ := (∑ τ : F →+* ℂ, D.sig τ * (D.n - D.sig τ)) / 2

structure IntModel (D : Datum F) (p N : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp (D.OEp p)
  qproj : IsQProjOver s
  smooth : SmoothOfRelativeDimension D.dim s
  univ : Obj D p N s
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (D.OEp p)), IsReduced S → ∀ o : Obj D p N s',
    ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (ObjMap o univ f)
  unram : ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ X) (o : Obj D p N (x ≫ s)),
    Nonempty (ObjMap o univ x) → Nonempty (ObjMap o univ (constPt x)) → x = constPt x

def Good (F : Type) [Field F] [NumberField F] (p N : ℕ) : Prop :=
  p.Prime ∧ ¬ (p : ℤ) ∣ NumberField.discr F ∧ 3 ≤ N ∧ N.Coprime p

def Datum.Definite (D : Datum F) : Prop := ∃ τ : F →+* ℂ, D.sig τ = 0

section Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem conj_mem_type_iff (H : Host E) (τ : E →+* ℂ) :
    ((starRingEnd ℂ).comp τ) (H.rt : E) = H.rt0 ↔ ¬ τ (H.rt : E) = H.rt0 := by
  have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  have h0 : H.rt0 ≠ 0 := fun h1 => hd (by have h2 := H.sqrt_neg_disc_sq; rw [h1] at h2; linear_combination h2)
  have hsq : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by rw [← map_pow, HostModel.coe_rt_sq, H.sqrt_neg_disc_sq]; simp
  rw [RingHom.comp_apply, HostModel.conj_embedding_rt]
  constructor
  · intro h h'
    rw [h'] at h
    exact h0 (by linear_combination (-1 / 2 : ℂ) * h)
  · intro h
    rw [(sq_eq_sq_iff_eq_or_eq_neg.mp hsq).resolve_left h, neg_neg]


open Classical in
theorem sum_mult_eq (D : Geo.Tor.Datum H) (a : E) :
    ∑ τ : E →+* ℂ, (D.mult τ : ℂ) * τ a =
      ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
        ((D.p : ℂ) * τ a + (D.q : ℂ) * starRingEnd ℂ (τ a)) := by
  rw [Finset.sum_add_distrib,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  congr 1
  · refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [Geo.Tor.Datum.mult, if_pos (Finset.mem_filter.1 hτ).2]
  · refine Finset.sum_nbij' (fun τ => (starRingEnd ℂ).comp τ) (fun τ => (starRingEnd ℂ).comp τ) ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      exact (conj_mem_type_iff H τ).2 hτ
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      exact fun h => (conj_mem_type_iff H τ).1 h hτ
    · intro τ _; ext x; simp
    · intro τ _; ext x; simp
    · intro τ hτ
      rw [Geo.Tor.Datum.mult, if_neg (Finset.mem_filter.1 hτ).2]
      simp

@[reducible] def Datum.ofHost (D : Geo.Tor.Datum H) : Datum E where
  bar := H.bar
  bar_eq := H.bar_eq
  w := H.w0
  w_add := by rw [HostModel.cmHost_bar_halfIntegerGenerator]; ring
  La := D.La
  fin := D.fin
  proj := D.proj
  n := D.p + D.q
  rank := D.rank
  EF := D.EF
  alt := D.alt
  unimod := D.unimod
  adj := D.adj
  sig := D.mult
  sig_conj τ := by
    unfold Geo.Tor.Datum.mult
    by_cases h : τ (H.rt : E) = H.rt0
    · rw [if_pos h, if_neg fun h' => (conj_mem_type_iff H τ).1 h' h]
    · rw [if_neg h, if_pos ((conj_mem_type_iff H τ).2 h), add_comm]
  dom := by
    obtain ⟨J, h₁, h₂, h₃, h₄⟩ := D.dom
    exact ⟨J, h₁, h₂, h₃, fun a A hA => h₄ a A _ hA (by convert sum_mult_eq D (a : E))⟩

theorem definite_ofHost_iff (D : Geo.Tor.Datum H) : (Datum.ofHost D).Definite ↔ D.p = 0 ∨ D.q = 0 := by
  obtain ⟨τ₀, h₀⟩ := HostModel.exists_embedding_rt_eq H
  constructor
  · rintro ⟨τ, hτ⟩
    change D.mult τ = 0 at hτ
    unfold Geo.Tor.Datum.mult at hτ
    split_ifs at hτ
    exacts [Or.inl hτ, Or.inr hτ]
  · rintro (h | h)
    · exact ⟨τ₀, (if_pos h₀).trans h⟩
    · exact ⟨(starRingEnd ℂ).comp τ₀, (if_neg fun h' => (conj_mem_type_iff H τ₀).1 h' h₀).trans h⟩


end Host

end GlobalTheory.UPel
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
noncomputable section

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

namespace GlobalTheory.GamMul

section Blocks

variable {R : Type} [CommRing R]


open Classical in
def toGL {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : GL (Fin n) R := if h : IsUnit M then h.unit else 1

end Blocks

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (p q : ℕ) (c : kˣ) : Set (Matrix (Fin p) (Fin q) k) := {X | ∀ i j, valuation k (X i j) ≤ valuation k (c : k)}

end GlobalTheory.GamMul

end
end
