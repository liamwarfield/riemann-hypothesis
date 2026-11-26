module

public import Formalism.LocalRingCardinality.DataKap
public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial

@[expose] public section

section -- merged from Formalism.LocalRingCardinality.DataKerI
open Formalism.MainNotions.G NumberField

noncomputable section

namespace Formalism.BasicNotions

instance factResChar (D : D7) (w : D.what₂.places.Pl) : Fact (D.what₂.places.resChar w).Prime :=
  ⟨D.what₂.places.resChar_prime w⟩

namespace KM

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)

abbrev XZ (Lt : Type) (N0 N1 : ℕ) : Type := (Lt × ℕ × Fin N0) ⊕ (Lt × Fin N0 × Fin N1)

def minorXZ (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) : MvPolynomial (XZ Lt N0 N1) ℤ :=
  Matrix.det (Matrix.of fun i k : Fin p => ∑ a : Fin N0,
    MvPolynomial.X (Sum.inl (s, (i : ℕ), a)) * MvPolynomial.X (Sum.inr (s, a, I k)))

def ColChoice (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def Gxz (nu : Lt → YoungDiagram) (I : ColChoice N1 nu) : MvPolynomial (XZ Lt N0 N1) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), minorXZ N0 N1 s ((nu s).colLen c) (I s c)

def applyAt0 (l : ℕ) [Fact l.Prime] (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  ∑ μ ∈ P.support, MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
    (((AddMonoidAlgebra.coeff P μ : ℤ) : ℂ_[l]) *
      ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) *
      MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th)

def nablaX (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) : MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) =>
    (MvPolynomial.X (s, (i : ℕ), J s c k) : MvPolynomial (Lt × ℕ × Fin N0) ℤ))

end KM

def nuD (D : D7) (u : D.what₂.Word) (i : ℕ) (z : Bool × HH D) : YoungDiagram where
  cells := ((Finset.range (D.R.N i)) ×ˢ (Finset.range ⌈DV.nuRow D u (i + 1) (tauPl D z) 0⌉₊)).filter
    fun x => ∀ r' ≤ x.1, (x.2 : ℝ) < DV.nuRow D u (i + 1) (tauPl D z) r'
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := ha
    have hb1 : b.1 ≤ a.1 := hba.1
    have hb2 : b.2 ≤ a.2 := hba.2
    refine ⟨⟨lt_of_le_of_lt hb1 h1, lt_of_le_of_lt hb2 h2⟩, fun r' hr' => ?_⟩
    exact lt_of_le_of_lt (by exact_mod_cast hb2) (h3 r' (le_trans hr' hb1))

theorem nuD_rows (D : D7) (u : D.what₂.Word) (i : ℕ) (z : Bool × HH D) : (nuD D u i z).colLen 0 ≤ D.R.N i := by
  by_contra hlt
  have hmem : (D.R.N i, 0) ∈ nuD D u i z := YoungDiagram.mem_iff_lt_colLen.2 (not_le.1 hlt)
  have : (D.R.N i, 0) ∈ (nuD D u i z).cells := hmem
  simp only [nuD, Finset.mem_filter, Finset.mem_product, Finset.mem_range, lt_irrefl, false_and] at this

def NuRowOK (D : D7) : Prop :=
  ∀ u i, i < D.R.m → ∀ z r, (((nuD D u i z).rowLen r : ℕ) : ℝ) =
    if r < D.R.N i then DV.nuRow D u (i + 1) (tauPl D z) r else 0

def LevFree {D : D7} (Dx : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) : Prop :=
  D.what₂.places.resChar w ≠ (D.mem u).A.T ∧ D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) ∧
    D.what₂.places.resChar w ∉ Dx.Qp μ


open Classical in
def lamV {p : ℕ} [Fact p.Prime] (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p]) (x : ℂ) : ℂ_[p] :=
  if h : x ∈ algebraicClosure ℚ ℂ then lam ⟨x, h⟩ else 0

structure KerEnt (D : D7) (Dx : DivX D) (Tw : TwForms D) where

  lam : ∀ w : D.what₂.places.Pl, (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]
  iL : ∀ w : D.what₂.places.Pl, D.what₂.LL →+* ℂ_[D.what₂.places.resChar w]
  iL_lam : ∀ w x, iL w x = lamV (lam w) (D.what₂.embLL x)
  iL_int : ∀ w x, x ∈ intW D.what₂.places w ↔ ‖iL w x‖ ≤ 1

  Th : ∀ u μ (w : D.what₂.places.Pl) (i : ℕ), (D.chTw u μ).cls i → (D.chTw u μ).cls (i + 1) →
    MvPowerSeries ((Bool × HH D) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[D.what₂.places.resChar w]

  VQ : ∀ u μ (i : ℕ), (D.chTw u μ).cls i → Type
  [vqAcg : ∀ u μ i c, AddCommGroup (VQ u μ i c)]
  [vqMod : ∀ u μ i c, Module D.what₂.LL (VQ u μ i c)]
  ev : ∀ u μ i c, VQ u μ i c →ₛₗ[D.what₂.embLL] ((D.chTw u μ).Y i → ℂ)
  ev_inj : ∀ u μ i c, Function.Injective (ev u μ i c)

  prS : ∀ u μ (w : D.what₂.places.Pl) (i : ℕ) (c : (D.chTw u μ).cls i), VQ u μ i c →ₛₗ[iL w]
    Module.Dual ℂ_[D.what₂.places.resChar w]
      (MvPolynomial ((Bool × HH D) × ℕ × Fin (D.R.N i)) ℂ_[D.what₂.places.resChar w])

  prT : ∀ u μ (w : D.what₂.places.Pl) (i : ℕ) (c' : (D.chTw u μ).cls (i + 1)), VQ u μ (i + 1) c' →ₛₗ[iL w]
    (KM.ColChoice (D.R.N (i + 1)) (nuD D u i) → ℂ_[D.what₂.places.resChar w])

  prT_val : ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m → ∀ c' (v' : VQ u μ (i + 1) c') I,
    ∃ b : D.what₂.LL, ‖prT u μ w i c' v' I‖ = ‖iL w b‖

  lat_S : ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m → ∀ φ : (D.chTw u μ).cls i → (D.chTw u μ).Y i → ℂ,
    (∃ x ∈ locW D.what₂.places w ((Tw.fm u μ).lat i).L, (Tw.fm u μ).emb i x = φ) ↔
      (φ ∈ (Tw.fm u μ).Fi i ∧ ∀ c, ∃ v : VQ u μ i c, ev u μ i c v = φ c ∧
        ∀ J : KM.ColChoice (D.R.N i) (nuD D u i),
          ‖prS u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX (D.R.N i) (nuD D u i) J))‖ ≤ 1)

  levelFree_lattice_condition : ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m →
    ∀ φ : (D.chTw u μ).cls (i + 1) → (D.chTw u μ).Y (i + 1) → ℂ,
    (∃ y ∈ locW D.what₂.places w ((Tw.fm u μ).lat (i + 1)).L, (Tw.fm u μ).emb (i + 1) y = φ) ↔
      (φ ∈ (Tw.fm u μ).Fi (i + 1) ∧ ∀ c', ∃ v' : VQ u μ (i + 1) c', ev u μ (i + 1) c' v' = φ c' ∧
        ∀ I, ‖prT u μ w i c' v' I‖ ≤ 1)

  un : ∀ u μ (w : D.what₂.places.Pl) (i : ℕ), (D.chTw u μ).cls i → (D.chTw u μ).cls (i + 1) → ℂ_[D.what₂.places.resChar w]
  un_ne : ∀ u μ w i c c', un u μ w i c c' ≠ 0

  kform : ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1))
    (v : VQ u μ i c) (v' : VQ u μ (i + 1) c'),
    ev u μ (i + 1) c' v' = (D.chTw u μ).Kmap i c c' (ev u μ i c v) →
    ∀ I, prT u μ w i c' v' I =
      un u μ w i c c' *
        prS u μ w i c v (KM.applyAt0 (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (Th u μ w i c c')
          (KM.Gxz (D.R.N i) (D.R.N (i + 1)) (nuD D u i) I))

attribute [instance] KerEnt.vqAcg KerEnt.vqMod

namespace KerEnt

variable {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw)

def UnUnit : Prop :=
  ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m → ∀ c c', ‖E.un u μ w i c c'‖ = 1

def valS (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c : (D.chTw u μ).cls i) :
    Set ((D.chTw u μ).Y i → ℂ) :=
  E.ev u μ i c '' {v | ∀ J : KM.ColChoice (D.R.N i) (nuD D u i),
    ‖E.prS u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX (D.R.N i) (nuD D u i) J))‖ ≤ 1}

end KerEnt

def linAt {σ κ : Type*} [Fintype κ] {p : ℕ} [Fact p.Prime] (c : σ → κ → ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries κ ℂ_[p] :=
  MvPowerSeries.subst (fun k : σ => ∑ x : κ, algebraMap ℂ_[p] (MvPowerSeries κ ℂ_[p]) (c k x) * MvPowerSeries.X x) F

def posJ {D : D7} (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : Fills (D.gat u w h)) :
    (j : ℕ) → ((Σ v : Fin (Fl.Pj j).nV, Fin ((Fl.Pj j).n' v)) ≃ D.what₂.Tau)
  | 0 => Gt.gat_pos u w h
  | _ + 1 => Gt.gat_pos u w h

def rhoMat {D : D7} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    {Ch : Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch) (j : ℕ) (τ : D.what₂.Tau)
    (g : ∀ v, Matrix (Fin ((Fl.Pj j).m + 1)) (Fin ((Fl.Pj j).m + 1)) ((Fl.Pj j).Qq v)) :
    Matrix (Fin ((Fl.Pj j).m + 1)) (Fin ((Fl.Pj j).m + 1)) ℂ_[D.what₂.places.resChar w] :=
  (g ((posJ Gt u w h Fl j).symm τ).1).map fun y =>
    Kp.iK ((Fl.Pj j).ι ((posJ Gt u w h Fl j).symm τ).1
      ((((Fl.Pj j).σ ((posJ Gt u w h Fl j).symm τ).1) ^ ((posJ Gt u w h Fl j).symm τ).2.val) y))


open Classical in
def ThAtServed {D : D7} {Dx : DivX D} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word}
    {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)}
    {Lv : Levels Fl} {Ch : Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch) (E : KerEnt D Dx Tw) : Prop :=
  Kp.lam = E.lam w ∧
  ∃ g : ∀ (j : ℕ) (_ : Lv.comp j × (Fl.Pj j).Tup) (v : Fin (Fl.Pj j).nV),
      Matrix (Fin ((Fl.Pj j).m + 1)) (Fin ((Fl.Pj j).m + 1)) ((Fl.Pj j).Qq v),
    (∀ j, j ≤ D.R.m → ∀ La : Lv.comp j × (Fl.Pj j).Tup, (Fl.Pj j).IsLatTup La.2 →
      ∀ v, IsUnit (g j La v).det ∧ La.2 v = colSpan ((Fl.Pj j).W v) (g j La v)) ∧
    ∀ j, j < D.R.m → ∀ (hN : (Fl.Pj j).m + 1 = D.R.N j) (hN' : (Fl.Pj (j + 1)).m + 1 = D.R.N (j + 1))
      (La : Lv.comp j × (Fl.Pj j).Tup) (La' : Lv.comp (j + 1) × (Fl.Pj (j + 1)).Tup),
      (Fl.Pj j).IsLatTup La.2 → (Fl.Pj (j + 1)).IsLatTup La'.2 →
      ∃ c0 : D.what₂.Tau → ℂ_[D.what₂.places.resChar w], (∀ τ, ‖c0 τ‖ = 1) ∧
        E.Th u (D.what₂.muAt w) w j (Kp.cls j La.1 La.2) (Kp.cls (j + 1) La'.1 La'.2) =
          linAt (fun (k : D.what₂.Tau × Fin ((Fl.Pj (j + 1)).m + 1) × Fin ((Fl.Pj j).m + 1))
              (x : (Bool × HH D) × Fin (D.R.N j) × Fin (D.R.N (j + 1))) =>
            if tauPl D x.1 = k.1 then
              (if IsTypeV ((posJ Gt u w h Fl j).symm k.1).2 then
                c0 k.1 * (rhoMat Kp (j + 1) k.1 (g (j + 1) La')) k.2.1 (Fin.cast hN'.symm x.2.2) *
                  ((rhoMat Kp j k.1 (g j La))⁻¹) (Fin.cast hN.symm x.2.1) k.2.2
              else
                c0 k.1 * (((rhoMat Kp (j + 1) k.1 (g (j + 1) La'))⁻¹).transpose) k.2.1 (Fin.cast hN'.symm x.2.2) *
                  ((rhoMat Kp j k.1 (g j La)).transpose) (Fin.cast hN.symm x.2.1) k.2.2)
            else 0) (Kp.Th j La La')

end Formalism.BasicNotions
end
end

section -- merged from Formalism.LocalRingCardinality.NFLeTwoMulTSq
namespace Formalism.BasicNotions

theorem ParamsT.nV_eq {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    D.R.nV = T.TO * T.nWn + (8 * D.R.f * D.R.r + 4) := by
  have h1 := T.split
  have h2 := T.nP_eq
  unfold Ranks.nV
  omega

theorem ParamsT.nV_ge {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    8 * D.R.f * D.R.r + 4 ≤ D.R.nV := by
  rw [T.nV_eq]; exact Nat.le_add_left _ _

end Formalism.BasicNotions
end

section -- merged from Formalism.LocalRingCardinality.KernelPlaceMeanBound
noncomputable section

namespace Formalism.BasicNotions.DV

open Formalism.BasicNotions

def logHook (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, Real.log (Real.Gamma (a i + n - i))) -
    ∑ i ∈ Finset.range n, ∑ l ∈ Finset.Ioo i n, Real.log (a i - a l + l - i)

def Lprime (D : D7) (L : SizeData₂ D) : ℝ :=
  Real.log (L.sc.b * D.host.rdE * ((D.host.g 0 : ℝ) * D.host.g 1) * D.R.nV)

def L6lo (D : D7) (L : SizeData₂ D) (C : ℝ) (j : ℕ) : ℝ :=
  (∑ ρ : D.what₂.Tau, logHook (D.R.sigW j).1 (aPlus D j ρ)) -
    C * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lprime D L

def kernelPlaceMeanBound (D : D7) (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) (j : ℕ) : ℝ :=
  (∑ ρ : D.what₂.Tau, kerPlace D L u j ρ) +
    C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La +
    C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * L.sc.L

def hExpl6 (D : D7) (L : SizeData₂ D) (X : DivX D) (C : ℝ) (u : D.what₂.Word) : ℝ :=
  SZbP D L C u + (∑ j ∈ SizeData₂.lifts D, kernelPlaceMeanBound D L C u j) - (∑ j ∈ SizeData₂.lifts D, L6lo D L C j) -
    meanE D (fun e => Real.log (X.kapR e))

end Formalism.BasicNotions.DV

end
end

section -- merged from Formalism.LocalRingCardinality.MinkMEqMinkowskiNumber
namespace Formalism.BasicNotions

open Formalism.HermitianLatticeCounting.S6 (minkowskiM minkowskiExp)

theorem minkM_pos (n : ℕ) : 0 < minkM n :=
  Finset.prod_pos fun _ hp => pow_pos (Finset.mem_filter.1 hp).2.pos _

theorem minkM_dvd_factorial (n : ℕ) : minkM n ∣ (2 * n).factorial := Formalism.HermitianLatticeCounting.P.minkowski_number_dvd_factorial n

theorem log_minkM_le_two (n : ℕ) : Real.log (minkM n : ℝ) ≤ 2 * n * Real.log (2 * n) := by
  have h1 : minkM n ≤ (2 * n) ^ (2 * n) :=
    (Nat.le_of_dvd (Nat.factorial_pos _) (minkM_dvd_factorial n)).trans (Nat.factorial_le_pow _)
  have h2 : (minkM n : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ (2 * n) := by exact_mod_cast h1
  have h3 : (0 : ℝ) < minkM n := by exact_mod_cast minkM_pos n
  have h4 := Real.log_le_log h3 h2
  rw [Real.log_pow] at h4
  push_cast at h4
  exact h4

theorem Ranks.two_le_fN (R : Ranks) : 2 ≤ R.f * R.N R.m := by
  have hf : 2 ≤ R.f := by
    have h1 := R.two_le_m
    have h2 := R.m_le_f
    unfold Ranks.f Ranks.n; omega
  have hN : 1 ≤ R.N R.m := by
    have h1 := R.k_ge
    have h2 : R.k ≤ R.N R.m := Nat.le_add_right _ _
    omega
  calc 2 = 2 * 1 := rfl
    _ ≤ R.f * R.N R.m := Nat.mul_le_mul hf hN

theorem DGamMink.mem {D : D7} (h : DGamMink D) (hD : DGamDef D) (u : D.what₂.Word) :
    (D.mem u).C.DGam = minkM (2 * D.R.f * D.R.N D.R.m) := by
  rw [← hD.one u D.u₀ D.what₂.mu0, hD.one D.u₀ D.u₀ D.what₂.mu0]; exact h

theorem DGamMink.fact {D : D7} (h : DGamMink D) (hD : DGamDef D) : FactDGam D 12 := by
  intro u
  rw [h.mem hD u]
  have hy : (2 : ℝ) ≤ (D.R.f : ℝ) * D.R.N D.R.m := by exact_mod_cast D.R.two_le_fN
  have h1 := log_minkM_le_two (2 * D.R.f * D.R.N D.R.m)
  have e : ((2 * D.R.f * D.R.N D.R.m : ℕ) : ℝ) = 2 * ((D.R.f : ℝ) * D.R.N D.R.m) := by push_cast; ring
  rw [e] at h1
  have e2 : (2 : ℝ) * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) = 2 * 2 * ((D.R.f : ℝ) * D.R.N D.R.m) := by ring
  have h2 : Real.log (2 * (2 * ((D.R.f : ℝ) * D.R.N D.R.m))) =
      Real.log 2 + Real.log 2 + Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := by
    rw [e2, Real.log_mul (by norm_num) (by linarith), Real.log_mul (by norm_num) (by norm_num)]
  have h3 : Real.log 2 ≤ Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := Real.log_le_log (by norm_num) hy
  rw [h2] at h1
  have h4 : 2 * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) * (Real.log 2 + Real.log 2 + Real.log ((D.R.f : ℝ) * D.R.N D.R.m)) ≤
      2 * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) * (3 * Real.log ((D.R.f : ℝ) * D.R.N D.R.m)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  calc Real.log (minkM (2 * D.R.f * D.R.N D.R.m) : ℝ)
      ≤ 2 * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) * (3 * Real.log ((D.R.f : ℝ) * D.R.N D.R.m)) := h1.trans h4
    _ = 12 * D.R.f * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := by ring

end Formalism.BasicNotions
end
