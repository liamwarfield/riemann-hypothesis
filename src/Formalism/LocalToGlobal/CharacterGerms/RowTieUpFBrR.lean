module

public import Formalism.LocalToGlobal.CharacterGerms.ChartHypothesisOfCharacters
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrI
section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBr
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ CharacteristicFromRanks ValuationFitting
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (IsCh dl res HasAF)

section Series

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ}
variable {R : Type} [CommRing R] [Algebra R C]

abbrev toC {n : ℕ} (f : PS R n dd) : PS C n dd := MvPowerSeries.map (algebraMap R C) f

theorem mpt_pt {n : ℕ} (j : Fin n) : MapFB.mpt (algebraMap R C) (pt R dd j) = pt C dd j := by
  funext i
  simp [MapFB.mpt, pt]

theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin dd) : MvPowerSeries.constantCoeff (pt R dd j i) = 0 := by
  simp [pt]

theorem isChar_of_isCh (Y : FBChart C V OE dd) (hR : ∀ x : R, V.Ge 0 (algebraMap R C x))
    (FR : Fin dd → PS R 2 dd) (hF : ∀ i, Y.B.G.F i = toC (FR i))
    (hF0 : ∀ i, MvPowerSeries.constantCoeff (FR i) = 0) {u : PS R 1 dd} (hu : IsCh FR u) :
    Y.IsChar (toC u) := by
  refine ⟨fun μ => ?_, ?_, ?_⟩
  · rw [MvPowerSeries.coeff_map]; exact hR _
  · rw [MvPowerSeries.constantCoeff_map, hu.1, map_one]
  · have h := congrArg (MvPowerSeries.map (algebraMap R C)) hu.2
    have hadd : ∀ i, MvPowerSeries.constantCoeff (addOf FR (pt R (n := 2) dd 0) (pt R (n := 2) dd 1) i) = 0 := by
      intro i
      refine MapFB.cc_ev _ ?_ _ (hF0 i)
      intro j i'
      fin_cases j <;> simp [pt]
    rw [map_mul, MapFB.map_ev1 _ _ hadd, MapFB.map_ev1 _ _ (cc_pt 0), MapFB.map_ev1 _ _ (cc_pt 1), mpt_pt, mpt_pt] at h
    have e : MapFB.mpt (algebraMap R C) (addOf FR (pt R (n := 2) dd 0) (pt R (n := 2) dd 1)) =
        addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) := by
      funext i
      show MvPowerSeries.map (algebraMap R C) (ev ![pt R (n := 2) dd 0, pt R (n := 2) dd 1] (FR i)) = _
      rw [MapFB.map_ev2 _ _ _ (cc_pt 0) (cc_pt 1), mpt_pt, mpt_pt]
      show _ = ev ![pt C (n := 2) dd 0, pt C (n := 2) dd 1] (Y.B.G.F i)
      rw [hF i]
    rw [e] at h
    exact h

end Series

section Len

theorem lenCoker_mono {R : Type} [CommRing R] (v : AddValuation R (WithTop ℝ)) {m h h' : ℕ}
    (B : Matrix (Fin m) (Fin h') R) (f : Fin h → Fin h') :
    S4.lenCoker v B ≤ S4.lenCoker v (B.submatrix id f) := by
  unfold S4.lenCoker
  refine Finset.le_inf fun g _ => ?_
  exact Finset.inf_le (f := fun g : Fin m → Fin h' => v (B.submatrix id g).det) (Finset.mem_univ (f ∘ g))

variable {C : Type} [Field C] {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C] {dd : ℕ}

theorem lenCoker_le_of_hasLen (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ))
    (h1 : (vm (V.l : C) : ℝ) < 1) {s N : ℕ} (W : Fin s → Fin dd → R) (u : Fin N → PS R 1 dd) {x : NNReal}
    (hx : ReciprocityTheory.PGsh.Up.HasLen vm R
      ((Fin s → R) ⧸ Submodule.span R (Set.range fun k => res W (dl (u k)))) x)
    {S : ℝ} (hS : vm (V.l : C) ^ S ≤ x) :
    S4.lenCoker V.v (Matrix.of fun c k => ∑ i, dlogC (toC (C := C) (u k)) i * algebraMap R C (W c i)) ≤
      ((S : ℝ) : WithTop ℝ) := by
  set α : Matrix (Fin s) (Fin N) R := Matrix.of fun c k => res W (dl (u k)) c with hα
  have hr : LinearMap.range α.mulVecLin = Submodule.span R (Set.range fun k => res W (dl (u k))) := by
    rw [Matrix.range_mulVecLin]
    rfl
  rw [← hr] at hx
  have hSr : (vm (V.l : C) : ℝ) ^ S ≤ (x : ℝ) := by exact_mod_cast hS
  have hpos : 0 < (x : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos h0 S) hSr
  have e := lenCoker_eq_logb hT hv h0 h1 α hx hpos
  have e2 : (Matrix.of fun c k => ∑ i, dlogC (toC (C := C) (u k)) i * algebraMap R C (W c i)) =
      Matrix.of fun c k => algebraMap R C (α c k) := by
    ext c k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.of_apply, hα, res, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e2, e]
  refine WithTop.coe_le_coe.mpr ?_
  have h2 : Real.logb (vm (V.l : C) : ℝ) x ≤ Real.logb (vm (V.l : C) : ℝ) ((vm (V.l : C) : ℝ) ^ S) :=
    (Real.logb_le_logb_of_base_lt_one h0 h1 hpos (Real.rpow_pos_of_pos h0 S)).mpr hSr
  rwa [Real.logb_rpow h0 (ne_of_lt h1)] at h2

end Len

section Sum

theorem frobSum_conj_alt {d : ℕ} {l : ℕ} (hl : 1 < l) (n j j' : ℕ) (big : ZMod d → Prop)
    (halt : ∀ b, big (b + 1) ↔ ¬ big b) (q : ZMod d → ℕ)
    (hqb : ∀ b, big b → q b = j') (hqs : ∀ b, ¬ big b → q b = n + j) (a : ZMod d) (ha : big a) :
    S4.frobSum l q a = upB l (n + j) j' (gam l) := by
  rw [S4.frobSum_alt hl j' 0 (n + j) big halt q (fun b hb => by rw [hqb b hb]; rfl) hqs a ha]
  have h1 := S4.one_div_eq_gam_add_rho hl
  have hg : gam l = S4.gam l := rfl
  have hdiv : (j' : ℝ) / ((l : ℝ) - 1) = j' * (S4.gam l + S4.rho l) := by rw [← h1]; ring
  unfold upB
  rw [hg, hdiv]
  push_cast
  ring

theorem frobSum_conj_all {d : ℕ} {l : ℕ} (hl : 1 < l) (n j j' : ℕ) (q : ZMod d → ℕ) (hq : ∀ b, q b = j')
    (a : ZMod d) : S4.frobSum l q a = upB l (n + j) j' 0 := by
  rw [S4.frobSum_const hl j' q hq a]
  unfold upB
  ring

end Sum

section Core

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

end Core

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds CharacteristicFromRanks ValuationFitting
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

def GeoJ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
    (OE : Type) [CommRing OE] [StarRing OE] (aG : OE → (G ⟶ G)) (dd : ℕ) (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) : Prop :=
  ∃ (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T))))
    (U : Out.UnifPre (maximalIdeal T) D A G) (F : FGLaw T dd)
    (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin dd) m) ⟶ G) (_ : Module OE D.toPre.X) (io : Out.RingAct G OE)
    (oD : D.OAct OE) (oA : A.OAct OE) (act : Germ.OAct OE F),
    F.F = FT ∧ act.act = actT ∧ (∀ a, io.act a = aG a) ∧ IsChartJ G F x ∧ U.OLinear OE oD oA io ∧
      ChartActs G x io act

def PlaceIn (l : ℕ) [Fact l.Prime] (OE : Type) [CommRing OE] (R : Type) [CommRing R] [Algebra ℤ_[l] R] (d : ℕ)
    (em : ZMod d → OE →+* R) : Prop :=
  ∃ (w : PlaceU l OE) (_ : NeZero w.n) (t : Fin w.n ≃ Emb (O := R) w.e) (jj : ZMod d ≃ Fin w.n),
    (∀ a, jj (a + 1) = jj a + 1) ∧ (∀ a, ((t (jj a) : Emb (O := R) w.e) : OE →+* R) = em a) ∧
    ∃ b : Module.Basis (Fin w.n) ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] w.e)),
      IsUnit (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := R) w.e) : OE →+* R) (b i : ℤ_[l] ⊗[ℤ] OE)))

def UpFLaw (p : ℕ) [Fact p.Prime] (T : Type) [CommRing T] (OE : Type) [CommRing OE] [StarRing OE] (dd : ℕ)
    (FT : Fin dd → PS T 2 dd) (actT : OE → Fin dd → PS T 1 dd) : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsLocalRing O]
      [Algebra ℤ_[p] O] (iota : T →+* O), IsLocalHom iota →
    ∀ (w : PlaceU p OE) [NeZero w.n] (t : Fin w.n ≃ Emb (O := O) w.e),
    (∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)),
      IsUnit (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b i : ℤ_[p] ⊗[ℤ] OE)))) →
    (∀ (j : Fin w.n) (a : OE), ((t (j + 1) : Emb (O := O) w.e) : OE →+* O) a -
        (((t j : Emb (O := O) w.e) : OE →+* O) a) ^ p ∈ maximalIdeal O) →
    ∀ (r : (OE →+* O) → ℕ) (W : ∀ τ : OE →+* O, Fin (r τ) → Fin dd → O),
      (∀ τ, IsEigBasis (fun a i => MvPowerSeries.map iota (actT a i)) τ (W τ)) →
    ∀ j : Fin w.n, ∃ xs : NNReal,
      HasAF v (fun i => MvPowerSeries.map iota (FT i)) (W ((t j : Emb (O := O) w.e) : OE →+* O)) xs ∧
      v (algebraMap O C (p : O)) ^ (∑' n : ℕ, ((p : ℝ) ^ (-((n : ℝ) + 1))) *
        (r (((t (j + Fin.ofNat w.n (n + 1)) : Emb (O := O) w.e) : OE →+* O).comp
          ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) : ℝ)) ≤ xs

theorem upFLaw_of_geoJ {p : ℕ} [Fact p.Prime] (hUp : UpFSt p) (hp2 : p ≠ 2)
    (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (maximalIdeal T) T] (hlT : ¬ IsUnit (p : T))
    (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
    {OE : Type} [CommRing OE] [StarRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE]
    (aG : OE → (G ⟶ G)) {dd : ℕ} (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) (hG : GeoJ T G OE aG dd FT actT)
    (hdisc : ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE))) : UpFLaw p T OE dd FT actT := by
  obtain ⟨D, A, U, F, x, iM, io, oD, oA, act, rfl, rfl, -, hx, hO, hA⟩ := hG
  intro C _ _ _ v O _ _ hv _ _ _ _ iota hloc w _ t hbas hfrob r W hW j
  exact hUp T hlT G D A U dd F x hx hp2 OE io oD oA hO hdisc act hA C v O hv iota hloc w t hbas hfrob r W hW j

section Inst

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem ofNat_succ (n : ℕ) [NeZero n] (k : ℕ) : Fin.ofNat n (k + 1) = Fin.ofNat n k + 1 := by
  apply Fin.ext
  simp [Fin.ofNat, Fin.val_add, Nat.add_mod]

theorem jj_add {n : ℕ} [NeZero n] (jj : ZMod d ≃ Fin n) (h : ∀ a, jj (a + 1) = jj a + 1) (a : ZMod d) :
    ∀ k : ℕ, jj (a + (k : ZMod d)) = jj a + Fin.ofNat n k
  | 0 => by
    have : Fin.ofNat n 0 = 0 := by apply Fin.ext; simp [Fin.ofNat]
    simp [this]
  | k + 1 => by
    have e : a + ((k + 1 : ℕ) : ZMod d) = (a + (k : ZMod d)) + 1 := by push_cast; ring
    rw [e, h, jj_add jj h a k, ofNat_succ, add_assoc]

end Inst

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open ValuationFitting

structure RingPk {C : Type} [Field C] (V : VF C) where
  vm : Valuation C NNReal
  tie : ValTie V vm
  int : vm.Integers V.RR
  pos : 0 < (vm (V.l : C) : ℝ)
  lt : (vm (V.l : C) : ℝ) < 1
  nonunit : ¬ IsUnit ((V.l : ℕ) : V.RR)
  cpl : IsAdicComplete (Ideal.span {((V.l : ℕ) : V.RR)}) V.RR
  loc : IsLocalRing V.RR
  alg : Algebra ℤ_[V.l] V.RR
  mm : ∀ x : V.RR, V.MM (x : C) → x ∈ IsLocalRing.maximalIdeal V.RR

def RingPkSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C),
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → Nonempty (RingPk V)

end UpFBr

end Formalism.L2.FormalSeriesBounds
