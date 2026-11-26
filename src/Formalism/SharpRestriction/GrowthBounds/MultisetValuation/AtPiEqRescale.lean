module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NatCastInvMemRp
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.OmegaOfTraceDuality

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.InParamMap
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.IntRPsubst
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AllPlacesOfRestrictions
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.KernelExpansionOfRestrictions
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

def RestSExp (p : ℕ) [Fact p.Prime] : Prop :=
  5 ≤ p → DworkLemma p → ∀ be : MvPowerSeries (Fin 2) (K0 p), BeProp p be →
  ∀ (n' r0 r1 : ℕ), 2 ≤ n' → Even n' → ∀ (B : OmBasis p n')
    (Ph : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (K0 p)),
    Simeq p Ph (∑ e : Eidx n' r0 r1, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))) →
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∃ u : Fin n' → K', (∀ s, u s ∈ Rp p K' vp) ∧ ∃ V : MvPowerSeries (Zidx n' r0 r1) K', IntR (Rp p K' vp) V ∧
      ThZ B K' vp (MvPowerSeries.map (algebraMap (K0 p) K') (expS p (-Ph))) =
        expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * hhS p K' u)) * V

def RestSInt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (n' r0 r1 : ℕ) (B : OmBasis p n') (K1 : Type) [Field K1] [Algebra (K0 p) K1] (R1 : Subring K1)
    (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K1), IntR R1 (inParamK p K1 U) →
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (R' : Subring K')
    (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ R1, algebraMap K1 K' x ∈ R') →
    IntR R' (ThZ B K' vp (MvPowerSeries.map (algebraMap K1 K') U))

def RestSExpA {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  DworkLemma p → ∀ be : MvPowerSeries (Fin 2) (K0 p), BeProp p be →
  ∀ (j : ℕ) (Ph : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)),
    Simeq p Ph (∑ e : X.EA j, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))) →
  ∀ (K1 : Type) [Field K1] [Algebra (K0 p) K1] (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K']
    [IsScalarTower (K0 p) K1 K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∃ u : ∀ v : X.Pl, Fin (X.G.P.n' v) → K', (∀ v s, u v s ∈ Rp p K' vp) ∧
      ∃ V : MvPowerSeries (X.ZA j) K', IntR (Rp p K' vp) V ∧
        atPi vp (MvPowerSeries.map (algebraMap K1 K')
          (X.ThZA K1 j (MvPowerSeries.map (algebraMap (K0 p) K1) (expS p (-Ph))))) =
          (∏ v, expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * X.hhA K' j v (u v)))) * V

def RestSIntA {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  ∀ (j : ℕ) (K1 : Type) [Field K1] [Algebra (K0 p) K1] (R1 : Subring K1)
    (U : MvPowerSeries (X.EA j ⊕ X.EA j) K1), IntR R1 (inParamK p K1 U) →
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (R' : Subring K')
    (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ R1, algebraMap K1 K' x ∈ R') →
    IntR R' (atPi vp (MvPowerSeries.map (algebraMap K1 K') (X.ThZA K1 j U)))

section Formal

variable {p : ℕ} [hp : Fact p.Prime]

theorem sSer_const {n' r0 r1 : ℕ} (K' : Type) [Field K'] (e : Fin n') (a : Fin r0) (b : Fin r1) :
    MvPowerSeries.constantCoeff (sSer p K' e a b) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ l ∈ range ((0 : Zidx n' r0 r1 →₀ ℕ).degree + 1),
    if (0 : Zidx n' r0 r1 →₀ ℕ) = Finsupp.single (posSub e (2 * l), a, b) (p ^ (2 * l)) then ((-1 : K') ^ l) else 0) = 0
  refine Finset.sum_eq_zero fun l _ => if_neg fun h => ?_
  exact pow_ne_zero (2 * l) hp.out.ne_zero (Finsupp.single_eq_zero.1 h.symm)

theorem hhS_const {n' r0 r1 : ℕ} (K' : Type) [Field K'] (u : Fin n' → K') :
    MvPowerSeries.constantCoeff (hhS (r0 := r0) (r1 := r1) p K' u) = 0 := by
  unfold hhS
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, sSer_const, mul_zero, Finset.sum_const_zero]

theorem coordZ_const {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K')
    (x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) : MvPowerSeries.constantCoeff (coordZ B K' vp x) = 0 := by
  rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;>
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordZ, map_sum, map_mul, MvPowerSeries.constantCoeff_X, mul_zero, Finset.sum_const_zero]

theorem ThZ_mul {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K')
    (f g : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K') :
    ThZ B K' vp (f * g) = ThZ B K' vp f * ThZ B K' vp g :=
  MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero (coordZ_const B K' vp)) f g

theorem map_map_tower {ι : Type} (K1 K' : Type) [Field K1] [Algebra (K0 p) K1] [Field K'] [Algebra (K0 p) K']
    [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (f : MvPowerSeries ι (K0 p)) :
    MvPowerSeries.map (algebraMap K1 K') (MvPowerSeries.map (algebraMap (K0 p) K1) f) =
      MvPowerSeries.map (algebraMap (K0 p) K') f := by
  rw [IsScalarTower.algebraMap_eq (K0 p) K1 K', MvPowerSeries.map_comp]
  rfl

theorem atPi_mul {σ R : Type} [CommRing R] (vp : R) (f g : MvPowerSeries σ R) :
    atPi vp (f * g) = atPi vp f * atPi vp g := by
  classical
  ext n
  show vp ^ n.degree * MvPowerSeries.coeff n (f * g) = MvPowerSeries.coeff n (atPi vp f * atPi vp g)
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  show _ = (vp ^ x.1.degree * MvPowerSeries.coeff x.1 f) * (vp ^ x.2.degree * MvPowerSeries.coeff x.2 g)
  rw [← hx', map_add (f := _), pow_add]
  ring

theorem exp_change {ι : Type} (K' : Type) [Field K'] [Algebra (K0 p) K'] (c : K') (hh hh' G : MvPowerSeries ι K')
    (h0 : MvPowerSeries.constantCoeff hh = 0) (h0' : MvPowerSeries.constantCoeff hh' = 0)
    (hE : hh' = hh + MvPowerSeries.C (p : K') * G) :
    expK (-(MvPowerSeries.C (c / (p : K')) * hh)) =
      expK (-(MvPowerSeries.C (c / (p : K')) * hh')) * expK (MvPowerSeries.C c * G) := by
  have := charZero_K' p K'
  have hp0 := pK'_ne p K'
  have hG : MvPowerSeries.constantCoeff G = 0 := by
    have := congrArg MvPowerSeries.constantCoeff hE
    rw [map_add (f := _), map_mul, h0, h0', zero_add, MvPowerSeries.constantCoeff_C] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h hp0
    · exact h
  rw [← expK_add (by rw [map_neg, map_mul, h0', mul_zero, neg_zero]) (by rw [map_mul, hG, mul_zero])]
  congr 1
  have e : (MvPowerSeries.C (c / (p : K')) : MvPowerSeries ι K') * MvPowerSeries.C (p : K') = MvPowerSeries.C c := by
    rw [← map_mul, div_mul_cancel₀ _ hp0]
  rw [hE, mul_add, ← mul_assoc, e]
  ring

end Formal

theorem SConcl_of {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (hD : DworkLemma p) (hE : RestSExp p) (hI : RestSInt p)
    {n' r0 r1 : ℕ} (h2 : 2 ≤ n') (hev : Even n') (B : OmBasis p n') (K1 : Type) [Field K1] [Algebra (K0 p) K1]
    (R1 : Subring K1) (be : MvPowerSeries (Fin 2) (K0 p)) (Th : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K1)
    (hK : ExtensionLocalCondition p K1 R1 be Th) : SConcl B K1 R1 Th := by
  obtain ⟨Ph, U, hTh, hU, _, hbe, hPh⟩ := hK
  intro K' _ _ _ _ R' vp hvp hRp hR1
  obtain ⟨u, hu, V, hV, hEq⟩ := hE h5 hD be hbe n' r0 r1 h2 hev B Ph hPh K' vp hvp
  refine ⟨u, fun s => hRp (hu s), fun hh' h0' hG => ?_⟩
  obtain ⟨G, hG, hhE⟩ := hG
  have hW := hI n' r0 r1 B K1 R1 U hU K' R' vp hvp hRp hR1
  have hc : ∀ k : ℕ, (vp ^ (p + 1)) ^ k * ((k.factorial : K'))⁻¹ ∈ R' := fun k => hRp (piFact p K' vp hvp k)
  have e1 : ThZ B K' vp (MvPowerSeries.map (algebraMap K1 K') Th) =
      expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * hh')) *
        (expK (MvPowerSeries.C (vp ^ (p + 1)) * G) * V * ThZ B K' vp (MvPowerSeries.map (algebraMap K1 K') U)) := by
    rw [hTh, map_mul, map_map_tower, ThZ_mul, hEq,
      exp_change K' (vp ^ (p + 1)) (hhS p K' u) hh' G (hhS_const K' u) h0' hhE]
    ring
  rw [e1]
  exact inClass_of_exp (pK'_ne p K') hc hh' h0' (IntR_mul (IntR_mul (IntR_expK hc hG) (IntR_mono hRp hV)) hW)

theorem kernel_expansion_of_restrictions (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) (hA : admitted D X Y)
    (hE : RestSExp p) (hI : RestSInt p) : Conclusion1 D X Y := by
  intro v j hj La La' h1 h2 φ
  exact SConcl_of (X.std v).five_le (hA.1 p) hE hI (X.std v).two_le (X.std v).even (X.om v) Y.Kc Y.Oc Y.be _
    (hA.2.1 v j hj La La' h1 h2 φ)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

theorem sSA_const (K' : Type) [Field K'] (j : ℕ) (v : X.Pl) (e : Fin (X.G.P.n' v)) (a : Fin (NN X.G.P.m X.t j))
    (b : Fin (NN X.G.P.m X.t (j + 1))) : MvPowerSeries.constantCoeff (X.sSA K' j v e a b) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ l ∈ range ((0 : X.ZA j →₀ ℕ).degree + 1),
    if (0 : X.ZA j →₀ ℕ) = Finsupp.single (⟨v, (posSub e (2 * l), a, b)⟩ : X.ZA j) (p ^ (2 * l))
      then ((-1 : K') ^ l) else 0) = 0
  refine Finset.sum_eq_zero fun l _ => if_neg fun h => ?_
  exact pow_ne_zero (2 * l) hp.out.ne_zero (Finsupp.single_eq_zero.1 h.symm)

theorem hhA_const (K' : Type) [Field K'] (j : ℕ) (v : X.Pl) (u : Fin (X.G.P.n' v) → K') :
    MvPowerSeries.constantCoeff (X.hhA K' j v u) = 0 := by
  unfold Sys.hhA
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, sSA_const, mul_zero, Finset.sum_const_zero]

theorem coordZA_const (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    MvPowerSeries.constantCoeff (X.coordZA K' j x) = 0 := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;>
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Sys.coordZA, map_sum, map_mul, MvPowerSeries.constantCoeff_X, mul_zero, Finset.sum_const_zero]

theorem ThZA_mul (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (f g : MvPowerSeries (X.EA j ⊕ X.EA j) K') :
    X.ThZA K' j (f * g) = X.ThZA K' j f * X.ThZA K' j g :=
  MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero (coordZA_const X K' j)) f g

theorem all_places_of_restrictions (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y)
    (hE : RestSExpA X) (hI : RestSIntA X) : ExpansionsMultiply D X Y := by
  intro j hj La La' h1 h2 φ K' _ _ _ _ R' vp hvp hRp hR1
  obtain ⟨Ph, U, hTh, hU, _, hbe, hPh⟩ := hA.2.2.1 j hj La La' h1 h2 φ
  obtain ⟨u, hu, V, hV, hEq⟩ := hE (hA.1 p) Y.be hbe j Ph hPh Y.Kc K' vp hvp
  refine ⟨u, fun v s => hRp (hu v s), fun h' hh' => ?_⟩
  choose h0' G hG hGE using hh'
  have hW := hI j Y.Kc Y.Oc U hU K' R' vp hvp hRp hR1
  have hc : ∀ k : ℕ, (vp ^ (p + 1)) ^ k * ((k.factorial : K'))⁻¹ ∈ R' := fun k => hRp (piFact p K' vp hvp k)
  have e1 : atPi vp (MvPowerSeries.map (algebraMap Y.Kc K') (X.ThZA Y.Kc j (Y.ThA j La La' φ))) =
      (∏ v, expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * h' v))) *
        ((∏ v, expK (MvPowerSeries.C (vp ^ (p + 1)) * G v)) * V *
          atPi vp (MvPowerSeries.map (algebraMap Y.Kc K') (X.ThZA Y.Kc j U))) := by
    rw [hTh, ThZA_mul, map_mul, atPi_mul, hEq,
      Finset.prod_congr rfl fun v _ => exp_change K' (vp ^ (p + 1)) (X.hhA K' j v (u v)) (h' v) (G v)
        (hhA_const X K' j v (u v)) (h0' v) (hGE v), Finset.prod_mul_distrib]
    ring
  rw [e1]
  exact inProd_of_exp (pK'_ne p K') hc h' h0'
    (IntR_mul (IntR_mul (IntR_prod _ _ fun v _ => IntR_expK hc (hG v)) (IntR_mono hRp hV)) hW)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF)

section Gen

variable {K : Type} [Field K] {R : Subring K}

theorem IntR_add {ι : Type} {f g : MvPowerSeries ι K} (hf : IntR R f) (hg : IntR R g) : IntR R (f + g) := by
  intro n
  rw [map_add (f := _)]
  exact R.add_mem (hf n) (hg n)

theorem IntR_zero {ι : Type} : IntR R (0 : MvPowerSeries ι K) := by
  intro n
  rw [map_zero]
  exact R.zero_mem

theorem IntR_sum {ι α : Type} (s : Finset α) (f : α → MvPowerSeries ι K) (h : ∀ a ∈ s, IntR R (f a)) :
    IntR R (∑ a ∈ s, f a) := by
  intro n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact R.sum_mem fun a ha => h a ha n

theorem IntR_X {ι : Type} (i : ι) : IntR R (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

private theorem intR_iff_mem_range_map_subtype {ι : Type} {f : MvPowerSeries ι K} :
    IntR R f ↔ f ∈ (MvPowerSeries.map R.subtype).range := by
  constructor
  · intro hf
    unfold IntR at hf
    let g : MvPowerSeries ι R := fun n => ⟨MvPowerSeries.coeff n f, hf n⟩
    refine ⟨g, ?_⟩
    ext n
    rw [MvPowerSeries.coeff_map]
    rfl
  · rintro ⟨g, rfl⟩ n
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n g).2

theorem IntR_subst {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ K)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha : ∀ i, IntR R (a i)) {f : MvPowerSeries σ K}
    (hf : IntR R f) : IntR R (MvPowerSeries.subst a f) := by
  classical
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hprod : ∀ d : σ →₀ ℕ, IntR R (d.prod fun s k => (a s) ^ k) := by
    intro d
    rw [intR_iff_mem_range_map_subtype, Finsupp.prod]
    exact Subring.prod_mem _ fun s _ => Subring.pow_mem _ (intR_iff_mem_range_map_subtype.1 (ha s)) _
  intro e
  rw [MvPowerSeries.coeff_subst hs]
  by_cases hfin : (Function.support fun d : σ →₀ ℕ =>
      MvPowerSeries.coeff d f • MvPowerSeries.coeff e (d.prod fun s k => (a s) ^ k)).Finite
  · rw [finsum_eq_sum _ hfin]
    exact R.sum_mem fun d _ => by
      rw [smul_eq_mul]
      exact R.mul_mem (hf d) (hprod d e)
  · rw [finsum_of_infinite_support hfin]
    exact R.zero_mem

theorem IntR_of_ps {f : PowerSeries K} (hf : ∀ n, PowerSeries.coeff n f ∈ R) :
    IntR R (f : MvPowerSeries Unit K) := by
  intro n
  have hn : n = Finsupp.single () (n ()) := Finsupp.unique_single n
  rw [hn]
  exact hf (n ())

theorem IntR_psubst {τ : Type} {L : MvPowerSeries τ K} (hL0 : MvPowerSeries.constantCoeff L = 0) (hL : IntR R L)
    {f : PowerSeries K} (hf : ∀ n, PowerSeries.coeff n f ∈ R) : IntR R (PowerSeries.subst L f) :=
  IntR_subst (fun _ : Unit => L) (fun _ => hL0) (fun _ => hL) (IntR_of_ps hf)

end Gen

section Mu

variable (p : ℕ) [hp : Fact p.Prime] (K' : Type) [Field K'] [Algebra (K0 p) K']

private theorem mul_add_one_le_succ_pow (b j : ℕ) : b * j + 1 ≤ (b + 1) ^ j := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    nlinarith [Nat.mul_le_mul_right (b + 1) ih, Nat.zero_le (b * b * k)]

theorem lamF_mem (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) (n : ℕ) :
    PowerSeries.coeff n (lamF p vp) ∈ Rp p K' vp := by
  have hvpR : vp ∈ Rp p K' vp := by
    unfold Rp
    exact Subring.subset_closure (Set.mem_union_right _ rfl)
  simp only [lamF, lgF, PowerSeries.coeff_mk, Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  split_ifs with h
  · have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
    have hle : (p ^ 2 - 1) * j + 1 ≤ (p ^ 2) ^ j := by
      have := mul_add_one_le_succ_pow (p ^ 2 - 1) j
      rwa [Nat.sub_add_cancel hp1] at this
    obtain ⟨m, hm⟩ : ∃ m, n - 1 = (p ^ 2 - 1) * j + m := by
      refine ⟨n - 1 - (p ^ 2 - 1) * j, ?_⟩
      rw [h]
      generalize (p ^ 2 - 1) * j = A at hle ⊢
      generalize (p ^ 2) ^ j = B at hle ⊢
      omega
    rw [hm, pow_add, ← hvp, ← pow_mul]
    by_cases h0 : vp ^ ((p ^ 2 - 1) * j) = 0
    · rw [h0, zero_mul, zero_mul]
      exact (Rp p K' vp).zero_mem
    · rw [mul_comm (vp ^ ((p ^ 2 - 1) * j)), mul_assoc, mul_inv_cancel₀ h0, mul_one]
      exact (Rp p K' vp).pow_mem hvpR m
  · rw [mul_zero]
    exact (Rp p K' vp).zero_mem

theorem exists_mu (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) :
    ∃ μ : PowerSeries K', PowerSeries.constantCoeff μ = 0 ∧ (∀ n, PowerSeries.coeff n μ ∈ Rp p K' vp) ∧
      (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X := by
  let l0 : PowerSeries (Rp p K' vp) := PowerSeries.mk fun n => ⟨_, lamF_mem p K' vp hvp n⟩
  have hmap : PowerSeries.map (Rp p K' vp).subtype l0 = lamF p vp := by
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    rfl
  have hc : PowerSeries.constantCoeff l0 = 0 := by
    apply Subtype.ext
    have := Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.constantCoeff_lamF p vp
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at this ⊢
    rw [PowerSeries.coeff_mk]
    exact this
  have hu : IsUnit (PowerSeries.coeff 1 l0) := by
    have : PowerSeries.coeff 1 l0 = 1 := by
      apply Subtype.ext
      rw [PowerSeries.coeff_mk]
      exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.coeff_one_lamF hp.out.two_le vp
    rw [this]
    exact isUnit_one
  have h1 := PowerSeries.subst_substInvOfIsUnit_right l0 hc hu
  refine ⟨PowerSeries.map (Rp p K' vp).subtype (l0.substInvOfIsUnit hu), ?_, fun n => ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_substInvOfIsUnit, map_zero]
  · rw [PowerSeries.coeff_map]
    exact Subtype.property _
  · have h2 := congrArg (PowerSeries.map (Rp p K' vp).subtype) h1
    rw [Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.ps_map_subst _ (PowerSeries.HasSubst.substInvOfIsUnit l0 hu), hmap, PowerSeries.map_X] at h2
    exact h2

theorem map_logF : PowerSeries.map (algebraMap (K0 p) K') (logF p) = lgF K' p := by
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PowerSeries.coeff_map, logF, lgF, PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_mul]
  split_ifs <;> simp

end Mu

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF)

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Gen

variable (p : ℕ) [hp : Fact p.Prime] (K' : Type) [Field K'] [Algebra (K0 p) K']

theorem lgF_const : PowerSeries.constantCoeff (lgF K' p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, lgF, PowerSeries.coeff_mk]
  simp

private theorem cc_subst_lemma {Kf : Type} [Field Kf] {ρ : Type} (a : MvPowerSeries ρ Kf) (f : PowerSeries Kf)
    (ha : MvPowerSeries.constantCoeff a = 0) (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [← PowerSeries.coe_substAlgHom hs, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs, map_mul,
    ha, zero_mul]

theorem log_at {τ : Type} (vp : K') (μ : PowerSeries K') (h0 : PowerSeries.constantCoeff μ = 0)
    (h1 : (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X)
    (L : MvPowerSeries τ K') (hL : MvPowerSeries.constantCoeff L = 0) :
    PowerSeries.subst (PowerSeries.subst L (PowerSeries.C vp * μ) : MvPowerSeries τ K') (lgF K' p) =
      MvPowerSeries.C vp * L := by
  have hμ : PowerSeries.HasSubst μ := PowerSeries.HasSubst.of_constantCoeff_zero h0
  have hL' : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero hL
  have hvμ : PowerSeries.HasSubst (PowerSeries.C vp * μ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by rw [map_mul]; exact mul_eq_zero_of_right _ h0)
  have hvX : PowerSeries.HasSubst (vp • PowerSeries.X : PowerSeries K') :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp; exact Or.inr (PowerSeries.constantCoeff_X (R := K')))
  have hres : PowerSeries.rescale vp (lgF K' p) = vp • lamF p vp := by
    ext n
    rcases n with _ | n
    · rw [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, lamF, PowerSeries.coeff_mk,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, lgF_const p K']
      simp
    · rw [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, lamF, PowerSeries.coeff_mk]
      simp only [Nat.add_sub_cancel, smul_eq_mul]
      ring
  have hsub : PowerSeries.subst (PowerSeries.C vp * μ) (lgF K' p) = vp • PowerSeries.subst μ (lamF p vp) := by
    have hvμe : PowerSeries.C vp * μ = PowerSeries.subst μ (vp • PowerSeries.X : PowerSeries K') := by
      rw [← PowerSeries.coe_substAlgHom hμ, map_smul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hμ,
        PowerSeries.smul_eq_C_mul]
    rw [hvμe, ← PowerSeries.subst_comp_subst_apply hvX hμ, ← PowerSeries.rescale_eq_subst, hres,
      ← PowerSeries.coe_substAlgHom hμ, map_smul]
  rw [← PowerSeries.subst_comp_subst_apply hvμ hL', hsub, h1, ← PowerSeries.coe_substAlgHom hL', map_smul,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X hL', MvPowerSeries.smul_eq_C_mul]

theorem genInt {σ τ : Type} [Finite σ] (R' : Subring K') (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K'))
    (hRp : Rp p K' vp ≤ R') (U : MvPowerSeries σ K') (hU : IntR R' (inParamK p K' U))
    (L : σ → MvPowerSeries τ K') (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) (hL : ∀ i, IntR R' (L i)) :
    IntR R' (MvPowerSeries.subst (fun i => MvPowerSeries.C vp * L i) U) := by
  obtain ⟨μ, h0, hμ, h1⟩ := exists_mu (p := p) (K' := K') vp hvp
  have hlg : PowerSeries.map (algebraMap (K0 p) K') (logF p) = lgF K' p := map_logF (p := p) (K' := K')
  let M : σ → MvPowerSeries τ K' := fun i => PowerSeries.subst (L i) (PowerSeries.C vp * μ)
  have hvμ0 : PowerSeries.constantCoeff (PowerSeries.C vp * μ) = 0 := by simp [h0]
  have hM0 : ∀ i, MvPowerSeries.constantCoeff (M i) = 0 := fun i => cc_subst_lemma _ _ (hL0 i) hvμ0
  have hvp_mem : vp ∈ R' := hRp (Subring.subset_closure (Or.inr rfl))
  have hvμI : IntR R' (PowerSeries.C vp * μ : PowerSeries K') := by
    intro n
    rw [← PowerSeries.smul_eq_C_mul, MvPowerSeries.coeff_smul]
    refine R'.mul_mem hvp_mem (hRp ?_)
    have hn : n = Finsupp.single () (n ()) := Finsupp.ext fun u => by cases u; simp
    rw [hn]
    exact hμ (n ())
  have hMint : ∀ i, IntR R' (M i) := fun i =>
    IntR_subst (K := K') (R := R') (fun _ : Unit => L i) (fun _ => hL0 i) (fun _ => hL i) hvμI
  have hMs : MvPowerSeries.HasSubst M := MvPowerSeries.hasSubst_of_constantCoeff_zero hM0
  have hMeq : ∀ i, PowerSeries.subst (M i) (lgF K' p) = MvPowerSeries.C vp * L i := fun i =>
    log_at p K' vp μ h0 h1 (L i) (hL0 i)
  have key : MvPowerSeries.subst (fun i => MvPowerSeries.C vp * L i) U =
      MvPowerSeries.subst M (inParamK p K' U) := by
    have hXs : MvPowerSeries.HasSubst
        (fun i : σ => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K') (lgF K' p)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
        cc_subst_lemma _ _ (MvPowerSeries.constantCoeff_X i) (lgF_const p K')
    rw [inParamK, hlg, MvPowerSeries.subst_comp_subst_apply hXs hMs]
    congr 1
    funext i
    rw [← hMeq i]
    have hXi : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries σ K')) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X i
    show _ = MvPowerSeries.subst M (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries σ K'))
      (lgF K' p))
    rw [MvPowerSeries.subst_comp_subst_apply hXi hMs, MvPowerSeries.subst_X hMs]
    rfl
  rw [key]
  exact IntR_subst (K := K') (R := R') M hM0 hMint hU

theorem inParam_map {σ : Type} [Finite σ] (K1 : Type) [Field K1] [Algebra (K0 p) K1] [Algebra K1 K']
    [IsScalarTower (K0 p) K1 K'] (R1 : Subring K1) (R' : Subring K') (hR1 : ∀ x ∈ R1, algebraMap K1 K' x ∈ R')
    (U : MvPowerSeries σ K1) (hU : IntR R1 (inParamK p K1 U)) :
    IntR R' (inParamK p K' (MvPowerSeries.map (algebraMap K1 K') U)) := by
  have hXs1 : MvPowerSeries.HasSubst (fun i : σ => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K1)
      (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      cc_subst_lemma _ _ (MvPowerSeries.constantCoeff_X i) (by rw [map_logF (p := p) (K' := K1)]; exact lgF_const p K1)
  have e : inParamK p K' (MvPowerSeries.map (algebraMap K1 K') U) =
      MvPowerSeries.map (algebraMap K1 K') (inParamK p K1 U) := by
    rw [inParamK, inParamK, MvPowerSeries.map_subst hXs1]
    congr 1
    funext i
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)),
      MvPowerSeries.map_X]
    congr 1
    ext n
    simp [PowerSeries.coeff_map, IsScalarTower.algebraMap_apply (K0 p) K1 K']
  rw [e]
  intro n
  rw [MvPowerSeries.coeff_map]
  exact hR1 _ (hU n)

end Gen

theorem restSInt (p : ℕ) [Fact p.Prime] : RestSInt p := by
  intro n' r0 r1 B K1 _ _ R1 U hU K' _ _ _ _ R' vp hvp hRp hR1
  have hc : coordZ (r0 := r0) (r1 := r1) B K' vp = fun x => MvPowerSeries.C vp * coordZ B K' 1 x := by
    funext x
    rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;> simp [coordZ, Finset.mul_sum, map_mul, mul_assoc]
  have hLint : ∀ x, IntR R' (coordZ (r0 := r0) (r1 := r1) B K' 1 x) := by
    intro x n
    rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;>
      simp only [coordZ, one_mul, map_sum] <;>
      refine R'.sum_mem fun s _ => ?_ <;>
      rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X] <;>
      split_ifs <;> simp only [mul_one, mul_zero]
    all_goals first | exact hRp (Subring.subset_closure (Or.inl ⟨_, rfl⟩)) | exact R'.zero_mem
  unfold ThZ
  rw [hc]
  exact genInt p K' R' vp hvp hRp (MvPowerSeries.map (algebraMap K1 K') U) (inParam_map p K' K1 R1 R' hR1 U hU)
    (coordZ B K' 1) (coordZ_const (p := p) B K' 1) hLint

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem atPi_eq_rescale {σ R : Type} [CommRing R] (vp : R) (f : MvPowerSeries σ R) :
    atPi vp f = MvPowerSeries.rescale (fun _ => vp) f := by
  ext n
  rw [MvPowerSeries.coeff_rescale]
  show vp ^ n.degree * MvPowerSeries.coeff n f = _
  congr 1
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree]
  rfl

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

private theorem atPi_sum_C_mul_X_eq_C_mul {σ R ι : Type} [CommRing R] (vp : R) (t : Finset ι) (a : ι → R)
    (g : ι → σ) :
    atPi vp (∑ i ∈ t, MvPowerSeries.C (a i) * MvPowerSeries.X (g i)) =
      MvPowerSeries.C vp * ∑ i ∈ t, MvPowerSeries.C (a i) * MvPowerSeries.X (g i) := by
  classical
  ext n
  rw [MvPowerSeries.coeff_C_mul]
  show vp ^ n.degree * MvPowerSeries.coeff n _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs with h
  · subst h
    simp
  · simp

theorem atPi_coordZA (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K') (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    atPi vp (X.coordZA K' j x) = MvPowerSeries.C vp * X.coordZA K' j x := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp only [Sys.coordZA] <;> exact atPi_sum_C_mul_X_eq_C_mul _ _ _ _

theorem map_coordZA (K1 K' : Type) [Field K1] [Algebra (K0 p) K1] [Field K'] [Algebra (K0 p) K'] [Algebra K1 K']
    [IsScalarTower (K0 p) K1 K'] (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    MvPowerSeries.map (algebraMap K1 K') (X.coordZA K1 j x) = X.coordZA K' j x := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Sys.coordZA, map_sum, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X,
      ← IsScalarTower.algebraMap_apply]

theorem atPi_map_ThZA (K1 K' : Type) [Field K1] [Algebra (K0 p) K1] [Field K'] [Algebra (K0 p) K'] [Algebra K1 K']
    [IsScalarTower (K0 p) K1 K'] (vp : K') (j : ℕ) (U : MvPowerSeries (X.EA j ⊕ X.EA j) K1) :
    atPi vp (MvPowerSeries.map (algebraMap K1 K') (X.ThZA K1 j U)) =
      MvPowerSeries.subst (fun x => MvPowerSeries.C vp * X.coordZA K' j x) (MvPowerSeries.map (algebraMap K1 K') U) := by
  have hA1 : MvPowerSeries.HasSubst (X.coordZA K1 j) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (coordZA_const X K1 j)
  have hA' : MvPowerSeries.HasSubst (X.coordZA K' j) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (coordZA_const X K' j)
  rw [Sys.ThZA, MvPowerSeries.map_subst hA1]
  simp only [map_coordZA X K1 K']
  rw [atPi_eq_rescale, MvPowerSeries.rescale_eq_subst,
    MvPowerSeries.subst_comp_subst_apply hA' (MvPowerSeries.HasSubst.smul_X _)]
  refine congrArg (fun a => MvPowerSeries.subst a (MvPowerSeries.map (algebraMap K1 K') U)) (funext fun s => ?_)
  rw [← MvPowerSeries.rescale_eq_subst, ← atPi_eq_rescale, atPi_coordZA]

theorem restSIntA : RestSIntA X := by
  intro j K1 _ _ R1 U hU K' _ _ _ _ R' vp hvp hRp hR1
  rw [atPi_map_ThZA X K1 K' vp j U]
  refine genInt p K' R' vp hvp hRp _ (inParam_map p K' K1 R1 R' hR1 U hU) (X.coordZA K' j)
    (coordZA_const X K' j) ?_
  intro i
  rcases i with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp only [Sys.coordZA] <;>
    exact IntR_sum _ _ (fun s _ => IntR_mul (IntR_C (hRp (W_mem_Rp (p := p) (K' := K') vp _))) (IntR_X _))

end Formalism.MainNotions.FormalGroupSystem.Pf
