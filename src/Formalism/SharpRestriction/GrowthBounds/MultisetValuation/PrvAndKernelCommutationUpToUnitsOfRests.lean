module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LiftBoundOfIntegrality
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StabilizerCount
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CoupledSumOfEntries
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SmulPsiGUp
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CommonEigenvectorThird
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RestEntOf
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.FirstTheoremPlaceBound

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HeckeConditionOfAdm
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HkEsymmSmul
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem hk_scal {K : Type} [Field K] (P a a' e : K) (hP : P ≠ 0) (ha : a ≠ 0) (h vm N g i l : ℤ) :
    P ^ (-(h * i * ((N + g) - i))) * (P ^ (vm * i) * (a' ^ (-i) * P ^ (h * N * i))) *
        (P ^ (2 * h * ((i - l) * (g - l))) * (P ^ (h * (l * (g - l))) * e)) *
        (P ^ (vm * (i - l)) * (a ^ (i - l) * P ^ (h * (N + g) * (i - l))))⁻¹ =
      ((a * a')⁻¹) ^ i * ((a * P ^ vm) ^ l * e) * P ^ (-(h * (i - l) * (N - (i - l)))) := by
  have e1 : P ^ (-(h * i * ((N + g) - i))) * P ^ (vm * i) * P ^ (h * N * i) * P ^ (2 * h * ((i - l) * (g - l))) *
      P ^ (h * (l * (g - l))) * (P ^ (vm * (i - l)))⁻¹ * (P ^ (h * (N + g) * (i - l)))⁻¹ =
      P ^ (vm * l) * P ^ (-(h * (i - l) * (N - (i - l)))) := by
    rw [← zpow_neg, ← zpow_neg]
    simp only [← zpow_add₀ hP]
    congr 1
    ring
  have e2 : (a ^ (i - l))⁻¹ = (a ^ i)⁻¹ * a ^ l := by
    rw [zpow_sub₀ ha, inv_div, div_eq_mul_inv, mul_comm]
  calc _ = (P ^ (-(h * i * ((N + g) - i))) * P ^ (vm * i) * P ^ (h * N * i) * P ^ (2 * h * ((i - l) * (g - l))) *
      P ^ (h * (l * (g - l))) * (P ^ (vm * (i - l)))⁻¹ * (P ^ (h * (N + g) * (i - l)))⁻¹) *
        (a ^ (i - l))⁻¹ * a' ^ (-i) * e := by ring
    _ = (P ^ (vm * l) * P ^ (-(h * (i - l) * (N - (i - l))))) * ((a ^ i)⁻¹ * a ^ l) * a' ^ (-i) * e := by
      rw [e1, e2]
    _ = _ := by
      rw [inv_zpow, mul_zpow, mul_zpow, ← zpow_mul, mul_inv, zpow_neg a' i]
      ring

theorem hk_esymm_smul {K σ : Type} [Field K] [Fintype σ] (c : K) (f : σ → K) (l : ℕ) :
    MvPolynomial.eval (fun x => c * f x) (MvPolynomial.esymm σ K l) =
      c ^ l * MvPolynomial.eval f (MvPolynomial.esymm σ K l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.eval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.1 ht).2]

theorem hk_esymm_zero {K σ : Type} [Field K] [Fintype σ] (l : ℕ) (h : Fintype.card σ < l) :
    MvPolynomial.esymm σ K l = 0 := by
  rw [MvPolynomial.esymm, Finset.powersetCard_eq_empty.2 (by rwa [Finset.card_univ]), Finset.sum_empty]

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def eBe (v : X.Pl) (l : ℕ) : X.G.Kf :=
  MvPolynomial.eval (fun x : Fin (X.t + 1) => X.qh v x.val) (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)

theorem nC_cast (hp : (p : X.G.Kf) ≠ 0) (v : X.Pl) (i l : ℕ) :
    (nC X v i l : X.G.Kf) = (p : X.G.Kf) ^ (2 * hv X v * (((i - l : ℕ) : ℤ) * ((X.t + 1 - l : ℕ) : ℤ))) *
      ((p : X.G.Kf) ^ (hv X v * ((l : ℤ) * ((X.t + 1 - l : ℕ) : ℤ))) * eBe X v l) := by
  obtain ⟨k, hk⟩ := (X.std v).even
  have h1 : X.G.P.n' v / 2 = k := by omega
  have h2 : p ^ X.G.P.n' v = (p ^ k) ^ 2 := by rw [← pow_mul]; congr 1; omega
  have hQ : (((p ^ k : ℕ) : ℕ) : X.G.Kf) ≠ 0 := by push_cast; exact pow_ne_zero _ hp
  have hG := Formalism.InvariantFactorPaths.G7.gauss_elementary_symmetric X.G.Kf (p ^ k) (X.t + 1) l hQ
  have hf : Formalism.InvariantFactorPaths.G7.beFam ((p : X.G.Kf) ^ k) (X.t + 1) = fun x => X.qh v x.val := funext fun x => by
    have := beFam_eq X v x
    rwa [h1] at this
  have hb : Formalism.InvariantFactorPaths.G7.eF (Formalism.InvariantFactorPaths.G7.beFam ((p : X.G.Kf) ^ k) (X.t + 1)) l = eBe X v l := by
    unfold Formalism.InvariantFactorPaths.G7.eF eBe
    rw [hf]
  unfold nC
  rw [h2]
  push_cast at hG ⊢
  rw [hG, hb]
  unfold hv
  rw [h1]
  congr 1
  · rw [← pow_mul, ← pow_mul, ← zpow_natCast]
    congr 1
    push_cast
    ring
  · congr 1
    rw [← pow_mul, ← zpow_natCast]
    congr 1

theorem NN_succ (k1 t j : ℕ) : (NN k1 t (j + 1) : ℤ) = (NN k1 t j : ℤ) + ((t + 1 : ℕ) : ℤ) := by
  unfold NN
  push_cast
  ring

theorem hk_coef (hp : (p : X.G.Kf) ≠ 0) (a a' : X.G.Kf) (ha : a ≠ 0) (v : X.Pl) (j i l : ℕ) (hl : l ≤ i) :
    (p : X.G.Kf) ^ (-(hv X v * i * ((NN X.G.P.m X.t (j + 1) : ℤ) - i))) * cA X a' v j i * (nC X v i l : X.G.Kf) *
        (cC X a v j (i - l))⁻¹ =
      ((a * a')⁻¹) ^ i * (MvPolynomial.eval (fun x : Fin (X.t + 1) => (a * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
          (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) *
        (p : X.G.Kf) ^ (-(hv X v * ((i - l : ℕ) : ℤ) * ((NN X.G.P.m X.t j : ℤ) - ((i - l : ℕ) : ℤ)))) := by
  rw [hk_esymm_smul, nC_cast X hp]
  show _ = ((a * a')⁻¹) ^ i * ((a * (p : X.G.Kf) ^ (X.vm v (j + 1))) ^ l * eBe X v l) * _
  by_cases hg : l ≤ X.t + 1
  · have := hk_scal (p : X.G.Kf) a a' (eBe X v l) hp ha (hv X v) (X.vm v (j + 1)) (NN X.G.P.m X.t j : ℤ)
      ((X.t + 1 : ℕ) : ℤ) i l
    unfold cA cC
    rw [NN_succ, Nat.cast_sub hl, Nat.cast_sub hg, ← zpow_natCast ((a * a')⁻¹) i,
      ← zpow_natCast (a * (p : X.G.Kf) ^ (X.vm v (j + 1))) l]
    exact this
  · have h0 : eBe X v l = 0 := by
      unfold eBe
      rw [hk_esymm_zero l (by simpa using not_le.1 hg), map_zero]
    rw [h0]
    simp

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem hk_point (Y : Pend X) (hC : CountLoc) (hT : RestTmFQ X)
    (hp : (p : X.G.Kf) ≠ 0) {a a' : X.G.Kf} {cK : Y.Kc} (ha : a ≠ 0) (ha' : a' ≠ 0) (v : X.Pl) (j : ℕ)
    (hTh : ThEq Y a a' v j) {Cl Yb : Type} [Fintype Cl] [Fintype Yb] {wt : Cl → ℕ} {La : Cl → Yb → X.Lt j}
    (hS : KSum Y j cK Cl Yb wt La) (hAd : KAdj Y j Cl Yb wt La)
    (i : ℕ) (F : X.Fm j) (hF : F ∈ X.FQ j) (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup)
    (hL' : (X.Pj (j + 1)).IsLatTup L') :
    X.Tm v i (j + 1) (X.Kz j F) c' L' =
      ∑ l ∈ range (i + 1), (cA X a' v j i * (nC X v i l : X.G.Kf) * (cC X a v j (i - l))⁻¹) •
        X.Kz j (X.Tm v (i - l) j F) c' L' := by
  obtain ⟨hlat, _, h4⟩ := hS
  apply MvPolynomial.map_injective (algebraMap X.G.Kf Y.Kc) (algebraMap X.G.Kf Y.Kc).injective
  have eT : X.Tm v i (j + 1) (X.Kz j F) c' L' =
      ∑ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
        X.Kz j F c' (Function.update L' (X.vJ (j + 1) v) L1) :=
    Tminus_eq (X.Pj (j + 1)) (X.vJ (j + 1) v) i (X.Kz j F c') L'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eT, map_sum, map_sum]
  have eL : ∀ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' (Function.update L' (X.vJ (j + 1) v) L1)) =
        ∑ x : Cl, (((wt x : Y.Kc))⁻¹ * cK) • ∑ y : Yb,
          Y.ker j (La x y) (c', Function.update L' (X.vJ (j + 1) v) L1) (F (La x y).1 (La x y).2) := by
    intro L1 hL1
    exact h4 F hF c' _ (hk_latTup_update _ hL' _ L1 ((mem_EE _).1 hL1).1)
  rw [Finset.sum_congr rfl eL, Finset.sum_comm]
  have eL2 : ∀ x ∈ (Finset.univ : Finset Cl), ∑ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
      (((wt x : Y.Kc))⁻¹ * cK) • ∑ y : Yb,
        Y.ker j (La x y) (c', Function.update L' (X.vJ (j + 1) v) L1) (F (La x y).1 (La x y).2) =
      (((wt x : Y.Kc))⁻¹ * cK) • ∑ y : Yb, (cA X a' v j i • ∑ l ∈ range (i + 1), (nC X v i l : X.G.Kf) •
        ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) (i - l) ((La x y).2 (X.vJ j v)),
          (cC X a v j (i - l))⁻¹ •
            Y.ker j ((La x y).1, Function.update (La x y).2 (X.vJ j v) A1) (c', L') (F (La x y).1 (La x y).2)) := by
    intro x _
    rw [← Finset.smul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    exact ker_dn_sum hC hp ha ha' hTh (La x y) (hlat x y) c' L' hL' i _
  rw [Finset.sum_congr rfl eL2]
  have eR : ∀ l ∈ range (i + 1), MvPolynomial.map (algebraMap X.G.Kf Y.Kc)
      ((cA X a' v j i * (nC X v i l : X.G.Kf) * (cC X a v j (i - l))⁻¹) • X.Kz j (X.Tm v (i - l) j F) c' L') =
      (cA X a' v j i * (nC X v i l : X.G.Kf) * (cC X a v j (i - l))⁻¹) • (cK • ∑ x : Cl,
        ((wt x : Y.Kc))⁻¹ • ∑ y : Yb, ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) (i - l) ((La x y).2 (X.vJ j v)),
          Y.ker j ((La x y).1, Function.update (La x y).2 (X.vJ j v) A1) (c', L') (F (La x y).1 (La x y).2)) := by
    intro l _
    rw [map_smulK Y, h4 _ (hT v (i - l) j F hF) c' L' hL', hAd v (i - l) F hF (c', L') hL',
      Finset.smul_sum (r := cK)]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_smul, mul_comm]
  rw [Finset.sum_congr rfl eR]
  have hs : ∀ (r : X.G.Kf) (z : XspC (X.Pj (j + 1)) Y.Kc), r • z = algebraMap X.G.Kf Y.Kc r • z :=
    fun r z => (algebraMap_smul Y.Kc r z).symm
  simp only [hs, Finset.smul_sum, smul_smul]
  symm
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun A1 _ => ?_
  congr 1
  simp only [map_mul, map_inv₀, map_natCast]
  ring

theorem heckeCondition_of_adm (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) (hA : admitted D X Y) (hC : CountLoc) (hT : RestTmFQ X) :
    RestHecke X := by
  obtain ⟨_, _, _, _, _, h3b, h4, h5, h5b, h6, _, _, _⟩ := hA
  intro v
  have hfr := frac_of_place X v
  have he := eO_pos X v
  have hp : (p : X.G.Kf) ≠ 0 := pKf_ne Y
  have h5' : ∀ j, ∃ a a' : X.G.Kf, j < X.mm → (X.vEqK a 0 ∧ X.vEqK a' 0 ∧ ThEq Y a a' v j) := by
    intro j
    by_cases hj : j < X.mm
    · obtain ⟨u, u', h1, h2, h3⟩ := h5 v j hj
      exact ⟨u, u', fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨1, 1, fun h => absurd h hj⟩
  choose a a' H using h5'
  refine ⟨fun l => (a (l - 1) * a' (l - 1))⁻¹, fun l => a (l - 1) * (p : X.G.Kf) ^ (X.vm v l), ?_, ?_, ?_⟩
  · intro l hl
    rw [Finset.mem_Icc] at hl
    obtain ⟨h1, h2, _⟩ := H (l - 1) (by omega)
    have := vEqK_inv X hfr (vEqK_mul X hfr h1 h2)
    simpa using this
  · intro l hl
    rw [Finset.mem_Icc] at hl
    obtain ⟨h1, _, _⟩ := H (l - 1) (by omega)
    have := vEqK_mul X hfr h1 (vEqK_ppow X hfr he (X.vm v l))
    simpa using this
  · intro j hj i F hF
    obtain ⟨h1, h2, hTh⟩ := H j hj
    obtain ⟨cK, Cl, Yb, iC, iY, wt, La, hS, hAd⟩ := ksa_of_adm D h4 h5b h6 hj
    have ha := vEqK.ne_zero X h1
    have ha' := vEqK.ne_zero X h2
    show X.ecal v i (j + 1) (X.Kz j F) = ((a j * a' j)⁻¹ ^ i) • X.Kz j (∑ l ∈ range (i + 1),
      (MvPolynomial.eval (fun x : Fin (X.t + 1) => (a j * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
        (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) • X.ecal v (i - l) j F)
    funext c' L'
    by_cases hL' : (X.Pj (j + 1)).IsLatTup L'
    · have eR : X.Kz j (∑ l ∈ range (i + 1),
          (MvPolynomial.eval (fun x : Fin (X.t + 1) => (a j * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
            (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) • X.ecal v (i - l) j F) =
          ∑ l ∈ range (i + 1),
            ((MvPolynomial.eval (fun x : Fin (X.t + 1) => (a j * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
              (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) *
              (p : X.G.Kf) ^ (-(hv X v * ((i - l : ℕ) : ℤ) * ((NN X.G.P.m X.t j : ℤ) - ((i - l : ℕ) : ℤ))))) •
              X.Kz j (X.Tm v (i - l) j F) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        unfold Sys.ecal
        rw [map_smul, map_smul, smul_smul]
        rfl
      rw [eR]
      show ((p : X.G.Kf) ^ (-(hv X v * i * ((NN X.G.P.m X.t (j + 1) : ℤ) - i)))) •
        X.Tm v i (j + 1) (X.Kz j F) c' L' = _
      rw [hk_point Y hC hT hp ha ha' v j hTh hS hAd i F hF c' L' hL']
      simp only [Pi.smul_apply, Finset.sum_apply, Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun l hl => ?_
      congr 1
      have := hk_coef X hp (a j) (a' j) ha v j i l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))
      rw [mul_assoc ((a j * a' j)⁻¹ ^ i)] at this
      rw [← this]
      ring
    · have e1 : X.Tm v i (j + 1) (X.Kz j F) c' L' = 0 :=
        (restTmEquiv X (j + 1) v i _ (Eqv_of_FQ X (h3b j hj F hF))).1 c' L' hL'
      have e2 : X.ecal v i (j + 1) (X.Kz j F) c' L' = 0 := by
        show ((p : X.G.Kf) ^ (-(hv X v * i * ((NN X.G.P.m X.t (j + 1) : ℤ) - i)))) •
          X.Tm v i (j + 1) (X.Kz j F) c' L' = 0
        rw [e1, smul_zero]
      rw [e2]
      have hmem : X.Kz j (∑ l ∈ range (i + 1),
          (MvPolynomial.eval (fun x : Fin (X.t + 1) => (a j * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
            (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) • X.ecal v (i - l) j F) ∈ X.FQ (j + 1) :=
        h3b j hj _ (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
          (Submodule.smul_mem _ _ (hT v (i - l) j F hF)))
      rw [Pi.smul_apply, Pi.smul_apply, FQ_zero_off X hmem c' L' hL', smul_zero]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RestrictedHeckeIntegralOfEdges
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

section PlacesLevel

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

def RestWeylEdge : Prop :=
  ∀ (v : Fin P.nV) (i : ℕ) (L : P.Tup) (L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)),
    P.IsLatTup L → IsEdge p (P.n' v) i ⟨L'', L v⟩ →
    ∀ x ∈ P.HtupW (Function.update L v L''), ((p : Kf) ^ (Ar i (P.lam0 v))) • x ∈ P.HtupW L

theorem latTup_update {L : P.Tup} (hL : P.IsLatTup L) {v : Fin P.nV}
    {A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)} (hA : IsLattice (P.W v) A) :
    P.IsLatTup (Function.update L v A) := by
  intro u
  by_cases h : u = v
  · subst h
    have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L u A u = A :=
      Function.update_self u A L
    exact e.symm ▸ hA
  · have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v A u = L u :=
      Function.update_of_ne h A L
    exact e.symm ▸ hL u

theorem Tminus_mem (h : RestWeylEdge P) (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp)
    (hF : ∀ L, P.IsLatTup L → F L ∈ P.HtupW L) (L : P.Tup) (hL : P.IsLatTup L) :
    ((p : Kf) ^ (Ar i (P.lam0 v))) • P.Tminus v i F L ∈ P.HtupW L := by
  rw [Tminus_eq, Finset.smul_sum]
  refine Submodule.sum_mem _ fun L'' hL'' => ?_
  have hE := (mem_EE P).1 hL''
  exact h v i L L'' hL hE _ (hF _ (latTup_update P hL hE.1))

end PlacesLevel

section Num

variable {n' k1 : ℕ} {p t m c r : ℕ} {TT : Finset (Fin n')} {a b : Fin n' → ℤ}
  {lam0 : Fin n' → Fin (k1 + 1) → ℤ} {w : ℕ → Fin n' → ℤ}

theorem neg_liftWt_le (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') (j : ℕ) (hj : j + 1 ≤ m)
    (x : Fin (k1 + (j + 1) * (t + 1) + 1)) :
    -liftWt t k1 (lam0 s) (fun l => w l s) (j + 1) x ≤ w (j + 1) s := by
  unfold liftWt
  split_ifs with hx
  · have e1 := h.dom s (Fin.le_last (⟨x.val, hx⟩ : Fin (k1 + 1)))
    have e2 := (h.w_low s).2
    have e3 := w_le h s (l := 1) (l' := j + 1) le_rfl (by omega) hj
    linarith
  · rw [neg_neg]
    refine w_le h s (Nat.le_add_left 1 _) ?_ hj
    have hx2 := x.isLt
    have : (x.val - (k1 + 1)) / (t + 1) < j + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    omega

theorem card_filter_lt_le (N i : ℕ) : (univ.filter fun x : Fin N => x.val < i).card ≤ i := by
  have := Finset.card_le_card_of_injOn (s := univ.filter fun x : Fin N => x.val < i) (t := range i)
    (fun x => x.val) (fun x hx => by
      have hx' := (mem_filter.1 (Finset.mem_coe.1 hx)).2
      exact Finset.mem_coe.2 (mem_range.2 hx')) (fun x _ y _ hxy => Fin.ext hxy)
  rwa [card_range] at this

theorem Ar_lift_le (h : Std p n' k1 t m c r TT a b lam0 w) (j i : ℕ) (hj : j + 1 ≤ m) (hi : i ≤ k1 + 1) :
    Ar i (fun s => liftWt t k1 (lam0 s) (fun l => w l s) (j + 1)) ≤ Nprime lam0 w (j + 1) i := by
  unfold Ar Nprime
  rw [← Finset.sum_filter_not_add_sum_filter univ (fun s : Fin n' => IsOddPos s), Finset.mul_sum]
  refine add_le_add (le_of_eq ?_) ?_
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [mem_filter] at hs
    have he : Even s.val := by
      rw [Nat.even_iff]
      have := hs.2
      unfold IsOddPos at this
      omega
    refine Finset.sum_bij (fun x _ => x.val + 1) ?_ ?_ ?_ ?_
    · intro x hx
      rw [mem_filter] at hx
      rw [mem_Icc]
      omega
    · intro x _ x' _ hxx
      exact Fin.ext (by omega)
    · intro y hy
      rw [mem_Icc] at hy
      exact ⟨⟨y - 1, by omega⟩, by rw [mem_filter]; exact ⟨mem_univ _, by show y - 1 < i; omega⟩,
        by show y - 1 + 1 = y; omega⟩
    · intro x hx
      rw [mem_filter] at hx
      unfold lamAt
      rw [if_pos he]
      show liftWt t k1 (lam0 s) (fun l => w l s) (j + 1) x = _
      unfold liftWt
      rw [dite_eq_left (by omega : x.val < k1 + 1)]
      exact (lamI_fin lam0 s ⟨x.val, by omega⟩).symm
  · refine Finset.sum_le_sum fun s hs => ?_
    rw [mem_filter] at hs
    have he : ¬ Even s.val := by
      rw [Nat.even_iff]
      have := hs.2
      unfold IsOddPos at this
      omega
    have hw0 : 0 ≤ w (j + 1) s := by
      have e2 := (h.w_low s).1
      have e3 := w_le h s (l := 1) (l' := j + 1) le_rfl (by omega) hj
      have : (0 : ℤ) ≤ c := Int.natCast_nonneg c
      linarith
    have h1 : ∑ x : Fin (k1 + (j + 1) * (t + 1) + 1) with x.val < i,
        lamAt (fun s => liftWt t k1 (lam0 s) (fun l => w l s) (j + 1)) s x ≤
        (univ.filter fun x : Fin (k1 + (j + 1) * (t + 1) + 1) => x.val < i).card • w (j + 1) s := by
      refine Finset.sum_le_card_nsmul _ _ _ fun x _ => ?_
      unfold lamAt
      rw [if_neg he]
      exact neg_liftWt_le h s j hj x.rev
    refine le_trans h1 ?_
    rw [nsmul_eq_mul]
    have h2 : ((univ.filter fun x : Fin (k1 + (j + 1) * (t + 1) + 1) => x.val < i).card : ℤ) ≤ i := by
      exact_mod_cast card_filter_lt_le _ i
    exact mul_le_mul_of_nonneg_right h2 hw0

end Num

section SysLevel

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem TmInt {j : ℕ} (h : RestWeylEdge (X.Pj j)) (v : X.Pl) (i : ℕ) {F : X.Fm j} (hF : F ∈ X.Int j) :
    ((p : X.G.Kf) ^ (Ar i ((X.Pj j).lam0 (X.vJ j v)))) • X.Tm v i j F ∈ X.Int j := by
  rw [mem_Int_iff] at hF ⊢
  exact ⟨fun c L hL => Tminus_mem (X.Pj j) h (X.vJ j v) i (F c) (hF.1 c) L hL,
    Eqv_smul X _ (restTmEquiv X j v i F hF.2)⟩

theorem p_ne_zero (v : X.Pl) : (p : X.G.Kf) ≠ 0 := Rep.ne_zero X (frac_of_place X v) (Rep.ofP X)

theorem restTmFQ_of (h : ∀ j, RestWeylEdge (X.Pj j)) : RestTmFQ X := by
  intro v i j F hF
  have hp := p_ne_zero X v
  have hle : X.FQ j ≤ (X.FQ j).comap (TmLin X v i j) := by
    refine Submodule.span_le.2 fun G hG => ?_
    show X.Tm v i j G ∈ X.FQ j
    have h1 := TmInt X (h j) v i hG
    have h2 : ((p : X.G.Kf) ^ (Ar i ((X.Pj j).lam0 (X.vJ j v))))⁻¹ •
        (((p : X.G.Kf) ^ (Ar i ((X.Pj j).lam0 (X.vJ j v)))) • X.Tm v i j G) ∈ X.FQ j :=
      Submodule.smul_mem _ _ (Submodule.subset_span h1)
    rwa [smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ hp), one_smul] at h2
  exact hle hF

theorem restricted_hecke_integral_of_edges (h : ∀ j, RestWeylEdge (X.Pj j)) : HeckeIntegralLevel X := by
  intro v j hj i hi F hF
  rw [mem_Icc] at hi
  have hp := p_ne_zero X v
  unfold Sys.Tt
  rw [if_neg (by omega)]
  have h1 := TmInt X (h (j + 1)) v i hF
  have hle : Ar i ((X.Pj (j + 1)).lam0 (X.vJ (j + 1) v)) ≤ Nprime (X.G.P.lam0 v) (X.w v) (j + 1) i :=
    Ar_lift_le (X.std v) j i hj (by have := (X.std v).two_r; omega)
  obtain ⟨d, hd⟩ := Int.le.dest hle
  rw [← hd, zpow_add₀ hp, zpow_natCast, mul_comm, mul_smul]
  have e : ∀ y : X.Fm (j + 1), ((p : X.G.Kf) ^ d) • y = ((p : X.G.O) ^ d) • y := by
    intro y
    rw [← algebraMap_smul X.G.Kf ((p : X.G.O) ^ d) y, map_pow, map_natCast]
  rw [e]
  exact Submodule.smul_mem _ _ h1

end SysLevel

section EdgeProof

open Formalism.MainNotions.G.LatticeSystems MvPolynomial

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem tenV_scale (v : Fin P.nV)
    (M M' : ∀ u, Submodule O (MvPolynomial (Fin (P.n' u) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf)) (c : Kf)
    (hv : ∀ F ∈ M v, c • F ∈ M' v) (hu : ∀ u, u ≠ v → M u ≤ M' u) :
    ∀ x ∈ P.tenV M, c • x ∈ P.tenV M' := by
  classical
  have key : P.tenV M ≤ (P.tenV M').comap ((LinearMap.lsmul Kf P.Xsp c).restrictScalars O) := by
    unfold Places.tenV
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    apply Submodule.subset_span
    refine ⟨Function.update F v (c • F v), ?_, ?_⟩
    · intro u
      by_cases h : u = v
      · subst h
        rw [Function.update_self]
        exact hv _ (hF u)
      · rw [Function.update_of_ne h]
        exact hu u h (hF u)
    · show c • ∏ u, P.vEmb u (F u) = ∏ u, P.vEmb u (Function.update F v (c • F v) u)
      rw [← Finset.mul_prod_erase Finset.univ (fun u => P.vEmb u (F u)) (Finset.mem_univ v),
        ← Finset.mul_prod_erase Finset.univ (fun u => P.vEmb u (Function.update F v (c • F v) u))
          (Finset.mem_univ v), Function.update_self, map_smul, smul_mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun u hu' => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hu')]
  exact fun x hx => key hx

theorem pKf_ne_of_place (v : Fin P.nV) : (p : Kf) ≠ 0 := by
  have hS := P.setting v
  have := hS.frac_alt
  have h1 : (p : P.Qq v) ≠ 0 := by
    have h2 : algebraMap (P.W v) (P.Qq v) (p : P.W v) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (P.W v) (P.Qq v))).2 hS.p_unif.ne_zero
    rwa [map_natCast] at h2
  have h3 : P.ι v (p : P.Qq v) ≠ 0 := (map_ne_zero (P.ι v)).2 h1
  rwa [map_natCast] at h3

theorem la_tw_diag (v : Fin P.nV) (s i : ℕ) (g : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) :
    la_tw (P.ι v) (P.σ v) s (g * Matrix.diagonal fun c => if c.val < i then ((p : P.Qq v))⁻¹ else 1) =
      la_tw (P.ι v) (P.σ v) s g * lb_D (P.m + 1) i (algebraMap O Kf (p : O)) := by
  unfold la_tw lb_D
  rw [map_mul]
  congr 1
  rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext c
  show (P.ι v).comp ((P.σ v ^ s : P.Qq v ≃+* P.Qq v) : P.Qq v →+* P.Qq v) (if c.val < i then ((p : P.Qq v))⁻¹ else 1) = _
  split_ifs
  · rw [map_inv₀, map_natCast, map_natCast]
  · rw [map_one]

theorem restWeylEdge : RestWeylEdge P := by
  intro v i L L'' hL hE x hx
  have hS := P.setting v
  have := hS.frac_alt
  have hinj : Function.Injective (algebraMap O Kf) := by
    have := hS.frac_O
    exact IsFractionRing.injective O Kf
  have hp := pKf_ne_of_place P v
  have hw : algebraMap O Kf (p : O) ≠ 0 := by rwa [map_natCast]
  obtain ⟨g, hg, hsrc, htgt⟩ := lc_main p (P.n' v) i (P.m + 1) hS.p_unif hS.res_card
    (by have := hS.five_le; omega) (by have := hS.two_le; omega) ⟨L'', L v⟩ hE
  have hsrc' : L'' = colSpan (P.W v) g := hsrc
  have htgt' : L v = colSpan (P.W v) (g * Matrix.diagonal fun c => if c.val < i then ((p : P.Qq v))⁻¹ else 1) := htgt
  have hfrob : ∀ x : P.W v, ∃ y : P.W v, P.σ v (algebraMap (P.W v) (P.Qq v) x) = algebraMap (P.W v) (P.Qq v) y := by
    intro x
    obtain ⟨y, hy⟩ := hS.frob x
    exact ⟨_, hy⟩
  have hloc : ∀ y ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val L''),
      ((p : Kf) ^ (Ar i (P.lam0 v))) • y ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val (L v)) := by
    intro y hy
    have h1 := lb_tensor O Kf (fun s => Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val L''))
      (fun s => Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val (L v)))
      (fun s => (p : Kf) ^ (∑ t : Fin (P.m + 1) with t.val < i, lamAt (P.lam0 v) s t)) (by
        intro s F hF
        rw [hsrc', la_extO (P.ι v) (P.σ v) (P.j v) hfrob hS.ι_comp] at hF
        rw [htgt', la_extO (P.ι v) (P.σ v) (P.j v) hfrob hS.ι_comp, la_tw_diag]
        have h2 := dl_pos O Kf hinj P.m i (lamAt (P.lam0 v) s) (p : O) hw _ (la_tw_det _ _ s.val g hg) F hF
        rwa [map_natCast] at h2 ⊢) y hy
    rw [lb_zpow_sum _ hp] at h1
    exact h1
  unfold Places.HtupW at hx ⊢
  refine tenV_scale P v _ _ _ ?_ ?_ x hx
  · intro F hF
    have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v L'' v = L'' :=
      Function.update_self v L'' L
    have hF' : F ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val L'') := by
      have h0 : F ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val
        (Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v L'' v)) := hF
      rwa [e] at h0
    exact hloc F hF'
  · intro u hu F hF
    have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v L'' u = L u :=
      Function.update_of_ne hu L'' L
    have h0 : F ∈ HtenW O (P.lam0 u) (fun s => extO O (P.ι u) (P.σ u) s.val
      (Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v L'' u)) := hF
    rwa [e] at h0

end EdgeProof

section Final

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem restTmFQ : RestTmFQ X := restTmFQ_of X fun j => restWeylEdge (X.Pj j)

theorem restricted_hecke_integral : HeckeIntegralLevel X := restricted_hecke_integral_of_edges X fun j => restWeylEdge (X.Pj j)

end Final

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TsumRatTail
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

theorem tsum_rat_tail (g : ℕ → ℚ) (hs : Summable (fun e => (g e : ℝ))) (E N : ℕ) (Q : ℚ) (hQ1 : 1 < Q)
    (h4 : ∀ e, E ≤ e → g (e + N) = g e / Q) : ∃ q : ℚ, ∑' e, (g e : ℝ) = q := by
  have hsE : Summable (fun i => (g (i + E) : ℝ)) := (summable_nat_add_iff E).2 hs
  have h1 := hsE.sum_add_tsum_nat_add N
  have h2 : ∀ i, (g (i + N + E) : ℝ) = (g (i + E) : ℝ) / Q := by
    intro i
    rw [show i + N + E = i + E + N by omega, h4 (i + E) (by omega)]
    push_cast
    try rfl
  simp only [h2] at h1
  rw [tsum_div_const] at h1
  have h0 := hs.sum_add_tsum_nat_add E
  have hQ0 : (Q : ℝ) ≠ 0 := by
    have : (1 : ℝ) < Q := by exact_mod_cast hQ1
    linarith
  have hQ1' : (Q : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Q := by exact_mod_cast hQ1
    linarith
  have hT : ∑' i, (g (i + E) : ℝ) = (∑ i ∈ range N, (g (i + E) : ℝ)) * Q / (Q - 1) := by
    rw [eq_div_iff hQ1']
    field_simp at h1
    linarith
  refine ⟨∑ i ∈ range E, g i + (∑ i ∈ range N, g (i + E)) * Q / (Q - 1), ?_⟩
  rw [← h0, hT]
  push_cast
  ring

def fqT (P : ℕ) (α : ℤ) (c : ℕ → ℤ) (Ds : Finset ℕ) (e : ℕ) : ℚ :=
  if 2 * e + 1 ∈ Ds then 0 else max ((α : ℚ) / (P : ℚ) ^ (2 * e + 1) - (c e : ℚ)) 0

theorem fqT_cast (P : ℕ) (α : ℤ) (c : ℕ → ℤ) (Ds : Finset ℕ) (e : ℕ) :
    (if 2 * e + 1 ∈ Ds then (0 : ℝ) else max ((α : ℝ) / (P : ℝ) ^ (2 * e + 1) - (c e : ℝ)) 0) =
      (fqT P α c Ds e : ℝ) := by
  unfold fqT
  split_ifs
  · simp
  · push_cast
    try rfl

theorem tsum_rat (P N : ℕ) (hP : 2 ≤ P) (hN : 0 < N) (α : ℤ) (c : ℕ → ℤ) (hc : ∀ e, c (e + N) = c e)
    (Ds : Finset ℕ) :
    ∃ q : ℚ, ∑' e : ℕ, (if 2 * e + 1 ∈ Ds then (0 : ℝ) else
      max ((α : ℝ) / (P : ℝ) ^ (2 * e + 1) - (c e : ℝ)) 0) = q := by
  simp_rw [fqT_cast]
  by_cases hs : Summable (fun e => (fqT P α c Ds e : ℝ))
  swap
  · exact ⟨0, by rw [tsum_eq_zero_of_not_summable hs]; simp⟩
  have hP0 : (0 : ℚ) < P := by exact_mod_cast (by omega : 0 < P)
  have h1 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → 2 * e + 1 ∉ Ds := fun e he hmem => by
    have := Finset.le_sup (f := id) hmem
    simp only [id] at this
    omega
  have h2 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → |(α : ℚ)| * 2 < (P : ℚ) ^ (2 * e + 1) := by
    intro e he
    have a1 : α.natAbs * 2 < P ^ (2 * e + 1) :=
      calc α.natAbs * 2 < 2 * e + 1 := by omega
        _ < 2 ^ (2 * e + 1) := Nat.lt_two_pow_self
        _ ≤ P ^ (2 * e + 1) := Nat.pow_le_pow_left hP _
    have a2 : ((α.natAbs : ℕ) : ℚ) = |(α : ℚ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [← a2]
    exact_mod_cast a1
  have h2' : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → |(α : ℚ) / (P : ℚ) ^ (2 * e + 1)| < 1 / 2 := by
    intro e he
    have hpos : (0 : ℚ) < (P : ℚ) ^ (2 * e + 1) := pow_pos hP0 _
    rw [abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
    linarith [h2 e he]
  have hcK : ∀ k e, c (e + k * N) = c e := by
    intro k
    induction k with
    | zero => intro e; simp
    | succ k ih => intro e; rw [Nat.succ_mul, ← add_assoc, hc, ih]
  have h3 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → 0 ≤ c e := by
    intro e0 he0
    by_contra hneg
    have hneg : c e0 ≤ -1 := by omega
    have tend := hs.tendsto_atTop_zero
    obtain ⟨M, hM⟩ := (tend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists_forall_of_atTop
    have hge : M ≤ e0 + M * N := by nlinarith
    have hlt : (fqT P α c Ds (e0 + M * N) : ℝ) < 1 / 2 := hM _ hge
    have hlt' : fqT P α c Ds (e0 + M * N) < 1 / 2 := by
      have : (fqT P α c Ds (e0 + M * N) : ℝ) < ((1 / 2 : ℚ) : ℝ) := by push_cast; exact hlt
      exact Rat.cast_lt.1 this
    have hE1 : Ds.sup id + α.natAbs + 1 ≤ e0 + M * N := le_trans he0 (Nat.le_add_right _ _)
    unfold fqT at hlt'
    rw [if_neg (h1 _ hE1), hcK] at hlt'
    have b1 := abs_lt.1 (h2' _ hE1)
    have b2 : ((c e0 : ℤ) : ℚ) ≤ -1 := by exact_mod_cast hneg
    have b3 := le_max_left ((α : ℚ) / (P : ℚ) ^ (2 * (e0 + M * N) + 1) - (c e0 : ℚ)) 0
    linarith [b1.1]
  have h4 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e →
      fqT P α c Ds (e + N) = fqT P α c Ds e / (P : ℚ) ^ (2 * N) := by
    intro e he
    have he' : Ds.sup id + α.natAbs + 1 ≤ e + N := le_trans he (Nat.le_add_right _ _)
    unfold fqT
    rw [if_neg (h1 _ he), if_neg (h1 _ he'), hc]
    have hQ : (0 : ℚ) < (P : ℚ) ^ (2 * N) := pow_pos hP0 _
    rcases (h3 e he).eq_or_lt with h0 | h0
    · rw [← h0]
      simp only [Int.cast_zero, sub_zero]
      have : (α : ℚ) / (P : ℚ) ^ (2 * (e + N) + 1) = (α : ℚ) / (P : ℚ) ^ (2 * e + 1) / (P : ℚ) ^ (2 * N) := by
        rw [div_div, ← pow_add]
        congr 2
        ring
      rw [this, ← max_div_div_right hQ.le, zero_div]
    · have b2 : (1 : ℚ) ≤ ((c e : ℤ) : ℚ) := by exact_mod_cast h0
      have c1 := abs_lt.1 (h2' _ he)
      have c2 := abs_lt.1 (h2' _ he')
      rw [max_eq_right (by linarith [c2.2]), max_eq_right (by linarith [c1.2]), zero_div]
  have hQ1 : (1 : ℚ) < (P : ℚ) ^ (2 * N) := by
    have : (1 : ℚ) < P := by exact_mod_cast (by omega : 1 < P)
    exact one_lt_pow₀ this (by omega)
  exact tsum_rat_tail _ hs _ N _ hQ1 h4

theorem gA_rat {n' k1 : ℕ} (p t : ℕ) (hp : 2 ≤ p) (hn : 0 < n') (TT : Finset (Fin n'))
    (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ) : ∃ q : ℚ, gA p t TT lam0 w j = q := by
  have h1 : ∀ s : Fin n', ∃ q : ℚ, ∑' e : ℕ,
      (if 2 * e + 1 ∈ dSet TT s then (0 : ℝ) else
        max ((al TT lam0 s : ℝ) / (p : ℝ) ^ (2 * e + 1) - (cap t TT lam0 w j (posAdd s (2 * e + 1)) : ℝ)) 0) = q := by
    intro s
    apply tsum_rat p n' hp hn (al TT lam0 s) (fun e => cap t TT lam0 w j (posAdd s (2 * e + 1))) _ (dSet TT s)
    intro e
    have : posAdd s (2 * (e + n') + 1) = posAdd s (2 * e + 1) := by
      unfold posAdd
      apply Fin.ext
      show (s.val + (2 * (e + n') + 1)) % n' = (s.val + (2 * e + 1)) % n'
      have : s.val + (2 * (e + n') + 1) = s.val + (2 * e + 1) + 2 * n' := by ring
      rw [this, Nat.add_mul_mod_self_right]
    simp only [this]
  choose q hq using h1
  refine ⟨∑ s ∈ TT, q s - (∑ s : Fin n', ((NN k1 t j : ℚ) * lgp p (al TT lam0 s) +
      (NN k1 t (j - 1) : ℚ) * (NN k1 t j : ℚ) * lgp p (lsz t TT lam0 w j s)) +
    ∑ s ∈ TT, ((lgp p (al TT lam0 s) : ℚ)) ^ 2), ?_⟩
  unfold gA de
  simp only [hq]
  push_cast
  ring

theorem restRat {p : ℕ} [Fact p.Prime] (X : Sys p) : RatCondition X := by
  intro v j
  have h := X.std v
  exact gA_rat p X.t (by have := h.five_le; omega) (by have := h.two_le; omega) _ _ _ j

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime]

theorem linD (X : Sys p) : LinD X :=
  { Tt_add := Tt_add X
    Tt_smul := Tt_smul X
    yv_add := fun v F F' => (yvLin X v).map_add F F'
    yv_smul := fun v a F => (yvLin X v).map_smul a F
    yv_comm := fun v v' F =>
      funext fun i => Formalism.MainNotions.G.LatticeSystems.ef_yv_comm X.G.P v v' (F i) }

variable {X : Sys p}

theorem vGe_of_eO_zero (he : X.eO = 0) {j : ℕ} {F : X.Fm j} {g g' : ℝ} (h : X.vGe j F g) : X.vGe j F g' := by
  unfold Sys.vGe Sys.vsc at h ⊢
  simpa [he] using h

theorem low_term_bound_of_eO_eq_zero_of_aux0 (D : Formalism.BasicNotions.D7) (Y : Pend X) (he : X.eO = 0) (h0 : Conclusion0 D X) : LowTermBound D X Y := by
  intro Gn G0n PRn S VV _ _ _ _ F hFm
  have hPl : ∀ _ : X.Pl, False := fun v => by have := eO_pos X v; omega
  have hFint : F ∈ X.Int 0 := by
    unfold Sys.Iprod at hFm
    refine (Submodule.span_le.2 ?_) hFm
    rintro F' ⟨BB, _, Lv, _, _, F0, hF0, rfl⟩
    have hLv : Lv = [] := by
      cases Lv with
      | nil => rfl
      | cons v _ => exact (hPl v).elim
    subst hLv
    have h1 : F0 ∈ scale (1 : X.G.Kf) (X.Int 0) := by simpa [he] using hF0
    rw [scale_one] at h1
    exact h1
  have key : ∀ m' ≤ X.mm, X.chainK m' F ∈ X.Int m' := by
    intro m'
    induction m' with
    | zero => intro _; exact hFint
    | succ n ih =>
      intro h
      have := h0 n (by omega) _ (ih (by omega))
      exact (vGe_zero_iff X).1 (vGe_of_eO_zero he this)
  exact vGe_of_eO_zero he ((vGe_zero_iff X).2 (key X.mm le_rfl))

structure Rests (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) : Prop where

  S1 : Conclusion1 D X Y

  allPlacesExpansion : ExpansionsMultiply D X Y

  U2 : VolumeRatio₂ D X Y

  Ent : EntCondition X Y

theorem prv_and_kernel_commutation_up_to_units_of_rests (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y) (R : Rests D X Y) :
    Conclusion₂ D X Y ∧ KernelCommutationUpToUnits D X := by
  have hF : FormB X Y := formB D X Y hA
  have hH : RestHecke X := heckeCondition_of_adm D X Y hA countLoc (restTmFQ X)
  obtain ⟨_, _, _, _, h3, h3b, _, _, _, _, _, h8, _⟩ := hA
  have p2b := hecke_integral_of_forms D hF R.Ent R.U2
  have p3 := latticeChain_succ_of_partial D hF R.Ent R.U2 (restricted_hecke_integral X)
  have pAlt := alternate_expansion_of_relations X D hH (restTmFQ X) h3b p3 p2b
  have p4 := theorem_of_alternate_form X D pAlt
  have p5D : LowTermBound D X Y := by
    rcases Nat.eq_zero_or_pos X.eO with he | he
    · exact low_term_bound_of_eO_eq_zero_of_aux0 D Y he (form_valuation_of_bound D hF h3)
    · exact lift_bound_of_integrality D (isFractionRing_of_pos_eO Y he) (pKf_ne Y) (linD X) hF R.Ent p4
        (fun v F hFm => h8.2 v F hFm)
  exact ⟨⟨form_valuation_of_bound D hF h3, R.S1, R.allPlacesExpansion, slopeEstimate_of_lemmaB_slopeLine D hF R.Ent R.U2, theorem_A_entries_of_corollary D R.Ent (restRat X) R.U2, R.U2, p2b, p3, p4,
    ramifiedLattice_of_chain_estimates D R.U2 p5D, p5D⟩, pAlt⟩

theorem rests (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y) : Rests D X Y :=
  { S1 := theta_kernel_expansion D X Y hA
    allPlacesExpansion := expansions_multiply D X Y hA
    U2 := auxU_of_firstTheoremPlaceBound D (first_theorem_place_bound X Y D (restGc p) (eb_brJet X)) hA
    Ent := restEnt_of X Y D (second_lemma_place_bound X Y D (restGc p) (eb_brJet X))
      (hecke_place_bound X Y D (restGc p) (eb_brJet X)) hA }

theorem packet_statements_hold (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y) : Conclusion₂ D X Y :=
  (prv_and_kernel_commutation_up_to_units_of_rests D Y hA (rests D Y hA)).1

theorem stmt_proved (D : Formalism.BasicNotions.D7) : Stmt D :=
  ⟨fun _ _ _ Y hA => packet_statements_hold D Y hA, relative_presentation_of_d7 D⟩

theorem stmtAt_proved (D : Formalism.BasicNotions.D7) : ErrorExponentStatement D :=
  fun _ _ _ _ _ Y _ hA => packet_statements_hold D Y hA

end Formalism.MainNotions.FormalGroupSystem.Pf
