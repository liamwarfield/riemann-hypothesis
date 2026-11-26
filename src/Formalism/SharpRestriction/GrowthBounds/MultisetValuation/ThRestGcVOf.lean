module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TwoSumsCondition
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaGeCOfNorm

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ThRestGcVOf
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF Gser)

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

theorem th_GtV_eq (j : ℕ) (v : X.Pl) (c c' : K0 p) :
    ea_GtV X j v c c' = ren (Sum.map (Sigma.mk v) (Sigma.mk v))
      (Gt p (Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) c c') := by
  unfold ea_GtV Gt
  rw [th_ren_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [th_ren_ren]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem th_restGcV_of (hG : RestGc p) : ea_RestGcV X := by
  intro c hc j v K' _ _ vp hvp μ hμ0 hμ
  have hs := X.std v
  obtain ⟨u, hu, V, hV, heq⟩ := hG hs.five_le c hc (X.G.P.n' v) (NN X.G.P.m X.t j)
    (NN X.G.P.m X.t (j + 1)) hs.two_le hs.even (X.om v) K' vp hvp μ hμ0 hμ
  let ρ : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) → X.ZA j := fun z => ⟨v, z⟩
  refine ⟨u, hu, ren ρ V, th_IntR_ren ρ hV, ?_⟩
  have hT : MvPowerSeries.HasSubst (tOf vp μ (X.coordZA K' j)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (th_tOf_const vp μ hμ0 _ (coordZA_const X K' j))
  have hT' : MvPowerSeries.HasSubst
      (tOf vp μ (coordZ (r0 := NN X.G.P.m X.t j) (r1 := NN X.G.P.m X.t (j + 1)) (X.om v) K' 1)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (th_tOf_const vp μ hμ0 _ (coordZ_const (X.om v) K' 1))
  have hg : MvPowerSeries.constantCoeff
      (-(MvPowerSeries.map (algebraMap (K0 p) K'))
        (Gt p (Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
          (wK p c) (wK p ((sigW p) c)))) = 0 := by
    simp [th_Gt_const]
  have hh : MvPowerSeries.constantCoeff
      (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * hhS p K' u :
        MvPowerSeries (Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) K')) = 0 := by
    simp [hhS_const]
  have hfun : (fun k => tOf vp μ (X.coordZA K' j) (Sum.map (Sigma.mk v) (Sigma.mk v) k)) =
      fun k => ren ρ (tOf vp μ (coordZ (X.om v) K' 1) k) := by
    funext k
    simp only [tOf]
    rw [th_coordZA_eq, th_ren_psubst ρ (coordZ_const (X.om v) K' 1 k)]
  rw [th_GtV_eq, th_map_ren, ← th_ren_neg, ← th_ren_expK _ hg, th_subst_ren _ hT, hfun,
    ← th_ren_subst ρ hT', heq, th_ren_mul, th_ren_expK ρ hh, th_ren_neg, th_ren_mul, th_ren_C,
    th_hhA_eq]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EbBrJet
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EbWMapDomain
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Gen

variable {σ κ τ τ' K : Type} [Field K]

def eb_w (F : MvPowerSeries σ K) (n : σ →₀ ℕ) : K :=
  (∏ x ∈ n.support, ((n x).factorial : K)) * MvPowerSeries.coeff n F

def eb_J (F : MvPowerSeries σ K) (Q : MvPolynomial σ (MvPolynomial τ K)) : MvPolynomial τ K :=
  ∑ n ∈ Q.support, eb_w F n • AddMonoidAlgebra.coeff Q n

theorem eb_J_subset (F : MvPowerSeries σ K) (Q : MvPolynomial σ (MvPolynomial τ K)) (S : Finset (σ →₀ ℕ))
    (h : Q.support ⊆ S) : eb_J F Q = ∑ n ∈ S, eb_w F n • AddMonoidAlgebra.coeff Q n := by
  unfold eb_J
  apply Finset.sum_subset h
  intro n _ hn
  rw [MvPolynomial.notMem_support_iff.1 hn, smul_zero]

theorem eb_applyD (P : MvPolynomial σ (MvPolynomial τ ℤ)) (F : MvPowerSeries σ K) :
    applyD P F = eb_J F (MvPolynomial.map (MvPolynomial.map (Int.castRingHom K)) P) := by
  rw [eb_J_subset F _ P.support (MvPolynomial.support_map_subset _ _)]
  unfold applyD eb_w
  apply Finset.sum_congr rfl
  intro n _
  rw [MvPolynomial.coeff_map]

theorem eb_w_mapDomain (ε : κ → σ) (hε : Function.Injective ε) (F : MvPowerSeries σ K) (n : κ →₀ ℕ) :
    eb_w F (n.mapDomain ε) = eb_w (resV ε F) n := by
  classical
  unfold eb_w
  rw [Finsupp.mapDomain_support_of_injective hε, Finset.prod_image (fun a _ b _ h => hε h)]
  congr 1
  apply Finset.prod_congr rfl
  intro y _
  rw [Finsupp.mapDomain_apply_of_injective hε]

theorem eb_J_rename (ε : κ → σ) (hε : Function.Injective ε) (F : MvPowerSeries σ K)
    (Q : MvPolynomial κ (MvPolynomial τ K)) : eb_J F (MvPolynomial.rename ε Q) = eb_J (resV ε F) Q := by
  classical
  unfold eb_J
  rw [MvPolynomial.support_rename_of_injective hε,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hε h)]
  apply Finset.sum_congr rfl
  intro n _
  rw [MvPolynomial.coeff_rename_mapDomain ε hε, eb_w_mapDomain ε hε]

theorem eb_J_map (φ : τ' → τ) (G : MvPowerSeries κ K) (Pc : MvPolynomial κ (MvPolynomial τ' K)) :
    eb_J G (MvPolynomial.map (MvPolynomial.rename φ : MvPolynomial τ' K →ₐ[K] MvPolynomial τ K).toRingHom Pc) =
      MvPolynomial.rename φ (Formalism.DworkPowerSeriesWeights.jetPairPoly Pc G) := by
  rw [eb_J_subset G _ Pc.support (MvPolynomial.support_map_subset _ _)]
  unfold Formalism.DworkPowerSeriesWeights.jetPairPoly
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [MvPolynomial.coeff_map, map_mul, MvPolynomial.rename_C, MvPolynomial.smul_eq_C_mul, mul_comm]
  congr 2
  unfold eb_w Formalism.DworkPowerSeriesWeights.mfact Finsupp.prod
  rw [Nat.cast_prod]

end Gen

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

def eb_phi (v : X.Pl) (j : ℕ) : ea_S X v × Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t j) → X.FrI j :=
  fun y => ⟨v, ((ea_e X v).symm y.1, y.2.1.val, y.2.2)⟩

theorem eb_phi_inj (v : X.Pl) (j : ℕ) : Function.Injective (eb_phi X v j) := by
  rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
  simp only [eb_phi, Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [h1, Fin.ext h2, h3]

theorem eb_eps_inj (v : X.Pl) (j : ℕ) : Function.Injective (ea_eps X v j) := by
  rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
  simp only [ea_eps, Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [h1, h2, h3]

theorem eb_fac (v : X.Pl) (j : ℕ) (K' : Type) [Field K'] (I : X.ColCh j) (s : ea_S X v) (c : Fin (ea_colN X v j s)) :
    MvPolynomial.rename (ea_eps X v j) (MvPolynomial.map
      (MvPolynomial.rename (eb_phi X v j) : MvPolynomial _ K' →ₐ[K'] MvPolynomial _ K').toRingHom
      (Matrix.of fun (r r' : Fin (ea_hts X v j s c)) =>
        (∑ a : Fin (NN X.G.P.m X.t j), MvPolynomial.C (MvPolynomial.X
            (s, (⟨r.val, lt_of_lt_of_le r.isLt (ea_hp X v j s c)⟩ : Fin (NN X.G.P.m X.t j)), a)) *
          MvPolynomial.X (s, a, ea_Ic X v j I s c r') :
        MvPolynomial (Formalism.DworkPowerSeriesWeights.ZV (2 * (X.G.P.n' v / 2)) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
          (MvPolynomial (ea_S X v × Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t j)) K'))).det) =
    MvPolynomial.map (MvPolynomial.map (Int.castRingHom K')) (X.colFac j I v ((ea_e X v).symm s) c.val) := by
  unfold Sys.colFac
  rw [RingHom.map_det, AlgHom.map_det, RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun r r' => ?_)
  change _ = MvPolynomial.map (MvPolynomial.map (Int.castRingHom K')) (∑ a : Fin (NN X.G.P.m X.t j),
    MvPolynomial.C (MvPolynomial.X (⟨v, ((ea_e X v).symm s, r.val, a)⟩ : X.FrI j)) *
      MvPolynomial.X (⟨v, ((ea_e X v).symm s, a, I v ((ea_e X v).symm s) c.val r'.val)⟩ : X.ZA j))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.rename_C, MvPolynomial.rename_X, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]
  rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

def eb_Pc (v : X.Pl) (j : ℕ) (K' : Type) [Field K'] (I : X.ColCh j) :
    MvPolynomial (Formalism.DworkPowerSeriesWeights.ZV (2 * (X.G.P.n' v / 2)) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
      (MvPolynomial (ea_S X v × Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t j)) K') :=
  ∏ s : ea_S X v, Formalism.DworkPowerSeriesWeights.minorProd
    (fun (i : Fin (NN X.G.P.m X.t j)) (b : Fin (NN X.G.P.m X.t (j + 1))) =>
      (∑ a : Fin (NN X.G.P.m X.t j), MvPolynomial.C (MvPolynomial.X (s, i, a)) * MvPolynomial.X (s, a, b) :
        MvPolynomial (Formalism.DworkPowerSeriesWeights.ZV (2 * (X.G.P.n' v / 2)) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
          (MvPolynomial (ea_S X v × Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t j)) K')))
    (ea_hts X v j s) (ea_hp X v j s) (ea_Ic X v j I s)

theorem eb_poly (v : X.Pl) (j : ℕ) (K' : Type) [Field K'] (I : X.ColCh j) :
    MvPolynomial.map (MvPolynomial.map (Int.castRingHom K')) (X.PIv j I v) =
      MvPolynomial.rename (ea_eps X v j) (MvPolynomial.map
        (MvPolynomial.rename (eb_phi X v j) : MvPolynomial _ K' →ₐ[K'] MvPolynomial _ K').toRingHom
        (eb_Pc X v j K' I)) := by
  unfold Sys.PIv eb_Pc Formalism.DworkPowerSeriesWeights.minorProd
  simp only [map_prod]
  refine (Fintype.prod_equiv (ea_e X v).symm _ _ fun s => ?_).symm
  rw [Finset.prod_range]
  exact Finset.prod_congr rfl fun c _ => eb_fac X v j K' I s c

theorem eb_jet (v : X.Pl) (j : ℕ) (K' : Type) [Field K'] (F : MvPowerSeries (X.ZA j) K') (I : X.ColCh j) :
    applyD (X.PIv j I v) F = MvPolynomial.rename (eb_phi X v j)
      (Formalism.DworkPowerSeriesWeights.frameJet (ea_colN X v j) (ea_hts X v j) (ea_hp X v j) (ea_Ic X v j I) (resV (ea_eps X v j) F)) := by
  rw [eb_applyD, eb_poly, eb_J_rename _ (eb_eps_inj X v j), eb_J_map]
  rfl

theorem eb_brJet : ea_BrJet X := by
  intro v j K' _ F I n
  rw [eb_jet]
  by_cases h : ∃ n', Finsupp.mapDomain (eb_phi X v j) n' = n
  · obtain ⟨n', rfl⟩ := h
    exact Or.inr ⟨n', MvPolynomial.coeff_rename_mapDomain _ (eb_phi_inj X v j) _ n'⟩
  · exact Or.inl (MvPolynomial.coeff_rename_eq_zero _ _ _ fun u hu => absurd ⟨u, hu⟩ h)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
