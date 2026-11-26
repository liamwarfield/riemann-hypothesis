module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverPoly
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.LocalLevelIsKOneAtT
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.ThirdMomentLaw

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexHeckeEigenvectorDescendsToCoefficientFiel
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexHeckeEigenvectorDescendsToCoefficientFiel
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.PtLocalEig

theorem eig_descends : ∀ (D : D7) (M : Formalism.L2.MtFam D) (B : Formalism.L2.NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), μ = D.what₂.muTw w → ∀ (φ : FractionRing (B.Oc j w) →+* ℂ), (∀ x, φ (B.ec j w x) = D.what₂.embLL x) → ∀ (κ : PlE D.host → ℕ → FractionRing (B.Oc j w)) (y : D.what₂.Mt μ j), y ≠ 0 → (∀ v k, Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ Formalism.AUTREP.IsUnif D.host.E s.v ϖ ∧ (∀ (c : ℂ) (f f' : Formalism.AUTREP.GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W), Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') = c • Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k f + Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k f') ∧ Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) = φ (κ v k) • (M μ j h1 h2).real y) → ∃ e : B.V j w, e ≠ 0 ∧ ∀ v k, Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → B.hK j w v k e = κ v k • e := by
  intro D M B j w μ h1 h2 hμ φ hφ κ y hy hgen
  subst hμ
  classical
  haveI := Formalism.L2.finite_chooseBasisIndex (D := D) j w
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  have hjb := D.what₂.jMt_basis (D.what₂.muTw w) j b
  let bC := Module.Basis.mk hjb.1 hjb.2.ge
  have hb := B.iV_basis j w b
  let bV := Module.Basis.mk hb.1 hb.2.ge
  have hbC : ∀ a, bC a = D.what₂.jMt (D.what₂.muTw w) j (b a) := fun a => by simp [bC]
  have hbV : ∀ a, bV a = B.iV j w (b a) := fun a => by simp [bV]
  have rC : ∀ x r, bC.repr (D.what₂.jMt (D.what₂.muTw w) j x) r = D.what₂.embLL (b.repr x r) :=
    fun x r => Formalism.L2.NCov.repr_transport D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) j) b hjb.1 hjb.2 x r
  have rV : ∀ x r, bV.repr (B.iV j w x) r = B.ec j w (b.repr x r) :=
    fun x r => Formalism.L2.NCov.repr_transport (B.ec j w) (B.iV j w) b hb.1 hb.2 x r
  let A : PlE D.host → ℕ → Matrix (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) D.what₂.LL :=
    fun v k => LinearMap.toMatrix b b (B.hL j w v k)
  let G := {p : PlE D.host × ℕ // Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) p.1 p.2}
  let Mg : G → Matrix (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) (FractionRing (B.Oc j w)) :=
    fun g => (A g.1.1 g.1.2).map (B.ec j w) - κ g.1.1 g.1.2 • 1
  have hd : (⇑(bC.repr y)) ≠ 0 := by
    intro h
    apply hy
    have h' : bC.repr y = 0 := Finsupp.coe_eq_zero.1 h
    exact bC.repr.injective (h'.trans (map_zero _).symm)
  have hC : ∀ g : G, Matrix.mulVec ((Mg g).map φ) (⇑(bC.repr y)) = 0 := by
    rintro ⟨⟨v, k⟩, hvk⟩
    obtain ⟨s, ϖ, hc, hu, hadd, heig⟩ := hgen v k hvk
    set Mw := M (D.what₂.muTw w) j h1 h2 with hMw
    let tC : Module.End ℂ (D.what₂.Mt (D.what₂.muTw w) j) :=
      bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))
    have htN0 : Formalism.L2.NG.tN Mw.J s ϖ k (0 : Formalism.AUTREP.GAf D.host.E D.R.nV → Mw.wt.W) = 0 := by
      have := hadd 1 0 0
      rw [one_smul, add_zero, one_smul] at this
      simpa using this
    let Lt : D.what₂.Mt (D.what₂.muTw w) j →ₗ[ℂ] (Formalism.AUTREP.GAf D.host.E D.R.nV → Mw.wt.W) :=
      { toFun := fun y => Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real y)
        map_add' := fun y y' => by
          have := hadd 1 (Mw.real y) (Mw.real y')
          rw [one_smul, one_smul] at this
          simp only [map_add (f := _)]
          exact this
        map_smul' := fun c y => by
          have := hadd c (Mw.real y) 0
          rw [add_zero, htN0, add_zero] at this
          simp only [map_smul, RingHom.id_apply]
          exact this }
    have hagree : ∀ x, Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real x) = Mw.real (tC x) := by
      have hLt : Lt = Mw.real.comp tC := bC.ext fun a => by
        have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) a
        show Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real (bC a)) =
          Mw.real ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) (bC a))
        rw [e, hbC a]
        exact (B.hL_def j w h1 h2 v k s ϖ hvk hc hu (b a)).symm
      intro x
      exact LinearMap.congr_fun hLt x
    have hty : tC y = φ (κ v k) • y := by
      apply Mw.real_inj
      rw [← hagree, heig, map_smul]
    have hmat : LinearMap.toMatrix bC bC tC = (A v k).map D.what₂.embLL := by
      ext r c
      rw [LinearMap.toMatrix_apply, Matrix.map_apply]
      have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) c
      show bC.repr ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) (bC c)) r = _
      rw [e, rC]
      simp only [A, LinearMap.toMatrix_apply]
    have hMg : (Mg ⟨(v, k), hvk⟩).map φ = (A v k).map D.what₂.embLL - φ (κ v k) • 1 := by
      ext r c
      simp only [Mg, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp [hφ]
    rw [hMg, Matrix.sub_mulVec, ← hmat, LinearMap.toMatrix_mulVec_repr, hty, Matrix.smul_mulVec,
      Matrix.one_mulVec, map_smul, Finsupp.coe_smul, sub_self]
  obtain ⟨c, hc0, hcM⟩ := GlobalTheory.PtLocalEig.descent φ Mg (⇑(bC.repr y)) hd hC
  refine ⟨bV.equivFun.symm c, ?_, fun v k hvk => ?_⟩
  · intro h
    apply hc0
    have := congrArg bV.equivFun h
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  · apply bV.equivFun.injective
    have hmat : LinearMap.toMatrix bV bV (B.hK j w v k) = (A v k).map (B.ec j w) := by
      ext r c'
      rw [LinearMap.toMatrix_apply, Matrix.map_apply, hbV, B.hK_def, rV]
      simp only [A, LinearMap.toMatrix_apply]
    have hM := hcM ⟨(v, k), hvk⟩
    simp only [Mg, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hM
    have hr := LinearMap.toMatrix_mulVec_repr bV bV (B.hK j w v k) (bV.equivFun.symm c)
    rw [hmat] at hr
    rw [map_smul, LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply, ← hr, ← Module.Basis.equivFun_apply,
      LinearEquiv.apply_symm_apply, hM]

end GlobalTheory.PtLocalEig
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexHeckeEigenvectorDescendsToCoefficientFielStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexHeckeEigenvector_descends_to_coefficientField : ∀ (D : D7) (M : Formalism.L2.MtFam D) (B : Formalism.L2.NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), μ = D.what₂.muTw w → ∀ (φ : FractionRing (B.Oc j w) →+* ℂ), (∀ x, φ (B.ec j w x) = D.what₂.embLL x) → ∀ (κ : PlE D.host → ℕ → FractionRing (B.Oc j w)) (y : D.what₂.Mt μ j), y ≠ 0 → (∀ v k, Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ Formalism.AUTREP.IsUnif D.host.E s.v ϖ ∧ (∀ (c : ℂ) (f f' : Formalism.AUTREP.GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W), Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') = c • Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k f + Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k f') ∧ Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) = φ (κ v k) • (M μ j h1 h2).real y) → ∃ e : B.V j w, e ≠ 0 ∧ ∀ v k, Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → B.hK j w v k e = κ v k • e := by
  exact @GlobalTheory.PtLocalEig.eig_descends
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasSubstCoordZA
noncomputable section

namespace GlobalTheory.TwU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits Classical Formalism.L2.KerInert.Loc

theorem resV_subst_two {ι κ σ τ R : Type} [CommRing R] [Finite ι] [Finite σ]
    {f : κ → ι} (hf : Function.Injective f) {g : τ → σ} (hg : Function.Injective g)
    {a : σ → MvPowerSeries ι R} (ha : MvPowerSeries.HasSubst a)
    {a' : τ → MvPowerSeries κ R} (ha' : MvPowerSeries.HasSubst a')
    (h1 : ∀ k, resV f (a (g k)) = a' k) (h0 : ∀ i, (∀ k, g k ≠ i) → resV f (a i) = 0)
    (T : MvPowerSeries σ R) :
    resV f (MvPowerSeries.subst a T) = MvPowerSeries.subst a' (resV g T) := by
  rw [resV_subst hf ha, resV_eq_subst hg T, MvPowerSeries.subst_comp_subst_apply (hasSubst_resFam g) ha']
  congr 1
  funext i
  by_cases h : ∃ k, g k = i
  · obtain ⟨k, rfl⟩ := h
    rw [h1, resFam_apply hg, MvPowerSeries.subst_X ha']
  · push_neg at h
    rw [h0 i h, resFam_off g i h, ← MvPowerSeries.coe_substAlgHom ha', map_zero]

theorem resV_CX {ι κ R : Type} [CommRing R] [Finite ι] {f : κ → ι} (hf : Function.Injective f) (c : R) (k : κ) :
    resV f (MvPowerSeries.C c * MvPowerSeries.X (f k) : MvPowerSeries ι R) = MvPowerSeries.C c * MvPowerSeries.X k := by
  rw [resV_mul hf, resV_X hf]
  congr 1
  ext n
  rw [resV_coeff, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn, if_neg]
    intro h0
    apply hn
    have := congrArg Finsupp.degree h0
    rw [degree_mapDomain] at this
    exact (Finsupp.degree_eq_zero_iff n).1 (by simpa using this)

theorem resV_CX_off {ι κ R : Type} [CommRing R] [Finite ι] {f : κ → ι} (hf : Function.Injective f) (c : R) (i : ι)
    (hi : ∀ k, f k ≠ i) :
    resV f (MvPowerSeries.C c * MvPowerSeries.X i : MvPowerSeries ι R) = 0 := by
  rw [resV_mul hf, resV_X_off hf i hi, mul_zero]

theorem inj_at {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) :
    Function.Injective (fun z : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, z⟩ : X.ZA j)) :=
  fun a b h => eq_of_heq (Sigma.mk.inj_iff.1 h).2

theorem inE_inj {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) : Function.Injective (inE X j v) := by
  have hg : Function.Injective (fun e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, e⟩ : X.EA j)) :=
    fun a b h => eq_of_heq (Sigma.mk.inj_iff.1 h).2
  exact hg.sumMap hg

end GlobalTheory.TwU

namespace GlobalTheory.TwU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits Classical Formalism.L2.KerInert.Loc

theorem hasSubst_coordZA {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) :
    MvPowerSeries.HasSubst (X.coordZA (K0 p) j) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by
    rintro (⟨w, r, a, b⟩ | ⟨w, r, a, b⟩) <;> simp [Sys.coordZA])

theorem hasSubst_coordZ {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (B : OmBasis p n') :
    MvPowerSeries.HasSubst (coordZ (r0 := r0) (r1 := r1) B (K0 p) 1) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by
    rintro (⟨r, a, b⟩ | ⟨r, a, b⟩) <;> simp [coordZ])

theorem resV_ThZA {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) (T : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)) :
    resV (fun z : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, z⟩ : X.ZA j)) (X.ThZA (K0 p) j T) =
      ThZ (X.om v) (K0 p) 1 (resV (inE X j v) T) := by
  have hE := inE_inj X j v
  have hZ := inj_at X j v
  unfold Sys.ThZA ThZ
  refine resV_subst_two hZ hE (hasSubst_coordZA X j) (hasSubst_coordZ _) ?_ ?_ T
  · rintro (⟨r, a, b⟩ | ⟨r, a, b⟩)
    · show resV _ (X.coordZA (K0 p) j (Sum.inl ⟨v, (r, a, b)⟩)) = _
      simp only [Sys.coordZA, coordZ]
      rw [resV_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [one_mul, Algebra.algebraMap_self, RingHom.id_apply]
      exact resV_CX hZ _ (s, a, b)
    · show resV _ (X.coordZA (K0 p) j (Sum.inr ⟨v, (r, a, b)⟩)) = _
      simp only [Sys.coordZA, coordZ]
      rw [resV_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [one_mul, Algebra.algebraMap_self, RingHom.id_apply]
      exact resV_CX hZ _ (s, a, b)
  · rintro (⟨w, r, a, b⟩ | ⟨w, r, a, b⟩) hi
    · have hw : w ≠ v := by
        rintro rfl
        exact hi (Sum.inl (r, a, b)) rfl
      simp only [Sys.coordZA]
      rw [resV_sum]
      refine Finset.sum_eq_zero fun s _ => ?_
      exact resV_CX_off hZ _ _ (fun z h => hw (congrArg Sigma.fst h).symm)
    · have hw : w ≠ v := by
        rintro rfl
        exact hi (Sum.inr (r, a, b)) rfl
      simp only [Sys.coordZA]
      rw [resV_sum]
      refine Finset.sum_eq_zero fun s _ => ?_
      exact resV_CX_off hZ _ _ (fun z h => hw (congrArg Sigma.fst h).symm)

theorem resV_phAt {p : ℕ} [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl) :
    resV (inE X j v) (phAt X be j v) =
      ∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
        sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) := by
  have hE := inE_inj X j v
  unfold phAt
  rw [resV_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [restrict_formalSum hE be (by simp) (by simp)]
  exact congrArg₂ (sub2 p be) (resV_X hE (Sum.inl e)) (resV_X hE (Sum.inr e))

theorem restr_onePlace : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl)
    (U : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)), MvPowerSeries.constantCoeff be = 0 → IntS p (inParam p U) →
    IntS p (inParam p (resV (inE X j v) U)) ∧
      resV (fun z : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, z⟩ : X.ZA j))
        (X.ThZA (K0 p) j (expS p (-phAt X be j v) * U)) = thOne (X.om v) be (resV (inE X j v) U) := by
  intro p _ X be j v U _ hU
  have hE := inE_inj X j v
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hg⟩ := hU
    exact ⟨resV (inE X j v) g, by rw [← resV_inParam hE, hg, resV_map]⟩
  · rw [resV_ThZA, resV_mul hE, resV_expS hE, resV_neg, resV_phAt]
    rfl

end GlobalTheory.TwU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RelIndexMatrixHomLatticeRatioEqResiduePow
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RelIndexMatrixHomLatticeRatioEqResiduePow
noncomputable section

namespace GlobalTheory.HomLatIndex

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt

variable {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [IsFractionRing W Qq]

theorem exists_pow_mul_mem (p : ℕ) (hp : Irreducible (p : W)) (x : Qq) :
    ∃ m : ℕ, ∀ m' ≥ m, (p : Qq) ^ m' * x ∈ (algebraMap W Qq).range := by
  by_cases hx : x = 0
  · exact ⟨0, fun m' _ => ⟨0, by simp [hx]⟩⟩
  obtain ⟨n, u, rfl⟩ := exists_eq_unit_mul_zpow₂ (Qq := Qq) hp hx
  refine ⟨(-n).toNat, fun m' hm' => ?_⟩
  have hnn : 0 ≤ n + m' := by omega
  refine ⟨(u : W) * (p : W) ^ (n + m').toNat, ?_⟩
  rw [map_mul, map_pow, map_natCast, ← zpow_natCast, Int.toNat_of_nonneg hnn, zpow_add₀ (pQ_ne hp), zpow_natCast]
  ring

theorem exists_pow_smul_integral (p : ℕ) (hp : Irreducible (p : W)) {ι κ : Type} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ Qq) : ∃ m : ℕ, ∀ m' ≥ m, ∀ i j, (p : Qq) ^ m' * M i j ∈ (algebraMap W Qq).range := by
  choose f hf using fun ij : ι × κ => exists_pow_mul_mem p hp (M ij.1 ij.2)
  exact ⟨Finset.univ.sup f, fun m' hm' i j =>
    hf (i, j) m' (le_trans (Finset.le_sup (Finset.mem_univ (i, j))) hm')⟩


omit [IsDomain W] [IsDiscreteValuationRing W] [IsFractionRing W Qq] in
theorem mul_integral {ι κ μ : Type} [Fintype κ] {A : Matrix ι κ Qq} {B : Matrix κ μ Qq}
    (hA : ∀ i j, A i j ∈ (algebraMap W Qq).range) (hB : ∀ i j, B i j ∈ (algebraMap W Qq).range) :
    ∀ i j, (A * B) i j ∈ (algebraMap W Qq).range := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hA i l) (hB l j)


omit [IsDomain W] [IsDiscreteValuationRing W] [IsFractionRing W Qq] in
theorem mem_movLat_iff {N N' : ℕ} (k : GL (Fin N) Qq) (k' : GL (Fin N') Qq) (y : Matrix (Fin N') (Fin N) Qq) :
    y ∈ UnitaryThetaMoves.movLat W Qq k k' ↔
      ∀ i j, (((k'⁻¹ : GL (Fin N') Qq) : Matrix (Fin N') (Fin N') Qq) * y * (k : Matrix (Fin N) (Fin N) Qq)) i j ∈
        (algebraMap W Qq).range := by
  constructor
  · rintro ⟨X, hX, rfl⟩
    have e : ((k'⁻¹ : GL (Fin N') Qq) : Matrix (Fin N') (Fin N') Qq) * UnitaryThetaMoves.movHom Qq k k' X *
        (k : Matrix (Fin N) (Fin N) Qq) = X := by
      simp only [UnitaryThetaMoves.movHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_assoc]
      rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [e]
    exact hX
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [UnitaryThetaMoves.movHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_assoc]
    rw [Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem homLat_eq_movLat {k k' : ℕ} (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq)
    (ha : IsUnit a.det) (hb : IsUnit b.det) :
    (homLat W (colSpan W a) (colSpan W b)).toAddSubgroup =
      UnitaryThetaMoves.movLat W Qq (Matrix.nonsingInvUnit a ha) (Matrix.nonsingInvUnit b hb) := by
  ext x
  rw [Submodule.mem_toAddSubgroup, mem_homLat, mem_movLat_iff]
  change (∀ z ∈ colSpan W a, x *ᵥ z ∈ colSpan W b) ↔ ∀ i j, (b⁻¹ * x * a) i j ∈ (algebraMap W Qq).range
  constructor
  · intro hx i c
    obtain ⟨y, hy⟩ := (Formalism.MainNotions.Pf14.mem_colSpan b _).1 (hx _ (Submodule.subset_span ⟨c, rfl⟩))
    refine ⟨y i, ?_⟩
    have h1 : (b⁻¹ * x * a) *ᵥ Pi.single c 1 = b⁻¹ *ᵥ (x *ᵥ fun i => a i c) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
      rfl
    rw [hy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hb, Matrix.one_mulVec, Matrix.mulVec_single_one] at h1
    exact (congrFun h1 i).symm
  · intro h z hz
    obtain ⟨v, rfl⟩ := (Formalism.MainNotions.Pf14.mem_colSpan a z).1 hz
    choose X₀ hX₀ using h
    refine (Formalism.MainNotions.Pf14.mem_colSpan b _).2 ⟨(Matrix.of X₀) *ᵥ v, ?_⟩
    have hM : (Matrix.of X₀).map (algebraMap W Qq) = b⁻¹ * x * a := by
      ext i j
      exact hX₀ i j
    have e : (fun c => algebraMap W Qq (((Matrix.of X₀) *ᵥ v) c)) =
        (b⁻¹ * x * a) *ᵥ (fun c => algebraMap W Qq (v c)) := by
      funext c
      rw [RingHom.map_mulVec, hM]
      rfl
    rw [e, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hb, Matrix.one_mul]

theorem det_inv_mul_eq (p : ℕ) (hp : Irreducible (p : W)) {N : ℕ} (k₁ k₂ : GL (Fin N) Qq) :
    ∃ w : Wˣ, ((k₁⁻¹ * k₂ : GL (Fin N) Qq) : Matrix (Fin N) (Fin N) Qq).det =
      algebraMap W Qq (p : W) ^ (ordP W p (k₂ : Matrix (Fin N) (Fin N) Qq).det -
        ordP W p (k₁ : Matrix (Fin N) (Fin N) Qq).det) * algebraMap W Qq (w : W) := by
  have hne : ∀ k : GL (Fin N) Qq, (k : Matrix (Fin N) (Fin N) Qq).det ≠ 0 := fun k =>
    ((Matrix.isUnit_iff_isUnit_det _).1 k.isUnit).ne_zero
  obtain ⟨n₁, u₁, h₁⟩ := exists_eq_unit_mul_zpow₂ (Qq := Qq) hp (hne k₁)
  obtain ⟨n₂, u₂, h₂⟩ := exists_eq_unit_mul_zpow₂ (Qq := Qq) hp (hne k₂)
  have hdi : ((k₁⁻¹ : GL (Fin N) Qq) : Matrix (Fin N) (Fin N) Qq).det =
      ((k₁ : Matrix (Fin N) (Fin N) Qq).det)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  refine ⟨u₁⁻¹ * u₂, ?_⟩
  rw [Units.val_mul, Matrix.det_mul, hdi, h₁, h₂, ordP_eq hp, ordP_eq hp, map_natCast, zpow_sub₀ (pQ_ne hp),
    Units.val_mul, map_mul, map_units_inv]
  ring

theorem relIndex_movLat (p n' : ℕ) (hp : Irreducible (p : W))
    (hcard : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') {N N' : ℕ} (k₁ k₂ : GL (Fin N) Qq)
    (k₁' k₂' : GL (Fin N') Qq) (hle : UnitaryThetaMoves.movLat W Qq k₁ k₁' ≤ UnitaryThetaMoves.movLat W Qq k₂ k₂') :
    (((UnitaryThetaMoves.movLat W Qq k₁ k₁').relIndex (UnitaryThetaMoves.movLat W Qq k₂ k₂') : ℕ) : ℝ) = (p : ℝ) ^ ((n' : ℤ) *
      ((N' : ℤ) * (ordP W p (k₂ : Matrix (Fin N) (Fin N) Qq).det - ordP W p (k₁ : Matrix (Fin N) (Fin N) Qq).det) -
        (N : ℤ) * (ordP W p (k₂' : Matrix (Fin N') (Fin N') Qq).det -
          ordP W p (k₁' : Matrix (Fin N') (Fin N') Qq).det))) := by
  set f := UnitaryThetaMoves.movHom Qq k₁⁻¹ k₁'⁻¹ with hf_def
  have hf : Function.Injective f := UnitaryThetaMoves.movHom_inv_injective k₁ k₁'
  have h1 : (UnitaryThetaMoves.movLat W Qq k₁ k₁').map f = UnitaryThetaMoves.matLat W Qq N N' := by
    rw [UnitaryThetaMoves.movLat, AddSubgroup.map_map]
    conv_rhs => rw [← AddSubgroup.map_id (UnitaryThetaMoves.matLat W Qq N N')]
    congr 1
    exact AddMonoidHom.ext fun x => UnitaryThetaMoves.movHom_inv_apply k₁ k₁' x
  have h2 : (UnitaryThetaMoves.movLat W Qq k₂ k₂').map f = UnitaryThetaMoves.movLat W Qq (k₁⁻¹ * k₂) (k₁'⁻¹ * k₂') := by
    rw [UnitaryThetaMoves.movLat, UnitaryThetaMoves.movLat, AddSubgroup.map_map]
    congr 1
    ext x : 1
    simp [hf_def, UnitaryThetaMoves.movHom, Matrix.mul_assoc, _root_.mul_inv_rev]
  have hle' : UnitaryThetaMoves.matLat W Qq N N' ≤ UnitaryThetaMoves.movLat W Qq (k₁⁻¹ * k₂) (k₁'⁻¹ * k₂') := by
    rw [← h1, ← h2]
    exact AddSubgroup.map_mono hle
  have hQ : Nat.card (IsLocalRing.ResidueField W) = p ^ n' := by
    show Nat.card (W ⧸ IsLocalRing.maximalIdeal W) = _
    rw [hp.maximalIdeal_eq]
    exact hcard
  obtain ⟨w, hw⟩ := det_inv_mul_eq p hp k₁ k₂
  obtain ⟨w', hw'⟩ := det_inv_mul_eq p hp k₁' k₂'
  obtain ⟨hnn, hidx⟩ := UnitaryThetaMoves.relIndexFormula W Qq (p : W) hp (p ^ n') hQ N N' (k₁⁻¹ * k₂) (k₁'⁻¹ * k₂') _ _ w w' hw hw'
    hle'
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf, h1, h2, hidx]
  set E : ℤ := (N' : ℤ) * (ordP W p (k₂ : Matrix (Fin N) (Fin N) Qq).det -
      ordP W p (k₁ : Matrix (Fin N) (Fin N) Qq).det) - (N : ℤ) * (ordP W p (k₂' : Matrix (Fin N') (Fin N') Qq).det -
          ordP W p (k₁' : Matrix (Fin N') (Fin N') Qq).det) with hE
  rw [Nat.cast_pow, Nat.cast_pow, ← pow_mul, ← zpow_natCast, Nat.cast_mul, Int.toNat_of_nonneg hnn]

theorem movLat_le {N N' : ℕ} (k₁ k₂ : GL (Fin N) Qq) (k₁' k₂' : GL (Fin N') Qq) (P : Matrix (Fin N') (Fin N') Qq)
    (R : Matrix (Fin N) (Fin N) Qq) (hP : ∀ i j, P i j ∈ (algebraMap W Qq).range)
    (hR : ∀ i j, R i j ∈ (algebraMap W Qq).range) (h' : (k₁' : Matrix (Fin N') (Fin N') Qq) = k₂' * P)
    (h : (k₂ : Matrix (Fin N) (Fin N) Qq) = k₁ * R) : UnitaryThetaMoves.movLat W Qq k₁ k₁' ≤ UnitaryThetaMoves.movLat W Qq k₂ k₂' := by
  rintro _ ⟨X, hX, rfl⟩
  rw [mem_movLat_iff]
  have e : ((k₂'⁻¹ : GL (Fin N') Qq) : Matrix (Fin N') (Fin N') Qq) * UnitaryThetaMoves.movHom Qq k₁ k₁' X *
      (k₂ : Matrix (Fin N) (Fin N) Qq) = P * X * R := by
    simp only [UnitaryThetaMoves.movHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [h', h]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (((k₂'⁻¹ : GL (Fin N') Qq) : Matrix (Fin N') (Fin N') Qq)), Units.inv_mul, Matrix.one_mul,
      ← Matrix.mul_assoc (((k₁⁻¹ : GL (Fin N) Qq) : Matrix (Fin N) (Fin N) Qq)), Units.inv_mul, Matrix.one_mul]
  rw [e]
  exact mul_integral (mul_integral hP hX) hR

theorem relIndex_homLat_ratio : ∀ {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p n' : ℕ) (hp : Irreducible (p : W)) (hcard : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') {k k' : ℕ} (a₀ a₁ : Matrix (Fin k) (Fin k) Qq) (b₀ b₁ : Matrix (Fin k') (Fin k') Qq) (ha₀ : IsUnit a₀.det) (ha₁ : IsUnit a₁.det) (hb₀ : IsUnit b₀.det) (hb₁ : IsUnit b₁.det), (((homLat W (colSpan W a₀) (colSpan W b₀)).toAddSubgroup.relIndex (homLat W (colSpan W a₁) (colSpan W b₁)).toAddSubgroup : ℕ) : ℝ) / (((homLat W (colSpan W a₁) (colSpan W b₁)).toAddSubgroup.relIndex (homLat W (colSpan W a₀) (colSpan W b₀)).toAddSubgroup : ℕ) : ℝ) = (p : ℝ) ^ ((n' : ℤ) * ((k : ℤ) * (ordP W p b₀.det - ordP W p b₁.det) - (k' : ℤ) * (ordP W p a₀.det - ordP W p a₁.det))) := by
  intro W Qq _ _ _ _ _ _ p n' hp hcard k k' a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁
  have hpQ : (p : Qq) ≠ 0 := pQ_ne hp
  have hp0 : (p : ℝ) ≠ 0 := by
    rintro h
    apply hp.ne_zero
    rw [Nat.cast_eq_zero.1 h, Nat.cast_zero]
  obtain ⟨m₁, hm₁⟩ := exists_pow_smul_integral p hp (b₀⁻¹ * b₁)
  obtain ⟨m₂, hm₂⟩ := exists_pow_smul_integral p hp (a₁⁻¹ * a₀)
  set c : Qq := (p : Qq) ^ (m₁ + m₂) with hc_def
  have hc : c ≠ 0 := pow_ne_zero _ hpQ
  have hcW : c ∈ (algebraMap W Qq).range := ⟨(p : W) ^ (m₁ + m₂), by rw [map_pow, map_natCast]⟩
  have hP₀ : ∀ i j, (c • (b₀⁻¹ * b₁)) i j ∈ (algebraMap W Qq).range := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hm₁ _ (Nat.le_add_right _ _) i j
  have hR₀ : ∀ i j, (c • (a₁⁻¹ * a₀)) i j ∈ (algebraMap W Qq).range := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hm₂ _ (Nat.le_add_left _ _) i j
  have hone : ∀ {n : ℕ} (i j : Fin n), (c • (1 : Matrix (Fin n) (Fin n) Qq)) i j ∈ (algebraMap W Qq).range := by
    intro n i j
    rw [Matrix.smul_apply, smul_eq_mul]
    refine Subring.mul_mem _ hcW ?_
    rw [Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have hA' : IsUnit (c⁻¹ • a₁).det := by
    rw [Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 (inv_ne_zero hc))).mul ha₁
  have hB' : IsUnit (c • b₁).det := by
    rw [Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 hc)).mul hb₁
  rw [homLat_eq_movLat a₀ b₀ ha₀ hb₀, homLat_eq_movLat a₁ b₁ ha₁ hb₁]
  set T₀ := UnitaryThetaMoves.movLat W Qq (Matrix.nonsingInvUnit a₀ ha₀) (Matrix.nonsingInvUnit b₀ hb₀) with hT₀
  set T₁ := UnitaryThetaMoves.movLat W Qq (Matrix.nonsingInvUnit a₁ ha₁) (Matrix.nonsingInvUnit b₁ hb₁) with hT₁
  set S := UnitaryThetaMoves.movLat W Qq (Matrix.nonsingInvUnit _ hA') (Matrix.nonsingInvUnit _ hB') with hS
  have hS₀ : S ≤ T₀ := movLat_le _ _ _ _ _ _ hP₀ hR₀
    (show c • b₁ = b₀ * (c • (b₀⁻¹ * b₁)) by
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hb₀, Matrix.one_mul])
    (show a₀ = (c⁻¹ • a₁) * (c • (a₁⁻¹ * a₀)) by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ ha₁, Matrix.one_mul])
  have hS₁ : S ≤ T₁ := movLat_le _ _ _ _ _ _ hone hone
    (show c • b₁ = b₁ * (c • (1 : Matrix (Fin k') (Fin k') Qq)) by rw [Matrix.mul_smul, Matrix.mul_one])
    (show a₁ = (c⁻¹ • a₁) * (c • (1 : Matrix (Fin k) (Fin k) Qq)) by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, Matrix.mul_one])
  have i₀ : ((S.relIndex T₀ : ℕ) : ℝ) = (p : ℝ) ^ ((n' : ℤ) * ((k' : ℤ) * (ordP W p a₀.det -
      ordP W p (c⁻¹ • a₁).det) - (k : ℤ) * (ordP W p b₀.det - ordP W p (c • b₁).det))) :=
    relIndex_movLat p n' hp hcard _ _ _ _ hS₀
  have i₁ : ((S.relIndex T₁ : ℕ) : ℝ) = (p : ℝ) ^ ((n' : ℤ) * ((k' : ℤ) * (ordP W p a₁.det -
      ordP W p (c⁻¹ • a₁).det) - (k : ℤ) * (ordP W p b₁.det - ordP W p (c • b₁).det))) :=
    relIndex_movLat p n' hp hcard _ _ _ _ hS₁
  have m₀ := AddSubgroup.relIndex_mul_relIndex S (T₀ ⊓ T₁) T₀ (le_inf hS₀ hS₁) inf_le_left
  have m₁ := AddSubgroup.relIndex_mul_relIndex S (T₀ ⊓ T₁) T₁ (le_inf hS₀ hS₁) inf_le_right
  rw [← AddSubgroup.inf_relIndex_right T₀ T₁, ← AddSubgroup.inf_relIndex_left T₀ T₁]
  have m₀' : ((S.relIndex (T₀ ⊓ T₁) : ℕ) : ℝ) * (((T₀ ⊓ T₁).relIndex T₀ : ℕ) : ℝ) = ((S.relIndex T₀ : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, m₀]
  have m₁' : ((S.relIndex (T₀ ⊓ T₁) : ℕ) : ℝ) * (((T₀ ⊓ T₁).relIndex T₁ : ℕ) : ℝ) = ((S.relIndex T₁ : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, m₁]
  rw [i₀] at m₀'
  rw [i₁] at m₁'
  have hs0 : ((S.relIndex (T₀ ⊓ T₁) : ℕ) : ℝ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at m₀'
    exact zpow_ne_zero _ hp0 m₀'.symm
  have hx₀ : (((T₀ ⊓ T₁).relIndex T₀ : ℕ) : ℝ) = (p : ℝ) ^ ((n' : ℤ) * ((k' : ℤ) * (ordP W p a₀.det -
      ordP W p (c⁻¹ • a₁).det) - (k : ℤ) * (ordP W p b₀.det - ordP W p (c • b₁).det))) /
        ((S.relIndex (T₀ ⊓ T₁) : ℕ) : ℝ) := by
    rw [← m₀']; field_simp
  have hx₁ : (((T₀ ⊓ T₁).relIndex T₁ : ℕ) : ℝ) = (p : ℝ) ^ ((n' : ℤ) * ((k' : ℤ) * (ordP W p a₁.det -
      ordP W p (c⁻¹ • a₁).det) - (k : ℤ) * (ordP W p b₁.det - ordP W p (c • b₁).det))) /
        ((S.relIndex (T₀ ⊓ T₁) : ℕ) : ℝ) := by
    rw [← m₁']; field_simp
  rw [hx₀, hx₁, div_div_div_cancel_right₀ hs0, ← zpow_sub₀ hp0]
  congr 1
  ring

end GlobalTheory.HomLatIndex
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RelIndexMatrixHomLatticeRatioEqResiduePowStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_matrixHomLattice_ratio_eq_residue_pow : ∀ {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p n' : ℕ) (hp : Irreducible (p : W)) (hcard : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') {k k' : ℕ} (a₀ a₁ : Matrix (Fin k) (Fin k) Qq) (b₀ b₁ : Matrix (Fin k') (Fin k') Qq) (ha₀ : IsUnit a₀.det) (ha₁ : IsUnit a₁.det) (hb₀ : IsUnit b₀.det) (hb₁ : IsUnit b₁.det), (((homLat W (colSpan W a₀) (colSpan W b₀)).toAddSubgroup.relIndex (homLat W (colSpan W a₁) (colSpan W b₁)).toAddSubgroup : ℕ) : ℝ) / (((homLat W (colSpan W a₁) (colSpan W b₁)).toAddSubgroup.relIndex (homLat W (colSpan W a₀) (colSpan W b₀)).toAddSubgroup : ℕ) : ℝ) = (p : ℝ) ^ ((n' : ℤ) * ((k : ℤ) * (ordP W p b₀.det - ordP W p b₁.det) - (k' : ℤ) * (ordP W p a₀.det - ordP W p a₁.det))) := by
  first | exact @GlobalTheory.HomLatIndex.relIndex_homLat_ratio | exact GlobalTheory.HomLatIndex.relIndex_homLat_ratio | (intros; apply GlobalTheory.HomLatIndex.relIndex_homLat_ratio <;> assumption)
end
end
