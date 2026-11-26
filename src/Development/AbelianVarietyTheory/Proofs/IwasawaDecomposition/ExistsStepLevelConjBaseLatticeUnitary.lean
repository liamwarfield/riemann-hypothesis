module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedLatticeFinitelyGeneratedSpanning

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelConjBaseLatticeUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelConjBaseLatticeUnitary
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem exists_stepLevel_conj : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (b : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), b ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ v, bc (prV (E := E) v) b ∈ levelVL σ J v S.Lb) → (∀ v, (T : 𝓞 F) ∈ v.asIdeal → (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = S.Uloc v) → (∀ v, v ∉ bad → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1) → ∃ S' : StepLevel F E σ J T f bad, S'.Lb = S.Lb ∧ S'.U = S.U.map (MulAut.conj b).toMonoidHom ∧ ∀ (x : S'.U) (z : S.U), x.1 = b * z.1 * b⁻¹ → S'.chi x = S.chi z := by
  intro F E _ _ _ _ _ σ n J T f bad S b hb hlev hT hone
  classical
  let eqv := Subgroup.equivMapOfInjective S.U (MulAut.conj b).toMonoidHom
    (fun x y h => (MulAut.conj b).injective h)
  have heqv : ∀ z : S.U, ((eqv z : S.U.map (MulAut.conj b).toMonoidHom) : GL (Fin n) _) = b * z.1 * b⁻¹ := fun z => rfl
  have hbc : ∀ v (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), bc (prV (E := E) v) (b⁻¹ * x * b) =
      (bc (prV (E := E) v) b)⁻¹ * bc (prV (E := E) v) x * bc (prV (E := E) v) b := fun v x => by
    rw [map_mul, map_mul, map_inv]
  have hP : ∀ x, b⁻¹ * x * b ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ↔ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := fun x => by
    constructor
    · intro h
      have e2 : b * (b⁻¹ * x * b) * b⁻¹ = x := by group
      rw [← e2]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb h) (Subgroup.inv_mem _ hb)
    · intro h
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) h) hb
  let S' : StepLevel F E σ J T f bad :=
    { Lb := S.Lb
      Lb_fin := S.Lb_fin
      Lb_span := S.Lb_span
      Lb_int := S.Lb_int
      Lb_dual := S.Lb_dual
      Lb_index := S.Lb_index
      Uloc := fun v => (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom
      Uloc_le := by
        intro v
        rintro _ ⟨y, hy, rfl⟩
        have hbv : bc (prV (E := E) v) b ∈ UPts σ J (v.adicCompletion F) := (hlev v).1
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hbv (S.Uloc_le v hy)) (Subgroup.inv_mem _ hbv)
      Uloc_lev := by
        intro v
        rintro _ ⟨y, hy, rfl⟩
        have hbv := hlev v
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hbv (S.Uloc_lev v hy)) (Subgroup.inv_mem _ hbv)
      Uloc_hyp := by
        intro v hv hTv
        show (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = levelVL σ J v S.Lb
        ext x
        rw [mem_map_conj, hone v hv hTv, inv_one, one_mul, mul_one, S.Uloc_hyp v hv hTv]
      fM := S.fM
      fM_acg := S.fM_acg
      fM_mod := S.fM_mod
      fT := S.fT
      fT_ne := S.fT_ne
      fT_T := S.fT_T
      fM_card := S.fM_card
      fT_L := S.fT_L
      UlocAlt := by
        intro v h
        show (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = _
        rw [hT v h]
        exact S.UlocAlt v h
      U := S.U.map (MulAut.conj b).toMonoidHom
      U_eq := by
        intro x
        rw [mem_map_conj, S.U_eq, hP]
        refine and_congr_right fun _ => forall_congr' fun v => ?_
        rw [hbc v x]
        exact (mem_map_conj _ _ _).symm
      U_compact := by
        letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
        letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Algebra.TensorProduct.rightAlgebra
        haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
        haveI : Module.Finite (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
          Module.Finite.equiv (Algebra.TensorProduct.commRight F (FiniteAdeleRing (𝓞 F) F) E).toLinearEquiv
        haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
        haveI : IsTopologicalRing (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
          IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) _
        have hc : Continuous (fun x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) => b * x * b⁻¹) :=
          (continuous_const.mul continuous_id).mul continuous_const
        have := S.U_compact.image hc
        convert this using 1
        rw [Subgroup.coe_map]
        rfl
      U_open := by
        letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
        letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Algebra.TensorProduct.rightAlgebra
        haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
        haveI : Module.Finite (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
          Module.Finite.equiv (Algebra.TensorProduct.commRight F (FiniteAdeleRing (𝓞 F) F) E).toLinearEquiv
        haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
        haveI : IsTopologicalRing (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
          IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) _
        haveI : ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)) :=
          inferInstanceAs (ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)).toSubmonoid)
        let b' : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨b, hb⟩
        have hc : Continuous (fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => b'⁻¹ * x * b') :=
          (continuous_const.mul continuous_id).mul continuous_const
        have := S.U_open.preimage hc
        convert this using 1
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_map_conj]
        rfl
      chi := S.chi.comp eqv.symm.toMonoidHom
      chi_triv := by
        intro x hx
        show S.chi (eqv.symm x) = 1
        apply S.chi_triv
        intro v hv
        have e1 : ((eqv.symm x : S.U) : GL (Fin n) _) = b⁻¹ * x.1 * b := by
          have h2 := heqv (eqv.symm x)
          rw [MulEquiv.apply_symm_apply] at h2
          rw [h2]
          group
        rw [e1, hbc v, hx v hv, mul_one, inv_mul_cancel] }
  refine ⟨S', rfl, rfl, fun x z hxz => ?_⟩
  show S.chi (eqv.symm x) = S.chi z
  congr 1
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (hxz.trans (heqv z).symm)

end GlobalTheory.Mem.Col2.ChEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelConjBaseLatticeUnitaryStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stepLevel_conj_baseLatticeUnitary : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (b : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), b ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ v, bc (prV (E := E) v) b ∈ levelVL σ J v S.Lb) → (∀ v, (T : 𝓞 F) ∈ v.asIdeal → (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = S.Uloc v) → (∀ v, v ∉ bad → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1) → ∃ S' : StepLevel F E σ J T f bad, S'.Lb = S.Lb ∧ S'.U = S.U.map (MulAut.conj b).toMonoidHom ∧ ∀ (x : S'.U) (z : S.U), x.1 = b * z.1 * b⁻¹ → S'.chi x = S.chi z := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.exists_stepLevel_conj | exact GlobalTheory.Mem.Col2.ChEx.exists_stepLevel_conj | (intros; apply GlobalTheory.Mem.Col2.ChEx.exists_stepLevel_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetsInFramesEqIffReductions
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetsInFramesEqIffReductions
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChEx

section Pt

open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

theorem ptAt_cosetG (q : PtAt R sel mu cst u j) (h : j + 1 = R.m) :
    ∃ y : Sp X.E (R.N j), (∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) ∧ y ∈ q.1.2 ∧
      ∀ z ∈ q.1.2, ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N := by
  obtain ⟨y, hy, hY⟩ := q.mem_ybSet h
  refine ⟨y, fun w hw => ?_, ?_, fun z hz w hw => ?_⟩
  · have := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy ⟨w, Finset.mem_union_left _ hw⟩
    simpa [hw] using this
  · rw [hY, Set.mem_setOf_eq, sub_self]
    exact zero_mem _
  · rw [hY, Set.mem_setOf_eq, Formalism.L2.Col.mem_locLat] at hz
    simpa [hw] using hz ⟨w, Finset.mem_union_left _ hw⟩

theorem cosetIn_eqG (q : PtAt R sel mu cst u j) {y : Sp X.E (R.N j)} (hy0 : y ∈ q.1.2)
    (hY : ∀ z ∈ q.1.2, ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    cosetIn q P = {z | z - (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y ∈ stdAt X.E (R.N j) P.1} := by
  have hf := GlobalTheory.TopStep.liftFr_spec q.1.1.deco.2 ⟨P.1, hP⟩
  have hfr : frsF sel mu q.1.1 P = q.1.1.deco.1.liftFr ⟨P.1, hP⟩ := by
    unfold frsF
    rw [dite_eq_left hP]
  ext z
  simp only [cosetIn, Set.mem_setOf_eq, if_pos hP, pow_zero, inv_one, one_smul, hfr]
  constructor
  · rintro ⟨y', hy', hz⟩
    have h1 : (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y' - (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y ∈ stdAt X.E (R.N j) P.1 := by
      rw [← map_sub]
      exact (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hY y' hy' P.1 hP)
    have := add_mem hz h1
    rwa [sub_add_sub_cancel] at this
  · intro hz
    exact ⟨y, hy0, hz⟩

theorem bar_eqG (q : PtAt R sel mu cst u j) {y : Sp X.E (R.N j)}
    (hy : ∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) (hy0 : y ∈ q.1.2)
    (hY : ∀ z ∈ q.1.2, ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) (w : Pr.vGs) :
    bar q w = {redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y)} := by
  have hd := q.1.1.deco.2
  have hf := GlobalTheory.TopStep.liftFr_spec hd w
  have hq := hy w.1 w.2
  have key : q.1.1.deco.1.be w (((qOf w.1 : ℕ) : X.E) • y) =
      redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y) := by
    rw [← map_smul]
    have hs : (q.1.1.deco.1.liftFr w).symm (((qOf w.1 : ℕ) : X.E) • y) ∈ stdAt X.E _ w.1 :=
      (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hq)
    rw [← hf.2 _ hs, LinearEquiv.apply_symm_apply]
  ext v
  simp only [bar, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← key]
    have ht : z - y ∈ q.1.1.deco.1.at w.1 := hY z hz w.1 w.2
    have e : ((qOf w.1 : ℕ) : X.E) • z = ((qOf w.1 : ℕ) : X.E) • y + ((qOf w.1 : ℕ) : X.E) • (z - y) := by
      rw [← smul_add, add_sub_cancel]
    rw [e, hd.be_add w _ hq _ (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) ht),
      GlobalTheory.TopStep.be_smul_int hd w (GlobalTheory.TopStep.intAt_nat _) ht, GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul, add_zero]
  · rintro rfl
    exact ⟨y, hy0, key.symm⟩

theorem cosetIn_eq_iff_bar_cq : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ},
    (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) →
    ∀ (r r' : PtAt R sel mu cst u j), cosetIn r = cosetIn r' ↔ bar r = bar r' ∧ GlobalTheory.Mem.Col2.ChEx.cqOf r = GlobalTheory.Mem.Col2.ChEx.cqOf r' := by
  intro X Pr R sel S mu cst u j _ hq q q'
  by_cases h : j + 1 = R.m
  · obtain ⟨y, hy, hy0, hY⟩ := ptAt_cosetG q h
    obtain ⟨y', hy', hy0', hY'⟩ := ptAt_cosetG q' h
    have hA : ∀ (p : PtAt R sel mu cst u j) (y : Sp X.E (R.N j)),
        (∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal p.1.1.deco.1.N) → ∀ w : Pr.vGs,
        ((qOf w.1 : ℕ) : X.E) • (p.1.1.deco.1.liftFr w).symm y ∈ stdAt X.E (R.N j) w.1 := by
      intro p y hy w
      have hf := GlobalTheory.TopStep.liftFr_spec p.1.1.deco.2 w
      rw [← map_smul]
      exact (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hy w.1 w.2)
    constructor
    · intro H
      refine ⟨funext fun w => ?_, funext fun P => ?_⟩
      · have := congrFun H ⟨w.1, Finset.mem_union_left _ w.2⟩
        rw [cosetIn_eqG q hy0 hY _ w.2, cosetIn_eqG q' hy0' hY' _ w.2] at this
        rw [bar_eqG q hy hy0 hY, bar_eqG q' hy' hy0' hY', Set.singleton_eq_singleton_iff]
        exact (coset_eq_iff_redV (hq w.1 w.2) (hA q y hy w) (hA q' y' hy' w)).1 this
      · unfold cqOf
        rw [H]
    · rintro ⟨H1, H2⟩
      funext P
      by_cases hP : P.1 ∈ Pr.vGs
      · have := congrFun H1 ⟨P.1, hP⟩
        rw [bar_eqG q hy hy0 hY, bar_eqG q' hy' hy0' hY', Set.singleton_eq_singleton_iff] at this
        rw [cosetIn_eqG q hy0 hY P hP, cosetIn_eqG q' hy0' hY' P hP]
        exact (coset_eq_iff_redV (hq P.1 hP) (hA q y hy ⟨P.1, hP⟩) (hA q' y' hy' ⟨P.1, hP⟩)).2 this
      · have hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.mp P.2).resolve_left hP
        have := congrFun H2 ⟨P.1, hQ⟩
        exact this
  · have e : ∀ p : PtAt R sel mu cst u j, p.1.2 = ∅ := fun p => by
      have := p.2
      rw [ysAt_ys_of_ne sel mu cst h] at this
      exact this
    have h1 : ∀ p : PtAt R sel mu cst u j, cosetIn p = fun _ => ∅ := fun p => by
      funext P
      ext z
      simp [cosetIn, e p]
    have h2 : ∀ p : PtAt R sel mu cst u j, bar p = fun _ => ∅ := fun p => by
      funext w
      ext v
      simp [bar, e p]
    have h3 : ∀ p : PtAt R sel mu cst u j, cqOf p = fun _ => ∅ := fun p => by
      funext P
      exact congrFun (h1 p) _
    rw [h1 q, h1 q', h2 q, h2 q', h3 q, h3 q']
    simp

end Pt

end GlobalTheory.Mem.Col2.ChEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetsInFramesEqIffReductionsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCosetsInFrames_eq_iff_reductions : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ (r r' : PtAt R sel mu cst u j), cosetIn r = cosetIn r' ↔ bar r = bar r' ∧ GlobalTheory.Mem.Col2.ChEx.cqOf r = GlobalTheory.Mem.Col2.ChEx.cqOf r' := by
  exact @GlobalTheory.Mem.Col2.ChEx.cosetIn_eq_iff_bar_cq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgWeightFWeightTensorDualRepOfEmbeddings
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgWeightFWeightTensorDualRepOfEmbeddings
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AlgWtF

open Formalism.L2.DIV
open scoped Matrix

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K]

theorem awf_eval_aeval {σ₁ σ₂ : Type} (f : σ₁ → MvPolynomial σ₂ K) (d : σ₂ → K) (P : MvPolynomial σ₁ K) :
    MvPolynomial.eval d (MvPolynomial.aeval f P) = MvPolynomial.eval (fun x => MvPolynomial.eval d (f x)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p x hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]

def awfPt (γ₀ : Matrix (Fin n) (Fin n) L) : (L →+* K) × Fin n × Fin n → K := fun p => p.1 (γ₀ p.2.1 p.2.2)

def awfLin {κ : Type} [Fintype κ] (e : Module.Basis κ ℚ L) (p : (L →+* K) × Fin n × Fin n) :
    MvPolynomial (κ × Fin n × Fin n) K :=
  ∑ k : κ, MvPolynomial.C (p.1 (e k)) * MvPolynomial.X (k, p.2.1, p.2.2)

theorem awf_emb_eq {κ : Type} [Fintype κ] (e : Module.Basis κ ℚ L) (σ : L →+* K) (x : L) :
    σ x = ∑ k : κ, σ (e k) * ((e.repr x k : ℚ) : K) := by
  conv_lhs => rw [← e.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast, mul_comm]

theorem isAlgWeightF_of_embPoly {W : Type} [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K W)
    (Q : ι → ι → MvPolynomial ((L →+* K) × Fin n × Fin n) K)
    (hQ : ∀ γ : GQ L n, LinearMap.toMatrix b b (ρ γ) =
      fun i j => MvPolynomial.eval (awfPt (ratHom (L := L) (n := n) γ : Matrix (Fin n) (Fin n) L)) (Q i j)) :
    NX.IsAlgWeightF L n K ρ := by
  let e := Module.finBasis ℚ L
  refine ⟨Module.Finite.of_basis b, ι, inferInstance, inferInstance, b, _, inferInstance, e,
    fun i j => MvPolynomial.aeval (awfLin e) (Q i j), ?_⟩
  intro γ γ₀ hm
  obtain rfl := ratHom_eq_of_match γ γ₀ hm
  rw [hQ γ]
  ext i j
  rw [awf_eval_aeval]
  refine congrArg (fun f => MvPolynomial.eval f (Q i j)) (funext fun p => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [awfLin, awfPt, map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  exact awf_emb_eq e p.1 _

end Gen

section Poly

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K]

def awfUniv : Pol K ι n →ₐ[K] MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) K) :=
  MvPolynomial.aeval fun v => ∑ b : Fin n, MvPolynomial.C (MvPolynomial.X (v.1, b, v.2.1)) * MvPolynomial.X (v.1, b, v.2.2)

theorem awfUniv_map (M : ι → Matrix (Fin n) (Fin n) K) (F : Pol K ι n) :
    MvPolynomial.map (MvPolynomial.eval fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2) (awfUniv F) =
      Formalism.GradedWeylDivisibility.blockAct K (fun τ => (M τ)ᵀ) F := by
  have h : (MvPolynomial.map (MvPolynomial.eval fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2)).comp
      (awfUniv (K := K) (ι := ι) (n := n)).toRingHom = (Formalism.GradedWeylDivisibility.blockAct K (n := n) fun τ => (M τ)ᵀ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [awfUniv, Formalism.GradedWeylDivisibility.blockAct]
    · intro v
      simp [awfUniv, Formalism.GradedWeylDivisibility.blockAct, Matrix.transpose_apply]
  exact congrArg (fun f : Pol K ι n →+* Pol K ι n => f F) h

def awfCf (ℓ : Pol K ι n →ₗ[K] K)
    (Q : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) K)) : MvPolynomial (ι × Fin n × Fin n) K :=
  ∑ m ∈ Q.support, AddMonoidAlgebra.coeff Q m * MvPolynomial.C (ℓ (MvPolynomial.monomial m 1))

theorem awfCf_eval (ℓ : Pol K ι n →ₗ[K] K) (y : ι × Fin n × Fin n → K)
    (Q : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) K)) :
    MvPolynomial.eval y (awfCf ℓ Q) = ℓ (MvPolynomial.map (MvPolynomial.eval y) Q) := by
  conv_rhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, awfCf, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    show MvPolynomial.monomial m (MvPolynomial.eval y (AddMonoidAlgebra.coeff Q m)) =
        MvPolynomial.eval y (AddMonoidAlgebra.coeff Q m) • (MvPolynomial.monomial m 1 : Pol K ι n) by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

def awfCoord (lam : ι → DomWeight n) (i : VVIdx lam) : Pol K ι n →ₗ[K] K :=
  (LinearMap.exists_extend ((bVV K lam).coord i)).choose

theorem awfCoord_spec (lam : ι → DomWeight n) (i : VVIdx lam) (F : VV K lam) :
    awfCoord lam i (F : Pol K ι n) = (bVV K lam).repr F i := by
  have h := (LinearMap.exists_extend ((bVV K lam).coord i)).choose_spec
  have := LinearMap.congr_fun h F
  simpa [awfCoord, Module.Basis.coord_apply] using this

def awfCoef (lam : ι → DomWeight n) (i j : VVIdx lam) : MvPolynomial (ι × Fin n × Fin n) K :=
  awfCf (awfCoord lam i) (awfUniv (bVVfun K lam j))

theorem awfCoef_eval (lam : ι → DomWeight n) (M : ι → Matrix (Fin n) (Fin n) K) (i j : VVIdx lam) :
    MvPolynomial.eval (fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2) (awfCoef lam i j) =
      awfCoord lam i (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (M τ)ᵀ) (bVVfun K lam j)) := by
  rw [awfCoef, awfCf_eval, awfUniv_map]

end Poly

section Alg

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type} [Field K]

def awfDetP (σ : L →+* K) : MvPolynomial ((L →+* K) × Fin n × Fin n) K :=
  (Matrix.of fun a b => (MvPolynomial.X (σ, a, b) : MvPolynomial ((L →+* K) × Fin n × Fin n) K)).det

theorem awfDetP_eval (σ : L →+* K) (γ₀ : Matrix (Fin n) (Fin n) L) :
    MvPolynomial.eval (awfPt γ₀) (awfDetP σ) = σ γ₀.det := by
  rw [awfDetP, RingHom.map_det, RingHom.map_det]
  congr 1
  ext a b
  simp [awfPt]

theorem awf_det_conj (σ : L →+* K) (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) :
    (σ.comp (IsCMField.complexConj L : L →+* L)) (γ₀ : Matrix (Fin n) (Fin n) L).det =
      (σ (γ₀ : Matrix (Fin n) (Fin n) L).det)⁻¹ := by
  have h1 : ((γ₀ : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) γ₀).det = 1 := by
    rw [show (γ₀ : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) γ₀ = 1 from hγ,
      Matrix.det_one]
  have h2 : ((γ₀ : Matrix (Fin n) (Fin n) L).map (IsCMField.complexConj L : L →+* L)).det =
      (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L).det := by
    rw [RingHom.map_det]
    rfl
  rw [Matrix.det_mul, conjT, Matrix.det_transpose, h2] at h1
  apply eq_inv_of_mul_eq_one_right
  rw [RingHom.comp_apply, ← map_mul, h1, map_one]

theorem awf_inv_entry (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) (k l : Fin n) :
    ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) k l =
      (IsCMField.complexConj L : L →+* L) ((γ₀ : Matrix (Fin n) (Fin n) L) l k) := by
  have h1 : ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L) :=
    Units.inv_eq_of_mul_eq_one_right hγ
  rw [h1]
  rfl

def awfTwP (emb : ι → L →+* K) (lam : ι → DomWeight n) : MvPolynomial ((L →+* K) × Fin n × Fin n) K :=
  ∏ τ, if 0 ≤ (lam τ).detShift then awfDetP (emb τ) ^ (lam τ).detShift.toNat
    else awfDetP ((emb τ).comp (IsCMField.complexConj L : L →+* L)) ^ (-(lam τ).detShift).toNat

theorem awfTwP_eval (emb : ι → L →+* K) (lam : ι → DomWeight n) (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) :
    MvPolynomial.eval (awfPt (γ₀ : Matrix (Fin n) (Fin n) L)) (awfTwP emb lam) = detTwK lam (embGLF emb γ₀) := by
  simp only [awfTwP, detTwK, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hd : ((Matrix.GeneralLinearGroup.det (embGLF emb γ₀ τ) : Kˣ) : K) = emb τ (γ₀ : Matrix (Fin n) (Fin n) L).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  rw [detPow, Units.val_zpow_eq_zpow_val, hd]
  split_ifs with h
  · rw [map_pow, awfDetP_eval, ← zpow_natCast, Int.toNat_of_nonneg h]
  · rw [map_pow, awfDetP_eval, awf_det_conj _ _ hγ, ← zpow_natCast, Int.toNat_of_nonneg (by omega), inv_zpow', neg_neg]

def awfTenP (emb : ι → L →+* K) (lam : ι → DomWeight n) (i j : VVIdx lam) :
    MvPolynomial ((L →+* K) × Fin n × Fin n) K :=
  awfTwP emb lam * MvPolynomial.aeval
    (fun y : ι × Fin n × Fin n => (MvPolynomial.X (emb y.1, y.2.1, y.2.2) : MvPolynomial ((L →+* K) × Fin n × Fin n) K))
    (awfCoef (K := K) lam i j)

theorem awfTenP_eval (emb : ι → L →+* K) (lam : ι → DomWeight n) (i j : VVIdx lam) (y : (L →+* K) × Fin n × Fin n → K) :
    MvPolynomial.eval y (awfTenP emb lam i j) = MvPolynomial.eval y (awfTwP emb lam) *
      awfCoord lam i (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (Matrix.of fun a b => y (emb τ, a, b))ᵀ) (bVVfun K lam j)) := by
  rw [awfTenP, MvPolynomial.eval_mul, awf_eval_aeval, ← awfCoef_eval]
  simp

theorem tenRepF_toMatrix (emb : ι → L →+* K) (lam : ι → DomWeight n) (γ : GQ L n) :
    LinearMap.toMatrix (bVV K lam) (bVV K lam) (tenRepF emb lam γ) =
      fun i j => MvPolynomial.eval (awfPt (ratHom (L := L) (n := n) γ : Matrix (Fin n) (Fin n) L))
        (awfTenP emb lam i j) := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply, ← awfCoord_spec, awfTenP_eval, awfTwP_eval _ _ _ (ratHom_mem γ)]
  simp only [tenRepF, MonoidHom.comp_apply, rhoK, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_restrict_apply, bVV_coe,
    actP, trAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_eq_mul]
  congr 2

end Alg

section Dual

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type} [Field K]


open Classical in
theorem wtRepF_toMatrix (emb : ι → L →+* K) (lam : ι → DomWeight n) (γ : GQ L n) :
    LinearMap.toMatrix (bVV K lam).dualBasis (bVV K lam).dualBasis (wtRepF emb lam γ) =
      fun i j => MvPolynomial.eval (awfPt (ratHom (L := L) (n := n) γ : Matrix (Fin n) (Fin n) L))
        (MvPolynomial.rename (fun p : (L →+* K) × Fin n × Fin n =>
          (p.1.comp (IsCMField.complexConj L : L →+* L), p.2.2, p.2.1)) (awfTenP emb lam j i)) := by
  have e : LinearMap.toMatrix (bVV K lam).dualBasis (bVV K lam).dualBasis (wtRepF emb lam γ) =
      (LinearMap.toMatrix (bVV K lam) (bVV K lam) (tenRepF emb lam γ⁻¹))ᵀ := by
    rw [wtRepF, Representation.dual_apply, LinearMap.toMatrix_transpose]
  rw [e, tenRepF_toMatrix]
  ext i j
  show MvPolynomial.eval (awfPt (ratHom (L := L) (n := n) γ⁻¹ : Matrix (Fin n) (Fin n) L))
    (awfTenP emb lam j i) = _
  rw [MvPolynomial.eval_rename]
  refine congrArg (fun f => MvPolynomial.eval f (awfTenP emb lam j i)) (funext fun p => ?_)
  simp only [Function.comp_apply, awfPt, RingHom.comp_apply, map_inv]
  rw [awf_inv_entry _ (ratHom_mem γ)]

end Dual

theorem wtRepF_alg : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), NX.IsAlgWeightF L n K (GlobalTheory.AlgWtF.wtRepF emb lam) := by
  intro L _ _ _ n ι _ K _ emb lam
  classical
  exact isAlgWeightF_of_embPoly _ (bVV K lam).dualBasis _ (wtRepF_toMatrix emb lam)

end GlobalTheory.AlgWtF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgWeightFWeightTensorDualRepOfEmbeddingsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgWeightF_weightTensorDualRepOfEmbeddings : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), NX.IsAlgWeightF L n K (GlobalTheory.AlgWtF.wtRepF emb lam) := by
  first | exact @GlobalTheory.AlgWtF.wtRepF_alg | exact GlobalTheory.AlgWtF.wtRepF_alg | (intros; apply GlobalTheory.AlgWtF.wtRepF_alg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeneratorPlacesOutsideLevelOfStable
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeneratorPlacesOutsideLevelOfStable
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.GenHypOut

theorem not_mem_bad (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (hQ : QOver C)
    (w : D.what₂.places.Pl) (j : Fin D.R.m) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (hv : GenAt D (D.what₂.places.resChar w) (C.Q w) v k) (hc : IsConjPl D.host v s.w) :
    s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw w) j) := by
  have hov : NG.OverPl v s.v := GlobalTheory.LocLevel.overPl_of_isConjPl hc
  obtain ⟨_, hl, hS, hvQ, _, _⟩ := hv
  have hp : v ∉ placesOver D.host.E
      (if D.what₂.places.resChar w = D.host.pde then D.host.pde' else D.host.pde) :=
    fun h => hS ⟨Or.inr (Or.inr h), hl⟩
  rintro (⟨w', hov', kk, hk⟩ | hq)
  · apply hS
    refine ⟨?_, hl⟩
    have hvk := GlobalTheory.LocLevel.mem_placesOver_of_overPl' hov hov' hk
    fin_cases kk
    · exact Or.inl hvk
    · exact Or.inr (Or.inl hvk)
  · by_cases htw : D.what₂.muAt w ≠ D.what₂.mu0
    · obtain ⟨w', hov', hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp w htw j hq
      rcases hw' with hQ' | hp'
      · exact hvQ (hQ w w' v hQ' ⟨s.v, hov', hov⟩)
      · exact hp (GlobalTheory.LocLevel.mem_placesOver_of_overPl' hov hov' hp')
    · rw [not_not] at htw
      obtain ⟨hg, w', hov', hu⟩ := hq
      apply hu
      unfold TupTied.tup
      rw [tp.xi_tw, tp.psi_un w htw]
      refine HChar.UnrAt.mul ((cf.isMu0 j).unr w' fun kk hk => hg ⟨w', hov', kk, hk⟩)
        (HChar.UnrAt.mul ?_ (((isPsi_one (D.what₂.places.resChar w)).ram w').2 (Finset.notMem_empty _)))
      have hnp : w' ∉ placesOver D.host.E
          (if D.what₂.places.resChar w = D.host.pde then D.host.pde' else D.host.pde) :=
        fun h => hp (GlobalTheory.LocLevel.mem_placesOver_of_overPl' hov hov' h)
      unfold CharFrame.delAt
      split_ifs with h
      · exact cf.isDel'.unr w' fun h' => hnp (by rw [if_pos h]; exact h')
      · exact cf.isDel.unr w' fun h' => hnp (by rw [if_neg h]; exact h')

theorem genHyp : ∀ (D : D7) (cf : CharFrame D) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C),
    MtInput D M tp.tup C.Q → QOver C → GenHyp M C.Q := by
  intro D cf M C tp hM hQ w j h1 h2
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  refine ⟨gPl D ∪ qPl D (tp.tup (D.what₂.muTw w) ⟨j', by omega⟩), hM.hyp w ⟨j', by omega⟩, ?_⟩
  intro v k s hv hc
  exact not_mem_bad D cf C tp hQ w _ v k s hv hc

end GlobalTheory.GenHypOut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeneratorPlacesOutsideLevelOfStableStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeGeneratorPlacesOutsideLevel_of_stable : ∀ (D : D7) (cf : CharFrame D) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), MtInput D M tp.tup C.Q → QOver C → GenHyp M C.Q := by
  first | exact @GlobalTheory.GenHypOut.genHyp | exact GlobalTheory.GenHypOut.genHyp | (intros; apply GlobalTheory.GenHypOut.genHyp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartClassesBijectiveOrbitsFramedLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartClassesBijectiveOrbitsFramedLattices
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

section OrbF

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}

theorem image_eq_iff_frStab {P : HeightOneSpectrum (𝓞 X.E)} (C : Set (Sp X.E n)) (g : ↥(GLint X.E n P)) :
    (fun v => g.1 v) '' C = C ↔ g ∈ frStab P C := by
  rw [mem_frStab]
  constructor
  · intro e v
    constructor
    · intro hv
      rw [← e] at hv
      obtain ⟨u, hu, huv⟩ := hv
      rwa [← g.1.injective huv]
    · intro hv
      rw [← e]
      exact ⟨v, hv, rfl⟩
  · intro h
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (h u).2 hu
    · intro hv
      refine ⟨g.1.symm v, (h _).1 ?_, LinearEquiv.apply_symm_apply g.1 v⟩
      rw [LinearEquiv.apply_symm_apply]
      exact hv

def frLift (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal))
    (D : ∀ P : Q, Set (Sp X.E n)) (g : UF X.E n × chG Λ C × (cutQ Θ D).grp) : FrmG Λ Θ :=
  (g.1, ⟨g.2.1.1, chG_le _ _ g.2.1.2⟩, ⟨g.2.2.1, cutQ_grp_le _ _ g.2.2.2⟩)

theorem ya_frLift (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal))
    (D : ∀ P : Q, Set (Sp X.E n)) (g : UF X.E n × chG Λ C × (cutQ Θ D).grp) (q : PtY ST SG Q y) :
    (ya Λ Θ (frLift Λ Θ C D g) q).1.1 = g • q.1.1 := rfl

end OrbF

end GlobalTheory.Mem.Col2.ChEx

namespace GlobalTheory.Mem.Col2.ChEx

theorem clsF_bij : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (p₀ : DecoF X.E n ST SG Q → Prop) (pref : β → PtY ST SG Q y → Prop) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)) [NeZero n], GlobalTheory.Mem.Col2.ChEx.InvActs cq → GlobalTheory.Mem.Col2.ChEx.PtDet cq → (∀ (r : PtY ST SG Q y) (p : DecoF X.E n ST SG Q), ∃ r' : PtY ST SG Q y, r'.1.1 = p ∧ bar r' = bar r ∧ cq r' = cq r) → (∀ b r r', bar r = bar r' → cq r = cq r' → bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r')) ∧ cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r'))) → ∀ (c₀ : (stR Λ Θ p₀ pref).Cl) (p : (stR Λ Θ p₀ pref).Cl → Prop), (∀ c, p c ↔ c.1 = c₀.1 ∧ bar (rp Λ Θ p₀ pref c) = bar (rp Λ Θ p₀ pref c₀) ∧ cq (rp Λ Θ p₀ pref c) = cq (rp Λ Θ p₀ pref c₀)) → Function.Bijective fun c : {c // p c} => (Quotient.mk'' (rp Λ Θ p₀ pref c.1).1.1 : DecoFCl (K := X.K) n ST SG Q (chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀))) (GlobalTheory.Mem.Col2.ChEx.cutQ (Θ c₀.1) (cq (rp Λ Θ p₀ pref c₀)))) := by
  intro X n ST SG Q y β _ _ Λ Θ p₀ pref cq _ hact hdet hsur hnorm c₀ p hp
  constructor
  · rintro ⟨c, h⟩ ⟨c', h'⟩ e
    obtain ⟨h1, h2, h3⟩ := (hp c).1 h
    obtain ⟨h1', h2', h3'⟩ := (hp c').1 h'
    apply Subtype.ext
    show c = c'
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.1 (Quotient.exact' e)
    have hb : bar (ya (Λ c₀.1) (Θ c₀.1) (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c')) = bar (rp Λ Θ p₀ pref c') :=
      (bar_ya_eq_iff _ _ _ _).2 fun w => by rw [h2']; exact (mem_chG.1 g.2.1.2).2 w
    have hq : cq (ya (Λ c₀.1) (Θ c₀.1) (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c')) = cq (rp Λ Θ p₀ pref c') := by
      funext P
      rw [hact, h3']
      exact (image_eq_iff_frStab _ _).2 ((mem_cutQ_grp.1 g.2.2.2).2 P)
    have e2 : ya (Λ c₀.1) (Θ c₀.1) (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c') = rp Λ Θ p₀ pref c :=
      hdet _ _ (by rw [ya_frLift]; exact hg) (hb.trans (h2'.trans h2.symm)) (hq.trans (h3'.trans h3.symm))
    have e3 := cl_ya Λ Θ p₀ pref c₀.1 (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c')
    rw [e2] at e3
    have e4 := cl_rp Λ Θ p₀ pref c
    have e5 := cl_rp Λ Θ p₀ pref c'
    have t : ∀ b b' : β, b = b' → ∀ q : PtY ST SG Q y, (stR Λ Θ p₀ pref).cl b q = (stR Λ Θ p₀ pref).cl b' q := by
      rintro b _ rfl q
      rfl
    exact e4.symm.trans ((t _ _ h1 _).trans (e3.trans ((t _ _ h1' _).symm.trans e5)))
  · intro z
    induction z using Quotient.inductionOn' with
    | h d =>
      obtain ⟨r', h1, h2, h3⟩ := hsur (rp Λ Θ p₀ pref c₀) d
      obtain ⟨hb, hq⟩ := hnorm c₀.1 _ _ h2.symm h3.symm
      rw [cl_rp] at hb hq
      refine ⟨⟨(stR Λ Θ p₀ pref).cl c₀.1 r', (hp _).2 ⟨rfl, hb.symm, hq.symm⟩⟩, ?_⟩
      obtain ⟨g, hg⟩ := exists_ya Λ Θ p₀ pref c₀.1 r'
      rw [hg] at hb hq
      have hb' : bar (ya (Λ c₀.1) (Θ c₀.1) g r') = bar r' := hb.symm.trans h2.symm
      have hq' : cq (ya (Λ c₀.1) (Θ c₀.1) g r') = cq r' := hq.symm.trans h3.symm
      rw [bar_ya_eq_iff, h2] at hb'
      have hC : ∀ P : Q, g.2.2.1 P ∈ frStab P.1 (cq (rp Λ Θ p₀ pref c₀) P) := fun P => by
        rw [← h3, ← image_eq_iff_frStab]
        have := congrFun hq' P
        rwa [hact] at this
      let g' : UF X.E n × chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀)) × (cutQ (Θ c₀.1) (cq (rp Λ Θ p₀ pref c₀))).grp :=
        (g.1, ⟨g.2.1.1, mem_chG.2 ⟨g.2.1.2, hb'⟩⟩, ⟨g.2.2.1, mem_cutQ_grp.2 ⟨g.2.2.2, hC⟩⟩)
      refine Quotient.sound' (MulAction.orbitRel_apply.2 ⟨g', ?_⟩)
      show g' • d = (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl c₀.1 r')).1.1
      rw [hg, ← h1]
      rfl

end GlobalTheory.Mem.Col2.ChEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartClassesBijectiveOrbitsFramedLatticesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartClasses_bijective_orbits_framedLattices : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (p₀ : DecoF X.E n ST SG Q → Prop) (pref : β → PtY ST SG Q y → Prop) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)) [NeZero n], GlobalTheory.Mem.Col2.ChEx.InvActs cq → GlobalTheory.Mem.Col2.ChEx.PtDet cq → (∀ (r : PtY ST SG Q y) (p : DecoF X.E n ST SG Q), ∃ r' : PtY ST SG Q y, r'.1.1 = p ∧ bar r' = bar r ∧ cq r' = cq r) → (∀ b r r', bar r = bar r' → cq r = cq r' → bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r')) ∧ cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r'))) → ∀ (c₀ : (stR Λ Θ p₀ pref).Cl) (p : (stR Λ Θ p₀ pref).Cl → Prop), (∀ c, p c ↔ c.1 = c₀.1 ∧ bar (rp Λ Θ p₀ pref c) = bar (rp Λ Θ p₀ pref c₀) ∧ cq (rp Λ Θ p₀ pref c) = cq (rp Λ Θ p₀ pref c₀)) → Function.Bijective fun c : {c // p c} => (Quotient.mk'' (rp Λ Θ p₀ pref c.1).1.1 : DecoFCl (K := X.K) n ST SG Q (chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀))) (GlobalTheory.Mem.Col2.ChEx.cutQ (Θ c₀.1) (cq (rp Λ Θ p₀ pref c₀)))) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.clsF_bij | exact GlobalTheory.Mem.Col2.ChEx.clsF_bij | (intros; apply GlobalTheory.Mem.Col2.ChEx.clsF_bij <;> assumption)
end
end
