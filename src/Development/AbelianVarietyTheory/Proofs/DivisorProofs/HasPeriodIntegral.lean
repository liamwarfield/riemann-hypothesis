module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupFormalChartOfConnectedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogarithmOfDualCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusMatrixQuasiLogarithmBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusMatrixIsUnitAdaptedBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusNilpotentModMaximalConnectedPDivGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilDualFrobenius
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryOneMapEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePeriodQuasiLogarithmPDivGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPeriodFrobeniusTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPeriodEqTangentHodgeTate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmIntegersAdaptedBasisNoLieComponents

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDimAddFinrankDualLieEqHeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDimAddFinrankDualLieEqHeight
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.PDivGroup.DimSum

theorem baseChange_bijective_of_ker {O : Type} [CommRing O] {M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (k : Type) [CommRing k] [Algebra O k] (a : O)
    (ha : algebraMap O k a = 0) (f : M →ₗ[O] N) (hf : Function.Surjective f)
    (hfa : ∀ v, f (a • v) = 0) (hk : ∀ w, f w = 0 → ∃ v, w = a • v) :
    Function.Bijective (f.baseChange k) := by
  rw [LinearMap.baseChange_eq_ltensor]
  refine ⟨?_, LinearMap.lTensor_surjective k hf⟩
  have hex : Function.Exact (a • LinearMap.id : M →ₗ[O] M) f := by
    intro w
    constructor
    · intro hw
      obtain ⟨v, rfl⟩ := hk w hw
      exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact hfa v
  have hex' := lTensor_exact k hex hf
  have hz : LinearMap.lTensor k (a • LinearMap.id : M →ₗ[O] M) = 0 := by
    refine TensorProduct.ext' fun c m => ?_
    rw [LinearMap.lTensor_tmul, LinearMap.smul_apply, LinearMap.id_apply, ← TensorProduct.smul_tmul,
      Algebra.smul_def, ha, zero_mul, TensorProduct.zero_tmul, LinearMap.zero_apply]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (hex' x).1 hx
  rw [hz, LinearMap.zero_apply]

open GlobalTheory.PDiv Module

theorem finrank_cot_baseChange_one {p : ℕ} {O : Type} [CommRing O] (H : PDivGroup p O) (k : Type)
    [Field k] [Algebra O k] (hp : algebraMap O k p = 0) :
    finrank k (Cot k (k ⊗[O] H.A 1)) = finrank k (k ⊗[O] H.omega) := by
  have h1 : Function.Bijective ((H.omegaLevel 1).baseChange k) :=
    baseChange_bijective_of_ker k (p : O) hp (H.omegaLevel 1) (H.omegaLevel_surjective 1)
      (fun v => by
        have := H.pow_smul_cot 1 (v.1 1)
        rw [pow_one] at this
        exact this)
      (fun w hw => by
        obtain ⟨v, hv⟩ := (H.omega_val_eq_zero_iff 1 w).1 hw
        exact ⟨v, by rw [hv, pow_one]⟩)
  let e1 := LinearEquiv.ofBijective _ h1
  let e2 := LinearEquiv.ofBijective _ (liftSemi_toBaseChange_cot_bijective O k (H.A 1))
  exact (e1.trans e2).finrank_eq.symm

theorem finrank_cot_congr {k X Y : Type} [Field k] [CommRing X] [CommRing Y] [Bialgebra k X]
    [Bialgebra k Y] (e : X ≃ₐc[k] Y) : finrank k (Cot k X) = finrank k (Cot k Y) := by
  have h1 : (e.symm : Y →ₐc[k] X).comp (e : X →ₐc[k] Y) = BialgHom.id k X :=
    BialgHom.ext fun x => e.symm_apply_apply x
  have h2 : (e : X →ₐc[k] Y).comp (e.symm : Y →ₐc[k] X) = BialgHom.id k Y :=
    BialgHom.ext fun x => e.apply_symm_apply x
  refine (LinearEquiv.ofLinear (cotMap (e : X →ₐc[k] Y)) (cotMap (e.symm : Y →ₐc[k] X)) ?_ ?_).finrank_eq
  · rw [← cotMap_comp, h2, cotMap_id]
  · rw [← cotMap_comp, h1, cotMap_id]

end GlobalTheory.PDivGroup.DimSum


open Module PDiv in
theorem GlobalTheory.PDivGroup.chart_dim_add_finrank_dual_lie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d),
      d + Module.finrank O G.dual.Lie = G.height := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  let k := IsLocalRing.ResidueField O
  have hpk : algebraMap O k p = 0 := by
    change IsLocalRing.residue O p = 0
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (Fact.out : ¬IsUnit (p : O))
  have hpk' : ((p : ℕ) : k) = 0 := by rw [← map_natCast (algebraMap O k), hpk]
  obtain ⟨hbij, -⟩ := GlobalTheory.T.pdDivGroupChart_forms_basis_and_differential p C v O hv G d c
  let eG : (Fin d → O) ≃ₗ[O] G.omega := LinearEquiv.ofBijective _ hbij
  haveI : Module.Free O G.omega := Module.Free.of_equiv eG
  obtain ⟨hfin, hproj⟩ := GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual
  haveI : Module.Free O G.dual.omega := Module.free_of_flat_of_isLocalRing
  have hd : finrank O G.omega = d := by rw [← eG.finrank_eq, Module.finrank_fin_fun]
  have hLie : finrank O G.dual.Lie = finrank O G.dual.omega := by
    let b := Module.Free.chooseBasis O G.dual.omega
    rw [finrank_eq_card_basis b.dualBasis, finrank_eq_card_basis b]
  obtain ⟨-, -, -, hsum⟩ := finrank_rigExt_omega p k hpk' (G.baseChange k)
  have hA : finrank k (G.baseChange k).omega = finrank O G.omega := by
    rw [(LinearEquiv.ofBijective _ ((G.baseChange k).omegaLevel_one_bijective hpk')).finrank_eq]
    exact (DimSum.finrank_cot_baseChange_one G k hpk).trans (Module.finrank_baseChange)
  have hB : finrank k (G.baseChange k).dual.omega = finrank O G.dual.omega := by
    rw [(LinearEquiv.ofBijective _ ((G.baseChange k).dual.omegaLevel_one_bijective hpk')).finrank_eq]
    refine (DimSum.finrank_cot_congr (CartierDual.baseChange O k (G.A 1))).symm.trans ?_
    exact (DimSum.finrank_cot_baseChange_one G.dual k hpk).trans (Module.finrank_baseChange)
  rw [hLie, ← hd, ← hA, ← hB]
  exact hsum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDimAddFinrankDualLieEqHeightStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartDim_add_finrank_dual_lie_eq_height : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), d + Module.finrank O G.dual.Lie = G.height := by
  first | exact @GlobalTheory.PDivGroup.chart_dim_add_finrank_dual_lie | exact GlobalTheory.PDivGroup.chart_dim_add_finrank_dual_lie | (intros; apply GlobalTheory.PDivGroup.chart_dim_add_finrank_dual_lie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAdaptedBasisQuasiLogarithmsFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAdaptedBasisQuasiLogarithmsFrame
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.LiftBasis

theorem exists_lift_isAdapted : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → ∀ (k : ℕ) (e0 : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C), IsBasis c.μ e0 → IsAdapted (RingHom.id O) c.μ e0 → ∃ e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q, (∀ l, map Θ (e l) = e0 l) ∧ IsBasis μ' e ∧ IsAdapted F.θ μ' e := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hμ' hμ Θ hΘ k e0 hB hA
  have hC : IsFrame p C (RingHom.id O) := GlobalTheory.T.isTorsionFreePDThickeningFrame_valuation_integers p C v O hv
  have hF : IsFrame p F.Q F.θ := F.frame
  have hμf : (fun i => map F.θ (μ' i)) = c.μ := funext hμ

  have hw : ∀ l, ∃ w : Fin d → F.B, (∀ i, lin (e0 l) i = algebraMap O C (F.θ (w i))) ∧
      ∀ j, l = Sum.inl j → w = Pi.single j 1 := by
    intro l
    cases l with
    | inl j =>
      refine ⟨Pi.single j 1, fun i => ?_, fun j' h => by cases h; rfl⟩
      rw [(hA j).2]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    | inr j =>
      refine ⟨fun i => Classical.choose (hF.surj (Classical.choose ((hB.1 (Sum.inr j)).2.1 i))),
        fun i => ?_, fun j' h => by cases h⟩
      rw [Classical.choose_spec (hF.surj _)]
      exact (Classical.choose_spec ((hB.1 (Sum.inr j)).2.1 i)).2
  choose w hw1 hw2 using hw
  have hlift : ∀ l, ∃ f : MvPowerSeries (Fin d) F.Q, QL μ' ⊤ f ∧ map Θ f = e0 l ∧
      ∀ i, lin f i = algebraMap F.B F.Q (w l i) := by
    intro l
    refine GlobalTheory.T.lift_quasiLogarithm_along_pdThickening p F.B O F.Q F.θ hF d μ' hμ' C hC Θ hΘ (e0 l) (w l) ?_ (hw1 l)
    rw [hμf]; exact hB.1 l
  choose e he1 he2 he3 using hlift
  refine ⟨e, he2, ?_, ?_⟩
  · refine GlobalTheory.T.quasiLogarithm_basis_lift_pdThickening p F.B O F.Q F.θ hF d μ' hμ' C hC Θ hΘ (Fin d ⊕ Fin k) e he1 ?_
      (GlobalTheory.T.ainfSquareZeroFrame_reflTransGen_cyclic_chain p C v O hv ε hε F)
    rw [hμf]
    have : (fun i => map Θ (e i)) = e0 := funext he2
    rw [this]; exact hB
  · intro i
    refine ⟨fun α => ?_, ?_⟩
    · obtain ⟨b, -, eb⟩ := (he1 (Sum.inl i)).2.2 α
      refine ⟨b, RingHom.mem_ker.2 ?_, eb⟩
      obtain ⟨b', hb', eb'⟩ := (hA i).1 α
      have hb0 : b' = 0 := RingHom.mem_ker.1 hb'
      have hup : up C c.μ = fun j => map Θ (up F.Q μ' j) :=
        funext (WindowMat.up_map F.θ Θ hΘ hμ)
      have key : algebraMap O C (F.θ b) = 0 := by
        rw [← hΘ, ← eb, ← coeff_map, Window.map_formalGroupLawCoboundaryOne_eq Θ _ (Window.constantCoeff_up hμ'.const),
          ← hup, he2, eb', hb0, map_zero]
      exact hC.inj (by rw [key, map_zero])
    · funext j
      rw [he3, hw2 _ i rfl]
      by_cases hij : j = i
      · subst hij; simp
      · simp [Pi.single_apply, hij]

end GlobalTheory.QLog.LiftBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAdaptedBasisQuasiLogarithmsFrameStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_adapted_basis_quasi_logarithms_frame : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → ∀ (k : ℕ) (e0 : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C), IsBasis c.μ e0 → IsAdapted (RingHom.id O) c.μ e0 → ∃ e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q, (∀ l, map Θ (e l) = e0 l) ∧ IsBasis μ' e ∧ IsAdapted F.θ μ' e := by
  first | exact @GlobalTheory.QLog.LiftBasis.exists_lift_isAdapted | exact GlobalTheory.QLog.LiftBasis.exists_lift_isAdapted | (intros; apply GlobalTheory.QLog.LiftBasis.exists_lift_isAdapted <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGroupLawLiftOfSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGroupLawLiftOfSurjective
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftLaw

def cmap {σ R S : Type} [CommRing R] [CommRing S] (g : R → S) (f : MvPowerSeries σ R) : MvPowerSeries σ S :=
  fun α => g (coeff α f)

theorem coeff_cmap {σ R S : Type} [CommRing R] [CommRing S] (g : R → S) (f : MvPowerSeries σ R) (α : σ →₀ ℕ) :
    coeff α (cmap g f) = g (coeff α f) := rfl

theorem swap_cmap {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (g : R → S)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) : swap (cmap g c) = cmap g (swap c) := by
  ext α
  obtain ⟨⟨a, e⟩, rfl⟩ := (Finsupp.sumFinsuppEquivProdFinsupp : (Fin d ⊕ Fin d →₀ ℕ) ≃ (Fin d →₀ ℕ) × (Fin d →₀ ℕ)).symm.surjective α
  have h : (Finsupp.sumFinsuppEquivProdFinsupp : (Fin d ⊕ Fin d →₀ ℕ) ≃ (Fin d →₀ ℕ) × (Fin d →₀ ℕ)).symm (a, e) = Finsupp.sumElim a e := rfl
  rw [h, coeff_cmap, SwapCoeff.coeff_swap, SwapCoeff.coeff_swap, coeff_cmap]

theorem coeff_subst_elim_zero {R : Type} [CommRing R] {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (β : Fin d →₀ ℕ) :
    coeff β (subst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun (_ : Fin d) => 0) c) =
      coeff (Finsupp.embDomain (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d) β) c := by
  classical
  have ha : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun (_ : Fin d) => 0) :=
    hasSubst_of_constantCoeff_zero fun s => by rcases s with i | i <;> simp
  have hb : HasSubst (X ∘ (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d) :
      Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) :=
    hasSubst_of_constantCoeff_zero fun s => by simp
  have hr : rename (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d)
      (subst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun (_ : Fin d) => 0) c) =
      subst (fun s : Fin d ⊕ Fin d => if s.isLeft then (X s : MvPowerSeries (Fin d ⊕ Fin d) R) else 0) c := by
    rw [rename_eq_subst, subst_comp_subst_apply ha hb]
    congr 1
    funext s
    rcases s with i | i
    · simp [subst_X hb]
    · simp only [Sum.elim_inr, Sum.isLeft_inr]
      rw [← coe_substAlgHom hb, map_zero]
      rfl
  rw [← coeff_embDomain_rename (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d), hr,
    OnePair.coeff_subst_kill]
  rw [if_pos]
  rintro (i | i) hi
  · simp at hi
  · simp [Finsupp.embDomain_apply]

theorem exists_isLift : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O), Function.Surjective θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∃ μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B, IsLift θ μ' ∧ ∀ i, map θ (μ' i) = μ i := by
  intro B O _ _ θ hθ d μ hμ
  classical
  by_cases h1 : (1 : O) = 0
  ·
    haveI : Subsingleton O := subsingleton_of_zero_eq_one h1.symm
    have hm : ∀ i, map θ (addLaw B d i) = μ i := fun i => by
      ext α
      exact Subsingleton.elim _ _
    have ha : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) B)) fun (_ : Fin d) => 0) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with i | i <;> simp
    have hs : HasSubst (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) B))
        fun i => X (Sum.inl i)) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with i | i <;> simp
    refine ⟨addLaw B d, ⟨fun i => by simp [addLaw], ?_, fun i => ?_, ?_⟩, hm⟩
    · funext i
      simp only [op, at2, addLaw]
      rw [subst_add ha, subst_X ha, subst_X ha]
      simp
    · simp only [swap, at2, addLaw]
      rw [subst_add hs, subst_X hs, subst_X hs]
      simp [add_comm]
    · have : (fun i => map θ (addLaw B d i)) = μ := funext hm
      rw [this]
      exact hμ
  ·
    let s : O → B := fun x => if x = 0 then 0 else if x = 1 then 1 else (hθ x).choose
    have hs : ∀ x, θ (s x) = x := fun x => by
      simp only [s]
      split_ifs with h h'
      · rw [map_zero, h]
      · rw [map_one, h']
      · exact (hθ x).choose_spec
    have hs0 : s 0 = 0 := by simp [s]
    have hs1 : s 1 = 1 := by simp [s, h1]
    refine ⟨fun i => cmap s (μ i), ⟨fun i => ?_, ?_, fun i => ?_, ?_⟩, fun i => ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_cmap, coeff_zero_eq_constantCoeff_apply,
        hμ.const i, hs0]
    · funext i
      ext β
      have hu := congrArg (coeff β) (congrFun hμ.unit i)
      simp only [op, at2] at hu ⊢
      rw [coeff_subst_elim_zero] at hu ⊢
      rw [coeff_cmap, hu, coeff_X, coeff_X]
      split_ifs
      · exact hs1
      · exact hs0
    · rw [swap_cmap, hμ.comm i]
    · have : (fun i => map θ (cmap s (μ i))) = μ := funext fun i => by
        ext α
        rw [coeff_map, coeff_cmap, hs]
      rw [this]
      exact hμ
    · ext α
      rw [coeff_map, coeff_cmap, hs]

end GlobalTheory.LiftLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGroupLawLiftOfSurjectiveStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalGroupLawLift_of_surjective : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O), Function.Surjective θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∃ μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B, IsLift θ μ' ∧ ∀ i, map θ (μ' i) = μ i := by
  first | exact @GlobalTheory.LiftLaw.exists_isLift | exact GlobalTheory.LiftLaw.exists_isLift | (intros; apply GlobalTheory.LiftLaw.exists_isLift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartHasPeriodLinearIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartHasPeriodLinearIntegral
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem lift_topNil {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B] [CommRing Q]
    [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ} (c : Chart G d)
    (t : G.Tate) (n : ℕ) (z : Fin d → B) (hz : ∀ i, θ (z i) = t.pt n (c.x n i)) :
    ∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N := by
  intro i
  obtain ⟨N, a, ha⟩ := c.nil n i
  obtain ⟨a', ha'⟩ := hF.surj (t.pt n a)
  have hw : θ (z i ^ N - p * a') = 0 := by
    rw [map_sub, map_pow, hz, map_mul, map_natCast, ha', ← map_pow, ha, map_mul, map_natCast, sub_self]
  obtain ⟨w, -, hw'⟩ := hF.pd _ hw
  refine ⟨N * p, ?_⟩
  have h1 : (p : B) * a' ∣ (z i ^ N) ^ p - (z i ^ N - p * a') ^ p := by
    have := sub_dvd_pow_sub_pow (z i ^ N) (z i ^ N - p * a') p
    simpa using this
  rw [pow_mul]
  have h2 : (p : B) ∣ (z i ^ N) ^ p - (z i ^ N - p * a') ^ p := dvd_trans (dvd_mul_right _ _) h1
  have h3 : (p : B) ∣ (z i ^ N - p * a') ^ p := hw' ▸ dvd_mul_right _ _
  have := dvd_add h2 h3
  simpa using this

end GlobalTheory.QLog

namespace GlobalTheory.QLog

theorem val_integral {p : ℕ} {σ B Q : Type} [Fintype σ] [DecidableEq σ] [CommRing B] [CommRing Q]
    [Algebra B Q] (z : σ → B) (s : MvPowerSeries σ B) (q : Q)
    (h : HasVal p z (map (algebraMap B Q) s) q) : ∃ b : B, q = algebraMap B Q b := by
  obtain ⟨N, hN⟩ := h 0
  obtain ⟨b, hb⟩ := hN N le_rfl
  have hE : (MvPolynomial.eval fun i => algebraMap B Q (z i))
      (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => N) (map (algebraMap B Q) s)) =
      algebraMap B Q (MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ => N) s)) := by
    rw [trunc'_map, MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_comp_left]
    rfl
  refine ⟨MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ => N) s) + b, ?_⟩
  rw [hE, pow_zero, one_mul, sub_eq_iff_eq_add'] at hb
  rw [hb, map_add (f := _)]

end GlobalTheory.QLog

namespace GlobalTheory.QLog

theorem hasPeriod_add_smul {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B]
    [CommRing Q] [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ}
    (c : Chart G d) (t : G.Tate) {f g : MvPowerSeries (Fin d) Q} {y y' : B} (b : B)
    (hf : c.HasPeriod θ t f y) (hg : c.HasPeriod θ t g y') :
    c.HasPeriod θ t (f + algebraMap B Q b • g) (y + b * y') := by
  rw [c.hasPeriod_iff hF] at hf hg ⊢
  intro n z hz
  obtain ⟨q, hq, b1, hb1⟩ := hf n z hz
  obtain ⟨r, hr, b2, hb2⟩ := hg n z hz
  have h1 := (GlobalTheory.QLog.ValLin.hasVal_add_smul_map p B O Q θ hF (Fin d) z g g r r hr).2.1 (algebraMap B Q b)
  have h2 := (GlobalTheory.QLog.ValLin.hasVal_add_smul_map p B O Q θ hF (Fin d) z _ _ q _ hq).1 h1
  refine ⟨_, h2, b1 + b * b2, ?_⟩
  have e : (p : Q) ^ n * (q + algebraMap B Q b * r) =
      (p : Q) ^ n * q + algebraMap B Q b * ((p : Q) ^ n * r) := by ring
  rw [e, hb1, hb2, ← map_mul, ← map_add (f := _)]
  congr 1
  ring

theorem hasPeriod_integral {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B]
    [CommRing Q] [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ}
    (c : Chart G d) (t : G.Tate) (s : MvPowerSeries (Fin d) B) :
    c.HasPeriod θ t (map (algebraMap B Q) s) 0 := by
  rw [c.hasPeriod_iff hF]
  intro n z hz
  have hD : DIn (⊤ : Ideal B) (map (algebraMap B Q) s) := fun α i =>
    ⟨(α i : B) * coeff α s, trivial, by rw [coeff_map, map_mul, map_natCast]⟩
  obtain ⟨q, hq, -⟩ := GlobalTheory.QLog.existsUnique_hasVal_of_dIn p B O Q θ hF (Fin d) z (lift_topNil hF c t n z hz) _ hD
  obtain ⟨e, he⟩ := val_integral z s q hq
  exact ⟨q, hq, e, by rw [he, zero_add, map_mul, map_pow, map_natCast]⟩

open MvPowerSeries in
private lemma exists_pow_dvd_of_theta_eq_of_isFrame {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] {θ : B →+* O} (hθ : _root_.GlobalTheory.QLog.IsFrame p Q θ)
    {z : B} {a : O} (hza : θ z = a) {N : ℕ} (ha : (p : O) ∣ a ^ N) :
    ∃ M, (p : B) ∣ z ^ M := by
  obtain ⟨w, hw⟩ := ha
  obtain ⟨b, hb⟩ := hθ.surj w
  obtain ⟨y, -, hy⟩ := hθ.pd (z ^ N - p * b)
    (by simp [hza, hb, hw])
  refine ⟨N * p, ?_⟩
  have h1 : (p : B) ∣ (z ^ N) ^ p - (z ^ N - p * b) ^ p :=
    (dvd_mul_right (p : B) b).trans (by simpa using sub_dvd_pow_sub_pow (z ^ N) (z ^ N - p * b) p)
  have h2 : (z ^ N) ^ p = ((z ^ N) ^ p - (z ^ N - p * b) ^ p) + p * y := by rw [← hy]; ring
  rw [pow_mul, h2]
  exact dvd_add h1 (dvd_mul_right _ _)

open MvPowerSeries in
private lemma eval_algebraMap_trunc'_map_eq_algebraMap_eval {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]
    {d : ℕ} (s : MvPowerSeries (Fin d) B) (z : Fin d → B) (N : ℕ) :
    MvPolynomial.eval (fun i ↦ algebraMap B Q (z i))
        (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ ↦ N) (map (algebraMap B Q) s)) =
      algebraMap B Q (MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s)) := by
  rw [MvPowerSeries.trunc'_map, MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  rfl


open MvPowerSeries in
theorem _root_.GlobalTheory.QLog.hasPeriod_linear : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : _root_.GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), ∀ F : _root_.GlobalTheory.QLog.BFrame ε, ∀ (G : _root_.GlobalTheory.PDivGroup p O) (d : ℕ) (c : _root_.GlobalTheory.QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), _root_.GlobalTheory.QLog.IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f g : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y y' b : F.B), c.HasPeriod F.θ t f y → c.HasPeriod F.θ t g y' → c.HasPeriod F.θ t (f + algebraMap F.B F.Q b • g) (y + b * y') ∧ (∀ s : MvPowerSeries (Fin d) F.B, constantCoeff s = 0 → c.HasPeriod F.θ t (map (algebraMap F.B F.Q) s) 0) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F G d c μ' _ _ f g t y y' b hf hg
  have hF := F.frame
  rw [c.hasPeriod_iff hF] at hf hg
  refine ⟨?_, ?_⟩
  · rw [c.hasPeriod_iff hF]
    intro n z hz
    obtain ⟨q, hq, b₁, hb₁⟩ := hf n z hz
    obtain ⟨r, hr, b₂, hb₂⟩ := hg n z hz
    have hbr := (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ F.θ hF (Fin d) z g f
      r q hr).2.1 (algebraMap _ _ b)
    refine ⟨q + algebraMap _ _ b * r,
      (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ F.θ hF (Fin d) z f _ q _
        hq).1 hbr, b₁ + b * b₂, ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, map_natCast] at hb₁ hb₂ ⊢
    linear_combination hb₁ + algebraMap _ _ b * hb₂
  · intro s _
    rw [c.hasPeriod_iff hF]
    intro n z hz
    have hz' : ∀ i, ∃ M, (p : F.B) ∣ z i ^ M := fun i => by
      obtain ⟨N, hN⟩ := c.nil n i
      refine exists_pow_dvd_of_theta_eq_of_isFrame hF (hz i) (N := N) ?_
      simpa [map_pow, map_natCast] using map_dvd (t.pt n) hN
    have hd : _root_.GlobalTheory.QLog.DIn (⊤ : Ideal F.B)
        (map (algebraMap F.B F.Q) s) := by
      intro α i
      exact ⟨(α i : F.B) * coeff α s, Submodule.mem_top, by simp⟩
    obtain ⟨q, hq, -⟩ := _root_.GlobalTheory.QLog.existsUnique_hasVal_of_dIn p _ O _
      F.θ hF (Fin d) z hz' _ hd
    have hq' := hq
    unfold _root_.GlobalTheory.QLog.HasVal at hq'
    obtain ⟨N, hN⟩ := hq' 0
    obtain ⟨e, he⟩ := hN N le_rfl
    refine ⟨q, hq, MvPolynomial.eval z
      (trunc' F.B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s) + e, ?_⟩
    rw [eval_algebraMap_trunc'_map_eq_algebraMap_eval, pow_zero, one_mul] at he
    have hq2 : q = algebraMap _ F.Q (MvPolynomial.eval z
        (trunc' F.B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s) + e) := by
      rw [map_add (f := _), ← he]
      ring
    rw [hq2, zero_add, map_mul, map_pow, map_natCast]

end GlobalTheory.QLog
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartHasPeriodLinearIntegralStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalChart_hasPeriod_linear_integral : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f g : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y y' b : F.B), c.HasPeriod F.θ t f y → c.HasPeriod F.θ t g y' → c.HasPeriod F.θ t (f + algebraMap F.B F.Q b • g) (y + b * y') ∧ (∀ s : MvPowerSeries (Fin d) F.B, constantCoeff s = 0 → c.HasPeriod F.θ t (map (algebraMap F.B F.Q) s) 0) := by
  first | exact @GlobalTheory.QLog.hasPeriod_linear | exact GlobalTheory.QLog.hasPeriod_linear | (intros; apply GlobalTheory.QLog.hasPeriod_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPeriodReduceAlongThetaToIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPeriodReduceAlongThetaToIntegers
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog


open MvPowerSeries in
theorem _root_.GlobalTheory.QLog.hasPeriod_reduce : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : _root_.GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), ∀ F : _root_.GlobalTheory.QLog.BFrame ε, ∀ (G : _root_.GlobalTheory.PDivGroup p O) (d : ℕ) (c : _root_.GlobalTheory.QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), _root_.GlobalTheory.QLog.IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (E : Type) [CommRing E] [Algebra O E], _root_.GlobalTheory.QLog.IsFrame p E (RingHom.id O) → ∀ Θ : F.Q →+* E, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O E (F.θ b)) → ∀ (f : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y : F.B), _root_.GlobalTheory.QLog.QL μ' ⊤ f → c.HasPeriod F.θ t f y → c.HasPeriod (RingHom.id O) t (map Θ f) (F.θ y) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F G d c μ' _ _ E _ _ hE Θ hΘ f t y _ hy
  have hF := F.frame
  rw [_root_.GlobalTheory.QLog.Chart.hasPeriod_iff c hF] at hy
  rw [_root_.GlobalTheory.QLog.Chart.hasPeriod_iff c hE]
  intro n z hz
  choose w hw using fun i => hF.surj (z i)
  obtain ⟨q, hq, b, hb⟩ := hy n w (fun i => by rw [hw]; exact hz i)
  refine ⟨Θ q, ?_, F.θ b, ?_⟩
  · have hmap := (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ F.θ hF _ w f f q q
      hq).2.2 O E F.θ Θ hΘ
    simpa [hw] using hmap
  · have h2 := congrArg Θ hb
    rw [map_mul, map_pow, map_natCast, hΘ, map_add (f := _), map_mul, map_pow, map_natCast] at h2
    exact h2

end GlobalTheory.QLog
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPeriodReduceAlongThetaToIntegersStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasPeriod_reduce_along_theta_to_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ Θ : F.Q →+* E, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O E (F.θ b)) → ∀ (f : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y : F.B), QL μ' ⊤ f → c.HasPeriod F.θ t f y → c.HasPeriod (RingHom.id O) t (map Θ f) (F.θ y) := by
  first | exact @GlobalTheory.QLog.hasPeriod_reduce | exact GlobalTheory.QLog.hasPeriod_reduce | (intros; apply GlobalTheory.QLog.hasPeriod_reduce <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentEqZeroOfFormalGroupLawCoboundaryOneEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentEqZeroOfFormalGroupLawCoboundaryOneEqZero
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.LieAdd

variable {R : Type} [CommRing R] {d : ℕ}

theorem subst_zero_of_constantCoeff {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    subst (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) f = 0 := by
  have ha : HasSubst (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  ext e
  rw [coeff_subst ha, map_zero]
  refine finsum_eq_zero_of_forall_eq_zero fun a => ?_
  by_cases h : a = 0
  · subst h
    rw [coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.1 h
    have : (a.prod fun _ k => (0 : MvPowerSeries (Fin d) R) ^ k) = 0 :=
      Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.2 (by simpa using hs))
        (zero_pow (by simpa using hs))
    rw [this, map_zero, smul_zero]

theorem constantCoeff_nmul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (i : Fin d) : constantCoeff (nmul μ n i) = 0 := by
  induction n generalizing i with
  | zero => simp [nmul]
  | succ n ih =>
    rw [nmul, Function.iterate_succ_apply', ← nmul, op, at2]
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j) <;> simp [ih]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

theorem subst_nmul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) {f : MvPowerSeries (Fin d) R} (hf0 : constantCoeff f = 0)
    (hf : cob1 μ f = 0) (n : ℕ) : subst (nmul μ n) f = (n : R) • f := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_smul]
    exact subst_zero_of_constantCoeff hf0
  | succ n ih =>
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j) <;> simp [constantCoeff_nmul hμ]
    have hb := hasSubst_of_constantCoeff_zero hs
    have hm : nmul μ (n + 1) = fun i => subst (Sum.elim (nmul μ n) fun i => X i) (μ i) := by
      rw [nmul, Function.iterate_succ_apply', ← nmul]; rfl
    have hc : subst μ f = inL f + inR f := by
      rw [cob1, sub_sub, sub_eq_zero] at hf; exact hf
    have hl0 : ∀ i, constantCoeff (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
      fun _ => constantCoeff_X _
    have hr0 : ∀ i, constantCoeff (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
      fun _ => constantCoeff_X _
    rw [hm, ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hμ) hb, hc,
      subst_add hb, inL, inR,
      subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hl0) hb,
      subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hr0) hb]
    simp only [subst_X hb, Sum.elim_inl, Sum.elim_inr]
    rw [ih, subst_self, id, Nat.cast_succ, add_smul, one_smul]

theorem nmul_succ {S : Type} [CommRing S] (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) fun i => X i := by
  rw [nmul, Function.iterate_succ_apply', ← nmul]

theorem up_nmul {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    up Q (nmul μ n) = nmul (up Q μ) n := by
  induction n with
  | zero => funext i; simp [up, nmul]
  | succ n ih =>
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) B)) j) = 0 := by
      rintro (j | j) <;> simp [constantCoeff_nmul hμ]
    funext i
    rw [nmul_succ, nmul_succ, ← ih]
    simp only [up, op, at2]
    rw [map_subst (hasSubst_of_constantCoeff_zero hs)]
    congr 1
    funext j
    rcases j with j | j <;> simp [map_X, up]

end GlobalTheory.QLog.LieAdd

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem Chart.isLie_zero_of_cob1_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (f : MvPowerSeries (Fin d) C),
    constantCoeff f = 0 → cob1 (up C c.μ) f = 0 → c.IsLie f 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c f hf0 hf
  have hμ := c.isLaw.const
  have hμC : ∀ i, constantCoeff (up C c.μ i) = 0 := fun i => by
    rw [up, constantCoeff_map, hμ, map_zero]
  refine (c.isLie_iff hv.hom_inj f 0).2 fun n => ⟨0, ?_, fun w φ _ => by simp⟩
  rw [map_zero, defect, LieAdd.up_nmul hμ, LieAdd.subst_nmul hμC hf0 hf, sub_self]

end GlobalTheory.QLog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentEqZeroOfFormalGroupLawCoboundaryOneEqZeroStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_eq_zero_of_formalGroupLawCoboundaryOne_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (f : MvPowerSeries (Fin d) C), constantCoeff f = 0 → cob1 (up C c.μ) f = 0 → c.IsLie f 0 := by
  first | exact @GlobalTheory.QLog.Chart.isLie_zero_of_cob1_eq_zero | exact GlobalTheory.QLog.Chart.isLie_zero_of_cob1_eq_zero | (intros; apply GlobalTheory.QLog.Chart.isLie_zero_of_cob1_eq_zero <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open GlobalTheory.QLog.Window

namespace GlobalTheory.QLog.WindowMat

section Frame

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O) {ε : PreTilt O p}
  (hε : IsPrimitiveSystem ε) (F : BFrame ε) {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)
  {μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B} (hL : IsLift F.θ μ')
  (hμ : ∀ i, map F.θ (μ' i) = c.μ i)
include hv hε hL hμ

theorem hasPeriod_add_smul (t : G.Tate) {f g : MvPowerSeries (Fin d) F.Q} {y y' : F.B} (b : F.B)
    (hg : DIn (⊤ : Ideal F.B) g) (h1 : c.HasPeriod F.θ t f y) (h2 : c.HasPeriod F.θ t g y') :
    c.HasPeriod F.θ t (f + algebraMap F.B F.Q b • g) (y + b * y') := by
  first
  | exact (GlobalTheory.T.formalChart_hasPeriod_linear_integral p C v O hv ε hε F G d c μ' hL hμ f g t y y' b hg h1 h2).1
  | exact (GlobalTheory.T.formalChart_hasPeriod_linear_integral p C v O hv ε hε F G d c μ' hL hμ f g t y y' b h1 h2).1

theorem hasPeriod_map_zero (t : G.Tate) (s : MvPowerSeries (Fin d) F.B) (hs : constantCoeff s = 0) :
    c.HasPeriod F.θ t (map (algebraMap F.B F.Q) s) 0 := by
  have hz := hasPeriod_zero c F.frame t
  have hd : DIn (⊤ : Ideal F.B) (0 : MvPowerSeries (Fin d) F.Q) := din_of_in (in_zero ⊤)
  first
  | exact (GlobalTheory.T.formalChart_hasPeriod_linear_integral p C v O hv ε hε F G d c μ' hL hμ 0 0 t 0 0 0 hd hz hz).2 s hs
  | exact (GlobalTheory.T.formalChart_hasPeriod_linear_integral p C v O hv ε hε F G d c μ' hL hμ 0 0 t 0 0 0 hz hz).2 s hs

theorem hasPeriod_comb (t : G.Tate) {ι : Type} [Fintype ι] (e : ι → MvPowerSeries (Fin d) F.Q)
    (hd : ∀ i, DIn (⊤ : Ideal F.B) (e i)) (y : ι → F.B) (hy : ∀ i, c.HasPeriod F.θ t (e i) (y i))
    (b : ι → F.B) : c.HasPeriod F.θ t (comb b e) (∑ i, b i * y i) := by
  classical
  unfold comb
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using hasPeriod_zero c F.frame t
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, add_comm (b a * y a)]
    exact hasPeriod_add_smul hv hε F c hL hμ t (b a) (hd a) ih (hy a)

theorem hasPeriod_integral (t : G.Tate) {D : MvPowerSeries (Fin d) F.Q}
    (hD : In (⊤ : Ideal F.B) D) (h0 : constantCoeff D = 0) : c.HasPeriod F.θ t D 0 := by
  obtain ⟨s, rfl⟩ := (in_top_iff D).1 hD
  have hs : constantCoeff s = 0 := by
    apply F.frame.inj
    rw [← constantCoeff_map, h0, map_zero]
  exact hasPeriod_map_zero hv hε F c hL hμ t s hs

theorem hasPeriod_unique (t : G.Tate) {f : MvPowerSeries (Fin d) F.Q} {y y' : F.B}
    (h1 : c.HasPeriod F.θ t f y) (h2 : c.HasPeriod F.θ t f y') : y = y' :=
  h1.unique F.frame h2

theorem hasPeriod_of_in (t : G.Tate) {f g : MvPowerSeries (Fin d) F.Q} {y : F.B}
    (hf : c.HasPeriod F.θ t f y) (hfg : In (⊤ : Ideal F.B) (f - g))
    (h0 : constantCoeff (f - g) = 0) : c.HasPeriod F.θ t g y := by
  have h := hasPeriod_add_smul hv hε F c hL hμ t (-1) (din_of_in hfg) hf
    (hasPeriod_integral hv hε F c hL hμ t hfg h0)
  rwa [map_neg, map_one, neg_one_smul, mul_zero, add_zero, neg_sub, add_sub_cancel] at h

end Frame

theorem window_matrices : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, PDivLat.IsConn G → PDivLat.IsConn G.dual → ∀ F : BFrame ε, ∃ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin G.height) F.B) (Gm : Matrix (Fin G.height) (Fin d ⊕ Fin k) F.B) (tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate) (χ : Fin G.height → G.dual.Tate) (w : Module.Basis (Fin d) O G.omega) (lb : Module.Basis (Fin k) O G.dual.Lie), d + k = G.height ∧ IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin G.height) (Fin G.height) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) ∧ (∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0) ∧ (∀ j m, F.θ (Y (Sum.inr j) m) = lb j (hodgeTate G (tb m))) ∧ ∀ m, dlog G (χ m) = ∑ i, F.θ (Gm m (Sum.inl i)) • w i := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG hGd F
  obtain ⟨d, ⟨c⟩⟩ := GlobalTheory.T.exists_pDivGroupFormalChart_of_connected p C v O hv G hG
  have hdk := GlobalTheory.T.chartDim_add_finrank_dual_lie_eq_height p C v O hv G d c
  have hCf := GlobalTheory.T.isTorsionFreePDThickeningFrame_valuation_integers p C v O hv
  obtain ⟨k, e0, lb, hB0, hA0, hcob0, hLie0⟩ := GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual p C v O hv G d c C hCf
  obtain ⟨μ', hL, hμ⟩ := GlobalTheory.T.exists_formalGroupLawLift_of_surjective F.B O F.θ F.frame.surj d c.μ c.isLaw
  obtain ⟨Θ, hΘ⟩ := frame_fraction_map p F.B O F.Q F.θ F.frame C hCf
  obtain ⟨e, he0, hB, hA⟩ := GlobalTheory.T.exists_lift_adapted_basis_quasi_logarithms_frame p C v O hv ε hε F G d c μ' hL hμ Θ hΘ k e0 hB0 hA0
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_frobenius_matrix_quasiLogarithm_basis p C v O hv ε hε F G d c μ' hL hμ k e hB hA
  have hUu := GlobalTheory.T.frobenius_matrix_isUnit_adapted_basis p C v O hv ε hε F G d c μ' hL hμ k e hB hA U hU
  have hN1 := GlobalTheory.T.frobenius_nilpotent_mod_maximal_connected_pDivGroup p C v O hv ε hε F G d c μ' hL hμ k e hB hA U fun i => (hU i).1
  have hN2 := GlobalTheory.T.isNil_dual_frobenius_alt p C v O hv ε hε F G d c μ' hL hμ k e hB hA hGd U hUu hU
  haveI := integers_isIntegrallyClosedIn hv
  haveI := G.finite_tate C
  haveI := G.free_tate C
  let tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate :=
    Module.finBasisOfFinrankEq ℤ_[p] G.Tate (G.finrank_tate C)
  obtain ⟨χ, hχ, -⟩ :=
    GlobalTheory.DieudonneSandwich.exists_dual_basis hε (G.pairing_flip_bijective C) tb.equivFun
  have hpair : ∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0 := by
    intro m m'
    have h1 := epsPairing_smul hε G (tb m) (χ m')
    rw [hχ m' (tb m)] at h1
    have h2 : epsPairing hε G (tb m) (χ m') = tb.equivFun (tb m) m' := (epsEquiv hε).injective h1
    rw [h2, Module.Basis.equivFun_self]
    all_goals
      by_cases h : m = m'
      · subst h; simp
      · simp [Pi.single_apply, h, Ne.symm h]
  have hQLe : ∀ l, QL μ' ⊤ (e l) := hB.1
  have hDe : ∀ l, DIn (⊤ : Ideal F.B) (e l) := fun l =>
    GlobalTheory.QLogDiff.dIn_of_QL p F.B O F.Q F.θ F.frame d μ' hL ⊤ (e l) (hQLe l)
  choose Y hY using fun l m =>
    (GlobalTheory.T.exists_unique_period_quasiLogarithm_pDivGroup p C v O hv ε hε F G d c μ' hL hμ (e l) (tb m) (hQLe l)).exists
  choose fχ wχ hfχ using fun m => GlobalTheory.T.exists_quasiLogarithm_of_dualCharacter p C v O hv ε hε F G d c μ' hL hμ (χ m)
  choose g hg using fun m => (hB.2 (fχ m) (hfχ m).1).exists
  obtain ⟨hbij, -⟩ := GlobalTheory.T.pdDivGroupChart_forms_basis_and_differential p C v O hv G d c
  let w : Module.Basis (Fin d) O G.omega :=
    Module.Basis.ofEquivFun (LinearEquiv.ofBijective (Fintype.linearCombination O c.form) hbij).symm
  have hw : ∀ i, w i = c.form i := by
    intro i
    simp [w, Module.Basis.ofEquivFun]
  have hcomb0 : ∀ m, constantCoeff (fχ m - comb (g m) e) = 0 := fun m => by
    rw [map_sub, (hfχ m).1.1, (ql_comb hL.const e hQLe (g m)).1, sub_zero]

  have hred : ∀ m, (∀ j, F.θ (g m (Sum.inr j)) = 0) ∧
      ∀ i, lin (map Θ (fχ m)) i = algebraMap O C (F.θ (g m (Sum.inl i))) := fun m => by
    refine GlobalTheory.T.logarithm_integers_adapted_basis_no_lie_components p C v O hv G d c k e0 lb hB0 hA0 hLie0 (map Θ (fχ m))
      (ql_map F.θ Θ hΘ hμ hL.const (hfχ m).1)
      (formalGroupLawCoboundaryOne_map_eq_zero F.θ Θ hΘ hμ hL.const (hfχ m).2.1) (fun l => F.θ (g m l)) ?_
    have := in_map_top F.θ Θ hΘ (hg m)
    rwa [map_sub, map_comb F.θ Θ hΘ, show (fun l => map Θ (e l)) = e0 from funext he0] at this

  have hperO : ∀ l m, c.HasPeriod (RingHom.id O) (tb m) (e0 l) (F.θ (Y l m)) := fun l m => by
    have h := GlobalTheory.T.hasPeriod_reduce_along_theta_to_integers p C v O hv ε hε F G d c μ' hL hμ C hCf Θ hΘ (e l) (tb m) (Y l m)
      (hQLe l) (hY l m)
    rwa [he0] at h
  refine ⟨d, k, U, Matrix.of Y, Matrix.of g, tb, χ, w, lb, ?_, hUu, ?_, ?_, ?_, ?_, ?_, hN1, hN2,
    hpair, ?_, ?_⟩
  · have := Module.finrank_eq_card_basis lb
    rw [Fintype.card_fin] at this
    omega
  ·
    ext i m
    have key : F.σ (Y i m) = ∑ l, (U * blk d k (p : F.B) 1) l i * Y l m := by
      have hc := hasPeriod_comb hv hε F c hL hμ (tb m) e hDe (fun l => Y l m) (fun l => hY l m)
        (fun l => (U * blk d k (p : F.B) 1) l i)
      have hf := GlobalTheory.T.quasiLogarithm_period_frobenius_twist p C v O hv ε hε F G d c μ' hL hμ (e i) (tb m) (Y i m) (hQLe i)
        (hY i m)
      refine hasPeriod_unique hv hε F c hL hμ (tb m)
        (hasPeriod_of_in hv hε F c hL hμ (tb m) hf (hU i).1 ?_) hc
      rw [map_sub, constantCoeff_frob p F.s (hQLe i).1, (ql_comb hL.const e hQLe _).1, sub_zero]
    rw [Matrix.map_apply, Matrix.of_apply, key, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [blk, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
      Matrix.of_apply]
    ring
  ·
    ext l m
    have key : (fun l => ∑ i, (U * blk d k (p : F.B) 1) l i * F.σ (g m i)) =
        fun l => (p : F.B) * g m l := by
      have hP : QL μ' ⊤ (algebraMap F.B F.Q (p : F.B) • fχ m) := by
        simpa using ql_add_smul hL.const (ql_zero (Q := F.Q) hL.const ⊤) (hfχ m).1 (p : F.B)
      refine (hB.2 _ hP).unique ?_ ?_
      · have e1 : algebraMap F.B F.Q (p : F.B) • fχ m -
            comb (fun l => ∑ i, (U * blk d k (p : F.B) 1) l i * F.σ (g m i)) e =
            -(frob p F.s (fχ m) - (p : F.Q) • fχ m) + frob p F.s (fχ m - comb (g m) e) +
              ∑ i, algebraMap F.B F.Q (F.σ (g m i)) •
                (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) := by
          rw [comb_sum (fun l i => (U * blk d k (p : F.B) 1) l i) (fun i => F.σ (g m i)) e, frob_sub, frob_comb p F.s F.σ F.s_alg, map_natCast]
          simp only [comb, smul_sub, Finset.sum_sub_distrib]
          abel
        rw [e1]
        refine in_add (in_add (in_neg (hfχ m).2.2.1) (in_frob p F.s F.σ F.s_alg (hg m)))
          (in_sum _ _ fun i _ => in_smul (hU i).1 _)
      · have e2 : algebraMap F.B F.Q (p : F.B) • fχ m - comb (fun l => (p : F.B) * g m l) e =
            algebraMap F.B F.Q (p : F.B) • (fχ m - comb (g m) e) := by
          simp only [comb, map_mul, mul_smul, smul_sub, Finset.smul_sum]
        rw [e2]
        exact in_smul (hg m) _
    have := congrFun key l
    simp only [Matrix.smul_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, ← this,
      Matrix.mul_apply, Matrix.map_apply]
  ·
    ext m m'
    have key : ∑ l, g m l * Y l m' =
        F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G (tb m') (χ m))) := by
      refine hasPeriod_unique hv hε F c hL hμ (tb m')
        (hasPeriod_comb hv hε F c hL hμ (tb m') e hDe (fun l => Y l m') (fun l => hY l m') (g m)) ?_
      exact hasPeriod_of_in hv hε F c hL hμ (tb m') ((hfχ m).2.2.2.2.2 (tb m')) (hg m) (hcomb0 m)
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    rw [key, hpair]
    by_cases h : m' = m
    · subst h; simp
    · simp [h, Ne.symm h]
  ·
    intro i m
    have hlie := GlobalTheory.T.tangent_eq_zero_of_formalGroupLawCoboundaryOne_eq_zero p C v O hv G d c (e0 (Sum.inl i)) (hB0.1 (Sum.inl i)).1 (hcob0 i)
    have h2 := GlobalTheory.T.quasiLogarithm_period_eq_tangent_hodgeTate p C v O hv G d c C hCf (e0 (Sum.inl i)) 0 (hB0.1 _) hlie (tb m)
    simpa using (hperO _ m).unique hCf h2
  · intro m j
    exact (hred m).1 j
  · intro j m
    exact (hperO _ m).unique hCf
      (GlobalTheory.T.quasiLogarithm_period_eq_tangent_hodgeTate p C v O hv G d c C hCf (e0 (Sum.inr j)) (lb j) (hB0.1 _) (hLie0 j) (tb m))
  · intro m
    rw [(hfχ m).2.2.2.2.1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := (hred m).2 i
    rw [lin_map F.θ Θ hΘ, (hfχ m).2.2.2.1 i, hΘ] at h1
    rw [hw, Matrix.of_apply, hCf.inj h1]

end GlobalTheory.QLog.WindowMat
