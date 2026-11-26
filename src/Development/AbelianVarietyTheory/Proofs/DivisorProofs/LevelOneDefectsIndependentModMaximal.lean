module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftQuasiLogarithmAlongPdThickening
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisLiftPdThickening
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedQuasiLogBasisPDivGroupLieDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameReflTransGenCyclicChain

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmTangentVectorsBasisDualLie
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmTangentVectorsBasisDualLie
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBasisChange

open GlobalTheory.QLog

variable {d : ℕ} {O E : Type} [CommRing O] [CommRing E] [Algebra O E]

def intMap : MvPowerSeries (Fin d) O →ₗ[O] MvPowerSeries (Fin d) E where
  toFun := map (algebraMap O E)
  map_add' := map_add _
  map_smul' a s := by
    ext α
    change algebraMap O E (a * s α) = a • algebraMap O E (s α)
    rw [map_mul, Algebra.smul_def]

theorem in_top_iff (f : MvPowerSeries (Fin d) E) :
    In (⊤ : Ideal O) f ↔ f ∈ LinearMap.range (intMap (d := d) (O := O) (E := E)) := by
  rw [In.top_iff]; rfl

theorem comb_eq {ι : Type} [Fintype ι] (b : ι → O) (e : ι → MvPowerSeries (Fin d) E) :
    comb b e = Fintype.linearCombination O e b := by
  simp [comb, Fintype.linearCombination_apply, algebraMap_smul]

theorem defect_add_smul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (f g : MvPowerSeries (Fin d) E) (a : O) :
    defect μ n (f + a • g) = defect μ n f + a • defect μ n g := by
  have hs := hasSubst_up_nmul (Q := E) hμ n
  simp only [defect, ← coe_substAlgHom hs, ← algebraMap_smul E a, map_add (f := _), map_smul]
  module

theorem isLie_add_smul {p : ℕ} {G : PDivGroup p O} (c : QLog.Chart G d)
    (hinj : Function.Injective (algebraMap O E)) {f g : MvPowerSeries (Fin d) E}
    {l l' : G.dual.Lie} (a : O) (hf : c.IsLie f l) (hg : c.IsLie g l') :
    c.IsLie (f + a • g) (l + a • l') := by
  rw [QLog.Chart.isLie_iff c hinj] at hf hg ⊢
  intro n
  obtain ⟨s, hs, H⟩ := hf n
  obtain ⟨s', hs', H'⟩ := hg n
  refine ⟨s + a • s', ?_, fun w φ hφ => ?_⟩
  · rw [defect_add_smul c.isLaw.const, ← hs, ← hs']
    have := (intMap (d := d) (O := O) (E := E)).map_add s (a • s')
    rw [LinearMap.map_smul] at this
    exact this
  · have := dvd_add (H w φ hφ) (dvd_mul_of_dvd_right (H' w φ hφ) a)
    rw [LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smul, map_add (f := _), map_smul,
      smul_eq_mul, smul_eq_mul]
    convert this using 1
    ring

theorem isLie_sum {p : ℕ} {G : PDivGroup p O} (c : QLog.Chart G d)
    (hinj : Function.Injective (algebraMap O E)) {ι : Type} [Fintype ι]
    (e : ι → MvPowerSeries (Fin d) E) (L : ι → G.dual.Lie) (hL : ∀ i, c.IsLie (e i) (L i))
    (b : ι → O) : c.IsLie (comb b e) (∑ i, b i • L i) := by
  classical
  rw [comb_eq, Fintype.linearCombination_apply]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using c.isLie_zero hinj
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, add_comm, add_comm (b i • L i)]
    exact isLie_add_smul c hinj (b i) ih (hL i)

theorem mul_eq_one {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} {ι κ : Type} [Fintype ι]
    [Fintype κ] [DecidableEq ι] {f : ι → MvPowerSeries (Fin d) E} {g : κ → MvPowerSeries (Fin d) E}
    (hf : IsBasis μ f) (P : ι → κ → O) (R : κ → ι → O)
    (hP : ∀ l, In (⊤ : Ideal O) (f l - comb (P l) g))
    (hR : ∀ m, In (⊤ : Ideal O) (g m - comb (R m) f)) :
    Matrix.of P * Matrix.of R = 1 := by
  ext l l'
  have h1 : In (⊤ : Ideal O) (f l - comb (Pi.single l (1 : O)) f) := by
    rw [in_top_iff, comb_eq, Fintype.linearCombination_apply_single, one_smul, sub_self]
    exact zero_mem _
  have h2 : In (⊤ : Ideal O) (f l - comb (∑ m, P l m • R m) f) := by
    have e1 : f l - comb (∑ m, P l m • R m) f =
        (f l - comb (P l) g) + ∑ m, P l m • (g m - comb (R m) f) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [comb_eq, map_sum, map_smul]
      simp only [Fintype.linearCombination_apply, smul_sub, Finset.sum_sub_distrib]
      abel
    rw [e1, in_top_iff]
    simp only [in_top_iff] at hP hR
    exact add_mem (hP l) (Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hR m))
  have := congrFun ((hf.2 (f l) (hf.1 l)).unique h2 h1) l'
  simpa [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, Finset.sum_apply, eq_comm] using this

theorem card_eq [Nontrivial O] {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (P : Matrix ι κ O) (R : Matrix κ ι O) (h1 : P * R = 1) (h2 : R * P = 1) :
    Fintype.card ι = Fintype.card κ := by
  have e : (κ → O) ≃ₗ[O] (ι → O) := LinearEquiv.ofLinear (Matrix.toLin' P) (Matrix.toLin' R)
    (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have := e.finrank_eq
  rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, eq_comm] at this

theorem lie_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E), IsBasis c.μ e → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → ∃ lb : Module.Basis (Fin k) O G.dual.Lie, ∀ j, c.IsLie (e (Sum.inr j)) (lb j) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ h k e he hlog
  classical
  obtain ⟨k0, e0, lb0, he0, -, -, hlie0⟩ := GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual p C v O hv G d c E h
  have hinj : Function.Injective (algebraMap O E) := h.inj
  have hex := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E h
  have hlin := GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E h
  choose L hL using fun l => (hex _ (he.1 l)).exists
  have hL0 : ∀ i, L (Sum.inl i) = 0 := fun i =>
    (hlin _ _ _ _ 0 (hL (Sum.inl i)) (hL (Sum.inl i))).2.2 (hlog i)
  have hspan : ⊤ ≤ Submodule.span O (Set.range (L ∘ Sum.inr)) := by
    rw [← lb0.span_eq, Submodule.span_le]
    rintro _ ⟨j', rfl⟩
    obtain ⟨b, hb, -⟩ := he.2 (e0 (Sum.inr j')) (he0.1 (Sum.inr j'))
    have h1 : c.IsLie (e0 (Sum.inr j') + (-1 : O) • comb b e)
        (lb0 j' + (-1 : O) • ∑ l, b l • L l) :=
      isLie_add_smul c hinj (-1) (hlie0 j') (isLie_sum c hinj e L hL b)
    rw [neg_one_smul, neg_one_smul, ← sub_eq_add_neg, ← sub_eq_add_neg] at h1
    have h2 := (hlin _ _ _ _ 0 h1 h1).2.1 ((In.top_iff.1 hb).imp fun s hs => hs.symm)
    rw [sub_eq_zero, Fintype.sum_sum_type] at h2
    simp only [hL0, smul_zero, Finset.sum_const_zero, zero_add] at h2
    rw [SetLike.mem_coe, h2]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  choose P hP using fun l => (he0.2 (e l) (he.1 l)).exists
  choose R hR using fun m => (he.2 (e0 m) (he0.1 m)).exists
  have hk := card_eq (Matrix.of P) (Matrix.of R) (mul_eq_one he P R hP hR)
    (mul_eq_one he0 R P hR hP)
  simp only [Fintype.card_sum, Fintype.card_fin] at hk
  obtain rfl : k0 = k := by omega
  have hsurj : Function.Surjective (Fintype.linearCombination O (L ∘ Sum.inr)) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact eq_top_iff.2 hspan
  have hinj2 : Function.Injective (Fintype.linearCombination O (L ∘ Sum.inr)) :=
    Function.Injective.of_comp (f := ⇑lb0.equivFun)
      (OrzechProperty.injective_of_surjective_endomorphism
        (lb0.equivFun.toLinearMap ∘ₗ Fintype.linearCombination O (L ∘ Sum.inr))
        (lb0.equivFun.surjective.comp hsurj))
  have hli : LinearIndependent O (L ∘ Sum.inr) :=
    linearIndependent_iff_injective_fintypeLinearCombination.2 hinj2
  exact ⟨Module.Basis.mk hli hspan, fun j => by rw [Module.Basis.mk_apply]; exact hL (Sum.inr j)⟩

end GlobalTheory.LieBasisChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmTangentVectorsBasisDualLieStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_tangentVectors_basis_dual_lie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E), IsBasis c.μ e → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → ∃ lb : Module.Basis (Fin k) O G.dual.Lie, ∀ j, c.IsLie (e (Sum.inr j)) (lb j) := by
  first | exact @GlobalTheory.LieBasisChange.lie_basis | exact GlobalTheory.LieBasisChange.lie_basis | (intros; apply GlobalTheory.LieBasisChange.lie_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiLogarithmBasisReductionThickening
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiLogarithmBasisReductionThickening
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ReduceBasis

section Ring

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_zero : In (⊤ : Ideal B) (0 : MvPowerSeries σ Q) :=
  fun _ => ⟨0, trivial, by simp⟩

theorem in_neg {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) : In (⊤ : Ideal B) (-f) := by
  simpa using KLift.in_sub in_zero hf

theorem in_smul (r : B) {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) :
    In (⊤ : Ideal B) (algebraMap B Q r • f) := fun α => by
  obtain ⟨b, -, hb⟩ := hf α
  exact ⟨r * b, trivial, by rw [coeff_smul, hb, map_mul]⟩

theorem in_sum {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ Q)
    (hf : ∀ i, In (⊤ : Ideal B) (f i)) : In (⊤ : Ideal B) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (in_zero : In (⊤ : Ideal B) (0 : MvPowerSeries σ Q))
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact KLift.in_add (hf a) ih

variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem comb_sub (x y : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb x e - comb y e = comb (x - y) e := by
  simp only [comb, ← Finset.sum_sub_distrib, Pi.sub_apply, map_sub, sub_smul]

theorem comb_single [DecidableEq ι] (l : ι) (e : ι → MvPowerSeries σ Q) :
    comb (Pi.single l (1 : B)) e = e l := by
  rw [comb, Finset.sum_eq_single l (fun j _ hj => by simp [Pi.single_apply, hj])
    (fun h => absurd (Finset.mem_univ l) h)]
  simp

theorem comb_comb (M : κ → B) (N : κ → ι → B) (e : ι → MvPowerSeries σ Q) :
    ∑ m, algebraMap B Q (M m) • comb (N m) e = comb (fun l => ∑ m, M m * N m l) e := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, Finset.smul_sum, smul_smul, ← map_mul, map_sum, Finset.sum_smul]
  exact Finset.sum_comm

theorem mul_eq_single [DecidableEq ι] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    {e : ι → MvPowerSeries (Fin d) Q} {f : κ → MvPowerSeries (Fin d) Q} (he : IsBasis μ e)
    (M : ι → κ → B) (N : κ → ι → B) (hM : ∀ l, In (⊤ : Ideal B) (e l - comb (M l) f))
    (hN : ∀ m, In (⊤ : Ideal B) (f m - comb (N m) e)) (l : ι) :
    (fun l' => ∑ m, M l m * N m l') = Pi.single l 1 := by
  refine (he.2 (e l) (he.1 l)).unique ?_ ?_
  · have hs : e l - comb (fun l' => ∑ m, M l m * N m l') e =
        (e l - comb (M l) f) + ∑ m, algebraMap B Q (M l m) • (f m - comb (N m) e) := by
      simp only [smul_sub, Finset.sum_sub_distrib, comb_comb]
      simp only [comb]; abel
    rw [hs]
    exact KLift.in_add (hM l) (in_sum _ _ fun m => in_smul _ (hN m))
  · rw [comb_single, sub_self]; exact in_zero

end Ring

section Map

variable {B O Q C : Type} [CommRing B] [CommRing O] [CommRing Q] [CommRing C] [Algebra B Q]
  [Algebra O C] {σ : Type} {θ : B →+* O} {Θ : Q →+* C}
  (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))

include hΘ in
theorem in_map {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) :
    In (⊤ : Ideal O) (map Θ f) := fun α => by
  obtain ⟨b, -, hb⟩ := hf α
  exact ⟨θ b, trivial, by rw [coeff_map, hb, hΘ]⟩

theorem map_smul_series (c : Q) (f : MvPowerSeries σ Q) : map Θ (c • f) = Θ c • map Θ f := by
  ext α
  simp [coeff_map, coeff_smul]

include hΘ in
theorem map_comb {ι : Type} [Fintype ι] (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    map Θ (comb b e) = comb (fun i => θ (b i)) (fun i => map Θ (e i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, map_sum, map_smul_series, hΘ]

end Map

end GlobalTheory.ReduceBasis

namespace GlobalTheory.ReduceBasis

theorem isBasis_map : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → IsBasis c.μ (fun l => map Θ (e l)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hμ k e he Θ hΘ
  classical
  have hC : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  have hcμ : (fun i => map F.θ (μ' i)) = c.μ := funext hμ
  have hμQ : ∀ i, constantCoeff (up F.Q μ' i) = 0 := KLift.const_map _ μ' hL.const
  have hμC : ∀ i, constantCoeff (up C c.μ i) = 0 := KLift.const_map _ _ c.isLaw.const
  have hΘμ : (fun i => map Θ (up F.Q μ' i)) = up C c.μ := by
    have hc : Θ.comp (algebraMap F.B F.Q) = (algebraMap O C).comp F.θ := RingHom.ext hΘ
    funext i
    unfold up
    rw [← hμ i, ← RingHom.comp_apply (map Θ), ← map_comp,
      ← RingHom.comp_apply (map (algebraMap O C)), ← map_comp, hc]
  have hQL : ∀ f, QL μ' ⊤ f → QL c.μ ⊤ (map Θ f) := by
    rintro f ⟨h0, h1, h2⟩
    refine ⟨?_, fun i => ?_, ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
        map_zero]
    · obtain ⟨b, -, hb⟩ := h1 i
      refine ⟨F.θ b, trivial, ?_⟩
      simp only [lin, coeff_map] at hb ⊢
      rw [hb, hΘ]
    · rw [← hΘμ, ← KLift.map_formalGroupLawCoboundaryOne_eq Θ _ hμQ]
      exact in_map hΘ h2

  have hlift : ∀ g, QL c.μ ⊤ g → ∃ f, QL μ' ⊤ f ∧ map Θ f = g := by
    intro g hg
    choose o _ ho using hg.2.1
    choose w hw using fun i => F.frame.surj (o i)
    obtain ⟨f, hf, hfg, -⟩ := KLift.lift_quasiLog p F.B O F.Q F.θ F.frame d μ' hL C hC Θ hΘ g w
      (by rw [hcμ]; exact hg) (fun i => by rw [ho, hw])
    exact ⟨f, hf, hfg⟩
  have key : ∀ x : Fin d ⊕ Fin k → O, In (⊤ : Ideal O) (comb x fun l => map Θ (e l)) → x = 0 := by
    intro x hx
    obtain ⟨k0, e0, -, he0, -⟩ := GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual p C v O hv G d c C hC
    choose f hf hfe using fun m => hlift (e0 m) (he0.1 m)
    have hfB : IsBasis μ' f := GlobalTheory.basis_lift p F.B O F.Q F.θ F.frame d μ' hL C hC Θ hΘ _ f hf
      (by rw [hcμ]; simpa only [hfe] using he0) (GlobalTheory.BChain.reflTransGen_isStep p C v O hv ε hε F)
    choose M hM _ using fun l => hfB.2 (e l) (he.1 l)
    choose N hN _ using fun m => he.2 (f m) (hf m)
    have hMN := mul_eq_single he M N hM hN
    set y : Fin d ⊕ Fin k0 → O := fun m => ∑ l, x l * F.θ (M l m) with hydef
    have hy : In (⊤ : Ideal O) (comb y e0) := by
      have hs : comb y e0 = comb x (fun l => map Θ (e l)) -
          ∑ l, algebraMap O C (x l) • map Θ (e l - comb (M l) f) := by
        simp only [map_sub, map_comb hΘ, hfe, smul_sub, Finset.sum_sub_distrib, comb_comb, hydef]
        simp only [comb]
        abel
      rw [hs]
      exact KLift.in_sub hx (in_sum _ _ fun l => in_smul _ (in_map hΘ (hM l)))
    have h0 : QL c.μ ⊤ (0 : MvPowerSeries (Fin d) C) := by
      refine ⟨by simp, fun i => ⟨0, trivial, by simp [lin]⟩, ?_⟩
      have : cob1 (up C c.μ) (0 : MvPowerSeries (Fin d) C) = 0 := by
        simpa using formalCoboundary_smul hμC (0 : C) (0 : MvPowerSeries (Fin d) C)
      rw [this]
      exact in_zero
    have hy0 : y = 0 := by
      refine (he0.2 0 h0).unique ?_ ?_
      · simpa using in_neg hy
      · have : comb (0 : Fin d ⊕ Fin k0 → O) e0 = 0 := by simp [comb]
        rw [this, sub_zero]
        exact in_zero
    funext l'
    have e1 : ∀ l, F.θ (∑ m, M l m * N m l') = if l' = l then 1 else 0 := fun l => by
      have h1 := congrFun (hMN l) l'
      rw [h1, Pi.single_apply]
      split_ifs <;> simp
    have s1 : x l' = ∑ l, x l * F.θ (∑ m, M l m * N m l') := by
      simp only [e1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have s2 : ∑ l, x l * F.θ (∑ m, M l m * N m l') = ∑ m, y m * F.θ (N m l') := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hydef, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
    rw [s1, s2, hy0]
    simp
  refine ⟨fun l => hQL _ (he.1 l), fun g hg => ?_⟩
  obtain ⟨f, hf, hfg⟩ := hlift g hg
  obtain ⟨b, hb, -⟩ := he.2 f hf
  have hx0 : In (⊤ : Ideal O) (g - comb (fun l => F.θ (b l)) fun l => map Θ (e l)) := by
    have := in_map hΘ hb
    rwa [map_sub, hfg, map_comb hΘ] at this
  refine ⟨fun l => F.θ (b l), hx0, fun y hy => ?_⟩
  have h := key ((fun l => F.θ (b l)) - y) (by
    rw [← comb_sub]
    convert KLift.in_sub hy hx0 using 1
    abel)
  exact (sub_eq_zero.1 h).symm

end GlobalTheory.ReduceBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiLogarithmBasisReductionThickeningStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQuasiLogarithmBasis_reduction_thickening : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → IsBasis c.μ (fun l => map Θ (e l)) := by
  first | exact @GlobalTheory.ReduceBasis.isBasis_map | exact GlobalTheory.ReduceBasis.isBasis_map | (intros; apply GlobalTheory.ReduceBasis.isBasis_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpPull2Cob1
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory

namespace Katz

namespace ExtCoeff

variable {O E : Type} [CommRing O] [CommRing E] {d : ℕ}

theorem hasSubst_XL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_XR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem map_inL (h : O →+* E) (f : MvPowerSeries (Fin d) O) : map h (inL f) = inL (map h f) := by
  unfold inL
  rw [map_subst hasSubst_XL]
  congr 1
  funext i
  exact map_X h _

theorem map_inR (h : O →+* E) (f : MvPowerSeries (Fin d) O) : map h (inR f) = inR (map h f) := by
  unfold inR
  rw [map_subst hasSubst_XR]
  congr 1
  funext i
  exact map_X h _

theorem map_formalGroupLawCoboundaryOne_eq (h : O →+* E) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)
    (s : MvPowerSeries (Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0) :
    cob1 (fun i => map h (μ i)) (map h s) = map h (cob1 μ s) := by
  unfold cob1
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero hμ), map_inL, map_inR]

end ExtCoeff

end Katz

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelOneDefectsIndependentModMaximal
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LevelOneIndep

variable {B Q O C : Type} [CommRing B] [CommRing Q] [CommRing O] [CommRing C] [Algebra B Q] [Algebra O C]
  {d : ℕ}

theorem map_up (θ : B →+* O) (Θ : Q →+* C) (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    {τ : Type} (u : MvPowerSeries τ B) :
    map Θ (map (algebraMap B Q) u) = map (algebraMap O C) (map θ u) := by
  ext α; simp [coeff_map, hΘ]

theorem map_formalGroupLawCoboundaryOne_square (θ : B →+* O) (Θ : Q →+* C) (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (hν : ∀ i, map θ (μ i) = ν i) (f : MvPowerSeries (Fin d) Q) :
    map Θ (cob1 (up Q μ) f) = cob1 (up C ν) (map Θ f) := by
  rw [← ExtCoeff.map_formalGroupLawCoboundaryOne_eq Θ (up Q μ) f (fun i => by simp [up, hμ])]
  congr 1
  funext i
  simp only [up]
  rw [map_up θ Θ hΘ, hν]

theorem map_defect (θ : B →+* O) (Θ : Q →+* C) (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (hν : ∀ i, map θ (μ i) = ν i) (n : ℕ)
    (f : MvPowerSeries (Fin d) Q) :
    map Θ (defect μ n f) = defect ν n (map Θ f) := by
  have hs : HasSubst (up Q (nmul μ n)) :=
    hasSubst_of_constantCoeff_zero fun i => by simp [up, MapNMul.cc_nmul μ hμ]
  unfold defect
  rw [map_sub, map_subst hs]
  congr 1
  · ext α; simp [coeff_map]
  · congr 1
    funext i
    simp only [up]
    rw [map_up θ Θ hΘ, MapNMul.map_nmul B O θ d μ hμ]
    congr 2
    funext j
    exact hν j

theorem constantCoeff_formalGroupLawCoboundaryOne {R : Type} [CommRing R] (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (g : MvPowerSeries (Fin d) R) :
    constantCoeff (cob1 μ g) = - constantCoeff g := by
  simp only [cob1, inL, inR, map_sub]
  rw [GlobalTheory.T.constantCoeff_subst_of_forall_constantCoeff_zero R _ _ _ hμ, GlobalTheory.T.constantCoeff_subst_of_forall_constantCoeff_zero R _ _ _ (fun _ => constantCoeff_X _),
    GlobalTheory.T.constantCoeff_subst_of_forall_constantCoeff_zero R _ _ _ (fun _ => constantCoeff_X _)]
  ring

theorem defect_add (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hν : ∀ i, constantCoeff (ν i) = 0)
    (n : ℕ) (f g : MvPowerSeries (Fin d) C) :
    defect ν n (f + g) = defect ν n f + defect ν n g := by
  have hs : HasSubst (up C (nmul ν n)) :=
    hasSubst_of_constantCoeff_zero fun i => by simp [up, MapNMul.cc_nmul ν hν]
  unfold defect
  rw [subst_add hs, smul_add]
  abel

theorem defect_log (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hν : ∀ i, constantCoeff (ν i) = 0)
    (n : ℕ) (g : MvPowerSeries (Fin d) C) (hg : cob1 (up C ν) g = 0) : defect ν n g = 0 := by
  have hνC : ∀ i, constantCoeff (up C ν i) = 0 := fun i => by simp [up, hν]
  have hc : constantCoeff g = 0 := by
    have := constantCoeff_formalGroupLawCoboundaryOne (up C ν) hνC g
    rw [hg, map_zero] at this
    exact neg_eq_zero.1 this.symm
  unfold defect
  rw [GlobalTheory.T.mapPowerSeriesFamilyToFractions_formalGroupLawNatMultiple O C d ν hν n, GlobalTheory.T.subst_formalGroupLawNatMultiple_eq_coboundary_sum C d (up C ν) hνC g n, hg, hc]
  have h0 : ∀ k, (at2 (0 : MvPowerSeries (Fin d ⊕ Fin d) C) (nmul (up C ν) k) fun i => X i) = 0 := by
    intro k
    have ha : HasSubst (Sum.elim (nmul (up C ν) k) fun i => (X i : MvPowerSeries (Fin d) C)) :=
      hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [MapNMul.cc_nmul _ hνC]
    unfold at2
    rw [← coe_substAlgHom ha, map_zero]
  simp [h0]

end GlobalTheory.LevelOneIndep

namespace GlobalTheory.LevelOneIndep

theorem map_smul' {Q C : Type} [CommRing Q] [CommRing C] (Θ : Q →+* C) {τ : Type} (r : Q)
    (g : MvPowerSeries τ Q) : map Θ (r • g) = Θ r • map Θ g := by
  ext α; simp [coeff_map]

theorem QL_map {B Q O C : Type} [CommRing B] [CommRing Q] [CommRing O] [CommRing C] [Algebra B Q]
    [Algebra O C] {d : ℕ} (θ : B →+* O) (Θ : Q →+* C)
    (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (hν : ∀ i, map θ (μ i) = ν i) (f : MvPowerSeries (Fin d) Q)
    (hf : QL μ ⊤ f) : QL ν ⊤ (map Θ f) := by
  refine ⟨?_, fun i => ?_, fun α => ?_⟩
  · rw [constantCoeff_map, hf.1, map_zero]
  · obtain ⟨b, -, hb⟩ := hf.2.1 i
    refine ⟨θ b, trivial, ?_⟩
    simp only [lin] at hb ⊢
    rw [coeff_map, hb, hΘ]
  · obtain ⟨b, -, hb⟩ := hf.2.2 α
    refine ⟨θ b, trivial, ?_⟩
    rw [← map_formalGroupLawCoboundaryOne_square θ Θ hΘ μ ν hμ hν, coeff_map, hb, hΘ]

theorem QL_comb' (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f g : MvPowerSeries (Fin d) E) (a : O) (hf : QL μ ⊤ f) (hg : QL μ ⊤ g) :
    QL μ ⊤ (f + algebraMap O E a • g) := by
  have hμE : ∀ i, constantCoeff (up E μ i) = 0 := fun i => by simp [up, hμ]
  refine ⟨?_, fun i => ?_, fun α => ?_⟩
  · simp [hf.1, hg.1]
  · obtain ⟨x, -, hx⟩ := hf.2.1 i
    obtain ⟨y, -, hy⟩ := hg.2.1 i
    refine ⟨x + a * y, trivial, ?_⟩
    simp only [lin] at hx hy ⊢
    rw [map_add (f := _), coeff_smul, hx, hy, map_add (f := _), map_mul]
  · obtain ⟨x, -, hx⟩ := hf.2.2 α
    obtain ⟨y, -, hy⟩ := hg.2.2 α
    refine ⟨x + a * y, trivial, ?_⟩
    rw [formalCoboundary_add hμE, formalCoboundary_smul hμE, map_add (f := _), coeff_smul, hx, hy, map_add (f := _), map_mul]

theorem isLie_comb (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O) (G : PDivGroup p O)
    (d : ℕ) (c : QLog.Chart G d) (E : Type) [CommRing E] [Algebra O E] (hF : IsFrame p E (RingHom.id O))
    (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Fin k → G.dual.Lie)
    (hQL : ∀ i, QL c.μ ⊤ (e i)) (hLie : ∀ j, c.IsLie (e (Sum.inr j)) (lb j)) (b : Fin k → O) :
    c.IsLie (comb (Sum.elim 0 b) e) (∑ j, b j • lb j) := by
  have hμ : ∀ i, constantCoeff (c.μ i) = 0 := c.isLaw.const
  have lin : ∀ (f g : MvPowerSeries (Fin d) E) (l l' : G.dual.Lie) (a : O), c.IsLie f l → c.IsLie g l' →
      QL c.μ ⊤ f → QL c.μ ⊤ g → c.IsLie (f + algebraMap O E a • g) (l + a • l') :=
    fun f g l l' a hf hg => (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hF f g l l' a hf hg).1
  have hQL0 : QL c.μ ⊤ (0 : MvPowerSeries (Fin d) E) := by
    refine ⟨by simp, fun i => ⟨0, trivial, by simp [Katz.lin]⟩, fun α => ⟨0, trivial, ?_⟩⟩
    have := formalCoboundary_smul (fun i => by simp [up, hμ] : ∀ i, constantCoeff (up E c.μ i) = 0) 0
      (0 : MvPowerSeries (Fin d) E)
    rw [zero_smul, zero_smul] at this
    rw [this]; simp
  have h00 : c.IsLie (0 : MvPowerSeries (Fin d) E) 0 := by
    have hd : ∀ n : ℕ, defect c.μ (p ^ n) (0 : MvPowerSeries (Fin d) E) = 0 := by
      intro n
      have ha : HasSubst (up E (nmul c.μ (p ^ n))) :=
        hasSubst_of_constantCoeff_zero fun i => by simp [up, MapNMul.cc_nmul c.μ hμ]
      unfold defect
      rw [← coe_substAlgHom ha, map_zero, smul_zero, sub_zero]
    refine ⟨fun n α => ⟨0, trivial, by rw [hd]; simp⟩, ?_⟩
    intro n w φ s _ hs
    have hs0 : s = 0 := by
      rw [hd] at hs
      ext α
      have := congrArg (coeff α) hs
      rw [coeff_map, map_zero] at this
      apply hF.inj
      rw [this]
      simp
    subst hs0
    simp
  have hsum : ∀ S : Finset (Fin k), QL c.μ ⊤ (∑ i ∈ S, algebraMap O E (b i) • e (Sum.inr i)) ∧
      c.IsLie (∑ i ∈ S, algebraMap O E (b i) • e (Sum.inr i)) (∑ i ∈ S, b i • lb i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      exact ⟨by simpa using hQL0, by simpa using h00⟩
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, add_comm (b a • lb a)]
      exact ⟨QL_comb' O E d c.μ hμ _ _ (b a) ih.1 (hQL _), lin _ _ _ _ (b a) ih.2 (hLie a) ih.1 (hQL _)⟩
  have hf_eq : comb (Sum.elim 0 b) e = ∑ i, algebraMap O E (b i) • e (Sum.inr i) := by
    simp [comb, Fintype.sum_sum_type]
  rw [hf_eq]
  exact (hsum Finset.univ).2

theorem span_le_smul {O : Type} [CommRing O] (A : Type) [CommRing A] [Algebra O A] (I : Ideal O)
    (S : Set O) (hS : ∀ o ∈ S, o ∈ I) (x : A) (hx : x ∈ Ideal.span (algebraMap O A '' S)) :
    x ∈ I • (⊤ : Submodule O A) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨o, ho, rfl⟩ := hy
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem_smul (hS o ho) trivial
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_eq_mul]
    exact Submodule.smul_induction_on (p := fun t => a * t ∈ I • (⊤ : Submodule O A)) hy
      (fun r hr t _ => by rw [mul_smul_comm]; exact Submodule.smul_mem_smul hr trivial)
      (fun u w hu hw => by rw [mul_add]; exact add_mem hu hw)

end GlobalTheory.LevelOneIndep

namespace GlobalTheory.LevelOneIndep

theorem defect_level_one_nonunit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ (w : Fin d ⊕ Fin k → F.B) (a : MvPowerSeries (Fin d) F.B), map (algebraMap F.B F.Q) a = defect μ' p (comb w e) → c.ev 1 (map F.θ a) ∈ Ideal.span (algebraMap O (G.A 1) '' {o | ¬IsUnit o}) → ∀ j, ¬IsUnit (F.θ (w (Sum.inr j))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hmap k e hbasis hadapt w a ha hev j
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hmem : ∀ o : O, o ∈ IsLocalRing.maximalIdeal O ↔ ¬IsUnit o := fun o =>
    IsLocalRing.mem_maximalIdeal o
  have hpm : (p : O) ∈ IsLocalRing.maximalIdeal O := (hmem _).2 Fact.out
  have hE := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  obtain ⟨Θ, hΘ⟩ := GlobalTheory.QLog.frame_fraction_map p F.B O F.Q F.θ F.frame C hE
  have hμ' : ∀ i, constantCoeff (μ' i) = 0 := hlift.const
  have hμ : ∀ i, constantCoeff (c.μ i) = 0 := c.isLaw.const
  have hμC : ∀ i, constantCoeff (up C c.μ i) = 0 := fun i => by simp [up, hμ]
  set e' : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C := fun l => map Θ (e l) with he'
  have hQL : ∀ l, QL c.μ ⊤ (e' l) := fun l => QL_map F.θ Θ hΘ μ' c.μ hμ' hmap _ (hbasis.1 l)
  have hlog : ∀ i, cob1 (up C c.μ) (e' (Sum.inl i)) = 0 := by
    intro i
    ext α
    obtain ⟨b, hb, hbα⟩ := (hadapt i).1 α
    rw [he', ← map_formalGroupLawCoboundaryOne_square F.θ Θ hΘ μ' c.μ hμ' hmap, coeff_map, hbα, hΘ, RingHom.mem_ker.1 hb,
      map_zero, map_zero]
  obtain ⟨lb, hlb⟩ := GlobalTheory.T.quasiLogarithm_tangentVectors_basis_dual_lie p C v O hv G d c C hE k e'
    (GlobalTheory.T.isQuasiLogarithmBasis_reduction_thickening p C v O hv ε hε F G d c μ' hlift hmap k e hbasis Θ hΘ) hlog
  set b : Fin k → O := fun j => F.θ (w (Sum.inr j)) with hb
  set f := comb (Sum.elim 0 b) e' with hf
  set L : G.dual.Lie := ∑ j, b j • lb j with hL
  have hfl : c.IsLie f L := isLie_comb p C v O hv G d c C hE k e' lb hQL hlb b
  have hlogcomb : cob1 (up C c.μ) (comb (Sum.elim (fun i => F.θ (w (Sum.inl i))) 0) e') = 0 := by
    let Φ : MvPowerSeries (Fin d) C →+ MvPowerSeries (Fin d ⊕ Fin d) C :=
      AddMonoidHom.mk' (cob1 (up C c.μ)) (formalCoboundary_add hμC)
    change Φ (comb _ e') = 0
    unfold comb
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    change cob1 (up C c.μ) _ = 0
    rw [formalCoboundary_smul hμC]
    cases l with
    | inl i => rw [hlog, smul_zero]
    | inr j => simp
  have hsplit : map Θ (comb w e) = comb (Sum.elim (fun i => F.θ (w (Sum.inl i))) 0) e' + f := by
    have h1 : map Θ (comb w e) = ∑ l, algebraMap O C (F.θ (w l)) • e' l := by
      unfold comb
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul', hΘ]
    rw [h1, hf]
    unfold comb
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [hb]
  have hs : map (algebraMap O C) (map F.θ a) = defect c.μ (p ^ 1) f := by
    rw [← map_up F.θ Θ hΘ, ha, map_defect F.θ Θ hΘ μ' c.μ hμ' hmap, pow_one, hsplit,
      defect_add _ hμ, defect_log _ hμ _ _ hlogcomb, zero_add]
  have key : ∀ w0 : G.dual.omega, L w0 ∈ IsLocalRing.maximalIdeal O := by
    intro w0
    obtain ⟨φ₀, hφ₀⟩ := AugCot.d_surjective _ (w0.1 1)
    set φ : CartierDual O (G.A 1) := φ₀ - algebraMap O _ (Coalgebra.counit (R := O) φ₀) with hφdef
    have hφd : PDiv.dUnit (R := O) φ = w0.1 1 := by
      rw [hφdef, PDiv.dUnit, map_sub, AugCot.d_algebraMap, sub_zero]; exact hφ₀
    obtain ⟨q, hq⟩ := hfl.2 1 w0 φ (map F.θ a) hφd hs
    have hx := span_le_smul (G.A 1) (IsLocalRing.maximalIdeal O) {o | ¬IsUnit o}
      (fun o ho => (hmem o).2 ho) _ hev
    have hle : IsLocalRing.maximalIdeal O • (⊤ : Submodule O (G.A 1)) ≤
        Submodule.comap φ.ofConv (IsLocalRing.maximalIdeal O) :=
      Submodule.smul_le.2 fun r hr x _ => by
        rw [Submodule.mem_comap, map_smul, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
    have hφm : φ (c.ev 1 (map F.θ a)) ∈ IsLocalRing.maximalIdeal O := hle hx
    have : L w0 = (p : O) ^ 1 * q + φ (c.ev 1 (map F.θ a)) := by rw [← hq]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (by simpa using hpm)) hφm
  obtain ⟨hfin, hproj⟩ := GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual
  have h6 := GlobalTheory.T.dualBasis_coord_mem_maximalIdeal_of_forall_apply O G.dual.omega k lb L key j
  have hrep : lb.repr L j = b j := by
    have : L = lb.equivFun.symm b := by rw [Module.Basis.equivFun_symm_apply]
    rw [← Module.Basis.equivFun_apply, this, LinearEquiv.apply_symm_apply]
  rw [hrep] at h6
  exact (hmem _).1 h6

end GlobalTheory.LevelOneIndep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelOneDefectsIndependentModMaximalStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelOne_defects_independent_mod_maximal : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ (w : Fin d ⊕ Fin k → F.B) (a : MvPowerSeries (Fin d) F.B), map (algebraMap F.B F.Q) a = defect μ' p (comb w e) → c.ev 1 (map F.θ a) ∈ Ideal.span (algebraMap O (G.A 1) '' {o | ¬IsUnit o}) → ∀ j, ¬IsUnit (F.θ (w (Sum.inr j))) := by
  first | exact @GlobalTheory.LevelOneIndep.defect_level_one_nonunit | exact GlobalTheory.LevelOneIndep.defect_level_one_nonunit | (intros; apply GlobalTheory.LevelOneIndep.defect_level_one_nonunit <;> assumption)
end
