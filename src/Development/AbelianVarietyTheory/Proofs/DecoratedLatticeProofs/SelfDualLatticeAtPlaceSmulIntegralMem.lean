module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictionExtendByZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContAutRapidDecBoundedIntegrable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalHeckeOperatorEqSmulOfLocalParameter

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSmulIntegralMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSmulIntegralMem
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.SDStable

variable {D : D7}

theorem hermAt_smul_left (S : HSp D) (a : AE D) (y x : Fin S.rank → AE D) :
    hermAt S (a • y) x = a * hermAt S y x := by
  unfold hermAt
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem mul_mem_intAt {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem smul_mem : ∀ (D : D7) (S : HSp D) (v : Pl D) (Λ : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v Λ →
    ∀ a ∈ intAt D (· = v), ∀ y ∈ Λ, a • y ∈ Λ := by
  intro D S v Λ hΛ a ha y hy
  have hsupp : ∀ i, (a • y) i ∈ idAt D (· = v) := fun i => by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_left _ _ (hΛ.1 y hy i)
  refine (hΛ.2.2 (a • y) hsupp).2 fun x hx => ?_
  rw [hermAt_smul_left]
  exact mul_mem_intAt ha ((hΛ.2.2 y (hΛ.1 y hy)).1 hy x hx)

end GlobalTheory.IwaPlace.SDStable

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSmulIntegralMemStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLatticeAtPlace_smul_integral_mem : ∀ (D : D7) (S : HSp D) (v : Pl D) (Λ : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v Λ → ∀ a ∈ intAt D (· = v), ∀ y ∈ Λ, a • y ∈ Λ := by
  first | exact @GlobalTheory.IwaPlace.SDStable.smul_mem | exact GlobalTheory.IwaPlace.SDStable.smul_mem | (intros; apply GlobalTheory.IwaPlace.SDStable.smul_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqZeroOfOrthogonalAllThetaFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqZeroOfOrthogonalAllThetaFunctions
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ThetaOrthTotal

theorem eq_zero_of_orthogonal_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ q : WO S T → ℂ, Continuous q → (∀ γ w, q (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * q w) → (∀ f, IsThetaFunO ψ S T f → ∫ w in 𝓕, q w * star (f w) ∂μ = 0) → q = 0 := by
  intro D ψ hψ S T μ 𝓕 hμ h𝓕 q hq hquasi horth
  obtain ⟨f₀, hne, h₀⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨hl, hr, halt, hdbl, hcont, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  obtain ⟨hψc, hψn, -, -⟩ := hψ.1
  have hann : ∀ x : WO S T, (∀ γ ∈ ratL T S, ψ (symplOH S T x γ + symplOH S T x γ) = 1) ↔ x ∈ ratL T S := by
    intro x
    simp only [hdbl]
    exact GlobalTheory.T.rationalSymplecticPoints_self_annihilator D ψ hψ S T x
  have hq' : ∀ γ ∈ ratL T S, ∀ w, q (γ + w) = ψ (-(symplOH S T γ w)) * q w := by
    intro γ hγ w
    obtain ⟨γ', rfl⟩ := hγ
    exact hquasi γ' w
  have horth' : ∀ w, ∫ x in 𝓕, heisO ψ S T w f₀ x * star (q x) ∂μ = 0 := by
    intro w
    have h := horth _ ((GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 w f₀ h₀)
    have e : (fun x => heisO ψ S T w f₀ x * star (q x)) = fun x => (starRingEnd ℂ) (q x * star (heisO ψ S T w f₀ x)) := by
      funext x
      simp only [map_mul, Complex.star_def, Complex.conj_conj]
      ring
    rw [e, integral_conj, h, map_zero]
  exact GlobalTheory.HeisTotal.eq_zero_abstract (G := WO S T) (ratL T S) K hK hcov ψ hψc hψn (symplOH S T) hl hr halt hcont hann
    f₀ q h₀.cont hq (GlobalTheory.HeisTotal.quasi_of_mem h₀) hq' hne μ 𝓕 hμ h𝓕 horth'

end GlobalTheory.ThetaOrthTotal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqZeroOfOrthogonalAllThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_orthogonal_all_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ q : WO S T → ℂ, Continuous q → (∀ γ w, q (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * q w) → (∀ f, IsThetaFunO ψ S T f → ∫ w in 𝓕, q w * star (f w) ∂μ = 0) → q = 0 := by
  first | exact @GlobalTheory.ThetaOrthTotal.eq_zero_of_orthogonal_theta | exact GlobalTheory.ThetaOrthTotal.eq_zero_of_orthogonal_theta | (intros; apply GlobalTheory.ThetaOrthTotal.eq_zero_of_orthogonal_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatTensorIndicatorCharacterFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatTensorIndicatorCharacterFacts
noncomputable section

open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix

namespace GlobalTheory.FinPl.SBFacts

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]

theorem charInd_mem (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n) : charInd χ Q ∈ SB (n → k) := by
  have : T2Space k := GlobalTheory.SplitWeil.t2Space k
  have hK : IsCompact (Q.lat : Set (n → k)) := GlobalTheory.FinPl.Comm.isCompact_lat Q.lat
  refine ⟨?_, HasCompactSupport.intro hK fun y hy => ?_⟩
  · refine (IsLocallyConstant.iff_exists_open _).2 fun y => ?_
    by_cases hy : y ∈ Q.lat
    · refine ⟨(fun z => z - y) ⁻¹' (Q.ker : Set (n → k)), (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.isOpen_lat Q.ker).preimage (by fun_prop),
        by simp [Q.ker.zero_mem], fun z hz => ?_⟩
      have hw : Q.HasVal (z - y) 0 := Pair.mem_ker.1 hz
      have hz' : Q.HasVal z (Q.ev y) := by
        simpa using hw.add (Pair.hasVal_ev hy)
      have hzl : z ∈ Q.lat := hz'.mem
      simp only [charInd, vecInd, ite_eq_left hzl, ite_eq_left hy, hz'.ev_eq]
    · refine ⟨(Q.lat : Set (n → k))ᶜ, hK.isClosed.isOpen_compl, hy, fun z hz => ?_⟩
      have hz' : z ∉ Q.lat := hz
      simp only [charInd, vecInd, ite_eq_right hz', ite_eq_right hy, mul_zero]
  · have hy' : y ∉ Q.lat := hy
    simp only [charInd, vecInd, ite_eq_right hy', mul_zero]

end GlobalTheory.FinPl.SBFacts

theorem GlobalTheory.FinPl.sb_facts : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'],
    (∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), Ψ ∈ SB (Matrix n n' k) → a ∈ SB (n → k) →
      GlobalTheory.FinPl.tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) ∧
    (∀ (Λ : Submodule 𝒪[k] (n → k)), Λ.IsFullLattice k → GlobalTheory.FinPl.vecInd Λ ∈ SB (n → k)) ∧
    ∀ (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n), GlobalTheory.FinPl.charInd χ Q ∈ SB (n → k) := by
  intro k _ _ _ _ n n' _ _ _ _
  refine ⟨fun Ψ a hΨ ha => GlobalTheory.FinPl.Comm.tensCol_mem hΨ ha, fun Λ hΛ => ?_,
    fun χ Q => GlobalTheory.FinPl.SBFacts.charInd_mem χ Q⟩
  have := hΛ
  exact GlobalTheory.FinPl.Comm.vecInd_mem Λ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatTensorIndicatorCharacterFactsStatement
open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_tensor_indicator_character_facts : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'], (∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), Ψ ∈ SB (Matrix n n' k) → a ∈ SB (n → k) → GlobalTheory.FinPl.tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) ∧ (∀ (Λ : Submodule 𝒪[k] (n → k)), Λ.IsFullLattice k → GlobalTheory.FinPl.vecInd Λ ∈ SB (n → k)) ∧ ∀ (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n), GlobalTheory.FinPl.charInd χ Q ∈ SB (n → k) := by
  exact @_root_.GlobalTheory.FinPl.sb_facts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OfTensColMem
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.TensSB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type}

theorem of_tensCol_mem {Ψ : Matrix n n' k → ℂ} {a : (n → k) → ℂ}
    (h : tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) (ha : a ≠ 0) : Ψ ∈ SB (Matrix n n' k) := by
  haveI := Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, a y₀ ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact ha (funext h0)
  have hg := Comm.comp_mem_SB h
    (p := fun x₀ : Matrix n n' k => Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y₀ i) j)
    (s := fun x : Matrix n (n' ⊕ Fin 1) k => x.submatrix id Sum.inl) ?_ (by fun_prop) (fun x₀ => rfl)
  · have e : Ψ = (a y₀)⁻¹ • fun x₀ : Matrix n n' k =>
        tensCol Ψ a (Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y₀ i) j) := by
      funext x₀
      show Ψ x₀ = (a y₀)⁻¹ * (Ψ x₀ * a y₀)
      field_simp
    rw [e]
    exact Submodule.smul_mem _ _ hg
  · refine continuous_matrix fun i j => ?_
    rcases j with j | j
    · exact continuous_id.matrix_elem i j
    · exact continuous_const

theorem of_tensRow_mem {Ψ : Matrix n n' k → ℂ} {b : (n' → k) → ℂ}
    (h : tensRow Ψ b ∈ SB (Matrix (n ⊕ Fin 1) n' k)) (hb : b ≠ 0) : Ψ ∈ SB (Matrix n n' k) := by
  haveI := Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  obtain ⟨η₀, hη₀⟩ : ∃ η₀, b η₀ ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hb (funext h0)
  have hg := Comm.comp_mem_SB h
    (p := fun x₀ : Matrix n n' k => Matrix.of fun i j => Sum.elim (fun i => x₀ i j) (fun _ => η₀ j) i)
    (s := fun x : Matrix (n ⊕ Fin 1) n' k => x.submatrix Sum.inl id) ?_ (by fun_prop) (fun x₀ => rfl)
  · have e : Ψ = (b η₀)⁻¹ • fun x₀ : Matrix n n' k =>
        tensRow Ψ b (Matrix.of fun i j => Sum.elim (fun i => x₀ i j) (fun _ => η₀ j) i) := by
      funext x₀
      show Ψ x₀ = (b η₀)⁻¹ * (Ψ x₀ * b η₀)
      field_simp
    rw [e]
    exact Submodule.smul_mem _ _ hg
  · refine continuous_matrix fun i j => ?_
    rcases i with i | i
    · exact continuous_id.matrix_elem i j
    · exact continuous_const

end GlobalTheory.FinPl.TensSB

namespace GlobalTheory.FinPl

theorem tens_SB_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'],
    (∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), Ψ ∈ SB (Matrix n n' k) → a ∈ SB (n → k) → tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) ∧
    (∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k) → a ≠ 0 → Ψ ∈ SB (Matrix n n' k)) ∧
    (∀ (Ψ : Matrix n' n k → ℂ) (b : (n → k) → ℂ), Ψ ∈ SB (Matrix n' n k) → b ∈ SB (n → k) → tensRow Ψ b ∈ SB (Matrix (n' ⊕ Fin 1) n k)) ∧
    (∀ (Ψ : Matrix n' n k → ℂ) (b : (n → k) → ℂ), tensRow Ψ b ∈ SB (Matrix (n' ⊕ Fin 1) n k) → b ≠ 0 → Ψ ∈ SB (Matrix n' n k)) := by
  intro k _ _ _ _ n n' _ _ _ _
  exact ⟨fun Ψ a hΨ ha => Comm.tensCol_mem hΨ ha, fun Ψ a h ha => TensSB.of_tensCol_mem h ha,
    fun Ψ b hΨ hb => Comm.tensRow_mem hΨ hb, fun Ψ b h hb => TensSB.of_tensRow_mem h hb⟩

end GlobalTheory.FinPl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittHyperbolicRankZeroProjMulEmb
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.TargetIsom

open GlobalTheory.Mem.Isom

variable {D : D7}

theorem entries_fix {A : Type} [CommRing A] {m n : ℕ} (c : A) {M : Matrix (Fin n) (Fin n) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (Q : Matrix (Fin n) (Fin m) A) (i j : Fin m) : c * (P * M * Q) i j = (P * M * Q) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l k]
  ring

theorem entries_fix' {A : Type} [CommRing A] {m n k : ℕ} (c : A) {M : Matrix (Fin n) (Fin k) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (i : Fin m) (j : Fin k) : c * (P * M) i j = (P * M) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l j]
  ring

theorem sub_one_conj {A : Type} [CommRing A] {m n : ℕ} {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A} (PQ : P * Q = 1)
    (M : Matrix (Fin n) (Fin n) A) : P * M * Q - 1 = P * (M - 1) * Q := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, PQ]

theorem det_conj_rect {A : Type} [CommRing A] {m n : ℕ} (h : n = m) {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A}
    (QP : Q * P = 1) (M : Matrix (Fin n) (Fin n) A) : (P * M * Q).det = M.det := by
  subst h
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (P.det), mul_assoc, ← Matrix.det_mul, mul_eq_one_comm.1 QP, Matrix.det_one, mul_one]

theorem isThetaFunO_tr {V V' : HSp D} (I : IsoMat V V') (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {f : WO S V → ℂ}
    (hf : IsThetaFunO ψ S V f) : IsThetaFunO ψ S V' (I.trW S f) := by
  have hinf : ∀ w : WO S V', w.map (infPart D) = 0 → ((I.phi S).symm w).map (infPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (infPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  have hfin : ∀ w : WO S V', w.map (finPart D) = 0 → ((I.phi S).symm w).map (finPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (finPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp (I.continuous_phi_symm S), fun k L hL h0 w => ?_⟩
  · obtain ⟨w, rfl⟩ := (I.phi S).surjective w
    have e : ratW V' S γ = I.phi S (ratW V S (I.Q * γ)) := by
      rw [IsoMat.phi_ratW, ← Matrix.mul_assoc, I.PQ, Matrix.one_mul]
    rw [e, ← map_add (f := _), I.symplOH_phi]
    simp only [IsoMat.trW, AddEquiv.symm_apply_apply]
    exact hf.quasi _ _
  · obtain ⟨U, hU, e⟩ := hf.level
    refine ⟨U.map (I.phi S).toAddMonoidHom, ?_, ?_⟩
    · have e : ((U.map (I.phi S).toAddMonoidHom : AddSubgroup (WO S V')) : Set (WO S V')) = (I.phi S).symm ⁻¹' U := by
        ext w
        simp only [AddSubgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe]
        constructor
        · rintro ⟨u, hu, rfl⟩
          simpa using hu
        · intro hw
          exact ⟨_, hw, by simp⟩
      rw [e]
      exact hU.preimage (I.continuous_phi_symm S)
    · rintro _ ⟨u, hu, rfl⟩ h0
      have h1 : u.map (infPart D) = 0 := by
        have := hinf _ h0
        simpa using this
      show heisO ψ S V' (I.phi S u) (I.trW S f) = I.trW S f
      rw [I.heisO_trW, e u hu h1]
  · have := hf.smooth k ((I.phi S).symm.toAddMonoidHom.comp L) ((I.continuous_phi_symm S).comp hL) (fun t => hfin _ (h0 t))
      ((I.phi S).symm w)
    simpa [IsoMat.trW] using this

theorem isWeilDatumO_tr {V V' : HSp D} (I : IsoMat V V') (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : (AE D)ˣ →* Circle}
    {om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)}
    (h : IsWeilDatumO ψ S V χ χ' om) : IsWeilDatumO ψ S V' χ χ' (I.omT S om) := by
  have hT : ∀ f, IsThetaFunO ψ S V' f → IsThetaFunO ψ S V (I.symm.trW S f) := fun f hf => isThetaFunO_tr I.symm S hf
  refine ⟨h.std, h.hecS, h.hecT, h.resS, I.rank_eq ▸ h.resT, fun p f hf => ?_, fun g k w₀ f hf => ?_, fun γ hγ γ' hγ' f hf => ?_,
    fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_, fun e he g k hg hk x y hx hy => ?_⟩
  · exact isThetaFunO_tr I S (h.om_pres _ _ (hT f hf))
  · rw [IsoMat.omT_apply, IsoMat.omT_apply, ← I.symm.heisO_trW S ψ w₀ f, h.om_heis _ _ _ _ (hT f hf), ← I.heisO_trW, I.actO_phi]
    congr 2
    · exact I.kap.apply_symm_apply k
    · exact (I.phi S).apply_symm_apply w₀
  · rw [IsoMat.omT_apply]
    show om (γ, I.kap.symm γ') (I.symm.trW S f) ((I.phi S).symm 0) = f 0
    have := h.om_aut γ hγ (I.kap.symm γ') (I.symm.kap_mem_GQ hγ') _ (hT f hf)
    rw [map_zero, this]
    show f ((I.phi S) 0) = f 0
    rw [map_zero]
  · exact (h.om_cont _ (hT f hf) ((I.phi S).symm w)).comp
      (continuous_fst.prodMk ((I.continuous_kap_symm).comp continuous_snd))
  · obtain ⟨ν, 𝓖, hν, h𝓖, hu⟩ := GlobalTheory.Mem.Isom.haar_fd_phi D V V' I S μ 𝓕 hμ h𝓕
    have e1 := hu fun x => ‖om (p.1, I.kap.symm p.2) (I.symm.trW S f) x‖ₑ ^ 2
    have e2 := hu fun x => ‖I.symm.trW S f x‖ₑ ^ 2
    have e3 : ∀ w, I.symm.trW S f ((I.phi S).symm w) = f w := fun w => congrArg f ((I.phi S).apply_symm_apply w)
    simp only [e3] at e2
    rw [IsoMat.omT_apply]
    exact e1.trans ((h.om_unit ν 𝓖 hν h𝓖 _ _ (hT f hf)).trans e2.symm)
  · have e0 : mt V (I.kap.symm k) - 1 = _ := sub_one_conj I.aQ_aP (mt V' k)
    have hsupp : SuppAt e V (I.kap.symm k) := fun i j => by
      unfold SuppAt at hk
      rw [e0]
      exact entries_fix _ hk _ _ i j
    have e1 : (mt V (I.kap.symm k)).det = (mt V' k).det := det_conj_rect I.rank_eq.symm I.aP_aQ (mt V' k)
    have hdet : IsDetAt e V (I.kap.symm k) y := by
      unfold IsDetAt at hy ⊢
      rw [e1]
      exact hy
    obtain ⟨r, hr, H⟩ := h.om_split e he g (I.kap.symm k) hg hsupp x y hx hdet
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    have hinv : ∀ u : WO S V, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S V f →
        (ℓ ∘ₗ I.trL S) (heisO ψ S V u f) = (ℓ ∘ₗ I.trL S) f := by
      intro u hu f hf
      show ℓ (I.trW S (heisO ψ S V u f)) = ℓ (I.trW S f)
      rw [← I.heisO_trW]
      exact hℓ _ (fun i j => entries_fix' _ hu I.aP i j) _ (isThetaFunO_tr I S hf)
    have := H (ℓ ∘ₗ I.trL S) hinv _ (hT f hf)
    have e1 : (ℓ ∘ₗ I.trL S) (I.symm.trW S f) = ℓ f := congrArg ℓ (I.symm.trW_symm_trW S f)
    rw [e1] at this
    exact this

variable {T T₀ : HSp D} (d : HypDec T T₀ 0)

theorem mul_fin_zero {m n : ℕ} (A : Matrix (Fin m) (Fin 0) D.host.E) (B : Matrix (Fin 0) (Fin n) D.host.E) : A * B = 0 := by
  ext i j; simp [Matrix.mul_apply]

theorem mul_fin_zero' {m n : ℕ} (A : Mx D m 0) (B : Mx D 0 n) : A ⬝ B = 0 := by
  ext i j; simp [Matrix.mul_apply]

theorem wittHyperbolicRankZero_proj_mul_emb : d.q0 * d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.p0_j0)

theorem wittHyperbolicRankZero_emb_mul_proj : d.i₀ * d.q0 = 1 := by
  have h := d.sum_eq_one_rat
  rwa [mul_fin_zero, mul_fin_zero, zero_add, add_zero] at h

def iso : IsoMat T₀ T where
  P := d.i₀
  Q := d.q0
  PQ := wittHyperbolicRankZero_emb_mul_proj d
  QP := wittHyperbolicRankZero_proj_mul_emb d
  gram := d.iso

theorem kap_eq (h : GA D T₀) : (iso d).kap h = d.emb0 h := by
  apply mt_injective T
  rw [IsoMat.mt_kap, IsoMat.conjM_apply, HypDec.unitaryMatrix_wittCoreEmbedding, mul_fin_zero' d.jX, mul_fin_zero' d.jY, zero_add, add_zero]
  rfl

end GlobalTheory.TargetIsom

open GlobalTheory.TargetIsom in
theorem GlobalTheory.TargetIsom.transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T T₀ : HSp D) (d : HypDec T T₀ 0), IsStdChar D ψ (-1) → Function.Bijective (d.inc0 S) ∧ (∀ f : WO S T → ℂ, IsThetaFunO ψ S T₀ (fun w => f (d.inc0 S w)) ↔ IsThetaFunO ψ S T f) ∧ ∀ (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S T₀), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T₀ χS χT om₀ → ∀ g h f, IsThetaFunO ψ S T f → om₀ (g, h) (fun w => f (d.inc0 S w)) = fun w => om (g, d.emb0 h) f (d.inc0 S w) := by
  intro D ψ S T T₀ d hψ
  have hphi : (d.inc0 S : WO S T₀ → WO S T) = (iso d).phi S := funext fun w => rfl
  refine ⟨hphi ▸ ((iso d).phi S).bijective, fun f => ⟨fun hf => ?_, fun hf => ?_⟩, fun χS χT om om₀ hom hom₀ g h f hf => ?_⟩
  · have := isThetaFunO_tr (iso d) S hf
    convert this using 1
    funext w
    show f w = f ((iso d).phi S (((iso d).phi S).symm w))
    rw [AddEquiv.apply_symm_apply]
  · exact isThetaFunO_tr (iso d).symm S hf
  · have hT := isWeilDatumO_tr (iso d).symm S hom
    have hf0 : IsThetaFunO ψ S T₀ (fun w => f (d.inc0 S w)) := isThetaFunO_tr (iso d).symm S hf
    rw [GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ S T₀ χS χT om₀ _ hom₀ hT (g, h) _ hf0]
    funext w
    rw [GlobalTheory.Mem.Isom.IsoMat.omT_apply]
    have e1 : ((iso d).symm.kap.symm h) = d.emb0 h := kap_eq d h
    have e2 : (iso d).symm.symm.trW S (fun w => f (d.inc0 S w)) = f := (iso d).symm.trW_symm_trW S f
    rw [e1, e2]
    rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLevelStepFourierJacobiPeriodLink
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLevelStepFourierJacobiPeriodLink
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.UnfLink

theorem star_psi {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem heisO_at_zero' {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  have h : hO S T 0 w = 0 := by simp [hO]
  simp [heisO, symplOH, symplO, h]

theorem link : ∀ D : D7, LinkLaw D := by
  intro D ψ ρ B J s L' ζ' hz l φ Ξ hφ hΞ
  refine ⟨GlobalTheory.T.besselToFourierJacobi_handedFamily_continuous_automorphic D ψ ρ B J s L' ζ' hz l φ Ξ hφ hΞ, fun G' => ?_⟩
  unfold JacLev.perAll JacLev.per fjAll fjSrcKer
  congr 1; funext h; congr 1; funext n
  have hk := GlobalTheory.T.fourierJacobiKernel_eq_weilRepresentation_apply D ψ J.W J.W₀ B.V₀ B.A B.L ρ J.d B.o B.ζ _ _ s.om₀ s.weil₀ Ξ hΞ
  obtain ⟨hp, hc⟩ := GlobalTheory.T.jacobiActions_match_through_linkMap D ρ ρ B L' ζ' hz l J.W J.W₀ J.d n.1 n.2
  simp only [fjAllFun, fjSrcKerFun, JacLev.ker, jacS, handBF, hk, Pi.smul_apply, smul_eq_mul, heisO_at_zero', hp, hc]
  rw [star_mul', star_star, star_psi s.weil₀.std]
  simp_rw [mul_left_comm (φ _) (ψ _)]
  rw [integral_const_mul]
  ring

end GlobalTheory.UnfLink
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLevelStepFourierJacobiPeriodLinkStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_level_step_fourierJacobi_period_link : ∀ D : D7, LinkLaw D := by
  first | exact @GlobalTheory.UnfLink.link | exact GlobalTheory.UnfLink.link | (intros; apply GlobalTheory.UnfLink.link <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbsConvOfInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.BesInt

theorem absConv_of_invariant : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∀ f : GA D B.V → ℂ, Continuous f →
    (∀ γ ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)), ∀ h, f (γ * h) = f h) →
    ∀ h, AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 fun h₁ n => f (n.1 * embA B.d B.o h₁ * h) := by
  intro D σ B f hf hinv h
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  obtain ⟨hemb, -, hconj, -, hrat⟩ := GlobalTheory.Unf.besSemi D σ B
  obtain ⟨KA, hKA, hcovA⟩ := B.cpt
  obtain ⟨⟨KN, hKN, hcovN⟩, -⟩ :=
    GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B.V σ B.d.e (isIsoSub_e B.d)

  let Φ : NFlag B.V B.d.e × GA D B.A → GA D B.V := fun p => p.1.1 * embA B.d B.o p.2 * h
  have hΦ : Continuous Φ :=
    ((continuous_subtype_val.comp continuous_fst).mul (hemb.comp continuous_snd)).mul continuous_const
  have hΩ : IsCompact (Φ '' (KN ×ˢ KA)) := (hKN.prod hKA).image hΦ
  obtain ⟨C, hC⟩ := hΩ.exists_bound_of_continuousOn hf.continuousOn

  have hbd : ∀ (h₁ : GA D B.A) (n : flagN B.d), ‖f (n.1 * embA B.d B.o h₁ * h)‖ ≤ C := by
    intro h₁ n
    obtain ⟨γ, hγ, hγK⟩ := hcovA h₁
    obtain ⟨δ, hδ, k, hk, hnk⟩ :=
      hcovN ⟨embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹, hconj n.1 n.2 γ⟩
    have heq : embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹ = δ.1 * k.1 := congrArg Subtype.val hnk
    have hγV : embA B.d B.o γ ∈ GQ B.V := by
      have := (hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩
      rwa [one_mul] at this
    have hδQ : (δ.1 : GA D B.V) ∈ GQ B.V := Subgroup.mem_subgroupOf.1 hδ
    have hηQ : (embA B.d B.o γ)⁻¹ * δ.1 ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hγV) hδQ,
        mul_mem (inv_mem (Subgroup.mem_sup_right ⟨γ, rfl⟩)) (Subgroup.mem_sup_left δ.2)⟩
    have e1 : n.1 = (embA B.d B.o γ)⁻¹ * (δ.1 * k.1) * embA B.d B.o γ := by rw [← heq]; group
    have e2 : n.1 * embA B.d B.o h₁ * h =
        ((embA B.d B.o γ)⁻¹ * δ.1) * (k.1 * embA B.d B.o (γ * h₁) * h) := by
      rw [e1, map_mul]; group
    rw [e2, hinv _ hηQ]
    exact hC _ ⟨(k, γ * h₁), ⟨hk, hγK⟩, rfl⟩

  have hfinA : B.vA.μ B.vA.𝓕 < ⊤ := by
    have hcov' : ∀ g : GA D B.A, ∃ γ ∈ GQ B.A, ∃ c ∈ KA, g = γ * c := fun g => by
      obtain ⟨γ, hγ, hc⟩ := hcovA g
      exact ⟨γ⁻¹, inv_mem hγ, γ * g, hc, by rw [inv_mul_cancel_left]⟩
    have h1 := GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain B.A B.vA.μ B.vA.𝓕 KA B.vA.haar B.vA.fund hKA
      hcov' (fun _ => (1 : ℂ)) continuous_const fun _ _ _ => rfl
    simpa using (integrableOn_const_iff (C := (1 : ℂ))).1 h1
  have hfinN : B.vN.ν B.vN.𝓝 < ⊤ := by rw [B.vN.unit.2.2]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2 hfinA.ne
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hfinN.ne
  have hK : Continuous (Function.uncurry fun (h₁ : GA D B.A) (n : flagN B.d) => f (n.1 * embA B.d B.o h₁ * h)) :=
    hf.comp (((continuous_subtype_val.comp continuous_snd).mul (hemb.comp continuous_fst)).mul continuous_const)
  exact Integrable.of_bound hK.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => hbd p.1 p.2)

end GlobalTheory.Unf.BesInt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicGLCircleCharacterTrivialOnDetOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicGLCircleCharacterTrivialOnDetOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory

theorem glChar_transvection {R : Type} [CommRing R] (h2 : IsUnit (2 : R)) {n : ℕ}
    (α : GL (Fin n) R →* Circle) (i j : Fin n) (hij : i ≠ j) (t : R)
    (u : GL (Fin n) R) (hu : u.1 = Matrix.transvection i j t) : α u = 1 := by
  obtain ⟨w, hw⟩ := h2
  let f : Fin n → R := Function.update 1 i 2
  let g : Fin n → R := Function.update 1 i (↑w⁻¹ : R)
  have hfg : ∀ k, f k * g k = 1 := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [f, g, ← hw]
    · simp [f, g, hk]
  have hgf : ∀ k, g k * f k = 1 := fun k => by rw [mul_comm]; exact hfg k
  let d : GL (Fin n) R :=
    ⟨Matrix.diagonal f, Matrix.diagonal g,
      by rw [Matrix.diagonal_mul_diagonal]; simp [hfg],
      by rw [Matrix.diagonal_mul_diagonal]; simp [hgf]⟩
  have hcomm : d * u = u * u * d := by
    apply Units.ext
    have hfi : f i = 2 := by simp [f]
    have hfj : f j = 1 := by simp [f, hij.symm]
    change Matrix.diagonal f * u.1 = u.1 * u.1 * Matrix.diagonal f
    rw [hu, Matrix.transvection_mul_transvection_same _ _ hij]
    ext a b
    simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
      Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply,
      Matrix.diagonal_apply, Matrix.one_apply]
    clear_value f g d
    clear hfg hgf
    split_ifs <;> subst_vars <;> simp_all <;> ring
  have h := congrArg α hcomm
  simp only [map_mul] at h
  have h' : α d * α u = α d * (α u * α u) := by rw [h]; exact mul_comm _ _ |>.trans (by rfl)
  have h'' := mul_left_cancel h'
  exact (mul_eq_left.mp h''.symm)

theorem glChar_eq_one_of_det_eq_one : ∀ (D : D7) (n : ℕ) (α : GL (Fin n) (AE D) →* Circle),
    Continuous α → ∀ a, Matrix.GeneralLinearGroup.det a = 1 → α a = 1 := by
  intro D n α _ a ha
  have h2 : IsUnit (2 : AE D) := by
    have h := (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map (algebraMap D.host.F (AE D))
    rwa [map_ofNat] at h
  have := GlobalTheory.T.special_linear_generated_by_transvections (AE D) (GlobalTheory.T.stableRangeOne_adeles_cmField D) n α.ker
    (fun i j hij t u hu => MonoidHom.mem_ker.mpr (glChar_transvection h2 α i j hij t u hu)) a ha
  exact MonoidHom.mem_ker.mp this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicGLCircleCharacterTrivialOnDetOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_GL_circle_character_trivial_on_det_one : ∀ (D : D7) (n : ℕ) (α : GL (Fin n) (AE D) →* Circle), Continuous α → ∀ a, Matrix.GeneralLinearGroup.det a = 1 → α a = 1 := by
  first | exact @GlobalTheory.glChar_eq_one_of_det_eq_one | exact GlobalTheory.glChar_eq_one_of_det_eq_one | (intros; apply GlobalTheory.glChar_eq_one_of_det_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingDualIndicatorAddNonzeroCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingDualIndicatorAddNonzeroCosets
noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd Lifts InDual)

namespace GlobalTheory.FinPl.Comm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n]


open Classical in
theorem integral_vecInd_eq_zero [MeasurableSpace k] [BorelSpace k] (χ : AddChar k Circle) (e : k)
    (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) (η : n → k) {y₀ : n → k}
    (hy₀ : y₀ ∈ L) (hne : χ (e * (η ⬝ᵥ y₀)) ≠ 1) :
    ∫ y, vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ = 0 := by
  have h := integral_add_right_eq_self (μ := μ) (fun y => vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ)) y₀
  have e2 : ∀ y, vecInd L (y + y₀) * (χ (e * (η ⬝ᵥ (y + y₀))) : ℂ) =
      (χ (e * (η ⬝ᵥ y₀)) : ℂ) * (vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ)) := fun y => by
    rw [dotProduct_add, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul, vecInd, vecInd,
      if_congr (L.add_mem_iff_left hy₀) rfl rfl]
    ring
  simp only [e2] at h
  rw [integral_const_mul] at h
  by_contra h0
  exact hne (Circle.ext (by simpa using (mul_eq_right₀ h0).1 h))

theorem exists_lifts_value (L : Submodule 𝒪[k] (n → k)) {f : Module.Dual 𝓀[k] (Red L)} (hf : f ≠ 0)
    {F : n → k} (hF : Lifts L F f) (b : 𝓀[k]) :
    ∃ y₀ ∈ L, ∃ s : 𝒪[k], (s : k) = F ⬝ᵥ y₀ ∧ residue 𝒪[k] s = b := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext h)
  obtain ⟨y, rfl⟩ := Red.mk_surjective L x
  obtain ⟨t, ht⟩ := residue_surjective (R := 𝒪[k]) (b * (f (Red.mk L y))⁻¹)
  obtain ⟨s, hs, hs'⟩ := hF (t • y)
  refine ⟨_, (t • y).2, s, hs, ?_⟩
  rw [hs', map_smul, ← Red.residue_smul, map_smul, ht, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one]

theorem integral_vecInd_coset [MeasurableSpace k] [BorelSpace k] (q : Unif k) (χ : AddChar k Circle)
    (hχ : HasConductor χ 1) (e : k) (he : e = 1 ∨ e = -1) (μ : Measure (n → k)) [μ.IsAddHaarMeasure]
    (L : Submodule 𝒪[k] (n → k)) {f : Module.Dual 𝓀[k] (Red L)} (hf : f ≠ 0) {F η : n → k}
    (hF : Lifts L F f) (hη : InDual L (η - q.inv • F)) :
    ∫ y, vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, resChar χ hχ q a ≠ 1 := by
    by_contra h
    push Not at h
    exact resChar_ne_one hχ q (by ext a; rw [h a, AddChar.one_apply])
  have hee : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  have heo : e ∈ 𝒪[k] := by
    rcases he with rfl | rfl
    · exact one_mem _
    · exact neg_mem (one_mem _)
  let ε : 𝒪[k] := ⟨e, heo⟩
  have hε : residue 𝒪[k] ε * residue 𝒪[k] ε = 1 := by
    rw [← map_mul, show ε * ε = 1 from Subtype.ext hee, map_one]
  obtain ⟨y₀, hy₀, s, hs, hs'⟩ := exists_lifts_value L hf hF (residue 𝒪[k] ε * a)
  refine integral_vecInd_eq_zero χ e μ L η hy₀ fun h => ha ?_
  have hl : e * ((η - q.inv • F) ⬝ᵥ y₀) ∈ 𝒪[k] := mul_mem heo (hη y₀ hy₀)
  have hsplit : e * (η ⬝ᵥ y₀) = q.inv * ((ε * s : 𝒪[k]) : k) + e * ((η - q.inv • F) ⬝ᵥ y₀) := by
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, Subring.coe_mul, hs]
    change _ = _ * (e * _) + _
    ring
  rw [hsplit, AddChar.map_add_eq_mul, apply_int_eq_one hχ ⟨_, hl⟩, mul_one] at h
  rw [show a = residue 𝒪[k] (ε * s) by rw [map_mul, hs', ← mul_assoc, hε, one_mul], resChar_residue, h]
  rfl

end GlobalTheory.FinPl.Comm

namespace GlobalTheory.FinPl.Comm

theorem fpair_vecInd_dualInd_add_cosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n]
    (q : Unif k) (χ : AddChar k Circle), HasConductor χ 1 → ∀ (e : k), (e = 1 ∨ e = -1) →
    ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k],
    fpair χ e μ (vecInd L) (dualInd L + ∑ Q ∈ withLat L, cosetInd q Q.lat Q.red) =
      fpair χ e μ (vecInd L) (dualInd L) := by
  intro k _ _ _ _ _ _ n _ _ q χ hχ e he μ _ L _
  unfold fpair
  congr 1
  funext η
  rw [Pi.add_apply, mul_add, Finset.sum_apply, Finset.mul_sum, add_eq_left]
  refine Finset.sum_eq_zero fun Q hQ => ?_
  have hL : Q.lat = L := mem_withLat.1 hQ
  classical
  unfold cosetInd
  split_ifs with h
  · obtain ⟨F, hF, hD⟩ := h
    have h0 := integral_vecInd_coset q χ hχ e he μ Q.lat Q.red_ne hF hD
    rw [hL] at h0
    rw [h0, zero_mul]
  · rw [mul_zero]

end GlobalTheory.FinPl.Comm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingDualIndicatorAddNonzeroCosetsStatement
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierPairing_dualIndicator_add_nonzeroCosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle), HasConductor χ 1 → ∀ (e : k), (e = 1 ∨ e = -1) → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k], fpair χ e μ (vecInd L) (dualInd L + ∑ Q ∈ withLat L, cosetInd q Q.lat Q.red) = fpair χ e μ (vecInd L) (dualInd L) := by
  first | exact @GlobalTheory.FinPl.Comm.fpair_vecInd_dualInd_add_cosets | exact GlobalTheory.FinPl.Comm.fpair_vecInd_dualInd_add_cosets | (intros; apply GlobalTheory.FinPl.Comm.fpair_vecInd_dualInd_add_cosets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorDualLatticeIndica
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorDualLatticeIndica
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)

noncomputable section

namespace GlobalTheory.FinPl.Comm

theorem fpair_charInd_dualInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n]
    (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (e : k), (e = 1 ∨ e = -1) →
    ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (Q : Pair k n),
      fpair χ e μ (charInd (resChar χ hχ q) Q) (dualInd Q.lat) = 0 := by
  intro k _ _ _ _ _ _ n _ _ q χ hχ e he μ _ Q
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI := secondCountable k
  set r := resChar χ hχ q with hr
  obtain ⟨a, ha⟩ : ∃ a, r a ≠ 1 := by
    by_contra h
    push_neg at h
    exact resChar_ne_one hχ q (by ext x; simpa using h x)
  obtain ⟨e₁, he₁⟩ := Q.exists_hasVal_one
  obtain ⟨s, hs⟩ := residue_surjective (R := 𝒪[k]) (-a)
  have hy₀ : Q.HasVal (s • e₁) (-a) := by simpa [hs] using he₁.smul s
  have hI : ∫ y, charInd r Q y ∂μ = 0 := by
    have h1 := integral_add_right_eq_self (μ := μ) (charInd r Q) (s • e₁)
    have h2 : ∀ y, charInd r Q (y + s • e₁) = r a * charInd r Q y := fun y => by
      by_cases hy : y ∈ Q.lat
      · have hyy : y + s • e₁ ∈ Q.lat := add_mem hy hy₀.mem
        rw [charInd, charInd, vecInd, vecInd, if_pos hy, if_pos hyy, ((Pair.hasVal_ev hy).add hy₀).ev_eq,
          neg_add, neg_neg, AddChar.map_add_eq_mul]
        ring
      · have hyy : y + s • e₁ ∉ Q.lat := fun h => hy (by simpa using sub_mem h hy₀.mem)
        rw [charInd, charInd, vecInd, vecInd, if_neg hy, if_neg hyy]
        simp
    simp only [h2] at h1
    rw [integral_const_mul] at h1
    by_contra h0
    exact ha ((mul_eq_right₀ h0).1 h1)
  unfold fpair
  have hF : ∀ η, (∫ y, charInd r Q y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ) * dualInd Q.lat η = 0 := fun η => by
    by_cases hη : GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.InDual Q.lat η
    · rw [dualInd, if_pos hη, mul_one]
      have : (fun y => charInd r Q y * (χ (e * (η ⬝ᵥ y)) : ℂ)) = fun y => charInd r Q y := by
        funext y
        by_cases hy : y ∈ Q.lat
        · have hm : e * (η ⬝ᵥ y) ∈ 𝒪[k] := by
            rcases he with rfl | rfl
            · simpa using hη y hy
            · simpa using hη y hy
          rw [show χ (e * (η ⬝ᵥ y)) = 1 from apply_int_eq_one hχ ⟨_, hm⟩]
          simp
        · rw [charInd, vecInd, if_neg hy]
          simp
      rw [this, hI]
    · rw [dualInd, if_neg hη, mul_zero]
  simp only [hF, integral_zero]

end GlobalTheory.FinPl.Comm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorDualLatticeIndicaStatement
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierPairing_pairCharIndicator_dualLatticeIndicator_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (e : k), (e = 1 ∨ e = -1) → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (Q : Pair k n), fpair χ e μ (charInd (resChar χ hχ q) Q) (dualInd Q.lat) = 0 := by
  first | exact @GlobalTheory.FinPl.Comm.fpair_charInd_dualInd | exact GlobalTheory.FinPl.Comm.fpair_charInd_dualInd | (intros; apply GlobalTheory.FinPl.Comm.fpair_charInd_dualInd <;> assumption)
end
end
