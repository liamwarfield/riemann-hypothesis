module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CapelliLowestGelfandConj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageSchwartzProjectionMemAdelicSchwart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaPartialFourierIntegralMemAdelicSchwartz

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

noncomputable section
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocChar

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem ι_one : p.ι 1 = p.e := by
  have h := p.ι_π 1
  rwa [map_one, mul_one] at h

theorem e_mul_ι (x : k) : p.e * p.ι x = p.ι x := by
  have h := p.ι_π (p.ι x)
  rw [p.π_ι] at h
  exact h.symm

theorem ι_mul (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  have h := p.ι_π (p.ι x * p.ι y)
  rw [map_mul, p.π_ι, p.π_ι] at h
  rw [h, ← mul_assoc, e_mul_ι]

theorem xi_ne : p.xi ≠ 0 :=
  (_root_.map_ne_zero (p.π.comp (incA D))).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)

theorem mul_aux (x y : k) : (p.ι x + (1 - p.e)) * (p.ι y + (1 - p.e)) = p.ι (x * y) + (1 - p.e) := by
  have h1 := e_mul_ι p x
  have h2 := e_mul_ι p y
  have h3 : p.e * p.e = p.e := p.split.1
  rw [ι_mul]
  linear_combination (-1 : AE D) * h1 + (-1 : AE D) * h2 + h3

def unitsHom : kˣ →* (AE D)ˣ where
  toFun x := ⟨p.ι x + (1 - p.e), p.ι ↑x⁻¹ + (1 - p.e),
    by rw [mul_aux, Units.mul_inv, ι_one, add_sub_cancel],
    by rw [mul_aux, Units.inv_mul, ι_one, add_sub_cancel]⟩
  map_one' := by
    ext
    simp only [Units.val_one, ι_one, Units.val_mk, add_sub_cancel]
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk]
    rw [mul_aux]

def wchar (ψ : AddChar (AF D.host.F) ℂ) (h : ∀ x, ‖ψ x‖ = 1) : AddChar k Circle where
  toFun x := (⟨psiE ψ (incA D D.host.xi0 * p.ι x), mem_sphere_zero_iff_norm.2 (h _)⟩ : Submonoid.unitSphere ℂ)
  map_zero_eq_one' := by
    apply Circle.ext
    show psiE ψ (incA D D.host.xi0 * p.ι 0) = 1
    simp [psiE]
  map_add_eq_mul' x y := by
    apply Circle.ext
    show psiE ψ (incA D D.host.xi0 * p.ι (x + y)) = psiE ψ (incA D D.host.xi0 * p.ι x) * psiE ψ (incA D D.host.xi0 * p.ι y)
    simp only [psiE, map_add (f := _), mul_add, AddChar.map_add_eq_mul]

end GlobalTheory.LocChar

namespace GlobalTheory.LocChar

theorem weil_char_split : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∃ ψk : AddChar k Circle, p.IsChar ψ ψk) ∧ (∀ ψk : AddChar k Circle, p.IsChar ψ ψk → Continuous ψk ∧ ψk ≠ 1) ∧ p.xi ≠ 0 ∧ (∀ x y, p.ι (x * y) = p.ι x * p.ι y) ∧ ∀ χ : (AE D)ˣ →* Circle, ∃ μ : kˣ →* ℂˣ, p.IsComp χ μ := by
  intro D k _ _ _ _ p ψ hψ
  refine ⟨⟨wchar p ψ hψ.1.2.1, fun x => rfl⟩, fun ψk hk => ⟨?_, ?_⟩, xi_ne p, ι_mul p, fun χ =>
    ⟨(Circle.toUnits.comp χ).comp (unitsHom p), fun x a ha => ?_⟩⟩
  · have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
    have hT : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
      IsModuleTopology.continuous_of_linearMap _
    have hc : Continuous fun x => ((ψk x : Circle) : ℂ) := by
      rw [funext hk]
      exact hψ.1.1.comp (hT.comp (continuous_const.mul p.cont_ι))
    exact continuous_induced_rng.2 hc
  · intro h1
    obtain ⟨v, he⟩ := (GlobalTheory.IdemModTwo.isSplitIdem_iff p.e).1 p.split
    obtain ⟨y, hy⟩ := GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ v
    have hta := GlobalTheory.SplitAnnihilator.trace_split he y 1
    rw [mul_one] at hta
    have hea : p.e * (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v y) * p.e * (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v 1) * p.e)) =
        GlobalTheory.IdemModTwo.fj D (singleV D.host.F v y) * p.e * (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v 1) * p.e) := by
      linear_combination (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v y) * GlobalTheory.IdemModTwo.fj D (singleV D.host.F v 1) * p.e) * he.1
    generalize GlobalTheory.IdemModTwo.fj D (singleV D.host.F v y) * p.e * (GlobalTheory.IdemModTwo.fj D (singleV D.host.F v 1) * p.e) = a at hea hta
    have hu0 : IsUnit (incA D D.host.xi0) := (isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map (incA D)
    obtain ⟨u, hu⟩ := hu0
    have hx : incA D D.host.xi0 * p.ι (p.π (↑u⁻¹ * a)) = a := by
      rw [p.ι_π, ← hu]
      calc (u : AE D) * (p.e * (↑u⁻¹ * a)) = ((u : AE D) * ↑u⁻¹) * (p.e * a) := by ring
        _ = a := by rw [Units.mul_inv, one_mul, hea]
    have h2 := hk (p.π (↑u⁻¹ * a))
    rw [h1, AddChar.one_apply, Circle.coe_one, hx] at h2
    exact hy (by rw [psiV, ← hta]; exact h2.symm)
  · have : unitsHom p x = a := Units.ext ha.symm
    simp only [MonoidHom.comp_apply, this]
    rfl

end GlobalTheory.LocChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontriviaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∃ ψk : AddChar k Circle, p.IsChar ψ ψk) ∧ (∀ ψk : AddChar k Circle, p.IsChar ψ ψk → Continuous ψk ∧ ψk ≠ 1) ∧ p.xi ≠ 0 ∧ (∀ x y, p.ι (x * y) = p.ι x * p.ι y) ∧ ∀ χ : (AE D)ˣ →* Circle, ∃ μ : kˣ →* ℂˣ, p.IsComp χ μ := by
  first | exact @GlobalTheory.LocChar.weil_char_split | exact GlobalTheory.LocChar.weil_char_split | (intros; apply GlobalTheory.LocChar.weil_char_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocSympl

variable {D : D7}

theorem conj_conj (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_ι (p : Place D k) (x : k) : p.e * p.ι x = p.ι x := by
  have h := p.ι_π (p.ι x)
  rw [p.π_ι] at h
  exact h.symm

theorem conj_ι_mul_ι (p : Place D k) (u v : k) : cA D (p.ι u) * p.ι v = 0 := by
  calc cA D (p.ι u) * p.ι v = cA D (p.e * p.ι u) * (p.e * p.ι v) := by rw [e_mul_ι, e_mul_ι]
    _ = (p.e * cA D p.e) * (cA D (p.ι u) * p.ι v) := by rw [map_mul]; ring
    _ = 0 := by rw [p.split.2.1, zero_mul]

end GlobalTheory.LocSympl

namespace GlobalTheory.LocSympl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem up_half (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x : Matrix Y Y' k) :
    IsHalf p.e (p.up FS FT x) := fun i j => e_mul_ι p _

theorem down_up (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x : Matrix Y Y' k) :
    p.down FS FT (p.up FS FT x) = x := by
  have hm : ((FT.β * x * FS.γ).map p.ι).map p.π = FT.β * x * FS.γ := by
    ext i j; simp [p.π_ι]
  unfold Place.down Place.up
  rw [hm, show FT.γ * (FT.β * x * FS.γ) * FS.β = (FT.γ * FT.β) * x * (FS.γ * FS.β) by simp only [Matrix.mul_assoc],
    FT.γβ, FS.γβ, Matrix.one_mul, Matrix.mul_one]

theorem up_down (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (z : WO S T)
    (hz : IsHalf p.e z) : p.up FS FT (p.down FS FT z) = z := by
  unfold Place.down Place.up
  rw [show FT.β * (FT.γ * (z : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * FS.β) * FS.γ
      = (FT.β * FT.γ) * (z : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * (FS.β * FS.γ) by
      simp only [Matrix.mul_assoc], FT.βγ, FS.βγ, Matrix.one_mul, Matrix.mul_one]
  ext i j
  simp only [Matrix.map_apply]
  rw [p.ι_π]
  exact hz i j

theorem hO_up_up (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x y : Matrix Y Y' k) :
    hO S T (p.up FS FT x) (p.up FS FT y) = 0 := by
  unfold hO
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  show incA D _ * cA D (p.ι _) * incA D _ * p.ι _ = 0
  rw [show ∀ A B C E' : AE D, A * C * B * E' = A * B * (C * E') from fun _ _ _ _ => by ring, conj_ι_mul_ι, mul_zero]

theorem e_mul_hO_up (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (t : Matrix Y Y' k)
    (y : WO S T) : p.e * hO S T (p.up FS FT t) y = hO S T (p.up FS FT t) y := by
  have key : ∀ (A B C : AE D) (u : k), p.e * (A * B * C * p.ι u) = A * B * C * p.ι u := fun A B C u => by
    calc p.e * (A * B * C * p.ι u) = A * B * C * (p.e * p.ι u) := by ring
      _ = _ := by rw [e_mul_ι]
  unfold hO
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  exact key _ _ _ _

end GlobalTheory.LocSympl

namespace GlobalTheory.LocSympl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem psi_sympl_up (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle) (hχ : p.IsChar ψ ψk) (t : Matrix Y Y' k) (y : WO S T) :
    ψ (symplO S T (p.up FS FT t) y) = ψk (p.π (hO S T (p.up FS FT t) y)) := by
  rw [hχ, p.ι_π, e_mul_hO_up]
  rfl

theorem sum_four_eq_trace_mul {m n : Type} [Fintype m] [Fintype n] (A : Matrix m m k) (N : Matrix m n k) (B : Matrix n n k)
    (X : Matrix n m k) : ∑ a, ∑ b, ∑ c, ∑ d, A a b * N b c * B c d * X d a = Matrix.trace (A * N * B * X) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun d _ => Finset.sum_comm))

theorem pi_hO_up (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (t : Matrix Y Y' k)
    (N : Matrix (Fin S.rank) (Fin T.rank) k) :
    p.π (hO S T (p.up FS FT t) (N.transpose.map fun a => cA D (p.ι a))) =
      Matrix.trace ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * (FT.β * t * FS.γ)) := by
  unfold hO
  rw [← sum_four_eq_trace_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul]
  have hterm : ∀ a b c d, p.π (incA D (S.gram⁻¹ a b)) * p.π (cA D ((N.transpose.map fun a => cA D (p.ι a)) c b)) *
      p.π (incA D (T.gram c d)) * p.π (p.up FS FT t d a) =
      (S.gram⁻¹).map (p.π.comp (incA D)) a b * N b c * T.gram.map (p.π.comp (incA D)) c d * (FT.β * t * FS.γ) d a := by
    intro a b c d
    simp only [Matrix.map_apply, Matrix.transpose_apply, conj_conj, p.π_ι, Place.up, RingHom.comp_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => hterm a b c d

theorem exists_pairing (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (b : Matrix Y Y' k) :
    ∃ y : WO S T, IsHalf (cA D p.e) y ∧ ∀ t, p.π (hO S T (p.up FS FT t) y) = ∑ r, ∑ q, b r q * t r q := by
  set f := p.π.comp (incA D)
  set N : Matrix (Fin S.rank) (Fin T.rank) k := S.gram.map f * FS.β * b.transpose * FT.γ * (T.gram⁻¹).map f
  refine ⟨N.transpose.map fun a => cA D (p.ι a), fun i j => ?_, fun t => ?_⟩
  · show cA D p.e * cA D (p.ι _) = cA D (p.ι _)
    rw [← map_mul, e_mul_ι]
  · rw [pi_hO_up]
    have hA : (S.gram⁻¹).map f * S.gram.map f = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S), Matrix.map_one _ (map_zero f) (map_one f)]
    have hB : (T.gram⁻¹).map f * T.gram.map f = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit T), Matrix.map_one _ (map_zero f) (map_one f)]
    have hANB : (S.gram⁻¹).map f * N * T.gram.map f = FS.β * b.transpose * FT.γ := by
      simp only [N, Matrix.mul_assoc]
      rw [hB, Matrix.mul_one, ← Matrix.mul_assoc ((S.gram⁻¹).map f), hA, Matrix.one_mul]
    rw [hANB]
    rw [show FS.β * b.transpose * FT.γ * (FT.β * t * FS.γ) = FS.β * (b.transpose * (FT.γ * FT.β) * t * FS.γ) by
      simp only [Matrix.mul_assoc], FT.γβ, Matrix.mul_one, Matrix.trace_mul_comm, Matrix.mul_assoc, FS.γβ, Matrix.mul_one]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_comm

end GlobalTheory.LocSympl

namespace GlobalTheory.LocSympl

theorem halves_at_split : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → (∀ x, IsHalf p.e (p.up FS FT x) ∧ p.down FS FT (p.up FS FT x) = x) ∧ (∀ z : WO S T, IsHalf p.e z → p.up FS FT (p.down FS FT z) = z) ∧ (∀ x y, symplO S T (p.up FS FT x) (p.up FS FT y) = 0) ∧ (∀ t (y : WO S T), IsHalf (cA D p.e) y → ψ (symplO S T (p.up FS FT t) y) = ψk (p.π (hO S T (p.up FS FT t) y))) ∧ ∀ b : Matrix Y Y' k, ∃ y : WO S T, IsHalf (cA D p.e) y ∧ ∀ t, p.π (hO S T (p.up FS FT t) y) = ∑ r, ∑ q, b r q * t r q := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ ψk hχ
  exact ⟨fun x => ⟨up_half p FS FT x, down_up p FS FT x⟩, fun z hz => up_down p FS FT z hz,
    fun x y => by unfold symplO; rw [hO_up_up, mul_zero, map_zero],
    fun t y _ => psi_sympl_up p FS FT ψ ψk hχ t y, fun b => exists_pairing p FS FT b⟩

end GlobalTheory.LocSympl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverseStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_frame_half_inverse : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → (∀ x, IsHalf p.e (p.up FS FT x) ∧ p.down FS FT (p.up FS FT x) = x) ∧ (∀ z : WO S T, IsHalf p.e z → p.up FS FT (p.down FS FT z) = z) ∧ (∀ x y, symplO S T (p.up FS FT x) (p.up FS FT y) = 0) ∧ (∀ t (y : WO S T), IsHalf (cA D p.e) y → ψ (symplO S T (p.up FS FT t) y) = ψk (p.π (hO S T (p.up FS FT t) y))) ∧ ∀ b : Matrix Y Y' k, ∃ y : WO S T, IsHalf (cA D p.e) y ∧ ∀ t, p.π (hO S T (p.up FS FT t) y) = ∑ r, ∑ q, b r q * t r q := by
  first | exact @GlobalTheory.LocSympl.halves_at_split | exact GlobalTheory.LocSympl.halves_at_split | (intros; apply GlobalTheory.LocSympl.halves_at_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsKFinOfMemKfin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.Core.Mi.StepSpans

theorem isKFin_of_mem_kfin {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) {x : M.H τ}
    (hx : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) : IsKFin (M.ε τ) (M.σ τ) x := by
  induction hx using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ v hv => by
      rw [(Submodule.mem_bot _).1 hv, map_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨S₁, h1, h2, h3⟩ := hx
    obtain ⟨S₂, k1, k2, k3⟩ := hy
    refine ⟨S₁ ⊔ S₂, inferInstance, Submodule.add_mem_sup h2 k2, fun g hg v hv => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h3 g hg a ha) (k3 g hg b hb)
  | smul c x _ hx =>
    obtain ⟨S₁, h1, h2, h3⟩ := hx
    exact ⟨S₁, h1, S₁.smul_mem c h2, h3⟩

end GlobalTheory.Core.Mi.StepSpans
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondOnCommonRangeOfSecond
noncomputable section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelWeilLitCompare

open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model
open GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

variable {D : D7} {n : ℕ}

theorem summable_rat {θ : InfFam D} (hθ : IsInfFam θ) {m : ℕ} (φ : schwartzA θ m n) :
    Summable fun ξ : Matrix (Fin m) (Fin n) D.host.E => ‖φ.1 (ξ.map (incA D))‖ := by
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ m n
  obtain ⟨-, K, hK, hC⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ m n φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n φ.1 φ.2)
  obtain ⟨C, hC⟩ := hC N
  obtain ⟨b, hb, hb'⟩ := hN K {0} hK isCompact_singleton
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => (hC _).trans ?_) (hb.mul_left |C|)
  have := hb' 0 rfl ξ
  rw [zero_add] at this
  exact mul_le_mul (le_abs_self C) this (GlobalTheory.Unf.maj_nonneg _ _ _ _) (abs_nonneg C)

theorem gramQ_adj {m : ℕ} {T : Matrix (Fin m) (Fin m) D.host.E} (hT : IsHermND D.sp.cm.sig T) (x y : Mx D m n) :
    adj (GramMatrixBlocks.gramQ T x y) = GramMatrixBlocks.gramQ T y x := by
  have h : adj (rat T : Mx D m m) = rat T := by
    ext i j
    exact (GlobalTheory.DualPairCheck.cA_incA _).trans (congrArg (incA D) (hT.1 i j))
  change adj ((adj x * (rat T : Mx D m m)) * y) = (adj y * (rat T : Mx D m m)) * x
  rw [adj_mul, adj_mul, adj_adj, h, Matrix.mul_assoc]

theorem selfDual_of_covolOne {m : ℕ} {T : Matrix (Fin m) (Fin m) D.host.E} (hT : IsHermND D.sp.cm.sig T)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (hμ : IsCovolOne (ratMx D m n) μ 𝓕) : SelfDual μ (GramMatrixBlocks.pairing (n := n) T ψ) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rationalAdelicMatrices_self_annihilator D m n T hT ψ hψ
  have hs : ∀ x y : Mx D m n, GramMatrixBlocks.pairing T ψ x y = GramMatrixBlocks.pairing T ψ y x := fun x y => by
    unfold GramMatrixBlocks.pairing GramMatrixBlocks.trA
    rw [← gramQ_adj hT x y, ← GlobalTheory.DualPairCheck.trace_cA (Matrix.trace (GramMatrixBlocks.gramQ T x y))]
    congr 2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, map_sum]
    rfl
  refine GlobalTheory.T.selfDual_of_fundamentalDomain_volume_eq_one _ (ratMx D m n) K hK hKc _ (fun y => ?_) hs (fun x x' y => ?_) (fun x y => hψ.2.1 _) h1 h2 μ 𝓕
    hμ.1 hμ.2.1 hμ.2.2
  · simp only [hs _ y]
    haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    have ht : Continuous (GramMatrixBlocks.trA (D := D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
    exact hψ.1.comp (ht.comp (continuous_const.matrix_mul continuous_id).matrix_trace)
  · simp only [hs _ y]
    unfold GramMatrixBlocks.pairing GramMatrixBlocks.trA GramMatrixBlocks.gramQ GramMatrixBlocks.mmul
    rw [Matrix.mul_add, Matrix.trace_add, map_add (f := _), AddChar.map_add_eq_mul]

theorem hE_equivFun (V : HSp D) (x y : V.V) :
    hE D.sp.cm.sig V.gram (V.frame.equivFun x) (V.frame.equivFun y) = V.hT x y := by
  conv_rhs => rw [← V.frame.sum_equivFun x, ← V.frame.sum_equivFun y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, HSpace.gram, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul,
    LinearMap.smul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  change star _ * _ * _ = _ * (star _ * _)
  ring

theorem wittIdx_eq (V : HSp D) : GramMatrixBlocks.wittIdx V.gram = Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  unfold GramMatrixBlocks.wittIdx Formalism.MainNotions.SchurIrreducible.wittIdx
  refine congrArg sSup (Set.ext fun r => ⟨?_, ?_⟩)
  · rintro ⟨W, hW, hr⟩
    refine ⟨W.map V.frame.equivFun.symm.toLinearMap, (LinearEquiv.finrank_map_eq V.frame.equivFun.symm W).trans hr, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    refine (hE_equivFun V _ _).symm.trans ?_
    rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hW x hx y hy
  · rintro ⟨W, hr, hW⟩
    refine ⟨W.map V.frame.equivFun.toLinearMap, ?_, (LinearEquiv.finrank_map_eq V.frame.equivFun W).trans hr⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (hE_equivFun V x y).trans (hW x hx y hy)

variable {V : HSp D} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}

theorem gramQ_eq (x y : Mx D V.rank n) : GramMatrixBlocks.gramQ V.gram x y = StdUnn.inner V x y := Matrix.mul_assoc _ _ _

theorem isWeilSch_unique {μ : Measure (Mx D V.rank n)} {ω ω' : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (h : IsWeilSch ψ χ θ V μ ω) (h' : IsWeilSch ψ χ θ V μ ω') : ω = ω' := by
  have := GlobalTheory.T.unitaryUnn_subgroup_eq_top_of_leviUnipotentWeyl D n (ω.toHomUnits.eqLocus ω'.toHomUnits)
    (fun g a hg => Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun x =>
      (h.levi g a hg Φ x).trans (h'.levi g a hg Φ x).symm)))
    (fun g b hg => Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun x =>
      (h.unip g b hg Φ x).trans (h'.unip g b hg Φ x).symm)))
    (fun g hg => Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun x =>
      (h.weyl g hg Φ x).trans (h'.weyl g hg Φ x).symm)))
  refine MonoidHom.ext fun g => ?_
  have hg : g ∈ ω.toHomUnits.eqLocus ω'.toHomUnits := this ▸ Subgroup.mem_top g
  exact congrArg Units.val hg

theorem leftInv_theta (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (Φ : schwartzA θ V.rank n) (g : G D n) :
    LeftInv (GQ V) (theta ω Φ g) := by
  intro γ hγ h
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin V.rank) D.host.E, mt V γ⁻¹ = rat u.1 := by
    obtain ⟨u, -, hu⟩ := (GQ V).inv_mem hγ
    exact ⟨u, (congrArg Units.val hu).symm⟩
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => u.1 * ξ, fun ξ => (u⁻¹).1 * ξ, fun ξ => by simp [← Matrix.mul_assoc], fun ξ => by simp [← Matrix.mul_assoc]⟩
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq _)
  have : mt V (γ * h)⁻¹ = mt V h⁻¹ * mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  rw [this, hu, Matrix.mul_assoc, ← rat_mul]
  rfl

end GlobalTheory.SiegelWeilLitCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiNormalFramesExistSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiNormalFramesExistSplitPlace
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod

theorem Frame.exists_of_vecMul {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (β : Matrix (Fin N) Y k) (hc : Fintype.card Y = N) (h : ∀ v, v ᵥ* β = 0 → v = 0) :
    ∃ F : GlobalTheory.LocMod.Frame k N Y, F.β = β := by
  obtain ⟨g, hg⟩ := β.vecMulLinear.exists_leftInverse_of_injective (LinearMap.ker_eq_bot'.2 h)
  have h1 : β * LinearMap.toMatrixRight' g = 1 := by
    ext i j
    have := congrFun (LinearMap.congr_fun hg (Pi.single i 1)) j
    have h2 : ∀ x, g x = x ᵥ* LinearMap.toMatrixRight' g := fun x => by
      conv_lhs => rw [← LinearMap.toMatrixRight'.symm_apply_apply g]
      rfl
    rw [LinearMap.comp_apply, h2, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, Matrix.single_one_vecMul] at this
    simpa [Pi.single_apply, Matrix.one_apply, eq_comm] using this
  exact ⟨⟨β, _, h1, (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hc])).1 h1⟩, rfl⟩

theorem Frame.card_eq {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k N Y) : Fintype.card Y = N := by
  have h1 := Matrix.rank_mul_le_left F.β F.γ
  have h2 := Matrix.rank_mul_le_left F.γ F.β
  rw [F.βγ, Matrix.rank_one] at h1
  rw [F.γβ, Matrix.rank_one] at h2
  have h3 := Matrix.rank_le_card_width F.β
  have h4 := Matrix.rank_le_card_width F.γ
  simp only [Fintype.card_fin] at h1 h4
  omega

theorem Frame.eq_zero {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k N Y) {v : Fin N → k} (h : v ᵥ* F.β = 0) : v = 0 := by
  rw [← Matrix.vecMul_one v, ← F.βγ, ← Matrix.vecMul_vecMul, h, Matrix.zero_vecMul]

theorem hyp_eq_zero {D : D7} {k : Type} [Field k] (f : D.host.E →+* k) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    {v : Fin S.rank → k} (h1 : v ᵥ* d.e.map f = 0) (h2 : v ᵥ* d.i₀.map f = 0) (h3 : v ᵥ* d.e'.map f = 0) : v = 0 := by
  have h := congrArg (fun M => v ᵥ* Matrix.map M f) d.sum_eq_one_rat
  simp only [Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_one _ (map_zero f) (map_one f), Matrix.vecMul_add,
    ← Matrix.vecMul_vecMul, h1, h2, h3, Matrix.zero_vecMul, add_zero, Matrix.vecMul_one] at h
  exact h.symm

theorem orth_eq_zero {D : D7} {k : Type} [Field k] (f : D.host.E →+* k) {S A L : HSp D} (o : OrthDec S A L)
    {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ)
    {v : Fin S.rank → k} (h1 : v ᵥ* o.iA.map f = 0) (h2 : v ⬝ᵥ (f ∘ vecB o ζ) = 0) : v = 0 := by
  have h3 : v ᵥ* o.iB.map f = 0 := by
    funext j
    have hs : Subsingleton (Fin L.rank) := by rw [hζ.1]; infer_instance
    have hj : ζ j ≠ 0 := fun h0 => hζ.2 (by
      have : ζ = 0 := funext fun i => by rw [Subsingleton.elim i j, h0]; rfl
      rw [this, Matrix.mulVec_zero, dotProduct_zero])
    have h4 : f ∘ vecB o ζ = o.iB.map f *ᵥ (f ∘ ζ) := funext fun i => RingHom.map_mulVec f o.iB ζ i
    rw [h4, Matrix.dotProduct_mulVec, dotProduct, Fintype.sum_subsingleton _ j] at h2
    exact (mul_eq_zero.1 h2).resolve_right ((map_ne_zero f).2 hj)
  have h := congrArg (fun M => v ᵥ* Matrix.map M f) o.iA_qA_add
  simp only [Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_one _ (map_zero f) (map_one f), Matrix.vecMul_add,
    ← Matrix.vecMul_vecMul, h1, h3, Matrix.zero_vecMul, add_zero, Matrix.vecMul_one] at h
  exact h.symm

theorem dot_eq_zero_of_smul {k : Type} [Field k] {N : ℕ} {v w : Fin N → k} {c : k} (hc : c ≠ 0)
    (h : v ⬝ᵥ (fun r => c * w r) = 0) : v ⬝ᵥ w = 0 := by
  have : v ⬝ᵥ (c • w) = 0 := h
  rw [dotProduct_smul] at this
  exact (mul_eq_zero.1 this).resolve_left hc

namespace Place

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} {s : k}

theorem xi_ne_zero : p.xi ≠ 0 := (map_ne_zero (p.π.comp (incA D))).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)

theorem hz_ne_zero (B : BesLev D ρ) : p.hz B ≠ 0 := (map_ne_zero (p.π.comp (incA D))).2 B.line.2

theorem exists_isCoreFrame (hs : s ≠ 0) (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n) :
    ∃ F, p.IsCoreFrame B s FA F := by
  obtain ⟨F, hF⟩ := Frame.exists_of_vecMul (N := B.V₀.rank) (Y := n ⊕ Unit)
    (Matrix.of fun r => Sum.elim (fun a => (B.o.iA.map p.pr * FA.β) r a) fun _ => s * p.pr (vecB B.o B.ζ r))
    (by rw [Fintype.card_sum, FA.card_eq, ← B.o.rank_add, B.line.1]; rfl) (fun v hv => by
      refine orth_eq_zero (p.π.comp (incA D)) B.o B.line (FA.eq_zero ?_) (dot_eq_zero_of_smul hs ?_)
      · rw [Matrix.vecMul_vecMul]; funext a; exact congrFun hv (Sum.inl a)
      · exact congrFun hv (Sum.inr ()))
  exact ⟨F, fun r a => by rw [hF]; rfl, fun r => by rw [hF]; rfl⟩

theorem exists_isJacFrame (hs : s ≠ 0) (J : JacLev D ρ) {hh : k} (hh0 : hh ≠ 0) (F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n) :
    ∃ F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F := by
  have hx := p.xi_ne_zero
  let β : Matrix (Fin J.W.rank) (n ⊕ Fin (2 * ρ)) k :=
    Matrix.of fun r => Sum.elim (fun a => (J.d.i₀.map p.pr * F₀.β) r a) fun j =>
      if h : j.val < ρ then s * p.xi ^ (ρ - j.val) * p.pr (J.d.e r ⟨j.val, h⟩)
      else s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - (2 * ρ - 1 - j.val)) * p.pr (J.d.e' r ⟨2 * ρ - 1 - j.val, by omega⟩)
  have b1 : ∀ (i : Fin ρ) (j : Fin (2 * ρ)), j.val = i.val → ∀ r,
      β r (Sum.inr j) = s * p.xi ^ (ρ - i.val) * p.pr (J.d.e r i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (rfl : j = i) r
    exact dif_pos hi
  have b2 : ∀ (i : Fin ρ) (j : Fin (2 * ρ)), j.val + i.val + 1 = 2 * ρ → ∀ r,
      β r (Sum.inr j) = s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (J.d.e' r i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (h : j + i + 1 = 2 * ρ) r
    obtain rfl : i = 2 * ρ - 1 - j := by omega
    exact dif_neg (show ¬ j < ρ by omega)
  obtain ⟨F, hF⟩ := Frame.exists_of_vecMul β
    (by rw [Fintype.card_sum, F₀.card_eq, ← J.d.rank_add, Fintype.card_fin]) (fun v hv => by
      refine hyp_eq_zero (p.π.comp (incA D)) J.d ?_ (F₀.eq_zero ?_) ?_
      · funext i
        have := congrFun hv (Sum.inr ⟨i.val, by omega⟩)
        refine dot_eq_zero_of_smul (c := s * p.xi ^ (ρ - i.val)) (mul_ne_zero hs (pow_ne_zero _ hx)) ?_
        refine Eq.trans ?_ this
        exact congrArg (v ⬝ᵥ ·) (funext fun r => (b1 i _ rfl r).symm)
      · rw [Matrix.vecMul_vecMul]; funext a; exact congrFun hv (Sum.inl a)
      · funext i
        have := congrFun hv (Sum.inr ⟨2 * ρ - 1 - i.val, by omega⟩)
        refine dot_eq_zero_of_smul (c := s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val))
          (mul_ne_zero (mul_ne_zero hs (div_ne_zero hh0 hx)) (pow_ne_zero _ (div_ne_zero (by simp) hx))) ?_
        refine Eq.trans ?_ this
        exact congrArg (v ⬝ᵥ ·) (funext fun r => (b2 i _ (by have := i.2; dsimp only; omega) r).symm))
  exact ⟨F, rfl, fun r a => by rw [hF]; rfl, by rw [hF]; exact b1, by rw [hF]; exact b2⟩

theorem exists_isBesFrame (hs : s ≠ 0) (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n) :
    ∃ F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F := by
  have hx := p.xi_ne_zero
  let β : Matrix (Fin B.V.rank) (n ⊕ Fin (2 * ρ + 1)) k :=
    Matrix.of fun r => Sum.elim (fun a => ((B.d.i₀ * B.o.iA).map p.pr * FA.β) r a) fun j =>
      if h : j.val < ρ then s * p.xi ^ (ρ - j.val) * p.pr (B.d.e r ⟨j.val, h⟩)
      else if h' : j.val = ρ then s * p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r)
      else s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - (2 * ρ - j.val)) * p.pr (B.d.e' r ⟨2 * ρ - j.val, by omega⟩)
  have b1 : ∀ (i : Fin ρ) (j : Fin (2 * ρ + 1)), j.val = i.val → ∀ r,
      β r (Sum.inr j) = s * p.xi ^ (ρ - i.val) * p.pr (B.d.e r i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (rfl : j = i) r
    exact dif_pos hi
  have b0 : ∀ j : Fin (2 * ρ + 1), j.val = ρ → ∀ r, β r (Sum.inr j) = s * p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r) := by
    rintro ⟨j, hj⟩ (h : j = ρ) r
    exact (dif_neg (show ¬ j < ρ by omega)).trans (dif_pos h)
  have b2 : ∀ (i : Fin ρ) (j : Fin (2 * ρ + 1)), j.val + i.val = 2 * ρ → ∀ r,
      β r (Sum.inr j) = s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (B.d.e' r i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (h : j + i = 2 * ρ) r
    obtain rfl : i = 2 * ρ - j := by omega
    exact (dif_neg (show ¬ j < ρ by omega)).trans (dif_neg (show ¬ j = ρ by omega))
  obtain ⟨F, hF⟩ := Frame.exists_of_vecMul β
    (by rw [Fintype.card_sum, FA.card_eq, ← B.d.rank_add, ← B.o.rank_add, B.line.1, Fintype.card_fin]; omega)
    (fun v hv => by
      refine hyp_eq_zero (p.π.comp (incA D)) B.d ?_
        (orth_eq_zero (p.π.comp (incA D)) B.o B.line (FA.eq_zero ?_) ?_) ?_
      · funext i
        have := congrFun hv (Sum.inr ⟨i.val, by omega⟩)
        refine dot_eq_zero_of_smul (c := s * p.xi ^ (ρ - i.val)) (mul_ne_zero hs (pow_ne_zero _ hx)) ?_
        refine Eq.trans ?_ this
        exact congrArg (v ⬝ᵥ ·) (funext fun r => (b1 i _ rfl r).symm)
      · rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.map_mul]
        funext a; exact congrFun hv (Sum.inl a)
      · have := congrFun hv (Sum.inr ⟨ρ, by omega⟩)
        rw [← Matrix.dotProduct_mulVec]
        refine dot_eq_zero_of_smul hs ?_
        refine Eq.trans ?_ this
        refine congrArg (v ⬝ᵥ ·) (funext fun r => ((b0 _ rfl r).trans ?_).symm)
        exact congrArg (s * ·) (RingHom.map_mulVec (p.π.comp (incA D)) _ _ r)
      · funext i
        have := congrFun hv (Sum.inr ⟨2 * ρ - i.val, by omega⟩)
        refine dot_eq_zero_of_smul (c := s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val))
          (mul_ne_zero (mul_ne_zero hs (div_ne_zero (neg_ne_zero.2 (p.hz_ne_zero B)) hx))
            (pow_ne_zero _ (div_ne_zero (by simp) hx))) ?_
        refine Eq.trans ?_ this
        exact congrArg (v ⬝ᵥ ·) (funext fun r => (b2 i _ (by have := i.2; dsimp only; omega) r).symm))
  exact ⟨F, rfl, fun r a => by rw [hF]; rfl, by rw [hF]; exact b1, by rw [hF]; exact b0, by rw [hF]; exact b2⟩

end Place

theorem normalFrames_exist : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (s : k), s ≠ 0 → (∀ (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n), (∃ F, p.IsCoreFrame B s FA F) ∧ (∃ F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ p.hz B ≠ 0) ∧ ∀ (J : JacLev D ρ) (hh : k), hh ≠ 0 → ∀ F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n, ∃ F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F :=
  fun _ _ _ _ _ _ p _ _ _ _ _ hs =>
    ⟨fun B FA => ⟨p.exists_isCoreFrame hs B FA, p.exists_isBesFrame hs B FA, p.hz_ne_zero B⟩,
      fun J _ hh0 F₀ => p.exists_isJacFrame hs J hh0 F₀⟩

end GlobalTheory.LocMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiNormalFramesExistSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_fourierJacobi_normalFrames_exist_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (s : k), s ≠ 0 → (∀ (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n), (∃ F, p.IsCoreFrame B s FA F) ∧ (∃ F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ p.hz B ≠ 0) ∧ ∀ (J : JacLev D ρ) (hh : k), hh ≠ 0 → ∀ F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n, ∃ F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F := by
  first | exact @GlobalTheory.LocMod.normalFrames_exist | exact GlobalTheory.LocMod.normalFrames_exist | (intros; apply GlobalTheory.LocMod.normalFrames_exist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JointStarProductNonvanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodBoundIff
noncomputable section

namespace GlobalTheory.ExpAtTypePrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain

theorem col_smul {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (a : ℂ)
    (φ : C.cls 0 → C.Y 0 → ℂ) : C.col (a • φ) = a • C.col φ := by
  unfold ColumnChain.col
  generalize R.m = n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext j
    simp only [Formalism.ThetaLiftIndependence.chainOpM, Formalism.ThetaLiftIndependence.kerOpM, ih, Pi.smul_apply, map_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem perCol_smul (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (a : ℂ) (φ : D.what₂.Mu u) (F : D.what₂.Amb μ) :
    D.what₂.perCol u μ (a • φ) F = a * D.what₂.perCol u μ φ F := by
  by_cases hμ : μ = D.what₂.mu0
  · subst hμ
    simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, Submodule.coe_smul, col_smul,
      LinearMap.smul_apply, smul_eq_mul]
  · simp only [D.perCol_tie u μ hμ, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, Submodule.coe_smul, col_smul,
      LinearMap.smul_apply, smul_eq_mul]

end GlobalTheory.ExpAtTypePrimes

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MiStar2OfAnchored
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

namespace GlobalTheory.MiTop

theorem miStar2_of_anchored : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) (V : X.EE →ₗ[ℂ] X.EE) (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ) (c : (fc X.zs).Dc.Mem → Bs.Tup → ℂ), OpsUnit X V U → Anchored X eV sEE V U c → UnitAt X c → X.MIstar2 eV sEE := by
  intro K _ _ _ Bs A X fc eV sEE V U c hOp hAn hUn
  choose p b hp hb hid using hAn
  refine ⟨⟨V, fun u => p u / (b u * c u Bs.μ0), U, fun u t => c u t / c u Bs.μ0⟩, ?_, ?_, ?_⟩
  · refine ⟨hOp.1, hOp.2, ⟨fun u t => div_ne_zero (hUn.1 u t) (hUn.1 u Bs.μ0), fun u w k hk => hUn.2 u w k hk⟩,
      fun u => div_self (hUn.1 u Bs.μ0)⟩
  · intro u t φ F
    have h := hid u t φ F
    have hc := hUn.1 u Bs.μ0
    have hbu := hb u
    dsimp only
    field_simp
    linear_combination h
  · intro u
    exact div_ne_zero (hp u) (mul_ne_zero (hb u) (hUn.1 u Bs.μ0))

end GlobalTheory.MiTop
end

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

namespace GlobalTheory.MiTop.AtReal

open Formalism.IndefR.Links

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K}

theorem cols_heq {Df Df' : DefSide Bs} (hDf : Df = Df') {Dc : DefCols Df} {Dc' : DefCols Df'} (hD : HEq Dc Dc')
    {m : Dc.Mem} {m' : Dc'.Mem} (hm : HEq m m') :
    Dc.a m = Dc'.a m' ∧ (∀ v, HEq (Dc.Xc m v) (Dc'.Xc m' v)) ∧
      ∀ t (x : Fin (Dc.a m) → K) (x' : Fin (Dc'.a m') → K) (F : Fin (Df.nV t) → K) (F' : Fin (Df'.nV t) → K),
        HEq x x' → HEq F F' → Dc.Pt m t x F = Dc'.Pt m' t x' F' := by
  subst hDf
  obtain rfl := eq_of_heq hD
  obtain rfl := eq_of_heq hm
  refine ⟨rfl, fun v => HEq.rfl, fun t x x' F F' hx hF => ?_⟩
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hF
  rfl

theorem cols_mem {Df Df' : DefSide Bs} (hDf : Df = Df') {Dc : DefCols Df} {Dc' : DefCols Df'} (hD : HEq Dc Dc')
    (m : Dc.Mem) : ∃ m' : Dc'.Mem, HEq m m' := by
  subst hDf
  obtain rfl := eq_of_heq hD
  exact ⟨m, HEq.rfl⟩

end Gen

theorem heq_fin {α : Type} {n n' : ℕ} (h : n = n') (x : Fin n → α) : ∃ x' : Fin n' → α, HEq x x' := by
  subst h; exact ⟨x, HEq.rfl⟩

theorem heq_fin' {α : Type} {n n' : ℕ} (h : n = n') (x' : Fin n' → α) : ∃ x : Fin n → α, HEq x x' := by
  subst h; exact ⟨x', HEq.rfl⟩

theorem heq_mat {n n' : ℕ} (h : n = n') (M' : Matrix (Fin n') (Fin n') ℂ) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, HEq M M' := by
  subst h; exact ⟨M', HEq.rfl⟩

theorem heq_mulVec {n n' : ℕ} (h : n = n') {M : Matrix (Fin n) (Fin n) ℂ} {M' : Matrix (Fin n') (Fin n') ℂ}
    (hM : HEq M M') {x : Fin n → ℂ} {x' : Fin n' → ℂ} (hx : HEq x x') : HEq (M.mulVec x) (M'.mulVec x') := by
  subst h; obtain rfl := eq_of_heq hM; obtain rfl := eq_of_heq hx; rfl

theorem heq_fnorm {n n' : ℕ} (h : n = n') {Y : Matrix (Fin n) (Fin n) ℂ} {Y' : Matrix (Fin n') (Fin n') ℂ}
    (hY : HEq Y Y') {x : Fin n → ℂ} {x' : Fin n' → ℂ} (hx : HEq x x') : fnorm Y x = fnorm Y' x' := by
  subst h; obtain rfl := eq_of_heq hY; obtain rfl := eq_of_heq hx; rfl

theorem heq_cpt {K : Type} [Field K] (σ : K →+* ℂ) {n n' : ℕ} (h : n = n') {x : Fin n → K} {x' : Fin n' → K}
    (hx : HEq x x') : HEq (cpt σ x) (cpt σ x') := by
  subst h; obtain rfl := eq_of_heq hx; rfl

theorem heq_cjv (s : Bool) {n n' : ℕ} (h : n = n') {x : Fin n → ℂ} {x' : Fin n' → ℂ}
    (hx : HEq x x') : HEq (Formalism.L2.SG.JoinSI.cjv s x) (Formalism.L2.SG.JoinSI.cjv s x') := by
  subst h; obtain rfl := eq_of_heq hx; rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end GlobalTheory.MiTop.AtReal

namespace GlobalTheory.MiTop.AtReal

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end GlobalTheory.MiTop.AtReal

namespace GlobalTheory.MiTop

open Formalism.IndefR.Links GlobalTheory.MiTop.AtReal


end GlobalTheory.MiTop

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstTermExistenceOfUniversal
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.FirstTermCompare

variable {D : D7}

theorem hasIw_of_good {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {l : Lvl T} (hl : l.Good) :
    HasIw d l.K ∧ IsCompact (l.K : Set (GA D T)) := by
  have h := GlobalTheory.T.goodMajorantLevel_conj_unitaryAdelicMaximalCompact D T T₀ r d l.c hl.2.2
    (GlobalTheory.T.adelic_iwasawa_decomposition_wittIsotropicStabilizer D T T₀ r d l.c GlobalTheory.Core.Rk.IP.Model.isSplit_two hl.2.2) l hl
  exact ⟨h.1, h.2.1⟩

end GlobalTheory.RegSch.FirstTermCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

namespace GlobalTheory.LocOm

def LawLoc {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (ω : Om S T) (μS μT : kˣ →* ℂˣ) (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ))
    (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k) : Prop :=
  ∀ Φ Φ' : SB (Matrix Y Y' k),
    Φ'.1 = (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk Φ.1 →
      ω (g, h) (Tm Φ) = Tm Φ'

def Enl {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (gk : GL Y' k) (hk : GL Y k) : Prop :=
  ∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) →
    ∀ r q, ((↑(hk⁻¹) : Matrix Y Y k) * x * (↑gk : Matrix Y' Y' k)) r q ∈ 𝒪[k]

end GlobalTheory.LocOm

end
end
