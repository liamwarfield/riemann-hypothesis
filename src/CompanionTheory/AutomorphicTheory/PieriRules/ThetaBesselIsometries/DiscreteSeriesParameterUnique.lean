module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesParameterUnique

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesParameterUnique
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace GlobalTheory
namespace DSInequiv

open PI.DSInfCharCap

lemma eq_of_capP {n : ℕ} (mu mu' : Fin n → ℝ) (h : StrictAnti mu) (h' : StrictAnti mu')
    (e : ∀ Y : ℂ, Formalism.QuantumDeterminants.capP (fun s => (mu s : ℂ)) Y = Formalism.QuantumDeterminants.capP (fun s => (mu' s : ℂ)) Y) :
    mu = mu' := _root_.GlobalTheory.DSInequiv.eq_of_capP (n := n) mu mu' h h' e

section
variable {n : ℕ} {ε : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {τ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

def toReal (V : H ≃L[ℂ] H') : H ≃L[ℝ] H' :=
  { V.toLinearEquiv.restrictScalars ℝ with
    continuous_toFun := V.continuous
    continuous_invFun := V.symm.continuous }

lemma dsig_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Formalism.REAL.inG ε X) (v : H) :
    V (PI.PhMeasCore.dsig τ X v) = PI.PhMeasCore.dsig τ' X (V v) := by
  unfold PI.PhMeasCore.dsig
  have e : (fun t : ℝ => τ' (NormedSpace.exp ((t : ℂ) • X)) (V v)) =
      (toReal V) ∘ (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • X)) v) := by
    funext t
    exact (hV _ (Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t) v).symm
  rw [e]
  unfold deriv
  rw [ContinuousLinearEquiv.comp_fderiv]
  rfl

lemma dsigC_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (Y : Matrix (Fin n) (Fin n) ℂ) (v : H) : V (dsigC ε τ Y v) = dsigC ε τ' Y (V v) := _root_.GlobalTheory.DSInequiv.dsigC_equiv V hV Y v

lemma dsigCW_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (w : List (Matrix (Fin n) (Fin n) ℂ)) (v : H) : V (dsigCW ε τ w v) = dsigCW ε τ' w (V v) := by
  induction w with
  | nil => rfl
  | cons Y w ih => simp only [dsigCW]; rw [dsigC_equiv V hV, ih]

lemma actU_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (p : FreeAlgebra ℂ (Fin n × Fin n)) (v : H) : V (actU ε τ p v) = actU ε τ' p (V v) := by
  unfold actU Finsupp.sum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_smul, dsigCW_equiv V hV]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma smooth_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    {v : H} (hv : v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ) :
    V v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hm, hF, hE⟩ := hv g₀ hg₀
  refine ⟨U, fun g => V (F g), hU, hm, ?_, fun g hg hg' => ?_⟩
  · exact ((toReal V).contDiff).comp_contDiffOn hF
  · exact (hV g hg' v).symm.trans (congrArg V (hE g hg hg'))

lemma smooth_conj {A B P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hA : Pᴴ * A * P = B) {v : H}
    (hv : PI.UpqRep.SmoothOnH B (fun g => τ g v)) :
    v ∈ PI.PhMeasCore.smoothVecs A (fun g => τ (P⁻¹ * g * P)) := _root_.GlobalTheory.DSInequiv.smooth_conj (A := A) (B := B) (P := P) (v := v) hP hA hv

lemma eq_of_equiv {mu mu' : Fin n → ℝ} (hm : Formalism.QuantumDeterminants.IsHCParam mu) (hm' : Formalism.QuantumDeterminants.IsHCParam mu')
    (h : ∀ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ, ∀ Y : ℂ,
      actU ε τ (Formalism.REAL.qdet (Egl n) (Y + ((n : ℂ) - 1) / 2)) v = Formalism.QuantumDeterminants.capP (fun s => (mu s : ℂ)) Y • v)
    (h' : ∀ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ', ∀ Y : ℂ,
      actU ε τ' (Formalism.REAL.qdet (Egl n) (Y + ((n : ℂ) - 1) / 2)) v = Formalism.QuantumDeterminants.capP (fun s => (mu' s : ℂ)) Y • v)
    (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    {v : H} (hv : v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ) (h0 : v ≠ 0) : mu = mu' := by
  refine eq_of_capP mu mu' hm.1 hm'.1 fun Y => ?_
  have e1 := h v hv Y
  have e2 := h' (V v) (smooth_equiv V hV hv) Y
  rw [← actU_equiv V hV, e1, map_smul] at e2
  exact smul_left_injective ℂ (by simpa using h0) e2

lemma inUJ_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ PI.UpqRep.UJset ε) (hb : b ∈ PI.UpqRep.UJset ε) :
    a * b ∈ PI.UpqRep.UJset ε := by
  show (a * b)ᴴ * PI.UpqRep.Jm ε * (a * b) = PI.UpqRep.Jm ε
  have ha' : aᴴ * PI.UpqRep.Jm ε * a = PI.UpqRep.Jm ε := ha
  have hb' : bᴴ * PI.UpqRep.Jm ε * b = PI.UpqRep.Jm ε := hb
  calc _ = bᴴ * (aᴴ * PI.UpqRep.Jm ε * a) * b := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha', hb']

lemma cayley_quot {B P Q : Matrix (Fin n) (Fin n) ℂ} (hQ : IsUnit Q) (hP : Pᴴ * PI.UpqRep.Jm ε * P = B)
    (hQ' : Qᴴ * PI.UpqRep.Jm ε * Q = B) : P * Q⁻¹ ∈ PI.UpqRep.UJset ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  show (P * Q⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * Q⁻¹) = PI.UpqRep.Jm ε
  calc _ = (Q⁻¹)ᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * Q⁻¹ := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (Q * Q⁻¹)ᴴ * PI.UpqRep.Jm ε * (Q * Q⁻¹) := by
      rw [hP, ← hQ', conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

end

lemma exists_kfin {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} (R : Rep k r)
    {P : Mx k r} (hP : PI.UpqRep.IsCayleyU k r ε P) (h : PI.UpqRep.IsDS ε mu (fun g => R.σ (P⁻¹ * g * P))) :
    ∃ v, R.KFin v ∧ v ≠ 0 := _root_.GlobalTheory.DSInequiv.exists_kfin (k := k) (r := r) (ε := ε) (mu := mu) (P := P) R hP h

theorem param_eq_of_equiv : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r), R.IsDG ε mu → R'.IsDG ε mu' → ∀ U : R.H ≃ₗᵢ[ℂ] R'.H, (∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x)) → mu = mu' := by
  intro hy k r ε mu mu' R R' hR hR' U hU
  obtain ⟨hm, ⟨P, hP, h⟩, hgp⟩ := hR
  obtain ⟨hm', ⟨Q, hQ, h'⟩, hgp'⟩ := hR'
  obtain ⟨v, hv, hv0⟩ := exists_kfin R hP h
  have hs := hy.1.2.2.1 k r ε mu R.H R.σ hm ⟨P, hP, h⟩ v hv
  have hs' := smooth_conj (A := Formalism.REAL.Jm ε) hP.1.1 hP.1.2 hs
  have hdP := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hdQ := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.1.1
  have p1 := Matrix.mul_nonsing_inv _ hdP
  have q1 := Matrix.mul_nonsing_inv _ hdQ
  have p2 := Matrix.nonsing_inv_mul _ hdP
  have q2 := Matrix.nonsing_inv_mul _ hdQ
  have p3 : ∀ B : Mx k r, P⁻¹ * (P * B) = B := fun B => by rw [← Matrix.mul_assoc, p2, Matrix.one_mul]
  have q3 : ∀ B : Mx k r, Q⁻¹ * (Q * B) = B := fun B => by rw [← Matrix.mul_assoc, q2, Matrix.one_mul]
  have p4 : ∀ B : Mx k r, P * (P⁻¹ * B) = B := fun B => by rw [← Matrix.mul_assoc, p1, Matrix.one_mul]
  have ha := cayley_quot hQ.1.1 hP.1.2 hQ.1.2
  have hb := cayley_quot hP.1.1 hQ.1.2 hP.1.2
  obtain ⟨⟨hone, hmul⟩, -⟩ := h'.2.2.1
  set τ' : Mx k r → (R'.H →L[ℂ] R'.H) := fun g => R'.σ (Q⁻¹ * g * Q) with hτ'
  have hmul' : ∀ a ∈ PI.UpqRep.UJset ε, ∀ b ∈ PI.UpqRep.UJset ε, ∀ x, τ' a (τ' b x) = τ' (a * b) x := by
    intro a ha b hb x
    rw [hmul a ha b hb]; rfl
  have hab : (P * Q⁻¹) * (Q * P⁻¹) = 1 := by simp only [Matrix.mul_assoc, q3, p1]
  have hba : (Q * P⁻¹) * (P * Q⁻¹) = 1 := by simp only [Matrix.mul_assoc, p3, q1]
  let A : R'.H ≃L[ℂ] R'.H := ContinuousLinearEquiv.equivOfInverse (τ' (P * Q⁻¹)) (τ' (Q * P⁻¹))
    (fun x => by rw [hmul' _ hb _ ha, hba, hone]; rfl) (fun x => by rw [hmul' _ ha _ hb, hab, hone]; rfl)
  refine eq_of_equiv hm hm' (hy.2.2.1 k r ε mu _ _ ⟨P, hP⟩ hgp hm h) (hy.2.2.1 k r ε mu' _ _ ⟨P, hP⟩ hgp' hm' h') (U.toContinuousLinearEquiv.trans A) ?_ hs' hv0
  intro g hg x
  have hg' : g ∈ PI.UpqRep.UJset ε := hg
  have hG : P⁻¹ * g * P ∈ GG k r := by
    show (P⁻¹ * g * P)ᴴ * PI.UpqRep.Hpk k r * (P⁻¹ * g * P) = PI.UpqRep.Hpk k r
    have hgg : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε := hg
    have hc := hP.1.2
    calc _ = (P * (P⁻¹ * g * P))ᴴ * PI.UpqRep.Jm ε * (P * (P⁻¹ * g * P)) := by
          rw [← hc, conjTranspose_mul P]; simp only [Matrix.mul_assoc]
      _ = Pᴴ * (gᴴ * PI.UpqRep.Jm ε * g) * P := by
          simp only [Matrix.mul_assoc, p4, conjTranspose_mul g]
      _ = _ := by rw [hgg, hc]
  show τ' (P * Q⁻¹) (U (R.σ (P⁻¹ * g * P) x)) = τ' g (τ' (P * Q⁻¹) (U x))
  have e : R'.σ (P⁻¹ * g * P) = τ' (Q * P⁻¹ * g * (P * Q⁻¹)) := by
    simp only [hτ', Matrix.mul_assoc, q3, q2, Matrix.mul_one]
  rw [hU _ hG, e, hmul' _ ha _ (inUJ_mul (inUJ_mul hb hg') ha), hmul' _ hg' _ ha]
  congr 2
  simp only [Matrix.mul_assoc, q3, p4]

end DSInequiv
end GlobalTheory
end
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesParameterUniqueStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.discrete_series_parameter_unique : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r), R.IsDG ε mu → R'.IsDG ε mu' → ∀ U : R.H ≃ₗᵢ[ℂ] R'.H, (∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x)) → mu = mu' := by
  first | exact @GlobalTheory.DSInequiv.param_eq_of_equiv | exact GlobalTheory.DSInequiv.param_eq_of_equiv | (intros; apply GlobalTheory.DSInequiv.param_eq_of_equiv <;> assumption)
end Gp91
end
