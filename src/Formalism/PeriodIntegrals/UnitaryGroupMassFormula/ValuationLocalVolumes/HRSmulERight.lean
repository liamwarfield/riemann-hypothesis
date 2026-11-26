module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CountPOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUTyp

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HRSmulERight
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HRSmulRight
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem sigR_alg (c : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, sigR_tmul_one]

theorem hR_smul_right (c : Fv F v) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c • hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_smul_left (c : Fv F v) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (c • x) y = c • hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum, map_mul, sigR_alg]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_add_right (x y y' : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (y + y') = hR (Fv F v) σ J x y + hR (Fv F v) σ J x y' := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hR_add_left (x x' y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (x + x') y = hR (Fv F v) σ J x y + hR (Fv F v) σ J x' y := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hR_zero_right (x : Fin n → Fv F v ⊗[F] E) : hR (Fv F v) σ J x 0 = 0 := by
  simp [hR, Formalism.UG.hform]

theorem hR_zero_left (y : Fin n → Fv F v ⊗[F] E) : hR (Fv F v) σ J 0 y = 0 := by
  simp [hR, Formalism.UG.hform]

theorem oev_smul {c : v.adicCompletionIntegers F} {w : Fv F v ⊗[F] E} (hw : w ∈ OEv (E := E) v) :
    (c : Fv F v) • w ∈ OEv (E := E) v :=
  Submodule.smul_mem _ c hw

theorem hR_mem_of (Λ : Set (Fin n → E))
    (hL : ∀ a ∈ Λ, ∀ b ∈ Λ, ∃ o : 𝓞 E, hE σ J a b = (o : E))
    {x y : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc (E := E) v Λ) (hy : y ∈ latLoc (E := E) v Λ) :
    hR (Fv F v) σ J x y ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      obtain ⟨o, ho⟩ := hL a ha b hb
      have h' : hR (Fv F v) σ J (fun i => inclR (Fv F v) (a i)) (fun i => inclR (Fv F v) (b i)) =
          inclR (Fv F v) (hE σ J a b) := hR_ratTup (Fv F v) σ J ![a, b] 0 1
      change hR (Fv F v) σ J (fun i => inclR (Fv F v) (a i)) (fun i => inclR (Fv F v) (b i)) ∈ _
      rw [h', ho]
      exact Submodule.subset_span ⟨o, trivial, rfl⟩
    | zero => rw [hR_zero_right]; exact Submodule.zero_mem _
    | add y y' _ _ h1 h2 => rw [hR_add_right]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h =>
      change hR (Fv F v) σ J _ ((c : Fv F v) • y) ∈ _
      rw [hR_smul_right]; exact oev_smul v h
  | zero => rw [hR_zero_left]; exact Submodule.zero_mem _
  | add x x' _ _ h1 h2 => rw [hR_add_left]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    change hR (Fv F v) σ J ((c : Fv F v) • x) _ ∈ _
    rw [hR_smul_left]; exact oev_smul v h

end Gen

variable {D : D7} (X : HidaSetting D)

theorem hE_L (a : Fin X.B.I.n → X.B.I.E) (ha : a ∈ abelian₂ X) (b : Fin X.B.I.n → X.B.I.E) (hb : b ∈ abelian₂ X) :
    ∃ o : 𝓞 X.B.I.E, hE X.B.I.cm.sig X.B.I.J a b = (o : X.B.I.E) := by
  obtain ⟨o, ho⟩ := (X.B.I.L_dual b).1 hb a ha
  exact ⟨o, ho.symm⟩

theorem omVSD_fwd (v : PlX X) {x y : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E}
    (hx : x ∈ latLoc (E := X.B.I.E) v (abelian₂ X)) (hy : y ∈ latLoc (E := X.B.I.E) v (abelian₂ X)) :
    hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J x y ∈ OEv (E := X.B.I.E) v :=
  hR_mem_of X.B.I.cm.sig X.B.I.J v (abelian₂ X) (hE_L X) hx hy

def OmVSDBwd : Prop :=
  ∀ (v : PlX X) (y : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E),
    (∀ x ∈ latLoc (E := X.B.I.E) v (abelian₂ X), hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J x y ∈ OEv (E := X.B.I.E) v) →
      y ∈ latLoc (E := X.B.I.E) v (abelian₂ X)

theorem omVSD_of (h : OmVSDBwd X) : OmVSD X := fun v y =>
  ⟨fun hy x hx => omVSD_fwd X v hx hy, h v y⟩

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem hR_smulE_right (c : Fv F v ⊗[F] E) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_sum_right {ι : Type} (s : Finset ι) (x : Fin n → Fv F v ⊗[F] E) (f : ι → Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (∑ i ∈ s, f i) = ∑ i ∈ s, hR (Fv F v) σ J x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact hR_zero_right σ J v x
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hR_add_right, ih]

theorem oev_mul {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, _, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, _, rfl⟩ := hy
      rw [← map_mul]
      exact Submodule.subset_span ⟨a * b, trivial, by simp⟩
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y y' _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x x' _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

end Gen

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem lat_oev_smul (v : PlX X) {c : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E} (hc : c ∈ OEv (E := X.B.I.E) v)
    {x : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E} (hx : x ∈ latLoc (E := X.B.I.E) v (abelian₂ X)) :
    c • x ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨o, _, rfl⟩ := hc
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      refine Submodule.subset_span ⟨o • l, X.B.I.L.smul_mem o hl, ?_⟩
      funext i
      simp only [ratV, Pi.smul_apply, smul_eq_mul]
      rw [← map_mul]
      rfl
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x x' _ _ h1 h2 => rw [smul_add]; exact Submodule.add_mem _ h1 h2
    | smul d x _ h =>
      beta_reduce
      beta_reduce at h
      have e : inclR (F := X.B.I.F) (Fv X.B.I.F v) (o : X.B.I.E) • (d • x) =
          d • (inclR (F := X.B.I.F) (Fv X.B.I.F v) (o : X.B.I.E) • x) := by
        funext i
        change _ * ((d : Fv X.B.I.F v) • x i) = (d : Fv X.B.I.F v) • (_ * x i)
        rw [mul_smul_comm]
      rw [e]; exact Submodule.smul_mem _ d h
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add c c' _ _ h1 h2 => rw [add_smul]; exact Submodule.add_mem _ h1 h2
  | smul d c _ h =>
    have e : (d • c) • x = d • (c • x) := by
      funext i
      change ((d : Fv X.B.I.F v) • c) * x i = (d : Fv X.B.I.F v) • (c * x i)
      rw [smul_mul_assoc]
    rw [e]; exact Submodule.smul_mem _ d h

abbrev zi : Fin (D.R.rS + 1 + D.R.rS) := Fin.castAdd D.R.rS (Fin.last D.R.rS)

theorem gramE_entry (j i : Fin (D.R.rS + 1 + D.R.rS)) :
    gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i = if i = piv D.R.rS j then cD X u' j else 0 := by
  rw [gram_eq, diagonal_mul]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Function.Involutive.coe_toPerm]
  by_cases h : i = piv D.R.rS j
  · rw [if_pos h.symm, if_pos h, mul_one]
  · rw [if_neg (fun e => h e.symm), if_neg h, mul_zero]

def OmVMem : Prop := ∀ (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)), yTup X u' v i ∈ latLoc (E := X.B.I.E) v (abelian₂ X)

def OmVZPrim : Prop :=
  ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal → ∀ c : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E,
    c • yTup X u' v (zi (D := D)) ∈ latLoc (E := X.B.I.E) v (abelian₂ X) → c ∈ OEv (E := X.B.I.E) v

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertB
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
  PI.VolStabSW
open scoped TensorProduct

def CorOne {R : Type} [CommRing R] {a : ℕ} (T : Matrix (Fin a) (Fin a) R) : Prop :=
  ∃ i₀ : Fin a, (∀ j, T i₀ j = 0) ∧ (∀ j, T j i₀ = 0) ∧ IsUnit (T + Matrix.single i₀ i₀ 1).det

def FFInertB : Prop :=
  ∀ (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K),
    (∀ x, σ (σ x) = x) → Module.finrank k K = 2 → σ ≠ AlgEquiv.refl →
    ∀ (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) K, (∀ i j, σ (J j i) = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) K, (∀ i j, σ (T j i) = T i j) → CorOne T →
    (Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T ∧ LinearIndependent K X} : ℝ) =
      (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) *
        ∏ j ∈ Finset.Icc (M - a) M, (1 - (-1 : ℝ) ^ j * (Nat.card k : ℝ) ^ (-(j : ℤ)))

def FFSplitB : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) (k × k), (∀ i j, (J j i).swap = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) (k × k), (∀ i j, (T j i).swap = T i j) → CorOne T →
    (Nat.card {X : Fin a → Fin M → k × k //
        ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J X = T ∧ LinearIndependent (k × k) X} : ℝ) =
      (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) *
        ∏ j ∈ Finset.Icc (M - a) M, (1 - (1 : ℝ) ^ j * (Nat.card k : ℝ) ^ (-(j : ℤ)))

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def RedP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = Ideal.absNorm v.asIdeal ∧
      ((etaV (E := E) v = -1 ∧ ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K)
          (J' : Matrix (Fin n) (Fin n) K) (T' : Matrix (Fin a) (Fin a) K),
          (∀ x, σ' (σ' x) = x) ∧ Module.finrank k K = 2 ∧ σ' ≠ AlgEquiv.refl ∧
          (∀ i j, σ' (J' j i) = J' i j) ∧ IsUnit J'.det ∧ (∀ i j, σ' (T' j i) = T' i j) ∧ CorOne T' ∧
          Nat.card (clsP σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) =
            Nat.card {X : Fin a → Fin n → K // ffGram (σ' : K →+* K) J' X = T' ∧ LinearIndependent K X}) ∨
       (etaV (E := E) v = 1 ∧ ∃ (J' : Matrix (Fin n) (Fin n) (k × k)) (T' : Matrix (Fin a) (Fin a) (k × k)),
          (∀ i j, (J' j i).swap = J' i j) ∧ IsUnit J'.det ∧ (∀ i j, (T' j i).swap = T' i j) ∧ CorOne T' ∧
          Nat.card (clsP σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) =
            Nat.card {X : Fin a → Fin n → k × k //
              ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J' X = T' ∧ LinearIndependent (k × k) X}))

theorem clsP_of (a : ℕ) (Y : TupV (E := E) v n a) (hR : RedP σ J ψ v Λ a Y) (hI : FFInertB) (hS : FFSplitB) :
    ClsP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have ha : a ≤ n := hG.2.2.2.2.1
  obtain ⟨k, _, _, hk, h⟩ := hR hG ϖ hϖ
  rcases h with ⟨hη, K, _, _, σ', J', T', hσ, h2, hne, hJ, hJu, hT, hTu, hc⟩ |
    ⟨hη, J', T', hJ, hJu, hT, hTu, hc⟩
  · rw [hc, hI k K σ' hσ h2 hne n a ha J' hJ hJu T' hT hTu, hk]
    unfold prodEtaB qv
    rw [hη]
    push_cast
    rfl
  · rw [hc, hS k n a ha J' hJ hJu T' hT hTu, hk]
    unfold prodEtaB qv
    rw [hη]
    push_cast
    rfl

end Gen

end PI.OmVd
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUHerm
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolUHm

open Formalism.L2.SG.Pf.NcVal Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

theorem sigR_inclR (x : E) : sigR (Fv F v) σ (inclR (F := F) (Fv F v) x) = inclR (F := F) (Fv F v) (σ x) := by
  simp [sigR, inclR]

theorem sigR_sc (c : Fv F v) : sigR (Fv F v) σ (sc (E := E) v c) = sc (E := E) v c := by
  simp [sigR, sc, Algebra.TensorProduct.map_tmul]

theorem sigR_smul (c : Fv F v) (x : Fv F v ⊗[F] E) : sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  rw [← VolTU.sc_mul_eq_smul, ← VolTU.sc_mul_eq_smul, map_mul, sigR_sc]

theorem sigR_mem {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : sigR (Fv F v) σ x ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    rw [sigR_inclR]
    exact VolUTr.TrW.inclR_mem' (E := E) v ⟨σ a, (a.2).map σ.toRingHom.toIntAlgHom⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ h1 h2 => rw [map_add (f := _)]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    have e : c • x = (c : Fv F v) • x := rfl
    rw [e, sigR_smul]
    exact Submodule.smul_mem _ c h

def sigL : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) where
  toFun := sigR (Fv F v) σ
  map_add' := map_add _
  map_smul' := sigR_smul σ v

theorem sigR_cont : Continuous (sigR (Fv F v) σ : Fv F v ⊗[F] E → Fv F v ⊗[F] E) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  exact IsModuleTopology.continuous_of_linearMap (sigL σ v)

theorem sigR_sigR (hinv : ∀ y, σ (σ y) = y) (x : Fv F v ⊗[F] E) : sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, Algebra.TensorProduct.map_tmul, hinv]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

section Phi

variable (r : ℕ)

def phiF (Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E :=
  fun p => if p.1 < p.2 then Y p + sigR (Fv F v) σ (Y (p.2, p.1)) else Y p

def phiB (Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E :=
  fun p => if p.1 < p.2 then Y p - sigR (Fv F v) σ (Y (p.2, p.1)) else Y p

theorem phiF_low (Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) {i j : Fin (r + 1)} (h : ¬ i < j) :
    phiF σ v r Y (i, j) = Y (i, j) := by
  simp [phiF, h]

theorem phiF_up (Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) {i j : Fin (r + 1)} (h : i < j) :
    phiF σ v r Y (i, j) = Y (i, j) + sigR (Fv F v) σ (Y (j, i)) := by
  simp [phiF, h]

def phiE : (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) ≃ₜ+ (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) where
  toFun := phiF σ v r
  invFun := phiB σ v r
  left_inv Y := by
    funext p
    by_cases h : p.1 < p.2
    · have h' : ¬ p.2 < p.1 := fun h2 => lt_asymm h h2
      simp [phiF, phiB, h, h']
    · simp [phiF, phiB, h]
  right_inv Y := by
    funext p
    by_cases h : p.1 < p.2
    · have h' : ¬ p.2 < p.1 := fun h2 => lt_asymm h h2
      simp [phiF, phiB, h, h']
    · simp [phiF, phiB, h]
  map_add' Y Z := by
    funext p
    by_cases h : p.1 < p.2
    · simp only [phiF, h, if_true, Pi.add_apply, map_add (f := _)]
      abel
    · simp [phiF, h]
  continuous_toFun := by
    haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
    refine continuous_pi fun p => ?_
    by_cases h : p.1 < p.2
    · simp only [phiF, h, if_true]
      exact (continuous_apply p).add ((sigR_cont σ v).comp (continuous_apply (p.2, p.1)))
    · simp only [phiF, h, if_false]
      exact continuous_apply p
  continuous_invFun := by
    haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
      IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
    refine continuous_pi fun p => ?_
    by_cases h : p.1 < p.2
    · simp only [phiB, h, if_true]
      exact (continuous_apply p).sub ((sigR_cont σ v).comp (continuous_apply (p.2, p.1)))
    · simp only [phiB, h, if_false]
      exact continuous_apply p

theorem phiF_mem_iff (Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :
    (∀ i j, phiF σ v r Y (i, j) ∈ OEv (E := E) v) ↔ ∀ i j, Y (i, j) ∈ OEv (E := E) v := by
  constructor
  · intro h i j
    by_cases hij : i < j
    · have h1 := h i j
      have h2 := h j i
      rw [phiF_up σ v r Y hij] at h1
      rw [phiF_low σ v r Y (fun h3 => lt_asymm hij h3)] at h2
      have e : Y (i, j) = (Y (i, j) + sigR (Fv F v) σ (Y (j, i))) - sigR (Fv F v) σ (Y (j, i)) := by ring
      rw [e]
      exact Submodule.sub_mem _ h1 (sigR_mem σ v h2)
    · have h1 := h i j
      rwa [phiF_low σ v r Y hij] at h1
  · intro h i j
    by_cases hij : i < j
    · rw [phiF_up σ v r Y hij]
      exact Submodule.add_mem _ (h i j) (sigR_mem σ v (h j i))
    · rw [phiF_low σ v r Y hij]
      exact h i j

def hermBox (g r : ℕ) (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) :
    Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :=
  {Y | ∀ i j, Y (i, j) ∈ OEv (E := E) v ∧
    (i < j → (Y (i, j) - c i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v) ∧
    (i = j → (Y (i, j) + sigR (Fv F v) σ (Y (i, j)) - c i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v)}

theorem volTW_eq (hinv : ∀ y, σ (σ y) = y) (g r : ℕ) (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E))
    (hc : VolTHermInt σ v r c) : VolTW σ v g r c = phiF σ v r ⁻¹' hermBox σ v g r c := by
  ext Y
  simp only [VolTW, hermBox, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · intro h i j
    refine ⟨(phiF_mem_iff σ v r Y).2 (fun i j => (h i j).1) i j, fun hij => ?_, fun hij => ?_⟩
    · rw [phiF_up σ v r Y hij]
      exact (h i j).2
    · subst hij
      rw [phiF_low σ v r Y (lt_irrefl _)]
      exact (h i i).2
  · intro h
    have hO := (phiF_mem_iff σ v r Y).1 (fun i j => (h i j).1)
    intro i j
    refine ⟨hO i j, ?_⟩
    rcases lt_trichotomy i j with hij | hij | hij
    · have := (h i j).2.1 hij
      rwa [phiF_up σ v r Y hij] at this
    · subst hij
      have := (h i i).2.2 rfl
      rwa [phiF_low σ v r Y (lt_irrefl _)] at this
    · have h1 := sigR_mem σ v ((h j i).2.1 hij)
      rw [phiF_up σ v r Y hij, map_mul, sigR_sc, map_sub, map_add (f := _), sigR_sigR σ v hinv, ← hc.1 j i] at h1
      rw [show Y (i, j) + sigR (Fv F v) σ (Y (j, i)) - c i j =
        sigR (Fv F v) σ (Y (j, i)) + Y (i, j) - c i j by ring]
      exact h1

theorem volTW_meas (hinv : ∀ y, σ (σ y) = y) (μ : Measure (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E))
    [μ.IsAddHaarMeasure] (hK : μ (VolTO (E := E) v (Fin (r + 1) × Fin (r + 1))) = 1) (g : ℕ)
    (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) (hc : VolTHermInt σ v r c) :
    μ (VolTW σ v g r c) = μ (hermBox σ v g r c) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := VolUH.top_facts (E := E) v (Fin (r + 1) × Fin (r + 1))
  have h := VolUH.haar_pre μ (phiE σ v r) (VolTO (E := E) v (Fin (r + 1) × Fin (r + 1))) hK (hermBox σ v g r c)
  have hK' : (phiE σ v r) ⁻¹' VolTO (E := E) v (Fin (r + 1) × Fin (r + 1)) =
      VolTO (E := E) v (Fin (r + 1) × Fin (r + 1)) := by
    ext Y
    simp only [VolTO, Set.mem_preimage, Set.mem_setOf_eq, Prod.forall]
    exact phiF_mem_iff σ v r Y
  rw [hK', hK, one_mul] at h
  rw [volTW_eq σ v hinv g r c hc]
  exact h

variable (ψ : AddChar (AF F) ℂ)

def VolTHermBox (g : ℕ) : Prop :=
  ∀ c, VolTHermInt σ v r c →
    sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) (hermBox σ v g r c) = ((g : ℝ≥0∞) ^ ((r + 1) ^ 2))⁻¹

theorem volTHermCnt_of_box (hψ : IsCharAF F ψ) (hfin : Module.finrank F E = 2) (hann : VolUL.AnnAt (E := E) ψ v)
    (hd : absV v (dV v) = 1) (hinv : ∀ y, σ (σ y) = y) (g : ℕ) (hB : VolTHermBox σ v r ψ g) :
    VolTHermCnt σ ψ v g r := by
  obtain ⟨hH, -, hO⟩ := VolUL.sd_facts ψ v hψ hfin hann hd (Fin (r + 1) × Fin (r + 1))
  intro c hc
  rw [volTW_meas σ v r hinv _ hO g c hc]
  exact hB c hc

end Phi

end Formalism.L2.SG.Pf.NcVal.VolUHm
end
end
