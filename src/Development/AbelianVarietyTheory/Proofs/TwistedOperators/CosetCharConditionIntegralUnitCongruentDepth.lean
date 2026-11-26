module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorConjugateHalfVacuumEqSemichara

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplOSmulHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section
namespace GlobalTheory.CosDual

variable {D : D7}

theorem symplO_smul_half (S T : HSp D) (e : AE D) (u y : WO S T) (hy : IsHalf (cA D e) y) :
    symplO S T (e • u) y = symplO S T u y := by
  have hc : ∀ c b, cA D (y c b) = e * cA D (y c b) := fun c b => by
    conv_lhs => rw [← hy c b]
    rw [map_mul, GlobalTheory.LatVac.cA_cA]
  unfold symplO
  congr 2
  unfold hO
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl
    (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [Matrix.smul_apply, smul_eq_mul]
  conv_rhs => rw [hc c b]
  ring

theorem half_actO (S T : HSp D) (c : AE D) (h : GA D T) (Y : WO S T) (hY : IsHalf c Y) :
    IsHalf c (actO S T 1 h Y) := by
  have hYe : c • Y = Y := by
    ext a b
    exact hY a b
  have hm : c • actO S T 1 h Y = actO S T 1 h Y := by
    unfold actO
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hYe]
  intro a b
  exact congrFun (congrFun hm a) b

theorem actO_add (S T : HSp D) (h : GA D T) (Y Y' : WO S T) :
    actO S T 1 h (Y + Y') = actO S T 1 h Y + actO S T 1 h Y' := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem actO_inv (S T : HSp D) (h : GA D T) (y : WO S T) :
    actO S T 1 h (actO S T 1 h⁻¹ y) = y := by
  have h1 : Formalism.L2.Theta.mt T h * Formalism.L2.Theta.mt T h⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    first
      | rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
      | simp
  unfold actO
  simp [← Matrix.mul_assoc, h1]

end GlobalTheory.CosDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridCoreNodeUnitReadingIntegralCongruent
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridCoreNodeUnitReadingIntegralCongruent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.UnitRead

theorem core_gen {R : Type} [CommRing R] (S : Subring R) (J : Ideal S) {n : ℕ} (f : R) (hf : f ∈ S)
    (γ : GL (Fin n) R) (B₁ B₂ : Matrix (Fin n) (Fin n) R)
    (hB₁ : ∀ i j, ∃ s ∈ J, (s : R) = B₁ i j) (hB₂ : ∀ i j, ∃ s ∈ J, (s : R) = B₂ i j)
    (heq : f • (1 - B₁) = γ.1 * (f • (1 - B₂))) (w₁ w₂ : R) (hw₁ : w₁ ∈ S) (hw₂ : w₂ ∈ S)
    (h1 : (1 - B₁).det * w₁ * f = f) (h2 : (1 - B₂).det * w₂ * f = f) :
    (∀ i j, (f • γ.1) i j ∈ S) ∧ (∀ i j, (f • (γ⁻¹).1) i j ∈ S) ∧
      ∀ i j, ∃ s ∈ J, (s : R) = (f • γ.1 - f • 1) i j := by
  choose s₁ hs₁ e₁ using hB₁
  choose s₂ hs₂ e₂ using hB₂
  have hint : ∀ (t : Fin n → Fin n → S), (1 - Matrix.of fun i j => (t i j : R)) = (1 - Matrix.of t).map S.subtype := by
    intro t
    ext i j
    rw [Matrix.map_apply, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.of_apply, Matrix.of_apply, Matrix.one_apply,
      Matrix.one_apply]
    split_ifs <;> simp
  have hB₁' : B₁ = Matrix.of fun i j => (s₁ i j : R) := by ext i j; exact (e₁ i j).symm
  have hB₂' : B₂ = Matrix.of fun i j => (s₂ i j : R) := by ext i j; exact (e₂ i j).symm
  have isInt_map : ∀ (X : Matrix (Fin n) (Fin n) S) i j, X.map S.subtype i j ∈ S := fun X i j => (X i j).2
  have isInt_adj : ∀ (X : Matrix (Fin n) (Fin n) S) i j, (X.map S.subtype).adjugate i j ∈ S := by
    intro X i j
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_adjugate, RingHom.mapMatrix_apply]
    exact isInt_map _ i j
  have isInt_mul : ∀ (X Y : Matrix (Fin n) (Fin n) R), (∀ i j, X i j ∈ S) → (∀ i j, Y i j ∈ S) → ∀ i j, (X * Y) i j ∈ S := by
    intro X Y hX hY i j
    rw [Matrix.mul_apply]
    exact S.sum_mem fun k _ => S.mul_mem (hX i k) (hY k j)
  have isInt_smul : ∀ (c : R) (X : Matrix (Fin n) (Fin n) R), c ∈ S → (∀ i j, X i j ∈ S) → ∀ i j, (c • X) i j ∈ S := by
    intro c X hc hX i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact S.mul_mem hc (hX i j)
  have heq' : f • (1 - B₂) = (γ⁻¹).1 * (f • (1 - B₁)) := by
    rw [heq, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have adj : ∀ (C C' G : Matrix (Fin n) (Fin n) R) (w : R), C'.det * w * f = f → f • C = G * (f • C') →
      f • G = (w • (f • C)) * C'.adjugate := by
    intro C C' G w hw hC
    rw [hC]
    calc f • G = (C'.det * w * f) • G := by rw [hw]
      _ = _ := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_one, smul_smul]
        congr 1
        ring
  have hγ := adj _ _ _ w₂ h2 heq
  have hγ' := adj _ _ _ w₁ h1 heq'
  have hI₁ : ∀ i j, (1 - B₁) i j ∈ S := by rw [hB₁', hint]; exact isInt_map _
  have hI₂ : ∀ i j, (1 - B₂) i j ∈ S := by rw [hB₂', hint]; exact isInt_map _
  have hA₁ : ∀ i j, (1 - B₁).adjugate i j ∈ S := by rw [hB₁', hint]; exact isInt_adj _
  have hA₂ : ∀ i j, (1 - B₂).adjugate i j ∈ S := by rw [hB₂', hint]; exact isInt_adj _
  have hiγ : ∀ i j, (f • γ.1) i j ∈ S := by
    rw [hγ]
    exact isInt_mul _ _ (isInt_smul _ _ hw₂ (isInt_smul _ _ hf hI₁)) hA₂
  refine ⟨hiγ, ?_, ?_⟩
  · rw [hγ']
    exact isInt_mul _ _ (isInt_smul _ _ hw₁ (isInt_smul _ _ hf hI₂)) hA₁
  · have e1 : (f • γ.1) * (1 - B₂) = f • (1 - B₁) := by
      rw [heq, Matrix.smul_mul, Matrix.mul_smul]
    have e2 : f • γ.1 - f • 1 = (f • γ.1) * B₂ - f • B₁ := by
      have e3 : f • γ.1 - (f • γ.1) * B₂ = f • 1 - f • B₁ := by
        rw [← smul_sub, ← e1, Matrix.mul_sub, Matrix.mul_one]
      rw [← sub_eq_zero] at e3 ⊢
      rw [← e3]
      abel
    intro i j
    rw [e2, Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    refine ⟨(∑ k, (⟨_, hiγ i k⟩ : S) * s₂ k j) - ⟨f, hf⟩ * s₁ i j,
      sub_mem (J.sum_mem fun k _ => J.mul_mem_left _ (hs₂ k j)) (J.mul_mem_left _ (hs₁ i j)), ?_⟩
    simp [e₁, e₂]

end GlobalTheory.UnitRead

namespace GlobalTheory.UnitRead

variable {D : D7}

theorem toEAf_idem_int {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) :
    toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h := GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e P he 1
    (fun Q _ h => Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h))
  simp at h
  exact GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h

theorem resS_idS {𝔪 : Ideal (𝓞 D.host.E)} {PP : Pl D.host.E} (h : 𝔪 ≤ PP.asIdeal)
    {s : Formalism.L2.Herm.intAf D.host.F D.host.E} (hs : s ∈ idS D.host.F 𝔪) : resS D.host.F PP s = 0 := by
  have hle : idS D.host.F 𝔪 ≤ RingHom.ker (resS D.host.F PP) := by
    unfold idS
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, resS_oToS, Ideal.Quotient.eq_zero_iff_mem]
    exact h ha
  exact hle hs

theorem one_sub_unit {𝔪 : Ideal (𝓞 D.host.E)} {Z : Finset (Pl D.host.E)} (hZ : ∀ PP ∈ Z, 𝔪 ≤ PP.asIdeal)
    {e : AE D} (he : IsIdemSum e Z) {n : ℕ} (B : Matrix (Fin n) (Fin n) (EAf D))
    (hB : ∀ i j, ∃ s ∈ idS D.host.F 𝔪, (s : EAf D) = B i j) :
    ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, (1 - B).det * w * toEAf D e = toEAf D e := by
  choose s hs hsB using hB
  have e0 : (1 - B) = (1 - Matrix.of s).map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype := by
    ext i j
    rw [Matrix.map_apply, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.of_apply, Matrix.one_apply,
      Matrix.one_apply, ← hsB]
    split_ifs <;> simp
  have hdet : (1 - B).det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [e0, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((1 - Matrix.of s).det).2
  refine GlobalTheory.T.exists_integral_inverse_at_splitPlaces_of_units Z e he _ hdet fun PP hPP => ?_
  have hm : (1 - Matrix.of s).map (resS D.host.F PP) = 1 := by
    ext i j
    rw [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.of_apply, resS_idS (hZ PP hPP) (hs i j), sub_zero,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hd : (⟨(1 - B).det, hdet⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = (1 - Matrix.of s).det := by
    apply Subtype.ext
    change (1 - B).det = ((1 - Matrix.of s).det : EAf D)
    rw [e0, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  rw [hd, RingHom.map_det, RingHom.mapMatrix_apply, hm, Matrix.det_one]
  exact isUnit_one

end GlobalTheory.UnitRead

namespace GlobalTheory.UnitRead

variable {D : D7}

theorem map_smul_one_sub {n : ℕ} (e : AE D) (a : Matrix (Fin n) (Fin n) (AE D)) :
    (e • (1 - a)).map (toEAf D) = toEAf D e • (1 - a.map (toEAf D)) := by
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply,
    smul_eq_mul, smul_eq_mul, map_mul, map_sub, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem smul_mulVec_f {n : ℕ} (c : EAf D) (M : Matrix (Fin n) (Fin n) (EAf D)) (v : Fin n → EAf D) :
    (c • M) *ᵥ v = c • (M *ᵥ v) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc]

theorem conj_sub_one {R : Type} [CommRing R] {n : ℕ} (f : R) (b b' G : Matrix (Fin n) (Fin n) R) (h : b' * b = 1) :
    f • (b' * (G - 1) * b) = f • (b' * G * b) - f • (1 : Matrix (Fin n) (Fin n) R) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h, smul_sub]

theorem read_gen {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hlat : Submodule.IsFullLattice D.host.E Λ) {𝔪 : Ideal (𝓞 D.host.E)} {Z : Finset (Pl D.host.E)}
    (hZ : ∀ PP ∈ Z, 𝔪 ≤ PP.asIdeal) {e : AE D} (he : IsIdemSum e Z) (g : GA D V)
    (a₁ a₂ : Mx D V.rank V.rank) (ha₁ : a₁ ∈ GlobalTheory.ChiGrid.hatMx (𝔪 • GlobalTheory.ChiGrid.homLat Λ Λ))
    (ha₂ : a₂ ∈ GlobalTheory.ChiGrid.hatMx (𝔪 • GlobalTheory.ChiGrid.homLat Λ Λ))
    (heq : e • ((1 : WO V V) - a₁) = actO V V 1 g (e • (1 - a₂)))
    (x : Fin V.rank → D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    toEAf D e • ((Lev.finE V g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • (((Lev.finE V g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) := by
  obtain ⟨β, hβ⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E V.rank Λ hlat
  have hf := toEAf_idem_int he
  have hr : ∀ a : Mx D V.rank V.rank, a ∈ GlobalTheory.ChiGrid.hatMx (𝔪 • GlobalTheory.ChiGrid.homLat Λ Λ) →
      ∀ i j, ∃ s ∈ idS D.host.F 𝔪, (s : EAf D) = ((β⁻¹).1 * a.map (toEAf D) * β.1) i j :=
    fun a ha => ((GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D Λ Λ β β hβ hβ 𝔪 a).1 ha).2
  have hbb : (β⁻¹).1 * β.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hbb' : β.1 * (β⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

  have hmap : toEAf D e • (1 - a₁.map (toEAf D)) =
      (Lev.finE V g).1 * (toEAf D e • (1 - a₂.map (toEAf D))) := by
    rw [actO, inv_one, GlobalTheory.ChainOnto.FrameAct.mt_one', Matrix.mul_one] at heq
    have h := congrArg (fun N : Mx D V.rank V.rank => N.map (toEAf D)) heq
    rw [map_smul_one_sub, Matrix.map_mul, map_smul_one_sub] at h
    exact h
  have hc : ∀ A : Matrix (Fin V.rank) (Fin V.rank) (EAf D),
      toEAf D e • (1 - (β⁻¹).1 * A * β.1) = (β⁻¹).1 * (toEAf D e • (1 - A)) * β.1 := by
    intro A
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [hbb]
  have hfr : toEAf D e • (1 - (β⁻¹).1 * a₁.map (toEAf D) * β.1) =
      (β⁻¹ * Lev.finE V g * β).1 * (toEAf D e • (1 - (β⁻¹).1 * a₂.map (toEAf D) * β.1)) := by
    rw [hc, hc, hmap, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc β.1 (β⁻¹).1, hbb', Matrix.one_mul]
  obtain ⟨w₁, hw₁, h1⟩ := one_sub_unit hZ he _ (hr a₁ ha₁)
  obtain ⟨w₂, hw₂, h2⟩ := one_sub_unit hZ he _ (hr a₂ ha₂)
  obtain ⟨hi1, hi2, hi3⟩ := core_gen (Formalism.L2.Herm.intAf D.host.F D.host.E) (idS D.host.F 𝔪) (toEAf D e) hf
    (β⁻¹ * Lev.finE V g * β) _ _ (hr a₁ ha₁) (hr a₂ ha₂) hfr w₁ w₂ hw₁ hw₂ h1 h2
  have key : ∀ (N : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) (y : Fin V.rank → EAf D),
      (β⁻¹).1 *ᵥ (toEAf D e • (N *ᵥ y)) = (toEAf D e • ((β⁻¹).1 * N * β.1)) *ᵥ ((β⁻¹).1 *ᵥ y) := by
    intro N y
    rw [Matrix.mulVec_smul, smul_mulVec_f, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ β.1,
      hbb', Matrix.mul_one]
  have hy : ∀ k, ((β⁻¹).1 *ᵥ x) k ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (hβ x).1 hx
  have intv : ∀ (M : Matrix (Fin V.rank) (Fin V.rank) (EAf D)), (∀ i j, M i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
      ∀ k, (M *ᵥ ((β⁻¹).1 *ᵥ x)) k ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro M hM k
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hM k j) (hy j)
  refine ⟨(hβ _).2 fun k => ?_, (hβ _).2 fun k => ?_, ?_⟩
  · rw [key]
    exact intv _ (by simpa [Units.val_mul, Matrix.mul_assoc] using hi1) k
  · rw [key]
    have e4 := GlobalTheory.ChainOnto.FrameAct.conj_inv_val' β (Lev.finE V g)
    exact intv _ (by rw [← e4]; exact hi2) k
  · have e5 : toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) = toEAf D e • (((Lev.finE V g).1 - 1) *ᵥ x) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [e5, GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hβ 𝔪]
    intro k
    rw [key]
    have e6 : toEAf D e • ((β⁻¹).1 * ((Lev.finE V g).1 - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D))) * β.1) =
        toEAf D e • (β⁻¹ * Lev.finE V g * β).1 - toEAf D e • (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) := by
      rw [Units.val_mul, Units.val_mul]
      exact conj_sub_one _ _ _ _ hbb
    rw [e6]
    simp only [Matrix.mulVec, dotProduct]
    refine GlobalTheory.FrameIdeal.inId_sum _ fun j => ?_
    rw [mul_comm]
    exact GlobalTheory.FrameIdeal.inId_mul (hy j) (hi3 k j)

end GlobalTheory.UnitRead

theorem GlobalTheory.UnitRead.unit_read : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ a₁ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))), ∀ a₂ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))),
    e • ((1 : WO (G.V (.core i)) (G.V (.core i))) - a₁) = actO (G.V (.core i)) (G.V (.core i)) 1 g (e • (1 - a₂)) →
    ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)),
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • (((Lev.finE (G.V (.core i)) g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.modul • G.Λ (.core i)) := by
  intro D _ T L μ0 hL sc G W M hM i hi e he g a₁ ha₁ a₂ ha₂ heq x hx
  have hlat : Submodule.IsFullLattice D.host.E (G.Λ (.core i)) := GlobalTheory.AdIsom.selfDual_isFullLattice (G.sp.P_is i hi.le).sd
  have hZ : ∀ PP ∈ G.pl.W0, G.modul ≤ PP.asIdeal := by
    intro PP hPP
    classical
    simp only [GlobalTheory.ChiGrid.Places.W0, Finset.mem_image] at hPP
    obtain ⟨v, hv, rfl⟩ := hPP
    have h1 : G.modul ≤ (G.pl.w v).asIdeal ^ G.pl.depth sc v := Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)
    exact h1.trans (Ideal.pow_le_self (G.pl.depth_pos sc v).ne')
  exact GlobalTheory.UnitRead.read_gen hlat hZ he g a₁ a₂ ha₁ ha₂ heq x hx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridCoreNodeUnitReadingIntegralCongruentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridCoreNode_unitReading_integral_congruent : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ a₁ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))), ∀ a₂ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))),
    e • ((1 : WO (G.V (.core i)) (G.V (.core i))) - a₁) = actO (G.V (.core i)) (G.V (.core i)) 1 g (e • (1 - a₂)) →
    ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)),
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • (((Lev.finE (G.V (.core i)) g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.modul • G.Λ (.core i)) := by
  first | exact @GlobalTheory.UnitRead.unit_read | exact GlobalTheory.UnitRead.unit_read | (intros; apply GlobalTheory.UnitRead.unit_read <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfPointMemSumTranslateOfAnnihilator
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfPointMemSumTranslateOfAnnihilator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

namespace GlobalTheory.AnnSum

theorem latO_comm {D : D7} (S T : HSp D) {A A' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {B B' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hA : A.FG) (hB : B.FG)
    (hA' : Submodule.IsFullLattice D.host.E A') (hB' : Submodule.IsFullLattice D.host.E B') : ∃ N : ℕ, 0 < N ∧
    ∀ y ∈ latO S T (A : Set (Fin S.rank → D.host.E)) (B : Set (Fin T.rank → D.host.E)) (fun _ => True),
      N • y ∈ latO S T (A' : Set (Fin S.rank → D.host.E)) (B' : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hA hB
  obtain ⟨K, hK, hKm⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hA' hB'
  refine ⟨K * M, Nat.mul_pos hK hM, fun y hy => ?_⟩
  rw [mul_smul]
  refine hKm _ (Matrix.ext fun i j => ?_) fun i j => ?_
  · rw [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, GlobalTheory.LatVac.infPart_of_mem hy i j,
      mul_zero, Matrix.zero_apply]
  · rw [Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, map_natCast]
    exact hden y hy i j

theorem stdHom_eq {D : D7} (S T : HSp D) : GlobalTheory.AdForm.stdHom S T =
    latO S T (Formalism.L2.Col.stdLat D.host.E S.rank : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
      (Formalism.L2.Col.stdLat D.host.E T.rank : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (fun _ => True) := by
  rw [GlobalTheory.AdForm.coe_colStdLat, GlobalTheory.AdForm.coe_colStdLat]

theorem std_le_hat {D : D7} (S T : HSp D) {A : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {B : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hA : IsSelfDualC S A) (hB : IsSelfDualC T B)
    {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) : ∃ N : ℕ, 0 < N ∧ ∀ u ∈ GlobalTheory.AdForm.stdHom S T,
      N • u ∈ GlobalTheory.ChiGrid.hatMx (𝔪 • GlobalTheory.ChiGrid.homLat A B) := by
  obtain ⟨M, hM, h1⟩ := latO_comm S T (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := S.rank)).fg
    (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := T.rank)).fg
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S A hA)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T B hB)
  obtain ⟨K, hK, h2⟩ := GlobalTheory.GridWeil.exists_nsmul_latO (T := T) (ΛT := B) hA h𝔪
  refine ⟨K * M, Nat.mul_pos hK hM, fun u hu => ?_⟩
  rw [mul_smul]
  rw [stdHom_eq] at hu
  exact h2 _ (h1 u hu)

theorem hat_le_std {D : D7} (S T : HSp D) {A : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {B : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hA : IsSelfDualC S A) (hB : IsSelfDualC T B)
    (𝔪 : Ideal (𝓞 D.host.E)) : ∃ N : ℕ, 0 < N ∧ ∀ v ∈ GlobalTheory.ChiGrid.hatMx (𝔪 • GlobalTheory.ChiGrid.homLat A B),
      N • v ∈ GlobalTheory.AdForm.stdHom S T := by
  have hstd (n : ℕ) : Submodule.IsFullLattice D.host.E (Formalism.L2.Col.stdLat D.host.E n) := by
    haveI := Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := n)
    refine ⟨?_⟩
    apply top_unique
    intro v _
    have hv : v = ∑ i, v i • (Pi.single i (1 : D.host.E) : Fin n → D.host.E) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (by simpa using Formalism.L2.Col.single_mem_stdLat (E := D.host.E) i 1))
  obtain ⟨K, hK, h⟩ := GlobalTheory.GridWeil.exists_nsmul_hatMx (S := S) (T := T)
    (hstd S.rank) (hstd T.rank)
    (GlobalTheory.ChiGrid.homLat A B) (Module.Finite.iff_fg.1 (homLat_fg (GlobalTheory.PlaceVec.selfDual_isFullLattice S A hA) hB.1.fg))
  refine ⟨K, hK, fun v hv => ?_⟩
  rw [stdHom_eq]
  refine h _ (AddSubgroup.closure_mono ?_ hv)
  rintro _ ⟨α, hα, x, hx, rfl⟩
  exact ⟨α, hα, x, Submodule.smul_le_right hx, rfl⟩


set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem act_le_std (D : D7) (S T : HSp D) (g : GA D T) : ∃ N : ℕ, 0 < N ∧
    ∀ u ∈ GlobalTheory.AdForm.stdHom S T, N • actO S T 1 g u ∈ GlobalTheory.AdForm.stdHom S T := by
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T)
    (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := S.rank)).fg
    (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := T.rank)).fg
  rw [← stdHom_eq] at hden
  obtain ⟨K, hK, hKm⟩ := GlobalTheory.AdForm.exists_nsmul_mem_stdHom S T
  obtain ⟨N, hN, h'⟩ := GlobalTheory.PlaceDatum.exists_den_matrix (Formalism.L2.Herm.intAf D.host.F D.host.E)
    GlobalTheory.PlaceDatum.exists_den_adele ((mt T g).map (toEAf D))
  refine ⟨K * (N * M), Nat.mul_pos hK (Nat.mul_pos hN hM), fun u hu => ?_⟩
  have hact : ∀ i j, actO S T 1 g u i j = ∑ k, mt T g i k * u k j := fun i j => by
    have h1 : mt S (1 : GA D S)⁻¹ = 1 := by rw [inv_one]; rfl
    unfold actO
    rw [h1, Matrix.mul_one, Matrix.mul_apply]
  rw [mul_smul]
  refine hKm _ (Matrix.ext fun i j => ?_) fun i j => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    · have hz : ∑ k, (infPart D) (mt T g i k * u k j) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        rw [RingHom.map_mul, GlobalTheory.LatVac.infPart_of_mem hu k j, mul_zero]
      rw [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, hact, map_sum, hz,
        mul_zero, Matrix.zero_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, map_natCast, hact, map_sum, Finset.mul_sum]
      refine sum_mem fun k _ => ?_
      have h3 := mul_mem (h' i k) (hden u hu k j)
      rw [Matrix.map_apply, mul_mul_mul_comm, ← Nat.cast_mul, ← RingHom.map_mul] at h3
      exact h3

end GlobalTheory.AnnSum

namespace GlobalTheory.AnnSum

variable {D : D7}

def halfSub {m n : ℕ} (f : AE D) : AddSubgroup (Mx D m n) where
  carrier := {u | IsHalf f u}
  zero_mem' := fun i j => by simp
  add_mem' := fun {u v} hu hv i j => by rw [Matrix.add_apply, mul_add, hu i j, hv i j]
  neg_mem' := fun {u} hu i j => by rw [Matrix.neg_apply, mul_neg, hu i j]

theorem exists_div_half {m n : ℕ} (f : AE D) (k : ℕ) (hk : 0 < k) (x : Mx D m n) (hx : IsHalf f x) :
    ∃ x' : Mx D m n, IsHalf f x' ∧ k • x' = x := by
  refine ⟨algebraMap D.host.F (AE D) ((k : D.host.F)⁻¹) • x, fun i j => ?_, ?_⟩
  · rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hx i j]
  · ext i j
    have hF : (k : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, ← mul_assoc,
      show ((k : AE D)) = algebraMap D.host.F (AE D) (k : D.host.F) from (map_natCast _ k).symm,
      ← map_mul, mul_inv_cancel₀ hF, map_one, one_mul]

end GlobalTheory.AnnSum

namespace GlobalTheory.AnnSum

variable {D : D7}

theorem nsmul_smul_comm' {m n : ℕ} (k : ℕ) (c : AE D) (v : Mx D m n) : k • (c • v) = c • (k • v) := by
  ext a b
  simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
  ring


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem ann_sum_gen (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) (he : IsIdemSum e Q) (g : GA D T) (Mh : AddSubgroup (WO S T))
    (NA NB NC : ℕ) (hNA : 0 < NA) (hNB : 0 < NB) (hNC : 0 < NC)
    (hA : ∀ u ∈ GlobalTheory.AdForm.stdHom S T, IsHalf e u → NA • u ∈ Mh)
    (hB : ∀ v ∈ Mh, NB • v ∈ GlobalTheory.AdForm.stdHom S T)
    (hC : ∀ u ∈ GlobalTheory.AdForm.stdHom S T, NC • actO S T 1 g u ∈ GlobalTheory.AdForm.stdHom S T)
    (Z : WO S T) (hZ : IsHalf e Z)
    (hyp : ∀ y : WO S T, IsHalf (cA D e) y → (∀ v ∈ Mh, ψ (symplO S T (e • v) y) = 1) →
      (∀ v ∈ Mh, ψ (symplO S T (actO S T 1 g (e • v)) y) = 1) → ψ (symplO S T Z y) = 1) :
    ∃ a ∈ Mh, ∃ b ∈ Mh, Z = e • a + actO S T 1 g (e • b) := by
  classical
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hχ : GlobalTheory.PlaceModel.IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y; rw [GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y; rw [GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul]
    · intro y; rw [GlobalTheory.PlaceModel.symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y; rw [GlobalTheory.PlaceModel.symplO_zero_right, AddChar.map_zero_eq_one]
  let f1 : WO S T →+ WO S T := AddMonoidHom.mk' (fun v => e • v) (fun a b => smul_add e a b)
  let f2 : WO S T →+ WO S T := AddMonoidHom.mk' (fun v => actO S T 1 g (e • v))
    (fun a b => by rw [smul_add, GlobalTheory.CosDual.actO_add])
  let Lsum : AddSubgroup (WO S T) := Mh.map f1 ⊔ Mh.map f2
  have he_half : ∀ v : WO S T, IsHalf e (e • v) := fun v a b => by
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
  have heint : ∀ u ∈ GlobalTheory.AdForm.stdHom S T, e • u ∈ GlobalTheory.AdForm.stdHom S T := fun u hu =>
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hee])) _ hu
  have hN : 0 < NA * (NB * NC) := Nat.mul_pos hNA (Nat.mul_pos hNB hNC)
  have hNL : ∀ u ∈ GlobalTheory.AnnConjHalf.stdHalf S T e, (NA * (NB * NC)) • u ∈ Lsum := by
    intro u hu
    have h1 : NA • u ∈ Lsum := by
      refine AddSubgroup.mem_sup_left ⟨NA • u, hA u hu.1 hu.2, ?_⟩
      change e • (NA • u) = NA • u
      rw [← nsmul_smul_comm']
      congr 1
      exact Matrix.ext fun a b => hu.2 a b
    rw [mul_nsmul]
    exact AddSubgroup.nsmul_mem _ h1 _
  have hLN : ∀ u ∈ Lsum, (NA * (NB * NC)) • u ∈ GlobalTheory.AnnConjHalf.stdHalf S T e := by
    intro u hu
    obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hu
    obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hy
    obtain ⟨b, hb, rfl⟩ := AddSubgroup.mem_map.1 hz
    refine ⟨?_, ?_⟩
    · rw [smul_add]
      refine add_mem ?_ ?_
      · have h1 : NB • (e • a) ∈ GlobalTheory.AdForm.stdHom S T := by
          rw [nsmul_smul_comm']; exact heint _ (hB a ha)
        have e1 : (NA * (NB * NC)) • f1 a = (NA * NC) • (NB • (e • a)) := by
          rw [← mul_nsmul']; congr 1; ring
        rw [e1]
        exact AddSubgroup.nsmul_mem _ h1 _
      · have h1 : NC • f2 (NB • b) ∈ GlobalTheory.AdForm.stdHom S T := hC _ (heint _ (hB b hb))
        rw [map_nsmul, ← mul_nsmul'] at h1
        have e1 : (NA * (NB * NC)) • f2 b = NA • ((NC * NB) • f2 b) := by
          rw [← mul_nsmul']; congr 1; ring
        rw [e1]
        exact AddSubgroup.nsmul_mem _ h1 _
    · refine GlobalTheory.AnnConjHalf.half_nsmul ?_ _
      intro a' b'
      rw [Matrix.add_apply, mul_add]
      congr 1
      · exact he_half a a' b'
      · exact GlobalTheory.CosDual.half_actO S T e g (e • b) (he_half b) a' b'
  have h2 : ∀ x ∈ halfSub (m := T.rank) (n := S.rank) e, (∀ y ∈ GlobalTheory.AnnConjHalf.annHalf ψ S T e,
      ψ (symplO S T x y) = 1) → x ∈ GlobalTheory.AnnConjHalf.stdHalf S T e := fun x hx H =>
    ⟨GlobalTheory.HalfDoubleAnn.mem_of_ann_ann D ψ hψ S T Q e he x hx (fun y hy hann => H y ⟨hy, hann⟩), hx⟩
  have hann : ∀ y ∈ halfSub (m := T.rank) (n := S.rank) (cA D e), (∀ u ∈ Lsum, ψ (symplO S T u y) = 1) →
      ψ (symplO S T Z y) = 1 := fun y hy h =>
    hyp y hy (fun v hv => h _ (AddSubgroup.mem_sup_left ⟨v, hv, rfl⟩))
      (fun v hv => h _ (AddSubgroup.mem_sup_right ⟨v, hv, rfl⟩))
  have hNx : (NA * (NB * NC)) • Z ∈ GlobalTheory.AnnConjHalf.stdHalf S T e := by
    refine h2 _ (GlobalTheory.AnnConjHalf.half_nsmul hZ _) fun y hy => ?_
    rw [hχ.nsmul]
    refine hann _ (GlobalTheory.AnnConjHalf.half_nsmul hy.1 _) fun u hu => ?_
    rw [← hχ.nsmul]
    have h := hLN u hu
    exact hy.2 _ h.1 h.2
  have key : Z ∈ Lsum := GlobalTheory.DualTransfer.mem_of_double_annihilator (fun x y => ψ (symplO S T x y)) hχ
    (halfSub e) (halfSub (cA D e)) (GlobalTheory.AnnConjHalf.stdHalf S T e) (GlobalTheory.AnnConjHalf.annHalf ψ S T e) Lsum
    (fun u hu => hu.2) (fun u hu => hu.1)
    (sup_le (by rintro _ ⟨v, -, rfl⟩; exact he_half v)
      (by rintro _ ⟨v, -, rfl⟩; exact GlobalTheory.CosDual.half_actO S T e g (e • v) (he_half v)))
    (fun u hu y hy => hy.2 u hu.1 hu.2) h2
    (fun y hy H => ⟨hy, fun x hx hxh => H x ⟨hx, hxh⟩⟩)
    (fun k hk x hx => exists_div_half e k hk x hx)
    (fun k hk y hy => exists_div_half (cA D e) k hk y hy)
    (fun k hk a b hab => by
      have h0 : k • (a - b) = 0 := by rw [smul_sub]; exact sub_eq_zero.2 hab
      exact sub_eq_zero.1 (GlobalTheory.AnnConjHalf.nsmul_eq_zero_WO S T hk _ h0))
    (fun k hk => by
      obtain ⟨R, hR⟩ := GlobalTheory.HalfStdFin.exists_reps_half_stdHom D S T Q e he k hk
      refine ⟨(R : Set (WO S T)), R.finite_toSet, fun t ht => ?_⟩
      obtain ⟨r, hr, v, hv, hvh, htv⟩ := hR t ht.1 ht.2
      exact ⟨r, hr, v, ⟨hv, hvh⟩, htv⟩)
    (fun k hk => by
      obtain ⟨R, hR⟩ := GlobalTheory.AnnConjHalf.ann_conj_half_finite D ψ hψ S T Q e he k hk
      refine ⟨(R : Set (WO S T)), R.finite_toSet, fun t ht => ?_⟩
      obtain ⟨r, hr, v, hvh, hv, htv⟩ := hR t ht.1 ht.2
      exact ⟨r, hr, v, ⟨hvh, hv⟩, htv⟩)
    _ hN hNL hLN Z hZ hNx hann
  obtain ⟨y, hy, z, hz, hyz⟩ := AddSubgroup.mem_sup.1 key
  obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hy
  obtain ⟨b, hb, rfl⟩ := AddSubgroup.mem_map.1 hz
  exact ⟨a, ha, b, hb, hyz.symm⟩

end GlobalTheory.AnnSum

namespace GlobalTheory.AnnSum

theorem ann_sum : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ Z : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf e Z →
    (∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • v) y) = 1) →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO _ _ 1 g (e • v)) y) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) Z y) = 1) →
    ∃ a ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), ∃ b ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), Z = e • a + actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • b) := by
  intro D hq T L μ0 hL sc G W M hM i hi e he g Z hZ hyp
  have dS : IsSelfDualC (G.pS (.core i)) (G.latS (.core i)) := isSelfDualC_neg (G.sp.P_is (i + 1) hi).sd
  have dT : IsSelfDualC (G.pT (.core i)) (G.latT (.core i)) := (G.sp.P_is i hi.le).sd
  obtain ⟨NA, hNA, hA⟩ := std_le_hat _ _ dS dT (G.pl.modul_ne_bot sc)
  obtain ⟨NB, hNB, hB⟩ := hat_le_std _ _ dS dT G.modul
  obtain ⟨NC, hNC, hC⟩ := act_le_std D (G.pS (.core i)) (G.pT (.core i)) g
  exact ann_sum_gen W.ψ W.ψ_std _ _ G.pl.W0 e he g _ NA NB NC hNA hNB hNC (fun u hu _ => hA u hu) hB hC Z hZ hyp

end GlobalTheory.AnnSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfPointMemSumTranslateOfAnnihilatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfPoint_mem_sum_translate_of_annihilator : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ Z : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf e Z →
    (∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • v) y) = 1) →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO _ _ 1 g (e • v)) y) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) Z y) = 1) →
    ∃ a ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), ∃ b ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), Z = e • a + actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • b) := by
  first | exact @GlobalTheory.AnnSum.ann_sum | exact GlobalTheory.AnnSum.ann_sum | (intros; apply GlobalTheory.AnnSum.ann_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetEquationMulRightCongruentOneModDepthIdealAl
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetEquationMulRightCongruentOneModDepthIdealAl
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section
namespace GlobalTheory.CosDualStep

variable {D : D7}

theorem actO_one_left (S T : HSp D) (h : GA D T) (Z : WO S T) :
    actO S T 1 h Z = HMul.hMul (Formalism.L2.Theta.mt T h) (Z : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
  unfold actO
  simp [Formalism.L2.Theta.mt]

theorem infPart_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) : infPart D e = 0 := by
  classical
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  subst hsum
  induction P using Finset.induction_on with
  | empty => rw [Finset.sum_empty, RingHom.map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, RingHom.map_add (f := _), GlobalTheory.SplitScalar.infPart_splitIdem (hes a (Finset.mem_insert_self a s)).1,
      ih fun PP hPP => hes PP (Finset.mem_insert_of_mem hPP), add_zero]

def finLift {m n : ℕ} (c : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  Matrix.of fun a b => pairA D.host.F 0 1 ⊗ₜ[D.host.F] c a b

theorem smul_map_incA {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {m n : ℕ}
    (c : Matrix (Fin m) (Fin n) D.host.E) :
    e • c.map (incA D) = e • finLift c := by
  ext a b
  simp only [finLift, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [map_mul, map_mul, infPart_idemSum he, zero_mul, zero_mul]
  · rw [map_mul, map_mul, GlobalTheory.LatVac.finPart_pair, GlobalTheory.LatVac.finPart_incA]

theorem homLat_mul {a b c : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin c → D.host.E)}
    {x : Matrix (Fin c) (Fin b) D.host.E} {y : Matrix (Fin b) (Fin a) D.host.E}
    (hx : x ∈ homLat Λ' Λ'') (hy : y ∈ homLat Λ Λ') : x * y ∈ homLat Λ Λ'' := by
  show ∀ v ∈ Λ, (x * y) *ᵥ v ∈ Λ''
  intro v hv
  rw [← Matrix.mulVec_mulVec]
  exact hx _ (hy v hv)

theorem smul_homLat_mul {a b c : ℕ} {𝔪 : Ideal (𝓞 D.host.E)} {Λ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin c → D.host.E)}
    {x : Matrix (Fin c) (Fin b) D.host.E} {y : Matrix (Fin b) (Fin a) D.host.E}
    (hx : x ∈ 𝔪 • homLat Λ' Λ'') (hy : y ∈ homLat Λ Λ') : x * y ∈ 𝔪 • homLat Λ Λ'' := by
  refine Submodule.smul_induction_on hx (fun r hr n hn => ?_) (fun p q hp hq => ?_)
  · rw [Matrix.smul_mul]
    exact Submodule.smul_mem_smul hr (homLat_mul hn hy)
  · rw [Matrix.add_mul]
    exact Submodule.add_mem _ hp hq

theorem hatMx_mul {a b c : ℕ} {M : Submodule (𝓞 D.host.E) (Matrix (Fin c) (Fin b) D.host.E)}
    {N : Submodule (𝓞 D.host.E) (Matrix (Fin c) (Fin a) D.host.E)} (y : Matrix (Fin b) (Fin a) D.host.E)
    (hMN : ∀ x ∈ M, x * y ∈ N) {u : Mx D c b} (hu : u ∈ hatMx M) : u * y.map (incA D) ∈ hatMx N := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, x * y, hMN x hx, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show _ * (Algebra.TensorProduct.includeRight (y k j)) = _
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add p q _ _ hp hq => rw [Matrix.add_mul]; exact add_mem hp hq
  | neg p _ hp => rw [Matrix.neg_mul]; exact neg_mem hp

theorem smul_one_sub {n : ℕ} (e : AE D) (A A' C : Matrix (Fin n) (Fin n) (AE D)) (h : e • A = e • C) :
    e • (1 - (A' - C)) = e • (1 + A - A') := by
  rw [smul_sub, smul_sub, smul_sub, smul_add, h]
  abel

theorem core_step {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {n n' : ℕ}
    (x₀ : Matrix (Fin n) (Fin n') D.host.E) (y₀ : Matrix (Fin n') (Fin n) D.host.E)
    (mg : Matrix (Fin n) (Fin n) (AE D)) (u u' : Matrix (Fin n) (Fin n') (AE D))
    (heq : e • (x₀.map (incA D) - u) = HMul.hMul mg (e • (x₀.map (incA D) - u'))) :
    e • ((1 : Matrix (Fin n) (Fin n) (AE D)) - (HMul.hMul u (y₀.map (incA D)) -
        finLift (x₀ * y₀ - 1))) =
      HMul.hMul mg (e • ((1 : Matrix (Fin n) (Fin n) (AE D)) - (HMul.hMul u' (y₀.map (incA D)) -
        finLift (x₀ * y₀ - 1)))) := by
  have hxy : x₀ * y₀ = 1 + (x₀ * y₀ - 1) := by abel
  have hXY : HMul.hMul (x₀.map (incA D)) (y₀.map (incA D)) = (1 : Matrix (Fin n) (Fin n) (AE D)) + (x₀ * y₀ - 1).map (incA D) := by
    rw [← Matrix.map_mul]
    conv_lhs => rw [hxy]
    rw [Matrix.map_add (incA D) (fun a b => RingHom.map_add _ a b),
      Matrix.map_one (incA D) (RingHom.map_zero _) (RingHom.map_one _)]
  have hce := smul_map_incA he (x₀ * y₀ - 1)
  have key : ∀ v : Matrix (Fin n) (Fin n') (AE D),
      e • ((1 : Matrix (Fin n) (Fin n) (AE D)) - (HMul.hMul v (y₀.map (incA D)) -
        finLift (x₀ * y₀ - 1))) =
        HMul.hMul (e • (x₀.map (incA D) - v)) (y₀.map (incA D)) := by
    intro v
    rw [Matrix.smul_mul, Matrix.sub_mul, hXY]
    exact smul_one_sub e _ _ _ hce
  rw [key u, key u', heq, Matrix.mul_assoc]

theorem coset_equation_mul_right_congruent_one_mod_depthIdeal : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ u ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), ∀ u' ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))),
    e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - u) =
      actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - u')) →
    ∃ a₁ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))), ∃ a₂ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))),
      e • ((1 : WO (G.V (.core i)) (G.V (.core i))) - a₁) = actO (G.V (.core i)) (G.V (.core i)) 1 g (e • (1 - a₂)) := by
  intro D _ T L μ0 _ sc G W M _ i _ x₀ hx₀ e he g u hu u' hu' heq
  obtain ⟨-, y₀, hy₀, hc⟩ := hx₀
  have h1 : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by simp
  have hcf : finLift (x₀ * y₀ - 1) ∈
      hatMx (G.modul • homLat (G.Λ (.core i)) (G.Λ (.core i))) :=
    AddSubgroup.subset_closure ⟨1, h1, x₀ * y₀ - 1, hc, rfl⟩
  have hmul : ∀ x ∈ G.modul • homLat (G.latS (.core i)) (G.latT (.core i)),
      x * y₀ ∈ G.modul • homLat (G.Λ (.core i)) (G.Λ (.core i)) := fun x hx => smul_homLat_mul hx hy₀
  refine ⟨_, sub_mem (hatMx_mul y₀ hmul hu) hcf, _, sub_mem (hatMx_mul y₀ hmul hu') hcf, ?_⟩
  rw [actO_one_left] at heq ⊢
  exact core_step he x₀ y₀ _ u u' heq

end GlobalTheory.CosDualStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetEquationMulRightCongruentOneModDepthIdealAlStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_equation_mul_right_congruent_one_mod_depthIdeal_alt : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ u ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), ∀ u' ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))),
    e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - u) =
      actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - u')) →
    ∃ a₁ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))), ∃ a₂ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))),
      e • ((1 : WO (G.V (.core i)) (G.V (.core i))) - a₁) = actO (G.V (.core i)) (G.V (.core i)) 1 g (e • (1 - a₂)) := by
  first | exact @GlobalTheory.CosDualStep.coset_equation_mul_right_congruent_one_mod_depthIdeal | exact GlobalTheory.CosDualStep.coset_equation_mul_right_congruent_one_mod_depthIdeal | (intros; apply GlobalTheory.CosDualStep.coset_equation_mul_right_congruent_one_mod_depthIdeal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetCharConditionIntegralUnitCongruentDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section
namespace GlobalTheory.CosDual

theorem ann_depLat : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
    (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • v) y) = 1) →
    ∀ u ∈ depLat G (.core i), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1 := by
  intro D hq T L μ0 hL sc G W M hM i hi e he y hy h u hu
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have h1 := h (e • u) (hu.2 e he)
  rw [smul_smul, hee, symplO_smul_half _ _ e u y hy] at h1
  exact h1


set_option maxHeartbeats 1000000 in
theorem cosDual : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)),
    (∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u (actO _ _ 1 g⁻¹ y)) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) =
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) (actO _ _ 1 g⁻¹ y))) →
    ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)),
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • (((Lev.finE (G.V (.core i)) g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.modul • G.Λ (.core i)) := by
  intro D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ e he g hyp x hx
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨X, hXdef⟩ : ∃ X : WO (G.pS (.core i)) (G.pT (.core i)), X = e • x₀.map (incA D) := ⟨_, rfl⟩
  have hXh : IsHalf e X := fun a b => by
    simp only [hXdef, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
  obtain ⟨Z, hZdef⟩ : ∃ Z : WO (G.pS (.core i)) (G.pT (.core i)), Z = X - actO (G.pS (.core i)) (G.pT (.core i)) 1 g X := ⟨_, rfl⟩
  have hZ : IsHalf e Z := fun a b => by
    simp only [hZdef, Matrix.sub_apply, mul_sub, hXh a b, half_actO _ _ e g X hXh a b]
  have key : ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • v) y) = 1) →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO _ _ 1 g (e • v)) y) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) Z y) = 1 := by
    intro y hy h1 h2
    have hy' : IsHalf (cA D e) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g⁻¹ y) := half_actO _ _ _ _ _ hy
    have hA := ann_depLat D hq T L μ0 hL sc G W M hM i hi e he y hy h1
    have hB := ann_depLat D hq T L μ0 hL sc G W M hM i hi e he _ hy' (fun v hv => by
      have h3 := h2 v hv
      rw [← GlobalTheory.SymplOInv.symplO_actO D _ _ 1 g (e • v) (actO _ _ 1 g⁻¹ y), actO_inv]
      exact h3)
    have H := hyp y hy hA hB
    rw [← hXdef] at H
    rw [← GlobalTheory.SymplOInv.symplO_actO D _ _ 1 g X (actO _ _ 1 g⁻¹ y), actO_inv] at H
    have hsum : X = Z + actO (G.pS (.core i)) (G.pT (.core i)) 1 g X := by
      rw [hZdef]; abel
    have hs : symplO (G.pS (.core i)) (G.pT (.core i)) X y =
        symplO (G.pS (.core i)) (G.pT (.core i)) Z y +
          symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y := by
      conv_lhs => rw [hsum]
      exact GlobalTheory.LatVac.symplO_add_left _ _ _ _ _
    rw [hs, AddChar.map_add_eq_mul] at H
    generalize hcdef : W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y) = c at H
    have hc : c ≠ 0 := by
      intro h0
      have h5 : W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y) *
          W.ψ (-(symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y)) = 1 := by
        rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
      rw [show W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y) = c from hcdef,
        h0, zero_mul] at h5
      exact zero_ne_one h5
    have H' : (W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) Z y) - 1) * c = 0 := by
      rw [sub_mul, H, one_mul, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 H').resolve_right hc)
  obtain ⟨a, ha, b, hb, hZeq⟩ := GlobalTheory.T.halfPoint_mem_sum_translate_of_annihilator D hq T L μ0 hL sc G W M hM i hi e he g Z hZ key
  have heq : e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - a) =
      actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - -b)) := by
    rw [smul_sub, sub_neg_eq_add, smul_add, actO_add, ← hXdef]
    have h6 : X = Z + actO (G.pS (.core i)) (G.pT (.core i)) 1 g X := by rw [hZdef]; abel
    rw [hZeq] at h6
    conv_lhs => rw [h6]
    abel
  obtain ⟨a₁, h1, a₂, h2, heq2⟩ := GlobalTheory.T.coset_equation_mul_right_congruent_one_mod_depthIdeal_alt D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ e he g a ha (-b) (neg_mem hb) heq
  exact GlobalTheory.T.gridCoreNode_unitReading_integral_congruent D hq T L μ0 hL sc G W M hM i hi e he g a₁ h1 a₂ h2 heq2 x hx

end GlobalTheory.CosDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetCharConditionIntegralUnitCongruentDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetCharCondition_integral_unit_congruent_depth : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)),
    (∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u (actO _ _ 1 g⁻¹ y)) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) =
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) (actO _ _ 1 g⁻¹ y))) →
    ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)),
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • (((Lev.finE (G.V (.core i)) g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.modul • G.Λ (.core i)) := by
  first | exact @GlobalTheory.CosDual.cosDual | exact GlobalTheory.CosDual.cosDual | (intros; apply GlobalTheory.CosDual.cosDual <;> assumption)
end
