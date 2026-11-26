module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SmulFinsum
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum

namespace Formalism.IndefR.Fin.LevelGroupLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem mt_mul' (V : HSp D) (a b : GA D V) : Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one' (V : HSp D) : Formalism.L2.Theta.mt V (1 : GA D V) = 1 := by
  simp [Formalism.L2.Theta.mt, map_one, Units.val_one]

theorem actO_eq {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h x = HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h) x) (Formalism.L2.Theta.mt S g⁻¹) := rfl

theorem actO_actO {S T : HSp D} (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  rw [actO_eq, actO_eq, actO_eq, _root_.mul_inv_rev, mt_mul', mt_mul']
  simp only [Matrix.mul_assoc]

theorem actO_one {S T : HSp D} (x : WO S T) : actO S T 1 1 x = x := by
  rw [actO_eq, inv_one, mt_one', mt_one', Matrix.one_mul, Matrix.mul_one]

theorem actO_add {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  rw [actO_eq, actO_eq, actO_eq, Matrix.mul_add, Matrix.add_mul]

theorem actO_nsmul {S T : HSp D} (g : GA D S) (h : GA D T) (k : ℕ) (x : WO S T) :
    actO S T g h (k • x) = k • actO S T g h x := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, actO_eq, Matrix.mul_zero, Matrix.zero_mul]
  | succ k ih => rw [succ_nsmul, actO_add, ih, succ_nsmul]

theorem isHalf_mul_mul {e : AE D} {a b c : ℕ} (M : Matrix (Fin a) (Fin b) (AE D)) (x : Matrix (Fin b) (Fin c) (AE D))
    (N : Matrix (Fin c) (Fin c) (AE D)) (hx : IsHalf e x) : IsHalf e (M * x * N) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hx k l]
  ring

theorem isHalf_actO {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) (x : WO S T) :
    IsHalf e (actO S T g h x) ↔ IsHalf e x := by
  constructor
  · intro hx
    have : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
      rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]
    rw [← this]
    exact isHalf_mul_mul _ _ _ hx
  · intro hx
    exact isHalf_mul_mul _ _ _ hx

def actPull {S T : HSp D} (p : GA D S × GA D T) (Φ : WO S T → ℂ) : WO S T → ℂ :=
  fun t => Φ (actO S T p.1⁻¹ p.2⁻¹ t)

end Formalism.IndefR.Fin.LevelGroupLemmas

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.StepVecThetaLem
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StepVecThetaSD (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank) (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (f₀ f : WO S T → ℂ),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT →
    IsStepVecOf ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) βS βT LS χj Q ξ f₀ f →
    IsThetaFunO ψ S T f

def ThPVecThetaSD (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (f₀ f : WO S T → ℂ),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT →
    IsThPVecOf ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) βS βT Pg Q ξ f₀ f →
    IsThetaFunO ψ S T f

def VecThetaSD (D : D7) : Prop := StepVecThetaSD D ∧ ThPVecThetaSD D

end Formalism.IndefR.Fin
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceHeis
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

def heisL (w : WO S T) : Module.End ℂ (WO S T → ℂ) where
  toFun := heisO ψ S T w
  map_add' f g := by
    funext x
    simp only [heisO, Pi.add_apply, mul_add]
  map_smul' c f := by
    funext x
    simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem heisL_apply (w : WO S T) (f : WO S T → ℂ) : heisL ψ S T w f = heisO ψ S T w f := rfl

def halfSub (e : AE D) : AddSubgroup (WO S T) where
  carrier := {u | IsHalf e u}
  add_mem' {a b} ha hb := fun i j => by rw [Matrix.add_apply, mul_add, ha i j, hb i j]
  zero_mem' := fun i j => by rw [Matrix.zero_apply, mul_zero]
  neg_mem' {a} ha := fun i j => by rw [Matrix.neg_apply, mul_neg, ha i j]

theorem heisO_heisO (w w' : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w (heisO ψ S T w' f) = ψ (symplOH S T w w') • heisO ψ S T (w + w') f := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  rw [symplOH_add_left S T x w w', symplOH_add_right S T x w w', AddChar.map_add_eq_mul,
    AddChar.map_add_eq_mul, add_assoc x w w']
  ring

theorem psi_ne_zero (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem symplO_half {e : AE D} (he : e * cA D e = 0) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    symplO S T x y = 0 := by
  have hz : ∀ a b c d, incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a = 0 := by
    intro a b c d
    rw [← hy c b, ← hx d a, map_mul]
    linear_combination (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) * he
  simp [symplO, hO, hz]

theorem symplOH_half {e : AE D} (he : e * cA D e = 0) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    symplOH S T x y = 0 := by
  rw [symplOH, symplO_half S T he hx hy, mul_zero]

theorem heisL_add_half {e : AE D} (he : e * cA D e = 0) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    heisL ψ S T (x + y) = heisL ψ S T x * heisL ψ S T y := by
  ext1 f
  rw [Module.End.mul_apply, heisL_apply, heisL_apply, heisL_apply, heisO_heisO, symplOH_half S T he hx hy,
    AddChar.map_zero_eq_one, one_smul]

theorem heisL_comm (x y : WO S T) :
    heisL ψ S T x * heisL ψ S T y = ψ (symplO S T x y) • (heisL ψ S T y * heisL ψ S T x) := by
  ext1 f
  simp only [Module.End.mul_apply, LinearMap.smul_apply, heisL_apply]
  rw [heisO_heisO, heisO_heisO, smul_smul, add_comm y x, symplOH_swap S T x y, ← symplOH_two S T x y,
    ← AddChar.map_add_eq_mul, show symplOH S T x y + symplOH S T x y + -symplOH S T x y = symplOH S T x y by abel]

theorem cA_half_orth {e : AE D} (he : e * cA D e = 0) : cA D e * cA D (cA D e) = 0 := by
  rw [cA_cA, mul_comm, he]

end Formalism.IndefR.Fin

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplit
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {R : Ranks}

def alphaH (H : Host R) : H.E := (1 + H.sqrtMinusD) / 2

theorem alphaH_sq (H : Host R) :
    alphaH H * (alphaH H - 1) = -(((H.d + 1) / 4 : ℕ) : H.E) := by
  have hd16 : H.d % 16 = 7 := H.hyp.2.2.2.1
  have hb : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq
  have h4 : ((H.d + 1) / 4 : ℕ) * 4 = H.d + 1 := by omega
  have h4' : ((((H.d + 1) / 4 : ℕ) : H.E)) * 4 = (H.d : H.E) + 1 := by exact_mod_cast h4
  unfold alphaH
  linear_combination (1 / 4 : H.E) * hb + (1 / 4 : H.E) * h4'

theorem alphaH_integral (H : Host R) : IsIntegral ℤ (alphaH H) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((H.d + 1) / 4 : ℕ) : ℤ), by monicity!, ?_⟩
  have h := alphaH_sq H
  rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    algebraMap_int_eq, eq_intCast, Int.cast_natCast]
  linear_combination h

theorem star_alphaH (H : Host R) : (letI := H.cmStar; star (alphaH H)) = 1 - alphaH H := by
  rw [Formalism.BasicNotions.Examples₂.star_eq_conj]
  unfold alphaH
  rw [map_div₀, map_add (f := _), map_one, Formalism.MainNotions.UnusedSlot33.HK.conj_b]
  have h2 : H.conj (2 : H.E) = 2 := map_ofNat _ 2
  rw [h2]
  ring

theorem twoSplits (D : D7) : TwoSplits D := by
  intro P h2 hconj
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E a = alphaH D.host :=
    ⟨⟨alphaH D.host, alphaH_integral D.host⟩, rfl⟩
  have inj := FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
  have coe : ∀ x : 𝓞 D.host.E, (x : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E x := fun _ => rfl
  have hP := P.isPrime
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hprod : a * (a - 1) ∈ P.asIdeal := by
    have heven : ((D.host.d + 1) / 4 : ℕ) = 2 * (((D.host.d + 1) / 4 : ℕ) / 2) := by omega
    have hk : ((((D.host.d + 1) / 4 : ℕ) : D.host.E)) = 2 * ((((D.host.d + 1) / 4 / 2 : ℕ) : D.host.E)) := by
      conv_lhs => rw [heven]
      push_cast; ring
    have he : a * (a - 1) = 2 * (-((((D.host.d + 1) / 4 / 2 : ℕ) : 𝓞 D.host.E))) := by
      apply inj
      have h := alphaH_sq D.host
      rw [hk] at h
      simp only [map_mul, map_sub, map_one, map_neg, map_natCast, map_ofNat, ha]
      linear_combination h
    rw [he]
    exact P.asIdeal.mul_mem_right _ h2
  have hstar : ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal →
      ∃ c' ∈ P.asIdeal, algebraMap (𝓞 D.host.E) D.host.E c' = star (algebraMap (𝓞 D.host.E) D.host.E x) := hconj
  have hsa := star_alphaH D.host
  rcases hP.mem_or_mem hprod with hm | hm
  · obtain ⟨c', hc', hc'e⟩ := hstar a hm
    have h1 : a + c' = 1 := by
      apply inj
      rw [map_add (f := _), map_one, hc'e, ha, hsa]; ring
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ P.asIdeal.add_mem hm hc'))
  · obtain ⟨c', hc', hc'e⟩ := hstar _ hm
    have h1 : -c' - (a - 1) = 1 := by
      apply inj
      rw [map_sub, map_neg, map_sub, map_one, hc'e, map_sub, map_one, star_sub, star_one, ha, hsa]; ring
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ P.asIdeal.sub_mem (P.asIdeal.neg_mem hc') hm))

end Formalism.IndefR.Fin

end
end
