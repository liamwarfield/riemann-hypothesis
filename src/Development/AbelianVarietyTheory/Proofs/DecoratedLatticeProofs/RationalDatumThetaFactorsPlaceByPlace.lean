module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoefficientVectorReadingRealRepresentation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardLatticeHalfEqDoubleAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteQuotientAnnihilatorStandardLatticeConjHalf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepRankZeroWittEmbeddingValueAtZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceModelStandardLatticeValuesAreTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceModelStandardLatticeValuesAreTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section
namespace GlobalTheory.LocMod.StdTheta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Fin

variable {D : D7}

theorem symplO_zero_r (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  have h := GlobalTheory.FinPl.ExtZeroLat.symplO_add_right S T x 0 0
  simp only [add_zero] at h
  exact left_eq_add.mp h

theorem symplO_neg_r (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have h := GlobalTheory.FinPl.ExtZeroLat.symplO_add_right S T x y (-y)
  rw [add_neg_cancel, symplO_zero_r] at h
  linear_combination -h

theorem psi_ne_zero' (ψ : AddChar (AF D.host.F) ℂ) (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

def halfGrp (S T : HSp D) (e : AE D) : AddSubgroup (WO S T) where
  carrier := {u | IsHalf e u}
  add_mem' {a b} ha hb := fun i j => by rw [Matrix.add_apply, mul_add, ha i j, hb i j]
  zero_mem' := fun i j => by rw [Matrix.zero_apply, mul_zero]
  neg_mem' {a} ha := fun i j => by rw [Matrix.neg_apply, mul_neg, ha i j]

def heisLin (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) : Module.End ℂ (WO S T → ℂ) where
  toFun := heisO ψ S T w
  map_add' f g := by
    funext x
    simp only [heisO, Pi.add_apply, mul_add]
  map_smul' c f := by
    funext x
    simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def annHalf (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) :
    AddSubgroup (WO S T) where
  carrier := {y | IsHalf (cA D e) y ∧ ∀ x ∈ Λ, IsHalf e x → ψ (symplO S T x y) = 1}
  add_mem' {a b} ha hb := ⟨(halfGrp S T (cA D e)).add_mem ha.1 hb.1, fun x hx hxe => by
    rw [GlobalTheory.FinPl.ExtZeroLat.symplO_add_right, AddChar.map_add_eq_mul, ha.2 x hx hxe, hb.2 x hx hxe, one_mul]⟩
  zero_mem' := ⟨(halfGrp S T (cA D e)).zero_mem, fun x _ _ => by
    rw [symplO_zero_r, AddChar.map_zero_eq_one]⟩
  neg_mem' {a} ha := ⟨(halfGrp S T (cA D e)).neg_mem ha.1, fun x hx hxe => by
    rw [symplO_neg_r, AddChar.map_neg_eq_inv, ha.2 x hx hxe, inv_one]⟩

theorem half_inf_half {e : AE D} (he : e * cA D e = 0) (S T : HSp D) {u : WO S T}
    (h1 : IsHalf e u) (h2 : IsHalf (cA D e) u) : u = 0 := by
  ext i j
  rw [Matrix.zero_apply, ← h1 i j, ← h2 i j, ← mul_assoc, he, zero_mul]

theorem half_div' (S T : HSp D) {e : AE D} {k : ℕ} (hk : 0 < k) {s : WO S T} (hs : IsHalf e s) :
    ∃ t, IsHalf e t ∧ k • t = s := by
  refine ⟨s.map (fun a => algebraMap D.host.F (AE D) (k : D.host.F)⁻¹ * a), fun i j => ?_, ?_⟩
  · simp only [Matrix.map_apply]
    rw [mul_left_comm, hs i j]
  · ext i j
    rw [Matrix.smul_apply, Matrix.map_apply, nsmul_eq_mul, ← mul_assoc]
    have h1 : (k : AE D) * algebraMap D.host.F (AE D) (k : D.host.F)⁻¹ = 1 := by
      rw [show (k : AE D) = algebraMap D.host.F (AE D) (k : D.host.F) by simp, ← map_mul,
        mul_inv_cancel₀ (Nat.cast_ne_zero.2 hk.ne'), map_one]
    rw [h1, one_mul]

theorem nsmul_eq_zero' (S T : HSp D) {k : ℕ} (hk : 0 < k) {t : WO S T} (h : k • t = 0) : t = 0 := by
  have hu : IsUnit (k : AE D) := by
    have e1 : (k : AE D) = algebraMap D.host.F (AE D) (k : D.host.F) := by simp
    rw [e1]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hk.ne')).map _
  ext i j
  have := congrFun (congrFun h i) j
  rw [Matrix.smul_apply, nsmul_eq_mul, Matrix.zero_apply] at this
  rw [Matrix.zero_apply]
  exact (hu.mul_right_eq_zero).1 this

theorem finite_qt' {W : Type*} [AddCommGroup W] {H : AddSubgroup W} {k : ℕ} (R : Finset W)
    (hR : ∀ u ∈ H, ∃ r ∈ R, ∃ v ∈ H, u = r + k • v) : Finite (Four.Qt k H) := by
  classical
  let R' : Finset W := R.filter (· ∈ H)
  let f : R' → Four.Qt k H := fun r => QuotientAddGroup.mk ⟨r.1, (Finset.mem_filter.1 r.2).2⟩
  refine Finite.of_surjective f ?_
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H u =>
    obtain ⟨r, hr, v, hv, huv⟩ := hR u u.2
    have hrH : r ∈ H := by
      have := H.sub_mem u.2 (H.nsmul_mem hv k)
      rwa [huv, add_sub_cancel_right] at this
    refine ⟨⟨r, Finset.mem_filter.2 ⟨hr, hrH⟩⟩, ?_⟩
    apply QuotientAddGroup.eq.2
    rw [AddSubgroup.mem_addSubgroupOf]
    refine Four.mem_smulSub.2 ⟨v, hv, ?_⟩
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [huv]
    abel

theorem isSB_congr {W : Type*} [AddCommGroup W] {L₁ L₂ X : AddSubgroup W} (h : L₁ ⊓ X = L₂ ⊓ X) {Φ : W → ℂ}
    (hΦ : Four.IsSB L₁ X Φ) : Four.IsSB L₂ X Φ := by
  obtain ⟨hs, k, hk, hi, hl⟩ := hΦ
  refine ⟨hs, k, hk, fun u hu t => hi u (h ▸ hu) t, fun t ht => ?_⟩
  have hm : k • t ∈ L₁ ⊓ X := AddSubgroup.mem_inf.2 ⟨hl t ht, X.nsmul_mem (hs t ht) k⟩
  rw [h] at hm
  exact (AddSubgroup.mem_inf.1 hm).1

theorem isSB_of_half {e : AE D} {S T : HSp D} {Λ : AddSubgroup (WO S T)} {Φ : WO S T → ℂ} (h : IsSBHalf e Λ Φ) :
    Four.IsSB Λ (halfGrp S T e) Φ := by
  obtain ⟨hs, k, hk, hi, hl⟩ := h
  exact ⟨hs, k, hk, fun u hu t => hi u (AddSubgroup.mem_inf.1 hu).1 (AddSubgroup.mem_inf.1 hu).2 t, hl⟩

theorem half_of_isSB {e : AE D} {S T : HSp D} {Λ : AddSubgroup (WO S T)} {Φ : WO S T → ℂ}
    (h : Four.IsSB Λ (halfGrp S T e) Φ) : IsSBHalf e Λ Φ := by
  obtain ⟨hs, k, hk, hi, hl⟩ := h
  exact ⟨hs, k, hk, fun u hu hue t => hi u (AddSubgroup.mem_inf.2 ⟨hu, hue⟩) t, hl⟩

open Classical in
theorem theta_of_facts (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (E₂ : AE D) (hE : E₂ * cA D E₂ = 0)
    (hdd : ∀ x : WO S T, IsHalf E₂ x → (∀ y, IsHalf (cA D E₂) y →
      (∀ x' ∈ stdHom S T, IsHalf E₂ x' → ψ (symplO S T x' y) = 1) → ψ (symplO S T x y) = 1) → x ∈ stdHom S T)
    (hfX : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ stdHom S T, IsHalf E₂ u →
      ∃ r ∈ R, ∃ v ∈ stdHom S T, IsHalf E₂ v ∧ u = r + k • v)
    (hfY : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u, IsHalf (cA D E₂) u →
      (∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x u) = 1) →
      ∃ r ∈ R, ∃ v, IsHalf (cA D E₂) v ∧ (∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x v) = 1) ∧ u = r + k • v)
    (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (hf₀ : IsThetaFunO ψ S T f₀)
    (hPM : IsPlaceModel ψ (symplO S T) (heisO ψ S T) E₂ (stdHom S T) 1 f₀ T')
    (Φ : WO S T → ℂ) (hΦ : IsSBHalf E₂ (stdHom S T) Φ) : IsThetaFunO ψ S T (T' Φ) := by
  set Λ := stdHom S T with hΛ
  set X := halfGrp S T E₂ with hX
  set Y := halfGrp S T (cA D E₂) with hY
  set A := annHalf ψ S T E₂ Λ with hA
  set L' := (Λ ⊓ X) ⊔ A with hL'
  have mi := fun {x : WO S T} {H K : AddSubgroup (WO S T)} (h : x ∈ H ⊓ K) => AddSubgroup.mem_inf.1 h
  have hAY : ∀ {y}, y ∈ A → y ∈ Y := fun h => h.1
  have hXY : ∀ {u : WO S T}, u ∈ X → u ∈ Y → u = 0 := fun h1 h2 => half_inf_half hE S T h1 h2

  have hLX : L' ⊓ X = Λ ⊓ X := by
    apply le_antisymm
    · intro z hz
      obtain ⟨hzL, hzX⟩ := mi hz
      obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hzL
      have hbX : b ∈ X := by
        have := X.sub_mem hzX (mi ha).2
        rwa [add_sub_cancel_left] at this
      rw [hXY hbX (hAY hb), add_zero]
      exact ha
    · intro z hz
      exact AddSubgroup.mem_inf.2 ⟨AddSubgroup.mem_sup_left hz, (mi hz).2⟩
  have hLY : L' ⊓ Y = A := by
    apply le_antisymm
    · intro z hz
      obtain ⟨hzL, hzY⟩ := mi hz
      obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hzL
      have haY : a ∈ Y := by
        have := Y.sub_mem hzY (hAY hb)
        rwa [add_sub_cancel_right] at this
      rw [hXY (mi ha).2 haY, zero_add]
      exact hb
    · intro z hz
      exact AddSubgroup.mem_inf.2 ⟨AddSubgroup.mem_sup_right hz, hAY hz⟩
  have hχl : ∀ t t' y : WO S T, ψ (symplO S T (t + t') y) = ψ (symplO S T t y) * ψ (symplO S T t' y) := fun t t' y => by
    rw [GlobalTheory.FinPl.ExtZeroLat.symplO_add_left S T, AddChar.map_add_eq_mul]
  have hχr : ∀ t y y' : WO S T, ψ (symplO S T t (y + y')) = ψ (symplO S T t y) * ψ (symplO S T t y') := fun t y y' => by
    rw [GlobalTheory.FinPl.ExtZeroLat.symplO_add_right S T, AddChar.map_add_eq_mul]
  have hχ0 : ∀ t y : WO S T, ψ (symplO S T t y) ≠ 0 := fun t y => psi_ne_zero' ψ _
  have hLL' : ∀ x ∈ L' ⊓ X, ∀ y ∈ L' ⊓ Y, ψ (symplO S T x y) = 1 := by
    intro x hx y hy
    rw [hLX] at hx
    rw [hLY] at hy
    exact hy.2 x (mi hx).1 (mi hx).2
  have hdX' : ∀ x ∈ X, (∀ y ∈ L' ⊓ Y, ψ (symplO S T x y) = 1) → x ∈ L' := by
    intro x hx h
    have hxΛ : x ∈ Λ := hdd x hx fun y hy hy' => h y (by rw [hLY]; exact ⟨hy, hy'⟩)
    exact AddSubgroup.mem_sup_left (AddSubgroup.mem_inf.2 ⟨hxΛ, hx⟩)
  have hdivX : ∀ k : ℕ, 0 < k → ∀ s ∈ X, ∃ t ∈ X, k • t = s := fun k hk s hs => by
    obtain ⟨t, ht, hts⟩ := half_div' S T hk hs
    exact ⟨t, ht, hts⟩
  have hdivY : ∀ k : ℕ, 0 < k → ∀ s ∈ Y, ∃ t ∈ Y, k • t = s := fun k hk s hs => by
    obtain ⟨t, ht, hts⟩ := half_div' S T hk hs
    exact ⟨t, ht, hts⟩
  have hfinX : ∀ k, 0 < k → Finite (Four.Qt k (L' ⊓ X)) := fun k hk => by
    rw [hLX]
    obtain ⟨R, hR⟩ := hfX k hk
    exact finite_qt' R fun u hu => by
      obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
      exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩
  have hfinY : ∀ k, 0 < k → Finite (Four.Qt k (L' ⊓ Y)) := fun k hk => by
    rw [hLY]
    obtain ⟨R, hR⟩ := hfY k hk
    exact finite_qt' R fun u hu => by
      obtain ⟨r, hr, v, hv, hv', huv⟩ := hR u hu.1 hu.2
      exact ⟨r, hr, v, ⟨hv, hv'⟩, huv⟩
  have htf : ∀ k : ℕ, 0 < k → ∀ t : WO S T, k • t = 0 → t = 0 := fun k hk t h => nsmul_eq_zero' S T hk h
  have hSB : ∀ Φ', Four.IsSB L' X Φ' → IsSBHalf E₂ Λ Φ' := fun Φ' h =>
    half_of_isSB (isSB_congr hLX h)
  have htr : ∀ Φ', Four.IsSB L' X Φ' → ∀ x ∈ X, T' (fun t => Φ' (t + x)) = heisLin ψ S T x (T' Φ') :=
    fun Φ' h x hx => hPM.trans Φ' (hSB Φ' h) x hx
  have hmo : ∀ Φ', Four.IsSB L' X Φ' → ∀ y ∈ Y,
      T' (fun t => ψ (symplO S T t y) * Φ' t) = heisLin ψ S T y (T' Φ') :=
    fun Φ' h y hy => hPM.modul Φ' (hSB Φ' h) y hy
  have hva : T' (fun t => if t ∈ L' ∧ t ∈ X then (1 : ℂ) else 0) = f₀ := by
    have h := hPM.vac
    rw [one_smul] at h
    rw [← h]
    congr 1
    funext t
    have hiff : (t ∈ L' ∧ t ∈ X) ↔ (t ∈ Λ ∧ IsHalf E₂ t) := by
      constructor
      · intro h'
        have := AddSubgroup.mem_inf.2 h'
        rw [hLX] at this
        exact mi this
      · intro h'
        have : t ∈ Λ ⊓ X := AddSubgroup.mem_inf.2 h'
        rw [← hLX] at this
        exact mi this
    unfold halfInd
    by_cases ht : t ∈ Λ ∧ IsHalf E₂ t
    · rw [if_pos (hiff.2 ht), if_pos ht]
    · rw [if_neg (fun h' => ht (hiff.1 h')), if_neg ht]
  have hspan := Four.model_mem_span hχl hχr hχ0 hLL' hdX' hdivX hdivY hfinX hfinY htf T' htr hmo hva
    (isSB_congr hLX.symm (isSB_of_half hΦ))
  have hzero : IsThetaFunO ψ S T 0 := by
    have := Formalism.IndefR.Eqv.thetaO_smul (0 : ℂ) hf₀
    rwa [zero_smul] at this
  generalize T' Φ = v₀ at hspan ⊢
  induction hspan using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, -, y, -, rfl⟩ := hv
    exact GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀ y) a
  | zero => exact hzero
  | add v w _ _ hv hw => exact Formalism.IndefR.Eqv.thetaO_add hv hw
  | smul c v _ hv => exact Formalism.IndefR.Eqv.thetaO_smul c hv

theorem theta_placeModel_std : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) E₂ (stdHom S T) 1 f₀ T' → ∀ Φ, IsSBHalf E₂ (stdHom S T) Φ → IsThetaFunO ψ S T (T' Φ) := by
  intro D ψ hψ S T Q E₂ hE f₀ T' hf₀ _ hPM Φ hΦ
  exact theta_of_facts ψ hψ S T E₂ hE.2 (GlobalTheory.T.standard_lattice_half_eq_double_annihilator D ψ hψ S T Q E₂ hE) (GlobalTheory.T.exists_finite_reps_half_standardHom_mod_nsmul D S T Q E₂ hE)
    (GlobalTheory.T.finite_quotient_annihilator_standardLattice_conjHalf D ψ hψ S T Q E₂ hE) f₀ T' hf₀ hPM Φ hΦ

end GlobalTheory.LocMod.StdTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceModelStandardLatticeValuesAreThetaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeModel_standardLattice_values_are_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) E₂ (stdHom S T) 1 f₀ T' → ∀ Φ, IsSBHalf E₂ (stdHom S T) Φ → IsThetaFunO ψ S T (T' Φ) := by
  first | exact @GlobalTheory.LocMod.StdTheta.theta_placeModel_std | exact GlobalTheory.LocMod.StdTheta.theta_placeModel_std | (intros; apply GlobalTheory.LocMod.StdTheta.theta_placeModel_std <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumThetaFactorsPlaceByPlace
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
namespace GlobalTheory.LocMod

theorem pi_e_self {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : p.π p.e = 1 := by
  have h := p.ι_π 1
  rw [map_one, mul_one] at h
  rw [← h, p.π_ι]

theorem pi_eq_zero_of {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {e : AE D} (h : e * p.e = 0) : p.π e = 0 := by
  have := congrArg p.π h
  rwa [map_mul, pi_e_self, mul_one, map_zero] at this

theorem up_down_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (t : WO S T) :
    p.up FS FT (p.down FS FT t) = t.map (fun x => p.e * x) := by
  unfold Place.up Place.down
  have hM : FT.β * (FT.γ * (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * FS.β) * FS.γ =
      (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
  rw [hM]
  ext i j
  simp only [Matrix.map_apply, p.ι_π]

theorem ratDatum_factor : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → DenseRange p.pr → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → IsIdemSum (e + p.e) (@insert _ _ (@Finset.instInsert _ (Classical.decEq _)) PP P) → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → ∀ (Ξ Ξ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (Ξk : Matrix Y Y' k → ℂ), Ξk ∈ SB (Matrix Y Y' k) → (∀ γ, Ξ' γ = Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) → ∀ c, p.IsCombAt ψ FS FT c Ξk → ∀ f₀ f f', IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → IsRatDatum ψ S T e Ξ f₀ f → IsRatDatum ψ S T (e + p.e) Ξ' f₀ f' → f' = comb ψ S T c f := by
  intro D k _ _ _ _ p ψ hψ _hdense S T Y Y' _ _ _ _ FS FT P PP e hPP hIdemAt hE hE' hstd Ξ Ξ' Ξk hΞk hΞ' c hc f₀ f f' hf₀ hvac hf hf'
  obtain ⟨Φ, hΦSB, hΦrat, hθ⟩ := hf
  obtain ⟨Φ', hΦ'SB, hΦ'rat, hθ'⟩ := hf'
  obtain ⟨T', hT'⟩ := hθ'.1
  have hf'T : f' = T' Φ' := hθ'.2 T' hT'
  have horth : e * p.e = 0 := GlobalTheory.T.splitPlaceIdempotent_mul_idemSum_eq_zero_of_not_mem D k p P PP e hPP hIdemAt hE
  have hstabp := GlobalTheory.T.standardLatticeHomCompletion_stable_splitIdempotent D S T p.e p.split
  have hθT' := GlobalTheory.T.placeModel_standardLattice_values_are_theta D ψ hψ S T _ (e + p.e) hE' f₀ T' hf₀ hvac hT'
  have hsb := GlobalTheory.T.isSchwartzBruhat_tensor_half_add_placeIdempotent D k p S T Y Y' FS FT e horth hstd hstabp Φ hΦSB
  have hmodel := GlobalTheory.T.isLocalModel_tensorWithHalfFunction D k p ψ S T Y Y' FS FT e horth Φ hΦSB.1 f₀ T' hT' hθT' hsb
  have hvacm := GlobalTheory.T.isPlaceModel_tensorIntegralIndicator D k p ψ S T Y Y' FS FT e horth hstd hstabp f₀ T' hT'
    (fun Φ₁ h₁ => GlobalTheory.T.isSchwartzBruhat_tensor_half_add_placeIdempotent D k p S T Y Y' FS FT e horth hstd hstabp Φ₁ h₁ _ (GlobalTheory.T.splitPlaceIntegralMatrixIndicator_mem_schwartzBruhat k Y Y'))
  have hfT : f = T' (p.tensorOne FS FT Φ) := hθ.2 _ hvacm
  have hπe : p.π e = 0 := pi_eq_zero_of p horth
  have hpe2 : p.e * p.e = p.e := p.split.1
  have hid : Φ' = p.tensorAt FS FT Φ Ξk := by
    refine GlobalTheory.T.schwartzBruhat_half_eq_of_eq_on_rational D S T _ (e + p.e) hE' Φ' _ hΦ'SB (hsb Ξk hΞk) fun γ => ?_
    rw [hΦ'rat, hΞ']
    have hd : p.down FS FT (γ.map fun a => (e + p.e) * incA D a) = FT.γ * γ.map p.pr * FS.β := by
      unfold Place.down
      congr 2
      ext i j
      simp only [Matrix.map_apply, map_mul, map_add (f := _), hπe, pi_e_self, zero_add, one_mul, Place.pr]
    have hs : (γ.map fun a => (e + p.e) * incA D a) - p.up FS FT (p.down FS FT (γ.map fun a => (e + p.e) * incA D a)) =
        γ.map fun a => e * incA D a := by
      rw [up_down_eq]
      ext i j
      simp only [Matrix.sub_apply, Matrix.map_apply]
      have h2 : p.e * e = 0 := by rw [mul_comm]; exact horth
      linear_combination (-(incA D (γ i j))) * h2 + (-(incA D (γ i j))) * hpe2
    simp only [Place.tensorAt]
    rw [hs, hd, hΦrat]
  have key := hc.2 (T' ∘ₗ p.tensorL FS FT Φ) hmodel ⟨Place.intInd Y Y', GlobalTheory.T.splitPlaceIntegralMatrixIndicator_mem_schwartzBruhat k Y Y'⟩ ⟨Ξk, hΞk⟩ rfl rfl
  rw [hf'T, hid, hfT]
  simpa only [LinearMap.comp_apply, Place.tensorL_apply, Place.tensorOne_apply] using key

end GlobalTheory.LocMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumThetaFactorsPlaceByPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalDatum_theta_factors_placeByPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → DenseRange p.pr → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → IsIdemSum (e + p.e) (@insert _ _ (@Finset.instInsert _ (Classical.decEq _)) PP P) → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → ∀ (Ξ Ξ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (Ξk : Matrix Y Y' k → ℂ), Ξk ∈ SB (Matrix Y Y' k) → (∀ γ, Ξ' γ = Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) → ∀ c, p.IsCombAt ψ FS FT c Ξk → ∀ f₀ f f', IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → IsRatDatum ψ S T e Ξ f₀ f → IsRatDatum ψ S T (e + p.e) Ξ' f₀ f' → f' = comb ψ S T c f := by
  first | exact @GlobalTheory.LocMod.ratDatum_factor | exact GlobalTheory.LocMod.ratDatum_factor | (intros; apply GlobalTheory.LocMod.ratDatum_factor <;> assumption)
end
