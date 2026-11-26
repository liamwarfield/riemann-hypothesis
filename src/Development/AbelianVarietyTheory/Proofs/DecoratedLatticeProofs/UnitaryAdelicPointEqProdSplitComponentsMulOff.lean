module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataLocalRelation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiTTransport
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoprimeScalingIdealValuationLe
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointEqProdSplitComponentsMulOff
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointEqProdSplitComponentsMulOff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LocProd

variable {D : D7}

theorem mem_congGrp_entries (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, (Formalism.L2.Theta.mt V g - 1) i j ∈ I := by
  rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one]
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
  change ((matHom V g).1.map (Ideal.Quotient.mk I)) i j = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j ↔ _
  rw [Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, map_one]
    rfl
  · simp only [Matrix.one_apply_ne hij, map_zero]
    rfl

theorem congGrp_mono (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J := fun g hg =>
  (mem_congGrp_entries V J g).2 fun i j => h ((mem_congGrp_entries V I g).1 hg i j)

theorem idAt_le_idOff (P P' : Pl D → Prop) (h : ∀ w, P w → ¬ P' w) : idAt D P ≤ idOff D P' := by
  intro a ha
  have h2 := (Submodule.mem_inf.1 ha).2
  rw [Submodule.mem_iInf] at h2
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]
  intro w hw
  exact h2 ⟨w, fun h' => h w h' hw⟩

theorem grpAt_le_grpOff' (V : HSp D) (P P' : Pl D → Prop) (h : ∀ w, P w → ¬ P' w) : grpAt V P ≤ grpOff V P' :=
  congGrp_mono V (idAt_le_idOff P P' h)

theorem mem_idOff_of_forall (P : Pl D → Prop) (a : AE D) (h : ∀ w, P w → a ∈ idOff D (· = w)) : a ∈ idOff D P := by
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall] at h ⊢
  intro w hw
  exact h w hw w rfl

theorem mem_grpOff_of_forall (V : HSp D) (P : Pl D → Prop) (g : GA D V) (h : ∀ w, P w → g ∈ grpOff V (· = w)) :
    g ∈ grpOff V P := by
  unfold grpOff
  rw [mem_congGrp_entries]
  intro i j
  exact mem_idOff_of_forall P _ fun w hw => (mem_congGrp_entries V _ g).1 (h w hw) i j

theorem map_list_prod_eq_one {ι G H : Type*} [Monoid G] [Monoid H] (φ : G →* H) (f : ι → G) :
    ∀ J : List ι, (∀ i ∈ J, φ (f i) = 1) → φ (J.map f).prod = 1
  | [], _ => by simp
  | a :: J, h => by
    rw [List.map_cons, List.prod_cons, map_mul, h a List.mem_cons_self,
      map_list_prod_eq_one φ f J fun i hi => h i (List.mem_cons_of_mem a hi), one_mul]

theorem map_list_prod_single {ι G H : Type*} [Monoid G] [Monoid H] (φ : G →* H) (f : ι → G) (j : ι)
    (h1 : ∀ i, i ≠ j → φ (f i) = 1) : ∀ J : List ι, J.Nodup → j ∈ J → φ (J.map f).prod = φ (f j)
  | [], _, hj => absurd hj List.not_mem_nil
  | a :: J, hn, hj => by
    have ha : a ∉ J := List.Nodup.notMem hn
    have hn' : J.Nodup := List.Nodup.of_cons hn
    rw [List.map_cons, List.prod_cons, map_mul]
    by_cases haj : a = j
    · subst haj
      rw [map_list_prod_eq_one φ f J fun i hi => h1 i fun e => ha (e ▸ hi), mul_one]
    · have hjJ : j ∈ J := by
        rcases List.mem_cons.1 hj with e | e
        · exact absurd e.symm haj
        · exact e
      rw [h1 a haj, one_mul, map_list_prod_single φ f j h1 J hn' hjJ]

theorem eq_prod_gl_mul_off : ∀ (D : D7) (S : HSp D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n), Function.Injective (fun i => (p i).v) → ∀ J : List ι, J.Nodup → (∀ i, i ∈ J) → ∀ κ : GA D S, ∃ g : ι → GL n k, (∀ i, κ * ((β i).gl (g i))⁻¹ ∈ grpOff S (· = (p i).v)) ∧ ∃ κ' ∈ grpOff S (fun x => ∃ i, x = (p i).v), κ = (J.map fun i => (β i).gl (g i)).prod * κ' := by
  intro D S k _ _ _ _ ι p n _ _ β hinj J hJ hall κ
  have hloc := fun i => ((GlobalTheory.FinPl.localComponents D (· = (p i).v)).2 S).1 κ
  have hcomm := fun i => ((GlobalTheory.FinPl.localComponents D (· = (p i).v)).2 S).2.1
  choose x hx y hy hxy using hloc
  have hfr := fun i => ((GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) S n (β i)).1 (x i)).1 (hx i)
  choose g hg using hfr
  have hglAt : ∀ i, (β i).gl (g i) ∈ grpAt S (· = (p i).v) := fun i =>
    ((GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) S n (β i)).1 _).2 ⟨g i, rfl⟩
  have key : ∀ i, κ * ((β i).gl (g i))⁻¹ ∈ grpOff S (· = (p i).v) := by
    intro i
    rw [← hg i, hxy i, hcomm i (x i) (hx i) (y i) (hy i), mul_assoc, mul_inv_cancel, mul_one]
    exact hy i
  refine ⟨g, key, (J.map fun i => (β i).gl (g i)).prod⁻¹ * κ, ?_, (mul_inv_cancel_left _ _).symm⟩
  apply mem_grpOff_of_forall
  rintro w ⟨j, rfl⟩
  let φ := (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (idOff D (· = (p j).v)))).comp (matHom S)
  have hker : ∀ h, h ∈ grpOff S (· = (p j).v) ↔ φ h = 1 := fun h => MonoidHom.mem_ker
  have hκ : φ κ = φ ((β j).gl (g j)) := by
    have := (hker _).1 (key j)
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    exact this
  have h1 : ∀ i, i ≠ j → φ ((β i).gl (g i)) = 1 := fun i hij =>
    (hker _).1 (grpAt_le_grpOff' S _ _ (fun w hw hw' => hij (hinj (hw.symm.trans hw'))) (hglAt i))
  rw [hker, map_mul, map_inv, map_list_prod_single φ (fun i => (β i).gl (g i)) j h1 J hJ (hall j), hκ, inv_mul_cancel]

end GlobalTheory.FinPl.LocProd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointEqProdSplitComponentsMulOffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicPoint_eq_prod_splitComponents_mul_off : ∀ (D : D7) (S : HSp D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n), Function.Injective (fun i => (p i).v) → ∀ J : List ι, J.Nodup → (∀ i, i ∈ J) → ∀ κ : GA D S, ∃ g : ι → GL n k, (∀ i, κ * ((β i).gl (g i))⁻¹ ∈ grpOff S (· = (p i).v)) ∧ ∃ κ' ∈ grpOff S (fun x => ∃ i, x = (p i).v), κ = (J.map fun i => (β i).gl (g i)).prod * κ' := by
  first | exact @GlobalTheory.FinPl.LocProd.eq_prod_gl_mul_off | exact GlobalTheory.FinPl.LocProd.eq_prod_gl_mul_off | (intros; apply GlobalTheory.FinPl.LocProd.eq_prod_gl_mul_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceModelRestrictedTensorFixedHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceModelRestrictedTensorFixedHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.FinPl.PutIn.Factor

variable {D : D7}

theorem half_nsmul {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (k : ℕ) : IsHalf e (k • x) := fun i j => by
  have h := hx i j
  simp only [Matrix.smul_apply, nsmul_eq_mul]
  linear_combination (k : AE D) * h

theorem isSBHalf_of_half_eq {S T : HSp D} {b : AE D} {Λ Λ' : AddSubgroup (WO S T)} {Ψ : WO S T → ℂ}
    (hΛ : ∀ t, IsHalf b t → (t ∈ Λ' ↔ t ∈ Λ)) (hΨ : IsSBHalf b Λ' Ψ) : IsSBHalf b Λ Ψ := by
  obtain ⟨hsupp, k, hk, hinv, hfin⟩ := hΨ
  refine ⟨hsupp, k, hk, fun u hu hub t => hinv u ((hΛ u hub).2 hu) hub t, fun t ht => ?_⟩
  exact (hΛ _ (half_nsmul (hsupp t ht) k)).1 (hfin t ht)

theorem half_smul_self {m n : ℕ} {b : AE D} {x : Mx D m n} (hx : IsHalf b x) : b • x = x := by
  ext i j; exact hx i j

theorem half_of_idem {m n : ℕ} {b : AE D} (hb : b * b = b) (t : Mx D m n) : IsHalf b (b • t) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  linear_combination (t i j) * hb

theorem isSBHalf_tens {S T : HSp D} {a b : AE D} {Λ : AddSubgroup (WO S T)} {Φ Ψ : WO S T → ℂ}
    (hab : a * b = 0) (hb : b * b = b) (hbΛ : ∀ u ∈ Λ, b • u ∈ Λ) (hΦ : IsSBHalf a Λ Φ) (hΨ : IsSBHalf b Λ Ψ) :
    IsSBHalf (a + b) Λ (tens b Φ Ψ) := by
  obtain ⟨sΦ, kΦ, hkΦ, iΦ, fΦ⟩ := hΦ
  obtain ⟨sΨ, kΨ, hkΨ, iΨ, fΨ⟩ := hΨ
  have hne : ∀ t, tens b Φ Ψ t ≠ 0 → Φ (t - b • t) ≠ 0 ∧ Ψ (b • t) ≠ 0 := fun t ht => by
    rw [tens_apply] at ht
    exact ⟨left_ne_zero_of_mul ht, right_ne_zero_of_mul ht⟩
  refine ⟨fun t ht => ?_, kΦ * kΨ, Nat.mul_pos hkΦ hkΨ, fun u hu hua t => ?_, fun t ht => ?_⟩
  · obtain ⟨h1, -⟩ := hne t ht
    intro i j
    have h := sΦ _ h1 i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    linear_combination h + (t i j) * hab
  · have hbu : b • u ∈ Λ := hbΛ u hu
    have hsub : u - b • u ∈ Λ := Λ.sub_mem hu hbu
    have hau : IsHalf a (u - b • u) := fun i j => by
      have e1 := hua i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      linear_combination e1 - (u i j) * hab - (u i j) * hb + (u i j) * hb
    have hA : (t + (kΦ * kΨ) • u) - b • (t + (kΦ * kΨ) • u) = (t - b • t) + kΦ • (kΨ • (u - b • u)) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
      ring
    have hB : b • (t + (kΦ * kΨ) • u) = b • t + kΨ • (kΦ • (b • u)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [tens_apply, tens_apply, hA, hB,
      iΦ _ (AddSubgroup.nsmul_mem Λ hsub kΨ) (half_nsmul hau kΨ),
      iΨ _ (AddSubgroup.nsmul_mem Λ hbu kΦ) (half_nsmul (half_of_idem hb u) kΦ)]
  · obtain ⟨h1, h2⟩ := hne t ht
    have hC : (kΦ * kΨ) • t = kΨ • (kΦ • (t - b • t)) + kΦ • (kΨ • (b • t)) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [hC]
    exact Λ.add_mem (AddSubgroup.nsmul_mem Λ (fΦ _ h1) kΨ) (AddSubgroup.nsmul_mem Λ (fΨ _ h2) kΦ)


open GlobalTheory.LocMod.TensorModel in
theorem isPlaceModel_tensR : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AE D) (Λ Λ' : AddSubgroup (WO S T)) (Φ f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → (∀ t, IsHalf b t → (t ∈ Λ' ↔ t ∈ Λ)) → IsSBHalf a Λ Φ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ Tm → IsPlaceModel ψ (symplO S T) (heisO ψ S T) b Λ' 1 (Tm (GlobalTheory.FinPl.PutIn.tens b Φ (halfInd b Λ))) (Tm ∘ₗ GlobalTheory.FinPl.PutIn.tensR b Φ) := by
  intro D ψ S T a b Λ Λ' Φ f₀ Tm hab hb hbΛ hΛ hΦ hP
  refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
  · have hΨ' := isSBHalf_of_half_eq hΛ hΨ
    have key : tens b Φ (fun t => Ψ (t + x)) = fun t => tens b Φ Ψ (t + x) := by
      funext t
      simp only [tens_apply]
      rw [smul_add, half_smul_self hx, add_sub_add_right_eq_sub]
    simp only [LinearMap.comp_apply, tensR_apply]
    rw [key]
    exact hP.trans _ (isSBHalf_tens hab hb hbΛ hΦ hΨ') x (half_sum hab hx)
  · have hΨ' := isSBHalf_of_half_eq hΛ hΨ
    have key : tens b Φ (fun t => ψ (symplO S T t y) * Ψ t) = fun t => ψ (symplO S T t y) * tens b Φ Ψ t := by
      funext t
      simp only [tens_apply]
      by_cases h0 : Φ (t - b • t) = 0
      · rw [h0]; ring
      · have e1 : symplO S T t y = symplO S T (t - b • t) y + symplO S T (b • t) y := by
          rw [← symplO_add_left', sub_add_cancel]
        rw [e1, symplO_half_zero hab (hΦ.1 _ h0) hy, zero_add]
        ring
    simp only [LinearMap.comp_apply, tensR_apply]
    rw [key]
    exact hP.modul _ (isSBHalf_tens hab hb hbΛ hΦ hΨ') y (half_sum_cA hab hy)
  · have hind : halfInd b Λ' = halfInd b Λ := by
      funext t
      unfold halfInd
      have hiff : (t ∈ Λ' ∧ IsHalf b t) ↔ (t ∈ Λ ∧ IsHalf b t) :=
        ⟨fun h => ⟨(hΛ t h.2).1 h.1, h.2⟩, fun h => ⟨(hΛ t h.2).2 h.1, h.2⟩⟩
      by_cases h : t ∈ Λ ∧ IsHalf b t
      · rw [if_pos (hiff.2 h), if_pos h]
      · rw [if_neg (mt hiff.1 h), if_neg h]
    rw [one_smul, hind]
    rfl

end GlobalTheory.FinPl.PutIn.Factor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceModelRestrictedTensorFixedHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_model_restricted_tensor_fixed_half : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AE D) (Λ Λ' : AddSubgroup (WO S T)) (Φ f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → (∀ t, IsHalf b t → (t ∈ Λ' ↔ t ∈ Λ)) → IsSBHalf a Λ Φ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ Tm → IsPlaceModel ψ (symplO S T) (heisO ψ S T) b Λ' 1 (Tm (GlobalTheory.FinPl.PutIn.tens b Φ (halfInd b Λ))) (Tm ∘ₗ GlobalTheory.FinPl.PutIn.tensR b Φ) := by
  first | exact @GlobalTheory.FinPl.PutIn.Factor.isPlaceModel_tensR | exact GlobalTheory.FinPl.PutIn.Factor.isPlaceModel_tensR | (intros; apply GlobalTheory.FinPl.PutIn.Factor.isPlaceModel_tensR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselJacobiKernelLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselJacobiKernelLaws
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.UnfKer

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem zEll_rat (T : HSp D) (ρ : ℕ) (z : Fin T.rank → D.host.E) : zEll T ρ z ∈ ratMx D T.rank ρ := by
  refine ⟨vecMulVec z (fun i : Fin ρ => if i.1 + 1 = ρ then (1 : D.host.E) else 0), ?_⟩
  rw [zEll, GlobalTheory.CharLaws.ell_eq]
  ext i j
  change incA D (_ * _) = _
  rw [map_mul]; rfl

theorem incAdj_rat {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) {y : Mx D S.rank ρ}
    (hy : y ∈ ratMx D S.rank ρ) : d.incAdj S y ∈ ratMx D T.rank S.rank := by
  rw [d.incAdj_apply, d.incY_apply]
  exact ratMx_mul (rat_mem _) (ratMx_smul _ (ratMx_mul (ratMx_adj hy) (rat_mem _)))

theorem jacT_rat (hψ : IsCharAF D.host.F ψ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) {y : Mx D S.rank ρ}
    (hy : y ∈ ratMx D S.rank ρ) {n : GA D T} (hn : n ∈ GQ T) {f : WO S T₀ → ℂ} (hf : IsThetaFunO ψ S T₀ f) :
    jacT ψ d S y n f 0 = f 0 := by
  have h1 := incAdj_rat d S hy
  have h2 : mt T n⁻¹ ⬝ d.incAdj S y ∈ ratMx D T.rank S.rank := ratMx_mul ((mem_GQ_iff T _).1 (inv_mem hn)) h1
  obtain ⟨a, ha⟩ := (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.2.2.1 _ h1 _ h2
  obtain ⟨δ, hδ⟩ : ptT d S y n ∈ ratMx D T₀.rank S.rank := ratMx_mul (rat_mem _) h2
  have h3 := hf.quasi δ 0
  rw [show ratW T₀ S δ = ptT d S y n from hδ, symplOH_zero_right, neg_zero, AddChar.map_zero_eq_one, one_mul,
    add_zero] at h3
  rw [jacT, Pi.smul_apply, cenT, ha, hψ.2.2.1, one_smul, heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul,
    zero_add, h3]

variable {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)

theorem flatBF_eq (Ψ : WO B.V J.W → ℂ) : flatBF s Ψ =
    flatAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat J.d.e) (yZero B.V₀ ρ (vecB B.o B.ζ)) Ψ := rfl

theorem flatBF_theta {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) : IsThetaFunO ψ B.V₀ J.W₀ (flatBF s Ψ) :=
  (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D ψ s.weil.std B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU J.d.e
    (GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d).1.1 _ Ψ hΨ).2

variable {om' : Om B.V₀ J.W} (hom : IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om')
include hom

theorem flat_rat {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) {γ₀ : GA D B.A} (h₀ : γ₀ ∈ GQ B.A) {γ : GA D J.W}
    (hγ : γ ∈ GQ J.W ⊓ jacGrp J.d) : flatBF s (s.om (embA B.d B.o γ₀, γ) Ψ) 0 = flatBF s Ψ 0 := by
  obtain ⟨n, hn, h', rfl⟩ := (GlobalTheory.MixPer.Decomp.mem_jacGrp_iff J.d).1 hγ.2
  obtain ⟨hnQ, hh'⟩ := ((GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d).2.2.2.2.2 n hn h').1 hγ.1
  have hψ := s.weil.std.1
  have hΞ := flatBF_theta s hΨ
  have hy : yZero B.V₀ ρ (vecB B.o B.ζ) ∈ ratMx D B.V₀.rank ρ := neg_mem (zEll_rat _ _ _)
  have e1 : flatBF s (s.om (embA B.d B.o 1, n * J.d.emb0 h') Ψ) 0 = flatBF s Ψ 0 := by
    rw [GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant D ψ ρ B J s om' hom Ψ hΨ 1 n hn h', psiFlag_eq, GlobalTheory.CharLaws.psiBes_rat ψ J.d hψ.2.2.1 1 0 hnQ,
      star_one, one_smul, Prod.mk_one_one, map_one, Prod.mk_one_one, map_one, Module.End.one_apply, opA,
      jacT_rat hψ J.d B.V₀ hy hnQ (s.weil₀.om_pres _ _ hΞ), s.weil₀.om_aut 1 (one_mem _) h' hh' _ hΞ]
  have hΨ' := s.weil.om_pres (embA B.d B.o 1, n * J.d.emb0 h') Ψ hΨ
  have e2 : s.om (embA B.d B.o γ₀, n * J.d.emb0 h') Ψ =
      s.om (embA B.d B.o γ₀, 1 * J.d.emb0 1) (s.om (embA B.d B.o 1, n * J.d.emb0 h') Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul s.om, Prod.mk_mul_mk, map_one, map_one, mul_one, mul_one, one_mul]
  rw [e2, GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant D ψ ρ B J s om' hom _ hΨ' γ₀ 1 (one_mem _) 1, psiFlag_eq,
    GlobalTheory.CharLaws.psiBes_rat ψ J.d hψ.2.2.1 1 0 (one_mem _), star_one, one_smul, opA, jacT_one, Prod.mk_one_one, map_one,
    Module.End.one_apply, id, s.weil₀.om_aut _ (B.o.emb_mem_GQ h₀ (one_mem _)) 1 (one_mem _) _ (flatBF_theta s hΨ'), e1]

theorem flat_left {Φ : WO B.V J.W → ℂ} (hΦ : IsThetaFunO ψ B.V J.W Φ) {γ₀ : GA D B.A} (h₀ : γ₀ ∈ GQ B.A) {γ : GA D J.W}
    (hγ : γ ∈ GQ J.W ⊓ jacGrp J.d) (g : GA D B.A) (h : GA D J.W) :
    flatBF s (s.om (embA B.d B.o (γ₀ * g), γ * h) Φ) 0 = flatBF s (s.om (embA B.d B.o g, h) Φ) 0 := by
  rw [map_mul, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]
  exact flat_rat s hom (s.weil.om_pres _ _ hΦ) h₀ hγ

end GlobalTheory.UnfKer

namespace GlobalTheory.Unf

theorem kerBF_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → Continuous (kerBF s φ G Φ) ∧ (∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, kerBF s φ G Φ (γ * h) = kerBF s φ G Φ h) ∧ (∀ γ ∈ GQ B.A, ∀ h₀ h, flatBF s (s.om (embA B.d B.o (γ * h₀), h) Φ) 0 = flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0) ∧ ∀ h h' (n : flagN J.d), kerBF s φ G Φ (n.1 * J.d.emb0 h' * h) = fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flatBF s (s.om (1, h) Φ)) h' n := by
  intro D ψ ρ B J s om' hom φ G Φ hφ hG hΦ
  have h3 : ∀ γ ∈ GQ B.A, ∀ h₀ h, flatBF s (s.om (embA B.d B.o (γ * h₀), h) Φ) 0 =
      flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0 := fun γ hγ h₀ h => by
    have := GlobalTheory.UnfKer.flat_left s hom hΦ hγ (one_mem _) h₀ h
    rwa [one_mul] at this
  refine ⟨?_, fun γ hγ h => ?_, h3, fun h h' n => ?_⟩
  · have hc := GlobalTheory.T.continuous_flatMap_weilRepresentation_joint D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil s.vU J.d.e
      (GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d).1.1 Φ hΦ
    have he : Continuous (embA B.d B.o) :=
      B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
    have hq : Continuous fun p : GA D B.A × GA D J.W =>
        (((embA B.d B.o p.1, p.2), yZero B.V₀ ρ (vecB B.o B.ζ), 0) :
          (GA D B.V × GA D J.W) × Mx D B.V₀.rank ρ × WO B.V₀ J.W₀) :=
      ((he.comp continuous_fst).prodMk continuous_snd).prodMk continuous_const
    have hF : Continuous fun p : GA D B.A × GA D J.W => flatBF s (s.om (embA B.d B.o p.1, p.2) Φ) 0 := by
      refine (hc.comp hq).congr fun p => ?_
      rw [Function.comp_apply, GlobalTheory.UnfKer.flatBF_eq]
    have hK : Continuous (Function.uncurry fun (h₀ : GA D B.A) (h : GA D J.W) =>
        φ h₀ * flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0) := by
      refine ((hφ.2.comp continuous_fst).mul hF).congr fun p => ?_
      rw [Function.uncurry, Pi.mul_apply, Function.comp_apply]
    exact hG.2.1.mul (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D B.A B.cpt B.vA (GA D J.W) _ hK
      (fun γ hγ g p => by rw [hφ.1 γ hγ, h3 γ hγ])).2.1
  · rw [kerBF, kerBF, hG.1 γ hγ.1]
    congr 2
    funext h₀
    have := GlobalTheory.UnfKer.flat_left s hom hΦ (one_mem _) hγ h₀ h
    rw [one_mul] at this
    rw [this]
  · rw [kerBF, fjAllFun, rTrans, mul_assoc (G _), ← integral_const_mul (star _)]
    congr 2
    funext h₀
    have e : s.om (embA B.d B.o h₀, n.1 * J.d.emb0 h' * h) Φ =
        s.om (embA B.d B.o h₀, n.1 * J.d.emb0 h') (s.om (1, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul s.om, Prod.mk_mul_mk, mul_one]
    rw [e, GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant D ψ ρ B J s om' hom _ (s.weil.om_pres _ _ hΦ) h₀ n.1 n.2 h', Pi.smul_apply, smul_eq_mul, fjKer]
    ring

end GlobalTheory.Unf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselJacobiKernelLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedBesselJacobiKernel_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → Continuous (kerBF s φ G Φ) ∧ (∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, kerBF s φ G Φ (γ * h) = kerBF s φ G Φ h) ∧ (∀ γ ∈ GQ B.A, ∀ h₀ h, flatBF s (s.om (embA B.d B.o (γ * h₀), h) Φ) 0 = flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0) ∧ ∀ h h' (n : flagN J.d), kerBF s φ G Φ (n.1 * J.d.emb0 h' * h) = fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flatBF s (s.om (1, h) Φ)) h' n := by
  first | exact @GlobalTheory.Unf.kerBF_laws | exact GlobalTheory.Unf.kerBF_laws | (intros; apply GlobalTheory.Unf.kerBF_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeCongruentMapsFrameReadingsBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeCongruentMapsFrameReadingsBound
noncomputable section

namespace GlobalTheory.Transport.TwistRead

section Gen

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open GlobalTheory.Transport.LevelDatum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {hc : Formalism.BasicNotions.CMData F E}
  {a b : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

omit [NumberField E] [StarRing E] in
theorem toMatrix_inFr (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    LinearMap.toMatrix' f'.toLinearMap * LinearMap.toMatrix' (inFr f f' x) = LinearMap.toMatrix' x * LinearMap.toMatrix' f.toLinearMap := by
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  exact congrArg _ (LinearMap.ext fun z => f'.apply_symm_apply _)

theorem map_ptFr {n : ℕ} {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) {P : HeightOneSpectrum (𝓞 E)}
    (hPQ : P ∈ Q) (hPG : P ∉ SG) :
    (LinearMap.toMatrix' (ptFr p P).toLinearMap).map (algebraMap E (P.adicCompletion E)) =
      (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, Matrix.map_apply, LinearMap.toMatrix'_apply, ptFr_of_mem p hPG hPQ]
  exact (h.fr ⟨P, hPQ⟩ i j).symm

omit [StarRing E] in
theorem map_inv_mul_map {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (AfE F E)) :
    ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) *
      (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_read {g : GL (Fin a) (AfE F E)} {g' : GL (Fin b) (AfE F E)} {p : DecoF E a ST SG Q} {p' : DecoF E b ST SG Q}
    (h : IsPtOf hc g p) (h' : IsPtOf hc g' p') {P : HeightOneSpectrum (𝓞 E)} (hPQ : P ∈ Q) (hPG : P ∉ SG) (x : HomE E a b) :
    (LinearMap.toMatrix' (inFr (ptFr p P) (ptFr p' P) x)).map (algebraMap E (P.adicCompletion E)) =
      (mid g g' x).map (adAt F P) := by
  have f1 := congrArg (fun A => Matrix.map A (algebraMap E (P.adicCompletion E))) (toMatrix_inFr (ptFr p P) (ptFr p' P) x)
  simp only [Matrix.map_mul] at f1
  rw [map_ptFr h hPQ hPG, map_ptFr h' hPQ hPG] at f1
  have hx : (LinearMap.toMatrix' x).map (algebraMap E (P.adicCompletion E)) = (adMat F x).map (adAt F P) :=
    Matrix.ext fun i j => (adAt_inclE F P _).symm
  unfold mid
  rw [Matrix.map_mul, Matrix.map_mul, ← hx, Matrix.mul_assoc, ← f1, ← Matrix.mul_assoc, map_inv_mul_map, Matrix.one_mul]

theorem read_sub_le {k y : GL (Fin a) (AfE F E)} {k' y' : GL (Fin b) (AfE F E)} {p q : DecoF E a ST SG Q} {p' q' : DecoF E b ST SG Q}
    (hp : IsPtOf hc k p) (hpN : p.deco.1.N = stdLat E a) (hp' : IsPtOf hc k' p') (hpN' : p'.deco.1.N = stdLat E b)
    (hq : IsPtOf hc (y * k) q) (hq' : IsPtOf hc (y' * k') q') {P : HeightOneSpectrum (𝓞 E)} (hPQ : P ∈ Q) (hPG : P ∉ SG)
    (M₀ : ℕ) (x x₀ : HomE E a b)
    (h : ∀ r s, Valued.v (adAt F P ((mid y y' x - adMat F x₀) r s)) ≤ Valued.v ((M₀ : ℕ) : P.adicCompletion E)) (r : Fin b) (s : Fin a) :
    P.valuation E ((LinearMap.toMatrix' (inFr (ptFr q P) (ptFr q' P) x) - LinearMap.toMatrix' (inFr (ptFr p P) (ptFr p' P) x₀)) r s) ≤
      P.valuation E ((M₀ : ℕ) : E) := by
  have hd : mid (y * k) (y' * k') x - mid k k' x₀ =
      ((k'⁻¹ : GL (Fin b) (AfE F E)) : Matrix (Fin b) (Fin b) (AfE F E)) * (mid y y' x - adMat F x₀) *
        (k : Matrix (Fin a) (Fin a) (AfE F E)) := by
    unfold mid
    rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  have hA : ∀ r s, Valued.v (adAt F P (((k'⁻¹ : GL (Fin b) (AfE F E)) : Matrix (Fin b) (Fin b) (AfE F E)) r s)) ≤ 1 := fun r s => by
    have := Splice.valued_inv_mul_le (w := P) (hpN' ▸ hp'.lat) (carries_one (F := F) b) le_rfl r s
    rwa [mul_one] at this
  have hK : ∀ r s, Valued.v (adAt F P ((k : Matrix (Fin a) (Fin a) (AfE F E)) r s)) ≤ 1 := fun r s => by
    have := Splice.valued_inv_mul_le (w := P) (carries_one (F := F) a) (hpN ▸ hp.lat) le_rfl r s
    rwa [inv_one, one_mul] at this
  have e1 := congrFun (congrFun (map_read hq hq' hPQ hPG x) r) s
  have e2 := congrFun (congrFun (map_read hp hp' hPQ hPG x₀) r) s
  simp only [Matrix.map_apply] at e1 e2
  rw [← valued_algebraMap, ← valued_algebraMap, map_natCast, Matrix.sub_apply, map_sub, e1, e2, ← map_sub, ← Matrix.sub_apply, hd]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul, map_mul]
  refine (mul_le_of_le_one_right' (hK j s)).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul, map_mul]
  exact (mul_le_of_le_one_left' (hA r l)).trans (h l j)

end Gen

end GlobalTheory.Transport.TwistRead

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker

namespace GlobalTheory.Transport.TwistRead

theorem qread : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a)),
    P.1 ∈ I.Q a → Disjoint (B.primes X).vGs (I.Q a) →
    ∀ (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N i)) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 →
    ∀ (M₀ : ℕ) (x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      ∀ r s, P.1.valuation B.fields.E
        ((LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x) -
          LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)) r s) ≤
        P.1.valuation B.fields.E ((M₀ : ℕ) : B.fields.E) := by
  intro B X I u a i P hP hd p q p' q' k y k' y' hp hpN hp' hpN' hq hq' M₀ x x₀ hC r s
  rw [frsF_eq_ptFr, frsF_eq_ptFr, frsF_eq_ptFr, frsF_eq_ptFr]
  exact read_sub_le hp hpN hp' hpN' hq hq' hP (Finset.disjoint_right.1 hd hP) M₀ x x₀ (fun r s => hC r s) r s

end GlobalTheory.Transport.TwistRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeCongruentMapsFrameReadingsBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_prime_congruent_maps_frame_readings_bound : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a)),
    P.1 ∈ I.Q a → Disjoint (B.primes X).vGs (I.Q a) →
    ∀ (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N i)) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 →
    ∀ (M₀ : ℕ) (x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      ∀ r s, P.1.valuation B.fields.E
        ((LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x) -
          LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)) r s) ≤
        P.1.valuation B.fields.E ((M₀ : ℕ) : B.fields.E) := by
  exact @GlobalTheory.Transport.TwistRead.qread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittProjAnisotropicMulVecLeviEq
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.MonoIdele

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

def diagU (b : Fin ρ → (AE D)ˣ) : GL (Fin ρ) (AE D) :=
  ⟨Matrix.diagonal fun i => (b i : AE D), Matrix.diagonal fun i => (((b i)⁻¹ : (AE D)ˣ) : AE D),
    by rw [Matrix.diagonal_mul_diagonal]; simp, by rw [Matrix.diagonal_mul_diagonal]; simp⟩

theorem diagU_inv_val (b : Fin ρ → (AE D)ˣ) :
    ((diagU b)⁻¹).1 = Matrix.diagonal fun i => (((b i)⁻¹ : (AE D)ˣ) : AE D) := rfl

theorem diagU_inv_inv_val (b : Fin ρ → (AE D)ˣ) :
    (((diagU b)⁻¹)⁻¹).1 = Matrix.diagonal fun i => (b i : AE D) := by rw [inv_inv]; rfl

theorem mulVec_supp {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) {P : Pl D → Prop} {z : Fin n → AE D}
    (hz : ∀ j, z j ∈ idAt D P) (k : Fin m) : (A *ᵥ z) k ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hz j)

theorem mt_mulVec_inv (g : GA D S) (z : Fin S.rank → AE D) : mt S g *ᵥ (mt S g⁻¹ *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, show mt S g * mt S g⁻¹ = mt S (g * g⁻¹) from rfl, mul_inv_cancel]
  exact Matrix.one_mulVec z

theorem mem_iff_of_moves {L M : Lat S} {v : Pl D} {g : GA D S} (hm : Moves S g L M (· = v)) (z : Fin S.rank → AE D) :
    z ∈ latV S M (· = v) ↔ mt S g⁻¹ *ᵥ z ∈ latV S L (· = v) := by
  constructor
  · intro hz
    have hs : ∀ k, z k ∈ idAt D (· = v) := fun k => GlobalTheory.FinPl.FrameLat.latV_supp hz k
    rw [hm _ (fun k => mulVec_supp _ hs k), mt_mulVec_inv]
    exact hz
  · intro hz
    have hs : ∀ k, (mt S g⁻¹ *ᵥ z) k ∈ idAt D (· = v) := fun k => GlobalTheory.FinPl.FrameLat.latV_supp hz k
    have h := (hm _ hs).1 hz
    rwa [mt_mulVec_inv] at h

theorem diagonal_mulVec_single {n : ℕ} (u : Fin n → AE D) (i : Fin n) (c : AE D) :
    Matrix.diagonal u *ᵥ Pi.single i c = Pi.single i (u i * c) := by
  funext j
  rw [Matrix.mulVec_diagonal]
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem adj_diagonal {n : ℕ} (u : Fin n → AE D) :
    adj (Matrix.diagonal u) = Matrix.diagonal fun i => cA D (u i) := by
  ext i j
  show cA D (Matrix.diagonal u j i) = Matrix.diagonal (fun k => cA D (u k)) i j
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.diagonal_apply_ne _ (Ne.symm h), Matrix.diagonal_apply_ne _ h, map_zero]

variable (d : HypDec S S₀ ρ)

theorem levi_colMul_jX (a : GL (Fin ρ) (AE D)) {u : Fin ρ → AE D} (ha : a.1 = Matrix.diagonal u) (i : Fin ρ) (c : AE D) :
    mt S (d.levi a) *ᵥ colMul d.jX i c = colMul d.jX i (u i * c) := by
  rw [SplitLat.colMul_eq_mulVec, SplitLat.colMul_eq_mulVec, Matrix.mulVec_mulVec, d.levi_jX, ← Matrix.mulVec_mulVec, ha,
    diagonal_mulVec_single]

theorem levi_colMul_jY (a : GL (Fin ρ) (AE D)) {u : Fin ρ → AE D} (ha : (a⁻¹).1 = Matrix.diagonal u) (i : Fin ρ) (c : AE D) :
    mt S (d.levi a) *ᵥ colMul d.jY i c = colMul d.jY i (cA D (u i) * c) := by
  rw [SplitLat.colMul_eq_mulVec, SplitLat.colMul_eq_mulVec, Matrix.mulVec_mulVec, d.levi_jY, ← Matrix.mulVec_mulVec, ha,
    adj_diagonal, diagonal_mulVec_single]

theorem pX_levi_mulVec (a : GL (Fin ρ) (AE D)) {u : Fin ρ → AE D} (ha : a.1 = Matrix.diagonal u) (y : Fin S.rank → AE D)
    (i : Fin ρ) : (d.pX *ᵥ (mt S (d.levi a) *ᵥ y)) i = u i * (d.pX *ᵥ y) i := by
  rw [Matrix.mulVec_mulVec, d.pX_levi, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_diagonal]

theorem pY_levi_mulVec (a : GL (Fin ρ) (AE D)) {u : Fin ρ → AE D} (ha : (a⁻¹).1 = Matrix.diagonal u)
    (y : Fin S.rank → AE D) (i : Fin ρ) : (d.pY *ᵥ (mt S (d.levi a) *ᵥ y)) i = cA D (u i) * (d.pY *ᵥ y) i := by
  rw [Matrix.mulVec_mulVec, d.pY_levi, ← Matrix.mulVec_mulVec, ha, adj_diagonal, Matrix.mulVec_diagonal]

theorem wittProjAnisotropic_mulVec_levi_eq (a : GL (Fin ρ) (AE D)) (y : Fin S.rank → AE D) :
    d.p0 *ᵥ (mt S (d.levi a) *ᵥ y) = d.p0 *ᵥ y := by
  rw [Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_levi]

theorem mem_dualC_one (c : D.host.E) : c ∈ SplitLat.dualC (1 : FI D) ↔ c ∈ (1 : FI D) := by
  rw [SplitLat.mem_dualC, FractionalIdeal.mem_one_iff]
  constructor
  · intro h
    obtain ⟨o, ho⟩ := h 1 ((FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩)
    exact ⟨o, by rw [ho, star_one, one_mul]⟩
  · rintro ⟨o, rfl⟩ b hb
    obtain ⟨o', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
    obtain ⟨r, hr⟩ := GlobalTheory.HypLattice.star_mem_int ⟨o', rfl⟩
    exact ⟨r * o, by rw [map_mul, hr]⟩

variable (L₀ : Lat S₀)

theorem line_splitL_jY (v : Pl D) (i : Fin ρ) (a : AE D) :
    colMul d.jY i a ∈ latV S (SplitLat.splitL d L₀ (fun _ => (1 : FI D))) (· = v) ↔ a ∈ idV (1 : FI D) v := by
  constructor
  · intro ha
    have key : ∀ y ∈ latV S (SplitLat.splitL d L₀ (fun _ => (1 : FI D))) (· = v), (d.pY *ᵥ y) i ∈ idV (1 : FI D) v := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
        rw [Set.mem_singleton_iff] at hc
        subst hc
        change (rat d.qY *ᵥ _) i ∈ _
        rw [SplitLat.rat_mulVec_gen]
        refine AddSubgroup.subset_closure ⟨β, hβi, hβ, _, ?_, rfl⟩
        rw [one_mul]
        exact (mem_dualC_one _).1 (((SplitLat.mem_splitL d L₀ _ x).1 hx).2.2 i)
      | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
      | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
      | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz
    have h := key _ ha
    rwa [SplitLat.colMul_eq_mulVec, Matrix.mulVec_mulVec, d.pY_jY, Matrix.one_mulVec, Pi.single_eq_same] at h
  · intro ha
    rw [idV] at ha
    induction ha using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨β, hβi, hβ, b, hb, rfl⟩ := hz
      have e : colMul d.jY i (pairA D.host.F 0 β ⊗ₜ[D.host.F] b) =
          rat d.e' *ᵥ fun l => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * (Pi.single i b : Fin ρ → D.host.E) l) := by
        rw [SplitLat.colMul_eq_mulVec]
        change rat d.e' *ᵥ _ = _
        congr 1
        funext l
        by_cases h : l = i
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      rw [e, SplitLat.rat_mulVec_gen]
      exact AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, _,
        SplitLat.e'_mem (SplitLat.single_mem_of_mem (I := fun _ => SplitLat.dualC (1 : FI D)) i ((mem_dualC_one _).2 hb)), rfl⟩
    | zero =>
      have : colMul d.jY i 0 = 0 := by funext k; simp [colMul]
      rw [this]; exact zero_mem _
    | add z z' _ _ hz hz' =>
      have : colMul d.jY i (z + z') = colMul d.jY i z + colMul d.jY i z' := by funext k; simp [colMul, add_mul]
      rw [this]; exact add_mem hz hz'
    | neg z _ hz =>
      have : colMul d.jY i (-z) = -colMul d.jY i z := by funext k; simp [colMul]
      rw [this]; exact neg_mem hz

end GlobalTheory.FinPl.MonoIdele


open GlobalTheory.FinPl.MonoIdele in
theorem GlobalTheory.FinPl.exists_selfDual_mono_idele : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L₀ : Lat S₀), IsSelfDualC S₀ L₀ → ∀ b : Fin ρ → (AE D)ˣ, ∃ L : Lat S, IsSelfDualC S L ∧ ∀ x : Pl D, MonoAt d L L₀ x ∧ (∀ i, ∀ a ∈ idAt D (· = x), colMul d.jX i a ∈ latV S L (· = x) ↔ (((b i)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) ∧ ∀ i, ∀ a ∈ idAt D (· = x), colMul d.jY i a ∈ latV S L (· = x) ↔ cA D (b i : AE D) * a ∈ intAt D (· = x) := by
  intro D S S₀ ρ d L₀ hL₀ b
  have hL1 : IsSelfDualC S (SplitLat.splitL d L₀ (fun _ => (1 : FI D))) :=
    SplitLat.isSelfDualC_splitL d (fun _ => one_ne_zero) hL₀
  obtain ⟨M, hM, hmv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D S _ hL1).1 (d.levi (diagU b))
  refine ⟨M, hM, fun x => ⟨?_, fun i a _ => ?_, fun i a _ => ?_⟩⟩
  · have key := mem_iff_of_moves (hmv (· = x))
    rw [← map_inv] at key
    intro y
    rw [key y, SplitLat.monoAt_splitL d L₀ (fun _ => (1 : FI D)) x (mt S (d.levi (diagU b)⁻¹) *ᵥ y)]
    simp only [key, levi_colMul_jX d _ (diagU_inv_val b), levi_colMul_jY d _ (diagU_inv_inv_val b),
      pX_levi_mulVec d _ (diagU_inv_val b), pY_levi_mulVec d _ (diagU_inv_inv_val b), wittProjAnisotropic_mulVec_levi_eq]
  · have key := mem_iff_of_moves (hmv (· = x))
    rw [← map_inv] at key
    rw [key, levi_colMul_jX d _ (diagU_inv_val b)]
    exact (SplitLat.line_splitL d L₀ _ x i _).trans (GlobalTheory.SeeSaw.idV_one_eq_intAt D x _)
  · have key := mem_iff_of_moves (hmv (· = x))
    rw [← map_inv] at key
    rw [key, levi_colMul_jY d _ (diagU_inv_inv_val b)]
    exact (line_splitL_jY d L₀ x i _).trans (GlobalTheory.SeeSaw.idV_one_eq_intAt D x _)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepInverseCharacterLocalComponentChainTame
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepInverseCharacterLocalComponentChainTame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.QTw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QTw.StepChar

open _root_.Formalism.L2.Col _root_.Formalism.L2.DIV
open _root_.Formalism.L2.Host (HChar)

theorem locK_unif {L : Type} [Field L] [NumberField L] (χ : HChar L) (Q : HeightOneSpectrum (𝓞 L)) (hu : χ.UnrAt Q) (k : Lˣ)
    (hk : Q.valuation L (k : L) = WithZero.exp (-1 : ℤ)) : χ.locK Q k = χ.val Q :=
  χ.val_eq hu _ ((Formalism.UG.P.levelaf_valued_algebraMap Q (k : L)).trans hk)

section General

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {σ : X.K →+* ℂ} {e : Fin R.m → X.Tau → ℚ} {m0 : Fin R.m → HChar X.E} {eta ξ : HChar X.E}

theorem g_notMem (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : ∀ k, Pr.g k ∈ S) (P : rowSG Pr sel mu)
    (hP : P.1 ∉ Pr.vGs) (k : Fin 2) : ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal :=
  have hlp := GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P
  GlobalTheory.ColPeriod.natCast_notMem_of_ne (hPr.g_prime k) hlp.1.1 (fun h => hlp.2 hP (h ▸ hg k)) P.1 (Ideal.absNorm_mem _)

theorem res_eq (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : ∀ k, Pr.g k ∈ S) (ht : Ch.Tied σ e m0 eta)
    (h : GlobalTheory.Mem.Col2.Reads σ (mu : Chr X.F X.E X.K) ξ) (j : Fin R.m) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (x : X.Eˣ) (y : 𝓞 X.E) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (hx : (x : X.E) = (y : X.E))
    (hc : (c : 𝓞 X.E ⧸ P.1.asIdeal) = Ideal.Quotient.mk P.1.asIdeal y) :
    σ ((resChar (mu : Chr X.F X.E X.K) P.1 c : X.Kˣ) : X.K) = (((m0 j * ξ).locK P.1 x : ℂˣ) : ℂ) := by
  have hta := GlobalTheory.Mem.ReadTwist.tameAt h fun v => Subgroup.mem_iInf.1 mu.2.1.2 v
  have hu : P.1.valuation X.E (x : X.E) = 1 := by
    rw [hx]
    exact GlobalTheory.NormOneUnit.val_eq_one fun hy => c.ne_zero (hc.trans (Ideal.Quotient.eq_zero_iff_mem.2 hy))
  have e1 : (m0 j * ξ).locK P.1 x = (m0 j).locK P.1 x * ξ.locK P.1 x := rfl
  rw [e1, GlobalTheory.NormOneUnit.locK_unr ((ht.mu0 j).unr _ (g_notMem hX hPr hsel hg P hP)) hu, one_mul,
    GlobalTheory.NormOneUnit.resChar_eq h hta P.1 c y x hx hc.symm]

theorem map_muAt (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : ∀ k, Pr.g k ∈ S) (ht : Ch.Tied σ e m0 eta)
    (h : GlobalTheory.Mem.Col2.Reads σ (mu : Chr X.F X.E X.K) ξ) (j : Fin R.m) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hQ : cst.muq (j.1 + 1) P = (((Ch.muVal j P.1)⁻¹ * (qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K)) (a : X.Eˣ) :
    σ (muAt Ch sel mu cst j.1 P (a : X.E)) = (((m0 j * ξ).locK P.1 a : ℂˣ) : ℂ)⁻¹ := by
  classical
  have hlp := GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P
  have hta := GlobalTheory.Mem.ReadTwist.tameAt h fun v => Subgroup.mem_iInf.1 mu.2.1.2 v
  have hq := (GlobalTheory.TwistVal.main X.F X.E X.K σ _ ξ h hta P.1).2 hlp.1.2
  have hg' := g_notMem hX hPr hsel hg P hP
  have hm : ∀ x, (((m0 j * ξ)⁻¹.locK P.1 x : ℂˣ) : ℂ) = (((m0 j * ξ).locK P.1 x : ℂˣ) : ℂ)⁻¹ := fun x => by
    rw [← Units.val_inv_eq_inv_val]
    rfl
  rw [← hm]
  refine GlobalTheory.LocCharComp.locChar_eq_locK X.E X.K σ P.1 (m0 j * ξ)⁻¹ _ _ hlp.1.2 (fun q hq' => ?_) (fun x y c hx hc => ?_) a
  · have e1 : (m0 j * ξ).locK P.1 q = (m0 j).locK P.1 q * ξ.locK P.1 q := rfl
    rw [hm, e1, Units.val_mul, ← hq q hq', hQ, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul,
      map_inv₀, map_inv₀, ht.muVal j P.1 hg', ← locK_unif (m0 j) P.1 ((ht.mu0 j).unr _ hg') q
        (hq' ▸ GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _) hlp.1.2), mul_inv]
    rfl
  · rw [hm, if_neg hP, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, res_eq hX hPr hsel hg ht h j P hP x y c hx hc]

end General

theorem comp_eq_muAt_and_tame : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (P : BadPr I a), P.1 ∉ (B.primes X).vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt (D := I.rec7 l Z) q.e P.1 → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt P.1 x) → DenseRange (ofSplit q).pr → ∀ (i : ℕ) (hi : i < B.R.m) (χ : (AE (I.rec7 l Z))ˣ →* Circle), ChrEq (D := I.rec7 l Z) χ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → ∀ μ : kˣ →* ℂˣ, (ofSplit q).IsComp χ⁻¹ μ → (∀ (x : B.fields.E) (u : kˣ), (u : k) = (ofSplit q).pr x → (μ u : ℂ) = B.embLL (Formalism.L2.Col.muAt I.Ch I.sel (I.tup a) (I.cst a) i P x)) ∧ IsTame μ := by
  intro B X I hI l Z a P hP k _ _ _ _ q hq hint hden i hi χ hχ μ hμ
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hμ' : (ofSplit q).IsComp χ μ⁻¹ := fun x b hb => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hμ x b hb, MonoidHom.inv_apply, Circle.coe_inv, inv_inv]
  constructor
  · intro x u hu
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact u.ne_zero (hu.trans (q.pr.comp (incA (I.rec7 l Z))).map_zero)
    have h1 := GlobalTheory.LocMod.SplitHecke.chi_idlU_rat q hq hχ hx0 u hu
    have h2 := map_muAt hX hPr hI.sel_ok hI.g_mem hI.ch_tied (hI.xi_reads a) ⟨i, hi⟩ P hP
      ((hI.idx_ok a).muqQ i hi P hP) (Units.mk0 x hx0)
    have h3 := hμ u (GlobalTheory.LocMod.SplitHecke.idlU q u) rfl
    rw [MonoidHom.inv_apply, Circle.coe_inv, h1] at h3
    exact h3.trans h2.symm
  · have hr : IsRes (D := I.rec7 l Z) (I.C.mu0 ⟨i, hi⟩ * I.xi a) P.1
        ((Units.map (B.embLL : B.fields.K →* ℂ)).comp (resChar (I.tup a : Chr B.fields.F B.fields.E B.fields.K) P.1)) :=
      fun y x c hx hc => Units.ext (res_eq hX hPr hI.sel_ok hI.g_mem hI.ch_tied (hI.xi_reads a) ⟨i, hi⟩ P hP x y c hx hc)
    have ht := (GlobalTheory.LocMod.SplitHecke.tame_and_res (I.rec7 l Z) k q P.1 hq hint hden χ _ _ μ⁻¹ hχ hr hμ').1
    intro x hx
    have := ht x hx
    rwa [MonoidHom.inv_apply, inv_eq_one] at this

end GlobalTheory.QTw.StepChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepInverseCharacterLocalComponentChainTameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.QTw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_inverse_character_local_component_chain_tame : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (P : BadPr I a), P.1 ∉ (B.primes X).vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt (D := I.rec7 l Z) q.e P.1 → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt P.1 x) → DenseRange (ofSplit q).pr → ∀ (i : ℕ) (hi : i < B.R.m) (χ : (AE (I.rec7 l Z))ˣ →* Circle), ChrEq (D := I.rec7 l Z) χ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → ∀ μ : kˣ →* ℂˣ, (ofSplit q).IsComp χ⁻¹ μ → (∀ (x : B.fields.E) (u : kˣ), (u : k) = (ofSplit q).pr x → (μ u : ℂ) = B.embLL (Formalism.L2.Col.muAt I.Ch I.sel (I.tup a) (I.cst a) i P x)) ∧ IsTame μ := by
  first | exact @GlobalTheory.QTw.StepChar.comp_eq_muAt_and_tame | exact GlobalTheory.QTw.StepChar.comp_eq_muAt_and_tame | (intros; apply GlobalTheory.QTw.StepChar.comp_eq_muAt_and_tame <;> assumption)
end
end
