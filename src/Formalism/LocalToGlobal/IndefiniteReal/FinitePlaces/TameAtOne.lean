module

public import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TameAtOne
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def UnrOff (e : AE D) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → (e + cA D e) * (x : AE D) = e + cA D e → χ x = 1




end Formalism.IndefR.Fin

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ThetaFinsetSum
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem dRhoStable (D : D7) : DRhoStable D := by
  intro ψ θ hψ hθ S T τ z f hf
  exact (Formalism.IndefR.Fock.DRho.thetaDRho D ψ θ hψ hθ (Formalism.IndefR.Eqv.lineAtExists_holds D) S T τ z f hf).1

section Pt

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

lemma theta_sub {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f - g) := by
  convert Formalism.IndefR.Fock.CCR.theta_add_smul hf hg (-1) using 1 <;>
    ext x <;> simp [sub_eq_add_neg]

lemma theta_finsetSum {ι : Type*} (s : Finset ι) (g : ι → WO S T → ℂ) (hg : ∀ i ∈ s, IsThetaFunO ψ S T (g i)) :
    IsThetaFunO ψ S T (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Formalism.IndefR.Fock.CCR.theta_zero ψ S T
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Formalism.IndefR.Fock.CCR.theta_add (hg a (Finset.mem_insert_self a s))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

lemma theta_opPow {ι : Type} (A : ι → (WO S T → ℂ) → (WO S T → ℂ))
    (hA : ∀ i g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (A i g)) (k : ι →₀ ℕ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (opPow A k f) := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => exact hf
  | cons i l ih => exact hA i _ ih

theorem ptStable (D : D7) : PtStable D := by
  intro ψ θ hψ hθ S T sS sT BS BT f P hf
  have hA : ∀ (i : FVar D T.rank S.rank) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) := by
    intro i g hg
    unfold aPlusAll aPlus crea
    exact Formalism.IndefR.Fock.CCR.theta_smul
      (theta_sub (dRhoStable D ψ θ hψ hθ S T i.1 _ g hg)
        (Formalism.IndefR.Fock.CCR.theta_smul (dRhoStable D ψ θ hψ hθ S T i.1 _ g hg) _)) _
  unfold pureTensorO pureTensorL
  rw [Module.Basis.constr_apply, Finsupp.sum]
  exact theta_finsetSum _ _ fun k _ =>
    Formalism.IndefR.Fock.CCR.theta_smul (theta_opPow _ hA k hf) _

end Pt

end Formalism.IndefR.Fin
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.VacExA
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 400000

namespace Formalism.IndefR.Fin.VacEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsDyIdem (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) : Prop :=
  IsSplitIdem D e ∧ finPart D e ∈ intAE D ∧
    ∃ ε : AF D.host.F, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε


theorem fstA_pairA (x : Ainf D.host.F) (y : Af D.host.F) : fstA D.host.F (pairA D.host.F x y) = x := rfl
theorem sndA_pairA (x : Ainf D.host.F) (y : Af D.host.F) : sndA D.host.F (pairA D.host.F x y) = y := rfl



section Sym

variable (S T : HSp D)

end Sym

section Phi

variable (S T : HSp D)

def U0 (Λ : AddSubgroup (WO S T)) : AddSubgroup (WO S T) where
  carrier := {w | ∃ u ∈ Λ, ∀ i j, finPart D ((w - u) i j) = 0}
  add_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨u', hu', hb⟩
    refine ⟨u + u', Λ.add_mem hu hu', fun i j => ?_⟩
    have : (a + b - (u + u')) i j = (a - u) i j + (b - u') i j := by
      simp only [Matrix.sub_apply, Matrix.add_apply]; abel
    rw [this, map_add (f := _), ha, hb, add_zero]
  zero_mem' := ⟨0, Λ.zero_mem, fun i j => by simp⟩
  neg_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨-u, Λ.neg_mem hu, fun i j => ?_⟩
    have : (-a - -u) i j = -((a - u) i j) := by simp only [Matrix.sub_apply, Matrix.neg_apply]; abel
    rw [this, map_neg, ha, neg_zero]

theorem mem_U0 {Λ : AddSubgroup (WO S T)} {w : WO S T} :
    w ∈ U0 S T Λ ↔ ∃ u ∈ Λ, ∀ i j, finPart D ((w - u) i j) = 0 := Iff.rfl

theorem le_open_neighbourhood {Λ : AddSubgroup (WO S T)} : Λ ≤ U0 S T Λ := fun u hu => ⟨u, hu, fun i j => by simp⟩

theorem open_neighbourhood_set_eq (Λ : AddSubgroup (WO S T)) :
    (U0 S T Λ : Set (WO S T)) = {w | ∃ u ∈ Λ, (w - u).map (finPart D) = 0} := by
  ext w
  simp only [SetLike.mem_coe, mem_U0, Set.mem_setOf_eq]
  refine exists_congr fun u => and_congr_right fun _ => ⟨fun h => ?_, fun h i j => ?_⟩
  · ext i j; exact h i j
  · have := congrFun (congrFun h i) j; simpa using this


end Phi

section Lat

variable (S T : HSp D)

variable {S T}

end Lat

end Formalism.IndefR.Fin.VacEx
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LiftsCart
noncomputable section

namespace Formalism.IndefR.Fin.Lifts

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix Formalism.L2.Theta
open scoped ComplexOrder
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem posDef_of_sig {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G n 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    unfold Formalism.UG.Jpq
    rw [show (-1 : Matrix (Fin 0) (Fin 0) ℂ) = 1 by ext i; exact i.elim0, Matrix.fromBlocks_one]
  have hc : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) =
      star (P : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) := by
    ext i j
    simp [Formalism.UG.cT, Matrix.star_apply]
  rw [hJ, hc] at hP
  have hU : IsUnit (P : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) := P.isUnit
  have h1 : (G.reindex e e).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff hU).1 (hP ▸ Matrix.PosDef.one)
  have hG : G = (G.reindex e e).submatrix e e := by
    ext i j
    simp
  rw [hG]
  exact h1.submatrix e.injective

end Formalism.IndefR.Fin.Lifts

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.IndefR.Fin

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceSum
section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceInst
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

theorem isSBHalf_iff {e : AE D} {Λ : AddSubgroup (WO S T)} {Φ : WO S T → ℂ} :
    IsSBHalf e Λ Φ ↔ Four.IsSB Λ (halfSub S T e) Φ := by
  constructor
  · rintro ⟨hs, k, hk, hi, hl⟩
    exact ⟨hs, k, hk, fun u hu t => hi u (AddSubgroup.mem_inf.1 hu).1 (AddSubgroup.mem_inf.1 hu).2 t, hl⟩
  · rintro ⟨hs, k, hk, hi, hl⟩
    exact ⟨hs, k, hk, fun u hu hue t => hi u (AddSubgroup.mem_inf.2 ⟨hu, hue⟩) t, hl⟩

theorem finite_qt_of {H : AddSubgroup (WO S T)} {k : ℕ} (R : Finset (WO S T))
    (hR : ∀ u ∈ H, ∃ r ∈ R, ∃ v ∈ H, u = r + k • v) : Finite (Four.Qt k H) := by
  classical
  let R' : Finset (WO S T) := R.filter (· ∈ H)
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

theorem nsmul_eq_zero_WO {k : ℕ} (hk : 0 < k) {t : WO S T} (h : k • t = 0) : t = 0 := by
  have hu : IsUnit (k : AE D) := by
    have e1 : (k : AE D) = algebraMap D.host.F (AE D) (k : D.host.F) := by simp
    rw [e1]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hk.ne')).map _
  ext i j
  have := congrFun (congrFun h i) j
  rw [Matrix.smul_apply, nsmul_eq_mul, Matrix.zero_apply] at this
  rw [Matrix.zero_apply]
  exact (hu.mul_right_eq_zero).1 this

open Classical in
theorem exists_placeModel (e₁ : AE D) (he : e₁ * cA D e₁ = 0) (Λ : AddSubgroup (WO S T)) (f₀ : WO S T → ℂ)
    (hLL : ∀ x ∈ Λ, IsHalf e₁ x → ∀ y ∈ Λ, IsHalf (cA D e₁) y → ψ (symplO S T x y) = 1)
    (hdY : ∀ y, IsHalf (cA D e₁) y → (∀ x ∈ Λ, IsHalf e₁ x → ψ (symplO S T x y) = 1) → y ∈ Λ)
    (hfX : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf e₁ u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf e₁ v ∧ u = r + k • v)
    (hfY : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf (cA D e₁) u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf (cA D e₁) v ∧ u = r + k • v)
    (hoX : ∀ x, IsHalf e₁ x → ∃ k : ℕ, 0 < k ∧ k • x ∈ Λ)
    (hoY : ∀ y, IsHalf (cA D e₁) y → ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    (hvX : ∀ u ∈ Λ, IsHalf e₁ u → heisO ψ S T u f₀ = f₀)
    (hvY : ∀ u ∈ Λ, IsHalf (cA D e₁) u → heisO ψ S T u f₀ = f₀) :
    ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e₁ Λ 1 f₀ Tm ∧
      ∀ Φ, IsSBHalf e₁ Λ Φ → Tm Φ = Four.tfun (heisL ψ S T) (fun t y => ψ (symplO S T t y)) Λ
        (halfSub S T e₁) (halfSub S T (cA D e₁)) f₀ Φ := by
  have mi := fun {x : WO S T} {H K : AddSubgroup (WO S T)} (h : x ∈ H ⊓ K) => AddSubgroup.mem_inf.1 h
  obtain ⟨Tm, hTe, htr, hmo, hva⟩ := Four.exists_model (ρ := heisL ψ S T) (χ := fun t y => ψ (symplO S T t y))
    (L := Λ) (X := halfSub S T e₁) (Y := halfSub S T (cA D e₁)) (f₀ := f₀)
    (hX := fun x hx x' hx' => heisL_add_half ψ S T he hx hx')
    (hY := fun y hy y' hy' => heisL_add_half ψ S T (cA_half_orth he) hy hy')
    (hXY := fun x _ y _ => heisL_comm ψ S T x y)
    (hχl := fun t t' y => by simp only [symplO_add_left, AddChar.map_add_eq_mul])
    (hχr := fun t y y' => by simp only [symplO_add_right, AddChar.map_add_eq_mul])
    (hχ0 := fun t y => psi_ne_zero ψ _)
    (hLL := fun x hx y hy => hLL x (mi hx).1 (mi hx).2 y (mi hy).1 (mi hy).2)
    (hdY := fun y hy h => hdY y hy fun x hx hxe => h x (AddSubgroup.mem_inf.2 ⟨hx, hxe⟩))
    (hfinX := fun k hk => by
      obtain ⟨R, hR⟩ := hfX k hk
      exact finite_qt_of S T R fun u hu => by
        obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
        exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩)
    (hfinY := fun k hk => by
      obtain ⟨R, hR⟩ := hfY k hk
      exact finite_qt_of S T R fun u hu => by
        obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
        exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩)
    (htf := fun k hk t h => nsmul_eq_zero_WO S T hk h)
    (hoX := fun x hx => hoX x hx) (hoY := fun y hy => hoY y hy)
    (hfX := fun u hu => hvX u (mi hu).1 (mi hu).2)
    (hfY := fun u hu => hvY u (mi hu).1 (mi hu).2)
  refine ⟨Tm, ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩, fun Φ hΦ => hTe Φ ((isSBHalf_iff S T).1 hΦ)⟩
  · exact htr Φ ((isSBHalf_iff S T).1 hΦ) x hx
  · exact hmo Φ ((isSBHalf_iff S T).1 hΦ) y hy
  · rw [one_smul]
    exact hva

end Formalism.IndefR.Fin

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isSplitIdem_cA {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hε, by rw [cA_cA, add_comm, h3]⟩

theorem psi_neg_one (ψ : AddChar (AF D.host.F) ℂ) {a : AF D.host.F} (h : ψ a = 1) : ψ (-a) = 1 := by
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, one_mul] at this
  exact this.symm

variable (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

theorem heisO_zero (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO_zero_right]

end Formalism.IndefR.Fin

end
end
