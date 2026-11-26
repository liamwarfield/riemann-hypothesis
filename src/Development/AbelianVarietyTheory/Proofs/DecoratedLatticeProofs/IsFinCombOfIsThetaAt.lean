module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaConstMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOConstMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFinCombOfIsThetaAt
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.FinComb

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f₀ : WO S T → ℂ}

theorem isFinComb_zero : IsFinComb ψ S T f₀ 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, by simp⟩

theorem isFinComb_add {f g : WO S T → ℂ} (hf : IsFinComb ψ S T f₀ f) (hg : IsFinComb ψ S T f₀ g) :
    IsFinComb ψ S T f₀ (f + g) := by
  obtain ⟨n, c, x, hx, rfl⟩ := hf
  obtain ⟨m, c', x', hx', rfl⟩ := hg
  refine ⟨n + m, Fin.append c c', Fin.append x x', fun k => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [Fin.append_left]; exact hx i
    · rw [Fin.append_right]; exact hx' i
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem isFinComb_smul (a : ℂ) {f : WO S T → ℂ} (hf : IsFinComb ψ S T f₀ f) : IsFinComb ψ S T f₀ (a • f) := by
  obtain ⟨n, c, x, hx, rfl⟩ := hf
  exact ⟨n, fun k => a * c k, x, hx, by rw [Finset.smul_sum]; simp only [smul_smul]⟩

theorem isFinComb_single (a : ℂ) (x : WO S T) (hx : x.map (infPart D) = 0) :
    IsFinComb ψ S T f₀ (a • heisO ψ S T x f₀) :=
  ⟨1, fun _ => a, fun _ => x, fun _ => hx, by simp⟩

end GlobalTheory.AdForm.FinComb

namespace GlobalTheory.AdForm

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.AdForm.FinComb

theorem isFinComb_of_isThetaAt : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (e : AE D) (f₀ Φ f : WO S T → ℂ),
    IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → e * e = e → infPart D e = 0 →
    IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ →
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Φ f →
    IsFinComb ψ S T f₀ f := by
  intro D ψ S T ΛS ΛT e f₀ Φ f hψ hS hT he hinf hΦ hθ
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  rw [hall Tm hTm]
  clear hall
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hLL' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) →
      x ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e := fun x hx h => by
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin' : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, ∃ r ∈ R,
        ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u := fun k hk => by
    obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ (latO S T ΛS ΛT fun _ => True) := fun y hy =>
    exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y; rw [symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y; rw [symplO_add_right, AddChar.map_add_eq_mul]
    · intro y; rw [symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y; rw [symplO_zero_right, AddChar.map_zero_eq_one]
  have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
      ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin' Φ
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
  clear hΦ
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    have s0 := GlobalTheory.isSBHalf_halfInd e (latO S T ΛS ΛT fun _ => True)
    have s1 : IsSBHalf e (latO S T ΛS ΛT fun _ => True)
        fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t := by
      obtain ⟨k, hk, hk'⟩ := hden y hy
      obtain ⟨a1, k', hk1, a2, a3⟩ := s0
      refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
        fun t ht => ?_⟩
      · have e1 : halfInd e (latO S T ΛS ΛT fun _ => True) (t + (k * k') • u) =
            halfInd e (latO S T ΛS ΛT fun _ => True) t := by
          rw [mul_nsmul]
          exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
        have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
          rw [mul_nsmul']
          exact (hb.nsmul k _ y).trans
            (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _ ⟨hk', nsmul_mem hy k⟩)
        simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
      · rw [mul_nsmul']
        exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) x y =
        fun t => (fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t) (t + x) := by
      rw [halfInd_eq_ind]; rfl
    have v1 := hTm.vac
    rw [one_smul] at v1
    rw [e1, hTm.trans _ s1 x ((isHalf_iff S T).2 hx), hTm.modul _ s0 y ((isHalf_iff S T).2 hy), v1]
    have hxy := heisL_heisL S T ψ x y f₀
    change heisO ψ S T x (heisO ψ S T y f₀) = ψ (symplOH S T x y) • heisO ψ S T (x + y) f₀ at hxy
    rw [hxy]
    refine isFinComb_single _ _ ?_
    have h1 := infPart_of_half hinf ((isHalf_iff S T).2 hx)
    have h2 := infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy)
    ext i j
    have a1 := congrFun (congrFun h1 i) j
    have a2 := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.zero_apply] at a1 a2 ⊢
    rw [RingHom.map_add (f := _), a1, a2, add_zero]
  | zero => rw [LinearMap.map_zero]; exact isFinComb_zero
  | add g g' _ _ hg hg' => rw [LinearMap.map_add (f := _)]; exact isFinComb_add hg hg'
  | smul c g _ hg => rw [LinearMap.map_smul]; exact isFinComb_smul c hg

end GlobalTheory.AdForm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiCombEqLOpROp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section

namespace GlobalTheory.ProdLocInv

section Ops

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D)

def lOp (c : WO A S →₀ ℂ) (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => comb ψ A S c (fun u' => C u' v) u

def rOp (c : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u => comb ψ S A' c (C u)

theorem biComb_eq_lOp_rOp (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' c c' C = lOp ψ A S A' c (rOp ψ A S A' c' C) := rfl

theorem lOp_rOp (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    lOp ψ A S A' c (rOp ψ A S A' c' C) = rOp ψ A S A' c' (lOp ψ A S A' c C) := by
  funext u v
  simp only [lOp, rOp, comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem lOp_lOp (c d e : WO A S →₀ ℂ) (h : ∀ f, comb ψ A S e f = comb ψ A S c (comb ψ A S d f))
    (C : WO A S → WO S A' → ℂ) : lOp ψ A S A' c (lOp ψ A S A' d C) = lOp ψ A S A' e C := by
  funext u v
  exact congrFun (h fun u'' => C u'' v).symm u

theorem rOp_rOp (c d e : WO S A' →₀ ℂ) (h : ∀ f, comb ψ S A' e f = comb ψ S A' c (comb ψ S A' d f))
    (C : WO A S → WO S A' → ℂ) : rOp ψ A S A' c (rOp ψ A S A' d C) = rOp ψ A S A' e C := by
  funext u
  exact (h (C u)).symm

theorem lOp_comm (c d : WO A S →₀ ℂ) (h : ∀ f, comb ψ A S c (comb ψ A S d f) = comb ψ A S d (comb ψ A S c f))
    (C : WO A S → WO S A' → ℂ) : lOp ψ A S A' c (lOp ψ A S A' d C) = lOp ψ A S A' d (lOp ψ A S A' c C) := by
  funext u v
  exact congrFun (h fun u'' => C u'' v) u

theorem rOp_comm (c d : WO S A' →₀ ℂ) (h : ∀ f, comb ψ S A' c (comb ψ S A' d f) = comb ψ S A' d (comb ψ S A' c f))
    (C : WO A S → WO S A' → ℂ) : rOp ψ A S A' c (rOp ψ A S A' d C) = rOp ψ A S A' d (rOp ψ A S A' c C) := by
  funext u
  exact h (C u)

theorem biComb_comp (c d e : WO A S →₀ ℂ) (c' d' e' : WO S A' →₀ ℂ)
    (hl : ∀ f, comb ψ A S e f = comb ψ A S c (comb ψ A S d f))
    (hr : ∀ f, comb ψ S A' e' f = comb ψ S A' c' (comb ψ S A' d' f)) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' c c' (biComb ψ A S A' d d' C) = biComb ψ A S A' e e' C := by
  simp only [biComb_eq_lOp_rOp]
  rw [← lOp_rOp ψ A S A' d c', lOp_lOp ψ A S A' c d e hl, rOp_rOp ψ A S A' c' d' e' hr]

theorem biComb_comm (c d : WO A S →₀ ℂ) (c' d' : WO S A' →₀ ℂ)
    (hl : ∀ f, comb ψ A S c (comb ψ A S d f) = comb ψ A S d (comb ψ A S c f))
    (hr : ∀ f, comb ψ S A' c' (comb ψ S A' d' f) = comb ψ S A' d' (comb ψ S A' c' f)) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' c c' (biComb ψ A S A' d d' C) = biComb ψ A S A' d d' (biComb ψ A S A' c c' C) := by
  simp only [biComb_eq_lOp_rOp]
  rw [← lOp_rOp ψ A S A' d c', lOp_comm ψ A S A' c d hl, rOp_comm ψ A S A' c' d' hr, lOp_rOp ψ A S A' c d']

theorem comb_single_zero (T T' : HSp D) (f : WO T T' → ℂ) : comb ψ T T' (Finsupp.single 0 1) f = f := by
  classical
  funext w
  have h0 : symplOH T T' w 0 = 0 := by simp [symplOH, symplO, hO]
  simp [comb, heisO, h0]

end Ops

theorem comm_foldr {α ι : Type} (F : α → α) (H : ι → α → α) (l : List ι) (h : ∀ i ∈ l, ∀ x, F (H i x) = H i (F x))
    (x : α) : F (l.foldr H x) = l.foldr H (F x) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]

theorem foldr_mem {α ι : Type} (H : ι → α → α) (s : Set α) (l : List ι) (h : ∀ i ∈ l, ∀ x ∈ s, H i x ∈ s) (x : α)
    (hx : x ∈ s) : l.foldr H x ∈ s := by
  induction l with
  | nil => exact hx
  | cons i l ih => exact h i (by simp) _ (ih fun j hj => h j (by simp [hj]))

section Lists

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D)

theorem prodList {ι' : Type} (e₁ : ι' → WO A S →₀ ℂ) (e₂ : ι' → WO S A' →₀ ℂ) (l : List ι') :
    ∃ (e : WO A S →₀ ℂ) (e' : WO S A' →₀ ℂ),
      (∀ w ∈ e.support, w ∈ AddSubmonoid.closure (⋃ i ∈ l, ((e₁ i).support : Set (WO A S)))) ∧
      (∀ w ∈ e'.support, w ∈ AddSubmonoid.closure (⋃ i ∈ l, ((e₂ i).support : Set (WO S A')))) ∧
      ∀ C, biComb ψ A S A' e e' C = l.foldr (fun i C => biComb ψ A S A' (e₁ i) (e₂ i) C) C := by
  classical
  induction l with
  | nil =>
    refine ⟨Finsupp.single 0 1, Finsupp.single 0 1, ?_, ?_, fun C => ?_⟩
    · intro w hw
      rw [Finsupp.mem_support_single] at hw
      rw [hw.1]; exact zero_mem _
    · intro w hw
      rw [Finsupp.mem_support_single] at hw
      rw [hw.1]; exact zero_mem _
    · funext u v
      simp only [List.foldr_nil, biComb, comb_single_zero]
  | cons i l ih =>
    obtain ⟨e0, e0', hs, hs', hc⟩ := ih
    obtain ⟨c, hcs, hcf⟩ := (GlobalTheory.HeisComb.main D ψ A S).1 (e₁ i) e0
    obtain ⟨c', hcs', hcf'⟩ := (GlobalTheory.HeisComb.main D ψ S A').1 (e₂ i) e0'
    refine ⟨c, c', ?_, ?_, fun C => ?_⟩
    · intro w hw
      obtain ⟨x, hx, y, hy, rfl⟩ := hcs w hw
      refine add_mem (AddSubmonoid.subset_closure ?_) (AddSubmonoid.closure_mono ?_ (hs y hy))
      · simp only [Set.mem_iUnion]
        exact ⟨i, by simp, hx⟩
      · intro z hz
        simp only [Set.mem_iUnion] at hz ⊢
        obtain ⟨j, hj, hz⟩ := hz
        exact ⟨j, List.mem_cons_of_mem _ hj, hz⟩
    · intro w hw
      obtain ⟨x, hx, y, hy, rfl⟩ := hcs' w hw
      refine add_mem (AddSubmonoid.subset_closure ?_) (AddSubmonoid.closure_mono ?_ (hs' y hy))
      · simp only [Set.mem_iUnion]
        exact ⟨i, by simp, hx⟩
      · intro z hz
        simp only [Set.mem_iUnion] at hz ⊢
        obtain ⟨j, hj, hz⟩ := hz
        exact ⟨j, List.mem_cons_of_mem _ hj, hz⟩
    · rw [List.foldr_cons, ← hc]
      exact (biComb_comp ψ A S A' _ _ _ _ _ _ hcf hcf' C).symm

theorem keyList {ι' : Type} (e₁ g₁ : ι' → WO A S →₀ ℂ) (e₂ g₂ : ι' → WO S A' →₀ ℂ)
    (Cl Vl : ι' → Set (WO A S → WO S A' → ℂ)) (l : List ι') (hl : l.Nodup)
    (horth : ∀ i ∈ l, ∀ i' ∈ l, i ≠ i' → (∀ x, x ∈ (e₁ i).support ∨ x ∈ (g₁ i).support → ∀ y ∈ (e₁ i').support,
      symplO A S x y = 0) ∧ ∀ x, x ∈ (e₂ i).support ∨ x ∈ (g₂ i).support → ∀ y ∈ (e₂ i').support, symplO S A' x y = 0)
    (hloc : ∀ i ∈ l, ∀ C ∈ Cl i, biComb ψ A S A' (e₁ i) (e₂ i) C ∈ Vl i ∧
      C = biComb ψ A S A' (g₁ i) (g₂ i) (biComb ψ A S A' (e₁ i) (e₂ i) C))
    (hstab : ∀ i ∈ l, ∀ i' ∈ l, i ≠ i' → ∀ C ∈ Cl i, biComb ψ A S A' (e₁ i') (e₂ i') C ∈ Cl i)
    (C : WO A S → WO S A' → ℂ) (hC : ∀ i ∈ l, C ∈ Cl i) :
    (∀ i ∈ l, l.foldr (fun i C => biComb ψ A S A' (e₁ i) (e₂ i) C) C ∈ Vl i) ∧
      C = l.foldr (fun i C => biComb ψ A S A' (g₁ i) (g₂ i) C)
        (l.foldr (fun i C => biComb ψ A S A' (e₁ i) (e₂ i) C) C) := by
  induction l generalizing C with
  | nil => simp
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    have ih' := ih hl.2 (fun a ha b hb hab => horth a (by simp [ha]) b (by simp [hb]) hab)
      (fun a ha => hloc a (by simp [ha])) (fun a ha b hb hab => hstab a (by simp [ha]) b (by simp [hb]) hab)
    have hne : ∀ j ∈ l, i ≠ j := fun j hj h => hl.1 (h ▸ hj)
    have hEE : ∀ j ∈ l, ∀ Y, biComb ψ A S A' (e₁ i) (e₂ i) (biComb ψ A S A' (e₁ j) (e₂ j) Y) =
        biComb ψ A S A' (e₁ j) (e₂ j) (biComb ψ A S A' (e₁ i) (e₂ i) Y) := by
      intro j hj Y
      obtain ⟨h1, h2⟩ := horth i (by simp) j (by simp [hj]) (hne j hj)
      exact biComb_comm ψ A S A' _ _ _ _
        ((GlobalTheory.HeisComb.main D ψ A S).2.1 _ _ fun x hx y hy => h1 x (Or.inl hx) y hy)
        ((GlobalTheory.HeisComb.main D ψ S A').2.1 _ _ fun x hx y hy => h2 x (Or.inl hx) y hy) Y
    have hGE : ∀ j ∈ l, ∀ Y, biComb ψ A S A' (e₁ i) (e₂ i) (biComb ψ A S A' (g₁ j) (g₂ j) Y) =
        biComb ψ A S A' (g₁ j) (g₂ j) (biComb ψ A S A' (e₁ i) (e₂ i) Y) := by
      intro j hj Y
      obtain ⟨h1, h2⟩ := horth j (by simp [hj]) i (by simp) (hne j hj).symm
      exact (biComb_comm ψ A S A' _ _ _ _
        ((GlobalTheory.HeisComb.main D ψ A S).2.1 (g₁ j) (e₁ i) fun x hx y hy => h1 x (Or.inr hx) y hy)
        ((GlobalTheory.HeisComb.main D ψ S A').2.1 (g₂ j) (e₂ i) fun x hx y hy => h2 x (Or.inr hx) y hy) Y).symm
    have hEL := comm_foldr (biComb ψ A S A' (e₁ i) (e₂ i)) (fun j C => biComb ψ A S A' (e₁ j) (e₂ j) C) l hEE
    have hGL := comm_foldr (biComb ψ A S A' (e₁ i) (e₂ i)) (fun j C => biComb ψ A S A' (g₁ j) (g₂ j) C) l hGE
    have hCi : C ∈ Cl i := hC i (by simp)
    have hstabL : l.foldr (fun j C => biComb ψ A S A' (e₁ j) (e₂ j) C) C ∈ Cl i :=
      foldr_mem _ (Cl i) l (fun j hj Y hY => hstab i (by simp) j (by simp [hj]) (hne j hj) Y hY) C hCi
    obtain ⟨-, ihC⟩ := ih' C (fun j hj => hC j (by simp [hj]))
    obtain ⟨ihV2, -⟩ := ih' (biComb ψ A S A' (e₁ i) (e₂ i) C)
      (fun j hj => hstab j (by simp [hj]) i (by simp) (hne j hj).symm C (hC j (by simp [hj])))
    refine ⟨fun j hj => ?_, ?_⟩
    · simp only [List.foldr_cons]
      rcases List.mem_cons.1 hj with h | hj
      · subst h
        exact (hloc _ (by simp) _ hstabL).1
      · rw [hEL]
        exact ihV2 j hj
    · simp only [List.foldr_cons]
      rw [← hGL, ← ihC]
      exact (hloc i (by simp) C hCi).2

end Lists

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (ι' P : Type) (l : List ι') (X : P → WO A S → WO S A' → ℂ) (e₁ g₁ : ι' → WO A S →₀ ℂ) (e₂ g₂ : ι' → WO S A' →₀ ℂ) (Cl Vl : ι' → Set (WO A S → WO S A' → ℂ)), l.Nodup → (∀ i ∈ l, ∀ i' ∈ l, i ≠ i' → (∀ x, x ∈ (e₁ i).support ∨ x ∈ (g₁ i).support → ∀ y ∈ (e₁ i').support, symplO A S x y = 0) ∧ ∀ x, x ∈ (e₂ i).support ∨ x ∈ (g₂ i).support → ∀ y ∈ (e₂ i').support, symplO S A' x y = 0) → (∀ i ∈ l, ∀ p, X p ∈ Cl i) → (∀ i ∈ l, ∀ C ∈ Cl i, biComb ψ A S A' (e₁ i) (e₂ i) C ∈ Vl i ∧ C = biComb ψ A S A' (g₁ i) (g₂ i) (biComb ψ A S A' (e₁ i) (e₂ i) C)) → (∀ i ∈ l, ∀ i' ∈ l, i ≠ i' → ∀ C ∈ Cl i, biComb ψ A S A' (e₁ i') (e₂ i') C ∈ Cl i) → ∃ (e : WO A S →₀ ℂ) (e' : WO S A' →₀ ℂ), (∀ w ∈ e.support, w ∈ AddSubmonoid.closure (⋃ i ∈ l, ((e₁ i).support : Set (WO A S)))) ∧ (∀ w ∈ e'.support, w ∈ AddSubmonoid.closure (⋃ i ∈ l, ((e₂ i).support : Set (WO S A')))) ∧ ∀ p, (∀ i ∈ l, biComb ψ A S A' e e' (X p) ∈ Vl i) ∧ X p = l.foldr (fun i C => biComb ψ A S A' (g₁ i) (g₂ i) C) (biComb ψ A S A' e e' (X p)) := by
  intro D ψ A S A' ι' P l X e₁ g₁ e₂ g₂ Cl Vl hl horth hX hloc hstab
  obtain ⟨e, e', hs, hs', hc⟩ := prodList ψ A S A' e₁ e₂ l
  refine ⟨e, e', hs, hs', fun p => ?_⟩
  rw [hc]
  exact keyList ψ A S A' e₁ g₁ e₂ g₂ Cl Vl l hl horth hloc hstab (X p) fun i hi => hX i hi p

end GlobalTheory.ProdLocInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubleStep
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel
open GlobalTheory.LocMod Filter
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.DblInhab

section Gram

variable (E : Type) [Field E] [CharZero E] [StarRing E]



end Gram


section Place

open GlobalTheory.FinPl (SplitPt Pl idAt intAt)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem sec_one : q.sec 1 = q.e := GlobalTheory.LocChar.ι_one (ofSplit q)

theorem sec_mul_pr (a : k) (o : AE D) : q.sec (a * q.pr o) = q.sec a * o := by
  have h := q.sec_pr (q.sec a * o)
  rw [map_mul, q.pr_sec] at h
  rw [h, ← mul_assoc]
  exact congrArg (· * o) (GlobalTheory.LocChar.e_mul_ι (ofSplit q) a)

theorem sec_mem_idAt (a : k) : q.sec a ∈ idAt D (· = q.v) := by
  obtain ⟨ε, hε, hsum⟩ := q.above
  obtain ⟨hee, hec, -⟩ := q.split
  have he : q.e ∈ idAt D (· = q.v) := by
    refine ((GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D q.v ε hε).1 q.e).2 ?_
    rw [← hsum, add_mul, hee, mul_comm (cA D q.e), hec, add_zero]
  have h : q.e * q.sec a = q.sec a := GlobalTheory.LocChar.e_mul_ι (ofSplit q) a
  rw [← h]
  exact Ideal.mul_mem_right _ _ he

theorem sec_mem_intAt (a : k) : q.sec a ∈ intAt D (· = q.v) ↔ valuation k a ≤ 1 :=
  (and_iff_right (sec_mem_idAt q a)).trans (q.int_iff a).symm

theorem pr_le_one {o : AE D} (ho : o ∈ intAt D (· = q.v)) : valuation k (q.pr o) ≤ 1 := by
  refine (q.int_iff _).2 ?_
  rw [q.sec_pr, ← sec_one, map_mul]
  exact GlobalTheory.HostAdeleIso.intAE_mul_mem D ((q.int_iff 1).1 (one_mem _)) ho.2

end Place


end GlobalTheory.LocMod.DblInhab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelElementEqProdLocalParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelElementEqProdLocalParts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelCut

variable {D : D7}

theorem tensor_prod_zero {F A B E : Type} [Field F] [CommRing A] [CommRing B] [CommRing E] [Algebra F A]
    [Algebra F B] [Algebra F E] (z : (A × B) ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z = 0)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z = 0) : z = 0 := by
  have key : ∀ z : (A × B) ⊗[F] E, z =
      (LinearMap.inl F A B).rTensor E (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      (LinearMap.inr F A B).rTensor E (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [key z, h1, h2]; simp

theorem adele_zero (z : AE D) (h1 : infPart D z = 0) (h2 : finPart D z = 0) : z = 0 :=
  tensor_prod_zero (F := D.host.F) (A := Ainf D.host.F) (B := Af D.host.F) (E := D.host.E) z h1 h2

theorem mem_GfC_of (V : HSp D) (y : GA D V) (hy : ∀ i j, infPart D ((mt V y - 1) i j) = 0) : y ∈ GfC V := by
  show infHom V y = 1
  apply Units.ext
  change (mt V y).map (infPart D) = 1
  ext i j
  have := hy i j
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem eq_one_of_parts (V : HSp D) (y : GA D V) (h1 : y ∈ GfC V) (h2 : y ∈ GinfC V) : y = 1 := by
  have k1 : (mt V y).map (infPart D) = 1 := by
    have := congrArg Units.val (show infHom V y = 1 from h1)
    exact this
  have k2 : (mt V y).map (finPart D) = 1 := by
    have := congrArg Units.val (show finHom V y = 1 from h2)
    exact this
  apply GlobalTheory.SplitCut.mt_injective
  rw [GlobalTheory.SplitCut.mt_one]
  ext i j
  apply sub_eq_zero.mp
  apply adele_zero
  · rw [RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun (k1.trans (Matrix.map_one (infPart D) (RingHom.map_zero _) (RingHom.map_one _)).symm) i) j
  · rw [RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun (k2.trans (Matrix.map_one (finPart D) (RingHom.map_zero _) (RingHom.map_one _)).symm) i) j

theorem mem_GfC_of_grpAt (V : HSp D) (P : Pl D → Prop) (x : GA D V) (hx : x ∈ grpAt V P) : x ∈ GfC V := by
  refine mem_GfC_of V x fun i j => ?_
  have h := congrArg (fun y : GL (Fin V.rank) (AE D ⧸ idAt D P) => y.1 i j) (show _ = (1 : GL _ _) from hx)
  change Ideal.Quotient.mk (idAt D P) (mt V x i j) = _ at h
  have h2 : Ideal.Quotient.mk (idAt D P) (mt V x i j) =
      Ideal.Quotient.mk (idAt D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have h4 : (mt V x - 1) i j ∈ idAt D P := by
    rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2
  exact (RingHom.mem_ker).mp (Ideal.mem_inf.mp h4).1

theorem mem_GfC_of_supp (V : HSp D) {w : Pl D} (e : AE D) (he : ∃ ε, IsPlaceIdem D w ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε)
    (y : GA D V) (hy : SuppAt e V y) : y ∈ GfC V := by
  obtain ⟨ε, ⟨α, rfl, -⟩, hε⟩ := he
  have h0 : infPart D (e + cA D e) = 0 := by
    rw [hε]
    exact TensorProduct.zero_tmul _ _
  refine mem_GfC_of V y fun i j => ?_
  rw [← hy i j, RingHom.map_mul, h0, zero_mul]

end GlobalTheory.LevelCut

namespace GlobalTheory.LevelCut

variable {D : D7}

theorem entry_mem_of (V : HSp D) (I : Ideal (AE D)) (g : GA D V) (hg : g ∈ congGrp V I) (i j : Fin V.rank) :
    (mt V g - 1) i j ∈ I := by
  have h := congrArg (fun y : GL (Fin V.rank) (AE D ⧸ I) => y.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk I (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk I (mt V g i j) =
      Ideal.Quotient.mk I ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2

theorem mem_of_entry (V : HSp D) (I : Ideal (AE D)) (g : GA D V) (hg : ∀ i j, (mt V g - 1) i j ∈ I) :
    g ∈ congGrp V I := by
  show (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)) (matHom V g) = 1
  apply Units.ext
  ext i j
  change Ideal.Quotient.mk I (mt V g i j) = (1 : GL (Fin V.rank) (AE D ⧸ I)).1 i j
  rw [Units.val_one]
  have h2 : Ideal.Quotient.mk I (mt V g i j) =
      Ideal.Quotient.mk I ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) :=
    Ideal.Quotient.eq.mpr (by rw [← Matrix.sub_apply]; exact hg i j)
  rw [h2]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem congGrp_le (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J :=
  fun g hg => mem_of_entry V J g fun i j => h (entry_mem_of V I g hg i j)

theorem idAt_le_idOff_compl (P Q : Pl D → Prop) (hPQ : ∀ w, Q w → ¬ P w) : idAt D P ≤ idOff D Q := by
  intro a ha
  unfold idAt at ha
  unfold idOff
  simp only [Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  intro u
  exact ha.2 ⟨u.1, hPQ u.1 u.2⟩

end GlobalTheory.LevelCut

namespace GlobalTheory.LevelCut

theorem grpAt_eq_prod_local : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ}, c.Is → v.Is → ∀ (G : Fin n → GLoc v), GPin G →
    ∀ (j' : ℕ), ∀ x ∈ grpAt (c.V j') (· ∈ v.gP), ∃ xs : Fin n → GA D (c.V j'),
      (∀ i, SuppAt (G i).q.e (c.V j') (xs i)) ∧ x = (List.ofFn xs).prod := by
  intro D c v n _ _ G hG j' x hx
  have hoff : x ∈ grpOff (c.V j') (fun w => w ∉ Set.range fun i => (G i).q.v) := by
    refine congGrp_le (c.V j') (idAt_le_idOff_compl _ _ fun w hw hP => hw ?_) hx
    obtain ⟨i, hi⟩ := (hG.places w).mp hP
    exact ⟨i, hi.symm⟩
  obtain ⟨a, ha, h, hsupp, hcomm, -, hxa, -⟩ := GlobalTheory.SplitCut.prod_of_trivOff D (c.V j') (Fin n) (fun i => (G i).q.v)
    (fun i => (G i).q.e) hG.inj (fun i => ⟨(G i).q.split, (G i).q.above⟩) x hoff
  have hperm : (Finset.univ.toList.map h).prod = (List.ofFn h).prod := by
    rw [List.ofFn_eq_map]
    refine List.Perm.prod_eq' ((List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) (List.nodup_finRange n)
      (by ext i; simp)).map h) ?_
    exact List.Pairwise.map _ (fun i i' hii => hcomm i i' hii) (Finset.nodup_toList _)
  refine ⟨h, hsupp, ?_⟩
  have hP : (List.ofFn h).prod ∈ GfC (c.V j') := by
    refine (GfC (c.V j')).list_prod_mem fun y hy => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact mem_GfC_of_supp (c.V j') _ (G i).q.above (h i) (hsupp i)
  have hxf : x ∈ GfC (c.V j') := mem_GfC_of_grpAt _ _ x hx
  rw [hperm] at hxa
  have haf : a ∈ GfC (c.V j') := by
    have : a = x * ((List.ofFn h).prod)⁻¹ := by rw [hxa, mul_inv_cancel_right]
    rw [this]
    exact mul_mem hxf (inv_mem hP)
  rw [hxa, eq_one_of_parts _ a haf ha, one_mul]

end GlobalTheory.LevelCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelElementEqProdLocalPartsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_fixedLevel_element_eq_prod_local_parts : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ}, c.Is → v.Is → ∀ (G : Fin n → GLoc v), GPin G → ∀ (j' : ℕ), ∀ x ∈ grpAt (c.V j') (· ∈ v.gP), ∃ xs : Fin n → GA D (c.V j'), (∀ i, SuppAt (G i).q.e (c.V j') (xs i)) ∧ x = (List.ofFn xs).prod := by
  first | exact @GlobalTheory.LevelCut.grpAt_eq_prod_local | exact GlobalTheory.LevelCut.grpAt_eq_prod_local | (intros; apply GlobalTheory.LevelCut.grpAt_eq_prod_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder

namespace GlobalTheory.KJReal

variable {D : D7}

theorem detPlus_one_one {m n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.WeilParts.detPlus 1 1 a b = b.det ^ n * a.det ^ m := by
  unfold GlobalTheory.WeilParts.detPlus
  have e2 : (1 + 1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) = (2 : ℂ) • 1 := by
    rw [two_smul]
  rw [Matrix.transpose_one, Matrix.one_kronecker_one, sub_self, smul_zero, add_zero, e2, Matrix.smul_mul,
    Matrix.one_mul, smul_smul, show (1 / 2 * 2 : ℂ) = 1 by norm_num, one_smul, Matrix.det_kronecker,
    Matrix.det_transpose, Fintype.card_fin, Fintype.card_fin]

theorem exp_identity (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (e mS mT : ℤ) (nS nT : ℕ) (hS : (nS : ℤ) = mS + mS)
    (hT : (nT : ℤ) = mT + mT) :
    (a ^ (e - mT))⁻¹ * b ^ (e - mS) * (b ^ nS * a⁻¹ ^ nT) = a ^ (-e - mT) * b ^ (e + mS) := by
  rw [inv_pow, ← zpow_natCast b, ← zpow_natCast a, ← zpow_neg a, ← zpow_neg a]
  calc (a ^ (-(e - mT)) * b ^ (e - mS) * (b ^ (nS : ℤ) * a ^ (-(nT : ℤ))))
      = a ^ (-(e - mT)) * a ^ (-(nT : ℤ)) * (b ^ (e - mS) * b ^ (nS : ℤ)) := by ring
    _ = a ^ (-(e - mT) + -(nT : ℤ)) * b ^ (e - mS + (nS : ℤ)) := by rw [← zpow_add₀ ha, ← zpow_add₀ hb]
    _ = a ^ (-e - mT) * b ^ (e + mS) := by
      congr 2
      · rw [hT]; ring
      · rw [hS]; ring

end GlobalTheory.KJReal

namespace GlobalTheory.KJReal

end GlobalTheory.KJReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftDatumIsNonzeroFockVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftDatumIsNonzeroFockVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftFockVac

theorem levVec_fockVac : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → l2 μ 𝓧 f f ≠ 0 ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ (∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1) ∧ ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i σ) τ)) f := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hμ
  have hθf := (GlobalTheory.FinZeta.levVec_vacFin R F i t σ s P cμ cη m ω BW f₀ f c io h).1
  obtain ⟨hC, -, -, -, -, hW, -, hlv, -, -, -⟩ := h
  obtain ⟨⟨hψ, hv⟩, e, he, hth⟩ := hlv
  have hinf : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hinf' : infPart D (cA D (cA D e)) = 0 := by
    rw [GlobalTheory.DualPairCheck.cA_cA]; exact GlobalTheory.PlaceVec.idemSum_infPart he
  have hS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  have hr : (Wc D i).rank ≤ (Vc D i).rank := (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)
  have hf0 : f ≠ 0 := by
    have h00 : f₀ ≠ 0 := by
      rintro rfl
      obtain ⟨⟨p, hp⟩, h2⟩ := hv.norm
      have := h2 p hp
      simp [nrm2] at this
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
    rw [hall Tm hTm]
    have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
    have hee : e * e = e := ho.idem
    obtain ⟨-, hFS, -⟩ := hC.lev.βV i
    obtain ⟨-, hFT, -⟩ := hC.lev.βW i
    have hSB := GlobalTheory.FinZeta.isSBHalf_levDatum D _ _ _ _ _ _ (R.datWp i P) (R.Q t) m _ e hS hT hFS hFT he
    refine GlobalTheory.PlaceModelInj.placeModel_ne_zero D R.ψ _ _ _ _ (cA D e) f₀ _ Tm hψ hS hT ho.conj.idem
      (by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, he.2]) hinf hTm h00 hSB ?_
    obtain ⟨x, hx, hx'⟩ := GlobalTheory.AdjDatumNe.exists_half_frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) hee
      (GlobalTheory.AdjDatumNe.rectOne _ _ _)
    obtain ⟨hi, hres⟩ := GlobalTheory.AdjDatumNe.idemSum_res he
    have hint : IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) := by
      rw [hx']; exact GlobalTheory.AdjDatumNe.isIntM_smul_rectOne hi _ _
    have hred : ∀ PP ∈ (R.datWp i P).Pg ∪ R.Q t,
        redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) = GlobalTheory.Chain.StepVac.rectOne (kP PP) _ _ := by
      intro PP hPP
      rw [hx', GlobalTheory.AdjDatumNe.redM_smul_rectOne hi PP (hres PP hPP)]
      rfl
    intro hz
    have := congrFun hz x
    rw [if_pos ⟨hx, hint⟩, GlobalTheory.PlaceDatum.omegaG_congr _ m _ (fun PP => GlobalTheory.Chain.StepVac.rectOne (kP PP) _ _)
      fun PP hP => hred PP (Finset.mem_union_left _ hP),
      GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ (y' := fun PP => GlobalTheory.Chain.StepVac.rectOne (kP PP) _ _)
      fun PP hP => hred PP (Finset.mem_union_right _ hP)] at this
    exact mul_ne_zero (GlobalTheory.Chain.StepVac.omegaG_rectOne hr _ m) (GlobalTheory.Chain.StepVac.omegaQ_rectOne le_rfl hr _ m _) this
  refine ⟨?_, hθf, fun τ => GlobalTheory.RawLift.isCartanInv_one_of_onb (hC.models.BV i τ), fun τ => ?_⟩
  · have h1 := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hW.std hθf hf0 hμ
    have e1 : l2 μ 𝓧 f f = GlobalTheory.RawLift.thetaIP μ 𝓧 f f := by
      show (∫ w in 𝓧, f w * starRingEnd ℂ (f w) ∂μ) = ∫ w in 𝓧, star (f w) * f w ∂μ
      congr 1
      funext w
      rw [mul_comm]
      rfl
    rw [e1]
    exact h1
  · exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hv.inf hinf hinf' hth hv.theta hθf (hv.fock τ)

end GlobalTheory.LiftFockVac
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftDatumIsNonzeroFockVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftDatum_isNonzeroFockVacuum : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → l2 μ 𝓧 f f ≠ 0 ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ (∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1) ∧ ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i σ) τ)) f := by
  first | exact @GlobalTheory.LiftFockVac.levVec_fockVac | exact GlobalTheory.LiftFockVac.levVec_fockVac | (intros; apply GlobalTheory.LiftFockVac.levVec_fockVac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDataDistinctPlacesCommute
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDataDistinctPlacesCommute
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix GlobalTheory.FinPl GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OverSwap

variable {D : D7}

theorem eq_zero_of_two {v v' : Pl D} (hne : v ≠ v') {z : AE D} (h : z ∈ idAt D (· = v))
    (h' : z ∈ idAt D (· = v')) : z = 0 := by
  have hc : compAt D v z = 0 := by
    unfold idAt at h'
    exact (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 h').2 ⟨v, hne⟩
  rw [GlobalTheory.FinPl.Model.eq_single h, hc]
  exact (GlobalTheory.AdelicU.Supp.singleTens D.host.E v).map_zero'

theorem cA_mem_idAt {v : Pl D} {y : AE D} (h : y ∈ idAt D (· = v)) : cA D y ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff] at h ⊢
  rw [← Algebra.smul_def] at h ⊢
  conv_rhs => rw [← h]
  rw [GlobalTheory.HeisDisj.cA_smul]

theorem symplO_eq_zero_of_ne {v v' : Pl D} (hne : v ≠ v') {S T : HSp D} {x y : WO S T} (hx : MxAt (· = v) x)
    (hy : MxAt (· = v') y) : symplO S T x y = 0 := by
  have hh : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    have h0 : cA D (y c b) * x d a = 0 :=
      eq_zero_of_two hne (Ideal.mul_mem_left _ _ (hx d a)) (Ideal.mul_mem_right _ _ (cA_mem_idAt (hy c b)))
    calc incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a
        = incA D (S.gram⁻¹ a b) * incA D (T.gram c d) * (cA D (y c b) * x d a) := by ring
      _ = 0 := by rw [h0, mul_zero]
  unfold symplO
  rw [hh, mul_zero, map_zero]

theorem comb_comm {v v' : Pl D} (hne : v ≠ v') (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {c c' : WO S T →₀ ℂ}
    (hc : CombAt (· = v) c) (hc' : CombAt (· = v') c') (f : WO S T → ℂ) :
    GlobalTheory.SeeSaw.comb ψ S T c (GlobalTheory.SeeSaw.comb ψ S T c' f) = GlobalTheory.SeeSaw.comb ψ S T c' (GlobalTheory.SeeSaw.comb ψ S T c f) :=
  (GlobalTheory.HeisComb.main D ψ S T).2.1 c c' (fun x hx y hy => symplO_eq_zero_of_ne hne (hc x hx) (hc' y hy)) f

end GlobalTheory.FinPl.OverSwap

namespace GlobalTheory.FinPl


open GlobalTheory.FinPl.OverSwap in
theorem overSwap : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p p' : SplitPt D k) (n n' m m' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype m]
    [DecidableEq m] [Fintype m'] [DecidableEq m'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA →
    p'.UnitAA → p.v ≠ p'.v → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (α' : Frame p' S m')
    (β' : Frame p' T m) (LS : Lat S) (LT : Lat T) (f₀ g h : WO S T → ℂ) (Ψ : Matrix n n' k → ℂ)
    (Ψ' : Matrix m m' k → ℂ), Vac ψ S T LS LT (· = p'.v) f₀ → Over ψ α β LS LT f₀ Ψ g →
      Over ψ α' β' LS LT g Ψ' h → ∃ g', Over ψ α' β' LS LT f₀ Ψ' g' ∧ Over ψ α β LS LT g' Ψ h := by
  intro D k _ _ _ _ p p' n n' m m' _ _ _ _ _ _ _ _ ψ hψ hp hp' hne S T α β α' β' LS LT f₀ g h Ψ Ψ' hv' hO1 hO2
  obtain ⟨hLS, hLT, hf₀, hΨ, -⟩ := id hO1
  obtain ⟨-, -, hg, hΨ', -⟩ := id hO2
  obtain ⟨c, hc, hcO⟩ := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k p n n' ψ hψ hp S T α β LS LS LT LT hLS hLT hLS hLT).2 Ψ hΨ
  obtain ⟨c', hc', hcO'⟩ := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k p' m m' ψ hψ hp' S T α' β' LS LS LT LT hLS hLT hLS hLT).2 Ψ' hΨ'
  have eg : g = GlobalTheory.SeeSaw.comb ψ S T c f₀ :=
    ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hψ S T α β LS LT hLS hLT f₀ hf₀).1 Ψ hΨ).unique hO1 (hcO f₀ hf₀)
  have eh : h = GlobalTheory.SeeSaw.comb ψ S T c' g :=
    ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p' m m' ψ hψ S T α' β' LS LT hLS hLT g hg).1 Ψ' hΨ').unique hO2 (hcO' g hg)
  have hO3 := hcO' f₀ hv'
  have hvac : Vac ψ S T LS LT (· = p.v) (GlobalTheory.SeeSaw.comb ψ S T c' f₀) :=
    ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p' m m' ψ hψ S T α' β' LS LT hLS hLT f₀ hv').2.1 Ψ' _ hO3).2 LS LT (· = p.v)
      (fun e => hne e.symm) hf₀
  refine ⟨_, hO3, ?_⟩
  have e : h = GlobalTheory.SeeSaw.comb ψ S T c (GlobalTheory.SeeSaw.comb ψ S T c' f₀) := by
    rw [eh, eg, comb_comm hne ψ hc hc']
  rw [e]
  exact hcO _ hvac

end GlobalTheory.FinPl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDataDistinctPlacesCommuteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix GlobalTheory.FinPl GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceData_distinct_places_commute : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p p' : SplitPt D k) (n n' m m' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype m]
    [DecidableEq m] [Fintype m'] [DecidableEq m'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA →
    p'.UnitAA → p.v ≠ p'.v → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (α' : Frame p' S m')
    (β' : Frame p' T m) (LS : Lat S) (LT : Lat T) (f₀ g h : WO S T → ℂ) (Ψ : Matrix n n' k → ℂ)
    (Ψ' : Matrix m m' k → ℂ), Vac ψ S T LS LT (· = p'.v) f₀ → Over ψ α β LS LT f₀ Ψ g →
      Over ψ α' β' LS LT g Ψ' h → ∃ g', Over ψ α' β' LS LT f₀ Ψ' g' ∧ Over ψ α β LS LT g' Ψ h := by
  first | exact @GlobalTheory.FinPl.overSwap | exact GlobalTheory.FinPl.overSwap | (intros; apply GlobalTheory.FinPl.overSwap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOTargetSliceOrthogonalSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOTargetSliceOrthogonalSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem isThetaFunO_sliceT :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (f : WO T S → ℂ) (y : WO T L),
      IsThetaFunO ψ T S f → IsThetaFunO ψ T A (fun w => f ((o.resT T).symm (w, y))) :=
  fun _ _ _ _ _ _ o _ y hf => GlobalTheory.SliceModelT.isThetaFunO_sliceT_left o hf y

end GlobalTheory.FinPl.ExtZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOTargetSliceOrthogonalSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunO_target_slice_orthogonal_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (f : WO T S → ℂ) (y : WO T L), IsThetaFunO ψ T S f → IsThetaFunO ψ T A (fun w => f ((o.resT T).symm (w, y))) := by
  first | exact @GlobalTheory.FinPl.ExtZero.isThetaFunO_sliceT | exact GlobalTheory.FinPl.ExtZero.isThetaFunO_sliceT | (intros; apply GlobalTheory.FinPl.ExtZero.isThetaFunO_sliceT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColumnDimensionWindowThreeOfColumnCount
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColumnDimensionWindowThreeOfColumnCount
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Diag

theorem standingNumericalData_three_of_dataNW_rankMu : ∀ D : D7, DataNW D → (∀ u, GlobalTheory.Core.Rk.RankMu D u) → StandingNumericalData D 3 := by
  intro D hN hR
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _, h11⟩ := hN
  have hW : GlobalTheory.Diag.PG.DuWin D 3 := GlobalTheory.Diag.PG.duWin_three_of_count D fun u => by
    have := hR u
    unfold GlobalTheory.Core.Rk.RankMu at this
    rw [GlobalTheory.Core.Rk.d0_eq] at this
    exact this
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hW, h11⟩

end GlobalTheory.Core.Diag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColumnDimensionWindowThreeOfColumnCountStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnDimension_window_three_of_columnCount : ∀ D : D7, DataNW D → (∀ u, GlobalTheory.Core.Rk.RankMu D u) → StandingNumericalData D 3 := by
  first | exact @GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu | exact GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu | (intros; apply GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu <;> assumption)
end
end
