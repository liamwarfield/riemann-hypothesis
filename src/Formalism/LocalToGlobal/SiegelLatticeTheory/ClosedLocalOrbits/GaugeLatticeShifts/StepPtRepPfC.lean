module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfB
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfA
noncomputable section

open Matrix Formalism.MainNotions.S

namespace Formalism.L2.SG.RealObj.InfCut.PtRepPf

open Formalism.L2.SG.HidaSetting

section Calc

variable {n : ℕ} (ε : Fin n → Bool)

theorem hJ_apply (x y : Fin n → ℂ) :
    hJ ε x y = ∑ i, star (x i) * ((if ε i then 1 else -1) * y i) := by
  simp [hJ, Formalism.REAL.Jm, dotProduct, mulVec_diagonal]

theorem hJ_conj (x y : Fin n → ℂ) : star (hJ ε x y) = hJ ε y x := by
  rw [hJ_apply, hJ_apply, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ε i <;> simp [h] <;> ring

theorem hJ_add_right (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  simp only [hJ, mulVec_add, dotProduct_add]

theorem hJ_add_left (x x' y : Fin n → ℂ) : hJ ε (x + x') y = hJ ε x y + hJ ε x' y := by
  simp only [hJ, star_add, add_dotProduct]

theorem hJ_sub_right (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  simp only [hJ, mulVec_sub, dotProduct_sub]

theorem hJ_smul_right (c : ℂ) (x y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  simp only [hJ, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_smul_left (c : ℂ) (x y : Fin n → ℂ) : hJ ε (c • x) y = star c * hJ ε x y := by
  simp only [hJ, star_smul, smul_dotProduct, smul_eq_mul]

theorem hJ_zero_right (x : Fin n → ℂ) : hJ ε x 0 = 0 := by simp [hJ]

theorem hJ_zero_left (y : Fin n → ℂ) : hJ ε 0 y = 0 := by simp [hJ]

def formB : (Fin n → ℂ) →ₗ⋆[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => hJ ε x y)
    (fun x x' y => hJ_add_left ε x x' y)
    (fun c x y => by rw [hJ_smul_left, smul_eq_mul, starRingEnd_apply])
    (fun x y y' => hJ_add_right ε x y y')
    (fun c x y => by rw [hJ_smul_right, smul_eq_mul, RingHom.id_apply])

theorem formB_apply (x y : Fin n → ℂ) : formB ε x y = hJ ε x y := rfl

theorem hJ_sum_right {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, y i) = ∑ i ∈ s, hJ ε x (y i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← formB_apply, map_sum]

theorem hJ_sum_left {ι : Type*} (s : Finset ι) (x : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ i ∈ s, x i) y = ∑ i ∈ s, hJ ε (x i) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← formB_apply, map_sum, LinearMap.sum_apply]

theorem hJ_mulVec (A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    hJ ε (A *ᵥ x) (A *ᵥ y) = star x ⬝ᵥ ((Aᴴ * Formalism.REAL.Jm ε * A) *ᵥ y) := by
  unfold hJ
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem hJ_UJ (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    hJ ε (uMat g *ᵥ x) (uMat g *ᵥ y) = hJ ε x y := by
  rw [hJ_mulVec, show (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε from g.2]
  rfl

theorem mat_eq_of_mulVec {A B : Matrix (Fin n) (Fin n) ℂ} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

theorem inUJ_of_iso (A : Matrix (Fin n) (Fin n) ℂ) (h : ∀ x y, hJ ε (A *ᵥ x) (A *ᵥ y) = hJ ε x y) :
    Formalism.REAL.inUJ ε A := by
  unfold Formalism.REAL.inUJ
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hJ_mulVec] at this
  unfold hJ at this
  simpa [mulVec_single_one] using this

theorem eq_zero_of_hJ (d : Fin n → ℂ) (h : ∀ x, hJ ε x d = 0) : d = 0 := by
  funext i
  have h1 := h (Pi.single i 1)
  rw [hJ_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at h1
  by_cases hi : ε i <;> simp_all

theorem li_of_pair {ι : Type*} [Fintype ι] [DecidableEq ι] (s d : ι → Fin n → ℂ) (M : Matrix ι ι ℂ)
    (hM : IsUnit M.det) (h : ∀ j i, hJ ε (d j) (s i) = M j i) : LinearIndependent ℂ s := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hMc : M *ᵥ c = 0 := by
    funext j
    have := congrArg (hJ ε (d j)) hc
    rw [hJ_sum_right, hJ_zero_right] at this
    simp only [hJ_smul_right, h] at this
    simpa [mulVec, dotProduct, mul_comm] using this
  have h0 : c = 0 := by
    have := congrArg (fun v => M⁻¹ *ᵥ v) hMc
    simpa [mulVec_mulVec, nonsing_inv_mul _ hM] using this
  intro i
  simp [h0]

theorem expand_of_dual {ι : Type*} [Fintype ι] [DecidableEq ι] (φ d : ι → Fin n → ℂ)
    (hcard : Fintype.card ι = n) (hd : ∀ j i, hJ ε (d j) (φ i) = if j = i then 1 else 0)
    (v : Fin n → ℂ) : v = ∑ i, hJ ε (d i) v • φ i := by
  have hli : LinearIndependent ℂ d := li_of_pair ε d φ 1 (by simp) (fun j i => by
    rw [← hJ_conj, hd]
    change star (if i = j then (1 : ℂ) else 0) = if j = i then 1 else 0
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij])
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by rw [hcard, Module.finrank_fin_fun])
  rw [← sub_eq_zero]
  apply eq_zero_of_hJ ε
  intro x
  have hx : x ∈ Submodule.span ℂ (Set.range d) := by rw [hspan]; trivial
  refine Submodule.span_induction (p := fun x _ => hJ ε x (v - ∑ i, hJ ε (d i) v • φ i) = 0)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨j, rfl⟩
    rw [hJ_sub_right, hJ_sum_right]
    simp only [hJ_smul_right, hd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      sub_self]
  · exact hJ_zero_left ε _
  · intro x y _ _ hx hy; rw [hJ_add_left, hx, hy, add_zero]
  · intro c x _ hx; rw [hJ_smul_left, hx, mul_zero]

end Calc

section Witt

variable {n : ℕ} (ε : Fin n → Bool)

theorem wittFam {ι : Type*} [Fintype ι] (s t : ι → Fin n → ℂ) (hs : LinearIndependent ℂ s)
    (ht : LinearIndependent ℂ t) (hG : ∀ i j, hJ ε (t i) (t j) = hJ ε (s i) (s j)) :
    ∃ g : Formalism.REAL.UJ ε, ∀ i, uMat g *ᵥ s i = t i := by
  classical
  let U := Submodule.span ℂ (Set.range s)
  let bs : Module.Basis ι ℂ U := Module.Basis.span hs
  let f : U →ₗ[ℂ] (Fin n → ℂ) := bs.constr ℂ t
  have hf : ∀ i, f (bs i) = t i := fun i => bs.constr_basis ℂ t i
  have hsum : ∀ x : U, (x : Fin n → ℂ) = ∑ i, bs.repr x i • s i := by
    intro x
    have := congrArg (fun y : U => (y : Fin n → ℂ)) (bs.sum_repr x)
    simp only [Submodule.coe_sum, Submodule.coe_smul, bs] at this
    refine this.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    congr 1
    exact congrArg Subtype.val (Module.Basis.span_apply hs i)
  have hfsum : ∀ x : U, f x = ∑ i, bs.repr x i • t i := by
    intro x
    have := congrArg f (bs.sum_repr x)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [map_smul, hf] at this
    exact this.symm
  have e1 : ∀ x : U, Finsupp.linearCombination ℂ t (bs.repr x) = f x := fun x => by
    rw [hfsum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp
  have finj : Function.Injective f := by
    intro x y hxy
    apply bs.repr.injective
    exact (show Function.Injective (Finsupp.linearCombination ℂ t) from ht) (by rw [e1, e1, hxy])
  have hiso : ∀ x y : U, formB ε (f x) (f y) = formB ε (x : Fin n → ℂ) y := by
    intro x y
    simp only [formB_apply, hfsum, hsum, hJ_sum_left, hJ_sum_right, hJ_smul_left, hJ_smul_right, hG]
  have hnd : ∀ x, (∀ y, formB ε x y = 0) → x = 0 := by
    intro x hx
    apply eq_zero_of_hJ ε
    intro y
    rw [← hJ_conj ε x y, ← formB_apply, hx y, star_zero]
  obtain ⟨g, hgiso, hgext⟩ := witt_extension_theorem ℂ (Fin n → ℂ) (formB ε)
    (fun x y => hJ_conj ε x y) hnd U f finj hiso
  let A : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
  let Ai : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (g.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
  have hA : ∀ v, A *ᵥ v = g v := fun v => LinearMap.toMatrix'_mulVec _ v
  have hAi : ∀ v, Ai *ᵥ v = g.symm v := fun v => LinearMap.toMatrix'_mulVec _ v
  have h1 : A * Ai = 1 := mat_eq_of_mulVec fun v => by
    rw [← mulVec_mulVec, hAi, hA, one_mulVec, LinearEquiv.apply_symm_apply]
  have h2 : Ai * A = 1 := mat_eq_of_mulVec fun v => by
    rw [← mulVec_mulVec, hA, hAi, one_mulVec, LinearEquiv.symm_apply_apply]
  have hmem : Formalism.REAL.inUJ ε A := inUJ_of_iso ε A fun x y => by
    rw [hA, hA, ← formB_apply, hgiso, formB_apply]
  refine ⟨⟨⟨A, Ai, h1, h2⟩, hmem⟩, fun i => ?_⟩
  show A *ᵥ s i = t i
  rw [hA]
  have := hgext (bs i)
  rw [Module.Basis.span_apply] at this
  rw [this, ← Module.Basis.span_apply hs i]
  exact hf i

end Witt

section Rot

variable {n : ℕ} (ε : Fin n → Bool)

def rotM (ω : Fin n → ℂ) (φ : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (if i = j then 1 else 0) + (φ - 1) * ω i * (star (ω j) * (if ε j then 1 else -1))

theorem rotM_mulVec (ω : Fin n → ℂ) (φ : ℂ) (v : Fin n → ℂ) :
    rotM ε ω φ *ᵥ v = v + ((φ - 1) * hJ ε ω v) • ω := by
  funext i
  simp only [rotM, mulVec, dotProduct, of_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    hJ_apply]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring

theorem rotM_mul (ω : Fin n → ℂ) (hω : hJ ε ω ω = 1) (α β : ℂ) (hab : α * β = 1) :
    rotM ε ω α * rotM ε ω β = 1 := mat_eq_of_mulVec fun v => by
  rw [← mulVec_mulVec, rotM_mulVec, rotM_mulVec, hJ_add_right, hJ_smul_right, hω, one_mulVec, add_assoc,
    ← add_smul]
  have e : ∀ c : ℂ, c = 0 → v + c • ω = v := fun c hc => by rw [hc, zero_smul, add_zero]
  apply e
  linear_combination (hJ ε ω v) * hab

theorem rotM_iso (ω : Fin n → ℂ) (hω : hJ ε ω ω = 1) (φ : ℂ) (hφ : star φ * φ = 1) (x y : Fin n → ℂ) :
    hJ ε (rotM ε ω φ *ᵥ x) (rotM ε ω φ *ᵥ y) = hJ ε x y := by
  simp only [rotM_mulVec, hJ_add_left, hJ_add_right, hJ_smul_left, hJ_smul_right, hω, star_mul', star_sub,
    star_one]
  rw [← hJ_conj ε ω x]
  linear_combination (star (hJ ε ω x) * hJ ε ω y) * hφ

def rotU (ω : Fin n → ℂ) (hω : hJ ε ω ω = 1) (φ : ℂ) (hφ : star φ * φ = 1) : Formalism.REAL.UJ ε :=
  ⟨⟨rotM ε ω φ, rotM ε ω (star φ), rotM_mul ε ω hω _ _ (by rw [mul_comm]; exact hφ),
    rotM_mul ε ω hω _ _ hφ⟩, inUJ_of_iso ε _ (rotM_iso ε ω hω φ hφ)⟩

theorem rotU_mulVec (ω : Fin n → ℂ) (hω : hJ ε ω ω = 1) (φ : ℂ) (hφ : star φ * φ = 1) (v : Fin n → ℂ) :
    uMat (rotU ε ω hω φ hφ) *ᵥ v = v + ((φ - 1) * hJ ε ω v) • ω :=
  rotM_mulVec ε ω φ v

end Rot

end Formalism.L2.SG.RealObj.InfCut.PtRepPf
end
end

noncomputable section

open Matrix Formalism.MainNotions.S
open scoped ComplexOrder

namespace Formalism.L2.SG.RealObj.InfCut.PtRepPf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

section Frame

variable {n : ℕ} (ε : Fin n → Bool)

structure Fr (r k : ℕ) where
  e : Fin r → Fin n → ℂ
  fd : Fin r → Fin n → ℂ
  z : Fin n → ℂ
  wb : Fin k → Fin n → ℂ
  T : ℝ
  T_pos : 0 < T
  card : n = r + r + (1 + k)
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ff : ∀ a b, hJ ε (fd a) (fd b) = 0
  ef : ∀ a b, hJ ε (e a) (fd b) = if a = b then 1 else 0
  ez : ∀ a, hJ ε (e a) z = 0
  fz : ∀ a, hJ ε (fd a) z = 0
  zz : hJ ε z z = -(T : ℂ)
  ww : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0
  ew : ∀ a i, hJ ε (e a) (wb i) = 0
  fw : ∀ a i, hJ ε (fd a) (wb i) = 0
  zw : ∀ i, hJ ε z (wb i) = 0

variable {ε}

theorem swapJ {x y : Fin n → ℂ} {c : ℂ} (h : hJ ε x y = c) : hJ ε y x = star c := by
  rw [← h]
  simp only [hJ, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, star_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [star_mul'] <;> ring

theorem fam_cs {r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (a : Fin r) :
    fam e z (Fin.castSucc a) = e a := by
  simp [fam]

theorem fam_last {r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : fam e z (Fin.last r) = z := by
  simp [fam]

namespace Fr

variable {r k : ℕ} (F : Fr ε r k)

theorem fe (a b : Fin r) : hJ ε (F.fd a) (F.e b) = if a = b then 1 else 0 := by
  rw [swapJ (F.ef b a)]
  by_cases h : a = b
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem ze (a : Fin r) : hJ ε F.z (F.e a) = 0 := by
  rw [swapJ (F.ez a), star_zero]
theorem zf (a : Fin r) : hJ ε F.z (F.fd a) = 0 := by
  rw [swapJ (F.fz a), star_zero]
theorem we (i : Fin k) (a : Fin r) : hJ ε (F.wb i) (F.e a) = 0 := by
  rw [swapJ (F.ew a i), star_zero]
theorem wf (i : Fin k) (a : Fin r) : hJ ε (F.wb i) (F.fd a) = 0 := by
  rw [swapJ (F.fw a i), star_zero]
theorem wz (i : Fin k) : hJ ε (F.wb i) F.z = 0 := by
  rw [swapJ (F.zw i), star_zero]

theorem T_ne : (F.T : ℂ) ≠ 0 := by
  exact_mod_cast F.T_pos.ne'

theorem star_cz : star (-(F.T : ℂ)⁻¹) = -(F.T : ℂ)⁻¹ := by
  simp [Complex.star_def]

def zd : Fin n → ℂ := (-(F.T : ℂ)⁻¹) • F.z

private lemma hJ_smul_left_eq_star_mul (c : ℂ) (x y : Fin n → ℂ) : hJ ε (c • x) y = star c * hJ ε x y := by
  simp only [hJ, star_smul, smul_dotProduct, smul_eq_mul]

private lemma hJ_smul_right_gauge_lattice_shifts (c : ℂ) (x y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  simp only [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem frame_dual_z_pairing_one : hJ ε F.zd F.z = 1 := by
  rw [zd, hJ_smul_left_eq_star_mul, F.star_cz, F.zz]
  field_simp [F.T_ne]

theorem zd_zd : hJ ε F.zd F.zd = -(F.T : ℂ)⁻¹ := by
  rw [zd, hJ_smul_left_eq_star_mul, hJ_smul_right_gauge_lattice_shifts, F.star_cz, F.zz]
  field_simp [F.T_ne]

theorem zd_left (y : Fin n → ℂ) : hJ ε F.zd y = -(F.T : ℂ)⁻¹ * hJ ε F.z y := by
  rw [zd, hJ_smul_left_eq_star_mul, F.star_cz]

theorem zd_right (y : Fin n → ℂ) : hJ ε y F.zd = -(F.T : ℂ)⁻¹ * hJ ε y F.z := by
  rw [zd, hJ_smul_right_gauge_lattice_shifts]

theorem zd_e (a : Fin r) : hJ ε F.zd (F.e a) = 0 := by
  rw [F.zd_left, F.ze, mul_zero]
theorem zd_f (a : Fin r) : hJ ε F.zd (F.fd a) = 0 := by
  rw [F.zd_left, F.zf, mul_zero]
theorem zd_w (i : Fin k) : hJ ε F.zd (F.wb i) = 0 := by
  rw [F.zd_left, F.zw, mul_zero]
theorem e_zd (a : Fin r) : hJ ε (F.e a) F.zd = 0 := by
  rw [F.zd_right, F.ez, mul_zero]
theorem f_zd (a : Fin r) : hJ ε (F.fd a) F.zd = 0 := by
  rw [F.zd_right, F.fz, mul_zero]
theorem w_zd (i : Fin k) : hJ ε (F.wb i) F.zd = 0 := by
  rw [F.zd_right, F.wz, mul_zero]

abbrev Ix (r k : ℕ) := (Fin r ⊕ Fin r) ⊕ (Unit ⊕ Fin k)

def bv : Ix r k → Fin n → ℂ := Sum.elim (Sum.elim F.e F.fd) (Sum.elim (fun _ => F.z) F.wb)

def dv : Ix r k → Fin n → ℂ :=
  Sum.elim (Sum.elim F.fd F.e) (Sum.elim (fun _ => F.zd) F.wb)

theorem card_ix (G : Fr ε r k) : Fintype.card (Ix r k) = n := by
  simp only [Ix, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  exact G.card.symm

theorem dual (j i : Ix r k) : hJ ε (F.dv j) (F.bv i) = if j = i then 1 else 0 := by
  rcases j with (a | a) | (⟨⟩ | a) <;> rcases i with (b | b) | (⟨⟩ | b) <;>
    simp [dv, bv, F.fe, F.ff, F.fz, F.fw, F.ee, F.ef, F.ez, F.ew, F.zd_e, F.zd_f, F.frame_dual_z_pairing_one, F.zd_w,
      F.we, F.wf, F.wz, F.ww]

private lemma hJ_finset_sum_left' {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ a ∈ s, f a) y = ∑ a ∈ s, hJ ε (f a) y := by
  simp only [hJ, star_sum, sum_dotProduct]

private lemma hJ_finset_sum_right_eq_sum {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (f : ι → Fin n → ℂ) :
    hJ ε x (∑ a ∈ s, f a) = ∑ a ∈ s, hJ ε x (f a) := by
  simp only [hJ, Matrix.mulVec_sum, dotProduct_sum]

theorem pair (w y : Fin n → ℂ) (hw : ∀ a, hJ ε (F.e a) w = 0) (hy : ∀ a, hJ ε (F.e a) y = 0) :
    hJ ε w y = -(F.T : ℂ)⁻¹ * hJ ε F.z y * star (hJ ε F.z w) +
      ∑ i, hJ ε (F.wb i) y * star (hJ ε (F.wb i) w) := by
  have hcoef : ∀ (g : Ix r k → ℂ) (j : Ix r k), hJ ε (F.dv j) (∑ i, g i • F.bv i) = g j := by
    intro g j
    rw [hJ_finset_sum_right_eq_sum]
    simp only [hJ_smul_right_gauge_lattice_shifts, F.dual, mul_ite, mul_one, mul_zero]
    simp [Finset.sum_ite_eq]
  have hli : LinearIndependent ℂ F.bv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 := hcoef g j
    rw [hg] at h1
    rw [← h1]
    simp [hJ]
  have hspan := hli.span_eq_top_of_card_eq_finrank (by rw [F.card_ix, Module.finrank_fin_fun])
  have hwm : w ∈ Submodule.span ℂ (Set.range F.bv) := by
    rw [hspan]
    trivial
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hwm
  have hgj : ∀ j, g j = hJ ε (F.dv j) w := fun j => by rw [← hg, hcoef]
  conv_lhs => rw [← hg, hJ_finset_sum_left']
  simp only [hJ_smul_left_eq_star_mul, hgj]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [bv, dv, Sum.elim_inl, Sum.elim_inr, hy, hw, mul_zero, star_zero, zero_mul,
    Finset.sum_const_zero, zero_add, Fintype.univ_unit, Finset.sum_singleton]
  rw [F.zd_left, star_mul', F.star_cz]
  clear hcoef hli hspan hwm hg hgj hw hy
  rw [Finset.sum_congr rfl (fun i _ => mul_comm (star (hJ ε (F.wb i) w)) (hJ ε (F.wb i) y))]
  ring

theorem gf (a b : Fin (r + 1)) :
    hJ ε (fam F.e F.z a) (fam F.e F.z b) = if a = Fin.last r ∧ b = Fin.last r then -(F.T : ℂ) else 0 := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl <;>
    simp [fam_cs, fam_last, F.ee, F.ez, F.ze, F.zz, Fin.castSucc_ne_last]

theorem w_fam (i : Fin k) (a : Fin (r + 1)) : hJ ε (F.wb i) (fam F.e F.z a) = 0 := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;> simp [fam_cs, fam_last, F.we, F.wz]

theorem fam_w (a : Fin (r + 1)) (i : Fin k) : hJ ε (fam F.e F.z a) (F.wb i) = 0 := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;> simp [fam_cs, fam_last, F.ew, F.zw]

def Fv : Fin (r + 1) → Fin n → ℂ := fam F.fd F.zd

def E0 : Fin (r + 1) → Fin n → ℂ := fam F.e 0

theorem Fv_fam (a b : Fin (r + 1)) : hJ ε (F.Fv a) (fam F.e F.z b) = if a = b then 1 else 0 := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl <;>
    simp [Fv, fam_cs, fam_last, F.fe, F.fz, F.zd_e, F.frame_dual_z_pairing_one, Fin.castSucc_ne_last,
      (Fin.castSucc_ne_last _).symm]

theorem Fv_w (a : Fin (r + 1)) (i : Fin k) : hJ ε (F.Fv a) (F.wb i) = 0 := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;> simp [Fv, fam_cs, fam_last, F.fw, F.zd_w]

theorem w_Fv (i : Fin k) (a : Fin (r + 1)) : hJ ε (F.wb i) (F.Fv a) = 0 := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;> simp [Fv, fam_cs, fam_last, F.wf, F.w_zd]

theorem frame_w_e_zero_orthogonal (i : Fin k) (a : Fin (r + 1)) : hJ ε (F.wb i) (F.E0 a) = 0 := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl
  · simp [E0, fam_cs, F.we]
  · simp [E0, fam_last, hJ]

def yv (i0 : Fin k) (Z Aα : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (t : Fin (r + 1) → ℂ) (b : Fin (r + 1)) :
    Fin n → ℂ :=
  ∑ a, Z a b • F.Fv a + ∑ a, Aα a b • F.E0 a + t b • F.wb i0

variable (i0 : Fin k) (Z Aα : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (t : Fin (r + 1) → ℂ)

private lemma hJ_add_right_gauge_lattice_shifts (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  simp only [hJ, Matrix.mulVec_add, dotProduct_add]

private lemma hJ_finset_sum_right' {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (f : ι → Fin n → ℂ) :
    hJ ε x (∑ a ∈ s, f a) = ∑ a ∈ s, hJ ε x (f a) := by
  simp only [hJ, Matrix.mulVec_sum, dotProduct_sum]

theorem pair_yv (x : Fin n → ℂ) (b : Fin (r + 1)) :
    hJ ε x (F.yv i0 Z Aα t b) =
      ∑ a, Z a b * hJ ε x (F.Fv a) + ∑ a, Aα a b * hJ ε x (F.E0 a) + t b * hJ ε x (F.wb i0) := by
  unfold yv
  rw [hJ_add_right_gauge_lattice_shifts, hJ_add_right_gauge_lattice_shifts, hJ_finset_sum_right', hJ_finset_sum_right', hJ_smul_right_gauge_lattice_shifts]
  simp only [hJ_smul_right_gauge_lattice_shifts]

theorem p1 (a b : Fin (r + 1)) : hJ ε (fam F.e F.z a) (F.yv i0 Z Aα t b) = Z a b := by
  rw [F.pair_yv]
  have h1 : ∀ c, hJ ε (fam F.e F.z a) (F.Fv c) = if c = a then 1 else 0 := fun c => by
    rw [swapJ (F.Fv_fam c a)]
    split_ifs <;> simp
  have h2 : ∀ c, hJ ε (fam F.e F.z a) (F.E0 c) = 0 := fun c => by
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last c with ⟨c, rfl⟩ | rfl <;>
      first
      | (simp [E0, fam_cs, fam_last, F.ee, F.ze]; done)
      | (simp [E0, fam_cs, fam_last, hJ]; done)
  simp only [h1, h2, F.fam_w, mul_zero, Finset.sum_const_zero, add_zero, mul_ite, mul_one]
  simp [Finset.sum_ite_eq']

theorem p2 (hA : ∀ j, Aα (Fin.last r) j = 0) (a c : Fin (r + 1)) :
    hJ ε (F.Fv a) (F.yv i0 Z Aα t c) =
      (if a = Fin.last r then -(F.T : ℂ)⁻¹ * Z (Fin.last r) c else 0) + Aα a c := by
  rw [F.pair_yv]
  have h1 : ∀ d, hJ ε (F.Fv a) (F.Fv d) =
      if a = Fin.last r ∧ d = Fin.last r then -(F.T : ℂ)⁻¹ else 0 := fun d => by
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last d with ⟨d, rfl⟩ | rfl <;>
      simp [Fv, fam_cs, fam_last, F.ff, F.f_zd, F.zd_f, F.zd_zd, Fin.castSucc_ne_last]
  have h2 : ∀ d, hJ ε (F.Fv a) (F.E0 d) = if d = a ∧ a ≠ Fin.last r then 1 else 0 := fun d => by
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last d with ⟨d, rfl⟩ | rfl
    · simp [Fv, E0, fam_cs, F.fe, Fin.castSucc_ne_last, eq_comm]
    · simp [Fv, E0, fam_cs, fam_last, hJ, (Fin.castSucc_ne_last _).symm]
    · simp [Fv, E0, fam_cs, fam_last, F.zd_e]
    · simp [Fv, E0, fam_last, hJ]
  simp only [h1, h2, F.Fv_w, mul_zero, add_zero]
  by_cases ha : a = Fin.last r
  · subst ha
    simp [hA, mul_comm]
  · simp [ha, mul_ite, Finset.sum_ite_eq']

theorem p3 (a c : Fin (r + 1)) :
    hJ ε (F.E0 a) (F.yv i0 Z Aα t c) = if a = Fin.last r then 0 else Z a c := by
  rw [F.pair_yv]
  have h1 : ∀ d, hJ ε (F.E0 a) (F.Fv d) = if a = Fin.last r then 0 else (if d = a then 1 else 0) := fun d => by
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last d with ⟨d, rfl⟩ | rfl <;>
      first
      | (simp [E0, Fv, fam_cs, fam_last, F.ef, F.e_zd, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm, eq_comm]; done)
      | (simp [E0, Fv, fam_cs, fam_last, hJ]; done)
  have h2 : ∀ d, hJ ε (F.E0 a) (F.E0 d) = 0 := fun d => by
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last d with ⟨d, rfl⟩ | rfl <;>
      first
      | (simp [E0, fam_cs, fam_last, F.ee]; done)
      | (simp [E0, fam_cs, fam_last, hJ]; done)
  have h3 : hJ ε (F.E0 a) (F.wb i0) = 0 := by
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl
    · simp [E0, fam_cs, F.ew]
    · simp [E0, fam_last, hJ]
  simp only [h1, h2, h3, mul_zero, Finset.sum_const_zero, add_zero]
  split_ifs with ha
  · simp
  · simp [mul_ite, Finset.sum_ite_eq']

theorem p4 (i : Fin k) (c : Fin (r + 1)) :
    hJ ε (F.wb i) (F.yv i0 Z Aα t c) = if i = i0 then t c else 0 := by
  rw [F.pair_yv]
  simp only [F.w_Fv, F.frame_w_e_zero_orthogonal, mul_zero, Finset.sum_const_zero, zero_add, F.ww]
  split_ifs with h
  · subst h
    simp
  · simp [Ne.symm h]

private lemma hJ_yv_left_eq_sum (y : Fin n → ℂ) (b : Fin (r + 1)) :
    hJ ε (F.yv i0 Z Aα t b) y = ∑ a, star (Z a b) * hJ ε (F.Fv a) y +
      ∑ a, star (Aα a b) * hJ ε (F.E0 a) y + star (t b) * hJ ε (F.wb i0) y := by
  have hs : ∀ x, star (hJ ε y x) = hJ ε x y := fun x => (swapJ rfl).symm
  rw [swapJ (rfl : hJ ε y (F.yv i0 Z Aα t b) = _), F.pair_yv]
  simp only [star_add, star_sum, star_mul', hs]

theorem gram (hA : ∀ j, Aα (Fin.last r) j = 0) (b c : Fin (r + 1)) :
    hJ ε (F.yv i0 Z Aα t b) (F.yv i0 Z Aα t c) =
      -(F.T : ℂ)⁻¹ * (star (Z (Fin.last r) b) * Z (Fin.last r) c) + (Zᴴ * Aα) b c + (Aαᴴ * Z) b c +
        star (t b) * t c := by
  rw [hJ_yv_left_eq_sum, F.p4 i0 Z Aα t i0 c, if_pos rfl]
  simp only [F.p2 i0 Z Aα t hA, F.p3 i0 Z Aα t]
  have hAZ : ∑ a, star (Aα a b) * (if a = Fin.last r then 0 else Z a c) = ∑ a, star (Aα a b) * Z a c := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a = Fin.last r
    · subst ha
      simp [hA]
    · simp [ha]
  rw [hAZ, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end Fr

end Frame

section Mat

variable {m : ℕ}

theorem dot_vmv (x a b y : Fin m → ℂ) : star x ⬝ᵥ (vecMulVec a b *ᵥ y) = (star x ⬝ᵥ a) * (b ⬝ᵥ y) := by
  simp only [dotProduct, mulVec, vecMulVec, Matrix.of_apply]
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem solveHerm (Z Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hZ : IsUnit Z.det) (hQ : Qᴴ = Q)
    (hc : star (Z⁻¹ *ᵥ Pi.single (Fin.last m) 1) ⬝ᵥ (Q *ᵥ (Z⁻¹ *ᵥ Pi.single (Fin.last m) 1)) = 0) :
    ∃ A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, (∀ j, A (Fin.last m) j = 0) ∧ Zᴴ * A + Aᴴ * Z = Q := by
  set e : Fin (m + 1) → ℂ := Pi.single (Fin.last m) 1 with he
  set c : Fin (m + 1) → ℂ := Z⁻¹ *ᵥ e with hcdef
  have hZc : Z *ᵥ c = e := by
    rw [hcdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hZ, Matrix.one_mulVec]
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, Matrix.mulVec_zero] at hZc
    have h1 := congrFun hZc (Fin.last m)
    simp [he] at h1
  have hs : star c ⬝ᵥ c ≠ 0 := fun h0 => hc0 (dotProduct_star_self_eq_zero.1 h0)
  set q := Q *ᵥ c with hq
  set c' := (star c ⬝ᵥ c)⁻¹ • c with hc'
  set W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    (1 / 2 : ℂ) • Q + (1 / 2 : ℂ) • (vecMulVec q (star c') - vecMulVec c' (star q)) with hW
  have hZH : IsUnit (Zᴴ).det := by
    rw [det_conjTranspose]
    exact hZ.star
  refine ⟨(Zᴴ)⁻¹ * W, ?_, ?_⟩
  · intro j
    have hrow : ∀ k, (Zᴴ)⁻¹ (Fin.last m) k = star (c k) := by
      intro k
      rw [← Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_apply, hcdef]
      simp [Matrix.mulVec, dotProduct, he, Pi.single_apply]
    have hvv : ∀ (x a b : Fin (m + 1) → ℂ), x ᵥ* vecMulVec a b = (x ⬝ᵥ a) • b := by
      intro x a b
      ext l
      simp [Matrix.vecMul, dotProduct, vecMulVec, Finset.sum_mul, mul_assoc]
    have hcq : star c ⬝ᵥ q = 0 := hc
    have hcc : star c ⬝ᵥ c' = 1 := by
      rw [hc', dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hs]
    have hsq : star c ᵥ* Q = star q := by
      rw [hq, Matrix.star_mulVec Q c, hQ]
    have hv : star c ᵥ* W = 0 := by
      rw [hW, Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_smul, Matrix.vecMul_sub, hvv, hvv,
        hcq, hcc, hsq]
      ext l
      simp
    have h2 := congrFun hv j
    rw [Matrix.mul_apply]
    simp only [hrow]
    simpa [Matrix.vecMul, dotProduct] using h2
  · have h1 : Zᴴ * ((Zᴴ)⁻¹ * W) = W := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hZH, Matrix.one_mul]
    have h2 : ((Zᴴ)⁻¹ * W)ᴴ * Z = Wᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hZ, Matrix.mul_one]
    rw [h1, h2]
    ext a b
    simp only [hW, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply,
      vecMulVec, Matrix.of_apply, smul_eq_mul, star_add, star_mul', star_sub, Pi.star_apply, star_star]
    have hQab : star (Q b a) = Q a b := by
      have := congrFun (congrFun hQ a) b
      rwa [Matrix.conjTranspose_apply] at this
    rw [hQab]
    simp
    ring

theorem dl_top {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Dl Z (r + 1) = Z.det := by
  unfold Dl
  rw [dite_eq_left le_rfl]
  congr 1

theorem dl_r {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Dl Z r = adjugate Z (Fin.last r) (Fin.last r) := by
  unfold Dl
  rw [dite_eq_left (Nat.le_succ r), Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  have h1 : (Fin.castLE (Nat.le_succ r) : Fin r → Fin (r + 1)) = Fin.castSucc := by
    funext i
    exact Fin.ext rfl
  rw [h1, Even.neg_one_pow ⟨_, rfl⟩, one_mul]

theorem inv_last {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Z⁻¹ (Fin.last r) (Fin.last r) = (Z.det)⁻¹ * Dl Z r := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', dl_r]

theorem gv_facts {r : ℕ} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hG : 0 < Gv T T' Z) : IsUnit Z.det ∧ T * T' * ‖Z⁻¹ (Fin.last r) (Fin.last r)‖ ^ 2 < 1 := by
  unfold Gv at hG
  rw [dl_top] at hG
  have hdet : Z.det ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hG
    nlinarith [sq_nonneg ‖Dl Z r‖, mul_pos hT hT']
  refine ⟨isUnit_iff_ne_zero.2 hdet, ?_⟩
  rw [inv_last, norm_mul, norm_inv, mul_pow, inv_pow]
  have hd : 0 < ‖Z.det‖ ^ 2 := by positivity
  rw [show T * T' * ((‖Z.det‖ ^ 2)⁻¹ * ‖Dl Z r‖ ^ 2) = (T * T' * ‖Dl Z r‖ ^ 2) / ‖Z.det‖ ^ 2 by ring]
  rw [div_lt_one hd]
  linarith

end Mat

end Formalism.L2.SG.RealObj.InfCut.PtRepPf
end
end

noncomputable section

open Matrix Formalism.MainNotions.S
open scoped ComplexOrder

namespace Formalism.L2.SG.RealObj.InfCut.PtRepPf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ}

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by simp [uMat]

theorem eN_single (i0 : Fin k) (z : ℂ) : eN (Pi.single i0 z) = ‖z‖ := by
  unfold eN
  rw [Finset.sum_eq_single i0 (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same,
    Real.sqrt_sq (norm_nonneg _)]

theorem single_last_smul (L : Fin (r + 1)) (d : ℂ) : Pi.single L d = d • Pi.single L (1 : ℂ) := by
  funext j
  by_cases hj : j = L
  · subst hj; simp
  · simp [hj]

theorem realize (A B : Fr ε r k) (i0 : Fin k) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hZ : IsUnit Z.det)
    (σ : ℝ) (hσ2 : σ ^ 2 = (A.T)⁻¹ - B.T * ‖(Z⁻¹ *ᵥ Pi.single (Fin.last r) 1) (Fin.last r)‖ ^ 2) :
    ∃ g : Formalism.REAL.UJ ε, ∃ y : Fin (r + 1) → Fin n → ℂ, ∃ t : Fin (r + 1) → ℂ,
      t ⬝ᵥ (Z⁻¹ *ᵥ Pi.single (Fin.last r) 1) = σ ∧
      (∀ b, uMat g *ᵥ fam B.e B.z b = y b) ∧ (∀ i, i ≠ i0 → uMat g *ᵥ B.wb i = A.wb i) ∧
      (∀ a b, hJ ε (fam A.e A.z a) (y b) = Z a b) ∧
      (∀ i b, hJ ε (A.wb i) (y b) = if i = i0 then t b else 0) := by
  classical
  set L := Fin.last r with hL
  set c := Z⁻¹ *ᵥ Pi.single L 1 with hcdef
  have hZc : Z *ᵥ c = Pi.single L 1 := by rw [hcdef, mulVec_mulVec, mul_nonsing_inv _ hZ, one_mulVec]
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, mulVec_zero] at hZc
    have := congrFun hZc L
    simp at this
  obtain ⟨N, hNdef⟩ : ∃ N : ℂ, N = star c ⬝ᵥ c := ⟨_, rfl⟩
  have hN : N ≠ 0 := by rw [hNdef]; exact fun h => hc0 (dotProduct_star_self_eq_zero.1 h)
  obtain ⟨t, htdef⟩ : ∃ t : Fin (r + 1) → ℂ, t = ((σ : ℂ) / N) • star c := ⟨_, rfl⟩
  have htc : t ⬝ᵥ c = σ := by rw [htdef, smul_dotProduct, smul_eq_mul, ← hNdef, div_mul_cancel₀ _ hN]
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ,
      Γ = Matrix.of fun b c' => if b = L then (if c' = L then -(B.T : ℂ) else 0) else 0 := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ,
      Q = Γ + ((A.T : ℂ)⁻¹) • vecMulVec (star (Z L)) (Z L) - vecMulVec (star t) t := ⟨_, rfl⟩
  have hAstar : star ((A.T : ℂ)⁻¹) = (A.T : ℂ)⁻¹ := by rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hBstar : star (-(B.T : ℂ)) = -(B.T : ℂ) := by rw [star_neg, Complex.star_def, Complex.conj_ofReal]
  have hQ : Qᴴ = Q := by
    ext b c'
    simp only [hQdef, hΓ, conjTranspose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, of_apply,
      vecMulVec_apply, Pi.star_apply, smul_eq_mul, star_add, star_sub, star_mul', star_star, hAstar]
    by_cases hb : b = L <;> by_cases hc : c' = L <;> simp [hb, hc, hBstar] <;> ring
  have hzc : Z L ⬝ᵥ c = 1 := by
    have := congrFun hZc L
    simpa [mulVec] using this
  have hΓv : Γ *ᵥ c = Pi.single L (-(B.T : ℂ) * c L) := by
    funext b
    by_cases hb : b = L
    · subst hb; simp [hΓ, mulVec, dotProduct, Finset.sum_ite_eq']
    · simp [hΓ, mulVec, dotProduct, hb]
  have hcQ : star c ⬝ᵥ (Q *ᵥ c) = 0 := by
    rw [hQdef, sub_mulVec, add_mulVec, smul_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul, dot_vmv,
      dot_vmv, hΓv, dotProduct_single, star_dotProduct_star, star_dotProduct_star, hzc, htc, smul_eq_mul,
      star_one, mul_one, mul_one]
    have h1 : star (c L) * c L = ((‖c L‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
    have h2 : star (σ : ℂ) * σ = ((σ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
    rw [h2, hσ2, Pi.star_apply, show star (c L) * (-(B.T : ℂ) * c L) = -(B.T : ℂ) * (star (c L) * c L) by ring, h1]
    push_cast
    ring
  obtain ⟨Aα, hAlast, hAeq⟩ := solveHerm Z Q hZ hQ hcQ
  set y := A.yv i0 Z Aα t with hydef
  have hgram : ∀ b c', hJ ε (y b) (y c') = hJ ε (fam B.e B.z b) (fam B.e B.z c') := by
    intro b c'
    rw [hydef, A.gram i0 Z Aα t hAlast, B.gf]
    have hq := congrFun (congrFun hAeq b) c'
    rw [Matrix.add_apply] at hq
    have hQbc : Q b c' = Γ b c' + (A.T : ℂ)⁻¹ * (star (Z L b) * Z L c') - star (t b) * t c' := by
      simp [hQdef, vecMulVec_apply]
    have hΓbc : Γ b c' = if b = L ∧ c' = L then -(B.T : ℂ) else 0 := by
      rw [hΓ, of_apply]
      by_cases hb : b = L <;> by_cases hc : c' = L <;> simp [hb, hc]
    rw [← hΓbc]
    linear_combination hq + hQbc
  let s : (Fin (r + 1) ⊕ {i : Fin k // i ≠ i0}) → Fin n → ℂ := Sum.elim (fam B.e B.z) (fun i => B.wb i.1)
  let tt : (Fin (r + 1) ⊕ {i : Fin k // i ≠ i0}) → Fin n → ℂ := Sum.elim y (fun i => A.wb i.1)
  have hs : LinearIndependent ℂ s :=
    li_of_pair ε s (Sum.elim B.Fv (fun i => B.wb i.1)) 1 (by simp) (by
      rintro (a|j) (b|i)
      · simp [s, B.Fv_fam, Matrix.one_apply]
      · simp [s, B.Fv_w]
      · simp [s, B.w_fam]
      · simp [s, B.ww, Matrix.one_apply, Subtype.coe_inj])
  have ht : LinearIndependent ℂ tt :=
    li_of_pair ε tt (Sum.elim (fam A.e A.z) (fun i => A.wb i.1)) (Matrix.fromBlocks Z 0 0 1)
      (by rw [det_fromBlocks_zero₂₁, det_one, mul_one]; exact hZ) (by
      rintro (a|j) (b|i)
      · simp [tt, hydef, A.p1]
      · simp [tt, A.fam_w]
      · simp [tt, hydef, A.p4, j.2]
      · simp [tt, A.ww, Matrix.one_apply, Subtype.coe_inj])
  have hG : ∀ i j, hJ ε (tt i) (tt j) = hJ ε (s i) (s j) := by
    rintro (b|i) (c'|j)
    · exact hgram b c'
    · show hJ ε (y b) (A.wb j.1) = hJ ε (fam B.e B.z b) (B.wb j.1)
      rw [swapJ (A.p4 i0 Z Aα t j.1 b), if_neg j.2, star_zero, B.fam_w]
    · show hJ ε (A.wb i.1) (y c') = hJ ε (B.wb i.1) (fam B.e B.z c')
      rw [hydef, A.p4, if_neg i.2, B.w_fam]
    · show hJ ε (A.wb i.1) (A.wb j.1) = hJ ε (B.wb i.1) (B.wb j.1)
      rw [A.ww, B.ww]
  obtain ⟨g, hg⟩ := wittFam ε s tt hs ht hG
  exact ⟨g, y, t, htc, fun b => hg (Sum.inl b), fun i hi => hg (Sum.inr ⟨i, hi⟩), A.p1 i0 Z Aα t,
    A.p4 i0 Z Aα t⟩

end Formalism.L2.SG.RealObj.InfCut.PtRepPf
