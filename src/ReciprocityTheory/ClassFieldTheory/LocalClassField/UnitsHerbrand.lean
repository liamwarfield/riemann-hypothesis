module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic

@[expose] public section

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandF
section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandE
section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandD
section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandC
section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandB
section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandA
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

section approx

variable {U : Type*} [CommGroup U]

theorem exists_of_approx (V : ℕ → Subgroup U)
    (hcomp : ∀ v : ℕ → U, (∀ k, v k ∈ V k) → ∃ s ∈ V 0, ∀ n, s / ∏ k ∈ range n, v k ∈ V n)
    (hsep : ∀ u, (∀ n, u ∈ V n) → u = 1) (Z : Subgroup U) (f : U →* U)
    (hfV : ∀ n, ∀ u ∈ V n, f u ∈ V n) (hfZ : ∀ u, f u ∈ Z)
    (step : ∀ n, ∀ u ∈ V n, u ∈ Z → ∃ v ∈ V n, u / f v ∈ V (n + 1)) :
    ∀ u ∈ V 0, u ∈ Z → ∃ v ∈ V 0, f v = u := by
  classical
  intro u hu hZ
  choose! c hc using step
  let w : ℕ → U := fun n => Nat.rec u (fun n x => x / f (c n x)) n
  have hw : ∀ n, w n ∈ V n ∧ w n ∈ Z := by
    intro n
    induction n with
    | zero => exact ⟨hu, hZ⟩
    | succ n ih => exact ⟨(hc n _ ih.1 ih.2).2, Z.div_mem ih.2 (hfZ _)⟩
  have hprod : ∀ n, w n = u / f (∏ k ∈ range n, c k (w k)) := by
    intro n
    induction n with
    | zero => simp [w]
    | succ n ih =>
      rw [prod_range_succ, map_mul, ← div_div, ← ih]
  obtain ⟨s, hs0, hs⟩ := hcomp (fun k => c k (w k)) (fun k => (hc k _ (hw k).1 (hw k).2).1)
  refine ⟨s, hs0, ?_⟩
  have h1 : u / f s = 1 := hsep _ fun n => by
    have h2 : u / f s = w n / f (s / ∏ k ∈ range n, c k (w k)) := by
      rw [hprod n, map_div, div_div_div_cancel_right]
    rw [h2]
    exact (V n).div_mem (hw n).1 (hfV n _ (hs n))
  exact (div_eq_one.1 h1).symm

end approx

variable {R : Type*} [Field R] (G : Type*) [Group G] [Fintype G] [MulSemiringAction G R]

structure Filt (I : ℕ → AddSubgroup R) (e : R →+ R) : Prop where
  anti : ∀ n, I (n + 1) ≤ I n
  mul : ∀ n x y, x ∈ I n → y ∈ I 0 → x * y ∈ I (n + 1)
  smul : ∀ n (g : G) x, x ∈ I n → g • x ∈ I n
  comp : ∀ x : ℕ → R, (∀ k, x k ∈ I k) → ∃ s, ∀ n, s - ∑ k ∈ range n, x k ∈ I n
  sep : ∀ x, (∀ n, x ∈ I n) → x = 0
  inv : ∀ n x, x ∈ I n → (1 + x)⁻¹ - 1 ∈ I n
  e_mem : ∀ n x, x ∈ I n → e x ∈ I n
  e_sum : ∀ x, ∑ g : G, g • e (g⁻¹ • x) = x

namespace Filt

variable {G} {I : ℕ → AddSubgroup R} {e : R →+ R} (h : Filt G I e)

include h

theorem le_zero (n : ℕ) : I n ≤ I 0 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (h.anti n).trans ih

theorem mul_unit {n : ℕ} {x u : R} (hx : x ∈ I n) (hu : u - 1 ∈ I 0) : x * u ∈ I n := by
  have : x * u = x * (u - 1) + x := by ring
  rw [this]
  exact (I n).add_mem (h.anti n (h.mul n _ _ hx hu)) hx

theorem one_add_ne_zero {x : R} (hx : x ∈ I 0) : 1 + x ≠ 0 := by
  intro h0
  have h1 : (1 : R) ∈ I 0 := by
    have : (1 : R) = - x := by linear_combination h0
    rw [this]; exact (I 0).neg_mem hx
  have hn : ∀ n, (1 : R) ∈ I n := by
    intro n
    induction n with
    | zero => exact h1
    | succ n ih => simpa using h.mul n 1 1 ih h1
  exact one_ne_zero (h.sep 1 hn)

def V (n : ℕ) : Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ I n}
  one_mem' := by simp
  mul_mem' := fun {u v} hu hv => by
    have hu' : (u : R) - 1 ∈ I n := hu
    have hv' : (v : R) - 1 ∈ I n := hv
    show ((u * v : Rˣ) : R) - 1 ∈ I n
    have : ((u * v : Rˣ) : R) - 1 = ((u : R) - 1) * v + ((v : R) - 1) := by
      rw [Units.val_mul]; ring
    rw [this]
    exact (I n).add_mem (h.mul_unit hu' (h.le_zero n hv')) hv'
  inv_mem' := fun {u} hu => by
    have hu' : (u : R) - 1 ∈ I n := hu
    show ((u⁻¹ : Rˣ) : R) - 1 ∈ I n
    have := h.inv n _ hu'
    rwa [add_sub_cancel, ← Units.val_inv_eq_inv_val] at this

theorem mem_V {n : ℕ} {u : Rˣ} : u ∈ h.V n ↔ (u : R) - 1 ∈ I n := Iff.rfl

theorem V_le_zero (n : ℕ) : h.V n ≤ h.V 0 := fun _ hu => h.le_zero n hu

noncomputable def mkU (x : R) (hx : x ∈ I 0) : Rˣ := Units.mk0 (1 + x) (h.one_add_ne_zero hx)

theorem mkU_val (x : R) (hx : x ∈ I 0) : (h.mkU x hx : R) = 1 + x := rfl

theorem mkU_mem {n : ℕ} (x : R) (hx : x ∈ I n) : h.mkU x (h.le_zero n hx) ∈ h.V n := by
  rw [mem_V, mkU_val, add_sub_cancel_left]; exact hx

theorem div_mem_V {n : ℕ} {u v : Rˣ} (hv : v ∈ h.V 0) (huv : (u : R) - v ∈ I n) : u / v ∈ h.V n := by
  rw [mem_V]
  have : ((u / v : Rˣ) : R) - 1 = ((u : R) - v) * ((v⁻¹ : Rˣ) : R) := by
    rw [div_eq_mul_inv, Units.val_mul, sub_mul, Units.mul_inv]
  rw [this]
  exact h.mul_unit huv ((h.V 0).inv_mem hv)

theorem prod_one_add {ι : Type*} {n : ℕ} (s : Finset ι) (y : ι → R) (hy : ∀ j ∈ s, y j ∈ I n) :
    ∏ j ∈ s, (1 + y j) - 1 - ∑ j ∈ s, y j ∈ I (n + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hE := ih fun j hj => hy j (mem_insert_of_mem hj)
    have hS : ∑ j ∈ s, y j ∈ I n := (I n).sum_mem fun j hj => hy j (mem_insert_of_mem hj)
    have hya := hy a (mem_insert_self a s)
    rw [prod_insert ha, sum_insert ha]
    have : (1 + y a) * ∏ j ∈ s, (1 + y j) - 1 - (y a + ∑ j ∈ s, y j) =
        (∏ j ∈ s, (1 + y j) - 1 - ∑ j ∈ s, y j) + y a * (∏ j ∈ s, (1 + y j) - 1 - ∑ j ∈ s, y j)
          + y a * ∑ j ∈ s, y j := by ring
    rw [this]
    exact (I (n + 1)).add_mem ((I (n + 1)).add_mem hE (h.mul n _ _ hya (h.le_zero _ hE)))
      (h.mul n _ _ hya (h.le_zero _ hS))

theorem V_comp (v : ℕ → Rˣ) (hv : ∀ k, v k ∈ h.V k) :
    ∃ s ∈ h.V 0, ∀ n, s / ∏ k ∈ range n, v k ∈ h.V n := by
  have hP : ∀ n, ∏ k ∈ range n, v k ∈ h.V 0 := fun n =>
    (h.V 0).prod_mem fun k _ => h.V_le_zero k (hv k)
  have hx : ∀ k, ((v k : R) - 1) * ((∏ j ∈ range k, v j : Rˣ) : R) ∈ I k := fun k =>
    h.mul_unit (hv k) (hP k)
  obtain ⟨t, ht⟩ := h.comp _ hx
  have hsum : ∀ n, ∑ k ∈ range n, ((v k : R) - 1) * ((∏ j ∈ range k, v j : Rˣ) : R) =
      ((∏ j ∈ range n, v j : Rˣ) : R) - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih, prod_range_succ, Units.val_mul]; ring
  have ht0 : t ∈ I 0 := by simpa using ht 0
  refine ⟨h.mkU t ht0, h.mkU_mem t ht0, fun n => h.div_mem_V (hP n) ?_⟩
  have := ht n
  rw [hsum] at this
  rw [mkU_val]
  convert this using 1
  ring

theorem V_sep (u : Rˣ) (hu : ∀ n, u ∈ h.V n) : u = 1 :=
  Units.ext (sub_eq_zero.1 (h.sep _ hu))

end Filt

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

variable {R : Type*} [Field R] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G R]

def act (g : G) : Rˣ →* Rˣ := Units.map (MulSemiringAction.toRingHom G R g : R →* R)

theorem act_val (g : G) (u : Rˣ) : ((act g u : Rˣ) : R) = g • (u : R) := rfl


variable (G) in
def normU : Rˣ →* Rˣ := ∏ g : G, act g

theorem normU_val (u : Rˣ) : ((normU G u : Rˣ) : R) = ∏ g : G, g • (u : R) := by
  simp [normU, Units.coe_prod, act_val]

theorem smul_prod_univ (g : G) (x : R) : g • ∏ g' : G, g' • x = ∏ g' : G, g' • x := by
  rw [← MulSemiringAction.toRingHom_apply, map_prod]
  simp only [MulSemiringAction.toRingHom_apply, smul_smul]
  exact Fintype.prod_equiv (Equiv.mulLeft g) _ _ fun _ => rfl

theorem prod_smul_smul (g : G) (x : R) : ∏ g' : G, g' • g • x = ∏ g' : G, g' • x := by
  simp only [smul_smul]
  exact Fintype.prod_equiv (Equiv.mulRight g) _ _ fun _ => rfl

theorem sum_pow_eq {g₀ : G} (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (f : G → R) :
    ∑ k ∈ range (orderOf g₀), f (g₀ ^ k) = ∑ g, f g := by
  classical
  rw [← IsCyclic.image_range_orderOf hg, sum_image]
  intro a ha b hb hab
  exact pow_injOn_Iio_orderOf (by simpa using ha) (by simpa using hb) hab

theorem telescope (g₀ : G) (z : R) (k : ℕ) :
    g₀ • ∑ j ∈ range k, g₀ ^ j • z - ∑ j ∈ range k, g₀ ^ j • z = g₀ ^ k • z - z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, smul_add, smul_smul, ← pow_succ']
    linear_combination ih

namespace Filt

variable {I : ℕ → AddSubgroup R} {e : R →+ R} (h : Filt G I e)

include h

theorem act_mem {n : ℕ} (g : G) {u : Rˣ} (hu : u ∈ h.V n) : act g u ∈ h.V n := by
  rw [mem_V, act_val]
  have := h.smul n g _ hu
  rwa [smul_sub, smul_one] at this

theorem normU_mem {n : ℕ} {u : Rˣ} (hu : u ∈ h.V n) : normU G u ∈ h.V n := by
  rw [normU, MonoidHom.finsetProd_apply]
  exact (h.V n).prod_mem fun g _ => h.act_mem g hu

theorem norm_surj (u : Rˣ) (hu : (u : R) - 1 ∈ I 0) (hfix : ∀ g : G, g • (u : R) = u) :
    ∃ v : Rˣ, (v : R) - 1 ∈ I 0 ∧ ∏ g : G, g • (v : R) = u := by
  let Z : Subgroup Rˣ :=
    { carrier := {u | ∀ g : G, act g u = u}
      one_mem' := fun g => map_one _
      mul_mem' := fun {a b} ha hb g => by rw [map_mul, ha g, hb g]
      inv_mem' := fun {a} ha g => by rw [map_inv, ha g] }
  have step : ∀ n, ∀ u ∈ h.V n, u ∈ Z → ∃ v ∈ h.V n, u / normU G v ∈ h.V (n + 1) := by
    intro n u hu hZ
    have hx : ∀ g : G, g • ((u : R) - 1) = (u : R) - 1 := fun g => by
      rw [smul_sub, smul_one, ← act_val, hZ g]
    have hy : e ((u : R) - 1) ∈ I n := h.e_mem n _ hu
    have htr : ∑ g : G, g • e ((u : R) - 1) = (u : R) - 1 := by
      conv_rhs => rw [← h.e_sum ((u : R) - 1)]
      exact Finset.sum_congr rfl fun g _ => by rw [hx]
    refine ⟨h.mkU _ (h.le_zero n hy), h.mkU_mem _ hy, h.div_mem_V (h.normU_mem (h.mkU_mem _ (h.le_zero n hy))) ?_⟩
    have hp := h.prod_one_add (n := n) univ (fun g : G => g • e ((u : R) - 1)) (fun g _ => h.smul n g _ hy)
    rw [htr] at hp
    rw [normU_val, mkU_val]
    simp only [smul_add, smul_one]
    have := (I (n + 1)).neg_mem hp
    convert this using 1
    ring
  obtain ⟨v, hv, hvu⟩ := exists_of_approx h.V h.V_comp h.V_sep Z (normU G)
    (fun n u hu => h.normU_mem hu)
    (fun u g => Units.ext (by rw [act_val, normU_val, smul_prod_univ])) step u hu
    (fun g => Units.ext (hfix g))
  exact ⟨v, hv, by rw [← normU_val, hvu]⟩

theorem hilbert90_matrix_subalgebra_norm_one (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (u : Rˣ) (hu : (u : R) - 1 ∈ I 0)
    (hN : ∏ g : G, g • (u : R) = 1) :
    ∃ v : Rˣ, (v : R) - 1 ∈ I 0 ∧ g₀ • (v : R) = u * v := by
  have step : ∀ n, ∀ u ∈ h.V n, u ∈ (normU G).ker →
      ∃ v ∈ h.V n, u / (act g₀ / MonoidHom.id _ : Rˣ →* Rˣ) v ∈ h.V (n + 1) := by
    intro n u hu hZ
    set x : R := (u : R) - 1 with hxdef
    have hx : x ∈ I n := hu
    have hux : (u : R) = 1 + x := by rw [hxdef]; ring
    have htr : ∑ g : G, g • x ∈ I (n + 1) := by
      have hp := h.prod_one_add (n := n) univ (fun g : G => g • x) (fun g _ => h.smul n g _ hx)
      have h1 : ∏ g : G, (1 + g • x) = 1 := by
        have := congrArg Units.val (MonoidHom.mem_ker.1 hZ)
        rw [normU_val, hux] at this
        simpa only [smul_add, smul_one, Units.val_one] using this
      rw [h1, sub_self, zero_sub] at hp
      simpa using (I (n + 1)).neg_mem hp
    set y : R := ∑ k ∈ range (orderOf g₀), ∑ j ∈ range k, g₀ ^ j • e ((g₀ ^ k)⁻¹ • x) with hydef
    have hy : y ∈ I n := (I n).sum_mem fun k _ => (I n).sum_mem fun j _ =>
      h.smul n _ _ (h.e_mem n _ (h.smul n _ _ hx))
    have hd : g₀ • y - y = x - e (∑ g : G, g • x) := by
      rw [hydef, smul_sum, ← sum_sub_distrib]
      simp only [telescope]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [sum_sub_distrib, sum_pow_eq hg (fun g => g • e (g⁻¹ • x)), h.e_sum, ← map_sum,
        sum_pow_eq hg (fun g => g⁻¹ • x)]
      congr 2
      exact Fintype.sum_equiv (Equiv.inv G) _ _ fun _ => rfl
    have hy0 := h.le_zero n hy
    have hvV : h.mkU y hy0 ∈ h.V n := h.mkU_mem y hy
    refine ⟨h.mkU y hy0, hvV, h.div_mem_V
      ((h.V 0).div_mem (h.act_mem g₀ (h.V_le_zero n hvV)) (h.V_le_zero n hvV)) ?_⟩
    set z : R := (1 + y)⁻¹ - 1 with hzdef
    have hz : z ∈ I n := h.inv n y hy
    have hyz : (1 + y) * (1 + z) = 1 := by
      rw [hzdef, add_sub_cancel, mul_inv_cancel₀ (h.one_add_ne_zero hy0)]
    have hval : (((act g₀ / MonoidHom.id _ : Rˣ →* Rˣ) (h.mkU y hy0) : Rˣ) : R) = (1 + g₀ • y) * (1 + z) := by
      rw [MonoidHom.div_apply, MonoidHom.id_apply, div_eq_mul_inv, Units.val_mul, act_val,
        Units.val_inv_eq_inv_val, mkU_val, smul_add, smul_one, hzdef, add_sub_cancel]
    rw [hval, hux]
    have : 1 + x - (1 + g₀ • y) * (1 + z) = e (∑ g : G, g • x) - (g₀ • y - y) * z := by
      linear_combination -hyz - hd
    rw [this]
    exact (I (n + 1)).sub_mem (h.e_mem _ _ htr)
      (h.mul n _ _ ((I n).sub_mem (h.smul n _ _ hy) hy) (h.le_zero n hz))
  obtain ⟨v, hv, hvu⟩ := exists_of_approx h.V h.V_comp h.V_sep (normU G).ker (act g₀ / MonoidHom.id _)
    (fun n u hu => (h.V n).div_mem (h.act_mem g₀ hu) hu)
    (fun u => by
      rw [MonoidHom.mem_ker, MonoidHom.div_apply, MonoidHom.id_apply, map_div, div_eq_one]
      exact Units.ext (by rw [normU_val, normU_val, act_val, prod_smul_smul])) step u hu
    (Units.ext (by rw [normU_val, hN]; rfl))
  refine ⟨v, hv, ?_⟩
  rw [MonoidHom.div_apply, MonoidHom.id_apply, div_eq_iff_eq_mul] at hvu
  rw [← act_val, hvu, Units.val_mul]

end Filt

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

variable (K L : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

noncomputable def Phi : L ≃L[K] ((L ≃ₐ[K] L) → K) :=
  (IsGalois.normalBasis K L).equivFun.toContinuousLinearEquiv

variable {K L}

theorem Phi_symm_apply (c : (L ≃ₐ[K] L) → K) :
    (Phi K L).symm c = ∑ σ, c σ • σ (IsGalois.normalBasis K L 1) := by
  show (IsGalois.normalBasis K L).equivFun.symm c = _
  rw [Module.Basis.equivFun_symm_apply]
  exact Finset.sum_congr rfl fun σ _ => by rw [IsGalois.normalBasis_apply]

theorem Phi_map (σ : L ≃ₐ[K] L) (x : L) (τ : L ≃ₐ[K] L) : Phi K L (σ x) τ = Phi K L x (σ⁻¹ * τ) := by
  have : σ x = (Phi K L).symm (fun τ => Phi K L x (σ⁻¹ * τ)) := by
    rw [Phi_symm_apply]
    calc σ x = σ ((Phi K L).symm (Phi K L x)) := by simp
      _ = ∑ ρ, Phi K L x ρ • (σ * ρ) (IsGalois.normalBasis K L 1) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Phi_symm_apply, map_sum]
        exact Finset.sum_congr rfl fun ρ _ => by rw [map_smul]; rfl
      _ = ∑ τ, Phi K L x (σ⁻¹ * τ) • τ (IsGalois.normalBasis K L 1) :=
        Fintype.sum_equiv (Equiv.mulLeft σ) _ _ (fun ρ => by simp)
  rw [this, ContinuousLinearEquiv.apply_symm_apply]

theorem norm_Phi_map (σ : L ≃ₐ[K] L) (x : L) : ‖Phi K L (σ x)‖ ≤ ‖Phi K L x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro τ
  rw [Phi_map]
  exact norm_le_pi_norm _ _


variable (K L) in
noncomputable def proj1 : L →+ L where
  toFun x := Phi K L x 1 • IsGalois.normalBasis K L 1
  map_zero' := by simp
  map_add' x y := by rw [map_add (f := _), Pi.add_apply, add_smul]

theorem norm_Phi_proj1 (x : L) : ‖Phi K L (proj1 K L x)‖ ≤ ‖Phi K L x‖ := by
  classical
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro τ
  show ‖Phi K L (Phi K L x 1 • IsGalois.normalBasis K L 1) τ‖ ≤ _
  rw [map_smul, Pi.smul_apply]
  have : Phi K L (IsGalois.normalBasis K L 1) τ = if 1 = τ then 1 else 0 :=
    Module.Basis.equivFun_self _ _ _
  rw [this, smul_eq_mul]
  split_ifs
  · rw [mul_one]; exact norm_le_pi_norm _ _
  · rw [mul_zero, norm_zero]; exact norm_nonneg _

theorem sum_proj1 (x : L) : ∑ σ : L ≃ₐ[K] L, σ • proj1 K L (σ⁻¹ • x) = x := by
  calc ∑ σ : L ≃ₐ[K] L, σ • proj1 K L (σ⁻¹ • x)
      = ∑ σ : L ≃ₐ[K] L, Phi K L x σ • σ (IsGalois.normalBasis K L 1) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        show σ (Phi K L (σ⁻¹ x) 1 • IsGalois.normalBasis K L 1) = _
        rw [map_smul, Phi_map, inv_inv, mul_one]
    _ = x := by rw [← Phi_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem norm_le_Phi (x : L) : ‖x‖ ≤ ‖((Phi K L).symm : ((L ≃ₐ[K] L) → K) →L[K] L)‖ * ‖Phi K L x‖ := by
  have := ((Phi K L).symm : ((L ≃ₐ[K] L) → K) →L[K] L).le_opNorm (Phi K L x)
  simpa using this

theorem norm_Phi_le (x : L) : ‖Phi K L x‖ ≤ ‖(Phi K L : L →L[K] ((L ≃ₐ[K] L) → K))‖ * ‖x‖ :=
  (Phi K L : L →L[K] ((L ≃ₐ[K] L) → K)).le_opNorm x

theorem exists_consts : ∃ A B C : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧ (∀ x : L, ‖x‖ ≤ A * ‖Phi K L x‖) ∧
    (∀ x : L, ‖Phi K L x‖ ≤ B * ‖x‖) ∧ ∀ x y : L, ‖Phi K L (x * y)‖ ≤ C * ‖Phi K L x‖ * ‖Phi K L y‖ := by
  set A := ‖((Phi K L).symm : ((L ≃ₐ[K] L) → K) →L[K] L)‖
  set B := ‖(Phi K L : L →L[K] ((L ≃ₐ[K] L) → K))‖
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  refine ⟨A, B, B * A * A, hA, hB, by positivity, norm_le_Phi, norm_Phi_le, fun x y => ?_⟩
  calc ‖Phi K L (x * y)‖ ≤ B * ‖x * y‖ := norm_Phi_le _
    _ = B * (‖x‖ * ‖y‖) := by rw [norm_mul]
    _ ≤ B * ((A * ‖Phi K L x‖) * (A * ‖Phi K L y‖)) := by
      gcongr
      · exact norm_le_Phi x
      · exact norm_le_Phi y
    _ = B * A * A * ‖Phi K L x‖ * ‖Phi K L y‖ := by ring


variable (K L) in
def ball (t : ℝ) (ht : 0 ≤ t) : AddSubgroup L where
  carrier := {x | ‖Phi K L x‖ ≤ t}
  zero_mem' := by simpa using ht
  add_mem' := fun {x y} hx hy => by
    show ‖Phi K L (x + y)‖ ≤ t
    rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  neg_mem' := fun {x} hx => by
    show ‖Phi K L (-x)‖ ≤ t
    rw [map_neg, norm_neg]; exact hx

theorem mem_ball {t : ℝ} {ht : 0 ≤ t} {x : L} : x ∈ ball K L t ht ↔ ‖Phi K L x‖ ≤ t := Iff.rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem rad_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) : 0 ≤ ρ * (1 / 2 : ℝ) ^ n := by positivity

theorem filt_ball {A C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hA1 : ∀ x : L, ‖x‖ ≤ A * ‖Phi K L x‖) (hA : 0 ≤ A)
    (hC1 : ∀ x y : L, ‖Phi K L (x * y)‖ ≤ C * ‖Phi K L x‖ * ‖Phi K L y‖)
    (hAρ : A * ρ < 1) (hCρ : C * ρ ≤ 1 / 2) :
    Filt (L ≃ₐ[K] L) (fun n => ball (K := K) (L := L) (ρ * (1 / 2 : ℝ) ^ n) (rad_nonneg hρ n)) (proj1 (K := K) (L := L)) := by
  refine {
    anti := ?_
    mul := ?_
    smul := ?_
    comp := ?_
    sep := ?_
    inv := ?_
    e_mem := ?_
    e_sum := ?_ }
  · intro n x hx
    change ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ (n + 1) at hx
    change ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ n
    refine hx.trans ?_
    rw [pow_succ]
    nlinarith [rad_nonneg hρ n]
  · intro n x y hx hy
    change ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ n at hx
    change ‖Phi K L y‖ ≤ ρ * (1 / 2 : ℝ) ^ 0 at hy
    change ‖Phi K L (x * y)‖ ≤ ρ * (1 / 2 : ℝ) ^ (n + 1)
    rw [pow_zero, mul_one] at hy
    calc ‖Phi K L (x * y)‖ ≤ C * ‖Phi K L x‖ * ‖Phi K L y‖ := hC1 x y
      _ ≤ C * (ρ * (1 / 2 : ℝ) ^ n) * ρ := by gcongr
      _ = (C * ρ) * (ρ * (1 / 2 : ℝ) ^ n) := by ring
      _ ≤ (1 / 2) * (ρ * (1 / 2 : ℝ) ^ n) := by
        exact mul_le_mul_of_nonneg_right hCρ (rad_nonneg hρ n)
      _ = ρ * (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
  · intro n g x hx
    exact (norm_Phi_map g x).trans hx
  · intro x hx
    have hx' : ∀ k, ‖Phi K L (x k)‖ ≤ ρ * (1 / 2 : ℝ) ^ k := fun k => by
      exact hx k
    have hsum : Summable fun k => Phi K L (x k) :=
      Summable.of_norm_bounded ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left ρ) hx'
    refine ⟨(Phi K L).symm (∑' k, Phi K L (x k)), fun n => ?_⟩
    change ‖Phi K L ((Phi K L).symm (∑' k, Phi K L (x k)) - ∑ k ∈ range n, x k)‖ ≤ ρ * (1 / 2 : ℝ) ^ n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, ContinuousLinearEquiv.apply_symm_apply, map_sum,
      ← hsum.sum_add_tsum_nat_add n, add_sub_cancel_left]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (rad_nonneg hρ n) fun k => ?_
    refine (hx' (k + n)).trans ?_
    gcongr ρ * ?_
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left n k)
  · intro x hx
    have hx' : ∀ n, ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ n := hx
    have hlim : Filter.Tendsto (fun n : ℕ => ρ * (1 / 2 : ℝ) ^ n) Filter.atTop (nhds (ρ * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul ρ
    have h0 : ‖Phi K L x‖ ≤ ρ * 0 := ge_of_tendsto' hlim hx'
    rw [mul_zero] at h0
    have := norm_le_zero_iff.1 h0
    simpa using this
  · intro n x hx
    change ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ n at hx
    change ‖Phi K L ((1 + x)⁻¹ - 1)‖ ≤ ρ * (1 / 2 : ℝ) ^ n
    have hr : ρ * (1 / 2 : ℝ) ^ n ≤ ρ := by
      have : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have hxlt : ‖x‖ < 1 := by
      refine lt_of_le_of_lt ((hA1 x).trans ?_) hAρ
      gcongr
      exact hx.trans hr
    have hne : 1 + x ≠ 0 := by
      intro h0
      have : x = -1 := by linear_combination h0
      rw [this, norm_neg, norm_one] at hxlt
      exact lt_irrefl _ hxlt
    set y : L := (1 + x)⁻¹ - 1 with hy
    have hy1 : y = -x + -(x * y) := by
      rw [hy]; field_simp; ring
    have h1 : ‖Phi K L y‖ ≤ max ‖Phi K L x‖ ‖Phi K L (x * y)‖ := by
      conv_lhs => rw [hy1, map_add (f := _), map_neg, map_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_neg, norm_neg]
    have h2 : ‖Phi K L (x * y)‖ ≤ (1 / 2) * ‖Phi K L y‖ := by
      refine (hC1 x y).trans ?_
      gcongr
      refine le_trans ?_ hCρ
      gcongr
      exact hx.trans hr
    rcases le_max_iff.1 h1 with h3 | h3
    · exact h3.trans hx
    · have : ‖Phi K L y‖ ≤ 0 := by linarith
      exact this.trans (rad_nonneg hρ n)
  · intro n x hx
    classical
    have hbound : ‖Phi K L (Phi K L x 1 • IsGalois.normalBasis K L 1)‖ ≤ ‖Phi K L x‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro τ
      show ‖Phi K L (Phi K L x 1 • IsGalois.normalBasis K L 1) τ‖ ≤ _
      rw [map_smul, Pi.smul_apply]
      have h : Phi K L (IsGalois.normalBasis K L 1) τ = if 1 = τ then 1 else 0 :=
        Module.Basis.equivFun_self _ _ _
      rw [h, smul_eq_mul]
      split_ifs
      · rw [mul_one]
        exact norm_le_pi_norm _ _
      · rw [mul_zero, norm_zero]
        exact norm_nonneg _
    exact hbound.trans (by change ‖Phi K L x‖ ≤ _; exact hx)
  · intro x
    calc ∑ σ : L ≃ₐ[K] L, σ • proj1 (K := K) (L := L) (σ⁻¹ • x)
        = ∑ σ : L ≃ₐ[K] L, Phi K L x σ • σ (IsGalois.normalBasis K L 1) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          show σ (Phi K L (σ⁻¹ • x) 1 • IsGalois.normalBasis K L 1) = _
          rw [map_smul]
          congr 1
          have h := Phi_map (σ⁻¹) x (1 : L ≃ₐ[K] L)
          simpa [inv_inv] using h
      _ = x := by
        rw [← Phi_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem exists_units_subgroup [IsUltrametricDist L] : ∃ S : Subgroup Lˣ,
    (∀ (σ : L ≃ₐ[K] L) (u v : Lˣ), u ∈ S → (v : L) = σ u → v ∈ S) ∧
    (∀ u ∈ S, ‖(u : L)‖ = 1) ∧ (∃ ε : ℝ, 0 < ε ∧ ∀ u : Lˣ, ‖(u : L) - 1‖ < ε → u ∈ S) ∧
    (∀ u ∈ S, (∀ σ : L ≃ₐ[K] L, σ (u : L) = u) → ∃ v ∈ S, ∏ σ : L ≃ₐ[K] L, σ (v : L) = u) ∧
    ∀ σ₀ : L ≃ₐ[K] L, (∀ σ, σ ∈ Subgroup.zpowers σ₀) → ∀ u ∈ S, ∏ σ : L ≃ₐ[K] L, σ (u : L) = 1 →
      ∃ v ∈ S, σ₀ (v : L) = u * v := by
  obtain ⟨A, B, C, hA, hB, hC, hA1, hB1, hC1⟩ := exists_consts (K := K) (L := L)
  set ρ : ℝ := (2 * (C + A + 1))⁻¹ with hρdef
  have hpos : 0 < 2 * (C + A + 1) := by positivity
  have hρ : 0 < ρ := inv_pos.2 hpos
  have hρ1 : ρ * (2 * (C + A + 1)) = 1 := inv_mul_cancel₀ hpos.ne'
  have hAρ : A * ρ < 1 := by nlinarith [mul_nonneg hC hρ.le, mul_nonneg hA hρ.le]
  have hCρ : C * ρ ≤ 1 / 2 := by nlinarith [mul_nonneg hC hρ.le, mul_nonneg hA hρ.le]
  have F := filt_ball hC hρ.le hA1 hA hC1 hAρ hCρ
  refine ⟨F.V 0, fun σ u v hu hv => ?_, fun u hu => ?_, ⟨ρ / (B + 1), by positivity, fun u hu => ?_⟩,
    fun u hu hfix => F.norm_surj u hu hfix, fun σ₀ hσ₀ u hu hN => F.hilbert90_matrix_subalgebra_norm_one σ₀ hσ₀ u hu hN⟩
  · have : v = act σ u := Units.ext hv
    rw [this]
    exact F.act_mem σ hu
  · have hu' : ‖Phi K L ((u : L) - 1)‖ ≤ ρ * (1 / 2 : ℝ) ^ 0 := hu
    rw [pow_zero, mul_one] at hu'
    have hlt : ‖(u : L) - 1‖ < 1 := by
      refine lt_of_le_of_lt ((hA1 _).trans ?_) hAρ
      gcongr
    have h1 : (u : L) = 1 + ((u : L) - 1) := by ring
    rw [h1, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne'), norm_one]
    exact max_eq_left hlt.le
  · show ‖Phi K L ((u : L) - 1)‖ ≤ ρ * (1 / 2 : ℝ) ^ 0
    rw [pow_zero, mul_one]
    refine (hB1 _).trans ?_
    have h2 : B * ‖(u : L) - 1‖ ≤ (B + 1) * (ρ / (B + 1)) := by
      gcongr
      · linarith
    refine h2.trans (le_of_eq ?_)
    field_simp

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem exists_units_subgroup_padic (hK : FiniteDimensional ℚ_[p] K) (E : IntermediateField K (PadicAlgCl p))
    [FiniteDimensional K E] [IsGalois K E] : ∃ S : Subgroup Eˣ,
    (∀ (σ : E ≃ₐ[K] E) (u v : Eˣ), u ∈ S → (v : E) = σ u → v ∈ S) ∧
    (∀ u ∈ S, ‖((u : E) : PadicAlgCl p)‖ = 1) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ u : Eˣ, ‖((u : E) : PadicAlgCl p) - 1‖ < ε → u ∈ S) ∧
    (∀ u ∈ S, (∀ σ : E ≃ₐ[K] E, σ (u : E) = u) → ∃ v ∈ S, ∏ σ : E ≃ₐ[K] E, σ (v : E) = u) ∧
    ∀ σ₀ : E ≃ₐ[K] E, (∀ σ, σ ∈ Subgroup.zpowers σ₀) → ∀ u ∈ S, ∏ σ : E ≃ₐ[K] E, σ (u : E) = 1 →
      ∃ v ∈ S, σ₀ (v : E) = u * v := by
  have hnt : ∃ x : K, 1 < ‖x‖ := by
    obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm ℚ_[p]
    refine ⟨algebraMap ℚ_[p] K x, ?_⟩
    show 1 < ‖algebraMap ℚ_[p] (PadicAlgCl p) x‖
    rwa [norm_algebraMap']
  let _ : NontriviallyNormedField K := { (inferInstance : NormedField K) with non_trivial := hnt }
  have : CompleteSpace K := FiniteDimensional.complete ℚ_[p] K
  let _ : NormedAlgebra K E :=
    { (inferInstance : Algebra K E) with
      norm_smul_le := fun a x => le_of_eq (by
        show ‖(a : PadicAlgCl p) * (x : PadicAlgCl p)‖ = _
        rw [norm_mul]; rfl) }
  exact UnitsFilt.exists_units_subgroup (K := K) (L := E)

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

def uval [(subG p K L).Normal] (w : (layerU p K L).V) : PadicAlgCl p :=
  ((Additive.toMul (Subtype.val (p := fun x => x ∈ Ubar p) w.1) : (PadicAlgCl p)ˣ) : PadicAlgCl p)

section

variable [(subG p K L).Normal]

theorem uval_add (a b : (layerU p K L).V) : uval (a + b) = uval a * uval b := rfl

theorem uval_neg (a : (layerU p K L).V) : uval (-a) = (uval a)⁻¹ := Units.val_inv_eq_inv_val _

theorem uval_sub (a b : (layerU p K L).V) : uval (a - b) = uval a * (uval b)⁻¹ := by
  rw [sub_eq_add_neg, uval_add, uval_neg]

theorem uval_sum {ι : Type*} (s : Finset ι) (f : ι → (layerU p K L).V) :
    uval (∑ i ∈ s, f i) = ∏ i ∈ s, uval (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, uval_add, ih]

theorem uval_rho (σ : GK p K) (w : (layerU p K L).V) :
    uval ((layerU p K L).rho (QuotientGroup.mk σ) w) = σ (uval w) := rfl

theorem uval_injective : Injective (uval : (layerU p K L).V → PadicAlgCl p) := fun _ _ hab =>
  Subtype.ext (Subtype.ext (Units.ext hab))

theorem uval_ne_zero (w : (layerU p K L).V) : uval w ≠ 0 := Units.ne_zero _

theorem vbar_eq_zero_iff (x : KbarMult p) :
    vbar p x = 0 ↔ ‖((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ = 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpos : 0 < ‖((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ :=
    norm_pos_iff.2 (Units.ne_zero _)
  rw [vbar_apply, neg_eq_zero, Real.logb_eq_zero]
  constructor
  · rintro (h | h | h | h | h | h) <;> linarith
  · intro h; right; right; right; right; left; exact h

theorem norm_uval (w : (layerU p K L).V) : ‖uval w‖ = 1 :=
  (vbar_eq_zero_iff _).1 ((mem_Ubar_iff p _).1 (Subtype.property (p := fun x => x ∈ Ubar p) w.1))

theorem uval_mem (h : K ≤ L) (w : (layerU p K L).V) : uval w ∈ L :=
  (mem_iff_fixed h _).2 fun σ hσ =>
    congrArg (fun y : Ubar p => ((Additive.toMul (y : KbarMult p) : (PadicAlgCl p)ˣ) : PadicAlgCl p))
      (w.2 ⟨σ, hσ⟩)

theorem exists_uval {x : PadicAlgCl p} (hx : x ∈ L) (h1 : ‖x‖ = 1) : ∃ w : (layerU p K L).V, uval w = x := by
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
  let y : KbarMult p := Additive.ofMul (Units.mk0 x hx0)
  have hy : y ∈ Ubar p := (mem_Ubar_iff p y).2 ((vbar_eq_zero_iff y).2 h1)
  refine ⟨⟨(⟨y, hy⟩ : Ubar p), fun g => Subtype.ext (Units.ext ?_)⟩, rfl⟩
  exact g.2 x hx

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

noncomputable def uE (h : K ≤ L) [(subG p K L).Normal] :
    (layerU p K L).V →+ Additive (IntermediateField.extendScalars h)ˣ where
  toFun w := Additive.ofMul (Units.mk0 (⟨uval w, uval_mem h w⟩ : IntermediateField.extendScalars h)
    (fun h0 => uval_ne_zero w (congrArg Subtype.val h0)))
  map_zero' := Units.ext (Subtype.ext rfl)
  map_add' _ _ := Units.ext (Subtype.ext rfl)

theorem finiteIndex_of_ball (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal]
    (X : AddSubgroup (layerU p K L).V) {ε : ℝ} (hε : 0 < ε) (hX : ∀ w, ‖uval w - 1‖ < ε → w ∈ X) :
    X.FiniteIndex := by
  have : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  have hc : IsCompact (Metric.closedBall (0 : L) 1) := isCompact_closedBall 0 1
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact hc (e := ε) hε
  have hex : ∀ w : (layerU p K L).V, ∃ y : t, ‖uval w - ((y : L) : PadicAlgCl p)‖ < ε := by
    intro w
    have hw : (⟨uval w, uval_mem h w⟩ : L) ∈ Metric.closedBall (0 : L) 1 := by
      rw [mem_closedBall_zero_iff]; exact (norm_uval w).le
    obtain ⟨y, hy, hwy⟩ := Set.mem_iUnion₂.1 (hcov hw)
    rw [Metric.mem_ball, dist_eq_norm] at hwy
    exact ⟨⟨y, hy⟩, hwy⟩
  choose c hc' using hex
  have hsub : ∀ w w', c w = c w' → w - w' ∈ X := by
    intro w w' hww
    apply hX
    have h1 : uval (w - w') - 1 = (uval w - uval w') * (uval w')⁻¹ := by
      rw [uval_sub, sub_mul, mul_inv_cancel₀ (uval_ne_zero w')]
    rw [h1, norm_mul, norm_inv, norm_uval, inv_one, mul_one]
    have h2 : uval w - uval w' = (uval w - ((c w : L) : PadicAlgCl p)) - (uval w' - ((c w : L) : PadicAlgCl p)) := by
      ring
    rw [h2, sub_eq_add_neg]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hc' w) ?_)
    rw [norm_neg, hww]; exact hc' w'
  have : Finite t := htf
  have hfin : Finite ((layerU p K L).V ⧸ X) := by
    refine Finite.of_injective (fun q => c q.out) fun q q' hqq => ?_
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq]
    have := hsub _ _ hqq.symm
    rwa [sub_eq_neg_add] at this
  exact AddSubgroup.finiteIndex_of_finite_quotient

theorem exists_layerU_sub (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] [Fintype (GalLK p K L)] :
    ∃ W : Submodule ℤ (layerU p K L).V, (∀ g, ∀ w ∈ W, (layerU p K L).rho g w ∈ W) ∧
      W.toAddSubgroup.FiniteIndex ∧
      (∀ w ∈ W, (∀ g, (layerU p K L).rho g w = w) → ∃ w' ∈ W, ∑ g, (layerU p K L).rho g w' = w) ∧
      ∀ g₀ : GalLK p K L, (∀ g, g ∈ Subgroup.zpowers g₀) → ∀ w ∈ W, ∑ g, (layerU p K L).rho g w = 0 →
        ∃ w' ∈ W, (layerU p K L).rho g₀ w' - w' = w := by
  classical
  let E : IntermediateField K (PadicAlgCl p) := IntermediateField.extendScalars h
  have hfd : FiniteDimensional K E := by
    have : FiniteDimensional ℚ_[p] E := hL
    exact FiniteDimensional.right ℚ_[p] K _
  have hst : ∀ (σ : GK p K), ∀ x ∈ L, σ x ∈ L := (subG_normal_iff h).1 inferInstance
  have hnorm : Normal K E := by
    rw [IntermediateField.normal_iff_forall_map_le']
    rintro σ _ ⟨x, hx, rfl⟩
    exact hst σ x hx
  have hgal : IsGalois K E := ⟨⟩
  obtain ⟨S, hS1, hS2, ⟨ε, hε, hS3⟩, hS4, hS5⟩ := exists_units_subgroup_padic hK E
  let r : GK p K →* (E ≃ₐ[K] E) := AlgEquiv.restrictNormalHom E
  have hr : ∀ (σ : GK p K) (x : E), ((r σ x : E) : PadicAlgCl p) = σ x := fun σ x =>
    AlgEquiv.restrictNormalHom_apply E σ x
  have hrs : Surjective r := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (PadicAlgCl p)
  have hker : ∀ σ : GK p K, r σ = 1 ↔ σ ∈ subG p K L := by
    intro σ
    constructor
    · intro h1 x hx
      have := hr σ ⟨x, hx⟩
      rw [h1] at this
      exact this.symm
    · intro hσ
      ext x
      rw [hr]
      exact hσ x.1 x.2
  let f : GalLK p K L →* (E ≃ₐ[K] E) := QuotientGroup.lift (subG p K L) r fun σ hσ => (hker σ).2 hσ
  have hf : ∀ σ : GK p K, f (QuotientGroup.mk σ) = r σ := fun σ => rfl
  have hfb : Bijective f := by
    refine ⟨(injective_iff_map_eq_one f).2 fun q hq => ?_, fun τ => ?_⟩
    · induction q using QuotientGroup.induction_on with
      | H σ => exact (QuotientGroup.eq_one_iff σ).2 ((hker σ).1 hq)
    · obtain ⟨σ, rfl⟩ := hrs τ
      exact ⟨QuotientGroup.mk σ, rfl⟩
  let e : GalLK p K L ≃* (E ≃ₐ[K] E) := MulEquiv.ofBijective f hfb
  let ι : (layerU p K L).V → Eˣ := fun w => Additive.toMul (uE h w)
  have hι : ∀ w, (((ι w : Eˣ) : E) : PadicAlgCl p) = uval w := fun w => rfl
  have hιrho : ∀ g w, ((ι ((layerU p K L).rho g w) : Eˣ) : E) = e g (ι w : E) := by
    intro g w
    induction g using QuotientGroup.induction_on with
    | H σ =>
      apply Subtype.ext
      rw [hι, uval_rho]
      exact (hr σ (ι w : E)).symm
  have hιsurj : ∀ v ∈ S, ∃ w, ι w = v := by
    intro v hv
    obtain ⟨w, hw⟩ := exists_uval (K := K) (L := L) (x := ((v : E) : PadicAlgCl p)) (v : E).2 (hS2 v hv)
    exact ⟨w, Units.ext (Subtype.ext hw)⟩
  have hprod : ∀ w, uval (∑ g, (layerU p K L).rho g w) = ((∏ τ : E ≃ₐ[K] E, τ (ι w : E) : E) : PadicAlgCl p) := by
    intro w
    rw [uval_sum, ← Fintype.prod_equiv e.toEquiv (fun g => e g (ι w : E)) (fun τ => τ (ι w : E)) (fun _ => rfl),
      IntermediateField.coe_prod]
    exact Finset.prod_congr rfl fun g _ => by rw [← hιrho, hι]
  let X : AddSubgroup (layerU p K L).V := (Subgroup.toAddSubgroup S).comap (uE h)
  have hX : ∀ w, w ∈ X ↔ ι w ∈ S := fun w => Iff.rfl
  refine ⟨AddSubgroup.toIntSubmodule X, fun g w hw => ?_, ?_, fun w hw hfix => ?_, fun g₀ hg₀ w hw hN => ?_⟩
  · exact hS1 (e g) (ι w) _ hw (hιrho g w)
  · rw [AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact finiteIndex_of_ball hL h X hε fun w hw => hS3 (ι w) hw
  · obtain ⟨v, hv, hvw⟩ := hS4 (ι w) hw fun τ => by
      obtain ⟨g, rfl⟩ := e.surjective τ
      rw [← hιrho, hfix]
    obtain ⟨w', rfl⟩ := hιsurj v hv
    refine ⟨w', hv, uval_injective ?_⟩
    rw [hprod, hvw, hι]
  · obtain ⟨v, hv, hvw⟩ := hS5 (e g₀) (fun τ => by
      obtain ⟨g, rfl⟩ := e.surjective τ
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg₀ g)
      rw [map_zpow]
      exact Subgroup.zpow_mem_zpowers _ _) (ι w) hw (by
        apply Subtype.ext
        rw [← hprod, hN]
        rfl)
    obtain ⟨w', rfl⟩ := hιsurj v hv
    refine ⟨w', hv, uval_injective ?_⟩
    rw [uval_sub, ← hι, hιrho, hvw, MulMemClass.coe_mul, hι, hι, mul_assoc, mul_inv_cancel₀ (uval_ne_zero w'),
      mul_one]

theorem herbrand_of_sub {G M : Type*} [Group G] [Fintype G] [AddCommGroup M] (ρ : Representation ℤ G M) (g₀ : G)
    (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (W : Submodule ℤ M) (hW1 : ∀ g, ∀ w ∈ W, ρ g w ∈ W)
    (hW2 : W.toAddSubgroup.FiniteIndex)
    (hW3 : ∀ w ∈ W, (∀ g, ρ g w = w) → ∃ w' ∈ W, ∑ g, ρ g w' = w)
    (hW4 : ∀ w ∈ W, ∑ g, ρ g w = 0 → ∃ w' ∈ W, ρ g₀ w' - w' = w) :
    Herbrand.HFin ρ g₀ ∧ Herbrand.h ρ g₀ = 1 := by
  let ρW : Representation ℤ G W :=
    { toFun := fun g => (ρ g).restrict (p := W) (q := W) (hW1 g)
      map_one' := LinearMap.ext fun x => Subtype.ext (by
        show ρ 1 x.1 = x.1
        rw [map_one]; rfl)
      map_mul' := fun a b => LinearMap.ext fun x => Subtype.ext (by
        show ρ (a * b) x.1 = ρ a (ρ b x.1)
        rw [map_mul]; rfl) }
  have hρ : ∀ g (x : W), ((ρW g x : W) : M) = ρ g x.1 := fun _ _ => rfl
  have hsum : ∀ x : W, ((∑ g, ρW g x : W) : M) = ∑ g, ρ g x.1 := by
    intro x
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun g _ => hρ g x
  have h0 : Subsingleton (Herbrand.TateZerothCohomology ρW g₀) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientAddGroup.induction_on with
    | H a =>
    induction b using QuotientAddGroup.induction_on with
    | H b =>
    rw [Herbrand.mk_eq_mk_iff]
    have hab : ((a : W) - (b : W)) ∈ (Herbrand.dHom ρW g₀).ker := (a - b).2
    rw [Herbrand.mem_ker_dHom_iff ρW g₀ hg] at hab
    obtain ⟨w', hw', hw⟩ := hW3 ((a : W) - (b : W) : W).1 ((a : W) - (b : W) : W).2
      (fun g => congrArg Subtype.val (hab g))
    refine ⟨⟨w', hw'⟩, ?_⟩
    rw [Herbrand.nHom_apply]
    exact Subtype.ext ((hsum _).trans hw)
  have h1 : Subsingleton (Herbrand.H1 ρW g₀) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientAddGroup.induction_on with
    | H a =>
    induction b using QuotientAddGroup.induction_on with
    | H b =>
    rw [Herbrand.mk_eq_mk_iff]
    have hab : ((a : W) - (b : W)) ∈ (Herbrand.nHom ρW).ker := (a - b).2
    rw [AddMonoidHom.mem_ker, Herbrand.nHom_apply] at hab
    obtain ⟨w', hw', hw⟩ := hW4 ((a : W) - (b : W) : W).1 ((a : W) - (b : W) : W).2
      ((hsum _).symm.trans (congrArg Subtype.val hab))
    exact ⟨⟨w', hw'⟩, Subtype.ext hw⟩
  obtain ⟨hf, hh⟩ := Herbrand.h_of_subsingleton ρW g₀
  have hfi : (W.subtype.toAddMonoidHom).range.FiniteIndex := by
    have : (W.subtype.toAddMonoidHom).range = W.toAddSubgroup := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩; exact y.2
      · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
    rw [this]; exact hW2
  obtain ⟨hiff, heq⟩ := Herbrand.h_eq_of_finiteIndex ρW ρ g₀ W.subtype.toAddMonoidHom
    Subtype.val_injective hfi (fun _ _ => rfl)
  exact ⟨hiff.1 hf, (heq hf).symm.trans hh⟩

theorem herbrand_layerU (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] [Fintype (GalLK p K L)] (g₀ : GalLK p K L) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    Herbrand.HFin (layerU p K L).rho g₀ ∧ Herbrand.h (layerU p K L).rho g₀ = 1 := by
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := exists_layerU_sub hK hL h
  exact herbrand_of_sub (layerU p K L).rho g₀ hg W hW1 hW2 hW3 (hW4 g₀ hg)

end ReciprocityTheory.DiscreteGroups.LocalClassField
