module

public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittEmbeddingsCompatible
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DetOfColSpanEq
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WeightUpdateAtPlace
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DetYtMatNeZero
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.FrobeniusSqIterateTeichmuller

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SubstZOfXCoordZA
open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset
open scoped Kronecker Matrix

noncomputable section

namespace Formalism.L2.G.Pend

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem rank_eq (j : ℕ) : (X.Fl.Pj j).m + 1 = NN X.G.P.m X.Fl.t j := by
  cases j with
  | zero => simp [Fills.Pj, NN]
  | succ j => simp only [Fills.Pj, Places.withWt, NN]; omega

structure Frm (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) where
  g : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)
  g' : ∀ v : X.Pl, GL (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)
  hg : ∀ v, X.latAt v j La.2 = colSpan (X.G.P.W v) (g v : Matrix _ _ (X.G.P.Qq v))
  hg' : ∀ v, X.latAt v (j + 1) La'.2 = colSpan (X.G.P.W v) (g' v : Matrix _ _ (X.G.P.Qq v))

variable (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc]

def tw (v : X.Pl) (s : Fin (X.G.P.n' v)) : X.G.P.Qq v →+* Kc :=
  (algebraMap X.G.Kf Kc).comp ((X.G.P.ι v).comp (X.G.P.σ v ^ s.val : X.G.P.Qq v ≃+* X.G.P.Qq v).toRingHom)

def mAt (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v))
    (A : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) :
    Matrix (Fin (NN X.G.P.m X.t j)) (Fin (NN X.G.P.m X.t j)) Kc :=
  (A.map (tw X Kc v s)).submatrix (finCongr (rank_eq X j).symm) (finCongr (rank_eq X j).symm)

theorem mAt_mul (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v))
    (A B : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) :
    mAt X Kc j v s A * mAt X Kc j v s B = mAt X Kc j v s (A * B) := by
  unfold mAt
  rw [Matrix.submatrix_mul_equiv, Matrix.map_mul]

theorem mAt_one (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) : mAt X Kc j v s 1 = 1 := by
  unfold mAt
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.submatrix_one_equiv]

variable {X} {j : ℕ} {La : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j La La')

def Pf (v : X.Pl) (s : Fin (X.G.P.n' v)) : Matrix (Fin (NN X.G.P.m X.t j)) (Fin (NN X.G.P.m X.t j)) Kc :=
  if IsOddPos s then mAt X Kc j v s ((φ.g v)⁻¹ : GL _ _) else (mAt X Kc j v s (φ.g v))ᵀ

def Pi (v : X.Pl) (s : Fin (X.G.P.n' v)) : Matrix (Fin (NN X.G.P.m X.t j)) (Fin (NN X.G.P.m X.t j)) Kc :=
  if IsOddPos s then mAt X Kc j v s (φ.g v) else (mAt X Kc j v s ((φ.g v)⁻¹ : GL _ _))ᵀ

def Qf (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc :=
  if IsOddPos s then (mAt X Kc (j + 1) v s (φ.g' v))ᵀ else mAt X Kc (j + 1) v s ((φ.g' v)⁻¹ : GL _ _)

def Qi (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc :=
  if IsOddPos s then (mAt X Kc (j + 1) v s ((φ.g' v)⁻¹ : GL _ _))ᵀ else mAt X Kc (j + 1) v s (φ.g' v)

def linF : X.ZA j → MvPowerSeries (X.ZA j) Kc
  | ⟨v, (s, ab)⟩ => ∑ ab' : Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t (j + 1)),
      MvPowerSeries.C ((Pf Kc φ v s ⊗ₖ Qf Kc φ v s) ab ab') * MvPowerSeries.X ⟨v, (s, ab')⟩

def linI : X.ZA j → MvPowerSeries (X.ZA j) Kc
  | ⟨v, (s, ab)⟩ => ∑ ab' : Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t (j + 1)),
      MvPowerSeries.C ((Pi Kc φ v s ⊗ₖ Qi Kc φ v s) ab ab') * MvPowerSeries.X ⟨v, (s, ab')⟩

def bc (z z' : X.ZA j) : Kc := MvPowerSeries.coeff (Finsupp.single z' 1) (linF Kc φ z)


variable (X) in
def zOfX (j : ℕ) : X.ZA j → MvPowerSeries (X.EA j ⊕ X.EA j) Kc
  | ⟨v, (s, a, b)⟩ =>
    if IsOddPos s then ∑ r : Fin (X.G.P.n' v / 2),
      MvPowerSeries.C (algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] ((X.om v).omS r)))) *
        MvPowerSeries.X (Sum.inr ⟨v, (r, a, b)⟩)
    else ∑ r : Fin (X.G.P.n' v / 2),
      MvPowerSeries.C (algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] ((X.om v).om r)))) *
        MvPowerSeries.X (Sum.inl ⟨v, (r, a, b)⟩)

def invF : X.ZA j → MvPowerSeries (X.EA j ⊕ X.EA j) Kc
  | ⟨v, (s, ab)⟩ => ∑ ab' : Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t (j + 1)),
      MvPowerSeries.C ((Pi Kc φ v s ⊗ₖ Qi Kc φ v s) ab ab') * zOfX X Kc j ⟨v, (s, ab')⟩

def thA (F : MvPowerSeries (X.ZA j) Kc) : MvPowerSeries (X.EA j ⊕ X.EA j) Kc :=
  MvPowerSeries.subst (invF Kc φ) F

section Lin

variable {K : Type*} [Field K]

theorem sum_lin {ι M : Type*} [Fintype ι] [CommRing M] (c : K →+* M) (A B : Matrix ι ι K) (x : ι → M)
    (i : ι) : ∑ y, c (A i y) * ∑ w, c (B y w) * x w = ∑ w, c ((A * B) i w) * x w := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.mul_sum, Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sum_one {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommRing M] (c : K →+* M) (x : ι → M) (i : ι) :
    ∑ w, c ((1 : Matrix ι ι K) i w) * x w = x i := by
  simp [Matrix.one_apply, apply_ite c, ite_mul]

theorem lin_repr {σ ι : Type*} [Fintype σ] [Fintype ι] (k : ι → K) (e : ι → σ) :
    ∑ y, MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single y 1)
        (∑ i, MvPowerSeries.C (k i) * MvPowerSeries.X (e i) : MvPowerSeries σ K)) * MvPowerSeries.X y =
      ∑ i, MvPowerSeries.C (k i) * MvPowerSeries.X (e i) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (e i)]
  · simp
  · intro y _ hy
    simp [hy]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem subst_lin {σ τ ι : Type*} [Fintype ι] {a : σ → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a)
    (k : ι → K) (f : ι → MvPowerSeries σ K) :
    MvPowerSeries.subst a (∑ i, MvPowerSeries.C (k i) * f i) =
      ∑ i, MvPowerSeries.C (k i) * MvPowerSeries.subst a (f i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_C]

end Lin

section Dual

variable {n' : ℕ} (B : OmBasis p n')

theorem dual' (i i' : Fin (n' / 2)) :
    ∑ r, (sigW p)^[2 * i.val] (B.omS r) * (sigW p)^[2 * i'.val] (B.om r) = if i = i' then 1 else 0 := by
  let A : Matrix (Fin (n' / 2)) (Fin (n' / 2)) (WW p) := fun r i => (sigW p)^[2 * i.val] (B.om r)
  let Bm : Matrix (Fin (n' / 2)) (Fin (n' / 2)) (WW p) := fun i r => (sigW p)^[2 * i.val] (B.omS r)
  have h1 : A * Bm = 1 := by
    refine Matrix.ext fun r r' => ?_
    rw [Matrix.mul_apply, Matrix.one_apply, ← B.dual r r']
    apply Finset.sum_congr rfl
    intro i _
    exact (iterate_map_mul (sigW p) _ _ _).symm
  have h2 : Bm * A = 1 := mul_eq_one_comm.1 h1
  have h3 := congrFun (congrFun h2 i) i'
  rw [Matrix.mul_apply, Matrix.one_apply] at h3
  exact h3

theorem dualS (he : Even n') (s s' : Fin n') (hp : s.val % 2 = s'.val % 2) :
    ∑ r, (sigW p)^[s.val] (B.omS r) * (sigW p)^[s'.val] (B.om r) = if s = s' then 1 else 0 := by
  obtain ⟨h, rfl⟩ := he
  have hs := s.isLt
  have hs' := s'.isLt
  let i : Fin ((h + h) / 2) := ⟨s.val / 2, by omega⟩
  let i' : Fin ((h + h) / 2) := ⟨s'.val / 2, by omega⟩
  have e1 : s.val = s.val % 2 + 2 * i.val := by show s.val = s.val % 2 + 2 * (s.val / 2); omega
  have e2 : s'.val = s.val % 2 + 2 * i'.val := by show s'.val = s.val % 2 + 2 * (s'.val / 2); omega
  have h0 := congrArg ((sigW p)^[s.val % 2]) (dual' B i i')
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← RingHom.coe_pow, map_sum] at h0
  simp only [map_mul] at h0
  rw [RingHom.coe_pow] at h0
  simp only [← Function.iterate_add_apply, ← e1, ← e2] at h0
  rw [h0, ← RingHom.coe_pow, apply_ite (⇑((sigW p) ^ (s.val % 2))), map_one, map_zero]
  have : (i = i') ↔ (s = s') := by
    rw [Fin.ext_iff, Fin.ext_iff]
    show s.val / 2 = s'.val / 2 ↔ _
    omega
  simp only [this]

theorem dualK (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] (he : Even n') (s s' : Fin n')
    (hp : s.val % 2 = s'.val % 2) :
    ∑ r, algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] (B.omS r))) *
      algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s'.val] (B.om r))) = if s = s' then 1 else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_mul, ← map_sum]
  rw [dualS B he s s' hp]
  split_ifs <;> simp

end Dual

section Main

variable {X : Sys p} (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] {j : ℕ} {La : X.Lt j}
  {La' : X.Lt (j + 1)} (φ : Frm X j La La')

theorem Pi_mul_Pf (v : X.Pl) (s : Fin (X.G.P.n' v)) : Pi Kc φ v s * Pf Kc φ v s = 1 := by
  unfold Pi Pf
  split_ifs
  · rw [mAt_mul, Units.mul_inv, mAt_one]
  · rw [← Matrix.transpose_mul, mAt_mul, Units.mul_inv, mAt_one, Matrix.transpose_one]

theorem Qi_mul_Qf (v : X.Pl) (s : Fin (X.G.P.n' v)) : Qi Kc φ v s * Qf Kc φ v s = 1 := by
  unfold Qi Qf
  split_ifs
  · rw [← Matrix.transpose_mul, mAt_mul, Units.mul_inv, mAt_one, Matrix.transpose_one]
  · rw [mAt_mul, Units.mul_inv, mAt_one]

theorem kron_inv (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (Pi Kc φ v s ⊗ₖ Qi Kc φ v s) * (Pf Kc φ v s ⊗ₖ Qf Kc φ v s) = 1 := by
  rw [← Matrix.mul_kronecker_mul, Pi_mul_Pf, Qi_mul_Qf, Matrix.one_kronecker_one]

theorem hasSubst_linF : MvPowerSeries.HasSubst (linF Kc φ) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun ⟨v, (s, ab)⟩ => by simp [linF]

theorem hasSubst_linI : MvPowerSeries.HasSubst (linI Kc φ) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun ⟨v, (s, ab)⟩ => by simp [linI]

theorem hasSubst_coordZA : MvPowerSeries.HasSubst (X.coordZA Kc j) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun e => by
    rcases e with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA]

theorem constantCoeff_zOfX (z : X.ZA j) : MvPowerSeries.constantCoeff (zOfX X Kc j z) = 0 := by
  obtain ⟨v, s, a, b⟩ := z
  simp only [zOfX]
  split_ifs <;> simp

theorem hasSubst_invF : MvPowerSeries.HasSubst (invF Kc φ) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun ⟨v, (s, ab)⟩ => by simp [invF, constantCoeff_zOfX]

theorem bc_lin (z : X.ZA j) :
    ∑ y, MvPowerSeries.C (bc Kc φ z y) * MvPowerSeries.X y = linF Kc φ z := by
  obtain ⟨v, s, ab⟩ := z
  exact lin_repr _ _

theorem subst_linF_linI (z : X.ZA j) :
    MvPowerSeries.subst (linF Kc φ) (linI Kc φ z) = MvPowerSeries.X z := by
  obtain ⟨v, s, ab⟩ := z
  simp only [linI]
  rw [subst_lin (hasSubst_linF Kc φ)]
  simp only [MvPowerSeries.subst_X (hasSubst_linF Kc φ), linF]
  rw [sum_lin (MvPowerSeries.C) _ _ (fun ab' => (MvPowerSeries.X ⟨v, (s, ab')⟩ : MvPowerSeries (X.ZA j) Kc)), kron_inv,
    sum_one]

theorem subst_coordZA_zOfX (z : X.ZA j) :
    MvPowerSeries.subst (X.coordZA Kc j) (zOfX X Kc j z) = MvPowerSeries.X z := by
  obtain ⟨v, s, a, b⟩ := z
  have he : Even (X.G.P.n' v) := (X.G.P.setting v).even
  simp only [zOfX]
  split_ifs with h
  · rw [subst_lin (hasSubst_coordZA Kc)]
    simp only [MvPowerSeries.subst_X (hasSubst_coordZA Kc), Sys.coordZA, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_eq_single_of_mem s (by simp [h])]
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [← mul_assoc, ← map_mul MvPowerSeries.C, ← Finset.sum_mul, ← map_sum MvPowerSeries.C]
      rw [dualK (X.om v) Kc he s s rfl]
      simp
    · intro s' hs' hne
      have hs'' : IsOddPos s' := (Finset.mem_filter.1 hs').2
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← mul_assoc, ← map_mul MvPowerSeries.C, ← Finset.sum_mul, ← map_sum MvPowerSeries.C]
      rw [dualK (X.om v) Kc he s s' (by rw [show s.val % 2 = 1 from h, show s'.val % 2 = 1 from hs''])]
      simp [Ne.symm hne]
  · rw [subst_lin (hasSubst_coordZA Kc)]
    simp only [MvPowerSeries.subst_X (hasSubst_coordZA Kc), Sys.coordZA, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_eq_single_of_mem s (by simp [h])]
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [← mul_assoc, ← map_mul MvPowerSeries.C, ← Finset.sum_mul, ← map_sum MvPowerSeries.C]
      simp only [mul_comm (algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] ((X.om v).om _))))]
      rw [dualK (X.om v) Kc he s s rfl]
      simp
    · intro s' hs' hne
      have hs'' : ¬ IsOddPos s' := (Finset.mem_filter.1 hs').2
      have h1 : s.val % 2 = 0 := by have : ¬ s.val % 2 = 1 := h; omega
      have h2 : s'.val % 2 = 0 := by have : ¬ s'.val % 2 = 1 := hs''; omega
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← mul_assoc, ← map_mul MvPowerSeries.C, ← Finset.sum_mul, ← map_sum MvPowerSeries.C]
      simp only [mul_comm (algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] ((X.om v).om _))))]
      rw [dualK (X.om v) Kc he s' s (by rw [h1, h2])]
      simp [hne]

theorem subst_coordZA_invF (z : X.ZA j) :
    MvPowerSeries.subst (X.coordZA Kc j) (invF Kc φ z) = linI Kc φ z := by
  obtain ⟨v, s, ab⟩ := z
  simp only [invF, linI]
  rw [subst_lin (hasSubst_coordZA Kc)]
  simp only [subst_coordZA_zOfX]

theorem thF_frm (F : MvPowerSeries (X.ZA j) Kc) :
    F = linSub (bc Kc φ) (X.ThZA Kc j (thA Kc φ F)) := by
  unfold linSub Sys.ThZA thA
  simp only [bc_lin]
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_invF Kc φ) (hasSubst_coordZA Kc)]
  simp only [subst_coordZA_invF]
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_linI Kc φ) (hasSubst_linF Kc φ)]
  simp only [subst_linF_linI]
  exact (congrFun MvPowerSeries.subst_self F).symm

end Main

section Ex

variable (X : Sys p)

theorem latAt_isLattice (j : ℕ) (L : (X.Pj j).Tup) (hL : (X.Pj j).IsLatTup L) (v : X.Pl) :
    IsLattice (X.G.P.W v) (X.latAt v j L) := by
  cases j with
  | zero => exact hL v
  | succ j => exact hL v

theorem exists_frm (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (h : (X.Pj j).IsLatTup La.2)
    (h' : (X.Pj (j + 1)).IsLatTup La'.2) : Nonempty (Frm X j La La') := by
  choose g hg1 hg2 using latAt_isLattice X j La.2 h
  choose g' hg1' hg2' using latAt_isLattice X (j + 1) La'.2 h'
  exact ⟨⟨fun v => Matrix.nonsingInvUnit (g v) (hg1 v), fun v => Matrix.nonsingInvUnit (g' v) (hg1' v), hg2, hg2'⟩⟩

end Ex

section Uniq

theorem sum_parity {M : Type*} [AddCommMonoid M] {n' : ℕ} (he : Even n') (ε : ℕ) (hε : ε < 2)
    (P : Fin n' → Prop) [DecidablePred P] (hP : ∀ s, P s ↔ s.val % 2 = ε) (f : ℕ → M) :
    ∑ s ∈ univ.filter P, f s.val = ∑ i : Fin (n' / 2), f (ε + 2 * i.val) := by
  obtain ⟨h, rfl⟩ := he
  refine Finset.sum_bij' (fun s _ => (⟨s.val / 2, by have := s.isLt; omega⟩ : Fin ((h + h) / 2)))
    (fun i _ => (⟨ε + 2 * i.val, by have := i.isLt; omega⟩ : Fin (h + h))) ?_ ?_ ?_ ?_ ?_
  · intro s _
    exact Finset.mem_univ _
  · intro i _
    rw [Finset.mem_filter, hP]
    exact ⟨Finset.mem_univ _, by show (ε + 2 * i.val) % 2 = ε; omega⟩
  · intro s hs
    have := (hP s).1 (Finset.mem_filter.1 hs).2
    apply Fin.ext
    show ε + 2 * (s.val / 2) = s.val
    omega
  · intro i _
    apply Fin.ext
    show (ε + 2 * i.val) / 2 = i.val
    omega
  · intro s hs
    have := (hP s).1 (Finset.mem_filter.1 hs).2
    congr 1
    show s.val = ε + 2 * (s.val / 2)
    omega

theorem dualT {n' : ℕ} (B : OmBasis p n') (he : Even n') (ε : ℕ) (hε : ε < 2) (P : Fin n' → Prop) [DecidablePred P]
    (hP : ∀ s, P s ↔ s.val % 2 = ε) (r r' : Fin (n' / 2)) :
    ∑ s ∈ univ.filter P, (sigW p)^[s.val] (B.om r) * (sigW p)^[s.val] (B.omS r') = if r = r' then 1 else 0 := by
  rw [sum_parity he ε hε P hP (fun n => (sigW p)^[n] (B.om r) * (sigW p)^[n] (B.omS r'))]
  have h0 := congrArg ((sigW p)^[ε]) (B.dual r r')
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← RingHom.coe_pow, map_sum] at h0
  rw [apply_ite (⇑((sigW p) ^ ε)), map_one, map_zero] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.coe_pow, ← Function.iterate_add_apply, iterate_map_mul]

variable {X : Sys p} (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] {j : ℕ} {La : X.Lt j}
  {La' : X.Lt (j + 1)} (φ : Frm X j La La')

theorem bc_same (v : X.Pl) (s : Fin (X.G.P.n' v)) (ab ab' : Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t (j + 1))) :
    bc Kc φ ⟨v, (s, ab)⟩ ⟨v, (s, ab')⟩ = Pf Kc φ v s ab.1 ab'.1 * Qf Kc φ v s ab.2 ab'.2 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [bc, linF, map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X,
    Finsupp.single_left_inj one_ne_zero]
  rw [Finset.sum_eq_single ab']
  · simp [Matrix.kroneckerMap_apply]
  · intro y _ hy
    have : ¬ ((⟨v, (s, ab')⟩ : X.ZA j) = ⟨v, (s, y)⟩) := by
      intro h
      simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h
      exact hy h.symm
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem bc_ne (z z' : X.ZA j) (h : (⟨z.1, z.2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) ≠ ⟨z'.1, z'.2.1⟩) :
    bc Kc φ z z' = 0 := by
  classical
  obtain ⟨v, s, ab⟩ := z
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [bc, linF, map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X,
    Finsupp.single_left_inj one_ne_zero]
  refine Finset.sum_eq_zero fun y _ => ?_
  have : ¬ (z' = (⟨v, (s, y)⟩ : X.ZA j)) := by
    rintro rfl
    exact h rfl
  simp [this]

end Uniq

end Formalism.L2.G.Pend
end
end

section -- merged from Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionAlgebraCp
section -- merged from Formalism.LocalToGlobal.GroupLattices.PendingLemmas.XiOfSpec
noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]
  (ThF : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc)

def volE (v : X.Pl) (j : ℕ) (L : (X.Pj j).Tup) (L' : (X.Pj (j + 1)).Tup) : ℤ :=
  (NN X.G.P.m X.t j : ℤ) * len X v (j + 1) L' - (NN X.G.P.m X.t (j + 1) : ℤ) * len X v j L

abbrev XiTy (v : X.Pl) (j : ℕ) : Type :=
  Aw X v j → ((Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) → ℚ) →+ MvPowerSeries (X.ZA j) Kc)

def IsXi (v : X.Pl) (j : ℕ) (Ξ : XiTy X Kc v j) : Prop :=
  ∃ u u' : X.G.Kf, X.vEqK u 0 ∧ X.vEqK u' 0 ∧
    ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
      ThF j La La' = (u ^ (len X v j La.2) * u' ^ (len X v (j + 1) La'.2) *
        (p : X.G.Kf) ^ (-(((X.G.P.n' v / 2 : ℕ) : ℤ) * volE X v j La.2 La'.2))) •
        Ξ (aw X v j La La') (X.ind v j La.2 La'.2)

def XiEx (v : X.Pl) (j : ℕ) : Prop := ∃ Ξ : XiTy X Kc v j, IsXi X Kc ThF v j Ξ

def xiOf (v : X.Pl) (j : ℕ) : XiTy X Kc v j := by
  classical exact if h : XiEx X Kc ThF v j then Classical.choose h else fun _ => 0

theorem xiOf_spec {v : X.Pl} {j : ℕ} (h : XiEx X Kc ThF v j) : IsXi X Kc ThF v j (xiOf X Kc ThF v j) := by
  rw [xiOf, dite_eq_left h]
  exact Classical.choose_spec h

end Formalism.L2.G.Pend
end
end

noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

variable {p : ℕ} [Fact p.Prime]

@[reducible] def wittFractionAlgebraCp (p : ℕ) [Fact p.Prime] : Algebra (K0 p) ℂ_[p] := (k0ToC p).toAlgebra

@[reducible] def algKfC {G : GAtP p} (E : CEmb G) : Algebra G.Kf ℂ_[p] := E.iK.toAlgebra

abbrev DelTy (X : Sys p) (E : CEmb X.G) : Type :=
  letI := algKfC E
  ∀ j, (X.Pj j).Xsp →ₗ[X.G.Kf] MvPowerSeries (X.ZA j) ℂ_[p] →ₗ[X.G.Kf] XspC (X.Pj (j + 1)) ℂ_[p]

def DelDeg (X : Sys p) (E : CEmb X.G) (DelF : DelTy X E) : Prop :=
  letI := algKfC E
  ∀ j (G : (X.Pj j).Xsp) (f : MvPowerSeries (X.ZA j) ℂ_[p]),
    (∀ n : X.ZA j →₀ ℕ, (∀ (v : X.Pl) (s : Fin (X.G.P.n' v)),
        ((∑ a, ∑ b, n ⟨v, (s, a, b)⟩ : ℕ) : ℤ) = ∑ i ∈ Finset.Icc 1 (NN X.G.P.m X.t (j + 1)), X.nuv v (j + 1) s i) →
      MvPowerSeries.coeff n f = 0) → DelF j G f = 0

abbrev pendOf (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    (be : MvPowerSeries (Fin 2) (K0 p))
    (ThF : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p])
    (DelF : DelTy X E) (hDel : DelDeg X E DelF) : Pend X :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E
  { Kc := ℂ_[p]
    Oc := OcC p
    Oc_val := OcC_val
    witt_mem_integers_Cp := fun x => by
      show ‖k0ToC p (algebraMap (WW p) (K0 p) x)‖ ≤ 1
      rw [witt_fraction_to_Cp_algebraMap]
      exact norm_wToC_le p x
    Oc_K := fun x => E.mem_iff x
    Oc_rank1 := OcC_rank1
    be := be
    Rep := repOf X.Lv hfin
    Rep_lat := repOf_lat X.Lv hfin
    Rep_ex := fun j _ => repOf_ex X.Lv hfin j
    stab_fin := fun j _ => stab_fin X hst j
    Frm := Frm X
    ThA := fun j La La' φ => thA ℂ_[p] φ (ThF j La La')
    bc := fun _ _ _ φ => bc ℂ_[p] φ
    ThF := ThF
    ThF_frm := fun j La La' φ => thF_frm ℂ_[p] φ (ThF j La La')
    DelF := DelF
    Del_deg := hDel
    len := len X
    len_edge := len_edge X
    len_other := len_other X
    Aw := Aw X
    aw := aw X
    weight_update_at_place := weight_update_at_place X
    aw_tgt := aw_tgt X
    Xi := xiOf X ℂ_[p] ThF }

abbrev pendC (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    (be : MvPowerSeries (Fin 2) (K0 p))
    (ThF : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p]) : Pend X :=
  letI := algKfC E
  pendOf X E hfin hst be ThF (delF X ℂ_[p]) (del_deg X ℂ_[p])

end Formalism.L2.G.Pend
end
end

section -- merged from Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SysC
noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

abbrev sysC {p : ℕ} [Fact p.Prime] (G : GAtP p) (Fl : Fills G) (Lv : Levels Fl) (Ch : Chain Lv)
    (std : ∀ v, Std p (G.P.n' v) G.P.m Fl.t Fl.mm Fl.c G.P.r (Fl.TT v) (Fl.a v) (Fl.b v) (G.P.lam0 v) (Fl.w v))
    (hfin : ∀ j c, (Lv.lev j c).FinClasses) (h0 : (p : G.O) ≠ 0) : Sys p :=
  sysOf G Fl Lv Ch std hfin h0 fun v => omOf p (G.P.n' v) (G.P.setting v).even (G.P.setting v).two_le

end Formalism.L2.G.Pend
end
end

section -- merged from Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DelEquiv
noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def glAt : (j : ℕ) → (∀ v : Fin (X.Fl.Pj j).nV, GL (Fin ((X.Fl.Pj j).m + 1)) ((X.Fl.Pj j).Qq v)) →
    ∀ v : X.Pl, GL (Fin ((X.Fl.Pj j).m + 1)) (X.G.P.Qq v)
  | 0, A => A
  | _ + 1, A => A

variable (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc]

def actS (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) : X.ZA j → MvPowerSeries (X.ZA j) Kc
  | ⟨v, (s, a, b)⟩ => ∑ a' : Fin (NN X.G.P.m X.t j),
      MvPowerSeries.C (if IsOddPos s then mAt X Kc j v s ((B v)⁻¹ : GL _ _) a a' else mAt X Kc j v s (B v) a' a) *
        MvPowerSeries.X ⟨v, (s, a', b)⟩

def SA (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (f : MvPowerSeries (X.ZA j) Kc) :
    MvPowerSeries (X.ZA j) Kc :=
  MvPowerSeries.subst (actS X Kc j B) f

def cA (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) : Kc :=
  ∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v),
    (tw X Kc v s (B v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det) ^ ((if IsOddPos s then -1 else 1) * X.w v (j + 1) s)

def GoodG (j : ℕ) (G : (X.Pj j).Xsp) : Prop := denD X Kc j ∣ subD X Kc j G * numD X Kc j

def gamAt (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) :=
  glAt X j fun v => (X.Lv.lev j c).act v γ

def kapG (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) : Kc :=
  algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf (((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O)) * cA X Kc j (gamAt X j c γ) *
    ∏ v : X.Pl, (p : Kc) ^ (-(X.vm v (j + 1) * ordP (X.G.P.W v) p (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det))

variable (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)

def delt (j : ℕ) (c : X.Lv.comp j) (L : (X.Pj j).Tup) : (X.Lv.lev j c).Γ := by
  classical exact if h : (X.Pj j).IsLatTup L then (Classical.choose_spec (repOf_ex X.Lv hfin j c L h).exists).2.choose else 1

def chiN (j : ℕ) (La : X.Lt j) : Kc := (kapG X Kc j La.1 (delt X hfin j La.1 La.2))⁻¹

def thFN (Th0 : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) :
    MvPowerSeries (X.ZA j) Kc :=
  MvPowerSeries.C (chiN X Kc hfin j La) * Th0 j La La'

end Formalism.L2.G.Pend
end
end
