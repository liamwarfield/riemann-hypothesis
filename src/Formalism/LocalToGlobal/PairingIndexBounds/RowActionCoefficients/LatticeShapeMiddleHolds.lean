module

public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.AdmissibleGeneralLatticeTuple
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.XShape
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideEdge
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.SubDRenameHvE
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.SumIccEqRange

@[expose] public section

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.BranchingSourceIdentity
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions.G.LatticeSystems

section Cast

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) (N : ℕ) (hm : P.m + 1 = N)

def emC (b : GlobalTheory P) (v : Fin N × Fin N) : (Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) :=
  emP P b (Fin.cast hm.symm v.1, Fin.cast hm.symm v.2)

def gamC (g : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (b : GlobalTheory P) : Matrix (Fin N) (Fin N) Kf :=
  (gam P g b).submatrix (Fin.cast hm.symm) (Fin.cast hm.symm)

def nuC (b : GlobalTheory P) : Fin N → ℕ := fun t => nuB P b (Fin.cast hm.symm t)

variable (g : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (hg : ∀ v, IsUnit (g v).det)

include hg in
theorem htupW_leC (hinj : Function.Injective (algebraMap O Kf)) (T : Submodule O P.Xsp)
    (hT : ∀ F : GlobalTheory P → MvPolynomial (Fin N × Fin N) Kf,
      (∀ b, F b ∈ deltaL O Kf N (nuC P N hm b) (gamC P N hm g b)) →
        (∏ b : GlobalTheory P, (gamC P N hm g b).det ^ (-(eB P b))) • ∏ b, rename (emC P N hm b) (F b) ∈ T) :
    P.HtupW (fun v => colSpan (P.W v) (g v)) ≤ T := by
  subst hm
  exact htupW_le P g hg hinj T hT

include hg in
theorem mem_htupWC (hinj : Function.Injective (algebraMap O Kf)) (F : GlobalTheory P → MvPolynomial (Fin N × Fin N) Kf)
    (hF : ∀ b, F b ∈ deltaL O Kf N (nuC P N hm b) (gamC P N hm g b)) :
    (∏ b : GlobalTheory P, (gamC P N hm g b).det ^ (-(eB P b))) • ∏ b, rename (emC P N hm b) (F b) ∈
      P.HtupW (fun v => colSpan (P.W v) (g v)) := by
  subst hm
  exact mem_htupW P g hg hinj F hF

end Cast

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem branching_source_identity : XBrS := by
  intro p _ X hinj j L g hg hL T hT
  cases j with
  | zero =>
    have hLe : L = fun v => colSpan (X.G.P.W v) (g v) := funext hL
    rw [hLe]
    exact htupW_leC X.G.P _ (rankJ X 0) g hg hinj T hT
  | succ j =>
    have hLe : L = fun v => colSpan (X.G.P.W v) (g v) := funext hL
    rw [hLe]
    exact htupW_leC (X.Fl.Pj (j + 1)) _ (rankJ X (j + 1)) g hg hinj T hT

theorem branching_target_identity : XBrT := by
  intro p _ X hinj j L g hg hL F hF
  cases j with
  | zero =>
    have hLe : L = fun v => colSpan (X.G.P.W v) (g v) := funext hL
    rw [hLe]
    exact mem_htupWC X.G.P _ (rankJ X 0) g hg hinj F hF
  | succ j =>
    have hLe : L = fun v => colSpan (X.G.P.W v) (g v) := funext hL
    rw [hLe]
    exact mem_htupWC (X.Fl.Pj (j + 1)) _ (rankJ X (j + 1)) g hg hinj F hF

end Formalism.L2.PairingIndexBounds.Ent
end
end

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.ProdItePow
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

namespace MiddleFrameLemmas

theorem prod_sign {ι K : Type*} [CommRing K] (s : Finset ι) (ε : ι → K) (h : ∀ i, ε i = 1 ∨ ε i = -1) :
    (∏ i ∈ s, ε i) = 1 ∨ (∏ i ∈ s, ε i) = -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => left; simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    rcases h a with h1 | h1 <;> rcases ih with h2 | h2 <;> rw [h1, h2] <;> simp

theorem map_rowAct {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (P : MvPolynomial (Fin r × Fin n) R) : map f (rowAct R g P) = rowAct S (g.map f) (map f P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [map_C, show (C a : MvPolynomial (Fin r × Fin n) R) = algebraMap R _ a from rfl, AlgHom.commutes,
      show (C (f a) : MvPolynomial (Fin r × Fin n) S) = algebraMap S _ (f a) from rfl, AlgHom.commutes]
    exact map_C f a
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    unfold rowAct
    rw [aeval_X, aeval_X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_mul, map_C, map_X]

theorem sum_C_mul {σ K : Type*} [CommRing K] (κ : K) (R0 : MvPolynomial σ K) (d : (σ →₀ ℕ) → K) :
    ∑ n ∈ (C κ * R0).support, d n * AddMonoidAlgebra.coeff (C κ * R0) n = κ * ∑ n ∈ R0.support, d n * AddMonoidAlgebra.coeff R0 n := by
  classical
  have hsub : (C κ * R0).support ⊆ R0.support := by
    intro n hn
    rw [mem_support_iff, coeff_C_mul] at hn
    rw [mem_support_iff]
    intro h0
    exact hn (by rw [h0, mul_zero])
  rw [Finset.sum_subset hsub, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [coeff_C_mul]; ring
  · intro n _ hn
    rw [notMem_support_iff.1 hn, mul_zero]

section Ev

variable {K : Type} [CommRing K] {n : ℕ}

theorem evX_gX (x : ℕ × Fin n → K) (a : Fin n) (i : ℕ) : evX x (gX K n a i) = C (x (i, a)) := by
  simp [evX, gX]

theorem gY_map_evX (x : ℕ × Fin n → K) : (gY K n).map (evX x) = yV K n := by
  ext a t
  simp [evX, gY, yV]

theorem evX_hvO (x : ℕ × Fin n → K) (c : ℕ) (h : Fin c → ℕ) :
    evX x (hvO (gX K n) (gY K n) c h) = hvO (fun a i => C (x (i, a))) (yV K n) c h := by
  rw [map_hvO, gY_map_evX]
  congr 1
  funext a i
  exact evX_gX x a i

theorem evX_hvE (x : ℕ × Fin n → K) (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k, h k ≤ n) :
    evX x (hvE (gX K n) (gY K n) c h hh) = hvE (fun a i => C (x (i, a))) (yV K n) c h hh := by
  rw [map_hvE, gY_map_evX]
  congr 1
  funext a i
  exact evX_gX x a i

theorem evX_det (x : ℕ × Fin n → K) :
    evX x (Matrix.of fun a i : Fin n => gX K n a i.val).det = C (Matrix.of fun a i : Fin n => x (i.val, a)).det := by
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  refine Matrix.ext fun a i => ?_
  exact evX_gX x a i.val

theorem src_even (g gi : Matrix (Fin n) (Fin n) K) (hg : g * gi = 1) (x : Fin n → ℕ → K) (c e : ℕ) (h : Fin c → ℕ)
    (hh : ∀ k, h k ≤ n) :
    rowAct K gi (C ((Matrix.of fun a i : Fin n => x a i.val).det ^ e) * hvE (fun a i => C (x a i)) (yV K n) c h hh) =
      g.det ^ e • (C ((Matrix.of fun a i : Fin n => mulC gi.transpose x a i.val).det ^ e) *
        hvE (fun a i => C (mulC gi.transpose x a i)) (yV K n) c h hh) := by
  have h1 : (Matrix.of fun a i : Fin n => mulC gi.transpose x a i.val) =
      gi.transpose * (Matrix.of fun a i : Fin n => x a i.val) := by
    ext a i
    simp [mulC, Matrix.mul_apply]
  have h2 : g.det * gi.det = 1 := by rw [← Matrix.det_mul, hg, Matrix.det_one]
  have h3 : (Matrix.of fun a i : Fin n => x a i.val).det =
      g.det * (Matrix.of fun a i : Fin n => mulC gi.transpose x a i.val).det := by
    rw [h1, Matrix.det_mul, Matrix.det_transpose, ← mul_assoc, h2, one_mul]
  rw [map_mul, rowAct_hvE, show (C ((Matrix.of fun a i : Fin n => x a i.val).det ^ e) : MvPolynomial (Fin n × Fin n) K) =
    algebraMap K _ ((Matrix.of fun a i : Fin n => x a i.val).det ^ e) from rfl, AlgHom.commutes, smul_eq_C_mul, ← mul_assoc,
    ← C_mul, ← mul_pow, ← h3]
  rfl

end Ev

section Col

variable {K : Type} [Field K]

theorem prod_ite_pow {l n : ℕ} (π : K) (i0 : ℕ) (I : Fin l → Fin n) (J : ℕ → Fin n) (hJ : ∀ q : Fin l, J q.val = I q) :
    ∏ q : Fin l, (if (I q).val < i0 then π else 1) = π ^ ((Finset.range l).filter fun i' => (J i').val < i0).card := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
    ← BidetPairing.card_fin_filter l fun i' => (J i').val < i0]
  congr 2
  ext q
  simp [hJ]

theorem card_le_min {l n : ℕ} (i0 : ℕ) (I : Fin l → Fin n) (hI : Function.Injective I) (J : ℕ → Fin n)
    (hJ : ∀ q : Fin l, J q.val = I q) : ((Finset.range l).filter fun i' => (J i').val < i0).card ≤ min l i0 := by
  refine le_min ?_ ?_
  · exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
  · have hh : ((Finset.range l).filter fun i' => (J i').val < i0).card ≤ (Finset.range i0).card := ?_
    · rwa [Finset.card_range] at hh
    refine Finset.card_le_card_of_injOn (fun i' => (J i').val) ?_ ?_
    · intro i' hi'
      have := (Finset.mem_filter.1 hi').2
      exact Finset.mem_coe.2 (Finset.mem_range.2 this)
    · intro a ha b hb hab
      have ha' := Finset.mem_range.1 (Finset.mem_filter.1 ha).1
      have hb' := Finset.mem_range.1 (Finset.mem_filter.1 hb).1
      have h1 := hJ ⟨a, ha'⟩
      have h2 := hJ ⟨b, hb'⟩
      simp only at h1 h2 hab
      have h3 : I ⟨a, ha'⟩ = I ⟨b, hb'⟩ := by rw [← h1, ← h2]; exact Fin.ext hab
      exact congrArg Fin.val (hI h3)

theorem col_even (π : K) (hπ : π ≠ 0) {n l : ℕ} (i0 : ℕ) (I : Fin l → Fin n) (hI : Function.Injective I) (J : ℕ → Fin n)
    (hJ : ∀ q : Fin l, J q.val = I q) (w : Fin n → ℕ → K) :
    (Matrix.of fun p q : Fin l => (if (I p).val < i0 then π⁻¹ else 1) * w (I p) q.val).det =
      π⁻¹ ^ (min l i0) * (π ^ (min l i0 - ((Finset.range l).filter fun i' => (J i').val < i0).card) *
        (Matrix.of fun i i' : Fin l => w (J i'.val) i.val).det) := by
  have h1 := Matrix.det_mul_column (fun p : Fin l => if (I p).val < i0 then π⁻¹ else 1)
    (Matrix.of fun p q : Fin l => w (I p) q.val)
  have h2 : (Matrix.of fun p q : Fin l => w (I p) q.val).det = (Matrix.of fun i i' : Fin l => w (J i'.val) i.val).det := by
    rw [← Matrix.det_transpose]
    congr 1
    ext i i'
    simp [hJ]
  have h3 := card_le_min i0 I hI J hJ
  rw [show (Matrix.of fun p q : Fin l => (if (I p).val < i0 then π⁻¹ else 1) * w (I p) q.val) =
    Matrix.of fun p q : Fin l => (fun p : Fin l => if (I p).val < i0 then π⁻¹ else 1) p *
      (Matrix.of fun p q : Fin l => w (I p) q.val) p q from rfl, h1, h2, prod_ite_pow π⁻¹ i0 I J hJ, ← mul_assoc]
  congr 1
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h3
  rw [hd, Nat.add_sub_cancel_left, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hπ, one_pow, mul_one]

theorem col_odd (π : K) {n l : ℕ} (i0 : ℕ) (I : Fin l → Fin n) (J : ℕ → Fin n)
    (hJ : ∀ q : Fin l, J q.val = I q) (w : Fin n → ℕ → K) :
    (Matrix.of fun i i' : Fin l => (if (I i').val < i0 then π else 1) * w (I i') i.val).det =
      π ^ (((Finset.range l).filter fun i' => (J i').val < i0).card) *
        (Matrix.of fun i i' : Fin l => w (J i'.val) i.val).det := by
  have h1 := Matrix.det_mul_row (fun p : Fin l => if (I p).val < i0 then π else 1)
    (Matrix.of fun i i' : Fin l => w (I i') i.val)
  rw [show (Matrix.of fun i i' : Fin l => (if (I i').val < i0 then π else 1) * w (I i') i.val) =
    Matrix.of fun i i' : Fin l => (fun p : Fin l => if (I p).val < i0 then π else 1) i' *
      (Matrix.of fun i i' : Fin l => w (I i') i.val) i i' from rfl, h1, prod_ite_pow π i0 I J hJ]
  congr 2
  ext i i'
  simp [hJ]

end Col

section GlobalTheory

variable (K : Type) [Field K] [CharZero K] (π : K) (hπ : π ≠ 0) (n : ℕ) (hn : 0 < n) (μ : Fin n → ℕ) (hμ : Antitone μ) (c : ℕ)
  (hc : ∀ t, μ t ≤ c) (ht : ℕ → ℕ) (hht : ∀ k, colH μ k = ht k) (i0 : ℕ) (sz : Fin c → ℕ) (hsz : ∀ k, sz k ≤ n)

include hπ hn hμ hc hht in
theorem blk_even (hs : sz = fun k => colH μ k.val) (I : ∀ k, Fin (sz k) → Fin n) (hI : ∀ k, Function.Injective (I k)) :
    ∃ J : Fin c → ℕ → Fin n, ∀ (h : Matrix (Fin n) (Fin n) K) (z w : Fin n → ℕ → K),
      (mulC h.transpose z = fun a i => (if a.val < i0 then π⁻¹ else 1) * w a i) →
      fockR (hvE (fun a i => C (z a i)) (yV K n) c (fun k => colH μ k.val) (fun k => colH_le μ k.val))
          (rowAct K h.transpose (bideterminant K sz hsz I)) =
        π ^ (-((∑ k : Fin c, min (ht k.val) i0 : ℕ) : ℤ)) * cN K μ *
          ∏ k : Fin c, (π ^ (min (ht k.val) i0 - ((Finset.range (ht k.val)).filter fun i' => (J k i').val < i0).card) *
            (Matrix.of fun i i' : Fin (ht k.val) => w (J k i'.val) i.val).det) := by
  obtain rfl : colH μ = ht := funext hht
  subst hs
  refine ⟨fun k i' => if h : i' < colH μ k.val then I k ⟨i', h⟩ else ⟨0, hn⟩, fun h z w hz => ?_⟩
  have hQ : bideterminant K (fun k : Fin c => colH μ k.val) hsz I ∈ dualWeyl K n n μ := by
    have := bidetMem K n n c (fun k : Fin c => colH μ k.val) hsz I
    rwa [shape_even_holds n μ hμ c hc] at this
  rw [← Top.fockRRowAct, rowAct_hvE, hz, pairing_even_holds K n μ hμ c hc _ _ hQ, BidetPairing.eval_bidet]
  have hk : ∀ k : Fin c, (Matrix.of fun p q : Fin (colH μ k.val) =>
      (if (I k p).val < i0 then π⁻¹ else 1) * w (I k p) (Fin.castLE (hsz k) q).val).det = _ := fun k =>
    col_even π hπ i0 (I k) (hI k) (fun i' => if h : i' < colH μ k.val then I k ⟨i', h⟩ else ⟨0, hn⟩)
      (fun q => by simp) w
  rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, zpow_neg, zpow_natCast,
    inv_pow]
  unfold cN
  ring

include hn hμ hc hht in
theorem blk_odd (hs : sz = fun k => n - colH μ k.val) (I : ∀ k, Fin (sz k) → Fin n) (hI : ∀ k, Function.Injective (I k)) :
    ∃ (J : Fin c → ℕ → Fin n) (ε : K), (ε = 1 ∨ ε = -1) ∧ ∀ (h hi : Matrix (Fin n) (Fin n) K), h * hi = 1 →
      ∀ (z w : Fin n → ℕ → K), (mulC hi z = fun a i => (if a.val < i0 then π else 1) * w a i) →
      fockR (hvO (fun a i => C (z a i)) (yV K n) c (fun k => colH μ k.val))
          (rowAct K h.transpose (bideterminant K sz hsz I)) =
        ε * h.det ^ c * cN K (fun t : Fin n => c - μ t.rev) *
          ∏ k : Fin c, (π ^ (((Finset.range (ht k.val)).filter fun i' => (J k i').val < i0).card) *
            (Matrix.of fun i i' : Fin (ht k.val) => w (J k i'.val) i.val).det) := by
  obtain rfl : colH μ = ht := funext hht
  subst hs
  choose J0 ε0 _ _ hε hdet using fun k : Fin c => unit_columns_holds n (colH μ k.val) (colH_le μ k.val) (I k) (hI k)
  refine ⟨fun k i' => if h : i' < colH μ k.val then J0 k ⟨i', h⟩ else ⟨0, hn⟩, ∏ k, (ε0 k : K), ?_, fun h hi hh z w hz => ?_⟩
  · refine prod_sign _ _ fun k => ?_
    rcases hε k with h1 | h1 <;> rw [h1] <;> simp
  rw [← Top.fockRRowAct, rowAct_hvO h hi hh, hz, fockR_smul_left, pairing_odd_holds K n μ hμ c hc]
  have hk : ∀ k : Fin c, (catM (colH μ k.val) (unitM K (I k)) fun a i => (if a.val < i0 then π else 1) * w a i).det =
      (ε0 k : K) * _ := fun k => (hdet k K _).trans (congrArg (fun y => (ε0 k : K) * y)
    (col_odd π i0 (J0 k) (fun i' => if h : i' < colH μ k.val then J0 k ⟨i', h⟩ else ⟨0, hn⟩) (fun q => by simp) w))
  rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib]
  unfold cN
  ring

end GlobalTheory

section Mat

variable {K : Type*} [CommRing K] {n n' : ℕ}

theorem z_even (Γ Γi : Matrix (Fin n) (Fin n) K) (Γ' Γ'i D : Matrix (Fin n') (Fin n') K) (h1 : Γi * Γ = 1) (h2 : Γ'i * Γ' = 1)
    (hD : D.transpose = D) (d0 : Matrix (Fin n) (Fin n') K) (x : Fin n → ℕ → K) :
    mulC (Γ' * D).transpose (mulC (Γ.transpose.transpose * d0 * Γ'i).transpose (mulC Γi.transpose x)) =
      mulC D (mulC d0.transpose x) := by
  simp only [← mulC_mul]
  congr 1
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, Matrix.transpose_transpose]
  have : Γi * (Γ * d0 * Γ'i) * (Γ' * D) = d0 * D := by
    calc Γi * (Γ * d0 * Γ'i) * (Γ' * D) = (Γi * Γ) * d0 * (Γ'i * Γ') * D := by simp only [Matrix.mul_assoc]
      _ = d0 * D := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  rw [this, Matrix.transpose_mul, hD]

theorem z_odd (Γ Γi : Matrix (Fin n) (Fin n) K) (Γ' Γ'i Di : Matrix (Fin n') (Fin n') K) (h1 : Γi * Γ = 1) (h2 : Γ'i * Γ' = 1)
    (d0 : Matrix (Fin n) (Fin n') K) (x : Fin n → ℕ → K) :
    mulC (Di * Γ'i) (mulC (Γi.transpose * d0 * Γ'.transpose).transpose (mulC Γ x)) = mulC Di (mulC d0.transpose x) := by
  simp only [← mulC_mul]
  congr 1
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
  calc Di * Γ'i * (Γ' * (d0.transpose * Γi) * Γ) = Di * (Γ'i * Γ') * d0.transpose * (Γi * Γ) := by simp only [Matrix.mul_assoc]
    _ = Di * d0.transpose := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one]

theorem mulC_diag (δ : Fin n → K) (w : Fin n → ℕ → K) : mulC (Matrix.diagonal δ) w = fun a i => δ a * w a i := by
  funext a i
  simp [mulC, Matrix.diagonal_apply]

theorem map_mulC {S : Type*} [CommRing S] (f : K →+* S) (B : Matrix (Fin n') (Fin n) K) (x : Fin n → ℕ → K) :
    (fun a i => f (mulC B x a i)) = mulC (B.map f) fun a i => f (x a i) := by
  funext a i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [mulC, map_sum, map_mul]

end Mat

section MF

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def twF (b : BX X) : X.G.P.Qq b.1 →+* X.G.Kf :=
  (X.G.P.ι b.1).comp (X.G.P.σ b.1 ^ b.2.val : X.G.P.Qq b.1 ≃+* X.G.P.Qq b.1).toRingHom

theorem mF_eq (j : ℕ) (b : BX X) (A : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)) :
    mF X j b A = (A.map (twF X b)).submatrix (finCongr (rank_eq X j).symm) (finCongr (rank_eq X j).symm) := rfl

theorem mF_mul (j : ℕ) (b : BX X) (A B : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)) :
    mF X j b A * mF X j b B = mF X j b (A * B) := by
  rw [mF_eq, mF_eq, mF_eq, Matrix.submatrix_mul_equiv, Matrix.map_mul]

theorem mF_one (j : ℕ) (b : BX X) : mF X j b 1 = 1 := by
  rw [mF_eq, Matrix.map_one _ (map_zero _) (map_one _), Matrix.submatrix_one_equiv]

theorem mF_inv (j : ℕ) (b : BX X) (g : GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)) :
    mF X j b g * mF X j b (g⁻¹ : GL _ _) = 1 := by
  rw [mF_mul, Units.mul_inv, mF_one]

theorem DgX_map (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (i0 : X.Pl → ℕ) (v : X.Pl) :
    (DgX X X.G.Kf j i0 v).map (algebraMap X.G.Kf Kc) = DgX X Kc j i0 v := by
  unfold DgX
  rw [Matrix.diagonal_map (map_zero _)]
  congr 1
  funext a
  show algebraMap X.G.Kf Kc (if a.val < i0 v then (p : X.G.Kf)⁻¹ else 1) = _
  split_ifs
  · rw [map_inv₀, map_natCast]
  · rw [map_one]

theorem emX_inj (j : ℕ) : Function.Injective fun x : BX X × (Fin (NJ X j) × Fin (NJ X j)) => emX X j x.1 x.2 := by
  rintro ⟨⟨v, s⟩, y⟩ ⟨⟨v', s'⟩, y'⟩ h
  have h1 := congrArg (idxJ X j) h
  simp only [emX, idxJ_idxI] at h1
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h1
  have h3 := eq_of_heq h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h3
  rfl

theorem NJ_pos (j : ℕ) : 0 < NJ X j := by
  show 0 < NN X.G.P.m X.t j
  unfold NN
  omega

end MF

section SrcX

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def xB {K' : Type} (j : ℕ) (x : X.FrI j → K') (b : BX X) : Fin (NJ X j) → ℕ → K' := fun a i => x ⟨b.1, (b.2, i, a)⟩

theorem ev_Hg (j : ℕ) (b : BX X) (x : X.FrI j → X.G.Kf) :
    evX (fun s => x (xmX X j b s)) (HgX X X.G.Kf j b) = srcN X j b (xB X j x b) := by
  unfold HgX srcN
  split_ifs
  · rw [evX_hvO]; rfl
  · rw [map_mul, map_pow, evX_det, evX_hvE, ← C_pow]; rfl

def xT {K' : Type} [CommRing K'] (j : ℕ) (b : BX X) (γ γi : Matrix (Fin (NJ X j)) (Fin (NJ X j)) K') (y : Fin (NJ X j) → ℕ → K') :
    Fin (NJ X j) → ℕ → K' :=
  if IsOddPos b.2 then mulC γ y else mulC γi.transpose y

def aS (j : ℕ) (b : BX X) (γ γi : Matrix (Fin (NJ X j)) (Fin (NJ X j)) X.G.Kf) : X.G.Kf :=
  if IsOddPos b.2 then γi.det ^ (cX X j b) else γ.det ^ (eX X j b)

theorem src_row (j : ℕ) (b : BX X) (γ γi : Matrix (Fin (NJ X j)) (Fin (NJ X j)) X.G.Kf) (h1 : γ * γi = 1)
    (y : Fin (NJ X j) → ℕ → X.G.Kf) :
    rowAct X.G.Kf γi (srcN X j b y) = aS X j b γ γi • srcN X j b (xT X j b γ γi y) := by
  unfold srcN aS xT
  split_ifs
  · exact rowAct_hvO γi γ (mul_eq_one_comm.1 h1) y _ _
  · exact src_even γ γi h1 y _ _ _ _

theorem map_xT (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (b : BX X) (γ γi : Matrix (Fin (NJ X j)) (Fin (NJ X j)) X.G.Kf)
    (y : Fin (NJ X j) → ℕ → X.G.Kf) :
    (fun a i => algebraMap X.G.Kf Kc (xT X j b γ γi y a i)) =
      xT X j b (γ.map (algebraMap X.G.Kf Kc)) (γi.map (algebraMap X.G.Kf Kc)) fun a i => algebraMap X.G.Kf Kc (y a i) := by
  unfold xT
  split_ifs
  · exact map_mulC _ _ _
  · rw [map_mulC, Matrix.transpose_map]

end SrcX

section BlkX

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [CharZero Kc]

theorem p_ne : (p : Kc) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero

theorem Dg_mul (j : ℕ) (i0 : X.Pl → ℕ) (v : X.Pl) :
    DgX X Kc j i0 v * Matrix.diagonal (fun a : Fin (NJ X (j + 1)) => if a.val < i0 v then (p : Kc) else 1) = 1 := by
  unfold DgX
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs
  · exact inv_mul_cancel₀ (p_ne Kc)
  · exact one_mul 1

theorem blkX (hS : XShape) (j : ℕ) (b : BX X) (i0 : X.Pl → ℕ)
    (I : ∀ k : Fin (cX X j b), Fin (szT X j b k) → Fin (NJ X (j + 1))) (hI : ∀ k, Function.Injective (I k)) :
    ∃ (J : Fin (cX X j b) → ℕ → Fin (NJ X (j + 1))) (ε : Kc), (ε = 1 ∨ ε = -1) ∧
      ∀ (Γ Γi : Matrix (Fin (NJ X j)) (Fin (NJ X j)) Kc) (Γ' Γ'i : Matrix (Fin (NJ X (j + 1))) (Fin (NJ X (j + 1))) Kc),
        Γ * Γi = 1 → Γ' * Γ'i = 1 → ∀ (d0 : Matrix (Fin (NJ X j)) (Fin (NJ X (j + 1))) Kc) (y : Fin (NJ X j) → ℕ → Kc),
        fockR (tgtN X Kc j b (mulC ((if IsOddPos b.2 then Γi else Γ.transpose).transpose * d0 *
              (if IsOddPos b.2 then Γ'.transpose else Γ'i)).transpose (xT X j b Γ Γi y)))
            (rowAct Kc (Γ' * DgX X Kc j i0 b.1).transpose (bideterminant Kc (szT X j b) (szT_le X j b) I)) =
          ε * (if IsOddPos b.2 then (Γ' * DgX X Kc j i0 b.1).det ^ (cX X j b)
              else (p : Kc) ^ (-((∑ k : Fin (cX X j b), min (X.colHt b.1 (j + 1) b.2 k.val) (i0 b.1) : ℕ) : ℤ))) *
            cN Kc (nuT X j b) *
            ∏ k : Fin (cX X j b), ((p : Kc) ^ (if IsOddPos b.2 then
                ((Finset.range (X.colHt b.1 (j + 1) b.2 k.val)).filter fun i' => (J k i').val < i0 b.1).card
              else min (X.colHt b.1 (j + 1) b.2 k.val) (i0 b.1) -
                ((Finset.range (X.colHt b.1 (j + 1) b.2 k.val)).filter fun i' => (J k i').val < i0 b.1).card) *
              (Matrix.of fun i i' : Fin (X.colHt b.1 (j + 1) b.2 k.val) => mulC d0.transpose y (J k i'.val) i.val).det) := by
  obtain ⟨_, _, hanti, hle, _, hcol, _⟩ := hS p X j b
  by_cases ho : IsOddPos b.2
  · obtain ⟨J, ε, hε, H⟩ := blk_odd Kc (p : Kc) (NJ X (j + 1)) (NJ_pos X (j + 1)) (muX X j (NJ X (j + 1)) b) (hanti _)
      (cX X j b) (hle _) (X.colHt b.1 (j + 1) b.2) hcol (i0 b.1) (szT X j b) (szT_le X j b)
      (by funext k; unfold szT; rw [if_pos ho]) I hI
    refine ⟨J, ε, hε, fun Γ Γi Γ' Γ'i h1 h2 d0 y => ?_⟩
    have h3 : (Γ' * DgX X Kc j i0 b.1) *
        (Matrix.diagonal (fun a : Fin (NJ X (j + 1)) => if a.val < i0 b.1 then (p : Kc) else 1) * Γ'i) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (DgX X Kc j i0 b.1), Dg_mul, Matrix.one_mul, h2]
    have h4 := H _ _ h3 (mulC (Γi.transpose * d0 * Γ'.transpose).transpose (mulC Γ y)) (mulC d0.transpose y)
      (by rw [z_odd Γ Γi Γ' Γ'i _ (mul_eq_one_comm.1 h1) (mul_eq_one_comm.1 h2), mulC_diag])
    unfold tgtN nuT xT
    simp only [if_pos ho]
    exact h4
  · obtain ⟨J, H⟩ := blk_even Kc (p : Kc) (p_ne Kc) (NJ X (j + 1)) (NJ_pos X (j + 1)) (muX X j (NJ X (j + 1)) b) (hanti _)
      (cX X j b) (hle _) (X.colHt b.1 (j + 1) b.2) hcol (i0 b.1) (szT X j b) (szT_le X j b)
      (by funext k; unfold szT; rw [if_neg ho]) I hI
    refine ⟨J, 1, Or.inl rfl, fun Γ Γi Γ' Γ'i h1 h2 d0 y => ?_⟩
    have h4 := H (Γ' * DgX X Kc j i0 b.1) (mulC (Γ.transpose.transpose * d0 * Γ'i).transpose (mulC Γi.transpose y))
      (mulC d0.transpose y)
      (by
        rw [z_even Γ Γi Γ' Γ'i _ (mul_eq_one_comm.1 h1) (mul_eq_one_comm.1 h2) (by unfold DgX; exact Matrix.diagonal_transpose _)]
        unfold DgX
        rw [mulC_diag])
    unfold tgtN nuT xT
    simp only [if_neg ho, one_mul]
    exact h4

end BlkX

section PIX

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]

theorem eval_colFac (j : ℕ) (Ist : X.ColCh j) (v : X.Pl) (s : Fin (X.G.P.n' v)) (c : ℕ) (xK : X.FrI j → Kc) (d0 : X.ZA j → Kc) :
    eval d0 (map (eval₂Hom (Int.castRingHom Kc) xK) (X.colFac j Ist v s c)) =
      (Matrix.of fun i i' : Fin (X.colHt v (j + 1) s c) =>
        mulC (dM X Kc j ⟨v, s⟩ d0).transpose (xB X j xK ⟨v, s⟩) (Ist v s c i'.val) i.val).det := by
  unfold Sys.colFac
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i i' => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, map_C, map_X, eval_C, eval_X,
    coe_eval₂Hom, eval₂_X, mulC, dM, xB, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem eval_PI (j : ℕ) (Ist : X.ColCh j) (i0 : X.Pl → ℕ) (xK : X.FrI j → Kc) (d0 : X.ZA j → Kc) :
    eval d0 (map (eval₂Hom (Int.castRingHom Kc) xK) (X.PI j Ist i0)) =
      ∏ b : BX X, ∏ k : Fin (cX X j b), ((p : Kc) ^ (X.colExp j Ist i0 b.1 b.2 k.val) *
        (Matrix.of fun i i' : Fin (X.colHt b.1 (j + 1) b.2 k.val) =>
          mulC (dM X Kc j b d0).transpose (xB X j xK b) (Ist b.1 b.2 k.val i'.val) i.val).det) := by
  unfold Sys.PI
  rw [Fintype.prod_sigma]
  simp only [map_prod, map_mul, map_pow, map_natCast, eval_colFac]
  refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
  exact Finset.prod_range _

end PIX

section Main

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] [CharZero Kc]

def IstOf (j : ℕ) (J : ∀ b : BX X, Fin (cX X j b) → ℕ → Fin (NJ X (j + 1))) : X.ColCh j :=
  fun v s k i' => if hk : k < cX X j ⟨v, s⟩ then J ⟨v, s⟩ ⟨k, hk⟩ i' else ⟨0, NJ_pos X (j + 1)⟩

theorem IstOf_apply (j : ℕ) (J : ∀ b : BX X, Fin (cX X j b) → ℕ → Fin (NJ X (j + 1))) (b : BX X) (k : Fin (cX X j b)) (i' : ℕ) :
    IstOf X j J b.1 b.2 k.val i' = J b k i' := by
  obtain ⟨v, s⟩ := b
  unfold IstOf
  rw [dite_eq_left k.isLt]

omit [Algebra (MainNotions.FormalGroupSystem.K0 p) Kc] [CharZero Kc] in
theorem map_tgt (j : ℕ) (i0 : X.Pl → ℕ) (H : BX X → Matrix (Fin (NJ X (j + 1))) (Fin (NJ X (j + 1))) X.G.Kf)
    (I : ∀ (b : BX X) (k : Fin (cX X j b)), Fin (szT X j b k) → Fin (NJ X (j + 1))) :
    map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b)
      (rowAct X.G.Kf (H b * DgX X X.G.Kf j i0 b.1).transpose (bideterminant X.G.Kf (szT X j b) (szT_le X j b) (I b)))) =
    ∏ b, rename (emX X (j + 1) b) (rowAct Kc ((H b).map (algebraMap X.G.Kf Kc) * DgX X Kc j i0 b.1).transpose
      (bideterminant Kc (szT X j b) (szT_le X j b) (I b))) := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun _ _ => ?_
  rw [map_rename, map_rowAct, BidetPairing.map_bidet', Matrix.transpose_map, Matrix.map_mul, DgX_map]

theorem pair_of_hyp (hB : XB) (hG : XG) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La') (P : DA X Kc j)
    (f : MvPowerSeries (X.ZA j) Kc) (T' : XspC (X.Pj (j + 1)) Kc) (κ : Kc) (Ist : X.ColCh j) (i0 : X.Pl → ℕ) (xK : X.FrI j → Kc)
    (h : ∀ d0 : X.ZA j → Kc, fockR (evD X Kc j (fun y => ∑ z, bc Kc φ z y * d0 z) P) T' =
      κ * eval d0 (map (eval₂Hom (Int.castRingHom Kc) xK) (X.PI j Ist i0))) :
    fockR (pairD X Kc j P (linSub (bc Kc φ) f)) T' = κ * eval xK (applyD (X.PI j Ist i0) f) := by
  have : Infinite Kc := CharZero.infinite Kc
  have h1 := hB p X Kc j La La' φ P f (fockL T') (C κ * map (eval₂Hom (Int.castRingHom Kc) xK) (X.PI j Ist i0))
    (fun d0 => by rw [map_mul, eval_C]; exact (h d0).symm)
  rw [sum_C_mul, hG] at h1
  exact h1

omit [Algebra (MainNotions.FormalGroupSystem.K0 p) Kc] [CharZero Kc] in
theorem scal (j : ℕ) (b : BX X) (γ γi : Matrix (Fin (NJ X j)) (Fin (NJ X j)) X.G.Kf)
    (γ' : Matrix (Fin (NJ X (j + 1))) (Fin (NJ X (j + 1))) X.G.Kf) (h : γ * γi = 1) (i0 : X.Pl → ℕ) (q : Kc) :
    algebraMap X.G.Kf Kc (aS X j b γ γi) *
        (if IsOddPos b.2 then (γ'.map (algebraMap X.G.Kf Kc) * DgX X Kc j i0 b.1).det ^ (cX X j b) else q) =
      if IsOddPos b.2 then (algebraMap X.G.Kf Kc γ.det) ^ (-(cX X j b : ℤ)) *
        (algebraMap X.G.Kf Kc (γ' * DgX X X.G.Kf j i0 b.1).det) ^ (cX X j b)
      else (algebraMap X.G.Kf Kc γ.det) ^ (eX X j b) * q := by
  unfold aS
  split_ifs
  · have h2 : γ.det * γi.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
    have h3 : algebraMap X.G.Kf Kc (γ' * DgX X X.G.Kf j i0 b.1).det =
        (γ'.map (algebraMap X.G.Kf Kc) * DgX X Kc j i0 b.1).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, DgX_map]
    rw [eq_inv_of_mul_eq_one_right h2, map_pow, map_inv₀, zpow_neg, zpow_natCast, inv_pow, h3]
  · rw [map_pow]

end Main

end MiddleFrameLemmas

open MiddleFrameLemmas in
theorem xMid_of (hS : XShape) (hA : XA) (hB : XB) (hB2 : TransposedFrameImageBlockwise) (hC : XC) (hG : XG) : XMid := by
  intro p _ X Kc _ _ _ _ j La La' φ i0 I hI
  choose J ε hε hblk using fun b : BX X => blkX X Kc hS j b i0 (I b) (hI b)
  refine ⟨IstOf X j J, ∏ b, ε b, prod_sign _ _ hε, fun f x => ?_⟩
  have hsrc : (∏ b, rename (emX X j b) (rowAct X.G.Kf (mF X j b ((φ.g b.1)⁻¹ : GL _ _))
        (evX (fun s => x (xmX X j b s)) (HgX X X.G.Kf j b)))) =
      (∏ b, aS X j b (mF X j b (φ.g b.1)) (mF X j b ((φ.g b.1)⁻¹ : GL _ _))) •
        ∏ b, rename (emX X j b) (srcN X j b
          (xT X j b (mF X j b (φ.g b.1)) (mF X j b ((φ.g b.1)⁻¹ : GL _ _)) (xB X j x b))) := by
    rw [← Finset.prod_smul]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [ev_Hg, src_row X j b _ _ (mF_inv X j b (φ.g b.1)), map_smul]
  rw [hsrc, map_smul, LinearMap.smul_apply, delF_apply, hA p X Kc j, map_tgt, ← algebraMap_smul Kc, fockR_smul_left]
  rw [pair_of_hyp X Kc hB hG j La La' φ _ f _
    (∏ b : BX X, (ε b * (if IsOddPos b.2 then
        ((mF X (j + 1) b (φ.g' b.1).val).map (algebraMap X.G.Kf Kc) * DgX X Kc j i0 b.1).det ^ (cX X j b)
      else (p : Kc) ^ (-((∑ k : Fin (cX X j b), min (X.colHt b.1 (j + 1) b.2 k.val) (i0 b.1) : ℕ) : ℤ))) *
        cN Kc (nuT X j b))) (IstOf X j J) i0 (fun t => algebraMap X.G.Kf Kc (x t))]
  · rw [← mul_assoc]
    congr 1
    unfold numericalIdentityScalar
    rw [map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    have hs := scal X Kc j b (mF X j b (φ.g b.1)) (mF X j b ((φ.g b.1)⁻¹ : GL _ _)) (mF X (j + 1) b (φ.g' b.1).val)
      (mF_inv X j b (φ.g b.1)) i0
      ((p : Kc) ^ (-((∑ k : Fin (cX X j b), min (X.colHt b.1 (j + 1) b.2 k.val) (i0 b.1) : ℕ) : ℤ)))
    linear_combination (ε b * cN Kc (nuT X j b)) * hs
  · intro d0
    rw [map_prod, Finset.prod_congr rfl fun b _ => hC p X Kc j b _ _,
      fock_product_holds Kc (BX X) _ _ (emX X (j + 1)) (emX_inj X (j + 1)), eval_PI, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [hB2 p X Kc j La La' φ d0 b, map_xT]
    have h := hblk b ((mF X j b (φ.g b.1)).map (algebraMap X.G.Kf Kc))
      ((mF X j b ((φ.g b.1)⁻¹ : GL _ _)).map (algebraMap X.G.Kf Kc))
      ((mF X (j + 1) b (φ.g' b.1).val).map (algebraMap X.G.Kf Kc))
      ((mF X (j + 1) b ((φ.g' b.1)⁻¹).val).map (algebraMap X.G.Kf Kc))
      (by rw [← Matrix.map_mul, mF_inv, Matrix.map_one _ (map_zero _) (map_one _)])
      (by rw [← Matrix.map_mul, mF_inv, Matrix.map_one _ (map_zero _) (map_one _)])
      (dM X Kc j b d0) (fun a i => algebraMap X.G.Kf Kc (xB X j x b a i))
    simp only [Sys.colExp, IstOf_apply]
    exact h

end Formalism.L2.PairingIndexBounds.Ent
end
end

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.FrameEdgeIdentityHolds
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def dgQ (K : Type) [Field K] (p k r : ℕ) : Matrix (Fin k) (Fin k) K := Matrix.diagonal fun c => if c.val < r then (p : K)⁻¹ else 1

theorem dgQ_det_ne (K : Type) [Field K] (p k r : ℕ) (hp : (p : K) ≠ 0) : (dgQ K p k r).det ≠ 0 := by
  unfold dgQ
  rw [Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun c _ => ?_
  split_ifs
  · exact inv_ne_zero hp
  · exact one_ne_zero

theorem mF_dgQ (j : ℕ) (b : BX X) (i0 : X.Pl → ℕ) :
    mF X (j + 1) b (dgQ (X.G.P.Qq b.1) p _ (i0 b.1)) = DgX X X.G.Kf j i0 b.1 := by
  unfold mF dgQ DgX
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases hac : a = c
  · subst hac
    rw [if_pos rfl, if_pos rfl]
    have : ((finCongr (rank_eq X (j + 1)).symm) a).val = a.val := rfl
    rw [this]
    split_ifs
    · rw [map_inv₀, map_inv₀, map_natCast, map_natCast]
    · rw [map_one, map_one]
  · rw [if_neg hac, if_neg (fun h => hac ((finCongr (rank_eq X (j + 1)).symm).injective h)), map_zero, map_zero]

theorem frame_edge_identity_holds : XEdge := by
  intro p _ X j L' L'' i0 h2 h4
  have key : ∀ v : X.Pl, ∃ g' h' : GL (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v),
      X.latAt v (j + 1) L'' = colSpan (X.G.P.W v) (g' : Matrix _ _ (X.G.P.Qq v)) ∧
      X.latAt v (j + 1) L' = colSpan (X.G.P.W v) (h' : Matrix _ _ (X.G.P.Qq v)) ∧
      (h' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)) =
        (g' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)) *
          dgQ (X.G.P.Qq v) p ((X.Pj (j + 1)).m + 1) (i0 v) := by
    intro v
    have hS := X.G.P.setting v
    have := hS.frac_alt
    have hp0 : (p : X.G.P.Qq v) ≠ 0 := pQ_ne hS.p_unif
    rcases h4 v with ⟨h0, hL⟩ | ⟨_, he⟩
    · obtain ⟨g, hg, hgL⟩ := h2 v
      have h0' : i0 v = 0 := h0
      refine ⟨Matrix.nonsingInvUnit g hg, Matrix.nonsingInvUnit g hg, ?_, hgL, ?_⟩
      · show L'' v = _
        rw [hL]; exact hgL
      · have : dgQ (X.G.P.Qq v) p ((X.Pj (j + 1)).m + 1) (i0 v) = 1 := by
          unfold dgQ
          rw [h0']
          simp
        rw [this, mul_one]
    · obtain ⟨g, hg, hsrc, htgt⟩ := Formalism.L2.G.Model.edgeBasis hS _ _ _ he
      have hd : IsUnit (g * dgQ (X.G.P.Qq v) p ((X.Pj (j + 1)).m + 1) (i0 v)).det := by
        rw [Matrix.det_mul]
        exact hg.mul (isUnit_iff_ne_zero.2 (dgQ_det_ne _ _ _ _ hp0))
      exact ⟨Matrix.nonsingInvUnit g hg, Matrix.nonsingInvUnit _ hd, hsrc, htgt, rfl⟩
  choose g' h' h1 h2' h3 using key
  refine ⟨g', h', h1, h2', fun b => ?_⟩
  rw [h3 b.1, ← mF_dgQ X j b i0]
  unfold mF
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  exact Matrix.map_mul (f := (X.G.P.ι b.1).comp (X.G.P.σ b.1 ^ b.2.val : X.G.P.Qq b.1 ≃+* X.G.P.Qq b.1).toRingHom)

end Formalism.L2.PairingIndexBounds.Ent
end
end

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.FinalOf
noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])

theorem pending_tuple_admissible_of_shape (hS : XShape) (hBrS : XBrS) (hBrT : XBrT) (hInj : XInj) (hSp : XSpanN) (hMid : XMid) (hU : XUnit)
    (hE : XEdge) (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.FormalGroupSystem.adm7 D X (pendT X E hfin hst hLT pos F) := by
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  intro j _ La c' L' L'' i0 h1 h2 h3 h4
  exact admissible_general_lattice_tuple X ℂ_[p] hS hBrS hBrT hInj hSp hMid hU hE (OcC p) OcC_val
    (fun o => ((pendT X E hfin hst hLT pos F).Oc_K _).2 ⟨o, rfl⟩) j La c' L' L'' i0 h1 h2 h3 h4

end Formalism.L2.PairingIndexBounds.Ent
end
end

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

theorem lattice_shape_a_holds : XA := xA_of frame_shape_identity_holds
theorem lattice_span_normal_holds : XSpanN := xSpanN_of frame_shape_identity_holds
theorem lattice_shape_middle_holds : XMid := xMid_of frame_shape_identity_holds lattice_shape_a_holds frame_change_pairing_holds transposed_frame_image_blockwise_holds frame_change_compatibility_holds frame_change_group_action_holds
theorem lattice_shape_unit_holds : XUnit := xUnit_of frame_shape_identity_holds

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])

theorem pending_tuple_admissible (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.FormalGroupSystem.adm7 D X (pendT X E hfin hst hLT pos F) :=
  pending_tuple_admissible_of_shape X E hfin hst hLT pos F frame_shape_identity_holds branching_source_identity branching_target_identity frame_change_injective_holds lattice_span_normal_holds lattice_shape_middle_holds lattice_shape_unit_holds
    frame_edge_identity_holds D

end Formalism.L2.PairingIndexBounds.Ent
