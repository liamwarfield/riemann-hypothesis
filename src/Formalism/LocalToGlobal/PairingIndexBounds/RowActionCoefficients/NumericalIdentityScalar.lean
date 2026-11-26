module

public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SuccMulSuccSubOneDivSucc
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.HighestVectorFullHolds

@[expose] public section

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.YVMapRowAct
section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.FinalTheorems
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.MainNotions.G

def evX {K : Type} [CommRing K] {n : ℕ} (x : ℕ × Fin n → K) : GenR K n →+* MvPolynomial (Fin n × Fin n) K :=
  eval₂Hom (RingHom.id _) fun s => C (x s)

section FinalTheorems

variable {O K Kc : Type} [CommRing O] [Field K] [Algebra O K] [Infinite K] [Field Kc] [Algebra K Kc]
  {B τ τx : Type} [Fintype B] [DecidableEq B] {n : ℕ} (em : B → Fin n × Fin n → τ)
  (xm : B → ℕ × Fin n → τx) (hxm : Function.Injective fun x : B × (ℕ × Fin n) => xm x.1 x.2)
  (ν : B → Fin n → ℕ)
  (h hi : B → Matrix (Fin n) (Fin n) K) (hh : ∀ b, hi b * h b = 1)
  (M : AddSubgroup Kc) (hM : ∀ (o : O), ∀ a ∈ M, algebraMap K Kc (algebraMap O K o) * a ∈ M)
  (Hg : B → GenR K n)
  (hQ : ∀ b, (weyl O n n le_rfl (ν b)).map (toK O K) ≤ Submodule.span O (Set.range fun m => AddMonoidAlgebra.coeff (Hg b) m))
  (Φ : MvPolynomial τ K →ₗ[K] Kc) (A : MvPolynomial τx Kc) (hA : ∀ m, AddMonoidAlgebra.coeff A m ∈ M)
  (hnum : ∀ x : τx → K, Φ (∏ b, rename (em b) (rowAct K (hi b) (evX (fun s => x (xm b s)) (Hg b)))) =
    eval (fun t => algebraMap K Kc (x t)) A)


include hxm hh hM hQ hA hnum in
theorem src_abs (hI : Interp) (hCP : CoefProd) (F : B → MvPolynomial (Fin n × Fin n) K)
    (hF : ∀ b, F b ∈ deltaL O K n (ν b) (h b)) : Φ (∏ b, rename (em b) (F b)) ∈ M := by
  classical
  have hh' : ∀ b, h b * hi b = 1 := fun b => mul_eq_one_comm.1 (hh b)
  let ψ : ∀ b, MvPolynomial (Fin n × Fin n) K →ₐ[K] MvPolynomial τ K := fun b => (rename (em b)).comp (rowAct K (hi b))
  let HH : MvPolynomial τx (MvPolynomial τ K) := ∏ b, rename (xm b) (map (ψ b : MvPolynomial (Fin n × Fin n) K →+* MvPolynomial τ K) (Hg b))
  have hcoef : ∀ p : B → (ℕ × Fin n →₀ ℕ), AddMonoidAlgebra.coeff HH (∑ b, (p b).mapDomain (xm b)) = ∏ b, ψ b (AddMonoidAlgebra.coeff (Hg b) (p b)) := by
    intro p
    rw [hCP (MvPolynomial τ K) B (ℕ × Fin n) τx xm hxm]
    exact Finset.prod_congr rfl fun b _ => coeff_map _ _ _
  have hev : ∀ x : τx → K, eval₂ (RingHom.id (MvPolynomial τ K)) (fun t => C (x t)) HH =
      ∏ b, rename (em b) (rowAct K (hi b) (evX (fun s => x (xm b s)) (Hg b))) := by
    intro x
    show eval₂Hom (RingHom.id (MvPolynomial τ K)) (fun t => C (x t)) HH = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [coe_eval₂Hom, eval₂_rename, eval₂_map]
    show _ = ψ b (eval₂ (RingHom.id _) (fun s => C (x (xm b s))) (Hg b))
    rw [← AlgHom.coe_toRingHom, eval₂_comp_left]
    congr 1
    funext s
    show C (x (xm b s)) = ψ b (C (x (xm b s)))
    exact ((ψ b).commutes (x (xm b s))).symm
  have hw : ∀ m, Φ (AddMonoidAlgebra.coeff HH m) = AddMonoidAlgebra.coeff A m := by
    intro m
    by_cases hm : m ∈ HH.support ∪ A.support
    · have := hI K τx Kc (HH.support ∪ A.support) (fun m => Φ (AddMonoidAlgebra.coeff HH m) - AddMonoidAlgebra.coeff A m) ?_ m hm
      · exact sub_eq_zero.1 this
      · intro x
        simp only [smul_sub]
        rw [Finset.sum_sub_distrib, sub_eq_zero]
        have e1 : ∑ m ∈ HH.support ∪ A.support, (m.prod fun t k => x t ^ k) • Φ (AddMonoidAlgebra.coeff HH m) =
            Φ (eval₂ (RingHom.id (MvPolynomial τ K)) (fun t => C (x t)) HH) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [eval₂_eq, map_sum, ← Finset.sum_subset Finset.subset_union_left]
          · refine Finset.sum_congr rfl fun d _ => ?_
            rw [← map_smul]
            congr 1
            rw [RingHom.id_apply, smul_eq_C_mul, mul_comm, Finsupp.prod, map_prod]
            simp only [map_pow]
          · intro d _ hd
            rw [notMem_support_iff.1 hd, map_zero, smul_zero]
        have e2 : ∑ m ∈ HH.support ∪ A.support, (m.prod fun t k => x t ^ k) • AddMonoidAlgebra.coeff A m =
            eval (fun t => algebraMap K Kc (x t)) A := by
          rw [eval_eq, ← Finset.sum_subset Finset.subset_union_right]
          · refine Finset.sum_congr rfl fun d _ => ?_
            rw [Algebra.smul_def, mul_comm, Finsupp.prod, map_prod]
            simp only [map_pow]
          · intro d _ hd
            rw [notMem_support_iff.1 hd, smul_zero]
        rw [e1, e2, hev, hnum]
    · rw [Finset.mem_union, not_or] at hm
      rw [notMem_support_iff.1 hm.1, notMem_support_iff.1 hm.2, map_zero]
  let T : Submodule O (MvPolynomial τ K) :=
    { carrier := {G | Φ G ∈ M}
      add_mem' := fun {a b} ha hb => by
        show Φ (a + b) ∈ M
        rw [map_add (f := _)]; exact M.add_mem ha hb
      zero_mem' := by show Φ 0 ∈ M; rw [map_zero]; exact M.zero_mem
      smul_mem' := fun o G hG => by
        show Φ (o • G) ∈ M
        rw [← algebraMap_smul K o G, map_smul, Algebra.smul_def]
        exact hM o _ hG }
  refine prod_span (R := O) (fun b => Set.range fun m => ψ b (AddMonoidAlgebra.coeff (Hg b) m)) T ?_ _ ?_
  · intro f hf
    choose p hp using hf
    show Φ _ ∈ M
    rw [← Finset.prod_congr rfl fun b _ => hp b, ← hcoef, hw]
    exact hA _
  · intro b
    have h2 : rowAct K (h b) (F b) ∈ Submodule.span O (Set.range fun m => AddMonoidAlgebra.coeff (Hg b) m) := hQ b (hF b)
    have h3 : rename (em b) (F b) = ψ b (rowAct K (h b) (F b)) := by
      show _ = rename (em b) (rowAct K (hi b) (rowAct K (h b) (F b)))
      rw [rowAct_rowAct, hh' b, rowAct_one]
    rw [h3]
    have h4 := Submodule.mem_map_of_mem (f := (ψ b).toLinearMap.restrictScalars O) h2
    rw [Submodule.map_span, ← Set.range_comp] at h4
    exact h4

end FinalTheorems

end Formalism.L2.PairingIndexBounds.Ent
end
end

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Pend

section Gen

variable {A A' : Type*} [CommRing A] [CommRing A']

theorem map_hvE (f : A →+* A') {n : ℕ} (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A) (c : ℕ) (h : Fin c → ℕ)
    (hh : ∀ k, h k ≤ n) : f (hvE x y c h hh) = hvE (fun a i => f (x a i)) (y.map f) c h hh := by
  unfold hvE
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i t
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.map_apply, map_sum, map_mul]

theorem map_hvO (f : A →+* A') {n : ℕ} (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A) (c : ℕ) (h : Fin c → ℕ) :
    f (hvO x y c h) = hvO (fun a i => f (x a i)) (y.map f) c h := by
  unfold hvO
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_catM]

theorem hvE_mul {n : ℕ} (g : Matrix (Fin n) (Fin n) A) (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A) (c : ℕ) (h : Fin c → ℕ)
    (hh : ∀ k, h k ≤ n) : hvE x (g * y) c h hh = hvE (mulC g.transpose x) y c h hh := by
  unfold hvE
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  ext i t
  simp only [Matrix.of_apply, Matrix.mul_apply, mulC, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hvO_mul {n : ℕ} (g : Matrix (Fin n) (Fin n) A) (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A) (c : ℕ) (h : Fin c → ℕ) :
    hvO (mulC g x) (g * y) c h = g.det ^ c * hvO x y c h := by
  unfold hvO
  have : ∀ k : Fin c, (catM (h k) (g * y) (mulC g x)).det = g.det * (catM (h k) y x).det := by
    intro k
    rw [← mul_catM, Matrix.det_mul]
  rw [Finset.prod_congr rfl fun k _ => this k, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Gen

section Row

variable {K : Type} [CommRing K] {n : ℕ}

theorem yV_map_rowAct (g : Matrix (Fin n) (Fin n) K) :
    (yV K n).map (rowAct K g) = g.map C * yV K n := by
  ext a t
  simp only [Matrix.map_apply, yV, Matrix.mul_apply]
  unfold rowAct
  rw [aeval_X]

theorem rowAct_hvE (g : Matrix (Fin n) (Fin n) K) (x : Fin n → ℕ → K) (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k, h k ≤ n) :
    rowAct K g (hvE (fun a i => C (x a i)) (yV K n) c h hh) = hvE (fun a i => C (mulC g.transpose x a i)) (yV K n) c h hh := by
  have h1 := map_hvE (rowAct K (n := n) g : MvPolynomial (Fin n × Fin n) K →+* MvPolynomial (Fin n × Fin n) K)
    (fun a i => C (x a i)) (yV K n) c h hh
  rw [RingHom.coe_coe] at h1
  rw [h1, yV_map_rowAct g, hvE_mul]
  congr 1
  funext a i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulC, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  exact (rowAct K g).commutes _

theorem rowAct_hvO (g gi : Matrix (Fin n) (Fin n) K) (hg : g * gi = 1) (x : Fin n → ℕ → K) (c : ℕ) (h : Fin c → ℕ) :
    rowAct K g (hvO (fun a i => C (x a i)) (yV K n) c h) = g.det ^ c • hvO (fun a i => C (mulC gi x a i)) (yV K n) c h := by
  have h1 := map_hvO (rowAct K (n := n) g : MvPolynomial (Fin n × Fin n) K →+* MvPolynomial (Fin n × Fin n) K)
    (fun a i => C (x a i)) (yV K n) c h
  rw [RingHom.coe_coe] at h1
  rw [h1, yV_map_rowAct g]
  have h2 : (fun a i => rowAct K (n := n) g (C (x a i))) =
      mulC (g.map C) (fun a i => (C (mulC gi x a i) : MvPolynomial (Fin n × Fin n) K)) := by
    funext a i
    rw [show rowAct K (n := n) g (C (x a i)) = C (x a i) from (rowAct K g).commutes _]
    have h3 : x a i = mulC g (mulC gi x) a i := by rw [← mulC_mul, hg]; simp [mulC, Matrix.one_apply]
    rw [h3]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mulC, Matrix.map_apply, map_sum, map_mul]
  rw [h2, hvO_mul, smul_eq_C_mul, map_pow]
  congr 2
  exact (RingHom.map_det C g).symm

end Row

end Formalism.L2.PairingIndexBounds.Ent
end
end

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.TgtBidet
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.MainNotions.G

variable {O K Kc : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [CharZero K] [Field Kc] [Algebra K Kc]
  {B τ : Type} [Fintype B] [DecidableEq B] {n : ℕ} (em : B → Fin n × Fin n → τ)
  (hem : Function.Injective fun x : B × (Fin n × Fin n) => em x.1 x.2)
  (ν : B → Fin n → ℕ) (hν : ∀ b, Antitone (ν b))
  (h hi : B → Matrix (Fin n) (Fin n) K) (hh : ∀ b, hi b * h b = 1)
  (M : AddSubgroup Kc) (hM : ∀ (o : O), ∀ a ∈ M, algebraMap K Kc (algebraMap O K o) * a ∈ M)

theorem toK_bidet {r n K' : ℕ} (sz : Fin K' → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    toK O K (bideterminant O sz hsz I) = bideterminant K sz hsz I := by
  show map (algebraMap O K) _ = _
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp


include hem hν hh hM in
theorem tgt_bidet (hDB : DualBases) (hFP : FockProd) (hRe : Reorder) (c : B → ℕ) (sz : ∀ b, Fin (c b) → ℕ)
    (hsz : ∀ b k, sz b k ≤ n) (hshape : ∀ b, shapeDeg (sz b) = ν b) (y : MvPolynomial τ Kc)
    (hy : y ∈ Submodule.span Kc {z | ∃ F : B → MvPolynomial (Fin n × Fin n) K, (∀ b, F b ∈ dualWeyl K n n (ν b)) ∧
      z = map (algebraMap K Kc) (∏ b, rename (em b) (F b))})
    (hp : ∀ I : ∀ b, ∀ k, Fin (sz b k) → Fin n,
      ∃ a ∈ M, fockR y (map (algebraMap K Kc) (∏ b, rename (em b) (rowAct K (h b).transpose (bideterminant K (sz b) (hsz b) (I b))))) =
        a * ∏ b, cN Kc (ν b)) :
    y ∈ AddSubgroup.closure {z | ∃ a ∈ M, ∃ F : B → MvPolynomial (Fin n × Fin n) K,
      (∀ b, F b ∈ deltaL O K n (ν b) (h b)) ∧ z = a • map (algebraMap K Kc) (∏ b, rename (em b) (F b))} := by
  refine tgt_abs (O := O) em hem ν hν h hi hh M hDB hFP y hy fun Q hQ => ?_
  let T : Submodule O (MvPolynomial τ K) :=
    { carrier := {Z | ∃ a ∈ M, fockR y (map (algebraMap K Kc) Z) = a * ∏ b, cN Kc (ν b)}
      add_mem' := by
        rintro Z Z' ⟨a, ha, h1⟩ ⟨a', ha', h2⟩
        refine ⟨a + a', M.add_mem ha ha', ?_⟩
        rw [map_add (f := _), fockR_comm, fockR_add_left, fockR_comm _ y, fockR_comm _ y, h1, h2, add_mul]
      zero_mem' := ⟨0, M.zero_mem, by rw [map_zero, fockR_comm, fockR_zero_left, zero_mul]⟩
      smul_mem' := by
        rintro o Z ⟨a, ha, h1⟩
        refine ⟨_, hM o a ha, ?_⟩
        rw [← algebraMap_smul K o Z, smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul, fockR_comm, fockR_smul_left, fockR_comm, h1,
          mul_assoc] }
  refine prod_span (R := O) (fun b => Set.range fun I : ∀ k, Fin (sz b k) → Fin n =>
    rename (em b) (rowAct K (h b).transpose (bideterminant K (sz b) (hsz b) I))) T ?_ _ ?_
  · intro f hf
    choose I hI using hf
    obtain ⟨a, ha, h1⟩ := hp I
    refine ⟨a, ha, ?_⟩
    rw [← Finset.prod_congr rfl fun b _ => hI b]
    exact h1
  · intro b
    have h1 := hQ b
    rw [standardMonomialSpanDomain O n n (ν b), Submodule.map_span] at h1
    have h2 := Submodule.mem_map_of_mem (f := (((rename (em b) : MvPolynomial (Fin n × Fin n) K →ₐ[K] MvPolynomial τ K).comp
      (rowAct K (h b).transpose)).toLinearMap).restrictScalars O) h1
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨_, ⟨K', sz', hsz', I', hs', rfl⟩, rfl⟩, rfl⟩
    obtain ⟨I'', hI''⟩ := hRe K n n K' (c b) sz' (sz b) hsz' (hsz b) (hs'.trans (hshape b).symm) I'
    refine ⟨I'', ?_⟩
    rw [toK_bidet, hI'']
    rfl

end Formalism.L2.PairingIndexBounds.Ent
end
end

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.Bridge
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems Formalism.MainNotions.FormalGroupSystem.Pf

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

abbrev GlobalTheory : Type := Σ v : Fin P.nV, Fin (P.n' v)

def emP (b : GlobalTheory P) (v : Fin (P.m + 1) × Fin (P.m + 1)) :
    (Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) := ⟨b.1, (b.2, v)⟩

def gam (g : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (b : GlobalTheory P) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf :=
  la_tw (P.ι b.1) (P.σ b.1) b.2.val (g b.1)

def nuB (b : GlobalTheory P) : Fin (P.m + 1) → ℕ := nuOf (lamAt (P.lam0 b.1) b.2)

def eB (b : GlobalTheory P) : ℤ := lamAt (P.lam0 b.1) b.2 (Fin.last P.m)

def sB (g : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) : Kf := ∏ b : GlobalTheory P, (gam P g b).det ^ (-(eB P b))

theorem prod_blocks (c : GlobalTheory P → Kf) (F : GlobalTheory P → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf) :
    ∏ v, P.vEmb v (∏ s, blockEmb Kf s (c ⟨v, s⟩ • F ⟨v, s⟩)) = (∏ b, c b) • ∏ b, rename (emP P b) (F b) := by
  have e1 : ∀ (b : GlobalTheory P) (G : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf),
      P.vEmb b.1 (blockEmb Kf b.2 G) = rename (emP P b) G := by
    intro b G
    simp only [Places.vEmb, blockEmb]
    rw [rename_rename]
    rfl
  rw [show (∏ b, c b) • ∏ b, rename (emP P b) (F b) = ∏ b : GlobalTheory P, c b • rename (emP P b) (F b) by
    simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]]
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_smul, map_smul, e1 ⟨v, s⟩]

theorem delta_zero_eq_twisted_delta (hinj : Function.Injective (algebraMap O Kf)) (v : Fin P.nV) (s : Fin (P.n' v))
    (g : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (hg : IsUnit g.det) :
    Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val (colSpan (P.W v) g)) =
      deltaLTw O Kf P.m (lamAt (P.lam0 v) s) (la_tw (P.ι v) (P.σ v) s.val g) := by
  have hd : Antitone (lamAt (P.lam0 v) s) := by
    unfold lamAt
    split_ifs
    · exact P.dom v s
    · intro i j hij
      exact neg_le_neg (P.dom v s (Fin.rev_le_rev.2 hij))
  rw [la_extO (P.ι v) (P.σ v) (P.j v)
    (fun x => by obtain ⟨y, hy⟩ := (P.setting v).frob x; exact ⟨_, hy⟩) (P.setting v).ι_comp s.val g]
  have hg' := la_tw_det (P.ι v) (P.σ v) s.val g hg
  refine le_antisymm (lowest_invariant_le_delta _ _ hd _ hg') ?_
  unfold Dl0
  rw [if_pos hd]
  refine le_iInf₂ fun h hh => ?_
  exact dl_indep O Kf hinj _ _ _ h hg' hh.2

variable (g : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (hg : ∀ v, IsUnit (g v).det)


include hg in
theorem htupW_le (hinj : Function.Injective (algebraMap O Kf)) (T : Submodule O P.Xsp)
    (hT : ∀ F : GlobalTheory P → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf,
      (∀ b, F b ∈ deltaL O Kf (P.m + 1) (nuB P b) (gam P g b)) → sB P g • ∏ b, rename (emP P b) (F b) ∈ T) :
    P.HtupW (fun v => colSpan (P.W v) (g v)) ≤ T := by
  have key : ∀ S : Fin P.nV → Set P.Xsp,
      (∀ f : Fin P.nV → P.Xsp, (∀ v, f v ∈ S v) → ∏ v, f v ∈ T) →
      ∀ f : Fin P.nV → P.Xsp, (∀ v, f v ∈ Submodule.span O (S v)) → ∏ v, f v ∈ T := by
    intro S h f hf
    classical
    suffices H : ∀ A : Finset (Fin P.nV), ∀ f : Fin P.nV → P.Xsp,
        (∀ i ∈ A, f i ∈ Submodule.span O (S i)) → (∀ i ∉ A, f i ∈ S i) → ∏ i, f i ∈ T from
      H Finset.univ f (fun i _ => hf i) (fun i hi => absurd (Finset.mem_univ i) hi)
    intro A
    refine Finset.induction_on A ?_ ?_
    · intro f _ h2
      exact h f (fun i => h2 i (by simp))
    · intro a A ha ih f h1 h2
      have hR : ∀ x ∈ Submodule.span O (S a), x * ∏ j ∈ Finset.univ \ {a}, f j ∈ T := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          have h3 := ih (Function.update f a y) (fun i hi => ?_) (fun i hi => ?_)
          · rwa [Finset.prod_update_of_mem (Finset.mem_univ a)] at h3
          · have hia : i ≠ a := by rintro rfl; exact ha hi
            simp only [Function.update_apply, hia, if_false]
            exact h1 i (Finset.mem_insert_of_mem hi)
          · by_cases hia : i = a
            · subst hia
              simp only [Function.update_apply, if_true]
              exact hy
            · simp only [Function.update_apply, hia, if_false]
              exact h2 i (by simp [hia, hi])
        | zero => rw [zero_mul]; exact T.zero_mem
        | add x y _ _ hx hy => rw [add_mul]; exact T.add_mem hx hy
        | smul c x _ hx => rw [smul_mul_assoc]; exact T.smul_mem c hx
      have h4 := Finset.prod_update_of_mem (Finset.mem_univ a) f (f a)
      rw [Function.update_eq_self] at h4
      rw [h4]
      exact hR _ (h1 a (Finset.mem_insert_self a A))
  unfold Places.HtupW Places.tenV
  rw [Submodule.span_le]
  rintro X ⟨F, hF, rfl⟩
  have hF' : ∀ v, P.vEmb v (F v) ∈ Submodule.span O
      (((P.vEmb v).toLinearMap.restrictScalars O) '' {Q | ∃ G : Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf,
        (∀ s, G s ∈ deltaLTw O Kf P.m (lamAt (P.lam0 v) s) (la_tw (P.ι v) (P.σ v) s.val (g v))) ∧
          Q = ∏ s, blockEmb Kf s (G s)}) := by
    intro v
    rw [Submodule.span_image]
    refine Submodule.mem_map_of_mem ?_
    have h := hF v
    unfold HtenW tensorLat at h
    simp only [delta_zero_eq_twisted_delta P hinj v _ (g v) (hg v)] at h
    exact h
  refine key _ ?_ (fun v => P.vEmb v (F v)) hF'
  intro f hf
  choose Q hQ hfQ using hf
  choose G hG hQG using hQ
  have hG' : ∀ v s, ∃ H, H ∈ deltaL O Kf (P.m + 1) (nuB P ⟨v, s⟩) (gam P g ⟨v, s⟩) ∧
      (gam P g ⟨v, s⟩).det ^ (-(eB P ⟨v, s⟩)) • H = G v s := fun v s => Submodule.mem_map.1 (hG v s)
  choose H hH hHG using hG'
  have e : ∏ v, f v = sB P g • ∏ b : GlobalTheory P, rename (emP P b) (H b.1 b.2) := by
    rw [show sB P g • ∏ b : GlobalTheory P, rename (emP P b) (H b.1 b.2) = _ from
      (prod_blocks P (fun b => (gam P g b).det ^ (-(eB P b))) (fun b => H b.1 b.2)).symm]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← hfQ v, hQG v]
    show P.vEmb v _ = _
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [← hHG v s]
  rw [e]
  exact hT (fun b => H b.1 b.2) (fun b => hH b.1 b.2)


include hg in
theorem mem_htupW (hinj : Function.Injective (algebraMap O Kf)) (F : GlobalTheory P → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf)
    (hF : ∀ b, F b ∈ deltaL O Kf (P.m + 1) (nuB P b) (gam P g b)) :
    sB P g • ∏ b, rename (emP P b) (F b) ∈ P.HtupW (fun v => colSpan (P.W v) (g v)) := by
  rw [show sB P g • ∏ b, rename (emP P b) (F b) = _ from
    (prod_blocks P (fun b => (gam P g b).det ^ (-(eB P b))) F).symm]
  unfold Places.HtupW Places.tenV
  apply Submodule.subset_span
  refine ⟨fun v => ∏ s, blockEmb Kf s ((gam P g ⟨v, s⟩).det ^ (-(eB P ⟨v, s⟩)) • F ⟨v, s⟩), fun v => ?_, rfl⟩
  unfold HtenW tensorLat
  apply Submodule.subset_span
  refine ⟨fun s => (gam P g ⟨v, s⟩).det ^ (-(eB P ⟨v, s⟩)) • F ⟨v, s⟩, fun s => ?_, rfl⟩
  show _ ∈ Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val (colSpan (P.W v) (g v)))
  rw [delta_zero_eq_twisted_delta P hinj v s (g v) (hg v)]
  exact Submodule.mem_map.2 ⟨F ⟨v, s⟩, hF ⟨v, s⟩, rfl⟩

end Formalism.L2.PairingIndexBounds.Ent
end
end

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.GeXZero
noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

variable {Kc : Type} [Field Kc] (p : ℕ) (Oc : Subring Kc)

def geX (x : Kc) (g : ℝ) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → (a : ℝ) ≤ g * b → x ^ b * (p : Kc) ^ (-a) ∈ Oc

variable {p Oc}

theorem geX_mul {u x : Kc} {g : ℝ} (hu : u ∈ Oc) (hx : geX p Oc x g) : geX p Oc (u * x) g := by
  intro a b hb hab
  rw [mul_pow, mul_assoc]
  exact Oc.mul_mem (Oc.pow_mem hu b) (hx a b hb hab)

theorem geX_zero (g : ℝ) : geX p Oc (0 : Kc) g := by
  intro a b hb _
  rw [zero_pow hb.ne', zero_mul]
  exact Oc.zero_mem

theorem geX_neg {x : Kc} {g : ℝ} (hx : geX p Oc x g) : geX p Oc (-x) g := by
  have h := geX_mul (Oc.neg_mem Oc.one_mem) hx
  simpa using h

theorem geX_add (hval : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc) {x y : Kc} {g : ℝ} (hx : geX p Oc x g) (hy : geX p Oc y g) :
    geX p Oc (x + y) g := by
  intro a b hb hab
  rcases eq_or_ne y 0 with rfl | hy0
  · simpa using hx a b hb hab
  rcases eq_or_ne x 0 with rfl | hx0
  · simpa using hy a b hb hab
  rcases hval (x / y) with h | h
  · have e : (x + y) ^ b * (p : Kc) ^ (-a) = (1 + x / y) ^ b * (y ^ b * (p : Kc) ^ (-a)) := by
      rw [← mul_assoc, ← mul_pow, add_mul, one_mul, div_mul_cancel₀ x hy0, add_comm y x]
    rw [e]
    exact Oc.mul_mem (Oc.pow_mem (Oc.add_mem Oc.one_mem h) b) (hy a b hb hab)
  · rw [inv_div] at h
    have e : (x + y) ^ b * (p : Kc) ^ (-a) = (1 + y / x) ^ b * (x ^ b * (p : Kc) ^ (-a)) := by
      rw [← mul_assoc, ← mul_pow, add_mul, one_mul, div_mul_cancel₀ y hx0]
    rw [e]
    exact Oc.mul_mem (Oc.pow_mem (Oc.add_mem Oc.one_mem h) b) (hx a b hb hab)


variable (p Oc) in
def MG (hval : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc) (g : ℝ) : AddSubgroup Kc where
  carrier := {x | geX p Oc x g}
  add_mem' := fun hx hy => geX_add hval hx hy
  zero_mem' := geX_zero g
  neg_mem' := fun hx => geX_neg hx

end Formalism.L2.PairingIndexBounds.Ent
end
end

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.XFacts
section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.SzTLe
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

abbrev BX : Type := Σ v : X.Pl, Fin (X.G.P.n' v)

abbrev NJ (j : ℕ) : ℕ := NN X.G.P.m X.t j

def emX (j : ℕ) (b : BX X) (v : Fin (NJ X j) × Fin (NJ X j)) :
    (Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :=
  idxI X j ⟨b.1, (b.2, v)⟩

def xmX (j : ℕ) (b : BX X) (s : ℕ × Fin (NJ X j)) : X.FrI j := ⟨b.1, (b.2, s.1, s.2)⟩

def mF (j : ℕ) (b : BX X) (A : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)) :
    Matrix (Fin (NJ X j)) (Fin (NJ X j)) X.G.Kf :=
  (A.map fun x => X.G.P.ι b.1 ((X.G.P.σ b.1 ^ b.2.val) x)).submatrix (finCongr (rank_eq X j).symm) (finCongr (rank_eq X j).symm)

def nuM : (j : ℕ) → BX X → Fin (NJ X j) → ℕ
  | 0, b, t => nuOf (lamAt (X.G.P.lam0 b.1) b.2) (Fin.cast (rankJ X 0).symm t)
  | j + 1, b, t => nuOf (lamAt ((X.Fl.Pj (j + 1)).lam0 b.1) b.2) (Fin.cast (rankJ X (j + 1)).symm t)

def sX (j : ℕ) (g : ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) : X.G.Kf :=
  ∏ b : BX X, (mF X j b (g b.1)).det ^ (-(eJ X j b.1 b.2))

def muX (j n : ℕ) (b : BX X) : Fin n → ℕ := fun t => (X.nuv b.1 (j + 1) b.2 (t.val + 1)).toNat

def cX (j : ℕ) (b : BX X) : ℕ := (X.nuv b.1 (j + 1) b.2 1).toNat

def eX (j : ℕ) (b : BX X) : ℕ := (X.nuv b.1 (j + 1) b.2 (NJ X j)).toNat

def nuS (j : ℕ) (b : BX X) : Fin (NJ X j) → ℕ :=
  if IsOddPos b.2 then fun t => cX X j b - muX X j (NJ X j) b t.rev else fun t => muX X j (NJ X j) b t - eX X j b

def nuT (j : ℕ) (b : BX X) : Fin (NJ X (j + 1)) → ℕ :=
  if IsOddPos b.2 then fun t => cX X j b - muX X j (NJ X (j + 1)) b t.rev else muX X j (NJ X (j + 1)) b

def HgX (R : Type) [CommRing R] (j : ℕ) (b : BX X) : GenR R (NJ X j) :=
  if IsOddPos b.2 then hvO (gX R (NJ X j)) (gY R (NJ X j)) (cX X j b) (fun k => colH (muX X j (NJ X j) b) k.val)
  else (Matrix.of fun a i : Fin (NJ X j) => gX R (NJ X j) a i.val).det ^ (eX X j b) *
    hvE (gX R (NJ X j)) (gY R (NJ X j)) (cX X j b) (fun k => colH (nuS X j b) k.val) (fun k => colH_le _ k.val)

def szT (j : ℕ) (b : BX X) (k : Fin (cX X j b)) : ℕ :=
  if IsOddPos b.2 then NJ X (j + 1) - colH (muX X j (NJ X (j + 1)) b) k.val else colH (muX X j (NJ X (j + 1)) b) k.val

theorem szT_le (j : ℕ) (b : BX X) (k : Fin (cX X j b)) : szT X j b k ≤ NJ X (j + 1) := by
  unfold szT
  split_ifs
  · exact Nat.sub_le _ _
  · exact colH_le _ _

end Formalism.L2.PairingIndexBounds.Ent
end
end

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Defs

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def srcN (j : ℕ) (b : BX X) (x : Fin (NJ X j) → ℕ → X.G.Kf) : MvPolynomial (Fin (NJ X j) × Fin (NJ X j)) X.G.Kf :=
  if IsOddPos b.2 then hvO (fun a i => C (x a i)) (yV X.G.Kf (NJ X j)) (cX X j b) (fun k => colH (muX X j (NJ X j) b) k.val)
  else C ((Matrix.of fun a i : Fin (NJ X j) => x a i.val).det ^ (eX X j b)) *
    hvE (fun a i => C (x a i)) (yV X.G.Kf (NJ X j)) (cX X j b) (fun k => colH (nuS X j b) k.val) (fun k => colH_le _ k.val)

def tgtN (K' : Type) [CommRing K'] (j : ℕ) (b : BX X) (z : Fin (NJ X (j + 1)) → ℕ → K') :
    MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) K' :=
  if IsOddPos b.2 then
    hvO (fun a i => C (z a i)) (yV K' (NJ X (j + 1))) (cX X j b) (fun k => colH (muX X j (NJ X (j + 1)) b) k.val)
  else hvE (fun a i => C (z a i)) (yV K' (NJ X (j + 1))) (cX X j b) (fun k => colH (muX X j (NJ X (j + 1)) b) k.val)
    (fun k => colH_le _ k.val)

variable (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]

def tgtD (j : ℕ) (b : BX X) (x : Fin (NJ X j) → ℕ → X.G.Kf) : DA X Kc j :=
  if IsOddPos b.2 then
    hvO (xd X Kc j b.1 b.2 x) (yMat X Kc j b.1 b.2) (cX X j b) (fun k => colH (muX X j (NJ X (j + 1)) b) k.val)
  else hvE (xd X Kc j b.1 b.2 x) (yMat X Kc j b.1 b.2) (cX X j b) (fun k => colH (muX X j (NJ X (j + 1)) b) k.val)
    (fun k => colH_le _ k.val)

def evD (j : ℕ) (d0 : X.ZA j → Kc) : DA X Kc j →+* XspC (X.Pj (j + 1)) Kc :=
  eval₂Hom (RingHom.id _) fun z => C (d0 z)

def dM (j : ℕ) (b : BX X) (d0 : X.ZA j → Kc) : Matrix (Fin (NJ X j)) (Fin (NJ X (j + 1))) Kc :=
  fun a b' => d0 ⟨b.1, (b.2, a, b')⟩

end Defs

def XShape : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (j : ℕ) (b : BX X),
    nuM X j b = nuS X j b ∧ nuM X (j + 1) b = nuT X j b ∧
    (∀ n, Antitone (muX X j n b)) ∧ (∀ n t, muX X j n b t ≤ cX X j b) ∧
    (∀ k, colH (muX X j (NJ X j) b) k = X.colHt b.1 (j + 1) b.2 k) ∧
    (∀ k, colH (muX X j (NJ X (j + 1)) b) k = X.colHt b.1 (j + 1) b.2 k) ∧
    (∀ t, eX X j b ≤ muX X j (NJ X j) b t) ∧ (∀ t : Fin (NJ X j), t.val + 1 = NJ X j → muX X j (NJ X j) b t = eX X j b) ∧
    (¬ IsOddPos b.2 → (eX X j b : ℤ) = eJ X j b.1 b.2 + X.w b.1 (j + 1) b.2 ∧ eJ X (j + 1) b.1 b.2 = -X.w b.1 (j + 1) b.2) ∧
    (IsOddPos b.2 → (cX X j b : ℤ) = X.w b.1 (j + 1) b.2 - eJ X j b.1 b.2 ∧ eJ X (j + 1) b.1 b.2 = eJ X j b.1 b.2)

def XBrS : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p), Function.Injective (algebraMap X.G.O X.G.Kf) →
    ∀ (j : ℕ) (L : (X.Pj j).Tup) (g : ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)),
      (∀ v, IsUnit (g v).det) → (∀ v, X.latAt v j L = colSpan (X.G.P.W v) (g v)) →
      ∀ T : Submodule X.G.O (X.Pj j).Xsp,
        (∀ F : BX X → MvPolynomial (Fin (NJ X j) × Fin (NJ X j)) X.G.Kf,
          (∀ b, F b ∈ deltaL X.G.O X.G.Kf (NJ X j) (nuM X j b) (mF X j b (g b.1))) →
            sX X j g • ∏ b, rename (emX X j b) (F b) ∈ T) → (X.Pj j).HtupW L ≤ T

def XBrT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p), Function.Injective (algebraMap X.G.O X.G.Kf) →
    ∀ (j : ℕ) (L : (X.Pj j).Tup) (g : ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)),
      (∀ v, IsUnit (g v).det) → (∀ v, X.latAt v j L = colSpan (X.G.P.W v) (g v)) →
      ∀ F : BX X → MvPolynomial (Fin (NJ X j) × Fin (NJ X j)) X.G.Kf,
        (∀ b, F b ∈ deltaL X.G.O X.G.Kf (NJ X j) (nuM X j b) (mF X j b (g b.1))) →
          sX X j g • ∏ b, rename (emX X j b) (F b) ∈ (X.Pj j).HtupW L

def XInj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (j : ℕ),
    (Function.Injective fun x : BX X × (Fin (NJ X j) × Fin (NJ X j)) => emX X j x.1 x.2) ∧
    (Function.Injective fun x : BX X × (ℕ × Fin (NJ X j)) => xmX X j x.1 x.2)

def XA : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)
    (x : ∀ b : BX X, Fin (NJ X j) → ℕ → X.G.Kf),
    polDel X Kc j (∏ b, rename (emX X j b) (srcN X j b (x b))) = ∏ b, tgtD X Kc j b (x b)

def XB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] [Infinite Kc] (j : ℕ)
    (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La') (P : DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc)
    (l : XspC (X.Pj (j + 1)) Kc →ₗ[Kc] Kc) (R : MvPolynomial (X.ZA j) Kc),
    (∀ d0 : X.ZA j → Kc, eval d0 R = l (evD X Kc j (fun y => ∑ z, bc Kc φ z y * d0 z) P)) →
      l (pairD X Kc j P (linSub (bc Kc φ) f)) = ∑ n ∈ R.support, derAt X Kc j n f * AddMonoidAlgebra.coeff R n

def TransposedFrameImageBlockwise : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (j : ℕ)
    (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La') (d0 : X.ZA j → Kc) (b : BX X),
    dM X Kc j b (fun y => ∑ z, bc Kc φ z y * d0 z) = (Pf Kc φ b.1 b.2).transpose * dM X Kc j b d0 * Qf Kc φ b.1 b.2

def XC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (b : BX X)
    (x : Fin (NJ X j) → ℕ → X.G.Kf) (d0 : X.ZA j → Kc),
    evD X Kc j d0 (tgtD X Kc j b x) =
      rename (emX X (j + 1) b) (tgtN X Kc j b (mulC (dM X Kc j b d0).transpose fun a i => algebraMap X.G.Kf Kc (x a i)))

def XG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ)
    (f : MvPowerSeries (X.ZA j) Kc) (x : X.FrI j → Kc),
    ∑ n ∈ (map (eval₂Hom (Int.castRingHom Kc) x) (X.PI j I i0)).support,
        derAt X Kc j n f * AddMonoidAlgebra.coeff (map (eval₂Hom (Int.castRingHom Kc) x) (X.PI j I i0)) n =
      eval x (applyD (X.PI j I i0) f)

end Formalism.L2.PairingIndexBounds.Ent
end
end

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Defs

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def DgX (K' : Type) [Field K'] (j : ℕ) (i0 : X.Pl → ℕ) (v : X.Pl) : Matrix (Fin (NJ X (j + 1))) (Fin (NJ X (j + 1))) K' :=
  Matrix.diagonal fun a => if a.val < i0 v then (p : K')⁻¹ else 1

variable (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]

def numericalIdentityScalar (j : ℕ) (g : ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (g' : ∀ v : X.Pl, Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)) (i0 : X.Pl → ℕ) : Kc :=
  ∏ b : BX X, if IsOddPos b.2 then
      (algebraMap X.G.Kf Kc (mF X j b (g b.1)).det) ^ (-(cX X j b : ℤ)) *
        (algebraMap X.G.Kf Kc (mF X (j + 1) b (g' b.1) * DgX X X.G.Kf j i0 b.1).det) ^ (cX X j b)
    else (algebraMap X.G.Kf Kc (mF X j b (g b.1)).det) ^ (eX X j b) *
      (p : Kc) ^ (-((∑ k : Fin (cX X j b), min (X.colHt b.1 (j + 1) b.2 k.val) (i0 b.1) : ℕ) : ℤ))

end Defs

def PairingSeriesLinearForm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] [Infinite Kc] (j : ℕ)
    (P : DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc) (l : XspC (X.Pj (j + 1)) Kc →ₗ[Kc] Kc) (R : MvPolynomial (X.ZA j) Kc),
    (∀ d0 : X.ZA j → Kc, eval d0 R = l (evD X Kc j d0 P)) →
      l (pairD X Kc j P f) = ∑ n ∈ R.support, derAt X Kc j n f * AddMonoidAlgebra.coeff R n

def XMid : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] [CharZero Kc] (j : ℕ)
    (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La') (i0 : X.Pl → ℕ)
    (I : ∀ (b : BX X) (k : Fin (cX X j b)), Fin (szT X j b k) → Fin (NJ X (j + 1))), (∀ b k, Function.Injective (I b k)) →
    ∃ (Ist : X.ColCh j) (ε : Kc), (ε = 1 ∨ ε = -1) ∧
      ∀ (f : MvPowerSeries (X.ZA j) Kc) (x : X.FrI j → X.G.Kf),
        fockR (delF X Kc j (∏ b, rename (emX X j b) (rowAct X.G.Kf (mF X j b ((φ.g b.1)⁻¹ : GL _ _))
            (evX (fun s => x (xmX X j b s)) (HgX X X.G.Kf j b)))) (linSub (bc Kc φ) f))
          (map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b)
            (rowAct X.G.Kf (mF X (j + 1) b (φ.g' b.1).val * DgX X X.G.Kf j i0 b.1).transpose
              (bideterminant X.G.Kf (szT X j b) (szT_le X j b) (I b))))) =
        ε * numericalIdentityScalar X Kc j (fun v => φ.g v) (fun v => φ.g' v) i0 * (∏ b, cN Kc (nuT X j b)) *
          eval (fun t => algebraMap X.G.Kf Kc (x t)) (applyD (X.PI j Ist i0) f)

def XSpanN : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] [CharZero Kc] (j : ℕ)
    (x : ∀ b : BX X, Fin (NJ X j) → ℕ → X.G.Kf) (f : MvPowerSeries (X.ZA j) Kc),
    delF X Kc j (∏ b, rename (emX X j b) (srcN X j b (x b))) f ∈
      Submodule.span Kc {z | ∃ F : BX X → MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) X.G.Kf,
        (∀ b, F b ∈ dualWeyl X.G.Kf (NJ X (j + 1)) (NJ X (j + 1)) (nuT X j b)) ∧
          z = map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b) (F b))}

def XUnit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (Oc : Subring Kc),
    (∀ o : X.G.O, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) ∈ Oc) → (p : Kc) ≠ 0 →
    ∀ (j : ℕ) (L : (X.Pj j).Tup) (L'' : (X.Pj (j + 1)).Tup)
      (g : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (g' : ∀ v : X.Pl, GL (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)),
      (∀ v, X.latAt v j L = colSpan (X.G.P.W v) (g v : Matrix _ _ (X.G.P.Qq v))) →
      (∀ v, X.latAt v (j + 1) L'' = colSpan (X.G.P.W v) (g' v : Matrix _ _ (X.G.P.Qq v))) →
      ∀ i0 : X.Pl → ℕ, (∀ v, i0 v ≤ X.G.P.r) →
        algebraMap X.G.Kf Kc ((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) *
            ((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j L)) *
              (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) L''))⁻¹) *
            sX X j (fun v => g v) *
            (∏ b : BX X, (mF X (j + 1) b (g' b.1).val * DgX X X.G.Kf j i0 b.1).det ^ (-(eJ X (j + 1) b.1 b.2)))⁻¹) *
          numericalIdentityScalar X Kc j (fun v => g v) (fun v => g' v) i0 ∈ Oc

def XEdge : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (j : ℕ) (L' L'' : (X.Pj (j + 1)).Tup) (i0 : X.Pl → ℕ),
    (X.Pj (j + 1)).IsLatTup L' →
    (∀ v' : Fin (X.Pj (j + 1)).nV, (i0 (X.vB (j + 1) v') = 0 ∧ L'' v' = L' v') ∨
      (1 ≤ i0 (X.vB (j + 1) v') ∧ IsEdge p ((X.Pj (j + 1)).n' v') (i0 (X.vB (j + 1) v')) ⟨L'' v', L' v'⟩)) →
    ∃ g' h' : ∀ v : X.Pl, GL (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v),
      (∀ v, X.latAt v (j + 1) L'' = colSpan (X.G.P.W v) (g' v : Matrix _ _ (X.G.P.Qq v))) ∧
      (∀ v, X.latAt v (j + 1) L' = colSpan (X.G.P.W v) (h' v : Matrix _ _ (X.G.P.Qq v))) ∧
      ∀ b : BX X, mF X (j + 1) b (h' b.1).val = mF X (j + 1) b (g' b.1).val * DgX X X.G.Kf j i0 b.1

end Formalism.L2.PairingIndexBounds.Ent
