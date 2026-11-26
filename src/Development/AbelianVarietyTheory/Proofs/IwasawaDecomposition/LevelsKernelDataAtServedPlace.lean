module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ServedPlaceLevelsClassesComparisonMaps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesServedPlaceEqLocalOrbitPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesServedPlaceEqLocalOrbitPairs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.KerOne

theorem stepZeroClasses_servedPlace_eq_localOrbitPairs_alt : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ cls0 : ((w.D Z).gat u v hg).comp → ((w.D Z).gat u v hg).P.Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls 0,
        (∀ (a a' : ((w.D Z).gat u v hg).comp) (L L' : ((w.D Z).gat u v hg).P.Tup), ((w.D Z).gat u v hg).P.IsLatTup L →
          ((w.D Z).gat u v hg).P.IsLatTup L' →
          (cls0 a L = cls0 a' L' ↔ a = a' ∧ ∃ γ : (((w.D Z).gat u v hg).lev a).Γ, L' = (((w.D Z).gat u v hg).lev a).smul γ L)) ∧
        ∀ x, ∃ a L, ((w.D Z).gat u v hg).P.IsLatTup L ∧ cls0 a L = x := by
  intro K B f T w _ _ _ Z t Wt nch _ Y _ _ O _ _ E _ u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  have e : ((w.D Z).mem u).C.cls 0 ≃ ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls 0 := TC.eCls0 w.I w.l u ((w.D Z).what₂.muAt v)
  obtain ⟨W, Qq, O', Kf, _, _, _, _, _, _, _, _, _, _, n', ι, σ, j, w0, hS, nV, r, m, lam0, dom, hk, I, ψ, e', hH, heq⟩ :=
    t.g.gat u v hg
  obtain ⟨c⟩ := Formalism.L2.G.TwTie0.class_local_of_eq (w.D Z) t.g.herm.lev0 u e hS nV r m lam0 dom hk I ψ e' hH ((w.D Z).gat u v hg) heq
  exact ⟨c.cls, c.cls_iff, c.cls_surj⟩

end GlobalTheory.Mem.Top.KerOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesServedPlaceEqLocalOrbitPairsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroClasses_servedPlace_eq_localOrbitPairs : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ cls0 : ((w.D Z).gat u v hg).comp → ((w.D Z).gat u v hg).P.Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls 0,
        (∀ (a a' : ((w.D Z).gat u v hg).comp) (L L' : ((w.D Z).gat u v hg).P.Tup), ((w.D Z).gat u v hg).P.IsLatTup L →
          ((w.D Z).gat u v hg).P.IsLatTup L' →
          (cls0 a L = cls0 a' L' ↔ a = a' ∧ ∃ γ : (((w.D Z).gat u v hg).lev a).Γ, L' = (((w.D Z).gat u v hg).lev a).smul γ L)) ∧
        ∀ x, ∃ a L, ((w.D Z).gat u v hg).P.IsLatTup L ∧ cls0 a L = x := by
  first | exact @GlobalTheory.Mem.Top.KerOne.stepZeroClasses_servedPlace_eq_localOrbitPairs_alt | exact GlobalTheory.Mem.Top.KerOne.stepZeroClasses_servedPlace_eq_localOrbitPairs_alt | (intros; apply GlobalTheory.Mem.Top.KerOne.stepZeroClasses_servedPlace_eq_localOrbitPairs_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEmbeddingAtOrbitPositionEqInduced
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEmbeddingAtOrbitPositionEqInduced
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.KerOne

theorem splitPlace_embedding_at_orbitPosition_eq_induced : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (q : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' q)) (x : (w.D Z).host.E),
        ((w.D Z).gat u v hg).P.ι q ((((w.D Z).gat u v hg).P.σ q ^ s.val) (GlobalTheory.Mem.Top.KerOne.iw0 t.full.1.g u v hg q x)) =
          t.cmp.embW u v hg (tauLL (w.D Z) (t.Gt.gat_pos u v hg ⟨q, s⟩) (if s.val % 2 = 1 then (w.D Z).host.conj x else x)) := by
  intro K B f T w _ _ _ Z t _ _ _ _ _ _ _ _ _ _ _ u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  intro q s x
  have h := (t.g.cmp.tie u v hg).pos_emb q s x
  have key : ∀ (X : Formalism.L2.Herm.Herm0 (w.D Z)) (Bm : GL (Fin (w.D Z).R.k) (w.D Z).host.E), X = t.full.1.to0 →
      (Formalism.L2.G.Cmp.locAt X u v hg Bm).iw q x = iw0 t.full.1.g u v hg q x := by
    rintro X Bm rfl; rfl
  rw [key _ _ t.herm_eq] at h
  rw [← h]
  have h3 : Formalism.L2.Forms.sigD (w.D Z) x = (w.D Z).host.conj x := Formalism.BasicNotions.bridge_star_holds (w.D Z).R (w.D Z).host x
  rw [h3]
  show _ = (t.cmp.embW u v hg) (Formalism.L2.G.Cmp.tEL (w.D Z) _ _)
  congr 2
  by_cases hs : s.val % 2 = 1
  · have : ¬ Even s.val := by rw [Nat.not_even_iff_odd, Nat.odd_iff]; exact hs
    simp [hs, this]
  · have : Even s.val := by rw [Nat.even_iff]; omega
    simp [hs, this]

end GlobalTheory.Mem.Top.KerOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEmbeddingAtOrbitPositionEqInducedStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_embedding_at_orbitPosition_eq_induced_alt : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (q : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' q)) (x : (w.D Z).host.E),
        ((w.D Z).gat u v hg).P.ι q ((((w.D Z).gat u v hg).P.σ q ^ s.val) (GlobalTheory.Mem.Top.KerOne.iw0 t.full.1.g u v hg q x)) =
          t.cmp.embW u v hg (tauLL (w.D Z) (t.Gt.gat_pos u v hg ⟨q, s⟩) (if s.val % 2 = 1 then (w.D Z).host.conj x else x)) := by
  first | exact @GlobalTheory.Mem.Top.KerOne.splitPlace_embedding_at_orbitPosition_eq_induced | exact GlobalTheory.Mem.Top.KerOne.splitPlace_embedding_at_orbitPosition_eq_induced | (intros; apply GlobalTheory.Mem.Top.KerOne.splitPlace_embedding_at_orbitPosition_eq_induced <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalModuleLocalisingToLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalMatrixApproximationModIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalMatrixApproximationModIntegral
noncomputable section

namespace GlobalTheory.GlobApx

open Formalism.MainNotions.G

theorem mulVec_mem_colSpan {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (w : Fin k → R) :
    g.mulVec (fun j => algebraMap R K (w j)) ∈ colSpan R g := by
  have : g.mulVec (fun j => algebraMap R K (w j)) = ∑ j, w j • fun i => g i j := by
    funext i
    simp [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_pow_smul_ge {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π) {k : ℕ} (g : Matrix (Fin k) (Fin k) K) :
    ∃ a : ℕ, ∀ N, a ≤ N → ∃ g0 : Matrix (Fin k) (Fin k) R,
      algebraMap R K π ^ N • g = g0.map (algebraMap R K) := by
  obtain ⟨a, g0, h⟩ := GlobalTheory.GO.TupApx.exists_pow_smul (K := K) hπ g
  refine ⟨a, fun N hN => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨π ^ d • g0, ?_⟩
  rw [pow_add, mul_comm, mul_smul, h]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow]

theorem exists_glob_approx : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (W Q : ι → Type) [∀ q, CommRing (W q)] [∀ q, IsDomain (W q)] [∀ q, IsDiscreteValuationRing (W q)] [∀ q, Field (Q q)] [∀ q, Algebra (W q) (Q q)] [∀ q, IsFractionRing (W q) (Q q)] {F : Type} [Field F] (f : ∀ q, F →+* Q q) (π : ∀ q, W q), (∀ q, Irreducible (π q)) → ∀ (t : F), (∀ q, f q t = algebraMap (W q) (Q q) (π q)) → (∀ (y : ∀ q, W q) (N : ℕ), ∃ x : F, ∀ q, ∃ z : W q, f q x = algebraMap (W q) (Q q) (y q + π q ^ N * z)) → ∀ {n : ℕ} (g : ∀ q, Matrix (Fin n) (Fin n) (Q q)), (∀ q, IsUnit (g q).det) → ∀ (q0 : ι), ∃ (B : Matrix (Fin n) (Fin n) F) (u : Matrix (Fin n) (Fin n) (W q0)), IsUnit u.det ∧ B.map (f q0) = g q0 * u.map (algebraMap (W q0) (Q q0)) ∧ ∀ q, q ≠ q0 → ∀ c, (fun i => f q (B i c)) ∈ Formalism.MainNotions.G.colSpan (W q) (g q) := by
  intro ι _ _ W Q _ _ _ _ _ _ F _ f π hπ t ht hd n g hg q0
  have hp0 : ∀ q, algebraMap (W q) (Q q) (π q) ≠ 0 := fun q =>
    (map_ne_zero_iff _ (IsFractionRing.injective (W q) (Q q))).2 (hπ q).ne_zero
  choose a ha using fun q => exists_pow_smul_ge (hπ q) (g q)
  choose b hb using fun q => exists_pow_smul_ge (hπ q) (g q)⁻¹
  set M := Finset.univ.sup (fun q => a q + b q) with hMdef
  have hM : ∀ q, a q ≤ M ∧ b q ≤ M := fun q => by
    have := Finset.le_sup (f := fun q => a q + b q) (Finset.mem_univ q)
    constructor <;> omega
  choose G hG using fun q => ha q M (hM q).1
  choose H hH using fun q => hb q M (hM q).2
  choose x hx using fun i j => hd (Pi.single (M := W) q0 (G q0 i j)) (2 * M + 1)
  choose z hz using hx
  have hB : ∀ q i j, f q ((t ^ M)⁻¹ * x i j) = (algebraMap (W q) (Q q) (π q) ^ M)⁻¹ *
      (algebraMap (W q) (Q q) (Pi.single (M := W) q0 (G q0 i j) q) +
        algebraMap (W q) (Q q) (π q) ^ (2 * M + 1) * algebraMap (W q) (Q q) (z i j q)) := by
    intro q i j
    rw [map_mul, map_inv₀, map_pow, ht, hz, map_add (f := _), map_mul, map_pow]
  refine ⟨Matrix.of fun i j => (t ^ M)⁻¹ * x i j, 1 + π q0 • (H q0 * Matrix.of fun i j => z i j q0), ?_, ?_, ?_⟩
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have hr : IsLocalRing.residue (W q0) (π q0) = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff]; exact (hπ q0).not_isUnit
    have : (IsLocalRing.residue (W q0)).mapMatrix (1 + π q0 • (H q0 * Matrix.of fun i j => z i j q0)) = 1 := by
      rw [map_add (f := _), map_one]
      have : (IsLocalRing.residue (W q0)).mapMatrix (π q0 • (H q0 * Matrix.of fun i j => z i j q0)) = 0 := by
        ext i j; simp [hr]
      rw [this, add_zero]
    rw [this]; simp
  · have e1 : (1 + π q0 • (H q0 * Matrix.of fun i j => z i j q0)).map (algebraMap (W q0) (Q q0)) =
        1 + algebraMap (W q0) (Q q0) (π q0) • ((H q0).map (algebraMap (W q0) (Q q0)) *
          (Matrix.of fun i j => z i j q0).map (algebraMap (W q0) (Q q0))) := by
      rw [← Matrix.map_mul]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
        Matrix.one_apply, apply_ite (algebraMap (W q0) (Q q0)), map_one, map_zero]
    rw [e1, ← hH q0, mul_add, mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (hg q0), Matrix.one_mul]
    ext i j
    have h2 := congrFun (congrFun (hG q0) i) j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h2
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hB, Pi.single_eq_same, ← h2]
    have := hp0 q0
    field_simp
    ring
  · intro q hq c
    set zc : Fin n → W q := fun i => z i c q
    have hv : (fun i => f q ((Matrix.of fun i j => (t ^ M)⁻¹ * x i j) i c)) =
        (g q).mulVec (fun j => algebraMap (W q) (Q q) ((π q • (H q).mulVec zc) j)) := by
      have e2 : (fun j => algebraMap (W q) (Q q) ((π q • (H q).mulVec zc) j)) =
          algebraMap (W q) (Q q) (π q) • ((H q).map (algebraMap (W q) (Q q))).mulVec
            (fun j => algebraMap (W q) (Q q) (zc j)) := by
        funext j
        set_option synthInstance.maxHeartbeats 100000 in
          simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [e2, ← hH q, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (hg q), Matrix.one_mulVec]
      funext i
      simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      rw [hB, Pi.single_eq_of_ne hq, map_zero, zero_add]
      have := hp0 q
      field_simp
      ring
    rw [hv]
    exact mulVec_mem_colSpan _ _

end GlobalTheory.GlobApx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalMatrixApproximationModIntegralStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_matrix_approximation_mod_integral : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (W Q : ι → Type) [∀ q, CommRing (W q)] [∀ q, IsDomain (W q)] [∀ q, IsDiscreteValuationRing (W q)] [∀ q, Field (Q q)] [∀ q, Algebra (W q) (Q q)] [∀ q, IsFractionRing (W q) (Q q)] {F : Type} [Field F] (f : ∀ q, F →+* Q q) (π : ∀ q, W q), (∀ q, Irreducible (π q)) → ∀ (t : F), (∀ q, f q t = algebraMap (W q) (Q q) (π q)) → (∀ (y : ∀ q, W q) (N : ℕ), ∃ x : F, ∀ q, ∃ z : W q, f q x = algebraMap (W q) (Q q) (y q + π q ^ N * z)) → ∀ {n : ℕ} (g : ∀ q, Matrix (Fin n) (Fin n) (Q q)), (∀ q, IsUnit (g q).det) → ∀ (q0 : ι), ∃ (B : Matrix (Fin n) (Fin n) F) (u : Matrix (Fin n) (Fin n) (W q0)), IsUnit u.det ∧ B.map (f q0) = g q0 * u.map (algebraMap (W q0) (Q q0)) ∧ ∀ q, q ≠ q0 → ∀ c, (fun i => f q (B i c)) ∈ Formalism.MainNotions.G.colSpan (W q) (g q) := by
  first | exact @GlobalTheory.GlobApx.exists_glob_approx | exact GlobalTheory.GlobApx.exists_glob_approx | (intros; apply GlobalTheory.GlobApx.exists_glob_approx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApproxFinitePlacesNumberField
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApproxFinitePlacesNumberField
open NumberField IsDedekindDomain

namespace GlobalTheory

private theorem exp_neg_le_of_natAbs_log_le {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) {n : ℕ}
    (h : (WithZero.log x).natAbs ≤ n) : WithZero.exp (-(n : ℤ)) ≤ x := by
  rw [← WithZero.exp_log hx, WithZero.exp_le_exp]
  omega

theorem exists_approx_finite_places :
    ∀ {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 F)),
      Function.Injective w → ∀ (y : ∀ i, (w i).adicCompletion F) (c : F), c ≠ 0 →
      ∃ a : F, ∀ i, Valued.v (algebraMap F ((w i).adicCompletion F) a - y i) ≤
        Valued.v (algebraMap F ((w i).adicCompletion F) c) := by
  intro F _ _ ι _ w hw y c hc
  classical
  have hb : ∀ i, ∃ b : F, Valued.v (algebraMap F ((w i).adicCompletion F) b - y i) ≤
      Valued.v (algebraMap F ((w i).adicCompletion F) c) := by
    intro i
    let c' : (w i).adicCompletion F := algebraMap F ((w i).adicCompletion F) c⁻¹
    have hcc : c' * algebraMap F ((w i).adicCompletion F) c = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    have ho : IsOpen ((fun z => (z - y i) * c') ⁻¹'
        ((Valued.v : Valuation ((w i).adicCompletion F) (WithZero (Multiplicative ℤ))).integer : Set ((w i).adicCompletion F))) :=
      (Valued.isOpen_integer _).preimage ((continuous_id.sub continuous_const).mul continuous_const)
    obtain ⟨b, hb⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := F) (v := w i)).exists_mem_open ho ⟨y i, by
      simp only [Set.mem_preimage, sub_self, zero_mul, SetLike.mem_coe]
      exact zero_mem _⟩
    refine ⟨b, ?_⟩
    have h1 : Valued.v ((algebraMap F ((w i).adicCompletion F) b - y i) * c') ≤ 1 :=
      (Valuation.mem_integer_iff _ _).1 hb
    calc Valued.v (algebraMap F ((w i).adicCompletion F) b - y i)
        = Valued.v ((algebraMap F ((w i).adicCompletion F) b - y i) * c') *
            Valued.v (algebraMap F ((w i).adicCompletion F) c) := by
          rw [← map_mul, mul_assoc, hcc, mul_one]
      _ ≤ 1 * Valued.v (algebraMap F ((w i).adicCompletion F) c) := by gcongr
      _ = _ := one_mul _
  choose b hbv using hb
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (M := nonZeroDivisors (𝓞 F))
    (Finset.univ : Finset ι) b
  have hd' : ∀ i, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = (d : 𝓞 F) • b i :=
    fun i => hd i (Finset.mem_univ i)
  choose r hr using hd'
  have hd0 : algebraMap (𝓞 F) F d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  have ht : algebraMap (𝓞 F) F d * c ≠ 0 := mul_ne_zero hd0 hc
  obtain ⟨s0, hs0⟩ := exists_forall_sub_mem_ideal (s := Finset.univ) (fun i => (w i).asIdeal)
    (fun i => (WithZero.log ((w i).valuation F (algebraMap (𝓞 F) F d * c))).natAbs)
    (fun i _ => (w i).prime) (fun i _ j _ hij h => hij (hw (HeightOneSpectrum.ext h)))
    (fun i => r i.1)
  refine ⟨algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d, fun i => ?_⟩
  have hloc : (w i).valuation F (algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d - b i) ≤
      (w i).valuation F c := by
    have e1 : algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d - b i =
        algebraMap (𝓞 F) F (s0 - r i) / algebraMap (𝓞 F) F d := by
      rw [map_sub, hr i, Algebra.smul_def]
      field_simp
    have e2 : c = algebraMap (𝓞 F) F d * c / algebraMap (𝓞 F) F d := by
      field_simp
    have hint : (w i).intValuation (s0 - r i) ≤ WithZero.exp
        (-((WithZero.log ((w i).valuation F (algebraMap (𝓞 F) F d * c))).natAbs : ℤ)) :=
      ((w i).intValuation_le_pow_iff_mem _ _).2 (hs0 i (Finset.mem_univ i))
    have hv : (w i).valuation F (algebraMap (𝓞 F) F (s0 - r i)) ≤
        (w i).valuation F (algebraMap (𝓞 F) F d * c) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact hint.trans (exp_neg_le_of_natAbs_log_le ((Valuation.ne_zero_iff _).2 ht) le_rfl)
    rw [e1]
    conv_rhs => rw [e2]
    rw [map_div₀, map_div₀, div_eq_mul_inv, div_eq_mul_inv]
    gcongr
  have e3 : ∀ x : F, Valued.v (algebraMap F ((w i).adicCompletion F) x) = (w i).valuation F x :=
    fun x => (w i).valuedAdicCompletion_eq_valuation' x
  calc Valued.v (algebraMap F ((w i).adicCompletion F)
        (algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d) - y i)
      = Valued.v ((algebraMap F ((w i).adicCompletion F)
          (algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d) -
            algebraMap F ((w i).adicCompletion F) (b i)) +
          (algebraMap F ((w i).adicCompletion F) (b i) - y i)) := by
        rw [sub_add_sub_cancel]
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ ≤ _ := max_le (by rw [← map_sub, e3, e3]; exact hloc) (hbv i)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApproxFinitePlacesNumberFieldStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approx_finite_places_numberField : ∀ {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 F)), Function.Injective w → ∀ (y : ∀ i, (w i).adicCompletion F) (c : F), c ≠ 0 → ∃ a : F, ∀ i, Valued.v (algebraMap F ((w i).adicCompletion F) a - y i) ≤ Valued.v (algebraMap F ((w i).adicCompletion F) c) := by
  first | exact @GlobalTheory.exists_approx_finite_places | exact GlobalTheory.exists_approx_finite_places | (intros; apply GlobalTheory.exists_approx_finite_places <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalModuleLocalisingToLattices
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Top.KerGlob

theorem weak_approx {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (w : ι → HeightOneSpectrum (𝓞 F)) (hw : Function.Injective w) (y : ∀ i, (w i).adicCompletion F) (c : F) (hc : c ≠ 0) :
    ∃ a : F, ∀ i, Valued.v (algebraMap F ((w i).adicCompletion F) a - y i) ≤
      Valued.v (algebraMap F ((w i).adicCompletion F) c) :=
  GlobalTheory.T.exists_approx_finite_places_numberField w hw y c hc

theorem matrix_approx {ι : Type} [Fintype ι] [DecidableEq ι] (W Q : ι → Type) [∀ q, CommRing (W q)] [∀ q, IsDomain (W q)]
    [∀ q, IsDiscreteValuationRing (W q)] [∀ q, Field (Q q)] [∀ q, Algebra (W q) (Q q)] [∀ q, IsFractionRing (W q) (Q q)]
    {F : Type} [Field F] (f : ∀ q, F →+* Q q) (π : ∀ q, W q) (hπ : ∀ q, Irreducible (π q)) (t : F)
    (ht : ∀ q, f q t = algebraMap (W q) (Q q) (π q))
    (hd : ∀ (y : ∀ q, W q) (N : ℕ), ∃ x : F, ∀ q, ∃ z : W q, f q x = algebraMap (W q) (Q q) (y q + π q ^ N * z))
    {n : ℕ} (g : ∀ q, Matrix (Fin n) (Fin n) (Q q)) (hg : ∀ q, IsUnit (g q).det) (q0 : ι) :
    ∃ (B : Matrix (Fin n) (Fin n) F) (u : Matrix (Fin n) (Fin n) (W q0)), IsUnit u.det ∧
      B.map (f q0) = g q0 * u.map (algebraMap (W q0) (Q q0)) ∧
      ∀ q, q ≠ q0 → ∀ c, (fun i => f q (B i c)) ∈ Formalism.MainNotions.G.colSpan (W q) (g q) :=
  GlobalTheory.T.exists_global_matrix_approximation_mod_integral W Q f π hπ t ht hd g hg q0

theorem colSpan_mul_le {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (g : Matrix (Fin k) (Fin k) K)
    (u : Matrix (Fin k) (Fin k) R) :
    Formalism.MainNotions.G.colSpan R (g * u.map (algebraMap R K)) ≤ Formalism.MainNotions.G.colSpan R g := by
  rw [Formalism.MainNotions.G.colSpan, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  have : (fun i => (g * u.map (algebraMap R K)) i c) = ∑ j, u j c • fun i => g i j := by
    funext i
    simp [Matrix.mul_apply, Algebra.smul_def, mul_comm]
  change (fun i => (g * u.map (algebraMap R K)) i c) ∈ Formalism.MainNotions.G.colSpan R g
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem colSpan_mul_eq {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (g : Matrix (Fin k) (Fin k) K)
    (u : Matrix (Fin k) (Fin k) R) (hu : IsUnit u.det) :
    Formalism.MainNotions.G.colSpan R (g * u.map (algebraMap R K)) = Formalism.MainNotions.G.colSpan R g := by
  refine le_antisymm (colSpan_mul_le g u) ?_
  have := colSpan_mul_le (g * u.map (algebraMap R K)) u⁻¹
  rwa [Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this

theorem map_int {F E : Type} [Field F] [NumberField F] [Field E] (w : HeightOneSpectrum (𝓞 F))
    (φ : E →+* w.adicCompletion F) (x : 𝓞 E) : φ x ∈ w.adicCompletionIntegers F := by
  have h2 : IsIntegral (w.adicCompletionIntegers F) (φ x) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) φ (RingHom.ext_int _ _) x.isIntegral_coe
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := w.adicCompletionIntegers F)
    (K := w.adicCompletion F)).1 h2
  rw [← hy]
  exact y.2

theorem step {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {W Q : Type} [CommRing W] [Field Q]
    [Algebra W Q] (e : Q ≃+* w.adicCompletion F)
    (heW : ∀ x, x ∈ Set.range (algebraMap W Q) ↔ e x ∈ w.adicCompletionIntegers F) (p N : ℕ) (hp : (p : F) ≠ 0)
    (a : F) (y : W)
    (hv : Valued.v (algebraMap F (w.adicCompletion F) a - e (algebraMap W Q y)) ≤
      Valued.v (algebraMap F (w.adicCompletion F) ((p : F) ^ N))) :
    ∃ z : W, e.symm (algebraMap F (w.adicCompletion F) a) = algebraMap W Q (y + (p : W) ^ N * z) := by
  have hcc0 : algebraMap F (w.adicCompletion F) ((p : F) ^ N) ≠ 0 := (map_ne_zero _).2 (pow_ne_zero _ hp)
  have hz' : (algebraMap F (w.adicCompletion F) a - e (algebraMap W Q y)) / algebraMap F (w.adicCompletion F) ((p : F) ^ N) ∈
      w.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
    exact div_le_one_of_le₀ hv zero_le
  obtain ⟨z, hz⟩ := (heW (e.symm _)).2 (by rw [e.apply_symm_apply]; exact hz')
  refine ⟨z, ?_⟩
  apply e.injective
  rw [e.apply_symm_apply, map_add (f := _), map_add (f := _), map_mul, hz, map_mul, e.apply_symm_apply, map_pow, map_pow, map_natCast,
    map_natCast]
  have hcc' : algebraMap F (w.adicCompletion F) ((p : F) ^ N) = (p : w.adicCompletion F) ^ N := by
    rw [map_pow, map_natCast]
  rw [← hcc', mul_div_cancel₀ _ hcc0]
  ring

variable {D : D7} {H : Formalism.L2.Herm.HermColsCh D} (Gs : Formalism.L2.Herm.SymmetricGroupCompatibility D H) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v))

theorem splitPlaceEmbedding_integers_mem_localIntegers (q : Fin (D.gat u v hg).P.nV) (r : 𝓞 D.host.E) :
    KerOne.iw0 Gs u v hg q (algebraMap (𝓞 D.host.E) D.host.E r) ∈
      Set.range (algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q)) := by
  refine ((Gs u v hg).completion_integers_iff q _ rfl _).2 ?_
  rw [KerOne.splitPlaceIdempotent_cmEmbedding_compat]
  exact map_int _ (((RingHom.fst _ _).comp ((Gs u v hg).spl _ ((Gs u v hg).pl q).2).toRingHom).comp
      (Formalism.UG.inclE (F := D.host.F) ((((Gs u v hg).pl q).1).adicCompletion D.host.F))) r

theorem splitPlaceEmbedding_baseField_eq_completion (q : Fin (D.gat u v hg).P.nV) (a : D.host.F) :
    KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E a) =
      ((Gs u v hg).eQ q _ rfl).symm (algebraMap D.host.F ((((Gs u v hg).pl q).1).adicCompletion D.host.F) a) := by
  apply ((Gs u v hg).eQ q _ rfl).injective
  rw [KerOne.splitPlaceIdempotent_cmEmbedding_compat]
  refine ((Gs u v hg).spl_F _ _ a).trans ?_
  exact (RingEquiv.apply_symm_apply _ _).symm

theorem pl_inj : Function.Injective (fun q : Fin (D.gat u v hg).P.nV => ((Gs u v hg).pl q).1) :=
  fun _ _ h => (Gs u v hg).pl.injective (Subtype.ext h)

theorem dense (y : ∀ q, (D.gat u v hg).P.W q) (N : ℕ) : ∃ x : D.host.F, ∀ q, ∃ z : (D.gat u v hg).P.W q,
    KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E x) =
      algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q)
        (y q + ((D.what₂.places.resChar v : ℕ) : (D.gat u v hg).P.W q) ^ N * z) := by
  rcases isEmpty_or_nonempty (Fin (D.gat u v hg).P.nV) with h | ⟨⟨q1⟩⟩
  · exact ⟨0, fun q => (IsEmpty.false q).elim⟩
  have hp0 : ((D.what₂.places.resChar v : ℕ) : D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (((D.gat u v hg).P.setting q1).prime.ne_zero)
  obtain ⟨a, ha⟩ := weak_approx (fun q => ((Gs u v hg).pl q).1) (pl_inj Gs u v hg)
    (fun q => (Gs u v hg).eQ q _ rfl (algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q) (y q)))
    (((D.what₂.places.resChar v : ℕ) : D.host.F) ^ N) (pow_ne_zero _ hp0)
  refine ⟨a, fun q => ?_⟩
  obtain ⟨z, hz⟩ := step _ ((Gs u v hg).eQ q _ rfl) ((Gs u v hg).completion_integers_iff q _ rfl) _ N hp0 a (y q) (ha q)
  exact ⟨z, (splitPlaceEmbedding_baseField_eq_completion Gs u v hg q a).trans hz⟩

theorem exists_global_lattice (n : ℕ)
    (L : ∀ q : Fin (D.gat u v hg).P.nV, Submodule ((D.gat u v hg).P.W q) (Fin n → (D.gat u v hg).P.Qq q)) :
    (∀ q, G.IsLattice ((D.gat u v hg).P.W q) (L q)) →
    ∃ Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E), ∀ q,
      L q = Submodule.span ((D.gat u v hg).P.W q) {y | ∃ x ∈ Λ, y = fun i => KerOne.iw0 Gs u v hg q (x i)} := by
  intro hL
  choose g hgu hgL using hL
  have hfr : ∀ q, IsFractionRing ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q) :=
    fun q => ((D.gat u v hg).P.setting q).frac_alt
  let Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
    { carrier := {x | ∀ q, (fun i => KerOne.iw0 Gs u v hg q (x i)) ∈ L q}
      add_mem' := fun {x y} hx hy q => by
        have : (fun i => KerOne.iw0 Gs u v hg q ((x + y) i)) =
            (fun i => KerOne.iw0 Gs u v hg q (x i)) + fun i => KerOne.iw0 Gs u v hg q (y i) := by
          funext i; simp
        rw [this]; exact (L q).add_mem (hx q) (hy q)
      zero_mem' := fun q => by
        have : (fun i => KerOne.iw0 Gs u v hg q ((0 : Fin n → D.host.E) i)) = 0 := by funext i; simp
        rw [this]; exact (L q).zero_mem
      smul_mem' := fun r x hx q => by
        obtain ⟨c, hc⟩ := splitPlaceEmbedding_integers_mem_localIntegers Gs u v hg q r
        have : (fun i => KerOne.iw0 Gs u v hg q ((r • x) i)) = c • fun i => KerOne.iw0 Gs u v hg q (x i) := by
          funext i
          rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_mul, ← hc, Algebra.smul_def]
        rw [this]; exact (L q).smul_mem c (hx q) }
  refine ⟨Λ, fun q0 => ?_⟩
  obtain ⟨B, w, hw, hB, hoff⟩ := matrix_approx (fun q => (D.gat u v hg).P.W q) (fun q => (D.gat u v hg).P.Qq q)
    (fun q => (KerOne.iw0 Gs u v hg q).comp (algebraMap D.host.F D.host.E))
    (fun q => ((D.what₂.places.resChar v : ℕ) : (D.gat u v hg).P.W q)) (fun q => ((D.gat u v hg).P.setting q).p_unif)
    ((D.what₂.places.resChar v : ℕ) : D.host.F) (fun q => by rw [map_natCast, map_natCast])
    (fun y N => dense Gs u v hg y N) g hgu q0
  have hcol : ∀ c, (fun i => algebraMap D.host.F D.host.E (B i c)) ∈ Λ := by
    intro c q
    by_cases hq : q = q0
    · subst hq
      have : (fun i => KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E (B i c))) =
          fun i => (g q * w.map (algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q))) i c := by
        funext i; exact congrFun (congrFun hB i) c
      show (fun i => KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E (B i c))) ∈ L q
      rw [this, hgL q, ← colSpan_mul_eq (g q) w hw]
      exact Submodule.subset_span ⟨c, rfl⟩
    · show (fun i => KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E (B i c))) ∈ L q
      rw [hgL q]; exact hoff q hq c
  apply le_antisymm
  · rw [hgL q0, ← colSpan_mul_eq (g q0) w hw, Formalism.MainNotions.G.colSpan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    refine Submodule.subset_span ⟨_, hcol c, ?_⟩
    funext i; exact (congrFun (congrFun hB i) c).symm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx q0

end GlobalTheory.Mem.Top.KerGlob
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalModuleLocalisingToLatticesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_module_localising_to_lattices : ∀ {D : D7} {H : Formalism.L2.Herm.HermColsCh D} (Gs : Formalism.L2.Herm.SymmetricGroupCompatibility D H) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)) (n : ℕ)
    (L : ∀ q : Fin (D.gat u v hg).P.nV, Submodule ((D.gat u v hg).P.W q) (Fin n → (D.gat u v hg).P.Qq q)),
    (∀ q, G.IsLattice ((D.gat u v hg).P.W q) (L q)) →
    ∃ Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E), ∀ q,
      L q = Submodule.span ((D.gat u v hg).P.W q) {y | ∃ x ∈ Λ, y = fun i => GlobalTheory.Mem.Top.KerOne.iw0 Gs u v hg q (x i)} := by
  first | exact @GlobalTheory.Mem.Top.KerGlob.exists_global_lattice | exact GlobalTheory.Mem.Top.KerGlob.exists_global_lattice | (intros; apply GlobalTheory.Mem.Top.KerGlob.exists_global_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalCoefficientFieldEmbeddingKernelPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalCoefficientFieldEmbeddingKernelPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KerIK

open Cardinal

theorem kf_hom_of_isRec {sc : Scale} {D : D7} {Gt : GatTies D} {c : LatCmp D} {H : Formalism.L2.Herm.Herm0 D}
    {F : ∀ u, Formalism.L2.Forms.Forms0 D u} (h : IsRecG sc D Gt c H F) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)) [Fact (D.what₂.places.resChar v).Prime] :
    Nonempty ((D.gat u v hg).Kf →+* ℂ_[D.what₂.places.resChar v]) := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, eq⟩ := h
  cases eq
  exact ⟨iK u v hg⟩

theorem mk_LL_le (D : D7) : #D.what₂.LL ≤ ℵ₀ := by
  have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ D.what₂.LL
  rwa [Cardinal.mkRat, max_self] at this

theorem exists_iK : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ iK : ((w.D Z).gat u v hg).Kf →+* ℂ_[(w.D Z).what₂.places.resChar v],
        ∀ (x : (w.D Z).what₂.LL) (hx : (w.D Z).what₂.embLL x ∈ algebraicClosure ℚ ℂ),
          iK (t.cmp.embW u v hg x) = E.lam v ⟨(w.D Z).what₂.embLL x, hx⟩ := by
  intro K B f T w _ _ _ Z t Wt nch _ Y _ _ O _ _ E _ u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  obtain ⟨i0⟩ := kf_hom_of_isRec t.isRec u v hg
  have hC : ℵ₀ < #ℂ_[(w.D Z).what₂.places.resChar v] :=
    Cardinal.aleph0_lt_continuum.trans_le (continuum_le_cardinal_of_nontriviallyNormedField _)
  obtain ⟨σ, hσ⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.extEmb_equiv_comp (i0.comp (t.cmp.embW u v hg)) (E.iL v)
    (mk_LL_le (w.D Z)) hC rfl
  refine ⟨σ.toRingHom.comp i0, fun x hx => ?_⟩
  have h1 := hσ x
  have h2 := E.iL_lam v x
  simp only [RingHom.comp_apply] at h1
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [h1, h2, lamV, dite_eq_left hx]

end GlobalTheory.KerIK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalCoefficientFieldEmbeddingKernelPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localCoefficientField_embedding_kernelPlace : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ iK : ((w.D Z).gat u v hg).Kf →+* ℂ_[(w.D Z).what₂.places.resChar v],
        ∀ (x : (w.D Z).what₂.LL) (hx : (w.D Z).what₂.embLL x ∈ algebraicClosure ℚ ℂ),
          iK (t.cmp.embW u v hg x) = E.lam v ⟨(w.D Z).what₂.embLL x, hx⟩ := by
  first | exact @GlobalTheory.KerIK.exists_iK | exact GlobalTheory.KerIK.exists_iK | (intros; apply GlobalTheory.KerIK.exists_iK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFreeSeriesKernelServedPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFreeSeriesKernelServedPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KerTieServed
open MvPowerSeries

section Lin
variable {p : ℕ} [Fact p.Prime] {σ σ' : Type*} [Fintype σ] [Fintype σ']

theorem hasSubst_linear {κ : Type*} [Fintype κ] (c : σ → κ → ℂ_[p]) :
    HasSubst (fun k : σ => ∑ x : κ, algebraMap ℂ_[p] (MvPowerSeries κ ℂ_[p]) (c k x) * X x) :=
  hasSubst_of_constantCoeff_zero fun k => by simp

theorem linAt_comp {κ : Type*} [Fintype κ] (c₁ : σ → σ' → ℂ_[p]) (c₂ : σ' → κ → ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) :
    linAt c₂ (linAt c₁ F) = linAt (fun k x => ∑ j, c₁ k j * c₂ j x) F := by
  unfold linAt
  rw [subst_comp_subst_apply (hasSubst_linear c₁) (hasSubst_linear c₂)]
  congr 1
  funext k
  rw [← coe_substAlgHom (hasSubst_linear c₂)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, AlgHom.commutes, substAlgHom_X, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem linAt_delta [DecidableEq σ] (F : MvPowerSeries σ ℂ_[p]) :
    linAt (fun k x : σ => if k = x then (1 : ℂ_[p]) else 0) F = F := by
  unfold linAt
  have e : (fun k : σ => ∑ x : σ, algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) (if k = x then (1 : ℂ_[p]) else 0) * X x) =
      X := by
    funext k
    simp [apply_ite]
  rw [e, subst_self]
  rfl

end Lin

section Mat
variable {K : Type*} [Field K] {T J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

def blk (ev : T → Prop) [DecidablePred ev] (A : T → Matrix J J K) (e : I ≃ J) (τ : T) : Matrix J I K :=
  if ev τ then (A τ).submatrix id e else ((A τ)⁻¹).transpose.submatrix id e

def blkInv (ev : T → Prop) [DecidablePred ev] (A : T → Matrix J J K) (e : I ≃ J) (τ : T) : Matrix I J K :=
  if ev τ then ((A τ)⁻¹).submatrix e id else (A τ).transpose.submatrix e id

theorem blkInv_mul_blk (ev : T → Prop) [DecidablePred ev] (A : T → Matrix J J K) (e : I ≃ J)
    (hA : ∀ τ, IsUnit (A τ).det) (τ : T) : blkInv ev A e τ * blk ev A e τ = 1 := by
  unfold blk blkInv
  split_ifs
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.nonsing_inv_mul _ (hA τ),
      Matrix.submatrix_one_equiv]
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (hA τ), Matrix.transpose_one,
      Matrix.submatrix_one_equiv]

end Mat

section Sum
variable {K : Type*} [CommRing K] {S T J₁ J₂ I₁ I₂ : Type*} [Fintype T] [DecidableEq T] [Fintype J₁] [Fintype J₂]
  [DecidableEq S] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq J₁] [DecidableEq J₂]

def coef (t : S → T) (P : T → Matrix J₂ I₂ K) (Q : T → Matrix I₁ J₁ K) : T × J₂ × J₁ → S × I₁ × I₂ → K :=
  fun k x => if t x.1 = k.1 then P k.1 k.2.1 x.2.2 * Q k.1 x.2.1 k.2.2 else 0

def coefInv (t : S → T) (P' : T → Matrix I₂ J₂ K) (Q' : T → Matrix J₁ I₁ K) : S × I₁ × I₂ → T × J₂ × J₁ → K :=
  fun x k => if t x.1 = k.1 then P' k.1 x.2.2 k.2.1 * Q' k.1 k.2.2 x.2.1 else 0

theorem sum_coefInv_coef (t : S → T) (ht : Function.Injective t) (P : T → Matrix J₂ I₂ K) (Q : T → Matrix I₁ J₁ K)
    (P' : T → Matrix I₂ J₂ K) (Q' : T → Matrix J₁ I₁ K) (hP : ∀ τ, P' τ * P τ = 1) (hQ : ∀ τ, Q τ * Q' τ = 1)
    (x x' : S × I₁ × I₂) :
    ∑ k, coefInv t P' Q' x k * coef t P Q k x' = if x = x' then 1 else 0 := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (t x.1)]
  · unfold coef coefInv
    simp only [if_true]
    by_cases hxx : t x'.1 = t x.1
    · have h1 : x'.1 = x.1 := ht hxx
      simp only [hxx, if_true]
      have e : ∀ y : J₂ × J₁, P' (t x.1) x.2.2 y.1 * Q' (t x.1) y.2 x.2.1 * (P (t x.1) y.1 x'.2.2 * Q (t x.1) x'.2.1 y.2) =
          (P' (t x.1) x.2.2 y.1 * P (t x.1) y.1 x'.2.2) * (Q (t x.1) x'.2.1 y.2 * Q' (t x.1) y.2 x.2.1) := fun y => by ring
      rw [Finset.sum_congr rfl fun y _ => e y, Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      have e1 := congrFun (congrFun (hP (t x.1)) x.2.2) x'.2.2
      have e2 := congrFun (congrFun (hQ (t x.1)) x'.2.1) x.2.1
      rw [Matrix.mul_apply] at e1 e2
      rw [e1, e2, Matrix.one_apply, Matrix.one_apply]
      obtain ⟨a, b, c⟩ := x
      obtain ⟨a', b', c'⟩ := x'
      simp only at h1 ⊢
      subst h1
      rcases eq_or_ne b b' with rfl | hb <;> rcases eq_or_ne c c' with rfl | hc <;>
        first | (simp; done) | (simp [hb, hb.symm]; done) | (simp [hc, hc.symm]; done) | simp [hb, hb.symm, hc, hc.symm]
    · have hne : x ≠ x' := fun hx => hxx (by rw [hx])
      simp only [hxx, if_false, mul_zero, Finset.sum_const_zero, hne]
  · intro τ _ hτ
    refine Finset.sum_eq_zero fun y _ => ?_
    unfold coefInv
    rw [if_neg (Ne.symm hτ), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end Sum

section Main

theorem isUnit_det_rhoMat {D : D7} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : G.Fills (D.gat u w h)} {Lv : G.Levels Fl}
    {Ch : G.Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch) (j : ℕ) (τ : D.what₂.Tau)
    (g : ∀ v, Matrix (Fin ((Fl.Pj j).m + 1)) (Fin ((Fl.Pj j).m + 1)) ((Fl.Pj j).Qq v)) (hg : ∀ v, IsUnit (g v).det) :
    IsUnit (rhoMat Kp j τ g).det := by
  unfold rhoMat
  have e := RingHom.map_det (Kp.iK.comp (((Fl.Pj j).ι ((posJ Gt u w h Fl j).symm τ).1).comp
    (RingEquiv.toRingHom (((Fl.Pj j).σ ((posJ Gt u w h Fl j).symm τ).1) ^ ((posJ Gt u w h Fl j).symm τ).2.val))))
    (g ((posJ Gt u w h Fl j).symm τ).1)
  rw [RingHom.mapMatrix_apply] at e
  have hu := (hg ((posJ Gt u w h Fl j).symm τ).1).map (Kp.iK.comp (((Fl.Pj j).ι ((posJ Gt u w h Fl j).symm τ).1).comp
    (RingEquiv.toRingHom (((Fl.Pj j).σ ((posJ Gt u w h Fl j).symm τ).1) ^ ((posJ Gt u w h Fl j).symm τ).2.val))))
  rw [e] at hu
  exact hu


open Classical in
theorem exists_th_served : ∀ {D : D7} {Dx : DivX D} (Gt : GatTies D) {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : G.Fills (D.gat u w h)} {Lv : G.Levels Fl}
    (KD : Formalism.L2.G.Cmp.KerData D c Tw u w h Lv) (E : KerEnt D Dx Tw), KD.lam = E.lam w →
    ∃ Th, ThAtServed (Formalism.L2.G.Cmp.kerAtP_of Gt { KD with Th := Th }) E := by
  intro D Dx Gt c Tw u w h Fl Lv KD E hlam
  let g : ∀ (j : ℕ) (_ : Lv.comp j × (Fl.Pj j).Tup) (v : Fin (Fl.Pj j).nV),
      Matrix (Fin ((Fl.Pj j).m + 1)) (Fin ((Fl.Pj j).m + 1)) ((Fl.Pj j).Qq v) :=
    fun j La v => if hL : (Fl.Pj j).IsLatTup La.2 then (hL v).choose else 1
  have hg : ∀ j La v, IsUnit (g j La v).det := by
    intro j La v
    by_cases hL : (Fl.Pj j).IsLatTup La.2
    · simp only [g, dif_pos hL]; exact (hL v).choose_spec.1
    · simp only [g, dif_neg hL, Matrix.det_one]; exact isUnit_one
  let K0 := Formalism.L2.G.Cmp.kerAtP_of Gt KD
  let ev : ℕ → D.what₂.Tau → Prop := fun j τ => Formalism.MainNotions.G.IsTypeV ((posJ Gt u w h Fl j).symm τ).2
  let Th : ∀ j, Lv.comp j × (Fl.Pj j).Tup → Lv.comp (j + 1) × (Fl.Pj (j + 1)).Tup →
      MvPowerSeries (D.what₂.Tau × Fin ((Fl.Pj (j + 1)).m + 1) × Fin ((Fl.Pj j).m + 1)) ℂ_[D.what₂.places.resChar w] :=
    fun j La La' => if hh : (Fl.Pj j).m + 1 = D.R.N j ∧ (Fl.Pj (j + 1)).m + 1 = D.R.N (j + 1) then
      linAt (coefInv (Formalism.BasicNotions.tauPl D)
          (blkInv (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hh.2.symm))
          (blk (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hh.1.symm)))
        (E.Th u (D.what₂.muAt w) w j (KD.cls j La.1 La.2) (KD.cls (j + 1) La'.1 La'.2))
    else 0
  refine ⟨Th, hlam, g, ?_, ?_⟩
  · intro j _ La hL v
    refine ⟨hg j La v, ?_⟩
    simp only [g, dif_pos hL]
    exact (hL v).choose_spec.2
  · intro j _ hN hN' La La' _ _
    refine ⟨fun _ => 1, fun _ => norm_one, ?_⟩
    have hTh : Th j La La' = linAt (coefInv (Formalism.BasicNotions.tauPl D)
          (blkInv (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
          (blk (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm)))
        (E.Th u (D.what₂.muAt w) w j (KD.cls j La.1 La.2) (KD.cls (j + 1) La'.1 La'.2)) := by
      simp only [Th, dif_pos (And.intro hN hN')]
    have hC : (fun (k : D.what₂.Tau × Fin ((Fl.Pj (j + 1)).m + 1) × Fin ((Fl.Pj j).m + 1))
              (x : (Bool × G.HH D) × Fin (D.R.N j) × Fin (D.R.N (j + 1))) =>
            if Formalism.BasicNotions.tauPl D x.1 = k.1 then
              (if Formalism.MainNotions.G.IsTypeV ((posJ Gt u w h Fl j).symm k.1).2 then
                (fun _ => (1 : ℂ_[D.what₂.places.resChar w])) k.1 * (rhoMat K0 (j + 1) k.1 (g (j + 1) La')) k.2.1 (Fin.cast hN'.symm x.2.2) *
                  ((rhoMat K0 j k.1 (g j La))⁻¹) (Fin.cast hN.symm x.2.1) k.2.2
              else
                (fun _ => (1 : ℂ_[D.what₂.places.resChar w])) k.1 * (((rhoMat K0 (j + 1) k.1 (g (j + 1) La'))⁻¹).transpose) k.2.1 (Fin.cast hN'.symm x.2.2) *
                  ((rhoMat K0 j k.1 (g j La)).transpose) (Fin.cast hN.symm x.2.1) k.2.2)
            else 0) =
        coef (Formalism.BasicNotions.tauPl D) (blk (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
          (blkInv (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm)) := by
      funext k x
      simp only [coef, blk, blkInv, ev]
      split_ifs <;> simp [Matrix.submatrix_apply, Matrix.transpose_apply]
    have hS := sum_coefInv_coef (Formalism.BasicNotions.tauPl D) (Formalism.BasicNotions.tauPl_bij D).1
      (blk (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
      (blkInv (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm))
      (blkInv (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
      (blk (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm))
      (blkInv_mul_blk _ _ _ fun τ => isUnit_det_rhoMat K0 (j + 1) τ _ (hg (j + 1) La'))
      (blkInv_mul_blk _ _ _ fun τ => isUnit_det_rhoMat K0 j τ _ (hg j La))
    have key : E.Th u (D.what₂.muAt w) w j (KD.cls j La.1 La.2) (KD.cls (j + 1) La'.1 La'.2) =
        linAt (coef (Formalism.BasicNotions.tauPl D) (blk (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
          (blkInv (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm))) (Th j La La') := by
      rw [hTh, linAt_comp]
      simp only [hS]
      exact (linAt_delta _).symm
    rw [← hC] at key
    exact key

end Main

end GlobalTheory.KerTieServed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFreeSeriesKernelServedPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_freeSeries_kernel_servedPlace : ∀ {D : D7} {Dx : DivX D} (Gt : GatTies D) {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : G.Fills (D.gat u w h)} {Lv : G.Levels Fl}
    (KD : Formalism.L2.G.Cmp.KerData D c Tw u w h Lv) (E : KerEnt D Dx Tw), KD.lam = E.lam w →
    ∃ Th, ThAtServed (Formalism.L2.G.Cmp.kerAtP_of Gt { KD with Th := Th }) E := by
  first | exact @GlobalTheory.KerTieServed.exists_th_served | exact GlobalTheory.KerTieServed.exists_th_served | (intros; apply GlobalTheory.KerTieServed.exists_th_served <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsKernelDataAtServedPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.KerOne

theorem kerData_at_served : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ (Lv : G.Levels (Fl u v hg)) (KD : Formalism.L2.G.Cmp.KerData (w.D Z) t.cmp (w.tw Z) u v hg Lv),
        KD.lam = E.lam v ∧
        ThAtServed (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) E ∧
        Formalism.L2.Herm.SymmetricKernelCompatibleAtPlace t.full.1.base.toHermColsCh t.full.1.g u v hg (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) ∧
        Formalism.L2.Herm.GIwPos u v hg (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) := by
  intro K B f T w hO hF hP Z t Wt nch hn Y hMu hQp O hStd hUnf E hE Fl hFl hw u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  obtain ⟨iK, hiK⟩ := GlobalTheory.T.exists_localCoefficientField_embedding_kernelPlace w hO hF hP Z t Wt nch hn Y hMu hQp O hStd hUnf E hE u v hg
  have hpos := GlobalTheory.T.splitPlace_embedding_at_orbitPosition_eq_induced_alt w hO hF hP Z t Wt nch hn Y hMu hQp O hStd hUnf E hE u v hg
  obtain ⟨cls0, h0iff, h0surj⟩ := GlobalTheory.T.stepZeroClasses_servedPlace_eq_localOrbitPairs w hO hF hP Z t Wt nch hn Y hMu hQp O hStd hUnf E hE u v hg
  obtain ⟨Lv, clsS, up, hSiff, hSsurj, hInt⟩ := GlobalTheory.T.served_place_levels_classes_comparison_maps w hO hF hP Z t Wt nch hn Y hMu hQp O hStd hUnf E hE Fl hFl hw u v hg
  classical
  let Gs := t.full.1.g
  let iwJ : ∀ j (q : Fin ((Fl u v hg).Pj j).nV), (w.D Z).host.E →+* ((Fl u v hg).Pj j).Qq q := fun j =>
    match j with
    | 0 => fun q => iw0 Gs u v hg q
    | _ + 1 => fun q => iw0 Gs u v hg q
  let globJ : ∀ j, Lv.comp j → ((Fl u v hg).Pj j).Tup →
      Submodule (𝓞 (w.D Z).host.E) (Fin (((Fl u v hg).Pj j).m + 1) → (w.D Z).host.E) := fun j =>
    match j with
    | 0 => fun _ L => if hL : ((Fl u v hg).Pj 0).IsLatTup L then
        Classical.choose (GlobalTheory.T.exists_global_module_localising_to_lattices Gs u v hg (((Fl u v hg).Pj 0).m + 1) L hL) else ⊥
    | j + 1 => fun _ L => if hL : ((Fl u v hg).Pj (j + 1)).IsLatTup L then
        Classical.choose (GlobalTheory.T.exists_global_module_localising_to_lattices Gs u v hg (((Fl u v hg).Pj (j + 1)).m + 1) L hL) else ⊥
  let clsJ : ∀ j, Lv.comp j → ((Fl u v hg).Pj j).Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls j := fun j =>
    match j with
    | 0 => fun a L => cls0 a L
    | j + 1 => fun a L => clsS j a L
  let KD0 : Formalism.L2.G.Cmp.KerData (w.D Z) t.cmp (w.tw Z) u v hg Lv :=
    { fl_t := (hFl u v hg).1
      fl_m := (hFl u v hg).2
      lam := E.lam v
      iK := iK
      iLL_lam := hiK
      iw := iwJ
      glob := globJ
      glob_loc := by
        intro j _ a L hL q
        cases j with
        | zero =>
          have h := Classical.choose_spec (GlobalTheory.T.exists_global_module_localising_to_lattices Gs u v hg (((Fl u v hg).Pj 0).m + 1) L hL) q
          simp only [globJ, iwJ, dif_pos hL]
          exact h
        | succ j =>
          have h := Classical.choose_spec (GlobalTheory.T.exists_global_module_localising_to_lattices Gs u v hg (((Fl u v hg).Pj (j + 1)).m + 1) L hL) q
          simp only [globJ, iwJ, dif_pos hL]
          exact h
      cls := clsJ
      cls_iff := by
        intro j hj a a' L L' hL hL'
        cases j with
        | zero => exact h0iff a a' L L' hL hL'
        | succ j => exact hSiff j hj a a' L L' hL hL'
      cls_surj := by
        intro j hj x
        cases j with
        | zero => exact h0surj x
        | succ j => exact hSsurj j hj x
      Th := fun _ _ _ => 0
      up := up
      intS := hInt }
  obtain ⟨Th, hTh⟩ := GlobalTheory.T.exists_freeSeries_kernel_servedPlace t.Gt KD0 E rfl
  refine ⟨Lv, { KD0 with Th := Th }, rfl, hTh, ?_, ?_⟩
  · intro q x
    exact splitPlaceIdempotent_cmEmbedding_compat Gs u v hg q x
  · intro q s x
    exact hpos q s x

end GlobalTheory.Mem.Top.KerOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsKernelDataAtServedPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levels_kernelData_at_served_place : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ (Lv : G.Levels (Fl u v hg)) (KD : Formalism.L2.G.Cmp.KerData (w.D Z) t.cmp (w.tw Z) u v hg Lv),
        KD.lam = E.lam v ∧
        ThAtServed (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) E ∧
        Formalism.L2.Herm.SymmetricKernelCompatibleAtPlace t.full.1.base.toHermColsCh t.full.1.g u v hg (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) ∧
        Formalism.L2.Herm.GIwPos u v hg (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) := by
  first | exact @GlobalTheory.Mem.Top.KerOne.kerData_at_served | exact GlobalTheory.Mem.Top.KerOne.kerData_at_served | (intros; apply GlobalTheory.Mem.Top.KerOne.kerData_at_served <;> assumption)
end
