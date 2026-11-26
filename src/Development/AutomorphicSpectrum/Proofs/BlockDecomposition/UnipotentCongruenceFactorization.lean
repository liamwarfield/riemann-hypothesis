module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentCongruenceFactorization
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentCongruenceFactorization
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto.Key1

open GlobalTheory.SplitWeil ValuativeRel

section Core

variable {k : Type} [Field k]

def rowM (n : ℕ) (a : Fin (n + 1) → k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  1 + Matrix.of fun r c => if r = Fin.last n then a c else 0

theorem rowM_apply (n : ℕ) (a : Fin (n + 1) → k) (r c : Fin (n + 1)) :
    rowM n a r c = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) r c + if r = Fin.last n then a c else 0 := rfl

theorem rowM_mul (n : ℕ) (a b : Fin (n + 1) → k) :
    rowM n a * rowM n b = rowM n (a + b + a (Fin.last n) • b) := by
  ext r c
  have e : rowM n a * rowM n b = 1 + (Matrix.of fun r c => if r = Fin.last n then a c else 0) +
      (Matrix.of fun r c => if r = Fin.last n then b c else 0) +
      (Matrix.of fun r c => if r = Fin.last n then a c else 0) *
        (Matrix.of fun r c => if r = Fin.last n then b c else 0) := by
    unfold rowM
    noncomm_ring
  rw [e]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, rowM_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hr : r = Fin.last n
  · subst hr
    simp [Finset.sum_ite_eq', ite_mul]
    ring
  · simp [hr]

def rowGL (n : ℕ) (a : Fin (n + 1) → k) (hu : 1 + a (Fin.last n) ≠ 0) : GL (Fin (n + 1)) k where
  val := rowM n a
  inv := rowM n (-(1 + a (Fin.last n))⁻¹ • a)
  val_inv := by
    rw [rowM_mul]
    have : a + -(1 + a (Fin.last n))⁻¹ • a + a (Fin.last n) • -(1 + a (Fin.last n))⁻¹ • a = 0 := by
      ext c
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      field_simp
      ring
    rw [this]
    ext r c
    simp [rowM_apply]
  inv_val := by
    rw [rowM_mul]
    have : -(1 + a (Fin.last n))⁻¹ • a + a + (-(1 + a (Fin.last n))⁻¹ • a) (Fin.last n) • a = 0 := by
      ext c
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      field_simp
      ring
    rw [this]
    ext r c
    simp [rowM_apply]

theorem rowGL_inv_val (n : ℕ) (a : Fin (n + 1) → k) (hu : 1 + a (Fin.last n) ≠ 0) :
    (((rowGL n a hu)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      rowM n (-(1 + a (Fin.last n))⁻¹ • a) := rfl

end Core

section Core2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rowM_near (s : kˣ) (n : ℕ) (a : Fin (n + 1) → k) (ha : ∀ c, a c ∈ cball s) :
    GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s (rowM n a) := by
  intro r c
  rw [rowM_apply, add_sub_cancel_left]
  split_ifs
  · exact ha c
  · exact (ballSub s).zero_mem

theorem rowGL_mem (s : kˣ) (hs : valuation k (s : k) ≤ 1) (n : ℕ) (a : Fin (n + 1) → k)
    (hu : 1 + a (Fin.last n) ≠ 0) (hv : valuation k (1 + a (Fin.last n)) = 1) (ha : ∀ c, a c ∈ cball s) :
    rowGL n a hu ∈ congGL k s hs (n + 1) := by
  refine ⟨rowM_near s n a ha, ?_⟩
  rw [rowGL_inv_val]
  refine rowM_near s n _ fun c => ?_
  show valuation k ((-(1 + a (Fin.last n))⁻¹ • a) c) ≤ valuation k (s : k)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, Valuation.map_neg, map_inv₀, hv, inv_one, one_mul]
  exact ha c

theorem core (s : kˣ) (hs : valuation k (s : k) ≤ 1) (hs1 : valuation k (s : k) < 1) {n i : ℕ} (hi : i < n)
    (A B M : GL (Fin (n + 1)) k) (hM : M ∈ Mir k n) (hMAB : M = A * B) (hB : B ∈ congGL k s hs (n + 1))
    (hA : ∀ r c : Fin (n + 1), i < r.val → c.val ≤ i → (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) r c = 0) :
    ∃ a x : GL (Fin (n + 1)) k, a ∈ Mir k n ∧ x ∈ Mir k n ∧ x ∈ congGL k s hs (n + 1) ∧ M = a * x ∧
      ∀ r c : Fin (n + 1), i < r.val → c.val ≤ i → (a : Matrix (Fin (n + 1)) (Fin (n + 1)) k) r c = 0 := by
  classical
  set Bi : Matrix (Fin (n + 1)) (Fin (n + 1)) k := ((B⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) with hBi
  let a : Fin (n + 1) → k := fun c => Bi (Fin.last n) c - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) c
  have ha : ∀ c, a c ∈ cball s := fun c => hB.2 (Fin.last n) c
  have hv : valuation k (1 + a (Fin.last n)) = 1 :=
    Valuation.map_one_add_of_lt _ (lt_of_le_of_lt (ha _) hs1)
  have hu : 1 + a (Fin.last n) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv

  have hAB : A = M * B⁻¹ := by rw [hMAB]; group
  have hlast : ∀ c, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) c = Bi (Fin.last n) c := by
    intro c
    have hl := (mem_Mir_iff k M).1 hM
    rw [hAB, Units.val_mul, Matrix.mul_apply, hl]
    simp [eLast, Pi.single_apply, hBi]
  have ha0 : ∀ c : Fin (n + 1), c.val ≤ i → a c = 0 := by
    intro c hc
    have h1 : Bi (Fin.last n) c = 0 := by
      rw [← hlast c]
      exact hA _ c (by simpa using hi) hc
    have h2 : Fin.last n ≠ c := by
      intro e
      rw [← e] at hc
      simp at hc
      omega
    simp [a, h1, Matrix.one_apply_ne h2]
  let R := rowGL n a hu
  have hRlast : ∀ c, (R : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) c = Bi (Fin.last n) c := by
    intro c
    show rowM n a _ _ = _
    rw [rowM_apply]
    simp [a]
  have hR : R ∈ congGL k s hs (n + 1) := rowGL_mem s hs n a hu hv ha
  have hx : R * B ∈ Mir k n := by
    rw [mem_Mir_iff]
    funext c
    have e : (Bi * (B : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) = 1 := by
      rw [hBi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e2 := congrFun (congrFun e (Fin.last n)) c
    rw [Matrix.mul_apply] at e2
    rw [Units.val_mul, Matrix.mul_apply]
    simp only [hRlast]
    rw [e2]
    simp [eLast, Pi.single_apply, Matrix.one_apply, eq_comm]
  refine ⟨A * R⁻¹, R * B, ?_, hx, (congGL k s hs (n + 1)).mul_mem hR hB, ?_, ?_⟩
  · have : A * R⁻¹ = M * (R * B)⁻¹ := by rw [hMAB]; group
    rw [this]
    exact (Mir k n).mul_mem hM ((Mir k n).inv_mem hx)
  · rw [hMAB]; group
  · intro r c hr hc
    have e : ((R⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = rowM n (-(1 + a (Fin.last n))⁻¹ • a) := rfl
    have e1 : ∀ l, rowM n (-(1 + a (Fin.last n))⁻¹ • a) l c = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) l c := by
      intro l
      rw [rowM_apply]
      simp [ha0 c hc]
    rw [Units.val_mul, e, Matrix.mul_apply]
    simp only [e1]
    simp [Matrix.one_apply, hA r c hr hc]

end Core2

theorem near_block {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : kˣ) {n : ℕ} (g : Mir k n)
    (hg : NearOne s ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) :
    NearOne s ((mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro a b
  have h := hg (Fin.castSucc a) (Fin.castSucc b)
  have e : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.castSucc b) =
      (1 : Matrix (Fin n) (Fin n) k) a b := by
    simp [Matrix.one_apply]
  rw [e] at h
  exact h

theorem mirProj_mem_cong {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : kˣ) (hs : valuation k (s : k) ≤ 1) {n : ℕ} (g : Mir k n) (hg : g ∈ congM k s hs n) :
    mirabolicProjection k n g ∈ congGL k s hs n := by
  refine ⟨near_block s g hg.1, ?_⟩
  rw [← map_inv]
  exact near_block s g⁻¹ hg.2

theorem mirProj_sEmb {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (m : Mir k n) : mirabolicProjection k (n + 1) (sEmb k n m) = (m : GL (Fin (n + 1)) k) := by
  apply Units.ext
  ext a b
  show glEmbMat k (n + 1) ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.castSucc b) = _
  simp [glEmbMat]

theorem mirProj_dEmb {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ) (d : Fin (t + 1) → k) : mirabolicProjection k ((i + 1) + t + 1) (dEmb k i t d) = 1 :=
  GlobalTheory.CompanionTheory.BZPhiPG.Grp.mirProj_eq_one_of_mem _ (Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩)

theorem mem_mirabolicParabolic_mul_cong : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (hs1 : ValuativeRel.valuation k (s : k) < 1)
    (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)) (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1))
    (κ : Mir k ((i + 1) + t + 1)) (hκ : κ ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t + 1))
    (e : dEmb k i t d * sEmb k ((i + 1) + t) m = h * κ),
  ∃ a ∈ MirabolicParabolic k (i + 1) t, ∃ x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t), m = a * x := by
  intro k _ _ _ _ i t s hs hs1 d m h hh κ hκ e
  have e1 := congrArg (mirabolicProjection k ((i + 1) + t + 1)) e
  rw [map_mul, map_mul, mirProj_dEmb, mirProj_sEmb, one_mul] at e1
  have hA : ∀ r c : Fin ((i + 1) + t + 1), i < r.val → c.val ≤ i →
      ((mirabolicProjection k ((i + 1) + t + 1) h : GL (Fin ((i + 1) + t + 1)) k) :
        Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) r c = 0 := by
    intro r c hr hc
    have := GlobalTheory.CompanionTheory.BZPhiPG.Grp.hpg_entry h hh (Fin.castSucc r) (by simpa using hr)
      (by have := r.isLt; simp; omega) ⟨c.val, by omega⟩
    exact this
  obtain ⟨a, x, ha, hx, hxc, hax, hent⟩ := core s hs hs1 (n := (i + 1) + t) (i := i) (by omega) _ _
    (m : GL (Fin ((i + 1) + t + 1)) k) m.2 e1 (mirProj_mem_cong s hs κ hκ) hA
  refine ⟨⟨a, ha⟩, (GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff k (i + 1) t _).2 ?_, ⟨x, hx⟩, hxc, Subtype.ext hax⟩
  intro b c
  apply hent
  · rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val]
    omega
  · rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val]
    have := c.isLt
    omega

end GlobalTheory.CompanionTheory.BZPhiPG.Onto.Key1

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentCongruenceFactorizationStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_congruence_factorization : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (hs1 : ValuativeRel.valuation k (s : k) < 1)
    (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)) (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1))
    (κ : Mir k ((i + 1) + t + 1)) (hκ : κ ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t + 1))
    (e : dEmb k i t d * sEmb k ((i + 1) + t) m = h * κ),
  ∃ a ∈ MirabolicParabolic k (i + 1) t, ∃ x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t), m = a * x := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Onto.Key1.mem_mirabolicParabolic_mul_cong | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.Key1.mem_mirabolicParabolic_mul_cong | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Onto.Key1.mem_mirabolicParabolic_mul_cong <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameStabilizerFlagConverse
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameStabilizerFlagConverse
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin.BdU

theorem gram_apply {L : Type} [CommRing L] (s : L →+* L) {a b c : Type} [Fintype a]
    (M : Matrix a b L) (H : Matrix a a L) (N : Matrix a c L) (i : b) (j : c) :
    (cT s M * H * N) i j = ∑ k, ∑ l, s (M k i) * H k l * N l j := by
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem cT_cT_self {L : Type} [CommRing L] (s : L →+* L) (hs : ∀ x, s (s x) = x) {a b : Type}
    (M : Matrix a b L) : cT s (cT s M) = M := by
  ext i j
  simp [cT, hs]

theorem gram_bd {ι L : Type} [Fintype ι] [CommRing L] (s : L →+* L) (b : ι → ℤ)
    (G H : Matrix ι ι L) (hG : G.BlockTriangular b) (hH : ∀ u v, H u v ≠ 0 → b u + b v = 0)
    (hGH : cT s G * H * G = H) : cT s (bd b G) * H * bd b G = H := by
  ext i j
  have e := congrFun (congrFun hGH i) j
  rw [gram_apply] at e ⊢
  by_cases hij : b i + b j = 0
  · rw [← e]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    simp only [bd, Matrix.of_apply]
    by_cases hGki : G k i = 0
    · simp [hGki]
    by_cases hGlj : G l j = 0
    · simp [hGlj]
    by_cases hHkl : H k l = 0
    · simp [hHkl]
    have h1 := hH k l hHkl
    have h2 : ¬ b i < b k := fun hlt => hGki (hG hlt)
    have h3 : ¬ b j < b l := fun hlt => hGlj (hG hlt)
    have hk : b k = b i := by omega
    have hl : b l = b j := by omega
    simp [hk, hl]
  · have hHij : H i j = 0 := by
      by_contra hne
      exact hij (hH i j hne)
    rw [hHij]
    refine Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ => ?_))
    simp only [bd, Matrix.of_apply]
    by_cases hk : b k = b i
    · by_cases hl : b l = b j
      · have hHkl : H k l = 0 := by
          by_contra hne
          have := hH k l hne
          exact hij (by omega)
        simp [hHkl]
      · simp [hl]
    · simp [hk]

theorem levi_unitary {ι L : Type} [Fintype ι] [DecidableEq ι] [Field L] (s : L →+* L) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) L) (Q : Matrix (Fin n) ι L) (Qi : Matrix ι (Fin n) L) (b : ι → ℤ)
    (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (hH : ∀ u v, (cT s Q * J * Q) u v ≠ 0 → b u + b v = 0)
    (g : Matrix (Fin n) (Fin n) L) (hg : IsUnit g) (hgJ : cT s g * J * g = J)
    (hB : (Qi * g * Q).BlockTriangular b) :
    IsUnit (Q * bd b (Qi * g * Q) * Qi) ∧
      cT s (Q * bd b (Qi * g * Q) * Qi) * J * (Q * bd b (Qi * g * Q) * Qi) = J := by
  have cTm : ∀ {a b c : Type} [Fintype b] (A : Matrix a b L) (B : Matrix b c L),
      cT s (A * B) = cT s B * cT s A := by
    intro a b c _ A B
    unfold Formalism.UG.cT
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have cT1 : cT s (1 : Matrix (Fin n) (Fin n) L) = 1 := by
    unfold Formalism.UG.cT
    rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]
  have hQQ : cT s Qi * cT s Q = 1 := by rw [← cTm, h2, cT1]
  have hGu : cT s (Qi * g * Q) * (cT s Q * J * Q) * (Qi * g * Q) = cT s Q * J * Q := by
    calc cT s (Qi * g * Q) * (cT s Q * J * Q) * (Qi * g * Q)
        = cT s Q * (cT s g * ((cT s Qi * cT s Q) * (J * ((Q * Qi) * (g * Q))))) := by
          rw [cTm, cTm]
          simp only [Matrix.mul_assoc]
      _ = cT s Q * ((cT s g * J * g) * Q) := by
          rw [hQQ, h2, Matrix.one_mul, Matrix.one_mul]
          simp only [Matrix.mul_assoc]
      _ = cT s Q * J * Q := by rw [hgJ, Matrix.mul_assoc]
  have hbdu := gram_bd s b (Qi * g * Q) (cT s Q * J * Q) hB hH hGu
  obtain ⟨u, hu⟩ := hg
  have hGunit : IsUnit (Qi * g * Q) := by
    refine ⟨⟨Qi * g * Q, Qi * (↑u⁻¹ : Matrix (Fin n) (Fin n) L) * Q, ?_, ?_⟩, rfl⟩
    · calc Qi * g * Q * (Qi * (↑u⁻¹ : Matrix (Fin n) (Fin n) L) * Q) = Qi * (g * (Q * Qi) * (↑u⁻¹ : Matrix (Fin n) (Fin n) L)) * Q := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, ← hu, Units.mul_inv, Matrix.mul_one, h1]
    · calc Qi * (↑u⁻¹ : Matrix (Fin n) (Fin n) L) * Q * (Qi * g * Q) = Qi * ((↑u⁻¹ : Matrix (Fin n) (Fin n) L) * (Q * Qi) * g) * Q := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, ← hu, Units.inv_mul, Matrix.mul_one, h1]
  have hbdtri : (bd b (Qi * g * Q)).BlockTriangular b := by
    intro i j hij
    simp only [bd, Matrix.of_apply]
    rw [if_neg (ne_of_gt hij)]
  have hdet : (bd b (Qi * g * Q)).det = (Qi * g * Q).det := by
    rw [hbdtri.det, hB.det]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    congr 1
    ext i j
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, bd]
    rw [if_pos (i.2.trans j.2.symm)]
  have hbdunit : IsUnit (bd b (Qi * g * Q)) := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet, ← Matrix.isUnit_iff_isUnit_det]
    exact hGunit
  obtain ⟨w, hw⟩ := hbdunit
  refine ⟨⟨⟨Q * (↑w : Matrix ι ι L) * Qi, Q * (↑w⁻¹ : Matrix ι ι L) * Qi, ?_, ?_⟩, ?_⟩, ?_⟩
  · calc Q * (↑w : Matrix ι ι L) * Qi * (Q * (↑w⁻¹ : Matrix ι ι L) * Qi) = Q * ((↑w : Matrix ι ι L) * (Qi * Q) * (↑w⁻¹ : Matrix ι ι L)) * Qi := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, Units.mul_inv, Matrix.mul_one, h2]
  · calc Q * (↑w⁻¹ : Matrix ι ι L) * Qi * (Q * (↑w : Matrix ι ι L) * Qi) = Q * ((↑w⁻¹ : Matrix ι ι L) * (Qi * Q) * (↑w : Matrix ι ι L)) * Qi := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, Units.inv_mul, Matrix.mul_one, h2]
  · show Q * (↑w : Matrix ι ι L) * Qi = Q * bd b (Qi * g * Q) * Qi
    rw [hw]
  · calc cT s (Q * bd b (Qi * g * Q) * Qi) * J * (Q * bd b (Qi * g * Q) * Qi)
        = cT s Qi * ((cT s (bd b (Qi * g * Q)) * (cT s Q * J * Q) * bd b (Qi * g * Q)) * Qi) := by
          rw [cTm, cTm]
          simp only [Matrix.mul_assoc]
      _ = cT s Qi * ((cT s Q * J * Q) * Qi) := by rw [hbdu]
      _ = (cT s Qi * cT s Q) * J * (Q * Qi) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hQQ, h2, Matrix.one_mul, Matrix.mul_one]

theorem gram_frm_degree {L : Type} [Field L] (s : L →+* L) (hs : ∀ x, s (s x) = x) {n r m : ℕ}
    (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L)
    (hJ : cT s J = J) (hXX : cT s X * J * X = 0) (hYY : cT s Y * J * Y = 0)
    (hXY : cT s X * J * Y = 1) (hXZ : cT s X * J * Z = 0) (hYZ : cT s Y * J * Z = 0)
    (S : Finset (Fin r)) (u v : Idx r m)
    (h : (cT s (frm X Z Y) * J * frm X Z Y) u v ≠ 0) : lev m S u + lev m S v = 0 := by
  have cTm : ∀ {a b c : Type} [Fintype b] (A : Matrix a b L) (B : Matrix b c L),
      cT s (A * B) = cT s B * cT s A := by
    intro a b c _ A B
    unfold Formalism.UG.cT
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have cT1 : cT s (1 : Matrix (Fin r) (Fin r) L) = 1 := by
    unfold Formalism.UG.cT
    rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]
  have cT0 : ∀ {a b : Type}, cT s (0 : Matrix a b L) = 0 := by
    intro a b
    unfold Formalism.UG.cT
    ext i j
    simp
  have hYX : cT s Y * J * X = 1 := by
    have e := congrArg (cT s) hXY
    rw [cTm, cTm, cT_cT_self s hs, hJ, cT1, ← Matrix.mul_assoc] at e
    exact e
  have hZX : cT s Z * J * X = 0 := by
    have e := congrArg (cT s) hXZ
    rw [cTm, cTm, cT_cT_self s hs, hJ, cT0, ← Matrix.mul_assoc] at e
    exact e
  have hZY : cT s Z * J * Y = 0 := by
    have e := congrArg (cT s) hYZ
    rw [cTm, cTm, cT_cT_self s hs, hJ, cT0, ← Matrix.mul_assoc] at e
    exact e
  rcases u with i | i | i <;> rcases v with j | j | j
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inl i) (Sum.inl j) = (cT s X * J * X) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hXX] at h
    simp at h
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inl i) (Sum.inr (Sum.inl j)) = (cT s X * J * Z) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hXZ] at h
    simp at h
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inl i) (Sum.inr (Sum.inr j)) = (cT s X * J * Y) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hXY] at h
    have hij : i = j := by
      by_contra hne
      exact h (Matrix.one_apply_ne hne)
    subst hij
    show (cnt S i - (S.card : ℤ)) + ((S.card : ℤ) - cnt S i) = 0
    ring
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inl i)) (Sum.inl j) = (cT s Z * J * X) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hZX] at h
    simp at h
  · show (0 : ℤ) + 0 = 0
    rfl
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j)) = (cT s Z * J * Y) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hZY] at h
    simp at h
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inr i)) (Sum.inl j) = (cT s Y * J * X) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hYX] at h
    have hij : i = j := by
      by_contra hne
      exact h (Matrix.one_apply_ne hne)
    subst hij
    show ((S.card : ℤ) - cnt S i) + (cnt S i - (S.card : ℤ)) = 0
    ring
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) = (cT s Y * J * Z) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hYZ] at h
    simp at h
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) = (cT s Y * J * Y) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hYY] at h
    simp at h

theorem bd_unitary : ∀ (L : Type) [Field L] (s : L →+* L), (∀ x, s (s x) = x) → ∀ (n r m : ℕ) (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L), cT s J = J → cT s X * J * X = 0 → cT s Y * J * Y = 0 → cT s X * J * Y = 1 → cT s X * J * Z = 0 → cT s Y * J * Z = 0 → Qi * frm X Z Y = 1 → frm X Z Y * Qi = 1 → ∀ (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L), IsUnit g → cT s g * J * g = J → (Qi * g * frm X Z Y).BlockTriangular (lev m S) → IsUnit (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) ∧ cT s (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) * J * (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) = J := by
  intro L _ s hs n r m J X Y Z Qi hJ hXX hYY hXY hXZ hYZ h1 h2 S g hg hgJ hB
  exact levi_unitary s J (frm X Z Y) Qi (lev m S) h1 h2
    (fun u v h => gram_frm_degree s hs J X Y Z hJ hXX hYY hXY hXZ hYZ S u v h) g hg hgJ hB

end GlobalTheory.CompanionTheory.CFin.BdU

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameStabilizerFlagConverseStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_stabilizer_flag_converse : ∀ (L : Type) [Field L] (s : L →+* L), (∀ x, s (s x) = x) → ∀ (n r m : ℕ) (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L), cT s J = J → cT s X * J * X = 0 → cT s Y * J * Y = 0 → cT s X * J * Y = 1 → cT s X * J * Z = 0 → cT s Y * J * Z = 0 → Qi * frm X Z Y = 1 → frm X Z Y * Qi = 1 → ∀ (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L), IsUnit g → cT s g * J * g = J → (Qi * g * frm X Z Y).BlockTriangular (lev m S) → IsUnit (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) ∧ cT s (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) * J * (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) = J := by
  first | exact @GlobalTheory.CompanionTheory.CFin.BdU.bd_unitary | exact GlobalTheory.CompanionTheory.CFin.BdU.bd_unitary | (intros; apply GlobalTheory.CompanionTheory.CFin.BdU.bd_unitary <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionOpenCellAltBis
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnRowM
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Chart

open GlobalTheory.CompanionTheory.BZPhiPG.Cells

section Alg

variable {k : Type} [Field k]

def rowM {ι : Type} [DecidableEq ι] (ρ : ι → k) (c j : ι) : Matrix ι ι k :=
  ((1 : Matrix ι ι k).updateRow c ρ).submatrix (Equiv.swap c j) id

theorem rowM_det_ne {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ι → k) (c j : ι) (hc : ρ c ≠ 0) :
    (rowM ρ c j).det ≠ 0 := by
  have hT : ((1 : Matrix ι ι k).updateRow c ρ).det = ρ c := by
    have h := Matrix.cramer_transpose_apply (1 : Matrix ι ι k) ρ c
    rw [Matrix.transpose_one, Matrix.cramer_one] at h
    simpa using h.symm
  have h := Matrix.det_permute (Equiv.swap c j) ((1 : Matrix ι ι k).updateRow c ρ)
  have h2 : (rowM ρ c j).det = _ := h
  rw [h2, hT]
  refine mul_ne_zero ?_ hc
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap c j)) with e | e <;> simp [e]

theorem rowM_row {ι : Type} [DecidableEq ι] (ρ : ι → k) (c j : ι) : rowM ρ c j j = ρ := by
  ext x
  show ((1 : Matrix ι ι k).updateRow c ρ) (Equiv.swap c j j) x = ρ x
  simp

theorem rowM_zero {ι : Type} [DecidableEq ι] (s : ι → Prop) (ρ : ι → k) (c j : ι) (hc : s c) (hj : s j)
    (r x : ι) (hr : ¬ s r) (hx : s x) : rowM ρ c j r x = 0 := by
  have hrc : r ≠ c := fun e => hr (e ▸ hc)
  have hrj : r ≠ j := fun e => hr (e ▸ hj)
  have hrx : r ≠ x := fun e => hr (e ▸ hx)
  show ((1 : Matrix ι ι k).updateRow c ρ) (Equiv.swap c j r) x = 0
  rw [Equiv.swap_apply_of_ne_of_ne hrc hrj, Matrix.updateRow_ne hrc, Matrix.one_apply_ne hrx]


open Classical in
def rowB {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ι → k) (c j : ι) : GL ι k :=
  if h : (rowM ρ c j).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero _ h else 1

theorem rowB_val {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ι → k) (c j : ι) (hc : ρ c ≠ 0) :
    (rowB ρ c j).val = rowM ρ c j := by
  rw [rowB, dif_pos (rowM_det_ne ρ c j hc)]
  rfl

end Alg

section Top

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]

theorem continuousOn_GL {X ι : Type} [TopologicalSpace X] [Fintype ι] [DecidableEq ι] (f : X → GL ι k) (V : Set X)
    (hf : ContinuousOn (fun x => (f x).val) V) : ContinuousOn f V := by
  rw [continuousOn_iff_continuous_restrict] at hf ⊢
  refine Units.continuous_iff.2 ⟨hf, ?_⟩
  have hdet : Continuous fun x : V => ((f x).val).det := hf.matrix_det
  have hne : ∀ x : V, ((f x).val).det ≠ 0 := fun x => (Matrix.GeneralLinearGroup.det (f x)).ne_zero
  have e : (fun x : V => (((f x)⁻¹ : GL ι k)).val) = fun x : V => (((f x).val).det)⁻¹ • ((f x).val).adjugate := by
    funext x
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
  show Continuous (fun x : V => (((f x)⁻¹ : GL ι k)).val)
  rw [e]
  exact (hdet.inv₀ hne).smul hf.matrix_adjugate

theorem continuousOn_rowM {X ι : Type} [TopologicalSpace X] [DecidableEq ι] (ρ : X → ι → k) (c j : ι)
    (hρ : Continuous ρ) : Continuous fun x => rowM (ρ x) c j := by
  refine continuous_matrix fun a b => ?_
  show Continuous fun x => ((1 : Matrix ι ι k).updateRow c (ρ x)) (Equiv.swap c j a) b
  by_cases h : Equiv.swap c j a = c
  · simp only [h, Matrix.updateRow_self]
    exact (continuous_apply b).comp hρ
  · simp only [Matrix.updateRow_ne h]
    exact continuous_const

end Top

section Group

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem core' (i t : ℕ) (p : Mir k ((i + 1) + t + 1)) (X B : GL (Fin ((i + 1) + t + 1)) k) (j : Fin ((i + 1) + t + 1))
    (hX : X.val j = eLast k ((i + 1) + t))
    (hBj : B.val j = (mirabolicProjection k _ p⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val (Fin.last ((i + 1) + t)))
    (hB : ∀ r x : Fin ((i + 1) + t + 1), ¬ r.val < i + 1 → x.val < i + 1 → B.val r x = 0) :
    ∃ hM : (X⁻¹ * B * mirabolicProjection k _ p) ∈ Mir k ((i + 1) + t), ∃ h ∈ HPG k (i + 1) (t + 1), ∃ (d : Fin (t + 1) → k),
      p = h * dEmb k i t d * levi k _ X * sEmb k ((i + 1) + t) ⟨_, hM⟩ := by
  set g : GL (Fin ((i + 1) + t + 1)) k := mirabolicProjection k _ p with hg
  have hginv : mirabolicProjection k _ p⁻¹ = g⁻¹ := map_inv _ _
  rw [hginv] at hBj
  have hM : (X⁻¹ * B * g) ∈ Mir k ((i + 1) + t) := by
    have h1 : (g⁻¹ * (B⁻¹ * X)) ∈ Mir k ((i + 1) + t) := by
      rw [mem_Mir_iff, Units.val_mul, Matrix.mul_apply_eq_vecMul, ← hBj, ← Matrix.mul_apply_eq_vecMul, ← Units.val_mul,
        mul_inv_cancel_left, hX]
    have h2 := (Mir k ((i + 1) + t)).inv_mem h1
    simpa [mul_assoc] using h2
  let v : Fin ((i + 1) + (t + 1)) → k := fun r =>
    (p : GL (Fin ((i + 1) + t + 1 + 1)) k).val (Fin.castSucc r) (Fin.last _)
  let v' : Fin ((i + 1) + (t + 1)) → k := B.val.mulVec v
  let a : Fin ((i + 1) + (t + 1)) → k := Fin.append (fun x => v' (Fin.castAdd (t + 1) x)) (0 : Fin (t + 1) → k)
  let d : Fin (t + 1) → k := fun x => v' (Fin.natAdd (i + 1) x)
  let b : Fin ((i + 1) + (t + 1)) → k := Fin.append (0 : Fin (i + 1) → k) d
  have hsum : a + b = v' := by
    funext x
    induction x using Fin.addCases with
    | left x => simp [a, b]
    | right x => simp [a, b, d]
  let ua : Mir k ((i + 1) + t + 1) := ⟨unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd a), MirU_le_Mir k _ ⟨_, rfl⟩⟩
  have hua : ua ∈ HPG k (i + 1) (t + 1) := by
    refine mem_HPG_of (I := i + 1) (T := t + 1) ua ?_ ?_
    · intro x y
      refine unip_castSucc_castSucc _ a _ _ ?_
      intro e
      have := congrArg Fin.val e
      simp only at this
      omega
    · intro x
      refine (unip_apply_castSucc_last k _ _ _).trans ?_
      show a (Fin.natAdd (i + 1) x) = 0
      simp [a]
  have hlB : levi k _ B⁻¹ ∈ HPG k (i + 1) (t + 1) := by
    have : levi k _ B ∈ HPG k (i + 1) (t + 1) := by
      refine mem_HPG_of (I := i + 1) (T := t + 1) _ ?_ ?_
      · intro x y
        refine (glEmb_castSucc_castSucc _ B _ _).trans ?_
        exact hB _ _ (by simp; omega) (by simp; omega)
      · intro x
        exact glEmb_castSucc_last _ B _
    rw [map_inv]
    exact (HPG k (i + 1) (t + 1)).inv_mem this
  refine ⟨hM, levi k _ B⁻¹ * ua, (HPG k (i + 1) (t + 1)).mul_mem hlB hua, d, ?_⟩
  apply Subtype.ext
  have hp : (p : GL (Fin ((i + 1) + t + 1 + 1)) k) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) * glEmb k _ g := eq_unip_glEmb p
  have e1 : unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) *
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v') := by
    rw [← map_mul, ← ofAdd_add, hsum]
  have e2 : glEmb k _ B * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v') * glEmb k _ B := glEmb_mul_unip' k _ B _
  have e3 : glEmb k _ X * glEmb k _ (X⁻¹ * B * g) = glEmb k _ B * glEmb k _ g := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  show (p : GL (Fin ((i + 1) + t + 1 + 1)) k) = glEmb k _ B⁻¹ * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) *
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b) *
      glEmb k _ X * glEmb k _ (X⁻¹ * B * g)
  calc (p : GL (Fin ((i + 1) + t + 1 + 1)) k)
      = (glEmb k _ B)⁻¹ * (glEmb k _ B * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v)) * glEmb k _ g := by
        rw [hp]; group
    _ = (glEmb k _ B)⁻¹ * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v') * (glEmb k _ B * glEmb k _ g) := by
        rw [e2]; simp only [mul_assoc]
    _ = _ := by
        rw [← e3, ← e1, map_inv]; simp only [mul_assoc]

end Group

theorem chart :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ)
      (p₀ : Mir k ((i + 1) + t + 1)), p₀ ∉ Cl k i t →
  ∃ V ∈ nhds p₀, ∃ μ : Mir k ((i + 1) + t + 1) → Mir k ((i + 1) + t), ContinuousOn μ V ∧
    ∀ p ∈ V, ∃ h ∈ HPG k (i + 1) (t + 1), ∃ d : Fin (t + 1) → k,
      p = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) (μ p) := by
  classical
  intro k _ _ _ _ i t p₀ h₀
  have hp' : ¬ _ := fun h => h₀ ((Cl_iff i t p₀).2 h)
  push_neg at hp'
  obtain ⟨c, hcs, hc⟩ := hp'
  have hj : (piPerm i t (Fin.last ((i + 1) + t))).val < i + 1 := by rw [piPerm_last_val]; omega
  set j := piPerm i t (Fin.last ((i + 1) + t)) with hjdef
  let ρ : Mir k ((i + 1) + t + 1) → Fin ((i + 1) + t + 1) → k := fun p =>
    (mirabolicProjection k _ p⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val (Fin.last ((i + 1) + t))
  have hG : Continuous fun p : Mir k ((i + 1) + t + 1) => mirabolicProjection k _ p :=
    GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k _
  have hρ : Continuous ρ := by
    have hv : Continuous fun p : Mir k ((i + 1) + t + 1) =>
        ((mirabolicProjection k _ p⁻¹ : GL (Fin ((i + 1) + t + 1)) k) : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) :=
      Units.continuous_val.comp (hG.comp continuous_inv)
    exact continuous_pi fun x => hv.matrix_elem _ _
  let V : Set (Mir k ((i + 1) + t + 1)) := {p | ρ p c ≠ 0}
  have hV : IsOpen V := isOpen_ne_fun ((continuous_apply c).comp hρ) continuous_const
  let W : Mir k ((i + 1) + t + 1) → GL (Fin ((i + 1) + t + 1)) k := fun p =>
    (wGL k i t)⁻¹ * rowB (ρ p) c j * mirabolicProjection k _ p
  let μ : Mir k ((i + 1) + t + 1) → Mir k ((i + 1) + t) := fun p =>
    if h : W p ∈ Mir k ((i + 1) + t) then ⟨W p, h⟩ else 1
  have key : ∀ p ∈ V, ∃ hM : W p ∈ Mir k ((i + 1) + t), ∃ h ∈ HPG k (i + 1) (t + 1), ∃ d : Fin (t + 1) → k,
      p = h * dEmb k i t d * levi k _ (wGL k i t) * sEmb k ((i + 1) + t) ⟨_, hM⟩ := by
    intro p hp
    refine core' i t p (wGL k i t) (rowB (ρ p) c j) j (wGL_row i t) ?_ ?_
    · rw [rowB_val _ _ _ hp, rowM_row]
    · intro r x hr hx
      rw [rowB_val _ _ _ hp]
      exact rowM_zero (fun x : Fin ((i + 1) + t + 1) => x.val < i + 1) _ c j hcs hj r x hr hx
  refine ⟨V, hV.mem_nhds hc, μ, ?_, ?_⟩
  · have hB : ContinuousOn (fun p => rowB (ρ p) c j) V := by
      refine continuousOn_GL _ _ ?_
      refine (continuousOn_rowM ρ c j hρ).continuousOn.congr ?_
      intro p hp
      exact rowB_val _ _ _ hp
    have hW : ContinuousOn W V :=
      (continuousOn_const.mul hB).mul hG.continuousOn
    refine (Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_iff).2 ?_
    refine hW.congr ?_
    intro p hp
    obtain ⟨hM, -⟩ := key p hp
    show ((μ p : Mir k ((i + 1) + t)) : GL _ k) = W p
    simp only [μ, dif_pos hM]
  · intro p hp
    obtain ⟨hM, h, hh, d, e⟩ := key p hp
    refine ⟨h, hh, d, ?_⟩
    have hμ : μ p = ⟨W p, hM⟩ := dif_pos hM
    rw [hμ]
    exact e

end GlobalTheory.CompanionTheory.BZPhiPG.Chart

end
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_local_section_of_not_mem_Cl : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (p₀ : Mir k ((i + 1) + t + 1)), p₀ ∉ Cl k i t →
  ∃ V ∈ nhds p₀, ∃ μ : Mir k ((i + 1) + t + 1) → Mir k ((i + 1) + t), ContinuousOn μ V ∧
    ∀ p ∈ V, ∃ h ∈ HPG k (i + 1) (t + 1), ∃ d : Fin (t + 1) → k,
      p = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) (μ p) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Chart.chart | exact GlobalTheory.CompanionTheory.BZPhiPG.Chart.chart | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Chart.chart <;> assumption)
end
