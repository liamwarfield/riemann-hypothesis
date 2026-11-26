module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.RowFlagIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedCore

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FrameMemSG
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSGIffFlagC
noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3

variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] {m : ℕ}

def FlagC (M : Matrix n n K) (v : Fin m → n → K) : Prop :=
  ∀ b, M *ᵥ v b - v b ∈ Submodule.span K (v '' {a | a < b})

theorem span_mulVec (M : Matrix n n K) {w : n → K} {S : Set (n → K)} (h : w ∈ Submodule.span K S) :
    M *ᵥ w ∈ Submodule.span K ((fun u => M *ᵥ u) '' S) := by
  have e : (fun u => M *ᵥ u) = ⇑(Matrix.mulVecLin M) := rfl
  rw [e, Submodule.span_image]
  exact Submodule.mem_map_of_mem h

theorem flagC_conj_imp (P Pi M : Matrix n n K) (hP : Pi * P = 1) (v : Fin m → n → K) (h : FlagC M v) :
    FlagC (P * M * Pi) (fun b => P *ᵥ v b) := by
  intro b
  have h1 : (P * M * Pi) *ᵥ (P *ᵥ v b) - P *ᵥ v b = P *ᵥ (M *ᵥ v b - v b) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hP, Matrix.mul_one, Matrix.mulVec_sub,
      Matrix.mulVec_mulVec]
  rw [h1]
  have h2 := span_mulVec P (h b)
  rwa [Set.image_image] at h2

theorem flagC_conj (P Pi M : Matrix n n K) (hP : Pi * P = 1) (hP' : P * Pi = 1) (v : Fin m → n → K) :
    FlagC (P * M * Pi) (fun b => P *ᵥ v b) ↔ FlagC M v := by
  refine ⟨fun h => ?_, flagC_conj_imp P Pi M hP v⟩
  have h2 := flagC_conj_imp Pi P (P * M * Pi) hP' (fun b => P *ᵥ v b) h
  have e1 : Pi * (P * M * Pi) * P = M := by
    simp only [← Matrix.mul_assoc, hP, Matrix.one_mul]
    rw [Matrix.mul_assoc, hP, Matrix.mul_one]
  have e2 : (fun b => Pi *ᵥ (P *ᵥ v b)) = v := by
    funext b
    rw [Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
  rw [e1, e2] at h2
  exact h2

theorem span_smul_eq (c : Fin m → K) (hc : ∀ b, c b ≠ 0) (v : Fin m → n → K) (s : Set (Fin m)) :
    Submodule.span K ((fun b => c b • v b) '' s) = Submodule.span K (v '' s) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have e : v b = (c b)⁻¹ • (c b • v b) := by rw [smul_smul, inv_mul_cancel₀ (hc b), one_smul]
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)

theorem flagC_smul (M : Matrix n n K) (c : Fin m → K) (hc : ∀ b, c b ≠ 0) (v : Fin m → n → K) :
    FlagC M (fun b => c b • v b) ↔ FlagC M v := by
  unfold FlagC
  simp only [span_smul_eq c hc v, Matrix.mulVec_smul, ← smul_sub]
  refine forall_congr' (fun b => ⟨fun h => ?_, fun h => Submodule.smul_mem _ _ h⟩)
  have h3 := Submodule.smul_mem _ (c b)⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ (hc b), one_smul] at h3

variable {r k : ℕ}

theorem colFlag_eq (M : Matrix (Idx r k) (Idx r k) K) :
    ColFlag M ↔ FlagC M (fun b => Pi.single (pe (k := k) b) (1 : K)) := Iff.rfl

theorem rowFlag_eq (M : Matrix (Idx r k) (Idx r k) K) :
    RowFlag M ↔ FlagC Mᵀ (fun b => Pi.single (pf (k := k) b) (1 : K)) := Iff.rfl

theorem mem_sG_iff_flagC (g : GL (Idx r k) K) :
    g ∈ sG K r k ↔ FlagC (g : Matrix (Idx r k) (Idx r k) K) (fun b => Pi.single (pe (k := k) b) (1 : K)) ∧
      FlagC ((g⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K)ᵀ (fun b => Pi.single (pf (k := k) b) (1 : K)) := by
  rw [mem_sG_iff_flags, ← colFlag_eq, ← rowFlag_eq, colFlag_iff, rowFlag_iff]

end MassDataIdxStIm
end
end

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3

variable {K : Type} [Field K] {r k : ℕ}

theorem frame_mem_sG (g1 Q : GL (Idx r k) K) (g2 J1 : Matrix (Idx r k) (Idx r k) K) (hJ : IsUnit J1.det)
    (hU : g2ᵀ * J1 * (g1 : Matrix (Idx r k) (Idx r k) K) = J1)
    (y1 y2 : Fin (r + 1) → Idx r k → K) (l : Fin (r + 1) → K) (hl : ∀ b, l b ≠ 0)
    (hy1 : ∀ b, ((Q⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) *ᵥ y1 b = Pi.single (pe b) 1)
    (hy2 : ∀ b, (Q : Matrix (Idx r k) (Idx r k) K)ᵀ *ᵥ (J1ᵀ *ᵥ y2 b) = l b • Pi.single (pf b) 1) :
    (FlagC (g1 : Matrix (Idx r k) (Idx r k) K) y1 ∧ FlagC g2 y2) ↔ Q⁻¹ * g1 * Q ∈ sG K r k := by
  set G1 : Matrix (Idx r k) (Idx r k) K := (g1 : Matrix (Idx r k) (Idx r k) K) with hG1
  set G1i : Matrix (Idx r k) (Idx r k) K := ((g1⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) with hG1i
  set Qm : Matrix (Idx r k) (Idx r k) K := (Q : Matrix (Idx r k) (Idx r k) K) with hQm
  set Qi : Matrix (Idx r k) (Idx r k) K := ((Q⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) with hQi
  have e1 : G1 * G1i = 1 := by rw [hG1, hG1i, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e1' : G1i * G1 = 1 := by rw [hG1, hG1i, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have eQ : Qm * Qi = 1 := by rw [hQm, hQi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have eQ' : Qi * Qm = 1 := by rw [hQm, hQi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hJt : IsUnit J1ᵀ.det := by rw [Matrix.det_transpose]; exact hJ
  have eJ : J1ᵀ⁻¹ * J1ᵀ = 1 := Matrix.nonsing_inv_mul _ hJt
  have eJ' : J1ᵀ * J1ᵀ⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJt
  have hS : ((Q⁻¹ * g1 * Q : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) = Qi * G1 * Qm := by
    simp [hQi, hG1, hQm, Units.val_mul]
  have hSi : (((Q⁻¹ * g1 * Q)⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) = Qi * G1i * Qm := by
    have : (Q⁻¹ * g1 * Q)⁻¹ = Q⁻¹ * g1⁻¹ * Q := by group
    rw [this]
    simp [hQi, hG1i, hQm, Units.val_mul]

  have hT : J1ᵀ * g2 * J1ᵀ⁻¹ = G1iᵀ := by
    have hUt : G1ᵀ * J1ᵀ * g2 = J1ᵀ := by
      have := congrArg Matrix.transpose hU
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
    have hit : G1iᵀ * G1ᵀ = 1 := by rw [← Matrix.transpose_mul, e1, Matrix.transpose_one]
    calc J1ᵀ * g2 * J1ᵀ⁻¹ = G1iᵀ * (G1ᵀ * J1ᵀ * g2) * J1ᵀ⁻¹ := by
          rw [← Matrix.mul_assoc G1iᵀ, ← Matrix.mul_assoc G1iᵀ, hit, Matrix.one_mul]
      _ = G1iᵀ := by rw [hUt, Matrix.mul_assoc, eJ', Matrix.mul_one]
  rw [mem_sG_iff_flagC, hS, hSi]
  refine and_congr ?_ ?_
  · rw [← flagC_conj Qi Qm G1 eQ eQ' y1]
    exact Iff.of_eq (congrArg _ (funext hy1))
  · rw [← flagC_conj J1ᵀ J1ᵀ⁻¹ g2 eJ eJ' y2, hT]
    have eQt : Qiᵀ * Qmᵀ = 1 := by rw [← Matrix.transpose_mul, eQ, Matrix.transpose_one]
    have eQt' : Qmᵀ * Qiᵀ = 1 := by rw [← Matrix.transpose_mul, eQ', Matrix.transpose_one]
    rw [← flagC_conj Qmᵀ Qiᵀ G1iᵀ eQt eQt' _]
    have hv : (fun b => Qmᵀ *ᵥ (J1ᵀ *ᵥ y2 b)) = fun b => l b • Pi.single (pf (k := k) b) (1 : K) := funext hy2
    rw [hv, flagC_smul _ l hl]
    have hm : Qmᵀ * G1iᵀ * Qiᵀ = (Qi * G1i * Qm)ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hm]

end MassDataIdxStIm
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondProjSplitMulVec
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FstMemSpan
noncomputable section

namespace MassDataIdxSpl

variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K) {n : Type}

def pr1 : (n → T) →ₗ[K] (n → K) where
  toFun v i := (θ (v i)).1
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp

def pr2 : (n → T) →ₗ[K] (n → K) where
  toFun v i := (θ (v i)).2
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp

theorem fst_apply_alt (v : n → T) (i : n) : pr1 θ v i = (θ (v i)).1 := rfl
theorem snd_apply_alt (v : n → T) (i : n) : pr2 θ v i = (θ (v i)).2 := rfl

variable {ι : Type} (Y : ι → n → T) (s : Set ι)

end MassDataIdxSpl
end
end

noncomputable section

namespace MassDataIdxSpl

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Matrix
open scoped TensorProduct

theorem firstProj_split_mulVec {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K) {n : Type}
    [Fintype n] (M : Matrix n n T) (v : n → T) :
    pr1 θ (M *ᵥ v) = (M.map fun t => (θ t).1) *ᵥ pr1 θ v := by
  ext i
  simp [pr1, Matrix.mulVec, dotProduct, Prod.fst_sum]

theorem secondProj_split_mulVec {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K) {n : Type}
    [Fintype n] (M : Matrix n n T) (v : n → T) :
    pr2 θ (M *ᵥ v) = (M.map fun t => (θ t).2) *ᵥ pr2 θ v := by
  ext i
  simp [pr2, Matrix.mulVec, dotProduct, Prod.snd_sum]

section Uni

variable {F E R : Type} [Field F] [Field E] [Algebra F E] [Field R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (θ : R ⊗[F] E ≃ₐ[R] R × R)

end Uni

end MassDataIdxSpl
end
end

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3 Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MassDataIdxSpl
open scoped TensorProduct

section Reindex

variable {K : Type} [Field K] {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] {m : ℕ}

end Reindex

section Split

variable {F E R : Type} [Field F] [Field E] [Algebra F E] [Field R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (θ : R ⊗[F] E ≃ₐ[R] R × R)

def cmp1 (g : HA R σ J) : Matrix (Fin n) (Fin n) R :=
  ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map (fun t => (θ t).1)

def cmp2 (g : HA R σ J) : Matrix (Fin n) (Fin n) R :=
  ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map (fun t => (θ t).2)

def jm1 : Matrix (Fin n) (Fin n) R := (JR R J).map (fun t => (θ t).1)

theorem cmp_unit (hθ : ∀ t, θ (sigR R σ t) = (θ t).swap) (g : HA R σ J) :
    (cmp2 σ J θ g)ᵀ * jm1 J θ * cmp1 σ J θ g = jm1 J θ := by
  have hg : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * JR R J * ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = JR R J := g.2
  let f1 : R ⊗[F] E →+* R := (RingHom.fst R R).comp θ.toRingEquiv.toRingHom
  have h1 := congrArg (fun M => Matrix.map M f1) hg
  simp only [Matrix.map_mul] at h1
  have e1 : (Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))).map f1 = (cmp2 σ J θ g)ᵀ := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply]
    show (θ (sigR R σ (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) j i))).1 = (θ (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) j i)).2
    rw [hθ]
    rfl
  rw [e1] at h1
  exact h1

private theorem mem_span_image_iff_pr1_pr2_mem_span {ι : Type} [Fintype ι] (s : Set ι) (u : ι → Fin n → R ⊗[F] E)
    (w : Fin n → R ⊗[F] E) :
    w ∈ Submodule.span (R ⊗[F] E) (u '' s) ↔
      pr1 θ w ∈ Submodule.span R ((fun i => pr1 θ (u i)) '' s) ∧
      pr2 θ w ∈ Submodule.span R ((fun i => pr2 θ (u i)) '' s) := by
  classical
  have h1 : ∀ (c : R ⊗[F] E) (v : Fin n → R ⊗[F] E), pr1 θ (c • v) = (θ c).1 • pr1 θ v := by
    intro c v
    funext i
    show (θ (c * v i)).1 = (θ c).1 * (θ (v i)).1
    rw [map_mul]
    rfl
  have h2 : ∀ (c : R ⊗[F] E) (v : Fin n → R ⊗[F] E), pr2 θ (c • v) = (θ c).2 • pr2 θ v := by
    intro c v
    funext i
    show (θ (c * v i)).2 = (θ c).2 * (θ (v i)).2
    rw [map_mul]
    rfl
  have hinj : ∀ x y : Fin n → R ⊗[F] E, pr1 θ x = pr1 θ y → pr2 θ x = pr2 θ y → x = y := by
    intro x y hx hy
    funext i
    apply θ.injective
    exact Prod.ext (congrFun hx i) (congrFun hy i)
  simp only [Set.image_eq_range, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨⟨fun i => (θ (c i)).1, ?_⟩, ⟨fun i => (θ (c i)).2, ?_⟩⟩
    · rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact (h1 (c i) (u ↑i)).symm
    · rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact (h2 (c i) (u ↑i)).symm
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨fun i => θ.symm (a i, b i), ?_⟩
    apply hinj
    · rw [map_sum]
      simp only [h1, AlgEquiv.apply_symm_apply]
      exact ha
    · rw [map_sum]
      simp only [h2, AlgEquiv.apply_symm_apply]
      exact hb

private theorem pr1_lin_eq_cmp1_mulVec (g : HA R σ J) (v : Fin n → R ⊗[F] E) :
    pr1 θ (lin R σ J g v) = cmp1 σ J θ g *ᵥ pr1 θ v := by
  have hp : ∀ (w : Fin n → R ⊗[F] E) (k : Fin n), pr1 θ w k = (θ (w k)).1 := fun _ _ => rfl
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hp, lin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, cmp1, Matrix.map_apply,
    map_sum, Prod.fst_sum, map_mul, Prod.fst_mul]

private theorem pr2_lin_eq_cmp2_mulVec (g : HA R σ J) (v : Fin n → R ⊗[F] E) :
    pr2 θ (lin R σ J g v) = cmp2 σ J θ g *ᵥ pr2 θ v := by
  have hp : ∀ (w : Fin n → R ⊗[F] E) (k : Fin n), pr2 θ w k = (θ (w k)).2 := fun _ _ => rfl
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hp, lin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, cmp2, Matrix.map_apply,
    map_sum, Prod.snd_sum, map_mul, Prod.snd_mul]

theorem mem_Ssub_iff_flagC {r : ℕ} (P : Frame E n r) (g : HA R σ J) :
    g ∈ Ssub R σ J P ↔ FlagC (cmp1 σ J θ g) (fun b => pr1 θ (ratV (F := F) R (F0 P b))) ∧
      FlagC (cmp2 σ J θ g) (fun b => pr2 θ (ratV (F := F) R (F0 P b))) := by
  have hm : g ∈ Ssub R σ J P ↔ UniC R σ J (F0 P) g := Iff.rfl
  rw [hm]
  unfold UniC FlagC
  rw [← forall_and]
  apply forall_congr'
  intro b
  show lin R σ J g (ratV (F := F) R (F0 P b)) - ratV (F := F) R (F0 P b) ∈ spanR (F := F) R (F0 P) {a | a < b} ↔
    (cmp1 σ J θ g *ᵥ pr1 θ (ratV (F := F) R (F0 P b)) - pr1 θ (ratV (F := F) R (F0 P b)) ∈
      Submodule.span R ((fun c => pr1 θ (ratV (F := F) R (F0 P c))) '' {a | a < b})) ∧
    (cmp2 σ J θ g *ᵥ pr2 θ (ratV (F := F) R (F0 P b)) - pr2 θ (ratV (F := F) R (F0 P b)) ∈
      Submodule.span R ((fun c => pr2 θ (ratV (F := F) R (F0 P c))) '' {a | a < b}))
  unfold spanR
  rw [mem_span_image_iff_pr1_pr2_mem_span, map_sub, map_sub, pr1_lin_eq_cmp1_mulVec, pr2_lin_eq_cmp2_mulVec]

end Split

end MassDataIdxStIm
