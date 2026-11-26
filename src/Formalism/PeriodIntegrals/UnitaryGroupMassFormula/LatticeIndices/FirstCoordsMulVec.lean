module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImABwdEps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfBasisAdapted

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfTransitive
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfFrame
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def StFrameA (p : TypX X) : Prop :=
  ∃ π : Op X p →+* ZMod (gOf p), Function.Surjective π ∧
    RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)} ∧
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∃ c, ∀ x : K, LocCong X p x ↔
        (glRed π c)⁻¹ * glRed π (ψ x) * glRed π c ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k

theorem reduction_image_of_frame (p : TypX X) (h : StFrameA X p) : LevelReductionImage X hb p := by
  obtain ⟨π, hπ, hker, K, hKc, ψ, hψ, hP, c, hc⟩ := h
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  set ρ₀ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)) :=
    (MulAut.conj (glRed π c)⁻¹).toMonoidHom.comp ((glRed π).comp ψ) with hρ₀
  have hval : ∀ x : K, ρ₀ x = (glRed π c)⁻¹ * glRed π (ψ x) * glRed π c := by
    intro x; simp [hρ₀]
  have hk₀ : ∀ x : K, ρ₀ x = 1 ↔ (x : HAp X p) ∈ KgX X p := by
    intro x
    rw [hρ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      MonoidHom.comp_apply, glRed_eq_one_iff, hker]
    exact hP x
  have hon : Function.Surjective ρ₀ := by
    have h := (MulEquiv.surjective (MulAut.conj (glRed π c)⁻¹)).comp
      ((glRed_surjective π hπ (isUnit_of_map π hπ)).comp hψ)
    exact h
  refine ⟨K, hKc, ρ₀, hon, hk₀, (nuG (ZMod (gOf p)) D.R.rS D.R.k).comap ρ₀, ?_, ?_, 1, ?_⟩
  · ext y
    rw [stImAloc_holds X hb p]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, (hc x).2 ((hval x) ▸ hx)⟩
      rw [← hKc]; exact x.2
    · rintro ⟨hy, hcy⟩
      have hyK : y ∈ K := by rw [← hKc] at hy; exact hy
      refine ⟨⟨y, hyK⟩, ?_, rfl⟩
      show ρ₀ ⟨y, hyK⟩ ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k
      rw [hval]; exact (hc ⟨y, hyK⟩).1 hcy
  · intro x hx
    show ρ₀ x ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k
    rw [MonoidHom.mem_ker.mp hx]; exact one_mem _
  · rw [Subgroup.map_comap_eq_self_of_surjective hon]
    ext z; simp

end MassDataIdxSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParUniIffFlags
noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni isUpUni_inv isUpUni_det)

variable {K : Type} [Field K] {r k : ℕ}

def posW (i : Fin k) : Set (Idx r k) := Set.range Sum.inl ∪ wI '' {j | j < i}

def ColW (m : Matrix (Idx r k) (Idx r k) K) : Prop :=
  ∀ i : Fin k, m *ᵥ Pi.single (wI i) 1 - Pi.single (wI i) 1 ∈
    Submodule.span K ((fun j => Pi.single j (1 : K)) '' posW (r := r) i)

theorem colW_iff (m : Matrix (Idx r k) (Idx r k) K) :
    ColW m ↔ ∀ i : Fin k, ∀ j, j ∉ posW (r := r) i → m j (wI i) = if j = wI i then 1 else 0 := by
  unfold ColW
  refine forall_congr' fun i => ?_
  rw [mem_span_single]
  refine forall_congr' fun j => forall_congr' fun _ => ?_
  have e : (m *ᵥ Pi.single (wI i) (1 : K)) j = m j (wI i) := by rw [Matrix.mulVec_single_one]; rfl
  rw [Pi.sub_apply, sub_eq_zero, e, Pi.single_apply]

theorem par_uni_iff_flags (x y : Matrix (Idx r k) (Idx r k) K) (hxy : x * y = 1) (hyx : y * x = 1) :
    Par IsUpUni x ↔ ColC x ∧ ColW x ∧ RowC y := by
  constructor
  · intro hx
    have hu : Par (fun h => IsUnit h.det) x := by
      obtain ⟨h11, h33, h21, h31, h32, h, hh, h22⟩ := hx
      exact ⟨h11, h33, h21, h31, h32, h, uni_unit hh, h22⟩
    obtain ⟨hC, hR⟩ := (par_iff_flags x y hxy hyx).1 hu
    refine ⟨hC, ?_, hR⟩
    obtain ⟨h11, h33, h21, h31, h32, h, hh, h22⟩ := hx
    rw [colW_iff]
    intro i j hj
    rcases j with a | (j | u) | c
    · exact absurd (Or.inl ⟨a, rfl⟩) hj
    · have e := congrFun (congrFun h22 (Sum.inl j)) (Sum.inl i)
      simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₁₁] at e
      have hji : ¬ j < i := fun hlt => hj (Or.inr ⟨j, hlt, rfl⟩)
      show x (wI j) (wI i) = _
      rw [show x (wI j) (wI i) = h j i from e]
      by_cases hij : j = i
      · subst hij; simp [hh.2 j, wI]
      · have hlt : i < j := lt_of_le_of_ne (not_lt.1 hji) (Ne.symm hij)
        rw [hh.1 hlt]
        have : (wI j : Idx r k) ≠ wI i := by
          intro e'; apply hij; simpa [wI] using e'
        simp [wI, hij]
    · have e := congrFun (congrFun h22 (Sum.inr u)) (Sum.inl i)
      simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] at e
      have e' : x (Sum.inr (Sum.inl (Sum.inr u))) (wI i) = 0 := e
      rw [e']; simp [wI]
    · have e := congrFun (congrFun h32 c) (Sum.inl i)
      simp only [b32, Matrix.of_apply, Matrix.zero_apply] at e
      have e' : x (Sum.inr (Sum.inr c)) (wI i) = 0 := e
      rw [e']; simp [wI]
  · rintro ⟨hC, hW, hR⟩
    obtain ⟨h11, h33, h21, h31, h32, h, -, h22⟩ := (par_iff_flags x y hxy hyx).2 ⟨hC, hR⟩
    refine ⟨h11, h33, h21, h31, h32, h, ⟨fun j i hlt => ?_, fun i => ?_⟩, h22⟩
    ·
      have e := congrFun (congrFun h22 (Sum.inl j)) (Sum.inl i)
      simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₁₁] at e
      rw [← e]
      have hnot : (wI j : Idx r k) ∉ posW (r := r) i := by
        rintro (⟨a, ha⟩ | ⟨j', hj', he⟩)
        · simp [wI] at ha
        · have : j' = j := by simpa [wI] using he
          subst this
          exact absurd hlt (not_lt.2 (le_of_lt hj'))
      have := (colW_iff x).1 hW i (wI j) hnot
      rw [show x (wI j) (wI i) = x (Sum.inr (Sum.inl (Sum.inl j))) (Sum.inr (Sum.inl (Sum.inl i))) from rfl] at this
      rw [this]
      have hne : (wI j : Idx r k) ≠ wI i := by
        intro e'; have : j = i := by simpa [wI] using e'
        exact absurd hlt (by rw [this]; exact lt_irrefl _)
      simp [hne]
    · have e := congrFun (congrFun h22 (Sum.inl i)) (Sum.inl i)
      simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₁₁] at e
      rw [← e]
      have hnot : (wI i : Idx r k) ∉ posW (r := r) i := by
        rintro (⟨a, ha⟩ | ⟨j', hj', he⟩)
        · simp [wI] at ha
        · have : j' = i := by simpa [wI] using he
          subst this
          exact lt_irrefl j' hj'
      have := (colW_iff x).1 hW i (wI i) hnot
      have h1 : x (wI i) (wI i) = 1 := by simpa using this
      exact h1

theorem mem_nuG_iff_flags (g : GL (Idx r k) K) :
    g ∈ nuG K r k ↔ ColFlag (g : Matrix (Idx r k) (Idx r k) K) ∧ ColW (g : Matrix (Idx r k) (Idx r k) K) ∧
      RowFlag ((g⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) := by
  rw [colFlag_iff, rowFlag_iff]
  exact par_uni_iff_flags _ _ (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])

end MassDataIdxStIm
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix

section Loc

variable {D : D7} (X : HidaSetting D)

def TransA (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
    (Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) (π : Op X p →+* ZMod (gOf p)) : Prop :=
  ∀ x : HAp X p, x ∈ KvX X p → ∀ Y : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p),
    ((glRed (algebraMap (Op X p) (FpX X p)) Y : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) :
        Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) =
      ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) :
          Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) *
        Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ x) *
        (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) →
    (LocCong X p x ↔ glRed π Y ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k)

def StTransA (p : TypX X) : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧
      ∃ π : Op X p →+* ZMod (gOf p), Function.Surjective π ∧
        RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)} ∧ TransA X p θ Q π

theorem stFrameA_of_trans (hC : LatCoreX) (p : TypX X) (h : StTransA X p) : StFrameA X p := by
  obtain ⟨θ, hθ, Q, hL, π, hπ, hker, hT⟩ := h
  obtain ⟨ψ, hψ, hk, hform⟩ := hC X p θ hθ Q hL (stK_holds X p).choose (stK_holds X p).choose_spec.1
  refine ⟨π, hπ, hker, (stK_holds X p).choose, (stK_holds X p).choose_spec.1, ψ, hψ, hk, 1, fun x => ?_⟩
  rw [map_one, inv_one, one_mul, mul_one]
  have hx : (x : HAp X p) ∈ KvX X p :=
    (Set.ext_iff.mp (stK_holds X p).choose_spec.1 (x : HAp X p)).1 x.2
  exact hT x hx (ψ x) (hform x)

end Loc

end MassDataIdxSteps
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
open scoped TensorProduct

abbrev IdxD (D : D7) : Type := Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

abbrev OvA : ValuationSubring (FpX X p) := p.1.adicCompletionIntegers X.B.I.F

abbrev gA : OvA X p := ((gOf p : ℕ) : OvA X p)

def crd1 (v : Fin X.B.I.n → TpX X p) : IdxD D → FpX X p :=
  ((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ (pr1 θ v ∘ (idxEquiv X).symm)

def crd2 (v : Fin X.B.I.n → TpX X p) : IdxD D → FpX X p :=
  (Q : Matrix (IdxD D) (IdxD D) (FpX X p))ᵀ *ᵥ
    ((Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ *ᵥ (pr2 θ v ∘ (idxEquiv X).symm))

def SplitA : Prop :=
  ∀ (S : Set (Fin X.B.I.n → TpX X p)) (y : Fin X.B.I.n → TpX X p),
    InModP X p (gOf p) S y ↔
      MassDataIdxFrA.CongSpan (OvA X p) (gA X p) (crd1 X p θ Q '' S) (crd1 X p θ Q y) ∧
      MassDataIdxFrA.CongSpan (OvA X p) (gA X p) (crd2 X p θ Q '' S) (crd2 X p θ Q y)

def CongG (v w : IdxD D → FpX X p) : Prop :=
  ∃ z, MassDataIdxFrA.IntVec (OvA X p) z ∧ v = w + ((gA X p : OvA X p) : FpX X p) • z

def AdaptA : Prop :=
  (∀ a : Fin D.R.rS, CongG X p (crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.e0 a))) (Pi.single (Sum.inl a) 1)) ∧
  CongG X p (crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 X.z0)) (Pi.single zI 1) ∧
  (∀ i : Fin D.R.k, CongG X p (crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.bw i))) (Pi.single (wI i) 1)) ∧
  (∀ a : Fin D.R.rS, CongG X p (crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.e0 a)))
    (Pi.single (Sum.inr (Sum.inr (Fin.rev a))) 1)) ∧
  CongG X p (crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 X.z0)) (-Pi.single zI 1) ∧
  ∀ i : Fin D.R.k, pr2 θ (PI.FinKW.vecV X.B.I p.1 (X.bw i)) = 0

theorem firstCoords_mulVec (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) (v : Fin X.B.I.n → TpX X p) :
    crd1 X p θ Q (M *ᵥ v) =
      (((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
        Matrix.reindex (idxEquiv X) (idxEquiv X) (M.map fun t => (θ t).1) *
          (Q : Matrix (IdxD D) (IdxD D) (FpX X p))) *ᵥ crd1 X p θ Q v := by

  have key : ∀ j, (pr1 θ (M *ᵥ v)) j = ((M.map fun t => (θ t).1) *ᵥ pr1 θ v) j := by
    intro j
    change (θ ((M *ᵥ v) j)).1 = ∑ k, (θ (M j k)).1 * (θ (v k)).1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, Prod.fst_sum]
  have key2 : pr1 θ (M *ᵥ v) ∘ (idxEquiv X).symm =
      Matrix.reindex (idxEquiv X) (idxEquiv X) (M.map fun t => (θ t).1) *ᵥ
        (pr1 θ v ∘ (idxEquiv X).symm) := by
    funext i
    rw [Function.comp_apply, key]
    simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
      Function.comp_apply]
    exact (Fintype.sum_equiv (idxEquiv X).symm _ _ (fun _ => rfl)).symm
  have hQ : (Q : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      ((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) = 1 :=
    Units.mul_inv Q
  simp only [crd1]
  rw [key2]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hQ, Matrix.mul_one]

end Loc

end MassDataIdxSteps
