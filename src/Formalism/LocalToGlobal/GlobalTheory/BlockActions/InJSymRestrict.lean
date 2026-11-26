module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.TilEqLevel
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ExistsOnOfPosDef

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.BlockActions.CTExtUnitary
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

section Gen

theorem exists_proj {E : Type} [Field E] {N n : ℕ} (hN : n + 1 = N) (A : Matrix (Fin N) (Fin n) E) (z : Fin N → E)
    (hA : Function.Injective A.mulVec) (hz : ∀ x, A *ᵥ x ≠ z) :
    ∃ P : Matrix (Fin n) (Fin N) E, P * A = 1 ∧ P *ᵥ z = 0 := by
  subst hN
  have hB := isUnit_det_cols rfl A z hA hz
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
    Matrix.of (fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) with hBdef
  have h := nonsing_inv_mul B hB
  refine ⟨Matrix.of fun a j => B⁻¹ (Fin.castSucc a) j, ?_, ?_⟩
  · ext a b
    have e := congrFun (congrFun h (Fin.castSucc a)) (Fin.castSucc b)
    have hcol (j : Fin (n + 1)) : B j (Fin.castSucc b) = A j b := by
      simp [hBdef]
    simp only [Matrix.mul_apply, hcol, Matrix.one_apply, Fin.castSucc_inj] at e
    simpa [Matrix.mul_apply, Matrix.one_apply] using e
  · funext a
    have e := congrFun (congrFun h (Fin.castSucc a)) (Fin.last n)
    simp only [Matrix.mul_apply, hBdef, of_apply, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true, one_apply] at e
    simpa [mulVec, dotProduct, (Fin.castSucc_lt_last a).ne] using e

theorem cT_ext_unitary {A : Type} [CommRing A] (τ : A →+* A) {N n : ℕ} (I : Matrix (Fin N) (Fin n) A)
    (J : Matrix (Fin N) (Fin N) A) (G : Matrix (Fin N) (Fin N) A) (k : Matrix (Fin n) (Fin n) A)
    (hG : cT τ G * J * G = J) (hE : G * I = I * k) :
    cT τ k * (cT τ I * J * I) * k = cT τ I * J * I := by
  calc cT τ k * (cT τ I * J * I) * k = cT τ (I * k) * J * (I * k) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT τ (G * I) * J * (G * I) := by rw [hE]
    _ = cT τ I * (cT τ G * J * G) * I := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT τ I * J * I := by rw [hG]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem latS_mulVec (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R)) {n N : ℕ}
    (M : Matrix (Fin N) (Fin n) E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (Λ : Submodule (𝓞 E) (Fin N → E))
    (hM : ∀ x ∈ Λ', M *ᵥ x ∈ Λ) :
    ∀ x ∈ latS (F := F) R S Λ', (M.map (inclE (F := F) R)) *ᵥ x ∈ latS (F := F) R S Λ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x0, hx0, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨M *ᵥ x0, hM x0 hx0, ?_⟩
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have e : (M.map (inclE (F := F) R)) *ᵥ (a • x) = a • ((M.map (inclE (F := F) R)) *ᵥ x) := by
      rw [Subring.smul_def, Subring.smul_def, mulVec_smul]
    rw [e]; exact Submodule.smul_mem _ a hx

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem exists_projP (Tf : FormsTiedSym D u Ch chOf) :
    ∃ P : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E, P * iXm D = 1 ∧ P *ᵥ Tf.til.z0 = 0 := by
  obtain ⟨P, h1, h2⟩ := exists_proj (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (iXm D) (fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E))
    (iXm_mulVec_injective D) (quotient_not_in_range_symmetric Tf)
  refine ⟨P, h1, ?_⟩
  have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have e : Tf.til.z0 = ((D.mem u).A.T : D.host.E) • (fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E)) := by
    funext i; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
  rw [e, mulVec_smul, h2, smul_zero]

theorem lat_in_out (Tf : FormsTiedSym D u Ch chOf) (P : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E)
    (hP1 : P * iXm D = 1) (hPz : P *ᵥ Tf.til.z0 = 0) :
    (∀ x ∈ Tf.clsP.lev.Lb, iXm D *ᵥ x ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb) ∧
    (∀ y ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb, P *ᵥ y ∈ Tf.clsP.lev.Lb) := by
  have hL : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb =
      Tf.clsP.lev.Lb.map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {Tf.til.z0} := Tf.tilLat
  have hiX : ∀ x, iXm D *ᵥ x = iXc D x := fun x => by simp only [iXm, LinearMap.toMatrix'_mulVec]
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rw [hL, hiX]
    exact Submodule.mem_sup_left (Submodule.mem_map_of_mem hx)
  · rw [hL] at hy
    obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy1
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy2
    have e1 : P *ᵥ ((iXc D).restrictScalars (𝓞 D.host.E) x) = x := by
      show P *ᵥ (iXc D x) = x
      rw [← hiX, mulVec_mulVec, hP1, one_mulVec]
    have e2 : P *ᵥ (a • Tf.til.z0) = 0 := by
      rw [← algebraMap_smul D.host.E a Tf.til.z0, mulVec_smul, hPz, smul_zero]
    rw [mulVec_add, e1, e2, add_zero]
    exact hx

theorem isExt_prV {z0 : Fin (D.R.N D.R.m) → D.host.E} (v : HeightOneSpectrum (𝓞 D.host.F))
    {k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {G : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    (h : IsExt D z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k G) :
    IsExt D z0 (inclE (F := D.host.F) (v.adicCompletion D.host.F)) (k.map (prV (E := D.host.E) v)) (G.map (prV (E := D.host.E) v)) := by
  obtain ⟨h1, h2⟩ := h
  have hc : (prV (E := D.host.E) v).comp (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =
      inclE (F := D.host.F) (v.adicCompletion D.host.F) := RingHom.ext fun e => rfl
  refine ⟨?_, ?_⟩
  · have := congrArg (fun M => M.map (prV (E := D.host.E) v)) h1
    simp only [Matrix.map_mul, Matrix.map_map] at this
    rw [← RingHom.coe_comp, hc] at this
    exact this
  · funext i
    have := congrArg (fun w => prV (E := D.host.E) v (w i)) h2
    simp only at this
    exact (RingHom.map_mulVec _ _ _ _).symm.trans this


set_option maxHeartbeats 4000000 in
theorem lev_lat (Tf : FormsTiedSym D u Ch chOf)
    (k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k G.1)
    (hG : G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U) (v : HeightOneSpectrum (𝓞 D.host.F))
    (x : Fin (D.R.N D.R.m - 1) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F)
      (tensInt (F := D.host.F) (v.adicCompletion D.host.F) (intOE D.host.E) (v.adicCompletionIntegers D.host.F).toSubring) Tf.clsP.lev.Lb ↔
    (k.map (prV (E := D.host.E) v)) *ᵥ x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F)
      (tensInt (F := D.host.F) (v.adicCompletion D.host.F) (intOE D.host.E) (v.adicCompletionIntegers D.host.F).toSubring) Tf.clsP.lev.Lb := by
  set S := tensInt (F := D.host.F) (v.adicCompletion D.host.F) (intOE D.host.E) (v.adicCompletionIntegers D.host.F).toSubring
  set Km := (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev
  have hGv : bc (prV (E := D.host.E) v) G ∈ levelVL (sigD D) (gramN D D.R.m le_rfl) v Km.Lb :=
    Km.Uloc_lev v (((Km.U_eq G).1 hG).2 v)
  have hst := (Subgroup.mem_inf.mp hGv).2
  have hGm : ((bc (prV (E := D.host.E) v) G : GL _ _) : Matrix _ _ _) = G.1.map (prV (E := D.host.E) v) := rfl
  obtain ⟨hEv, -⟩ := isExt_prV v hE
  obtain ⟨P, hP1, hPz⟩ := exists_projP Tf
  obtain ⟨hin, hout⟩ := lat_in_out Tf P hP1 hPz
  have hI := latS_mulVec (F := D.host.F) (v.adicCompletion D.host.F) S (iXm D) _ _ hin
  have hO := latS_mulVec (F := D.host.F) (v.adicCompletion D.host.F) S P _ _ hout
  have hPI : (P.map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) * ((iXm D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) = 1 := by
    rw [← Matrix.map_mul, hP1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hback : ∀ y, y = (P.map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *ᵥ
      (((iXm D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *ᵥ y) := fun y => by
    rw [mulVec_mulVec, hPI, one_mulVec]
  have hcomm : ∀ y, G.1.map (prV (E := D.host.E) v) *ᵥ (((iXm D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *ᵥ y) =
      ((iXm D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *ᵥ ((k.map (prV (E := D.host.E) v)) *ᵥ y) := fun y => by
    rw [mulVec_mulVec, hEv, ← mulVec_mulVec]
  have hs : ∀ y, y ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) S Km.Lb ↔
      G.1.map (prV (E := D.host.E) v) *ᵥ y ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) S Km.Lb := fun y => by
    rw [← hGm]; exact hst y
  constructor
  · intro hx
    have h1 := (hs _).1 (hI x hx)
    rw [hcomm] at h1
    rw [hback ((k.map (prV (E := D.host.E) v)) *ᵥ x)]
    exact hO _ h1
  · intro hx
    have h1 := hI _ hx
    rw [← hcomm] at h1
    rw [hback x]
    exact hO _ ((hs _).2 h1)

theorem lev_unit (Tf : FormsTiedSym D u Ch chOf)
    (k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k G.1)
    (hG : G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U) :
    cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k *
      (gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * k =
      (gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  set Km := (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev
  have hU : G ∈ UPts (sigD D) (gramN D D.R.m le_rfl) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := ((Km.U_eq G).1 hG).1
  have hc : (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).comp (sigD D : D.host.E →+* D.host.E) =
      (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).comp (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    ext e
    simp [sigR, inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
  have hJ : (gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =
      cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((iXm D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) *
        (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) *
        (iXm D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    rw [Formalism.UG.P.cT_map _ _ _ hc, ← Matrix.map_mul, ← Matrix.map_mul, gramP_eq]
    rfl
  rw [hJ]
  exact cT_ext_unitary _ _ _ _ _ hU hE.1

theorem lev_isUnit (Tf : FormsTiedSym D u Ch chOf)
    (k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k G.1) :
    IsUnit k.det := by
  obtain ⟨P, hP1, -⟩ := exists_projP Tf
  obtain ⟨Gi, hGi⟩ : ∃ Gi : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      Gi * G.1 = 1 := ⟨(G⁻¹ : GL _ _).1, by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]⟩
  have hQ : HMul.hMul (HMul.hMul Gi ((iXm D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))) k = (iXm D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    rw [Matrix.mul_assoc, ← hE.1, ← Matrix.mul_assoc, hGi, Matrix.one_mul]
  have hl : HMul.hMul (HMul.hMul (P.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) (HMul.hMul Gi ((iXm D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))))) k = 1 := by
    rw [Matrix.mul_assoc, hQ, ← Matrix.map_mul, hP1, Matrix.map_one _ (map_zero _) (map_one _)]
  exact Matrix.isUnit_det_of_left_inverse hl

end Formalism.L2.GlobalTheoryTheory.Br
end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

section Gen

theorem inJSym_restrict {κ : Type} [Field κ] {n : ℕ} {k rS t : ℕ} {zl : Bool} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) κ)
    (R : Matrix (Fin n) (Fin n) κ) (hR : ∀ x y, R x y = M x.castSucc y.castSucc) (h : InJSym k rS t zl M) :
    InJSym k rS t false R := by
  obtain ⟨h1, h2, h3, -⟩ := h
  refine ⟨fun x y hxy => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun h => absurd h Bool.false_ne_true⟩
  · rw [hR]; exact h1 _ _ (by simpa only [Fin.val_castSucc] using hxy)
  · rw [hR]; exact h2 _ (by simpa only [Fin.val_castSucc] using hx)
  · rw [hR]; exact h3 _ _ (by simpa only [Fin.val_castSucc] using hx) (by simpa only [Fin.val_castSucc] using hy)

theorem jsym_of_blk {κ : Type} [Field κ] {n N : ℕ} (hN : n + 1 = N) {k rS t : ℕ} (Mm : GL (Fin N) κ)
    (hMm : Mm ∈ JSymG κ N k rS t true) (R : Matrix (Fin n) (Fin n) κ)
    (hR : ∀ x y : Fin n, R x y = Mm.1 ⟨x, by omega⟩ ⟨y, by omega⟩) :
    ∃ M ∈ JSymG κ n k rS t false, M.1 = R := by
  subst hN
  obtain ⟨h1, h2⟩ := hMm
  have hRc : ∀ x y : Fin n, R x y = Mm.1 x.castSucc y.castSucc := fun x y => hR x y
  set R' : Matrix (Fin n) (Fin n) κ := fun x y => (Mm⁻¹ : GL (Fin (n + 1)) κ).1 x.castSucc y.castSucc with hR'
  have hl : ∀ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) κ), InJSym k rS t true M → ∀ x : Fin n,
      M x.castSucc (Fin.last n) = 0 := by
    intro M hM x
    have := (hM.2.2.2 rfl x.castSucc (Fin.last n) (by simp)).1
    simpa [Fin.castSucc_ne_last] using this
  have hmul : ∀ (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) κ), InJSym k rS t true A → ∀ x y : Fin n,
      (A * B) x.castSucc y.castSucc = ∑ j : Fin n, A x.castSucc j.castSucc * B j.castSucc y.castSucc := by
    intro A B hA x y
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc, hl A hA x, zero_mul, add_zero]
  have e1 : R * R' = 1 := by
    ext x y
    have := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) κ => M x.castSucc y.castSucc)
      (show Mm.1 * (Mm⁻¹).1 = 1 from Mm.mul_inv)
    rw [hmul _ _ h1] at this
    rw [Matrix.mul_apply]
    simp only [hRc, hR']
    rw [this]
    change (if x.castSucc = y.castSucc then (1 : κ) else 0) = (if x = y then 1 else 0)
    simp only [Fin.castSucc_inj]
  have e2 : R' * R = 1 := by
    ext x y
    have := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) κ => M x.castSucc y.castSucc)
      (show (Mm⁻¹).1 * Mm.1 = 1 from Mm.inv_mul)
    rw [hmul _ _ h2] at this
    rw [Matrix.mul_apply]
    simp only [hRc, hR']
    rw [this]
    change (if x.castSucc = y.castSucc then (1 : κ) else 0) = (if x = y then 1 else 0)
    simp only [Fin.castSucc_inj]
  refine ⟨⟨R, R', e1, e2⟩, ⟨?_, ?_⟩, rfl⟩
  · exact inJSym_restrict _ R hRc h1
  · exact inJSym_restrict _ R' (fun x y => rfl) h2

theorem blk_conj {K : Type} [CommRing K] {n N : ℕ} (hN : n + 1 = N) (gm Fm Fm' : Matrix (Fin N) (Fin N) K) (hFm : Fm' * Fm = 1)
    (A : Matrix (Fin N) (Fin n) K) (Fp gk M' : Matrix (Fin n) (Fin n) K) (hM' : Fp * M' = gk * Fp)
    (hgA : gm * A = A * gk) (w : Fin N → K) (hgw : gm *ᵥ w = w)
    (hF1 : ∀ x (b : Fin n) (b' : Fin N), (b : ℕ) = b' → Fm x b' = (A * Fp) x b)
    (hF2 : ∀ x (l : Fin N), (l : ℕ) + 1 = N → Fm x l = w x) :
    ∀ x y : Fin n, (Fm' * gm * Fm) ⟨x, by omega⟩ ⟨y, by omega⟩ = M' x y := by
  subst hN
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of (fun x y : Fin (n + 1) =>
    if h : (x : ℕ) < n ∧ (y : ℕ) < n then M' ⟨x, h.1⟩ ⟨y, h.2⟩ else if (x : ℕ) = y then 1 else 0) with hB
  have hne : ∀ j : Fin n, (j : ℕ) ≠ n := fun j => j.is_lt.ne
  have key : gm * Fm = Fm * B := by
    ext x y
    refine Fin.lastCases ?_ (fun y' => ?_) y
    · have e1 : (gm * Fm) x (Fin.last n) = w x := by
        rw [← congrFun hgw x, Matrix.mul_apply]
        simp only [mulVec, dotProduct]
        exact Finset.sum_congr rfl (fun j _ => by rw [hF2 j (Fin.last n) (by simp)])
      rw [e1, Matrix.mul_apply, Fin.sum_univ_castSucc]
      simp [hB, hne, hF2 x (Fin.last n) (by simp)]
    · have eL : (gm * Fm) x y'.castSucc = (A * (Fp * M')) x y' := by
        rw [hM', ← Matrix.mul_assoc, ← hgA, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun j _ => by rw [hF1 j y' y'.castSucc (by simp)])
      have eR : (Fm * B) x y'.castSucc = ((A * Fp) * M') x y' := by
        rw [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.mul_apply]
        have hlast : B (Fin.last n) y'.castSucc = 0 := by
          simp [hB, (hne y').symm]
        rw [hlast, mul_zero, add_zero]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hF1 x j j.castSucc (by simp)]
        simp [hB]
      rw [eL, eR, Matrix.mul_assoc]
  intro x y
  have e : Fm' * gm * Fm = B := by rw [Matrix.mul_assoc, key, ← Matrix.mul_assoc, hFm, Matrix.one_mul]
  rw [e]
  simp [hB]

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem redM_entry {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {m m' : ℕ}
    (X : Matrix (Fin m) (Fin m) (v.adicCompletion F)) (Y : Matrix (Fin m') (Fin m') (v.adicCompletion F))
    (a b : Fin m) (a' b' : Fin m') (h : X a b = Y a' b') : redM F v X a b = redM F v Y a' b' := by
  simp only [redM, h]
  by_cases hY : Y a' b' ∈ v.adicCompletionIntegers F
  · rw [dite_eq_left (by rw [h]; exact hY), dite_eq_left hY]
  · rw [dite_eq_right (by rw [h]; exact hY), dite_eq_right hY]


set_option maxHeartbeats 4000000 in
theorem lev_bad (Tf : FormsTiedSym D u Ch chOf) (K : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) K.1 G.1)
    (hG : G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hlev : bc (prV (E := D.host.E) v) K ∈ levelVL (sigD D) (gramP D) v Tf.clsP.lev.Lb)
    (i : Fin 2) (h : (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal) :
    bc (prV (E := D.host.E) v) K ∈ Tf.clsP.lev.Uloc v := by
  set Km := (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev
  rw [Tf.glevP.mem i v h _ hlev]
  have hGv : bc (prV (E := D.host.E) v) G ∈ Km.Uloc v := ((Km.U_eq G).1 hG).2 v
  obtain ⟨Mm, hMm, hMmeq⟩ := (Tf.glevM.mem i v h _ (Km.Uloc_lev v hGv)).1 hGv
  obtain ⟨hEv1, hEv2⟩ := isExt_prV v hE
  obtain ⟨hF1, hF2⟩ := Tf.frExt i v h
  have hmatG : Tf.gl.mat i v h (Tf.glevM.fr i v h) (bc (prV (E := D.host.E) v) G) =
      ((Tf.glevM.fr i v h)⁻¹ : GL _ _).1 * (G.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h) * (Tf.glevM.fr i v h).1 := by
    simp only [GLoc.mat, Units.val_mul]; rfl
  have hmatK : Tf.gl.mat i v h (Tf.glevP.fr i v h) (bc (prV (E := D.host.E) v) K) =
      ((Tf.glevP.fr i v h)⁻¹ : GL _ _).1 * (K.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h) * (Tf.glevP.fr i v h).1 := by
    simp only [GLoc.mat, Units.val_mul]; rfl
  have hb := blk_conj (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R)
    ((G.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h)) (Tf.glevM.fr i v h).1 ((Tf.glevM.fr i v h)⁻¹ : GL _ _).1
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
    ((iXm D).map ((Tf.gl.phi i v h).comp (inclE (F := D.host.F) (v.adicCompletion D.host.F))))
    (Tf.glevP.fr i v h).1 ((K.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h))
    (((Tf.glevP.fr i v h)⁻¹ : GL _ _).1 * (K.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h) * (Tf.glevP.fr i v h).1)
    (by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul])
    (by
      have := congrArg (fun M => M.map (Tf.gl.phi i v h)) hEv1
      simp only [Matrix.map_mul, Matrix.map_map] at this
      rw [RingHom.coe_comp]
      exact this)
    (fun a => Tf.gl.phi i v h (inclE (F := D.host.F) (v.adicCompletion D.host.F) (Tf.til.z0 a)))
    (by
      funext a
      exact (RingHom.map_mulVec (Tf.gl.phi i v h) _ _ a).symm.trans (congrArg (fun w => Tf.gl.phi i v h (w a)) hEv2))
    hF1 hF2
  refine jsym_of_blk (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) Mm hMm _ (fun x y => ?_)
  rw [hMmeq]
  refine redM_entry v _ _ _ _ _ _ ?_
  rw [hmatK, hmatG]
  exact (hb x y).symm


set_option maxHeartbeats 4000000 in
theorem lev_mem (Tf : FormsTiedSym D u Ch chOf) (K : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) K.1 G.1)
    (hG : G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U) : K ∈ Tf.clsP.lev.U := by
  have hU : K ∈ UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := lev_unit Tf K.1 G hE hG
  rw [Tf.clsP.lev.U_eq]
  refine ⟨hU, fun v => ?_⟩
  have hu := Formalism.UG.P.base_change_mem_holds _ _ _ (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (sigR (sigD D) (v.adicCompletion D.host.F)) (prV (E := D.host.E) v)
    (Formalism.UG.P.afsplit_prV_comp_sigR (sigD D) v) _ K hU
  have e : ((gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))).map (prV (E := D.host.E) v) =
      (gramP D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F)) := by
    rw [Matrix.map_map]; rfl
  rw [e] at hu
  have hlev : bc (prV (E := D.host.E) v) K ∈ levelVL (sigD D) (gramP D) v Tf.clsP.lev.Lb :=
    Subgroup.mem_inf.mpr ⟨hu, fun x => lev_lat Tf K.1 G hE hG v x⟩
  by_cases hv : v ∈ badG D
  · obtain ⟨i, hi⟩ : ∃ i : Fin 2, (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal := by
      rcases hv with h0 | h1
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
    exact lev_bad Tf K G hE hG v hlev i hi
  · have h1 : ((1 : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
      rw [Nat.cast_one]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    rw [Tf.clsP.lev.Uloc_hyp v hv h1]
    exact hlev

end Formalism.L2.GlobalTheoryTheory.Br
