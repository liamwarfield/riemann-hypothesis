module

public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.WeightCompApply
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementB
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.HomRelationHolds

@[expose] public section

section -- merged from Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.CommProjectionHolds
namespace Formalism.InvariantFactorPaths.PW

open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem isoC_stable (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    GlStableC p LL j Cs (IsoC p LL j Cs la) := by
  intro c hc d hd x hx
  rw [IsoC, Submodule.mem_sInf] at hx ⊢
  intro S hS
  exact hS.2 c hc d hd x (hx S hS)

theorem hwc_le_isoC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    HWC p LL j Cs la ≤ IsoC p LL j Cs la := by
  rw [IsoC]
  exact le_sInf fun S hS => hS.1

theorem coeff_glAct_diag (LL : Letters N) (j : ℕ) (c : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (m : Fin N × Fin r →₀ ℕ) :
    AddMonoidAlgebra.coeff (glAct p LL j c c x) m = ((wt LL j c m : ℤ) : ℚ_[p]) * AddMonoidAlgebra.coeff x m := by
  classical
  conv_lhs => rw [x.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, coeff_sum]
  simp only [glAct_diag_monomial, coeff_smul, coeff_monomial, smul_eq_mul]
  rw [Finset.sum_eq_single m]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb, mul_zero]
  · intro hm
    rw [if_pos rfl, notMem_support_iff.mp hm, mul_zero]

theorem wtSpC_iff_eig (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ WtSpC p LL j Cs la ↔ ∀ c ∈ Cs, glAct p LL j c c x = ((la c : ℤ) : ℚ_[p]) • x := by
  rw [WtSpC, MvPolynomial.mem_restrictSupport_iff]
  constructor
  · intro h c hc
    ext m
    rw [coeff_glAct_diag, coeff_smul, smul_eq_mul]
    by_cases hm : AddMonoidAlgebra.coeff x m = 0
    · rw [hm, mul_zero, mul_zero]
    · have := h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c hc
      rw [this]
  · intro h m hm c hc
    have hm' : AddMonoidAlgebra.coeff x m ≠ 0 := mem_support_iff.mp (Finset.mem_coe.mp hm)
    have e := congrArg (AddMonoidAlgebra.coeff · m) (h c hc)
    rw [coeff_glAct_diag, coeff_smul, smul_eq_mul] at e
    have := mul_right_cancel₀ hm' e
    exact_mod_cast this

theorem hwc_map_of_comm (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x)) (la : Fin r → ℤ) :
    ∀ x ∈ HWC p LL j Cs la, A x ∈ HWC p LL j Cs la := by
  intro x hx
  rw [HWC, Submodule.mem_inf] at hx ⊢
  refine ⟨?_, ?_⟩
  · rw [wtSpC_iff_eig]
    intro c hc
    rw [← hA c hc c hc, (wtSpC_iff_eig LL j Cs la x).mp hx.1 c hc, map_smul]
  · have h2 := hx.2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h2 ⊢
    intro c d hcd
    rw [← hA c hcd.1 d hcd.2.1, h2 c d hcd, map_zero]

theorem isoC_map_of_comm (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x)) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p LL j Cs la, A x ∈ IsoC p LL j Cs la := by
  have hle : IsoC p LL j Cs la ≤ (IsoC p LL j Cs la).comap A := by
    conv_lhs => rw [IsoC]
    refine sInf_le ⟨?_, ?_⟩
    · intro x hx
      exact hwc_le_isoC LL j Cs la (hwc_map_of_comm LL j Cs A hA la x hx)
    · intro c hc d hd x hx
      rw [Submodule.mem_comap] at hx ⊢
      rw [hA c hc d hd]
      exact isoC_stable LL j Cs la c hc d hd _ hx
  exact fun x hx => hle hx

theorem iSup_isoC_map (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (Q : (Fin r → ℤ) → Prop)
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ la, ∀ x ∈ IsoC p LL j Cs la, A x ∈ IsoC p LL j Cs la) :
    ∀ x ∈ (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la),
      A x ∈ (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la) := by
  have hle : (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la) ≤
      (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la).comap A := by
    refine iSup_le fun la => iSup_le fun hla => ?_
    intro x hx
    rw [Submodule.mem_comap]
    exact (le_iSup_of_le la (le_iSup_of_le hla le_rfl) :
      IsoC p LL j Cs la ≤ ⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la) (hA la x hx)
  exact fun x hx => hle hx

theorem typeProj_comm (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs T P)
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ la, ∀ x ∈ IsoC p LL j Cs la, A x ∈ IsoC p LL j Cs la) : P ∘ₗ A = A ∘ₗ P := by
  obtain ⟨hPP, hr, hk⟩ := hP
  have hPP' : ∀ x, P (P x) = P x := fun x => congrArg (fun f => f x) hPP
  have hR : ∀ x ∈ LinearMap.range P, A x ∈ LinearMap.range P := by
    rw [hr]; exact iSup_isoC_map LL j Cs (fun la => la ∈ T) A hA
  have hK : ∀ x ∈ LinearMap.ker P, A x ∈ LinearMap.ker P := by
    rw [hk]; exact iSup_isoC_map LL j Cs (fun la => la ∉ T) A hA
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  have h1 : P (A (P x)) = A (P x) := by
    obtain ⟨y, hy⟩ := hR (P x) ⟨x, rfl⟩
    rw [← hy, hPP']
  have h2 : P (A (x - P x)) = 0 := by
    apply hK
    rw [LinearMap.mem_ker, map_sub, hPP', sub_self]
  rw [map_sub, map_sub, h1, sub_eq_zero] at h2
  exact h2

theorem comm_projection_holds : CommP := by
  intro p _ N r LL j j' Cs Cs' T T' P P' hj hC hP hP'
  have h1 : ∀ c ∈ Cs', ∀ d ∈ Cs', ∀ x, P (glAct p LL j' c d x) = glAct p LL j' c d (P x) := by
    intro c hc d hd x
    have := typeProj_comm LL j Cs T P hP (glAct p LL j' c d) (by
      intro la y hy
      rw [glAct_split LL hj c d, LinearMap.add_apply]
      refine Submodule.add_mem _ (isoC_stable LL j Cs la c (hC hc) d (hC hd) y hy) ?_
      exact isoC_map_of_comm LL j Cs (midAct p LL j j' c d)
        (fun c' _ d' _ z => midAct_comm LL j j' c d c' d' z) la y hy)
    exact congrArg (fun f => f x) this
  exact (typeProj_comm LL j' Cs' T' P' hP' P (isoC_map_of_comm LL j' Cs' P h1)).symm

end Formalism.InvariantFactorPaths.PW
end

section -- merged from Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.SchurTraceOfHomInv
namespace Formalism.InvariantFactorPaths.PW

open Finset Formalism.GM.DimensionMonotonicity

section gen

variable {K V V₁ V₂ : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]
  [AddCommGroup V₂] [Module K V₂] {n : ℕ}

theorem glRel_of (G : GlW K V n) : GlRel G.E := by
  intro a b c d
  ext x
  have h := G.comm a b c d x
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  rw [h]
  split_ifs <;> simp

def mapsInto (V₁ : Type) [AddCommGroup V₁] [Module K V₁] (W : Submodule K V₂) : Submodule K (V₁ →ₗ[K] V₂) where
  carrier := {φ | ∀ x, φ x ∈ W}
  add_mem' := fun {φ ψ} hφ hψ x => by rw [LinearMap.add_apply]; exact W.add_mem (hφ x) (hψ x)
  zero_mem' := fun x => by rw [LinearMap.zero_apply]; exact W.zero_mem
  smul_mem' := fun c φ hφ x => by rw [LinearMap.smul_apply]; exact W.smul_mem c (hφ x)

theorem hom_eig_zero [CharZero K] (G₁ : GlW K V₁ n) (G₂ : GlW K V₂ n) (W : Submodule K V₂) (l : ℕ)
    (hW : G₂.Stable W) (hb : WtBound2 G₁ G₂ W l) (z : Fin n) (k : ℤ) (φ : V₁ →ₗ[K] V₂) (hφ : ∀ x, φ x ∈ W)
    (he : homAct G₁.E G₂.E z z φ = (k : K) • φ) (hk : (l : ℤ) < |k|) : φ = 0 := by
  have key : ∀ μ x, φ (G₁.comp μ x) = 0 := by
    intro μ x
    by_contra hy
    have hx' : G₁.comp μ x ≠ 0 := fun h => hy (by rw [h, map_zero])
    have hE : G₂.E z z (φ (G₁.comp μ x)) = ((k + μ z : ℤ) : K) • φ (G₁.comp μ x) := by
      have h := congrArg (fun ψ : V₁ →ₗ[K] V₂ => ψ (G₁.comp μ x)) he
      simp only [homAct_apply, LinearMap.smul_apply] at h
      rw [G₁.diag, map_smul] at h
      rw [Int.cast_add, add_smul, ← h]
      abel
    have hc : ∀ ν, G₂.comp ν (φ (G₁.comp μ x)) = 0 := by
      intro ν
      by_contra hν
      have e1 := G₂.comp_Ecc ν z (φ (G₁.comp μ x))
      rw [hE, map_smul] at e1
      have e2 : (((k + μ z : ℤ) : K) - ((ν z : ℤ) : K)) • G₂.comp ν (φ (G₁.comp μ x)) = 0 := by
        rw [sub_smul, e1, sub_self]
      rcases smul_eq_zero.mp e2 with h | h
      · have h3 : k + μ z = ν z := by exact_mod_cast sub_eq_zero.mp h
        have h4 := hb μ ν (G₁.comp μ x) _ hx' hν (G₂.graded_of hW ν _ (hφ _)) (G₁.isWt_comp μ x)
          (G₂.isWt_comp ν _) z
        rw [← h3, add_sub_cancel_right] at h4
        omega
      · exact hν h
    apply hy
    have h := G₂.sum_comp (φ (G₁.comp μ x)) ∅ (fun ν _ => hc ν)
    simpa using h.symm
  ext x
  obtain ⟨S, hS⟩ := G₁.dec x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← G₁.sum_comp x S hS, map_sum, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun μ _ => key μ x

end gen

theorem homInv_of (h1 : InvInv) : HomInv := by
  intro K V₁ V₂ _ _ _ _ _ _ n G₁ G₂ W l hW hb φ hφ h0
  have hrel : GlRel (homAct G₁.E G₂.E) := hom_relation_holds K V₁ V₂ (Fin n) G₁.E G₂.E (glRel_of G₁) (glRel_of G₂)
  obtain ⟨c1, c2, c3⟩ := h1 K (V₁ →ₗ[K] V₂) (Fin n) (homAct G₁.E G₂.E) hrel l (mapsInto V₁ W)
    (fun a b ψ hψ x => by
      rw [homAct_apply]
      exact W.sub_mem (hW a b _ (hψ x)) (hψ _))
    (fun z k ψ hψ he hk => hom_eig_zero G₁ G₂ W l hW hb z k ψ hψ he hk)
    (List.finRange n) (List.nodup_finRange n) φ hφ (fun a _ => h0 a)
  refine ⟨fun a b x => ?_, c2, c3⟩
  have h := congrArg (fun ψ : V₁ →ₗ[K] V₂ => ψ x) (c1 a (List.mem_finRange a) b (List.mem_finRange b))
  simp only [homAct_apply, LinearMap.zero_apply] at h
  exact (sub_eq_zero.mp h).symm

theorem schurTrace_of_homInv (h2 : HomInv) : SchurTrace := by
  intro K V _ _ _ _ n G W l hW hfd hfW hb la h hh hhW hh0 φ h0
  have hUW : G.gS {h} ≤ W := G.gS_le (by simpa using hhW) hW
  have : FiniteDimensional K (G.gS {h}) := Submodule.finiteDimensional_of_le hUW
  obtain ⟨c1, -, c3⟩ := h2 K (G.gS {h}) (G.gS {h}) n (res G _ (G.gS_stable {h})) (res G _ (G.gS_stable {h})) ⊤ l
    (fun _ _ _ _ => Submodule.mem_top)
    (fun μ ν x y hx hy _ hwx hwy c => hb μ ν x y (fun e => hx (Subtype.ext e)) (fun e => hy (Subtype.ext e))
      (hUW x.2) (hUW y.2) (congrArg Subtype.val hwx) (congrArg Subtype.val hwy) c)
    φ (fun _ => Submodule.mem_top) h0
  generalize InvOp (homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E) l (List.finRange n) φ = ψ
    at c1 c3 ⊢
  have hmem : h ∈ G.gS {h} := G.subset_gS {h} rfl
  have hwt : (res G _ (G.gS_stable {h})).IsWt la ⟨h, hmem⟩ := Subtype.ext hh.1
  have hwψ : (res G _ (G.gS_stable {h})).IsWt la (ψ ⟨h, hmem⟩) :=
    Formalism.CountingSumsFrames.GlX.isWt_of_eig _ (fun c => by
      rw [← c1, (res G _ (G.gS_stable {h})).E_diag_of_isWt hwt c, map_smul])
  obtain ⟨c, hc⟩ := G.comp_top_of_mem hh (ψ ⟨h, hmem⟩).2
  have hc' : ((ψ ⟨h, hmem⟩ : G.gS {h}) : V) = c • h := by
    rw [← hc]; exact (congrArg Subtype.val hwψ).symm
  have hle : G.gS {h} ≤ Submodule.map (G.gS {h}).subtype (LinearMap.ker (ψ - c • LinearMap.id)) := by
    apply G.gS_le
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      refine ⟨⟨y, hmem⟩, ?_, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [sub_eq_zero]
      exact Subtype.ext hc'
    · rintro a b _ ⟨y, hy, rfl⟩
      refine ⟨(res G _ (G.gS_stable {h})).E a b y, ?_, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hy ⊢
      rw [c1, ← map_smul, ← map_sub, hy, map_zero]
  have hψ : ψ = c • LinearMap.id := by
    ext x
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have hyx' : y = x := Subtype.ext hyx
    subst hyx'
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at hy
    rw [sub_eq_zero.mp hy]
    rfl
  have htr : LinearMap.trace K _ (ψ - φ) = 0 := hom_trace_holds K (G.gS {h}) (Fin n) _ _ c3
  have : Nontrivial (G.gS {h}) := ⟨⟨⟨h, hmem⟩, 0, fun e => hh0 (congrArg Subtype.val e)⟩⟩
  have hfr : (Module.finrank K (G.gS {h}) : K) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := G.gS {h})).ne'
  rw [map_sub, sub_eq_zero, hψ, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  rw [hψ, ← htr, mul_div_assoc, div_self hfr, mul_one]

theorem schurTrace_of (h1 : InvInv) : SchurTrace := schurTrace_of_homInv (homInv_of h1)

end Formalism.InvariantFactorPaths.PW
end
