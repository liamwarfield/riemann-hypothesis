module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParabolicInductionTrivialPreservesVirtualCharact
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedDerivWeierstrassPTorsion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMul
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.FunObj
open Matrix

section Ratio
variable {G : Type*} [Group G]

def idxRatio (A B : Subgroup G) : ℚ := (B.relIndex A : ℚ) / A.relIndex B

theorem idxRatio_eq_of_le {A B D : Subgroup G} (hD : D ≤ A ⊓ B) (h0 : D.relIndex (A ⊓ B) ≠ 0) :
    idxRatio A B = (D.relIndex A : ℚ) / D.relIndex B := by
  have h1 := Subgroup.relIndex_mul_relIndex D (A ⊓ B) A hD inf_le_left
  have h2 := Subgroup.relIndex_mul_relIndex D (A ⊓ B) B hD inf_le_right
  have e1 : (A ⊓ B).relIndex A = B.relIndex A := by rw [inf_comm]; exact Subgroup.inf_relIndex_right B A
  have e2 : (A ⊓ B).relIndex B = A.relIndex B := Subgroup.inf_relIndex_right A B
  rw [idxRatio, ← h1, ← h2, e1, e2]
  push_cast
  rw [mul_div_mul_left _ _ (by exact_mod_cast h0)]

theorem idxRatio_map {f : G →* G} (hf : Function.Injective f) (A B : Subgroup G) :
    idxRatio (A.map f) (B.map f) = idxRatio A B := by
  rw [idxRatio, idxRatio, Subgroup.relIndex_map_map_of_injective _ _ hf,
    Subgroup.relIndex_map_map_of_injective _ _ hf]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem relIndex_inf_ne_zero {N O C H : Subgroup G} (hO : IsOpen (O : Set G)) (hC : IsCompact (C : Set G))
    (hHN : H ≤ N) (hHC : H ≤ C) : (N ⊓ O).relIndex H ≠ 0 := by
  intro h
  have h1 : O ⊓ H ≤ N ⊓ O := fun x hx => Subgroup.mem_inf.2 ⟨hHN (Subgroup.mem_inf.1 hx).2, (Subgroup.mem_inf.1 hx).1⟩
  have h2 := Subgroup.relIndex_eq_zero_of_le_left h1 h
  rw [Subgroup.inf_relIndex_right] at h2
  exact relIndex_ne_zero_of_isOpen hO hC hHC h2

theorem idxRatio_cocycle (N : Subgroup G) {U V W : Subgroup G} (hUo : IsOpen (U : Set G))
    (hUc : IsCompact (U : Set G)) (hVo : IsOpen (V : Set G)) (hVc : IsCompact (V : Set G))
    (hWo : IsOpen (W : Set G)) (hWc : IsCompact (W : Set G)) :
    idxRatio (N ⊓ U) (N ⊓ V) * idxRatio (N ⊓ V) (N ⊓ W) = idxRatio (N ⊓ U) (N ⊓ W) := by
  have hO : IsOpen ((U ⊓ V ⊓ W : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf, Subgroup.coe_inf]; exact (hUo.inter hVo).inter hWo
  have l1 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ U) ⊓ (N ⊓ V) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  have l2 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ V) ⊓ (N ⊓ W) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  have l3 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ U) ⊓ (N ⊓ W) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  have nV : (N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ V) ≠ 0 := relIndex_inf_ne_zero hO hVc inf_le_left inf_le_right
  have nW : (N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ W) ≠ 0 := relIndex_inf_ne_zero hO hWc inf_le_left inf_le_right
  rw [idxRatio_eq_of_le l1 (relIndex_inf_ne_zero hO hUc (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right)),
    idxRatio_eq_of_le l2 (relIndex_inf_ne_zero hO hVc (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right)),
    idxRatio_eq_of_le l3 (relIndex_inf_ne_zero hO hUc (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right))]
  have nV' : ((N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ V) : ℚ) ≠ 0 := by exact_mod_cast nV
  have nW' : ((N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ W) : ℚ) ≠ 0 := by exact_mod_cast nW
  field_simp

end Ratio

section Diag
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem diagGL_mul' (d e : n → kˣ) : diagGL (d * e) = diagGL d * diagGL e :=
  Units.ext (by simp [diagonal_mul_diagonal])

theorem diagGL_inv' (d : n → kˣ) : diagGL d⁻¹ = (diagGL d)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← diagGL_mul']; exact Units.ext (by simp))

theorem conj_diagGL_InN {p : ℕ} (d : n ⊕ Fin c → kˣ) {x : GL (n ⊕ Fin c) k} (hx : InN p x) :
    InN p (MulAut.conj (diagGL d) x) := by
  intro r s hrs
  have h := hx r s hrs
  have hinv : ((diagGL d)⁻¹ : GL (n ⊕ Fin c) k).val = diagonal fun i => (((d i)⁻¹ : kˣ) : k) := rfl
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, hinv, diagGL_val, mul_diagonal, diagonal_mul, h]
  by_cases hrs' : r = s
  · subst hrs'; simp
  · simp [hrs']

theorem map_conj_diagGL_N_le (p : ℕ) (d : n ⊕ Fin c → kˣ) :
    (N k n c p).map (MulAut.conj (diagGL d)).toMonoidHom ≤ N k n c p := by
  rw [N, MonoidHom.map_closure]
  exact (Subgroup.closure_le _).2 (by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.subset_closure (conj_diagGL_InN d hx))

theorem map_conj_diagGL_symN (d : n ⊕ Fin c → kˣ) :
    (symN k n c).map (MulAut.conj (diagGL d)).toMonoidHom = symN k n c := by
  have hle : ∀ d : n ⊕ Fin c → kˣ, (symN k n c).map (MulAut.conj (diagGL d)).toMonoidHom ≤ symN k n c := by
    intro d
    rw [symN, Subgroup.map_sup]
    exact sup_le_sup (map_conj_diagGL_N_le _ d) (map_conj_diagGL_N_le _ d)
  refine le_antisymm (hle d) ?_
  have h := Subgroup.map_mono (f := (MulAut.conj (diagGL d)).toMonoidHom) (hle d⁻¹)
  have e : (MulAut.conj (diagGL d)).toMonoidHom.comp (MulAut.conj (diagGL d⁻¹)).toMonoidHom = MonoidHom.id _ := by
    ext1 x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply, diagGL_inv']
    group
  rwa [Subgroup.map_map, e, Subgroup.map_id] at h

end Diag

end GlobalTheory.FunObj

namespace GlobalTheory.FunObj
open Matrix

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem relIndex_congr_inf {G : Type*} [Group G] {A B L : Subgroup G} (h : A ⊓ L = B ⊓ L) :
    A.relIndex L = B.relIndex L := by
  rw [← Subgroup.inf_relIndex_right A L, h, Subgroup.inf_relIndex_right]


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem invVol_eq_idxRatio (C : Subgroup (GL (n ⊕ Fin c) k)) :
    invVol C = idxRatio (symN k n c ⊓ KO k _) (symN k n c ⊓ C) := by
  rw [invVol, idxRatio, relIndex_congr_inf (A := C) (B := symN k n c ⊓ C),
    relIndex_congr_inf (A := KO k _) (B := symN k n c ⊓ KO k _)]
  · ext x; simp only [Subgroup.mem_inf]; tauto
  · ext x; simp only [Subgroup.mem_inf]; tauto

theorem isOpen_map_conj_KO (x : GL (n ⊕ Fin c) k) :
    IsOpen (((KO k (n ⊕ Fin c)).map (MulAut.conj x).toMonoidHom : Subgroup _) : Set (GL (n ⊕ Fin c) k)) := by
  rw [Subgroup.map_equiv_eq_comap_symm']
  exact isOpen_KO.preimage ((continuous_const.mul continuous_id).mul continuous_const)

theorem isCompact_map_conj_KO (x : GL (n ⊕ Fin c) k) :
    IsCompact (((KO k (n ⊕ Fin c)).map (MulAut.conj x).toMonoidHom : Subgroup _) : Set (GL (n ⊕ Fin c) k)) :=
  isCompact_KO.image ((continuous_const.mul continuous_id).mul continuous_const)

theorem invVol_conj_diagGL_mul (d e : n ⊕ Fin c → kˣ) :
    invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (d * e))).toMonoidHom) =
      invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL d)).toMonoidHom) *
        invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom) := by
  have hmapN : ∀ (d : n ⊕ Fin c → kˣ) (K' : Subgroup (GL (n ⊕ Fin c) k)),
      (symN k n c ⊓ K').map (MulAut.conj (diagGL d)).toMonoidHom =
        symN k n c ⊓ K'.map (MulAut.conj (diagGL d)).toMonoidHom := by
    intro d K'
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (diagGL d)).injective, map_conj_diagGL_symN]
  have hcomp : (KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (d * e))).toMonoidHom =
      ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom).map
        (MulAut.conj (diagGL d)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext1 x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, diagGL_mul']
    group
  rw [invVol_eq_idxRatio, invVol_eq_idxRatio, invVol_eq_idxRatio, hcomp,
    ← idxRatio_cocycle (symN k n c) isOpen_KO isCompact_KO (isOpen_map_conj_KO (diagGL d))
      (isCompact_map_conj_KO (diagGL d)) (hcomp ▸ isOpen_map_conj_KO (diagGL (d * e)))
      (hcomp ▸ isCompact_map_conj_KO (diagGL (d * e)))]
  congr 1
  rw [← hmapN d (KO k _), ← hmapN d ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom),
    idxRatio_map (MulAut.conj (diagGL d)).injective]

end Main

end GlobalTheory.FunObj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMulStatement
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseUnipotentVolume_conj_diagonalUnitsGL_mul : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (d e : n ⊕ Fin c → kˣ), invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (d * e))).toMonoidHom) = invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL d)).toMonoidHom) * invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom) := by
  first | exact @GlobalTheory.FunObj.invVol_conj_diagGL_mul | exact GlobalTheory.FunObj.invVol_conj_diagGL_mul | (intros; apply GlobalTheory.FunObj.invVol_conj_diagGL_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterTrivialMatrixLatticeOpenCompactBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterTrivialMatrixLatticeOpenCompactBasis
open Filter Topology ValuativeRel

noncomputable section

namespace GlobalTheory.LinSchurLatt

theorem eq_one_of_pow_near (z : ℂ) (h : ∀ m : ℕ, ‖z ^ m - 1‖ ≤ 1 / 2) : z = 1 := by
  have hre : ∀ m : ℕ, 1 / 2 ≤ (z ^ m).re := by
    intro m
    have h1 := (Complex.abs_re_le_norm (z ^ m - 1)).trans (h m)
    rw [Complex.sub_re, Complex.one_re] at h1
    linarith [(abs_le.1 h1).1]
  have hS : ∀ N : ℕ, (N : ℝ) / 2 ≤ ‖∑ m ∈ Finset.range N, z ^ m‖ := by
    intro N
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    calc (N : ℝ) / 2 = ∑ m ∈ Finset.range N, (1 / 2 : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun m _ => hre m
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have e := geom_sum_mul z N
  have h2 : ‖z - 1‖ * ((N : ℝ) / 2) ≤ 1 / 2 := by
    calc ‖z - 1‖ * ((N : ℝ) / 2) ≤ ‖z - 1‖ * ‖∑ m ∈ Finset.range N, z ^ m‖ :=
          mul_le_mul_of_nonneg_left (hS N) hpos.le
      _ = ‖z ^ N - 1‖ := by rw [← e, norm_mul, mul_comm]
      _ ≤ 1 / 2 := h N
  rw [div_lt_iff₀ hpos] at hN
  nlinarith

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_natCast_le_one (m : ℕ) : valuation k (m : k) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (natCast_mem (valuation k).integer m)

theorem ker_int_mem_nhds (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) :
    {u : k | ∀ o : k, valuation k o ≤ 1 → ψ0 (o * u) = 1} ∈ 𝓝 (0 : k) := by
  have hO : IsCompact {x : k | valuation k x ≤ 1} := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hU : {u : k | ‖ψ0 u - 1‖ ≤ 1 / 2} ∈ 𝓝 (0 : k) := by
    have h1 : Metric.closedBall (ψ0 0) (1 / 2) ∈ 𝓝 (ψ0 0) := Metric.closedBall_mem_nhds _ (by norm_num)
    filter_upwards [hc.continuousAt.preimage_mem_nhds h1] with u hu
    simpa [Metric.mem_closedBall, dist_eq_norm, AddChar.map_zero_eq_one] using hu
  have hev : ∀ᶠ w in 𝓝 (0 : k), ∀ a ∈ {x : k | valuation k x ≤ 1}, a * w ∈ {u : k | ‖ψ0 u - 1‖ ≤ 1 / 2} := by
    refine hO.eventually_forall_of_forall_eventually fun a _ => ?_
    have hcm : Continuous fun z : k × k => z.2 * z.1 := continuous_snd.mul continuous_fst
    have h0 : (fun z : k × k => z.2 * z.1) (0, a) = 0 := by simp
    exact hcm.continuousAt.preimage_mem_nhds (by simpa using hU)
  filter_upwards [hev] with w hw o ho
  apply eq_one_of_pow_near
  intro m
  have hmo : valuation k ((m : k) * o) ≤ 1 := by
    rw [map_mul]
    exact mul_le_one' (valuation_natCast_le_one m) ho
  have h1 := hw _ hmo
  have h2 : (m : k) * o * w = m • (o * w) := by rw [nsmul_eq_mul, mul_assoc]
  rwa [h2, AddChar.map_nsmul_eq_pow] at h1

theorem ker_int_lt {ψ0 : AddChar k ℂ} {t : k} (ht : ψ0 t ≠ 1) {u : k}
    (hu : ∀ o : k, valuation k o ≤ 1 → ψ0 (o * u) = 1) : valuation k u < valuation k t := by
  by_contra h
  push_neg at h
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply ht
    have : t = 0 := by simpa using h
    rw [this, AddChar.map_zero_eq_one]
  have hvu : valuation k u ≠ 0 := by simpa using hu0
  apply ht
  have hle : valuation k (t / u) ≤ 1 := by
    rw [map_div₀, div_eq_mul_inv]
    calc valuation k t * (valuation k u)⁻¹ ≤ valuation k u * (valuation k u)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hvu
  have := hu (t / u) hle
  rwa [div_mul_cancel₀ _ hu0] at this

theorem nhdsNE_neBot' : (𝓝[≠] (0 : k)).NeBot := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  exact NormedField.nhdsNE_neBot (0 : k)

theorem isCompact_ball_mat (n d : ℕ) (γ : ValueGroupWithZero k) :
    IsCompact {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ γ} := by
  have : {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ γ} =
      Set.univ.pi fun _ => Set.univ.pi fun _ => {x : k | valuation k x ≤ γ} := by
    ext x
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ

theorem exists_smul_int_mem' (n d : ℕ) (W : Set (Matrix (Fin n) (Fin d) k)) (hW : W ∈ 𝓝 0) :
    ∃ c : k, c ≠ 0 ∧ ∀ x : Matrix (Fin n) (Fin d) k, (∀ i j, valuation k (x i j) ≤ 1) → c • x ∈ W := by
  have hev : ∀ᶠ c in 𝓝 (0 : k), ∀ x ∈ {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ 1}, c • x ∈ W := by
    refine (isCompact_ball_mat n d 1).eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous fun z : k × Matrix (Fin n) (Fin d) k => z.1 • z.2 := continuous_fst.smul continuous_snd
    have h0 : (fun z : k × Matrix (Fin n) (Fin d) k => z.1 • z.2) (0, y) = 0 := by simp
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hW)
  haveI := nhdsNE_neBot' (k := k)
  obtain ⟨c, hc1, hc2⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := {(0 : k)}ᶜ))).and
    (self_mem_nhdsWithin (s := {(0 : k)}ᶜ))).exists
  exact ⟨c, hc2, fun x hx => hc1 x hx⟩

end GlobalTheory.LinSchurLatt

namespace GlobalTheory.LinSchurLatt

theorem latt_open_compact_basis : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 → (∀ s : k, s ≠ 0 → IsOpen (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ∧ IsCompact (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k))) ∧ ∀ W ∈ 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∃ s : k, s ≠ 0 ∧ (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ⊆ W := by
  intro k _ _ _ _ n d ψ0 hc hne
  obtain ⟨t, ht⟩ : ∃ t, ψ0 t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (AddChar.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (AddChar.map_zero_eq_one ψ0)
  have hvt : valuation k t ≠ 0 := by simpa using ht0
  have hK := ker_int_mem_nhds ψ0 hc
  refine ⟨fun s hs => ⟨?_, ?_⟩, fun W hW => ?_⟩
  · apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    have hev : ∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∀ i j,
        s * Y i j ∈ {u : k | ∀ o : k, valuation k o ≤ 1 → ψ0 (o * u) = 1} := by
      refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
      have hcont : Continuous fun Y : Matrix (Fin n) (Fin d) k => s * Y i j :=
        continuous_const.mul (continuous_id.matrix_elem i j)
      exact hcont.continuousAt.preimage_mem_nhds (by simpa using hK)
    filter_upwards [hev] with Y hY
    exact GlobalTheory.LinSchur.mem_latt.2 fun i j o ho => hY i j o ho
  · have hsub : (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ⊆
        {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ valuation k t * (valuation k s)⁻¹} := by
      intro Y hY i j
      have h1 := ker_int_lt ht fun o ho => GlobalTheory.LinSchur.mem_latt.1 hY i j o ho
      have hvs : valuation k s ≠ 0 := by simpa using hs
      rw [map_mul] at h1
      calc valuation k (Y i j) = valuation k s * valuation k (Y i j) * (valuation k s)⁻¹ := by
            rw [mul_comm (valuation k s), mul_assoc, mul_inv_cancel₀ hvs, mul_one]
        _ ≤ valuation k t * (valuation k s)⁻¹ := by gcongr
    have hcl : IsClosed (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) := by
      have e : (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) =
          ⋂ i, ⋂ j, ⋂ o : {o : k // valuation k o ≤ 1}, {Y | ψ0 (o.1 * (s * Y i j)) = 1} := by
        ext Y
        simp only [SetLike.mem_coe, GlobalTheory.LinSchur.mem_latt, Set.mem_iInter, Set.mem_setOf_eq, Subtype.forall]
      rw [e]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun o =>
        isClosed_eq (hc.comp (continuous_const.mul (continuous_const.mul (continuous_id.matrix_elem i j))))
          continuous_const
    exact (isCompact_ball_mat n d _).of_isClosed_subset hcl hsub
  · obtain ⟨c, hc0, hcW⟩ := exists_smul_int_mem' n d W hW
    refine ⟨t / c, div_ne_zero ht0 hc0, fun Y hY => ?_⟩
    have hx : ∀ i j, valuation k ((c⁻¹ • Y) i j) ≤ 1 := by
      intro i j
      have h1 := ker_int_lt ht fun o ho => GlobalTheory.LinSchur.mem_latt.1 hY i j o ho
      have e : (c⁻¹ • Y) i j = (t / c * Y i j) * t⁻¹ := by
        rw [Matrix.smul_apply, smul_eq_mul]
        field_simp
      rw [e, map_mul, map_inv₀]
      calc valuation k (t / c * Y i j) * (valuation k t)⁻¹ ≤ valuation k t * (valuation k t)⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hvt
    have := hcW _ hx
    rwa [smul_smul, mul_inv_cancel₀ hc0, one_smul] at this

end GlobalTheory.LinSchurLatt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterTrivialMatrixLatticeOpenCompactBasisStatement
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterTrivialMatrixLattice_open_compact_basis : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 → (∀ s : k, s ≠ 0 → IsOpen (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ∧ IsCompact (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k))) ∧ ∀ W ∈ 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∃ s : k, s ≠ 0 ∧ (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ⊆ W := by
  first | exact @GlobalTheory.LinSchurLatt.latt_open_compact_basis | exact GlobalTheory.LinSchurLatt.latt_open_compact_basis | (intros; apply GlobalTheory.LinSchurLatt.latt_open_compact_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyGLHarishChandraRecursio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyGLHarishChandraRecursio
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct GlobalTheory.ParabVirt
open scoped Classical

noncomputable section
namespace GlobalTheory.ShinPsiRec

variable {F : Type} [Field F]

def low (a n : ℕ) : Submodule F (Fin n → F) where
  carrier := {v | ∀ i : Fin n, a ≤ (i : ℕ) → v i = 0}
  add_mem' := fun {u v} hu hv i hi => by simp [hu i hi, hv i hi]
  zero_mem' := fun i _ => rfl
  smul_mem' := fun c v hv i hi => by simp [hv i hi]

theorem mem_stab_low_iff (a n : ℕ) (x : GL (Fin n) F) : x ∈ stab (low (F := F) a n) ↔ InPar a x := by
  rw [mem_stab]
  constructor
  · intro h i j hj hi
    have hv : (Pi.single j 1 : Fin n → F) ∈ low a n := by
      intro k hk
      have : k ≠ j := by intro e; subst e; omega
      simp [Pi.single_apply, this]
    have := h _ hv i hi
    simpa [Matrix.toLin'_apply, Matrix.mulVec_single_one] using this
  · intro h v hv i hi
    rw [Matrix.toLin'_apply]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : (j : ℕ) < a
    · rw [h i j hj hi, zero_mul]
    · rw [hv j (by omega), mul_zero]

def lowEquiv {a n : ℕ} (ha : a ≤ n) : low (F := F) a n ≃ₗ[F] (Fin a → F) where
  toFun v := fun i => v.1 (Fin.castLE ha i)
  map_add' u v := rfl
  map_smul' c v := rfl
  invFun w := ⟨fun k => if h : (k : ℕ) < a then w ⟨k, h⟩ else 0, fun k hk => dif_neg (by omega)⟩
  left_inv v := by
    ext k
    dsimp only
    split_ifs with h
    · rfl
    · exact (v.2 k (by omega)).symm
  right_inv w := by
    funext i
    simp

theorem resMat_low {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F) (hp : p ∈ stab (low (F := F) a n)) :
    resMat (low a n) (lowEquiv ha) ⟨p, hp⟩ = tl a (p : Matrix (Fin n) (Fin n) F) := by
  ext i j
  have hs : ((lowEquiv (F := F) ha).symm (Pi.single j 1)).1 = Pi.single (Fin.castLE ha j) 1 := by
    funext k
    change (if h : (k : ℕ) < a then (Pi.single j 1 : Fin a → F) ⟨k, h⟩ else 0) = _
    split_ifs with h
    · simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castLE]
    · have : k ≠ Fin.castLE ha j := by
        intro e; rw [e, Fin.val_castLE] at h; exact h j.2
      simp [Pi.single_apply, this]
  simp only [resMat, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.toMatrix'_apply, LinearEquiv.conj_apply_apply]
  change (Matrix.toLin' (p : Matrix (Fin n) (Fin n) F) ((lowEquiv (F := F) ha).symm (Pi.single j 1)).1)
    (Fin.castLE ha i) = _
  rw [hs, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  have hi : (i : ℕ) < n := by omega
  have hj : (j : ℕ) < n := by omega
  simp only [tl, ent, dif_pos (And.intro hi hj), Matrix.transpose_apply]
  rfl

theorem tl_isUnit {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F) (hp : InPar a p) :
    IsUnit (tl a (p : Matrix (Fin n) (Fin n) F)) := by
  have hp' := (mem_stab_low_iff a n p).2 hp
  rw [← resMat_low ha p hp']
  exact IsUnit.map (resMat (low a n) (lowEquiv ha)) (Group.isUnit _)

theorem coe_tlG {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F) (hp : InPar a p) :
    ((tlG a p : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = tl a (p : Matrix (Fin n) (Fin n) F) := by
  unfold tlG toG
  rw [dif_pos (tl_isUnit ha p hp)]
  rfl

theorem psi_restrict_low (S : F[X] → ℂ) {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F)
    (hp : p ∈ stab (low (F := F) a n)) :
    psi S (low (F := F) a n) ((Matrix.toLin' (p : Matrix (Fin n) (Fin n) F)).restrict hp) =
      psiG S a (tlG a p) := by
  rw [psiG, coe_tlG ha p ((mem_stab_low_iff a n p).1 hp), ← resMat_low ha p hp]
  simp only [resMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.toLin'_toMatrix']
  rw [psi_conj]

def resPsi (S : F[X] → ℂ) {n : ℕ} (x : GL (Fin n) F) (W : Submodule F (Fin n → F)) : ℂ :=
  if h : x ∈ stab W then psi S W ((Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)).restrict h) else 0

theorem finsum_rank_eq_hc [Finite F] (S : F[X] → ℂ) {a n : ℕ} (ha : a ≤ n) (x : GL (Fin n) F) :
    ∑ᶠ W : {W : Submodule F (Fin n → F) // Module.finrank F W = a}, resPsi S x W.1 =
      hc a (n - a) (psiG S a) (fun _ => 1) n x := by
  classical
  haveI : Finite (Submodule F (Fin n → F)) :=
    Finite.of_injective (fun W : Submodule F (Fin n → F) => (W : Set (Fin n → F))) SetLike.coe_injective
  letI := Fintype.ofFinite (GL (Fin n) F)
  letI := Fintype.ofFinite (Submodule F (Fin n → F))
  set W₀ := low (F := F) a n with hW₀def
  have hW₀ : Module.finrank F W₀ = a := (lowEquiv ha).finrank_eq.trans (Module.finrank_fin_fun F)
  let π : GL (Fin n) F → {W : Submodule F (Fin n → F) // Module.finrank F W = a} := fun t =>
    ⟨W₀.map (lin t).toLinearMap, (LinearEquiv.finrank_map_eq _ _).trans hW₀⟩
  have hs : Function.Surjective π := by
    intro W
    obtain ⟨f⟩ : Nonempty (W₀ ≃ₗ[F] W.1) :=
      FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (hW₀.trans W.2.symm)
    obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
    obtain ⟨t, rfl⟩ := lin_surjective g
    refine ⟨t, Subtype.ext ?_⟩
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v, hv, rfl⟩
      have := (f ⟨v, hv⟩).2
      rw [hg] at this
      exact this
    · exact (π t).2.trans W.2.symm
  have hsum := sum_fibres (stab W₀) π hs
    (fun s t => Subtype.ext_iff.trans (map_eq_map_iff W₀ s t)) (fun W => resPsi S x W.1)
  have hg : ∀ t : GL (Fin n) F, gal (RingHom.id F) n t = t := by
    intro t; ext i j; simp [gal]
  have hterm : ∀ t : GL (Fin n) F, resPsi S x (π t).1 =
      (if InPar a (t⁻¹ * x * gal (RingHom.id F) n t) then
        psiG S a (tlG a (t⁻¹ * x * gal (RingHom.id F) n t)) *
          (fun _ => (1 : ℂ)) (brG a (n - a) (t⁻¹ * x * gal (RingHom.id F) n t)) else 0) := by
    intro t
    rw [hg, mul_one]
    simp only [resPsi, π]
    by_cases h : t⁻¹ * x * t ∈ stab W₀
    · have h' := (conj_mem_stab_iff W₀ x t).1 h
      rw [dif_pos h', if_pos ((mem_stab_low_iff a n _).1 h), ← psi_restrict_low S ha _ h,
        ← psi_conj F S _ _ ((lin t).submoduleMap W₀)]
      congr 1
      refine LinearMap.ext fun v => ?_
      obtain ⟨w, rfl⟩ := ((lin t).submoduleMap W₀).surjective v
      rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
      ext1
      change lin x (lin t w) = lin t (lin (t⁻¹ * x * t) w)
      rw [← lin_mul, ← lin_mul, mul_assoc, mul_inv_cancel_left]
    · rw [dif_neg (fun h' => h ((conj_mem_stab_iff W₀ x t).2 h')),
        if_neg (fun h'' => h ((mem_stab_low_iff a n _).2 h''))]
  have hcard : Nat.card {p : GL (Fin n) F // InPar a p} = Nat.card (stab W₀) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun p => (mem_stab_low_iff a n p).symm)
  have hc0 : (Nat.card (stab W₀) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  simp only [hc, hcTw]
  rw [hcard, ← finsum_congr hterm, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, hsum,
    inv_mul_cancel_left₀ hc0]

end GlobalTheory.ShinPsiRec

namespace GlobalTheory.ShinPsiRec

theorem ne_top_iff_finrank_lt {F : Type} [Field F] {n : ℕ} (W : Submodule F (Fin n → F)) :
    W ≠ ⊤ ↔ Module.finrank F W < n := by
  constructor
  · intro h
    have := Submodule.finrank_lt h
    rwa [Module.finrank_fin_fun] at this
  · intro h htop
    rw [htop, finrank_top, Module.finrank_fin_fun] at h
    exact lt_irrefl _ h

theorem psiG_eq_chG_sub_hc (F : Type) [Field F] [Finite F] (S : F[X] → ℂ) (n : ℕ) (x : GL (Fin n) F) :
    psiG S n x = chG S n x - ∑ a ∈ Finset.range n, hc a (n - a) (psiG S a) (fun _ => 1) n x := by
  classical
  haveI : Finite (Submodule F (Fin n → F)) :=
    Finite.of_injective (fun W : Submodule F (Fin n → F) => (W : Set (Fin n → F))) SetLike.coe_injective
  letI := Fintype.ofFinite (Submodule F (Fin n → F))
  show psi S _ _ = S _ - _
  rw [psi_eq, Matrix.charpoly_toLin']
  congr 1
  rw [Finset.sum_congr rfl fun a ha =>
    (finsum_rank_eq_hc S (le_of_lt (Finset.mem_range.1 ha)) x).symm]
  have step : ∀ a : ℕ, ∑ᶠ W : {W : Submodule F (Fin n → F) // Module.finrank F W = a}, resPsi S x W.1 =
      ∑ W : Submodule F (Fin n → F), if Module.finrank F W = a then resPsi S x W else 0 := by
    intro a
    rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) _).symm
  simp only [step]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq]
  rw [finsum_eq_sum_of_fintype]
  rw [Finset.sum_congr rfl (g := fun W => resPsi S x W.1) fun W _ => by
    unfold resPsi; rw [dif_pos (show x ∈ stab W.1 from W.2.2)]]
  rw [← Finset.sum_subtype (Finset.univ.filter fun W : Submodule F (Fin n → F) => W ≠ ⊤ ∧ ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W)
    (fun W => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) (resPsi S x), Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  by_cases hx : ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W
  · simp only [Finset.mem_range, ne_top_iff_finrank_lt, and_iff_left hx]
  · have hx' : x ∉ stab W := hx
    simp [resPsi, hx', hx]

end GlobalTheory.ShinPsiRec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyGLHarishChandraRecursioStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion : ∀ (F : Type) [Field F] [Finite F], ∀ (S : F[X] → ℂ) (n : ℕ) (x : GL (Fin n) F), psiG S n x = chG S n x - ∑ a ∈ Finset.range n, hc a (n - a) (psiG S a) (fun _ => 1) n x := by
  first | (exact @GlobalTheory.ShinPsiRec.psiG_eq_chG_sub_hc) | (exact GlobalTheory.ShinPsiRec.psiG_eq_chG_sub_hc) | (intros; apply GlobalTheory.ShinPsiRec.psiG_eq_chG_sub_hc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLinearEquivAddHaarLocalField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLinearEquivAddHaarLocalField
noncomputable section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped NNReal ENNReal

namespace GlobalTheory.KSp

theorem map_linearEquiv_haar : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (T : V ≃ₗ[F] V), μ.map T = (distribHaarChar F (LinearEquiv.det T))⁻¹ • μ := by
  intro F _ _ _ _ _ V _ _ _ _ _ _ _ μ _ T
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable F
  haveI := GlobalTheory.SplitWeil.t2Space F
  set n := Module.finrank F V
  set b := Module.finBasis F V
  set e : V ≃ₗ[F] (Fin n → F) := b.equivFun
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup F V
  have hec : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hes : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

  let E : V ≃L[F] (Fin n → F) := { e with continuous_toFun := hec, continuous_invFun := hes }
  let Em : V ≃ᵐ (Fin n → F) := E.toHomeomorph.toMeasurableEquiv
  have hEm : (Em : V → Fin n → F) = e := rfl
  have hEms : (Em.symm : (Fin n → F) → V) = e.symm := rfl
  let P : Measure (Fin n → F) := Measure.pi fun _ => (Measure.addHaar : Measure F)
  set X := μ.map Em with hX
  haveI : X.IsAddHaarMeasure := E.isAddHaarMeasure_map μ
  set M := LinearMap.toMatrix b b T.toLinearMap
  have hM : ∀ y, M.mulVec (e y) = e (T y) := fun y => by
    simp [M, e, LinearMap.toMatrix_mulVec_repr]
  have hdet : ((LinearEquiv.det T : Fˣ) : F) = M.det := by
    simp [M, LinearMap.det_toMatrix]
  set d := distribHaarChar F (LinearEquiv.det T)
  have key : (d : ℝ≥0∞) • P.map M.mulVec = P :=
    GlobalTheory.WeilM.smul_map_mulVec_pi (Measure.addHaar : Measure F) M (LinearEquiv.det T) hdet
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by simpa using (distribHaarChar_pos (A := F) (g := LinearEquiv.det T)).ne'
  have hPM : P.map M.mulVec = ((d⁻¹ : ℝ≥0) : ℝ≥0∞) • P := by
    conv_rhs => rw [← key]
    rw [smul_smul, ENNReal.coe_inv (by simpa using hd0), ENNReal.inv_mul_cancel hd0 ENNReal.coe_ne_top,
      one_smul]
  have hXP : X = (Measure.addHaarScalarFactor X P : ℝ≥0∞) • P := Measure.isAddLeftInvariant_eq_smul X P
  have hmv : Measurable M.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  have hXM : X.map M.mulVec = ((d⁻¹ : ℝ≥0) : ℝ≥0∞) • X := by
    rw [hXP, Measure.map_smul _ hmv.aemeasurable, hPM, smul_comm]
  have hμ : μ = X.map Em.symm := by rw [hX, Measure.map_map Em.symm.measurable Em.measurable]; simp
  have hcomp : (T : V → V) ∘ Em.symm = Em.symm ∘ M.mulVec := by
    funext x
    show T (e.symm x) = e.symm (M.mulVec x)
    apply e.injective
    rw [← hM, e.apply_symm_apply, e.apply_symm_apply]
  have hTm : Measurable (T : V → V) := by
    have : Continuous (T : V → V) := IsModuleTopology.continuous_of_linearMap T.toLinearMap
    exact this.measurable
  calc μ.map T = (X.map Em.symm).map T := by rw [← hμ]
    _ = X.map ((T : V → V) ∘ Em.symm) := Measure.map_map hTm Em.symm.measurable
    _ = X.map (Em.symm ∘ M.mulVec) := by rw [hcomp]
    _ = (X.map M.mulVec).map Em.symm := (Measure.map_map Em.symm.measurable hmv).symm
    _ = (d⁻¹ : ℝ≥0) • μ := by rw [hXM, Measure.map_smul _ Em.symm.measurable.aemeasurable, ← hμ]; rfl

end GlobalTheory.KSp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLinearEquivAddHaarLocalFieldStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_linearEquiv_addHaar_localField : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : V ≃ₗ[F] V), μ.map T = (distribHaarChar F (LinearEquiv.det T))⁻¹ • μ := by
  first | exact @GlobalTheory.KSp.map_linearEquiv_haar | exact GlobalTheory.KSp.map_linearEquiv_haar | (intros; apply GlobalTheory.KSp.map_linearEquiv_haar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedWeierstrassPTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassConstantQExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassConstantQExpansion
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem weierstrass_constant_eq_E2 (τ : ℍ) : gN τ = (-1 / 12) * EisensteinSeries.E2 τ := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [gN, EisensteinSeries.E2, Pi.smul_apply, smul_eq_mul, riemannZeta_two, mul_pow, Complex.I_sq]
  field_simp
  ring

theorem hasQ_gN : ∀ (N : ℕ) [NeZero N], HasQ N gN (cG N) := by
  intro N _ τ
  have hN : N ≠ 0 := NeZero.ne N
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hinj : Function.Injective (fun m : ℕ => N * m) := fun a b h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN) h
  rw [← hinj.hasSum_iff]
  · have h := (EisensteinSeries.hasSum_qExpansion_E2 (z := τ)).mul_left (-1 / 12 : ℂ)
    rw [weierstrass_constant_eq_E2]
    convert! h using 1
    funext m
    have he : Complex.exp (2 * Real.pi * Complex.I * ((N * m : ℕ) : ℂ) * τ / N) =
        Complex.exp (2 * Real.pi * Complex.I * τ) ^ m := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; field_simp
    simp only [Function.comp, he, smul_eq_mul]
    by_cases hm : m = 0
    · simp [hm, cG]
    · have h1 : N * m ≠ 0 := mul_ne_zero hN hm
      simp only [cG, if_neg h1, if_neg hm, if_pos (dvd_mul_right N m),
        Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hN)]
      ring
  · intro k hk
    have hd : ¬ N ∣ k := fun ⟨m, hm⟩ => hk ⟨m, hm.symm⟩
    have h0 : k ≠ 0 := fun h => hd (h ▸ dvd_zero N)
    simp [cG, hd, h0]

end GlobalTheory.WpFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassConstantQExpansionStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_constant_q_expansion : ∀ (N : ℕ) [NeZero N], HasQ N gN (cG N) := by
  first | exact @GlobalTheory.WpFam.hasQ_gN | exact GlobalTheory.WpFam.hasQ_gN | (intros; apply GlobalTheory.WpFam.hasQ_gN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedWeierstrassPTorsion
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.ExpP

theorem main : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), HasQ N (wp N x) (cP N x) := by
  intro N _ x τ
  by_cases hx : x = 0
  · subst hx
    have h0 : wp N 0 τ = 0 := by
      simp [wp, tors, PeriodPair.weierstrassP_zero]
    simp only [cP, h0, if_true]
    simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  · have hB := GlobalTheory.T.weierstrass_division_value_q_expansion N x hx τ
    have hG := GlobalTheory.T.weierstrass_constant_q_expansion N τ
    have hd := hB.sub hG
    have hw : wp N x τ = wB N x τ - gN τ := by simp [wB]
    have hf : (fun n : ℕ => cP N x n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) =
        fun n : ℕ => cB N x n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N) -
          cG N n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N) := by
      funext n
      simp [cP, hx, sub_mul]
    rw [hw, hf]
    exact hd

end GlobalTheory.WpFam.ExpP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedWeierstrassPTorsionStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), HasQ N (wp N x) (cP N x) := by
  first | exact @GlobalTheory.WpFam.ExpP.main | exact GlobalTheory.WpFam.ExpP.main | (intros; apply GlobalTheory.WpFam.ExpP.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenStabilizerSchwartzBruhat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenStabilizerSchwartzBruhat
open Matrix Topology GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM

namespace GlobalTheory.OmAStab

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLocallyConstant_of_isOpen_ker {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] (χ : G →* H) (hχ : IsOpen (χ.ker : Set G)) : IsLocallyConstant χ := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_
  have hn : (fun g => g0⁻¹ * g) ⁻¹' (χ.ker : Set G) ∈ 𝓝 g0 :=
    (hχ.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : χ (g0⁻¹ * g) = 1 := hg
  rw [map_mul, map_inv, inv_mul_eq_one] at hg'
  exact hg'.symm

theorem continuous_invT_val {D : Type} [Fintype D] [DecidableEq D] :
    Continuous fun h : GL D k => (invT h).val :=
  (Units.continuous_coe_inv (M := Matrix D D k)).matrix_transpose

theorem continuous_invT_inv_val {D : Type} [Fintype D] [DecidableEq D] :
    Continuous fun h : GL D k => ((invT h)⁻¹).val :=
  (Units.continuous_val (M := Matrix D D k)).matrix_transpose

theorem isLocallyConstant_comp_invT {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    {Φ : Matrix A D k → ℂ} (hΦ : Φ ∈ SB (Matrix A D k)) :
    IsLocallyConstant fun h : GL D k => fun X : Matrix A D k => Φ (X * (invT h).val) := by
  obtain ⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun h0 => ?_
  set M : GL D k → Matrix D D k := fun h => (invT h).val with hM
  set N : GL D k → Matrix D D k := fun h => ((invT h)⁻¹).val with hN
  have hMc : Continuous M := continuous_invT_val
  have hNc : Continuous N := continuous_invT_inv_val
  have hMN : ∀ h, M h * N h = 1 := fun h => Units.mul_inv (invT h)
  have hNM : ∀ h, N h * M h = 1 := fun h => Units.inv_mul (invT h)
  have hq : IsLocallyConstant fun p : GL D k × Matrix A D k => Φ (p.2 * M p.1) :=
    hl.comp_continuous (continuous_snd.matrix_mul (hMc.comp continuous_fst))
  have hr : IsLocallyConstant fun p : GL D k × Matrix A D k => Φ (p.2 * N p.1 * M h0) :=
    hl.comp_continuous ((continuous_snd.matrix_mul (hNc.comp continuous_fst)).matrix_mul continuous_const)
  have hK1 : IsCompact ((fun Y => Y * N h0) '' tsupport Φ) :=
    hK.isCompact.image (continuous_id.matrix_mul continuous_const)
  have htend : ∀ X : Matrix A D k, Filter.Tendsto (fun p : GL D k × Matrix A D k => (h0, p.2))
      (𝓝 (h0, X)) (𝓝 (h0, X)) := fun X => (continuous_const.prodMk continuous_snd).tendsto' _ _ rfl
  have e1 : ∀ᶠ h in 𝓝 h0, ∀ X ∈ (fun Y => Y * N h0) '' tsupport Φ, Φ (X * M h) = Φ (X * M h0) := by
    refine hK1.eventually_forall_of_forall_eventually fun X _ => ?_
    have a1 := hq.eventually_eq (h0, X)
    have a2 := (htend X).eventually (hq.eventually_eq (h0, X))
    filter_upwards [a1, a2] with p hp1 hp2
    exact hp1.trans hp2.symm
  have e2 : ∀ᶠ h in 𝓝 h0, ∀ Y ∈ tsupport Φ, Φ (Y * N h * M h0) = Φ Y := by
    refine hK.isCompact.eventually_forall_of_forall_eventually fun Y _ => ?_
    have a2 := (continuous_snd.tendsto (h0, Y)).eventually (hl.eventually_eq Y)
    filter_upwards [hr.eventually_eq (h0, Y), a2] with p hp hp2
    refine hp.trans (Eq.trans ?_ hp2.symm)
    show Φ (Y * N h0 * M h0) = Φ Y
    rw [Matrix.mul_assoc, hNM, Matrix.mul_one]
  filter_upwards [e1, e2] with h h1 h2
  funext X
  show Φ (X * M h) = Φ (X * M h0)
  by_cases hA : X * M h0 ∈ tsupport Φ
  · exact h1 X ⟨X * M h0, hA, by simp only [Matrix.mul_assoc, hMN, Matrix.mul_one]⟩
  by_cases hB : X * M h ∈ tsupport Φ
  · have := h2 _ hB
    rw [Matrix.mul_assoc X, hMN, Matrix.mul_one] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hA, image_eq_zero_of_notMem_tsupport hB]

theorem isOpen_omA_stab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a d : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k),
      IsOpen {h : GL (Fin d) k | GlobalTheory.SplitFlip.omA ν β 1 h Φ = Φ} := by
  intro k _ _ _ _ a d ν β hβ Φ hΦ
  have hb : IsLocallyConstant fun h : GL (Fin d) k => β (gdet h) :=
    (isLocallyConstant_of_isOpen_ker β hβ).comp_continuous Matrix.GeneralLinearGroup.continuous_det
  have hn : IsLocallyConstant fun h : GL (Fin d) k => GlobalTheory.SplitWeil.nabs k (gdet h) :=
    (GlobalTheory.SplitWeil.isLocallyConstant_nabs k).comp_continuous Matrix.GeneralLinearGroup.continuous_det
  have hc : IsLocallyConstant fun h : GL (Fin d) k => omA ν β 1 h Φ := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun h0 => ?_
    filter_upwards [hb.eventually_eq h0, hn.eventually_eq h0,
      (isLocallyConstant_comp_invT hΦ).eventually_eq h0] with h e1 e2 e3
    funext X
    have e4 := congrFun e3 X
    simp only [omA, apow, inv_one, Units.val_one, Matrix.one_mul, e1, e2, e4]
  exact hc.isOpen_fiber Φ

end GlobalTheory.OmAStab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenStabilizerSchwartzBruhatStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_stabilizer_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), IsOpen {h : GL (Fin d) k | GlobalTheory.SplitFlip.omA ν β 1 h Φ = Φ} := by
  first | exact @GlobalTheory.OmAStab.isOpen_omA_stab | exact GlobalTheory.OmAStab.isOpen_omA_stab | (intros; apply GlobalTheory.OmAStab.isOpen_omA_stab <;> assumption)
end
end
