module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepA
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepC
noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {ψ : AddChar (AF F) ℂ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)}

namespace LatC

theorem relIndex_ne_zero_of_compact {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (H K : AddSubgroup G) (hK : IsCompact (K : Set G)) {V : Set G} (hV : V ∈ 𝓝 (0 : G))
    (h : ∀ u ∈ V, u ∈ K → u ∈ H) : H.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have h1 : ((H.addSubgroupOf K : AddSubgroup K) : Set K) ∈ 𝓝 (0 : K) := by
    have h2 : (Subtype.val ⁻¹' V : Set K) ∈ 𝓝 (0 : K) := continuous_subtype_val.continuousAt.preimage_mem_nhds hV
    exact Filter.mem_of_superset h2 fun u hu => h u.1 hu u.2
  haveI := AddSubgroup.quotient_finite_of_isOpen (H.addSubgroupOf K) (AddSubgroup.isOpen_of_mem_nhds _ h1)
  exact AddSubgroup.index_ne_zero_of_finite

theorem ft_mem {α : Af F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf F) {γ : Matrix (Fin nT) (Fin nS) E} (hγ : γ ∈ Λ) :
    algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F := F) γ ∈ latOF F E nS nT Λ :=
  AddSubgroup.subset_closure ⟨α, hα, γ, hγ, rfl⟩

theorem hOF_rat (M N : Matrix (Fin nT) (Fin nS) E) :
    hOF σ JS JT (ratWF (F := F) M) (ratWF (F := F) N) = incAF F E (hRatF σ JS JT M N) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hOF, hRatF, ratWF, Matrix.map_apply, GlobalTheory.HeisLineF.cAF_incAF, map_sum, map_mul]

theorem sympl_ft (hσ : ∀ x, σ (σ x) = x) (α β : Af F) (M N : Matrix (Fin nT) (Fin nS) E) :
    symplOF σ JS JT ξ₀ (algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F := F) M)
      (algebraMap (AF F) (AEF F E) (pairA F 0 β) • ratWF (F := F) N) =
      pairA F 0 (α * β * algebraMap F (Af F) (Algebra.trace F E (ξ₀ * hRatF σ JS JT M N))) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have e : hOF σ JS JT (algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F := F) M)
      (algebraMap (AF F) (AEF F E) (pairA F 0 β) • ratWF (F := F) N) =
      algebraMap (AF F) (AEF F E) (pairA F 0 α) * (algebraMap (AF F) (AEF F E) (pairA F 0 β) *
        incAF F E (hRatF σ JS JT M N)) := by
    rw [hOF_smul_left, ← hOF_rat, ← hOF_smul_right σ JS JT hσ (algebraMap (AF F) (AEF F E) (pairA F 0 β)),
      GlobalTheory.HeisThetaF.cAF_algebraMap]
  have e2 : incAF F E ξ₀ * (algebraMap (AF F) (AEF F E) (pairA F 0 α) * (algebraMap (AF F) (AEF F E) (pairA F 0 β) *
        incAF F E (hRatF σ JS JT M N))) = (pairA F 0 α * pairA F 0 β) ⊗ₜ[F] (ξ₀ * hRatF σ JS JT M N) := by
    show ((1 : AF F) ⊗ₜ[F] ξ₀) * ((pairA F 0 α ⊗ₜ[F] (1 : E)) * ((pairA F 0 β ⊗ₜ[F] (1 : E)) *
      ((1 : AF F) ⊗ₜ[F] hRatF σ JS JT M N))) = _
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [symplOF, e, e2, GlobalTheory.LatVac.trace_tmul]
  refine Prod.ext ?_ rfl
  show (0 : Ainf F) * 0 * _ = 0
  rw [zero_mul, zero_mul]

theorem hRatF_smul (c : E) (M N : Matrix (Fin nT) (Fin nS) E) : hRatF σ JS JT (c • M) N = c * hRatF σ JS JT M N := by
  simp only [hRatF, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem psi_ft (hσ : ∀ x, σ (σ x) = x) (hψ : IsStd ψ) (h : RatSD σ JS JT ξ₀ Λ) {α β : Af F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf F)
    (hβ : β ∈ Formalism.MainNotions.StandardLattice.intAf F) {M N : Matrix (Fin nT) (Fin nS) E} (hM : M ∈ Λ) (hN : N ∈ Λ) :
    ψ (symplOF σ JS JT ξ₀ (algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F := F) M)
      (algebraMap (AF F) (AEF F E) (pairA F 0 β) • ratWF (F := F) N)) = 1 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [sympl_ft hσ]
  refine PositivityTheory.ThKG.Tow.Pln.psi_int hψ _ (fun a => ?_) _ (fun v => mul_mem (hα v) (hβ v))
  obtain ⟨n, hn⟩ := (h _).1 (Λ.smul_mem (algebraMap (𝓞 F) (𝓞 E) a) hM) N hN
  refine ⟨n, ?_⟩
  have e : algebraMap (𝓞 F) (𝓞 E) a • M = algebraMap F E (a : F) • M := rfl
  rw [← hn, e, hRatF_smul, ← smul_eq_mul, ← map_smul, Algebra.trace_trace, Algebra.smul_def, mul_left_comm]

theorem psi_lat (hσ : ∀ x, σ (σ x) = x) (hψ : IsStd ψ) (h : RatSD σ JS JT ξ₀ Λ) {x y : WOF F E nS nT}
    (hx : x ∈ latOF F E nS nT Λ) (hy : y ∈ latOF F E nS nT Λ) : ψ (symplOF σ JS JT ξ₀ x y) = 1 := by
  have z1 : ∀ y, symplOF σ JS JT ξ₀ (0 : WOF F E nS nT) y = 0 := fun y => by
    have := GlobalTheory.HeisLineF.symplOF_add_left σ JS JT ξ₀ (0 : WOF F E nS nT) 0 y
    rw [add_zero] at this
    exact left_eq_add.1 this
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, M, hM, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨β, hβ, N, hN, rfl⟩ := hy
      exact psi_ft hσ hψ h hα hβ hM hN
    | zero => rw [GlobalTheory.HeisLineF.symplOF_zero_right, AddChar.map_zero_eq_one]
    | add u v _ _ hu hv => rw [GlobalTheory.HeisLineF.symplOF_add_right, AddChar.map_add_eq_mul, hu, hv, one_mul]
    | neg u _ hu =>
      have := GlobalTheory.HeisLineF.symplOF_add_right σ JS JT ξ₀
        (algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F := F) M) u (-u)
      rw [add_neg_cancel, GlobalTheory.HeisLineF.symplOF_zero_right] at this
      have h2 := congrArg ψ this
      rw [AddChar.map_zero_eq_one, AddChar.map_add_eq_mul, hu, one_mul] at h2
      exact h2.symm
  | zero => rw [z1, AddChar.map_zero_eq_one]
  | add u v _ _ hu hv => rw [GlobalTheory.HeisLineF.symplOF_add_left, AddChar.map_add_eq_mul, hu, hv, one_mul]
  | neg u _ hu =>
    have := GlobalTheory.HeisLineF.symplOF_add_left σ JS JT ξ₀ u (-u) y
    rw [add_neg_cancel, z1] at this
    have h2 := congrArg ψ this
    rw [AddChar.map_zero_eq_one, AddChar.map_add_eq_mul, hu, one_mul] at h2
    exact h2.symm

theorem one_int : (1 : Af F) ∈ Formalism.MainNotions.StandardLattice.intAf F := fun v => by
  rw [map_one]; exact one_mem _

theorem lat_sd (hσ : ∀ x, σ (σ x) = x) (hψ : IsStd ψ) (hg : GoodLat Λ) (h : RatSD σ JS JT ξ₀ Λ) :
    SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  intro x
  refine ⟨fun hx a ha => psi_lat hσ hψ h hx ha, fun H => ?_⟩
  obtain ⟨γ, hγ⟩ := lat_approx hg (x : WOF F E nS nT) x.fin
  have hΛ : γ ∈ Λ := (h γ).2 fun N hN => by
    have h1 := ft_mem (F := F) one_int hN
    have h2 : ψ (symplOF σ JS JT ξ₀ (x : WOF F E nS nT) _) = 1 := H (XFF.mk _ (lat_fin h1)) h1
    have h3 := psi_lat (JS := JS) (JT := JT) (ξ₀ := ξ₀) hσ hψ h hγ h1
    rw [← sub_add_cancel (x : WOF F E nS nT) (algebraMap (AF F) (AEF F E) (pairA F 0 1) • ratWF (F := F) γ),
      GlobalTheory.HeisLineF.symplOF_add_left, AddChar.map_add_eq_mul, XFF.coe_mk, h3, one_mul, sympl_ft hσ, one_mul, one_mul,
      PositivityTheory.ThKG.Tow.Pln.psi_fin_rat hψ, Algebra.trace_trace, Complex.exp_eq_one_iff] at h2
    obtain ⟨n, hn⟩ := h2
    refine ⟨n, ?_⟩
    have h4 : ((Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT γ N) : ℚ) : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
      rw [hn]; ring
    exact_mod_cast h4
  have h5 := add_mem hγ (ft_mem (F := F) one_int hΛ)
  rw [sub_add_cancel] at h5
  exact h5

theorem continuous_mtF {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Continuous (mtF (F := F) σ J) ∧ Continuous fun g : GAF (F := F) σ J => mtF σ J g⁻¹ :=
  ⟨Units.continuous_val.comp continuous_subtype_val, Units.continuous_coe_inv.comp continuous_subtype_val⟩

theorem continuous_act : Continuous fun z : (GAF (F := F) σ JS × GAF (F := F) σ JT) × WOF F E nS nT =>
    actOF σ JS JT z.1.1 z.1.2 z.2 := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  exact (((continuous_mtF JT).1.comp (continuous_snd.comp continuous_fst)).matrix_mul continuous_snd).matrix_mul
    ((continuous_mtF JS).2.comp (continuous_fst.comp continuous_fst))

theorem continuous_act_left (x : WOF F E nS nT) :
    Continuous fun p : GAF (F := F) σ JS × GAF (F := F) σ JT => actOF σ JS JT p.1 p.2 x := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  exact (((continuous_mtF JT).1.comp continuous_snd).matrix_mul continuous_const).matrix_mul
    ((continuous_mtF JS).2.comp continuous_fst)

theorem continuous_act_right (g : GAF (F := F) σ JS) (h : GAF (F := F) σ JT) :
    Continuous fun x : WOF F E nS nT => actOF σ JS JT g h x := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem idx_ne_zero (hg : GoodLat Λ) (B : Submodule (𝓞 E) (XFF F E nS nT)) (φ : WOF F E nS nT →+ WOF F E nS nT)
    (hφ : Continuous φ) (h1 : ∀ l ∈ latOF F E nS nT Λ, (φ l).map (infPartF F E) = 0)
    (h2 : ∀ b ∈ B, ∃ l ∈ latOF F E nS nT Λ, φ l = b) : idx (latF F E nS nT Λ) B ≠ 0 := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have e : idx (latF F E nS nT Λ) B = (latOF F E nS nT Λ).relIndex (B.toAddSubgroup.map (XFF.incl F E nS nT)) :=
    AddSubgroup.relIndex_comap (latOF F E nS nT Λ) (XFF.incl F E nS nT) B.toAddSubgroup
  obtain ⟨V, hV, hV'⟩ := lat_nhds (F := F) hg
  have h3 := relIndex_ne_zero_of_compact (latOF F E nS nT Λ) ((latOF F E nS nT Λ).map φ)
    ((lat_compact hg).image hφ) hV (by rintro _ hu ⟨l, hl, rfl⟩; exact hV' _ hu (h1 l hl))
  rw [e]
  refine fun h0 => h3 (AddSubgroup.relIndex_eq_zero_of_le_right ?_ h0)
  rintro _ ⟨b, hb, rfl⟩
  exact h2 b hb

theorem lat_lev (hg : GoodLat Λ) (U : AddSubgroup (WOF F E nS nT)) (hU : IsOpen (U : Set (WOF F E nS nT))) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latOF F E nS nT Λ, N • u ∈ U := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have h := relIndex_ne_zero_of_compact U (latOF F E nS nT Λ) (lat_compact hg) (hU.mem_nhds U.zero_mem)
    fun u hu _ => hu
  exact ⟨_, Nat.pos_of_ne_zero h, fun u hu => AddSubgroup.nsmul_relIndex_mem U hu⟩

theorem nsmul_inv_smul {M : Type} [AddCommGroup M] [Module (AEF F E) M] {N : ℕ} (hN : 0 < N) (x : M) :
    N • (incAF F E (N : E)⁻¹ • x) = x := by
  have h : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [← Nat.cast_smul_eq_nsmul (AEF F E), smul_smul, ← map_natCast (incAF F E) N, ← map_mul, mul_inv_cancel₀ h, map_one,
    one_smul]

theorem fin_smul (a : AEF F E) {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) : (a • u).map (infPartF F E) = 0 :=
  (finSubF F E nS nT).smul_mem a hu

theorem near (hg : GoodLat Λ) : ∀ᶠ p in 𝓝 (1 : GAF (F := F) σ JS × GAF (F := F) σ JT),
    ∀ a ∈ latF F E nS nT Λ, rhoFF σ JS JT p a ∈ latF F E nS nT Λ := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  obtain ⟨V, hV, hV'⟩ := lat_nhds (F := F) hg
  have h := (lat_compact (F := F) hg).eventually_forall_of_forall_eventually
    (x₀ := (1 : GAF (F := F) σ JS × GAF (F := F) σ JT)) (P := fun p y => actOF σ JS JT p.1 p.2 y - y ∈ V) fun y _ => by
      have h1 := ((continuous_act (σ := σ) (JS := JS) (JT := JT)).sub continuous_snd).continuousAt
        (x := ((1 : GAF (F := F) σ JS × GAF (F := F) σ JT), y))
      refine h1.preimage_mem_nhds ?_
      show V ∈ 𝓝 (actOF σ JS JT 1 1 y - y)
      rw [actOF_one, sub_self]
      exact hV
  filter_upwards [h] with p hp a ha
  have h2 := hV' _ (hp a ha) (rhoFF σ JS JT p a - a).fin
  have h3 := add_mem h2 (show (a : WOF F E nS nT) ∈ latOF F E nS nT Λ from ha)
  rw [sub_add_cancel] at h3
  exact h3

theorem near' (hg : GoodLat Λ) (x : XFF F E nS nT) (N : ℕ) (hN : 0 < N) :
    ∀ᶠ p in 𝓝 (1 : GAF (F := F) σ JS × GAF (F := F) σ JT), ∃ l ∈ latF F E nS nT Λ, rhoFF σ JS JT p x = x + N • l := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  obtain ⟨V, hV, hV'⟩ := lat_nhds (F := F) hg
  have h0 : Continuous fun p : GAF (F := F) σ JS × GAF (F := F) σ JT =>
      incAF F E (N : E)⁻¹ • (actOF σ JS JT p.1 p.2 x - x) :=
    by
      have h00 : Continuous fun p : GAF (F := F) σ JS × GAF (F := F) σ JT => actOF σ JS JT p.1 p.2 x :=
        continuous_act_left _
      have h01 : Continuous fun p : GAF (F := F) σ JS × GAF (F := F) σ JT => actOF σ JS JT p.1 p.2 x - x :=
        h00.sub continuous_const
      exact h01.const_smul (incAF F E (N : E)⁻¹)
  have h1 : (fun p : GAF (F := F) σ JS × GAF (F := F) σ JT =>
      incAF F E (N : E)⁻¹ • (actOF σ JS JT p.1 p.2 x - x)) ⁻¹' V ∈ 𝓝 1 := by
    refine h0.continuousAt.preimage_mem_nhds ?_
    show V ∈ 𝓝 (incAF F E (N : E)⁻¹ • (actOF σ JS JT 1 1 x - x))
    rw [actOF_one, sub_self, smul_zero]
    exact hV
  filter_upwards [h1] with p hp
  refine ⟨incAF F E (N : E)⁻¹ • (rhoFF σ JS JT p x - x), hV' _ hp (XFF.fin _), ?_⟩
  rw [nsmul_inv_smul hN, add_sub_cancel]

end LatC

end PositivityTheory.ThKW

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.RowsStackRight
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sig_sig (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem exists_nsmul_mem {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} (h : L.IsFullLattice E) (v : Fin n → E) :
    ∃ N : ℕ, 0 < N ∧ N • v ∈ L := by
  letI := h
  have hv : v ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [Submodule.IsFullLattice.span_eq_top]; trivial
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ v hv
  rw [Submodule.span_eq] at ht
  have ht0 : (t : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero t.2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {(t : 𝓞 E)}))
  refine ⟨Ideal.absNorm (Ideal.span {(t : 𝓞 E)}), Nat.pos_of_ne_zero fun h0 => ht0 ?_, ?_⟩
  · exact Ideal.span_singleton_eq_bot.1 (Ideal.absNorm_eq_zero_iff.1 h0)
  · rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hc, mul_smul]
    exact L.smul_mem c ht

theorem trace_int_iff (z : E) : (∃ n : ℤ, Algebra.trace ℚ E z = n) ↔ IsIntegral ℤ (Algebra.trace ℚ E z) := by
  rw [IsIntegrallyClosed.isIntegral_iff]
  exact ⟨fun ⟨n, h⟩ => ⟨n, h.symm⟩, fun ⟨n, h⟩ => ⟨n, h.symm⟩⟩

section Tensor

variable {n d : ℕ}

def ctr (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (t : Fin n → E) :
    Matrix (Fin n) (Fin d) E →ₗ[𝓞 E] (Fin d → E) where
  toFun M := fun a => ∑ j, M j a * ∑ k, σ (t k) * J j k
  map_add' M M' := by
    funext a
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    funext a
    simp [Algebra.smul_def, Finset.mul_sum, mul_assoc]

def ten (t : Fin n → E) : (Fin d → E) →ₗ[𝓞 E] Matrix (Fin n) (Fin d) E where
  toFun s := Matrix.of fun j a => t j * s a
  map_add' s s' := by
    ext j a
    simp [mul_add]
  map_smul' c s := by
    ext j a
    simp [Algebra.smul_def, mul_left_comm]

theorem ctr_ten (J : Matrix (Fin n) (Fin n) E) (t t' : Fin n → E) (s : Fin d → E) :
    ctr σ J t' (ten t s) = form σ J t t' • s := by
  funext a
  simp only [ctr, ten, form, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, dotProduct,
    Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hRat_ten (JX : Matrix (Fin n) (Fin n) E) (JW JS : Matrix (Fin d) (Fin d) E) (ξ₀ : E) (h : ξ₀ • JS⁻¹ = -JW)
    (M : Matrix (Fin n) (Fin d) E) (t : Fin n → E) (s : Fin d → E) :
    ξ₀ * hRatF σ JS JXᵀ M (ten t s) = -form σ JW (ctr σ JX t M) s := by
  have e : ∀ a b, ξ₀ * JS⁻¹ a b = -JW a b := fun a b => congrFun (congrFun h a) b
  simp only [hRatF, ctr, ten, form, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, Matrix.transpose_apply, map_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  linear_combination (σ (t k) * σ (s b) * JX j k * M j a) * e a b

theorem hRat_sum {ι : Type} [Fintype ι] (JT : Matrix (Fin n) (Fin n) E) (JS : Matrix (Fin d) (Fin d) E)
    (M : Matrix (Fin n) (Fin d) E) (N : ι → Matrix (Fin n) (Fin d) E) :
    hRatF σ JS JT M (∑ i, N i) = ∑ i, hRatF σ JS JT M (N i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [hRatF]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    simp only [hRatF, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem latH_of {B : Base F E} (hcm : IsCMExt F E σ) {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} {ξ₀ : E}
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hXu : IsUnit X.J.det) (hWu : IsUnit W.J.det) (hξ : ξ₀ ≠ 0) :
    LatH σ (-ξ₀ • W.J⁻¹) X.Jᵀ ξ₀ := by
  have e1 : (-ξ₀ • W.J⁻¹)⁻¹ = (-ξ₀)⁻¹ • W.J := Matrix.inv_eq_left_inv (by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hWu,
      inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
  have e2 : ξ₀ • (-ξ₀ • W.J⁻¹)⁻¹ = -W.J := by
    rw [e1, smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
  letI : StarRing E :=
    { star := σ
      star_involutive := sig_sig hcm
      star_mul := fun a b => by show σ (a * b) = σ b * σ a; rw [map_mul, mul_comm]
      star_add := fun a b => map_add σ a b }
  obtain ⟨m, u, u', hu, hd⟩ := GlobalTheory.LatVacDual.exists_dual_family X.Jᵀ (fun i j => hX.herm i j)
    (by rwa [Matrix.det_transpose]) X.L hX.lat.fg (by letI := hX.lat; exact Submodule.IsFullLattice.span_eq_top) (fun y hy => (hX.dual y).2 fun x hx => by
      obtain ⟨b, hb⟩ := hy x hx
      have : form σ X.J y x = b := by
        rw [hb, Finset.sum_comm]
        simp only [form, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply]
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
        show _ = σ _ * _ * _
        ring
      rw [this]
      exact b.2)
  have key : ∀ M : Matrix (Fin n) (Fin d) E, M = ∑ i, ten (u i) (ctr σ X.J (u' i) M) := fun M => by
    ext j a
    have : ∀ l, ∑ i, u i j * ∑ k, σ (u' i k) * X.J l k = if j = l then 1 else 0 := fun l => hd j l
    calc M j a = ∑ l, M l a * ∑ i, u i j * ∑ k, σ (u' i k) * X.J l k := by simp [this]
      _ = _ := by
        rw [Matrix.sum_apply]
        simp only [ten, ctr, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
        simp only [Finset.mul_sum (s := (Finset.univ : Finset (Fin m)))]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun _ _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _
  let Λ : Submodule (𝓞 E) (Matrix (Fin n) (Fin d) E) := ⨅ t ∈ X.L, W.L.comap (ctr σ X.J t)
  have hΛ : ∀ M, M ∈ Λ ↔ ∀ t ∈ X.L, ctr σ X.J t M ∈ W.L := fun M => by simp [Λ, Submodule.mem_iInf]
  have hten : ∀ t ∈ X.L, ∀ s ∈ W.L, ten t s ∈ Λ := fun t ht s hs => (hΛ _).2 fun t' ht' => by
    rw [ctr_ten]
    exact W.L.smul_mem (⟨_, (hX.dual t).1 ht t' ht'⟩ : 𝓞 E) hs
  refine ⟨Λ, ⟨?_, fun M => ?_⟩, fun M => ⟨fun hM M' hM' => ?_, fun H => (hΛ _).2 fun t ht => (hW.dual _).2 fun x hx o => ?_⟩⟩
  · have : Λ = ⨆ i, W.L.map (ten (u i)) := le_antisymm (fun M hM => by
      rw [key M]
      exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨_, (hΛ M).1 hM _ (hu i).2, rfl⟩)
      (iSup_le fun i => by
        rintro _ ⟨x, hx, rfl⟩
        exact hten _ (hu i).1 x hx)
    rw [this]
    exact Submodule.fg_iSup _ fun i => hW.lat.fg.map _
  · choose N hN hN' using fun i => exists_nsmul_mem hW.lat (ctr σ X.J (u' i) M)
    refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, ?_⟩
    rw [key M, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ i)
    rw [← map_nsmul, hc, mul_comm, mul_smul]
    exact hten _ (hu i).1 _ (nsmul_mem (hN' i) c)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [trace_int_iff, key M', hRat_sum, Finset.mul_sum, map_sum]
      refine IsIntegral.sum _ fun i _ => ?_
      rw [hRat_ten X.J W.J _ ξ₀ e2, map_neg]
      have := (hW.dual _).1 ((hΛ M).1 hM _ (hu i).1) _ ((hΛ M').1 hM' _ (hu i).2) 1
      simpa using this.neg
  · let o' : 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E) o
    have h1 := (trace_int_iff _).1 (H _ (hten t ht _ (W.L.smul_mem o' hx)))
    rw [hRat_ten X.J W.J _ ξ₀ e2, map_neg] at h1
    have h2 : form σ W.J (ctr σ X.J t M) (o' • x) = o * form σ W.J (ctr σ X.J t M) x := by
      have : ∀ i, σ ((o' • x) i) = o * σ (x i) := fun i => by
        show σ (σ o * x i) = _
        rw [map_mul, sig_sig hcm]
      simp only [form, this, dotProduct, Matrix.mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h2] at h1
    simpa using h1.neg

end Tensor

section Dbl

variable {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}

def rowsL {m : ℕ} (f : Fin nT → Fin m) : Matrix (Fin m) (Fin nS) E →ₗ[𝓞 E] Matrix (Fin nT) (Fin nS) E where
  toFun M := M.submatrix f id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def stackL : (Matrix (Fin nT) (Fin nS) E × Matrix (Fin nT) (Fin nS) E) →ₗ[𝓞 E] Matrix (Fin (nT + nT)) (Fin nS) E where
  toFun p := Matrix.of fun i j => Fin.append (fun k => p.1 k j) (fun k => p.2 k j) i
  map_add' p q := by
    ext i j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;> simp [-Fin.natAdd_eq_addNat]
  map_smul' c p := by
    ext i j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;> simp [-Fin.natAdd_eq_addNat]

theorem rowsL_apply {m : ℕ} (f : Fin nT → Fin m) (M : Matrix (Fin m) (Fin nS) E) (i j) : rowsL f M i j = M (f i) j := rfl

theorem stackL_apply (p : Matrix (Fin nT) (Fin nS) E × Matrix (Fin nT) (Fin nS) E) (i j) :
    stackL p i j = Fin.append (fun k => p.1 k j) (fun k => p.2 k j) i := rfl

theorem rows_stack_left (p : Matrix (Fin nT) (Fin nS) E × Matrix (Fin nT) (Fin nS) E) :
    rowsL (Fin.castAdd nT) (stackL p) = p.1 := by
  ext i j
  simp [rowsL_apply, stackL_apply]

theorem rows_stack_right (p : Matrix (Fin nT) (Fin nS) E × Matrix (Fin nT) (Fin nS) E) :
    rowsL (Fin.natAdd nT) (stackL p) = p.2 := by
  ext i j
  simp [rowsL_apply, stackL_apply, -Fin.natAdd_eq_addNat]

theorem stack_rows (M : Matrix (Fin (nT + nT)) (Fin nS) E) :
    stackL (rowsL (Fin.castAdd nT) M, rowsL (Fin.natAdd nT) M) = M := by
  ext i j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;> simp [rowsL_apply, stackL_apply, -Fin.natAdd_eq_addNat]

theorem hRat_dbl (x y : Matrix (Fin (nT + nT)) (Fin nS) E) :
    hRatF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) x y =
      hRatF σ JS JT (rowsL (Fin.castAdd nT) x) (rowsL (Fin.castAdd nT) y) -
        hRatF σ JS JT (rowsL (Fin.natAdd nT) x) (rowsL (Fin.natAdd nT) y) := by
  simp [hRatF, rowsL_apply, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, Fin.sum_univ_add, sub_eq_add_neg, Finset.sum_add_distrib,
    -Fin.natAdd_eq_addNat]

theorem hRat_zero_right (x : Matrix (Fin nT) (Fin nS) E) : hRatF σ JS JT x 0 = 0 := by simp [hRatF]

theorem LatH.dblT (h : LatH σ JS JT ξ₀) : LatH σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ := by
  obtain ⟨Λ, ⟨h1, h2⟩, h3⟩ := h
  have hm : ∀ M, M ∈ (Λ.prod Λ).map stackL ↔ rowsL (Fin.castAdd nT) M ∈ Λ ∧ rowsL (Fin.natAdd nT) M ∈ Λ := fun M =>
    ⟨by
      rintro ⟨p, hp, rfl⟩
      rw [rows_stack_left, rows_stack_right]
      exact hp, fun H => ⟨(_, _), H, stack_rows M⟩⟩
  refine ⟨(Λ.prod Λ).map stackL, ⟨(h1.prod h1).map _, fun M => ?_⟩, fun M => ⟨fun hM M' hM' => ?_, fun H => (hm _).2 ⟨?_, ?_⟩⟩⟩
  · obtain ⟨N, hN, a⟩ := h2 (rowsL (Fin.castAdd nT) M)
    obtain ⟨N', hN', b⟩ := h2 (rowsL (Fin.natAdd nT) M)
    refine ⟨N * N', Nat.mul_pos hN hN', (hm _).2 ⟨?_, ?_⟩⟩
    · rw [map_nsmul, mul_comm, mul_smul]
      exact nsmul_mem a _
    · rw [map_nsmul, mul_smul]
      exact nsmul_mem b _
  · obtain ⟨a, ha⟩ := (h3 _).1 ((hm _).1 hM).1 _ ((hm _).1 hM').1
    obtain ⟨b, hb⟩ := (h3 _).1 ((hm _).1 hM).2 _ ((hm _).1 hM').2
    exact ⟨a - b, by rw [hRat_dbl, mul_sub, map_sub, ha, hb, Int.cast_sub]⟩
  · refine (h3 _).2 fun M' hM' => ?_
    obtain ⟨a, ha⟩ := H (stackL (M', 0)) ⟨_, ⟨hM', Λ.zero_mem⟩, rfl⟩
    rw [hRat_dbl, rows_stack_left, rows_stack_right, hRat_zero_right, sub_zero] at ha
    exact ⟨a, ha⟩
  · refine (h3 _).2 fun M' hM' => ?_
    obtain ⟨a, ha⟩ := H (stackL (0, M')) ⟨_, ⟨Λ.zero_mem, hM'⟩, rfl⟩
    rw [hRat_dbl, rows_stack_left, rows_stack_right, hRat_zero_right, zero_sub, mul_neg, map_neg] at ha
    exact ⟨-a, by rw [Int.cast_neg, ← ha, neg_neg]⟩

end Dbl

end PositivityTheory.ThKW

end
end
