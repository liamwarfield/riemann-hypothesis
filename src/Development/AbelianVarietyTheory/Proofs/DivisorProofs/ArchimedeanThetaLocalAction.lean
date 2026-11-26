module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTrigPolynomialAnnihilatingAdelicSchwartz

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSupportCompactInvariance
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSupportCompactInvariance
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open Matrix

noncomputable section

namespace GlobalTheory.FinLocSchA

open GlobalTheory.WeilM

theorem exists_open_addStab {X : Type} [AddGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    {g : X → ℂ} (hg : g ∈ SB X) :
    ∃ K : AddSubgroup X, IsOpen (K : Set X) ∧ ∀ z, ∀ k ∈ K, g (z + k) = g z := by
  let K : AddSubgroup X :=
    { carrier := {k | ∀ z, g (z + k) = g z}
      zero_mem' := by intro z; simp
      add_mem' := by
        intro a b ha hb z
        rw [← add_assoc, hb, ha]
      neg_mem' := by
        intro a ha z
        have := ha (z + -a)
        simpa using this.symm }
  refine ⟨K, ?_, fun z k hk => hk z⟩
  have h1 : ∀ᶠ k in nhds (0 : X), ∀ z ∈ tsupport g, g (z + k) = g z := by
    apply IsCompact.eventually_forall_of_forall_eventually hg.2
    intro z _
    have a1 : IsLocallyConstant (fun p : X × X => g (p.2 + p.1)) :=
      hg.1.comp_continuous (by fun_prop)
    have a2 : IsLocallyConstant (fun p : X × X => g p.2) :=
      hg.1.comp_continuous (by fun_prop)
    filter_upwards [a1.eventually_eq (0, z), a2.eventually_eq (0, z)] with p hp1 hp2
    simp only [hp1, hp2, add_zero]
  have h2 : ∀ᶠ k in nhds (0 : X), ∀ z ∈ tsupport g, g (z + -k) = g z := by
    have : Filter.Tendsto (fun k : X => -k) (nhds 0) (nhds 0) := by
      simpa using (continuous_neg (G := X)).tendsto 0
    exact this.eventually h1
  apply AddSubgroup.isOpen_of_mem_nhds K (g := 0)
  filter_upwards [h1, h2] with k hk1 hk2
  intro z
  by_cases hz : z ∈ tsupport g
  · exact hk1 z hz
  · by_cases hz' : z + k ∈ tsupport g
    · simpa using (hk2 _ hz').symm
    · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']

theorem compact_support_locally_constant_fin : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∃ (C K : Set (κ → Af F)), IsCompact C ∧ IsOpen K ∧ (0 : κ → Af F) ∈ K ∧
      (∀ x : κ → AF F, Φ x ≠ 0 → (fun i => (x i).2) ∈ C) ∧
      ∀ x x' : κ → AF F, (∀ i, (x i).1 = (x' i).1) → (fun i => (x' i).2 - (x i).2) ∈ K → Φ x' = Φ x := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨K, hKo, hK⟩ := exists_open_addStab hg
    refine ⟨tsupport g, K, hg.2, hKo, K.zero_mem, ?_, ?_⟩
    · intro x hx
      by_contra hc
      apply hx
      simp only [pureA]
      rw [image_eq_zero_of_notMem_tsupport hc, mul_zero]
    · intro x x' h1 h2
      simp only [pureA, ← h1]
      congr 1
      have e2 : (fun i => (x' i).2) = (fun i => (x i).2) + (fun i => (x' i).2 - (x i).2) := by
        ext i; simp
      rw [e2]
      exact hK _ _ h2
  | zero =>
    refine ⟨∅, Set.univ, isCompact_empty, isOpen_univ, trivial, ?_, ?_⟩
    · intro x hx; exact absurd rfl hx
    · intro x x' _ _; rfl
  | add Φ Ψ _ _ ihΦ ihΨ =>
    obtain ⟨C₁, K₁, hC₁, hK₁, h0₁, hs₁, hi₁⟩ := ihΦ
    obtain ⟨C₂, K₂, hC₂, hK₂, h0₂, hs₂, hi₂⟩ := ihΨ
    refine ⟨C₁ ∪ C₂, K₁ ∩ K₂, hC₁.union hC₂, hK₁.inter hK₂, ⟨h0₁, h0₂⟩, ?_, ?_⟩
    · intro x hx
      by_cases h : Φ x = 0
      · right; apply hs₂ x; intro h'; apply hx; simp [h, h']
      · left; exact hs₁ x h
    · intro x x' h1 h2
      simp only [Pi.add_apply, hi₁ x x' h1 h2.1, hi₂ x x' h1 h2.2]
  | smul a Φ _ ih =>
    obtain ⟨C, K, hC, hK, h0, hs, hi⟩ := ih
    refine ⟨C, K, hC, hK, h0, ?_, ?_⟩
    · intro x hx
      apply hs x
      intro h; apply hx; simp [h]
    · intro x x' h1 h2
      simp only [Pi.smul_apply, hi x x' h1 h2]

end GlobalTheory.FinLocSchA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSupportCompactInvarianceStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_schwartz_support_compact_invariance : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∃ (C K : Set (κ → Af F)), IsCompact C ∧ IsOpen K ∧ (0 : κ → Af F) ∈ K ∧
      (∀ x : κ → AF F, Φ x ≠ 0 → (fun i => (x i).2) ∈ C) ∧
      ∀ x x' : κ → AF F, (∀ i, (x i).1 = (x' i).1) → (fun i => (x' i).2 - (x i).2) ∈ K → Φ x' = Φ x := by
  first | exact @GlobalTheory.FinLocSchA.compact_support_locally_constant_fin | exact GlobalTheory.FinLocSchA.compact_support_locally_constant_fin | (intros; apply GlobalTheory.FinLocSchA.compact_support_locally_constant_fin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPartitionOfUnitySupport
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPartitionOfUnitySupport
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open Matrix

noncomputable section

namespace GlobalTheory.FinCharCut

open GlobalTheory.FinTrig

theorem exists_lev_subset {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (K : Set (κ → Af F)) (hK : K ∈ nhds (0 : κ → Af F)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ u : κ → Af F, Lev d u → u ∈ K := by
  rw [nhds_pi, Filter.mem_pi] at hK
  obtain ⟨I, -, t, ht, hIt⟩ := hK
  have hW : (⋂ i, t i) ∈ nhds (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.2 ht
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  refine ⟨d, hd0, fun u hu => hIt fun i _ => ?_⟩
  have hdK : (algebraMap (𝓞 F) F d) ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have hmem := hd (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) (hu i)
  have he : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d) *
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) = u i := by
    rw [← mul_assoc, ← map_mul]
    have : algebraMap (𝓞 F) F d * (d : F)⁻¹ = 1 := mul_inv_cancel₀ hdK
    rw [this, map_one, one_mul]
  rw [he] at hmem
  exact Set.mem_iInter.1 hmem i

theorem fin_char_cut : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (C K : Set (κ → Af F)), IsCompact C → IsOpen K → (0 : κ → Af F) ∈ K →
    ∀ y : κ → AF F, ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, ∀ i, (b i).1 = 0) ∧
      ∑ b ∈ s, c b * ψ (y ⬝ᵥ b) = 1 ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ C → (∀ k ∈ K, (fun i => (x i).2) ≠ (fun i => (y i).2) + k) →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = 0 := by
  intro F _ _ κ _ ψ hψ C K hC hK h0 y
  classical
  obtain ⟨d, -, hdK⟩ := exists_lev_subset K (hK.mem_nhds h0)
  set yf : κ → FiniteAdeleRing (𝓞 F) F := fun i => (y i).2 with hyf
  set C' := C ∩ {z | Lev d (z - yf)}ᶜ with hC'def
  have hC' : IsCompact C' := hC.inter_right (isOpen_lev d yf).isClosed_compl
  obtain ⟨t, htC, hcov⟩ := hC'.elim_nhds_subcover (fun a => {z | Lev d (z - a)})
    (fun a _ => (isOpen_lev d a).mem_nhds (by simp only [Set.mem_setOf_eq, sub_self]; exact lev_zero d))
  have hsep : ∀ a ∈ C', ∃ q ∈ (Q0 : Set (κ → AF F)), ψ (vecFin (a - yf) ⬝ᵥ q) ≠ 1 ∧
      ∀ u, Lev d u → ψ (vecFin u ⬝ᵥ q) = 1 := fun a ha => exists_sep ψ hψ d (a - yf) ha.2
  choose! q hq0 hq1 hq2 using hsep
  set c : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun a => ψ (vecFin (a - yf) ⬝ᵥ q a) with hc
  set φ : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AF F) → ℂ := fun a =>
    (1 - c a)⁻¹ • (ψ (-(y ⬝ᵥ q a)) • GlobalTheory.FinTrig.chi ψ (q a) - c a • 1) with hφ
  have hφx : ∀ a ∈ C', ∀ x, φ a x = (1 - c a)⁻¹ * (ψ (vecFin ((fun i => (x i).2) - yf) ⬝ᵥ q a) - c a) := by
    intro a ha x
    have e1 : ψ (-(y ⬝ᵥ q a)) * ψ (x ⬝ᵥ q a) = ψ (vecFin ((fun i => (x i).2) - yf) ⬝ᵥ q a) := by
      rw [← AddChar.map_add_eq_mul, neg_add_eq_sub, ← sub_dotProduct, dot_eq_vecFin (hq0 a ha)]
      rfl
    simp only [hφ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, GlobalTheory.FinTrig.chi, Pi.one_apply, mul_one]
    rw [e1]
  have hφmem : ∀ a ∈ t, φ a ∈ TP ψ := fun a ha =>
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ (chi_mem ψ (hq0 a (htC a ha))))
      (Submodule.smul_mem _ _ (one_mem_TP ψ)))
  obtain ⟨s, cc, hs, hP⟩ := exists_of_mem_TP ψ (prod_mem_TP ψ t φ hφmem)
  refine ⟨s, cc, fun b hb i => fst_eq_zero (hs b hb i), ?_, fun x hxC hxK => ?_⟩
  · rw [← hP y, Finset.prod_apply]
    refine Finset.prod_eq_one fun a ha => ?_
    rw [hφx a (htC a ha)]
    have e0 : (fun i => (y i).2) - yf = 0 := sub_self _
    have hne : 1 - c a ≠ 0 := sub_ne_zero.mpr (Ne.symm (hq1 a (htC a ha)))
    rw [e0, vecFin_zero, zero_dotProduct, AddChar.map_zero_eq_one, inv_mul_cancel₀ hne]
  · rw [← hP x, Finset.prod_apply]
    have hL : ¬ Lev d ((fun i => (x i).2) - yf) := by
      intro hL
      refine hxK _ (hdK _ hL) ?_
      funext i
      simp [yf]
    have hxC' : (fun i => (x i).2) ∈ C' := ⟨hxC, hL⟩
    obtain ⟨a, hat, hxa⟩ := Set.mem_iUnion₂.mp (hcov hxC')
    rw [Finset.prod_eq_zero hat]
    rw [hφx a (htC a hat)]
    have e : (fun i => (x i).2) - yf = ((fun i => (x i).2) - a) + (a - yf) := (sub_add_sub_cancel _ _ _).symm
    rw [e, vecFin_add, add_dotProduct, AddChar.map_add_eq_mul, hq2 a (htC a hat) _ hxa, one_mul, sub_self,
      mul_zero]

end GlobalTheory.FinCharCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPartitionOfUnitySupportStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_partition_of_unity_support : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (C K : Set (κ → Af F)), IsCompact C → IsOpen K → (0 : κ → Af F) ∈ K →
    ∀ y : κ → AF F, ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, ∀ i, (b i).1 = 0) ∧
      ∑ b ∈ s, c b * ψ (y ⬝ᵥ b) = 1 ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ C → (∀ k ∈ K, (fun i => (x i).2) ≠ (fun i => (y i).2) + k) →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = 0 := by
  first | exact @GlobalTheory.FinCharCut.fin_char_cut | exact GlobalTheory.FinCharCut.fin_char_cut | (intros; apply GlobalTheory.FinCharCut.fin_char_cut <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanThetaLocalAction
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.ArchPure

open Matrix

variable {F : Type} [Field F] [NumberField F]

def mk (a : Ainf F) (b : Af F) : AF F := (a, b)

theorem evI_fin (b : Af F) : evI F (((0 : Ainf F), b) : AF F) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
  exact map_zero _

theorem snd_of_at {z : AF F} (hz : At (evI F) z) : z.2 = 0 := by
  have h := hz (((0 : Ainf F), (1 : Af F)) : AF F) (evI_fin 1)
  have h2 : (1 : Af F) * z.2 = 0 := congrArg Prod.snd h
  rwa [one_mul] at h2

theorem slice {κ : Type} [Fintype κ] (c : κ → Af F) :
    ∀ Ψ ∈ schA F κ, ∃ f' : SInf F κ, ∀ s : κ → mixedEmbedding.mixedSpace F,
      Ψ (fun i => mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (s i)) (c i)) = f' s := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, -, rfl⟩ := hx
    refine ⟨g c • f, fun s => ?_⟩
    simp only [pureA, mk, RingEquiv.apply_symm_apply, SchwartzMap.smul_apply, smul_eq_mul,
      mul_comm]
  | zero => exact ⟨0, fun s => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨f1, h1⟩ := hx
    obtain ⟨f2, h2⟩ := hy
    exact ⟨f1 + f2, fun s => by rw [Pi.add_apply, h1, h2, SchwartzMap.add_apply]⟩
  | smul a x _ hx =>
    obtain ⟨f1, h1⟩ := hx
    exact ⟨a • f1, fun s => by rw [Pi.smul_apply, h1, SchwartzMap.smul_apply]⟩

theorem locA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∃ (C K : Set (κ → Af F)), IsCompact C ∧ IsOpen K ∧ (0 : κ → Af F) ∈ K ∧
      (∀ x : κ → AF F, Φ x ≠ 0 → (fun i => (x i).2) ∈ C) ∧
      ∀ x x' : κ → AF F, (∀ i, (x i).1 = (x' i).1) → (fun i => (x' i).2 - (x i).2) ∈ K → Φ x' = Φ x := GlobalTheory.T.adelic_schwartz_support_compact_invariance

theorem locB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (C K : Set (κ → Af F)), IsCompact C → IsOpen K → (0 : κ → Af F) ∈ K →
    ∀ y : κ → AF F, ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, ∀ i, (b i).1 = 0) ∧
      ∑ b ∈ s, c b * ψ (y ⬝ᵥ b) = 1 ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ C → (∀ k ∈ K, (fun i => (x i).2) ≠ (fun i => (y i).2) + k) →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = 0 := GlobalTheory.T.character_partition_of_unity_support

theorem fibre : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (T : Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ → (∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) →
    (∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ schA F κ, ∀ y : κ → AF F, (∀ z, At (evI F) z → Φ (y + z) = 0) → T Φ y = 0 := by
  intro F _ _ κ _ ψ T hψ hkeep hcomm Φ hΦ y hy
  obtain ⟨C, K, hC, hK, hK0, hsupp, hinv⟩ := locA Φ hΦ
  obtain ⟨s, c, hs, hy1, hm⟩ := locB ψ hψ C K hC hK hK0 y
  have hu0 : evI F (mk 0 1) = 0 := evI_fin 1
  have hub : ∀ b ∈ s, (mk 0 1 : AF F) • b = b := fun b hb => funext fun i =>
    Prod.ext (show (0 : Ainf F) * (b i).1 = (b i).1 by rw [zero_mul, hs b hb i])
      (show (1 : Af F) * (b i).2 = (b i).2 from one_mul _)
  have hsch : ∀ (b : κ → AF F) (Ψ : (κ → AF F) → ℂ), schr ψ (0, b) Ψ = fun x => ψ (x ⬝ᵥ b) * Ψ x :=
    fun b Ψ => funext fun x => by simp [schr]
  have hfac : ∀ (Ψ : (κ → AF F) → ℂ) x, (∑ b ∈ s, c b • schr ψ (0, b) Ψ) x = (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Ψ x := by
    intro Ψ x
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Pi.smul_apply, hsch, smul_eq_mul]
    ring
  have hzero : (∑ b ∈ s, c b • schr ψ (0, b) Φ) = 0 := by
    funext x
    rw [hfac, Pi.zero_apply]
    by_cases hx : Φ x = 0
    · rw [hx, mul_zero]
    · refine mul_eq_zero_of_left (hm x (hsupp x hx) fun k hk he => hx ?_) _
      have hk' : (fun i => (x i).2 - (y i).2) = k := funext fun i => by
        rw [congrFun he i, Pi.add_apply]
        abel
      have e1 : Φ x = Φ (fun i => mk (x i).1 (y i).2) := hinv _ _ (fun i => rfl) (by rw [← hk'] at hk; exact hk)
      rw [e1]
      have hz : At (evI F) (fun i => mk ((x i).1 - (y i).1) (0 : Af F)) := by
        intro u' hu'
        have h1 : u'.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hu'
        funext i
        exact Prod.ext (show u'.1 * ((x i).1 - (y i).1) = 0 by rw [h1, zero_mul])
          (show u'.2 * (0 : Af F) = 0 from mul_zero _)
      have e2 := hy _ hz
      have e3 : y + (fun i => mk ((x i).1 - (y i).1) (0 : Af F)) = fun i => mk (x i).1 (y i).2 := by
        funext i
        exact Prod.ext (show (y i).1 + ((x i).1 - (y i).1) = (x i).1 by abel)
          (show (y i).2 + 0 = (y i).2 from add_zero _)
      rwa [e3] at e2
  have hT : T (∑ b ∈ s, c b • schr ψ (0, b) Φ) = ∑ b ∈ s, c b • schr ψ (0, b) (T Φ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [map_smul]
    congr 1
    have := hcomm (mk 0 1) hu0 0 b Φ hΦ
    rwa [smul_zero, hub b hb] at this
  have e := congrFun hT y
  rw [hzero, map_zero, Pi.zero_apply, hfac, hy1, one_mul] at e
  exact e.symm

end GlobalTheory.ArchPure

namespace GlobalTheory.ArchPure

open Matrix

theorem arch_pure : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (g : UA σ G.V'.J) (h : UA σ G.W.J), At (evI F) (mat g - 1) → At (evI F) (mat h - 1) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ f₂ : SInf F (Fin a' × Fin (a + a')), om' (g, h) (pure f φ) = pure f₂ φ := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT g h hg hh f φ hφ hstd
  have hW := IsUWeilPair.isUSplitting hT.weil'
  set T := om' (g, h) with hTdef
  have hkeep : ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), T Φ ∈ schA F _ := fun Φ hΦ => hW.pres (g, h) Φ hΦ
  have hcomm : ∀ u : AF F, evI F u = 0 → ∀ p q : Fin a' × Fin (a + a') → AF F, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')),
      T (schr B.ψ (u • p, u • q) Φ) = schr B.ψ (u • p, u • q) (T Φ) := by
    intro u hu p q Φ hΦ
    set w := G.M'.co.e.symm (p, q) with hw
    have he : G.M'.co.e (u • w) = (u • p, u • q) := by
      rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
    have h1 : u • (mat g - 1) = 0 := hg u hu
    have h2 : u • (mat h - 1) = 0 := hh u hu
    have e1 : mat g * (u • w) = u • w := by
      have : mat g * (u • w) - u • w = (u • (mat g - 1)) * w := by
        rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
      rw [h1, Matrix.zero_mul, sub_eq_zero] at this
      exact this
    have e2 : (u • w) * (mat h)ᵀ = u • w := by
      have : (u • w) * (mat h)ᵀ - u • w = w * (u • (mat h - 1))ᵀ := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
          Matrix.mul_sub, Matrix.mul_one, smul_sub]
      rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
      exact this
    have hact : actAB (cA σ) (g, h) (u • w) = u • w := by
      simp only [actAB]
      simp only [mat] at e1 e2
      rw [e1, e2]
    have h3 := hW.impl (g, h) (u • w) Φ hΦ
    simp only [Darboux.rho, he, hact] at h3
    exact h3
  have hstd' : ∀ᶠ w in Filter.cofinite,
      φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hstd, hT.geo.hM'.std] with w h1 h2
    rw [h1, h2]
  have hΦ : pure f φ ∈ schA F _ := GlobalTheory.TensUniq.pure_mem_schA f φ hφ hstd'
  set P : (Fin a' × Fin (a + a') → AF F) → ℂ := fun x => ∏ᶠ v, φ v fun i => evFin F v (x i) with hPdef
  have hPf : ∀ x x' : Fin a' × Fin (a + a') → AF F, (∀ i, (x i).2 = (x' i).2) → P x = P x' := by
    intro x x' hx
    simp only [hPdef]
    congr 1
    funext v
    congr 1
    funext i
    show evalV F v (x i).2 = evalV F v (x' i).2
    rw [hx i]
  have hpure : ∀ (f₀ : SInf F (Fin a' × Fin (a + a'))) x, pure f₀ φ x = f₀ (fun i => evI F (x i)) * P x :=
    fun _ _ => rfl
  by_cases h0 : ∀ x, P x = 0
  · refine ⟨f, ?_⟩
    have e : pure f φ = 0 := funext fun x => by rw [hpure, h0 x, mul_zero]; rfl
    rw [e, map_zero]
  push_neg at h0
  obtain ⟨y0, hy0⟩ := h0
  obtain ⟨f', hf'⟩ := slice (fun i => (y0 i).2) (T (pure f φ)) (hkeep _ hΦ)
  refine ⟨(P y0)⁻¹ • f', ?_⟩
  funext y
  set d : Fin a' × Fin (a + a') → AF F := fun i => mk 0 ((y0 i).2 - (y i).2) with hd
  set u : AF F := mk 0 1 with hu
  have hu0 : evI F u = 0 := evI_fin 1
  have hud : u • d = d := by
    funext i
    exact Prod.ext (show (0 : Ainf F) * 0 = 0 from mul_zero _) (show (1 : Af F) * _ = _ from one_mul _)
  have hsh : ∀ Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ, schr B.ψ (d, 0) Φ' = fun x => Φ' (x + d) :=
    fun Φ' => funext fun x => by simp [schr]
  have htr : ∀ Ψ ∈ schA F (Fin a' × Fin (a + a')), T (fun x => Ψ (x + d)) = fun x => T Ψ (x + d) := by
    intro Ψ hΨ
    have := hcomm u hu0 d 0 Ψ hΨ
    rw [hud, smul_zero, hsh, hsh] at this
    exact this
  set c : ℂ := P y / P y0 with hc
  set Θ : (Fin a' × Fin (a + a') → AF F) → ℂ := c • fun x => pure f φ (x + d) with hΘdef
  have hΘ : Θ ∈ schA F _ := by
    refine Submodule.smul_mem _ c ?_
    have := GlobalTheory.HeisSchA.schr_mem_schA B.ψ hT.base.std (d, 0) _ hΦ
    rwa [hsh] at this
  have hvan : ∀ z, At (evI F) z → (pure f φ - Θ) (y + z) = 0 := by
    intro z hz
    have hz2 : ∀ i, (z i).2 = 0 := fun i => snd_of_at (fun u' hu' => congrFun (hz u' hu') i)
    have hevI : (fun i => evI F ((y + z + d) i)) = fun i => evI F ((y + z) i) := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F (((y + z) i).1 + (0 : Ainf F)) =
        InfiniteAdeleRing.ringEquiv_mixedSpace F ((y + z) i).1
      rw [add_zero]
    have hP1 : P (y + z) = P y := hPf _ _ fun i => by
      show (y i).2 + (z i).2 = (y i).2
      rw [hz2 i, add_zero]
    have hP2 : P (y + z + d) = P y0 := hPf _ _ fun i => by
      show (y i).2 + (z i).2 + ((y0 i).2 - (y i).2) = (y0 i).2
      rw [hz2 i, add_zero]
      abel
    rw [Pi.sub_apply, hΘdef, Pi.smul_apply, smul_eq_mul, hpure, hpure, hevI, hP1, hP2, hc]
    field_simp
    ring
  have h1 := fibre B.ψ T hT.base.std hkeep hcomm _ (sub_mem hΦ hΘ) y hvan
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h1
  have h2 : T Θ y = c * T (pure f φ) (y + d) := by
    rw [hΘdef, map_smul, htr _ hΦ]
    rfl
  have hyd : y + d = fun i => mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (evI F (y i))) ((y0 i).2) := by
    funext i
    refine Prod.ext ?_ ?_
    · show (y i).1 + 0 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)
      rw [add_zero, RingEquiv.symm_apply_apply]
    · show (y i).2 + ((y0 i).2 - (y i).2) = (y0 i).2
      abel
  rw [hpure, h1, h2, hyd, hf', SchwartzMap.smul_apply, smul_eq_mul, hc]
  field_simp

end GlobalTheory.ArchPure
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanThetaLocalActionStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_theta_local_action : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (g : UA σ G.V'.J) (h : UA σ G.W.J), At (evI F) (mat g - 1) → At (evI F) (mat h - 1) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ f₂ : SInf F (Fin a' × Fin (a + a')), om' (g, h) (pure f φ) = pure f₂ φ := by
  first | exact @GlobalTheory.ArchPure.arch_pure | exact GlobalTheory.ArchPure.arch_pure | (intros; apply GlobalTheory.ArchPure.arch_pure <;> assumption)
end
