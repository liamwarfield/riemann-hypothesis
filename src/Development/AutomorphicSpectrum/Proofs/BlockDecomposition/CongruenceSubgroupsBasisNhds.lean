module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupsBasisNhds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupsBasisNhds
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

theorem exists_entry_nhds {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] (m : ℕ)
    {t : Set (Matrix (Fin m) (Fin m) k)} (ht : t ∈ 𝓝 (1 : Matrix (Fin m) (Fin m) k)) :
    ∃ U ∈ 𝓝 (0 : k), ∀ A : Matrix (Fin m) (Fin m) k,
      (∀ a b, A a b - (1 : Matrix (Fin m) (Fin m) k) a b ∈ U) → A ∈ t := by
  have hc : Continuous fun B : Matrix (Fin m) (Fin m) k => 1 + B := continuous_const.add continuous_id
  have hs : (fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t ∈ 𝓝 (0 : Matrix (Fin m) (Fin m) k) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa using ht
  have e : 𝓝 (0 : Fin m → Fin m → k) = Filter.pi fun a => 𝓝 ((0 : Fin m → Fin m → k) a) := nhds_pi
  have hs' : ((fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t : Set (Fin m → Fin m → k)) ∈
      Filter.pi fun a => 𝓝 ((0 : Fin m → Fin m → k) a) := by
    rw [← e]
    exact hs
  obtain ⟨I, -, t₁, ht₁, hsub⟩ := Filter.mem_pi.1 hs'
  have h2 : ∀ a, ∃ t₂ : Fin m → Set k, (∀ b, t₂ b ∈ 𝓝 (0 : k)) ∧ Set.univ.pi t₂ ⊆ t₁ a := by
    intro a
    have e' : 𝓝 (0 : Fin m → k) = Filter.pi fun b => 𝓝 ((0 : Fin m → k) b) := nhds_pi
    have h : t₁ a ∈ Filter.pi fun b => 𝓝 ((0 : Fin m → k) b) := by
      rw [← e']
      exact ht₁ a
    obtain ⟨J, -, t₂, ht₂, hJ⟩ := Filter.mem_pi.1 h
    exact ⟨t₂, ht₂, fun x hx => hJ fun b _ => hx b (Set.mem_univ b)⟩
  choose t₂ ht₂ hsub₂ using h2
  refine ⟨⋂ a, ⋂ b, t₂ a b, Filter.iInter_mem.2 fun a => Filter.iInter_mem.2 fun b => ht₂ a b,
    fun A hA => ?_⟩
  have hmem : A - 1 ∈ (fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t :=
    hsub fun a _ => hsub₂ a fun b _ => Set.mem_iInter.1 (Set.mem_iInter.1 (hA a b) a) b
  simpa using hmem

theorem congM_subset_nhds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (O : Set (Mir k n)) (hO : O ∈ 𝓝 (1 : Mir k n)) :
    ∃ s₀ : kˣ, ∀ (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1),
      ValuativeRel.valuation k (s : k) ≤ ValuativeRel.valuation k (s₀ : k) →
        (GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n : Set (Mir k n)) ⊆ O := by
  obtain ⟨u, hu, huO⟩ :=
    (mem_nhds_subtype ((GlobalTheory.BZMir.Mir k n : Set (GL (Fin (n + 1)) k))) 1 O).1 hO
  have hu1 : u ∈ 𝓝 (1 : GL (Fin (n + 1)) k) := by simpa using hu
  rw [Units.isEmbedding_embedProduct.toIsInducing.nhds_eq_comap, Filter.mem_comap] at hu1
  obtain ⟨w, hw, hwu⟩ := hu1
  rw [Units.embedProduct_apply, nhds_prod_eq, Filter.mem_prod_iff] at hw
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := hw
  have ht₁' : t₁ ∈ 𝓝 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by simpa using ht₁
  have ht₂' : MulOpposite.op ⁻¹' t₂ ∈ 𝓝 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    have h := MulOpposite.continuous_op.continuousAt.preimage_mem_nhds ht₂
    simpa using h
  obtain ⟨U₁, hU₁, h₁⟩ := GlobalTheory.CompanionTheory.BZPhiPG.Onto.exists_entry_nhds (n + 1) ht₁'
  obtain ⟨U₂, hU₂, h₂⟩ := GlobalTheory.CompanionTheory.BZPhiPG.Onto.exists_entry_nhds (n + 1) ht₂'
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.SplitWeil.exists_cball_subset (Filter.inter_mem hU₁ hU₂)
  refine ⟨s₀, fun s hs hss₀ g hg => ?_⟩
  have hball : ∀ x : k, x ∈ GlobalTheory.SplitWeil.cball s → x ∈ GlobalTheory.SplitWeil.cball s₀ := by
    intro x hx
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq] at hx ⊢
    exact le_trans hx hss₀
  refine huO (hwu (hsub (Set.mem_prod.2 ⟨?_, ?_⟩)))
  · have hg' : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
      hg.1
    show ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈ t₁
    exact h₁ _ fun a b => (hs₀ (hball _ (hg' a b))).1
  · have hg' : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s
        (((g : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
      hg.2
    show MulOpposite.op (((g : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈ t₂
    exact h₂ _ fun a b => (hs₀ (hball _ (hg' a b))).2

end GlobalTheory.CompanionTheory.BZPhiPG.Onto
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupsBasisNhdsStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroups_basis_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (O : Set (Mir k n)) (hO : O ∈ nhds (1 : Mir k n)),
  ∃ s₀ : kˣ, ∀ (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1), ValuativeRel.valuation k (s : k) ≤ ValuativeRel.valuation k (s₀ : k) →
    (GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n : Set (Mir k n)) ⊆ O := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM_subset_nhds | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM_subset_nhds | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM_subset_nhds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemSubmoduleOfBumps
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemSubmoduleOfBumps
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem mem_of_bumps {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (ρ : Representation ℂ H W) (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (y : cIndSpace H ρ) (hy : ∀ g, ∀ x ∈ K, y.1.1.1 (g * x) = y.1.1.1 g)
    (S : Submodule ℂ (cIndSpace H ρ)) (hS : ∀ c B, IsBump H ρ K c (y.1.1.1 c) B → B ∈ S) : y ∈ S := by
  classical
  obtain ⟨C, hC, hsupp⟩ := y.2
  have hyeq : ∀ (a : H) (g : G), y.1.1.1 ((a : G) * g) = ρ a (y.1.1.1 g) := y.1.1.2
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun c => (fun x => c * x) '' (K : Set G)) (fun c _ => by
    have : (fun y => c⁻¹ * y) ⁻¹' (K : Set G) ∈ 𝓝 c :=
      (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [one_mem])
    filter_upwards [this] with y hy
    exact ⟨c⁻¹ * y, hy, by group⟩)
  let T : Finset (DoubleCoset.Quotient (H : Set G) (K : Set G)) := t.image (DoubleCoset.mk H K)
  have hres := fun d : DoubleCoset.Quotient (H : Set G) (K : Set G) =>
    GlobalTheory.CompanionTheory.LeibPhi.exists_indicator H ρ (GlobalTheory.CompanionTheory.LeibPhi.isHK_doubleCoset H K hKo (Quotient.out d)) y
  choose f hf1 hf0 using hres
  have hbump : ∀ d, IsBump H ρ K (Quotient.out d) (y.1.1.1 (Quotient.out d)) (f d) := by
    intro d
    refine ⟨fun a x hx => ?_, fun g hg => hf0 d g ?_⟩
    · rw [hf1 d _ ⟨a, a.2, x, hx, rfl⟩, hy _ x hx, hyeq]
    · rintro ⟨a, ha, x, hx, e⟩
      exact hg ⟨⟨a, ha⟩, x, hx, e⟩
  have hoff : ∀ (d : DoubleCoset.Quotient (H : Set G) (K : Set G)) (g : G), DoubleCoset.mk H K g ≠ d →
      (f d).1.1.1 g = 0 := by
    intro d g hne
    apply hf0
    rintro ⟨a, ha, x, hx, e⟩
    apply hne
    rw [← DoubleCoset.out_eq' d]
    exact ((@DoubleCoset.eq _ _ H K _ _).2 ⟨a, ha, x, hx, e⟩).symm
  have hmem : ∑ d ∈ T, f d ∈ S := S.sum_mem fun d _ => hS _ _ (hbump d)
  have hval : ∀ g, y.1.1.1 g = (∑ d ∈ T, f d).1.1.1 g := by
    intro g
    let ev : cIndSpace H ρ →ₗ[ℂ] W :=
      (LinearMap.proj g) ∘ₗ (indSpace H ρ).subtype ∘ₗ (smoothPart (ind H ρ)).subtype ∘ₗ (cIndSpace H ρ).subtype
    have hsum : (∑ d ∈ T, f d).1.1.1 g = ∑ d ∈ T, (f d).1.1.1 g := map_sum ev _ _
    rw [hsum]
    by_cases hg : DoubleCoset.mk H K g ∈ T
    · rw [Finset.sum_eq_single_of_mem _ hg (fun d _ hd => hoff d g (Ne.symm hd))]
      obtain ⟨a, ha, x, hx, e⟩ := (@DoubleCoset.eq _ _ H K _ _).1 (DoubleCoset.out_eq' (DoubleCoset.mk H K g))
      exact (hf1 _ g ⟨a, ha, x, hx, e⟩).symm
    · rw [Finset.sum_eq_zero (fun d hd => hoff d g (fun h => hg (h ▸ hd)))]
      by_contra hne
      obtain ⟨a, ha, c', hc', e⟩ := hsupp g hne
      obtain ⟨c, hc, hcc⟩ := Set.mem_iUnion₂.1 (ht hc')
      obtain ⟨x, hx, rfl⟩ := hcc
      apply hg
      have : DoubleCoset.mk H K c = DoubleCoset.mk H K g :=
        (@DoubleCoset.eq _ _ H K _ _).2 ⟨a, ha, x, hx, by rw [e]; group⟩
      rw [← this]
      exact Finset.mem_image_of_mem _ hc
  have e : y = ∑ d ∈ T, f d := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact hval g
  rw [e]
  exact hmem

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemSubmoduleOfBumpsStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_submodule_of_bumps : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (H : Subgroup G) (ρ : Representation ℂ H W) (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (y : cIndSpace H ρ) (hy : ∀ g, ∀ x ∈ K, y.1.1.1 (g * x) = y.1.1.1 g)
    (S : Submodule ℂ (cIndSpace H ρ)) (hS : ∀ c B, IsBump H ρ K c (y.1.1.1 c) B → B ∈ S), y ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.mem_of_bumps | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.mem_of_bumps | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.mem_of_bumps <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedEmbeddingMemCongruenceIff
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedEmbeddingMemCongruenceIff
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nearOne_glEmbMat_iff (s : kˣ) (m : ℕ) (A : Matrix (Fin m) (Fin m) k) :
    NearOne s (glEmbMat k m A) ↔ NearOne s A := by
  have e1 : ∀ a b : Fin m, glEmbMat k m A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
    intro a b
    simp [glEmbMat]
  have e2 : ∀ a b : Fin m, (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.castSucc a) (Fin.castSucc b) =
      (1 : Matrix (Fin m) (Fin m) k) a b := by
    intro a b
    simp [Matrix.one_apply, Fin.castSucc_inj]
  have z : (0 : k) ∈ (ballSub s : Set k) := (ballSub s).zero_mem
  constructor
  · intro h a b
    have h1 := h (Fin.castSucc a) (Fin.castSucc b)
    rwa [e1, e2] at h1
  · intro h a b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last =>
        have e : glEmbMat k m A (Fin.last m) (Fin.last m) - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) (Fin.last m) = 0 := by
          simp [glEmbMat]
        rw [e]
        exact z
      | cast j =>
        have e : glEmbMat k m A (Fin.last m) (Fin.castSucc j) - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) (Fin.castSucc j) = 0 := by
          rw [Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne', sub_zero]
          simp [glEmbMat]
        rw [e]
        exact z
    | cast i =>
      induction b using Fin.lastCases with
      | last =>
        have e : glEmbMat k m A (Fin.castSucc i) (Fin.last m) - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.castSucc i) (Fin.last m) = 0 := by
          rw [Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne, sub_zero]
          simp [glEmbMat]
        rw [e]
        exact z
      | cast j =>
        rw [e1, e2]
        exact h i j

theorem sEmb_mem_congM_iff (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (x : Mir k n) :
    sEmb k n x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs (n + 1) ↔ x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n := by
  have e1 : (((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) =
      glEmbMat k (n + 1) ((x : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := rfl
  have e2 : ((((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k)⁻¹ : GL (Fin (n + 1 + 1)) k) :
        Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) =
      glEmbMat k (n + 1) (((x : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    have : ((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k)⁻¹ = ((sEmb k n x⁻¹ : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) := by
      rw [map_inv]; rfl
    rw [this]
    rfl
  show (NearOne s (((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) ∧
        NearOne s ((((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k)⁻¹ : GL (Fin (n + 1 + 1)) k) :
          Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k)) ↔
      (NearOne s ((x : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∧
        NearOne s (((x : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
  rw [e1, e2, nearOne_glEmbMat_iff, nearOne_glEmbMat_iff]

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedEmbeddingMemCongruenceIffStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shifted_embedding_mem_congruence_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (x : Mir k n),
  sEmb k n x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs (n + 1) ↔ x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Onto.sEmb_mem_congM_iff | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.sEmb_mem_congM_iff | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Onto.sEmb_mem_congM_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusParabolicProjFactor
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusParabolicProjFactor
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem det_hgp (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m j : ℕ) (h : MirabolicParabolic k m j) :
    GeneralLinearGroup.det ((h : Mir k (m + j)) : GL (Fin (m + j + 1)) k) =
      GeneralLinearGroup.det (gpProj k m j h).1 *
        GeneralLinearGroup.det ((gpProj k m j h).2 : GL (Fin (j + 1)) k) := by
  let f : Fin m ⊕ Fin (j + 1) → Fin (m + j + 1) :=
    Sum.elim (fun a => GlobalTheory.BZMir.Leib.eGP m j ⟨false, a⟩)
      (fun b => GlobalTheory.BZMir.Leib.eGP m j ⟨true, b⟩)
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) hab <;>
      have hs := (GlobalTheory.BZMir.Leib.eGP m j).injective hab <;>
      simp_all [Sigma.mk.inj_iff]
  have hf : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by simp only [Fintype.card_sum, Fintype.card_fin]; omega⟩
  have hA : ∀ a b : Fin m,
      (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a b =
        (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (GlobalTheory.BZMir.Leib.eGP m j ⟨false, a⟩) (GlobalTheory.BZMir.Leib.eGP m j ⟨false, b⟩) :=
    fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j h) false a b
  have hD : ∀ a b : Fin (j + 1),
      (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) : Matrix (Fin (j + 1)) (Fin (j + 1)) k) a b =
        (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (GlobalTheory.BZMir.Leib.eGP m j ⟨true, a⟩) (GlobalTheory.BZMir.Leib.eGP m j ⟨true, b⟩) :=
    fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j h) true a b
  have hzero := (GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff k m j (h : GlobalTheory.BZMir.Mir k (m + j))).mp h.2
  have hsub : (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k).submatrix (Equiv.ofBijective f hf) (Equiv.ofBijective f hf) =
      Matrix.fromBlocks
        (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)
        (Matrix.of fun a b => (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
          Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) (f (Sum.inl a)) (f (Sum.inr b)))
        0
        (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) :
          Matrix (Fin (j + 1)) (Fin (j + 1)) k) := by
    ext (a | a) (b | b)
    · exact (hA a b).symm
    · rfl
    · exact hzero a b
    · exact (hD a b).symm
  have key : Matrix.det (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) =
      Matrix.det (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *
        Matrix.det (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) :
          Matrix (Fin (j + 1)) (Fin (j + 1)) k) := by
    rw [← Matrix.det_submatrix_equiv_self (Equiv.ofBijective f hf), hsub, Matrix.det_fromBlocks_zero₂₁]
  ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]
  exact key

theorem dpowM_hgp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (s : ℝ) (h : MirabolicParabolic k m j),
    dpowM (m + j) s (h : Mir k (m + j)) = dpow m s (gpProj k m j h).1 * dpowM j s (gpProj k m j h).2 := by
  intro k _ _ _ _ m j s h
  have h1 : GlobalTheory.RgGu.Leib.dpowM (m + j) s (h : GlobalTheory.BZMir.Mir k (m + j)) =
      GlobalTheory.BZMir.Leib.dpow (m + j + 1) s ((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) := rfl
  have h2 : GlobalTheory.RgGu.Leib.dpowM j s (GlobalTheory.BZMir.Leib.gpProj k m j h).2 =
      GlobalTheory.BZMir.Leib.dpow (j + 1) s ((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) := rfl
  have h3 : ∀ (n : ℕ) (g : GL (Fin n) k),
      GlobalTheory.BZMir.Leib.dpow n s g = GlobalTheory.SmGL.absPow k (s : ℂ) (GeneralLinearGroup.det g) :=
    fun _ _ => rfl
  rw [h1, h2, h3, h3, h3, GlobalTheory.CompanionTheory.LeibPhi.det_hgp, map_mul]

end GlobalTheory.CompanionTheory.LeibPhi

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusParabolicProjFactorStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_parabolic_proj_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (s : ℝ) (h : MirabolicParabolic k m j),
    dpowM (m + j) s (h : Mir k (m + j)) = dpow m s (gpProj k m j h).1 * dpowM j s (gpProj k m j h).2 := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.dpowM_hgp | exact GlobalTheory.CompanionTheory.LeibPhi.dpowM_hgp | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.dpowM_hgp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemParabolicIffMemEmbedded
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemParabolicIffMemEmbedded
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.IotaMem

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem iotaM_castSucc_castSucc (n : ℕ) (y : Mir k n) (r c : Fin (n + 1)) :
    (((embedding₂ k n y : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix _ _ k) (Fin.castSucc r) (Fin.castSucc c) =
      ((y : GL (Fin (n + 1)) k) : Matrix _ _ k) r c := by
  simp only [embedding₂, MonoidHom.coe_comp, Function.comp_apply]
  unfold levi
  simp [glEmb, glEmbHom, glEmbMat]

theorem iotaM_last_castSucc (n : ℕ) (y : Mir k n) (c : Fin (n + 1)) :
    (((embedding₂ k n y : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix _ _ k) (Fin.last (n + 1)) (Fin.castSucc c) = 0 := by
  simp only [embedding₂, MonoidHom.coe_comp, Function.comp_apply]
  unfold levi
  simp [glEmb, glEmbHom, glEmbMat]

end GlobalTheory.CompanionTheory.LeibPhi.IotaMem

namespace GlobalTheory.CompanionTheory.LeibPhi


open GlobalTheory.CompanionTheory.LeibPhi.IotaMem in
theorem mem_mirabolicParabolic_iff_iotaM_mem (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) (y : Mir k (m + j)) :
    y ∈ MirabolicParabolic k m j ↔ embedding₂ k (m + j) y ∈ MirabolicParabolic k m (j + 1) := by
  have mem_iff (m j : ℕ) (g : Mir k (m + j)) :
      g ∈ MirabolicParabolic k m j ↔ ∀ (b : Fin (j + 1)) (a : Fin m),
        ((g : GL (Fin (m + j + 1)) k) : Matrix _ _ k)
          (eGP m j ⟨true, b⟩) (eGP m j ⟨false, a⟩) = 0 := by
    show (g : GL (Fin (m + j + 1)) k) ∈ parab k (eGP m j) ↔ _
    rw [mem_parab_iff]
    constructor
    · intro h b a
      exact h true false b a (by decide)
    · intro h x y i l hxy
      cases x <;> cases y <;> first | exact absurd hxy (by decide) | exact h i l
  rw [mem_iff, mem_iff]
  have eF : ∀ a : Fin m, eGP m (j + 1) ⟨false, a⟩ = Fin.castSucc (eGP m j ⟨false, a⟩) := by
    intro a
    ext
    simp [blockIndex_false_val]
  have eT : ∀ b : Fin (j + 1),
      eGP m (j + 1) ⟨true, Fin.castSucc b⟩ = Fin.castSucc (eGP m j ⟨true, b⟩) := by
    intro b
    ext
    simp [blockIndex_true_val]
  have eL : eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩ = Fin.last (m + j + 1) := by
    ext
    simp [blockIndex_true_val]
    omega
  constructor
  · intro h b a
    induction b using Fin.lastCases with
    | last =>
      rw [eL, eF]
      exact iotaM_last_castSucc k (m + j) y _
    | cast b =>
      rw [eT, eF]
      rw [iotaM_castSucc_castSucc k (m + j) y]
      exact h b a
  · intro h b a
    have hb := h (Fin.castSucc b) a
    rw [eT, eF, iotaM_castSucc_castSucc k (m + j) y] at hb
    exact hb

end GlobalTheory.CompanionTheory.LeibPhi

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemParabolicIffMemEmbeddedStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_parabolic_iff_mem_embedded : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (y : Mir k (m + j)), y ∈ MirabolicParabolic k m j ↔ embedding₂ k (m + j) y ∈ MirabolicParabolic k m (j + 1) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff_iotaM_mem | exact GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff_iotaM_mem | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff_iotaM_mem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitOrderFgIdealProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitOrderFgIdealProduct
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

namespace GlobalTheory.CompanionTheory.KFin

theorem exists_larger_of_valuationSubring {k : Type} [Field k] (O : ValuationSubring k) (a b : k) :
    ∃ c : k, (c = a ∨ c = b) ∧ (∃ u ∈ O, a = c * u) ∧ (∃ u ∈ O, b = c * u) := by
  by_cases ha : a = 0
  · exact ⟨b, Or.inr rfl, ⟨0, O.zero_mem, by simp [ha]⟩, ⟨1, O.one_mem, by simp⟩⟩
  by_cases hb : b = 0
  · exact ⟨a, Or.inl rfl, ⟨1, O.one_mem, by simp⟩, ⟨0, O.zero_mem, by simp [hb]⟩⟩
  rcases O.mem_or_inv_mem (a / b) with h | h
  · exact ⟨b, Or.inr rfl, ⟨a / b, h, by field_simp⟩, ⟨1, O.one_mem, by simp⟩⟩
  · refine ⟨a, Or.inl rfl, ⟨1, O.one_mem, by simp⟩, ⟨(a / b)⁻¹, h, ?_⟩⟩
    field_simp

theorem fg_eq_prod_principal {k R : Type} [Field k] [CommRing R] (O : ValuationSubring k)
    (φ : R ≃+* k × k) (𝔬 : Subring R)
    (h𝔬 : ∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) (I : Submodule 𝔬 R) (hI : I.FG) :
    ∃ α β : k, ∀ r, r ∈ I ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ (∃ y ∈ O, (φ r).2 = β * y) := by
  induction I, hI using Submodule.fg_induction with
  | singleton r₀ =>
    refine ⟨(φ r₀).1, (φ r₀).2, fun r => ?_⟩
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨t, rfl⟩
      have ht := (h𝔬 t).1 t.2
      have hs : φ (t • r₀) = φ (t : R) * φ r₀ := by
        rw [Subring.smul_def, smul_eq_mul, map_mul]
      refine ⟨⟨(φ (t : R)).1, ht.1, ?_⟩, ⟨(φ (t : R)).2, ht.2, ?_⟩⟩
      · rw [hs, Prod.fst_mul, mul_comm]
      · rw [hs, Prod.snd_mul, mul_comm]
    · rintro ⟨⟨x, hx, h1⟩, ⟨y, hy, h2⟩⟩
      have hmem : φ.symm (x, y) ∈ 𝔬 := by
        rw [h𝔬]
        simpa using ⟨hx, hy⟩
      refine ⟨⟨φ.symm (x, y), hmem⟩, ?_⟩
      apply φ.injective
      rw [Subring.smul_def, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply]
      ext
      · simp [h1, mul_comm]
      · simp [h2, mul_comm]
  | sup I₁ I₂ _ _ ih₁ ih₂ =>
    obtain ⟨α₁, β₁, h₁⟩ := ih₁
    obtain ⟨α₂, β₂, h₂⟩ := ih₂
    obtain ⟨α, hα, ⟨u₁, hu₁, e₁⟩, ⟨u₂, hu₂, e₂⟩⟩ := exists_larger_of_valuationSubring O α₁ α₂
    obtain ⟨β, hβ, ⟨v₁, hv₁, f₁⟩, ⟨v₂, hv₂, f₂⟩⟩ := exists_larger_of_valuationSubring O β₁ β₂
    refine ⟨α, β, fun r => ?_⟩
    constructor
    · intro hr
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hr
      obtain ⟨⟨x₁, hx₁, p₁⟩, ⟨y₁, hy₁, q₁⟩⟩ := (h₁ a).1 ha
      obtain ⟨⟨x₂, hx₂, p₂⟩, ⟨y₂, hy₂, q₂⟩⟩ := (h₂ b).1 hb
      refine ⟨⟨u₁ * x₁ + u₂ * x₂, O.add_mem _ _ (O.mul_mem _ _ hu₁ hx₁) (O.mul_mem _ _ hu₂ hx₂), ?_⟩,
        ⟨v₁ * y₁ + v₂ * y₂, O.add_mem _ _ (O.mul_mem _ _ hv₁ hy₁) (O.mul_mem _ _ hv₂ hy₂), ?_⟩⟩
      · rw [map_add (f := _), Prod.fst_add, p₁, p₂, e₁, e₂]
        ring
      · rw [map_add (f := _), Prod.snd_add, q₁, q₂, f₁, f₂]
        ring
    · rintro ⟨⟨x, hx, p⟩, ⟨y, hy, q⟩⟩
      have hsplit : r = φ.symm ((φ r).1, 0) + φ.symm (0, (φ r).2) := by
        apply φ.injective
        rw [map_add (f := _), RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
        ext <;> simp
      rw [hsplit]
      refine Submodule.add_mem _ ?_ ?_
      · rcases hα with rfl | rfl
        · refine Submodule.mem_sup_left ((h₁ _).2 ?_)
          simp only [RingEquiv.apply_symm_apply]
          exact ⟨⟨x, hx, p⟩, ⟨0, O.zero_mem, by simp⟩⟩
        · refine Submodule.mem_sup_right ((h₂ _).2 ?_)
          simp only [RingEquiv.apply_symm_apply]
          exact ⟨⟨x, hx, p⟩, ⟨0, O.zero_mem, by simp⟩⟩
      · rcases hβ with rfl | rfl
        · refine Submodule.mem_sup_left ((h₁ _).2 ?_)
          simp only [RingEquiv.apply_symm_apply]
          exact ⟨⟨0, O.zero_mem, by simp⟩, ⟨y, hy, q⟩⟩
        · refine Submodule.mem_sup_right ((h₂ _).2 ?_)
          simp only [RingEquiv.apply_symm_apply]
          exact ⟨⟨0, O.zero_mem, by simp⟩, ⟨y, hy, q⟩⟩

end GlobalTheory.CompanionTheory.KFin
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitOrderFgIdealProductStatement
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_order_fg_ideal_product : ∀ {k R : Type} [Field k] [CommRing R] (O : ValuationSubring k) (φ : R ≃+* k × k) (𝔬 : Subring R), (∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) → ∀ I : Submodule 𝔬 R, I.FG → ∃ α β : k, ∀ r, r ∈ I ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ (∃ y ∈ O, (φ r).2 = β * y) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.fg_eq_prod_principal | exact GlobalTheory.CompanionTheory.KFin.fg_eq_prod_principal | (intros; apply GlobalTheory.CompanionTheory.KFin.fg_eq_prod_principal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionTwistEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionTwistEquiv
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.TwCInd

section SlopeTestRemainingChoices

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W]

theorem cIndSpace_ext {H : Subgroup G} {τ : Representation ℂ H W} {a b : cIndSpace H τ}
    (h : ∀ g, a.1.1.1 g = b.1.1.1 g) : a = b :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

theorem mul_mem_indSpace {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    (fun g => ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g) ∈ indSpace H τ' := by
  intro h g
  have e : f.1.1.1 ((h : G) * g) = τ h (f.1.1.1 g) := f.1.1.2 h g
  beta_reduce
  rw [e, map_smul, hτ, map_mul, Units.val_mul, mul_smul, smul_comm]

theorem mul_mem_smoothPart {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    (⟨_, mul_mem_indSpace hτ f⟩ : indSpace H τ') ∈ smoothPart (ind H τ') := by
  obtain ⟨L, hL, hLi⟩ := cInd_right_inv H τ f
  refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H τ') (K ⊓ L) (hK.inter hL) _
    fun x hx => ?_
  apply Subtype.ext
  funext g
  show ((ψ (g * x) : ℂˣ) : ℂ) • f.1.1.1 (g * x) = ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g
  rw [hLi g x hx.2, map_mul, hψ x hx.1, mul_one]

def mulC {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    cIndSpace H τ' :=
  ⟨⟨⟨_, mul_mem_indSpace hτ f⟩, mul_mem_smoothPart hK hψ hτ f⟩, by
    obtain ⟨C, hC, hf⟩ := f.2
    refine ⟨C, hC, fun g hg => hf g fun h0 => hg ?_⟩
    show ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g = 0
    rw [show f.1.1.1 g = 0 from h0, smul_zero]⟩

theorem mulC_apply {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) (g : G) :
    (mulC hK hψ hτ f).1.1.1 g = ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g := rfl

end SlopeTestRemainingChoices

theorem nonempty_twist_cInd_equiv : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (χ : G →* ℂˣ), IsOpen (χ.ker : Set G) →
    Nonempty ((GlobalTheory.SmGL.twist (cInd H σ) χ).Equiv (cInd H (GlobalTheory.SmGL.twist σ (χ.comp H.subtype)))) := by
  intro G W _ _ _ _ _ H σ χ hχ
  have h1 : ∀ x ∈ χ.ker, χ x = 1 := fun x hx => hx
  have h2 : ∀ x ∈ χ.ker, χ⁻¹ x = 1 := fun x hx => by
    rw [MonoidHom.inv_apply, show χ x = 1 from hx, inv_one]
  have t1 : ∀ (h : H) (w : W), GlobalTheory.SmGL.twist σ (χ.comp H.subtype) h w = ((χ h : ℂˣ) : ℂ) • σ h w :=
    fun _ _ => rfl
  have t2 : ∀ (h : H) (w : W), σ h w =
      (((χ⁻¹) h : ℂˣ) : ℂ) • GlobalTheory.SmGL.twist σ (χ.comp H.subtype) h w := fun h w => by
    rw [t1, smul_smul, ← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one,
      one_smul]
  have cancel : ∀ g, (((χ⁻¹) g : ℂˣ) : ℂ) * ((χ g : ℂˣ) : ℂ) = 1 := fun g => by
    rw [← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one]
  have cancel' : ∀ g, ((χ g : ℂˣ) : ℂ) * (((χ⁻¹) g : ℂˣ) : ℂ) = 1 := fun g => by
    rw [mul_comm, cancel]
  let e : cIndSpace H σ ≃ₗ[ℂ] cIndSpace H (GlobalTheory.SmGL.twist σ (χ.comp H.subtype)) :=
    { toFun := mulC hχ h1 t1
      map_add' := fun a b => cIndSpace_ext fun g => smul_add _ (a.1.1.1 g) (b.1.1.1 g)
      map_smul' := fun c a => cIndSpace_ext fun g => smul_comm _ c (a.1.1.1 g)
      invFun := mulC hχ h2 t2
      left_inv := fun a => cIndSpace_ext fun g => by
        rw [mulC_apply, mulC_apply, smul_smul, cancel, one_smul]
      right_inv := fun a => cIndSpace_ext fun g => by
        rw [mulC_apply, mulC_apply, smul_smul, cancel', one_smul] }
  refine ⟨Representation.Equiv.mk e fun y => LinearMap.ext fun f => cIndSpace_ext fun g => ?_⟩
  show ((χ g : ℂˣ) : ℂ) • (((χ y : ℂˣ) : ℂ) • f.1.1.1 (g * y)) =
    ((χ (g * y) : ℂˣ) : ℂ) • f.1.1.1 (g * y)
  rw [smul_smul, map_mul, Units.val_mul]

end GlobalTheory.CompanionTheory.TwCInd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionTwistEquivStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactInduction_twist_equiv : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (χ : G →* ℂˣ), IsOpen (χ.ker : Set G) →
    Nonempty ((GlobalTheory.SmGL.twist (cInd H σ) χ).Equiv (cInd H (GlobalTheory.SmGL.twist σ (χ.comp H.subtype)))) := by
  first | exact @GlobalTheory.CompanionTheory.TwCInd.nonempty_twist_cInd_equiv | exact GlobalTheory.CompanionTheory.TwCInd.nonempty_twist_cInd_equiv | (intros; apply GlobalTheory.CompanionTheory.TwCInd.nonempty_twist_cInd_equiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylNotMemClosedCell
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylNotMemClosedCell
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem piPerm_last_val (i t : ℕ) : ((piPerm i t (Fin.last ((i + 1) + t)) : Fin ((i + 1) + t + 1)) : ℕ) = i := by
  have key : ∀ x : Fin (i + (t + 1) + 1), (x : ℕ) = i + 1 + t →
      ((GlobalTheory.BZMir.Leib.eGP (i + 1) t ((GlobalTheory.BZMir.Leib.ePG i (t + 1)).symm x) :
        Fin ((i + 1) + t + 1)) : ℕ) = i := by
    intro x hx
    have hxl : x = Fin.last (i + (t + 1)) := Fin.ext (by rw [Fin.val_last]; omega)
    subst hxl
    have h2 : (GlobalTheory.BZMir.Leib.ePG i (t + 1)).symm (Fin.last (i + (t + 1))) =
        ⟨false, Fin.last i⟩ := by
      rw [Equiv.symm_apply_eq, GlobalTheory.BZMir.Leib.ePG_false_last]
    rw [h2]
    exact GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val (i + 1) t (Fin.last i)
  first
    | (simp only [GlobalTheory.CompanionTheory.BZPhiPG.piPerm, Equiv.trans_apply]; exact key _ rfl)
    | exact key _ rfl

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem wEl_inv_entry (i t : ℕ) (c : Fin ((i + 1) + t + 1)) (hc : (c : ℕ) = i) :
    ((((wEl k i t)⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castSucc c) = 1 := by
  have hσ : GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t (Fin.last ((i + 1) + t)) = c :=
    Fin.ext ((GlobalTheory.CompanionTheory.BZPhiPG.OntoO.piPerm_last_val i t).trans hc.symm)
  rw [GlobalTheory.CompanionTheory.BZPhiPG.wEl, ← map_inv]
  change GlobalTheory.BZMir.glEmbMat k ((i + 1) + t + 1)
      (((GlobalTheory.CompanionTheory.BZPhiPG.wGL k i t)⁻¹ : GL (Fin ((i + 1) + t + 1)) k) :
        Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k)
      (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castSucc c) = 1
  simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc]
  change Equiv.Perm.permMatrix k (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t) (Fin.last ((i + 1) + t)) c = 1
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hσ]

theorem dEmb_zero (i t : ℕ) : dEmb k i t 0 = 1 := by
  have h : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
    funext j
    refine Fin.addCases (fun a => ?_) (fun b => ?_) j
    · rw [Fin.append_left]; rfl
    · rw [Fin.append_right]; rfl
  apply Subtype.ext
  change GlobalTheory.BZMir.unip k ((i + 1) + (t + 1))
      (Multiplicative.ofAdd (Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k))) = 1
  rw [h, ofAdd_zero, map_one]

theorem wEl_notMem_Cl (i t : ℕ) : wEl k i t ∉ Cl k i t := by
  intro hmem
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.Cl, Set.mem_setOf_eq] at hmem
  have h := hmem (Fin.last i)
  have hc : (Fin.castLE (by omega) (Fin.last i) : Fin ((i + 1) + t + 1 + 1)) =
      Fin.castSucc (⟨i, by omega⟩ : Fin ((i + 1) + t + 1)) := Fin.ext rfl
  rw [hc, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.wEl_inv_entry k i t ⟨i, by omega⟩ rfl] at h
  exact one_ne_zero h

theorem wEl_notMem_Cl_and_dEmb_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ), wEl k i t ∉ Cl k i t ∧ dEmb k i t 0 = 1 := by
  intro k _ _ _ _ i t
  exact ⟨GlobalTheory.CompanionTheory.BZPhiPG.OntoO.wEl_notMem_Cl k i t, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.dEmb_zero k i t⟩

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylNotMemClosedCellStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_not_mem_closed_cell :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] (i t : ℕ),
      GlobalTheory.CompanionTheory.BZPhiPG.wEl (k := k) i t ∉ Cl (k := k) i t ∧
        dEmb (k := k) i t 0 = 1 := by
  intro k _ _ _ _ i t
  constructor
  · intro hmem
    simp only [GlobalTheory.CompanionTheory.BZPhiPG.Cl, Set.mem_ofPred_eq] at hmem
    let c : Fin ((i + 1) + t + 1) := ⟨i, by omega⟩
    have hc : (Fin.castLE (by omega) (Fin.last i) : Fin ((i + 1) + t + 2)) =
        Fin.castSucc c := Fin.ext rfl
    have hzero := hmem (Fin.last i)
    rw [hc, GlobalTheory.CompanionTheory.BZPhiPG.wEl, ← map_inv] at hzero
    change GlobalTheory.BZMir.glEmbMat k ((i + 1) + t + 1)
        (((wGL (k := k) i t)⁻¹ : GL (Fin ((i + 1) + t + 1)) k) :
          Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k)
        (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castSucc c) = 0 at hzero
    simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc] at hzero
    change Equiv.Perm.permMatrix k (piPerm i t) (Fin.last ((i + 1) + t)) c = 0 at hzero
    have hperm : piPerm i t (Fin.last ((i + 1) + t)) = c :=
      Fin.ext (piPerm_last_val i t)
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hperm] at hzero
  · have h : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
      funext j
      refine Fin.addCases (fun a => ?_) (fun b => ?_) j
      · rw [Fin.append_left]; rfl
      · rw [Fin.append_right]; rfl
    apply Subtype.ext
    change GlobalTheory.BZMir.unip k ((i + 1) + (t + 1))
      (Multiplicative.ofAdd (Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k))) = 1
    rw [h, ofAdd_zero, map_one]
end
end
