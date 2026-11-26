module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingWordOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapSecondProperty

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriDoubleCosetFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriDoubleCosetFinite
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwDcosFin

theorem finite_image_mk_of_isCompact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Subgroup G} (hH : IsOpen (H : Set G)) {C : Set G} (hC : IsCompact C) :
    ((QuotientGroup.mk : G → G ⧸ H) '' C).Finite := by
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover (fun g : G => (fun x => g * x) '' (H : Set G))
    (fun g => (Homeomorph.mulLeft g).isOpenMap _ hH)
    (fun x _ => Set.mem_iUnion.2 ⟨x, 1, H.one_mem, mul_one x⟩)
  refine (s.finite_toSet.image (QuotientGroup.mk : G → G ⧸ H)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hy⟩ : ∃ g ∈ s, g⁻¹ * x ∈ H := by
    simpa using hs hx
  exact ⟨g, hg, QuotientGroup.eq.2 hy⟩

theorem dcos_finite_support_iwGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (a : ℕ) (t : GLw a w),
    (Function.support fun q : GLw a w ⧸ iwGL a w => dcos a w t q.out).Finite ∧ IsOpen (iwGL a w : Set (GLw a w)) ∧
      IsCompact (iwGL a w : Set (GLw a w)) ∧ iwGL a w ≤ GlobalTheory.LFun.KGL w (n := a) ∧
      (iwGL a w).relIndex (GlobalTheory.LFun.KGL w (n := a)) ≠ 0 := by
  intro E _ _ _ w a t
  have hIo : IsOpen (iwGL a w : Set (GLw a w)) :=
    GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin a)
  have hIc : IsCompact (iwGL a w : Set (GLw a w)) :=
    GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori (w.adicCompletion E) (Fin a)
  refine ⟨?_, hIo, hIc, GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w a,
    GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero hIo (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w a)⟩
  refine (finite_image_mk_of_isCompact hIo (GlobalTheory.CompanionTheory.IwFacts.isCompact_support_dcos w a t)).subset ?_
  intro q hq
  exact ⟨q.out, hq, QuotientGroup.out_eq' q⟩

end GlobalTheory.CompanionTheory.IwDcosFin
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriDoubleCosetFiniteStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwahori_double_coset_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (a : ℕ) (t : GLw a w), (Function.support fun q : GLw a w ⧸ iwGL a w => dcos a w t q.out).Finite ∧ IsOpen (iwGL a w : Set (GLw a w)) ∧ IsCompact (iwGL a w : Set (GLw a w)) ∧ iwGL a w ≤ GlobalTheory.LFun.KGL w (n := a) ∧ (iwGL a w).relIndex (GlobalTheory.LFun.KGL w (n := a)) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.IwDcosFin.dcos_finite_support_iwGL | exact GlobalTheory.CompanionTheory.IwDcosFin.dcos_finite_support_iwGL | (intros; apply GlobalTheory.CompanionTheory.IwDcosFin.dcos_finite_support_iwGL <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportProductQuotient
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportProductQuotient
namespace GlobalTheory.CompanionTheory.ProdQuotient

theorem support_mul_out_finite (G₁ G₂ : Type) [Group G₁] [Group G₂] (K₁ : Subgroup G₁)
    (K₂ : Subgroup G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ)
    (h₁ : (Function.support fun q : G₁ ⧸ K₁ => f₁ q.out).Finite)
    (h₂ : (Function.support fun q : G₂ ⧸ K₂ => f₂ q.out).Finite)
    (i₁ : ∀ k ∈ K₁, ∀ g, f₁ (g * k) = f₁ g) (i₂ : ∀ k ∈ K₂, ∀ g, f₂ (g * k) = f₂ g) :
    (Function.support fun q : (G₁ × G₂) ⧸ K₁.prod K₂ => f₁ q.out.1 * f₂ q.out.2).Finite := by
  let φ : (G₁ × G₂) ⧸ K₁.prod K₂ → (G₁ ⧸ K₁) × (G₂ ⧸ K₂) :=
    fun q => ((q.out.1 : G₁ ⧸ K₁), (q.out.2 : G₂ ⧸ K₂))
  have hinj : Function.Injective φ := by
    intro a b hab
    have e₁ : ((a.out.1 : G₁ ⧸ K₁)) = (b.out.1 : G₁ ⧸ K₁) := congrArg Prod.fst hab
    have e₂ : ((a.out.2 : G₂ ⧸ K₂)) = (b.out.2 : G₂ ⧸ K₂) := congrArg Prod.snd hab
    rw [QuotientGroup.eq] at e₁ e₂
    have key : ((a.out : G₁ × G₂) : (G₁ × G₂) ⧸ K₁.prod K₂) = (b.out : G₁ × G₂) := by
      rw [QuotientGroup.eq]
      exact Subgroup.mem_prod.mpr ⟨e₁, e₂⟩
    simpa using key
  have inv₁ : ∀ g : G₁, f₁ (g : G₁ ⧸ K₁).out = f₁ g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K₁ g
    rw [hk]
    exact i₁ k k.2 g
  have inv₂ : ∀ g : G₂, f₂ (g : G₂ ⧸ K₂).out = f₂ g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K₂ g
    rw [hk]
    exact i₂ k k.2 g
  refine ((h₁.prod h₂).preimage hinj.injOn).subset ?_
  intro q hq
  have hq' : f₁ q.out.1 * f₂ q.out.2 ≠ 0 := hq
  refine ⟨?_, ?_⟩
  · change f₁ (q.out.1 : G₁ ⧸ K₁).out ≠ 0
    rw [inv₁]
    exact left_ne_zero_of_mul hq'
  · change f₂ (q.out.2 : G₂ ⧸ K₂).out ≠ 0
    rw [inv₂]
    exact right_ne_zero_of_mul hq'

end GlobalTheory.CompanionTheory.ProdQuotient
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportProductQuotientStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_support_product_quotient : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ), (Function.support fun q : G₁ ⧸ K₁ => f₁ q.out).Finite → (Function.support fun q : G₂ ⧸ K₂ => f₂ q.out).Finite → (∀ k ∈ K₁, ∀ g, f₁ (g * k) = f₁ g) → (∀ k ∈ K₂, ∀ g, f₂ (g * k) = f₂ g) → (Function.support fun q : (G₁ × G₂) ⧸ K₁.prod K₂ => f₁ q.out.1 * f₂ q.out.2).Finite := by
  first | exact @GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite | exact GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite | (intros; apply GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumCosetSmulLinear
namespace GlobalTheory.CompanionTheory.HeckeSum

theorem finsum_coset_smul_linear :
    ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (K : Subgroup G) (J : Type) [Fintype J] (c : J → ℂ) (f : J → G → ℂ),
      (∀ j, (Function.support fun q : G ⧸ K => f j q.out).Finite) → ∀ v : V,
      ∑ᶠ q : G ⧸ K, (∑ j, c j * f j q.out) • ρ q.out v
        = ∑ j, c j • ∑ᶠ q : G ⧸ K, f j q.out • ρ q.out v := by
  intro G V _ _ _ ρ K J _ c f hf v
  have hs : ∀ j, (Function.support fun q : G ⧸ K => f j q.out • ρ q.out v).Finite := by
    intro j
    refine (hf j).subset ?_
    intro q hq h0
    apply hq
    show f j q.out • ρ q.out v = 0
    have h0' : f j q.out = 0 := h0
    rw [h0', zero_smul]
  have hs' : ∀ j ∈ (Finset.univ : Finset J),
      (Function.support fun q : G ⧸ K => c j • (f j q.out • ρ q.out v)).Finite := by
    intro j _
    refine (hs j).subset ?_
    intro q hq h0
    apply hq
    show c j • (f j q.out • ρ q.out v) = 0
    have h0' : f j q.out • ρ q.out v = 0 := h0
    rw [h0', smul_zero]
  calc ∑ᶠ q : G ⧸ K, (∑ j, c j * f j q.out) • ρ q.out v
      = ∑ᶠ q : G ⧸ K, ∑ j, c j • (f j q.out • ρ q.out v) := by
        refine finsum_congr fun q => ?_
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _
    _ = ∑ j, ∑ᶠ q : G ⧸ K, c j • (f j q.out • ρ q.out v) :=
        finsum_sum_comm _ _ hs'
    _ = ∑ j, c j • ∑ᶠ q : G ⧸ K, f j q.out • ρ q.out v := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_finsum' (c j) (hs j)]

end GlobalTheory.CompanionTheory.HeckeSum
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSumInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSumInvariant
namespace GlobalTheory.CompanionTheory.Hecke

theorem heckeSum_fixed :
    ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (K : Subgroup G) (f : G → ℂ), (Function.support fun q : G ⧸ K => f q.out).Finite →
      (∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → ∀ v : V, (∀ k ∈ K, ρ k v = v) →
      ∀ k ∈ K, ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v) = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v := by
  intro G V _ _ _ ρ K f hfin hbi v hv k hk
  have hsupp : (Function.support fun q : G ⧸ K => f q.out • ρ q.out v).Finite := by
    refine hfin.subset ?_
    intro q hq h0
    apply hq
    have h0' : f q.out = 0 := h0
    simp [h0']
  have hstep : ∀ q : G ⧸ K, ρ k (f q.out • ρ q.out v)
      = f (MulAction.toPerm k q).out • ρ (MulAction.toPerm k q).out v := by
    intro q
    have hmk : ((MulAction.toPerm k q : G ⧸ K).out : G ⧸ K) = ((k * q.out : G) : G ⧸ K) := by
      rw [QuotientGroup.out_eq', MulAction.toPerm_apply]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hκ : (k * q.out)⁻¹ * (MulAction.toPerm k q : G ⧸ K).out ∈ K :=
      QuotientGroup.eq.mp hmk.symm
    obtain ⟨κ, hκK, hκ⟩ : ∃ κ ∈ K, (MulAction.toPerm k q : G ⧸ K).out = k * q.out * κ :=
      ⟨_, hκ, by group⟩
    rw [hκ, (hbi κ hκK _).2, (hbi k hk _).1, map_mul, map_mul, map_smul]
    simp [hv κ hκK]
  have h1 := (ρ k).toAddMonoidHom.map_finsum hsupp
  have h2 : ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v)
      = ∑ᶠ q : G ⧸ K, ρ k (f q.out • ρ q.out v) := h1
  rw [h2, finsum_congr hstep]
  exact finsum_comp_equiv (MulAction.toPerm k) (f := fun q : G ⧸ K => f q.out • ρ q.out v)

end GlobalTheory.CompanionTheory.Hecke
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSumInvariantStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_sum_invariant : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ), (Function.support fun q : G ⧸ K => f q.out).Finite → (∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → ∀ v : V, (∀ k ∈ K, ρ k v = v) → ∀ k ∈ K, ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v) = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v := by
  first | exact @GlobalTheory.CompanionTheory.Hecke.heckeSum_fixed | exact GlobalTheory.CompanionTheory.Hecke.heckeSum_fixed | (intros; apply GlobalTheory.CompanionTheory.Hecke.heckeSum_fixed <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsJointEigenvectorNonzero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsJointEigenvectorNonzero
namespace GlobalTheory.CompanionTheory.LinAlg

open Module

theorem exists_common_eigenvector_in_submodule {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] {ι : Type} (H : ι → End ℂ W)
    (hc : ∀ i i', Commute (H i) (H i')) :
    ∀ (n : ℕ) (U : Submodule ℂ W), finrank ℂ U ≤ n → U ≠ ⊥ →
      (∀ i, ∀ x ∈ U, H i x ∈ U) →
      ∃ v ∈ U, v ≠ 0 ∧ ∃ χ : ι → ℂ, ∀ i, H i v = χ i • v := by
  intro n
  induction n with
  | zero =>
    intro U hU hne _
    exact absurd (Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hU)) hne
  | succ n ih =>
    intro U hU hne hinv
    by_cases hs : ∀ i, ∃ a : ℂ, ∀ x ∈ U, H i x = a • x
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      choose χ hχ using hs
      exact ⟨v, hv, hv0, χ, fun i => hχ i v hv⟩
    · push_neg at hs
      obtain ⟨i, hi⟩ := hs
      haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hne
      let R : End ℂ U := (H i).restrict (hinv i)
      obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue R
      obtain ⟨⟨w, hwU⟩, hw⟩ := ha.exists_hasEigenvector
      have hw' : H i w = a • w := by
        have h1 := congrArg Subtype.val hw.apply_eq_smul
        simpa [R] using h1
      have hw0 : w ≠ 0 := by
        intro h
        exact hw.2 (Subtype.ext h)
      have hmem : ∀ {x : W}, x ∈ End.eigenspace (H i) a ↔ H i x = a • x := by
        intro x
        exact End.mem_eigenspace_iff
      have hU'ne : U ⊓ End.eigenspace (H i) a ≠ ⊥ := by
        intro h
        have : w ∈ U ⊓ End.eigenspace (H i) a := ⟨hwU, hmem.mpr hw'⟩
        rw [h] at this
        exact hw0 ((Submodule.mem_bot ℂ).mp this)
      have hlt : U ⊓ End.eigenspace (H i) a < U := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro h
        obtain ⟨x, hx, hne'⟩ := hi a
        have : x ∈ U ⊓ End.eigenspace (H i) a := by rw [h]; exact hx
        exact hne' (hmem.mp this.2)
      have hfr := Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨v, hv, hv0, χ, hχ⟩ := ih (U ⊓ End.eigenspace (H i) a) (by omega) hU'ne (by
        intro k x hx
        refine ⟨hinv k x hx.1, hmem.mpr ?_⟩
        have h2 : H i x = a • x := hmem.mp hx.2
        have h3 : H i (H k x) = H k (H i x) := by
          have := congrArg (fun f : End ℂ W => f x) (hc i k).eq
          simpa using this
        rw [h3, h2, map_smul])
      exact ⟨v, hv.1, hv0, χ, hχ⟩

theorem exists_hasEigenvalue_ne_zero {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (T : End ℂ W) (v : W) (m : ℕ) (hm : finrank ℂ W ≤ m)
    (hv : (T ^ m) v ≠ 0) : ∃ μ : ℂ, μ ≠ 0 ∧ T.HasEigenvalue μ := by
  by_contra hno
  push_neg at hno
  have hbot : ∀ μ : ℂ, μ ≠ 0 → T.maxGenEigenspace μ = ⊥ := by
    intro μ hμ
    by_contra hne
    rw [End.maxGenEigenspace_eq_genEigenspace_finrank] at hne
    exact hno μ hμ (End.hasEigenvalue_of_hasGenEigenvalue (k := finrank ℂ W) hne)
  have htop : T.maxGenEigenspace 0 = ⊤ := by
    rw [eq_top_iff, ← End.iSup_maxGenEigenspace_eq_top T]
    refine iSup_le fun μ => ?_
    by_cases hμ : μ = 0
    · rw [hμ]
    · rw [hbot μ hμ]
      exact bot_le
  have hvm : v ∈ T.maxGenEigenspace 0 := htop ▸ Submodule.mem_top
  rw [End.maxGenEigenspace_eq_genEigenspace_finrank, End.mem_genEigenspace_nat] at hvm
  simp only [zero_smul, sub_zero, LinearMap.mem_ker] at hvm
  apply hv
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [add_comm, pow_add, Module.End.mul_apply, hvm, map_zero]

theorem exists_joint_eigenvector_combination_ne_zero :
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ι J : Type) [Fintype J]
      (H : ι → Module.End ℂ W), (∀ i i', Commute (H i) (H i')) →
      ∀ (c : J → ℂ) (s : J → ι) (v : W) (m : ℕ), Module.finrank ℂ W ≤ m →
        ((∑ j, c j • H (s j)) ^ m) v ≠ 0 →
        ∃ v₀ : W, v₀ ≠ 0 ∧ ∃ χ : ι → ℂ, (∀ i, H i v₀ = χ i • v₀) ∧ ∑ j, c j * χ (s j) ≠ 0 := by
  intro W _ _ _ ι J _ H hc c s v m hm hv
  obtain ⟨μ, hμ, hT⟩ := exists_hasEigenvalue_ne_zero _ v m hm hv
  have hcomm : ∀ i, Commute (∑ j, c j • H (s j)) (H i) := by
    intro i
    exact Commute.sum_left _ _ _ fun j _ => (hc (s j) i).smul_left (c j)
  obtain ⟨v₀, hv₀U, hv₀, χ, hχ⟩ := exists_common_eigenvector_in_submodule H hc _
    (End.eigenspace (∑ j, c j • H (s j)) μ) le_rfl hT (by
      intro i x hx
      rw [End.mem_eigenspace_iff] at hx ⊢
      have h3 : (∑ j, c j • H (s j)) (H i x) = H i ((∑ j, c j • H (s j)) x) := by
        have := congrArg (fun f : End ℂ W => f x) (hcomm i).eq
        simpa using this
      rw [h3, hx, map_smul])
  refine ⟨v₀, hv₀, χ, hχ, ?_⟩
  intro hsum
  have h1 : (∑ j, c j • H (s j)) v₀ = (∑ j, c j * χ (s j)) • v₀ := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hχ, Finset.sum_smul, mul_smul]
  rw [End.mem_eigenspace_iff, h1, hsum, zero_smul] at hv₀U
  exact hv₀ ((smul_eq_zero.mp hv₀U.symm).resolve_left hμ)

end GlobalTheory.CompanionTheory.LinAlg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsJointEigenvectorNonzeroStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_joint_eigenvector_nonzero : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ι J : Type) [Fintype J] (H : ι → Module.End ℂ W), (∀ i i', Commute (H i) (H i')) → ∀ (c : J → ℂ) (s : J → ι) (v : W) (m : ℕ), Module.finrank ℂ W ≤ m → ((∑ j, c j • H (s j)) ^ m) v ≠ 0 → ∃ v₀ : W, v₀ ≠ 0 ∧ ∃ χ : ι → ℂ, (∀ i, H i v₀ = χ i • v₀) ∧ ∑ j, c j * χ (s j) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.LinAlg.exists_joint_eigenvector_combination_ne_zero | exact GlobalTheory.CompanionTheory.LinAlg.exists_joint_eigenvector_combination_ne_zero | (intros; apply GlobalTheory.CompanionTheory.LinAlg.exists_joint_eigenvector_combination_ne_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativeCharacterOnCone
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativeCharacterOnCone
namespace GlobalTheory.CompanionTheory.StrictCone

theorem exists_char_of_mul_on_cone {G : Type*} [AddCommGroup G] (S : Set G)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) (f : G → ℂ)
    (hf : ∀ x ∈ S, ∀ y ∈ S, f (x + y) = f x * f y) (s₀ : G) (hs₀ : s₀ ∈ S) (hne : f s₀ ≠ 0)
    (arch : ∀ g : G, ∃ k : ℕ, 0 < k ∧ k • s₀ + g ∈ S) :
    ∃ φ : G → ℂˣ, (∀ g h, φ (g + h) = φ g * φ h) ∧ ∀ s ∈ S, f s = (φ s : ℂ) := by
  have hmem : ∀ k : ℕ, k • s₀ + s₀ ∈ S ∧ f (k • s₀ + s₀) ≠ 0 := by
    intro k
    induction k with
    | zero => simpa using ⟨hs₀, hne⟩
    | succ n ih =>
      have h1 : (n + 1) • s₀ + s₀ = (n • s₀ + s₀) + s₀ := by rw [succ_nsmul]
      rw [h1]
      refine ⟨hS _ ih.1 _ hs₀, ?_⟩
      rw [hf _ ih.1 _ hs₀]
      exact mul_ne_zero ih.2 hne
  have hmem' : ∀ k : ℕ, 0 < k → k • s₀ ∈ S ∧ f (k • s₀) ≠ 0 := by
    intro k hk
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    rw [succ_nsmul]
    exact hmem n
  have hnz : ∀ z ∈ S, f z ≠ 0 := by
    intro z hz h0
    obtain ⟨k, hk, hw⟩ := arch (-z)
    have h2 : k • s₀ = z + (k • s₀ + -z) := by abel
    have h3 := (hmem' k hk).2
    rw [h2, hf _ hz _ hw, h0, zero_mul] at h3
    exact h3 rfl
  have wd : ∀ c₁ ∈ S, ∀ c₂ ∈ S, ∀ d₁ ∈ S, ∀ d₂ ∈ S, c₁ - c₂ = d₁ - d₂ →
      f c₁ / f c₂ = f d₁ / f d₂ := by
    intro c₁ h₁ c₂ h₂ d₁ h₃ d₂ h₄ h
    have e : c₁ + d₂ = d₁ + c₂ := by
      have : c₁ + d₂ - (d₁ + c₂) = (c₁ - c₂) - (d₁ - d₂) := by abel
      rw [← sub_eq_zero, this, h, sub_self]
    have e' := congrArg f e
    rw [hf _ h₁ _ h₄, hf _ h₃ _ h₂] at e'
    rw [div_eq_div_iff (hnz _ h₂) (hnz _ h₄)]
    exact e'
  choose k hk hd using arch
  have hc : ∀ g, k g • s₀ ∈ S := fun g => (hmem' _ (hk g)).1
  let φ : G → ℂˣ := fun g =>
    Units.mk0 (f (k g • s₀ + g) / f (k g • s₀)) (div_ne_zero (hnz _ (hd g)) (hnz _ (hc g)))
  refine ⟨φ, ?_, ?_⟩
  · intro g h
    apply Units.ext
    simp only [φ, Units.val_mul, Units.val_mk0]
    have := wd _ (hd (g + h)) _ (hc (g + h)) _ (hS _ (hd g) _ (hd h)) _ (hS _ (hc g) _ (hc h))
      (by abel)
    rw [this, hf _ (hd g) _ (hd h), hf _ (hc g) _ (hc h), mul_div_mul_comm]
  · intro s hs
    simp only [φ, Units.val_mk0]
    rw [hf _ (hc s) _ hs, mul_div_cancel_left₀ _ (hnz _ (hc s))]

theorem char_eq_prod {n : ℕ} (φ : (Fin n → ℤ) → ℂˣ) (h : ∀ g g', φ (g + g') = φ g * φ g') (x : Fin n → ℤ) :
    φ x = ∏ i, φ (Pi.single i 1) ^ x i := by
  let F : (Fin n → ℤ) →+ Additive ℂˣ :=
    AddMonoidHom.mk' (fun g => Additive.ofMul (φ g)) (fun g g' => by rw [h]; rfl)
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℤ) : Fin n → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h2 : F x = ∑ i, x i • F (Pi.single i 1) := by
    conv_lhs => rw [hx]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_zsmul]
  have h3 := congrArg Additive.toMul h2
  simpa [F, toMul_sum] using h3

theorem zpow_sum_units (Q : ℂˣ) {n : ℕ} (e : Fin n → ℤ) : Q ^ (∑ i, e i) = ∏ i, Q ^ e i := by
  classical
  refine Finset.induction_on (Finset.univ : Finset (Fin n)) (by simp) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem char_split {n : ℕ} (c : Fin n → ℤ) (Q : ℂˣ) (φ : (Fin n → ℤ) → ℂˣ)
    (h : ∀ g g', φ (g + g') = φ g * φ g') :
    ∃ ξ : Fin n → ℂˣ, ∀ x, φ x = Q ^ (∑ i, c i * x i) * ∏ i, ξ i ^ x i := by
  refine ⟨fun i => φ (Pi.single i 1) * Q ^ (-c i), fun x => ?_⟩
  rw [char_eq_prod φ h x, zpow_sum_units, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_zpow, ← zpow_mul, mul_left_comm, ← zpow_add]
  simp

def IsStrict {n : ℕ} (x : Fin n → ℤ) : Prop := ∀ i j, i < j → x j + 1 ≤ x i

theorem IsStrict.add {n : ℕ} {x y : Fin n → ℤ} (hx : IsStrict x) (hy : IsStrict y) :
    IsStrict (x + y) := by
  intro i j hij
  have := hx i j hij
  have := hy i j hij
  simp only [Pi.add_apply]
  omega

theorem IsStrict.arch {n : ℕ} {s : Fin n → ℤ} (hs : IsStrict s) (g : Fin n → ℤ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → IsStrict (k • s + g) := by
  refine ⟨1 + ∑ i, ∑ j, (g i - g j).natAbs, fun k hk i j hij => ?_⟩
  have h1 : (g j - g i).natAbs ≤ ∑ i, ∑ j, (g i - g j).natAbs :=
    (Finset.single_le_sum (f := fun j' => (g j' - g i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (by
        rw [Finset.sum_comm]
        exact Finset.single_le_sum (f := fun i' => ∑ j', (g j' - g i').natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have h2 : s j + 1 ≤ s i := hs i j hij
  have h3 : (k : ℤ) * (s j + 1) ≤ (k : ℤ) * s i :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : (g j - g i) ≤ ((g j - g i).natAbs : ℤ) := by omega
  generalize (∑ i, ∑ j, (g i - g j).natAbs) = T at hk h1
  have h5 : (1 : ℤ) + T ≤ k := by exact_mod_cast hk
  have h6 : ((g j - g i).natAbs : ℤ) ≤ T := by exact_mod_cast h1
  rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
  nlinarith

theorem mul_on_cone_eq_delta_char : ∀ (a b : ℕ) (q : ℂ), q ≠ 0 → ∀ χ : (Fin a → ℤ) → (Fin b → ℤ) → ℂ, (∀ x x' y y', (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → x' j + 1 ≤ x' i) → (∀ i j, i < j → y j + 1 ≤ y i) → (∀ i j, i < j → y' j + 1 ≤ y' i) → χ (x + x') (y + y') = χ x y * χ x' y') → (∃ x y, (∀ i j, i < j → x j + 1 ≤ x i) ∧ (∀ i j, i < j → y j + 1 ≤ y i) ∧ χ x y ≠ 0) → ∃ (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ), ∀ x y, (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → y j + 1 ≤ y i) → χ x y = q ^ (∑ i : Fin a, ((a : ℤ) - 1 - 2 * (i : ℕ)) * x i) * (∏ i, ((ξa i ^ x i : ℂˣ) : ℂ)) * (q ^ (∑ i : Fin b, ((b : ℤ) - 1 - 2 * (i : ℕ)) * y i) * ∏ i, ((ξb i ^ y i : ℂˣ) : ℂ)) := by
  intro a b q hq χ hχ ⟨x₀, y₀, hx₀, hy₀, hne⟩
  let S : Set ((Fin a → ℤ) × (Fin b → ℤ)) := {z | IsStrict z.1 ∧ IsStrict z.2}
  obtain ⟨φ, hφ, hfφ⟩ := exists_char_of_mul_on_cone S
    (fun x hx y hy => ⟨hx.1.add hy.1, hx.2.add hy.2⟩) (fun z => χ z.1 z.2)
    (fun x hx y hy => hχ _ _ _ _ hx.1 hy.1 hx.2 hy.2) (x₀, y₀) ⟨hx₀, hy₀⟩ hne
    (fun g => by
      obtain ⟨K₁, h₁⟩ := IsStrict.arch (s := x₀) hx₀ g.1
      obtain ⟨K₂, h₂⟩ := IsStrict.arch (s := y₀) hy₀ g.2
      refine ⟨K₁ + K₂ + 1, by omega, ?_, ?_⟩
      · exact h₁ _ (by omega)
      · exact h₂ _ (by omega))
  let Q : ℂˣ := Units.mk0 q hq
  obtain ⟨ξa, ha⟩ := char_split (fun i : Fin a => (a : ℤ) - 1 - 2 * (i : ℕ)) Q
    (fun x => φ (x, 0)) (fun g g' => by rw [← hφ]; simp)
  obtain ⟨ξb, hb⟩ := char_split (fun i : Fin b => (b : ℤ) - 1 - 2 * (i : ℕ)) Q
    (fun y => φ (0, y)) (fun g g' => by rw [← hφ]; simp)
  refine ⟨ξa, ξb, fun x y hx hy => ?_⟩
  have h1 : χ x y = (φ (x, y) : ℂ) := hfφ (x, y) ⟨hx, hy⟩
  have h2 : φ (x, y) = φ (x, 0) * φ (0, y) := by rw [← hφ]; simp
  rw [h1, h2, ha x, hb y]
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, Q, Units.coe_prod]

end GlobalTheory.CompanionTheory.StrictCone
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativeCharacterOnConeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicative_character_on_cone : ∀ (a b : ℕ) (q : ℂ), q ≠ 0 → ∀ χ : (Fin a → ℤ) → (Fin b → ℤ) → ℂ, (∀ x x' y y', (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → x' j + 1 ≤ x' i) → (∀ i j, i < j → y j + 1 ≤ y i) → (∀ i j, i < j → y' j + 1 ≤ y' i) → χ (x + x') (y + y') = χ x y * χ x' y') → (∃ x y, (∀ i j, i < j → x j + 1 ≤ x i) ∧ (∀ i j, i < j → y j + 1 ≤ y i) ∧ χ x y ≠ 0) → ∃ (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ), ∀ x y, (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → y j + 1 ≤ y i) → χ x y = q ^ (∑ i : Fin a, ((a : ℤ) - 1 - 2 * (i : ℕ)) * x i) * (∏ i, ((ξa i ^ x i : ℂˣ) : ℂ)) * (q ^ (∑ i : Fin b, ((b : ℤ) - 1 - 2 * (i : ℕ)) * y i) * ∏ i, ((ξb i ^ y i : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.StrictCone.mul_on_cone_eq_delta_char | exact GlobalTheory.CompanionTheory.StrictCone.mul_on_cone_eq_delta_char | (intros; apply GlobalTheory.CompanionTheory.StrictCone.mul_on_cone_eq_delta_char <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdRelIndexNeZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdRelIndexNeZero
namespace GlobalTheory.CompanionTheory.GroupIndex.RelProd

theorem relIndex_prod_eq_mul {G₁ G₂ : Type} [Group G₁] [Group G₂]
    (I₁ K₁ : Subgroup G₁) (I₂ K₂ : Subgroup G₂) :
    (I₁.prod I₂).relIndex (K₁.prod K₂) = I₁.relIndex K₁ * I₂.relIndex K₂ := by
  have hmap : ((I₁.prod I₂).subgroupOf (K₁.prod K₂)) =
      ((I₁.subgroupOf K₁).prod (I₂.subgroupOf K₂)).comap
        (Subgroup.prodEquiv K₁ K₂).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_prod, Subgroup.mem_comap]
    exact Iff.rfl
  unfold Subgroup.relIndex
  rw [hmap, Subgroup.index_comap_of_surjective _ (Subgroup.prodEquiv K₁ K₂).surjective,
    Subgroup.index_prod]

theorem relIndex_prod_ne_zero_of_ne_zero :
    ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (I₁ K₁ : Subgroup G₁) (I₂ K₂ : Subgroup G₂),
      I₁.relIndex K₁ ≠ 0 → I₂.relIndex K₂ ≠ 0 → (I₁.prod I₂).relIndex (K₁.prod K₂) ≠ 0 := by
  intro G₁ G₂ _ _ I₁ K₁ I₂ K₂ h₁ h₂
  rw [relIndex_prod_eq_mul]
  exact mul_ne_zero h₁ h₂

end GlobalTheory.CompanionTheory.GroupIndex.RelProd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdRelIndexNeZeroStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_rel_index_ne_zero : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (I₁ K₁ : Subgroup G₁) (I₂ K₂ : Subgroup G₂), I₁.relIndex K₁ ≠ 0 → I₂.relIndex K₂ ≠ 0 → (I₁.prod I₂).relIndex (K₁.prod K₂) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_ne_zero_of_ne_zero | exact GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_ne_zero_of_ne_zero | (intros; apply GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_ne_zero_of_ne_zero <;> assumption)
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.Tail

section Gen

variable {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V]

theorem mem_fixed_iff' (ρ : Representation ℂ Γ V) (K : Subgroup Γ) (v : V) :
    v ∈ GlobalTheory.PRep.fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  simp [GlobalTheory.PRep.fixed, GlobalTheory.PRep.eig]

theorem hsum_eq (ρ : Representation ℂ Γ V) (K : Subgroup Γ) (f : Γ → ℂ) {s : Finset (Γ ⧸ K)}
    (hs : (Function.support fun q : Γ ⧸ K => f q.out) ⊆ s) (v : V) :
    ∑ᶠ q : Γ ⧸ K, f q.out • ρ q.out v = ∑ q ∈ s, f q.out • ρ q.out v := by
  apply finsum_eq_sum_of_support_subset
  intro q hq
  apply hs
  intro h0
  apply hq
  simp [h0]

theorem hk_apply_sum (ρ : Representation ℂ Γ V) (K : Subgroup Γ) (f : Γ → ℂ)
    (hfin : (Function.support fun q : Γ ⧸ K => f q.out).Finite) (v : V) :
    (∑ q ∈ hfin.toFinset, f q.out • ρ q.out) v = ∑ᶠ q : Γ ⧸ K, f q.out • ρ q.out v := by
  rw [hsum_eq ρ K f hfin.coe_toFinset.ge v, LinearMap.sum_apply]
  rfl

theorem hk_mapsTo (ρ : Representation ℂ Γ V) (K : Subgroup Γ) (f : Γ → ℂ)
    (hfin : (Function.support fun q : Γ ⧸ K => f q.out).Finite)
    (hbi : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) :
    ∀ v ∈ GlobalTheory.PRep.fixed ρ K, (∑ q ∈ hfin.toFinset, f q.out • ρ q.out) v ∈ GlobalTheory.PRep.fixed ρ K := by
  intro v hv
  rw [hk_apply_sum]
  exact (mem_fixed_iff' ρ K _).2 (GlobalTheory.T.hecke_sum_invariant Γ V ρ K f hfin hbi v ((mem_fixed_iff' ρ K v).1 hv))

def hkW (ρ : Representation ℂ Γ V) (K : Subgroup Γ) (f : Γ → ℂ)
    (hfin : (Function.support fun q : Γ ⧸ K => f q.out).Finite)
    (hbi : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) : Module.End ℂ (GlobalTheory.PRep.fixed ρ K) :=
  (∑ q ∈ hfin.toFinset, f q.out • ρ q.out).restrict (hk_mapsTo ρ K f hfin hbi)

theorem hkW_apply (ρ : Representation ℂ Γ V) (K : Subgroup Γ) (f : Γ → ℂ)
    (hfin : (Function.support fun q : Γ ⧸ K => f q.out).Finite)
    (hbi : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) (v : GlobalTheory.PRep.fixed ρ K) :
    ((hkW ρ K f hfin hbi v : GlobalTheory.PRep.fixed ρ K) : V) = ∑ᶠ q : Γ ⧸ K, f q.out • ρ q.out (v : V) := by
  rw [← hk_apply_sum ρ K f hfin]
  rfl

variable [TopologicalSpace Γ]

theorem iter_push {X : Type} [AddCommGroup X] [Module ℂ X]
    (R : Representation ℂ Γ X) (S : Submodule ℂ X) (ρ : Representation ℂ Γ V) (Lj : X →ₗ[ℂ] V)
    (hS : ∀ g, ∀ x ∈ S, R g x ∈ S) (hL : ∀ g, ∀ x ∈ S, SmVec R x → Lj (R g x) = ρ g (Lj x))
    (I : Subgroup Γ) (hI : IsOpen (I : Set Γ)) (f : Γ → ℂ)
    (hfin : (Function.support fun q : Γ ⧸ I => f q.out).Finite)
    (hbi : ∀ k ∈ I, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) (κ : ℂ) (A : X → X)
    (hA : ∀ F, (∀ k ∈ I, R k F = F) → A F = κ • ∑ᶠ q : Γ ⧸ I, f q.out • R q.out F)
    (G : X) (hGS : G ∈ S) (hGI : ∀ k ∈ I, R k G = G) : ∀ r : ℕ,
    A^[r] G ∈ S ∧ (∀ k ∈ I, R k (A^[r] G) = A^[r] G) ∧
      Lj (A^[r] G) = (fun v => κ • ∑ᶠ q : Γ ⧸ I, f q.out • ρ q.out v)^[r] (Lj G) := by
  intro r
  induction r with
  | zero => exact ⟨hGS, hGI, rfl⟩
  | succ r ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hsm : SmVec R (A^[r] G) := ⟨I, hI, (mem_fixed_iff' R I _).2 h2⟩
    have hfix := GlobalTheory.T.hecke_sum_invariant Γ X R I f hfin hbi (A^[r] G) h2
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hA _ h2, ← h3]
    refine ⟨?_, ?_, ?_⟩
    · apply S.smul_mem
      rw [hsum_eq R I f hfin.coe_toFinset.ge]
      exact S.sum_mem fun q _ => S.smul_mem _ (hS _ _ h1)
    · intro k hk
      rw [map_smul, hfix k hk]
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, hsum_eq R I f hfin.coe_toFinset.ge, hsum_eq ρ I f hfin.coe_toFinset.ge, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [map_smul, hL _ _ h1 hsm]

end Gen

theorem dcos_inv {E : Type} [Field E] [NumberField E] [IsCMField E] (N : ℕ) (w : Pl E) (t : GLw N w) :
    ∀ k ∈ iwGL N w, ∀ g, dcos N w t (k * g) = dcos N w t g ∧ dcos N w t (g * k) = dcos N w t g := by
  intro k hk g
  have e1 : (∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, k * g = x * t * z) ↔
      ∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, g = x * t * z := by
    constructor
    · rintro ⟨x, hx, z, hz, e⟩
      refine ⟨k⁻¹ * x, mul_mem (inv_mem hk) hx, z, hz, ?_⟩
      rw [show g = k⁻¹ * (k * g) by group, e]
      group
    · rintro ⟨x, hx, z, hz, e⟩
      exact ⟨k * x, mul_mem hk hx, z, hz, by rw [e]; group⟩
  have e2 : (∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, g * k = x * t * z) ↔
      ∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, g = x * t * z := by
    constructor
    · rintro ⟨x, hx, z, hz, e⟩
      refine ⟨x, hx, z * k⁻¹, mul_mem hz (inv_mem hk), ?_⟩
      rw [show g = g * k * k⁻¹ by group, e]
      group
    · rintro ⟨x, hx, z, hz, e⟩
      exact ⟨x, hx, z * k, mul_mem hz hk, by rw [e]; group⟩
  unfold dcos
  constructor
  · by_cases h : ∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, g = x * t * z
    · rw [if_pos (e1.2 h), if_pos h]
    · rw [if_neg (fun h' => h (e1.1 h')), if_neg h]
  · by_cases h : ∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, g = x * t * z
    · rw [if_pos (e2.2 h), if_pos h]
    · rw [if_neg (fun h' => h (e2.1 h')), if_neg h]

theorem gap_anti {N : ℕ} {x : Fin N → ℤ} (h : Gap x) : Antitone x := by
  intro i j hij
  rcases hij.lt_or_eq with hlt | rfl
  · have := h i j hlt
    omega
  · exact le_rfl

theorem gap_add {N : ℕ} {x x' : Fin N → ℤ} (h : Gap x) (h' : Gap x') : Gap (x + x') := by
  intro i j hij
  have := h i j hij
  have := h' i j hij
  simp only [Pi.add_apply]
  omega

section Place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem pair_double_coset_finite_support (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (x : Fin a → ℤ) (y : Fin b → ℤ) :
    (Function.support fun q : (GLw a w × GLw b w) ⧸ I2 a b w => dc2 w ϖ x y q.out).Finite :=
  GlobalTheory.T.finite_support_product_quotient _ _ _ _ _ _ (GlobalTheory.T.iwahori_double_coset_finite E w a _).1 (GlobalTheory.T.iwahori_double_coset_finite E w b _).1
    (fun k hk g => (dcos_inv a w _ k hk g).2) (fun k hk g => (dcos_inv b w _ k hk g).2)

theorem pair_double_coset_bi_invariant (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (x : Fin a → ℤ) (y : Fin b → ℤ) :
    ∀ k ∈ I2 a b w, ∀ g, dc2 w ϖ x y (k * g) = dc2 w ϖ x y g ∧ dc2 w ϖ x y (g * k) = dc2 w ϖ x y g := by
  intro k hk g
  obtain ⟨hk1, hk2⟩ := Subgroup.mem_prod.1 hk
  simp only [dc2, Prod.fst_mul, Prod.snd_mul, (dcos_inv a w (tdiag ϖ x) k.1 hk1 g.1).1,
    (dcos_inv a w (tdiag ϖ x) k.1 hk1 g.1).2, (dcos_inv b w (tdiag ϖ y) k.2 hk2 g.2).1,
    (dcos_inv b w (tdiag ϖ y) k.2 hk2 g.2).2, and_self]

theorem qh_ne (w : Pl E) : qh w ≠ 0 := by
  unfold qh
  have : (0 : ℝ) < (qV E w : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w)
  exact_mod_cast (Real.sqrt_pos.2 this).ne'

theorem core (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (hϖ : ordL (ϖ : w.adicCompletion E) = 1)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLw a w × GLw b w) V)
    [FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ (I2 a b w))]
    (J : Type) [Fintype J] (c : J → ℂ) (x : J → Fin a → ℤ) (y : J → Fin b → ℤ)
    (hgap : ∀ j, Gap (x j) ∧ Gap (y j)) (m : ℕ)
    (hm : Module.finrank ℂ (GlobalTheory.PRep.fixed ρ (I2 a b w)) ≤ m) (κ : ℂ) (u : GLw a w × GLw b w → ℂ)
    (hu : u = fun g => ∑ j, c j * dc2 w ϖ (x j) (y j) g) (v0 : V)
    (hv0 : v0 ∈ GlobalTheory.PRep.fixed ρ (I2 a b w))
    (hne : (fun v => κ • ∑ᶠ q : (GLw a w × GLw b w) ⧸ I2 a b w, u q.out • ρ q.out v)^[m] v0 ≠ 0) :
    ∃ (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ), (∃ v ∈ GlobalTheory.PRep.fixed ρ (I2 a b w), v ≠ 0 ∧
      ∀ x y, Gap x → Gap y → hkG ρ (I2 a b w) (dc2 w ϖ x y) v = ev2 w ξa ξb x y • v) ∧
      ∑ j, c j * ev2 w ξa ξb (x j) (y j) ≠ 0 := by
  have hIa := GlobalTheory.T.iwahori_double_coset_finite E w a
  have hIb := GlobalTheory.T.iwahori_double_coset_finite E w b
  have hmul : ∀ (x x' : Fin a → ℤ) (y y' : Fin b → ℤ), Gap x → Gap x' → Gap y → Gap y' →
      hkW ρ (I2 a b w) (dc2 w ϖ (x + x') (y + y')) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _) =
        hkW ρ (I2 a b w) (dc2 w ϖ x y) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _) *
          hkW ρ (I2 a b w) (dc2 w ϖ x' y') (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _) := by
    intro x x' y y' hx hx' hy hy'
    ext v
    rw [Module.End.mul_apply, hkW_apply, hkW_apply, hkW_apply]
    exact GlobalTheory.T.finite_support_convolution_triple _ _ _ ρ (iwGL a w) (iwGL b w) (dcos a w (tdiag ϖ x)) (dcos a w (tdiag ϖ x'))
      (dcos a w (tdiag ϖ (x + x'))) (dcos b w (tdiag ϖ y)) (dcos b w (tdiag ϖ y'))
      (dcos b w (tdiag ϖ (y + y')))
      (fun f hf => by rcases hf with rfl | rfl | rfl <;> exact ⟨(hIa _).1, dcos_inv a w _⟩)
      (fun f hf => by rcases hf with rfl | rfl | rfl <;> exact ⟨(hIb _).1, dcos_inv b w _⟩)
      (fun v hv => GlobalTheory.T.iwahori_hecke_sum_additive E w a ϖ hϖ x x' (gap_anti hx) (gap_anti hx') _
        (ρ.comp (MonoidHom.inl _ _)) v hv)
      (fun v hv => GlobalTheory.T.iwahori_hecke_sum_additive E w b ϖ hϖ y y' (gap_anti hy) (gap_anti hy') _
        (ρ.comp (MonoidHom.inr _ _)) v hv)
      v ((mem_fixed_iff' _ _ _).1 v.2)
  have hcomm : ∀ i i' : {p : (Fin a → ℤ) × (Fin b → ℤ) // Gap p.1 ∧ Gap p.2},
      Commute (hkW ρ (I2 a b w) (dc2 w ϖ i.1.1 i.1.2) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _))
        (hkW ρ (I2 a b w) (dc2 w ϖ i'.1.1 i'.1.2) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _)) := by
    intro i i'
    unfold Commute SemiconjBy
    rw [← hmul _ _ _ _ i.2.1 i'.2.1 i.2.2 i'.2.2, ← hmul _ _ _ _ i'.2.1 i.2.1 i'.2.2 i.2.2,
      add_comm i.1.1 i'.1.1, add_comm i.1.2 i'.1.2]
  have hT : ∀ v : GlobalTheory.PRep.fixed ρ (I2 a b w),
      ∑ᶠ q : (GLw a w × GLw b w) ⧸ I2 a b w, u q.out • ρ q.out (v : V) =
        (((∑ j, c j • hkW ρ (I2 a b w) (dc2 w ϖ (x j) (y j)) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _)) v :
          GlobalTheory.PRep.fixed ρ (I2 a b w)) : V) := by
    intro v
    rw [LinearMap.sum_apply, Submodule.coe_sum]
    simp only [LinearMap.smul_apply, Submodule.coe_smul, hkW_apply, hu]
    exact GlobalTheory.CompanionTheory.HeckeSum.finsum_coset_smul_linear _ _ ρ (I2 a b w) J c (fun j => dc2 w ϖ (x j) (y j))
      (fun j => pair_double_coset_finite_support w ϖ _ _) v
  have hiter : ∀ (r : ℕ) (v : V) (hv : v ∈ GlobalTheory.PRep.fixed ρ (I2 a b w)),
      (fun v => κ • ∑ᶠ q : (GLw a w × GLw b w) ⧸ I2 a b w, u q.out • ρ q.out v)^[r] v =
        ((((κ • ∑ j, c j • hkW ρ (I2 a b w) (dc2 w ϖ (x j) (y j)) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _)) ^ r)
          ⟨v, hv⟩ : GlobalTheory.PRep.fixed ρ (I2 a b w)) : V) := by
    intro r
    induction r with
    | zero => intro v hv; rfl
    | succ r ih =>
      intro v hv
      rw [Function.iterate_succ_apply', ih v hv, hT, pow_succ', Module.End.mul_apply, LinearMap.smul_apply,
        Submodule.coe_smul]
  have hTm : ((∑ j, c j • hkW ρ (I2 a b w) (dc2 w ϖ (x j) (y j)) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _)) ^ m)
      ⟨v0, hv0⟩ ≠ 0 := by
    intro h0
    apply hne
    rw [hiter m _ hv0, smul_pow, LinearMap.smul_apply, h0, smul_zero, Submodule.coe_zero]
  obtain ⟨v₀, hv₀, χ, hχ, hsum⟩ := GlobalTheory.T.exists_joint_eigenvector_nonzero (GlobalTheory.PRep.fixed ρ (I2 a b w))
    {p : (Fin a → ℤ) × (Fin b → ℤ) // Gap p.1 ∧ Gap p.2} J
    (fun p => hkW ρ (I2 a b w) (dc2 w ϖ p.1.1 p.1.2) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _)) hcomm c
    (fun j => ⟨(x j, y j), hgap j⟩) ⟨v0, hv0⟩ m hm hTm
  have hχ2 : ∀ (x : Fin a → ℤ) (y : Fin b → ℤ) (h : Gap x ∧ Gap y),
      hkW ρ (I2 a b w) (dc2 w ϖ x y) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _) v₀ = χ ⟨(x, y), h⟩ • v₀ :=
    fun x y h => hχ ⟨(x, y), h⟩
  obtain ⟨χ', hχ'⟩ : ∃ χ' : (Fin a → ℤ) → (Fin b → ℤ) → ℂ,
      χ' = fun x y => if h : Gap x ∧ Gap y then χ ⟨(x, y), h⟩ else 0 := ⟨_, rfl⟩
  have hχ'mul : ∀ x x' y y', Gap x → Gap x' → Gap y → Gap y' →
      χ' (x + x') (y + y') = χ' x y * χ' x' y' := by
    intro x x' y y' hx hx' hy hy'
    have e := congrArg (fun T => T v₀) (hmul x x' y y' hx hx' hy hy')
    simp only [Module.End.mul_apply] at e
    rw [hχ2 _ _ ⟨gap_add hx hx', gap_add hy hy'⟩, hχ2 x' y' ⟨hx', hy'⟩, map_smul, hχ2 x y ⟨hx, hy⟩,
      smul_smul] at e
    have e2 := smul_left_injective ℂ hv₀ e
    simp only [hχ']
    rw [dite_eq_left ⟨gap_add hx hx', gap_add hy hy'⟩, dite_eq_left ⟨hx, hy⟩, dite_eq_left ⟨hx', hy'⟩]
    rw [e2, mul_comm]
  obtain ⟨j0, -, hj0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hex : ∃ x y, Gap x ∧ Gap y ∧ χ' x y ≠ 0 := by
    refine ⟨x j0, y j0, (hgap j0).1, (hgap j0).2, ?_⟩
    simp only [hχ']
    rw [dite_eq_left (hgap j0)]
    exact right_ne_zero_of_mul hj0
  obtain ⟨ξa, ξb, hξ⟩ := GlobalTheory.T.multiplicative_character_on_cone a b (qh w) (qh_ne w) χ' hχ'mul hex
  have hev : ∀ x y (h : Gap x ∧ Gap y), ev2 w ξa ξb x y = χ ⟨(x, y), h⟩ := by
    intro x y h
    have := hξ x y h.1 h.2
    simp only [hχ'] at this
    rw [dite_eq_left h] at this
    exact this.symm
  refine ⟨ξa, ξb, ⟨(v₀ : V), v₀.2, by simpa using hv₀, fun x y hx hy => ?_⟩, ?_⟩
  · have e1 : hkG ρ (I2 a b w) (dc2 w ϖ x y) (v₀ : V) =
        ((hkW ρ (I2 a b w) (dc2 w ϖ x y) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _) v₀ :
          GlobalTheory.PRep.fixed ρ (I2 a b w)) : V) :=
      (hkW_apply _ _ _ _ _ _).symm
    rw [e1, hχ2 x y ⟨hx, hy⟩, Submodule.coe_smul, hev x y ⟨hx, hy⟩]
  · simp only [hev _ _ (hgap _)]
    exact hsum

end Place

set_option maxHeartbeats 1600000 in
theorem rReadT : RReadT := by
  intro hRM E _ _ _ n a b μ s₁ s₂ Pa Pb D hC w ϖ J _ c x y m G hϖ hgap hm hGS hGI hne
  obtain ⟨hinv, J', L, hLeq, hLsep⟩ := hRM E a b s₁ s₂ Pa Pb w hC.g₁ hC.g₂ hC.u₁ hC.u₂ hC.t₁ hC.t₂
  have hIa := GlobalTheory.T.iwahori_double_coset_finite E w a
  have hIb := GlobalTheory.T.iwahori_double_coset_finite E w b
  have hIopen : IsOpen ((I2 a b w : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (hIa 1).2.1.prod (hIb 1).2.1
  have hK : I2 a b w ≤ K2 a b w := Subgroup.prod_mono (hIa 1).2.2.2.1 (hIb 1).2.2.2.1
  have hidx : (I2 a b w).relIndex (K2 a b w) ≠ 0 :=
    GlobalTheory.T.prod_rel_index_ne_zero _ _ _ _ _ _ (hIa 1).2.2.2.2 (hIb 1).2.2.2.2
  obtain ⟨u, hu⟩ : ∃ u : GLw a w × GLw b w → ℂ, u = fun g => ∑ j, c j * dc2 w ϖ (x j) (y j) g := ⟨_, rfl⟩
  rw [← hu] at hne
  have hufin : (Function.support fun q : (GLw a w × GLw b w) ⧸ I2 a b w => u q.out).Finite := by
    refine (Set.finite_iUnion fun j => pair_double_coset_finite_support w ϖ (x j) (y j)).subset ?_
    intro q hq
    by_contra hcon
    apply hq
    simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hcon
    simp [hu, hcon]
  have hubi : ∀ k ∈ I2 a b w, ∀ g, u (k * g) = u g ∧ u (g * k) = u g := by
    intro k hk g
    simp only [hu, (pair_double_coset_bi_invariant w ϖ _ _ k hk g).1, (pair_double_coset_bi_invariant w ϖ _ _ k hk g).2, and_self]
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂ, κ = (((I2 a b w).relIndex (K2 a b w) : ℕ) : ℂ)⁻¹ := ⟨_, rfl⟩
  have hact : ∀ F : H E a b → ℂ, (∀ k ∈ I2 a b w, pairRt a b w k F = F) →
      actP w u F = κ • ∑ᶠ q : (GLw a w × GLw b w) ⧸ I2 a b w, u q.out • pairRt a b w q.out F := by
    intro F hF
    funext z
    have hr : ∀ l ∈ I2 a b w, ∀ g : GLw a w × GLw b w,
        (fun m => u m * pairRt a b w m F z) (g * l) = (fun m => u m * pairRt a b w m F z) g := by
      intro l hl g
      show u (g * l) * pairRt a b w (g * l) F z = u g * pairRt a b w g F z
      rw [(hubi l hl g).2, map_mul, Module.End.mul_apply, hF l hl]
    have hsub : (Function.support fun q : (GLw a w × GLw b w) ⧸ I2 a b w =>
        u q.out * pairRt a b w q.out F z) ⊆ hufin.toFinset := by
      intro q hq
      rw [Set.Finite.coe_toFinset]
      intro h0
      apply hq
      simp [h0]
    show hint (K2 a b w) (fun m => u m * pairRt a b w m F z) = _
    rw [GlobalTheory.T.hecke_integral_finite_sum _ (K2 a b w) (I2 a b w) (fun m => u m * pairRt a b w m F z) hK hidx hr, ← hκ,
      finsum_eq_sum_of_support_subset _ hsub, hsum_eq (pairRt a b w) (I2 a b w) u hufin.coe_toFinset.ge F]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hGI' : ∀ k ∈ I2 a b w, pairRt a b w k G = G := (mem_fixed_iff' _ _ _).1 hGI
  obtain ⟨hmS, hmI, -⟩ := iter_push (pairRt a b w) (pairSpace s₁.space s₂.space) (pairAt Pa Pb w) 0 hinv
    (fun _ _ _ _ => by simp) (I2 a b w) hIopen u hufin hubi κ (actP w u) hact G hGS hGI' m
  obtain ⟨j', hj'⟩ : ∃ j', L j' ((actP w u)^[m] G) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (hLsep _ hmS ⟨I2 a b w, hIopen, (mem_fixed_iff' _ _ _).2 hmI⟩ hcon)
  obtain ⟨-, -, hLm⟩ := iter_push (pairRt a b w) (pairSpace s₁.space s₂.space) (pairAt Pa Pb w) (L j') hinv
    (hLeq j') (I2 a b w) hIopen u hufin hubi κ (actP w u) hact G hGS hGI' m
  have hsmG : SmVec (pairRt a b w) G := ⟨I2 a b w, hIopen, hGI⟩
  have hv0 : L j' G ∈ GlobalTheory.PRep.fixed (pairAt Pa Pb w) (I2 a b w) :=
    (mem_fixed_iff' _ _ _).2 fun k hk => (hLeq j' k G hGS hsmG).symm.trans (congrArg (L j') (hGI' k hk))
  haveI hfd : FiniteDimensional ℂ (GlobalTheory.PRep.fixed (pairAt Pa Pb w) (I2 a b w)) :=
    GlobalTheory.T.finiteDimensional_fixed_tensor _ _ _ _ (lp Pa w) (lp Pb w) (iwGL a w) (iwGL b w)
      ((GlobalTheory.T.admissible_parabolic_induction (w.adicCompletion E) _ Pa.h (fun i => Pa.σ i w)).2 _ (hIa 1).2.1 (hIa 1).2.2.1)
      ((GlobalTheory.T.admissible_parabolic_induction (w.adicCompletion E) _ Pb.h (fun i => Pb.σ i w)).2 _ (hIb 1).2.1 (hIb 1).2.2.1)
  exact core w ϖ hϖ (pairAt Pa Pb w) J c x y hgap m hm κ u hu (L j' G) hv0 fun h => hj' (hLm.trans h)

end PositivityTheory.Rg.BcB.F.Tail

end
