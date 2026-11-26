module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyOfFinitePresentationOfCancel
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleQuadraticExistsUnitEqMulSg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.SchwartzDecay

open NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem continuous_mixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem norm_le_mixed (x : InfiniteAdeleRing F) (v : InfinitePlace F) :
    ‖x v‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := by
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  rcases v.isReal_or_isComplex with hv | hv
  · calc ‖x v‖ = ‖(e x).1 ⟨v, hv⟩‖ :=
          ((isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) (x v)).symm
      _ ≤ ‖e x‖ := (norm_le_pi_norm (e x).1 ⟨v, hv⟩).trans (norm_fst_le (e x))
  · calc ‖x v‖ = ‖(e x).2 ⟨v, hv⟩‖ :=
          ((isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) (x v)).symm
      _ ≤ ‖e x‖ := (norm_le_pi_norm (e x).2 ⟨v, hv⟩).trans (norm_snd_le (e x))

theorem abs_re_le (x : Ainf F) (v : InfinitePlace F) :
    |re x v| ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [(isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) (x v)]
  exact norm_le_mixed x v

theorem sz_nonneg (u : Fin N → AF F) : 0 ≤ sz u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem sz_le (u : Fin N → AF F) :
    sz u ≤ (N * Fintype.card (InfinitePlace F) : ℝ) *
      ‖fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (u i).1‖ := by
  set t : Fin N → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (u i).1
  calc sz u ≤ ∑ _l : Fin N, ∑ _w : InfinitePlace F, ‖t‖ :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun w _ =>
          (abs_re_le (inf u l) w).trans (norm_le_pi_norm t l)
    _ = _ := by simp [mul_assoc]

theorem decay_add {Φ Ψ : (Fin N → AF F) → ℂ} (h : Decay Φ) (h' : Decay Ψ) : Decay (Φ + Ψ) := by
  obtain ⟨hc, ⟨K, hK, hK0⟩, hd⟩ := h
  obtain ⟨hc', ⟨K', hK', hK0'⟩, hd'⟩ := h'
  refine ⟨hc.add hc', ⟨K ∪ K', hK.union hK', fun u hu => ?_⟩, fun k => ?_⟩
  · rw [Set.mem_union, not_or] at hu
    simp [hK0 u hu.1, hK0' u hu.2]
  · obtain ⟨C, hC⟩ := hd k
    obtain ⟨C', hC'⟩ := hd' k
    refine ⟨C + C', fun u => ?_⟩
    have h0 : 0 ≤ (1 + sz u) ^ k := pow_nonneg (by linarith [sz_nonneg u]) k
    calc ‖(Φ + Ψ) u‖ * (1 + sz u) ^ k ≤ (‖Φ u‖ + ‖Ψ u‖) * (1 + sz u) ^ k :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) h0
      _ ≤ C + C' := by rw [add_mul]; exact add_le_add (hC u) (hC' u)

theorem decay_smul (a : ℂ) {Φ : (Fin N → AF F) → ℂ} (h : Decay Φ) : Decay (a • Φ) := by
  obtain ⟨hc, ⟨K, hK, hK0⟩, hd⟩ := h
  refine ⟨hc.const_smul a, ⟨K, hK, fun u hu => by simp [hK0 u hu]⟩, fun k => ?_⟩
  obtain ⟨C, hC⟩ := hd k
  refine ⟨‖a‖ * C, fun u => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC u) (norm_nonneg a)

theorem schwartz_bound {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ t, (1 + ‖t‖) ^ k * ‖f t‖ ≤ C := by
  have := fun t => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl f t
  simp only [norm_iteratedFDeriv_zero] at this
  exact ⟨_, this⟩

theorem decay_pure (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → Af F) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin N → Af F)) : Decay (GlobalTheory.WeilM.pureA F f g) := by
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ⟨tsupport g, hg2, fun u hu => ?_⟩, fun k => ?_⟩
  · refine Continuous.mul (f.continuous.comp (continuous_pi fun i => ?_))
      (hg1.continuous.comp (continuous_pi fun i => ?_))
    · exact continuous_mixed.comp (continuous_fst.comp (continuous_apply i))
    · exact continuous_snd.comp (continuous_apply i)
  · exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hu)
  · obtain ⟨B, hB⟩ := hg1.continuous.bounded_above_of_compact_support hg2
    obtain ⟨C, hC⟩ := schwartz_bound f k
    set c : ℝ := N * Fintype.card (InfinitePlace F)
    have hc : 0 ≤ c := by positivity
    refine ⟨(1 + c) ^ k * C * B, fun u => ?_⟩
    set t : Fin N → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (u i).1
    have h1 : 1 + sz u ≤ (1 + c) * (1 + ‖t‖) := by
      have : sz u ≤ c * ‖t‖ := sz_le u
      nlinarith [norm_nonneg t]
    have h2 : (1 + sz u) ^ k ≤ (1 + c) ^ k * (1 + ‖t‖) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith [sz_nonneg u]) h1 k
    have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
    calc ‖GlobalTheory.WeilM.pureA F f g u‖ * (1 + sz u) ^ k
        = ‖f t‖ * ‖g fun i => (u i).2‖ * (1 + sz u) ^ k := by rw [← norm_mul]; rfl
      _ ≤ ‖f t‖ * ‖g fun i => (u i).2‖ * ((1 + c) ^ k * (1 + ‖t‖) ^ k) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (1 + c) ^ k * ((1 + ‖t‖) ^ k * ‖f t‖) * ‖g fun i => (u i).2‖ := by ring
      _ ≤ (1 + c) ^ k * C * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hC t) (by positivity)) (hB _) (norm_nonneg _) (by positivity)

theorem decay_of_mem_schA (F : Type) [Field F] [NumberField F] (N : ℕ) :
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), Decay Φ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    exact decay_pure f g hg
  | zero => exact decay_zero
  | add x y _ _ hx hy => exact decay_add hx hy
  | smul a x _ hx => exact decay_smul a hx

end GlobalTheory.SchwartzDecay
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpaceStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), Decay Φ := by
  first | exact @GlobalTheory.SchwartzDecay.decay_of_mem_schA | exact GlobalTheory.SchwartzDecay.decay_of_mem_schA | (intros; apply GlobalTheory.SchwartzDecay.decay_of_mem_schA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslations
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.TranslQuotient

theorem finiteSubsets_preimage {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (hL : L.IsLB)
    (hamp : Out.RelAmple A L) (U : S.Opens) (hU : IsAffineOpen U) :
    FiniteSubsetsInAffineOpens (A.hom ⁻¹ᵁ U) := by
  have h := GlobalTheory.isAmpleLB_of_relAmple A hL hamp U hU
  exact ⟨fun s hs => by
    obtain ⟨n, -, t, h1, -, h2⟩ := h.exists_affine_finite_subset hs (U := ⊤) (Set.subset_univ _)
    exact ⟨_, h2, h1⟩⟩

theorem transl_mul {S : Scheme.{0}} {A : Over S} [GrpObj A] (a c : 𝟙_ (Over S) ⟶ A) :
    Hecke.transl (a * c) = Hecke.transl a ≫ Hecke.transl c := by
  simp only [Hecke.transl, comp_mul, Category.id_comp, Category.comp_id]
  rw [← Category.assoc, toUnit_unique (_ ≫ toUnit A) (toUnit A)]
  exact (mul_assoc _ _ _).symm

theorem transl_one {S : Scheme.{0}} {A : Over S} [GrpObj A] :
    Hecke.transl (1 : 𝟙_ (Over S) ⟶ A) = 𝟙 A := by
  simp [Hecke.transl]

theorem isAbelianScheme_of_finite_etale {S : Scheme.{0}} (A Q : Over S) [GrpObj A] [GrpObj Q]
    (q : A ⟶ Q) (hA : IsAbelianScheme A) (hQ : IsCommMonObj Q) (hfin : IsFinite q.left)
    (het : Etale q.left) (hsurj : Surjective q.left) : IsAbelianScheme Q := by
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hw : q.left ≫ Q.hom = A.hom := Over.w q
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom
    hA.smooth hA.geomConnected
  have : Flat (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : IsSeparated (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyReduced (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyConnected (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : LocallyOfFinitePresentation (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have := GlobalTheory.flat_of_comp_of_flat_of_surjective q.left Q.hom
  have := UniversallyClosed.of_comp_surjective q.left Q.hom
  have := GlobalTheory.NilProper.isSeparated_of_comp_surjective q.left Q.hom
  have := GlobalTheory.AbelianQuotient.geometricallyReduced_of_comp q.left Q.hom
  have : LocallyOfFinitePresentation Q.hom :=
    GlobalTheory.T.locallyOfFinitePresentation_of_cancel q.left Q.hom hfin inferInstance inferInstance hsurj inferInstance
  exact ⟨hQ, GlobalTheory.AbelianQuotient.smooth_of_grpObj_of_flat Q, ⟨⟩,
    GlobalTheory.AbelianQuotient.geometricallyConnected_of_comp q.left Q.hom⟩


open GlobalTheory.AbelianQuotient in
theorem grp_descent : ∀ (S : Scheme.{0}) (A Q : Over S) [GrpObj A] [IsCommMonObj A] (q : A ⟶ Q),
    Flat q.left → Surjective q.left → QuasiCompact q.left →
    (∀ (W : Over S) (a b c d : W ⟶ A), a ≫ q = b ≫ q → c ≫ q = d ≫ q → (a * c) ≫ q = (b * d) ≫ q) →
    ∃ _ : GrpObj Q, IsCommMonObj Q ∧ IsMonHom q := by
  intro S A Q _ _ q _ _ _ hq
  have hinv : ∀ {W : Over S} (a b : W ⟶ A), a ≫ q = b ≫ q → a⁻¹ ≫ q = b⁻¹ ≫ q := by
    intro W a b h
    have h1 : (a⁻¹ * a) ≫ q = (a⁻¹ * b) ≫ q := hq W _ _ _ _ rfl h
    have h2 := hq W b⁻¹ b⁻¹ (a⁻¹ * b) (a⁻¹ * a) rfl h1.symm
    have e1 : b⁻¹ * (a⁻¹ * b) = a⁻¹ := by rw [mul_left_comm, inv_mul_cancel, _root_.mul_one]
    have e2 : b⁻¹ * (a⁻¹ * a) = b⁻¹ := by rw [inv_mul_cancel, _root_.mul_one]
    rwa [e1, e2] at h2
  have hμ : ∀ {W : Over S} (x : W ⟶ A ⊗ A), x ≫ μ[A] = (x ≫ fst A A) * (x ≫ snd A A) := by
    intro W x
    rw [Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]
  have := flat_tensorHom q q
  have := surjective_tensorHom q q
  have := quasiCompact_tensorHom q q
  have := FlatQuotient.epi_of_flat_surjective q
  have := FlatQuotient.epi_tensorHom q q
  have := FlatQuotient.epi_tensorHom (q ⊗ₘ q) q
  obtain ⟨m, hm⟩ := exists_desc (q ⊗ₘ q) (μ[A] ≫ q) (by
    intro W a b h
    have h1 : (a ≫ fst A A) ≫ q = (b ≫ fst A A) ≫ q := by simpa using h =≫ fst Q Q
    have h2 : (a ≫ snd A A) ≫ q = (b ≫ snd A A) ≫ q := by simpa using h =≫ snd Q Q
    rw [← Category.assoc, ← Category.assoc, hμ a, hμ b]
    exact hq W _ _ _ _ h1 h2)
  obtain ⟨n, hn⟩ := exists_desc q (GrpObj.inv ≫ q) (by
    intro W a b h
    rw [← Category.assoc, ← Category.assoc, ← Hom.inv_def, ← Hom.inv_def]
    exact hinv a b h)
  have key : ∀ {W : Over S} (a b : W ⟶ A), lift (a ≫ q) (b ≫ q) ≫ m = (a * b) ≫ q := by
    intro W a b
    rw [← lift_map, Category.assoc, hm, Hom.mul_def, Category.assoc]
  letI : MonObj Q :=
    { one := η[A] ≫ q
      mul := m
      one_mul := by
        rw [← cancel_epi (λ_ Q).inv, ← cancel_epi q]
        have := key (1 : A ⟶ A) (𝟙 A)
        rw [_root_.one_mul] at this
        rw [Iso.inv_hom_id, Category.comp_id]
        refine Eq.trans ?_ (this.trans (Category.id_comp _))
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext <;> simp [Hom.one_def]
      mul_one := by
        rw [← cancel_epi (ρ_ Q).inv, ← cancel_epi q]
        have := key (𝟙 A) (1 : A ⟶ A)
        rw [_root_.mul_one] at this
        rw [Iso.inv_hom_id, Category.comp_id]
        refine Eq.trans ?_ (this.trans (Category.id_comp _))
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext <;> simp [Hom.one_def]
      mul_assoc := by
        rw [← cancel_epi ((q ⊗ₘ q) ⊗ₘ q)]
        have h1 : ((q ⊗ₘ q) ⊗ₘ q) ≫ m ▷ Q = (μ[A] ▷ A) ≫ (q ⊗ₘ q) := by
          rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
            hm, Category.comp_id, Category.id_comp]
        have h2 : ((q ⊗ₘ q) ⊗ₘ q) ≫ (α_ Q Q Q).hom ≫ Q ◁ m =
            (α_ A A A).hom ≫ (A ◁ μ[A]) ≫ (q ⊗ₘ q) := by
          rw [associator_naturality_assoc]
          congr 1
          ext <;> simp [hm]
        rw [reassoc_of% h1, reassoc_of% h2, hm, MonObj.mul_assoc_assoc] }
  have hhom : IsMonHom q := ⟨rfl, hm.symm⟩
  letI : GrpObj Q :=
    { inv := n
      left_inv := by
        rw [← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]
        have := key GrpObj.inv (𝟙 A)
        rw [Category.id_comp] at this
        refine this.trans ?_
        rw [Hom.mul_def, GrpObj.left_inv, comp_toUnit_assoc, Category.assoc]
        rfl
      right_inv := by
        rw [← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]
        have := key (𝟙 A) GrpObj.inv
        rw [Category.id_comp] at this
        refine this.trans ?_
        rw [Hom.mul_def, GrpObj.right_inv, comp_toUnit_assoc, Category.assoc]
        rfl }
  refine ⟨inferInstance, ⟨?_⟩, hhom⟩
  rw [← cancel_epi (q ⊗ₘ q), BraidedCategory.braiding_naturality_assoc, ← IsMonHom.mul_hom,
    IsCommMonObj.mul_comm_assoc]

theorem comp_transl {S : Scheme.{0}} {A W : Over S} [GrpObj A] (x : W ⟶ A) (h : 𝟙_ (Over S) ⟶ A) :
    x ≫ Hecke.transl h = x * (toUnit _ ≫ h) := by
  rw [Hecke.transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit A) (toUnit _)]

theorem transl_compat : ∀ (S : Scheme.{0}) (A Q : Over S) [GrpObj A] [IsCommMonObj A]
    (H : Subgroup (𝟙_ (Over S) ⟶ A)) (q : A ⟶ Q),
    GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) q.left →
    ∀ (W : Over S) (a b c d : W ⟶ A), a ≫ q = b ≫ q → c ≫ q = d ≫ q → (a * c) ≫ q = (b * d) ≫ q := by
  intro S A Q _ _ H q hc W a b c d hab hcd
  have loc := (GlobalTheory.ZM.galoisCover_descent _ _ _ _ _ hc).2.1
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun p ↦ ?_
  obtain ⟨V₁, h, hp₁, e₁⟩ := loc W.left a.left b.left (congrArg CommaMorphism.left hab) p
  obtain ⟨V₂, k, hp₂, e₂⟩ := loc W.left c.left d.left (congrArg CommaMorphism.left hcd) p
  refine ⟨V₁ ⊓ V₂, ⟨hp₁, hp₂⟩, ?_⟩
  let jV : Over.mk ((V₁ ⊓ V₂).ι ≫ W.hom) ⟶ W := Over.homMk (V₁ ⊓ V₂).ι rfl
  have f₁ : jV ≫ b = (jV ≫ a) * (toUnit _ ≫ h.1) := by
    rw [← comp_transl, Category.assoc]
    ext
    simp only [Over.comp_left, Over.homMk_left, jV]
    rw [← W.left.homOfLE_ι (inf_le_left : V₁ ⊓ V₂ ≤ V₁), ]
    simp only [Category.assoc, e₁]
  have f₂ : jV ≫ d = (jV ≫ c) * (toUnit _ ≫ k.1) := by
    rw [← comp_transl, Category.assoc]
    ext
    simp only [Over.comp_left, Over.homMk_left, jV]
    rw [← W.left.homOfLE_ι (inf_le_right : V₁ ⊓ V₂ ≤ V₂), ]
    simp only [Category.assoc, e₂]
  have hinv : Hecke.transl (h * k).1 ≫ q = q := Over.OverMorphism.ext (hc.inv (h * k))
  have key : jV ≫ (b * d) = jV ≫ (a * c) ≫ Hecke.transl (h * k).1 := by
    rw [comp_mul, f₁, f₂, ← Category.assoc, comp_transl, comp_mul, Subgroup.coe_mul, comp_mul,
      _root_.mul_mul_mul_comm]
  have key' : jV ≫ (a * c) ≫ q = jV ≫ (b * d) ≫ q := by
    rw [← Category.assoc jV (b * d), key, Category.assoc, Category.assoc, hinv]
  simpa [jV] using congrArg CommaMorphism.left key'

theorem exists_quotient : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (H : Subgroup (𝟙_ (Over S) ⟶ A)), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Finite H → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ A), h ∈ H → toUnit (Over.mk x) ≫ h = 1 → h = 1) → ∃ (A' : Over S) (_ : GrpObj A') (_ : IsCommMonObj A') (ψ : A ⟶ A'), IsAbelianScheme A' ∧ IsMonHom ψ ∧ GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left := by
  intro S A _ _ L H hA hL hamp hH hfree
  let ρ : H → (A.left ⟶ A.left) := fun h => (Hecke.transl h.1).left
  have h1 : ρ 1 = 𝟙 _ := by
    show (Hecke.transl (1 : 𝟙_ (Over S) ⟶ A)).left = _
    rw [transl_one]; rfl
  have hm : ∀ a c, ρ (a * c) = ρ a ≫ ρ c := fun a c => by
    show (Hecke.transl (a.1 * c.1)).left = _
    rw [transl_mul]; rfl
  have hS : ∀ a, ρ a ≫ A.hom = A.hom := fun a => Over.w _
  let τ := GlobalTheory.ZM.autOfRightAction ρ h1 hm
  have hτ : ∀ a, (τ a).asIso.hom ≫ A.hom = A.hom := fun a => hS a⁻¹
  have : OrbitsInAffineOpens τ := OrbitsInAffineOpens.of_locally_on_base τ A.hom hτ fun s => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hsU, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
    exact ⟨U, hsU, finiteSubsets_preimage A L hL hamp U hU⟩
  have hfreeρ : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Spec (.of k) ⟶ A.left) (a : H),
      y ≫ ρ a = y → a = 1 := by
    intro k _ _ y a hy
    let y' : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y rfl
    have e : y' ≫ Hecke.transl a.1 = y' := Over.OverMorphism.ext hy
    have e' : y' ≫ Hecke.transl a.1 = y' * (toUnit _ ≫ a.1) := by
      rw [Hecke.transl, comp_mul, Category.comp_id, ← Category.assoc,
        toUnit_unique (y' ≫ toUnit A) (toUnit _)]
    rw [e'] at e
    have h2 : toUnit (Over.mk (y ≫ A.hom)) ≫ a.1 = 1 := mul_eq_left.mp e
    exact Subtype.ext (hfree k (y ≫ A.hom) a.1 a.2 h2)
  have hf : IsFreeAction τ := .of_isAlgClosed fun k _ _ y a h ↦ inv_eq_one.mp (hfreeρ k y a⁻¹ h)
  obtain ⟨Y, π, hQ⟩ := (GlobalTheory.exists_isAffineQuotient_iff τ).mpr ‹OrbitsInAffineOpens τ›
  let ψ : A ⟶ Over.mk (hQ.desc A.hom hτ) :=
    Over.homMk π (hQ.comp_desc A.hom hτ)
  have hc : GlobalTheory.ZM.IsGaloisCover H ρ ψ.left := by
    refine ⟨hH, h1, hm, fun a ↦ ?_, hQ.isFinite_of_isFreeAction hf,
      hQ.etale_of_isFreeAction hf, hQ.surjective, fun k _ _ y y' e ↦ ?_⟩
    · have := hQ.comp_eq a⁻¹
      rwa [GlobalTheory.ZM.autOfRightAction_hom, inv_inv] at this
    · obtain ⟨a, ha⟩ := (hQ.comp_eq_comp_iff y y').mp e
      have ha : y ≫ ρ a⁻¹ = y' := ha
      refine ⟨a⁻¹, ha, fun c hc ↦ ?_⟩
      have hc : y ≫ ρ c = y' := hc
      have : y ≫ ρ (c * a) = y := by
        rw [hm, reassoc_of% hc, ← ha, Category.assoc, ← hm, inv_mul_cancel, h1, Category.comp_id]
      exact eq_inv_of_mul_eq_one_left (hfreeρ k y _ this)
  have := hc.fin
  have := hc.etale
  have := hc.onto
  obtain ⟨inst, hcomm, hhom⟩ := grp_descent S A _ ψ inferInstance hc.onto inferInstance
    (transl_compat S A _ H ψ hc)
  exact ⟨_, inst, hcomm, ψ, isAbelianScheme_of_finite_etale A _ ψ hA hcomm hc.fin hc.etale hc.onto,
    hhom, hc⟩

end GlobalTheory.TranslQuotient

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslationsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianScheme_quotient_by_finite_translations : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (H : Subgroup (𝟙_ (Over S) ⟶ A)), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Finite H → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ A), h ∈ H → toUnit (Over.mk x) ≫ h = 1 → h = 1) → ∃ (A' : Over S) (_ : GrpObj A') (_ : IsCommMonObj A') (ψ : A ⟶ A'), IsAbelianScheme A' ∧ IsMonHom ψ ∧ GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left := by
  first | exact @GlobalTheory.TranslQuotient.exists_quotient | exact GlobalTheory.TranslQuotient.exists_quotient | (intros; apply GlobalTheory.TranslQuotient.exists_quotient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal
open scoped nonZeroDivisors

namespace GlobalTheory.CMVal.PicFin

variable {E : Type} [Field E] [NumberField E]

theorem mul_mem_hatO {c : Ideal (OF E)} {n : OF E} (hn : n ∈ c) {y : Af E}
    (hy : ∀ v, y v ∈ v.adicCompletionIntegers E) : algebraMap E (Af E) (algebraMap (OF E) E n) * y ∈ hatO c := by
  refine GlobalTheory.IntDense.mem_of_isClosed E (C := {y | algebraMap E (Af E) (algebraMap (OF E) E n) * y ∈ hatO c})
    ((Subring.isClosed_topologicalClosure _).preimage (continuous_const.mul continuous_id)) (fun b => ?_) y hy
  show _ * _ ∈ hatO c
  rw [← map_mul]
  refine algebraMap_mem_hatO (mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) n * b,
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hn), ?_⟩)
  rw [map_zero, zero_add, map_mul]
  rfl

def intR (E : Type) [Field E] [NumberField E] : Subring (Af E) where
  carrier := {y | ∀ v, y v ∈ v.adicCompletionIntegers E}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem _
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem _
  neg_mem' ha v := neg_mem (ha v)

theorem finite_quot {N : ℕ} (hN : N ≠ 0) : Finite (intR E ⧸ Ideal.span {(N : intR E)}) := by
  have hi : ∀ a : 𝓞 E, algebraMap (𝓞 E) (Af E) a ∈ intR E := fun a v =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans_le (v.valuation_le_one a))
  let f : 𝓞 E →+* intR E := (algebraMap (𝓞 E) (Af E)).codRestrict _ hi
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN)
  refine Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 E)}) (Ideal.span {(N : intR E)}) f
    ((Ideal.span_singleton_le_iff_mem _).2 (by
      rw [Ideal.mem_comap, map_natCast]; exact Ideal.mem_span_singleton_self _))) fun x => ?_
  obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, β, hβ, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E N (Nat.pos_of_ne_zero hN)).2 α.1 α.2
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨⟨β, hβ⟩, Subtype.ext ?_⟩
  show α.1 - algebraMap (𝓞 E) (Af E) a = (N : Af E) * β
  rw [e, ← nsmul_eq_mul]
  exact add_sub_cancel_left _ _

theorem mem_intR {u : (Af E)ˣ} (h : GlobalTheory.Idele.idealOf u = 1) : (u : Af E) ∈ intR E := fun v => by
  have h1 := (GlobalTheory.Idele.smul_eq_self_iff u (I := 1) one_ne_zero).1 (by rw [GlobalTheory.Idele.smul_one_eq, h]) v
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h1.le

theorem mem_sup {a : (Af E)ˣ} {x : E} (hx : GlobalTheory.Idele.idealOf a = FractionalIdeal.spanSingleton (𝓞 E)⁰ x) :
    a ∈ ((intR E).toSubmonoid.units ⊔ princ : Subgroup (Af E)ˣ) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact GlobalTheory.Idele.idealOf_ne_zero _ (hx.trans (FractionalIdeal.spanSingleton_zero))
  obtain ⟨b, hb⟩ : ∃ b : (Af E)ˣ, b = FiniteAdeleRing.unitEmbedding (𝓞 E) E (Units.mk0 x hx0) := ⟨_, rfl⟩
  have h2 : GlobalTheory.Idele.idealOf (a * b⁻¹) = 1 := by
    rw [GlobalTheory.Idele.idealOf_mul, GlobalTheory.Idele.idealOf_inv, hb, GlobalTheory.Idele.idealOf_unitEmbedding, hx]
    exact mul_inv_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx0)
  have h3 : GlobalTheory.Idele.idealOf (a * b⁻¹)⁻¹ = 1 := by rw [GlobalTheory.Idele.idealOf_inv, h2, inv_one]
  have h4 : a * b⁻¹ ∈ (intR E).toSubmonoid.units := (Submonoid.mem_units_iff _ _).2 ⟨mem_intR h2, mem_intR h3⟩
  have h5 : b ∈ princ := MonoidHom.mem_range.2 ⟨Units.mk0 x hx0, by rw [hb]; exact Units.ext (by simp)⟩
  have h6 := Subgroup.mul_mem_sup h4 h5
  rwa [inv_mul_cancel_right] at h6

theorem finiteIndex_top : ((intR E).toSubmonoid.units ⊔ princ : Subgroup (Af E)ˣ).FiniteIndex := by
  classical
  let g : (Af E)ˣ →* ClassGroup (𝓞 E) := (ClassGroup.mk E).comp (GlobalTheory.Mem.UnitIndex.idealHom E).toHomUnits
  have : g.ker.FiniteIndex := Subgroup.finiteIndex_ker _
  refine Subgroup.finiteIndex_of_le (H := g.ker) fun a ha => ?_
  have h1 : ClassGroup.mk E ((GlobalTheory.Mem.UnitIndex.idealHom E).toHomUnits a) = 1 := ha
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 h1
  exact mem_sup hx

theorem finiteIndex_units {c : Ideal (OF E)} (hc : c ≠ ⊥) :
    ((hatOUnits c).subgroupOf (intR E).toSubmonoid.units).FiniteIndex := by
  have hN : Ideal.absNorm c ≠ 0 := fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  have := finite_quot (E := E) hN
  let r : (intR E).toSubmonoid.units →* intR E ⧸ Ideal.span {((Ideal.absNorm c : ℕ) : intR E)} :=
    { toFun := fun u => Ideal.Quotient.mk _ ⟨(u.1 : Af E), u.2.1⟩
      map_one' := map_one (Ideal.Quotient.mk _)
      map_mul' := fun a b => by rw [← map_mul]; rfl }
  have h1 : r.toHomUnits.ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have key : ∀ u ∈ r.toHomUnits.ker, ((u.1 : (Af E)ˣ) : Af E) ∈ hatO c := fun u hu => by
    have h2 : Ideal.Quotient.mk (Ideal.span {((Ideal.absNorm c : ℕ) : intR E)}) ⟨(u.1 : Af E), u.2.1⟩ =
        Ideal.Quotient.mk _ 1 := congrArg Units.val (MonoidHom.mem_ker.1 hu)
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h2
    obtain ⟨β, hβ⟩ := h2
    have h3 : ((u.1 : (Af E)ˣ) : Af E) - 1 = ((Ideal.absNorm c : ℕ) : Af E) * β.1 := congrArg Subtype.val hβ
    have h4 := mul_mem_hatO (Ideal.absNorm_mem c) β.2
    rw [map_natCast, map_natCast, ← h3] at h4
    simpa using add_mem h4 (one_mem _)
  exact Subgroup.finiteIndex_of_le (H := r.toHomUnits.ker) fun u hu => ⟨key u hu, key u⁻¹ (inv_mem hu)⟩

theorem finite_picO : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → Finite (PicO c) := by
  intro E _ _ _ c hc
  let U : Subgroup (Af E)ˣ := (intR E).toSubmonoid.units
  let K : Subgroup (Af E)ˣ := princ ⊔ hatOUnits c
  have h1 := finiteIndex_units hc
  have h2 : (K.subgroupOf U).FiniteIndex :=
    Subgroup.finiteIndex_of_le (H := (hatOUnits c).subgroupOf U) (Subgroup.comap_mono le_sup_right)
  have := finiteIndex_top (E := E)
  have h3 : (U ⊔ K).FiniteIndex := Subgroup.finiteIndex_of_le (H := U ⊔ princ) (sup_le_sup_left le_sup_left _)
  have : K.FiniteIndex := ⟨by
    rw [← Subgroup.relIndex_mul_index (le_sup_right : K ≤ U ⊔ K), Subgroup.relIndex_sup_right]
    exact mul_ne_zero h2.1 h3.1⟩
  exact Subgroup.finite_quotient_of_finiteIndex

end GlobalTheory.CMVal.PicFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZeroStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_ringClassGroup_of_conductor_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → Finite (PicO c) := by
  first | exact @GlobalTheory.CMVal.PicFin.finite_picO | exact GlobalTheory.CMVal.PicFin.finite_picO | (intros; apply GlobalTheory.CMVal.PicFin.finite_picO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare

open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

section Res

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def resI (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) : Formalism.L2.Herm.intAf F E →+* 𝓞 E ⧸ I :=
  ((RingEquiv.ofBijective (cmpS F I) (cmpS_bij (F := F) I hI)).symm : _ →+* 𝓞 E ⧸ I).comp
    (Ideal.Quotient.mk (idS F I))

variable {F}

theorem resI_oToS (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (a : 𝓞 E) :
    resI F I hI (oToS F E a) = Ideal.Quotient.mk I a := by
  unfold resI
  rw [RingHom.comp_apply]
  show (RingEquiv.ofBijective (cmpS F I) _).symm _ = _
  rw [RingEquiv.symm_apply_eq]
  rfl

theorem resI_eq_zero_iff (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (s : Formalism.L2.Herm.intAf F E) :
    resI F I hI s = 0 ↔ s ∈ idS F I := by
  unfold resI
  rw [RingHom.comp_apply]
  show (RingEquiv.ofBijective (cmpS F I) _).symm _ = _ ↔ _
  rw [map_eq_zero_iff _ (RingEquiv.injective _), Ideal.Quotient.eq_zero_iff_mem]

theorem resS_eq_resI (w : Pl E) : resS F w = resI F w.asIdeal w.ne_bot := rfl

end Res

section CRT

variable {E : Type} [Field E] [NumberField E] {I : Ideal (𝓞 E)} {Pg : Finset (Pl E)}

end CRT

end GlobalTheory.GeoActCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneTorusClassNumberBoundProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerAddNsmul
open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.UCls.NormOneMod

theorem exists_integer_add_nsmul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (M : ℕ) (hM : 1 ≤ M) (k : RA F E) (hk : k ∈ hat1 F {x : E | IsIntegral ℤ x}) :
    ∃ x : 𝓞 E, ∃ y ∈ hat1 F {x : E | IsIntegral ℤ x},
      k = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) + M • y := by
  induction hk using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨u, b, hb, h⟩ := (strong_approximation_mod_nat F M hM).2 a ha
    have hu : IsIntegral ℤ (algebraMap F E (u : F)) := u.isIntegral_coe.algebraMap
    refine ⟨⟨algebraMap F E (u : F) * x, hu.mul hx⟩, b ⊗ₜ x, tmul_mem_adelicCompletion_of_integral F hb hx, ?_⟩
    rw [h, TensorProduct.add_tmul, TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]
    rfl
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨x, y, hy, rfl⟩ := h1
    obtain ⟨x', y', hy', rfl⟩ := h2
    refine ⟨x + x', y + y', add_mem hy hy', ?_⟩
    have : ((x + x' : 𝓞 E) : E) = x + x' := by simp
    rw [this, TensorProduct.tmul_add, smul_add]
    abel
  | neg y _ h1 =>
    obtain ⟨x, y, hy, rfl⟩ := h1
    refine ⟨-x, -y, neg_mem hy, ?_⟩
    have : ((-x : 𝓞 E) : E) = -x := by simp
    rw [this, TensorProduct.tmul_neg, smul_neg]
    abel

theorem exists_reps (E : Type) [Field E] [NumberField E] (M : ℕ) (hM : 1 ≤ M) :
    ∃ T : Finset (𝓞 E), T.card ≤ M ^ Module.finrank ℚ E ∧
      ∀ x : 𝓞 E, ∃ t ∈ T, ∃ y : 𝓞 E, x = t + M • y := by
  classical
  let b := Module.finBasis ℤ (𝓞 E)
  let g : (Fin (Module.finrank ℤ (𝓞 E)) → Fin M) → 𝓞 E := fun f => ∑ i, ((f i : ℕ) : ℤ) • b i
  refine ⟨Finset.univ.image g, ?_, fun x => ?_⟩
  · refine Finset.card_image_le.trans ?_
    simp [RingOfIntegers.rank]
  · have hM0 : (0 : ℤ) < M := by exact_mod_cast hM
    let f : Fin (Module.finrank ℤ (𝓞 E)) → Fin M := fun i =>
      ⟨(b.repr x i % M).toNat, by
        have h1 := Int.emod_nonneg (b.repr x i) hM0.ne'
        have h2 := Int.emod_lt_of_pos (b.repr x i) hM0
        omega⟩
    refine ⟨g f, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      ∑ i, (b.repr x i / M) • b i, ?_⟩
    conv_lhs => rw [← b.sum_repr x]
    simp only [g, f, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hM0.ne'), ← natCast_zsmul, smul_smul, ← add_smul,
      Int.emod_add_mul_ediv]

theorem two_mul_fdeg (E : Type) [Field E] [NumberField E] [IsCMField E] :
    2 * fdeg E = Module.finrank ℚ E := by
  have h := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  rw [h2] at h
  unfold fdeg
  omega

theorem exists_reps_normOne (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : E ≃ₐ[F] E) (M : ℕ) (hM : 1 ≤ M) :
    ∃ S : Finset (RA F E), S.card ≤ M ^ Module.finrank ℚ E ∧ ∀ k : RA F E, IsTA c k →
      k ∈ hat1 F {x : E | IsIntegral ℤ x} → ∃ s ∈ S, IsTA c s ∧ ∃ k', IsTA c k' ∧
        (∃ y ∈ hat1 F {x : E | IsIntegral ℤ x}, k' - 1 = M • y) ∧ k = s * k' := by
  classical
  obtain ⟨T, hT, hT'⟩ := exists_reps E M hM
  let P : 𝓞 E → RA F E → Prop := fun t k => IsTA c k ∧ k ∈ hat1 F {x : E | IsIntegral ℤ x} ∧
    ∃ y ∈ hat1 F {x : E | IsIntegral ℤ x},
      k = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (t : E) + M • y
  let s : 𝓞 E → RA F E := fun t => Classical.epsilon (P t)
  refine ⟨T.image s, Finset.card_image_le.trans hT, fun k hk hk' => ?_⟩
  obtain ⟨x, y, hy, hxy⟩ := exists_integer_add_nsmul F E M hM k hk'
  obtain ⟨t, ht, z, rfl⟩ := hT' x
  have hP : P t k := by
    refine ⟨hk, hk', (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (z : E) + y,
      add_mem (one_tmul_mem_adelicCompletionOfElementSet F z.isIntegral_coe) hy, ?_⟩
    have : ((t + M • z : 𝓞 E) : E) = t + M • (z : E) := by simp
    rw [hxy, this, TensorProduct.tmul_add, TensorProduct.tmul_smul, smul_add, add_assoc]
  obtain ⟨hs, hs', w, hw, hsw⟩ : P t (s t) := Classical.epsilon_spec ⟨k, hP⟩
  obtain ⟨-, -, w', hw', hkw⟩ := hP
  have hc : sg (FiniteAdeleRing (𝓞 F) F) c (s t) ∈ hat1 F {x : E | IsIntegral ℤ x} :=
    galoisAut_mem_adelicCompletionOfElementSet F c (fun x hx => IsIntegral.map (c : E →+* E).toIntAlgHom hx) hs'
  refine ⟨s t, Finset.mem_image_of_mem _ ht, hs, k * sg _ c (s t), ?_,
    ⟨(w' - w) * sg _ c (s t), mul_mem_adelicCompletionOfElementSet_of_mul_mem F (fun a ha b hb => IsIntegral.mul ha hb)
      (sub_mem hw' hw) hc, ?_⟩, ?_⟩
  · have h1 := congrArg (sg (FiniteAdeleRing (𝓞 F) F) c) hs
    rw [map_mul, map_one] at h1
    unfold IsTA at hk ⊢
    rw [map_mul, mul_mul_mul_comm, hk, h1, one_mul]
  · have h1 : k - s t = M • (w' - w) := by
      rw [smul_sub]
      conv_lhs => rw [hkw, hsw]
      abel
    unfold IsTA at hs
    rw [← smul_mul_assoc, ← h1, sub_mul, hs]
  · unfold IsTA at hs
    rw [mul_left_comm, hs, mul_one]

theorem normOne_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : ℕ), 1 ≤ M → ∃ S : Finset (RA (maximalRealSubfield E) E), S.card ≤ M ^ (2 * fdeg E) ∧ ∀ k : RA (maximalRealSubfield E) E, IsTA (IsCMField.complexConj E) k → k ∈ hat1 (maximalRealSubfield E) {x : E | IsIntegral ℤ x} → ∃ s ∈ S, IsTA (IsCMField.complexConj E) s ∧ ∃ k', IsTA (IsCMField.complexConj E) k' ∧ (∃ y ∈ hat1 (maximalRealSubfield E) {x : E | IsIntegral ℤ x}, k' - 1 = M • y) ∧ k = s * k' := by
  intro E _ _ _ M hM
  rw [two_mul_fdeg]
  exact exists_reps_normOne _ E _ M hM

end GlobalTheory.UCls.NormOneMod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneTorusClassNumberBoundProof
noncomputable section

open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

namespace GlobalTheory.UCls

theorem torusBound : TorusBound := by
  intro E _ _ _ r M G Λ hr hM hE hΛ
  classical
  set c := IsCMField.complexConj E
  obtain ⟨S, hS, hS'⟩ := GlobalTheory.UCls.normOne_classes_le_classNumber E hE
  obtain ⟨S', hS₂, hS₂'⟩ := GlobalTheory.UCls.NormOneMod.normOne_mod E M hM
  let T : Finset (RA (maximalRealSubfield E) E) := (S ×ˢ S').image fun p => p.1 * p.2
  have hT : T.card ≤ classNumber E * M ^ (2 * fdeg E) :=
    Finset.card_image_le.trans ((Finset.card_product S S').le.trans (Nat.mul_le_mul hS hS₂))
  have hTA : ∀ a b : RA (maximalRealSubfield E) E, IsTA c a → IsTA c b → IsTA c (a * b) := by
    intro a b ha hb
    unfold IsTA at *
    rw [map_mul, mul_mul_mul_comm, ha, hb, one_mul]
  have hone : IsTA c (1 : RA (maximalRealSubfield E) E) := by simp [IsTA]
  let Q := Quot fun a b : {t // IsTA c t} => TEquiv c G (Λ : Set (Fin r → E)) M a.1 b.1
  let φ : T → Q := fun x => if h : IsTA c x.1 then Quot.mk _ ⟨x.1, h⟩ else Quot.mk _ ⟨1, hone⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨t, ht⟩
    obtain ⟨s, hs, u, hu, k, hk, hkint, hsTA, rfl⟩ := hS' t ht
    obtain ⟨s', hs', hs'TA, k', hk'TA, hk'1, rfl⟩ := hS₂' k hk hkint
    obtain ⟨g, hg, hdet⟩ := GlobalTheory.UCls.Det.exists_isKM_det_eq E hE r M G Λ hr hM hΛ k' hk'TA hk'1
    have hmem : s * s' ∈ T := Finset.mem_image.2 ⟨(s, s'), Finset.mem_product.2 ⟨hs, hs'⟩, rfl⟩
    refine ⟨⟨s * s', hmem⟩, ?_⟩
    simp only [φ, dif_pos (hTA s s' hsTA hs'TA)]
    refine Quot.sound ⟨u, hu, g, hg, ?_⟩
    rw [hdet]
    ring
  calc torusNo c G (Λ : Set (Fin r → E)) M = ENat.card Q := rfl
    _ ≤ ENat.card T := ENat.card_le_card_of_injective (Function.injective_surjInv hφ)
    _ = T.card := by rw [ENat.card_eq_coe_fintype_card, Fintype.card_coe]
    _ ≤ _ := by exact_mod_cast hT

end GlobalTheory.UCls
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneTorusClassNumberBoundProofStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOneTorusClassNumberBound_proof : GlobalTheory.UCls.TorusBound := by
  first | exact @GlobalTheory.UCls.torusBound | exact GlobalTheory.UCls.torusBound | (intros; apply GlobalTheory.UCls.torusBound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedPullbackMulPairIsoTensorPowSq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedPullbackMulPairIsoTensorPowSq
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.BirigidPow

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem comp_pow_pt {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ A) (n : ℕ) : ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

def val {P : LB (G2 A).left} (hP : P.IsLB) {T : Over S} (x y : T ⟶ A) : CechPic.Pic T.left :=
  CechPic.pull (lift x y).left (CechPic.cls P hP)

variable {P : LB (G2 A).left} (hP : P.IsLB)

theorem val_one_left (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) {T : Over S}
    (y : T ⟶ A) : val hP 1 y = 0 := by
  have e : lift (1 : T ⟶ A) y = y ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    rw [comp_lift, MonObj.comp_one, Category.comp_id]
  rw [val, e, Over.comp_left, CechPic.pull_comp, ← CechPic.cls_pull hP _ (pull_isLB hP _),
    (CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 h₁, map_zero]

theorem val_one_right (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) {T : Over S}
    (x : T ⟶ A) : val hP x 1 = 0 := by
  have e : lift x (1 : T ⟶ A) = x ≫ lift (𝟙 A) (1 : A ⟶ A) := by
    rw [comp_lift, MonObj.comp_one, Category.comp_id]
  rw [val, e, Over.comp_left, CechPic.pull_comp, ← CechPic.cls_pull hP _ (pull_isLB hP _),
    (CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 h₂, map_zero]

theorem add_of_triv {T : Over S} (a b c : T.left ⟶ (G2 A).left)
    (H : ∃ t : (LB.LinComb P (K := Fin 3) ![a, b, c] ![1, -1, -1]).Gen, t.IsGen) :
    CechPic.pull a (CechPic.cls P hP) = CechPic.pull b (CechPic.cls P hP) + CechPic.pull c (CechPic.cls P hP) := by
  have hL := LB.isLB_linComb hP (![a, b, c] : Fin 3 → _) ![1, -1, -1]
  have z := (CechPic.cls_linComb hP _ _ hL).symm.trans ((CechPic.cls_eq_zero_iff hL).2 H)
  rw [Fin.sum_univ_three] at z
  have z' : (1 : ℤ) • CechPic.pull a (CechPic.cls P hP) + (-1 : ℤ) • CechPic.pull b (CechPic.cls P hP) +
      (-1 : ℤ) • CechPic.pull c (CechPic.cls P hP) = 0 := z
  rw [one_zsmul, neg_one_zsmul, neg_one_zsmul] at z'
  rw [← sub_eq_zero, ← z']
  abel

variable (hA : IsAbelianScheme A)
  (hamp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left))
  (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
  (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)

include hA hamp h₁ h₂

theorem val_mul_left {T : Over S} (x x' y : T ⟶ A) : val hP (x * x') y = val hP x y + val hP x' y :=
  add_of_triv hP _ _ _ (Biadditive.biadditive_of_triv_axes GlobalTheory.laws_without_cohomology.1 S A _ hA
    (pull_isLB hP _) hamp P hP h₁ h₂ T x x' y).1

theorem val_mul_right {T : Over S} (x y y' : T ⟶ A) : val hP x (y * y') = val hP x y + val hP x y' :=
  add_of_triv hP _ _ _ (Biadditive.biadditive_of_triv_axes GlobalTheory.laws_without_cohomology.1 S A _ hA
    (pull_isLB hP _) hamp P hP h₁ h₂ T y y' x).2

theorem val_pow_left {T : Over S} (x y : T ⟶ A) (n : ℕ) : val hP (x ^ n) y = n • val hP x y := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact val_one_left hP h₁ y
  | succ n ih => rw [pow_succ, val_mul_left hP hA hamp h₁ h₂, ih, succ_nsmul]

theorem val_pow_right {T : Over S} (x y : T ⟶ A) (n : ℕ) : val hP x (y ^ n) = n • val hP x y := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact val_one_right hP h₂ x
  | succ n ih => rw [pow_succ, val_mul_right hP hA hamp h₁ h₂, ih, succ_nsmul]

omit hA hamp h₁ h₂ in
theorem cls_lbPow (m : ℕ) (h : (Hecke.lbPow P m).IsLB) : CechPic.cls _ h = m • CechPic.cls P hP := by
  unfold Hecke.lbPow at h ⊢
  rw [CechPic.cls_linComb hP _ _ h]
  simp [CechPic.pull_id]


include hP in
theorem lineBundleIso_tensorPowSq_pullback_mulPair (n : ℕ) :
    LBIso (Hecke.lbPow P (n ^ 2)) (P.pull (Hecke.sq2 ((𝟙 A) ^ n))) := by
  have hL : (Hecke.lbPow P (n ^ 2)).IsLB := LB.isLB_linComb hP _ _
  refine (CechPic.cls_eq_iff hL (pull_isLB hP _)).1 ?_
  rw [cls_lbPow hP, CechPic.cls_pull hP _ (pull_isLB hP _)]
  change _ = val hP (fst A A ≫ (𝟙 A) ^ n) (snd A A ≫ (𝟙 A) ^ n)
  rw [comp_pow_pt, comp_pow_pt, Category.comp_id, Category.comp_id, val_pow_left hP hA hamp h₁ h₂,
    val_pow_right hP hA hamp h₁ h₂, val, lift_fst_snd, Over.id_left, CechPic.pull_id, smul_smul, sq]


omit hP hA hamp h₁ h₂ in
theorem birigidified_pullback_mulPair_iso_tensorPowSq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    ∀ n : ℕ, LBIso (GlobalTheory.UPel.HT.Hecke.lbPow P (n ^ 2)) (P.pull (GlobalTheory.UPel.HT.Hecke.sq2 ((𝟙 A) ^ n))) :=
  fun _ _ _ _ hA _ hP h₁ h₂ hamp n => lineBundleIso_tensorPowSq_pullback_mulPair hP hA hamp h₁ h₂ n

end GlobalTheory.BirigidPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedPullbackMulPairIsoTensorPowSqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbIso_lbPow_sq_pull_sq2_of_isGen_of_relAmple : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ n : ℕ, LBIso (GlobalTheory.UPel.HT.Hecke.lbPow P (n ^ 2)) (P.pull (GlobalTheory.UPel.HT.Hecke.sq2 ((𝟙 A) ^ n))) := by
  exact @GlobalTheory.BirigidPow.birigidified_pullback_mulPair_iso_tensorPowSq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCover
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CoverDeg

def GoodCover {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (π : Y ⟶ X) (D δ : ℕ)
    (U : X.Opens) : Prop :=
  IsAffineOpen U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧
    (∃ t : Fin D → Γ(X, U), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) t).Etale) ∧
    (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧
    (letI := (π.app U).hom.toAlgebra
     Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = δ)

end GlobalTheory.CoverDeg
end
end
