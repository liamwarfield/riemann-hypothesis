module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.BaseExt

section ext

variable {K K' : Type} [Field K] [Field K'] (f : K →+* K')

theorem span_image_span (s : Set K) :
    Submodule.span (𝓞 K') (f '' (Submodule.span (𝓞 K) s : Set K)) = Submodule.span (𝓞 K') (f '' s) := by
  refine le_antisymm (Submodule.span_le.2 ?_)
    (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : f (a • x) = RingOfIntegers.mapRingHom f a • f x := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ hx

def extend : Submodule (𝓞 K) K →* Submodule (𝓞 K') K' where
  toFun M := Submodule.span (𝓞 K') (f '' (M : Set K))
  map_one' := by
    rw [Submodule.one_eq_span, span_image_span, Submodule.one_eq_span]; simp
  map_mul' M N := by
    conv_lhs => rw [← M.span_eq, ← N.span_eq, Submodule.span_mul_span, span_image_span]
    rw [Submodule.span_mul_span, Set.image_mul]

theorem extend_span (s : Set K) :
    extend f (Submodule.span (𝓞 K) s) = Submodule.span (𝓞 K') (f '' s) := span_image_span f s

end ext

section host

variable {R : Ranks} (H : Host R)

theorem conjugate_emb (g : R.GG) :
    ComplexEmbedding.conjugate (H.emb g) = H.emb (g * R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp]
  refine RingHom.ext fun x => ?_
  have hcm := H.isCMField_hostE
  have h : IsCMField.complexConj H.E x = H.conj x := by
    apply H.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj, H.conjE_apply]
  show starRingEnd ℂ (H.emb g x) = H.emb g (H.conj x)
  rw [← h, IsCMField.complexEmbedding_complexConj]

theorem conjugate_emb_apply (g : R.GG) (x : H.E) :
    ComplexEmbedding.conjugate (H.emb g) x = H.emb g (H.conj x) := by
  rw [conjugate_emb, Formalism.L2.Geo.emb_mul_cc_comp]; rfl

theorem ex_emb_iff (g : R.GG) :
    (∃ t : Tau R, H.emb t = H.emb g) ↔ g ∈ R.Psi :=
  ⟨fun ⟨t, ht⟩ => (factEmb R H).1.1 ht ▸ t.2, fun h => ⟨⟨g, h⟩, rfl⟩⟩

theorem emb_cm (σ : H.E →+* ℂ) :
    (∃ t : Tau R, H.emb t = σ) ↔ ¬ ∃ t : Tau R, H.emb t = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb R H).1.2 σ
  rw [conjugate_emb, ex_emb_iff, ex_emb_iff]
  exact Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g

theorem sum_emb_bijective : Function.Bijective
    (Sum.elim (fun t : Tau R => H.emb t) fun t : Tau R => ComplexEmbedding.conjugate (H.emb t)) := by
  have hc : ∀ σ : H.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => star_star σ
  have hi : ∀ {a b : Tau R}, H.emb a = H.emb b → a = b := fun h => Subtype.ext ((factEmb R H).1.1 h)
  constructor
  · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · rw [hi h]
    · exact absurd ⟨a, h⟩ ((emb_cm H (H.emb b)).1 ⟨b, rfl⟩)
    · exact absurd ⟨b, h.symm⟩ ((emb_cm H (H.emb a)).1 ⟨a, rfl⟩)
    · have := congrArg ComplexEmbedding.conjugate h
      rw [hc, hc] at this
      rw [hi this]
  · intro σ
    by_cases h : ∃ t : Tau R, H.emb t = ComplexEmbedding.conjugate σ
    · obtain ⟨t, ht⟩ := h
      exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
    · obtain ⟨t, ht⟩ := (emb_cm H σ).2 h
      exact ⟨Sum.inl t, ht⟩

open Classical in
def typeExp (p q : ℕ) (σ : H.E →+* ℂ) : ℕ := if ∃ t : Tau R, H.emb t = σ then p else q

theorem typeExp_emb (p q : ℕ) (t : Tau R) : typeExp H p q (H.emb t) = p := if_pos ⟨t, rfl⟩

theorem typeExp_conj (p q : ℕ) (t : Tau R) :
    typeExp H p q (ComplexEmbedding.conjugate (H.emb t)) = q := if_neg ((emb_cm H _).1 ⟨t, rfl⟩)

theorem typeExp_add (p q : ℕ) (σ : H.E →+* ℂ) :
    typeExp H p q σ + typeExp H p q (ComplexEmbedding.conjugate σ) = p + q := by
  unfold typeExp
  by_cases h : ∃ t : Tau R, H.emb t = σ
  · rw [if_pos h, if_neg ((emb_cm H σ).1 h)]
  · rw [if_neg h, if_pos (not_not.1 (fun h' => h ((emb_cm H σ).2 h'))), add_comm]

theorem prod_typeExp {M : Type} [CommMonoid M] (p q : ℕ) (F : (H.E →+* ℂ) → M) :
    ∏ σ, F σ ^ typeExp H p q σ =
      ∏ t : Tau R, (F (H.emb t) ^ p * F (ComplexEmbedding.conjugate (H.emb t)) ^ q) := by
  rw [← (sum_emb_bijective H).prod_comp, Fintype.prod_sum_type, Finset.prod_mul_distrib]
  simp only [Sum.elim_inl, Sum.elim_inr, typeExp_emb, typeExp_conj]

end host

theorem isAlgebraic_exp (N : ℕ) : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * Complex.I / N)) := by
  rcases Nat.eq_zero_or_pos N with rfl | h
  · simpa using isAlgebraic_one
  · exact ((Complex.isPrimitiveRoot_exp N h.ne').isIntegral h).tower_top.isAlgebraic

theorem exists_gens (E : Type) [Field E] [NumberField E] : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ K : IntermediateField ℚ ℂ, (∀ z ∈ S, z ∈ K) → ∀ (τ : E →+* ℂ) x, τ x ∈ K := by
  classical
  let b := Module.finBasis ℚ E
  refine ⟨Finset.univ.image fun p : (E →+* ℂ) × Fin (Module.finrank ℚ E) => p.1 (b p.2), ?_, ?_⟩
  · intro z hz
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hz
    exact (Algebra.IsAlgebraic.isAlgebraic (b p.2)).algHom p.1.toRatAlgHom
  · intro K hK τ x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact K.smul_mem (hK _ (Finset.mem_image.2 ⟨(τ, i), Finset.mem_univ _, rfl⟩))

@[instance_reducible] def starOf (K : IntermediateField ℚ ℂ) (h : ∀ z ∈ K, starRingEnd ℂ z ∈ K) : StarRing K where
  star x := ⟨starRingEnd ℂ x, h _ x.2⟩
  star_involutive x := Subtype.ext (Complex.conj_conj _)
  star_mul x y := Subtype.ext (by
    show starRingEnd ℂ ((x : ℂ) * y) = starRingEnd ℂ y * starRingEnd ℂ x
    rw [map_mul, mul_comm])
  star_add x y := Subtype.ext (map_add (starRingEnd ℂ) (x : ℂ) (y : ℂ))

def toTop (K : IntermediateField ℚ ℂ) : K →+* (⊤ : IntermediateField ℚ K) :=
  (IntermediateField.topEquiv (F := ℚ) (E := K)).symm

theorem image_top {E : Type} [Field E] (K : IntermediateField ℚ ℂ) (𝔞 : Ideal (𝓞 E)) (τ : E →+* ℂ) (e : E → K)
    (he : ∀ a, (e a : ℂ) = τ a) :
    extend (toTop K) (Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)}) =
      Submodule.span (𝓞 (⊤ : IntermediateField ℚ K))
        {x : (⊤ : IntermediateField ℚ K) | ∃ a ∈ 𝔞, (x : K) = e (a : E)} := by
  rw [extend_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, hy⟩, rfl⟩
    exact ⟨a, ha, Subtype.ext (hy.trans (he _).symm)⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨x.1, ⟨a, ha, (congrArg Subtype.val hx).trans (he _)⟩, rfl⟩

theorem exists_base : ∀ (B : Pre) (S₀ S₁ S₂ : Finset ℂ), (∀ z ∈ S₀, IsAlgebraic ℚ z) → (∀ z ∈ S₁, IsAlgebraic ℚ z) → (∀ z ∈ S₂, IsAlgebraic ℚ z) → ∃ B' : Base, B'.toPre = B ∧ (∀ z ∈ S₀, ∃ x ∈ B'.Ks, B'.embLL x = z) ∧ (∀ z ∈ S₁, ∃ x ∈ B'.LL0, B'.embLL x = z) ∧ ∀ z ∈ S₂, ∃ x : B'.LL, B'.embLL x = z := by
  classical
  intro B S₀ S₁ S₂ h₀ h₁ h₂
  have hcm : IsCMField B.host.E := B.host.isCMField_hostE
  have hgal : IsGalois ℚ B.host.E := B.host.hostE_isGalois
  obtain ⟨SE, hSE, hE⟩ := exists_gens B.host.E
  choose MainNotions hSK hK using fun j : ℕ => GlobalTheory.Mem.exists_finset_typeNorm_principal B.host.E
    (typeExp B.host (B.R.sigW j).1 (B.R.sigW j).2) _ (typeExp_add B.host _ _)
  obtain ⟨SC, hSC, hC⟩ := GlobalTheory.Mem.exists_finset_capitulation B.host.E B.host.φ₀
  let l : List ℕ := [B.restRowsFiniteGroupCard, B.host.g 0 * (B.host.g 0 - 1), B.host.g 1 * (B.host.g 1 - 1), 3 ^ 4, 5 ^ 4]
  let l' : List ℕ := [B.host.pde, B.host.pde', classNumber B.host.E]
  let A : Finset ℕ := l.toFinset ∪ l'.toFinset ∪ {B.ramOrder} ∪ Finset.univ.image B.T
  let SR : Finset ℂ := A.image fun N : ℕ => Complex.exp (2 * Real.pi * Complex.I / N)
  obtain ⟨K, hfd, hKgal, hS, -, hconj⟩ := GlobalTheory.exists_galois_subfield_conj_stable
    (S₀ ∪ S₁ ∪ S₂ ∪ SE ∪ SC ∪ SR ∪ (Finset.range (B.R.m + 1)).biUnion MainNotions) (by
      intro z hz
      simp only [Finset.mem_union, Finset.mem_biUnion] at hz
      rcases hz with (((((hz | hz) | hz) | hz) | hz) | hz) | ⟨j, -, hz⟩
      exacts [h₀ z hz, h₁ z hz, h₂ z hz, hSE z hz, hSC z hz, by
        obtain ⟨N, -, rfl⟩ := Finset.mem_image.1 hz
        exact isAlgebraic_exp N, hSK j z hz])
  simp only [Finset.mem_union, Finset.mem_biUnion] at hS
  have hEK := hE K fun z hz => hS z (by tauto)
  have hR : ∀ N ∈ A, Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ K := fun N hN => by
    have hz : Complex.exp (2 * Real.pi * Complex.I / N) ∈ SR := Finset.mem_image.2 ⟨N, hN, rfl⟩
    exact hS _ (by tauto)
  have : NumberField K := {}
  let f := toTop K
  refine ⟨{ toPre := B
            LL := K
            starLL := starOf K hconj
            embLL := K.val
            starLL_cx := fun _ => rfl
            embE := B.host.φ₀.codRestrict K (hEK _)
            embE_φ₀ := rfl
            LL0 := ⊤
            coeffGaloisSubfield_isGalois := IsGalois.of_algEquiv IntermediateField.topEquiv.symm
            Ks := ⊤
            Ks_le := le_rfl
            E_le_Ks := fun _ => trivial
            roots_Ks := ?_
            roots_Ks' := ?_
            capit := ?_
            kPsi := ?_
            rootOfUnity_eightQ_mem_coeffGaloisSubfield := ⟨⟨_, hR B.ramOrder (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_singleton_self _)))⟩, trivial, rfl⟩
            roots_LL := fun u => ⟨⟨_, hR (B.T u) (Finset.mem_union_right _
              (Finset.mem_image_of_mem _ (Finset.mem_univ u)))⟩, rfl⟩ }, rfl, ?_, ?_, ?_⟩
  · intro N hN
    exact ⟨⟨_, hR N (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (List.mem_toFinset.2 hN))))⟩, trivial, rfl⟩
  · intro N hN
    exact ⟨⟨_, hR N (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (List.mem_toFinset.2 hN))))⟩, trivial, rfl⟩
  · intro 𝔞
    obtain ⟨β, hsp⟩ := hC K (fun z hz => hS z (by tauto)) (hEK _) 𝔞
    refine ⟨f β, ?_⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton] at h
    exact h.trans (image_top K 𝔞 B.host.φ₀ (B.host.φ₀.codRestrict K (hEK _)) fun _ => rfl)
  · intro j _ hj 𝔞 h𝔞
    obtain ⟨β, hβ, hsp, hn⟩ := hK j K
      (fun z hz => hS z (Or.inr ⟨j, Finset.mem_range.2 (by omega), hz⟩)) hEK 𝔞 h𝔞
    refine ⟨f β, (map_ne_zero f).2 hβ, ?_, fun σ => hn (σ.comp f)⟩
    have h := congrArg (extend f) hsp
    rw [prod_typeExp, extend_span, Set.image_singleton, map_prod] at h
    rw [h]
    refine Finset.prod_congr rfl fun g _ => ?_
    have e1 := image_top K 𝔞 (B.host.emb g)
      (fun a => B.host.φ₀.codRestrict K (hEK _) (B.host.sigmaOf g a)) fun _ => rfl
    have e2 := image_top K 𝔞 (ComplexEmbedding.conjugate (B.host.emb g))
      (fun a => B.host.φ₀.codRestrict K (hEK _) (B.host.sigmaOf g (B.host.conj a)))
      fun a => (conjugate_emb_apply B.host g a).symm
    rw [map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (congrArg (· ^ (B.R.sigW j).1) e1) (congrArg (· ^ (B.R.sigW j).2) e2)
  · exact fun z hz => ⟨⟨z, hS z (by tauto)⟩, trivial, rfl⟩
  · exact fun z hz => ⟨⟨z, hS z (by tauto)⟩, trivial, rfl⟩
  · exact fun z hz => ⟨⟨z, hS z (by tauto)⟩, rfl⟩

end GlobalTheory.Mem.BaseExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousInfIdele
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.InfTypeLocal

theorem denseRange_atInf (L : Type) [Field L] [NumberField L] :
    DenseRange (fun (k : Lˣ) (w : InfinitePlace L) => atInf w k) := by
  have hg : Topology.IsOpenEmbedding
      (Pi.map (fun (w : InfinitePlace L) => (Units.val : (w.Completion)ˣ → w.Completion))) :=
    Topology.IsOpenEmbedding.piMap (fun w => Units.isOpenEmbedding_val)
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ := (InfiniteAdeleRing.denseRange_algebraMap L).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
    have h1 := congrFun hk w
    rw [map_zero] at h1
    exact (v w).ne_zero h1
  refine ⟨v, hv, Units.mk0 k hk0, ?_⟩
  funext w
  exact Units.ext (congrFun hk w).symm

theorem continuous_infIdele (L : Type) [Field L] [NumberField L] (w : InfinitePlace L) :
    Continuous (infIdele L w) := by
  classical
  refine Continuous.units_map _ ?_
  exact Continuous.prodMk (continuous_mulSingle w) continuous_const

theorem exists_ext {L : Type} [Field L] (φ : L →+* ℂ) :
    ∃ e : (InfinitePlace.mk φ).Completion →+* ℂ, Continuous e ∧
      ∀ k : L, e (algebraMap L _ k) = φ k := by
  have h0 : ∀ k : L, InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ) (algebraMap L _ k) =
      (InfinitePlace.mk φ).embedding k := fun k => by
    rw [InfinitePlace.Completion.algebraMap_apply]
    simpa using InfinitePlace.Completion.extensionEmbedding_coe (InfinitePlace.mk φ) (WithAbs.toAbs _ k)
  have hc := (InfinitePlace.Completion.isometry_extensionEmbedding (InfinitePlace.mk φ)).continuous
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · exact ⟨_, hc, fun k => by rw [h0, h]⟩
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _),
      Complex.continuous_conj.comp hc, fun k => ?_⟩
    rw [RingHom.comp_apply, h0, h]
    simp

open Classical in
theorem infType_iff_local : ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ), (Function.Bijective fun i => InfinitePlace.mk (φ i)) → ∀ (ψ : Ideles L →* ℂˣ), Continuous ψ → ∀ n : I → ℤ, ((∀ k : Lˣ, ((ψ (infDiag k) : ℂˣ) : ℂ) = ∏ i, (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) ↔ ∀ i (k : Lˣ), ((ψ (infIdele L (InfinitePlace.mk (φ i)) (atInf _ k)) : ℂˣ) : ℂ) = (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) := by
  intro L _ _ I _ φ hφ ψ hψ n
  have hd : ∀ k : Lˣ, ((ψ (infDiag k) : ℂˣ) : ℂ) = ∏ w, ((ψ (infIdele L w (atInf w k)) : ℂˣ) : ℂ) := by
    intro k
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, map_prod, Units.coe_prod]
    rfl
  constructor
  · intro h
    choose e hec he using fun i => exists_ext (φ i)
    have key : (fun u : ∀ w : InfinitePlace L, (w.Completion)ˣ => ∏ w, ((ψ (infIdele L w (u w)) : ℂˣ) : ℂ)) =
        fun u => ∏ i, (e i (u (InfinitePlace.mk (φ i))) / ((‖e i (u (InfinitePlace.mk (φ i)))‖ : ℝ) : ℂ)) ^ n i := by
      refine (denseRange_atInf L).equalizer ?_ ?_ ?_
      · refine continuous_finsetProd _ fun w _ => ?_
        exact Units.continuous_val.comp (hψ.comp ((continuous_infIdele L w).comp (continuous_apply w)))
      · refine continuous_finsetProd _ fun i _ => ?_
        have h1 : Continuous fun u : ∀ w : InfinitePlace L, (w.Completion)ˣ => e i (u (InfinitePlace.mk (φ i))) :=
          (hec i).comp (Units.continuous_val.comp (continuous_apply _))
        have h2 : ∀ u : ∀ w : InfinitePlace L, (w.Completion)ˣ, e i (u (InfinitePlace.mk (φ i))) ≠ 0 := fun u =>
          (map_ne_zero _).2 (Units.ne_zero (u (InfinitePlace.mk (φ i))))
        have h3 : ∀ u : ∀ w : InfinitePlace L, (w.Completion)ˣ, ((‖e i (u (InfinitePlace.mk (φ i)))‖ : ℝ) : ℂ) ≠ 0 := fun u => by
          exact_mod_cast norm_ne_zero_iff.2 (h2 u)
        exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h3).zpow₀ _ fun u => Or.inl (div_ne_zero (h2 u) (h3 u))
      · funext k
        show ∏ w, ((ψ (infIdele L w (atInf w k)) : ℂˣ) : ℂ) =
          ∏ i, (e i (algebraMap L _ (k : L)) / ((‖e i (algebraMap L _ (k : L))‖ : ℝ) : ℂ)) ^ n i
        rw [← hd, h]
        simp only [he]
    intro i k
    have h1 := congrFun key (Pi.mulSingle (InfinitePlace.mk (φ i)) (atInf _ k))
    beta_reduce at h1
    rw [Finset.prod_eq_single (InfinitePlace.mk (φ i)), Finset.prod_eq_single i] at h1
    · rw [Pi.mulSingle_eq_same] at h1
      rw [h1, ← he i k]
      rfl
    · intro j _ hj
      rw [Pi.mulSingle_eq_of_ne (fun hh => hj (hφ.1 hh))]
      simp
    · simp
    · intro w _ hw
      rw [Pi.mulSingle_eq_of_ne hw]
      simp
    · simp
  · intro h k
    rw [hd, ← hφ.prod_comp]
    exact Finset.prod_congr rfl fun i _ => h i k

end GlobalTheory.InfTypeLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRationalInfTypeSubgroupAndInfTypeUnique
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Filter Topology

namespace GlobalTheory.HalfIntChars

theorem emb_mul_indep {L I : Type} [Field L] [CharZero L] [Fintype I] (σ : I → L →+* ℂ) (hσ : Function.Injective σ)
    (m : I → ℤ) (h : ∀ k : L, k ≠ 0 → ∏ i, σ i k ^ m i = 1) : m = 0 := by
  classical
  have key : ∀ x : L, ∑ i, (m i : ℂ) * σ i x = 0 := by
    intro x
    let f : ℂ → ℂ := fun t => ∏ i, (1 + t * σ i x) ^ m i
    have hd : ∀ i ∈ (Finset.univ : Finset I),
        HasDerivAt (fun t : ℂ => (1 + t * σ i x) ^ m i) ((m i : ℂ) * σ i x) 0 := by
      intro i _
      have h1 : HasDerivAt (fun t : ℂ => 1 + t * σ i x) (σ i x) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (σ i x)).const_add 1
      have h2 := (hasDerivAt_zpow (m i) ((fun t : ℂ => 1 + t * σ i x) 0) (Or.inl (by simp))).comp (0 : ℂ) h1
      simpa [Function.comp_def] using h2
    have hf : HasDerivAt f (∑ i, (m i : ℂ) * σ i x) 0 := by
      have := HasDerivAt.fun_finsetProd hd
      simpa [f] using this
    have hs := hasDerivAt_iff_tendsto_slope.1 hf
    have hu : Tendsto (fun n : ℕ => ((1 : ℂ) / ((n : ℂ) + 1))) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ), Eventually.of_forall fun n => ?_⟩
      exact one_div_ne_zero (Nat.cast_add_one_ne_zero n)
    have hfin : ∀ᶠ n : ℕ in atTop, (1 + (1 / ((n : L) + 1)) * x) ≠ 0 := by
      rw [← Nat.cofinite_eq_atTop]
      refine Set.Subsingleton.finite ?_
      intro a ha b hb
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at ha hb
      have ha1 : ((a : L) + 1) ≠ 0 := Nat.cast_add_one_ne_zero a
      have hb1 : ((b : L) + 1) ≠ 0 := Nat.cast_add_one_ne_zero b
      field_simp at ha hb
      have : (a : L) = b := by linear_combination ha - hb
      exact_mod_cast this
    have h0 : Tendsto (fun n : ℕ => slope f 0 ((1 : ℂ) / ((n : ℂ) + 1))) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' (hfin.mono fun n hn => ?_)
      have h1 := h _ hn
      have h2 : f ((1 : ℂ) / ((n : ℂ) + 1)) = 1 := by
        refine Eq.trans ?_ h1; simp [f]
      have h3 : f 0 = 1 := by simp [f]
      simp only [slope, h2, h3, vsub_self, smul_zero]
    exact tendsto_nhds_unique (hs.comp hu) h0
  have li := (linearIndependent_monoidHom L ℂ).comp (fun i => (σ i : L →* ℂ))
    (fun i j hij => hσ (RingHom.coe_monoidHom_injective hij))
  have := Fintype.linearIndependent_iff.1 li (fun i => (m i : ℂ)) (by
    funext x
    simpa [Finset.sum_apply] using key x)
  funext i
  exact_mod_cast this i

theorem unit_sq (z : ℂ) (hz : z ≠ 0) : (z / ((‖z‖ : ℝ) : ℂ)) ^ 2 = z / starRingEnd ℂ z := by
  have h1 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  have h2 : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have h3 : z * starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  field_simp
  rw [← h3]

theorem hasInf_unique {L I : Type} [Field L] [NumberField L] [Fintype I] (φ : I → L →+* ℂ) (h1 : Function.Injective φ)
    (h2 : ∀ i j, φ i ≠ (starRingEnd ℂ).comp (φ j)) {χ : HChar L} {n n' : I → ℤ} (h : χ.HasInf φ n) (h' : χ.HasInf φ n') :
    n = n' := by
  let σ : I ⊕ I → L →+* ℂ := Sum.elim φ fun i => (starRingEnd ℂ).comp (φ i)
  have hσ : Function.Injective σ := by
    rintro (i | i) (j | j) hij
    · exact congrArg _ (h1 hij)
    · exact absurd hij (h2 i j)
    · exact absurd hij.symm (h2 j i)
    · refine congrArg _ (h1 (RingHom.ext fun x => ?_))
      have := congrArg (fun f : L →+* ℂ => starRingEnd ℂ (f x)) hij
      simpa [σ] using this
  have := emb_mul_indep σ hσ (Sum.elim (n - n') (n' - n)) (fun k hk => by
    have e := (h (Units.mk0 k hk)).symm.trans (h' (Units.mk0 k hk))
    simp only [Units.val_mk0] at e
    have hne : ∀ i, φ i k ≠ 0 := fun i => by simpa using hk
    have hu : ∀ i, φ i k / ((‖φ i k‖ : ℝ) : ℂ) ≠ 0 := fun i =>
      div_ne_zero (hne i) (by exact_mod_cast norm_ne_zero_iff.2 (hne i))
    have e2 : ∏ i, (φ i k / ((‖φ i k‖ : ℝ) : ℂ)) ^ (n i - n' i) = 1 := by
      simp_rw [zpow_sub₀ (hu _)]
      rw [Finset.prod_div_distrib, e, div_self]
      exact Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hu i)
    have e3 := congrArg (· ^ 2) e2
    simp only [← Finset.prod_pow, one_pow] at e3
    rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← e3]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm (n i - n' i), zpow_mul, zpow_natCast, unit_sq _ (hne i), div_zpow]
    simp only [σ, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, RingHom.comp_apply]
    rw [div_eq_mul_inv, ← zpow_neg, neg_sub])
  funext i
  have := congrFun this (Sum.inl i)
  simpa [sub_eq_zero] using this

theorem hasInfQ_inv {L I : Type} [Field L] [NumberField L] [Fintype I] {φ : I → L →+* ℂ} {χ : HChar L} {a : I → ℚ}
    (h : χ.HasInfQ φ a) : (χ⁻¹).HasInfQ φ (-a) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨-n, fun i => by simp [hn], fun k => ?_⟩
  rw [HChar.inf_inv, Units.val_inv_eq_inv_val, h k, ← Finset.prod_inv_distrib]
  simp

theorem embPsi_inj {R : Ranks} (H : Formalism.BasicNotions.Host R) : Function.Injective (embPsi H) := fun _ _ h =>
  Subtype.ext ((factEmb R H).1.1 h)

theorem embPsi_ne_conj {R : Ranks} (H : Formalism.BasicNotions.Host R) (i j : R.Psi) :
    embPsi H i ≠ (starRingEnd ℂ).comp (embPsi H j) := by
  intro h
  have hi : embPsi H i (H.sqd) = Complex.I * ((Real.sqrt H.d : ℝ) : ℂ) :=
    ((factEmb R H).2 _).2 i.2
  have hj : embPsi H j (H.sqd) = Complex.I * ((Real.sqrt H.d : ℝ) : ℂ) :=
    ((factEmb R H).2 _).2 j.2
  rw [h, RingHom.comp_apply, hj, map_mul, Complex.conj_I, Complex.conj_ofReal] at hi
  have h0 : ((Real.sqrt H.d : ℝ) : ℂ) = 0 := by
    have : (2 * Complex.I) * ((Real.sqrt H.d : ℝ) : ℂ) = 0 := by linear_combination -hi
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  have hd : 0 < H.d := H.hyp.2.1.pos
  have : (0 : ℝ) < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  exact this.ne' (by exact_mod_cast h0)

end GlobalTheory.HalfIntChars
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdUnifMulUnitIdl
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr.IdlFact

variable {L : Type} [Field L] [NumberField L]

def valAt (w : HeightOneSpectrum (𝓞 L)) : Ideles L →* WithZero (Multiplicative ℤ) where
  toFun a := Valued.v ((a : AdeleRing (𝓞 L) L).2 w)
  map_one' := by
    show Valued.v (1 : w.adicCompletion L) = 1
    exact map_one _
  map_mul' a b := by
    show Valued.v ((a : AdeleRing (𝓞 L) L).2 w * (b : AdeleRing (𝓞 L) L).2 w) = _
    exact map_mul _ _ _

theorem valAt_apply (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) :
    valAt w a = Valued.v ((a : AdeleRing (𝓞 L) L).2 w) := rfl

theorem valAt_ne_zero (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) : valAt w a ≠ 0 :=
  ((Group.isUnit a).map (valAt w)).ne_zero

theorem valAt_localIdele_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    valAt v (localIdele L v x) = Valued.v (x : v.adicCompletion L) := by
  classical
  have h : ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
    have := Function.update_self (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
      (x : v.adicCompletion L) (fun _ => 1)
    convert this
    rfl
  rw [valAt_apply, h]

theorem valAt_localIdele_ne {v w : HeightOneSpectrum (𝓞 L)} (hw : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    valAt w (localIdele L v x) = 1 := by
  classical
  have h : ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
    have := Function.update_of_ne (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) hw
      (x : v.adicCompletion L) (fun _ => 1)
    convert this
    rfl
  rw [valAt_apply, h, map_one]

theorem finite_valAt_ne_one (a : Ideles L) : {v | valAt v a ≠ 1}.Finite := by
  have hu : IsUnit ((a : AdeleRing (𝓞 L) L).2) :=
    a.isUnit.map (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
  exact (FiniteAdeleRing.isUnit_iff.1 hu).2

open Classical in
theorem valAt_prod (S : Finset (HeightOneSpectrum (𝓞 L))) (n : HeightOneSpectrum (𝓞 L) → ℤ)
    (w : HeightOneSpectrum (𝓞 L)) :
    valAt w (∏ v ∈ S, localIdele L v (atFin v (unif v)) ^ n v) =
      WithZero.exp (-(if w ∈ S then n w else 0)) := by
  rw [map_prod]
  have h1 : ∀ v, v ≠ w → valAt w (localIdele L v (atFin v (unif v)) ^ n v) = 1 := fun v hv => by
    rw [map_zpow, valAt_localIdele_ne hv.symm, one_zpow]
  split_ifs with hw
  · rw [Finset.prod_eq_single_of_mem w hw (fun v _ hv => h1 v hv), map_zpow, valAt_localIdele_self]
    have h2 : Valued.v ((atFin w (unif w) : (w.adicCompletion L)ˣ) : w.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
      unif_spec w
    rw [h2, ← WithZero.exp_zsmul]
    simp
  · rw [Finset.prod_eq_one (fun v hv => h1 v (fun e => hw (e ▸ hv)))]
    simp

end GlobalTheory.Mem.Chr.IdlFact

open Classical in
theorem GlobalTheory.Mem.Chr.exists_prod_unif_mul_unitIdl : ∀ (L : Type) [Field L] [NumberField L] (a : Ideles L), ∃ (S : Finset (HeightOneSpectrum (𝓞 L))) (n : HeightOneSpectrum (𝓞 L) → ℤ) (u : Ideles L), u ∈ unitIdl L ∧ a = (∏ v ∈ S, localIdele L v (atFin v (unif v)) ^ n v) * u ∧ ∀ v, Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = WithZero.exp (-(if v ∈ S then n v else 0)) := by
  intro L _ _ a
  let S := (GlobalTheory.Mem.Chr.IdlFact.finite_valAt_ne_one a).toFinset
  let n : HeightOneSpectrum (𝓞 L) → ℤ := fun v => -WithZero.log (GlobalTheory.Mem.Chr.IdlFact.valAt v a)
  have hv : ∀ v, GlobalTheory.Mem.Chr.IdlFact.valAt v a = WithZero.exp (-(if v ∈ S then n v else 0)) := fun v => by
    split_ifs with h
    · simp only [n, neg_neg]
      exact (WithZero.exp_log (GlobalTheory.Mem.Chr.IdlFact.valAt_ne_zero v a)).symm
    · have : GlobalTheory.Mem.Chr.IdlFact.valAt v a = 1 := by simpa [S] using h
      rw [this]; simp
  refine ⟨S, n, (∏ v ∈ S, localIdele L v (atFin v (unif v)) ^ n v)⁻¹ * a, fun v => ?_, ?_, hv⟩
  · rw [← GlobalTheory.Mem.Chr.IdlFact.valAt_apply, map_mul, map_inv, GlobalTheory.Mem.Chr.IdlFact.valAt_prod, hv v]
    exact inv_mul_cancel₀ WithZero.exp_ne_zero
  · rw [mul_inv_cancel_left]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdFNonnegOfIsInteger
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.Chr.DetOrd

variable {L : Type} [Field L] [NumberField L]

theorem ordF_mul' (w : HeightOneSpectrum (𝓞 L)) (a b : Lˣ) : ordF w (a * b) = ordF w a + ordF w b := by
  have ha : w.valuation L (a : L) ≠ 0 := by simp
  have hb : w.valuation L (b : L) ≠ 0 := by simp
  unfold ordF
  rw [Units.val_mul, map_mul, WithZero.log_mul ha hb]
  ring

theorem ordF_nonneg_of_isInteger (w : HeightOneSpectrum (𝓞 L)) (a : Lˣ)
    (h : IsLocalization.IsInteger (𝓞 L) (a : L)) : 0 ≤ ordF w a := by
  obtain ⟨r, hr⟩ := h
  have ha : w.valuation L (a : L) ≠ 0 := by simp
  have hle : w.valuation L (a : L) ≤ 1 := by
    rw [← hr]; exact w.valuation_le_one r
  have := (WithZero.log_le_log ha one_ne_zero).2 hle
  unfold ordF
  simpa using this

theorem ordF_finite (a : Lˣ) : {w : HeightOneSpectrum (𝓞 L) | ordF w a ≠ 0}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 L) (a : L)).union
    (HeightOneSpectrum.Support.finite (𝓞 L) ((a⁻¹ : Lˣ) : L))).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, not_or, HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hn
  apply hw
  have h0 : w.valuation L (a : L) ≠ 0 := by simp
  have h1 : w.valuation L (a : L) = 1 := by
    refine le_antisymm hn.1 ?_
    have h2 := hn.2
    rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
    exact (inv_le_one₀ (zero_lt_iff.2 h0)).1 h2
  simp [ordF, h1]

theorem isFractional_detSub {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) (hM : M.FG) :
    IsFractional (𝓞 L)⁰ (detSub M) := by
  obtain ⟨a, ha, hint⟩ := Formalism.L2.LamCM.A2.exists_den M hM
  refine ⟨a ^ N, pow_mem ha N, fun b hb => ?_⟩
  induction hb using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨x, hx, rfl⟩ := hd
    have : (a ^ N) • (Matrix.of x).det = (Matrix.of fun i j => a • x i j).det := by
      rw [show (Matrix.of fun i j => a • x i j) = (algebraMap (𝓞 L) L a) • Matrix.of x by
        ext i j; simp [Algebra.smul_def]]
      rw [Matrix.det_smul, Fintype.card_fin, Algebra.smul_def, map_pow]
    rw [this]
    exact Formalism.L2.LamCM.A2.isInteger_det _ fun i j => hint _ (hx i) j
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy => rw [smul_add]; exact IsLocalization.isInteger_add hx hy
  | smul r x _ hx => rw [smul_comm]; exact IsLocalization.isInteger_smul hx

theorem exists_bound {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) :
    ∃ d : Lˣ, ∀ w : HeightOneSpectrum (𝓞 L), ∀ k : Lˣ, (k : L) ∈ A → -ordF w d ≤ ordF w k := by
  obtain ⟨a, ha, hint⟩ := h
  have ha0 : algebraMap (𝓞 L) L a ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero ha
  refine ⟨Units.mk0 _ ha0, fun w k hk => ?_⟩
  have h1 := ordF_nonneg_of_isInteger w (Units.mk0 _ ha0 * k) (by
    have := hint _ hk
    rwa [Algebra.smul_def] at this)
  rw [ordF_mul'] at h1
  linarith

theorem isLeast_ordSub {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A)
    (w : HeightOneSpectrum (𝓞 L)) :
    IsLeast {n | ∃ k : Lˣ, (k : L) ∈ A ∧ ordF w k = n} (ordSub w A) := by
  obtain ⟨d, hd⟩ := exists_bound h
  have hb : BddBelow {n | ∃ k : Lˣ, (k : L) ∈ A ∧ ordF w k = n} :=
    ⟨-ordF w d, by rintro n ⟨k, hk, rfl⟩; exact hd w k hk⟩
  exact ⟨Int.csInf_mem ⟨_, k0, hk0, rfl⟩ hb, fun n hn => csInf_le hb hn⟩

theorem ordSub_finite {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A) :
    {w : HeightOneSpectrum (𝓞 L) | ordSub w A ≠ 0}.Finite := by
  obtain ⟨d, hd⟩ := exists_bound h
  refine ((ordF_finite d).union (ordF_finite k0)).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
  apply hw
  obtain ⟨⟨k, hk, e⟩, hl⟩ := isLeast_ordSub h k0 hk0 w
  have h1 := hl ⟨k0, hk0, rfl⟩
  have h2 := hd w k hk
  omega

theorem det_of_mulVec {N : ℕ} (γ : Matrix (Fin N) (Fin N) L) (x : Fin N → Fin N → L) :
    (Matrix.of fun i => γ.mulVec (x i)).det = γ.det * (Matrix.of x).det := by
  have : (Matrix.of fun i => γ.mulVec (x i)) = Matrix.of x * γ.transpose := by
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [this, Matrix.det_mul, Matrix.det_transpose, mul_comm]

theorem detSub_map {N : ℕ} (γ : Matrix (Fin N) (Fin N) L) (M : Submodule (𝓞 L) (Fin N → L)) :
    detSub (M.map ((Matrix.toLin' γ).restrictScalars (𝓞 L))) =
      (detSub M).map (LinearMap.mulLeft (𝓞 L) γ.det) := by
  unfold detSub
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    choose x hx e using fun i => Submodule.mem_map.1 (hy i)
    refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
    have : y = fun i => γ.mulVec (x i) := funext fun i => by
      rw [← e i]; simp
    rw [this, det_of_mulVec]
    rfl
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨fun i => γ.mulVec (x i), fun i => Submodule.mem_map.2 ⟨x i, hx i, by simp⟩, ?_⟩
    rw [det_of_mulVec]
    rfl

theorem ordSub_map_mul {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A)
    (u : Lˣ) (w : HeightOneSpectrum (𝓞 L)) :
    ordSub w (A.map (LinearMap.mulLeft (𝓞 L) (u : L))) = ordF w u + ordSub w A := by
  obtain ⟨⟨k, hk, e⟩, hl⟩ := isLeast_ordSub h k0 hk0 w
  refine IsLeast.csInf_eq ⟨⟨u * k, Submodule.mem_map.2 ⟨k, hk, rfl⟩, by rw [ordF_mul', e]⟩, ?_⟩
  rintro n ⟨k', hk', rfl⟩
  obtain ⟨y, hy, ey⟩ := Submodule.mem_map.1 hk'
  have ey' : (u : L) * y = k' := ey
  have hy' : ((u⁻¹ * k' : Lˣ) : L) = y := by
    rw [Units.val_mul, ← ey', Units.inv_mul_cancel_left]
  have h1 := hl ⟨u⁻¹ * k', hy' ▸ hy, rfl⟩
  have h2 : ordF w k' = ordF w u + ordF w (u⁻¹ * k') := by
    rw [← ordF_mul', mul_inv_cancel_left]
  omega

end GlobalTheory.Mem.Chr.DetOrd

namespace GlobalTheory.Mem.Chr

open DetOrd

open Classical in
theorem ordSub_detSub_lattice :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (M : Submodule (𝓞 L) (Fin N → L)), M.FG → Submodule.span L (M : Set (Fin N → L)) = ⊤ → {w | ordSub w (detSub M) ≠ 0}.Finite ∧ (∀ w, IsLeast {n | ∃ k : Lˣ, (k : L) ∈ detSub M ∧ ordF w k = n} (ordSub w (detSub M))) ∧ ∀ (γ : Matrix (Fin N) (Fin N) L) (u : Lˣ), γ.det = u → ∀ w, ordSub w (detSub (M.map ((Matrix.toLin' γ).restrictScalars (𝓞 L)))) = ordF w u + ordSub w (detSub M) := by
  intro L _ _ N M hfg hsp
  have hf := isFractional_detSub M hfg
  obtain ⟨x, hx, hd⟩ := Formalism.L2.LamCM.A2.exists_det_ne M hsp
  have hk : ((Units.mk0 _ hd : Lˣ) : L) ∈ detSub M := det_mem_detSub x hx
  refine ⟨ordSub_finite hf _ hk, isLeast_ordSub hf _ hk, fun γ u hu w => ?_⟩
  have e := detSub_map γ M
  have hu' : γ.det = u := by convert hu
  rw [hu'] at e
  have := ordSub_map_mul hf _ hk u w
  rw [← e] at this
  convert this

end GlobalTheory.Mem.Chr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveCharacterOfIsCyclic
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory

theorem _root_.GlobalTheory.exists_heightOneSpectrum_natCast_mem (L : Type*) [Field L] [NumberField L] {p : ℕ}
    (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ v.asIdeal := by
  have hP : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨Q, hQm, hQ⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) (Ideal.span {(p : ℤ)})
      (by
        intro x hx
        rw [RingHom.mem_ker, (algebraMap ℤ (𝓞 L)).injective_int.eq_iff' (map_zero _)] at hx
        simp [hx])
  have hmem : ((p : ℕ) : 𝓞 L) ∈ Q := by
    have : (p : ℤ) ∈ Ideal.under ℤ Q := by
      rw [hQ]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQm.isPrime, ?_⟩, hmem⟩
  rintro rfl
  have : (p : ℤ) ∈ (⊥ : Ideal (𝓞 L)).comap (algebraMap ℤ (𝓞 L)) := by simpa using hmem
  rw [Ideal.mem_comap, Ideal.mem_bot] at this
  exact hp.ne_zero (by simpa using this)

private theorem exists_injective_units_zmod_hom_units_complex (p : ℕ) [Fact p.Prime] :
    ∃ f : (ZMod p)ˣ →* ℂˣ, Function.Injective f := by
  set n := Nat.card (ZMod p)ˣ
  have hn : NeZero n := ⟨Nat.card_pos.ne'⟩
  have hc : Nat.card (ZMod p)ˣ = Nat.card (rootsOfUnity n ℂ) := by
    rw [Complex.card_rootsOfUnity]
  exact ⟨(rootsOfUnity n ℂ).subtype.comp (mulEquivOfCyclicCardEq hc).toMonoidHom,
    Subtype.val_injective.comp (mulEquivOfCyclicCardEq hc).injective⟩

open Classical in
theorem _root_.GlobalTheory.nonempty_piBar_and_omg :
    ∀ (R : _root_.Formalism.BasicNotions.Ranks) (H : _root_.Formalism.BasicNotions.Host R), Nonempty (_root_.Formalism.L2.Host.PiBar H) ∧ Nonempty (_root_.Formalism.L2.Host.Omg H) := by
  intro R H
  refine ⟨⟨⟨fun k => (_root_.GlobalTheory.exists_heightOneSpectrum_natCast_mem H.K (H.g_prime k)).choose,
    fun k => (_root_.GlobalTheory.exists_heightOneSpectrum_natCast_mem H.K (H.g_prime k)).choose_spec⟩⟩, ?_⟩
  have : ∀ k : Fin 2, ∃ f : (ZMod (H.g k))ˣ →* ℂˣ, Function.Injective f := fun k =>
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    exists_injective_units_zmod_hom_units_complex (H.g k)
  exact ⟨⟨fun k => (this k).choose, fun k => (this k).choose_spec⟩⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfRoot
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

theorem CMData.embedding_conj {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    {c : L ≃ₐ[F] L} {I : Type} {φ : I → L →+* ℂ} (h : GlobalTheory.Mem.Chr.CMData F c φ) (ψ : L →+* ℂ) (x : L) :
    ψ (c x) = (starRingEnd ℂ) (ψ x) := by
  have := h.real
  have := h.cplx
  have : Algebra.IsQuadraticExtension F L := { finrank_eq_two' := h.rank }
  have hr : ComplexEmbedding.IsReal (ψ.comp (algebraMap F L)) :=
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) ψ
    (ComplexEmbedding.conjugate ψ) (by
      ext a
      exact (RingHom.congr_fun hr a).symm)
  have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, h.rank]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard
  have hne : σ.symm ≠ 1 := by
    intro e
    have hc : ¬ ComplexEmbedding.IsReal ψ :=
      InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex _)
    apply hc
    rw [ComplexEmbedding.isReal_iff, ← hσ, e]
    rfl
  have e : c = σ.symm := (hy c h.ne).trans (hy _ hne).symm
  rw [e]
  exact RingHom.congr_fun hσ x

open Classical in
theorem normOne_unit_isRoot : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → ∀ k : Lˣ, (k : L) * c (k : L) = 1 → (∀ v : HeightOneSpectrum (𝓞 L), v.valuation L (k : L) = 1) → ∃ m : ℕ, 0 < m ∧ (k : L) ^ m = 1 := by
  intro F L _ _ _ _ _ c I _ φ h k hk hv
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 L) L (k : L) fun v => (hv v).le
  have hi : IsIntegral ℤ (k : L) := ha ▸ a.isIntegral_coe
  obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one L ℂ hi (fun ψ => by
    have h1 := congrArg (fun z => ‖ψ z‖) hk
    simp only [map_mul, h.embedding_conj, map_one, norm_mul, norm_one, RCLike.norm_conj] at h1
    nlinarith [norm_nonneg (ψ (k : L))])
  exact ⟨n, hn, hp⟩

theorem exists_unit_of_root {L : Type} [Field L] [NumberField L] (k : Lˣ) (h : ∃ m : ℕ, 0 < m ∧ (k : L) ^ m = 1) :
    ∃ ζ : (𝓞 L)ˣ, Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L) ζ = k := by
  obtain ⟨m, hm, hk⟩ := h
  have hi : IsIntegral ℤ (k : L) := IsIntegral.of_pow hm (hk ▸ isIntegral_one)
  obtain ⟨X, hX⟩ : ∃ X : 𝓞 L, algebraMap (𝓞 L) L X = k := ⟨⟨k, hi⟩, rfl⟩
  have h1 : X ^ m = 1 := RingOfIntegers.coe_injective (by rw [map_pow, hX, hk, map_one])
  exact ⟨Units.ofPowEqOne X m h1 hm.ne', Units.ext hX⟩

end GlobalTheory.Mem.Chr
end
