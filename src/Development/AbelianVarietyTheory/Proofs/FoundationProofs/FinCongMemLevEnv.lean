module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLatticeDenominatorHeightBoundProof
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsPrimeIdemOfComp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
noncomputable section

namespace GlobalTheory.PrincInLevel

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

theorem exists_entries (S : Subring R) (β x : GL (Fin n) R) (H : Set (Fin n → R)) (N : ℕ)
    (hH : ∀ z, z ∈ H ↔ ∀ i, ((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).mulVec z i ∈ S)
    (hx : ∀ z ∈ H, ∃ y ∈ H, x.1 *ᵥ z - z = N • y) :
    ∃ s : Matrix (Fin n) (Fin n) S, (β⁻¹ * x * β).1 = (1 + N • s).map S.subtype := by
  have h : ∀ j, ∃ c : Fin n → S, ∀ i, (β⁻¹ * x * β).1 i j = (1 : Matrix (Fin n) (Fin n) R) i j + N • (c i : R) := by
    intro j
    have e0 : (β⁻¹).1 *ᵥ (β.1 *ᵥ Pi.single j 1) = Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    obtain ⟨y, hy, e⟩ := hx (β.1 *ᵥ Pi.single j 1) ((hH _).2 fun i => by
      rw [e0, Pi.single_apply]; split_ifs; exacts [one_mem _, zero_mem _])
    refine ⟨fun i => ⟨_, (hH y).1 hy i⟩, fun i => ?_⟩
    have e1 := congrArg (fun v => ((β⁻¹).1 *ᵥ v) i) e
    simp only [Matrix.mulVec_sub, e0, Matrix.mulVec_smul] at e1
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Pi.sub_apply, sub_eq_iff_eq_add'] at e1
    rw [Units.val_mul, Units.val_mul, Matrix.one_apply]
    rw [Pi.single_apply] at e1
    exact e1
  choose c hc using h
  refine ⟨Matrix.of fun i j => c j i, Matrix.ext fun i j => ?_⟩
  rw [hc, Matrix.map_apply, Matrix.add_apply, map_add (f := _), Matrix.smul_apply, map_nsmul, Matrix.one_apply,
    Matrix.one_apply]
  congr 1
  split_ifs <;> simp

theorem exists_int (S : Subring R) (β x : GL (Fin n) R) (H : Set (Fin n → R)) (N : ℕ)
    (hH : ∀ z, z ∈ H ↔ ∀ i, ((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).mulVec z i ∈ S)
    (hx : ∀ z ∈ H, ∃ y ∈ H, x.1 *ᵥ z - z = N • y) (hx' : ∀ z ∈ H, ∃ y ∈ H, (x⁻¹).1 *ᵥ z - z = N • y) :
    ∃ y : GL (Fin n) S, β * Formalism.UG.bc S.subtype y * β⁻¹ = x ∧
      ∀ (k : Type) [CommRing k] (φ : S →+* k), (N : k) = 0 → Formalism.UG.bc φ y = 1 := by
  obtain ⟨s, hs⟩ := exists_entries S β x H N hH hx
  obtain ⟨t, ht⟩ := exists_entries S β x⁻¹ H N hH hx'
  have inj : Function.Injective (fun m : Matrix (Fin n) (Fin n) S => m.map S.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have h1 : (1 + N • s) * (1 + N • t) = 1 := inj <| by
    simp only [Matrix.map_mul, ← hs, ← ht, ← Units.val_mul]
    rw [show β⁻¹ * x * β * (β⁻¹ * x⁻¹ * β) = 1 by group, Matrix.map_one _ (map_zero _) (map_one _)]; rfl
  have h2 : (1 + N • t) * (1 + N • s) = 1 := inj <| by
    simp only [Matrix.map_mul, ← hs, ← ht, ← Units.val_mul]
    rw [show β⁻¹ * x⁻¹ * β * (β⁻¹ * x * β) = 1 by group, Matrix.map_one _ (map_zero _) (map_one _)]; rfl
  refine ⟨⟨_, _, h1, h2⟩, ?_, fun k _ φ hN => ?_⟩
  · have : Formalism.UG.bc S.subtype (⟨_, _, h1, h2⟩ : GL (Fin n) S) = β⁻¹ * x * β := Units.ext hs.symm
    rw [this]; group
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change φ ((1 + N • s) i j) = (1 : Matrix (Fin n) (Fin n) k) i j
    rw [Matrix.add_apply, map_add (f := _), Matrix.smul_apply, map_nsmul, nsmul_eq_mul, hN, zero_mul, add_zero,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

end Ring

section Swap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem swap_mem_hatL (Λ : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E)
    (hz : z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) :
    (fun i => Algebra.TensorProduct.comm F _ E (z i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    have hm : (1 : E) ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E := Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
    have := Submodule.smul_mem (Formalism.L2.Herm.hatL (F := F) Λ) ⟨_, hm⟩ (Submodule.subset_span ⟨x, hx, rfl⟩)
    convert this using 1
    funext i
    change x i ⊗ₜ[F] a = ((1 : E) ⊗ₜ[F] a) * (x i ⊗ₜ[F] 1)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx

theorem smul_mem_hat (Λ : Submodule (𝓞 E) (Fin n → E)) (t : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (ht : t ∈ Formalism.L2.Herm.intAf F E) :
    ∀ y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)),
      (Algebra.TensorProduct.comm F _ E).symm t • y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
  have gen : ∀ t : FiniteAdeleRing (𝓞 F) F ⊗[F] E, (∀ a : FiniteAdeleRing (𝓞 F) F,
      (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ x ∈ Λ,
      t • (fun i => a ⊗ₜ[F] x i) ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) →
      ∀ y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), t • y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
    intro t ht y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz => obtain ⟨a, ha, x, hx, rfl⟩ := hz; exact ht a ha x hx
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  induction ht using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨b, rfl⟩
    · refine gen _ fun a ha x hx => AddSubgroup.subset_closure ⟨a, ha, c • x, Λ.smul_mem c hx, ?_⟩
      funext i
      change ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] algebraMap (𝓞 E) E c) * (a ⊗ₜ[F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Pi.smul_apply, Algebra.smul_def]
    · refine gen _ fun a ha x hx => AddSubgroup.subset_closure
        ⟨b * a, fun v => mul_mem (b.2 v) (ha v), x, hx, ?_⟩
      funext i
      change ((b : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (1 : E)) * (a ⊗ₜ[F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => intro y _; rw [map_zero, zero_smul]; exact zero_mem _
  | one => intro y hy; rwa [map_one, one_smul]
  | add a b _ _ ha hb => intro y hy; rw [map_add (f := _), add_smul]; exact add_mem (ha y hy) (hb y hy)
  | neg a _ ha => intro y hy; rw [map_neg, neg_smul]; exact neg_mem (ha y hy)
  | mul a b _ _ ha hb => intro y hy; rw [map_mul, mul_smul]; exact ha _ (hb y hy)

theorem swap_symm_mem_hat (Λ : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    (fun i => (Algebra.TensorProduct.comm F _ E).symm (z i)) ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩
  | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, map_add (f := _)]; exact add_mem hx hy
  | smul c x _ hx =>
    have := smul_mem_hat Λ c.1 c.2 _ hx
    convert this using 1
    funext i
    exact map_mul (Algebra.TensorProduct.comm F _ E).symm c.1 (x i)

theorem cong_swap (Λ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ)
    (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E))
    (h : ∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), ∃ y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)),
      M *ᵥ z - z = N • y) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∃ y ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      M.map (Algebra.TensorProduct.comm F _ E) *ᵥ z - z = N • y := by
  intro z hz
  obtain ⟨y, hy, e⟩ := h _ (swap_symm_mem_hat Λ z hz)
  refine ⟨_, swap_mem_hatL Λ y hy, funext fun i => ?_⟩
  have := congrArg (Algebra.TensorProduct.comm F _ E) (congrFun e i)
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [Pi.sub_apply, Pi.smul_apply, map_sub, map_nsmul, Matrix.mulVec, dotProduct, map_sum, map_mul,
    AlgEquiv.apply_symm_apply, Matrix.map_apply] using this

theorem swap_mem_UPts (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)) (hg : g ∈ HR (FiniteAdeleRing (𝓞 F) F) σ J) :
    Formalism.UG.bc (Algebra.TensorProduct.comm F _ E).toAlgHom.toRingHom g ∈
      Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
  refine Formalism.UG.Final.BCMem _ _ (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (Formalism.UG.sigR σ _)
    (Algebra.TensorProduct.comm F _ E).toAlgHom.toRingHom (RingHom.ext fun x => ?_) (JR _ J) g hg
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a x => rfl

end Swap

theorem eq_latC {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1) : Λ = GlobalTheory.Member.latC V := by
  obtain ⟨c, -, -, -, h1, h2⟩ := h
  rw [one_pow, Nat.cast_one, ← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq] at h1 h2
  ext x
  exact ⟨fun hx => by simpa using h2 x hx, fun hx => by simpa using h1 x hx⟩


set_option maxHeartbeats 800000 in
theorem finCong_mem_levEnv : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (N : ℕ) (k : GA D V), IsSDFrame V β Λ 1 → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → GlobalTheory.Member.FinCong V N k → (finHom V).rangeRestrict k ∈ (levEnv V β L).J := by
  intro D V β Λ L N k hΛ hN hk
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [eq_latC hΛ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  have hc : ∀ a : GA D V, GlobalTheory.Member.FinCong V N a → ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      ∃ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Lev.finE V a).1 *ᵥ z - z = N • y := by
    intro a ha
    unfold GlobalTheory.Member.FinCong at ha
    rw [hl] at ha
    exact cong_swap Λ N _ ha
  have hc' := hc _ (GlobalTheory.Member.PrincLevel.finCong_inv hk)
  rw [map_inv] at hc'
  obtain ⟨y, hy, hred⟩ := exists_int (Formalism.L2.Herm.intAf D.host.F D.host.E) β (Lev.finE V k)
    (Formalism.L2.Herm.hatL (F := D.host.F) Λ) N hfr (hc k hk) hc'
  have hy' : Formalism.L2.DIV.frGL β y = Lev.finE V k := hy
  have hSt : Lev.finE V k ∈ Formalism.L2.DIV.St β := ⟨y, hy'⟩
  have hr : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
    intro PP hP
    rw [← hy', Formalism.L2.DIV.redFn_frGL]
    refine hred _ _ ?_
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hN PP hP)
  have hU : Lev.finE V k ∈ Formalism.L2.DIV.UA D.sp.cm V.gram :=
    swap_mem_UPts _ _ _ (GlobalTheory.UnitarySplit.finHom_mem V k)
  change Lev.finE V k ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L)
  refine ⟨⟨⟨⟨hU, hSt⟩, ?_⟩, ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => Formalism.L2.DIV.mem_parah.2 ⟨hSt, ?_⟩
    rw [hr PP (Or.inl hP)]; exact one_mem _
  · refine Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => Formalism.L2.DIV.mem_parah.2 ⟨hSt, ?_⟩
    rw [hr PP (Or.inr hP)]; exact one_mem _
  · have e : Formalism.L2.DIV.rTup β L (Lev.finE V k) = 1 := by
      funext PP
      show Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn β PP.1 (Lev.finE V k)) = 1
      rw [hr PP.1 (Or.inl PP.2)]; exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
    show Formalism.L2.DIV.rTup β L (Lev.finE V k) ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 L.Pg L.r))
    rw [e]; exact Subgroup.one_mem _

end GlobalTheory.PrincInLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace HeightProper


omit [NumberField F] [NumberField E] in
theorem repr_map {R R' ι : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (b : Module.Basis ι F E)
    (φ : R →ₐ[F] R') (z : R ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) i =
      φ ((Algebra.TensorProduct.basis R b).repr z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add (f := _), Finsupp.add_apply, hy, hz]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem nnnorm_repr_le_absFin {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (hb : ∀ i, IsIntegral ℤ (b i)) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) (i : ι) :
    ‖(Algebra.TensorProduct.basis (Fv F v) b.traceDual).repr y i‖₊ ≤ absFin F v y := by
  rw [← absBar_algebraMap, algebraMap_basis_repr]
  refine (valBar F v).map_sum_le fun τ _ => ?_
  change absBar F v _ ≤ _
  rw [absBar_mul]
  refine (mul_le_of_le_one_right' ?_).trans (le_absFin F v τ y)
  have := (le_absFin F v τ _).trans (absFin_tmul_le F v 1 (⟨b i, hb i⟩ : 𝓞 E))
  rw [finEmb_tmul, map_one, one_mul, nnnorm_one] at this
  exact this

theorem exists_norm_repr_le {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (w : InfinitePlace F) (c : ℝ) (i : ι) : ∃ B : ℝ, ∀ y : w.Completion ⊗[F] E,
      (∀ τ : EmbOver E w, ‖infEmb τ y‖ ≤ c) →
      ‖(Algebra.TensorProduct.basis w.Completion b.traceDual).repr y i‖ ≤ B := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  let t : (E →ₐ[F] ℂ) → EmbOver E w := fun τ => ⟨τ, RingHom.ext τ.commutes⟩
  have key : ∀ y : w.Completion ⊗[F] E, InfinitePlace.Completion.extensionEmbedding w
      ((Algebra.TensorProduct.basis w.Completion b.traceDual).repr y i) =
      ∑ τ : E →ₐ[F] ℂ, infEmb (t τ) y * τ (b i) := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add (f := _), Finsupp.add_apply, hy, hz, add_mul, Finset.sum_add_distrib]
    | tmul a e =>
      have h : ∀ x : F, InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion x) =
          algebraMap F ℂ x := fun x => by
        rw [AbsoluteValue.Completion.algebraMap_def, InfinitePlace.Completion.extensionEmbedding_coe]
        rfl
      rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul,
        h, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply,
        trace_eq_sum_embeddings, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [infEmb_tmul, map_mul, mul_assoc]; rfl
  refine ⟨∑ τ : E →ₐ[F] ℂ, c * ‖τ (b i)‖, fun y hy => ?_⟩
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), key]
  refine norm_sum_le_of_le _ fun τ _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hy _) (norm_nonneg _)

theorem norm_entry_le_opNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (i j : n) :
    ‖A i j‖ ≤ opNorm A := by
  have h := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j 1)
  have h2 := PiLp.norm_apply_le (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i
  have h3 : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i = A i j := by
    change ∑ k, A i k * (EuclideanSpace.single j (1 : ℂ)) k = _
    simp [Pi.single_apply]
  rw [h3] at h2
  simpa [opNorm] using h2.trans h

theorem exists_compact_adeles (B : InfinitePlace F → ℝ) (c : ℝ≥0) : ∃ C : Set (AF F), IsCompact C ∧
    ∀ a : AF F, (∀ w, ‖evInf F w a‖ ≤ B w) → ∀ d : ℕ, 0 < d → (d : ℝ≥0) ≤ c →
      (∀ v, ‖(d : Fv F v) * evFin F v a‖ ≤ 1) → a ∈ C := by
  have h1 : IsCompact (X := Ainf F) (Set.pi Set.univ fun w : InfinitePlace F => {x : w.Completion | ‖x‖ ≤ B w}) :=
    isCompact_univ_pi fun w => by
      have := (InfinitePlace.Completion.isometry_extensionEmbedding w).isClosedEmbedding.isCompact_preimage
        (isCompact_closedBall 0 (B w))
      convert this using 1
      ext x
      rw [Set.mem_preimage, mem_closedBall_zero_iff,
        (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), Set.mem_setOf_eq]
  have h2 : IsCompact (⋃ d ∈ Finset.range (⌊c⌋₊ + 1), (fun x : Af F => algebraMap F (Af F) (d : F)⁻¹ * x) ''
      {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F}) :=
    (Finset.range _).isCompact_biUnion fun d _ =>
      (GlobalTheory.AdeleCocompact.isCompact_integral F).image (continuous_const.mul continuous_id)
  refine ⟨_, h1.prod h2, fun a ha d hd hdc hv => ⟨fun w _ => ha w, ?_⟩⟩
  refine Set.mem_biUnion (x := d) (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hdc))))
    ⟨(d : Af F) * a.2, fun v => ?_, ?_⟩
  · have := hv v
    rw [← map_natCast (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)] at this
    exact Valued.toNormedField.norm_le_one_iff.1 this
  · have hd0 : (d : F) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
    beta_reduce
    rw [← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, inv_mul_cancel₀ hd0, map_one, one_mul]

theorem exists_compact_entries (n : Type) [Fintype n] [DecidableEq n] (c : ℝ≥0) :
    ∃ C : Set (AF F ⊗[F] E), IsCompact C ∧
      ∀ g : GL n (AF F ⊗[F] E), heightGL F g ≤ c → ∀ i j, g.1 i j ∈ C := by
  classical
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 F) F E
  have hb' : ∀ i, IsIntegral ℤ (b i) := fun i => isIntegral_trans _ (hb i)
  choose B hB using fun (k : s) (w : InfinitePlace F) => exists_norm_repr_le b w c k
  choose C hC hC' using fun k : s => exists_compact_adeles (B k) c
  let e := (Algebra.TensorProduct.basis (AF F) b.traceDual).equivFun
  have he : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  refine ⟨e.symm '' Set.pi Set.univ C, (isCompact_univ_pi hC).image he, fun g hg i j =>
    ⟨e (g.1 i j), fun k _ => ?_, e.symm_apply_apply _⟩⟩
  obtain ⟨d, hd, hdc, hv⟩ := GlobalTheory.SmoothForms.denom_global (fun v => htFin F v (bc (compFin F E v) g))
    (fun v => one_le_htOf _ _) (finite_mulSupport_htFin F g)
  refine hC' k _ (fun w => ?_) d hd ?_ fun v => hv v _ ?_
  · refine (congrArg norm (repr_map b.traceDual (evInf F w) (g.1 i j) k)).symm.trans_le (hB k w _ fun τ => ?_)
    have h := (((normInf_le_iff F w).1 (le_htOf _ _) τ).trans (GlobalTheory.Grow.htInf_le_heightGL F g w)).trans hg
    exact (norm_entry_le_opNorm _ i j).trans (NNReal.coe_le_coe.2 h)
  · exact (hdc.trans (le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => one_le_htOf _ _))).trans hg
  · refine (congrArg nnnorm (repr_map b.traceDual (evFin F v) (g.1 i j) k)).symm.trans_le
      ((nnnorm_repr_le_absFin b hb' v _ k).trans ?_)
    exact (absFin_le_normFin F v (bc (compFin F E v) g).1 i j).trans (le_htOf _ _)

end HeightProper

section GeneralLinearIntegers

variable (F) {n : Type} [Fintype n] [DecidableEq n]

theorem isCompact_heightGL_le (c : ℝ≥0) : IsCompact {g : GL n (AF F ⊗[F] E) | heightGL F g ≤ c} := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  obtain ⟨C, hC, hC'⟩ := HeightProper.exists_compact_entries (F := F) (E := E) n c
  let S : Set (Matrix n n (AF F ⊗[F] E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  have hK := (Units.isClosedEmbedding_embedProduct (α := Matrix n n (AF F ⊗[F] E))).isCompact_preimage
    (hS.prod (hS.image MulOpposite.continuous_op))
  refine hK.of_isClosed_subset (isClosed_le (GlobalTheory.Grow.continuous_heightGL F) continuous_const) fun g hg => ?_
  exact ⟨fun i _ j _ => hC' g hg i j, (g⁻¹).1, fun i _ j _ => hC' g⁻¹ (by rwa [heightGL_inv]) i j, rfl⟩

end GeneralLinearIntegers

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem isClosedEmbedding_matHom_GAd : Topology.IsClosedEmbedding (matHom (AF F) σ J) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  have hcl : IsClosed (HR (AF F) σ J : Set (GL (Fin n) (AF F ⊗[F] E))) := by
    have hv : Continuous fun g : GL (Fin n) (AF F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hv) continuous_const
  exact hcl.isClosedEmbedding_subtypeVal

theorem continuous_height_GAd : Continuous (height σ J) :=
  (GlobalTheory.Grow.continuous_heightGL F).comp (isEmbedding_matHom _ σ J).continuous

theorem isCompact_height_le (c : ℝ≥0) : IsCompact {g : GAd σ J | height σ J g ≤ c} :=
  (isClosedEmbedding_matHom_GAd σ J).isCompact_preimage (isCompact_heightGL_le F c)

theorem height_bddAbove_of_isCompact {K : Set (GAd σ J)} (hK : IsCompact K) :
    ∃ c : ℝ≥0, ∀ g ∈ K, height σ J g ≤ c := by
  obtain ⟨c, hc⟩ := hK.bddAbove_image (continuous_height_GAd σ J).continuousOn
  exact ⟨c, fun g hg => hc ⟨g, hg, rfl⟩⟩

end GlobalTheory.AdelicU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
open MeasureTheory Filter Set GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AutomorphicL2Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G}
  [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {f : G → ℂ}

theorem integrableOn_rmul (F : L2 Γ μ) (y : G) {s : Set (Quot Γ)} (hs : AutomorphicL2Unitary.quotMeasure Γ μ s ≠ ⊤) :
    IntegrableOn (fun q => F (rmul Γ y q)) s (AutomorphicL2Unitary.quotMeasure Γ μ) :=
  (integrableOn_Lp_of_measure_ne_top (R Γ μ y F) (by norm_num) hs).congr (ae_restrict_of_ae (coeFn_R y F))

theorem setIntegral_norm_rmul_le (F : L2 Γ μ) (y : G) {s : Set (Quot Γ)} (hs : AutomorphicL2Unitary.quotMeasure Γ μ s ≠ ⊤) :
    ∫ q in s, ‖F (rmul Γ y q)‖ ∂AutomorphicL2Unitary.quotMeasure Γ μ ≤
      (AutomorphicL2Unitary.quotMeasure Γ μ).real s + ∫ q, ‖F q‖ ^ 2 ∂AutomorphicL2Unitary.quotMeasure Γ μ := by
  have h2 : Integrable (fun q => ‖F q‖ ^ 2) (AutomorphicL2Unitary.quotMeasure Γ μ) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).1 (Lp.memLp F)
  have h3 : Integrable (fun q => ‖F (rmul Γ y q)‖ ^ 2) (AutomorphicL2Unitary.quotMeasure Γ μ) :=
    ((measurePreserving_rmul y).integrable_comp h2.1).2 h2
  have h4 : ∫ q, ‖F (rmul Γ y q)‖ ^ 2 ∂AutomorphicL2Unitary.quotMeasure Γ μ = ∫ q, ‖F q‖ ^ 2 ∂AutomorphicL2Unitary.quotMeasure Γ μ := by
    have h := integral_map (μ := AutomorphicL2Unitary.quotMeasure Γ μ) (measurable_rmul (Γ := Γ) y).aemeasurable
      (f := fun q => ‖F q‖ ^ 2) (by rw [(measurePreserving_rmul y).map_eq]; exact h2.1)
    rw [(measurePreserving_rmul y).map_eq] at h
    exact h.symm
  have h1 : IntegrableOn (fun _ => (1 : ℝ)) s (AutomorphicL2Unitary.quotMeasure Γ μ) := integrableOn_const hs
  calc ∫ q in s, ‖F (rmul Γ y q)‖ ∂AutomorphicL2Unitary.quotMeasure Γ μ
      ≤ ∫ q in s, (1 + ‖F (rmul Γ y q)‖ ^ 2) ∂AutomorphicL2Unitary.quotMeasure Γ μ :=
        integral_mono (integrableOn_rmul F y hs).norm (Integrable.add h1 h3.integrableOn) fun q => by
          beta_reduce
          nlinarith [sq_nonneg (‖F (rmul Γ y q)‖ - 1), norm_nonneg (F (rmul Γ y q))]
    _ = (AutomorphicL2Unitary.quotMeasure Γ μ).real s + ∫ q in s, ‖F (rmul Γ y q)‖ ^ 2 ∂AutomorphicL2Unitary.quotMeasure Γ μ := by
        rw [integral_add h1 h3.integrableOn]
        simp
    _ ≤ _ := by
        rw [← h4]
        exact add_le_add le_rfl (setIntegral_le_integral h3 (.of_forall fun q => by positivity))

variable [SigmaFinite μ]

theorem integrable_prod (hf : Integrable f μ) (F : L2 Γ μ) {s : Set (Quot Γ)} (hs : AutomorphicL2Unitary.quotMeasure Γ μ s ≠ ⊤) :
    Integrable (fun p : Quot Γ × G => f p.2 * F (rmul Γ p.2 p.1)) (((AutomorphicL2Unitary.quotMeasure Γ μ).restrict s).prod μ) := by
  haveI : IsFiniteMeasure ((AutomorphicL2Unitary.quotMeasure Γ μ).restrict s) := isFiniteMeasure_restrict.2 hs
  have hm : AEStronglyMeasurable (fun p : Quot Γ × G => f p.2 * F (rmul Γ p.2 p.1))
      (((AutomorphicL2Unitary.quotMeasure Γ μ).restrict s).prod μ) :=
    hf.1.comp_snd.mul ((Lp.stronglyMeasurable F).comp_measurable measurable_rmul_uncurry).aestronglyMeasurable
  refine (integrable_prod_iff' hm).2 ⟨.of_forall fun y => (integrableOn_rmul F y hs).const_mul (f y), ?_⟩
  refine (hf.norm.mul_const ((AutomorphicL2Unitary.quotMeasure Γ μ).real s + ∫ q, ‖F q‖ ^ 2 ∂AutomorphicL2Unitary.quotMeasure Γ μ)).mono'
    hm.norm.prod_swap.integral_prod_right' (.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  simp only [norm_mul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (setIntegral_norm_rmul_le F y hs) (norm_nonneg _)

theorem ae_integrable (hf : Integrable f μ) (F : L2 Γ μ) :
    ∀ᵐ q ∂AutomorphicL2Unitary.quotMeasure Γ μ, Integrable (fun y => f y * F (rmul Γ y q)) μ := by
  haveI : SigmaFinite (AutomorphicL2Unitary.quotMeasure Γ μ) :=
    SigmaFinite.of_map _ (measurePreserving_sec (Γ := Γ) (μ := μ)).measurable.aemeasurable
      (by rw [measurePreserving_sec.map_eq]; infer_instance)
  refine ae_of_forall_measure_lt_top_ae_restrict _ fun s _ hs => ?_
  haveI : IsFiniteMeasure ((AutomorphicL2Unitary.quotMeasure Γ μ).restrict s) := isFiniteMeasure_restrict.2 hs.ne
  exact (integrable_prod hf F hs.ne).prod_right_ae

theorem coeFn_Rop [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] (hf : Integrable f μ) (F : L2 Γ μ) :
    Rop Γ μ f F =ᵐ[AutomorphicL2Unitary.quotMeasure Γ μ] fun q => ∫ y, f y * F (rmul Γ y q) ∂μ := by
  haveI : SigmaFinite (AutomorphicL2Unitary.quotMeasure Γ μ) :=
    SigmaFinite.of_map _ (measurePreserving_sec (Γ := Γ) (μ := μ)).measurable.aemeasurable
      (by rw [measurePreserving_sec.map_eq]; infer_instance)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top _ (by norm_num) hs.ne)
    (fun s _ hs => (integrable_prod hf F hs.ne).integral_prod_left) fun s hs hfin => ?_
  have hR := isRepOp_Rop (Γ := Γ) hf F
  rw [integral_integral_swap (f := fun q y => f y * F (rmul Γ y q)) (integrable_prod hf F hfin.ne),
    ← L2.inner_indicatorConstLp_one hs hfin.ne, hR.2]
  refine (integral_inner (𝕜 := ℂ) hR.1 _).symm.trans (integral_congr_ae (.of_forall fun y => ?_))
  beta_reduce
  rw [inner_smul_right, L2.inner_indicatorConstLp_one hs hfin.ne, integral_const_mul,
    integral_congr_ae (ae_restrict_of_ae (coeFn_R y F))]

theorem lift_Rop_eq_convR (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    ∀ f : G → ℂ, Integrable f μ → ∀ F : L2 Γ μ,
      (∀ᵐ x ∂μ, Integrable (fun y => f y * lift Γ F (x * y)) μ) ∧
        lift Γ (Rop Γ μ f F) =ᵐ[μ] convR μ f (lift Γ F) :=
  fun _ hf F => ⟨ae_quotMeasure_iff.1 (ae_integrable hf F), ae_quotMeasure_iff.1 (coeFn_Rop hf F)⟩

end GlobalTheory.AutomorphicL2Pointwise
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GlobalTheory.CMPrimeIdele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace EulerTie


variable (F E) in
def finComp : AE F E →+* FiniteAdeleRing (𝓞 E) E := (toFinAd F E).comp (finPart F E)

omit [NumberField E] in
theorem parts_extZero (y : Af F ⊗[F] E) :
    infPart F E (extZero F E y) = 0 ∧ finPart F E (extZero F E y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, and_self]
  | tmul a x => exact ⟨TensorProduct.zero_tmul _ _, rfl⟩
  | add a b ha hb => simp only [map_add (f := _), ha.1, ha.2, hb.1, hb.2, add_zero, and_self]

theorem comp_finComp : Comp (finComp F E) := by
  let c := (Algebra.TensorProduct.comm F E (Af F)).toRingEquiv
  have hι : ∀ x a, ((toFinAd F E).comp c.toRingHom) (x ⊗ₜ[F] a) =
      algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F E a := fun x a => (toFinAd_tmul a x).trans (mul_comm _ _)
  have hs : ∀ y, ((toFinAd F E).comp c.toRingHom) (swapAf F E y) = toFinAd F E y := fun y =>
    congrArg (toFinAd F E) ((Algebra.TensorProduct.comm F (Af F) E).symm_apply_apply y)
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  refine ⟨fun z h1 h2 => ?_, fun s => ?_, fun x => ?_, fun z => ?_, fun a Q => ?_⟩
  · have h3 : finPart F E z = 0 := toFinAd_bijective.1 (h2.trans (map_zero _).symm)
    apply e.injective
    rw [map_zero]
    exact Prod.ext ((he z).1.trans h1) ((he z).2.trans h3)
  · obtain ⟨y, rfl⟩ := (toFinAd_bijective (F := F)).2 s
    exact ⟨_, (parts_extZero y).1, congrArg (toFinAd F E) (parts_extZero y).2⟩
  · change toFinAd F E ((1 : Af F) ⊗ₜ[F] x) = _
    rw [toFinAd_tmul, map_one, one_mul]
  · rw [mem_intAE_iff]
    refine ⟨fun h => ?_, fun h => GlobalTheory.AdeleBaseChange.mem_int_of_map hι ?_⟩
    · have := GlobalTheory.AdeleBaseChange.map_mem_int hι h
      rw [hs] at this
      exact this
    · rw [hs]; exact h
  · change toFinAd F E (a.2 ⊗ₜ[F] (1 : E)) Q = _
    rw [toFinAd_tmul, map_one, mul_one]
    rfl

theorem parts_locIdele (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    infPart F E (locIdele F P u : AE F E) = 1 ∧
      finComp F E (locIdele F P u : AE F E) = (GlobalTheory.CMVal.single P u : FiniteAdeleRing (𝓞 E) E) := by
  have e : (locIdele F P u : AE F E) = 1 - extZero F E 1 +
      extZero F E ((finAdEquiv F E).symm (GlobalTheory.CMVal.single P u : FiniteAdeleRing (𝓞 E) E)) := rfl
  rw [e]
  constructor
  · rw [RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, (parts_extZero _).1, (parts_extZero _).1, sub_zero, add_zero]
  · change toFinAd F E (finPart F E _) = _
    rw [RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, (parts_extZero _).2, (parts_extZero _).2, sub_self, zero_add]
    exact (finAdEquiv F E).apply_symm_apply _

theorem comp_glue {P : HeightOneSpectrum (𝓞 E)} {e : AE F E} (he : IsDelta (finComp F E) P e) (a : AE F E) :
    infPart F E (e * a + (1 - e)) = 1 ∧ finComp F E (e * a + (1 - e)) P = finComp F E a P ∧
      ∀ Q, Q ≠ P → finComp F E (e * a + (1 - e)) Q = 1 := by
  have h : ∀ Q, finComp F E (e * a + (1 - e)) Q = finComp F E e Q * finComp F E a Q + (1 - finComp F E e Q) :=
    fun Q => by rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one]; rfl
  refine ⟨?_, ?_, fun Q hQ => ?_⟩
  · rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, he.1, zero_mul, sub_zero, zero_add]
  · rw [h, he.2.1, one_mul, sub_self, add_zero]
  · rw [h, he.2.2 Q hQ, zero_mul, sub_zero, zero_add]

theorem finComp_locIdele_self (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    finComp F E (locIdele F P u : AE F E) P = u := by
  rw [(parts_locIdele P u).2, GlobalTheory.CMVal.single_self]

theorem finComp_locIdele_ne {P Q : HeightOneSpectrum (𝓞 E)} (h : Q ≠ P) (u : (P.adicCompletion E)ˣ) :
    finComp F E (locIdele F P u : AE F E) Q = 1 := by
  classical
  rw [(parts_locIdele P u).2, GlobalTheory.CMVal.single_apply]
  exact Function.update_of_ne h _ _

theorem glue_eq_locIdele {P : HeightOneSpectrum (𝓞 E)} {e : AE F E} (he : IsDelta (finComp F E) P e) {a : AE F E}
    {u : (P.adicCompletion E)ˣ} (h : finComp F E a P = u) : e * a + (1 - e) = (locIdele F P u : AE F E) := by
  obtain ⟨h1, h2, h3⟩ := comp_glue he a
  refine comp_finComp.ext' (h1.trans (parts_locIdele P u).1.symm) fun Q => ?_
  by_cases hQ : Q = P
  · subst hQ; rw [h2, h, finComp_locIdele_self]
  · rw [h3 Q hQ, finComp_locIdele_ne hQ]

theorem locIdele_int_iff (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    finPart F E (locIdele F P u : AE F E) ∈ intAE F E ↔ Valued.v (u : P.adicCompletion E) ≤ 1 := by
  rw [comp_finComp.2.2.2.1]
  refine ⟨fun h => ?_, fun h Q => ?_⟩
  · have := h P
    rwa [finComp_locIdele_self] at this
  · by_cases hQ : Q = P
    · subst hQ; rw [finComp_locIdele_self]; exact h
    · rw [finComp_locIdele_ne hQ]; exact one_mem _

theorem isUnitAt_iff (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    Formalism.L2.Host.IsUnitAt P u ↔ Valued.v (u : P.adicCompletion E) ≤ 1 ∧
      Valued.v ((u⁻¹ : (P.adicCompletion E)ˣ) : P.adicCompletion E) ≤ 1 := by
  have h0 : 0 < Valued.v (u : P.adicCompletion E) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 u.ne_zero)
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ h0]
  exact le_antisymm_iff

variable {σ : E →ₐ[F] E}

theorem isDelta_of_isPrimeIdem {P : HeightOneSpectrum (𝓞 E)} {e f : AE F E} (h : IsPrimeIdem σ P e f) :
    IsDelta (finComp F E) P e := by
  rcases h with ⟨⟨⟨h1, h2, v, ε, hε, h3⟩, ht⟩, -⟩ | ⟨-, ⟨v, ε, hε, h3⟩, ht⟩
  · refine (tie_iff comp_finComp h1 ?_ P).1 ht
    have : e = e * algebraMap (AF F) (AE F E) ε := by rw [← h3, mul_add, h1, h2, add_zero]
    rw [this, RingHom.map_mul, (place_comp (comp_finComp (E := E)) hε).1, mul_zero]
  · obtain ⟨k0, k1, k2⟩ := place_comp (comp_finComp (E := E)) hε
    rw [← h3] at k0 k1 k2
    refine (tie_iff comp_finComp (comp_finComp.ext' (by rw [RingHom.map_mul, k0, mul_zero]) fun Q => ?_) k0 P).1 ht
    rw [ev_mul]
    by_cases hQ : Q.under (𝓞 F) = v
    · rw [k1 Q hQ, mul_one]
    · rw [k2 Q hQ, mul_zero]

theorem valuation_of_mem_notMem_sq (P : HeightOneSpectrum (𝓞 E)) {a : 𝓞 E} (h1 : a ∈ P.asIdeal)
    (h2 : a ∉ P.asIdeal ^ 2) : P.valuation E (a : E) = WithZero.exp (-1 : ℤ) := by
  have ha : a ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have k1 : P.intValuation a ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]; simpa using h1
  have k2 : ¬ P.intValuation a ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]; exact h2
  have h0 : P.intValuation a ≠ 0 := HeightOneSpectrum.intValuation_ne_zero P a ha
  refine (HeightOneSpectrum.valuation_of_algebraMap P a).trans ?_
  rw [← WithZero.exp_log h0] at k1 k2 ⊢
  rw [WithZero.exp_le_exp] at k1 k2
  congr 1
  omega

theorem exists_of_isUnifIdele {P : HeightOneSpectrum (𝓞 E)} {x : (AE F E)ˣ} (h : IsUnifIdele σ P x) :
    ∃ u, Formalism.L2.Host.IsUnifAt P u ∧ x = locIdele F P u := by
  obtain ⟨e, f, ϖ, he, h1, h2, hx⟩ := h
  have hv : Valued.v (algebraMap E (P.adicCompletion E) (ϖ : E)) = WithZero.exp (-1 : ℤ) :=
    (Formalism.UG.P.levelaf_valued_algebraMap _ _).trans (valuation_of_mem_notMem_sq P h1 h2)
  have h0 : algebraMap E (P.adicCompletion E) (ϖ : E) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  refine ⟨Units.mk0 _ h0, hv, Units.ext (hx.trans (glue_eq_locIdele (isDelta_of_isPrimeIdem he) ?_))⟩
  rw [comp_finComp.2.2.1]
  rfl

end EulerTie

open EulerTie

variable {σ : E →ₐ[F] E}

theorem isUnramAt_iff_unrAt (hσ : IsCMExt F E σ) (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)) :
    IsUnramAt σ χ P ↔ UnrAt χ P := by
  constructor
  · rintro ⟨e, f, he, h⟩ u hu
    obtain ⟨h1, h2⟩ := (isUnitAt_iff P u).1 hu
    have := h (locIdele F P u) (glue_eq_locIdele (isDelta_of_isPrimeIdem he) (finComp_locIdele_self P u)).symm
      ((locIdele_int_iff P u).2 h1) (by rw [← map_inv]; exact (locIdele_int_iff P u⁻¹).2 h2)
    exact (congrArg Circle.toUnits this).trans (map_one _)
  · intro h
    obtain ⟨e, f, -, he⟩ := exists_isPrimeIdem hσ P
    refine ⟨e, f, he, fun x hx h1 h2 => ?_⟩
    let π : AE F E →+* P.adicCompletion E := (evalV E P).toRingHom.comp (finComp F E)
    obtain ⟨u, rfl⟩ : ∃ u, x = locIdele F P u :=
      ⟨Units.map π.toMonoidHom x, Units.ext (hx.trans (glue_eq_locIdele (isDelta_of_isPrimeIdem he) rfl))⟩
    rw [← map_inv] at h2
    have := h u ((isUnitAt_iff P u).2 ⟨(locIdele_int_iff P u).1 h1, (locIdele_int_iff P u⁻¹).1 h2⟩)
    exact Circle.ext (congrArg Units.val this)

theorem chiAt_eq_val (hσ : IsCMExt F E σ) {χ : (AE F E)ˣ →* Circle} {P : HeightOneSpectrum (𝓞 E)} (h : UnrAt χ P) :
    chiAt σ χ P = (val χ P : ℂ) := by
  have hc : IsUnramAt σ χ P ∧ ∃ x, IsUnifIdele σ P x := ⟨(isUnramAt_iff_unrAt hσ χ P).2 h, exists_isUnifIdele hσ P⟩
  obtain ⟨u, hu, e⟩ := exists_of_isUnifIdele hc.2.choose_spec
  rw [chiAt, dite_eq_left hc, e, ← h.locChar_eq_val hu]
  rfl

theorem chiAt_eq_zero (hσ : IsCMExt F E σ) {χ : (AE F E)ˣ →* Circle} {P : HeightOneSpectrum (𝓞 E)}
    (h : ¬ UnrAt χ P) : chiAt σ χ P = 0 :=
  dif_neg fun hc => h ((isUnramAt_iff_unrAt hσ χ P).1 hc.1)

theorem lfac_eq_locL (hσ : IsCMExt F E σ) (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)) (s : ℂ) :
    lfac σ χ P s = locL (charFam χ) P s := by
  unfold lfac locL charFam
  split_ifs with h
  · rw [chiAt_eq_val hσ h, eulerFac_singleton]; rfl
  · rw [chiAt_eq_zero hσ h, eulerFac_zero, zero_mul, sub_zero, inv_one]

end GlobalTheory.LFun

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLocallyFiniteContinuous
open MeasureTheory GlobalTheory.AutomorphicL2Unitary Topology

namespace GlobalTheory.AutomorphicL2KernelContinuous

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  {Γ : Subgroup G} [DiscreteTopology Γ] {f : G → ℂ}

theorem finite_contributing (hc : HasCompactSupport f) {C C' : Set G} (hC : IsCompact C) (hC' : IsCompact C') :
    {γ : Γ | ∃ x ∈ C, ∃ y ∈ C', f (x⁻¹ * γ * y) ≠ 0}.Finite := by
  have hK := (hC.prod (hc.isCompact.prod hC')).image (f := fun p : G × G × G => p.1 * p.2.1 * p.2.2⁻¹) (by fun_prop)
  refine (finite_mem_compact (Γ := Γ) hK).subset ?_
  rintro γ ⟨x, hx, y, hy, h⟩
  exact ⟨(x, x⁻¹ * γ * y, y), ⟨hx, subset_tsupport f h, hy⟩, by simp [mul_assoc]⟩

theorem locallyFinite_support [LocallyCompactSpace G] (hc : HasCompactSupport f) :
    LocallyFinite fun γ : Γ => Function.support fun p : G × G => f (p.1⁻¹ * γ * p.2) := by
  rintro ⟨x, y⟩
  obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
  obtain ⟨C', hC', hy⟩ := exists_compact_mem_nhds y
  refine ⟨C ×ˢ C', prod_mem_nhds hx hy, (finite_contributing hc hC hC').subset ?_⟩
  rintro γ ⟨p, h, h1, h2⟩
  exact ⟨p.1, h1, p.2, h2, h⟩

theorem continuous_kernel [LocallyCompactSpace G] (hf : Continuous f) (hc : HasCompactSupport f) :
    Continuous fun p : G × G => kernel Γ f p.1 p.2 := by
  have h : Continuous fun p : G × G => ∑ᶠ γ : Γ, f (p.1⁻¹ * γ * p.2) :=
    continuous_finsum (fun γ => by fun_prop) (locallyFinite_support hc)
  refine h.congr fun p => ?_
  exact (tsum_eq_finsum (finite_support_kernel hc p.1 p.2)).symm

end GlobalTheory.AutomorphicL2KernelContinuous
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpLiftL2DiscreteQuotientOnCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpLiftL2DiscreteQuotientOnCompact
open MeasureTheory GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal Pointwise

namespace GlobalTheory.AutomorphicL2Local

theorem tsum_indicator_le {G : Type*} [Group G] (Γ : Subgroup G) (C : Set G) (x : G) (a : ℝ≥0∞) :
    ∑' γ : Γ, C.indicator (fun _ => a) (γ * x) ≤ ({γ : Γ | (γ : G) ∈ C * C⁻¹}.encard : ℝ≥0∞) * a := by
  classical
  set T : Set Γ := {γ | (γ : G) * x ∈ C} with hT
  have h1 : (fun γ : Γ => C.indicator (fun _ => a) ((γ : G) * x)) = T.indicator (fun _ => a) := by
    ext γ
    simp [T, Set.indicator_apply]
  rw [h1, ← tsum_subtype T (fun _ => a), ENNReal.tsum_set_const]
  have hle : T.encard ≤ {γ : Γ | (γ : G) ∈ C * C⁻¹}.encard := by
    rcases T.eq_empty_or_nonempty with h | ⟨γ₀, hγ₀⟩
    · simp [h]
    calc T.encard = ((fun γ => γ * γ₀⁻¹) '' T).encard :=
          (Set.InjOn.encard_image (s := T) (f := fun γ : Γ => γ * γ₀⁻¹)
            (fun _ _ _ _ h => mul_right_cancel h)).symm
      _ ≤ _ := by
          refine Set.encard_le_encard ?_
          rintro _ ⟨γ, hγ, rfl⟩
          refine Set.mem_mul.mpr ⟨(γ : G) * x, hγ, ((γ₀ : G) * x)⁻¹, by simpa [hT] using hγ₀, ?_⟩
          simp [mul_assoc]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) bot_le

theorem memLp_restrict_compact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ (F : L2 Γ μ) (C : Set G), IsCompact C → MemLp (lift Γ F) 2 (μ.restrict C) ∧ IntegrableOn (lift Γ F) C μ := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ F C hC
  classical
  have hmeas : AEStronglyMeasurable (lift Γ F) μ :=
    aestronglyMeasurable_quotMeasure_iff_lift.mp (Lp.aestronglyMeasurable F)
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  set N : ℝ≥0∞ := (({γ : Γ | (γ : G) ∈ C * C⁻¹}.encard : ℕ∞) : ℝ≥0∞) with hNdef
  have hN : N ≠ ⊤ := by
    have hfin : {γ : Γ | (γ : G) ∈ C * C⁻¹}.Finite := finite_mem_compact (Γ := Γ) (hC.mul hC.inv)
    simpa [N] using hfin.encard_lt_top.ne
  have hF2 : ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂AutomorphicL2Unitary.quotMeasure Γ μ < ∞ := by
    have := (Lp.memLp F).eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top (Lp.aestronglyMeasurable F)] at this
    simpa using this
  have key : ∫⁻ g, ‖lift Γ F g‖ₑ ^ (2 : ℝ) ∂μ.restrict C < ∞ := by
    rw [← lintegral_indicator hCm,
      lintegral_eq_lintegral_tsum (Γ := Γ) ((hmeas.enorm.pow_const (2 : ℝ)).indicator hCm)]
    calc ∫⁻ q, ∑' γ : Γ, C.indicator (fun g => ‖lift Γ F g‖ₑ ^ (2 : ℝ)) (γ * q.out) ∂AutomorphicL2Unitary.quotMeasure Γ μ
        ≤ ∫⁻ q, N * ‖F q‖ₑ ^ (2 : ℝ) ∂AutomorphicL2Unitary.quotMeasure Γ μ := by
          refine lintegral_mono fun q => ?_
          have e : ∀ γ : Γ, C.indicator (fun g => ‖lift Γ F g‖ₑ ^ (2 : ℝ)) (γ * q.out)
              = C.indicator (fun _ => ‖F q‖ₑ ^ (2 : ℝ)) (γ * q.out) := by
            intro γ
            simp only [Set.indicator_apply]
            split_ifs
            · simp [lift, mk_mul, Quotient.out_eq]
            · rfl
          simp_rw [e]
          exact tsum_indicator_le Γ C q.out _
      _ = N * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂AutomorphicL2Unitary.quotMeasure Γ μ := lintegral_const_mul' _ _ hN
      _ < ∞ := ENNReal.mul_lt_top hN.lt_top hF2
  have hLp : MemLp (lift Γ F) 2 (μ.restrict C) := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hmeas.restrict]
    simpa using key
  refine ⟨hLp, ?_⟩
  have : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  exact hLp.integrable one_le_two

end GlobalTheory.AutomorphicL2Local
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpLiftL2DiscreteQuotientOnCompactStatement
open MeasureTheory GlobalTheory.AutomorphicL2Unitary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memLp_lift_L2DiscreteQuotient_on_compact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ (F : L2 Γ μ) (C : Set G), IsCompact C → MemLp (lift Γ F) 2 (μ.restrict C) ∧ IntegrableOn (lift Γ F) C μ := by
  first | exact @GlobalTheory.AutomorphicL2Local.memLp_restrict_compact | exact GlobalTheory.AutomorphicL2Local.memLp_restrict_compact | (intros; apply GlobalTheory.AutomorphicL2Local.memLp_restrict_compact <;> assumption)
end
end
