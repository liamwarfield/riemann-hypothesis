module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.GraphHeightLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactAdelesRationalPointsFiniteEventuallyZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactAdelesRationalPointsFiniteEventuallyZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

namespace GlobalTheory.Eis.Conv.Discr

open Filter Topology

section Abstract

variable {A E : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [Field E]
  (ι : E →+* A)

theorem finite_of_isCompact (h : ∃ U ∈ 𝓝 (0 : A), ∀ x : E, ι x ∈ U → x = 0) {Ω : Set A}
    (hΩ : IsCompact Ω) : {x : E | ι x ∈ Ω}.Finite := by
  obtain ⟨U, hU, hx⟩ := h
  refine hΩ.induction_on (p := fun s => {x : E | ι x ∈ s}.Finite) (by simp)
    (fun s t hst ht => ht.subset fun x hx => hst hx)
    (fun s t hs ht => (hs.union ht).subset fun x hx => hx) fun a _ => ?_
  have hc : ContinuousAt (fun p : A × A => p.1 - p.2) (a, a) := by fun_prop
  have h1 : (fun p : A × A => p.1 - p.2) ⁻¹' U ∈ 𝓝 (a, a) :=
    hc.preimage_mem_nhds (by simpa using hU)
  rw [nhds_prod_eq, Filter.mem_prod_self_iff] at h1
  obtain ⟨V, hV, hVU⟩ := h1
  refine ⟨V, mem_nhdsWithin_of_mem_nhds hV, Set.Subsingleton.finite fun x hx' y hy => ?_⟩
  refine sub_eq_zero.1 (hx _ ?_)
  rw [map_sub]
  exact hVU (Set.mk_mem_prod hx' hy)

theorem eventually_eq_zero [T2Space A] (h : ∃ U ∈ 𝓝 (0 : A), ∀ x : E, ι x ∈ U → x = 0)
    {Ω : Set A} (hΩ : IsCompact Ω) {s ε : A} (hs : Tendsto (fun m : ℕ => s ^ m) atTop (𝓝 ε))
    (hε : ¬ IsUnit ε) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, ι x = s ^ m * ω → x = 0 := by
  have hK : IsCompact ((fun p : A × A => p.1 * p.2) ''
      (insert ε (Set.range fun m : ℕ => s ^ m) ×ˢ Ω)) :=
    (hs.isCompact_insert_range.prod hΩ).image (by fun_prop)
  have hfin := finite_of_isCompact ι h hK
  have hev : ∀ x : E, ∀ᶠ m : ℕ in atTop, ∀ ω ∈ Ω, ι x = s ^ m * ω → x = 0 := by
    intro x
    by_cases hx : x = 0
    · exact Eventually.of_forall fun _ _ _ _ => hx
    have h1 : ∀ᶠ t in 𝓝 ε, ∀ ω ∈ Ω, ι x ≠ t * ω := by
      refine hΩ.eventually_forall_of_forall_eventually (P := fun t ω => ι x ≠ t * ω)
        fun ω _ => ?_
      have ho : IsOpen {p : A × A | ι x ≠ p.1 * p.2} :=
        isOpen_ne_fun continuous_const (by fun_prop)
      refine ho.mem_nhds fun he => hε ?_
      have hu : IsUnit (ε * ω) := by
        have := (IsUnit.mk0 x hx).map ι
        rwa [he] at this
      exact isUnit_of_mul_isUnit_left hu
    filter_upwards [hs.eventually h1] with m hm ω hω he
    exact absurd he (hm ω hω)
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 ((eventually_all_finite hfin).2 fun x _ => hev x)
  refine ⟨m₀, fun m hm ω hω x hx => hm₀ m hm x ?_ ω hω hx⟩
  exact ⟨(s ^ m, ω), ⟨Or.inr ⟨m, rfl⟩, hω⟩, hx.symm⟩

end Abstract

theorem tendsto_halfInf_pow (F : Type) [Field F] [NumberField F] :
    Tendsto (fun m : ℕ => (halfInf F).1 ^ m) atTop (𝓝 ((0, 1) : AF F)) := by
  have h1 : Tendsto (fun m : ℕ => (algebraMap F (Ainf F) 2⁻¹) ^ m) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun v => ?_
    have h : ‖algebraMap F (Ainf F) 2⁻¹ v‖ < 1 := by
      rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]
      change v (2⁻¹ : F) < 1
      rw [← InfinitePlace.norm_embedding_eq, map_inv₀, map_ofNat, norm_inv]
      norm_num
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one h
  have h2 : Tendsto (fun m : ℕ => (1 : FiniteAdeleRing (𝓞 F) F) ^ m) atTop (𝓝 1) := by
    simp only [one_pow]
    exact tendsto_const_nhds
  exact h1.prodMk_nhds h2

theorem finite_and_eventually_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Ω : Set (AF F ⊗[F] E)), IsCompact Ω → {x : E | inclR (F := F) (AF F) x ∈ Ω}.Finite ∧ ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, inclR (F := F) (AF F) x = (halfE F E).1 ^ m * ω → x = 0 := by
  intro F E _ _ _ _ _ Ω hΩ
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  have h := GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)
  refine ⟨finite_of_isCompact _ h hΩ, eventually_eq_zero _ h hΩ
    (ε := algebraMap (AF F) (AF F ⊗[F] E) (0, 1)) ?_ fun hu => ?_⟩
  · have hc : Continuous (algebraMap (AF F) (AF F ⊗[F] E)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
    have := (hc.tendsto _).comp (tendsto_halfInf_pow F)
    refine this.congr fun m => ?_
    exact map_pow (algebraMap (AF F) (AF F ⊗[F] E)) _ m
  · have h0 : algebraMap (AF F) (AF F ⊗[F] E) (0, 1) * algebraMap (AF F) (AF F ⊗[F] E) (1, 0) = 0 := by
      refine (map_mul (algebraMap (AF F) (AF F ⊗[F] E)) _ _).symm.trans ?_
      refine (congrArg (algebraMap (AF F) (AF F ⊗[F] E)) ?_).trans (map_zero _)
      exact Prod.ext (zero_mul _) (mul_zero _)
    have h1 := hu.mul_right_eq_zero.1 h0
    have hinj : Function.Injective (algebraMap (AF F) (AF F ⊗[F] E)) :=
      Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
    have h2 : ((1, 0) : AF F) = 0 := hinj (h1.trans (map_zero _).symm)
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h3 : (1 : v.Completion) = 0 := congrFun (congrArg Prod.fst h2) v
    exact one_ne_zero h3

end GlobalTheory.Eis.Conv.Discr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactAdelesRationalPointsFiniteEventuallyZeroStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_adeles_rational_points_finite_eventually_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Ω : Set (AF F ⊗[F] E)), IsCompact Ω → {x : E | inclR (F := F) (AF F) x ∈ Ω}.Finite ∧ ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, inclR (F := F) (AF F) x = (halfE F E).1 ^ m * ω → x = 0 := by
  first | exact @GlobalTheory.Eis.Conv.Discr.finite_and_eventually_eq_zero | exact GlobalTheory.Eis.Conv.Discr.finite_and_eventually_eq_zero | (intros; apply GlobalTheory.Eis.Conv.Discr.finite_and_eventually_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignFrameUnitaryIso
open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.FrameIsoReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

theorem cT_star (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; rfl

theorem signFrame_map (h : IsCMExt F E σ) (τ : EmbOver E w) {ε : Fin n → Bool}
    {b : GL (Fin n) (w.Completion ⊗[F] E)} (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) :
    (b.1.map (infEmb τ))ᴴ * J.map τ.1 * b.1.map (infEmb τ) = Formalism.REAL.Jm ε := by
  have h1 : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1 * JR w.Completion J * b.1).map (infEmb τ) =
      (Matrix.diagonal fun i => if ε i then (1 : w.Completion ⊗[F] E) else -1).map (infEmb τ) :=
    congrArg (fun M => M.map (infEmb τ)) hb
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero _)] at h1
  have h2 : (JR w.Completion J).map (infEmb τ) = J.map τ.1 := by ext r s; simp [JR, inclR]
  have h3 : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1).map (infEmb τ) =
      (b.1.map (infEmb τ))ᴴ := by
    ext i j; exact (infEmb_sigR h τ _).symm
  rw [h2, h3] at h1
  rw [h1, Formalism.REAL.Jm]
  congr 1; funext i; split_ifs <;> simp

section Frame

variable (σ J) (h : IsCMExt F E σ) (τ : EmbOver E w) (ε : Fin n → Bool) (b : GL (Fin n) (w.Completion ⊗[F] E))

abbrev fB : Matrix (Fin n) (Fin n) ℂ := b.1.map (infEmb τ)

abbrev fBi : Matrix (Fin n) (Fin n) ℂ := (b⁻¹).1.map (infEmb τ)

theorem fBi_mul : fBi τ b * fB τ b = 1 := by
  rw [fBi, fB, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem fB_mul : fB τ b * fBi τ b = 1 := by
  rw [fBi, fB, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem inFrame_eq (g : GArch σ J w) :
    GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g = fBi τ b * (archEquiv J h τ g).1.1 * fB τ b := by
  rw [archEquiv_val]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame, Units.val_mul, Matrix.map_mul]

include h in
theorem isEmbedding_inFrame : Topology.IsEmbedding (GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b) := by
  have e : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b =
      (fun x : Matrix (Fin n) (Fin n) ℂ => fBi τ b * x * fB τ b) ∘ GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ) := by
    funext g
    exact (inFrame_eq σ J h τ b g).trans rfl
  have hc : Topology.IsEmbedding fun x : Matrix (Fin n) (Fin n) ℂ => fBi τ b * x * fB τ b :=
    Function.LeftInverse.isEmbedding (f := fun x => fB τ b * x * fBi τ b) (fun x => by
      simp only [← mul_assoc, fB_mul, one_mul]; rw [mul_assoc, fB_mul, mul_one])
      ((continuous_const.mul continuous_id).mul continuous_const)
      ((continuous_const.mul continuous_id).mul continuous_const)
  rw [e]
  exact hc.comp (GlobalTheory.Orb.isEmbedding_archMat J h τ)

variable {ε}

include h in
theorem inFrame_mem (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) (g : GArch σ J w) :
    Formalism.REAL.inUJ ε (GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g) := by
  have hS : (fB τ b)ᴴ * J.map τ.1 * fB τ b = Formalism.REAL.Jm ε := signFrame_map h τ hb
  have hA : ((archEquiv J h τ g).1.1)ᴴ * J.map τ.1 * (archEquiv J h τ g).1.1 = J.map τ.1 := by
    rw [← cT_star]; exact (archEquiv J h τ g).2
  rw [Formalism.REAL.inUJ, inFrame_eq σ J h]
  set A := (archEquiv J h τ g).1.1
  set T := J.map τ.1
  set B := fB τ b
  set Bi := fBi τ b
  have hT : Biᴴ * (Bᴴ * T * B) * Bi = T := by
    have : Biᴴ * (Bᴴ * T * B) * Bi = (B * Bi)ᴴ * T * (B * Bi) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, fB_mul, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  calc (Bi * A * B)ᴴ * Formalism.REAL.Jm ε * (Bi * A * B)
      = Bᴴ * Aᴴ * (Biᴴ * (Bᴴ * T * B) * Bi) * A * B := by
        rw [← hS]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Bᴴ * (Aᴴ * T * A) * B := by rw [hT]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hA, hS]

def hom0 : GArch σ J w →* (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  (Units.map (infEmb τ).mapMatrix.toMonoidHom).comp ((MulAut.conj b⁻¹).toMonoidHom.comp (matHom _ σ J))

theorem coe_archimedeanFrameConjMatrixHom (g : GArch σ J w) : ((hom0 σ J τ b g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
    GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g := by
  simp [hom0, GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame, MulAut.conj_apply]

include h in
theorem exists_inFrame_eq (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) (a : Formalism.REAL.UJ ε) :
    ∃ g : GArch σ J w, GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g = ((a : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
  have hS : (fB τ b)ᴴ * J.map τ.1 * fB τ b = Formalism.REAL.Jm ε := signFrame_map h τ hb
  let bU : (Matrix (Fin n) (Fin n) ℂ)ˣ := Units.map (infEmb τ).mapMatrix.toMonoidHom b
  have hbU : (bU : Matrix (Fin n) (Fin n) ℂ) = fB τ b := rfl
  have hbUi : ((bU⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = fBi τ b := by
    rw [← map_inv]; rfl
  let yU : (Matrix (Fin n) (Fin n) ℂ)ˣ := bU * (a : (Matrix (Fin n) (Fin n) ℂ)ˣ) * bU⁻¹
  set x := ((a : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  have hx : xᴴ * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε := a.2
  have hy : (yU : Matrix (Fin n) (Fin n) ℂ) = fB τ b * x * fBi τ b := by
    simp only [yU, Units.val_mul, hbU, hbUi, x]
  set T := J.map τ.1
  set B := fB τ b
  set Bi := fBi τ b
  have hT : Biᴴ * (Bᴴ * T * B) * Bi = T := by
    have : Biᴴ * (Bᴴ * T * B) * Bi = (B * Bi)ᴴ * T * (B * Bi) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, fB_mul, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hmem : yU ∈ Formalism.UG.UJ (starRingEnd ℂ) T := by
    change Formalism.UG.cT (starRingEnd ℂ) (yU : Matrix (Fin n) (Fin n) ℂ) * T * (yU : Matrix (Fin n) (Fin n) ℂ) = T
    rw [cT_star, hy]
    calc (B * x * Bi)ᴴ * T * (B * x * Bi) = Biᴴ * (xᴴ * (Bᴴ * T * B) * x) * Bi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = T := by rw [hS, hx, ← hS, hT]
  refine ⟨(archEquiv J h τ).symm ⟨yU, hmem⟩, ?_⟩
  rw [inFrame_eq σ J h, MulEquiv.apply_symm_apply]
  change Bi * (yU : Matrix (Fin n) (Fin n) ℂ) * B = x
  rw [hy]
  simp only [← Matrix.mul_assoc, fBi_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, fBi_mul, Matrix.mul_one, Matrix.one_mul]

def frameHom (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) : GArch σ J w →* Formalism.REAL.UJ ε :=
  (hom0 σ J τ b).codRestrict _ fun g => by
    change Formalism.REAL.inUJ ε _
    rw [coe_archimedeanFrameConjMatrixHom]; exact inFrame_mem σ J h τ b hb g

theorem frameHom_val (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) (g : GArch σ J w) :
    Formalism.REAL.coeMatrixAlt ε (frameHom σ J h τ b hb g) = GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g := coe_archimedeanFrameConjMatrixHom σ J τ b g

theorem frameHom_bijective (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) : Function.Bijective (frameHom σ J h τ b hb) := by
  refine ⟨fun g g' e => (isEmbedding_inFrame σ J h τ b).injective ?_, fun a => ?_⟩
  · rw [← frameHom_val σ J h τ b hb, ← frameHom_val σ J h τ b hb, e]
  · obtain ⟨g, hg⟩ := exists_inFrame_eq σ J h τ b hb a
    exact ⟨g, Formalism.REAL.injective_coeMatrix ε ((frameHom_val σ J h τ b hb g).trans hg)⟩

def frameEquiv (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) : GArch σ J w ≃ₜ* Formalism.REAL.UJ ε :=
  { MulEquiv.ofBijective _ (frameHom_bijective σ J h τ b hb) with
    continuous_toFun := ((Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding).continuous_iff.2
      ((isEmbedding_inFrame σ J h τ b).continuous.congr fun g => (frameHom_val σ J h τ b hb g).symm)
    continuous_invFun := (isEmbedding_inFrame σ J h τ b).continuous_iff.2 ((Formalism.REAL.continuous_coeMatrix ε).congr fun x => by
      have := frameHom_val σ J h τ b hb ((MulEquiv.ofBijective _ (frameHom_bijective σ J h τ b hb)).symm x)
      exact (congrArg (Formalism.REAL.coeMatrixAlt ε)
        ((MulEquiv.ofBijective _ (frameHom_bijective σ J h τ b hb)).apply_symm_apply x).symm).trans this) }

end Frame

end GlobalTheory.FrameIsoReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaKernelFiniteAdelicLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaKernelFiniteAdelicLaws
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl.KernLaws

theorem exists_finite_lift {D : D7} (V : HSp D) (q : Bridge.Gf V) : ∃ κ ∈ GfC V, fin V κ = q := by
  obtain ⟨_, g, rfl⟩ := q
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 (finHom V g)
  exact ⟨⟨k, (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ ((h1 _).1 g.2).2⟩⟩, k1, Subtype.ext k2⟩

theorem fin_mul {D : D7} (V : HSp D) (a b : GA D V) : fin V a * fin V b = fin V (a * b) :=
  (map_mul (finHom V).rangeRestrict a b).symm

theorem ratF_eq {D : D7} (V : HSp D) (γ : GQ V) : Bridge.ratF V γ = fin V γ := rfl

theorem lift_of_mem_J {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {κ : GA D V}
    (hκ : κ ∈ GfC V) (hk : fin V κ ∈ (levEnv V β L).J) :
    IsLevelLift V β L 1 κ ∧ ((((levEnv V β L).χ ⟨_, hk⟩)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  refine ⟨⟨hκ, hk.1, Subgroup.mem_bot.1 hk.2⟩, ?_⟩
  unfold levChi
  rw [← levFn_flag1, Units.val_inv_eq_inv_val]
  rfl

theorem exists_lift_J {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J) : ∃ κ, fin V κ = k ∧
    IsLevelLift V β L 1 κ ∧ ((((levEnv V β L).χ k)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  obtain ⟨k, hk⟩ := k
  obtain ⟨κ, hκ, rfl⟩ := exists_finite_lift V k
  exact ⟨κ, rfl, lift_of_mem_J V β L hκ hk⟩

theorem finE_of_fin {D : D7} (V : HSp D) {κ : GA D V} {x : Bridge.Gf V} (e : fin V κ = x) :
    finE V κ = Formalism.UG.bc (swapAE D) (x : GL _ _) := by
  have : finHom V κ = x.1 := congrArg Subtype.val e
  rw [finE_eq, this]

theorem exists_lift_Q {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).Q) : ∃ κ, fin V κ = k ∧
    IsLevelLift V β L (rTup β L (Formalism.UG.bc (swapAE D) ((k : Bridge.Gf V) : GL _ _))) κ ∧
      ((((levEnv V β L).ch k)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  obtain ⟨κ, hκ, e⟩ := exists_finite_lift V k.1
  have e' := finE_of_fin V e
  refine ⟨κ, e, ⟨hκ, ?_, congrArg (rTup β L) e'⟩, ?_⟩
  · rw [e']
    exact k.2.1
  · have e2 : (levEnv V β L).ch k = levFn β (flagL L) (finE V κ) := (congrArg (levFn β (flagL L)) e').symm
    rw [Units.val_inv_eq_inv_val, e2, levChi]

theorem lift_one {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsLevelLift V β L 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

theorem exists_actL {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (g0 : G0 L.Pg L.r) (hex : ∃ κ, IsLevelLift V β L g0 κ) : ∃ κ, IsLevelLift V β L g0 κ ∧
      ∀ F h, actL V β L g0 F h = (levChi V β (flagL L) κ)⁻¹ * F (h * κ) := by
  refine ⟨hex.choose, hex.choose_spec, fun F h => ?_⟩
  change actG0 V β L g0 F h = _
  unfold actG0
  rw [dite_eq_left hex]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)

theorem kernA_apply (h : GA D (Vc D i)) (w : (R.cV i).W) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    kernA R i t h w v g =
      Datum.thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w))) := rfl

theorem kernA_mul_real (hio : R.thP_ioP) (h : GA D (Vc D i)) {u : GA D (Vc D i)} (hu : u ∈ GinfC (Vc D i)) :
    kernA R i t (h * u) = kernA R i t h := by
  ext w v g
  rw [kernA_apply, kernA_apply]
  unfold Datum.thetaKO
  rw [show ((h * u, g) : GA D (Vc D i) × GA D (Wc D i)) = (h, g) * (u, 1) from Prod.ext rfl (mul_one g).symm,
    map_mul, Module.End.mul_apply, (hio i t).1 u hu, ← Module.End.mul_apply, ← map_mul, mul_inv_rev,
    mul_inv_cancel_left]

theorem kern_fin (hio : R.thP_ioP) (h : GA D (Vc D i)) : kern R i t (fin (Vc D i) h) = kernA R i t h := by
  unfold kern
  have e := (MonoidHom.mem_range.1 (fin (Vc D i) h).2).choose_spec
  generalize (MonoidHom.mem_range.1 (fin (Vc D i) h).2).choose = h' at e
  have hu : h⁻¹ * h' ∈ GinfC (Vc D i) := by
    change finHom (Vc D i) (h⁻¹ * h') = 1
    rw [map_mul, map_inv, e]
    exact inv_mul_cancel _
  rw [← kernA_mul_real R i t hio h hu, mul_inv_cancel_left]

theorem kernA_rat (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (γ : GQ (Vc D i)) (h : GA D (Vc D i)) (w : (R.cV i).W) :
    kernA R i t (γ * h) ((R.cV i).ρ γ w) = kernA R i t h w := by
  funext v g
  rw [kernA_apply, kernA_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ (hω i t) _
    (hpt i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w)))).1 γ γ.2 1 (one_mem _) h g
  rwa [one_mul] at this

theorem kernA_eigen (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta)
    {κ : GA D (Vc D i)} (hκ : κ ∈ GfC (Vc D i)) {κ' : GA D (Wc D i)} (hκ' : κ' ∈ GfC (Wc D i)) {c : ℂ}
    (e : R.ωP i t (κ, κ') (R.vP i t) = c • R.vP i t) (h : GA D (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    kernA R i t (h * κ) w v (g * κ') = c * kernA R i t h w v g := by
  rw [kernA_apply, kernA_apply, mul_inv_rev, map_mul, (hc i).1 _ (inv_mem hκ), one_mul]
  exact (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ (hω i t) _ (hpt i t _)).2 κ κ' c
    (GlobalTheory.FiniteFock.om_pureTensorO_of_finite _ _ _ _ _ _ _ hθ (hω i t) _ _ _ _ _ (hpt i t) κ hκ κ' hκ' c e _) h g

theorem levChi_flag_datWp (κ' : GA D (Wc D i)) : levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) κ' = 1 := by
  have h2 : ext1 (flagL (R.datWp i R.triv)).P.H (flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (flagL (R.datWp i R.triv)) (finE (Wc D i) κ')) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2, show (flagL (R.datWp i R.triv)).s = 0 from rfl, Finset.range_zero,
    show (flagL (R.datWp i R.triv)).Q = ∅ from rfl, Finset.prod_empty]
  simp only [Finset.prod_empty, Finset.prod_const_one, mul_one, Units.val_one]

theorem kern_rat (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP) (γ : GQ (Vc D i)) (h : Bridge.Gf (Vc D i))
    (w : (R.cV i).W) : kern R i t (Bridge.ratF (Vc D i) γ * h) ((R.cV i).coef.ρ γ w) = kern R i t h w := by
  obtain ⟨h', -, e⟩ := exists_finite_lift (Vc D i) h
  have e1 : kern R i t (Bridge.ratF (Vc D i) γ * h) = kernA R i t (γ * h') := by
    rw [← e, ratF_eq, fin_mul, kern_fin R i t hio]
  have e2 : kern R i t h = kernA R i t h' := by rw [← e, kern_fin R i t hio]
  rw [e1, e2]
  exact kernA_rat R i t hω hpt γ h' w

theorem kern_eigen (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP)
    {κ : GA D (Vc D i)} (hκ : κ ∈ GfC (Vc D i)) {κ' : GA D (Wc D i)} (hκ' : κ' ∈ GfC (Wc D i)) {c : ℂ}
    (e : R.ωP i t (κ, κ') (R.vP i t) = c • R.vP i t) (h : Bridge.Gf (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    kern R i t (h * fin (Vc D i) κ) w v (g * κ') = c * kern R i t h w v g := by
  obtain ⟨h', -, e0⟩ := exists_finite_lift (Vc D i) h
  have e1 : kern R i t (h * fin (Vc D i) κ) = kernA R i t (h' * κ) := by
    rw [← e0, fin_mul, kern_fin R i t hio]
  have e2 : kern R i t h = kernA R i t h' := by rw [← e0, kern_fin R i t hio]
  rw [e1, e2]
  exact kernA_eigen R i t hθ hc hω hpt hκ hκ' e h' w v g

theorem eq_smul_of_mul_one {X Y : Type} [Monoid Y] (F F' : X → Y → ℂ) (c : ℂ) (h : ∀ v g, F v (g * 1) = c * F' v g) :
    F = c • F' := by
  funext v g
  rw [← mul_one g, h, mul_one]
  rfl

theorem eq_smul_of_mul {Y : Type} [Monoid Y] (B F F' : Y → ℂ) (a c : ℂ) (y : Y) (ha : a = 1) (h1 : ∀ g, B g = a⁻¹ * F (g * y))
    (h : ∀ g, F (g * y) = c * F' g) : B = c • F' := by
  funext g
  rw [h1, ha, inv_one, one_mul, h]
  rfl

theorem kern_level (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP)
    (hD : DatumType R i t) (h : Bridge.Gf (Vc D i)) (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) (w : (R.cV i).W) :
    kern R i t (h * k) w = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k)⁻¹ : ℂˣ) : ℂ) • kern R i t h w := by
  obtain ⟨κ, e1, l1, e2⟩ := exists_lift_J (Vc D i) (R.βV i) (R.datVt i t) k
  rw [e2, ← e1]
  exact eq_smul_of_mul_one _ _ _ (kern_eigen R i t hθ hc hω hpt hio l1.1 (GfC (Wc D i)).one_mem
    (hD 1 κ 1 l1 (lift_one _ (R.βW i) (R.datWp i R.triv))) h w)

theorem kern_act (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP)
    (hD : DatumType R i t) (g0 : G0 R.Pg D.R.r) (q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q)
    (hg : g0 = rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _)))
    (hex : ∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ') (h : Bridge.Gf (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 (kern R i t (h * q) w v) =
      ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q)⁻¹ : ℂˣ) : ℂ) • kern R i t h w v := by
  refine (exists_lift_Q (Vc D i) (R.βV i) (R.datVt i t) q).elim fun κ H => ?_
  refine (exists_actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 hex).elim fun κ' H' => ?_
  have l1 : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ := ⟨H.2.1.1, H.2.1.2.1, H.2.1.2.2.trans hg.symm⟩
  have := kern_eigen R i t hθ hc hω hpt hio l1.1 H'.1.1 (hD g0 κ κ' l1 H'.1) h w v
  rw [H.2.2, ← H.1]
  exact eq_smul_of_mul _ _ _ _ _ κ' (levChi_flag_datWp R i κ') (H'.2 _) this

end GlobalTheory.TraceIncl.KernLaws

namespace GlobalTheory.TraceIncl

open KernLaws

theorem kern_laws : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0), R.models_inf → R.models_cV → R.thP_ωP → R.thP_pt_theta → R.thP_ioP → GlobalTheory.TraceIncl.DatumType R i t → (∀ h, GlobalTheory.TraceIncl.kern R i t (fin (Vc D i) h) = GlobalTheory.TraceIncl.kernA R i t h) ∧ (∀ (γ : GQ (Vc D i)) h w, GlobalTheory.TraceIncl.kern R i t (Bridge.ratF (Vc D i) γ * h) ((R.cV i).coef.ρ γ w) = GlobalTheory.TraceIncl.kern R i t h w) ∧ (∀ h (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) w, GlobalTheory.TraceIncl.kern R i t (h * k) w = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k)⁻¹ : ℂˣ) : ℂ) • GlobalTheory.TraceIncl.kern R i t h w) ∧ ∀ (g0 : G0 R.Pg D.R.r) (q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q), g0 = rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _)) → (∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ') → ∀ h w v, actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 (GlobalTheory.TraceIncl.kern R i t (h * q) w v) = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q)⁻¹ : ℂˣ) : ℂ) • GlobalTheory.TraceIncl.kern R i t h w v := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i t hθ hc hω hpt hio hD
  exact ⟨kern_fin R i t hio, kern_rat R i t hω hpt hio, kern_level R i t hθ hc hω hpt hio hD,
    kern_act R i t hθ hc hω hpt hio hD⟩

end GlobalTheory.TraceIncl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaKernelFiniteAdelicLawsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernelFiniteAdelic_laws : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0), R.models_inf → R.models_cV → R.thP_ωP → R.thP_pt_theta → R.thP_ioP → GlobalTheory.TraceIncl.DatumType R i t → (∀ h, GlobalTheory.TraceIncl.kern R i t (fin (Vc D i) h) = GlobalTheory.TraceIncl.kernA R i t h) ∧ (∀ (γ : GQ (Vc D i)) h w, GlobalTheory.TraceIncl.kern R i t (Bridge.ratF (Vc D i) γ * h) ((R.cV i).coef.ρ γ w) = GlobalTheory.TraceIncl.kern R i t h w) ∧ (∀ h (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) w, GlobalTheory.TraceIncl.kern R i t (h * k) w = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k)⁻¹ : ℂˣ) : ℂ) • GlobalTheory.TraceIncl.kern R i t h w) ∧ ∀ (g0 : G0 R.Pg D.R.r) (q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q), g0 = rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _)) → (∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ') → ∀ h w v, actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 (GlobalTheory.TraceIncl.kern R i t (h * q) w v) = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q)⁻¹ : ℂˣ) : ℂ) • GlobalTheory.TraceIncl.kern R i t h w v := by
  first | exact @GlobalTheory.TraceIncl.kern_laws | exact GlobalTheory.TraceIncl.kern_laws | (intros; apply GlobalTheory.TraceIncl.kern_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueCharIsOfFinOrder
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelCharOrder

theorem prod_isOfFinOrder {ι M : Type} [CommMonoid M] (s : Finset ι) (f : ι → M) (h : ∀ i ∈ s, IsOfFinOrder (f i)) :
    IsOfFinOrder (∏ i ∈ s, f i) :=
  Finset.prod_induction f IsOfFinOrder (fun _ _ ha hb => ha.mul hb) IsOfFinOrder.one h

theorem residue_char_isOfFinOrder {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E)
    (χ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (u : (Formalism.L2.DIV.kP PP)ˣ) : IsOfFinOrder (χ u) := by
  have : Finite (Formalism.L2.DIV.kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  exact χ.isOfFinOrder (isOfFinOrder_of_finite u)

theorem levFn_flag1_isOfFinOrder {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (x : GL (Fin V.rank) (Lev.EAf D)) :
    IsOfFinOrder (Formalism.L2.DIV.levFn β (flag1L L) x) := by
  have h1 : Formalism.L2.DIV.ext1 (flag1L L).P.H (flag1L L).P.chi (Formalism.L2.DIV.rTup β (flag1L L) x) = 1 :=
    subgroupCharExtension_one_apply _ _
  unfold Formalism.L2.DIV.levFn
  rw [h1]
  refine (IsOfFinOrder.one.mul ?_).mul ?_
  · exact prod_isOfFinOrder _ _ fun PP _ => prod_isOfFinOrder _ _ fun c _ => residue_char_isOfFinOrder PP _ _
  · exact prod_isOfFinOrder _ _ fun PP _ => residue_char_isOfFinOrder PP _ _

theorem levEnv_chi_isOfFinOrder : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J), IsOfFinOrder ((levEnv V β L).χ k) := by
  intro D V β L k
  exact levFn_flag1_isOfFinOrder V β L _

end GlobalTheory.LevelCharOrder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralEqSumOfSurjective
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassUnfold

theorem integral_eq_sum_of_surjective {G H : Type} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ]
    (π : G →* H) (hπ : Function.Surjective π) (J : Subgroup H) (𝓖 : Set G) (h𝓖 : IsFundamentalDomain Γ 𝓖 ν)
    (ho : IsOpen (J.comap π : Set G)) (h1 : ν (J.comap π) = 1) (I : Type) [Fintype I] (y : I → H)
    (hy : Bridge.IsReps (π.comp Γ.subtype) J y) (hf : ∀ c, Finite (Bridge.stab (π.comp Γ.subtype) J (y c)))
    (Φ : H → ℂ) (hΦ : ∀ (γ : Γ) h (k : J), Φ (π.comp Γ.subtype γ * h * k) = Φ h) :
    ∫ h in 𝓖, Φ (π h) ∂ν = ∑ c, (Nat.card (Bridge.stab (π.comp Γ.subtype) J (y c)) : ℂ)⁻¹ * Φ (y c) := by
  choose h hh using fun c => hπ (y c)
  have hS : ∀ c, {γ : G | γ ∈ Γ ∧ (h c)⁻¹ * γ * h c ∈ J.comap π} =
      Subtype.val '' (Bridge.stab (π.comp Γ.subtype) J (y c) : Set Γ) := by
    intro c
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, Bridge.mem_stab, Subgroup.mem_comap, map_mul,
      map_inv, hh]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨⟨γ, a⟩, b, rfl⟩
    · rintro ⟨δ, b, rfl⟩
      exact ⟨δ.2, b⟩
  have hfin : ∀ c, (Bridge.stab (π.comp Γ.subtype) J (y c) : Set Γ).Finite := fun c => hf c
  have key := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset G ν Γ (J.comap π) 𝓖 h𝓖 ho
    (by rw [h1]; exact ENNReal.one_ne_top) I h ?_ (fun c => by rw [hS]; exact (hfin c).image _)
    (fun x => Φ (π x)) ?_ ?_
  · rw [key.2.2, h1]
    simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hS, Set.ncard_image_of_injective _ Subtype.val_injective, hh]
    rfl
  · intro x
    refine (existsUnique_congr fun i => ?_).1 (hy (π x))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, γ.2, (γ * h i)⁻¹ * x, ?_, by group⟩
      rw [Subgroup.mem_comap, map_mul, map_inv, map_mul, hh, e]
      change (π γ * y i)⁻¹ * (π γ * y i * k) ∈ J
      rw [inv_mul_cancel_left]
      exact k.2
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨⟨γ, hγ⟩, ⟨π k, hk⟩, by rw [map_mul, map_mul, hh]; rfl⟩
  · intro γ hγ x
    have := hΦ ⟨γ, hγ⟩ (π x) 1
    rw [OneMemClass.coe_one, mul_one] at this
    rw [map_mul]
    exact this
  · intro k hk x
    have := hΦ 1 (π x) ⟨π k, hk⟩
    rw [map_one, one_mul] at this
    rw [map_mul]
    exact this

theorem integral_eq_classSum : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), L.P.H = ⊥ → IsMeasDef V (lev D.sp.cm V.gram β L) μ 𝓕 → ∀ (I : Type) [Fintype I] (y : I → Bridge.Gf V), Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y → (∀ c, Finite (Bridge.stab (Bridge.ratF V) (levEnv V β L).J (y c))) → ∀ Φ : Bridge.Gf V → ℂ, (∀ (γ : GQ V) h (k : (levEnv V β L).J), Φ (Bridge.ratF V γ * h * k) = Φ h) → ∫ h in 𝓕, Φ (fin V h) ∂μ = ∑ c, (Nat.card (Bridge.stab (Bridge.ratF V) (levEnv V β L).J (y c)) : ℂ)⁻¹ * Φ (y c) := by
  intro D V β L μ 𝓕 hL hμ I _ y hy hf Φ hΦ
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  haveI := hμ.1.1
  have hK : (levEnv V β L).J.comap (finHom V).rangeRestrict = (lev D.sp.cm V.gram β L).comap (finE V) := by
    ext g
    change (finE V g ∈ parLev D.sp.cm V.gram β L ∧ rTup β L (finE V g) ∈ (⊥ : Subgroup _)) ↔
      (finE V g ∈ parLev D.sp.cm V.gram β L ∧ rTup β L (finE V g) ∈ L.P.H)
    rw [hL]
  refine integral_eq_sum_of_surjective μ (GQ V) (finHom V).rangeRestrict (finHom V).rangeRestrict_surjective
    (levEnv V β L).J 𝓕 hμ.2 ?_ ?_ I y hy hf Φ hΦ
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_level V β L] with κ hκ
    exact hκ.1
  · rw [hK]
    exact GlobalTheory.Mass.Levels.measure_comap_finE hμ.1

end GlobalTheory.ClassUnfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodFormsCoordinateMapMemOfLiftsMem
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open Formalism.IndefR.Mult Formalism.IndefR.Cx
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl

theorem mem_of_mem_span_image {K V H : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] [AddCommGroup H]
    [Module ℂ H] {σ : K →+* ℂ} (j : V →ₛₗ[σ] H)
    (hj : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent ℂ fun k => j (b k))
    (N : Submodule K V) {z : V} (hz : j z ∈ Submodule.span ℂ (j '' (N : Set V))) : z ∈ N := by
  by_contra hn
  let b : Fin (Module.finrank K N) → V := fun k => (Module.finBasis K N k : V)
  have hb : LinearIndependent K b := (Module.finBasis K N).linearIndependent.map' N.subtype N.ker_subtype
  have hs : Submodule.span K (Set.range b) ≤ N := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact (Module.finBasis K N k).2)
  have h1 := hj _ (Fin.cons z b) (linearIndependent_finCons.2 ⟨hb, fun h => hn (hs h)⟩)
  have h2 : (fun k => j ((Fin.cons z b : Fin (Module.finrank K N + 1) → V) k)) =
      (Fin.cons (j z) (fun k => j (b k)) : Fin (Module.finrank K N + 1) → H) := by
    funext k
    refine Fin.cases rfl (fun _ => rfl) k
  rw [h2, linearIndependent_finCons] at h1
  refine h1.2 (Submodule.span_le.2 ?_ hz)
  rintro _ ⟨x, hx, rfl⟩
  have h3 := congrArg (fun z : N => (z : V)) ((Module.finBasis K N).sum_repr ⟨x, hx⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h3, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem exists_lvlE_eq {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
    (r : Representation K G S.Forms) (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ)
    (y : Fin (S.BaseDimension r X P ψ) → K) : ∃ x, (S.lvlE r P ψ).mulVecLin x = (S.V0E r X P ψ).mulVecLin y := by
  obtain ⟨u, hu⟩ := (image_idempotent_spec K _ (S.gaMat r (goodAt X P ψ))).2.le ⟨y, rfl⟩
  have h : S.gaMat r (goodAt X P ψ) = S.gaMat r (lvlIdem P ψ) * S.gaMat r (idemOf X) := by
    rw [← (group_action_matrix_hom K S G r).2, (idempotent_central K G X hX).2]
    rfl
  refine (image_idempotent_spec K _ (S.gaMat r (lvlIdem P ψ))).2.ge ⟨(S.gaMat r (idemOf X)).mulVec u, ?_⟩
  refine Eq.trans ?_ hu
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h]

theorem goodFormsCoordinateMap_apply {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : Formalism.L2.Indef.DefBase K} {Am : Formalism.L2.Indef.DefAmb Bs}
    (X : CxData Am) (b : Bool) (j : Bs.J) (c : Fin (X.dW b j) → ℂ) :
    X.w0C b j c = ∑ k, c k • X.eW b j (X.bW b j Bs.v0 k) := by
  show X.eW b j (∑ k, c k • X.bW b j Bs.v0 k) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => map_smul _ _ _

theorem goodFormsCoordinateMap_mem_of_lifts_mem {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : Formalism.L2.Indef.DefBase K} {Am : Formalism.L2.Indef.DefAmb Bs}
    (X : CxData Am) {fc : Formalism.L2.Indef.DefSub Am → Formalism.L2.Indef.DefFace Bs} (cr : Crd Am fc) (b : Bool) (h5 : X.H5 cr b)
    (j : Bs.J) (t : Bs.Tup) (N : Submodule ℂ (X.W j)) (h : ∀ y, X.θ' j t (X.jL j t (cr.toL X.zs b j t y)) ∈ N)
    (c : Fin (X.dW b j) → ℂ) : X.w0C b j c ∈ N := by
  obtain ⟨d, hd⟩ := (h5 j t).2.ge ⟨c, rfl⟩
  rw [← hd]
  show ∑ k, d k • X.θ' j t (X.jL j t (cr.toL X.zs b j t (Pi.single k 1))) ∈ N
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (h _)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem e_j_eOp (hU : R.LUnif) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (y : Fin (R.nW i) → D.what₂.LL) :
    (R.HW i σ).e ((R.FW i).j σ ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y)) =
      postOn _ (R.eWf i σ) ((R.HW i σ).e ((R.FW i).j σ y)) := by
  have htw : ∀ g, (R.HW i σ).e ((R.FW i).j σ (GlobalTheory.LevelForms.twRep (R.FW i) g y)) =
      postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) ((R.HW i σ).e ((R.FW i).j σ y)) := by
    intro g
    rw [GlobalTheory.LevelForms.twRep_apply, map_smulₛₗ, map_smul, (hU i σ).2.2, smul_smul, ← map_mul, Units.inv_mul, map_one,
      one_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.LevelForms.eOp_eq_sum, map_sum, map_sum]
  simp only [map_smulₛₗ, map_smul, htw]
  refine MultilinearMap.ext fun v => ?_
  simp only [RealDat.eWf, gaL, RealDat.eC, LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply,
    MultilinearMap.smul_apply, postOn_apply, RingHom.id_apply]
  all_goals rfl

theorem exists_w0C_eq (i : Fin D.R.m) {w : (R.HW i (sg0 D A)).H} (h1 : w ∈ R.WS F false i (sg0 D A)) :
    ∃ c, Tw.out (s := twAt D.what₂.embLL A.v0) ((R.toCx F).w0C false i c) = w := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 h1
  have hs : ((Real.sqrt (RealDat.nP F false) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (RealDat.nP_pos (F := F) false)).ne'
  let c' : Fin ((R.toCx F).dW false i) → ℂ :=
    fun k => cj (twAt D.what₂.embLL A.v0) (c k * ((Real.sqrt (RealDat.nP F false) : ℝ) : ℂ)⁻¹)
  have e1 := goodFormsCoordinateMap_apply (R.toCx F) false i c'
  refine ⟨c', (congrArg (Tw.out (s := twAt D.what₂.embLL A.v0)) e1).trans (Eq.trans ?_ hc)⟩
  show ∑ k, cj (twAt D.what₂.embLL A.v0) (c' k) • (((Real.sqrt (RealDat.nP F false) : ℝ) : ℂ) •
    R.bC F false i (sg0 D A) k) = _
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cj_cj, smul_smul, inv_mul_cancel_right₀ hs]

theorem exists_srcForm_eq (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) (t : T0)
    (Z : Submodule D.what₂.LL (A.fam.L i t).S.Forms) (y : Fin ((A.fam.L i t).dZ (A.fam.lvlA F.P0 F.ψ0) Z) → D.what₂.LL) :
    ∃ x, srcForm A i t F.P0 F.ψ0⁻¹ x = (A.fam.L i t).toF (A.fam.lvlA F.P0 F.ψ0) Z y := by
  obtain ⟨x, hx⟩ := exists_lvlE_eq (A.MtCSD i t) (A.leftGroupActionLift i t) A.X hX F.P0 F.ψ0⁻¹
    (((A.fam.L i t).zE (A.fam.lvlA F.P0 F.ψ0) Z).mulVecLin y)
  exact ⟨x, congrArg (fun u => (A.MtCSD i t).basis.equivFun.symm u) hx⟩

theorem out_lift_toL (i : Fin D.R.m) (t : T0)
    (y : Fin ((A.fam.L i t).dZ (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t)) → D.what₂.LL) :
    (R.toCx F).θ' i t ((R.toCx F).jL i t (F.cr.toL (R.toCx F).zs false i t y)) =
      Tw.mk (twAt D.what₂.embLL A.v0) (R.thG i t (jVx R i t
        ((A.fam.L i t).toF (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t) y))) := rfl

theorem j_eOp_of_adForm (hW : R.models_HW) (hG : R.thP_thG) (hU : R.LUnif) (i : Fin D.R.m) (t : T0) (ph : ℂ)
    (y : Fin (R.nW i) → D.what₂.LL) (u : (R.HV i t).H) (h0 : adForm R i y = ph • R.thF i t u) :
    (R.FW i).j (sg0 D A) ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y) = ph • R.thG i t u := by
  have h1 := e_j_eOp R hU i (sg0 D A) y
  unfold adForm at h0
  rw [h0, LinearMap.map_smul, ← hG i t u, ← LinearMap.map_smul] at h1
  exact (hW i _).1 h1

end GlobalTheory.TraceIncl
end
end
