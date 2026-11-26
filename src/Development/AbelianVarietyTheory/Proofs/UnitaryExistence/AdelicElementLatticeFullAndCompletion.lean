module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralTmulOneMulMemAdelicCompletion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRootNear
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NegIndexTransposeOfHasSignature

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
noncomputable section

namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem latOf_one_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (h1 : L.FG) (h2 : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    GlobalTheory.AdLat.latOf F (1 : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (L : Set (Fin n → E)) = L := by
  ext v
  have h := (GlobalTheory.AdLat.hat_rational_points_and_approx F E n L h1 h2).1 v
  simp only [GlobalTheory.AdLat.latOf, Set.mem_ofPred_eq, Set.mem_image, Matrix.one_mulVec, exists_eq_right,
    SetLike.mem_coe]
  exact h

theorem latG_eq_span_latOf (D : D7) (V : HSp D) (g : GA D V) :
    latG V g = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA,
      ∃ v ∈ GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (latC V : Set (Fin V.rank → D.host.E)), w = a • v} := by
  have hh := (latHat_eq_hat_and_gram D V).1
  unfold latG gLat
  rw [hh]
  rfl

theorem latGHat_eq_closure (D : D7) (V : HSp D) (g : GA D V) :
    latGHat V g = AddSubgroup.closure {w | ∃ a ∈ D.host.AA,
      ∃ z ∈ (finHom V g).1.mulVec '' (GlobalTheory.AdLat.hat D.host.F (latC V : Set (Fin V.rank → D.host.E))),
        w = fun i => ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] a) * z i} := by
  have hh := (latHat_eq_hat_and_gram D V).1
  unfold latGHat gLat
  rw [hh]

theorem latG_lattice_and_completion : ∀ (D : D7) (V : HSp D), ∀ g : GA D V, (latG V g).FG ∧ Submodule.span D.host.E (latG V g : Set (Fin V.rank → D.host.E)) = ⊤ ∧ (latG V g : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (latG V 1 : Set (Fin V.rank → D.host.E)) ∧ (latGHat V g : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) = (finHom V g).1.mulVec '' (GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E))) ∧ latGHat V g = GlobalTheory.AdLat.hat D.host.F (latG V g : Set (Fin V.rank → D.host.E)) ∧ latG V 1 = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x} := by
  intro D V g
  obtain ⟨-, -, hfg, hsp, -⟩ := latHat_eq_hat_and_gram D V
  have hA : D.host.AA ≠ 0 := AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have h6 : latG V 1 = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x} := by
    rw [latG_eq_span_latOf, map_one, Units.val_one, latOf_one_eq _ _ _ _ hfg hsp]
    rfl
  obtain ⟨s1, s2, s3, s4⟩ := GlobalTheory.AdLat.scale_latOf D.host.F D.host.E V.rank (latC V) (finHom V g) D.host.AA
    (latG V 1) hfg hsp hA h6
  have h3 : (latG V g : Set (Fin V.rank → D.host.E)) =
      GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (latG V 1 : Set (Fin V.rank → D.host.E)) := by
    rw [latG_eq_span_latOf D V g]; exact s1
  have h4 : (latGHat V g : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) =
      (finHom V g).1.mulVec '' (GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E))) := by
    rw [latGHat_eq_closure D V g]; exact s2
  obtain ⟨Λ, l1, l2, l3, l4⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E V.rank (latG V 1) (finHom V g) s3 s4
  have hΛ : Λ = latG V g := SetLike.coe_injective (l1.trans h3.symm)
  subst hΛ
  exact ⟨l2, l3, h3, h4, SetLike.coe_injective (h4.trans l4.symm), h6⟩

end GlobalTheory.Member
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletionStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicElementLattice_full_and_completion : ∀ (D : D7) (V : HSp D), ∀ g : GA D V, (latG V g).FG ∧ Submodule.span D.host.E (latG V g : Set (Fin V.rank → D.host.E)) = ⊤ ∧ (latG V g : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (latG V 1 : Set (Fin V.rank → D.host.E)) ∧ (latGHat V g : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) = (finHom V g).1.mulVec '' (GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E))) ∧ latGHat V g = GlobalTheory.AdLat.hat D.host.F (latG V g : Set (Fin V.rank → D.host.E)) ∧ latG V 1 = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x} := by
  first | exact @GlobalTheory.Member.latG_lattice_and_completion | exact GlobalTheory.Member.latG_lattice_and_completion | (intros; apply GlobalTheory.Member.latG_lattice_and_completion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem continuous_finPart (D : D7) : Continuous (finPart D) := by
  obtain ⟨e, he, hc, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
  rw [this]
  exact continuous_snd.comp hc

theorem continuous_infPart (D : D7) : Continuous (infPart D) := by
  obtain ⟨e, he, hc, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have : (infPart D : AE D → _) = fun z => (e z).1 := funext fun z => (he z).1.symm
  rw [this]
  exact continuous_fst.comp hc

theorem continuous_finHom_val (D : D7) (V : HSp D) : Continuous (fun k : GA D V => (finHom V k).1) := by
  have h : Continuous (fun k : GA D V => (matHom V k).1) :=
    Units.continuous_val.comp continuous_subtype_val
  exact h.matrix_map (continuous_finPart D)

theorem latHat_open_and_continuous : ∀ (D : D7) (V : HSp D), (∀ N : ℕ, 0 < N → IsOpen {z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E | ∃ y ∈ latHat V, z = N • y}) ∧ Continuous (fun k : GA D V => (finHom V k).1) ∧ Continuous (finPart D) ∧ Continuous (infPart D) := by
  intro D V
  refine ⟨?_, continuous_finHom_val D V, continuous_finPart D, continuous_infPart D⟩
  obtain ⟨h1, -, -, h4, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  rw [h1]
  exact (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat D.host.F D.host.E V.rank (latC V) h4).1

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicative
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicative
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.Arch

theorem unit_iff {E : Type} [CommRing E] {n : Type} [Fintype n] (τ : E →+* ℂ) (G : Matrix n n E) (u : Matrix n n ℂ) :
    uᵀ * (-Gᵀ).map τ * u.map (starRingEnd ℂ) = (-Gᵀ).map τ ↔ uᴴ * G.map τ * u = G.map τ := by
  have e : (-Gᵀ).map τ = -(G.map τ)ᵀ := by
    ext a b; simp
  have e2 : u.map (starRingEnd ℂ) = (uᴴ)ᵀ := by
    ext a b; simp
  rw [e, e2, Matrix.mul_neg, Matrix.neg_mul, neg_inj, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.transpose_mul]
  exact Matrix.transpose_injective.eq_iff

theorem form_map {A : Type} [CommRing A] {n : Type} [Fintype n] (s : A →+* A) (φ : A →+* ℂ)
    (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (M J : Matrix n n A) :
    (Formalism.UG.cT s M * J * M).map φ = (M.map φ)ᴴ * J.map φ * M.map φ := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext a b
  exact h _

theorem mat_ext {A : Type} [CommRing A] {n ι : Type} (θ : ι → (A →+* ℂ))
    (hθ : Function.Injective fun (z : A) (i : ι) => θ i z) {M N : Matrix n n A}
    (h : ∀ i, M.map (θ i) = N.map (θ i)) : M = N :=
  Matrix.ext fun a b => hθ (funext fun i => congrFun (congrFun (h i) a) b)

theorem exists_lift {A : Type} [CommRing A] {n ι : Type} [Fintype n] [DecidableEq n] (s : A →+* A)
    (θ : ι → (A →+* ℂ)) (hθ : Function.Bijective fun (z : A) (i : ι) => θ i z)
    (hs : ∀ i z, θ i (s z) = starRingEnd ℂ (θ i z)) (J : Matrix n n A) (hJ : ∀ i, (J.map (θ i)).det ≠ 0)
    (u : ι → Matrix n n ℂ) (hu : ∀ i, (u i)ᴴ * J.map (θ i) * u i = J.map (θ i)) :
    ∃ g : GL n A, g ∈ Formalism.UG.UJ s J ∧ ∀ i, g.1.map (θ i) = u i := by
  have lift : ∀ w : ι → Matrix n n ℂ, ∃ M : Matrix n n A, ∀ i, M.map (θ i) = w i := by
    intro w
    choose M hM using fun a b => hθ.2 fun i => w i a b
    exact ⟨Matrix.of M, fun i => Matrix.ext fun a b => congrFun (hM a b) i⟩
  have hd : ∀ i, IsUnit (u i).det := by
    intro i
    refine IsUnit.mk0 _ fun h0 => hJ i ?_
    rw [← hu i, Matrix.det_mul, h0, mul_zero]
  obtain ⟨M, hM⟩ := lift u
  obtain ⟨N, hN⟩ := lift fun i => (u i)⁻¹
  refine ⟨⟨M, N, mat_ext θ hθ.1 fun i => ?_, mat_ext θ hθ.1 fun i => ?_⟩, mat_ext θ hθ.1 fun i => ?_, hM⟩
  · rw [Matrix.map_mul, hM, hN, Matrix.mul_nonsing_inv _ (hd i), Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.map_mul, hM, hN, Matrix.nonsing_inv_mul _ (hd i), Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [form_map s (θ i) (hs i), hM, hu]

theorem gram_det_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have hy : S.frame.equivFun.symm v = 0 := by
    apply S.nondeg.2
    intro x
    have hi : ∀ i, S.hT (S.frame i) (S.frame.equivFun.symm v) = 0 := by
      intro i
      have := congrFun h0 i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Module.Basis.equivFun_symm_apply, map_sum]
      simpa [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, mul_comm] using this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← S.frame.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hi, smul_zero]
  exact S.frame.equivFun.symm.map_eq_zero_iff.1 hy

theorem continuous_inf (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Continuous (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) : AF F ⊗[F] E → Ainf F ⊗[F] E) := by
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Ainf F) _
  have : ContinuousSMul (Ainf F) (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  let φ : AF F ⊗[F] E →ₛₗ[(fstA F).toRingHom] Ainf F ⊗[F] E :=
    { toFun := Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)
      map_add' := map_add _
      map_smul' := fun a x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl }
  have hs : Continuous ((fstA F).toRingHom : AF F → Ainf F) := continuous_fst
  exact IsModuleTopology.continuous_of_linearMapₛₗ hs φ

theorem inf_mem {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (AF F ⊗[F] E)) (hg : g ∈ HR (AF F) σ J) :
    Formalism.UG.bc (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom g ∈ HR (Ainf F) σ J := by
  let π : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have hπ : ∀ z, π (sigR (AF F) σ z) = sigR (Ainf F) σ (π z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
    | tmul a x => rfl
  have hg' : Formalism.UG.cT (sigR (AF F) σ) g.1 * JR (AF F) J * g.1 = JR (AF F) J := hg
  have hJ : (JR (F := F) (AF F) J).map π = JR (Ainf F) J := rfl
  have hc : (Formalism.UG.cT (sigR (AF F) σ) g.1).map π = Formalism.UG.cT (sigR (Ainf F) σ) (g.1.map π) :=
    Matrix.ext fun a b => hπ _
  change Formalism.UG.cT (sigR (Ainf F) σ) (g.1.map π) * JR (Ainf F) J * g.1.map π = JR (Ainf F) J
  rw [← hc, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg']

variable {D : D7}

theorem JR_map (V : HSp D) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) : (JR (F := D.host.F) (Ainf D.host.F) V.gram).map θ = V.gram.map τ :=
  Matrix.ext fun _ _ => h.1 _

theorem archM_of_one (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) {k : GA D V}
    (hk : infHom V k = 1) : archM V θ k = 1 := by
  rw [archM, hk, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem continuous_archM (V : HSp D) {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ} (hθ : Continuous θ) :
    Continuous fun h => archM V θ h := by
  have h1 : Continuous fun h : GA D V => (matHom V h).1 :=
    Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)))
  exact (h1.matrix_map (continuous_inf D.host.F D.host.E)).matrix_map hθ

theorem archM_spec : ∀ (D : D7) (V : HSp D), ∀ (θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) → (∀ τ, archM V (θ τ) 1 = 1 ∧ (∀ h h', archM V (θ τ) (h * h') = archM V (θ τ) h * archM V (θ τ) h') ∧ (∀ k ∈ GfC V, archM V (θ τ) k = 1) ∧ Continuous (fun h => archM V (θ τ) h) ∧ ∀ h, (archM V (θ τ) h)ᵀ * (-V.gramᵀ).map τ * (archM V (θ τ) h).map (starRingEnd ℂ) = (-V.gramᵀ).map τ) ∧ (∀ h, (∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → archM V (θ τ) h = 1) → h ∈ GfC V) ∧ ∀ u : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → (u τ)ᵀ * (-V.gramᵀ).map τ * (u τ).map (starRingEnd ℂ) = (-V.gramᵀ).map τ) → ∃ a ∈ GinfC V, ∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → archM V (θ τ) a = u τ := by
  intro D V θ hθ
  obtain ⟨hc, hs, hb⟩ := (GlobalTheory.T.realAdeles_cmField_equiv_complex_cmType D).2 θ hθ
  refine ⟨fun τ => ⟨archM_of_one V _ (map_one _), fun h h' => ?_, fun k hk => archM_of_one V _ hk,
    continuous_archM V (hc τ), fun h => ?_⟩, fun h hh => ?_, fun u hu => ?_⟩
  · rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
  · have hm : Formalism.UG.cT (sigR (Ainf D.host.F) D.sp.cm.sig) (infHom V h).1 * JR (Ainf D.host.F) V.gram * (infHom V h).1 =
        JR (Ainf D.host.F) V.gram := inf_mem D.sp.cm.sig V.gram (matHom V h) h.2
    rw [unit_iff, ← JR_map V (hθ τ), archM, ← form_map _ _ (hs τ), hm]
  · refine Units.ext (mat_ext _ hb.1 fun τ => ?_)
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hh τ.1 τ.2
  · obtain ⟨g, hg, hgu⟩ := exists_lift (sigR (Ainf D.host.F) D.sp.cm.sig) _ hb (fun τ => hs τ.1)
      (JR (Ainf D.host.F) V.gram) (fun τ => by
        rw [JR_map V (hθ τ.1)]
        have : (V.gram.map τ.1).det = τ.1 V.gram.det := (τ.1.map_det V.gram).symm
        rw [this]
        exact (map_ne_zero τ.1).2 (gram_det_ne_zero V)) (fun τ => u τ.1) (fun τ => by
        rw [JR_map V (hθ τ.1)]
        exact (unit_iff _ _ _).1 (hu τ.1 τ.2))
    obtain ⟨a, ha, hag⟩ := (GlobalTheory.T.adelicUnitary_eq_real_mul_finite_split D V).2.2.2.2 g hg
    refine ⟨a, ha, fun τ hτ => ?_⟩
    rw [archM, hag]
    exact hgu ⟨τ, hτ⟩

end GlobalTheory.Member.Arch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicativeStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative : ∀ (D : D7) (V : HSp D), ∀ (θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) → (∀ τ, archM V (θ τ) 1 = 1 ∧ (∀ h h', archM V (θ τ) (h * h') = archM V (θ τ) h * archM V (θ τ) h') ∧ (∀ k ∈ GfC V, archM V (θ τ) k = 1) ∧ Continuous (fun h => archM V (θ τ) h) ∧ ∀ h, (archM V (θ τ) h)ᵀ * (-V.gramᵀ).map τ * (archM V (θ τ) h).map (starRingEnd ℂ) = (-V.gramᵀ).map τ) ∧ (∀ h, (∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → archM V (θ τ) h = 1) → h ∈ GfC V) ∧ ∀ u : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → (u τ)ᵀ * (-V.gramᵀ).map τ * (u τ).map (starRingEnd ℂ) = (-V.gramᵀ).map τ) → ∃ a ∈ GinfC V, ∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → archM V (θ τ) a = u τ := by
  first | exact @GlobalTheory.Member.Arch.archM_spec | exact GlobalTheory.Member.Arch.archM_spec | (intros; apply GlobalTheory.Member.Arch.archM_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalLevelEqHalfMarkingStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalLevelEqHalfMarkingStabilizer
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem halfVec_mem_latHat {D : D7} (V : HSp D) (b : 𝓞 D.host.E)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hz : z ∈ latHat V) :
    halfVec V b z ∈ latHat V := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a, ha, b • x, V.L0.smul_mem b hx, ?_⟩
    funext i
    have e : b • x = (b : D.host.E) • x := (algebraMap_smul D.host.E b x).symm
    simp only [halfVec, Algebra.TensorProduct.tmul_mul_tmul, one_mul, e, map_smul,
      Finsupp.smul_apply, smul_eq_mul]
  | zero =>
    have : halfVec V b 0 = 0 := by funext i; simp [halfVec]
    rw [this]; exact zero_mem _
  | add w w' _ _ h h' =>
    have : halfVec V b (w + w') = halfVec V b w + halfVec V b w' := by
      funext i; simp only [halfVec, Pi.add_apply, mul_add]
    rw [this]; exact add_mem h h'
  | neg w _ h =>
    have : halfVec V b (-w) = - halfVec V b w := by
      funext i; simp only [halfVec, Pi.neg_apply, mul_neg]
    rw [this]; exact neg_mem h

theorem finCong_iff_half (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D)
    (k : GA D V) :
    FinCong V l.M k ↔ ∀ b ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E), ∀ z ∈ latHat V,
      ∃ y ∈ latHat V, (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = l.M • y := by
  refine ⟨fun h b _ z hz => h _ (halfVec_mem_latHat V b z hz), fun h => ?_⟩
  obtain ⟨h1, -, h3, h4, h5, h6, -, h8, h9, -, h11⟩ := latHat_eq_hat_and_gram D V
  unfold FinCong
  rw [h1] at h ⊢
  refine GlobalTheory.AdLat.trivial_level_of_half D.host.F D.host.E V.rank (latC V) (cF D) V.gramᵀ 1
    (finHom V k) l.M (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) l.Mb h3 h4 h5 h8 h9
    one_ne_zero h11 (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V k).1 (lt_of_lt_of_le (by norm_num) l.three_le)
    (by rw [sup_comm]; exact l.coprime) (by rw [mul_comm]; exact l.prod) ?_ h
  intro b hb
  refine ⟨H.bar b, Ideal.mem_map_of_mem _ hb, ?_⟩
  rw [h6]
  exact H.bar_eq b

theorem finCong_iff_half_and_kfHalf : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D), (∀ k : GA D V, FinCong V l.M k ↔ ∀ b ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E), ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = l.M • y) ∧ ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → KfHalf V Kf l.M (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) := by
  intro D H l V
  refine ⟨finCong_iff_half D H l V, fun Kf hK k => ?_⟩
  rw [hK k]
  exact and_congr_right fun _ => finCong_iff_half D H l V k

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalLevelEqHalfMarkingStabilizerStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_eq_halfMarking_stabilizer : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D), (∀ k : GA D V, FinCong V l.M k ↔ ∀ b ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E), ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = l.M • y) ∧ ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → KfHalf V Kf l.M (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) := by
  first | exact @GlobalTheory.Member.finCong_iff_half_and_kfHalf | exact GlobalTheory.Member.finCong_iff_half_and_kfHalf | (intros; apply GlobalTheory.Member.finCong_iff_half_and_kfHalf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryAdelicCharOfHeckeChar
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRootNearOne
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem exists_root_near_one : ∀ (D : D7), ∀ W ∈ 𝓝 (1 : (AE D)ˣ), ∃ N ∈ 𝓝 (1 : (AE D)ˣ), ∀ u ∈ N, (u : AE D) * sigR (AF D.host.F) D.sp.cm.sig (u : AE D) = 1 → ∃ x ∈ W, (x : AE D) = (u : AE D) * sigR (AF D.host.F) D.sp.cm.sig (x : AE D) := by
  intro D
  have hP : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal →
      ∃ t s : 𝓞 D.host.E, (s : D.host.E) = cF D (t : D.host.E) ∧ t - s ∉ P := by
    intro P hP
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    exact ⟨θ, t, ht, hθ⟩
  have hc : cF D ≠ 1 := by
    intro h
    obtain ⟨P, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
    obtain ⟨t, s, hs, hts⟩ := hP P hM
    rw [h] at hs
    have : s = t := Subtype.ext hs
    rw [this, sub_self] at hts
    exact hts P.zero_mem
  exact GlobalTheory.AdLat.RootNear.exists_root_near D.host.F D.host.E (cF D) D.sp.cm.deg2 hc hP

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryAdelicCharOfHeckeChar
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem continuous_det_matHom (D : D7) (V : HSp D) :
    Continuous fun g : GA D V => Matrix.GeneralLinearGroup.det (matHom V g) := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  have hm : Continuous fun g : GA D V => matHom V g := continuous_subtype_val
  exact Matrix.GeneralLinearGroup.continuous_det.comp hm

theorem exists_muVal : ∀ (D : D7) (V : HSp D), ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a, χ (idF D a) = 1) → ∃ mu : GA D V → ℂ, MuVal V χ mu ∧ (∀ g g', mu (g * g') = mu g * mu g') ∧ (∀ g, ‖mu g‖ = 1) ∧ (∀ γ ∈ GQ V, mu γ = 1) ∧ Continuous mu := by
  intro D V χ hχ hF
  obtain ⟨hex, huniq, hrat, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D V
  choose r hr using hex
  have hval : ∀ g x, IsDetRoot V g x → χ (r g) = χ x := by
    intro g x hx
    obtain ⟨a, ha⟩ := huniq g _ _ (hr g) hx
    rw [ha, map_mul, hF, mul_one]
  have hm : ∀ g g', χ (r (g * g')) = χ (r g) * χ (r g') := by
    intro g g'
    rw [hval _ _ (hmul _ _ _ _ (hr g) (hr g')), map_mul]
  let m : GA D V →* Circle := MonoidHom.mk' (fun g => χ (r g)) hm
  have hcont : Continuous m := by
    haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
    refine continuous_of_continuousAt_one m ?_
    intro U hU
    rw [map_one] at hU
    have hW : χ ⁻¹' U ∈ 𝓝 (1 : (AE D)ˣ) := hχ.1.continuousAt.preimage_mem_nhds (by rwa [map_one])
    obtain ⟨N, hN, hNW⟩ := GlobalTheory.Member.exists_root_near_one D _ hW
    have hN' : (fun g : GA D V => Matrix.GeneralLinearGroup.det (matHom V g)) ⁻¹' N ∈ 𝓝 (1 : GA D V) :=
      (continuous_det_matHom D V).continuousAt.preimage_mem_nhds (by rwa [map_one, map_one])
    refine Filter.mem_map.2 (Filter.mem_of_superset hN' ?_)
    intro g hg
    obtain ⟨x, hxW, hx⟩ := hNW _ hg (GlobalTheory.Member.finHom_herm_det D V g).2.2
    have : m g = χ x := hval g x hx
    show m g ∈ U
    rw [this]
    exact hxW
  refine ⟨fun g => (m g : ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun g => ⟨r g, hr g⟩, fun g x hx => congrArg (fun z : Circle => (z : ℂ)) (hval g x hx)⟩
  · intro g g'
    simp only [map_mul, Circle.coe_mul]
  · intro g
    exact Circle.norm_coe _
  · intro γ hγ
    obtain ⟨x, hx⟩ := hrat γ hγ
    have : m γ = 1 := (hval γ _ hx).trans (hχ.2 x)
    simp only [this, Circle.coe_one]
  · exact continuous_subtype_val.comp hcont

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryAdelicCharOfHeckeCharStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryAdelicChar_of_heckeChar : ∀ (D : D7) (V : HSp D), ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a, χ (idF D a) = 1) → ∃ mu : GA D V → ℂ, MuVal V χ mu ∧ (∀ g g', mu (g * g') = mu g * mu g') ∧ (∀ g, ‖mu g‖ = 1) ∧ (∀ γ ∈ GQ V, mu γ = 1) ∧ Continuous mu := by
  first | exact @GlobalTheory.Member.exists_muVal | exact GlobalTheory.Member.exists_muVal | (intros; apply GlobalTheory.Member.exists_muVal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointFieldFromTestRing
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointFieldFromTestRing
namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem framedPoint_field_fromTest :
    Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
      (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), SpreadSt Xo c := by
  intro hB E _ _ _ H Dw l Xo c S _ _ y
  let xF : Sp S ⟶ Xo.XF c := pullback.lift y.x (spMap (algebraMap c.F S)) (by
    rw [y.x_over]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])
  have h1 : xF ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
  have h2 : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := pullback.lift_snd _ _ _
  let q : Sp S := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum S)
  obtain ⟨p, j, y₀, hj, hq⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hB E H Dw l Xo c (xF q)
  obtain ⟨g, hg, hfac⟩ := openChart_factor_near_prime E H Dw l Xo c p.R j y₀ hj S xF h2 q hq
  have hg0 : g ≠ 0 := fun h => hg (h ▸ Ideal.zero_mem _)
  obtain ⟨ψ, hψ⟩ := hfac S (AlgHom.id c.F S) (Ne.isUnit hg0)
  have hid : spMap (AlgHom.id c.F S).toRingHom = 𝟙 (Sp S) := Spec.map_id _
  rw [hid, Category.id_comp] at hψ
  have hx : y.x = spMap ψ.toRingHom ≫ y₀.x := by
    rw [← h1, hψ, Category.assoc, hj.2.1]
  obtain ⟨A, π, X, s, u, hu⟩ := GlobalTheory.T.exists_universalFrame_testRing hB E H Dw l Xo c p y₀
  obtain ⟨a, ⟨-, ha⟩, -⟩ := GlobalTheory.T.universalFrame_classifies_framedPoints hB E H Dw l Xo c p.R A.R y₀ π X s u hu S y ψ hx
  exact ⟨A, a, u, ha⟩

end GlobalTheory.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointFieldFromTestRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_field_from_testRing : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), SpreadSt Xo c := by
  first | exact @GlobalTheory.Frames.framedPoint_field_fromTest | exact GlobalTheory.Frames.framedPoint_field_fromTest | (intros; apply GlobalTheory.Frames.framedPoint_field_fromTest <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LiftDatumAlternatingFormSignEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LiftDatumAlternatingFormSignEqOne
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem neg_baseElement_im_neg_baseEmbedding (D : D7) : (D.host.φ₀ (-D.host.xi0)).im < 0 := by
  have h1 := xi0_embedding_im_pos D D.host.φ₀ ((mem_cm_type_iff D _).2 rfl)
  have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im := by
    rw [hφ]
    have hd : (0 : ℝ) < D.host.d := by exact_mod_cast d_pos D
    simpa using hd
  rw [if_pos hpos, Int.cast_one, _root_.one_mul] at h1
  rw [map_neg, Complex.neg_im]
  linarith

theorem sign_eq_one : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (j : ℕ), InR D j → (H.rt : D.host.E) = D.host.sqrtMinusD → H.rt0 = D.host.φ₀ D.host.sqrtMinusD → Dw.p = (D.R.sigW j).1 → Dw.q = (D.R.sigW j).2 → ∀ (φ : Dw.La →ₗ[𝓞 D.host.E] (D.sp.W j).V) (ε : ℤˣ), Function.Injective φ → Submodule.span D.host.E (Set.range φ) = ⊤ → (∀ x y, ((Dw.EF x y : ℤ) : ℚ) = ((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 * (D.sp.W j).hT (φ x) (φ y))) → ε = 1 := by
  intro D H Dw j hj hrt hrt0 hp _ φ ε hinj hspan0 hEF
  have hr := D.sp.W_rank j hj.1 hj.2
  let f := ((D.sp.W j).frame.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap
  have hio : Function.Injective (f ∘ₗ φ) := (D.sp.W j).frame.equivFun.injective.comp hinj
  have hdet := (GlobalTheory.RecDict.posIndex_gmW (D.sp.W j) (D.sp.W_sig j) hr D.host.φ₀).2
  have hherm := GlobalTheory.RecDict.cc_gmW (D.sp.W j) hr
  have hspan : Submodule.span D.host.E (Set.range (f ∘ₗ φ)) = ⊤ := by
    have : Set.range (f ∘ₗ φ) = (D.sp.W j).frame.equivFun.toLinearMap '' Set.range φ := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, hspan0, Submodule.map_top, LinearEquiv.range]
  rcases Int.units_eq_one_or ε with h | h
  · exact h
  exfalso
  subst h
  let c : (Fin (D.sp.W j).rank → D.host.E) ≃ₗ[D.host.E] (Fin D.R.r → D.host.E) :=
    LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr hr.symm)
  let ψ : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E) :=
    (c.restrictScalars (𝓞 D.host.E)).toLinearMap ∘ₗ f ∘ₗ φ
  have hψ : ∀ x, ψ x = (D.sp.W j).frame.equivFun (φ x) ∘ Fin.cast hr.symm := fun _ => rfl
  have hτ : D.host.φ₀ (H.rt : D.host.E) = H.rt0 := by rw [hrt, hrt0]
  have hξ : cc (-D.host.xi0) = -(-D.host.xi0) := by
    rw [cc, map_neg, conj_xi0_alt]
  have hsp : Submodule.span D.host.E (Set.range ψ) = ⊤ := by
    have : Set.range ψ = c.toLinearMap '' Set.range (f ∘ₗ φ) := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  obtain ⟨P, hP, hPg⟩ := (GlobalTheory.HermSign.signature_of_model D.host.E H Dw D.R.r (-D.host.xi0)
    _ ψ hξ ⟨c.injective.comp hio, hsp, hherm, hdet, fun x y => by
      rw [hEF, hψ, hψ, neg_mul, map_neg, GlobalTheory.RecDict.trace_herm_gmW]
      simp⟩ D.host.φ₀ hτ).2 (neg_baseElement_im_neg_baseEmbedding D)
  have hm := D.R.m_add_three_le_k
  have h1 := hj.1
  have h2 := hj.2
  have hle : Dw.p ≤ D.R.r := by
    rw [hp]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have h3 := (GlobalTheory.Inertia.gram_eq_sgn_iff D.host.φ₀ hherm hdet _).1 ⟨hle, P, hP, hPg⟩
  rw [(GlobalTheory.RecDict.posIndex_gmW (D.sp.W j) (D.sp.W_sig j) hr D.host.φ₀).1, D.sp.W_sigval j hj.1 hj.2, hp] at h3
  simp only [Ranks.sigW] at h3
  omega

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LiftDatumAlternatingFormSignEqOneStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftDatum_alternatingForm_sign_eq_one : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (j : ℕ), InR D j → (H.rt : D.host.E) = D.host.sqrtMinusD → H.rt0 = D.host.φ₀ D.host.sqrtMinusD → Dw.p = (D.R.sigW j).1 → Dw.q = (D.R.sigW j).2 → ∀ (φ : Dw.La →ₗ[𝓞 D.host.E] (D.sp.W j).V) (ε : ℤˣ), Function.Injective φ → Submodule.span D.host.E (Set.range φ) = ⊤ → (∀ x y, ((Dw.EF x y : ℤ) : ℚ) = ((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 * (D.sp.W j).hT (φ x) (φ y))) → ε = 1 := by
  first | exact @GlobalTheory.Member.sign_eq_one | exact GlobalTheory.Member.sign_eq_one | (intros; apply GlobalTheory.Member.sign_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameClassifiesUniqueOpenChart
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameClassifiesUniqueOpenChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

private theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem univFrame_classifies_unique : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [Algebra c.F R] (A : Type) [CommRing A] [Algebra c.F A] (j : Sp R ⟶ Xo.XF c) (y₀ : FrPt Xo c R) (π : R →ₐ[c.F] A) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A)) (s : Aˣ) (u : FrPt Xo c A), OpenChart j y₀ → UnivFrame y₀ π X s u → ∀ (T : Type) [CommRing T] [Algebra c.F T] (a a' : A →ₐ[c.F] T) (z : FrPt Xo c T), FrMap a u z → FrMap a' u z → a = a' := by
  intro hS E _ _ _ H Dw l Xo c R _ _ A _ _ j y₀ π X s u hj hu T _ _ a a' z ha ha'
  obtain ⟨hopen, hj1, hj2⟩ := hj
  obtain ⟨u₀, hπ, hchg⟩ := hu.2
  have key : ∀ b : A →ₐ[c.F] T, FrMap b u z → z.x = spMap (b.comp π).toRingHom ≫ y₀.x := by
    intro b hb
    rw [hb.1, hchg.1, hπ.1, ← Category.assoc, ← spectrumMap_comp]
    rfl
  have hov : ∀ ψ : R →ₐ[c.F] T, spMap ψ.toRingHom ≫ spMap (algebraMap c.F R) = spMap (algebraMap c.F T) := by
    intro ψ
    rw [← spectrumMap_comp]
    congr 1
    exact ψ.comp_algebraMap
  have h1 : spMap (a.comp π).toRingHom ≫ j = spMap (a'.comp π).toRingHom ≫ j := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hj1, ← key a ha, ← key a' ha']
    · rw [Category.assoc, Category.assoc, hj2, hov, hov]
  have h2 : spMap (a.comp π).toRingHom = spMap (a'.comp π).toRingHom := (cancel_mono j).1 h1
  have h3 : a.comp π = a'.comp π := by
    have h4 := Spec.map_injective h2
    have h5 := congrArg CommRingCat.Hom.hom h4
    exact AlgHom.coe_ringHom_injective h5
  obtain ⟨b, -, hb⟩ := GlobalTheory.T.universalFrame_classifies_framedPoints hS E H Dw l Xo c R A y₀ π X s u hu T z (a.comp π) (key a ha)
  exact (hb a ⟨rfl, ha⟩).trans (hb a' ⟨h3.symm, ha'⟩).symm

end GlobalTheory.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameClassifiesUniqueOpenChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalFrame_classifies_unique_openChart : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [Algebra c.F R] (A : Type) [CommRing A] [Algebra c.F A] (j : Sp R ⟶ Xo.XF c) (y₀ : FrPt Xo c R) (π : R →ₐ[c.F] A) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A)) (s : Aˣ) (u : FrPt Xo c A), OpenChart j y₀ → UnivFrame y₀ π X s u → ∀ (T : Type) [CommRing T] [Algebra c.F T] (a a' : A →ₐ[c.F] T) (z : FrPt Xo c T), FrMap a u z → FrMap a' u z → a = a' := by
  first | exact @GlobalTheory.Frames.univFrame_classifies_unique | exact GlobalTheory.Frames.univFrame_classifies_unique | (intros; apply GlobalTheory.Frames.univFrame_classifies_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingThird
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

open scoped Matrix nonZeroDivisors

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem coset_fv_mulVec (A : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    (A.map (inclR (F := F) (Af F))) *ᵥ AdLat.fv F x = AdLat.fv F (A *ᵥ x) := by
  funext i
  exact (RingHom.map_mulVec (inclR (F := F) (Af F)) A x i).symm

theorem coset_tmul_eq (t : Af F) (x : Fin n → E) :
    (fun i => t ⊗ₜ[F] x i : Fin n → AdLat.RA F E) = (t ⊗ₜ[F] (1 : E) : AdLat.RA F E) • AdLat.fv F x := by
  funext i
  simp only [AdLat.fv, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem coset_smul_mem_hat (L : Set (Fin n → E)) (t : Af F) (ht : ∀ v, t v ∈ v.adicCompletionIntegers F)
    (w : Fin n → AdLat.RA F E) (hw : w ∈ AdLat.hat F L) :
    (t ⊗ₜ[F] (1 : E) : AdLat.RA F E) • w ∈ AdLat.hat F L := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨s, hs, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨t * s, fun v => mul_mem (ht v) (hs v), x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add w w' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg w _ h => rw [smul_neg]; exact neg_mem h

theorem coset_mulVec_mem_hat (L : Set (Fin n → E)) (A : Matrix (Fin n) (Fin n) E) (hA : ∀ x ∈ L, A *ᵥ x ∈ L)
    (w : Fin n → AdLat.RA F E) (hw : w ∈ AdLat.hat F L) :
    (A.map (inclR (F := F) (Af F))) *ᵥ w ∈ AdLat.hat F L := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨s, hs, x, hx, rfl⟩ := hw
    rw [coset_tmul_eq, Matrix.mulVec_smul, coset_fv_mulVec]
    exact coset_smul_mem_hat L s hs _ (AdLat.Half.fv_mem_hat' L _ (hA x hx))
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add w w' _ _ h h' => rw [Matrix.mulVec_add]; exact add_mem h h'
  | neg w _ h => rw [Matrix.mulVec_neg]; exact neg_mem h

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem coset_latGHat (V : HSp D) (g : GA D V) :
    latGHat V g = AdLat.hat D.host.F (latG V g : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨hfg, hsp, h⟩ := comp_latG D V
  obtain ⟨Λ, h1, -, -, h2⟩ := AdLat.exists_lattice_latOf D.host.F D.host.E V.rank (latG V 1) (finHom V g) hfg hsp
  apply SetLike.coe_injective
  rw [(h g).2, (h g).1, ← h1, h2]

theorem coset_fin {R : Type} [CommRing R] {n : ℕ} (S T : AddSubgroup (Fin n → R)) (g₁ g₂ δ : GL (Fin n) R) (N : ℕ)
    (h1 : ∀ w ∈ T, ∃ z ∈ S, g₁.1 *ᵥ z = w) (hδ : ∀ w ∈ T, δ.1 *ᵥ w ∈ T) (hδ' : ∀ w ∈ T, (δ⁻¹).1 *ᵥ w ∈ T)
    (u v w₁ w₂ b : Fin n → R) (hw₁ : w₁ ∈ T) (hw₂ : w₂ ∈ T) (hb : b ∈ T)
    (e₁ : u - g₁.1 *ᵥ v = N • w₁) (e₂ : u - g₂.1 *ᵥ v = N • w₂) (e₃ : δ.1 *ᵥ u = u + N • b) :
    ∃ y ∈ S, ((δ * g₁)⁻¹ * g₂).1 *ᵥ v - v = N • y := by
  obtain ⟨z, hz, ez⟩ := h1 _ (hδ' _ (sub_mem (sub_mem (hδ _ hw₁) hw₂) hb))
  refine ⟨z, hz, ?_⟩
  have hz' : (δ * g₁).1 *ᵥ z = δ.1 *ᵥ w₁ - w₂ - b := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ez, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hinv : ∀ x, ((δ * g₁)⁻¹).1 *ᵥ ((δ * g₁).1 *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have e : g₂.1 *ᵥ v - (δ * g₁).1 *ᵥ v = N • ((δ * g₁).1 *ᵥ z) := by
    rw [hz', Units.val_mul, ← Matrix.mulVec_mulVec, smul_sub, smul_sub, ← Matrix.mulVec_smul, ← e₁, ← e₂,
      Matrix.mulVec_sub, e₃]
    abel
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  have e' := congrArg (fun x => ((δ * g₁)⁻¹).1 *ᵥ x) e
  simpa only [Matrix.mulVec_sub, Matrix.mulVec_smul, hinv] using e'

end GlobalTheory.RecDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsChartHolomorphicCoordinatesNearFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsChartHolomorphicCoordinatesNearFrame
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding Unf GoodEmb relab perFr gxFst gxSnd toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.HolChart

theorem isHolTo_congr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {X : Scheme.{0}}
    {a a' : V → (Sp ℂ ⟶ X)} (h : IsHolTo B a) (he : ∀ b ∈ B, a' b = a b) : IsHolTo B a' := by
  intro U f
  have hs : {b ∈ B | ⊤ ≤ a' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ a b ⁻¹ᵁ U} := by
    ext b
    exact and_congr_right fun hb => by rw [he b hb]
  rw [hs]
  exact ⟨(h U f).1, (h U f).2.congr fun b hb => by rw [he b hb.1]⟩

theorem valAt'_spMap {R : Type} [CommRing R] (ψ : R →+* ℂ) (t : R) :
    valAt' (spMap ψ) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t) = ψ t := by
  have h : ⊤ ≤ (spMap ψ) ⁻¹ᵁ ⊤ := le_top
  rw [valAt', dif_pos h, valAt]
  have e : (spMap ψ).appLE ⊤ ⊤ h = (spMap ψ).appTop := (spMap ψ).appLE_eq_app
  have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)
  have n' := congrArg (fun φ => φ.hom t) n
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n'
  rw [e]
  erw [← n']
  exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply _

theorem exists_coordinates {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {X : Scheme.{0}}
    {a : V → (Sp ℂ ⟶ X)} (h : IsHolTo B a) {R : Type} [CommRing R] (j : Sp R ⟶ X) [IsOpenImmersion j]
    {b₀ : V} (hb₀ : b₀ ∈ B) (hj : a b₀ (default : PrimeSpectrum ℂ) ∈ Set.range j) :
    ∃ (B' : Set V) (ψ : V → (R →+* ℂ)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ (∀ b ∈ B', a b = spMap (ψ b) ≫ j) ∧
      ∀ t : R, DifferentiableOn ℂ (fun b => ψ b t) B' := by
  classical
  let U : X.Opens := j ''ᵁ ⊤
  have hU : ∀ x : X, x ∈ U ↔ x ∈ Set.range j := fun x => by
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, trivial, rfl⟩
  have hl : ∀ x : Sp ℂ ⟶ X, ⊤ ≤ x ⁻¹ᵁ U → ∃ ψ : R →+* ℂ, x = spMap ψ ≫ j := fun x hx => by
    have hr : Set.range x ⊆ Set.range j := by
      rintro _ ⟨q, rfl⟩
      exact (hU _).1 (hx (Set.mem_univ q))
    refine ⟨(Spec.preimage (IsOpenImmersion.lift j x hr)).hom, ?_⟩
    rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have h₀ : ⊤ ≤ a b₀ ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 ((hU _).2 hj)
  let ψ : V → (R →+* ℂ) := fun b => if hb : ⊤ ≤ a b ⁻¹ᵁ U then (hl _ hb).choose else (hl _ h₀).choose
  have hψ : ∀ b, ⊤ ≤ a b ⁻¹ᵁ U → a b = spMap (ψ b) ≫ j := fun b hb => by
    simp only [ψ, dif_pos hb]
    exact (hl _ hb).choose_spec
  refine ⟨{b ∈ B | ⊤ ≤ a b ⁻¹ᵁ U}, ψ, (h U 0).1, ⟨hb₀, h₀⟩, fun b hb => hb.1, fun b hb => hψ b hb.2, fun t => ?_⟩
  refine (h U ((j.appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t))).2.congr fun b hb => ?_
  have hle : (⊤ : (Sp R).Opens) ≤ j ⁻¹ᵁ U := fun y _ => (hU _).2 ⟨y, rfl⟩
  have hid : (j.appIso ⊤).inv ≫ j.appLE U ⊤ hle = 𝟙 _ := by
    rw [Scheme.Hom.appIso_inv_appLE]
    exact (Sp R).presheaf.map_id _
  rw [hψ b hb.2, ← valAt'_appLE (spMap (ψ b)) j U ⊤ hle _ le_top, ← CommRingCat.comp_apply, hid]
  exact (valAt'_spMap (ψ b) t).symm

theorem exists_chart_holomorphic :
    Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b₀ ∈ T.co ⁻¹' (M.X k).dom, ∃ (p : TRing c.F) (y₀ : FrPt Xo c p.R) (B : Set (Fin T.m → ℂ)) (ψ : (Fin T.m → ℂ) → (p.R →ₐ[c.F] CAt σ)), IsOpen B ∧ b₀ ∈ B ∧ B ⊆ T.co ⁻¹' (M.X k).dom ∧ (∀ b ∈ B, F.u k (T.Pf (T.co b)) = spMap (ψ b).toRingHom ≫ y₀.x) ∧ ∀ t : p.R, DifferentiableOn ℂ (fun b => toC (ψ b t)) B := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M k T b₀ hb₀
  classical
  set D : Set (Fin T.m → ℂ) := T.co ⁻¹' (M.X k).dom with hD
  have hDo : IsOpen D := (FourierCoefficientDomain.isOpen_dom (M.X k)).preimage T.co.continuous
  have hu : IsHolTo D (fun b => F.u k (T.Pf (T.co b))) := (F.hol k T.m D _ hDo T.holPer).1
  have hw : ∀ b ∈ D, F.u k (T.Pf (T.co b)) ≫ Xo.s =
      spMap σ ≫ spMap (IntermediateField.inclusion c.le).toRingHom := fun b hb => by
    rw [F.over_σ k _ (T.isPer _ hb), spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  let a : (Fin T.m → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b =>
    if hb : b ∈ D then pullback.lift _ _ (hw b hb) else pullback.lift _ _ (hw b₀ hb₀)
  have ha₁ : ∀ b ∈ D, a b ≫ pullback.fst _ _ = F.u k (T.Pf (T.co b)) := fun b hb => by
    simp only [a, dif_pos hb, pullback.lift_fst]
  have ha₂ : ∀ b ∈ D, a b ≫ pullback.snd _ _ = spMap σ := fun b hb => by
    simp only [a, dif_pos hb, pullback.lift_snd]
  have ha : IsHolTo D a := GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
    (isHolTo_congr hu ha₁) (isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const hDo (spMap σ)) ha₂)
  obtain ⟨p, j, y₀, ⟨hj, hj₁, hj₂⟩, hz⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hS E H Dw l Xo c (a b₀ (default : PrimeSpectrum ℂ))
  obtain ⟨B, ψ, hBo, hb, hBD, hψ, hol⟩ := exists_coordinates ha j hb₀ hz
  have hc : ∀ b ∈ B, ∀ x, ψ b (algebraMap c.F p.R x) = σ x := fun b hb x => by
    have h₂ := ha₂ b (hBD hb)
    rw [hψ b hb, Category.assoc, hj₂, spMap, spMap, spMap, ← Spec.map_comp] at h₂
    exact congrArg (fun φ => φ.hom x) (Spec.map_injective h₂)
  let mk : ∀ b ∈ B, p.R →ₐ[c.F] CAt σ := fun b hb =>
    { toRingHom := (ψ b : p.R →+* CAt σ), commutes' := hc b hb }
  refine ⟨p, y₀, B, fun b => if h : b ∈ B then mk b h else mk b₀ hb, hBo, hb, hBD, fun b h => ?_, fun t => ?_⟩
  · simp only [dif_pos h]
    rw [← ha₁ b (hBD h), hψ b h, Category.assoc, hj₁]
    rfl
  · refine (hol t).congr fun b h => ?_
    simp only [dif_pos h]
    rfl

end GlobalTheory.HolChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsChartHolomorphicCoordinatesNearFrameStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding Unf GoodEmb relab perFr gxFst gxSnd toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_holomorphic_coordinates_near_frame : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b₀ ∈ T.co ⁻¹' (M.X k).dom, ∃ (p : TRing c.F) (y₀ : FrPt Xo c p.R) (B : Set (Fin T.m → ℂ)) (ψ : (Fin T.m → ℂ) → (p.R →ₐ[c.F] CAt σ)), IsOpen B ∧ b₀ ∈ B ∧ B ⊆ T.co ⁻¹' (M.X k).dom ∧ (∀ b ∈ B, F.u k (T.Pf (T.co b)) = spMap (ψ b).toRingHom ≫ y₀.x) ∧ ∀ t : p.R, DifferentiableOn ℂ (fun b => toC (ψ b t)) B := by
  first | exact @GlobalTheory.HolChart.exists_chart_holomorphic | exact GlobalTheory.HolChart.exists_chart_holomorphic | (intros; apply GlobalTheory.HolChart.exists_chart_holomorphic <;> assumption)
end
end
