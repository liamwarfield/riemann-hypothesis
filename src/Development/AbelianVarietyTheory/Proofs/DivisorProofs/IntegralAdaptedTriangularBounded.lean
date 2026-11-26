module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaPartialFourierIntegralMemAdelicSchwartz

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedTriangularBounded
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

namespace GlobalTheory.AnisoCocompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev finP : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

abbrev infP : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom

abbrev ratQ (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J

abbrev matA {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : HA (AF F) σ J) :
    Matrix (Fin M) (Fin M) (AF F ⊗[F] E) := (HA.mat (AF F) σ J g).1

theorem exists_finite_part (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) : ∃ C : Set (Af F ⊗[F] E), IsCompact C ∧
    ∀ g : HA (AF F) σ J, ∃ γ ∈ ratQ σ J, ∀ B : Matrix (Fin M) (Fin M) E, (∀ a b, IsIntegral ℤ (B a b)) →
      ∀ a b, finP ((matA (g * γ) * B.map (inclR (F := F) (AF F))) a b) ∈ C := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj σ J
  obtain ⟨S, hS⟩ := GlobalTheory.Mem.ClassFinite.exists_finset_classes F E σ hcm M J hJ _ (GlobalTheory.Mass.isOpen_stdLevel σ J)
  obtain ⟨C, hC, hCe⟩ := (GlobalTheory.Mass.intTens_open_compact F E).2
  obtain ⟨C₁, hC₁, hCe₁⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact_mul hC
    (S.finite_toSet.image fun s => (HA.mat (Af F) σ J s⁻¹).1)
  refine ⟨C₁, hC₁, fun g => ?_⟩
  obtain ⟨γ₀, s, hs, k, hk, e⟩ := hS (π g⁻¹)
  obtain ⟨γ, hγ, hγe⟩ : (γ₀.1 : HA (Af F) σ J) ∈ (GlobalTheory.Mass.ratIn (AF F) σ J).map π := by
    rw [hπ.map_ratIn]; exact γ₀.2
  refine ⟨γ, hγ, fun B hBi a b => ?_⟩
  have e' : π (g * γ) = k⁻¹ * s⁻¹ := by
    have e1 : π g⁻¹ = π γ * (s * k) := by rw [hγe]; exact e
    rw [map_mul, ← inv_inv g, map_inv, e1]; group
  generalize g * γ = x at e'
  have e3 : (matA x).map finP = (HA.mat (Af F) σ J k⁻¹).1 * (HA.mat (Af F) σ J s⁻¹).1 := by
    have := congrArg Units.val (hπ x)
    rw [e'] at this
    exact this.symm
  have e4 : finP ((matA x * B.map (inclR (F := F) (AF F))) a b) =
      ((matA x).map finP * (B.map (inclR (F := F) (AF F))).map finP) a b :=
    congrFun (congrFun (Matrix.map_mul (L := matA x) (M := B.map (inclR (F := F) (AF F))) (f := finP)) a) b
  rw [e4, e3]
  refine hCe₁ _ ⟨s, hs, rfl⟩ _ _ (fun a b => hCe _ ((GlobalTheory.Mass.mem_stdLevel _ _ _).1 (inv_mem hk) a b).1)
    (fun a b => hCe _ ?_) a b
  exact Subring.subset_closure (Or.inl ⟨⟨B a b, ⟨_, hBi a b⟩, rfl⟩, rfl⟩)

theorem exists_real_part (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : J.det ≠ 0) (han : ∀ x, x ≠ 0 → Formalism.UG.hform (σ : E →+* E) J x x ≠ 0)
    {I : Type} [Fintype I] {τ : I → (E →+* ℂ)} (hτ : GlobalTheory.Mem.Vol.IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, Formalism.MainNotions.StandardLattice.IsInfEmb (τ ρ) (θ ρ)) :
    ∃ (R : ℝ) (𝓒 : Set (Matrix (Fin M) (Fin M) E)), 𝓒.Finite ∧ ∀ x : HA (AF F) σ J,
      ∃ u ∈ ratQ σ J, ∃ B : Matrix (Fin M) (Fin M) E, ∃ N ∈ 𝓒,
        matA u = (B * N).map (inclR (F := F) (AF F)) ∧ (∀ a b, IsIntegral ℤ (B a b)) ∧
        ∀ a b ρ, ‖θ ρ (infP ((matA x * B.map (inclR (F := F) (AF F))) a b))‖ ≤ R := by
  haveI := hcm.2.1
  obtain ⟨R, 𝓒, h𝓒, H⟩ := GlobalTheory.Mem.AnisoQuotient.exists_bounded_unitary (σ := (σ : E →+* E)) hτ
    (fun ρ x => hcm.2.2.2 _ x) hJ han
  refine ⟨R, 𝓒, h𝓒, fun x => ?_⟩
  let p : AF F ⊗[F] E →+* (I → ℂ) := Pi.ringHom fun ρ => (θ ρ).comp infP
  have hp : ∀ N : Matrix (Fin M) (Fin M) E, (N.map (inclR (F := F) (AF F))).map p = N.map (Pi.ringHom τ) :=
    fun N => by ext i j ρ; exact (hθ ρ).1 _
  have hev : ∀ (ρ : I) (X : Matrix (Fin M) (Fin M) (I → ℂ)), X.map (Pi.evalRingHom (fun _ => ℂ) ρ) = X.map (fun z => z ρ) :=
    fun _ _ => rfl
  obtain ⟨u, hu, B, N, hN, hum, hBi, hBR⟩ := H ((matA x).map p) (by
    ext i j ρ
    have h1 := congrFun (congrFun (GlobalTheory.Mem.VolExists.infMat_unitary J hcm (hθ ρ) x) i) j
    have h2 : ((Formalism.UG.cT (starRingEnd (I → ℂ)) ((matA x).map p) * J.map (Pi.ringHom τ) * (matA x).map p).map
        (Pi.evalRingHom (fun _ => ℂ) ρ)) = (Formalism.MainNotions.StandardLattice.infMat σ J (θ ρ) x).conjTranspose * J.map (τ ρ) *
        Formalism.MainNotions.StandardLattice.infMat σ J (θ ρ) x := by
      have e1 : ((matA x).map p).map (Pi.evalRingHom (fun _ => ℂ) ρ) = Formalism.MainNotions.StandardLattice.infMat σ J (θ ρ) x := by
        ext a b; rfl
      have e2 : (Formalism.UG.cT (starRingEnd (I → ℂ)) ((matA x).map p)).map (Pi.evalRingHom (fun _ => ℂ) ρ) =
          (Formalism.MainNotions.StandardLattice.infMat σ J (θ ρ) x).conjTranspose := by
        rw [← e1]; ext a b; rfl
      have e3 : (J.map (Pi.ringHom τ)).map (Pi.evalRingHom (fun _ => ℂ) ρ) = J.map (τ ρ) := by
        ext a b; rfl
      rw [Matrix.map_mul, Matrix.map_mul, e1, e2, e3]
    have h3 := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply, Pi.evalRingHom_apply] at h3
    rw [h3, h1]
    rfl)
  refine ⟨⟨_, GlobalTheory.Mem.ClassFinite.baseChange_mem (AF F) σ J u hu⟩, ⟨u, hu, rfl⟩, B, N, hN,
    congrArg (fun X => X.map (inclR (F := F) (AF F))) hum, hBi, fun a b ρ => ?_⟩
  have := hBR a b
  rw [← hp, ← Matrix.map_mul] at this
  exact (norm_le_pi_norm (p ((matA x * B.map (inclR (F := F) (AF F))) a b)) ρ).trans this

theorem exists_compact (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (han : ∀ x, x ≠ 0 → Formalism.UG.hform (σ : E →+* E) J x x ≠ 0) :
    ∃ K : Set (HA (AF F) σ J), IsCompact K ∧ ∀ g, ∃ γ ∈ ratQ σ J, ∃ k ∈ K, g = γ * k := by
  haveI := hcm.1
  let τ : InfinitePlace E → (E →+* ℂ) := fun w => w.embedding
  have hτ : GlobalTheory.Mem.Vol.IsCMFam τ := by
    have : (fun w => InfinitePlace.mk (τ w)) = id := funext fun w => InfinitePlace.mk_embedding w
    unfold GlobalTheory.Mem.Vol.IsCMFam; rw [this]; exact Function.bijective_id
  choose θ hθ1 hθ2 using fun ρ => GlobalTheory.InfAdeleCM.exists_hom (F := F) (τ ρ)
  have hθ : ∀ ρ, Formalism.MainNotions.StandardLattice.IsInfEmb (τ ρ) (θ ρ) := fun ρ => ⟨hθ1 ρ, hθ2 ρ⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (HA (AF F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J))
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨C₁, hC₁, H₁⟩ := exists_finite_part σ hcm J hJ
  obtain ⟨R, 𝓒, h𝓒, H₂⟩ := exists_real_part σ hcm J hJ.2 han hτ hθ
  obtain ⟨C₂, hC₂, hCe₂⟩ := GlobalTheory.Mem.VolExists.exists_compact_adele hcm hτ hθ R C₁ hC₁
  obtain ⟨C₃, hC₃, hCe₃⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact_mul ((hC₂.insert 0).insert 1)
    (h𝓒.image fun N => N.map (inclR (F := F) (AF F)))
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF F) σ J hJ.2 C₃ hC₃
  refine ⟨Inv.inv '' K, hK.image continuous_inv, fun g => ?_⟩
  obtain ⟨γ, hγ, h₁⟩ := H₁ g⁻¹
  obtain ⟨u, hu, B, N, hN, hum, hBi, hBR⟩ := H₂ (g⁻¹ * γ)
  refine ⟨γ * u, mul_mem hγ hu, (g⁻¹ * γ * u)⁻¹, ⟨_, hKe _ fun a b => ?_, rfl⟩, by group⟩
  have e : matA (g⁻¹ * γ * u) = matA (g⁻¹ * γ) * B.map (inclR (F := F) (AF F)) *
      N.map (inclR (F := F) (AF F)) * 1 := by
    rw [show matA (g⁻¹ * γ * u) = matA (g⁻¹ * γ) * matA u from rfl, hum, Matrix.map_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  change matA (g⁻¹ * γ * u) a b ∈ C₃
  rw [e]
  refine hCe₃ _ ⟨N, hN, rfl⟩ _ _ (fun a b => Or.inr (Or.inr (hCe₂ _ (h₁ B hBi a b) (hBR a b)))) (fun a b => ?_) a b
  rw [Matrix.one_apply]
  split_ifs
  exacts [Or.inl rfl, Or.inr (Or.inl rfl)]

end GlobalTheory.AnisoCocompact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFormOperatorAct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFormOperatorAct
open NumberField GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.CuspStabFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem zfin_of_comm (T : Module.End ℂ (Sm E a)) (hT : ∀ z ∈ Zalg E a, z * T = T * z) {φ : Sm E a}
    (h : FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a))) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z (T φ)) '' Zalg E a)) := by
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
    Zalg E a)).map T) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z φ, Submodule.subset_span ⟨z, hz, rfl⟩, (LinearMap.congr_fun (hT z hz) φ).symm⟩

theorem zalg_comm_fin (k : GL (Fin a) (Af E)) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    z * finRep E a k = finRep E a k * z := by
  let S := Subalgebra.centralizer ℂ ({finRep E a k} : Set (Module.End ℂ (Sm E a)))
  have hL : ∀ X, lie E a X ∈ S := fun X T hT => by
    rw [Set.mem_singleton_iff.1 hT]; exact (lie_rt_fin X k).symm
  have hE : ∀ τ i j, Eop (a := a) τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hL _) (S.smul_mem (hL _) _)) _
  have hS : Zalg E a ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact (hS hz (finRep E a k) rfl).symm

theorem level_of_le {φ ψ : Sm E a} (h : IsOpen {k | finRep E a k φ = φ})
    (hle : ∀ k, finRep E a k φ = φ → finRep E a k ψ = ψ) : IsOpen {k | finRep E a k ψ = ψ} :=
  isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.mem_nhds (by simp)) fun k hk => hle k hk)

theorem fin_cpt_comm (k : GL (Fin a) (Af E)) (c : Kinf E a) :
    finRep E a k * cptRep E a c = cptRep E a c * finRep E a k := by
  change rt E a (finGL E a k) * rt E a (infGL E a (Unitary.toUnits c)) =
    rt E a (infGL E a (Unitary.toUnits c)) * rt E a (finGL E a k)
  rw [← map_mul, ← map_mul, infGL_comm]

theorem height_mul_le_const (c : GL (Fin a) (Cinf E)) : ∃ B : ℝ, 1 ≤ B ∧ ∀ y, height (y * c) ≤ B * height y := by
  refine ⟨1 + ‖rmul (toL c.val)‖ + ‖lmul (toL (c⁻¹).val)‖, by linarith [norm_nonneg (rmul (toL c.val)), norm_nonneg (lmul (toL (c⁻¹).val))], fun y => ?_⟩
  have h1 : toL (y * c).val = rmul (toL c.val) (toL y.val) := rfl
  have h2 : toL ((y * c)⁻¹).val = lmul (toL (c⁻¹).val) (toL (y⁻¹).val) := by
    rw [_root_.mul_inv_rev]; rfl
  have e1 := (rmul (toL c.val)).le_opNorm (toL y.val)
  have e2 := (lmul (toL (c⁻¹).val)).le_opNorm (toL (y⁻¹).val)
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (rmul (toL c.val))
  have n4 := norm_nonneg (lmul (toL (c⁻¹).val))
  unfold height
  rw [h1, h2]
  nlinarith

theorem growth_mul_const {f : GL (Fin a) (Cinf E) → ℂ} (c : GL (Fin a) (Cinf E))
    (h : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * height y ^ N) :
    ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f (y * c)‖ ≤ C * height y ^ N := by
  obtain ⟨C, N, hC⟩ := h
  obtain ⟨B, hB, hB'⟩ := height_mul_le_const c
  have C0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N := pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left this hp
  refine ⟨C * B ^ N, N, fun y => (hC _).trans ?_⟩
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (y * c)]) (hB' y) N) C0

theorem isCuspForm_act' (hP : GlobalTheory.Published.AutomorphicFormsFiniteGL) (o : Op E a) (φ : Sm E a) (h : IsCuspForm φ) : IsCuspForm (act o φ) := by
  obtain ⟨hA, hC⟩ := h
  cases o with
  | fin k =>
    refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
    · change φ.1 (ratGL E a γ * g * finGL E a k) = φ.1 (g * finGL E a k)
      rw [mul_assoc, hA.left]
    · have e : {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ} =
          (fun k' => k⁻¹ * k' * k) ⁻¹' {k' | finRep E a k' φ = φ} := by
        ext k'
        simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul]
        constructor
        · intro e
          rw [Module.End.mul_apply, Module.End.mul_apply, e, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
            map_one, Module.End.one_apply]
        · intro e
          have := congrArg (finRep E a k) e
          rwa [Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (finRep E a k), ← map_mul,
            mul_inv_cancel, map_one, Module.End.one_apply] at this
      change IsOpen {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ}
      rw [e]
      exact hA.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · have := hA.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun c => cptRep E a c φ)).map
        (finRep E a k)) (Submodule.span_le.2 ?_)
      rintro _ ⟨c, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨c, rfl⟩, (LinearMap.congr_fun (fin_cpt_comm k c) φ)⟩
    · exact zfin_of_comm _ (fun z hz => zalg_comm_fin k hz) hA.zfin
    · obtain ⟨C, N, h1⟩ := hA.growth (g * finGL E a k)
      refine ⟨C, N, fun y => ?_⟩
      change ‖φ.1 (g * infGL E a y * finGL E a k)‖ ≤ _
      rw [mul_assoc, infGL_comm, ← mul_assoc]
      exact h1 y
    · intro r h0 h1 _ _ μ 𝓕 hμ hF g
      change ∫ x in 𝓕, φ.1 (unip x * g * finGL E a k) ∂μ = 0
      simp_rw [mul_assoc]
      exact hC r h0 h1 μ 𝓕 hμ hF (g * finGL E a k)
  | cpt c =>
    refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
    · change φ.1 (ratGL E a γ * g * infGL E a (Unitary.toUnits c)) = φ.1 (g * infGL E a (Unitary.toUnits c))
      rw [mul_assoc, hA.left]
    · exact level_of_le hA.level fun k hk => by
        change finRep E a k (cptRep E a c φ) = cptRep E a c φ
        rw [← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk]
    · have := hA.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun c => cptRep E a c φ))
        (Submodule.span_le.2 ?_)
      rintro _ ⟨c', rfl⟩
      refine Submodule.subset_span ⟨c' * c, ?_⟩
      change _ = (cptRep E a c' * cptRep E a c) φ
      rw [← map_mul]
    · exact zfin_of_comm _ (fun z hz => GlobalTheory.T.mem_zalg_commute_compactRep E a c z hz) hA.zfin
    · obtain ⟨C, N, h1⟩ := growth_mul_const (Unitary.toUnits c) (hA.growth g)
      refine ⟨C, N, fun y => ?_⟩
      change ‖φ.1 (g * infGL E a y * infGL E a (Unitary.toUnits c))‖ ≤ _
      rw [mul_assoc, ← map_mul]
      exact h1 y
    · intro r h0 h1 _ _ μ 𝓕 hμ hF g
      change ∫ x in 𝓕, φ.1 (unip x * g * infGL E a (Unitary.toUnits c)) ∂μ = 0
      simp_rw [mul_assoc]
      exact hC r h0 h1 μ 𝓕 hμ hF (g * infGL E a (Unitary.toUnits c))
  | lie X =>
    refine ⟨⟨fun γ g => ?_, ?_, GlobalTheory.T.finiteDimensional_span_compact_orbit_lieDerivative E a X φ hA.kfin, zfin_of_comm _ (fun z hz => GlobalTheory.T.mem_zalg_commute_lie_action E a X z hz) hA.zfin, GlobalTheory.AutGrowth.lie_growth_of_finite hP E a X φ hA⟩,
      GlobalTheory.T.isCuspidal_lieAction_of_isCuspForm E a X φ ⟨hA, hC⟩⟩
    · change lieD X φ.1 (ratGL E a γ * g) = lieD X φ.1 g
      have e : chart φ.1 (ratGL E a γ * g) = chart φ.1 g := by
        funext x
        unfold chart
        split_ifs
        · rw [mul_assoc, hA.left]
        · rfl
      unfold lieD
      rw [e]
    · exact level_of_le hA.level fun k hk => by
        change finRep E a k (lie E a X φ) = lie E a X φ
        change (rt E a (finGL E a k) * lie E a X) φ = _
        rw [← lie_rt_fin, Module.End.mul_apply]
        exact congrArg (lie E a X) hk

end GlobalTheory.CuspStabFin

theorem GlobalTheory.CuspStabFin.isCuspForm_act : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (o : GlobalTheory.CuspRep.Op E a) (φ : GlobalTheory.CuspRep.Sm E a),
    GlobalTheory.CuspRep.IsCuspForm φ → GlobalTheory.CuspRep.IsCuspForm (GlobalTheory.CuspRep.act o φ) :=
  fun hP _ _ _ _ _ o φ h => GlobalTheory.CuspStabFin.isCuspForm_act' hP o φ h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFormOperatorActStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspForm_operator_act : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (o : Op E a) (φ : Sm E a), IsCuspForm φ → IsCuspForm (act o φ) := by
  first | exact @GlobalTheory.CuspStabFin.isCuspForm_act | exact GlobalTheory.CuspStabFin.isCuspForm_act | (intros; apply GlobalTheory.CuspStabFin.isCuspForm_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicColumnsExtendWitt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWittFrameInitCols
noncomputable section

namespace GlobalTheory.AdjugateAppendColumn

open Matrix

section General

variable {E : Type} [Field E] (s : E →+* E)

def adj {a b : Type} (A : Matrix a b E) : Matrix b a E := (A.map s)ᵀ

theorem adj_mul {a b c : Type} [Fintype b] (A : Matrix a b E) (B : Matrix b c E) :
    adj s (A * B) = adj s B * adj s A := by
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul]

theorem adj_one {a : Type} [DecidableEq a] : adj s (1 : Matrix a a E) = 1 := by
  simp only [adj, Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

theorem adj_sub {a b : Type} (A B : Matrix a b E) : adj s (A - B) = adj s A - adj s B := by
  ext i j; simp [adj]

theorem adj_smul {a b : Type} (c : E) (A : Matrix a b E) : adj s (c • A) = s c • adj s A := by
  ext i j; simp [adj]

theorem adj_adj (hs : ∀ x, s (s x) = x) {a b : Type} (A : Matrix a b E) : adj s (adj s A) = A := by
  ext i j; simp [adj, hs]

variable {n m : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem exists_left_inv {X : Matrix (Fin n) (Fin m) E} (hX : LinearIndependent E Xᵀ) :
    ∃ L : Matrix (Fin m) (Fin n) E, L * X = 1 := by
  have hi : Function.Injective X.mulVec := Matrix.mulVec_injective_iff.2 hX
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' X) (LinearMap.ker_eq_bot.2 hi)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem exists_dual [CharZero E] (hs : ∀ x, s (s x) = x) (hJ : adj s J = J) (hd : J.det ≠ 0)
    {X : Matrix (Fin n) (Fin m) E} (hX : LinearIndependent E Xᵀ) (h0 : adj s X * J * X = 0) :
    ∃ Y : Matrix (Fin n) (Fin m) E, adj s X * J * Y = 1 ∧ adj s Y * J * X = 1 ∧ adj s Y * J * Y = 0 := by
  obtain ⟨L, hL⟩ := exists_left_inv hX
  have flip : ∀ Z : Matrix (Fin n) (Fin m) E, adj s X * J * Z = 1 → adj s Z * J * X = 1 := fun Z hZ => by
    have := congrArg (adj s) hZ
    rwa [adj_mul, adj_mul, adj_adj s hs, hJ, adj_one, ← Matrix.mul_assoc] at this
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin n) (Fin m) E, adj s X * J * Z = 1 := ⟨J⁻¹ * adj s L, by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd.isUnit, ← adj_mul, hL, adj_one]⟩
  obtain ⟨G, hG⟩ : ∃ G, G = adj s Z * J * Z := ⟨_, rfl⟩
  have h1 : adj s X * J * (Z - (2 : E)⁻¹ • (X * G)) = 1 := by
    rw [Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, h0, hZ, Matrix.zero_mul, smul_zero, sub_zero]
  refine ⟨_, h1, flip _ h1, ?_⟩
  have hGG : adj s G = G := by
    rw [hG, adj_mul, adj_mul, adj_adj s hs, hJ, Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc _ X G, flip _ h1, Matrix.one_mul, adj_sub, adj_smul, adj_mul, hGG,
    Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc G, Matrix.mul_assoc G, hZ,
    Matrix.mul_one, ← hG, map_inv₀, map_ofNat, sub_sub, ← add_smul, show (2 : E)⁻¹ + 2⁻¹ = 1 by norm_num, one_smul, sub_self]

theorem gram_apply {a b : Type} (A : Matrix (Fin n) a E) (B : Matrix (Fin n) b E) (i : a) (j : b) :
    (adj s A * J * B) i j = (fun k => s (Aᵀ i k)) ⬝ᵥ J *ᵥ (Bᵀ j) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]; rfl

theorem form_symm (hs : ∀ x, s (s x) = x) (hJ : adj s J = J) (x y : Fin n → E) :
    s ((fun k => s (x k)) ⬝ᵥ J *ᵥ y) = (fun k => s (y k)) ⬝ᵥ J *ᵥ x := by
  have e : ∀ i j, s (J j i) = J i j := fun i j => congrFun (congrFun hJ i) j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hs, e, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def app (X : Matrix (Fin n) (Fin m) E) (z : Fin n → E) : Matrix (Fin n) (Fin (m + 1)) E :=
  (Matrix.of (Fin.snoc (α := fun _ => Fin n → E) Xᵀ z))ᵀ

theorem app_transpose (X : Matrix (Fin n) (Fin m) E) (z : Fin n → E) :
    (app X z)ᵀ = Fin.snoc (α := fun _ => Fin n → E) Xᵀ z := rfl

theorem app_last (X : Matrix (Fin n) (Fin m) E) (z : Fin n → E) : (app X z)ᵀ (Fin.last m) = z :=
  Fin.snoc_last (α := fun _ => Fin n → E) z Xᵀ

theorem app_cast (X : Matrix (Fin n) (Fin m) E) (z : Fin n → E) (i : Fin m) : (app X z)ᵀ i.castSucc = Xᵀ i :=
  Fin.snoc_castSucc (α := fun _ => Fin n → E) z Xᵀ i

theorem exists_ext [CharZero E] (hs : ∀ x, s (s x) = x) (hJ : adj s J = J) (hd : J.det ≠ 0) (k : ℕ) :
    ∀ (m : ℕ) (C : Matrix (Fin n) (Fin m) E), n ≤ m + k → LinearIndependent E Cᵀ → adj s C * J * C = 0 →
      ∃ (m' : ℕ) (hm : m ≤ m') (X Y : Matrix (Fin n) (Fin m') E), adj s X * J * X = 0 ∧ adj s Y * J * Y = 0 ∧
        adj s X * J * Y = 1 ∧ (∀ z : Fin n → E, (adj s X * J) *ᵥ z = 0 → (adj s Y * J) *ᵥ z = 0 →
          (fun k => s (z k)) ⬝ᵥ J *ᵥ z = 0 → z = 0) ∧ X.submatrix id (Fin.castLE hm) = C := by
  have step : ∀ (m : ℕ) (C Y : Matrix (Fin n) (Fin m) E) (z : Fin n → E), LinearIndependent E Cᵀ → adj s C * J * C = 0 →
      adj s Y * J * C = 1 → (adj s C * J) *ᵥ z = 0 → (adj s Y * J) *ᵥ z = 0 → (fun k => s (z k)) ⬝ᵥ J *ᵥ z = 0 → z ≠ 0 →
      LinearIndependent E (app C z)ᵀ ∧ adj s (app C z) * J * app C z = 0 := by
    intro m C Y z hC h0 h1 a b c hz
    constructor
    · rw [app_transpose]
      refine linearIndependent_finSnoc.2 ⟨hC, fun hm => hz ?_⟩
      obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hm
      have e : C *ᵥ u = z := by
        rw [← hu]; funext i; simp [Matrix.mulVec, dotProduct, mul_comm]
      rw [← e, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at b
      rw [← e, b, Matrix.mulVec_zero]
    · have a' : ∀ i, (fun k => s (Cᵀ i k)) ⬝ᵥ J *ᵥ z = 0 := fun i => by
        have := congrFun a i
        rw [← Matrix.mulVec_mulVec] at this
        exact this
      ext i j
      rw [gram_apply, Matrix.zero_apply]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rw [app_last]; exact c
        | cast j =>
          rw [app_last, app_cast, ← form_symm s hs hJ, a', map_zero]
      | cast i =>
        induction j using Fin.lastCases with
        | last => rw [app_last, app_cast]; exact a' i
        | cast j =>
          rw [app_cast, app_cast, ← gram_apply, h0, Matrix.zero_apply]
  induction k with
  | zero =>
    intro m C hm hC h0
    obtain ⟨Y, h1, h2, h3⟩ := exists_dual s hs hJ hd hC h0
    refine ⟨m, le_rfl, C, Y, h0, h3, h1, fun z a b c => ?_, rfl⟩
    by_contra hz
    have := (step m C Y z hC h0 h2 a b c hz).1.fintype_card_le_finrank
    simp at this
    omega
  | succ k ih =>
    intro m C hm hC h0
    obtain ⟨Y, h1, h2, h3⟩ := exists_dual s hs hJ hd hC h0
    by_cases H : ∀ z : Fin n → E, (adj s C * J) *ᵥ z = 0 → (adj s Y * J) *ᵥ z = 0 →
      (fun k => s (z k)) ⬝ᵥ J *ᵥ z = 0 → z = 0
    · exact ⟨m, le_rfl, C, Y, h0, h3, h1, H, rfl⟩
    push Not at H
    obtain ⟨z, a, b, c, hz⟩ := H
    obtain ⟨p, q⟩ := step m C Y z hC h0 h2 a b c hz
    obtain ⟨m', hm', X, Y', x1, x2, x3, x4, x5⟩ := ih (m + 1) (app C z) (by omega) p q
    refine ⟨m', by omega, X, Y', x1, x2, x3, x4, ?_⟩
    ext i j
    have := congrFun (congrFun x5 i) j.castSucc
    have e : app C z i j.castSucc = C i j := congrFun (app_cast C z j) i
    exact this.trans e

end General

theorem exists_wittFrame_initCols (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E)
    (hJ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J) (r : ℕ) (C : Matrix (Fin n) (Fin (r + 1)) E)
    (hC : LinearIndependent E (Matrix.transpose C)) (h0 : Formalism.UG.cT (σ : E →+* E) C * J * C = 0) :
    ∃ (m : ℕ) (hm : r < m) (X : Matrix (Fin n) (Fin m) E) (Y : Matrix (Fin n) (Fin m) E),
      GlobalTheory.SiegelSet.IsWittFrame σ J X Y ∧ GlobalTheory.StdPar.initCols X (⟨r, hm⟩ : Fin m) = C := by
  have hs : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have := h.2.2.2 τ
    simp only [RingHom.coe_coe]
    rw [this, this, star_star]
  obtain ⟨m, hm, X, Y, x1, x2, x3, x4, x5⟩ := exists_ext (σ : E →+* E) (J := J) hs (Matrix.ext fun i j => hJ.1 i j) hJ.2
    n (r + 1) C (by omega) hC h0
  refine ⟨m, hm, X, Y, ⟨x1, x2, x3, fun z a b c => x4 z a b ?_⟩, x5⟩
  simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, Formalism.UG.hform] at c
  simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using c

end GlobalTheory.AdjugateAppendColumn

end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
noncomputable section

namespace GlobalTheory.WittExt

open Matrix
open Formalism.UG (cT)

theorem exists_isWittFrame_initCols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (C : Matrix (Fin n) (Fin (r + 1)) E),
      LinearIndependent E C.transpose → Formalism.UG.cT (σ : E →+* E) C * J * C = 0 →
        ∃ (m : ℕ) (hm : r < m) (X Y : Matrix (Fin n) (Fin m) E), IsWittFrame σ J X Y ∧ GlobalTheory.StdPar.initCols X ⟨r, hm⟩ = C := by
  first
  | exact @_root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols
  | exact _root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols
  | (apply _root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols ..)

end GlobalTheory.WittExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCMRealLineAddNoPhase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCMRealLineAddNoPhase
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.HeisLineF

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cAF_incAF (σ : E →ₐ[F] E) (x : E) : cAF σ (incAF F E x) = incAF F E (σ x) := by
  simp [cAF, incAF, sigR, inclR]

theorem cAF_cAF (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : AEF F E) : cAF σ (cAF σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cAF, sigR, hσ]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem trace_cAF (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : AEF F E) :
    Algebra.trace (AF F) (AEF F E) (cAF σ a) = Algebra.trace (AF F) (AEF F E) a := by
  let f : AEF F E →ₐ[AF F] AEF F E := Algebra.TensorProduct.map (AlgHom.id _ _) σ
  have hf : ∀ a, f a = cAF σ a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [f, cAF, sigR]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  have hff : f.comp f = AlgHom.id _ _ := AlgHom.ext fun a => by
    rw [AlgHom.comp_apply, hf, hf, cAF_cAF σ hσ]; rfl
  let g : AEF F E ≃ₐ[AF F] AEF F E := AlgEquiv.ofAlgHom f f hff hff
  rw [← hf]
  exact Algebra.trace_eq_of_algEquiv g a

theorem herm_sum {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (P : Fin m → Fin m → A)
    (Q : Fin n → Fin n → A) (hP : ∀ i k, σ (P i k) = P k i) (hQ : ∀ i k, σ (Q i k) = Q k i)
    (x y : Matrix (Fin n) (Fin m) A) :
    σ (∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a) =
      ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (x c b) * Q c d * y d a := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hσ, hP, hQ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem inv_herm (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (i k : Fin n) :
    σ (J⁻¹ i k) = J⁻¹ k i := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
  have hT : Jᵀ = J.map σ := by
    ext i j
    simp [Matrix.transpose_apply, hJ.1 j i]
  have h1 : J⁻¹.map σ * Jᵀ = 1 := by
    rw [hT, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu]
    simp
  have h2 : (Jᵀ)⁻¹ = J⁻¹.map σ := Matrix.inv_eq_left_inv h1
  rw [← Matrix.transpose_nonsing_inv] at h2
  have := congrFun (congrFun h2 i) k
  simpa [Matrix.transpose_apply] using this.symm

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)

theorem hOF_herm (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (x y : WOF F E nS nT) :
    cAF σ (hOF σ JS JT x y) = hOF σ JS JT y x :=
  herm_sum (cAF σ) (cAF_cAF σ hσ) (fun i k => incAF F E (JS⁻¹ i k)) (fun i k => incAF F E (JT i k))
    (fun i k => by rw [cAF_incAF, inv_herm σ hS]) (fun i k => by rw [cAF_incAF, hT.1 k i]) x y

theorem symplOF_skew (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (ξ₀ : E) (hξ : σ ξ₀ = -ξ₀)
    (x y : WOF F E nS nT) : symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y := by
  unfold symplOF
  rw [← trace_cAF σ hσ (incAF F E ξ₀ * hOF σ JS JT x y), map_mul (cAF σ), cAF_incAF, hξ, hOF_herm σ JS JT hσ hS hT,
    map_neg, neg_mul, map_neg, neg_neg]

theorem symplOF_add_left (ξ₀ : E) (x x' y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (x + x') y = symplOF σ JS JT ξ₀ x y + symplOF σ JS JT ξ₀ x' y := by
  unfold symplOF hOF
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOF_add_right (ξ₀ : E) (x y y' : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ x (y + y') = symplOF σ JS JT ξ₀ x y + symplOF σ JS JT ξ₀ x y' := by
  unfold symplOF hOF
  simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOHF_add_left (ξ₀ : E) (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ (x + x') y = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x' y := by
  unfold symplOHF; rw [symplOF_add_left, mul_add]

theorem symplOHF_add_right (ξ₀ : E) (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ x (y + y') = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y' := by
  unfold symplOHF; rw [symplOF_add_right, mul_add]

theorem symplOF_zero_right (ξ₀ : E) (x : WOF F E nS nT) : symplOF σ JS JT ξ₀ x 0 = 0 := by
  have := symplOF_add_right σ JS JT ξ₀ x 0 0
  rw [add_zero] at this
  exact left_eq_add.mp this

theorem symplOF_self (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (ξ₀ : E) (hξ : σ ξ₀ = -ξ₀)
    (x : WOF F E nS nT) : symplOF σ JS JT ξ₀ x x = 0 := by
  have h := symplOF_skew σ JS JT hσ hS hT ξ₀ hξ x x
  have h2 : (2 : AF F) * symplOF σ JS JT ξ₀ x x = 0 := by
    rw [two_mul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  have hu : IsUnit (2 : AF F) := by
    have : (2 : AF F) = algebraMap F (AF F) 2 := (map_ofNat _ 2).symm
    rw [this]
    exact (isUnit_iff_ne_zero.mpr two_ne_zero).map _
  exact hu.mul_right_eq_zero.mp h2

theorem continuous_symplOF_left (ξ₀ : E) (y : WOF F E nS nT) :
    Continuous fun x : WOF F E nS nT => symplOF σ JS JT ξ₀ x y := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AEF F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have ht : Continuous (Algebra.trace (AF F) (AEF F E)) := IsModuleTopology.continuous_of_linearMap _
  refine ht.comp (continuous_const.mul ?_)
  unfold hOF
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun c _ =>
    continuous_finsetSum _ fun d _ => continuous_const.mul (continuous_id.matrix_elem d a)

omit [Algebra F E] [Field E] [NumberField E] in
theorem line_zero (g : ℝ →+ AF F) (hg : Continuous g) (t : ℝ) (ht : g t = 0) (u : ℝ) : g (u * t) = 0 := by
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have hq : ∀ r : ℚ, g ((r : ℝ) * t) = 0 := by
    intro r
    have hden : (r.den : ℝ) * ((r : ℝ) * t) = (r.num : ℝ) * t := by
      rw [← mul_assoc]
      congr 1
      have := congrArg (Rat.cast : ℚ → ℝ) (Rat.den_mul_eq_num r)
      push_cast at this
      exact this
    have h1 : r.den • g ((r : ℝ) * t) = 0 := by
      rw [← map_nsmul, nsmul_eq_mul, hden, ← zsmul_eq_mul, map_zsmul, ht, smul_zero]
    have hu : IsUnit ((r.den : ℕ) : AF F) := by
      have : ((r.den : ℕ) : AF F) = algebraMap F (AF F) (r.den : F) := (map_natCast _ _).symm
      rw [this]
      exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast r.den_nz)).map _
    rw [nsmul_eq_mul] at h1
    exact hu.mul_right_eq_zero.mp h1
  have : (fun u : ℝ => g (u * t)) = fun _ => 0 :=
    Rat.denseRange_cast.equalizer (hg.comp (continuous_id.mul continuous_const)) continuous_const (funext hq)
  exact congrFun this u

end GlobalTheory.HeisLineF

open GlobalTheory.HeisLineF in
theorem GlobalTheory.heisOF_line_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ) (w : Formalism.IndefR.DatumF.WOF F E nS nT) (s t : ℝ),
      Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L (s + t)) f w = B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ w (L s)) * Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L s) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ _ L hL _ f w s t
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  have key : Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ (L s) (L t) = 0 := by
    by_cases ht : t = 0
    · rw [ht, map_zero L, symplOF_zero_right]
    · let g : ℝ →+ AF F := AddMonoidHom.mk' (fun u => Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ (L u) (L t))
        (fun a b => by simp only [map_add L, symplOF_add_left])
      have hg : Continuous g := (continuous_symplOF_left σ JS JT ξ₀ (L t)).comp hL
      have h0 : g t = 0 := symplOF_self σ JS JT hσ hS hT ξ₀ hξ (L t)
      have := line_zero g hg t h0 (s / t)
      rwa [div_mul_cancel₀ s ht] at this
  have k2 : Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (L s) (L t) = 0 := by
    unfold Formalism.IndefR.DatumF.symplOHF; rw [key, mul_zero]
  unfold Formalism.IndefR.DatumF.heisOF
  rw [map_add L, symplOHF_add_right, symplOHF_add_left, k2, add_zero, AddChar.map_add_eq_mul, add_assoc, mul_assoc]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCMRealLineAddNoPhaseStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOp_realLine_add_eq_phase_mul_shifted : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ) (w : Formalism.IndefR.DatumF.WOF F E nS nT) (s t : ℝ),
      Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L (s + t)) f w = B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ w (L s)) * Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L s) := by
  first | exact @GlobalTheory.heisOF_line_add | exact GlobalTheory.heisOF_line_add | (intros; apply GlobalTheory.heisOF_line_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunOOfMatchedSquareBigRoute
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunOOfMatchedSquareBigRoute
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RouteSeesaw

theorem isThetaFunO_of_isMatched : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ d ∈ Θ.support, IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) d.2 := by
  intro D T L sc G μ₀ _hL W B ρ t i j Θ Θ' hM d hd
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, hF, rfl, -⟩ := hM
  obtain ⟨e, -, -, φ₁, φ₂, hφ, -⟩ := hF
  unfold tensT at hd
  obtain ⟨P, -, hd⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d', hd', hd⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  have hd := Finsupp.support_single_subset hd
  rw [Finset.mem_singleton] at hd
  subst hd
  obtain ⟨h₁, h₂⟩ := hφ d' hd'
  have v₁ := (ρ.vX_is i (j + 1) i.2 j.2).2.2
  have v₂ := (ρ.vT_is t (i + 1) j i.2 j.2).2.2
  exact ⟨GlobalTheory.FockTheta.ptStable D _ _ W.ψ_std W.θ_is _ _ _ _ _ _ _ _
      (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h₁.2 v₁),
    GlobalTheory.FockTheta.ptStable D _ _ W.ψ_std W.θ_is _ _ _ _ _ _ _ _
      (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h₂.2 v₂)⟩

end GlobalTheory.RouteSeesaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunOOfMatchedSquareBigRouteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunO_of_matchedSquare_bigRoute : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ d ∈ Θ.support, IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) d.2 := by
  first | exact @GlobalTheory.RouteSeesaw.isThetaFunO_of_isMatched | exact GlobalTheory.RouteSeesaw.isThetaFunO_of_isMatched | (intros; apply GlobalTheory.RouteSeesaw.isThetaFunO_of_isMatched <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOfMem
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SchwartzAInt

open GlobalTheory.RegSch.IkSchwartz GlobalTheory.PartialIntegral


set_option maxHeartbeats 800000 in
theorem integrable_pure {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (μ : Measure (Mx D m n))
    [μ.IsAddHaarMeasure] (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ) (g : (Fin m → Fin n → AEf D) → ℂ)
    (hg : g ∈ WeilM.SB (Fin m → Fin n → AEf D)) :
    Integrable (fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))) μ := by
  haveI : IsModuleTopology (Af D.host.F) (AEf D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AEf D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  haveI : LocallyCompactSpace (AEf D) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AEf D) := e0.secondCountableTopology
  haveI : T2Space (AEf D) := e0.isEmbedding.t2Space
  letI : MeasurableSpace (Fin m → Fin n → AEf D) := borel _
  haveI : BorelSpace (Fin m → Fin n → AEf D) := ⟨rfl⟩
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := (lattice_Mx D m n).1
  obtain ⟨e, he⟩ := exists_split hθ m n
  let μr : Measure (D.what₂.Tau → Fin m → Fin n → ℂ) := Measure.addHaar
  let ν : Measure (Fin m → Fin n → AEf D) := Measure.addHaar
  obtain ⟨c, hc⟩ := exists_integral_split e μ μr ν
  have hf : Integrable (fun x => f x) μr := f.integrable
  have hg' : Integrable g ν := hg.1.continuous.integrable_of_hasCompactSupport hg.2
  have := (hc _ _ hf hg').1
  convert this using 2 with x
  rw [he]

theorem integrable_of_mem : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)),
    IsCovolOne (ratMx D m n) μ 𝓕 → ∀ Φ ∈ schwartzA θ m n, Integrable Φ μ := by
  intro D θ hθ m n μ 𝓕 hμ Φ hΦ
  haveI := hμ.1
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact integrable_pure hθ μ f g hg
  | zero => exact integrable_zero _ _ _
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact h.smul c

end GlobalTheory.SchwartzAInt
end
end
