module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointsGenerate
noncomputable section

namespace GlobalTheory.RatGen

open scoped TensorProduct Matrix ComplexOrder

theorem closure_preimage_eq_top {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [PreconnectedSpace G] (φ : Γ →* G) (hφ : DenseRange φ) (N : Set G) (hN : IsOpen N) (h1 : (1 : G) ∈ N) :
    Subgroup.closure (φ ⁻¹' N) = ⊤ := by
  set H := Subgroup.closure (φ ⁻¹' N) with hH
  have hsub : N ⊆ (H.map φ).topologicalClosure := by
    refine (hφ.open_subset_closure_inter hN).trans (closure_mono ?_)
    rintro _ ⟨hx, γ, rfl⟩
    exact ⟨γ, Subgroup.subset_closure hx, rfl⟩
  have ho : IsOpen ((H.map φ).topologicalClosure : Set G) :=
    Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hN.mem_nhds h1) hsub)
  have hall : ((H.map φ).topologicalClosure : Set G) = Set.univ :=
    IsClopen.eq_univ ⟨Subgroup.isClosed_topologicalClosure _, ho⟩ ⟨1, one_mem _⟩
  refine (Subgroup.eq_top_iff' _).2 fun γ => ?_
  have h2 : φ γ ∈ closure (H.map φ : Set G) := by
    have : φ γ ∈ ((H.map φ).topologicalClosure : Set G) := hall ▸ Set.mem_univ _
    exact this
  obtain ⟨_, hx, h, hh, rfl⟩ := mem_closure_iff.1 h2 {x | x⁻¹ * φ γ ∈ N}
    (hN.preimage (continuous_inv.mul continuous_const)) (by simpa using h1)
  have h3 : h⁻¹ * γ ∈ H := Subgroup.subset_closure (by simpa using hx)
  simpa using H.mul_mem hh h3


open Formalism.UG GlobalTheory.UnRep.WeakApprox in
theorem preconnected_unitary {K R A : Type} [Field K] [CharZero K] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsArtinianRing R] (ι : K →+* R) (c : K →+* K) (σ : R →+* R)
    (hσι : ∀ x, σ (ι x) = ι (c x)) (hc : ∀ x, c (c x) = x) (hne : ∃ z, c z ≠ z) (hσ : ∀ x, σ (σ x) = x)
    (h2 : ∀ x : R, IsUnit x → ContinuousAt Ring.inverse x)
    [TopologicalSpace A] [PreconnectedSpace A] (p : A → R) (hp : Continuous p) (hpσ : ∀ a, σ (p a) = p a)
    (a₀ a₁ : A) (h₀ : p a₀ = 0) (h₁ : p a₁ = 1) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (hJ : cT σ J = J) (hdet : IsUnit J.det)
    (hdef : ∀ S : Matrix (Fin n) (Fin n) R, Sᵀ * Jᵀ + Jᵀ * S.map σ = 0 → IsUnit (1 + S).det) :
    PreconnectedSpace (UJ σ J) := by
  have he : Topology.IsEmbedding (Units.val : GL (Fin n) R → Matrix (Fin n) (Fin n) R) :=
    Units.isEmbedding_val_mk' (f := Inv.inv)
      (fun M hM => (continuousAt_matrix_inv M (h2 _ ((Matrix.isUnit_iff_isUnit_det _).1 hM))).continuousWithinAt)
      (fun u => (Matrix.coe_units_inv u).symm)
  have he' : Topology.IsInducing (fun h : UJ σ J => h.1.1) :=
    he.isInducing.comp Topology.IsInducing.subtypeVal
  have h2' : IsUnit (2 : R) := by
    have := (two_ne_zero (α := K)).isUnit.map ι
    rwa [map_ofNat] at this
  have hdet' : IsUnit (Jᵀ).det := by rwa [Matrix.det_transpose]
  obtain ⟨c1, c2, c3, -⟩ := GlobalTheory.CayleyInv.cayley_transform R σ n Jᵀ hσ
    (by rw [Matrix.transpose_map]; exact congrArg Matrix.transpose hJ) hdet' h2'
  have mk : ∀ M : Matrix (Fin n) (Fin n) R, Mᵀ * Jᵀ * M.map σ = Jᵀ → ∃ u : UJ σ J, u.1.1 = M := by
    intro M hM
    have hu : IsUnit M.det := by
      have := hdet'
      rw [← hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose M] at this
      exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left this)
    obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hu
    exact ⟨⟨u, (GlobalTheory.Mass.OnePlace.unitary_transpose _ _ _).2 hM⟩, rfl⟩
  have step : ∀ k : UJ σ J, IsUnit (1 + k.1.1).det → k ∈ Subgroup.connectedComponentOfOne (UJ σ J) := by
    intro k hk
    obtain ⟨hS, -⟩ := c1 k.1.1 ((GlobalTheory.Mass.OnePlace.unitary_transpose _ _ _).1 k.2) hk
    have hkS := c2 k.1.1 hk
    set S : Matrix (Fin n) (Fin n) R := (1 - k.1.1) * (1 + k.1.1)⁻¹
    have hsk : ∀ a, (p a • S)ᵀ * Jᵀ + Jᵀ * (p a • S).map σ = 0 := fun a => by
      rw [map_smul'', hpσ, Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm, ← smul_add, hS, smul_zero]
    choose f hf using fun a => mk _ (c3 _ (hsk a) (hdef _ (hsk a)))
    have hT : Continuous fun a => p a • S := hp.smul continuous_const
    have hfc : Continuous f := by
      rw [he'.continuous_iff]
      have : ((fun h : UJ σ J => h.1.1) ∘ f) = fun a => (1 - p a • S) * (1 + p a • S)⁻¹ := funext hf
      rw [this]
      refine (continuous_const.sub hT).mul (continuous_iff_continuousAt.2 fun a => ?_)
      exact ContinuousAt.comp (f := fun a => 1 + p a • S)
        (continuousAt_matrix_inv _ (h2 _ (hdef _ (hsk a)))) (continuous_const.add hT).continuousAt
    have e0 : f a₀ = 1 := Subtype.ext (Units.ext (by rw [hf, h₀]; simp))
    have e1 : f a₁ = k := Subtype.ext (Units.ext (by rw [hf, h₁, one_smul, hkS]))
    exact (isPreconnected_range hfc).subset_connectedComponent ⟨a₀, e0⟩ ⟨a₁, e1⟩
  have all : ∀ g : UJ σ J, g ∈ Subgroup.connectedComponentOfOne (UJ σ J) := by
    intro g
    obtain ⟨lam, ⟨hlam, hl1⟩, hu⟩ := GlobalTheory.NormSum.RepAt.exists_unit_det ι g.1.1 _
      (GlobalTheory.NormSum.RepAt.normOne_infinite c hc hne)
    have hl : ι lam * σ (ι lam) = 1 := by rw [hσι, ← map_mul, hlam, map_one]
    obtain ⟨s, hs⟩ := mk (ι lam • 1) (by
      rw [map_smul'', Matrix.transpose_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, hl,
        one_smul, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one, one_mul, mul_one])
    have m1 := step s (by
      have : (1 : Matrix (Fin n) (Fin n) R) + ι lam • 1 = ι (1 + lam) • 1 := by
        rw [map_add (f := _), map_one, add_smul, one_smul]
      rw [hs, this, Matrix.det_smul, Matrix.det_one, mul_one]
      exact (hl1.isUnit.map ι).pow _)
    have m2 := step (s * g) (by
      have : (s * g).1.1 = s.1.1 * g.1.1 := rfl
      rw [this, hs, smul_mul_assoc, one_mul]
      exact hu)
    simpa using mul_mem (inv_mem m1) m2
  refine ⟨?_⟩
  have : connectedComponent (1 : UJ σ J) = Set.univ := Set.eq_univ_of_forall all
  rw [← this]
  exact isPreconnected_connectedComponent

theorem det_one_add_ne_zero {n : ℕ} {J S : Matrix (Fin n) (Fin n) ℂ} (hJ : J.PosDef) (hS : Sᴴ * J + J * S = 0) :
    (1 + S).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have h1 : S *ᵥ v = -v := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec] at h0
    exact eq_neg_of_add_eq_zero_right h0
  have h2 : star v ⬝ᵥ ((Sᴴ * J + J * S) *ᵥ v) = 0 := by rw [hS]; simp
  rw [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec, h1, Matrix.mulVec_neg, star_neg, neg_dotProduct, dotProduct_neg] at h2
  have h3 := (hJ.dotProduct_mulVec_pos hv).ne'
  exact h3 (by linear_combination (-1 / 2 : ℂ) * h2)

theorem map_det_one_add_ne_zero {R : Type} [CommRing R] (σ : R →+* R) (θ : R →+* ℂ)
    (h : ∀ z, θ (σ z) = starRingEnd ℂ (θ z)) {n : ℕ} {J S : Matrix (Fin n) (Fin n) R} (hJ : (J.map θ).PosDef)
    (hS : Sᵀ * Jᵀ + Jᵀ * S.map σ = 0) : θ (1 + S).det ≠ 0 := by
  have e2 : ((S.map σ)ᵀ).map θ = (S.map θ)ᴴ := Matrix.ext fun i j => h _
  have e4 := congrArg Matrix.transpose hS
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, Matrix.transpose_zero] at e4
  have e3 : (J * S + (S.map σ)ᵀ * J).map θ = (0 : Matrix _ _ _).map θ := by rw [e4]
  rw [Matrix.map_add _ (map_add θ), Matrix.map_mul, Matrix.map_mul, e2, Matrix.map_zero _ (map_zero θ),
    add_comm] at e3
  have := det_one_add_ne_zero hJ e3
  rwa [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_add _ (map_add θ),
    Matrix.map_one _ (map_zero θ) (map_one θ)]

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem preconnected_infAdele (F : Type) [Field F] [NumberField F] : PreconnectedSpace (Ainf F) := by
  haveI : ∀ w : InfinitePlace F, PreconnectedSpace w.Completion := fun w => by
    rcases w.isReal_or_isComplex with hw | hw
    · let e := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm
      exact (e.surjective.connectedSpace e.continuous).toPreconnectedSpace
    · let e := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm
      exact (e.surjective.connectedSpace e.continuous).toPreconnectedSpace
  exact inferInstanceAs (PreconnectedSpace (∀ w : InfinitePlace F, w.Completion))

theorem exists_conj_ne (D : D7) : ∃ z, D.sp.cm.sig z ≠ z := by
  by_contra h
  push Not at h
  have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun z => (D.sp.cm.fixed z).1 (h z)
  have h1 : Module.finrank D.host.F D.host.E = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap D.host.F D.host.E).injective, hs⟩
  have h2 := D.sp.cm.deg2
  omega

theorem preconnected_inf {D : D7} (V : HSp D) (hp : V.IsPosDef) (hs : V.SigOK) :
    PreconnectedSpace (HA (Ainf D.host.F) D.sp.cm.sig V.gram) := by
  classical
  haveI : IsArtinianRing (Ainf D.host.F) :=
    inferInstanceAs (IsArtinianRing (∀ v : InfinitePlace D.host.F, v.Completion))
  haveI : IsArtinianRing (Ainf D.host.F ⊗[D.host.F] D.host.E) := IsArtinianRing.of_finite (Ainf D.host.F) _
  haveI : IsTopologicalRing (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Ainf D.host.F) _
  haveI := preconnected_infAdele D.host.F
  have a1 : IsOpen {x : (∀ v : InfinitePlace D.host.F, v.Completion) | IsUnit x} := Units.isOpen
  have a2 : ∀ x : (∀ v : InfinitePlace D.host.F, v.Completion), IsUnit x → ContinuousAt Ring.inverse x := by
    rintro _ ⟨x, rfl⟩
    exact NormedRing.inverse_continuousAt x
  have b1 : IsOpen {x : Ainf D.host.F | IsUnit x} := a1
  have b2 : ∀ x : Ainf D.host.F, IsUnit x → ContinuousAt Ring.inverse x := a2
  obtain ⟨-, h2⟩ := GlobalTheory.RealApprox.units_of_free (A := Ainf D.host.F) (R := Ainf D.host.F ⊗[D.host.F] D.host.E)
    (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)) b1 b2
  obtain ⟨⟨θ, hθ⟩, H⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  obtain ⟨-, hcj, hb⟩ := H θ hθ
  have hunit : ∀ z, (∀ τ, θ τ z ≠ 0) → IsUnit z := fun z hz => by
    obtain ⟨w, hw⟩ := hb.2 fun τ => (θ τ.1 z)⁻¹
    refine IsUnit.of_mul_eq_one w (hb.1 (funext fun τ => ?_))
    have := congrFun hw τ
    simp only at this ⊢
    rw [map_mul, this, map_one, mul_inv_cancel₀ (hz _)]
  have hσι : ∀ x, sigR (Ainf D.host.F) D.sp.cm.sig (inclR (F := D.host.F) (Ainf D.host.F) x) =
      inclR (F := D.host.F) (Ainf D.host.F) ((D.sp.cm.sig : D.host.E →+* D.host.E) x) := fun x => by
    simp [sigR, inclR]
  have hsm : Continuous fun a : Ainf D.host.F => a • (1 : Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    Continuous.smul (f := fun a : Ainf D.host.F => a)
      (g := fun _ : Ainf D.host.F => (1 : Ainf D.host.F ⊗[D.host.F] D.host.E)) continuous_id continuous_const
  refine preconnected_unitary (A := Ainf D.host.F) (inclR (F := D.host.F) (Ainf D.host.F))
    (D.sp.cm.sig : D.host.E →+* D.host.E) (sigR (Ainf D.host.F) D.sp.cm.sig) hσι (fun x => star_star x)
    (exists_conj_ne D) (fun x => hb.1 (funext fun τ => ?_)) h2 (fun a => a • 1) hsm
    (fun a => ?_) 0 1 (zero_smul _ _) (one_smul _ _) (JR (Ainf D.host.F) V.gram) ?_ ?_ fun S hS => hunit _ fun τ => ?_
  · simp only [hcj, Complex.conj_conj]
  · simp [sigR, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
  · ext i j
    exact (hσι _).trans (congrArg _ (congrFun (congrFun (GlobalTheory.AutFunCounterexample.gram_herm V) i) j))
  · have := (GlobalTheory.AutFunCounterexample.gram_det_ne V).isUnit.map (inclR (F := D.host.F) (Ainf D.host.F))
    rwa [RingHom.map_det] at this
  · have hJ : (V.gram.map τ).PosDef := GlobalTheory.DefiniteQuotient.posDef_of_signature (p := V.rank) (by
      have := hs τ
      rwa [hp τ] at this)
    have e1 : (JR (F := D.host.F) (Ainf D.host.F) V.gram).map (θ τ) = V.gram.map τ :=
      Matrix.ext fun _ _ => (hθ τ).1 _
    exact map_det_one_add_ne_zero _ (θ τ) (hcj τ) (e1 ▸ hJ) hS

theorem rational_points_generate : ∀ (D : D7) (V : HSp D) (c : CoefA V), V.IsPosDef → V.SigOK → c.Is → Subgroup.closure {γ : GQ V | LinearMap.trace ℂ c.W (c.ρ γ) ≠ 0} = ⊤ ∧ (∀ U : Submodule ℂ c.W, (∀ γ : GQ V, U.map (c.ρ γ) ≤ U) → U = ⊥ ∨ U = ⊤) ∧ ∀ u ∈ GinfC V, ∀ N ∈ nhds u, ∃ γ ∈ GQ V, ∃ k ∈ GfC V, γ * k ∈ N ∧ γ * k ∈ GinfC V := by
  intro D V c hp hs ⟨hfin, _, hcont, hnt, hirr⟩
  have h3 : ∀ u ∈ GinfC V, ∀ N ∈ nhds u, ∃ γ ∈ GQ V, ∃ k ∈ GfC V, γ * k ∈ N ∧ γ * k ∈ GinfC V := by
    intro u hu N hN
    obtain ⟨U, hUN, hU, huU⟩ := mem_nhds_iff.1 hN
    obtain ⟨γ, hγ, k, hk, h1, h2⟩ := GlobalTheory.RealApprox.weak_approx_real V u hu U hU huU
    exact ⟨γ, hγ, k, hk, hUN h1, h2⟩
  refine ⟨?_, fun U hU => hirr U fun h => ?_, h3⟩
  · haveI := preconnected_inf V hp hs
    haveI : IsTopologicalRing (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
      IsModuleTopology.isTopologicalRing (Ainf D.host.F) _
    haveI : IsTopologicalGroup (HA (Ainf D.host.F) D.sp.cm.sig V.gram) :=
      inferInstanceAs (IsTopologicalGroup (HR (Ainf D.host.F) D.sp.cm.sig V.gram))
    obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
    have hGi : ∀ h : GA D V, (e h).2 = 1 → h ∈ GinfC V := fun h H =>
      MonoidHom.mem_ker.2 (Units.ext ((he h).1.symm.trans (by rw [H]; rfl)))
    have hGf : ∀ h : GA D V, h ∈ GfC V ↔ (e h).1 = 1 := fun h =>
      ⟨fun H => Subtype.ext (Units.ext ((he h).2.trans (congrArg Units.val (MonoidHom.mem_ker.1 H)))),
        fun H => MonoidHom.mem_ker.2 (Units.ext ((he h).2.symm.trans (by rw [H]; rfl)))⟩
    let φ : GQ V →* HA (Ainf D.host.F) D.sp.cm.sig V.gram :=
      (MonoidHom.fst _ _).comp (e.toMulEquiv.toMonoidHom.comp (GQ V).subtype)
    have hφ : ∀ γ : GQ V, φ γ = (e γ.1).1 := fun _ => rfl
    have hd : DenseRange φ := by
      refine dense_iff_inter_open.2 ?_
      rintro O hO ⟨x, hx⟩
      obtain ⟨γ, hγ, k, hk, h1, -⟩ := h3 (e.symm (x, 1)) (hGi _ (by rw [e.apply_symm_apply])) {g | (e g).1 ∈ O}
        ((hO.preimage (continuous_fst.comp e.continuous)).mem_nhds (by
          change (e (e.symm (x, 1))).1 ∈ O
          rwa [e.apply_symm_apply]))
      refine ⟨_, ?_, ⟨γ, hγ⟩, rfl⟩
      rwa [Set.mem_setOf_eq, map_mul, Prod.fst_mul, (hGf k).1 hk, mul_one] at h1
    have htr : Continuous fun h : GA D V => LinearMap.trace ℂ c.W (c.ρ h) := by
      let b := Module.finBasis ℂ c.W
      simp only [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
      exact continuous_finsetSum _ fun i _ => (b.coord i).continuous_of_finiteDimensional.comp (hcont (b i))
    have hc : Continuous fun x : HA (Ainf D.host.F) D.sp.cm.sig V.gram => e.symm (x, 1) :=
      e.symm.continuous.comp (continuous_id.prodMk continuous_const)
    have key := closure_preimage_eq_top φ hd {x | LinearMap.trace ℂ c.W (c.ρ (e.symm (x, 1))) ≠ 0}
      (isOpen_ne_fun (htr.comp hc) continuous_const) (by
        change LinearMap.trace ℂ c.W (c.ρ (e.symm 1)) ≠ 0
        rw [map_one, map_one, LinearMap.trace_one]
        exact_mod_cast (Module.finrank_pos (R := ℂ) (M := c.W)).ne')
    rw [← key]
    congr 1
    ext γ
    have e1 : c.ρ γ = c.ρ (e.symm (φ γ, 1)) := by
      have hk : (γ : GA D V)⁻¹ * e.symm (φ γ, 1) ∈ GfC V := (hGf _).2 (by
        rw [map_mul, map_inv, e.apply_symm_apply, Prod.fst_mul, Prod.fst_inv, hφ, inv_mul_cancel])
      rw [← mul_inv_cancel_left (γ : GA D V) (e.symm (φ γ, 1)), map_mul, hfin _ hk, mul_one]
    rw [Set.mem_setOf_eq, e1]
    rfl
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h
    rw [map_mul, hfin k hk, mul_one]
    by_contra hn
    obtain ⟨γ, hγ, k', hk', h1, -⟩ := h3 a ha {g | c.ρ g x ∉ U}
      ((U.closed_of_finiteDimensional.isOpen_compl.preimage (hcont x)).mem_nhds hn)
    rw [Set.mem_setOf_eq, map_mul, hfin k' hk', mul_one] at h1
    exact h1 (hU ⟨γ, hγ⟩ ⟨x, hx, rfl⟩)

end GlobalTheory.RatGen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarOfIntertwinesUpToScalar
namespace GlobalTheory.AdTh

theorem scalar_of_intertwines_up_to_scalar (Γ M : Type) [Group Γ] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] [Nontrivial M] (ρ : Γ →* Module.End ℂ M) (S : Set Γ)
    (hS : Subgroup.closure S = ⊤) (htr : ∀ γ ∈ S, LinearMap.trace ℂ M (ρ γ) ≠ 0)
    (hirr : ∀ U : Submodule ℂ M, (∀ γ, U.map (ρ γ) ≤ U) → U = ⊥ ∨ U = ⊤)
    (T : M →ₗ[ℂ] M) (χ : Γ → ℂ) (hT : Function.Injective T)
    (h : ∀ γ x, T (ρ γ x) = χ γ • ρ γ (T x)) : ∃ a : ℂ, ∀ x, T x = a • x := by
  have hu : IsUnit (T : Module.End ℂ M) :=
    (Module.End.isUnit_iff _).2 ⟨hT, LinearMap.injective_iff_surjective.1 hT⟩
  obtain ⟨u, hu⟩ := hu
  have h1 : ∀ γ, (u : Module.End ℂ M) * ρ γ = χ γ • (ρ γ * u) := by
    intro γ
    ext x
    simp [hu, h]
  have hχ : ∀ γ ∈ S, χ γ = 1 := by
    intro γ hγ
    have h2 : (u : Module.End ℂ M) * ρ γ * (↑u⁻¹ : Module.End ℂ M) = χ γ • ρ γ := by
      rw [h1, smul_mul_assoc, mul_assoc, Units.mul_inv, mul_one]
    have h3 := congrArg (LinearMap.trace ℂ M) h2
    rw [LinearMap.trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul, map_smul, smul_eq_mul] at h3
    have h4 := htr γ hγ
    have : (χ γ - 1) * LinearMap.trace ℂ M (ρ γ) = 0 := by linear_combination -h3
    rcases mul_eq_zero.1 this with h5 | h5
    · exact sub_eq_zero.1 h5
    · exact absurd h5 h4
  have hc : ∀ γ, Commute (u : Module.End ℂ M) (ρ γ) := by
    intro γ
    have hγ : γ ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top γ
    induction hγ using Subgroup.closure_induction with
    | mem x hx =>
      have := h1 x
      rw [hχ x hx, one_smul] at this
      exact this
    | one => rw [map_one]; exact Commute.one_right _
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_right hy
    | inv x _ hx =>
      have e1 : ρ x * ρ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      have e2 : ρ x⁻¹ * ρ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      exact Commute.units_inv_right (u := ⟨ρ x, ρ x⁻¹, e1, e2⟩) hx
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (T : Module.End ℂ M)
  refine ⟨a, fun x => ?_⟩
  rcases hirr (Module.End.eigenspace T a) (by
      rintro γ _ ⟨y, hy, rfl⟩
      have hy' : T y = a • y := Module.End.mem_eigenspace_iff.1 hy
      rw [Module.End.mem_eigenspace_iff]
      have := congrArg (fun f : Module.End ℂ M => f y) (hc γ).eq
      simp only [hu, Module.End.mul_apply] at this
      rw [this, hy', map_smul]) with h0 | h0
  · exact absurd h0 (Module.End.hasEigenvalue_iff.1 ha)
  · exact Module.End.mem_eigenspace_iff.1 (h0 ▸ Submodule.mem_top)

end GlobalTheory.AdTh
end

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.PhaseMap

theorem proportional {Γ M N : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] [Nontrivial M]
    [AddCommGroup N] [Module ℂ N] (ρ : Γ →* Module.End ℂ M) (S : Set Γ) (hS : Subgroup.closure S = ⊤)
    (htr : ∀ γ ∈ S, LinearMap.trace ℂ M (ρ γ) ≠ 0)
    (hirr : ∀ U : Submodule ℂ M, (∀ γ, U.map (ρ γ) ≤ U) → U = ⊥ ∨ U = ⊤) (A B : M →ₗ[ℂ] N)
    (heq : ∀ γ, ∃ (s : N →ₗ[ℂ] N) (c : ℂ), (∀ w, A (ρ γ w) = s (A w)) ∧ ∀ w, B (ρ γ w) = c • s (B w))
    (w z : M) (hwz : A w = B z) (hne : B z ≠ 0) : ∃ a : ℂ, (∀ x, A x = a • B x) ∧ a • w = z := by
  choose s c hA hB using heq
  have hAi : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot]
    refine (hirr _ fun γ => ?_).resolve_right fun h => hne ?_
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : A x = 0 := hx
      show A _ = 0
      rw [hA, hx', map_zero]
    · rw [← hwz]
      exact (h ▸ Submodule.mem_top : w ∈ LinearMap.ker A)
  have hBi : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot]
    refine (hirr _ fun γ => ?_).resolve_right fun h => hne ?_
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : B x = 0 := hx
      show B _ = 0
      rw [hB, hx', map_zero, smul_zero]
    · exact (h ▸ Submodule.mem_top : z ∈ LinearMap.ker B)
  have hc : ∀ γ, c γ ≠ 0 := fun γ h => hne (by
    have h1 := hB γ (ρ γ⁻¹ z)
    rw [h, zero_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h1
    exact h1)
  have hs : ∀ γ x, s γ (B x) = B ((c γ)⁻¹ • ρ γ x) := fun γ x => by
    rw [map_smul, hB, smul_smul, inv_mul_cancel₀ (hc γ), one_smul]
  have hr : ∀ x, A x ∈ LinearMap.range B := by
    have h : (LinearMap.range B).comap A = ⊤ := by
      refine (hirr _ fun γ => ?_).resolve_left fun h => hne ?_
      · rintro _ ⟨x, ⟨y, hy⟩, rfl⟩
        exact ⟨_, by rw [hA, ← hy, hs]⟩
      · have hw : w ∈ (LinearMap.range B).comap A := ⟨z, hwz.symm⟩
        rw [h, Submodule.mem_bot] at hw
        rw [← hwz, hw, map_zero]
    exact fun x => (h ▸ Submodule.mem_top : x ∈ (LinearMap.range B).comap A)
  let T : M →ₗ[ℂ] M := (LinearEquiv.ofInjective B hBi).symm.toLinearMap ∘ₗ A.codRestrict _ hr
  have hT : ∀ x, B (T x) = A x := fun x =>
    congrArg Subtype.val ((LinearEquiv.ofInjective B hBi).apply_symm_apply ⟨A x, hr x⟩)
  obtain ⟨a, ha⟩ := GlobalTheory.AdTh.scalar_of_intertwines_up_to_scalar Γ M ρ S hS htr hirr T (fun γ => (c γ)⁻¹)
    (fun x y h => hAi (by rw [← hT, ← hT, h])) fun γ x => hBi (by rw [hT, hA, ← hT, hs])
  exact ⟨a, fun x => by rw [← hT, ha, map_smul], hBi (by rw [← ha, hT, hwz])⟩

theorem exists_ext {K X M N : Type} [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] {σ : K →+* ℂ} (c : X →ₛₗ[σ] M)
    (hli : ∀ (m : ℕ) (b : Fin m → X), LinearIndependent K b → LinearIndependent ℂ (fun j => c (b j)))
    (f : X →ₛₗ[σ] N) : ∃ B : M →ₗ[ℂ] N, ∀ v, B (c v) = f v := by
  let b := Module.finBasis K X
  have h := hli _ b b.linearIndependent
  obtain ⟨B, hB⟩ := LinearMap.exists_extend ((Module.Basis.span h).constr ℂ fun j => f (b j))
  have hj : ∀ j, B (c (b j)) = f (b j) := fun j => by
    have h1 := LinearMap.congr_fun hB (Module.Basis.span h j)
    rw [Module.Basis.constr_basis, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply] at h1
    exact h1
  refine ⟨B, fun v => ?_⟩
  rw [← b.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, hj, RingHom.id_apply]

theorem trace_parity {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) :
    B.det ≠ 0 ∧ ∃ x : ℤ, s.trace / 2 + (k : ℂ) / 2 = x := by
  obtain ⟨ε, hε, h1, h2⟩ := h
  have hd : B.det ≠ 0 := fun h0 => by
    have h3 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at h3
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h3.symm
    rcases hε a with h | h <;> simp [h.1] at ha
  refine ⟨hd, ∑ a, if ε a = 1 then 1 else 0, ?_⟩
  have h4 : s = B * Matrix.diagonal (fun a => (ε a : ℂ)) * B⁻¹ := by
    rw [← h2, Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.2 hd)]
  rw [h4, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hd), Matrix.one_mul, Matrix.trace_diagonal]
  have h5 : (k : ℂ) = ∑ _a : Fin k, (1 : ℂ) := by simp
  rw [h5, ← add_div, ← Finset.sum_add_distrib, Finset.sum_div]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rcases hε a with h | h
  · simp [h.1]
  · rw [if_neg (by rw [h.1]; norm_num)]
    simp [h.1]

section Letters

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {m n : ℕ} {l : Geo.Tor.Level H} (c : Coeff l)

def IsTyp (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) : Prop :=
  (∀ τ, InPsi H τ ↔ ∃ t, τ = tauE D t) ∧ ∀ τ, ¬ InPsi H τ ↔ ∃ t, τ = conjEmb (tauE D t)

def IsLt (lt : LtN Dw n → FVar D m n) : Prop :=
  ∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨
    (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = Dw.p + ℓ.2.1))

theorem conjEmb_inj {a b : D.host.E →+* ℂ} (h : conjEmb a = conjEmb b) : a = b := by
  ext x
  exact star_injective (RingHom.congr_fun h x)

theorem IsTyp.ne (h : IsTyp D H) (s t : D.what₂.Tau) : tauE D s ≠ conjEmb (tauE D t) :=
  fun e => (h.2 _).2 ⟨t, e⟩ ((h.1 _).2 ⟨s, rfl⟩)

theorem IsTyp.mult_pos (h : IsTyp D H) (Dw : Datum H) (t : D.what₂.Tau) : Dw.mult (tauE D t) = Dw.p :=
  if_pos ((h.1 _).2 ⟨t, rfl⟩)

theorem IsTyp.mult_neg (h : IsTyp D H) (Dw : Datum H) (t : D.what₂.Tau) : Dw.mult (conjEmb (tauE D t)) = Dw.q :=
  if_neg ((h.2 _).2 ⟨t, rfl⟩)

variable {lt : LtN Dw n → FVar D m n}

theorem IsLt.pos (hl : IsLt lt) (h : IsTyp D H) {ℓ : LtN Dw n} {t : D.what₂.Tau} (e : ℓ.1 = tauE D t) :
    (lt ℓ).1 = t ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1 ∧ (ℓ.2.1 : ℕ) < Dw.p := by
  have h3 : (ℓ.2.1 : ℕ) < Dw.p := lt_of_lt_of_eq ℓ.2.1.2 (by rw [e, h.mult_pos])
  rcases (hl ℓ).2 with ⟨h1, h2⟩ | ⟨h1, -⟩
  · exact ⟨GlobalTheory.SmoothForms.RealPts.tauE_injective D (h1.symm.trans e), h2, h3⟩
  · exact absurd (e.symm.trans h1) (h.ne _ _)

theorem IsLt.neg (hl : IsLt lt) (h : IsTyp D H) {ℓ : LtN Dw n} {t : D.what₂.Tau} (e : ℓ.1 = conjEmb (tauE D t)) :
    (lt ℓ).1 = t ∧ ((lt ℓ).2.1 : ℕ) = Dw.p + ℓ.2.1 := by
  rcases (hl ℓ).2 with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact absurd (h1.symm.trans e) (h.ne _ _)
  · exact ⟨GlobalTheory.SmoothForms.RealPts.tauE_injective D (conjEmb_inj (h1.symm.trans e)), h2⟩

theorem IsLt.injective (hl : IsLt lt) (h : IsTyp D H) : Function.Injective lt := by
  intro ℓ ℓ' e
  have h3 : ℓ.2.2 = ℓ'.2.2 := by rw [← (hl ℓ).1, e, (hl ℓ').1]
  have key : ℓ.1 = ℓ'.1 ∧ (ℓ.2.1 : ℕ) = ℓ'.2.1 := by
    rcases (hl ℓ).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases (hl ℓ').2 with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · exact ⟨by rw [h1, g1, e], by rw [← h2, ← g2, e]⟩
    · have := (hl.pos h h1).2.2
      rw [e] at h2
      omega
    · have := (hl.pos h g1).2.2
      rw [e] at h2
      omega
    · refine ⟨by rw [h1, g1, e], ?_⟩
      rw [e] at h2
      omega
  obtain ⟨σ, i, b⟩ := ℓ
  obtain ⟨σ', i', b'⟩ := ℓ'
  obtain ⟨rfl, h4⟩ := key
  obtain rfl : b = b' := h3
  obtain rfl : i = i' := Fin.ext h4
  rfl

theorem IsLt.col (hl : IsLt lt) (h : IsTyp D H) (ℓ : LtN Dw n) (j : Fin n) :
    lt ⟨ℓ.1, ℓ.2.1, j⟩ = ((lt ℓ).1, (lt ℓ).2.1, j) := by
  refine Prod.ext ?_ (Prod.ext (Fin.ext ?_) (hl _).1)
  · rcases (hl ℓ).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (hl.pos h (ℓ := ⟨ℓ.1, ℓ.2.1, j⟩) h1).1
    · exact (hl.neg h (ℓ := ⟨ℓ.1, ℓ.2.1, j⟩) h1).1
  · rcases (hl ℓ).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (hl.pos h (ℓ := ⟨ℓ.1, ℓ.2.1, j⟩) h1).2.1.trans h2.symm
    · exact (hl.neg h (ℓ := ⟨ℓ.1, ℓ.2.1, j⟩) h1).2.trans h2.symm

theorem X_eq_varF (k : FVar D m n) {t : D.what₂.Tau} {i b : ℕ} (h1 : k.1 = t) (h2 : (k.2.1 : ℕ) = i) (h3 : (k.2.2 : ℕ) = b) :
    (MvPolynomial.X k : MvPolynomial (FVar D m n) ℂ) = varF t i b := by
  subst h1 h2 h3
  rw [varF, dif_pos ⟨k.2.1.2, k.2.2.2⟩]

def toF (lt : LtN Dw n → FVar D m n) : MvPolynomial (LtN Dw n) c.F →+* MvPolynomial (FVar D m n) ℂ :=
  (MvPolynomial.rename lt).toRingHom.comp (MvPolynomial.map (inC c))

theorem toF_apply (P : MvPolynomial (LtN Dw n) c.F) :
    toF c lt P = MvPolynomial.rename lt (MvPolynomial.map (inC c) P) := rfl

theorem toF_X (ℓ : LtN Dw n) : toF c lt (MvPolynomial.X ℓ) = MvPolynomial.X (lt ℓ) := by
  simp [toF_apply]

theorem toF_C (a : c.F) : toF c lt (MvPolynomial.C a) = MvPolynomial.C (a : ℂ) := by
  simp [toF_apply]

theorem toF_injective (hl : IsLt lt) (h : IsTyp D H) : Function.Injective (toF c lt) :=
  (MvPolynomial.rename_injective _ (hl.injective h)).comp (MvPolynomial.map_injective _ (inC c).injective)

theorem toF_minorP (σ : D.host.E →+* ℂ) (i : ℕ) (hi : i < Dw.mult σ) (col : Fin (i + 1) → Fin n) :
    toF c lt (minorPolynomial c σ i hi col) =
      (Matrix.of fun b s : Fin (i + 1) =>
        (MvPolynomial.X (lt ⟨σ, ⟨s.val, by omega⟩, col b⟩) : MvPolynomial (FVar D m n) ℂ)).det := by
  rw [minorPolynomial, RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext1 b s
  exact toF_X c _

theorem toF_pG (hl : IsLt lt) (h : IsTyp D H) (hn : Dw.p + Dw.q ≤ n) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (hp : ∀ t, p t = Dw.p) (hq : ∀ t, q t = Dw.q)
    (hap : ∀ t k, k < Dw.p → a (tauE D t, k) = ap t k) (ham : ∀ t k, k < Dw.q → a (conjEmb (tauE D t), k) = am t k) :
    toF c lt (pG (Dw := Dw) c a n) = Formalism.IndefR.Datum.delta p q ap am := by
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => conjEmb (tauE D t)) := by
    refine ⟨?_, fun σ => ?_⟩
    · rintro (s | s) (t | t) e
      · exact congrArg _ (GlobalTheory.SmoothForms.RealPts.tauE_injective D e)
      · exact absurd e (h.ne _ _)
      · exact absurd (Eq.symm e) (h.ne _ _)
      · exact congrArg _ (GlobalTheory.SmoothForms.RealPts.tauE_injective D (conjEmb_inj e))
    · by_cases hσ : InPsi H σ
      · obtain ⟨t, ht⟩ := (h.1 σ).1 hσ
        exact ⟨Sum.inl t, ht.symm⟩
      · obtain ⟨t, ht⟩ := (h.2 σ).1 hσ
        exact ⟨Sum.inr t, ht.symm⟩
  have hprod : ∀ f : (D.host.E →+* ℂ) → MvPolynomial (FVar D m n) ℂ,
      ∏ σ, f σ = ∏ t, f (tauE D t) * f (conjEmb (tauE D t)) := fun f => by
    rw [← hb.prod_comp, Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
    rfl
  rw [pG, map_prod, hprod, Formalism.IndefR.Datum.delta]
  refine Finset.prod_congr rfl fun t _ => ?_
  have m1 := h.mult_pos Dw t
  have m2 := h.mult_neg Dw t
  rw [deltaAt, hp, hq]
  congr 1
  · rw [map_prod]
    conv_rhs => rw [← m1, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (i : ℕ) < Dw.p := lt_of_lt_of_eq i.2 m1
    rw [map_pow, dif_pos (by omega), if_pos ((h.1 _).2 ⟨t, rfl⟩), toF_minorP]
    congr 1
    · rw [minorPlus]
      congr 1
      ext1 b s
      have h1 := hl.pos h (ℓ := ⟨tauE D t, ⟨s.val, by have := s.2; omega⟩, Fin.castLE (by omega) b⟩) rfl
      exact X_eq_varF _ h1.1 h1.2.1 (congrArg Fin.val (hl _).1)
    · show aStep Dw a (tauE D t) i = _
      rw [aStep, hap t i hi]
      congr 1
      split_ifs with h1
      · exact hap t _ (by omega)
      · rfl
  · rw [map_prod]
    conv_rhs => rw [← m2, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (i : ℕ) < Dw.q := lt_of_lt_of_eq i.2 m2
    rw [map_pow, dif_pos (by omega), if_neg ((h.2 _).2 ⟨t, rfl⟩), toF_minorP]
    congr 1
    · rw [minorMinus]
      congr 1
      ext1 b s
      have h1 := hl.neg h (ℓ := ⟨conjEmb (tauE D t), ⟨s.val, by have := s.2; omega⟩,
        Fin.cast (by omega) (Fin.natAdd (n - (i.val + 1)) b)⟩) rfl
      exact X_eq_varF _ h1.1 h1.2 (congrArg Fin.val (hl _).1)
    · show aStep Dw a (conjEmb (tauE D t)) i = _
      rw [aStep, ham t i hi]
      congr 1
      split_ifs with h1
      · exact ham t _ (by omega)
      · rfl

abbrev sub (pW : D.what₂.Tau → ℕ) (U : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m n) ℂ :=
  MvPolynomial.aeval fun k : FVar D m n => ∑ b, MvPolynomial.C
    (if (k.2.1 : ℕ) < pW k.1 then (U k.1)⁻¹ k.2.2 b else conj ((U k.1)⁻¹ k.2.2 b)) * MvPolynomial.X (k.1, k.2.1, b)

theorem toF_gaStar (hl : IsLt lt) (h : IsTyp D H) (pW : D.what₂.Tau → ℕ) (hp : ∀ t, pW t = Dw.p)
    (ga : Matrix (Fin n) (Fin n) D.host.E) (U : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ t a b, (U t)⁻¹ a b = conj (tauE D t (ga b a))) (P : MvPolynomial (LtN Dw n) c.F) :
    toF c lt (gaStar c (ga.map (IsCMField.complexConj D.host.E)) P) = sub pW U (toF c lt P) := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, toF_C, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
  | add P Q hP hQ => simp only [map_add (f := _), hP, hQ]
  | mul_X P ℓ hP =>
    simp only [map_mul, hP]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [toF_X, gaStar, MvPolynomial.aeval_X, MvPolynomial.aeval_X, letB, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, toF_C, toF_X, hl.col h, hU, hp, (hl ℓ).1]
    congr 2
    show ℓ.1 (IsCMField.complexConj D.host.E (ga j ℓ.2.2)) = _
    rw [IsCMField.complexEmbedding_complexConj]
    rcases (hl ℓ).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos (h2 ▸ (hl.pos h h1).2.2)]
      exact congrArg (fun σ : D.host.E →+* ℂ => conj (σ _)) h1
    · rw [if_neg (by omega)]
      exact congrArg (fun σ : D.host.E →+* ℂ => conj (σ _)) h1

end Letters

section Real

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}

theorem gramAt_one (h : V.gram = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  rw [gramAt, h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem compAt_unitary (hθ : IsInfFam θ) (h : V.gram = 1) (g : GA D V) (τ : D.what₂.Tau) :
    (compAt θ τ (Formalism.L2.Theta.mt V g))ᴴ * compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  have h1 : (compAt θ τ (Formalism.L2.Theta.mt V g))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V g) = gramAt D V τ :=
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
  rwa [gramAt_one h, Matrix.mul_one] at h1

theorem det_ne_zero {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (h : gᴴ * g = 1) : g.det ≠ 0 :=
  (Matrix.isUnit_det_of_left_inverse h).ne_zero

theorem om_real {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hP : IsPair ψ θ V W χV χW om) {s BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ} {pW : D.what₂.Tau → ℕ}
    (hV : ∀ τ, IsCartanInv (gramAt D V τ) 1) (hs : ∀ τ, IsCartanInv (gramAt D W τ) (s τ))
    (hB : ∀ τ, IsONBasis (gramAt D W τ) (s τ) (BW τ) (pW τ)) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (s τ)) f) {g : GA D V} (hg : g ∈ GinfC V) :
    ∃ χ : ℂ, ‖χ‖ = 1 ∧ ∀ P, om (g, 1) (pureTensorO ψ θ V W (fun _ => 1) s (fun _ => 1) BW f P) =
      χ • pureTensorO ψ θ V W (fun _ => 1) s (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g)) BW f P := by
  choose a ha using hP.expV
  choose b hb using hP.expW
  choose x hx using fun τ => (trace_parity (hB τ)).2
  obtain ⟨k, hk⟩ := hP.even
  have h1 : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 := fun τ =>
    Matrix.map_one (f := (θ τ).comp (infPart D)) (map_zero _) (map_one _)
  have hvac := GlobalTheory.T.vacuum_character_positive_definite_source D ψ θ V W χV χW om hP.weil hP.inf hP.sigV hP.sigW s hV hs _ _ ha hb (fun τ => a τ + k)
    (fun τ => a τ - k) (fun τ => -(x τ + b τ)) (fun τ => by rw [hk]; push_cast; ring) (fun τ => by rw [hk]; push_cast; ring)
    (fun τ => by push_cast; rw [← hx]; ring) f hf hv g hg 1 (one_mem _) (fun τ => by rw [h1, Matrix.mul_one, Matrix.one_mul])
  refine ⟨_, ?_, fun P => by
    rw [(GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ V W χV χW om hP.weil hP.inf (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g)) s s BW BW g 1 (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [h1, Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [Matrix.mul_one])
      (fun τ => by rw [h1, Matrix.one_mul]) f hf P).2, hvac, GlobalTheory.FiniteFock.pureTensorO_smul]⟩
  rw [norm_prod]
  refine Finset.prod_eq_one fun τ _ => ?_
  have e1 : (1 / 2 : ℂ) • (1 + s τ) + (1 / 2 : ℂ) • (1 - s τ) = 1 := by module
  have e2 : (1 / 2 : ℂ) • (1 - s τ) + (1 / 2 : ℂ) • (1 + s τ) = 1 := by module
  have e3 : ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ = 1 := by
    have h2 := congrArg (fun M => ‖Matrix.det M‖) (compAt_unitary hP.inf hP.std g τ)
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star, Matrix.det_one, norm_one] at h2
    exact (mul_self_eq_one_iff.1 h2).resolve_right (by linarith [norm_nonneg (compAt θ τ (Formalism.L2.Theta.mt V g)).det])
  rw [h1, Matrix.mul_one, Matrix.mul_one, e1, e2, Matrix.det_one, _root_.one_zpow, _root_.one_zpow, one_mul, one_mul, norm_zpow, e3,
    _root_.one_zpow]

theorem rat_parts (hθ : IsInfFam θ) (h : V.gram = 1) (γ : GQ V) :
    ∃ (γE : GL (Fin V.rank) D.host.E) (a k : GA D V), Bridge.IsRatMat V γ γE ∧ a ∈ GinfC V ∧ k ∈ GfC V ∧ (γ : GA D V) = a * k ∧
      γE.valᴴ * γE.val = 1 ∧
      ∀ t i j, (compAt θ t (Formalism.L2.Theta.mt V a))⁻¹ i j = conj (tauE D t (γE.val j i)) := by
  obtain ⟨γE, hγ⟩ : ∃ γE, Bridge.IsRatMat V γ γE := by
    obtain ⟨x, hx⟩ := γ
    obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
    exact ⟨y, hy.symm⟩
  obtain ⟨a, ha, k, hk, e⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 γ
  have h1 : ∀ t, compAt θ t (Formalism.L2.Theta.mt V a) = γE.val.map (tauE D t) := fun t => by
    have h2 : compAt θ t (Formalism.L2.Theta.mt V (a * k)) =
        compAt θ t (Formalism.L2.Theta.mt V a) * compAt θ t (Formalism.L2.Theta.mt V k) :=
      Matrix.map_mul (L := Formalism.L2.Theta.mt V a) (M := Formalism.L2.Theta.mt V k) (f := (θ t).comp (infPart D))
    rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ t hk, Matrix.mul_one, ← e] at h2
    rw [← h2, Formalism.L2.Theta.mt, hγ]
    ext i j
    exact (hθ t).1 _
  refine ⟨γE, a, k, hγ, ha, hk, e, ?_, fun t i j => ?_⟩
  · have := D.host.isCMField_hostE
    obtain ⟨σ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    obtain ⟨t⟩ : Nonempty D.what₂.Tau := by
      by_cases hσ : ∃ τ, tauE D τ = σ
      · exact ⟨hσ.choose⟩
      · exact ⟨(not_not.1 ((GlobalTheory.SmoothForms.RealPts.tauE_cm D σ).not_left.1 hσ |> not_not.2)).choose⟩
    have h3 := compAt_unitary hθ h a t
    rw [h1] at h3
    refine Matrix.ext fun i j => (tauE D t).injective ?_
    have h4 := congrFun (congrFun h3 i) j
    rw [Matrix.mul_apply] at h4 ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Matrix.one_apply, apply_ite (tauE D t), map_one, map_zero, ← Matrix.one_apply, ← h4]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    congr 1
    exact IsCMField.complexEmbedding_complexConj D.host.E _ _
  · rw [Matrix.inv_eq_left_inv (compAt_unitary hθ h a t), h1]
    rfl

end Real


end GlobalTheory.AdTh.PhaseMap

end
