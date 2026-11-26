module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHtHalfSub
noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So GroundTheory.Global

namespace GlobalTheory.CompanionTheory.EisJMir

section Gen

variable {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']

theorem isHt_pull (j : G →* G') (hj : Continuous j) {Γ K P : Subgroup G} {Γ' K' P' : Subgroup G'} {η : G' → ℝ}
    (h : IsHt Γ' K' P' η) (hΓ : ∀ γ ∈ Γ, j γ ∈ Γ') (hK : ∀ k ∈ K, j k ∈ K') (hP : ∀ p ∈ P, j p ∈ P') :
    IsHt Γ K P (fun x => η (j x)) := by
  refine ⟨fun p hp g => ?_, fun g k hk => ?_, fun γ hγ hγP => ?_, h.cont.comp hj⟩
  · rw [map_mul]
    exact h.left (j p) (hP p hp) (j g)
  · rw [map_mul]
    exact h.right (j g) (j k) (hK k hk)
  · exact h.rat (j γ) (hΓ γ hγ) (hP γ hγP)

theorem isHt_of_top {Γ K P : Subgroup G} {η : G → ℝ} (h : IsHt Γ K ⊤ η) : IsHt Γ K P η := by
  exact ⟨fun p _ g => h.left p (Subgroup.mem_top p) g, h.right, fun γ hγ _ => h.rat γ hγ (Subgroup.mem_top γ),
    h.cont⟩

theorem isHt_half_add {Γ K P : Subgroup G} {a b : G → ℝ} (ha : IsHt Γ K P a) (hb : IsHt Γ K P b) :
    IsHt Γ K P (fun x => (a x + b x) / 2) := by
  refine ⟨fun p hp g => ?_, fun g k hk => ?_, fun γ hγ hγP => ?_, (ha.cont.add hb.cont).div_const 2⟩
  · rw [ha.left p hp g, hb.left p hp g]
    ring
  · rw [ha.right g k hk, hb.right g k hk]
  · rw [ha.rat γ hγ hγP, hb.rat γ hγ hγP]
    norm_num

theorem isHt_half_sub {Γ K P : Subgroup G} {a b : G → ℝ} (ha : IsHt Γ K P a) (hb : IsHt Γ K P b) :
    IsHt Γ K P (fun x => (a x - b x) / 2) := by
  refine ⟨fun p hp g => ?_, fun g k hk => ?_, fun γ hγ hγP => ?_, (ha.cont.sub hb.cont).div_const 2⟩
  · rw [ha.left p hp g, hb.left p hp g]
    ring
  · rw [ha.right g k hk, hb.right g k hk]
  · rw [ha.rat γ hγ hγP, hb.rat γ hγ hγP]
    norm_num

theorem isCh_pull (j : G →* G') (hj : Continuous j) {Γ P : Subgroup G} {Γ' P' : Subgroup G'} {u : G' → ℂ} {c : G → ℂ}
    (hu : IsCh Γ' P' u) (hc : IsCh Γ ⊤ c) (hΓ : ∀ γ ∈ Γ, j γ ∈ Γ') (hP : ∀ p ∈ P, j p ∈ P') :
    IsCh Γ P (fun x => u (j x) * (c x)⁻¹) := by
  have hc0 : ∀ x, c x ≠ 0 := fun x h0 => by
    have h1 := hc.norm x (Subgroup.mem_top x)
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  refine ⟨fun p hp q hq => ?_, fun p hp => ?_, fun γ hγ hγP => ?_, ?_⟩
  · rw [map_mul, hu.mul (j p) (hP p hp) (j q) (hP q hq), hc.mul p (Subgroup.mem_top p) q (Subgroup.mem_top q),
      mul_inv]
    ring
  · rw [norm_mul, norm_inv, hu.norm (j p) (hP p hp), hc.norm p (Subgroup.mem_top p)]
    norm_num
  · rw [hu.rat (j γ) (hΓ γ hγ) (hP γ hγP), hc.rat γ hγ (Subgroup.mem_top γ)]
    norm_num
  · refine (hu.cont.comp hj.continuousOn (fun x hx => hP x hx)).mul ?_
    exact (hc.cont.mono (fun x _ => Subgroup.mem_top x)).inv₀ (fun x _ => hc0 x)

end Gen

theorem jmir : StdGood → GrpTop → BdetLaw → ExtLaw → ParLaw → JTop → JCpt → JPar → JIwa → JRat → JCh → JMir := by
  intro hStd hGT hBd hExt hPar hJT hJC hJP hJI hJR hJCh F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hA hB
    hi hJ hIwa
  obtain ⟨hjc, -, -, -⟩ := hJT F E R A ε ν r δ α ω ι i j hA hB hi hJ
  have hcK := hJC F E R A ε ν r δ α ω ι i j hA hB hi hJ
  obtain ⟨hst, hQeq, hbd⟩ := hJP F E R A ε ν r δ α ω ι i j hA hB hi hJ
  have hIw := hJI F E R A ε ν r δ α ω ι i j hA hB hi hJ
  obtain ⟨hmapΓ, htr⟩ := hJR F E R A ε ν r δ α ω ι i j hA hB hi hJ
  obtain ⟨hc0, hld⟩ := hJCh F E R A ε ν r δ α ω ι i j hA hB hi hJ
  obtain ⟨hparU, hhtU, -⟩ := (hPar E R A hA ι ε Set.univ).2 (by rw [inf_idem]; exact hIwa)
  rw [inf_idem] at hparU
  have hGL := hA.toGoodL
  have hSG := (hStd F).lgmul
  have hlg1 : A.lg 1 = 0 := by
    have h := hGL.lgmul 1 1
    rw [mul_one] at h
    linarith
  have hP : ∀ p ∈ Subgroup.comap (prj A ν ι) (stab 𝔸[𝓞 F, F] {(Sum.inl i : ι ⊕ ι)}),
      j p ∈ A.uQ ε Set.univ := by
    intro p hp
    rw [← hQeq] at hp
    exact hp
  have hK : ∀ k ∈ cK α j, j k ∈ A.uK ε ι := fun k hk => (Subgroup.mem_inf.1 hk).1
  have hΓ : ∀ γ ∈ cΓ A ν ι, j γ ∈ A.uΓ ε ι := by
    intro γ hγ
    rw [← hmapΓ]
    exact Subgroup.mem_map_of_mem j hγ
  have hωsq : ∀ y : IdeleGroup F, ω.toIdele y * ω.toIdele y = 1 := by
    intro y
    rw [hB.ωχ, mul_eq_one_iff_eq_inv]
    have h1 := hA.χσ (Units.map (ν : 𝔸[𝓞 F, F] →* R) y)
    convert h1 using 2
    all_goals (ext; simp [hB.fix])
  have hcov : ∀ x : cover A ν ι, A.lg (x : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).1 =
      -(adStd F).lg (Matrix.GeneralLinearGroup.det (prj A ν ι x)) ∧
      A.χ (Units.map (ν : 𝔸[𝓞 F, F] →* R) (Matrix.GeneralLinearGroup.det (prj A ν ι x))) = 1 := by
    intro x
    have hx := MonoidHom.mem_ker.1 x.2
    simp only [MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst,
      MonoidHom.coe_snd] at hx
    constructor
    · have h := congrArg A.lg hx
      rw [hGL.lgmul, hGL.lgmul, hB.lgσ, hB.lg, hlg1] at h
      show A.lg (x : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).1 = -(adStd F).lg (Matrix.GeneralLinearGroup.det (x : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).2)
      linarith
    · have h := congrArg A.χ hx
      rw [map_mul, map_mul, hA.χσ, map_one, mul_inv_cancel, one_mul] at h
      exact h
  have hext : ∀ x ∈ Subgroup.comap (prj A ν ι) (stab 𝔸[𝓞 F, F] {(Sum.inl i : ι ⊕ ι)}),
      A.uH ε Set.univ (j x) = A.lg (bdet (Sum.inl '' (Set.univ : Set ι)) ((j x : A.U ε ι) : GL (ι ⊕ ι) R)) := by
    intro x hx
    obtain ⟨-, -, -, hT2U, -, -, hKc⟩ := hGT E R A hA ι ε
    haveI := hT2U
    obtain ⟨-, hmulS, hcontS, hratS, hkS, -⟩ := hBd E R A hGL (ι ⊕ ι) (Sum.inl '' (Set.univ : Set ι))
    have h := (hExt (A.U ε ι) (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε Set.univ)
      (fun p => A.lg (bdet (Sum.inl '' (Set.univ : Set ι)) (p : GL (ι ⊕ ι) R))) hKc hparU.closed hIwa
      (fun p hp q hq => by
        show A.lg (bdet _ ((p * q : A.U ε ι) : GL (ι ⊕ ι) R)) = _
        rw [Subgroup.coe_mul, hmulS _ (Subgroup.mem_subgroupOf.1 hp) _ (Subgroup.mem_subgroupOf.1 hq), hGL.lgmul])
      (hGL.lgcont.comp_continuousOn (hcontS.comp continuous_subtype_val.continuousOn
        (fun p hp => Subgroup.mem_subgroupOf.1 hp)))
      (fun p hp hk => hkS _ (Subgroup.mem_subgroupOf.1 hp) (Subgroup.mem_subgroupOf.1 hk))
      (fun p hp hg => by
        obtain ⟨e, he⟩ := hratS _ (Subgroup.mem_subgroupOf.1 hp) (Subgroup.mem_subgroupOf.1 hg)
        show A.lg _ = 0
        rw [he]
        exact hGL.lgi e)).2 (j x) (hP x hx) 1 (Subgroup.one_mem _)
    rw [mul_one] at h
    exact h
  refine ⟨?_, ?_, ?_, hcK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hld, ?_, ?_, fun g => rfl⟩
  · have h1 : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨i⟩
    rw [Fintype.card_sum]
    omega
  · refine ContinuousMonoidHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact hωsq y
  · exact continuous_snd.comp continuous_subtype_val
  · intro κ hκ
    obtain ⟨κ', hκ', hEq⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hκ).2)
    refine ⟨κ', hκ', ?_⟩
    have hd : (fun k : ι ⊕ ι => ((Sum.elim (fun _ => (1 : IdeleGroup F)) (fun _ => α) k : IdeleGroup F) : 𝔸[𝓞 F, F])) =
        (Sum.elim (fun _ => 1) (fun _ => (α : 𝔸[𝓞 F, F])) : ι ⊕ ι → 𝔸[𝓞 F, F]) := by
      funext k
      rcases k with k | k <;> rfl
    rw [hd]
    change ((prj A ν ι κ : GL (ι ⊕ ι) 𝔸[𝓞 F, F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[𝓞 F, F]) * ((dg ι α : GL (ι ⊕ ι) 𝔸[𝓞 F, F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[𝓞 F, F]) =
      ((dg ι α : GL (ι ⊕ ι) 𝔸[𝓞 F, F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[𝓞 F, F]) * (κ' : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[𝓞 F, F])
    rw [← hEq]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
  · intro γ hγ
    exact (Subgroup.mem_prod.1 (Subgroup.mem_subgroupOf.1 hγ)).2
  · intro s hs g hg
    obtain ⟨γ, hγ, h⟩ := htr g hg
    refine ⟨γ, hγ, ?_⟩
    rcases hs with rfl | rfl
    · exact h
    · rw [hst]
      exact h
  · refine ⟨?_, hIw, isCh_pull j hjc hparU.ch hc0 hΓ hP⟩
    rw [← hQeq, Subgroup.coe_comap]
    exact hparU.closed.preimage hjc
  · rw [hst]
    refine ⟨?_, hIw, isCh_pull j hjc hparU.ch hc0 hΓ hP⟩
    rw [← hQeq, Subgroup.coe_comap]
    exact hparU.closed.preimage hjc
  · exact isHt_half_add (isHt_pull j hjc hhtU hΓ hK hP) (isHt_of_top hld)
  · rw [hst]
    exact isHt_half_sub (isHt_pull j hjc hhtU hΓ hK hP) (isHt_of_top hld)
  · intro p hp
    obtain ⟨hb1, -⟩ := hbd p hp
    obtain ⟨hl, -⟩ := hcov p
    refine ⟨?_, ?_⟩
    · show (A.χ (bdet (Sum.inl '' Set.univ) ((j p : A.U ε ι) : GL (ι ⊕ ι) R)) : ℂ) *
          ((A.χ (p : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).1 : ℂ))⁻¹ = _
      rw [hb1, map_mul, Circle.coe_mul, hB.ωχ, mul_comm, ← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _),
        one_mul]
    · show (A.uH ε Set.univ (j p) + ld p) / 2 = _
      rw [hext p hp, hb1, hGL.lgmul, hB.lg, hl]
      simp only [So.ld]
      ring
  · intro p hp
    rw [hst] at hp
    obtain ⟨hb1, hb2⟩ := hbd p hp
    obtain ⟨hl, hχ⟩ := hcov p
    have hωb : ω.toIdele (bdet {Sum.inl i} (prj A ν ι p)) = ω.toIdele (bdet {Sum.inr i} (prj A ν ι p)) := by
      have h3 : ω.toIdele (bdet {Sum.inl i} (prj A ν ι p)) * ω.toIdele (bdet {Sum.inr i} (prj A ν ι p)) = 1 := by
        rw [hB.ωχ, hB.ωχ, ← map_mul, ← map_mul, ← hb2]
        exact hχ
      exact mul_right_cancel (h3.trans (hωsq _).symm)
    refine ⟨?_, ?_⟩
    · show (A.χ (bdet (Sum.inl '' Set.univ) ((j p : A.U ε ι) : GL (ι ⊕ ι) R)) : ℂ) *
          ((A.χ (p : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).1 : ℂ))⁻¹ = _
      rw [hb1, map_mul, Circle.coe_mul, ← hωb, hB.ωχ, mul_comm, ← mul_assoc,
        inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul]
    · show (A.uH ε Set.univ (j p) - ld p) / 2 = _
      rw [hext p hp, hb1, hGL.lgmul, hB.lg, hl]
      simp only [So.ld]
      rw [hb2, hSG]
      ring

end GlobalTheory.CompanionTheory.EisJMir
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinIdele
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GroundTheory.Global GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal
open scoped TensorProduct NumberField.AdeleRing WithZero

noncomputable section
namespace GlobalTheory.CompanionTheory.CMDelta

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_delta (h : IsCMExt F E σ) :
    ∃ (δ : E) (d : F), δ ≠ 0 ∧ σ δ = -δ ∧ algebraMap F E d = δ ^ 2 := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  have : IsGalois F E := inferInstance
  have hσ := GlobalTheory.LFun.InertChart.conj_conj h
  have hne := GlobalTheory.LFun.InertChart.conj_ne h
  obtain ⟨e, he⟩ : ∃ e, σ e ≠ e := by
    by_contra hn
    push Not at hn
    exact hne hn
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  have hs1 : s ≠ 1 := fun hs => he (congrArg (fun t : E ≃ₐ[F] E => t e) hs)
  have hfix : ∀ t : E ≃ₐ[F] E, t ((e - σ e) ^ 2) = (e - σ e) ^ 2 := fun t => by
    have hc : Nat.card (E ≃ₐ[F] E) = 2 := (IsGalois.card_aut_eq_finrank F E).trans h.2.2.1
    obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hc
    by_cases ht : t = 1
    · rw [ht]; rfl
    · rw [(hu t ht).trans (hu s hs1).symm]
      change σ _ = _
      rw [map_pow, map_sub, hσ]; ring
  obtain ⟨d, hd⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  exact ⟨e - σ e, d, sub_ne_zero.2 (Ne.symm he), by rw [map_sub, hσ]; ring, hd⟩

theorem val_square (hU : Algebra.Unramified (𝓞 F) (𝓞 E)) {δ : E} {d : F} (hd : algebraMap F E d = δ ^ 2)
    (w : HeightOneSpectrum (𝓞 E)) :
    w.valuation E δ ^ 2 = (below F w).valuation F d := by
  have hram : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have h1 := valued_completionMap (below F w) w (algebraMap F _ d)
  rw [completionMap_algebraMap, hram, pow_one, IsScalarTower.algebraMap_apply F E (w.adicCompletion E),
    HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.algebraMap_adicCompletion] at h1
  simp only [Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self, RingHom.id_apply] at h1
  rw [← h1, hd, map_pow]

theorem valued_alg {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self, RingHom.id_apply]

theorem exists_finIdele {d : F} (hd0 : d ≠ 0) :
    ∃ (X : (FiniteAdeleRing (𝓞 F) F)ˣ), ∀ (v : HeightOneSpectrum (𝓞 F)) (k : ℤ),
      v.valuation F d = WithZero.exp (2 * k) → Valued.v ((X : FiniteAdeleRing (𝓞 F) F) v) = WithZero.exp k := by
  classical
  choose π hπ using fun v : HeightOneSpectrum (𝓞 F) => v.valuation_exists_uniformizer F
  let n : HeightOneSpectrum (𝓞 F) → ℤ := fun v => WithZero.log (v.valuation F d) / 2
  have hev : ∀ᶠ v in Filter.cofinite, n v = 0 := by
    have h1 := (algebraMap F (FiniteAdeleRing (𝓞 F) F) d).2
    have h2 := (algebraMap F (FiniteAdeleRing (𝓞 F) F) d⁻¹).2
    filter_upwards [h1, h2] with v a b
    have a' : v.valuation F d ≤ 1 := by
      have := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 a
      exact (valued_alg v d).symm.le.trans this
    have b' : v.valuation F d⁻¹ ≤ 1 := by
      have := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 b
      exact (valued_alg v d⁻¹).symm.le.trans this
    have : v.valuation F d = 1 := by
      rw [map_inv₀] at b'
      exact le_antisymm a' ((inv_le_one₀ (zero_lt_iff.2 (by simpa using hd0))).1 b')
    simp [n, this]
  let f : ℤ → ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F := fun s v =>
    (algebraMap F (v.adicCompletion F) (π v)) ^ (s * n v)
  have hfmem : ∀ s : ℤ, ∀ᶠ v in Filter.cofinite, f s v ∈ v.adicCompletionIntegers F := fun s => by
    filter_upwards [hev] with v hv
    simp [f, hv, one_mem]
  let X (s : ℤ) : FiniteAdeleRing (𝓞 F) F := ⟨f s, hfmem s⟩
  have hne : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) (π v) ≠ 0 := fun v h => by
    have := valued_alg v (π v)
    rw [h, map_zero, hπ v] at this
    exact WithZero.exp_ne_zero this.symm
  refine ⟨⟨X (-1), X 1, ?_, ?_⟩, fun v k hk => ?_⟩
  · refine FiniteAdeleRing.ext (K := F) fun v => ?_
    change f (-1) v * f 1 v = 1
    simp only [f]
    rw [← zpow_add₀ (hne v)]
    simp
  · refine FiniteAdeleRing.ext (K := F) fun v => ?_
    change f 1 v * f (-1) v = 1
    simp only [f]
    rw [← zpow_add₀ (hne v)]
    simp
  · change Valued.v (f (-1) v) = _
    have hn : n v = k := by
      simp only [n]
      rw [hk, WithZero.log_exp]
      omega
    simp only [f, hn]
    rw [map_zpow₀, valued_alg, hπ]
    rw [← WithZero.exp_zsmul]
    simp

theorem exists_infIdele {d : F} (hd0 : d ≠ 0) (hr : NumberField.IsTotallyReal F) :
    ∃ T : (InfiniteAdeleRing F)ˣ, ∀ v : InfinitePlace F,
      (T : InfiniteAdeleRing F) v ^ 2 = algebraMap F (InfiniteAdeleRing F) d v ∨
      (T : InfiniteAdeleRing F) v ^ 2 = -algebraMap F (InfiniteAdeleRing F) d v := by
  have key : ∀ v : InfinitePlace F, ∃ t : v.Completion, t ≠ 0 ∧
      (t ^ 2 = algebraMap F (InfiniteAdeleRing F) d v ∨ t ^ 2 = -algebraMap F (InfiniteAdeleRing F) d v) := by
    intro v
    have hv : v.IsReal := NumberField.IsTotallyReal.isReal v
    let f := InfinitePlace.Completion.ringEquivRealOfIsReal hv
    have ha : algebraMap F (InfiniteAdeleRing F) d v ≠ 0 :=
      (map_ne_zero (algebraMap F v.Completion)).2 hd0
    set a := algebraMap F (InfiniteAdeleRing F) d v with hadef
    have hfa : f a ≠ 0 := (map_ne_zero f).2 ha
    refine ⟨f.symm (Real.sqrt |f a|), ?_, ?_⟩
    · exact (map_ne_zero f.symm).2 (Real.sqrt_ne_zero'.2 (abs_pos.2 hfa))
    · rw [← map_pow, Real.sq_sqrt (abs_nonneg _)]
      rcases abs_choice (f a) with h | h
      · left; rw [h]; simp
      · right; rw [h, map_neg]; simp
  choose t ht0 ht using key
  refine ⟨⟨t, fun v => (t v)⁻¹, ?_, ?_⟩, ht⟩
  · funext v; exact mul_inv_cancel₀ (ht0 v)
  · funext v; exact inv_mul_cancel₀ (ht0 v)

theorem bDel : PositivityTheory.RgEis.So.BDel := by
  intro F E _ _ _ _ _ σ χ c hcm hU _ _
  obtain ⟨δ, d, hδ0, hσ, hd⟩ := exists_delta hcm
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hd
    exact hδ0 (pow_eq_zero_iff (two_ne_zero) |>.1 hd.symm)
  obtain ⟨X, hX⟩ := exists_finIdele hd0
  obtain ⟨T, hT⟩ := exists_infIdele hd0 hcm.1
  let α : IdeleGroup F := MulEquiv.prodUnits.symm (T, X)
  let δu : Eˣ := Units.mk0 δ hδ0
  let A := PositivityTheory.RgEis.adCM σ χ
  let ν := PositivityTheory.RgEis.So.nuCM F E
  let u := Units.map A.i.toMonoidHom δu * (Units.map ν.toMonoidHom α)⁻¹
  have hνe : ∀ z, PositivityTheory.RgEis.eqv F E (ν z) = adeleMap F E z := fun z => by
    change GroundTheory.BlockD.ThmBHecke.adeleEquiv F E (z ⊗ₜ 1) = _
    rw [GroundTheory.BlockD.ThmBHecke.adeleEquiv_tmul, map_one, one_mul]
  have hie : ∀ e, PositivityTheory.RgEis.eqv F E (A.i e) = algebraMap E 𝔸[E] e := fun e => by
    change GroundTheory.BlockD.ThmBHecke.adeleEquiv F E (1 ⊗ₜ e) = _
    rw [GroundTheory.BlockD.ThmBHecke.adeleEquiv_tmul, map_one, mul_one]
  have hdec : A.i δ = ν α * u := by
    change A.i δ = ν α * (A.i δ * ((Units.map ν.toMonoidHom α)⁻¹ : (_)ˣ).1)
    have : ν α * ((Units.map ν.toMonoidHom α)⁻¹ : (_)ˣ).1 = 1 := Units.mul_inv (Units.map ν.toMonoidHom α)
    rw [mul_left_comm, this, mul_one]
  set y := PositivityTheory.RgEis.eqv F E u with hy
  set y' := PositivityTheory.RgEis.eqv F E ((u⁻¹ : (_)ˣ) : _) with hy'
  have h1 : adeleMap F E α * y = algebraMap E 𝔸[E] δ := by
    rw [← hνe, hy, ← map_mul, ← hdec, hie]
  have h2 : y * y' = 1 := by
    rw [hy, hy', ← map_mul, Units.mul_inv, map_one]
  have hfin : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (y.2 w) = 1 := by
    intro w
    have hram : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    have hw0 : w.valuation E δ ≠ 0 := by simpa using hδ0
    obtain ⟨k, hk⟩ : ∃ k : ℤ, w.valuation E δ = WithZero.exp k :=
      ⟨WithZero.log (w.valuation E δ), (WithZero.exp_log hw0).symm⟩
    have hsq := val_square hU hd w
    have hval : (below F w).valuation F d = WithZero.exp (2 * k) := by
      rw [← hsq, hk, ← WithZero.exp_nsmul]
      simp
    have hX' := hX (below F w) k hval
    have hA : Valued.v ((adeleMap F E α).2 w) = WithZero.exp k := by
      change Valued.v (completionMap (below F w) w ((X : FiniteAdeleRing (𝓞 F) F) (below F w))) = _
      rw [valued_completionMap, hram, pow_one, hX']
    have hc : (adeleMap F E α).2 w * y.2 w = algebraMap E (w.adicCompletion E) δ :=
      congrArg (fun z : 𝔸[E] => z.2 w) h1
    have hv := congrArg Valued.v hc
    rw [map_mul, hA, show Valued.v (algebraMap E (w.adicCompletion E) δ) = w.valuation E δ from valued_alg w δ, hk] at hv
    exact mul_left_cancel₀ (WithZero.exp_ne_zero (a := k)) (hv.trans (mul_one _).symm)
  have hfin' : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (y'.2 w) = 1 := by
    intro w
    have hc : y.2 w * y'.2 w = 1 := congrArg (fun z : 𝔸[E] => z.2 w) h2
    have hv := congrArg Valued.v hc
    rwa [map_mul, hfin w, one_mul, map_one] at hv
  have hinf : ∀ w : InfinitePlace E, ‖y.1 w‖ = 1 := by
    intro w
    set D : w.Completion := algebraMap E (InfiniteAdeleRing E) δ w with hD
    have hD0 : D ≠ 0 := (map_ne_zero (algebraMap E w.Completion)).2 hδ0
    set v := w.comap (algebraMap F E) with hv
    set Aw : w.Completion := (adeleMap F E α).1 w with hAw
    have hAsq : Aw ^ 2 = D ^ 2 ∨ Aw ^ 2 = -D ^ 2 := by
      obtain ⟨g, hg⟩ : ∃ g : v.Completion →+* w.Completion, ∀ x : InfiniteAdeleRing F,
          GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) x w = g (x v) :=
        ⟨_, fun x => GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply x w⟩
      have hAw' : Aw = g ((T : InfiniteAdeleRing F) v) := hg _
      have hm : g (algebraMap F (InfiniteAdeleRing F) d v) = D ^ 2 := by
        have := congrFun (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_algebraMap (K := F) (L := E) d) w
        rw [hg, hd, map_pow] at this
        exact this
      rcases hT v with h | h
      · left; rw [hAw', ← map_pow, h, hm]
      · right; rw [hAw', ← map_pow, h, map_neg, hm]
    have hnorm : ‖Aw‖ = ‖D‖ := by
      have : ‖Aw‖ ^ 2 = ‖D‖ ^ 2 := by
        rcases hAsq with h | h
        · rw [← norm_pow, h, norm_pow]
        · rw [← norm_pow, h, norm_neg, norm_pow]
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
    have hc : Aw * y.1 w = D := congrArg (fun z : 𝔸[E] => z.1 w) h1
    have hn := congrArg norm hc
    rw [norm_mul, hnorm] at hn
    exact mul_left_cancel₀ (norm_ne_zero_iff.2 hD0) (hn.trans (mul_one _).symm)
  have hint : ∀ z : 𝔸[E], (∀ w : HeightOneSpectrum (𝓞 E), Valued.v (z.2 w) = 1) → z ∈ PositivityTheory.RgEis.intAd E := by
    intro z hz
    refine (Subring.mem_iInf).2 fun w => ?_
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).2 (hz w).le
  have hφ : ∀ w : InfinitePlace E, ‖(InfinitePlace.Completion.extensionEmbedding w) (y.1 w)‖ = 1 := fun w => by
    rw [← hinf w]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _
  refine ⟨δu, α, u, hσ, hdec, hint y hfin, hint y' hfin', fun w => hφ w⟩

end GlobalTheory.CompanionTheory.CMDelta
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteKTypeDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteKTypeDecomposition
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelRep

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

section Rep

variable {G : Type} [Group G] {K : Subgroup G} {V : Submodule ℂ (G → ℂ)}

def rt (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) : K →* Module.End ℂ V where
  toFun k :=
    { toFun := fun v => ⟨fun x => v.1 (x * (k : G)), hV v.1 v.2 k⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext x
    simp
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext x
    simp [mul_assoc]

theorem rt_apply (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (k : K) (v : V) (x : G) :
    (rt hV k v).1 x = v.1 (x * (k : G)) := rfl

variable [FiniteDimensional ℂ V]

def mat (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (k : K) :
    Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
  LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (rt hV k)

theorem mat_mul (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (a b : K) :
    mat hV (a * b) = mat hV a * mat hV b := by
  simp only [mat, map_mul]
  exact LinearMap.toMatrix_mul _ _ _

theorem mat_one (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) : mat hV 1 = 1 := by
  simp only [mat, map_one]
  exact LinearMap.toMatrix_one _

def rho (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) :
    K →* ((Fin (Module.finrank ℂ V) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ V) → ℂ)) where
  toFun k := LinearMap.toContinuousLinearMap (Matrix.toLin' (mat hV k⁻¹)ᵀ)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro a
    simp [mat_one]
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro x
    simp [mul_inv_rev, mat_mul, Matrix.transpose_mul, Matrix.mulVec_mulVec]

theorem rho_apply (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (k : K)
    (a : Fin (Module.finrank ℂ V) → ℂ) (i : Fin (Module.finrank ℂ V)) :
    rho hV k a i = ∑ j, (Module.finBasis ℂ V).repr (rt hV k⁻¹ (Module.finBasis ℂ V i)) j * a j := by
  change ((mat hV k⁻¹)ᵀ *ᵥ a) i = _
  simp [Matrix.mulVec, dotProduct, mat, LinearMap.toMatrix_apply]

theorem sum_repr_apply (z : V) (x : G) :
    ∑ j, (Module.finBasis ℂ V).repr z j * (Module.finBasis ℂ V j).1 x = z.1 x := by
  have h := congrArg (fun y : V => y.1 x) ((Module.finBasis ℂ V).sum_repr z)
  simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  exact h

def w₀ (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V] : Fin (Module.finrank ℂ V) → ℂ :=
  fun j => (Module.finBasis ℂ V j).1 1

theorem rho_w₀ (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (k : K)
    (i : Fin (Module.finrank ℂ V)) : rho hV k (w₀ V) i = (Module.finBasis ℂ V i).1 ((k : G)⁻¹) := by
  rw [rho_apply]
  simp only [w₀]
  rw [sum_repr_apply, rt_apply]
  simp

end Rep

section Cont

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K : Subgroup G}
  {V : Submodule ℂ (G → ℂ)} [FiniteDimensional ℂ V]

def evl (V : Submodule ℂ (G → ℂ)) (x : G) : Module.Dual ℂ V := (LinearMap.proj x).comp V.subtype

theorem span_evl : Submodule.span ℂ (Set.range (evl V)) = ⊤ := by
  have h : (Submodule.span ℂ (Set.range (evl V))).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    have : v = 0 := by
      apply Subtype.ext
      funext x
      exact hv _ (Submodule.subset_span ⟨x, rfl⟩)
    simp [this]
  have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq
    (W := Submodule.span ℂ (Set.range (evl V)))
  rw [h] at h2
  simpa using h2.symm

theorem cont_coef (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V)
    (hc : ∀ v ∈ V, Continuous v) (ℓ : Module.Dual ℂ V) (v : V) :
    Continuous fun k : K => ℓ (rt hV k⁻¹ v) := by
  have hℓ : ℓ ∈ Submodule.span ℂ (Set.range (evl V)) := by
    rw [span_evl]
    trivial
  induction hℓ using Submodule.span_induction with
  | mem ℓ h =>
    obtain ⟨x, rfl⟩ := h
    have h1 : Continuous fun k : K => x * (((k⁻¹ : K)) : G) :=
      continuous_const.mul (continuous_subtype_val.comp continuous_inv)
    exact (hc v.1 v.2).comp h1
  | zero => simpa using continuous_const
  | add a b _ _ ha hb => exact ha.add hb
  | smul a ℓ _ h => exact continuous_const.mul h

theorem rho_cont (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V)
    (hc : ∀ v ∈ V, Continuous v) : Continuous (rho hV) := by
  rw [continuous_clm_apply]
  intro a
  refine continuous_pi fun i => ?_
  simp only [rho_apply]
  refine continuous_finsetSum _ fun j _ => ?_
  exact (cont_coef hV hc ((Module.finBasis ℂ V).coord j) _).mul continuous_const

end Cont

theorem ch_one {G : Type} [Group G] [TopologicalSpace G] {Γ P : Subgroup G} {c : G → ℂ}
    (h : IsCh Γ P c) : c 1 = 1 := by
  have h1 := h.mul 1 P.one_mem 1 P.one_mem
  have h2 := h.norm 1 P.one_mem
  have h0 : c 1 ≠ 0 := by
    intro h0
    simp [h0] at h2
  rw [mul_one] at h1
  exact mul_left_cancel₀ h0 (by rw [mul_one]; exact h1.symm)

theorem exists_rep : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ K P : Subgroup G) (c : G → ℂ) (η : G → ℝ), IsCh Γ P c → (∀ r ∈ P, r ∈ K → η r = 0) → (∀ p ∈ P, ∀ q ∈ P, η (p * q) = η p + η q) → ∀ (f : G → ℂ) (u : ℂ), Continuous f → (∀ p ∈ P, ∀ x, f (p * x) = c p * Complex.exp (u * η p) * f x) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * (k : G)))) → ∃ (d : ℕ) (ρ : K →* ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ))) (w : Fin d → ℂ) (e : (Fin d → ℂ) →L[ℂ] ℂ), Continuous ρ ∧ w ∈ secSp K P c ρ ∧ ∀ k : K, e (ρ k⁻¹ w) = f k := by
  intro G _ _ _ Γ K P c η hch hηK _ f u hf hlaw hfd
  obtain ⟨V, hVdef⟩ : ∃ V : Submodule ℂ (G → ℂ),
      V = Submodule.span ℂ (Set.range fun k : K => fun x => f (x * (k : G))) := ⟨_, rfl⟩
  rw [← hVdef] at hfd
  have hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V := by
    intro v hv k
    rw [hVdef] at hv ⊢
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k', rfl⟩ := hv
      exact Submodule.subset_span ⟨k * k', by funext x; simp [mul_assoc]⟩
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul a v _ hv => exact Submodule.smul_mem _ a hv
  have hcont : ∀ v ∈ V, Continuous v := by
    intro v hv
    rw [hVdef] at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k', rfl⟩ := hv
      exact hf.comp (continuous_id.mul continuous_const)
    | zero => exact continuous_const
    | add a b _ _ ha hb => exact ha.add hb
    | smul a v _ hv => exact continuous_const.smul hv
  have hl : ∀ v ∈ V, ∀ p ∈ P, ∀ x, v (p * x) = c p * Complex.exp (u * η p) * v x := by
    intro v hv p hp x
    rw [hVdef] at hv
    induction hv using Submodule.span_induction generalizing x with
    | mem v hv =>
      obtain ⟨k', rfl⟩ := hv
      change f (p * x * (k' : G)) = c p * Complex.exp (u * η p) * f (x * (k' : G))
      rw [mul_assoc, hlaw p hp]
    | zero => simp
    | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb]; ring
    | smul a v _ hv => simp only [Pi.smul_apply, hv, smul_eq_mul]; ring
  have hfV : f ∈ V := by
    rw [hVdef]
    exact Submodule.subset_span ⟨1, by funext x; simp⟩
  refine ⟨Module.finrank ℂ V, rho hV, w₀ V,
    ∑ i, (Module.finBasis ℂ V).repr ⟨f, hfV⟩ i •
      (ContinuousLinearMap.proj i : (Fin (Module.finrank ℂ V) → ℂ) →L[ℂ] ℂ),
    rho_cont hV hcont, ?_, ?_⟩
  · intro r hr
    funext i
    have hri : ((r : G))⁻¹ ∈ P := P.inv_mem hr
    have hrK : ((r : G))⁻¹ ∈ K := K.inv_mem r.2
    have h1 := hl _ (Module.finBasis ℂ V i).2 _ hri 1
    have h2 : c r * c ((r : G))⁻¹ = 1 := by
      rw [← hch.mul _ hr _ hri, mul_inv_cancel, ch_one hch]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [rho_w₀]
    rw [mul_one, hηK _ hri hrK] at h1
    rw [h1]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    rw [← mul_assoc, h2, one_mul]
    rfl
  · intro k
    have h := sum_repr_apply (V := V) ⟨f, hfV⟩ (k : G)
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    simp only [rho_w₀]
    simpa using h

end GlobalTheory.CompanionTheory.SiegelRep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteKTypeDecompositionStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_K_type_decomposition : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ K P : Subgroup G) (c : G → ℂ) (η : G → ℝ), IsCh Γ P c → (∀ r ∈ P, r ∈ K → η r = 0) → (∀ p ∈ P, ∀ q ∈ P, η (p * q) = η p + η q) → ∀ (f : G → ℂ) (u : ℂ), Continuous f → (∀ p ∈ P, ∀ x, f (p * x) = c p * Complex.exp (u * η p) * f x) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * (k : G)))) → ∃ (d : ℕ) (ρ : K →* ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ))) (w : Fin d → ℂ) (e : (Fin d → ℂ) →L[ℂ] ℂ), Continuous ρ ∧ w ∈ secSp K P c ρ ∧ ∀ k : K, e (ρ k⁻¹ w) = f k := by
  first | exact @GlobalTheory.CompanionTheory.SiegelRep.exists_rep | exact GlobalTheory.CompanionTheory.SiegelRep.exists_rep | (intros; apply GlobalTheory.CompanionTheory.SiegelRep.exists_rep <;> assumption)
end
end
