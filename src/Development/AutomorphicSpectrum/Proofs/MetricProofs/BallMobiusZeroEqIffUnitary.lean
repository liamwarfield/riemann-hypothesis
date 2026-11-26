module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFromOrbitCharts
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietySecond
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartImmersion

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroEqIffUnitary
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroEqIffUnitary
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab

variable {j j' : ℕ}

theorem sg_fb {a : Matrix (Fin j) (Fin j) ℂ} {b : Matrix (Fin j) (Fin j') ℂ}
    {c : Matrix (Fin j') (Fin j) ℂ} {d : Matrix (Fin j') (Fin j') ℂ}
    (h : IsSgU (fromBlocks a b c d)) :
    aᴴ * a - cᴴ * c = 1 ∧ aᴴ * b - cᴴ * d = 0 ∧ bᴴ * b - dᴴ * d = -1 := by
  unfold IsSgU sgI at h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h
  obtain ⟨h1, h2, -, h4⟩ := fromBlocks_inj.1 h
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.mul_neg, add_zero, zero_add] at h1 h2 h4
  refine ⟨?_, ?_, ?_⟩
  · simpa [sub_eq_add_neg] using h1
  · simpa [sub_eq_add_neg] using h2
  · simpa [sub_eq_add_neg] using h4

theorem unit_of_rel {a : Matrix (Fin j) (Fin j) ℂ} {c : Matrix (Fin j') (Fin j) ℂ}
    (h : aᴴ * a - cᴴ * c = 1) : IsUnit a.det := by
  have e : aᴴ * a = 1 + cᴴ * c := by rw [← h]; abel
  have pd : (aᴴ * a).PosDef := by
    rw [e]
    exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self c)
  have hu : IsUnit (aᴴ * a).det := (Matrix.isUnit_iff_isUnit_det _).1 pd.isUnit
  rw [Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

theorem sgI_mul_self : sgI j j' * sgI j j' = 1 := by
  unfold sgI
  rw [fromBlocks_multiply]
  simp

theorem IsSgU.mul {u v : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) (hv : IsSgU v) : IsSgU (u * v) := by
  unfold IsSgU at *
  rw [conjTranspose_mul]
  calc vᴴ * uᴴ * sgI j j' * (u * v) = vᴴ * (uᴴ * sgI j j' * u) * v := by
        simp only [Matrix.mul_assoc]
    _ = sgI j j' := by rw [hu, hv]

theorem IsSgU.det_unit {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) : IsUnit u.det := by
  have : (sgI j j' * uᴴ * sgI j j') * u = 1 := by
    have e : sgI j j' * uᴴ * sgI j j' * u = sgI j j' * (uᴴ * sgI j j' * u) := by
      simp only [Matrix.mul_assoc]
    rw [e, show uᴴ * sgI j j' * u = sgI j j' from hu, sgI_mul_self]
  exact Matrix.isUnit_det_of_left_inverse this

theorem unitary_iff_fb {p : Matrix (Fin j) (Fin j) ℂ} {b : Matrix (Fin j) (Fin j') ℂ}
    {r : Matrix (Fin j') (Fin j) ℂ} {s : Matrix (Fin j') (Fin j') ℂ}
    (h : IsSgU (fromBlocks p b r s)) :
    (fromBlocks p b r s)ᴴ * fromBlocks p b r s = 1 ↔ r = 0 := by
  obtain ⟨h1, h2, h3⟩ := sg_fb h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]
  constructor
  · intro e
    obtain ⟨e1, -, -, -⟩ := fromBlocks_inj.1 e
    have hz : (2 : ℂ) • (rᴴ * r) = 0 := by
      have : rᴴ * r + rᴴ * r = 0 := by
        have := sub_eq_zero.2 (e1.trans h1.symm)
        rw [← this]; abel
      rw [two_smul]; exact this
    have hz' : rᴴ * r = 0 := (smul_eq_zero.1 hz).resolve_left two_ne_zero
    exact conjTranspose_mul_self_eq_zero.1 hz'
  · rintro rfl
    simp only [conjTranspose_zero, Matrix.zero_mul, sub_zero, add_zero] at h1 h2 h3 ⊢
    have hp : p * pᴴ = 1 := mul_eq_one_comm.1 h1
    have hb : b = 0 := by
      have : p * (pᴴ * b) = b := by rw [← Matrix.mul_assoc, hp, Matrix.one_mul]
      rw [← this, h2, Matrix.mul_zero]
    subst hb
    simp only [conjTranspose_zero, Matrix.zero_mul, zero_sub, neg_inj] at h3
    simp [h1, h3]

theorem single_fb {a p : Matrix (Fin j) (Fin j) ℂ} {b e : Matrix (Fin j) (Fin j') ℂ}
    {c r : Matrix (Fin j') (Fin j) ℂ} {d s : Matrix (Fin j') (Fin j') ℂ}
    (hu : IsSgU (fromBlocks a b c d)) (hv : IsSgU (fromBlocks p e r s)) :
    c * a⁻¹ = (c * p + d * r) * (a * p + b * r)⁻¹ ↔ r = 0 := by
  have ha : IsUnit a.det := unit_of_rel (sg_fb hu).1
  have hp : IsUnit p.det := unit_of_rel (sg_fb hv).1
  have hw : IsUnit (a * p + b * r).det := by
    have := IsSgU.mul hu hv
    rw [fromBlocks_multiply] at this
    exact unit_of_rel (sg_fb this).1
  constructor
  · intro h
    have h' : c * a⁻¹ * (a * p + b * r) = c * p + d * r := by
      rw [h, Matrix.nonsing_inv_mul_cancel_right _ _ hw]
    have hs : (d - c * a⁻¹ * b) * r = 0 := by
      have e1 : c * a⁻¹ * (a * p + b * r) = c * p + c * a⁻¹ * b * r := by
        rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ ha, Matrix.mul_assoc (c * a⁻¹) b r]
      rw [e1] at h'
      have : c * a⁻¹ * b * r = d * r := add_left_cancel h'
      rw [Matrix.sub_mul, this, sub_self]
    have hS : IsUnit (d - c * a⁻¹ * b).det := by
      have hd := IsSgU.det_unit hu
      letI := Matrix.invertibleOfIsUnitDet a ha
      rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv] at hd
      exact isUnit_of_mul_isUnit_right hd
    have : (d - c * a⁻¹ * b)⁻¹ * ((d - c * a⁻¹ * b) * r) = r :=
      Matrix.nonsing_inv_mul_cancel_left _ _ hS
    rw [← this, hs, Matrix.mul_zero]
  · rintro rfl
    simp only [Matrix.mul_zero, add_zero]
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hp]

theorem single {u v : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) (hv : IsSgU v) :
    u.toBlocks₂₁ * u.toBlocks₁₁⁻¹ = (u * v).toBlocks₂₁ * (u * v).toBlocks₁₁⁻¹ ↔ vᴴ * v = 1 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, u = fromBlocks a b c d :=
    ⟨_, _, _, _, (fromBlocks_toBlocks u).symm⟩
  obtain ⟨p, e, r, s, rfl⟩ : ∃ a b c d, v = fromBlocks a b c d :=
    ⟨_, _, _, _, (fromBlocks_toBlocks v).symm⟩
  rw [unitary_iff_fb hv, ← single_fb hu hv, fromBlocks_multiply]
  simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₁₁]

theorem ballPt_inj {Ψ : Type} {n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)
    {W W' : Ψ → Matrix (Fin j') (Fin j) ℂ} (h : ballPt q W = ballPt q W') : W = W' := by
  funext τ
  ext i' i
  have := congrFun h (q (τ, i, i'))
  simpa [ballPt] using this

theorem moebBall_zero {Ψ : Type} [Fintype Ψ] {n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (w : Ψ → Matrix (Sg j j') (Sg j j') ℂ) :
    moebBall q w 0 = ballPt q fun τ => (w τ).toBlocks₂₁ * (w τ).toBlocks₁₁⁻¹ := by
  have hb : ∀ τ, (ballMat q (0 : Fin n → ℂ) τ)ᵀ = 0 := by
    intro τ
    ext a b
    simp [ballMat]
  unfold moebBall
  congr 1
  funext τ
  rw [hb τ]
  simp [moebW]

theorem moebBall_zero_iff : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, IsSgU (u τ)) → (∀ τ, IsSgU (v τ)) → (moebBall q u 0 = moebBall q (fun τ => u τ * v τ) 0 ↔ ∀ τ, (v τ)ᴴ * v τ = 1) := by
  intro Ψ _ j j' n q u v hu hv
  rw [moebBall_zero, moebBall_zero]
  constructor
  · intro h τ
    exact (single (hu τ) (hv τ)).1 (congrFun (ballPt_inj q h) τ)
  · intro h
    congr 1
    funext τ
    exact (single (hu τ) (hv τ)).2 (h τ)

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroEqIffUnitaryStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_mobius_zero_eq_iff_unitary : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, IsSgU (u τ)) → (∀ τ, IsSgU (v τ)) → (moebBall q u 0 = moebBall q (fun τ => u τ * v τ) 0 ↔ ∀ τ, (v τ)ᴴ * v τ = 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab.moebBall_zero_iff | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab.moebBall_zero_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab.moebBall_zero_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagBundlePartialBlockMap
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagBundlePartialBlockMap
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
open GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl

theorem exists_res {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
    (hP : IsMultiHomogIdeal P) (hnd : ¬ (⊤ : Ideal (MRing ι)) ≤ P)
    (hcov : ∀ z ∈ mcPts P, ∃ C : OrbitChart P e, z ∈ C.O) :
    ∃ R : AnLogRes P ⊤ e, ∀ C : OrbitChart P e, (mcPts P).Nonempty → ∃ ψ : OpenPartialHomeomorph R.X (Fin e → ℂ),
      IsCompatChart R.A ψ ∧ ψ.target = C.D ∧ (∀ x, x ∈ ψ.source ↔ R.lift x x ∈ C.O) ∧
        ∀ x ∈ ψ.source, SameOrbit (C.φ (ψ x)) (R.lift x x) := by
  have h' : ∀ x : PtsOf P, ∃ C : OrbitChart P e, x ∈ srcOf C := fun x => hcov _ (rep_mem_mcPts x)
  choose Cx hCx using h'
  haveI : CompactSpace (PtsOf P) := Top.compactSpace_pts (isMultiHomogIdeal_pC hP)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => srcOf (Cx x))
    (fun x _ => (isOpen_srcOf hP _).mem_nhds (hCx x))
  have hc : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y) := fun x => by
    simpa using ht.2 (Set.mem_univ x)
  refine ⟨resOf hP hnd Cx hCx t hc, fun C hne => ?_⟩
  obtain ⟨z, hz⟩ := hne
  have ho : ∀ x : PtsOf P, SameOrbit ((Cx x).φ ((Cx x).ρ (rep x))) (rep x) := fun x => (Cx x).φ_ρ _ (hCx x)
  have hm : ∀ x : PtsOf P, (Cx x).φ ((Cx x).ρ (rep x)) ∈ mcPts P := fun x => (Cx x).mem _ ((Cx x).ρ_mem _ (hCx x))
  refine ⟨orbChart hP C (cls z hz), isCompat_orbChart hP Cx t hc C _, rfl, fun x => ?_, fun x hx => ?_⟩
  · exact ⟨fun h => mem_O_of_orbit C hP h (ho x) (rep_mem_mcPts x),
      fun h => mem_O_of_orbit C hP h (Proj.orbit_symm (ho x)) (hm x)⟩
  · exact Proj.orbit_trans (C.φ_ρ _ hx) (Proj.orbit_symm (ho x))

theorem not_mem_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun h => by
  have := h.2 1 trivial
  simp at this

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n), d = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∀ (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → ∃ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e), ((∀ p, keep p) → e = d) ∧ ∃ pr : R.X → Rb.X, HoloMap R.A Rb.A pr ∧ (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (Rb.lift (pr x) (pr x))) ∧ ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e), IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb hd keep Kk _ ιk _ κ v hb hrng
  obtain ⟨e, he, ⟨ε⟩⟩ : ∃ e, e = n + Nat.card (PIdx j keep) ∧ Nonempty (Fin n ⊕ PIdx j keep ≃ Fin e) :=
    ⟨_, rfl, ⟨(Equiv.sumCongr (Equiv.refl _) (Finite.equivFin _)).trans finSumFinEquiv⟩⟩
  have hP : IsMultiHomogIdeal (mCoordIdeal (y ∘ v)) := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _
  have hnd : ¬ (⊤ : Ideal (MRing ιk)) ≤ mCoordIdeal (y ∘ v) := fun h =>
    (RingHom.ker_isPrime _ : (mCoordIdeal (y ∘ v)).IsPrime).ne_top (top_le_iff.mp h)
  have hcov := GlobalTheory.CompanionTheory.Ar.PB.PFl.Cover.main K ι Φ y Ψ N j M n Rb keep Kk ιk κ v hb hrng
  have mk : ∀ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsPCtx M Rb keep κ v F kb V bl r h →
      ∃ C : OrbitChart (mCoordIdeal (y ∘ v)) e, C.D = pD ε V ∧ C.φ = pPhi M F keep v bl h ε ∧
        C.O = pO M Rb keep v F kb V r h := by
    intro F kb V bl r h hc
    have hV : IsOpen V := hc.2.2.2.1.1
    have hh := GlobalTheory.CompanionTheory.Ar.PB.PFl.Holo.pPhi_holo K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hr := GlobalTheory.CompanionTheory.Ar.PB.PFl.ChartRead.chart_reads K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have ho := GlobalTheory.CompanionTheory.Ar.PB.PFl.Onto.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hO := GlobalTheory.CompanionTheory.Ar.PB.PFl.POpn.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hb' := GlobalTheory.CompanionTheory.Ar.PB.PFl.Orb.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have ht := GlobalTheory.CompanionTheory.Ar.PB.PFl.PCont.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hi := GlobalTheory.CompanionTheory.Ar.PB.PFl.Imm.chart_immersion K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    exact ⟨{ D := pD ε V
             isOpen_D := hV.preimage (continuous_pi fun i => continuous_apply _)
             φ := pPhi M F keep v bl h ε
             holo := hh
             mem := fun w hw => (hr w hw).1.1
             O := pO M Rb keep v F kb V r h
             O_open := hO
             O_orbit := fun z hz z' hz' e => (hb' z hz z' hz' e).1
             ρ := pRho M Rb keep v F kb r h ε
             ρ_cont := ht
             ρ_orbit := fun z hz z' hz' e => (hb' z hz z' hz'.1 e).2
             φ_mem_O := fun w hw => (hr w hw).1
             ρ_φ := fun w hw => (hr w hw).2
             ρ_mem := fun z hz => (ho z hz).1
             φ_ρ := fun z hz => (ho z hz).2
             immersion := hi }, rfl, rfl, rfl⟩
  obtain ⟨R, hR⟩ := exists_res (e := e) hP hnd (fun z hz => by
    obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov z hz
    obtain ⟨C, -, -, hO⟩ := mk F kb V bl r h hc
    exact ⟨C, hO ▸ hzO⟩)

  have key : ∀ x : R.X, ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)),
      IsPCtx M Rb keep κ v F kb V bl r h ∧ IsCompatChart R.A ψ ∧ ψ.target = pD ε V ∧ x ∈ ψ.source ∧
        ∀ x' ∈ ψ.source, SameOrbit (pPhi M F keep v bl h ε (ψ x')) (R.lift x' x') := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov _ (R.mem x x (R.mem_U x))
    obtain ⟨C, hD, hφ, hO⟩ := mk F kb V bl r h hc
    obtain ⟨ψ, h1, h2, h3, h4⟩ := hR C ⟨_, R.mem x x (R.mem_U x)⟩
    exact ⟨F, kb, V, bl, r, h, ψ, hc, h1, h2.trans hD, (h3 x).2 (hO ▸ hzO), fun x' hx' => hφ ▸ h4 x' hx'⟩
  have hob := (GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase.main K ι Φ y Ψ N j M keep Kk ιk κ v hb hrng).2

  have hbase : ∀ x : R.X, ∃ x' : Rb.X, SameOrbit (Rb.lift x' x') (pBase M v (R.lift x x)) := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, -, hT, hx, hs⟩ := key x
    have hB : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
    have hw : ψ x ∈ pD ε V := hT ▸ ψ.map_source hx
    have hE := GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact.chart_points K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc _ hw
    refine ⟨(Rb.A.chart kb).symm (pB ε (ψ x)), orbit_trans (hB.2.2.2.2 _ hw).2.2.2 ?_⟩
    have := hob _ _ (hs x hx)
    rwa [hE.2.1] at this
  choose pr hpr using hbase
  have hcoord : ∀ (x : R.X) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)),
      IsPCtx M Rb keep κ v F kb V bl r h → ψ.target = pD ε V → x ∈ ψ.source →
      SameOrbit (pPhi M F keep v bl h ε (ψ x)) (R.lift x x) →
      pr x = (Rb.A.chart kb).symm (pB ε (ψ x)) ∧ pr x ∈ (Rb.A.chart kb).source ∧
        ∀ i, Rb.A.chart kb (pr x) i = ψ x (ε (Sum.inl i)) := by
    intro x F kb V bl r h ψ hc hT hx hs
    have hB : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
    have hw : ψ x ∈ pD ε V := hT ▸ ψ.map_source hx
    have hE := GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact.chart_points K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc _ hw
    have h1 : SameOrbit (bl (pB ε (ψ x))) (pBase M v (R.lift x x)) := by
      have := hob _ _ hs
      rwa [hE.2.1] at this
    have h2 := orbit_trans (hB.2.2.2.2 _ hw).2.2.2 (orbit_trans h1 (orbit_symm (hpr x)))
    have h3 : (Rb.A.chart kb).symm (pB ε (ψ x)) = pr x := Rb.inj _ _ (not_mem_top _) h2
    have hwt : pB ε (ψ x) ∈ (Rb.A.chart kb).target := hB.2.1 hw
    rw [← h3]
    exact ⟨rfl, (Rb.A.chart kb).map_target hwt, fun i => by
      rw [(Rb.A.chart kb).right_inv hwt]
      rfl⟩
  have hlast : ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e),
      IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧
        ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, hψ, hT, hx, hs⟩ := key x
    refine ⟨ψ, kb, ⟨fun i => ε (Sum.inl i), fun a b e' => Sum.inl_injective (ε.injective e')⟩, hψ, hx, fun x' hx' => ?_⟩
    obtain ⟨-, h1, h2⟩ := hcoord x' F kb V bl r h ψ hc hT hx' (hs x' hx')
    exact ⟨h1, h2⟩
  refine ⟨e, R, ?_, pr, ?_, ?_, hlast⟩
  · intro hall
    rw [he, GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept.card_pIdx_of_all Ψ N j keep M.j_le hall, hd]
  · refine GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord.holoMap_of_coord e n R.X Rb.X R.A Rb.A pr fun x => ?_
    obtain ⟨ψ, kb, σ, h1, h2, h3⟩ := hlast x
    exact ⟨ψ, kb, σ, h1, h2, h3⟩
  · intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, -, hT, hx, hs⟩ := key x
    have hB : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
    have hw : ψ x ∈ pD ε V := hT ▸ ψ.map_source hx
    obtain ⟨z₀, hz₀, hzv, hzb⟩ := GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc _ hw
    obtain ⟨hpe, -, -⟩ := hcoord x F kb V bl r h ψ hc hT hx (hs x hx)
    obtain ⟨c, hc0, hce⟩ := orbit_symm (hs x hx)
    let c' : K → ℂ := fun k => if hk : ∃ k', κ k' = k then c hk.choose else 1
    have hc'0 : ∀ k, c' k ≠ 0 := fun k => by
      simp only [c']
      split_ifs
      · exact hc0 _
      · exact one_ne_zero
    have hc'κ : ∀ k', c' (κ k') = c k' := fun k' => by
      have hk : ∃ k'', κ k'' = κ k' := ⟨k', rfl⟩
      simp only [c']
      rw [dite_eq_left hk, hb.1 hk.choose_spec]
    have hyP : IsMultiHomogIdeal (mCoordIdeal y) := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _
    refine ⟨fun p => c' p.1 * z₀ p, mcPts_smul hyP c' hc'0 hz₀, ?_, ?_⟩
    · funext q
      have e1 : z₀ (v q) = pPhi M F keep v bl h ε (ψ x) q := congrFun hzv q
      have e2 := congrFun hce q
      show c' (v q).1 * z₀ (v q) = _
      rw [e2, e1, hb.2.2.1 q, hc'κ]
    · have h1 : SameOrbit (fun q => c' q.1.1 * basePart M.blk z₀ q) (bl (pB ε (ψ x))) := by
        rw [hzb]
        exact ⟨fun k => c' k.1, fun k => hc'0 _, rfl⟩
      have h2 : (basePart M.blk fun p => c' p.1 * z₀ p) = fun q => c' q.1.1 * basePart M.blk z₀ q := rfl
      rw [h2, hpe]
      exact orbit_trans h1 (orbit_symm (hB.2.2.2.2 _ hw).2.2.2)

end GlobalTheory.CompanionTheory.Ar.PB.PFl
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagBundlePartialBlockMapStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_partial_block_map : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n), d = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∀ (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → ∃ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e), ((∀ p, keep p) → e = d) ∧ ∃ pr : R.X → Rb.X, HoloMap R.A Rb.A pr ∧ (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (Rb.lift (pr x) (pr x))) ∧ ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e), IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.main | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameDeterminesLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameDeterminesLattice
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ}

namespace LatEmb

variable (C : LatEmb F)

theorem perExt_eq_sum (R : RiemLat E g Λ) (y : Ψ → Fin (j + j') → ℂ) :
    C.perExt R y = ∑ k, C.bas.repr y k • R.P (C.lam k) := by
  simp [perExt, Module.Basis.constr_apply_fintype]


omit [IsCMField E] in
theorem form_antisymm {M : Type} [AddCommGroup M] (f : M →ₗ[ℤ] M →ₗ[ℤ] ℤ) (hf : ∀ x, f x x = 0) (x y : M) :
    f x y = - f y x := by
  have h := hf (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, hf] at h
  linarith

theorem exists_dual (R : RiemLat E g Λ) (i : Fin (2 * g)) :
    ∃ z : Λ, ∀ k, R.form (C.lam k) z = if k = i then 1 else 0 := by
  obtain ⟨x, hx⟩ := R.unimod.2 (C.lam.coord i)
  refine ⟨-x, fun k => ?_⟩
  rw [map_neg, form_antisymm R.form R.alt, neg_neg, hx]
  simp [Module.Basis.coord_apply, Finsupp.single_apply]

theorem perExt_injective (R : RiemLat E g Λ) : Function.Injective (C.perExt R) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  have hc : ∀ i, C.bas.repr y i = 0 := by
    intro i
    obtain ⟨z, hz⟩ := C.exists_dual R i
    have h0 : ((C.perExt R y) ⬝ᵥ R.Hm *ᵥ star (R.P z)).im = 0 := by simp [hy]
    have hk : ∀ k, ((C.bas.repr y k • R.P (C.lam k)) ⬝ᵥ R.Hm *ᵥ star (R.P z)).im =
        C.bas.repr y k * (R.form (C.lam k) z : ℝ) := by
      intro k
      rw [smul_dotProduct, Complex.smul_im, R.im]
      simp
    rw [C.perExt_eq_sum, sum_dotProduct, Complex.im_sum] at h0
    simp only [hk, hz] at h0
    simpa using h0
  apply C.bas.repr.injective
  ext i
  simpa using hc i

theorem perExt_bijective (R : RiemLat E g Λ) : Function.Bijective (C.perExt R) := by
  have hd : Module.finrank ℝ (Ψ → Fin (j + j') → ℂ) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Module.finrank_eq_card_basis C.bas]
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  exact ⟨C.perExt_injective R, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).1 (C.perExt_injective R)⟩

def latPt (x : Λ) : Ψ → Fin (j + j') → ℂ := ∑ k, ((C.lam.repr x k : ℤ) : ℝ) • C.bas k

theorem perExt_latPt (R : RiemLat E g Λ) (x : Λ) : C.perExt R (C.latPt x) = R.P x := by
  have hb : ∀ k, C.perExt R (C.bas k) = R.P (C.lam k) := fun k => by
    simp [perExt, Module.Basis.constr_basis]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← C.lam.sum_repr x, map_sum]
  unfold latPt
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, hb, Int.cast_smul_eq_zsmul, map_zsmul]


omit [NumberField E] in
theorem sgI_mul_self : sgI j j' * sgI j j' = 1 := by
  simp [sgI, fromBlocks_multiply]

theorem cinv_mul {M : Matrix (Fin (j + j')) (Sg j j') ℂ} {τ : Ψ} (hu : Mᴴ * C.sgr τ * M = sgI j j') :
    C.cinv M τ * M = 1 := by
  unfold cinv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hu, sgI_mul_self]

theorem mul_cinv {M : Matrix (Fin (j + j')) (Sg j j') ℂ} {τ : Ψ} (hu : Mᴴ * C.sgr τ * M = sgI j j') :
    M * C.cinv M τ = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 (C.cinv_mul hu)

def aPart (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (y : Ψ → Fin (j + j') → ℂ) (τ : Ψ) : Fin (j + j') → ℂ :=
  A τ *ᵥ Sum.elim (fun i => (C.cinv (A τ) τ *ᵥ y τ) (Sum.inl i)) 0

def bPart (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (y : Ψ → Fin (j + j') → ℂ) (τ : Ψ) : Fin (j + j') → ℂ :=
  A τ *ᵥ Sum.elim 0 (fun i => (C.cinv (A τ) τ *ᵥ y τ) (Sum.inr i))

theorem aPart_add_bPart {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ}
    (hu : ∀ τ, (A τ)ᴴ * C.sgr τ * A τ = sgI j j') (y : Ψ → Fin (j + j') → ℂ) (τ : Ψ) :
    C.aPart A y τ + C.bPart A y τ = y τ := by
  unfold aPart bPart
  rw [← mulVec_add]
  have h : (Sum.elim (fun i => (C.cinv (A τ) τ *ᵥ y τ) (Sum.inl i)) (0 : Fin j' → ℂ) +
      Sum.elim (0 : Fin j → ℂ) (fun i => (C.cinv (A τ) τ *ᵥ y τ) (Sum.inr i)) : Sg j j' → ℂ) =
      C.cinv (A τ) τ *ᵥ y τ := by
    ext (i | i) <;> simp
  rw [h, mulVec_mulVec, C.mul_cinv (hu τ), one_mulVec]

def cxStr (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (y : Ψ → Fin (j + j') → ℂ) (τ : Ψ) : Fin (j + j') → ℂ :=
  (-Complex.I) • C.aPart A y τ + Complex.I • C.bPart A y τ


open Classical in
theorem perExt_single_I_of_pPart (R : RiemLat E g Λ) (τ : Ψ) (w : Fin (j + j') → ℂ) (h : C.pPart R τ w = 0) :
    C.perExt R (Pi.single τ (Complex.I • w)) = (-Complex.I) • C.perExt R (Pi.single τ w) := by
  have h2 := (smul_eq_zero.1 h).resolve_left (by norm_num)
  rw [sub_eq_zero.1 h2, smul_smul]
  simp


open Classical in
theorem perExt_single_I_of_pBar (R : RiemLat E g Λ) (τ : Ψ) (w : Fin (j + j') → ℂ) (h : C.pBar R τ w = 0) :
    C.perExt R (Pi.single τ (Complex.I • w)) = Complex.I • C.perExt R (Pi.single τ w) := by
  have h2 := (smul_eq_zero.1 h).resolve_left (by norm_num)
  rw [eq_neg_of_add_eq_zero_left h2, smul_neg, smul_smul]
  simp


open Classical in
theorem perExt_single_cxStr {R : RiemLat E g Λ} {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : C.IsAdapted R A)
    (y : Ψ → Fin (j + j') → ℂ) (τ : Ψ) :
    C.perExt R (Pi.single τ (C.cxStr A y τ)) = Complex.I • C.perExt R (Pi.single τ (y τ)) := by
  have ha := C.perExt_single_I_of_pPart R τ (C.aPart A y τ) (hA.ker τ _)
  have hb := C.perExt_single_I_of_pBar R τ (C.bPart A y τ) (hA.kerBar τ _)
  have hy : C.perExt R (Pi.single τ (y τ)) =
      C.perExt R (Pi.single τ (C.aPart A y τ)) + C.perExt R (Pi.single τ (C.bPart A y τ)) := by
    rw [← map_add (f := _), ← Pi.single_add, C.aPart_add_bPart hA.unit]
  unfold cxStr
  rw [neg_smul, Pi.single_add, map_add (f := _), Pi.single_neg, map_neg, ha, hb, hy, smul_add]
  simp


open Classical in
theorem perExt_eq_sum_single (R : RiemLat E g Λ) (y : Ψ → Fin (j + j') → ℂ) :
    C.perExt R y = ∑ τ, C.perExt R (Pi.single τ (y τ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, Finset.univ_sum_single]

theorem perExt_cxStr {R : RiemLat E g Λ} {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : C.IsAdapted R A)
    (y : Ψ → Fin (j + j') → ℂ) : C.perExt R (C.cxStr A y) = Complex.I • C.perExt R y := by
  classical
  rw [C.perExt_eq_sum_single R (C.cxStr A y), C.perExt_eq_sum_single R y, Finset.smul_sum]
  exact Finset.sum_congr rfl fun τ _ => C.perExt_single_cxStr hA y τ

theorem eqvBy_of_adapted (R R' : RiemLat E g Λ) {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ}
    (hA : C.IsAdapted R A) (hA' : C.IsAdapted R' A) : R.EqvBy R' 1 := by
  let eL := LinearEquiv.ofBijective (C.perExt R) (C.perExt_bijective R)
  let eL' := LinearEquiv.ofBijective (C.perExt R') (C.perExt_bijective R')
  let φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := eL.symm.trans eL'
  have hφL : ∀ y, φ (C.perExt R y) = C.perExt R' y := by
    intro y
    have h : eL.symm (C.perExt R y) = y := eL.symm_apply_apply y
    show eL' (eL.symm (C.perExt R y)) = _
    rw [h]
    rfl
  have hI : ∀ z, φ (Complex.I • z) = Complex.I • φ z := by
    intro z
    obtain ⟨y, rfl⟩ := (C.perExt_bijective R).2 z
    rw [← C.perExt_cxStr hA, hφL, hφL, C.perExt_cxStr hA']
  have hz : ∀ (c : ℂ) (w : Fin g → ℂ), c • w = c.re • w + c.im • (Complex.I • w) := by
    intro c w
    ext k
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  have hs : ∀ (c : ℂ) z, φ (c • z) = c • φ z := by
    intro c z
    rw [hz c z, map_add (f := _), map_smul, map_smul, hI, ← hz]
  refine ⟨{ toFun := φ, invFun := φ.symm, left_inv := φ.left_inv, right_inv := φ.right_inv,
            map_add' := φ.map_add, map_smul' := hs }, fun x => ?_⟩
  show R'.P x = φ (R.P x)
  rw [← C.perExt_latPt R x, hφL, C.perExt_latPt]

end LatEmb

theorem adapted_eqvBy (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ)
    (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R R' : RiemLat E g Λ)
    (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (_ : R.form = F.form) (_ : R'.form = F.form)
    (hA : C.IsAdapted R A) (hA' : C.IsAdapted R' A) : R.EqvBy R' 1 :=
  C.eqvBy_of_adapted R R' hA hA'

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameDeterminesLatticeStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frame_determines_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R R' : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), R.form = F.form → R'.form = F.form → C.IsAdapted R A → C.IsAdapted R' A → R.EqvBy R' 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.adapted_eqvBy | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.adapted_eqvBy | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.adapted_eqvBy <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SkewHermitianFormExists
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SkewHermitianFormExists
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.HermTrace

section Field

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem quadConj_eq_complexConj (x : E) :
    conj (maximalRealSubfield E) E x = IsCMField.complexConj E x := by
  set K := maximalRealSubfield E
  set t := IsCMField.complexConj E
  set y := conj K E x with hy
  have hyy : conj K E y = x := conj_conj x
  have fix : ∀ a : E, conj K E a = a → t a = a := by
    intro a ha
    obtain ⟨b, rfl⟩ := conj_eq_self_iff.1 ha
    exact (IsCMField.complexConj_eq_self_iff E _).2 b.2
  have ha : t (x + y) = x + y := fix _ (by rw [map_add (f := _), hyy, ← hy, add_comm])
  have hb : t (x * y) = x * y := fix _ (by rw [map_mul, hyy, ← hy, mul_comm])
  have hz : (t x - x) * (t x - y) = 0 := by
    have h0 : x * x - (x + y) * x + x * y = 0 := by ring
    have h1 := congrArg t h0
    rw [map_add (f := _), map_sub, map_mul, map_mul, ha, hb, map_zero] at h1
    linear_combination h1
  rcases mul_eq_zero.1 hz with h | h
  · have hx : t x = x := sub_eq_zero.1 h
    have : x ∈ K := (IsCMField.complexConj_eq_self_iff E x).1 hx
    have h2 : y = x := conj_eq_self_iff.2 ⟨⟨x, this⟩, rfl⟩
    rw [h2, hx]
  · exact (sub_eq_zero.1 h).symm

theorem complexConj_rt (H : Host E) : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h2 : (IsCMField.complexConj E (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
    rw [← map_pow, hsq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
  · exfalso
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hc : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
      rw [← IsCMField.complexEmbedding_complexConj E φ, h]
    obtain ⟨s, hs⟩ := Complex.conj_eq_iff_real.1 hc
    have h3 := congrArg φ hsq
    rw [map_pow, map_neg, map_natCast, hs] at h3
    have h4 : (s ^ 2 : ℝ) = -(H.d : ℝ) := by exact_mod_cast h3
    nlinarith [sq_nonneg s]
  · exact h

theorem sesq_skew {V : Type} [AddCommGroup V] [Module E V] [Module ℚ V]
    (B : LinearMap.BilinForm ℚ V)
    (hadj : ∀ (a : E) x y, B (a • x) y = B x (IsCMField.complexConj E a • y))
    (hskew : ∀ u v, B u v = - B v u) (h₁ : V → V → E)
    (htr : ∀ x y (a : E), Algebra.trace ℚ E (a * h₁ x y) = B (a • x) y) (u v : V) :
    h₁ v u = - IsCMField.complexConj E (h₁ u v) := by
  have nd := traceForm_nondegenerate ℚ E
  have htc : ∀ z : E, Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z := fun z =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z
  have : h₁ v u - (- IsCMField.complexConj E (h₁ u v)) = 0 := by
    apply nd.1
    intro a
    have e1 : Algebra.trace ℚ E (a * IsCMField.complexConj E (h₁ u v)) =
        Algebra.trace ℚ E (IsCMField.complexConj E a * h₁ u v) := by
      rw [← htc, map_mul, IsCMField.complexConj_apply_apply]
    have e2 : B u (a • v) = B (IsCMField.complexConj E a • u) v := by
      rw [hadj, IsCMField.complexConj_apply_apply]
    rw [Algebra.traceForm_apply, mul_comm, mul_sub, map_sub, mul_neg, map_neg, e1, htr, htr,
      hskew (a • v) u, e2]
    ring
  linear_combination this


omit [IsCMField E] in
theorem exists_nat_integral {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ] (F : Λ → Λ → E)
    (h1 : ∀ x x' y, F (x + x') y = F x y + F x' y) (h2 : ∀ x y y', F x (y + y') = F x y + F x y') :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ x y, (m : E) * F x y ∈ integralClosure ℤ E := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Λ)
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E)
    (Finset.univ.image fun p : Fin n × Fin n => F (s p.1) (s p.2))
  have step : ∀ g : Λ →+ E, (∀ i, g (s i) ∈ integralClosure ℤ E) →
      ∀ x, g x ∈ integralClosure ℤ E := by
    intro g hg x
    have hx : x ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨i, rfl⟩ := h
      exact hg i
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [map_zsmul]
      exact zsmul_mem hx a
  have core : ∀ m : ℕ, (∀ i k, (m : E) * F (s i) (s k) ∈ integralClosure ℤ E) →
      ∀ x y, (m : E) * F x y ∈ integralClosure ℤ E := by
    intro m hm x y
    let gy : Λ → Λ →+ E := fun x => AddMonoidHom.mk' (fun y => (m : E) * F x y)
      (fun a b => by rw [h2, mul_add])
    let gx : Λ → Λ →+ E := fun y => AddMonoidHom.mk' (fun x => (m : E) * F x y)
      (fun a b => by rw [h1, mul_add])
    exact step (gy x) (fun k => step (gx (s k)) (fun i => hm i k) x) y
  have hint : ∀ i k, IsIntegral ℤ (y • F (s i) (s k)) := fun i k =>
    hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, k)))
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨m, by simpa using hy0, core m fun i k => ?_⟩
    have := hint i k
    rwa [zsmul_eq_mul, Int.cast_natCast] at this
  · refine ⟨m, by simpa using hy0, core m fun i k => ?_⟩
    have := (hint i k).neg
    rwa [zsmul_eq_mul, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg] at this

end Field

theorem exists_hermitian_of_trace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] (N : ℕ) (e : Λ →+ (Fin N → E)) (B : LinearMap.BilinForm ℚ (Fin N → E)), (∀ (a : E) u v, B (a • u) v = B u (IsCMField.complexConj E a • v)) → (∀ u v, B u v = - B v u) → (∀ u, (∀ v, B v u = 0) → u = 0) → ∃ (h : HermitianForm (maximalRealSubfield E) E (Fin N → E)) (m : ℕ), m ≠ 0 ∧ (∀ (a : E) u v, Algebra.trace ℚ E (a * (((m : E) * (H.rt : E))⁻¹ * h.toSesq v u)) = B (a • u) v) ∧ ∀ x y, h.toSesq (e x) (e y) ∈ integralClosure ℤ E := by
  intro E _ _ _ H Λ _ _ N e B hadj hskew hnd
  obtain ⟨h₁, ⟨htr, hadd1, hadd2, hsm1, hsm2⟩, -⟩ :=
    GlobalTheory.CompanionTheory.Ar.Flat.existsUnique_sesq_of_trace E (Fin N → E) B hadj
  have hsk := sesq_skew B hadj hskew h₁ htr
  obtain ⟨m, hm0, hint⟩ := exists_nat_integral (fun x y : Λ => h₁ (e y) (e x))
    (fun x x' y => by rw [map_add (f := _), hadd2]) (fun x y y' => by rw [map_add (f := _), hadd1])
  have hrt0 : (H.rt : E) ≠ 0 := by
    intro h0
    have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [h0] at hsq
    have hd : (H.d : E) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
    apply hd
    linear_combination hsq
  set c : E := (m : E) * (H.rt : E) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 hm0) hrt0
  have htc : IsCMField.complexConj E c = -c := by
    rw [hc, map_mul, map_natCast, complexConj_rt]
    ring
  let S : (Fin N → E) →ₛₗ[conjHom (maximalRealSubfield E) E] (Fin N → E) →ₗ[E] E :=
    LinearMap.mk₂'ₛₗ (conjHom (maximalRealSubfield E) E) (RingHom.id E) (fun v u => c * h₁ u v)
      (fun v v' u => by rw [hadd2, mul_add])
      (fun a v u => by
        rw [hsm2, smul_eq_mul]
        have : conjHom (maximalRealSubfield E) E a = IsCMField.complexConj E a :=
          quadConj_eq_complexConj a
        rw [this]
        ring)
      (fun v u u' => by rw [hadd1, mul_add])
      (fun a v u => by
        rw [hsm1, RingHom.id_apply, smul_eq_mul]
        ring)
  have Sapp : ∀ v u, S v u = c * h₁ u v := fun _ _ => rfl
  have hinj : Function.Injective S := by
    intro v v' hvv
    have hz : ∀ w, h₁ w (v - v') = 0 := by
      intro w
      have h3 : c * h₁ w v = c * h₁ w v' := by
        rw [← Sapp, ← Sapp, hvv]
      have h4 := mul_left_cancel₀ hc0 h3
      have h5 := hadd2 w (v - v') v'
      rw [sub_add_cancel, h4] at h5
      linear_combination -h5
    have : v - v' = 0 := hnd _ fun w => by
      have h6 := htr w (v - v') 1
      rw [one_smul, hz, mul_zero, map_zero] at h6
      exact h6.symm
    exact sub_eq_zero.1 this
  have hsurj : Function.Surjective S := by
    let g0 : (Fin N → E) →+ (Fin N → E) := AddMonoidHom.mk' (fun u i => S u (Pi.single i 1))
      (fun a b => by
        funext i
        show S (a + b) (Pi.single i 1) = S a (Pi.single i 1) + S b (Pi.single i 1)
        rw [Sapp, Sapp, Sapp, hadd2, mul_add])
    let g : (Fin N → E) →ₗ[ℚ] (Fin N → E) := g0.toRatLinearMap
    have gapp : ∀ u i, g u i = S u (Pi.single i 1) := fun _ _ => rfl
    have ginj : Function.Injective g := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro u hu
      have : S u = S 0 := by
        apply (Pi.basisFun E (Fin N)).ext
        intro i
        rw [Pi.basisFun_apply, map_zero, ← gapp, hu]
        rfl
      exact hinj (this.trans (by rw [map_zero]) |>.trans (map_zero S).symm)
    have gsurj : Function.Surjective g := LinearMap.injective_iff_surjective.1 ginj
    intro f
    obtain ⟨u, hu⟩ := gsurj fun i => f (Pi.single i 1)
    refine ⟨u, (Pi.basisFun E (Fin N)).ext fun i => ?_⟩
    rw [Pi.basisFun_apply, ← gapp, hu]
  refine ⟨⟨S, ⟨fun x y => ?_⟩, hinj, hsurj⟩, m, hm0, ?_, ?_⟩
  · have h7 : conjHom (maximalRealSubfield E) E (S x y) = IsCMField.complexConj E (S x y) :=
      quadConj_eq_complexConj _
    rw [h7, Sapp, Sapp, map_mul, htc, hsk y x]
    ring
  · intro a u v
    have h8 : ((m : E) * (H.rt : E))⁻¹ * S v u = h₁ u v := by
      rw [Sapp, ← hc, inv_mul_cancel_left₀ hc0]
    show Algebra.trace ℚ E (a * (((m : E) * (H.rt : E))⁻¹ * S v u)) = _
    rw [h8, htr]
  · intro x y
    show S (e x) (e y) ∈ integralClosure ℤ E
    rw [Sapp, hc]
    have h9 : (H.rt : E) ∈ integralClosure ℤ E := (H.rt).isIntegral_coe
    have h10 := mul_mem h9 (hint x y)
    convert h10 using 1
    ring

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.HermTrace
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SkewHermitianFormExistsStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_hermitian_form_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] (N : ℕ) (e : Λ →+ (Fin N → E)) (B : LinearMap.BilinForm ℚ (Fin N → E)), (∀ (a : E) u v, B (a • u) v = B u (IsCMField.complexConj E a • v)) → (∀ u v, B u v = - B v u) → (∀ u, (∀ v, B v u = 0) → u = 0) → ∃ (h : HermitianForm (maximalRealSubfield E) E (Fin N → E)) (m : ℕ), m ≠ 0 ∧ (∀ (a : E) u v, Algebra.trace ℚ E (a * (((m : E) * (H.rt : E))⁻¹ * h.toSesq v u)) = B (a • u) v) ∧ ∀ x y, h.toSesq (e x) (e y) ∈ integralClosure ℤ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.HermTrace.exists_hermitian_of_trace | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.HermTrace.exists_hermitian_of_trace | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.HermTrace.exists_hermitian_of_trace <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateEmbeddingsCriterion
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateEmbeddingsCriterion
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj

theorem not_eq_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ]
    {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) (τ τ' : Ψ) (h : ∀ a : 𝓞 E, σ τ a = star (σ τ' a)) : False := by
  have h1 : σ τ = (starRingEnd ℂ).comp (σ τ') := RingHom.ext h
  exact ((hσ.2 (σ τ')).1 ⟨τ', rfl⟩) ⟨τ, h1⟩

theorem emb_eq_star_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' : ℕ}
    (σ : Ψ → (𝓞 E →+* ℂ)) (hσ : IsCMFam σ) (i k : Ix Ψ j j') :
    (∀ a : 𝓞 E, emb σ i a = star (emb σ k a)) ↔ (i.2 = k.2 ∧ i.1.isLeft ≠ k.1.isLeft) := by
  obtain ⟨s, τ⟩ := i
  obtain ⟨t, τ'⟩ := k
  cases s with
  | inl s =>
    cases t with
    | inl t =>
      simp only [emb, Sum.elim_inl, Sum.isLeft_inl, ne_eq, not_true_eq_false, and_false, iff_false]
      intro h
      exact not_eq_conj hσ τ τ' h
    | inr t =>
      simp only [emb, Sum.elim_inl, Sum.elim_inr, Sum.isLeft_inl, Sum.isLeft_inr, RingHom.comp_apply,
        starRingEnd_apply, star_star, ne_eq, Bool.true_eq_false, not_false_eq_true, and_true]
      constructor
      · intro h
        exact hσ.1 (RingHom.ext h)
      · rintro rfl a
        rfl
  | inr s =>
    cases t with
    | inl t =>
      simp only [emb, Sum.elim_inl, Sum.elim_inr, Sum.isLeft_inl, Sum.isLeft_inr, RingHom.comp_apply,
        starRingEnd_apply, ne_eq, Bool.false_eq_true, not_false_eq_true, and_true]
      constructor
      · intro h
        exact hσ.1 (RingHom.ext fun a => star_injective (h a))
      · rintro rfl a
        rfl
    | inr t =>
      simp only [emb, Sum.elim_inr, Sum.isLeft_inr, RingHom.comp_apply, starRingEnd_apply, star_star,
        ne_eq, not_true_eq_false, and_false, iff_false]
      intro h
      exact not_eq_conj hσ τ' τ fun a => (h a).symm

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateEmbeddingsCriterionStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_embeddings_criterion : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → ∀ i k : Ix Ψ j j', (∀ a : 𝓞 E, emb σ i a = star (emb σ k a)) ↔ (i.2 = k.2 ∧ i.1.isLeft ≠ k.1.isLeft) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj.emb_eq_star_iff | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj.emb_eq_star_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj.emb_eq_star_iff <;> assumption)
end
end
