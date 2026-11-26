module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRegAboveWeight
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagRatioFieldEq
section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ObjectsTied
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def GenLeadMinor0NeZero.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (τ : Ψ) (a : Fin (n - 1)), leadMinor (genMat0Fr F Ψ n j τ) a ≠ 0

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagSpan
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def HodgeFlagSpan.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D)
    (B : AdaptedBasis H) (τ : Ψ) (i : Fin (D.N - 1)),
    Submodule.span Ω (Set.range (Pl.pluecker0 B τ i)) =
      Submodule.span Ω (Set.range (flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.GenMat0FrEqMap
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem genMat0Fr_eq_map (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (τ : Ψ) :
    genMat0Fr F Ψ n j τ = (algebraMap (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n)).mapMatrix
      (Matrix.of fun (p q : Fin n) => if (p : ℕ) < j ∧ j ≤ (q : ℕ) then 0 else
        (X (τ, p, q) : MvPolynomial (Ψ × Fin n × Fin n) F)) := by
  ext p q
  simp only [genMat0Fr, genMatFr, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem GenLeadMinor0NeZero.full : GenLeadMinor0NeZero.Statement := by
  intro F _ Ψ n j τ a
  rw [genMat0Fr_eq_map, ← leadMinor_map]
  refine (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n))).2 ?_
  intro h0
  have h1 := congrArg (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)) h0
  rw [leadMinor_map, map_zero] at h1
  have hP : (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)).mapMatrix
      (Matrix.of fun (p q : Fin n) => if (p : ℕ) < j ∧ j ≤ (q : ℕ) then 0 else
        (X (τ, p, q) : MvPolynomial (Ψ × Fin n × Fin n) F)) = 1 := by
    ext p q
    by_cases hc : (p : ℕ) < j ∧ j ≤ (q : ℕ)
    · have hpq : p ≠ q := by
        rintro rfl
        obtain ⟨hc₁, hc₂⟩ := hc
        omega
      simp [hc, hpq]
    · simp [hc, Matrix.one_apply]
  rw [hP, leadMinor_one] at h1
  exact one_ne_zero h1

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagSpan
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem HodgeFlagSpan.full : HodgeFlagSpan.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B τ i
  classical
  let Be : Module.Basis (Fin D.N) Ω (E τ) := Module.Basis.mk (B.e_indep τ) (B.e_span τ).ge
  have hcoe : ⇑Be = B.e τ := Module.Basis.coe_mk _ _

  have hgen : Submodule.span Ω (Set.range (Pl.gen τ i)) = ⊤ := by
    choose cX hcX using D.arith.2.1.2.2
    have hy : ∀ k, D.y ⟨k, cX k⟩ ≠ 0 := by
      intro k h0
      apply hcX k
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]
    have hseg : segreCoord D.y cX ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
    obtain ⟨M, f, cc, -, -, hsum, hPr⟩ := Pl.generates τ i cX hseg
    have hM : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h | h
      · subst h
        simp at hsum
      · exact h
    obtain ⟨b, -, hspan, hA⟩ := hPr ⟨0, hM⟩
    have hli : LinearIndependent Ω b :=
      linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge
        (by rw [Module.finrank_eq_card_basis Be])
    let Bb : Module.Basis (Fin D.N) Ω (E τ) := Module.Basis.mk hli hspan.ge
    have hBb : ⇑Bb = b := Module.Basis.coe_mk _ _
    refine PlueckerSpan.span_eq_top_of_dual Bb (Pl.gen τ i) fun A hA0 => ?_
    obtain ⟨a, -, ha⟩ := hA A hA0
    refine ⟨fun m => a m * chartMono D.y cX (-Pl.bdeg τ i), fun A' hA' => ?_⟩
    rw [← ha A' hA', hBb]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring

  let P : Module.Dual Ω (⋀[Ω]^((i : ℕ) + 1) (E τ)) →ₗ[Ω] Pl.ΩY :=
    { toFun := fun φ => ∑ c : Fin ((i : ℕ) + 1) → Fin D.N,
        (∏ a, Pl.gvar0 τ (headIdx (step_le i) a) (c a)) *
          algebraMap Ω Pl.ΩY (φ (exteriorPower.ιMulti Ω _ (B.e τ ∘ c)))
      map_add' := fun φ ψ => by
        simp only [LinearMap.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
      map_smul' := fun x φ => by
        simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring }
  have hPpl : ∀ m, P (Pl.gen τ i m) = Pl.pluecker0 B τ i m := by
    intro m
    simp only [P, LinearMap.coe_mk, AddHom.coe_mk, PlueckerData.pluecker0, PlueckerData.ofΩ_eq]

  have hPexp : ∀ φ, P φ = ∑ T : Set.powersetCard (Fin D.N) ((i : ℕ) + 1),
      algebraMap Ω Pl.ΩY (φ (Be.exteriorPower _ T)) *
        flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i ⟨(T : Finset (Fin D.N)), Set.powersetCard.card_eq T⟩ := by
    intro φ
    have h := PlueckerSpan.sum_prod_mul_apply_eq (R := Pl.ΩY) Be
      (Matrix.of fun a b => Pl.gvar0 τ (headIdx (step_le i) a) b) φ
    rw [hcoe] at h
    exact h.trans (Finset.sum_congr rfl fun T _ => rfl)

  have hrange : LinearMap.range P =
      Submodule.span Ω (Set.range (flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i)) := by
    apply le_antisymm
    · rintro _ ⟨φ, rfl⟩
      rw [hPexp]
      refine Submodule.sum_mem _ fun T _ => ?_
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨S, rfl⟩
      let T : Set.powersetCard (Fin D.N) ((i : ℕ) + 1) := ⟨S.1, Set.powersetCard.mem_iff.2 S.2⟩
      refine ⟨(Be.exteriorPower _).coord T, ?_⟩
      rw [hPexp, Finset.sum_eq_single T]
      · rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, map_one, one_mul]
      · intro T' _ hT'
        rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne (Ne.symm hT'),
          map_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ T) h

  have hpl : Set.range (Pl.pluecker0 B τ i) = P '' Set.range (Pl.gen τ i) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun m => (hPpl m).symm)
  rw [hpl, ← Submodule.map_span, hgen, Submodule.map_top, hrange]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem HodgeFlagRatioFieldEq.proof (h₁ : RatioFieldSpan.Statement) (h₂ : HodgeFlagSpan.Statement)
    (h₃ : PivotMinorFlag.Statement) (h₄ : GenLeadMinor0NeZero.Statement) : HodgeFlagRatioFieldEq.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B c hc

  have hq : ∀ (τ : Ψ) (i : Fin (D.N - 1)),
      IntermediateField.adjoin Ω (Set.range fun m =>
          Pl.pluecker0 B τ i m / Pl.pluecker0 B τ i (c (Sum.inr (τ, i)))) =
        IntermediateField.adjoin Ω (Set.range fun S : PluckerBlocks D.N D.N i =>
          flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i S / leadMinor (genMat0Fr Ω Ψ D.N D.j τ) i) := by
    intro τ i
    have hspan := h₂ II Ψ K ι Ω E D Pl H B τ i
    obtain ⟨S₀, hS₀⟩ := h₃ _ D.N (genMat0Fr Ω Ψ D.N D.j τ) i (Fin.castLE (Nat.sub_le D.N 1) i) le_rfl
    refine h₁ Ω Pl.ΩY _ _ _ _ _ _ hspan (Submodule.subset_span ⟨_, rfl⟩) ?_ (hc (Sum.inr (τ, i)))
      (h₄ Ω Ψ D.N D.j τ i)
    rw [hspan]
    exact Submodule.subset_span ⟨S₀, by rw [leadMinor, hS₀]⟩
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k | q, t⟩, rfl⟩
    · show Pl.ofΩ (D.y ⟨k, t⟩) / Pl.ofΩ (D.y ⟨k, c (Sum.inl k)⟩) ∈ _
      rw [PlueckerData.ofΩ_eq, PlueckerData.ofΩ_eq, ← map_div₀]
      exact IntermediateField.algebraMap_mem _ _
    · have hmem : Pl.pluecker0 B q.1 q.2 t / Pl.pluecker0 B q.1 q.2 (c (Sum.inr (q.1, q.2))) ∈
          IntermediateField.adjoin Ω (Set.range fun m =>
            Pl.pluecker0 B q.1 q.2 m / Pl.pluecker0 B q.1 q.2 (c (Sum.inr (q.1, q.2)))) :=
        IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩
      rw [hq] at hmem
      refine IntermediateField.adjoin.mono _ _ _ ?_ hmem
      rintro _ ⟨S, rfl⟩
      exact ⟨(q.1, ⟨q.2, S⟩), rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨τ, i, S⟩, rfl⟩
    have hmem : flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i S / leadMinor (genMat0Fr Ω Ψ D.N D.j τ) i ∈
        IntermediateField.adjoin Ω (Set.range fun S : PluckerBlocks D.N D.N i =>
          flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i S / leadMinor (genMat0Fr Ω Ψ D.N D.j τ) i) :=
      IntermediateField.subset_adjoin _ _ ⟨S, rfl⟩
    rw [← hq] at hmem
    refine IntermediateField.adjoin.mono _ _ _ ?_ hmem
    rintro _ ⟨m, rfl⟩
    exact ⟨⟨Sum.inr (τ, i), m⟩, rfl⟩

theorem HodgeFlagRatioFieldEq.full : HodgeFlagRatioFieldEq.Statement :=
  HodgeFlagRatioFieldEq.proof RatioFieldSpan.full HodgeFlagSpan.full PivotMinorFlag.full GenLeadMinor0NeZero.full

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.HFl
section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PGrassHeightE
section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsGrassHeightE
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights Matrix

noncomputable section

def UnitDetBound (m j : ℕ) (e : ℝ) : Prop :=
  ∀ Z : Matrix (Fin m) (Fin j) ℂ, (∀ a b, ‖Z a b‖ = 1) → 1 / 2 * Real.log (1 + Z * Zᴴ).det.re ≤ e

def RootLogNormBoundE.Statement : Prop :=
  ∀ (f j m : ℕ) (e : ℝ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), UnitDetBound m j e → IsRootMatrix ζ →
    ∀ z ∈ mcPts (rootPointIdeal ζ),
      -((f : ℝ) * e) ≤ logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) z

def RootHeightE.Statement : Prop :=
  ∀ (f j m : ℕ) (e : ℝ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), 1 ≤ f → UnitDetBound m j e → IsRootMatrix ζ →
    ∀ II : IntersectionSystem, IsIntersectionSystem II →
      II (Fin f) (plBlocks f j m) (rootPointIdeal ζ) 1 ![fsMulti (plBlocks f j m)] ≤
        (f : ℝ) * e * degC (rootPointIdeal ζ)

def GrassHeightE.Statement : Prop :=
  SuccessiveMinimaUpperBound → ∀ (f j m : ℕ) (e : ℝ), 1 ≤ f → UnitDetBound m j e →
    ∀ II : IntersectionSystem, IsIntersectionSystem II →
      II (Fin f) (plBlocks f j m) (grassIdeal f j m) (f * j * m + 1) (fun _ => fsMulti (plBlocks f j m)) ≤
        ((f * j * m + 1 : ℕ) : ℝ) * ((f : ℝ) * e) *
          geomDeg (grassIdeal f j m) (fsMulti (plBlocks f j m)) (f * j * m)

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights MvPolynomial Matrix

noncomputable section

namespace GrassHeightEAux

theorem log_block (j m : ℕ) (e : ℝ) (he : UnitDetBound m j e) (Z : Matrix (Fin j) (Fin m) ℂ)
    (hZ : ∀ a b, ‖Z a b‖ = 1) (a : ℂ) (ha : a ≠ 0) (v : PlIdx j m → ℂ)
    (hv : ∀ I, v I = a * (colsOf (onePipe Z) I).det) :
    -e ≤ Real.log (‖a‖ / ‖WithLp.toLp 2 v‖) := by
  set S : ℝ := ∑ I : PlIdx j m, ‖(colsOf (onePipe Z) I).det‖ ^ 2 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnorm : ‖WithLp.toLp 2 v‖ = ‖a‖ * Real.sqrt S := by
    rw [EuclideanSpace.norm_eq]
    have hs : ∑ I, ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (PlIdx j m)) I‖ ^ 2 = ‖a‖ ^ 2 * S := by
      rw [hSdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp [hv, mul_pow]
    rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hdet : S = (1 + Z * Zᴴ).det.re := by
    rw [← PlueckerNormSq.full j m Z, Complex.ofReal_re]
  have hb := he Zᴴ fun a b => by rw [conjTranspose_apply, norm_star, hZ b a]
  rw [conjTranspose_conjTranspose, det_one_add_mul_comm, ← hdet] at hb
  rw [hnorm, div_mul_cancel_left₀ ha'.ne', Real.log_inv, Real.log_sqrt hS0]
  linarith

end GrassHeightEAux


open GrassHeightEAux in
theorem RootLogNormBoundE.full : RootLogNormBoundE.Statement := by
  intro f j m e ζ he hζ z hz
  have h₁ := RootAnchorNonzero.proof
  have hpos : ∀ τ : Fin f, 0 < ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖ := fun τ =>
    (fsMetric (ι := PlIdx j m)).pos _ fun h0 => by
      obtain ⟨i, hi⟩ := hz.1 τ
      exact hi (congrFun h0 i)
  have key : ∀ τ : Fin f, -e ≤
      Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖) := by
    intro τ
    obtain ⟨ζ', hζ', hz'⟩ := RootPointConj.full f j m ζ hζ z hz τ
    exact log_block j m e he ζ' (fun a b => by
        obtain ⟨k, hk, h⟩ := hζ' a b
        exact Complex.norm_eq_one_of_pow_eq_one h hk.ne')
      _ (h₁ f j m ζ hζ z hz τ) _ hz'
  have hne : ∀ τ ∈ (Finset.univ : Finset (Fin f)),
      ‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖ ≠ 0 := fun τ _ =>
    div_ne_zero (norm_ne_zero_iff.mpr (h₁ f j m ζ hζ z hz τ)) (hpos τ).ne'
  have e' : logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) z =
      ∑ τ, Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖) := by
    rw [← Real.log_prod hne]
    simp [logNorm, fsMulti, HermLine.ofMetrics, fsMetric, rootAnchorSection, Finset.prod_div_distrib]
  rw [e']
  calc -((f : ℝ) * e) = ∑ _τ : Fin f, -e := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ _ := Finset.sum_le_sum fun τ _ => key τ

theorem RootHeightE.full : RootHeightE.Statement := by
  intro f j m e ζ hf he hζ II hII
  have : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩
  have hV := RootArithVar.full f j m ζ hf hζ
  have hmem : rootAnchorSection f j m ∉ rootPointIdeal ζ := by
    rw [rootPointIdeal, MultiHomogMemCoord.proof (Fin f) (plBlocks f j m) ℂ (rootCoord ζ) _ _ (anchor_homog f j m)]
    simp [rootAnchorSection, rootCoord, anchor_minor]
  have hsm : IsSmoothHerm (fsMulti (plBlocks f j m)) := FsLineSmooth.proof _ _
  have hR := (hII (Fin f) (plBlocks f j m)).2.2 (rootPointIdeal ζ) 0 Fin.elim0
    (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) (fun _ => 1) hV (fun j => j.elim0) hsm
    (fun _ => by simp [fsMulti, HermLine.ofMetrics]) (anchor_homog f j m) hmem
  have e1 : (Fin.snoc (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) :
      Fin (0 + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) = ![fsMulti (plBlocks f j m)] := by
    funext i; fin_cases i; rfl
  rw [e1] at hR
  have hlow := PtsIntegralZeroLowerNE.proof (Fin f) (plBlocks f j m) (rootPointIdeal ζ)
    (fun i z => Real.log (((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) i).h z))
    (logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m)) (-((f : ℝ) * e))
    hV.2.1.2.1 (RootPointsFinite.full f j m ζ hζ) ?_ (RootLogNormBoundE.full f j m e ζ he hζ)
  · have : recR (II (Fin f) (plBlocks f j m)) (rootPointIdeal ζ)
        (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) =
        - arInt (rootPointIdeal ζ) (rootAnchorSection f j m) (fsMulti (plBlocks f j m)) Fin.elim0 := by
      simp [recR, RootDivSuppEmpty.proof f j m ζ hζ]
    rw [this] at hR
    show II _ _ _ 1 _ ≤ _
    rw [hR]
    simp only [arInt]
    have := hlow
    nlinarith
  · intro u z hu hz
    have hh := (fsMulti (plBlocks f j m)).smul u z hu
    have hfa : (fsMulti (plBlocks f j m)).a = fun _ => 1 := rfl
    simp only [logNorm, hh, hfa, zpow_one]
    have hs : eval (fun p : (Σ _ : Fin f, PlIdx j m) => u p.1 * z p)
        (map (Int.castRingHom ℂ) (rootAnchorSection f j m))
        = (∏ k, u k) * eval z (map (Int.castRingHom ℂ) (rootAnchorSection f j m)) := by
      simp [rootAnchorSection, Finset.prod_mul_distrib]
    have hu0 : (∏ k, ‖u k‖) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => norm_ne_zero_iff.mpr (hu k)
    congr 1
    erw [hs]
    rw [norm_mul, norm_prod]
    field_simp

theorem GrassHeightE.full : GrassHeightE.Statement := by
  intro hZ2 f j m e hf he II hII
  refine hZ2 (Fin f) (plBlocks f j m) (grassIdeal f j m) ⊥ (f * j * m) (fsMulti (plBlocks f j m))
    ((f : ℝ) * e) (rootFamily f j m) II hII (GrassArithVar.full f j m hf) bot_le
    (FsLineSemipositive.full _ _ _) (NefOfNonneg.proof _ _ _ _ fun _ => ?_) (FsConjInvariant.proof _ _) ?_
    (RootDense.full f j m)
  · show (0 : ℤ) ≤ 1
    exact zero_le_one
  · rintro W ⟨ζ, hζ, rfl⟩
    exact ⟨RootArithVar.full f j m ζ hf hζ, GrassLeRoot.proof f j m ζ, RootHeightE.full f j m e ζ hf he hζ II hII⟩

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

theorem GrassmannianHeightZTwo.proof (hZ2 : SuccessiveMinimaUpperBound) (hPush : FlagGrassPush.Statement)
    (hDeg : HilbertSamuel.FSGeomDegPos.Statement) : GrassmannianHeightZTwo.Statement := by
  intro II Ψ _ _ N j cf e hII hN hj1 hjN hJ hZ
  rcases isEmpty_or_nonempty Ψ with hΨ | hΨ
  · have hmu : muPoly Ψ N j = 0 := by
      unfold muPoly
      exact Finset.sum_eq_zero fun p _ => (IsEmpty.false p.1).elim
    have hFA : FA Ψ N j cf = 0 := by
      unfold FA
      rw [hmu, zero_pow (Nat.succ_ne_zero _), zero_mul]
    rw [hFA, Fintype.card_eq_zero]
    simp [hFl]
  · set f := Fintype.card Ψ with hfdef
    have hf : 1 ≤ f := Fintype.card_pos
    have hP := hPush II Ψ N j cf hII hN hj1 hjN
    have hG := GrassHeightE.full hZ2 f j (N - j) e hf hZ II hII
    have hD : 0 < geomDeg (grassIdeal f j (N - j)) (GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j (N - j)))
        (f * j * (N - j)) :=
      hDeg (Fin f) (plBlocks f j (N - j)) (grassIdeal f j (N - j)) (f * j * (N - j))
        (GrassArithVar.full f j (N - j) hf)
    have hJ' : (0 : ℝ) < (Jint Ψ N j cf : ℝ) := Rat.cast_pos.mpr hJ
    change -hFl Ψ N II (FA Ψ N j cf) * geomDeg (grassIdeal f j (N - j))
        (GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j (N - j))) (f * j * (N - j)) =
      (Jint Ψ N j cf : ℝ) * II (Fin f) (plBlocks f j (N - j)) (grassIdeal f j (N - j))
        (f * j * (N - j) + 1) (fun _ => GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j (N - j))) at hP
    change -hFl Ψ N II (FA Ψ N j cf) ≤ ((f * j * (N - j) + 1 : ℕ) : ℝ) * (Jint Ψ N j cf : ℝ) * (f : ℝ) * e
    have h1 := mul_le_mul_of_nonneg_left hG hJ'.le
    refine le_of_mul_le_mul_right ?_ hD
    rw [hP]
    calc _ ≤ _ := h1
      _ = _ := by ring

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
