module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticNinth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticEighth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsSumframe

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.LocalAnalyticSectionCoords
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.CovMap PositivityTheory.Xgp.c_algsq

noncomputable section
namespace PositivityTheory.Xgp.c_sqsys

section Join

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def joinPt {R : Type} (k₀ : K) (z₀ z₁ : (Σ k, ι k) → R) : (Σ o : Option K, ι (o.getD k₀)) → R
  | ⟨some k, m⟩ => z₀ ⟨k, m⟩
  | ⟨none, m⟩ => z₁ ⟨k₀, m⟩

theorem join_v₁ {R : Type} {k₀ : K} {z₀ z₁ : (Σ k, ι k) → R} (h : ∀ k, k ≠ k₀ → ∀ m, z₀ ⟨k, m⟩ = z₁ ⟨k, m⟩) :
    joinPt k₀ z₀ z₁ ∘ v₁ k₀ = z₁ := by
  funext ⟨k, m⟩
  by_cases e : k = k₀
  · subst e
    show joinPt k z₀ z₁ (v₁ k ⟨k, m⟩) = _
    rw [v₁_self]; rfl
  · show joinPt k₀ z₀ z₁ (v₁ k₀ ⟨k, m⟩) = _
    rw [v₁_ne (p := ⟨k, m⟩) e]
    exact h k e m

theorem orbit_of_blocks {z z' : (Σ k, ι k) → ℂ} (h : ∀ k, ∃ c : ℂ, c ≠ 0 ∧ ∀ m, z ⟨k, m⟩ = c * z' ⟨k, m⟩) :
    SameOrbit z z' := by
  choose c hc e using h
  exact ⟨c, hc, funext fun q => e q.1 q.2⟩

theorem blocks_of_orbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (k : K) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ m, z ⟨k, m⟩ = c * z' ⟨k, m⟩ := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c k, hc k, fun _ => rfl⟩

theorem fst_orbit {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := FibreCount.comp_orbit (Pts.isBlockMap_v₀ k₀) h

theorem snd_orbit {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := FibreCount.comp_orbit (isBlockMap_v₁ k₀) h

theorem sameOrbit_of_sameOrbit_fstPt_sndPt {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h₀ : SameOrbit (fstPt k₀ z) (fstPt k₀ z'))
    (h₁ : SameOrbit (sndPt k₀ z) (sndPt k₀ z')) : SameOrbit z z' := by
  refine orbit_of_blocks fun o => ?_
  cases o with
  | none =>
    obtain ⟨c, hc, e⟩ := blocks_of_orbit h₁ k₀
    exact ⟨c, hc, fun m => by simpa only [Pts.snd_self] using e m⟩
  | some k => exact blocks_of_orbit h₀ k

theorem join_orbit {k₀ : K} {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} {z₀ z₁ : (Σ k, ι k) → ℂ}
    (h₀ : SameOrbit z₀ (fstPt k₀ z)) (h₁ : SameOrbit z₁ (sndPt k₀ z)) : SameOrbit (joinPt k₀ z₀ z₁) z := by
  refine orbit_of_blocks fun o => ?_
  cases o with
  | none =>
    obtain ⟨c, hc, e⟩ := blocks_of_orbit h₁ k₀
    exact ⟨c, hc, fun m => (e m).trans (by rw [Pts.snd_self])⟩
  | some k => exact blocks_of_orbit h₀ k

theorem analytic_join {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k₀ : K) {f₀ f₁ : E → (Σ k, ι k) → ℂ}
    {x : E} (h₀ : AnalyticAt ℂ f₀ x) (h₁ : AnalyticAt ℂ f₁ x) :
    AnalyticAt ℂ (fun u => joinPt k₀ (f₀ u) (f₁ u)) x := by
  refine analyticAt_pi_iff.2 ?_
  rintro ⟨_ | k, m⟩
  · exact analyticAt_pi_iff.1 h₁ ⟨k₀, m⟩
  · exact analyticAt_pi_iff.1 h₀ ⟨k, m⟩

theorem analytic_comp_idx {α β : Type} [Fintype α] [Fintype β] (v : α → β) (x : β → ℂ) :
    AnalyticAt ℂ (fun z : β → ℂ => z ∘ v) x :=
  analyticAt_pi_iff.2 fun a => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : β => ℂ) (v a)).analyticAt x

theorem continuous_comp_idx {α β : Type} (v : α → β) : Continuous (fun z : β → ℂ => z ∘ v) :=
  continuous_pi fun a => continuous_apply (v a)

end Join

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def WA : Prop := ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) (d + 3) ∧ IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)) (d + 2) ∧ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ≤ mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0) ∧ imageZ (fun p : (Σ k, ι k) => (⟨some p.1, p.2⟩ : Σ o : Option K, ι (o.getD k₀))) (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y ∧ ∀ v₁ : (Σ k, ι k) → (Σ o : Option K, ι (o.getD k₀)), (∀ p : (Σ k, ι k), p.1 ≠ k₀ → v₁ p = ⟨some p.1, p.2⟩) → (∀ m : ι k₀, v₁ ⟨k₀, m⟩ = ⟨none, m⟩) → imageZ v₁ (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y

structure Sw (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) : Prop where
  hb : (b : ℕ) = a + 1
  hab : (b : ℕ) < j ∨ j ≤ (a : ℕ)
  hk : M.blk (τ, a) = some k₀
  hca : (ca : ℕ) = lastCol N j a
  hcb : (cb : ℕ) = ca + 1
  wa : WA

section W

variable {M : FlagModel y Ψ N j} {τ : Ψ} {a b : Fin N} {k₀ : K} {ca cb : Fin N} {d : ℕ}

theorem Sw.arith (S : Sw M τ a b k₀ ca cb) (hy : IsArithVar (mCoordIdeal y) (d + 2)) :
    IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) (d + 2 + 1) :=
  (S.wa K ι Φ y Ψ N j M d τ a b k₀ ca cb S.hb S.hab S.hk S.hca S.hcb hy).1

theorem Sw.im₀ (S : Sw M τ a b k₀ ca cb) (hy : IsArithVar (mCoordIdeal y) (d + 2)) :
    imageZ (v₀ k₀) (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y :=
  (S.wa K ι Φ y Ψ N j M d τ a b k₀ ca cb S.hb S.hab S.hk S.hca S.hcb hy).2.2.2.1

theorem fst_mem {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X))) : fstPt k₀ z ∈ mcPts (mCoordIdeal y) :=
  CPts.comp_mem_mcPts (Pts.isBlockMap_v₀ k₀) (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz

theorem Sw.snd_mem (S : Sw M τ a b k₀ ca cb) (hy : IsArithVar (mCoordIdeal y) (d + 2))
    {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X))) : sndPt k₀ z ∈ mcPts (mCoordIdeal y) :=
  Pts.snd_mem ((S.wa K ι Φ y Ψ N j M d τ a b k₀ ca cb S.hb S.hab S.hk S.hca S.hcb hy).2.2.2.2 (v₁ k₀)
    (fun _ h => v₁_ne h) (v₁_self k₀)) hz

theorem Sw.data (S : Sw M τ a b k₀ ca cb) {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    (h₀ : fstPt k₀ z ∈ mcPts (mCoordIdeal y)) (h₁ : sndPt k₀ z ∈ mcPts (mCoordIdeal y))
    {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal (basePart M.blk (fstPt k₀ z)))) :
    ∃ z', SameOrbit z' z ∧ ∃ (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFlagOf F (fstPt k₀ z') h ∧
      M.IsFlagOf F (sndPt k₀ z') (Function.update h τ (h τ * (1 + Matrix.single cb ca t))) := by
  obtain ⟨z₁, ⟨c, hc, e⟩, hn⟩ := FibreCount.exists_normal_base M.blk F.c (fstPt k₀ z) fun k =>
    FibreCount.chart_ne (hG.1 k)
  let z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun q => q.1.elim 1 c * z q
  have ho : SameOrbit z' z := ⟨fun o => o.elim 1 c, fun o => by cases o <;> simp [hc], rfl⟩
  have e' : fstPt k₀ z' = z₁ := by rw [e]; rfl
  have hI := CoordinateConeArithVar.isMultiHomogIdeal y
  have m₀ := mem_mcPts_of_sameOrbit hI (fst_orbit ho) h₀
  have m₁ := mem_mcPts_of_sameOrbit hI (snd_orbit ho) h₁
  have hG' : M.GoodAt F (mCoordIdeal (basePart M.blk (fstPt k₀ z'))) := by
    rw [FibreCount.mCoordIdeal_eq_of_orbit (FibreCount.basePart_orbit M.blk (fst_orbit ho))]; exact hG
  have hsnd := Pts.basePart_snd M S.hk z'
  have hc' : ∀ k, basePart M.blk (fstPt k₀ z') ⟨k, F.c k⟩ = 1 := by rw [e']; exact hn
  obtain ⟨h, H⟩ := CPts.flag_fwd M hF m₀ hG' hc'
  obtain ⟨h', H'⟩ := CPts.flag_fwd M hF m₁ (hsnd ▸ hG') (hsnd ▸ hc')
  exact ⟨z', ho, Pts.fwd_flags M S.hb S.hab S.hk S.hca S.hcb hF (CPts.base_mem M m₀) hG' H H'⟩

theorem Sw.mem (S : Sw M τ a b k₀ ca cb) {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    (h₀ : fstPt k₀ z ∈ mcPts (mCoordIdeal y)) (h₁ : sndPt k₀ z ∈ mcPts (mCoordIdeal y)) :
    z ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) := by
  obtain ⟨F, hF, hG⟩ := (GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).2.1 _ (CPts.base_mem M h₀)
  obtain ⟨z', ho, h, t, H, H'⟩ := S.data h₀ h₁ hF hG
  have m₀ := mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y) (fst_orbit ho) h₀
  have hG' : M.GoodAt F (mCoordIdeal (basePart M.blk (fstPt k₀ z'))) := by
    rw [FibreCount.mCoordIdeal_eq_of_orbit (FibreCount.basePart_orbit M.blk (fst_orbit ho))]; exact hG
  exact mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) (orbit_symm ho)
    (Pts.back M S.hb S.hab S.hk S.hca S.hcb hF (CPts.base_mem M m₀) hG' H H')

theorem ideal_W_le {Φ₂ : Type} [Field Φ₂] {y₂ : (Σ k, ι k) → Φ₂} {M₂ : FlagModel y₂ Ψ N j}
    (S : Sw M τ a b k₀ ca cb) (S₂ : Sw M₂ τ a b k₀ ca cb) (hy : IsArithVar (mCoordIdeal y) (d + 2))
    (e : mCoordIdeal y₂ = mCoordIdeal y) :
    mCoordIdeal (M₂.wCo (τ, a) k₀ ca cb RatFunc.X) ≤ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) := by
  by_contra hn
  obtain ⟨z, hz, hz'⟩ := HilbertSamuel.exists_mcPts_not_mem_mcPts (S.arith hy) hn
  exact hz' (S₂.mem (e ▸ fst_mem hz) (e ▸ S.snd_mem hy hz))

theorem ideal_W_eq {Φ₂ : Type} [Field Φ₂] {y₂ : (Σ k, ι k) → Φ₂} {M₂ : FlagModel y₂ Ψ N j}
    (S : Sw M τ a b k₀ ca cb) (S₂ : Sw M₂ τ a b k₀ ca cb) (hy : IsArithVar (mCoordIdeal y) (d + 2))
    (e : mCoordIdeal y₂ = mCoordIdeal y) :
    mCoordIdeal (M₂.wCo (τ, a) k₀ ca cb RatFunc.X) = mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) :=
  le_antisymm (ideal_W_le S S₂ hy e) (ideal_W_le S₂ S (e ▸ hy) e.symm)

end W

variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

section Cov

variable {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j}


open FibreCount in
theorem img_blk (Cv : FlagCover M' M) {d : ℕ}
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    {w₁ w₂ : (Σ k, ι k) → ℂ} (hw : w₁ ∈ mcPts (mCoordIdeal y)) {z₁ z₂ : (Σ k, ι' k) → ℂ}
    (h₁ : z₁ ∈ mcPts (mCoordIdeal y')) (h₂ : z₂ ∈ mcPts (mCoordIdeal y'))
    (i₁ : IsImg Cv z₁ w₁) (i₂ : IsImg Cv z₂ w₂)
    (hb : SameOrbit (basePart M'.blk z₁) (basePart M'.blk z₂)) {p : Ψ × Fin N} {k : K} {k' : K'}
    (hk : M.blk p = some k) (hp' : M'.blk p = some k') (hww : ∀ m, w₁ ⟨k, m⟩ = w₂ ⟨k, m⟩) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ m, z₁ ⟨k', m⟩ = c * z₂ ⟨k', m⟩ := by
  have P := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  have P' := GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M'
  obtain ⟨F', hF', hg'⟩ := P'.2.1 _ (P'.1 z₁ h₁)
  obtain ⟨a₁, o₁, n₁⟩ := exists_normal_base M'.blk F'.c z₁ fun k => chart_ne (hg'.1 k)
  obtain ⟨a₂, o₂, n₂⟩ := exists_normal_base M'.blk F'.c z₂ fun k =>
    chart_ne (by rw [← mCoordIdeal_eq_of_orbit hb]; exact hg'.1 k)
  have ob₁ := basePart_orbit M'.blk o₁
  have ob₂ := basePart_orbit M'.blk o₂
  have eb : basePart M'.blk a₁ = basePart M'.blk a₂ := eq_of_orbit_normal (c := F'.c)
    (Cj.sameOrbit_trans ob₁ (Cj.sameOrbit_trans hb (Cj.sameOrbit_symm ob₂))) n₁ n₂
  have hbm : basePart M'.blk a₁ ∈ mcPts (mCoordIdeal M'.x) :=
    mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) ob₁ (P'.1 z₁ h₁)
  have hgb : M'.GoodAt F' (mCoordIdeal (basePart M'.blk a₁)) := by rw [mCoordIdeal_eq_of_orbit ob₁]; exact hg'
  have ha₁ := mem_mcPts_of_sameOrbit hy'.2.1.2.1 o₁ h₁
  have ha₂ := mem_mcPts_of_sameOrbit hy'.2.1.2.1 o₂ h₂
  have hbw : SameOrbit (basePart M'.blk a₁ ∘ Cv.v) (basePart M.blk w₁) := Cj.sameOrbit_trans
    (comp_orbit Cv.block ob₁) (Cj.sameOrbit_symm (GlobalTheory.T.flag_cover_arithmetic_third K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' z₁ h₁ w₁ i₁))
  have hbv := mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) hbw (P.1 w₁ hw)
  obtain ⟨F, hF, hg⟩ := P.2.1 _ hbv
  obtain ⟨g₁, fl₁⟩ := (P'.2.2 F' hF' a₁ hbm hgb n₁).1 ha₁
  obtain ⟨g₂, fl₂⟩ := (P'.2.2 F' hF' a₂ (by rw [← eb]; exact hbm) (by rw [← eb]; exact hgb) n₂).1 ha₂
  obtain ⟨z₀, s₁, t₁, f₁⟩ := i₁ a₁ o₁ F' F hF' hF hgb hg g₁ fl₁
  obtain ⟨z₀', s₂, t₂, f₂⟩ := i₂ a₂ o₂ F' F hF' hF (by rw [← eb]; exact hgb) (by rw [← eb]; exact hg) g₂ fl₂
  rw [← eb] at t₂ f₂
  have eβ : basePart M.blk z₀ = basePart M.blk z₀' :=
    eq_of_orbit_normal (c := F.c) (Cj.sameOrbit_trans t₁ (Cj.sameOrbit_symm t₂)) f₁.1 f₂.1
  have hβ : basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) :=
    mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) t₁ hbv
  have hgβ : M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) := by rw [mCoordIdeal_eq_of_orbit t₁]; exact hg
  obtain ⟨c₁, hc₁, ez₁⟩ := blocks_of_orbit s₁ k
  obtain ⟨c₂, hc₂, ez₂⟩ := blocks_of_orbit s₂ k
  obtain ⟨c, hc, ez⟩ : ∃ c : ℂ, c ≠ 0 ∧ ∀ m, z₀ ⟨k, m⟩ = c * z₀' ⟨k, m⟩ :=
    ⟨c₁ / c₂, div_ne_zero hc₁ hc₂, fun m => by rw [ez₁, ez₂, hww]; field_simp⟩
  have hT := trans_unit Cv hbm hF' hF hgb hg
  have hpr : IsProperStep N j p.2 := by
    by_contra hn
    rw [(M'.blk_none p).2 hn] at hp'
    exact absurd hp' (by simp)
  obtain ⟨e₁, he₁, v₁⟩ := f₁.2.2 p k hk
  obtain ⟨e₂, he₂, v₂⟩ := f₂.2.2 p k hk
  have key := step_prop (M' := M') (c := c) (e₁ := e₁) (e₂ := e₂) hF hβ hgβ hk hpr (hT p.1) (fl₁.2.1 p.1).1
    (fl₂.2.1 p.1).1 he₁ (fun m => by
      have x3 := ez m
      have x1 := v₁ m
      have x2 := v₂ m
      rw [← eβ] at x2
      rw [x1, x2] at x3
      exact x3)
  obtain ⟨a, ha, w₁⟩ := fl₁.2.2 p k' hp'
  obtain ⟨a', ha', w₂⟩ := fl₂.2.2 p k' hp'
  obtain ⟨b₁, hb₁, eb₁⟩ := blocks_of_orbit o₁ k'
  obtain ⟨b₂, hb₂, eb₂⟩ := blocks_of_orbit o₂ k'
  refine ⟨a * (c * e₂ / e₁) / a' * b₂ / b₁, div_ne_zero (mul_ne_zero
    (div_ne_zero (mul_ne_zero ha (div_ne_zero (mul_ne_zero hc he₂) he₁)) ha') hb₂) hb₁, fun m => ?_⟩
  have g0 : a₁ ⟨k', m⟩ = a * (c * e₂ / e₁) / a' * a₂ ⟨k', m⟩ := by
    rw [w₁ m, w₂ m, ← eb]
    simp only [key]
    have g1 : ∑ I, valAt M'.x (F'.u ⟨k', m⟩ I) (basePart M'.blk a₁) *
        ((c * e₂ / e₁) * minorIJ (g₂ p.1) I (stepCols N j p.2)) =
        (c * e₂ / e₁) * ∑ I, valAt M'.x (F'.u ⟨k', m⟩ I) (basePart M'.blk a₁) * minorIJ (g₂ p.1) I (stepCols N j p.2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [g1]
    field_simp
  rw [eb₁, eb₂] at g0
  rw [div_mul_eq_mul_div, eq_div_iff hb₁]
  linear_combination g0

theorem blk_cover (M : FlagModel y Ψ N j) (M' : FlagModel y' Ψ N j) {p : Ψ × Fin N} {k' : K'}
    (hp : M'.blk p = some k') : ∃ k, M.blk p = some k :=
  Option.ne_none_iff_exists'.1 fun e => by
    rw [(M'.blk_none p).2 ((M.blk_none p).1 e)] at hp
    cases hp

variable {τ : Ψ} {a b : Fin N} {k₀ : K} {k₀' : K'} {ca cb : Fin N} {d : ℕ}

def RelW (Cv : FlagCover M' M) (k₀ : K) (k₀' : K') (z : (Σ o : Option K', ι' (o.getD k₀')) → ℂ)
    (w : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : Prop :=
  IsImg Cv (fstPt k₀' z) (fstPt k₀ w) ∧ IsImg Cv (sndPt k₀' z) (sndPt k₀ w)

theorem RelW.orbit {Cv : FlagCover M' M} {z z₁ : (Σ o : Option K', ι' (o.getD k₀')) → ℂ}
    {w w₁ : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : RelW Cv k₀ k₀' z w) (hz : SameOrbit z₁ z)
    (hw : SameOrbit w₁ w) : RelW Cv k₀ k₀' z₁ w₁ :=
  ⟨h.1.orbit (fst_orbit hz) (fst_orbit hw), h.2.orbit (snd_orbit hz) (snd_orbit hw)⟩

theorem exists_relW_lift_of_isImg (Cv : FlagCover M' M) (S : Sw M τ a b k₀ ca cb) (S' : Sw M' τ a b k₀' ca cb)
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    {w : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hw : w ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)))
    {z₀ : (Σ k, ι' k) → ℂ} (hz₀ : z₀ ∈ mcPts (mCoordIdeal y')) (hi : IsImg Cv z₀ (fstPt k₀ w)) :
    ∃ z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)), fstPt k₀' z = z₀ ∧ RelW Cv k₀ k₀' z w := by
  have hb := GlobalTheory.T.flag_cover_arithmetic_third K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' z₀ hz₀ _ hi
  obtain ⟨z₁, hz₁, ho, hi₁⟩ := FibreCount.img_surj Cv hy hy' (S.snd_mem hy hw) (CPts.base_mem M' hz₀)
    (by rw [Pts.basePart_snd M S.hk]; exact orbit_symm hb)
  have hs : SameOrbit (sndPt k₀' (joinPt k₀' z₀ z₁)) z₁ := by
    refine orbit_of_blocks fun k' => ?_
    by_cases e : k' = k₀'
    · subst e
      exact ⟨1, one_ne_zero, fun m => by rw [Pts.snd_self, one_mul]; rfl⟩
    · simp only [Pts.snd_fst_ne e]
      by_cases hk : ∀ p, M'.blk p ≠ some k'
      · exact blocks_of_orbit (orbit_symm ho) ⟨k', hk⟩
      · push_neg at hk
        obtain ⟨p, hp⟩ := hk
        obtain ⟨k, hk⟩ := blk_cover M M' hp
        have hne : k ≠ k₀ := fun e' => e (by
          have := M.blk_inj _ _ _ hk (e' ▸ S.hk)
          rw [this, S'.hk] at hp
          exact (Option.some.inj hp).symm)
        exact img_blk Cv hy hy' (fst_mem hw) hz₀ hz₁ hi hi₁ (orbit_symm ho) hk hp
          fun m => (Pts.snd_fst_ne hne w m).symm
  exact ⟨joinPt k₀' z₀ z₁, S'.mem hz₀ (mem_mcPts_of_sameOrbit hy'.2.1.2.1 hs hz₁), rfl, hi,
    hi₁.orbit hs (Cj.sameOrbit_refl _)⟩

theorem ncard_orbits_relW_eq_ncard_orbits_isImg (Cv : FlagCover M' M) (S : Sw M τ a b k₀ ca cb) (S' : Sw M' τ a b k₀' ca cb)
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    {w : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hw : w ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X))) :
    {O | ∃ z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)),
        O = {z'' | SameOrbit z'' z} ∧ RelW Cv k₀ k₀' z w}.ncard =
      {O | ∃ z ∈ mcPts (mCoordIdeal y'), O = {z'' | SameOrbit z'' z} ∧ IsImg Cv z (fstPt k₀ w)}.ncard := by
  have key : ∀ z : (Σ o : Option K', ι' (o.getD k₀')) → ℂ,
      {u | ∃ z₂ ∈ {z'' | SameOrbit z'' z}, SameOrbit u (fstPt k₀' z₂)} = {u | SameOrbit u (fstPt k₀' z)} := fun z => by
    ext u
    exact ⟨fun ⟨z₂, h1, h2⟩ => orbit_trans h2 (fst_orbit h1), fun h => ⟨z, Cj.sameOrbit_refl z, h⟩⟩
  refine Set.ncard_congr (fun O _ => {u | ∃ z₂ ∈ O, SameOrbit u (fstPt k₀' z₂)}) ?_ ?_ ?_
  · rintro O ⟨z, hz, rfl, hr⟩
    exact ⟨fstPt k₀' z, fst_mem hz, key z, hr.1⟩
  · rintro O O' ⟨z, hz, rfl, hr⟩ ⟨z', hz', rfl, hr'⟩ e
    simp only [key] at e
    have h0 := FibreCount.orbit_eq_iff.1 e
    refine FibreCount.orbit_eq_iff.2 (sameOrbit_of_sameOrbit_fstPt_sndPt h0 ?_)
    refine FibreCount.img_inj Cv hy hy' (S.snd_mem hy hw) (S'.snd_mem hy' hz) (S'.snd_mem hy' hz') hr.2 hr'.2 ?_
    rw [Pts.basePart_snd M' S'.hk, Pts.basePart_snd M' S'.hk]
    exact FibreCount.basePart_orbit _ h0
  · rintro O ⟨z₀, hz₀, rfl, hi⟩
    obtain ⟨z, hz, rfl, hr⟩ := exists_relW_lift_of_isImg Cv S S' hy hy' hw hz₀ hi
    exact ⟨_, ⟨z, hz, rfl, hr⟩, key z⟩

theorem local_analytic_section_coords (Cv : FlagCover M' M) (S : Sw M τ a b k₀ ca cb) (S' : Sw M' τ a b k₀' ca cb)
    (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    {z : (Σ o : Option K', ι' (o.getD k₀')) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X))) :
    ∃ (V : Set ((Σ o : Option K', ι' (o.getD k₀')) → ℂ))
      (f : ((Σ o : Option K', ι' (o.getD k₀')) → ℂ) → (Σ o : Option K, ι (o.getD k₀)) → ℂ), IsOpen V ∧ z ∈ V ∧
      AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)),
        f z' ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ∧ RelW Cv k₀ k₀' z' (f z') := by
  have hz₀ := fst_mem hz
  have hz₁ := S'.snd_mem hy' hz
  have hb := CPts.base_mem M' hz₀
  have hbv := (GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ hb).1
  obtain ⟨F', hF', hg'⟩ := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').2.1 _ hb
  obtain ⟨F, hF, hg⟩ := (GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).2.1 _ hbv
  have hsb := Pts.basePart_snd M' S'.hk
  obtain ⟨V₀, f₀, hV₀, hzV₀, hf₀, hs₀⟩ := GlobalTheory.T.flag_cover_frames_at_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F hz₀ hF' hF hg' hg
  obtain ⟨V₁, f₁, hV₁, hzV₁, hf₁, hs₁⟩ := GlobalTheory.T.flag_cover_frames_at_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F hz₁ hF' hF
    (by rw [hsb]; exact hg') (by rw [hsb]; exact hg)
  refine ⟨fstPt k₀' ⁻¹' V₀ ∩ sndPt k₀' ⁻¹' V₁, fun u => joinPt k₀ (f₀ (fstPt k₀' u)) (f₁ (sndPt k₀' u)),
    (hV₀.preimage (continuous_comp_idx _)).inter (hV₁.preimage (continuous_comp_idx _)), ⟨hzV₀, hzV₁⟩,
    fun u hu => analytic_join k₀ ((hf₀ _ hu.1).comp (analytic_comp_idx _ u))
      ((hf₁ _ hu.2).comp (analytic_comp_idx _ u)), fun u hu => ?_⟩
  have hu₀ := fst_mem hu.2
  have hu₁ := S'.snd_mem hy' hu.2
  obtain ⟨g1, g2, e₀⟩ := hs₀ _ ⟨hu.1.1, hu₀⟩
  obtain ⟨g3, g4, e₁⟩ := hs₁ _ ⟨hu.1.2, hu₁⟩
  obtain ⟨m₀, i₀⟩ := LocImg.img_spec K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F hu₀ hF' hF g1 g2
  obtain ⟨m₁, i₁⟩ := LocImg.img_spec K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F hu₁ hF' hF g3 g4
  have e : sndPt k₀ (joinPt k₀ (LocImg.img Cv F' F (fstPt k₀' u)) (LocImg.img Cv F' F (sndPt k₀' u))) =
      LocImg.img Cv F' F (sndPt k₀' u) := by
    refine join_v₁ fun k hk m => ?_
    by_cases hkb : ∀ p, M.blk p ≠ some k
    · have h1 := congrFun (LocImg.img_base Cv F' F (fstPt k₀' u)) ⟨⟨k, hkb⟩, m⟩
      have h2 := congrFun (LocImg.img_base Cv F' F (sndPt k₀' u)) ⟨⟨k, hkb⟩, m⟩
      rw [hsb] at h2
      exact h1.trans h2.symm
    · push_neg at hkb
      obtain ⟨p, hp⟩ := hkb
      obtain ⟨k', hk'⟩ := blk_cover M' M hp
      have hne : k' ≠ k₀' := fun e' => hk (by
        have := M'.blk_inj _ _ _ hk' (e' ▸ S'.hk)
        rw [this, S.hk] at hp
        exact (Option.some.inj hp).symm)
      rw [LocImg.img_step Cv F' F _ hp hk', LocImg.img_step Cv F' F _ hp hk']
      simp only [LocImg.stepCoord, hsb, Pts.snd_fst_ne hne]
  simp only [e₀, e₁]
  exact ⟨S.mem m₀ (by rw [e]; exact m₁), i₀, by rw [e]; exact i₁⟩

end Cov

end PositivityTheory.Xgp.c_sqsys
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.CovMap GlobalTheory.CompanionTheory.Ar.PB.CovGraph PositivityTheory.Xgp.c_algsq

noncomputable section
namespace PositivityTheory.Xgp.c_sqsys

section Mat

variable {R : Type} [CommRing R] {N j : ℕ}

theorem mul_transv_apply (A : Matrix (Fin N) (Fin N) R) (ca cb : Fin N) (t : R) (r c : Fin N) :
    (A * (1 + Matrix.single cb ca t)) r c = A r c + if c = ca then A r cb * t else 0 := by
  rw [mul_add, mul_one, Matrix.add_apply]
  congr 1
  split_ifs with h
  · subst h; exact Matrix.mul_single_apply_same _ _ _ _ _
  · exact Matrix.mul_single_apply_of_ne _ _ _ _ _ h _

theorem lowerUni_mul_transv {A : Matrix (Fin N) (Fin N) R} (hA : IsLowerUni A) {ca cb : Fin N}
    (hc : (cb : ℕ) = ca + 1) (t : R) : IsLowerUni (A * (1 + Matrix.single cb ca t)) := by
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  refine ⟨fun r => ?_, fun r c h => ?_⟩
  · rw [mul_transv_apply, hA.1]
    split_ifs with e
    · rw [hA.2 r cb (e ▸ hlt)]; simp
    · simp
  · rw [mul_transv_apply, hA.2 r c h]
    split_ifs with e
    · rw [hA.2 r cb (h.trans (e ▸ hlt))]; simp
    · simp

theorem minor_lowerUni {A : Matrix (Fin N) (Fin N) R} (hA : IsLowerUni A) (S : Finset (Fin N)) :
    minorIJ A S S = 1 := by
  rw [MinorCalc.minorIJ_eq_det A S S _ rfl rfl, det_of_lowerTriangular]
  · exact Finset.prod_eq_one fun i _ => hA.1 _
  · intro x y hxy
    exact hA.2 _ _ ((S.orderEmbOfFin rfl).strictMono hxy)

theorem minor_transv {a b ca cb i : Fin N} (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (hi : i ≠ a) (A : Matrix (Fin N) (Fin N) R) (t : R)
    (I : Finset (Fin N)) :
    minorIJ (A * (1 + Matrix.single cb ca t)) I (stepCols N j i) = minorIJ A I (stepCols N j i) := by
  have hu := lowerUni_mul_transv (isLowerUni_one (R := R) (N := N)) hcb t
  rw [one_mul] at hu
  rw [MinorCalc.minorIJ_mul_of_support A _ I _ ?_, minor_lowerUni hu, mul_one]
  intro k c hc hk
  have hkc : k ≠ c := fun e => hk (e ▸ hc)
  rw [Matrix.add_apply, Matrix.one_apply_ne hkc, zero_add]
  refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
  rintro ⟨rfl, rfl⟩
  apply hk
  have hi' : (i : ℕ) ≠ a := fun e => hi (Fin.ext e)
  have := b.2
  have := i.2
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, lastCol] at hc hca ⊢
  split_ifs at hc hca ⊢ <;> omega

end Mat

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

section Re

variable {L : Type} [Field L]

def ptOf (M : FlagModel y Ψ N j) (ψ : M.Ω →+* L) (G : Ψ → Matrix (Fin N) (Fin N) L) : (Σ k, ι k) → L := fun q =>
  if h : ∀ p, M.blk p ≠ some q.1 then ψ (M.x ⟨⟨q.1, h⟩, q.2⟩)
  else ∑ I, ψ (M.coef q I) * minorIJ (G (stepOf M q.1 h).1) I (stepCols N j (stepOf M q.1 h).2)

theorem ptOf_base (M : FlagModel y Ψ N j) (ψ : M.Ω →+* L) (G : Ψ → Matrix (Fin N) (Fin N) L)
    (q : Σ k, baseIdx ι M.blk k) : ptOf M ψ G ⟨q.1.1, q.2⟩ = ψ (M.x q) := dif_pos q.1.2

theorem ptOf_step (M : FlagModel y Ψ N j) (ψ : M.Ω →+* L) (G : Ψ → Matrix (Fin N) (Fin N) L)
    (p : Ψ × Fin N) (k : K) (hp : M.blk p = some k) (m : ι k) :
    ptOf M ψ G ⟨k, m⟩ = ∑ I, ψ (M.coef ⟨k, m⟩ I) * minorIJ (G p.1) I (stepCols N j p.2) := by
  have h : ¬ ∀ p, M.blk p ≠ some k := fun h => h p hp
  have e : stepOf M k h = p := M.blk_inj _ _ k (blk_stepOf M k h) hp
  show (if h : ∀ p, M.blk p ≠ some k then _ else _) = _
  rw [dite_eq_right h]
  simp only [e]

def IsGenLow {Ω : Type} [Field Ω] (ψ : Ω →+* L) (j : ℕ) (G : Ψ → Matrix (Fin N) (Fin N) L) : Prop :=
  (∀ τ, IsBlockDiag j (G τ) ∧ IsLowerUni (G τ)) ∧
    Function.Injective (eval₂Hom ψ fun q : LowIdx Ψ N j => G q.1.1 q.1.2.1 q.1.2.2)

def reModel (M : FlagModel y Ψ N j) (ψ : M.Ω →+* L) (G : Ψ → Matrix (Fin N) (Fin N) L) (hG : IsGenLow ψ j G) :
    FlagModel (ptOf M ψ G) Ψ N j where
  j_le := M.j_le
  Ω := M.Ω
  alg := ψ.toAlgebra
  blk := M.blk
  blk_none := M.blk_none
  blk_inj := M.blk_inj
  x := M.x
  x_ne := M.x_ne
  y_base q := ptOf_base M ψ G q
  g := G
  g_block τ := (hG.1 τ).1
  g_indep := by
    letI := ψ.toAlgebra
    exact IsGenericFlag.of_lowerUni (fun τ => (hG.1 τ).2) hG.2
  coef := M.coef
  y_step := ptOf_step M ψ G
  b := M.b
  lam := M.lam
  frames := M.frames

open GenIdeal in
theorem ideal_ptOf (M : FlagModel y Ψ N j) (ψ : M.Ω →+* L) (G : Ψ → Matrix (Fin N) (Fin N) L) (hG : IsGenLow ψ j G) :
    mCoordIdeal (ptOf M ψ G) = mCoordIdeal y := by
  obtain ⟨B, hB, hind⟩ := M.g_indep
  let ev : MvPolynomial (LowIdx Ψ N j) M.Ω →ₐ[M.Ω] Φ := aeval fun q => (M.g q.1.1 * B q.1.1) q.1.2.1 q.1.2.2
  obtain ⟨c, hc, hz⟩ := exists_scale M ev.toRingHom (algebraMap M.Ω Φ) (fun a => aeval_C _ a) M.g B M.g_block hB
    (fun q => aeval_X _ q) y M.y_base M.y_step
  obtain ⟨c', hc', hz'⟩ := exists_scale M (eval₂Hom ψ fun q : LowIdx Ψ N j => G q.1.1 q.1.2.1 q.1.2.2) ψ
    (fun a => eval₂Hom_C _ _ a) G (fun _ => 1) (fun τ => (hG.1 τ).1)
    (fun τ => ⟨isBlockDiag_one, blockTriangular_one, by rw [mul_one]; exact (hG.1 τ).2⟩)
    (fun q => by rw [mul_one]; exact eval₂Hom_X' _ _ q) (ptOf M ψ G) (ptOf_base M ψ G) (ptOf_step M ψ G)
  rw [mCoordIdeal_eq _ hG.2 _ _ c' hc' hz', mCoordIdeal_eq ev.toRingHom hind _ _ c hc hz]

theorem exists_genLow (M : FlagModel y Ψ N j) : ∃ G, IsGenLow (algebraMap M.Ω Φ) j (G : Ψ → Matrix (Fin N) (Fin N) Φ) := by
  obtain ⟨B, hB, hind⟩ := M.g_indep
  exact ⟨fun τ => M.g τ * B τ, fun τ => ⟨(M.g_block τ).mul (hB τ).1, (hB τ).2.2⟩, hind⟩

variable {Ω : Type} [Field Ω] {ψ : Ω →+* L} {G : Ψ → Matrix (Fin N) (Fin N) L}

theorem IsGenLow.restrict (h : IsGenLow ψ j G) {Ω₂ : Type} [Field Ω₂] (φ : Ω₂ →+* Ω) : IsGenLow (ψ.comp φ) j G := by
  refine ⟨h.1, ?_⟩
  have e : (eval₂Hom (ψ.comp φ) fun q : LowIdx Ψ N j => G q.1.1 q.1.2.1 q.1.2.2) =
      (eval₂Hom ψ fun q : LowIdx Ψ N j => G q.1.1 q.1.2.1 q.1.2.2).comp (MvPolynomial.map φ) :=
    MvPolynomial.ringHom_ext (fun a => by simp) fun q => by simp
  rw [e]
  exact h.2.comp (MvPolynomial.map_injective φ φ.injective)

def flag₀ (G : Ψ → Matrix (Fin N) (Fin N) L) : Ψ → Matrix (Fin N) (Fin N) (RatFunc L) :=
  fun τ => (G τ).map (algebraMap L (RatFunc L))

def flag₁ (G : Ψ → Matrix (Fin N) (Fin N) L) (τ : Ψ) (ca cb : Fin N) : Ψ → Matrix (Fin N) (Fin N) (RatFunc L) :=
  Function.update (flag₀ G) τ (flag₀ G τ * (1 + Matrix.single cb ca RatFunc.X))

theorem IsGenLow.flag₀ (h : IsGenLow ψ j G) : IsGenLow ((algebraMap L (RatFunc L)).comp ψ) j (flag₀ G) := by
  refine ⟨fun τ => ⟨(h.1 τ).1.map _, (h.1 τ).2.map _⟩, ?_⟩
  have e : (eval₂Hom ((algebraMap L (RatFunc L)).comp ψ) fun q : LowIdx Ψ N j =>
      c_sqsys.flag₀ G q.1.1 q.1.2.1 q.1.2.2) =
      (algebraMap L (RatFunc L)).comp (eval₂Hom ψ fun q : LowIdx Ψ N j => G q.1.1 q.1.2.1 q.1.2.2) :=
    MvPolynomial.ringHom_ext (fun a => by simp) fun q => by simp [c_sqsys.flag₀]
  rw [e]
  exact (algebraMap L (RatFunc L)).injective.comp h.2

theorem IsGenLow.flag₁ (h : IsGenLow ψ j G) (τ : Ψ) {ca cb : Fin N} (hc : (cb : ℕ) = ca + 1)
    (hS : ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j)) :
    IsGenLow ((algebraMap L (RatFunc L)).comp ψ) j (flag₁ G τ ca cb) := by
  refine ⟨fun τ' => ?_, ?_⟩
  · by_cases e : τ' = τ
    · subst e
      rw [c_sqsys.flag₁, Function.update_self]
      exact ⟨(h.flag₀.1 τ').1.mul (Pts.transv_block hS _), lowerUni_mul_transv (h.flag₀.1 τ').2 hc _⟩
    · rw [c_sqsys.flag₁, Function.update_of_ne e]
      exact h.flag₀.1 τ'
  · let P : LowIdx Ψ N j → Polynomial L := fun q => Polynomial.C (G q.1.1 q.1.2.1 q.1.2.2) +
      if q.1.1 = τ ∧ q.1.2.2 = ca then Polynomial.C (G q.1.1 q.1.2.1 cb) * Polynomial.X else 0
    have e : (eval₂Hom ((algebraMap L (RatFunc L)).comp ψ) fun q : LowIdx Ψ N j =>
        c_sqsys.flag₁ G τ ca cb q.1.1 q.1.2.1 q.1.2.2) =
        (algebraMap (Polynomial L) (RatFunc L)).comp (eval₂Hom (Polynomial.C.comp ψ) P) := by
      refine MvPolynomial.ringHom_ext (fun a => by simp) fun q => ?_
      simp only [eval₂Hom_X', RingHom.comp_apply, P, c_sqsys.flag₁]
      by_cases e : q.1.1 = τ
      · rw [e, Function.update_self, mul_transv_apply]
        by_cases e' : q.1.2.2 = ca <;> simp [e', c_sqsys.flag₀]
      · rw [Function.update_of_ne e]
        simp [e, c_sqsys.flag₀]
    have e2 : (Polynomial.evalRingHom 0).comp (eval₂Hom (Polynomial.C.comp ψ) P) =
        eval₂Hom ψ fun q : LowIdx Ψ N j => G q.1.1 q.1.2.1 q.1.2.2 := by
      refine MvPolynomial.ringHom_ext (fun a => by simp) fun q => ?_
      simp only [eval₂Hom_X', RingHom.comp_apply, P]
      split_ifs <;> simp
    rw [e]
    refine (IsFractionRing.injective (Polynomial L) (RatFunc L)).comp ?_
    have := h.2
    rw [← e2] at this
    exact Function.Injective.of_comp this

end Re

section Gen

variable {M : FlagModel y Ψ N j} {τ : Ψ} {a b : Fin N} {k₀ : K} {ca cb : Fin N}

theorem wCo_v₀ (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (k₀ : K) (ca cb : Fin N) :
    M.wCo p k₀ ca cb RatFunc.X ∘ v₀ k₀ =
      ptOf M ((algebraMap Φ (RatFunc Φ)).comp (algebraMap M.Ω Φ)) (flag₀ M.g) := by
  funext ⟨k, m⟩
  show algebraMap Φ (RatFunc Φ) (y ⟨k, m⟩) = _
  by_cases hk : ∀ p, M.blk p ≠ some k
  · exact (congrArg _ (M.y_base ⟨⟨k, hk⟩, m⟩)).trans
      (ptOf_base M ((algebraMap Φ (RatFunc Φ)).comp (algebraMap M.Ω Φ)) (flag₀ M.g) ⟨⟨k, hk⟩, m⟩).symm
  · push_neg at hk
    obtain ⟨p, hp⟩ := hk
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ptOf_step M _ _ p k hp, M.y_step p k hp, map_sum]
    exact Finset.sum_congr rfl fun I _ => by rw [map_mul, ← CPts.minorIJ_map]; rfl

theorem Sw.wCo_v₁ (S : Sw M τ a b k₀ ca cb) :
    M.wCo (τ, a) k₀ ca cb RatFunc.X ∘ v₁ k₀ =
      ptOf M ((algebraMap Φ (RatFunc Φ)).comp (algebraMap M.Ω Φ)) (flag₁ M.g τ ca cb) := by
  funext ⟨k, m⟩
  by_cases e : k = k₀
  · subst e
    show M.wCo (τ, a) k ca cb RatFunc.X (v₁ k ⟨k, m⟩) = _
    rw [v₁_self, ptOf_step M _ _ _ k S.hk]
    simp only [flag₁, Function.update_self]
    rfl
  · show M.wCo (τ, a) k₀ ca cb RatFunc.X (v₁ k₀ ⟨k, m⟩) = _
    rw [v₁_ne (p := ⟨k, m⟩) e]
    refine (congrFun (wCo_v₀ M (τ, a) k₀ ca cb) ⟨k, m⟩).trans ?_
    by_cases hk : ∀ p, M.blk p ≠ some k
    · exact (ptOf_base M _ _ ⟨⟨k, hk⟩, m⟩).trans (ptOf_base M _ _ ⟨⟨k, hk⟩, m⟩).symm
    · push_neg at hk
      obtain ⟨⟨τ', i⟩, hp⟩ := hk
      rw [ptOf_step M _ _ _ k hp, ptOf_step M _ _ _ k hp]
      by_cases e' : τ' = τ
      · subst e'
        have hi : i ≠ a := fun h => e (by rw [h, S.hk] at hp; exact (Option.some.inj hp).symm)
        simp only [flag₁, Function.update_self, minor_transv M.j_le S.hb S.hab S.hca S.hcb hi]
      · simp only [flag₁, Function.update_of_ne e']

end Gen

variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

def reCover {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) {L : Type} [Field L]
    (ψ : M'.Ω →+* L) (G : Ψ → Matrix (Fin N) (Fin N) L) (hG : IsGenLow ψ j G) : FlagCover (reModel M' ψ G hG) M where
  κ := Cv.κ
  v := Cv.v
  block := Cv.block
  φ := Cv.φ
  x_eq := Cv.x_eq
  deg_pos := Cv.deg_pos
  agree := Cv.agree

theorem transPt_eq {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) :
    ptOf M ((algebraMap M'.Ω Φ').comp Cv.φ) M'.g = transPt Cv := by
  funext ⟨k, m⟩
  by_cases hk : ∀ p, M.blk p ≠ some k
  · exact (ptOf_base M ((algebraMap M'.Ω Φ').comp Cv.φ) M'.g ⟨⟨k, hk⟩, m⟩).trans (transPt_base Cv ⟨⟨k, hk⟩, m⟩).symm
  · obtain ⟨p, hp⟩ : ∃ p, M.blk p = some k := by simpa using hk
    rw [ptOf_step M _ _ p k hp, transPt_step Cv p k hp]
    rfl

theorem isValueAt_pull {L : Type} [Field L] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v)
    {w : (Σ k, ι' k) → L} {z : (Σ k, ι' k) → ℂ} {s : L} {r : ℂ} (h : IsValueAt (w ∘ v) s (z ∘ v) r) :
    IsValueAt w s z r := by
  obtain ⟨d, g, h, hg, hh, h1, h2, h3, rfl⟩ := h
  refine ⟨_, rename v g, rename v h, CPts.isMultiHomog_rename_block hv hg, CPts.isMultiHomog_rename_block hv hh,
    ?_, ?_, ?_, ?_⟩
  · rwa [aeval_rename]
  · rwa [aeval_rename, aeval_rename]
  · rwa [CPts.eval_rename_block]
  · rw [CPts.eval_rename_block, CPts.eval_rename_block]

theorem blockFnField_comp_le {L : Type} [Field L] [CharZero L] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k}
    (hv : IsBlockMap κ v) (w : (Σ k, ι' k) → L) : blockFnField (w ∘ v) ≤ blockFnField w := by
  refine IntermediateField.adjoin.mono _ _ _ ?_
  rintro t ⟨p, q, h, rfl⟩
  exact ⟨v p, v q, by rw [hv.2.2.1, hv.2.2.1, h], rfl⟩

theorem val_img {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) {z : (Σ k, ι' k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y')) {w : (Σ k, ι k) → ℂ} (himg : IsImg Cv z w) (k : K) :
    ∃ (e : Φ') (s : ι k → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ i,
      transPt Cv ⟨k, i⟩ = e * s i ∧ IsValueAt y' (s i) z (t * w ⟨k, i⟩) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M'
  obtain ⟨-, g2, -⟩ := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  obtain ⟨F', hF', hG'⟩ := h2 _ (h1 z hz)
  obtain ⟨z₁, ho₁, hnorm⟩ := FibreCount.exists_normal_base M'.blk F'.c z fun k => FibreCount.chart_ne (hG'.1 k)
  have hz₁ := mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y') ho₁ hz
  have hG₁ : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) := by
    rw [FibreCount.mCoordIdeal_eq_of_orbit (FibreCount.basePart_orbit M'.blk ho₁)]; exact hG'
  obtain ⟨h, hh⟩ := (h3 F' hF' z₁ (h1 z₁ hz₁) hG₁ hnorm).1 hz₁
  have hv := GlobalTheory.T.flag_cover_base_point_maps_to_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ (h1 z₁ hz₁)
  obtain ⟨F, hF, hG⟩ := g2 _ hv
  obtain ⟨z₀, ho, hb, hfl⟩ := himg z₁ ho₁ F' F hF' hF hG₁ hG h hh
  obtain ⟨c, hc, ec⟩ := blocks_of_orbit ho k
  have hblk : ∃ (e : Φ') (s : ι k → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ i,
      transPt Cv ⟨k, i⟩ = e * s i ∧ IsValueAt y' (s i) z₁ (t * z₀ ⟨k, i⟩) := by
    by_cases hk : ∀ p, M.blk p ≠ some k
    · exact GlobalTheory.T.flag_cover_base_block_value K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z₁ z₀ ⟨k, hk⟩ hz₁ hb
    · obtain ⟨p, hp⟩ : ∃ p, M.blk p = some k := by simpa using hk
      exact GlobalTheory.T.flag_cover_frames_lift_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z₁ z₀ F' F h p k hz₁ hF' hF hG₁ hG hh hfl hb hp
  obtain ⟨e, s, t, he, ht, hs⟩ := hblk
  refine ⟨e, s, t * c, he, mul_ne_zero ht hc, fun i => ⟨(hs i).1, ?_⟩⟩
  rw [mul_assoc, ← ec]
  exact CovLift.isValueAt_orbit (hs i).2 (orbit_symm ho₁)

theorem ratio_mem {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) [CharZero Φ']
    (h : ∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) (k : K) (m m' : ι k) : transPt Cv ⟨k, m⟩ / transPt Cv ⟨k, m'⟩ ∈ blockFnField y' := by
  rw [GlobalTheory.T.flag_cover_block_field_eq K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv h]
  exact IntermediateField.subset_adjoin _ _ ⟨⟨.inl k, m⟩, ⟨.inl k, m'⟩, rfl, rfl⟩

theorem graph_alt {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) {τ : Ψ} {a b : Fin N} {k₀ : K}
    {k₀' : K'} {ca cb : Fin N} {d : ℕ} (S : Sw M τ a b k₀ ca cb) (S' : Sw M' τ a b k₀' ca cb)
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2)) :
    ∃ Pt : Ideal (MRing (Sum.elim (fun o : Option K => ι (o.getD k₀)) fun o : Option K' => ι' (o.getD k₀'))),
      IsArithVar Pt (d + 2 + 1) ∧ imageZ inlV Pt = mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ∧
      imageZ inrV Pt = mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X) ∧
      ∀ z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)),
        ∀ w ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)), RelW Cv k₀ k₀' z w → pairV w z ∈ mcPts Pt := by
  haveI : CharZero Φ' := charZero_of_injective_algebraMap (algebraMap M'.Ω Φ').injective
  haveI : CharZero (RatFunc Φ') := charZero_of_injective_algebraMap (algebraMap Φ' (RatFunc Φ')).injective
  obtain ⟨G, hG⟩ := exists_genLow M'
  have hG₀ := hG.flag₀
  have hG₁ := hG.flag₁ τ S.hcb (Pts.same_summand S.hb S.hab S.hca S.hcb)
  let ML := reModel M' _ G hG
  let MT := reModel M _ G (hG.restrict Cv.φ)
  have SL : Sw ML τ a b k₀' ca cb := ⟨S.hb, S.hab, S'.hk, S.hca, S.hcb, S.wa⟩
  have ST : Sw MT τ a b k₀ ca cb := ⟨S.hb, S.hab, S.hk, S.hca, S.hcb, S.wa⟩
  have eL := ideal_W_eq S' SL hy' (ideal_ptOf M' _ G hG)
  have eT := ideal_W_eq S ST hy (ideal_ptOf M _ G (hG.restrict Cv.φ))
  let C₀ := reCover Cv _ _ hG₀
  let C₁ := reCover Cv _ _ hG₁
  have e₀ := ideal_ptOf M' _ _ hG₀
  have e₁ := ideal_ptOf M' _ _ hG₁
  set w' := ML.wCo (τ, a) k₀' ca cb RatFunc.X with hw'
  set wT := MT.wCo (τ, a) k₀ ca cb RatFunc.X with hwT
  have l₀ : w' ∘ v₀ k₀' = ptOf M' ((algebraMap Φ' (RatFunc Φ')).comp (algebraMap M'.Ω Φ')) (flag₀ G) :=
    wCo_v₀ ML _ _ _ _
  have l₁ : w' ∘ v₁ k₀' = ptOf M' ((algebraMap Φ' (RatFunc Φ')).comp (algebraMap M'.Ω Φ')) (flag₁ G τ ca cb) :=
    SL.wCo_v₁
  have t₀ : wT ∘ v₀ k₀ = transPt C₀ := (wCo_v₀ MT (τ, a) k₀ ca cb).trans (transPt_eq C₀)
  have t₁ : wT ∘ v₁ k₀ = transPt C₁ := ST.wCo_v₁.trans (transPt_eq C₁)
  have t₀' : ∀ k m, wT ⟨some k, m⟩ = transPt C₀ ⟨k, m⟩ := fun k m => congrFun t₀ ⟨k, m⟩
  have t₁' : ∀ m, wT ⟨none, m⟩ = transPt C₁ ⟨k₀, m⟩ := fun m => by
    rw [← t₁, Function.comp, v₁_self]
  have aL : IsArithVar (mCoordIdeal w') (d + 2 + 1) := by rw [eL]; exact S'.arith hy'
  have aT : IsArithVar (mCoordIdeal wT) (d + 2 + 1) := by rw [eT]; exact S.arith hy
  have nz := fun {Kx : Type} [Fintype Kx] {ιx : Kx → Type} [∀ k, Fintype (ιx k)] (u : (Σ k, ιx k) → RatFunc Φ')
      (h : IsRelevant (mCoordIdeal u)) (k : Kx) => (show ∃ i, u ⟨k, i⟩ ≠ 0 from by
    obtain ⟨c, hc⟩ := HilbertSamuel.CoordArithOfFnField.nonzero_of_relevant u h
    exact ⟨c k, hc k⟩)
  have hnz : ∀ kk, ∃ i, pairV wT w' ⟨kk, i⟩ ≠ 0 := by
    rintro (k | k)
    · exact nz wT aT.2.1.2.2 k
    · exact nz w' aL.2.1.2.2 k
  have r₁ : ∀ m m' : ι k₀, wT ⟨none, m⟩ / wT ⟨none, m'⟩ ∈ blockFnField w' := fun m m' => by
    rw [t₁', t₁']
    refine blockFnField_comp_le (isBlockMap_v₁ k₀') w' ?_
    rw [l₁]
    exact ratio_mem C₁ (nz _ (by rw [e₁]; exact hy'.2.1.2.2)) k₀ m m'
  have r₀ : ∀ k (m m' : ι k), wT ⟨some k, m⟩ / wT ⟨some k, m'⟩ ∈ blockFnField w' := fun k m m' => by
    rw [t₀', t₀']
    refine blockFnField_comp_le (Pts.isBlockMap_v₀ k₀') w' ?_
    rw [l₀]
    exact ratio_mem C₀ (nz _ (by rw [e₀]; exact hy'.2.1.2.2)) k m m'
  refine ⟨mCoordIdeal (pairV wT w'), ?_, by rw [imageZ_inl, eT], by rw [imageZ_inr, eL], fun z hz w hw hr => ?_⟩
  · refine HilbertSamuel.CoordArithOfFnField.proof _ _ _ _ (RatFunc Φ') w' (pairV wT w') _ ⟨Sum.inr none⟩ hnz
      (le_antisymm (blockFnField_comp_le isBlockMap_inr (pairV wT w')) ?_) aL
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro t ⟨⟨k, m⟩, ⟨k', m'⟩, h, rfl⟩
    obtain rfl : k = k' := h
    rcases k with (_ | k) | k
    · exact r₁ m m'
    · exact r₀ k m m'
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨k, m⟩, ⟨k, m'⟩, rfl, rfl⟩
  · have hzL : z ∈ mcPts (mCoordIdeal w') := by rw [eL]; exact hz
    have hblk : ∀ kk, ∃ (e : RatFunc Φ') (s : Sum.elim (fun o : Option K => ι (o.getD k₀))
        (fun o : Option K' => ι' (o.getD k₀')) kk → RatFunc Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ i,
        pairV wT w' ⟨kk, i⟩ = e * s i ∧ IsValueAt w' (s i) z (t * pairV w z ⟨kk, i⟩) := by
      rintro ((_ | k) | k)
      · obtain ⟨e, s, t, he, ht, hs⟩ := val_img C₁ (z := sndPt k₀' z) (by rw [e₁]; exact S'.snd_mem hy' hz) hr.2 k₀
        refine ⟨e, s, t, he, ht, fun i => ⟨(t₁' i).trans (hs i).1, isValueAt_pull (isBlockMap_v₁ k₀') ?_⟩⟩
        have := (hs i).2
        rw [← l₁] at this
        exact (congrArg (fun r => IsValueAt (w' ∘ v₁ k₀') (s i) (z ∘ v₁ k₀') (t * r)) (Pts.snd_self w i)).mp this
      · obtain ⟨e, s, t, he, ht, hs⟩ := val_img C₀ (z := fstPt k₀' z) (by rw [e₀]; exact fst_mem hz) hr.1 k
        refine ⟨e, s, t, he, ht, fun i => ⟨(t₀' k i).trans (hs i).1, isValueAt_pull (Pts.isBlockMap_v₀ k₀') ?_⟩⟩
        have := (hs i).2
        rw [← l₀] at this
        exact this
      · obtain ⟨c, hc⟩ := hz.1 k
        obtain ⟨hy0, hval⟩ := GlobalTheory.T.coordinate_ratio_value_at_point _ _ _ w' z k c hzL hc
        exact ⟨w' ⟨k, c⟩, fun i => w' ⟨k, i⟩ / w' ⟨k, c⟩, (z ⟨k, c⟩)⁻¹, hy0, inv_ne_zero hc,
          fun i => ⟨(mul_div_cancel₀ _ hy0).symm, hval i⟩⟩
    choose e s t he ht hs using hblk
    refine GlobalTheory.T.scaled_coordinates_value_at_point _ _ _ _ _ (pairV wT w') w' z (pairV w z) e (fun q => s q.1 q.2) t hzL ?_ he ht
      (fun q => (hs q.1 q.2).1) (fun q => (hs q.1 q.2).2)
    rintro (k | k)
    · exact hw.1 k
    · exact hz.1 k

end PositivityTheory.Xgp.c_sqsys
