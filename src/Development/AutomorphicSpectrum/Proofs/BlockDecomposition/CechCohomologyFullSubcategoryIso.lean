module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.CechAugRowU
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIntegralMultipleBoundedPlaces
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechCohomologyFullSubcategoryIso
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechCohomologyFullSubcategoryIso
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

universe u v w

namespace GlobalTheory.CompanionTheory.CechFull

section Complexes

variable {R : Type} [CommRing R]

theorem mapH_mapH_of_inv {K : Cx.{w} R} {L : Cx.{w} R} (φ : Cx.Hom K L (RingHom.id R))
    (ψ : Cx.Hom L K (RingHom.id R)) (h : ∀ n x, ψ.f n (φ.f n x) = x) (p : ℕ) (x : K.H p) :
    ψ.mapH p (φ.mapH p x) = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (ψ.mapZ p (φ.mapZ p z)) = Submodule.Quotient.mk z
  exact congrArg _ (Subtype.ext (h p z.1))

def equivH {K : Cx.{w} R} {L : Cx.{w} R} (φ : Cx.Hom K L (RingHom.id R)) (ψ : Cx.Hom L K (RingHom.id R))
    (h : ∀ n x, ψ.f n (φ.f n x) = x) (h' : ∀ n x, φ.f n (ψ.f n x) = x) (p : ℕ) : K.H p ≃ₗ[R] L.H p :=
  LinearEquiv.ofLinear (φ.mapH p) (ψ.mapH p)
    (LinearMap.ext (mapH_mapH_of_inv ψ φ h' p)) (LinearMap.ext (mapH_mapH_of_inv φ ψ h p))

def cosHom {K L : Cos.{w} R} (f : ∀ n, K.X n →ₗ[R] L.X n)
    (h : ∀ n k x, L.δ n k (f n x) = f (n + 1) (K.δ n k x)) : Cx.Hom K.cx L.cx (RingHom.id R) :=
  ⟨f, fun n x => by
    change L.d n (f n x) = f (n + 1) (K.d n x)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Cos.d_apply, Cos.d_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_zsmul, h]⟩

end Complexes

section Cat

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem pull_pull_of_inv {C' : Type u} [Category.{v} C'] {G : C ⥤ ModuleCat.{w} R} {G' : C' ⥤ ModuleCat.{w} R}
    (m : CH.Mor G G' (RingHom.id R)) (m' : CH.Mor G' G (RingHom.id R))
    (h : ∀ n f, m'.pullC n (m.pullC n f) = f) (p : ℕ) (x : CH.H G p) : m'.pull p (m.pull p x) = x :=
  mapH_mapH_of_inv m.hom m'.hom h p x

variable (F : C ⥤ ModuleCat.{w} R) (Q : ObjectProperty C) {ι : Type} (W : ι → ObjectProperty C)

abbrev subFam : ι → ObjectProperty Q.FullSubcategory := fun α T => W α T.obj

variable {Q W}

def upG (hW : ∀ α, W α ≤ Q) {n : ℕ} (i : Fin (n + 1) → ι) :
    (capT W i).FullSubcategory ⥤ (capT (subFam Q W) i).FullSubcategory :=
  (capT (subFam Q W) i).lift (Q.lift (capT W i).ι fun T => hW (i 0) _ (T.property 0)) fun T => T.property

def downG {n : ℕ} (i : Fin (n + 1) → ι) :
    (capT (subFam Q W) i).FullSubcategory ⥤ (capT W i).FullSubcategory :=
  (capT W i).lift ((capT (subFam Q W) i).ι ⋙ Q.ι) fun T => T.property

def upM (hW : ∀ α, W α ≤ Q) {n : ℕ} (i : Fin (n + 1) → ι) :
    CH.Mor ((capT (subFam Q W) i).ι ⋙ Q.ι ⋙ F) ((capT W i).ι ⋙ F) (RingHom.id R) where
  G := upG hW i
  τ _ := LinearMap.id
  nat _ _ := rfl

def downM {n : ℕ} (i : Fin (n + 1) → ι) :
    CH.Mor ((capT W i).ι ⋙ F) ((capT (subFam Q W) i).ι ⋙ Q.ι ⋙ F) (RingHom.id R) where
  G := downG i
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem down_up_pullC (hW : ∀ α, W α ≤ Q) {n : ℕ} (i : Fin (n + 1) → ι) (m : ℕ)
    (f : CH.Cn ((capT (subFam Q W) i).ι ⋙ Q.ι ⋙ F) m) :
    (downM F i).pullC m ((upM F hW i).pullC m f) = f := rfl

theorem up_down_pullC (hW : ∀ α, W α ≤ Q) {n : ℕ} (i : Fin (n + 1) → ι) (m : ℕ)
    (f : CH.Cn ((capT W i).ι ⋙ F) m) :
    (upM F hW i).pullC m ((downM F i).pullC m f) = f := rfl

end Cat

section Assemble

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]
  (F : C ⥤ ModuleCat.{w} R) {Q : ObjectProperty C} {ι : Type} {W : ι → ObjectProperty C}

def upX (hW : ∀ α, W α ≤ Q) (q n : ℕ) :
    (cechH (Q.ι ⋙ F) (subFam Q W) q).X n →ₗ[R] (cechH F W q).X n :=
  LinearMap.pi fun i => ((upM F hW i).pull q).comp (LinearMap.proj i)

def downX (q n : ℕ) :
    (cechH F W q).X n →ₗ[R] (cechH (Q.ι ⋙ F) (subFam Q W) q).X n :=
  LinearMap.pi fun i => ((downM F i).pull q).comp (LinearMap.proj i)

theorem upX_δ (hW : ∀ α, W α ≤ Q) (q n : ℕ) (k : Fin (n + 2))
    (x : (cechH (Q.ι ⋙ F) (subFam Q W) q).X n) :
    (cechH F W q).δ n k (upX F hW q n x) = upX F hW q (n + 1) ((cechH (Q.ι ⋙ F) (subFam Q W) q).δ n k x) := by
  funext t
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (x (t ∘ k.succAbove))
  change (resU F _).pull q ((upM F hW (t ∘ k.succAbove)).pull q (x (t ∘ k.succAbove))) =
    (upM F hW t).pull q ((resU (Q.ι ⋙ F) _).pull q (x (t ∘ k.succAbove)))
  rw [← hz]
  rfl

theorem downX_δ (q n : ℕ) (k : Fin (n + 2)) (x : (cechH F W q).X n) :
    (cechH (Q.ι ⋙ F) (subFam Q W) q).δ n k (downX (Q := Q) F q n x) =
      downX (Q := Q) F q (n + 1) ((cechH F W q).δ n k x) := by
  funext t
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (x (t ∘ k.succAbove))
  change (resU (Q.ι ⋙ F) _).pull q ((downM F (t ∘ k.succAbove)).pull q (x (t ∘ k.succAbove))) =
    (downM F t).pull q ((resU F _).pull q (x (t ∘ k.succAbove)))
  rw [← hz]
  rfl

end Assemble

theorem cechH_fullSubcategory_H : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    (Q : ObjectProperty C) {ι : Type} (W : ι → ObjectProperty C), (∀ α, W α ≤ Q) → ∀ q p,
    Nonempty ((cechH (Q.ι ⋙ F) (fun α (T : Q.FullSubcategory) => W α T.obj) q).cx.H p ≃ₗ[R] (cechH F W q).cx.H p) := by
  intro R _ C _ F Q ι W hW q p
  exact ⟨equivH (cosHom (upX F hW q) (upX_δ F hW q)) (cosHom (downX (Q := Q) F q) (downX_δ F q))
    (fun n x => funext fun i => pull_pull_of_inv (upM F hW i) (downM F i) (down_up_pullC F hW i) q (x i))
    (fun n x => funext fun i => pull_pull_of_inv (downM F i) (upM F hW i) (up_down_pullC F hW i) q (x i)) p⟩

end GlobalTheory.CompanionTheory.CechFull
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechCohomologyFullSubcategoryIsoStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
universe u v w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_cohomology_full_subcategory_iso : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) (Q : ObjectProperty C) {ι : Type} (W : ι → ObjectProperty C), (∀ α, W α ≤ Q) → ∀ q p, Nonempty ((cechH (Q.ι ⋙ F) (fun α (T : Q.FullSubcategory) => W α T.obj) q).cx.H p ≃ₗ[R] (cechH F W q).cx.H p) := by
  first | exact @GlobalTheory.CompanionTheory.CechFull.cechH_fullSubcategory_H | exact GlobalTheory.CompanionTheory.CechFull.cechH_fullSubcategory_H | (intros; apply GlobalTheory.CompanionTheory.CechFull.cechH_fullSubcategory_H <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumNeZeroEqSum
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem support_finite (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (T : Finset (HeightOneSpectrum (𝓞 F))) (K : Set (Ainf F))
    (hK : IsCompact K) (Kv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hKv : ∀ v ∈ T, IsCompact (Kv v))
    (δ : ℝ) (hδ : 0 < δ) :
    {x : F | x ≠ 0 ∧ x ∈ IntOut T ∧ θ δ * algebraMap F (Ainf F) x ∈ K ∧
      ∀ v ∈ T, algebraMap F (Fv F v) x ∈ Kv v}.Finite := by
  obtain ⟨N, hN, hNx⟩ := GlobalTheory.T.exists_integral_multiple_bounded_places F T Kv hKv
  obtain ⟨C0, h⟩ := hC F hF θ hθ K hK N hN
  refine ((h δ hδ ⊤ top_ne_bot).1).subset ?_
  rintro x ⟨h0, h1, h2, h3⟩
  obtain ⟨y, hy⟩ := hNx x h1 h3
  exact ⟨h0, ⟨y, Submodule.mem_top, hy⟩, h2⟩

theorem tsum_ne_zero_eq_sum {F : Type} [Field F] (h : F → ℝ) (B : Finset F) (hB : ∀ x ∈ B, x ≠ 0)
    (hh : ∀ x, x ≠ 0 → x ∉ B → h x = 0) :
    ∑' β : {β : F // β ≠ 0}, h β.1 = ∑ x ∈ B, h x := by
  have h1 : ∑' β : {β : F // β ≠ 0}, h β.1 = ∑ β ∈ B.subtype (fun x => x ≠ 0), h β.1 := by
    refine tsum_eq_sum ?_
    intro b hb
    exact hh b.1 b.2 (by simpa [Finset.mem_subtype] using hb)
  rw [h1]
  refine Finset.sum_bij (fun b _ => b.1) ?_ ?_ ?_ ?_
  · intro a ha; simpa [Finset.mem_subtype] using ha
  · intro a _ b _ hab; exact Subtype.ext hab
  · intro b hb; exact ⟨⟨b, hB b hb⟩, by simpa [Finset.mem_subtype] using hb, rfl⟩
  · intro a _; rfl

theorem truncTerm_finite (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (hGc : HasCompactSupport G)
    (hψ : ∀ v ∈ T, HasCompactSupport (ψ v)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : Finset F, (∀ x ∈ B, x ≠ 0) ∧ ∀ x, x ≠ 0 → x ∉ B → (IntOut T).indicator
      (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, ψ v (algebraMap F (Fv F v) x)) x = 0 := by
  have hfin := support_finite hC F hF θ hθ T (tsupport G) hGc (fun v => tsupport (ψ v)) hψ δ hδ
  refine ⟨hfin.toFinset, fun x hx => ((hfin.mem_toFinset).1 hx).1, ?_⟩
  intro x hx0 hxB
  by_cases hxT : x ∈ IntOut T
  · rw [Set.indicator_of_mem hxT]
    by_cases h1 : θ δ * algebraMap F (Ainf F) x ∈ tsupport G
    · have : ∃ v ∈ T, algebraMap F (Fv F v) x ∉ tsupport (ψ v) := by
        by_contra hcon
        push_neg at hcon
        exact hxB ((hfin.mem_toFinset).2 ⟨hx0, hxT, h1, hcon⟩)
      obtain ⟨v, hv, hvx⟩ := this
      have h0 : ψ v (algebraMap F (Fv F v) x) = 0 := image_eq_zero_of_notMem_tsupport hvx
      rw [Finset.prod_eq_zero hv h0, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
  · exact Set.indicator_of_notMem hxT _

theorem truncTerm_summable (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (hGc : HasCompactSupport G)
    (hψ : ∀ v ∈ T, HasCompactSupport (ψ v)) (δ : ℝ) (hδ : 0 < δ) :
    Summable fun β : {β : F // β ≠ 0} => (IntOut T).indicator
      (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, ψ v (algebraMap F (Fv F v) x)) β.1 := by
  obtain ⟨B, hB, hh⟩ := truncTerm_finite hC F hF θ hθ T G ψ hGc hψ δ hδ
  refine summable_of_ne_finset_zero (s := B.subtype (fun x => x ≠ 0)) ?_
  intro b hb
  exact hh b.1 b.2 (by simpa [Finset.mem_subtype] using hb)

end GlobalTheory.CompanionTheory.Mass.MeanV

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalRiemannExtensionLocal
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Branch

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets MvPolynomial Topology Filter Metric

theorem normalRiemannExtensionLocal (hud : LocalUniversalDenominator.Statement)
    (hbq : NormalBoundedQuotient.Statement) (hvan : VanishNearPoint.Statement) :
    NormalRiemannExtensionLocal.Statement := by
  intro σ _ I h w U f hI hIc hh hw hU hf hb
  classical
  have hpoly : ∀ q : MvPolynomial σ ℂ, Differentiable ℂ (fun z : σ → ℂ => eval z q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [eval_add]; exact hp.add hq
    | mul_X p i hp => simp only [eval_mul, eval_X]; exact hp.mul (differentiable_apply i)
  obtain ⟨g, hg, N, hNo, hwN, hNU, F, hF, hFg⟩ := hud σ I h w U f hI hh hw hU hf hb
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  have hhg : h * g ∉ I := fun hm => (hI.mem_or_mem hm).elim hh hg
  obtain ⟨B, hBo, hwB, hBN, hdense⟩ : ∃ B : Set (σ → ℂ), IsOpen B ∧ w ∈ B ∧ B ⊆ N ∧
      zeroSetIn I ∩ B ⊆ closure ((zeroSetIn I ∩ B) \ {z | eval z (h * g) = 0}) := by
    refine ⟨N, hNo, hwN, subset_rfl, fun z hz => ?_⟩
    have h1 := hNo.inter_closure ⟨hz.2, zeroSetIn_subset_closure_diff hvan I (h * g) hI hhg hz.1⟩
    refine closure_mono (fun y hy => ?_) h1
    exact ⟨⟨hy.2.1, hy.1⟩, hy.2.2⟩
  set T := (zeroSetIn I ∩ B) \ {z | eval z (h * g) = 0} with hT
  have hGd : Differentiable ℂ (fun z : σ → ℂ => eval z g) := hpoly g

  have hTS : ∀ z ∈ T, z ∈ (zeroSetIn I ∩ U) \ {z | eval z h = 0} ∧ eval z g ≠ 0 ∧
      eval z g * f z = F z := by
    intro z hz
    have hz2 : eval z h ≠ 0 ∧ eval z g ≠ 0 := by
      simpa only [Set.mem_ofPred_eq, eval_mul, mul_eq_zero, not_or] using hz.2
    exact ⟨⟨⟨hz.1.1, hNU (hBN hz.1.2)⟩, hz2.1⟩, hz2.2,
      hFg z ⟨⟨hz.1.1, hBN hz.1.2⟩, hz2.1⟩⟩
  have hTf : ∀ z ∈ T, F z / eval z g = f z := fun z hz => by
    obtain ⟨-, hg0, he⟩ := hTS z hz
    rw [← he, mul_div_cancel_left₀ _ hg0]
  have hbound : (fun z => F z / eval z g) '' ((zeroSetIn I ∩ B) \ {z | eval z g = 0}) ⊆
      Metric.closedBall 0 M := by
    rintro _ ⟨p, hp, rfl⟩
    have hpc : p ∈ closure T := hdense hp.1
    have hcont : ContinuousWithinAt (fun z => F z / eval z g) T p :=
      (((hF.continuousOn.continuousAt (hNo.mem_nhds (hBN hp.1.2))).div
        (hGd p).continuousAt hp.2)).continuousWithinAt
    refine closure_minimal ?_ Metric.isClosed_closedBall (hcont.mem_closure_image hpc)
    rintro _ ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    show ‖F z / eval z g‖ ≤ M
    rw [hTf z hz]
    exact hM _ ⟨z, (hTS z hz).1, rfl⟩
  have hnv : ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → eval z g = 0) := by
    intro hev
    obtain ⟨z, hzW, hzT⟩ := mem_closure_iff_nhds.1 (hdense ⟨hw, hwB⟩) _ hev
    exact (hTS z hzT).2.1 (hzW hzT.1.1)
  obtain ⟨V, hVo, hwV, H, hH, hFGH⟩ := hbq σ I w B F (fun z => eval z g) hI hIc hw hBo hwB
    (hF.mono hBN) hGd.differentiableOn hnv ((Metric.isBounded_closedBall).subset hbound)
  refine ⟨V ∩ B, hVo.inter hBo, ⟨hwV, hwB⟩, fun z hz => hNU (hBN hz.2), H, hH.mono Set.inter_subset_left, ?_⟩
  intro p hp
  obtain ⟨Up, hUpo, hpUp, Fp, hFp, hfFp⟩ :=
    hf p ⟨⟨hp.1.1, hNU (hBN hp.1.2.2)⟩, hp.2⟩
  rw [hfFp ⟨⟨⟨hp.1.1, hNU (hBN hp.1.2.2)⟩, hp.2⟩, hpUp⟩]

  set O := V ∩ Up
  have hOo : IsOpen O := hVo.inter hUpo
  have hpO : p ∈ O := ⟨hp.1.2.1, hpUp⟩
  set s := O ∩ T
  have heq : Set.EqOn H Fp s := by
    intro z hz
    obtain ⟨hzS, hg0, he⟩ := hTS z hz.2
    have h1 : eval z g * H z = eval z g * f z := by
      rw [he, hFGH z ⟨hz.2.1.1, hz.1.1⟩]
    rw [mul_left_cancel₀ hg0 h1, hfFp ⟨hzS, hz.1.2⟩]
  have hsO : insert p s ⊆ O := Set.insert_subset_iff.2 ⟨hpO, fun z hz => hz.1⟩
  exact heq.of_subset_closure ((hH.mono Set.inter_subset_left).continuousOn.mono hsO)
    ((hFp.mono Set.inter_subset_right).continuousOn.mono hsO) (Set.subset_insert p s)
    (Set.insert_subset_iff.2 ⟨hOo.inter_closure ⟨hpO, hdense ⟨hp.1.1, hp.1.2.2⟩⟩, subset_closure⟩)
    (Set.mem_insert p s)

theorem irreducibleGermCurve
    (hslice : ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w →
      GermIrreducibleAt X w → AccPt w (𝓟 X) →
      ∃ (Y W : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), W ∈ 𝓝 w ∧ Y ∩ W ⊆ X ∧
        IsAnalyticNear Y w ∧ GermIrreducibleAt Y w ∧ (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) ∧
        ∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) →
          ∀ᶠ y in 𝓝 (A w), h y = 0)
    (hdisc : ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ)
      (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), IsAnalyticNear Y w → GermIrreducibleAt Y w →
      (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) →
      (∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) →
          ∀ᶠ y in 𝓝 (A w), h y = 0) →
      ∃ (Y' : Set (σ → ℂ)) (p : (σ → ℂ) →L[ℂ] ℂ) (ρ : ℝ) (N : ℕ), Y' ⊆ Y ∧ IsCentredDiscCover Y' w p ρ N)
    (hCv : CentredDiscCoverCurve.Statement) : IrreducibleGermCurve.Statement := by
  intro σ _ X w hX hirr hacc
  obtain ⟨Y, W, A, hW, hYX, hYa, hYi, hiso, hdom⟩ := hslice σ X w hX hirr hacc
  obtain ⟨Y', p, ρ, N, hY'Y, hcov⟩ := hdisc σ Y w A hYa hYi hiso hdom
  obtain ⟨r, hr, γ, hγd, hγi, hγ0, hγY⟩ := hCv σ Y' w p ρ N hcov
  have hcont : ContinuousAt γ 0 := hγd.continuousOn.continuousAt (ball_mem_nhds 0 hr)
  have hpre : γ ⁻¹' W ∈ 𝓝 (0 : ℂ) := hcont.preimage_mem_nhds (by rw [hγ0]; exact hW)
  obtain ⟨r', hr', hsub⟩ := Metric.mem_nhds_iff.1 (inter_mem hpre (ball_mem_nhds (0 : ℂ) hr))
  have hle : ball (0 : ℂ) r' ⊆ ball 0 r := fun t ht => (hsub ht).2
  exact ⟨r', hr', γ, hγd.mono hle, hγi.mono hle, hγ0,
    fun t ht => hYX ⟨hY'Y (hγY (hle ht)), (hsub ht).1⟩⟩

end GlobalTheory.CompanionTheory.Ar.Branch
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DvMemOf
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeCech

universe w

variable {R : Type} [CommRing R]

structure DFil (K : DCx.{w} R) where
  L : ℤ → ∀ p q, Submodule R (K.X p q)
  mem_h : ∀ r p q x, x ∈ L r p q → K.dh p q x ∈ L r (p + 1) q
  mem_v : ∀ r p q x, x ∈ L r p q → K.dv p q x ∈ L r p (q + 1)
  anti : ∀ {r r' : ℤ}, r ≤ r' → ∀ p q, L r' p q ≤ L r p q

def DFil.Ex {K : DCx.{w} R} (F : DFil K) (r : ℤ) (p : ℕ) : ℕ → Prop
  | 0 => ∀ x ∈ F.L r p 0, K.dv p 0 x ∈ F.L (r + 1) p 1 → x ∈ F.L (r + 1) p 0
  | q + 1 => ∀ x ∈ F.L r p (q + 1), K.dv p (q + 1) x ∈ F.L (r + 1) p (q + 2) →
      ∃ v ∈ F.L r p q, x - K.dv p q v ∈ F.L (r + 1) p (q + 1)

variable {K : DCx.{w} R} (F : DFil K)

theorem sgl_mem {r : ℤ} {p q : ℕ} {x : K.X p q} (hx : x ∈ F.L r p q) (a b : ℕ) : K.sgl p q x a b ∈ F.L r a b := by
  by_cases h : a = p ∧ b = q
  · obtain ⟨rfl, rfl⟩ := h
    rwa [K.sgl_self]
  · rw [K.sgl_ne x (by omega)]
    exact zero_mem _

theorem dv_mem_of {r : ℤ} {e q : ℕ} (y : ∀ p q, K.X p q) (h1 : K.D y e (q + 1) ∈ F.L r e (q + 1))
    (h2 : ∀ e', e = e' + 1 → y e' (q + 1) ∈ F.L r e' (q + 1)) : K.dv e q (y e q) ∈ F.L r e (q + 1) := by
  have h3 : K.Dh y e (q + 1) ∈ F.L r e (q + 1) := by
    cases e with
    | zero => exact zero_mem _
    | succ e => exact F.mem_h _ _ _ _ (h2 e rfl)
  rw [K.D_apply] at h1
  have h4 : (-1 : ℤ) ^ e • K.dv e q (y e q) ∈ F.L r e (q + 1) := (Submodule.add_mem_iff_right _ h3).1 h1
  rcases neg_one_pow_eq_or ℤ e with h | h <;> rw [h] at h4 <;> simpa using h4

theorem kill (r : ℤ) (m : ℕ) (y : ∀ p q, K.X p q) (hy : y ∈ K.T (m + 1)) (hyL : ∀ p q, y p q ∈ F.L r p q) :
    ∀ e : ℕ, (∀ p q, p < e → K.D y p q ∈ F.L (r + 1) p q) → (∀ p q, p < e → p + q = m + 1 → F.Ex r p q) →
      ∃ w ∈ K.T m, (∀ p q, e ≤ p → w p q = 0) ∧ (∀ p q, (y - K.D w) p q ∈ F.L r p q) ∧
        ∀ p q, p < e → (y - K.D w) p q ∈ F.L (r + 1) p q := by
  intro e
  induction e with
  | zero =>
    intro _ _
    refine ⟨0, zero_mem _, fun _ _ _ => rfl, fun p q => ?_, fun p q h => absurd h (by omega)⟩
    simpa using hyL p q
  | succ e ih =>
    intro hD hE
    obtain ⟨w, hwT, hw0, hwL, hwL'⟩ := ih (fun p q hp => hD p q (by omega)) (fun p q hp => hE p q (by omega))
    have hyT : y - K.D w ∈ K.T (m + 1) := sub_mem hy (K.D_mem m w hwT)
    have hDy : K.D (y - K.D w) = K.D y := by rw [map_sub, K.DD, sub_zero]
    generalize hy' : y - K.D w = y' at hyT hDy hwL hwL'
    by_cases he : e ≤ m + 1
    · obtain ⟨q, hq⟩ : ∃ q, e + q = m + 1 := ⟨m + 1 - e, by omega⟩
      have hx : K.dv e q (y' e q) ∈ F.L (r + 1) e (q + 1) :=
        dv_mem_of F y' (by rw [hDy]; exact hD e (q + 1) (by omega)) (fun e' h => hwL' e' (q + 1) (by omega))
      have hEx := hE e q (by omega) hq
      cases q with
      | zero =>
        have hx0 : y' e 0 ∈ F.L (r + 1) e 0 := hEx _ (hwL e 0) hx
        refine ⟨w, hwT, fun p q h => hw0 p q (by omega), by rw [hy']; exact hwL, fun p q hp => ?_⟩
        rw [hy']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
        · exact hwL' p q hp
        · by_cases hq0 : q = 0
          · subst hq0; exact hx0
          · rw [hyT p q (by omega)]; exact zero_mem _
      | succ q =>
        obtain ⟨v, hv, hxv⟩ := hEx _ (hwL e (q + 1)) hx
        have hDu : K.D ((-1 : ℤ) ^ e • K.sgl e q v) =
            (-1 : ℤ) ^ e • K.sgl (e + 1) q (K.dh e q v) + K.sgl e (q + 1) (K.dv e q v) := by
          rw [map_zsmul, K.D_sgl, smul_add, smul_smul, ← pow_add, ← two_mul, pow_mul]
          simp
        have hval : ∀ p q', (y - K.D (w + (-1 : ℤ) ^ e • K.sgl e q v)) p q' =
            y' p q' - (-1 : ℤ) ^ e • K.sgl (e + 1) q (K.dh e q v) p q' - K.sgl e (q + 1) (K.dv e q v) p q' := by
          intro p q'
          rw [map_add (f := _), hDu, ← sub_sub, hy']
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
          abel
        refine ⟨w + (-1 : ℤ) ^ e • K.sgl e q v, add_mem hwT (?_), fun p q' h => ?_, fun p q' => ?_, fun p q' hp => ?_⟩
        · refine (K.T m).smul_of_tower_mem _ ?_
          intro a b hab
          exact K.sgl_ne v (by omega)
        · simp only [Pi.add_apply, Pi.smul_apply]
          rw [hw0 p q' (by omega), K.sgl_ne v (Or.inl (by omega))]
          simp
        · rw [hval]
          exact sub_mem (sub_mem (hwL p q') ((F.L r p q').smul_of_tower_mem _ (sgl_mem F (F.mem_h _ _ _ _ hv) p q')))
            (sgl_mem F (F.mem_v _ _ _ _ hv) p q')
        · rw [hval]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
          · rw [K.sgl_ne _ (Or.inl (by omega)), K.sgl_ne _ (Or.inl (by omega))]
            simpa using hwL' p q' hp
          · rw [K.sgl_ne _ (Or.inl (by omega))]
            by_cases hq0 : q' = q + 1
            · subst hq0
              rw [K.sgl_self]
              simpa using hxv
            · rw [K.sgl_ne _ (Or.inr hq0), hyT p q' (by omega)]
              simp
    · refine ⟨w, hwT, fun p q h => hw0 p q (by omega), by rw [hy']; exact hwL, fun p q hp => ?_⟩
      rw [hy']
      rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
      · exact hwL' p q hp
      · rw [hyT p q (by omega)]; exact zero_mem _

theorem stair_up (n : ℕ) (hTop : ∀ p q, F.L 0 p q = ⊤) (hV : ∀ p q, n + 1 < p → Subsingleton (K.X p q))
    (hE : ∀ (r : ℕ) p q, q ≠ r → F.Ex (r : ℤ) p q) (P : K.X (n + 1) (n + 1)) (hP : P ∈ F.L ((n : ℤ) + 1) (n + 1) (n + 1))
    (y0 : ∀ p q, K.X p q) (hy0 : y0 ∈ K.T (2 * n + 1)) (hD : K.D y0 = K.sgl (n + 1) (n + 1) P) (r : ℕ) (hr : r ≤ n) :
    ∃ y ∈ K.T (2 * n + 1), K.D y = K.sgl (n + 1) (n + 1) P ∧ ∀ p q, y p q ∈ F.L (r : ℤ) p q := by
  induction r with
  | zero =>
    refine ⟨y0, hy0, hD, fun p q => ?_⟩
    rw [Nat.cast_zero, hTop]
    trivial
  | succ r ih =>
    obtain ⟨y, hyT, hDy, hyL⟩ := ih (by omega)
    have hPr : P ∈ F.L ((r : ℤ) + 1) (n + 1) (n + 1) := F.anti (by omega) _ _ hP
    obtain ⟨w, hwT, -, hwL, hwL'⟩ := kill F (r : ℤ) (2 * n) y hyT hyL (n + 2)
      (fun p q _ => by rw [hDy]; exact sgl_mem F hPr p q)
      (fun p q hp hq => hE r p q (by omega))
    refine ⟨y - K.D w, sub_mem hyT (K.D_mem _ w hwT), by rw [map_sub, K.DD, sub_zero, hDy], fun p q => ?_⟩
    rw [Nat.cast_succ]
    by_cases hp : p < n + 2
    · exact hwL' p q hp
    · have := hV p q (by omega)
      rw [Subsingleton.elim ((y - K.D w) p q) 0]
      exact zero_mem _

theorem stair (n : ℕ) (hTop : ∀ p q, F.L 0 p q = ⊤) (hV : ∀ p q, n + 1 < p → Subsingleton (K.X p q))
    (hE : ∀ (r : ℕ) p q, q ≠ r → F.Ex (r : ℤ) p q) (P : K.X (n + 1) (n + 1)) (hP : P ∈ F.L ((n : ℤ) + 1) (n + 1) (n + 1))
    (y0 : ∀ p q, K.X p q) (hy0 : y0 ∈ K.T (2 * n + 1)) (hD : K.D y0 = K.sgl (n + 1) (n + 1) P) :
    ∃ (ω : K.X n (n + 1)) (f : K.X (n + 1) n), ω ∈ F.L ((n : ℤ) + 1) n (n + 1) ∧
      K.dv n (n + 1) ω ∈ F.L ((n : ℤ) + 1 + 1) n (n + 2) ∧ f ∈ F.L (n : ℤ) (n + 1) n ∧
      P = K.dh n (n + 1) ω + (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n f := by
  obtain ⟨y, hyT, hDy, hyL⟩ := stair_up F n hTop hV hE P hP y0 hy0 hD n le_rfl

  obtain ⟨w, hwT, -, hwL, hwL'⟩ := kill F (n : ℤ) (2 * n) y hyT hyL (n + 1)
    (fun p q _ => by rw [hDy]; exact sgl_mem F hP p q) (fun p q hp hq => hE n p q (by omega))
  have hy1T : y - K.D w ∈ K.T (2 * n + 1) := sub_mem hyT (K.D_mem _ w hwT)
  have hDy1 : K.D (y - K.D w) = K.sgl (n + 1) (n + 1) P := by rw [map_sub, K.DD, sub_zero, hDy]
  generalize y - K.D w = y1 at hy1T hDy1 hwL hwL'

  have htT : y1 - K.sgl (n + 1) n (y1 (n + 1) n) ∈ K.T (2 * n + 1) :=
    sub_mem hy1T fun a b hab => K.sgl_ne _ (by omega)
  have hDt : K.D (y1 - K.sgl (n + 1) n (y1 (n + 1) n)) =
      K.sgl (n + 1) (n + 1) (P - (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n (y1 (n + 1) n)) := by
    have := hV (n + 2) n (by omega)
    rw [map_sub, K.D_sgl, hDy1, Subsingleton.elim (K.dh (n + 1) n (y1 (n + 1) n)) 0, map_zero, zero_add, map_sub, map_zsmul]
  have htL : ∀ p q, (y1 - K.sgl (n + 1) n (y1 (n + 1) n)) p q ∈ F.L ((n : ℤ) + 1) p q := by
    intro p q
    rw [Pi.sub_apply, Pi.sub_apply]
    by_cases hp : p < n + 1
    · rw [K.sgl_ne _ (Or.inl (by omega)), sub_zero]
      exact hwL' p q hp
    · by_cases hp' : p = n + 1
      · subst hp'
        by_cases hq : q = n
        · subst hq
          rw [K.sgl_self, sub_self]
          exact zero_mem _
        · rw [K.sgl_ne _ (Or.inr hq), hy1T _ _ (by omega), sub_zero]
          exact zero_mem _
      · have := hV p q (by omega)
        rw [Subsingleton.elim (y1 p q - K.sgl (n + 1) n (y1 (n + 1) n) p q) 0]
        exact zero_mem _
  have ecast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; rfl
  obtain ⟨w2, hw2T, hw20, hw2L, hw2L'⟩ := kill F ((n : ℤ) + 1) (2 * n) _ htT htL n
    (fun p q hp => by
      rw [hDt, K.sgl_ne _ (Or.inl (by omega))]
      exact zero_mem _)
    (fun p q hp hq => by
      have := hE (n + 1) p q (by omega)
      rwa [ecast] at this)
  have hDt' : K.D ((y1 - K.sgl (n + 1) n (y1 (n + 1) n)) - K.D w2) =
      K.sgl (n + 1) (n + 1) (P - (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n (y1 (n + 1) n)) := by
    rw [map_sub, K.DD, sub_zero, hDt]
  have ht0 : ((y1 - K.sgl (n + 1) n (y1 (n + 1) n)) - K.D w2) (n + 1) n = 0 := by
    have h1 : K.D w2 (n + 1) n = 0 := by
      rw [K.D_apply]
      have h2 : K.Dv w2 (n + 1) n = 0 := by
        cases n with
        | zero => rfl
        | succ n =>
          show K.dv (n + 1 + 1) n (w2 (n + 1 + 1) n) = 0
          rw [hw20 _ _ (by omega), map_zero]
      have h3 : K.Dh w2 (n + 1) n = 0 := by
        show K.dh n n (w2 n n) = 0
        rw [hw20 _ _ le_rfl, map_zero]
      rw [h2, h3]; simp
    show (y1 (n + 1) n - K.sgl (n + 1) n (y1 (n + 1) n) (n + 1) n) - K.D w2 (n + 1) n = 0
    rw [h1, K.sgl_self]
    simp
  generalize (y1 - K.sgl (n + 1) n (y1 (n + 1) n)) - K.D w2 = t at hDt' ht0 hw2L hw2L'
  refine ⟨t n (n + 1), y1 (n + 1) n, hw2L _ _, ?_, hwL _ _, ?_⟩
  · refine dv_mem_of F t ?_ (fun e' h => hw2L' e' _ (by omega))
    rw [hDt', K.sgl_ne _ (Or.inl (by omega))]
    exact zero_mem _
  · have h := congrFun (congrFun hDt' (n + 1)) (n + 1)
    rw [K.sgl_self, K.D_apply] at h
    have h2 : K.Dv t (n + 1) (n + 1) = 0 := by
      show K.dv (n + 1) n (t (n + 1) n) = 0
      rw [ht0, map_zero]
    rw [h2, smul_zero, add_zero] at h
    have h3 : K.Dh t (n + 1) (n + 1) = K.dh n (n + 1) (t n (n + 1)) := rfl
    rw [← h3, h]
    abel

end GlobalTheory.CompanionTheory.ConeCech
end
end
