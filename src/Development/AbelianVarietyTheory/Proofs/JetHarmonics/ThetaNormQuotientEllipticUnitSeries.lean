module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmTypeEmbeddingsIntoValuationRing
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThreePointSeriesExponentialOfDefect
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IdempotentEmbeddingsCard

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaNormQuotientEllipticUnitSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaNormQuotientEllipticUnitSeries
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ThetaQuot

def fac (d : ℕ) (y z : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq y : ℝ) : ℂ) +
    (-(Real.pi : ℂ) * h1 d z y - (Real.pi : ℂ) / 2 * h1 d y y))

lemma fac_ne (d : ℕ) (y z : ℂ) : fac d y z ≠ 0 := Complex.exp_ne_zero _

lemma nonzeroIndexPlaces_adelicDataResized_eq (d : ℕ) (y : ℂ) (F : ℂ → ℂ) (z : ℂ) : W1 d y F z = fac d y z * F (z + y) := by
  simp only [W1, U1, fac, Complex.exp_add]; ring

lemma fac_mul (d : ℕ) (α : ℂ) (m : ℕ) (hm : (m : ℂ) = α * conj α) (y z : ℂ) :
    fac d (α * y) (α * z) = fac d y z ^ m := by
  simp only [fac]
  rw [← Complex.exp_nat_mul]
  congr 1
  rw [hm, ← Complex.mul_conj, ← Complex.mul_conj]
  simp only [h1, map_mul]
  ring

lemma not_half (d : ℕ) (hd : 0 < d) : ¬ InOK d (0 - 1 / 2) := by
  rintro ⟨u, v, h⟩
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have h2 : (-1 : ℂ) = 2 * u + v * (1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) := by
    simp only [wK] at h
    linear_combination 2 * h
  have him := congrArg Complex.im h2
  have hre := congrArg Complex.re h2
  simp at him hre
  have hv : v = 0 := by
    rcases him with h | h
    · exact h
    · exact absurd h hd.ne'
  subst hv
  have : (-1 : ℤ) = 2 * u := by
    have : (-1 : ℝ) = 2 * u := by simpa using hre
    exact_mod_cast this
  omega

lemma inOK_mul (d : ℕ) (hd : d % 4 = 3) {α β : ℂ} (ha : InOK d α) (hb : InOK d β) : InOK d (α * β) := by
  obtain ⟨u, v, rfl⟩ := ha
  obtain ⟨u', v', rfl⟩ := hb
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k := ⟨(d + 1) / 4, by omega⟩
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]; simp
  have hk' : (d : ℂ) + 1 = 4 * k := by exact_mod_cast hk
  have hw : wK d ^ 2 = wK d - k := by
    simp only [wK]
    linear_combination (((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq - (1 / 4) * hs - (1 / 4) * hk'
  refine ⟨u * u' - k * v * v', u * v' + v * u' + v * v', ?_⟩
  push_cast
  linear_combination (v * v' : ℂ) * hw

lemma zero_of_pole {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (p : ℂ)
    (h : meromorphicOrderAt (fun z => F z / G z) p < 0) : G p = 0 := by
  by_contra hp
  have ha : AnalyticAt ℂ (fun z => F z / G z) p := (hF.analyticAt p).div (hG.analyticAt p) hp
  exact absurd ha.meromorphicOrderAt_nonneg (not_le.mpr h)

theorem theta_quot : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (α : ℂ) (m : ℕ), InOK d α → α ≠ 0 → (m : ℂ) = α * conj α → ∃ ε : ℂ → ℂ, Ell M.L ε ∧ AnalyticAt ℂ ε 0 ∧ ε 0 = 1 ∧ Bd 1 (hat M.ι (C ω * logS) ε) ∧ (∀ z, θ z ≠ 0 → θ (α * z) = θ z ^ m * ε z) ∧ ∀ y z, θ (z + y) ≠ 0 → W1 d (α * y) θ (α * z) = W1 d y θ z ^ m * ε (z + y) := by
  intro d q _ M ω θ hd hd16 hsp hL hch hθ α m hα hα0 hm
  obtain ⟨hdiff, h0, -, hW, hz⟩ := hθ
  have hd4 : d % 4 = 3 := by omega
  have hA : Differentiable ℂ (fun z => θ (α * z)) := hdiff.comp (differentiable_id.const_mul α)
  have hB : Differentiable ℂ (fun z => θ z ^ m) := hdiff.pow m
  have hper : ∀ l ∈ M.L.lattice, ∀ z, θ (α * z) = fac d l z ^ m * θ (α * (z + l)) ∧
      θ z ^ m = fac d l z ^ m * θ (z + l) ^ m := by
    intro l hl z
    have hl' := (hL l).1 hl
    constructor
    · have := congrFun (hW _ (inOK_mul d hd4 hα hl')) (α * z)
      rw [nonzeroIndexPlaces_adelicDataResized_eq, fac_mul d α m hm] at this
      rw [← this, mul_add]
    · have := congrFun (hW _ hl') z
      rw [nonzeroIndexPlaces_adelicDataResized_eq] at this
      rw [← mul_pow, this]
  have hEε : Ell M.L (fun z => θ (α * z) / θ z ^ m) := by
    refine ⟨fun p => (hA.analyticAt p).meromorphicAt.div (hB.analyticAt p).meromorphicAt, ?_⟩
    intro l hl z
    obtain ⟨h1', h2'⟩ := hper l hl z
    show θ (α * (z + l)) / θ (z + l) ^ m = θ (α * z) / θ z ^ m
    rw [h1', h2', mul_div_mul_left _ _ (pow_ne_zero m (fac_ne d l z))]
  have hEη : Ell M.L (fun z => θ z ^ m / θ (α * z)) := by
    refine ⟨fun p => (hB.analyticAt p).meromorphicAt.div (hA.analyticAt p).meromorphicAt, ?_⟩
    intro l hl z
    obtain ⟨h1', h2'⟩ := hper l hl z
    show θ (z + l) ^ m / θ (α * (z + l)) = θ z ^ m / θ (α * z)
    rw [h1', h2', mul_div_mul_left _ _ (pow_ne_zero m (fac_ne d l z))]
  have hA0 : θ (α * 0) ≠ 0 := by simp [h0]
  have hB0 : θ 0 ^ m ≠ 0 := by simp [h0]
  have haε : AnalyticAt ℂ (fun z => θ (α * z) / θ z ^ m) 0 :=
    (hA.analyticAt 0).div (hB.analyticAt 0) hB0
  have haη : AnalyticAt ℂ (fun z => θ z ^ m / θ (α * z)) 0 :=
    (hB.analyticAt 0).div (hA.analyticAt 0) hA0
  have hns : ∀ β p : ℂ, InOK d β → β ≠ 0 → θ (β * p) = 0 → ¬ M.Small p := by
    intro β p hβ hβ0 hp hs
    have hp0 : PrimeTo d q 0 := ⟨1, one_pos, Nat.coprime_one_left q, 0, 0, by simp⟩
    have := (GlobalTheory.T.smallTorsion_killed_by_prime_powers d q M ω hd hd16 hsp hL hch).2.2.2 p β 0 hβ hβ0 hp0
      (by simpa using hz _ hp) hs
    exact not_half d hd.pos this.2
  have hbε : Bdd (hat M.ι (C ω * logS) (fun z => θ (α * z) / θ z ^ m)) := by
    refine GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ _ hch hEε haε fun p hp => ?_
    have := zero_of_pole hA hB p hp
    exact hns 1 p ⟨1, 0, by simp⟩ one_ne_zero (by simpa using (pow_eq_zero_iff'.1 this).1)
  have hbη : Bdd (hat M.ι (C ω * logS) (fun z => θ z ^ m / θ (α * z))) := by
    refine GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ _ hch hEη haη fun p hp => ?_
    exact hns α p hα hα0 (zero_of_pole hB hA p hp)
  obtain ⟨hh1, hh2, -, hh4, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q M.ι (C ω * logS) hch.2.1
  have hprod : hat M.ι (C ω * logS) (fun z => θ (α * z) / θ z ^ m) *
      hat M.ι (C ω * logS) (fun z => θ z ^ m / θ (α * z)) = 1 := by
    rw [← (hh1 _ _ haε haη).2.1]
    have e1 : ∀ᶠ z in 𝓝 (0 : ℂ), θ (α * z) ≠ 0 := hA.continuous.continuousAt.eventually_ne hA0
    have e2 : ∀ᶠ z in 𝓝 (0 : ℂ), θ z ^ m ≠ 0 := hB.continuous.continuousAt.eventually_ne hB0
    have := (hh1 _ (fun _ => (1 : ℂ)) (haε.mul haη) analyticAt_const).2.2.1 (by
      filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2] with z h1' h2'
      show θ (α * z) / θ z ^ m * (θ z ^ m / θ (α * z)) = 1
      field_simp)
    refine Eq.trans this ?_
    rw [hh2]; simp
  have hε0 : θ (α * 0) / θ 0 ^ m = 1 := by simp [h0]
  have hmain : ∀ z, θ z ≠ 0 → θ (α * z) = θ z ^ m * (θ (α * z) / θ z ^ m) := by
    intro z hz'
    field_simp
  refine ⟨fun z => θ (α * z) / θ z ^ m, hEε, haε, hε0, ?_, hmain, ?_⟩
  · refine ((GlobalTheory.T.cpSeriesCoeffNormBounded_ring_laws q).2.2.2.2.1 _ _ hbε hbη hprod ?_).1
    rw [hh4]; simp [h0]
  · intro y z hyz
    rw [nonzeroIndexPlaces_adelicDataResized_eq, nonzeroIndexPlaces_adelicDataResized_eq, fac_mul d α m hm, ← mul_add, mul_pow, mul_assoc]
    exact congrArg _ (hmain _ hyz)

end GlobalTheory.MomOne.ThetaQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaNormQuotientEllipticUnitSeriesStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaNormQuotient_elliptic_unitSeries : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (α : ℂ) (m : ℕ), InOK d α → α ≠ 0 → (m : ℂ) = α * conj α → ∃ ε : ℂ → ℂ, Ell M.L ε ∧ AnalyticAt ℂ ε 0 ∧ ε 0 = 1 ∧ Bd 1 (hat M.ι (C ω * logS) ε) ∧ (∀ z, θ z ≠ 0 → θ (α * z) = θ z ^ m * ε z) ∧ ∀ y z, θ (z + y) ≠ 0 → W1 d (α * y) θ (α * z) = W1 d y θ z ^ m * ε (z + y) := by
  first | exact @GlobalTheory.MomOne.ThetaQuot.theta_quot | exact GlobalTheory.MomOne.ThetaQuot.theta_quot | (intros; apply GlobalTheory.MomOne.ThetaQuot.theta_quot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EigenEquationTranslationKernelGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EigenEquationTranslationKernelGenericFibre
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Jets

theorem units_mul_pow_mul_inv_cancel {R : Type} [CommRing R] (x y m : Rˣ) (s : R) :
    x.val * s * (y * x⁻¹ * m).val = y.val * (m.val * s) := by
  rw [Units.val_mul, Units.val_mul]
  linear_combination (s * y.val * m.val) * x.mul_inv

theorem ring_relation_transfer_identity {R : Type} [CommRing R] {t t' m m' e : R} (E : t' * m = e * (t * m')) (x y y' : R) :
    y' * t' * (y * x * m) = e * (y * t * (y' * x * m')) := by
  linear_combination (x * y * y') * E

theorem sval_of_isoRelM {Y Y' X₁ X₂ Z₁ Z : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {m : Y' ⟶ Y} {k : ℕ} {g₁ : Z₁ ⟶ X₁} {h₁ : Y' ⟶ Z₁}
    {a : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ)))}
    {b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => m ≫ f₂) (fun _ => (k : ℤ)))}
    (H : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a (m ≫ f₂) (𝟙 _) b) (r : Z ⟶ Y') (z : Z) {J₂} {J₁}
    (hJ₂ : Good L₂ z J₂) (hJ₁ : Good L₁ z J₁) :
    sval b r z J₂ = (isoVal w (r ≫ m) z (J₂ ((r ≫ m) ≫ f₂)) (J₁ ((r ≫ m) ≫ f₁)) ^ (k : ℤ)).val *
      sval a (r ≫ h₁) z J₁ := by
  have := (GlobalTheory.FieldBaseChange.isoRelM_iff w m k h₁ H.1 _ H.2.1 a b).1 H Z r z _ _
    (hJ₂ ((r ≫ m) ≫ f₂)) (hJ₁ ((r ≫ m) ≫ f₁))
  rw [Category.comp_id] at this
  rw [GlobalTheory.FieldBaseChange.sval_eq_powVal, GlobalTheory.FieldBaseChange.sval_eq_powVal, Category.assoc r h₁, H.1,
    ← Category.assoc r m f₁, ← Category.assoc r m f₂]
  exact this

theorem eigen_transfer {S X : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] (e : B ≅ A)
    [IsMonHom e.hom] {L₁ : LB A.left} {L₂ : LB X} (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (f : B.left ⟶ X)
    {K : Type} [Field K] (p : Spec (CommRingCat.of K) ⟶ S) (φ : X ⟶ X) (b : B ⟶ B) (hφ : b.left ≫ f = f ≫ φ)
    (a : A ⟶ A) (ha : IsMonHom a) (hb : b ≫ e.hom = e.hom ≫ a) (N k : ℕ)
    (mu : LB.Gen (LB.LinComb L₂ (K := Fin 2) ![𝟙 X, φ] ![(N : ℤ), -1])) (hmu : mu.IsGen)
    (w : LB.Iso (L₁.pull e.hom.left) (L₂.pull f)) (hw : w.IsGen)
    (σ₀ : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => (snd (Over.mk p) B).left ≫ f) (fun _ => (k : ℤ))))
    (σ' τ : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => (snd (Over.mk p) B).left ≫ f)
      (fun _ => ((k * N : ℕ) : ℤ))))
    (t' t : LB.Sec (LPow A L₁ ((k * N : ℕ) : ℤ) (Over.mk p)))
    (h₀ : ∀ (y : (Over.mk p ⊗ B).left) (J), Good L₂ y J → sval σ' (𝟙 _) y J =
      sval σ₀ (Over.mk p ◁ b).left y J * (val mu ((snd (Over.mk p) B).left ≫ f) y J).val ^ k)
    (h₁ : GeneratorPullback.IsoRelM L₁ L₂ e.hom.left f w (snd (Over.mk p) B).left (k * N) (snd (Over.mk p) A).left
      (lift (fst (Over.mk p) B) (snd (Over.mk p) B ≫ e.hom)).left t' ((snd (Over.mk p) B).left ≫ f) (𝟙 _) σ')
    (h₂ : GeneratorPullback.IsoRelM L₁ L₂ e.hom.left f w (snd (Over.mk p) B).left (k * N) (snd (Over.mk p) A).left
      (lift (fst (Over.mk p) B) (snd (Over.mk p) B ≫ e.hom)).left t ((snd (Over.mk p) B).left ≫ f) (𝟙 _) τ)
    (θ : ThetaGrp A L₁ ((k * N : ℕ) : ℤ) (Over.mk p)) (hθ : IsActOf A L₁ ((k * N : ℕ) : ℤ) θ t' t)
    (c : Over.mk p ⟶ A) (u : Γ((Over.mk p).left, ⊤)ˣ) (hc : c ≫ a = 1)
    (hW : WeilIs A L₁ ((k * N : ℕ) : ℤ) c θ.pt u)
    (Z : Scheme.{0}) (ρ : Z ⟶ (Over.mk p ⊗ B).left) (z : Z) (J) (hJ : Good L₂ z J) :
    sval τ (ρ ≫ (translT B (c ≫ e.inv)).left) z J * (val mu (ρ ≫ (snd (Over.mk p) B).left ≫ f) z J).val ^ k =
      gs (ρ ≫ (fst (Over.mk p) B).left) z ⊤ u.val * (sval τ ρ z J *
        (val mu ((ρ ≫ (translT B (c ≫ e.inv)).left) ≫ (snd (Over.mk p) B).left ≫ f) z J).val ^ k) := by
  obtain ⟨g, hg⟩ : ∃ g, g = lift (fst (Over.mk p) B) (snd (Over.mk p) B ≫ e.hom) := ⟨_, rfl⟩
  rw [← hg] at h₁ h₂
  have g₁ : g ≫ fst _ _ = fst _ _ := by rw [hg, lift_fst]
  have g₂ : g ≫ snd _ _ = snd _ _ ≫ e.hom := by rw [hg, lift_snd]
  let n : Over.mk p ⊗ A ⟶ Over.mk p ⊗ B := lift (fst _ _) (snd _ _ ≫ e.inv)
  have hn : n ≫ g = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n, g₁, g₂]
  have hn' : g ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n, g₁, reassoc_of% g₂]
  have hb' : a ≫ e.inv = e.inv ≫ b := by
    rw [Iso.comp_inv_eq, Category.assoc, hb, e.inv_hom_id_assoc]
  have gb : Over.mk p ◁ b ≫ g = g ≫ Over.mk p ◁ a := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [g₁, g₂, reassoc_of% g₂, hb]
  have gt : translT B (c ≫ e.inv) ≫ g = g ≫ translT A c := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [translT, g₁]
    · rw [Category.assoc, Category.assoc, g₂, translT, translT, lift_snd_assoc, lift_snd]
      show ((fst _ B ≫ c ≫ e.inv) * snd _ B) ≫ e.hom = g ≫ ((fst _ A ≫ c) * snd _ A)
      rw [MonObj.mul_comp, MonObj.comp_mul, g₂, reassoc_of% g₁]
      simp
  have tb : translT B (c ≫ e.inv) ≫ snd _ _ ≫ b = snd _ _ ≫ b := by
    rw [← cancel_mono e.hom]
    simp only [Category.assoc]
    rw [hb, ← reassoc_of% g₂, reassoc_of% gt, GlobalTheory.KernelEigen.translT_snd_comp a hc]
  obtain ⟨s, hs⟩ := ((GlobalTheory.FieldBaseChange.isoRelM_bijective (k := k) (m := (snd (Over.mk p) B).left)
    (g₁ := (snd (Over.mk p) A).left) (h₁ := g.left) hL₁ hL₂ hw (congrArg (fun q => q.left) g₂) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')).2 σ₀).exists
  obtain ⟨ν, hν, vν⟩ := exists_gen hL₂ (K' := Fin 2) (φ' := ![𝟙 X, φ]) (ε' := ![((k * N : ℕ) : ℤ), -(k : ℤ)])
    (fun U _ h => by simp [Fin.prod_univ_two]) (GeneratorPullback.powGen L₂ _ _ mu k) (GlobalTheory.FrameGeo.powGen_isGen _ _ _ _ hmu k)
  obtain ⟨mA, hmA, vmA⟩ := exists_gen_move_back _ _ _ _ _ L₁ L₂ hL₁ hL₂ _ _ w hw (Fin 2)
    ![(snd (Over.mk p) A ≫ e.inv).left, (snd (Over.mk p) A ≫ a ≫ e.inv).left] _
    ![(snd (Over.mk p) A).left, (snd (Over.mk p) A ≫ a).left]
    (fun i => by
      fin_cases i
      · show (snd (Over.mk p) A).left = (snd (Over.mk p) A ≫ e.inv).left ≫ e.hom.left
        rw [← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
      · show (snd (Over.mk p) A ≫ a).left = (snd (Over.mk p) A ≫ a ≫ e.inv).left ≫ e.hom.left
        rw [← Over.comp_left, Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id])
    _ ((snd (Over.mk p) A ≫ e.inv).left ≫ f)
    (fun i => by
      fin_cases i
      · exact Category.comp_id _
      · show ((snd (Over.mk p) A ≫ e.inv).left ≫ f) ≫ φ = (snd (Over.mk p) A ≫ a ≫ e.inv).left ≫ f
        rw [Category.assoc, ← hφ, ← Category.assoc, ← Over.comp_left, Category.assoc, hb'])
    ν hν
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk p ⊗ B).left) (z : Z) (J₂) (J₁), Good L₂ z J₂ → Good L₁ z J₁ →
      val mu (r ≫ (snd (Over.mk p) B).left ≫ f) z J₂ ^ k =
        isoVal w (r ≫ (snd (Over.mk p) B).left) z (J₂ ((r ≫ (snd (Over.mk p) B).left) ≫ f))
          (J₁ ((r ≫ (snd (Over.mk p) B).left) ≫ e.hom.left)) ^ ((k * N : ℕ) : ℤ) *
        (isoVal w (r ≫ (snd (Over.mk p) B ≫ b).left) z (J₂ ((r ≫ (snd (Over.mk p) B ≫ b).left) ≫ f))
          (J₁ ((r ≫ (snd (Over.mk p) B ≫ b).left) ≫ e.hom.left)) ^ (k : ℤ))⁻¹ * val mA (r ≫ g.left) z J₁ := by
    intro Z r z J₂ J₁ hJ₂ hJ₁
    have e₀ : (r ≫ g.left) ≫ (snd (Over.mk p) A ≫ e.inv).left = r ≫ (snd (Over.mk p) B).left := by
      rw [Category.assoc, ← Over.comp_left, reassoc_of% g₂, e.hom_inv_id, Category.comp_id]
    have e₁ : (r ≫ g.left) ≫ (snd (Over.mk p) A ≫ a ≫ e.inv).left = r ≫ (snd (Over.mk p) B ≫ b).left := by
      rw [Category.assoc, ← Over.comp_left, reassoc_of% g₂, hb', e.hom_inv_id_assoc]
    have := vmA Z (r ≫ g.left) z J₂ J₁ hJ₂ hJ₁
    rw [vν _ _ z J₂ hJ₂, GlobalTheory.FrameGeo.val_powGen, Fin.prod_univ_two, ← Category.assoc, e₀, Category.assoc] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₀, e₁, zpow_neg] at this
    exact this
  have hσ := secRel_iff hL₂ _ _ σ' _ _ σ₀ (Over.mk p ◁ b).left _ _
    (LB.pullGen L₂ _ _ (GeneratorPullback.powGen L₂ _ _ mu k) ((snd (Over.mk p) B).left ≫ f))
  have h₀' := hσ.1 (hσ.2 fun y J hJ => by
    rw [h₀ y J hJ, val_pull hJ, GlobalTheory.FrameGeo.val_powGen, Category.id_comp, Category.id_comp,
      Units.val_pow_eq_pow_val])
  choose J₁ hJ₁ using fun χ : Z ⟶ A.left => exists_chart hL₁ (χ z)
  have E := GlobalTheory.translate_pullback_eigensection S A L₁ hL₁ K p a ha N k mA hmA s t' t (fun y I₁ hI₁ => by
    choose I₂ hI₂ using fun χ : (Over.mk p ⊗ A).left ⟶ X => exists_chart hL₂ (χ y)
    have ng : n.left ≫ g.left = 𝟙 _ := congrArg (fun q => q.left) hn
    have e₁ : (n.left ≫ (Over.mk p ◁ b).left) ≫ g.left = (Over.mk p ◁ a).left := by
      rw [← Over.comp_left, ← Over.comp_left, Category.assoc, gb, reassoc_of% hn]
    have e₂ : (n.left ≫ (Over.mk p ◁ b).left) ≫ (snd (Over.mk p) B).left =
        n.left ≫ (snd (Over.mk p) B ≫ b).left := by
      rw [Category.assoc, ← Over.comp_left, whiskerLeft_snd]
    have := h₀' _ n.left y I₂ hI₂
    rw [val_pull hI₂, GlobalTheory.FrameGeo.val_powGen, hv _ _ y I₂ I₁ hI₂ hI₁, sval_of_isoRelM h₁ _ y hI₂ hI₁,
      sval_of_isoRelM hs _ y hI₂ hI₁, ng, e₁, e₂] at this
    refine (Units.mul_right_inj _).1 (this.trans ?_)
    exact units_mul_pow_mul_inv_cancel _ _ _ _) θ hθ c u hc hW Z (ρ ≫ g.left) z J₁ hJ₁
  have e₁ : (ρ ≫ (translT B (c ≫ e.inv)).left) ≫ g.left = (ρ ≫ g.left) ≫ (translT A c).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, gt]
  have e₂ : (ρ ≫ (translT B (c ≫ e.inv)).left) ≫ (snd (Over.mk p) B ≫ b).left =
      ρ ≫ (snd (Over.mk p) B ≫ b).left := by
    rw [Category.assoc, ← Over.comp_left, tb]
  have e₃ : (ρ ≫ g.left) ≫ (fst (Over.mk p) A).left = ρ ≫ (fst (Over.mk p) B).left := by
    rw [Category.assoc, ← Over.comp_left, g₁]
  rw [e₃] at E
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hv _ _ z J J₁ hJ hJ₁, hv _ _ z J J₁ hJ hJ₁,
    sval_of_isoRelM h₂ _ z hJ hJ₁, sval_of_isoRelM h₂ _ z hJ hJ₁, e₁, e₂]
  simp only [Units.val_mul]
  exact ring_relation_transfer_identity E _ _ _

theorem eigen_equation_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (φ : G ⟶ G) (a : A.A ⟶ A.A), IsMonHom a → (Over.pullback (jK R)).map φ ≫ U.gen.hom = U.gen.hom ≫ a → ∀ (N k : ℕ) (mu : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 G.left, φ.left] ![(N : ℤ), -1])), mu.IsGen → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → ∀ (σ₀ : U.SecGF F k) (σ' τ : U.SecGF F (k * N)) (t' t : LB.Sec (LPow A.A A.L ((k * N : ℕ) : ℤ) (TFK (R := R) F))), (∀ (y : (UnifPre.GF (G := G) F).left) (J), Good U.LG.L y J → sval σ' (𝟙 _) y J = sval σ₀ (TFK (R := R) F ◁ (Over.pullback (jK R)).map φ).left y J * (val mu (UnifPre.gFK (G := G) F) y J).val ^ k) → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (k * N) (snd (TFK (R := R) F) A.A).left (U.genF F).left t' (UnifPre.gFK (G := G) F) (𝟙 _) σ' → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (k * N) (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) τ → ∀ θ : ThetaGrp A.A A.L ((k * N : ℕ) : ℤ) (TFK (R := R) F), IsActOf A.A A.L ((k * N : ℕ) : ℤ) θ t' t → ∀ (z₀ : TFK (R := R) F ⟶ A.A) (ε : Fˣ), z₀ ≫ a = 1 → WeilIs A.A A.L ((k * N : ℕ) : ℤ) z₀ θ.pt (unitOn ε) → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (UnifPre.GF (G := G) F).left) (z : Z) (J), Good U.LG.L z J → sval τ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) (z₀ ≫ U.gen.inv)).left) z J * (val mu (ρ ≫ UnifPre.gFK (G := G) F) z J).val ^ k = constVal (ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) z (ε : F) * (sval τ ρ z J * (val mu ((ρ ≫ (translT ((Over.pullback (jK R)).obj G) (z₀ ≫ U.gen.inv)).left) ≫ UnifPre.gFK (G := G) F) z J).val ^ k) := by
  intro R _ _ I D A G _ _ U F _ _ φ a ha hφ N k mu hmu w hw σ₀ σ' τ t' t h₀ h₁ h₂ θ hθ z₀ ε hz hW Z ρ z J hJ
  haveI := U.gen_hom
  exact eigen_transfer U.gen A.isLB U.LG.isLB (pullback.fst G.hom (jK R)) (jFK (R := R) F) φ.left
    ((Over.pullback (jK R)).map φ) (pullback.lift_fst _ _ _) a ha hφ N k mu hmu w hw σ₀ σ' τ t' t h₀ h₁ h₂ θ hθ
    z₀ (unitOn ε) hz hW Z ρ z J hJ

end GlobalTheory.Jets
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EigenEquationTranslationKernelGenericFibreStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenEquation_translation_kernel_genericFibre : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (φ : G ⟶ G) (a : A.A ⟶ A.A), IsMonHom a → (Over.pullback (jK R)).map φ ≫ U.gen.hom = U.gen.hom ≫ a → ∀ (N k : ℕ) (mu : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 G.left, φ.left] ![(N : ℤ), -1])), mu.IsGen → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → ∀ (σ₀ : U.SecGF F k) (σ' τ : U.SecGF F (k * N)) (t' t : LB.Sec (LPow A.A A.L ((k * N : ℕ) : ℤ) (TFK (R := R) F))), (∀ (y : (UnifPre.GF (G := G) F).left) (J), Good U.LG.L y J → sval σ' (𝟙 _) y J = sval σ₀ (TFK (R := R) F ◁ (Over.pullback (jK R)).map φ).left y J * (val mu (UnifPre.gFK (G := G) F) y J).val ^ k) → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (k * N) (snd (TFK (R := R) F) A.A).left (U.genF F).left t' (UnifPre.gFK (G := G) F) (𝟙 _) σ' → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (k * N) (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) τ → ∀ θ : ThetaGrp A.A A.L ((k * N : ℕ) : ℤ) (TFK (R := R) F), IsActOf A.A A.L ((k * N : ℕ) : ℤ) θ t' t → ∀ (z₀ : TFK (R := R) F ⟶ A.A) (ε : Fˣ), z₀ ≫ a = 1 → WeilIs A.A A.L ((k * N : ℕ) : ℤ) z₀ θ.pt (unitOn ε) → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (UnifPre.GF (G := G) F).left) (z : Z) (J), Good U.LG.L z J → sval τ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) (z₀ ≫ U.gen.inv)).left) z J * (val mu (ρ ≫ UnifPre.gFK (G := G) F) z J).val ^ k = constVal (ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) z (ε : F) * (sval τ ρ z J * (val mu ((ρ ≫ (translT ((Over.pullback (jK R)).obj G) (z₀ ≫ U.gen.inv)).left) ≫ UnifPre.gFK (G := G) F) z J).val ^ k) := by
  first | exact @GlobalTheory.Jets.eigen_equation_generic | exact GlobalTheory.Jets.eigen_equation_generic | (intros; apply GlobalTheory.Jets.eigen_equation_generic <;> assumption)
end
end
