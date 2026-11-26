module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusProperties
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.SgnIdent

variable {D : D7}

theorem uj_neg_eq {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) :
    Formalism.UG.UJ σ (-J) = Formalism.UG.UJ σ J := by
  ext g
  show Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * (-J) * (g : Matrix (Fin n) (Fin n) A) = -J ↔
    Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * J * (g : Matrix (Fin n) (Fin n) A) = J
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem uh_neg_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Formalism.QuantumDeterminants.UH (-H) = Formalism.QuantumDeterminants.UH H := by
  ext g
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem gramAt_neg_eq (V : HSp D) (τ : D.what₂.Tau) : gramAt D (neg V) τ = -gramAt D V τ := by
  ext i j; simp [gramAt, neg_gram]

theorem mem_GQ_sgn (ε : Bool) (V : HSp D) (g : GA D (sgn ε V)) : g ∈ GQ (sgn ε V) ↔ ofSgn ε V g ∈ GQ V := by
  cases ε
  · exact Iff.rfl
  · constructor
    · rintro ⟨x, hx, e⟩
      exact ⟨x, by rw [← uj_neg_eq]; exact hx, e⟩
    · rintro ⟨x, hx, e⟩
      exact ⟨x, by rw [← uj_neg_eq] at hx; exact hx, e⟩

theorem mem_GfC_sgn (ε : Bool) (V : HSp D) (g : GA D (sgn ε V)) : g ∈ GfC (sgn ε V) ↔ ofSgn ε V g ∈ GfC V := Iff.rfl

theorem mem_GinfC_sgn (ε : Bool) (V : HSp D) (g : GA D (sgn ε V)) : g ∈ GinfC (sgn ε V) ↔ ofSgn ε V g ∈ GinfC V :=
  Iff.rfl

theorem uh_sgn (ε : Bool) (V : HSp D) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.UH (gramAt D (sgn ε V) τ) = Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  cases ε
  · rfl
  · rw [gramAt_neg_eq, uh_neg_eq]

theorem lieAt_sgn (ε : Bool) (V : HSp D) (τ : D.what₂.Tau) : lieAt (sgn ε V) τ = lieAt V τ := by
  cases ε
  · rfl
  · ext X
    show Xᴴ * gramAt D (neg V) τ + gramAt D (neg V) τ * X = 0 ↔ Xᴴ * gramAt D V τ + gramAt D V τ * X = 0
    rw [gramAt_neg_eq, Matrix.mul_neg, Matrix.neg_mul, ← neg_add, neg_eq_zero]

theorem isAtTau_sgn (θ : InfFam D) (ε : Bool) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (x : GA D (sgn ε V)) : IsAtTau θ (sgn ε V) τ g x ↔ IsAtTau θ V τ g (ofSgn ε V x) := Iff.rfl

theorem atTau_sgn (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (V : HSp D) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : ofSgn ε V (atTau θ (sgn ε V) τ g) = atTau θ V τ g := by
  by_cases h : ∃ x, IsAtTau θ V τ g x
  · have h₁ : ∃ x, IsAtTau θ (sgn ε V) τ g x := by
      obtain ⟨x, hx⟩ := h
      refine ⟨(ofSgn ε V).symm x, (isAtTau_sgn θ ε V τ g _).2 ?_⟩
      rw [MulEquiv.apply_symm_apply]; exact hx
    have a : IsAtTau θ (sgn ε V) τ g (atTau θ (sgn ε V) τ g) := by
      unfold atTau; rw [dite_eq_left h₁]; exact h₁.choose_spec
    have b : IsAtTau θ V τ g (atTau θ V τ g) := by
      unfold atTau; rw [dite_eq_left h]; exact h.choose_spec
    exact GlobalTheory.Published.AutFin.Model.isAtTau_unique θ V hθ ((isAtTau_sgn θ ε V τ g _).1 a) b
  · have h₁ : ¬ ∃ x, IsAtTau θ (sgn ε V) τ g x := fun ⟨x, hx⟩ => h ⟨_, (isAtTau_sgn θ ε V τ g x).1 hx⟩
    have a : atTau θ (sgn ε V) τ g = 1 := by unfold atTau; rw [dite_eq_right h₁]
    have b : atTau θ V τ g = 1 := by unfold atTau; rw [dite_eq_right h]
    rw [a, b, map_one]

theorem meas_sgn (ε : Bool) (V : HSp D) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)) (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) :
    ∃ ν₁ : Measure (GA D (sgn ε V)), ν₁.IsHaarMeasure ∧ IsFundamentalDomain (GQ (sgn ε V)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ∧
      ∀ φ : GA D V → ℂ, (IntegrableOn (fun g => φ (ofSgn ε V g)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ↔ IntegrableOn φ 𝓕 ν) ∧
        ∫ g in ofSgn ε V ⁻¹' 𝓕, φ (ofSgn ε V g) ∂ν₁ = ∫ g in 𝓕, φ g ∂ν := by
  obtain ⟨-, -, -, hb, hg, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨-, -, -, hb₁, hg₁, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (sgn ε V)
  let h : GA D (sgn ε V) ≃ₜ GA D V :=
    { toEquiv := (ofSgn ε V).toEquiv, continuous_toFun := continuous_ofSgn ε V,
      continuous_invFun := continuous_ofSgn_symm ε V }
  have me : MeasurableEmbedding (ofSgn ε V) := h.toMeasurableEquiv.measurableEmbedding
  have hm : Measurable (ofSgn ε V) := (continuous_ofSgn ε V).measurable
  have hm' : Measurable (ofSgn ε V).symm := (continuous_ofSgn_symm ε V).measurable
  have mp : MeasurePreserving (ofSgn ε V) (ν.map (ofSgn ε V).symm) ν := by
    refine ⟨hm, ?_⟩
    rw [Measure.map_map hm hm']
    have : (⇑(ofSgn ε V) ∘ ⇑(ofSgn ε V).symm) = id := funext fun x => (ofSgn ε V).apply_symm_apply x
    rw [this, Measure.map_id]
  refine ⟨ν.map (ofSgn ε V).symm,
    (ofSgn ε V).symm.isHaarMeasure_map ν (continuous_ofSgn_symm ε V) (continuous_ofSgn ε V), ?_, fun φ => ?_⟩
  · refine h𝓕.preimage_of_equiv mp.quasiMeasurePreserving
      (e := fun γ : GQ V => (⟨(ofSgn ε V).symm γ, (mem_GQ_sgn ε V _).2 (by rw [MulEquiv.apply_symm_apply]; exact γ.2)⟩ :
        GQ (sgn ε V))) ⟨fun a b hab => ?_, fun δ => ?_⟩ fun γ x => ?_
    · exact Subtype.ext ((ofSgn ε V).symm.injective (congrArg Subtype.val hab))
    · exact ⟨⟨ofSgn ε V δ, (mem_GQ_sgn ε V δ).1 δ.2⟩, Subtype.ext ((ofSgn ε V).symm_apply_apply δ)⟩
    · show ofSgn ε V ((ofSgn ε V).symm (γ : GA D V) * x) = (γ : GA D V) * ofSgn ε V x
      rw [map_mul, MulEquiv.apply_symm_apply]
  · exact ⟨mp.integrableOn_comp_preimage me, mp.setIntegral_preimage_emb me φ 𝓕⟩

theorem sgnLaw_holds : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (V : HSp D), SgnLaw θ ε V :=
  fun _ θ hθ ε V => ⟨mem_GQ_sgn ε V, mem_GfC_sgn ε V, mem_GinfC_sgn ε V, uh_sgn ε V, lieAt_sgn ε V,
    fun τ g => atTau_sgn θ hθ ε V τ g, fun ν 𝓕 hν h𝓕 => meas_sgn ε V ν 𝓕 hν h𝓕⟩

end GlobalTheory.SgnIdent

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signedUnitaryGroup_compat : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (V : HSp D), SgnLaw θ ε V := by
  first | exact @GlobalTheory.SgnIdent.sgnLaw_holds | exact GlobalTheory.SgnIdent.sgnLaw_holds | (intros; apply GlobalTheory.SgnIdent.sgnLaw_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWittDecompositionIsotropicSplitUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWittDecompositionIsotropicSplitUnipotent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped GlobalTheory.MixModel

namespace GlobalTheory.WittSect

theorem sub_one_mulVec_eq_zero {R : Type*} [CommRing R] {n a b : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (P : Matrix (Fin n) (Fin a) R) (Q : Matrix (Fin n) (Fin b) R) (v : Fin n → R) (p : Fin a → R) (q : Fin b → R)
    (hv : v = P *ᵥ p + Q *ᵥ q) (hP : M * P = P) (hQ : M * Q = Q) : (M - 1) *ᵥ v = 0 := by
  rw [hv, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP, hQ,
    sub_self]

theorem exists_hypDec_mem_NI : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B →
    ∃ d : GlobalTheory.MixModel.HypDec V V' r, d.e = C ∧ d.i₀ = B ∧ ∀ m : GA D V,
      HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = C.map (incA D) →
      HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = B.map (incA D) → m ∈ NI V C := by
  intro D V V' r C B hs
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.TwistDual.exists_isotropic_dual D V V' r C B hs
  have e : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D M = Mᴴ := fun _ => rfl
  have hG := GlobalTheory.MixModel.gram_conjTranspose V
  rw [e] at h1 h2 h3
  have hee : Cᴴ * V.gram * C = 0 := hs.frame.2.2
  have horth : Cᴴ * V.gram * B = 0 := by rw [← e]; exact hs.orth
  have hiso : Bᴴ * V.gram * B = V'.gram := by rw [← e]; exact hs.isom
  have h1' : C'ᴴ * V.gram * C = 1 := by
    have := congrArg Matrix.conjTranspose h1
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have h0e : Bᴴ * V.gram * C = 0 := by
    have := congrArg Matrix.conjTranspose horth
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have h0e' : Bᴴ * V.gram * C' = 0 := by
    have := congrArg Matrix.conjTranspose h3
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  let d : GlobalTheory.MixModel.HypDec V V' r :=
    { e := C, e' := C', i₀ := B, ee := hee, e'e' := h2, e'e := h1', iso := hiso, i₀e := h0e, i₀e' := h0e',
      rank_add := hs.rank.symm }
  refine ⟨d, rfl, rfl, fun m hC hB => Subgroup.subset_closure ?_⟩

  have hu := GlobalTheory.MixModel.mt_unitary V m
  have hsum : C * (C'ᴴ * V.gram) + B * (V'.gram⁻¹ * (Bᴴ * V.gram)) + C' * (Cᴴ * V.gram) = 1 :=
    d.sum_eq_one_rat
  have hCm : GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V * mt V m =
      GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V := by
    calc GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V * mt V m
        = GlobalTheory.MixModel.adj (mt V m * C.map (incA D)) * GlobalTheory.MixModel.gA V * mt V m := by rw [hC]
      _ = GlobalTheory.MixModel.adj (C.map (incA D)) * (GlobalTheory.MixModel.adj (mt V m) * (GlobalTheory.MixModel.gA V * mt V m)) := by
          simp only [GlobalTheory.MixModel.adj, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hu]
  simp only [Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · change (mt V m - 1) * C.map (incA D) = 0
    rw [Matrix.sub_mul, hC, Matrix.one_mul, sub_self]
  · rw [Matrix.map_mul]
    change GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V * (mt V m - 1) = 0
    rw [Matrix.mul_sub, hCm, Matrix.mul_one, sub_self]
  · intro x hx
    refine ⟨0, ?_⟩
    rw [Matrix.mulVec_zero]
    have hx0 : (Cᴴ * V.gram) *ᵥ x = 0 := hx
    obtain ⟨u, hu⟩ : ∃ u, u = (C'ᴴ * V.gram) *ᵥ x := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w, w = (V'.gram⁻¹ * (Bᴴ * V.gram)) *ᵥ x := ⟨_, rfl⟩
    have hx' : x = C *ᵥ u + B *ᵥ w := by
      have := congrArg (fun M => M *ᵥ x) hsum
      rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec (M := C),
        ← Matrix.mulVec_mulVec (M := B), ← Matrix.mulVec_mulVec (M := C'), hx0, Matrix.mulVec_zero, add_zero] at this
      rw [hu, hw]; exact this.symm
    have hxA : (fun i => incA D (x i)) = C.map (incA D) *ᵥ (incA D ∘ u) + B.map (incA D) *ᵥ (incA D ∘ w) := by
      funext i
      have hi : x i = (C *ᵥ u) i + (B *ᵥ w) i := congrFun hx' i
      have ha := RingHom.map_mulVec (incA D) C u i
      have hb := RingHom.map_mulVec (incA D) B w i
      rw [Pi.add_apply, ← ha, ← hb, hi]
      exact RingHom.map_add (incA D) _ _
    refine sub_one_mulVec_eq_zero _ (C.map (incA D)) (B.map (incA D)) _ (incA D ∘ u) (incA D ∘ w) ?_ ?_ ?_
    · exact hxA
    · exact hC
    · exact hB

end GlobalTheory.WittSect
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWittDecompositionIsotropicSplitUnipotentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wittDecomposition_isotropicSplit_unipotent : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∃ d : GlobalTheory.MixModel.HypDec V V' r, d.e = C ∧ d.i₀ = B ∧ ∀ m : GA D V, HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = C.map (incA D) → HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = B.map (incA D) → m ∈ NI V C := by
  first | exact @GlobalTheory.WittSect.exists_hypDec_mem_NI | exact GlobalTheory.WittSect.exists_hypDec_mem_NI | (intros; apply GlobalTheory.WittSect.exists_hypDec_mem_NI <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

section Family

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

def IsCan {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X}
    (pm : Gx x₁ ⟶ Gx x) : Prop :=
  x₁ = spMap χ ≫ x ∧ pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x₁) Xo.univ.t.G).left ∧
    pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left ≫ spMap χ

def IsFib {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x x' : Sp T ⟶ Xo.X} {x₁ x₁' : Sp Ω ⟶ Xo.X}
    (Ψ : Gx x ⟶ Gx x') (Ψ₁ : Gx x₁ ⟶ Gx x₁') : Prop :=
  ∃ (pm : Gx x₁ ⟶ Gx x) (pm' : Gx x₁' ⟶ Gx x'), IsCan χ pm ∧ IsCan χ pm' ∧ Ψ₁ ≫ pm' = pm ≫ Ψ ∧
    Ψ₁ ≫ (fst (Over.mk x₁') Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left

def IsHeckeFam (P : Ideal (𝓞 E)) (p i : ℕ) {T : Type} [CommRing T] {x x' : Sp T ⟶ Xo.X} (Ψ : Gx x ⟶ Gx x') : Prop :=
  IsLinHom Ψ ∧ Etale Ψ ∧ Surjective Ψ ∧ (∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ ((p : ℤ) ^ 2) β) ∧
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'),
      IsFib χ Ψ Ψ₁ → Xo.univ.t.HeckeKer (Over.mk x₁) Dw P p i (transKer Xo.univ.t.G Ψ₁) ∧
        IsHeckeIsog p (transKer Xo.univ.t.G Ψ₁) Ψ₁

def IsListed {T : Type} [CommRing T] {x x' : Sp T ⟶ Xo.X} (Ψ : Gx x ⟶ Gx x') {n : ℕ}
    (σ : Fin n → (Over.mk x ⟶ Xo.univ.t.G)) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'),
    IsFib χ Ψ Ψ₁ → ∃ e : Fin n ≃ transKer Xo.univ.t.G Ψ₁, ∀ j, (e j).1.left = spMap χ ≫ (σ j).left

theorem exists_isCan {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X}
    (hx : x₁ = spMap χ ≫ x) : ∃ pm : Gx x₁ ⟶ Gx x, IsCan χ pm :=
  ⟨pullback.lift (pullback.fst (Over.mk x₁).hom Xo.univ.t.G.hom ≫ spMap χ)
      (pullback.snd (Over.mk x₁).hom Xo.univ.t.G.hom)
      (by
        show pullback.fst (Over.mk x₁).hom Xo.univ.t.G.hom ≫ spMap χ ≫ x =
          pullback.snd (Over.mk x₁).hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
        rw [← hx]
        exact pullback.condition), hx, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

theorem exists_isFib {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x x' : Sp T ⟶ Xo.X}
    {x₁ x₁' : Sp Ω ⟶ Xo.X} (hx : x₁ = spMap χ ≫ x) (hx' : x₁' = spMap χ ≫ x') (Ψ : Gx x ⟶ Gx x')
    (hΨ : Ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left) :
    ∃ Ψ₁ : Gx x₁ ⟶ Gx x₁', IsFib χ Ψ Ψ₁ := by
  obtain ⟨pm, hp⟩ := exists_isCan χ hx
  obtain ⟨pm', hp'⟩ := exists_isCan χ hx'
  let Ψ₁ : Gx x₁ ⟶ Gx x₁' := pullback.lift (f := (Over.mk x₁').hom) (g := Xo.univ.t.G.hom)
    (fst (Over.mk x₁) Xo.univ.t.G).left (pm ≫ Ψ ≫ (snd (Over.mk x') Xo.univ.t.G).left) (by
      simp only [Category.assoc]
      rw [GlobalTheory.HeckeFrCompare.snd_hom, reassoc_of% hΨ, reassoc_of% hp.2.2, ← hx']
      rfl)
  have a : Ψ₁ ≫ (fst (Over.mk x₁') Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left := pullback.lift_fst _ _ _
  have b : Ψ₁ ≫ (snd (Over.mk x₁') Xo.univ.t.G).left = pm ≫ Ψ ≫ (snd (Over.mk x') Xo.univ.t.G).left :=
    pullback.lift_snd _ _ _
  refine ⟨Ψ₁, pm, pm', hp, hp', GlobalTheory.HeckeFrCompare.gx_ext ?_ ?_, a⟩
  · rw [Category.assoc, Category.assoc, hp'.2.2, hΨ, hp.2.2, reassoc_of% a]
  · rw [Category.assoc, Category.assoc, hp'.2.1, b]

@[reducible] def fieldCAt {K : Type} [Field K] (σ : K →+* ℂ) : Field (CAt σ) :=
  { (inferInstance : CommRing (CAt σ)), (inferInstanceAs (Field ℂ) : Field (CAt σ)) with }

theorem algClosedCAt {K : Type} [Field K] (σ : K →+* ℂ) : @IsAlgClosed (CAt σ) (fieldCAt σ) :=
  inferInstanceAs (IsAlgClosed ℂ)

def HkPtC {c : Coeff l} {σ : c.F →+* ℂ} (p : ℕ) (y : FrPt Xo c (CAt σ)) (C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G))
    (z : FrPt Xo c (CAt σ)) : Prop :=
  @HkPt E _ _ _ H Dw l Xo c p (CAt σ) (fieldCAt σ) (algClosedCAt σ) _
    (@hkTr E _ _ _ H Dw l Xo c p (CAt σ) (fieldCAt σ) (algClosedCAt σ) _) y C z

end Family

section Match

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Dict GlobalTheory.LevelCusp
open scoped Matrix ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

structure QMatch (X X' : Data E r) (N : ℕ) (a : GL (Fin r) E) : Prop where
  psi : X.Ψ = X'.Ψ
  p0 : X.p0 = X'.p0
  xi : X.ξ0 = X'.ξ0
  iso : ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm X.Gm u v
  lat : ∀ v ∈ X.Λ, (N : E) • ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) ∈ X'.Λ
  lat' : ∀ w ∈ X'.Λ, (N : E) • (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) ∈ X.Λ

variable {X X' : Data E r} {N : ℕ} {a : GL (Fin r) E}

theorem QMatch.mem (h : QMatch X X' N a) (τ : X'.Ψ) : τ.1 ∈ X.Ψ := by rw [h.psi]; exact τ.2

theorem QMatch.hermC_eq (h : QMatch X X' N a) (τ : E →+* ℂ) (u v : Fin r → ℂ) :
    hermC τ X'.Gm ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ u) ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ v) =
      hermC τ X.Gm u v := by
  rw [hermC_of_herm (ε := 1) (fun u v => by rw [h.iso, one_mul]), map_one, one_mul]

theorem QMatch.dmin_eq (h : QMatch X X' N a) (x : Frame X.Ψ r) (τ : X'.Ψ) (i : Fin (r + 1)) :
    dmin X'.Gm (lact a (castFr h.psi x)) τ i = dmin X.Gm x ⟨τ.1, h.mem τ⟩ i := by
  unfold dmin
  congr 1
  ext p q
  exact h.hermC_eq τ.1 (col (mat x ⟨τ.1, h.mem τ⟩) p) (col (mat x ⟨τ.1, h.mem τ⟩) q)

theorem QMatch.mem_dom (h : QMatch X X' N a) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact a (castFr h.psi x) ∈ X'.dom := fun τ => by
  refine ⟨?_, fun i => by rw [h.dmin_eq, ← h.p0]; exact (hx _).2 i⟩
  have e : mat (lact a (castFr h.psi x)) τ =
      (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, h.mem τ⟩ := rfl
  rw [e, Matrix.det_mul]
  refine mul_ne_zero ?_ (hx _).1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, map_ne_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 a.isUnit).ne_zero

end Match

end GlobalTheory.HeckeEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HyperbolicPairSplitTorus
open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd

noncomputable section

namespace GlobalTheory.SplitTorus

variable {n : ℕ} (ε : Fin n → Bool)

def bJ (u y : Fin n → ℂ) : ℂ := star u ⬝ᵥ (Jm ε *ᵥ y)

variable {ε}

theorem coord {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (b : Fin n) (y : Fin n → ℂ) :
    bJ ε (P *ᵥ Pi.single b 1) y = ((Pᴴ * Jm ε * P) *ᵥ (P⁻¹ *ᵥ y)) b := by
  have hPP : P * P⁻¹ = 1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).1 hP)
  conv_lhs => rw [show y = P *ᵥ (P⁻¹ *ᵥ y) by rw [mulVec_mulVec, hPP, one_mulVec]]
  rw [bJ, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  simp [Pi.star_def, Pi.single_apply, dotProduct]

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0)
include hP hpq hG

end

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0)
include hP hpq hG

end

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

end GlobalTheory.SplitTorus

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoMean

theorem isThetaFunO_bounded {D : D7} (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (F : WO V W → ℂ) (hF : IsThetaFunO ψ V W F) : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.cont.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨γ, ⟨γ', rfl⟩, hx⟩ := hKc x
  have hq := hF.quasi γ' x
  have e : (((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ') = ratW W V γ' := rfl
  rw [e] at hx
  have h1 := hψ.1.2.1 (-(symplOH V W (ratW W V γ') x))
  have := hC _ hx
  rw [hq, norm_mul, h1, one_mul] at this
  exact this

theorem continuous_emb {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) : Continuous (emb V W P Q) := by
  unfold emb
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem continuous_meanX : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ F : WO V W → ℂ, IsThetaFunO ψ V W F → Continuous (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F) := by
  intro D V W a b P Q ψ hψ μ 𝓨 hμ F hF
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  obtain ⟨-, -, i3, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  haveI : FirstCountableTopology (WO V W) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨C, hC⟩ := isThetaFunO_bounded V W ψ hψ F hF
  unfold meanX
  refine continuous_of_dominated (bound := fun _ => C) (fun x => ?_) (fun x => ?_) (integrable_const C) ?_
  · exact (hF.cont.comp ((continuous_emb V W P Q).add continuous_const)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => hC _
  · exact Filter.Eventually.of_forall fun y => hF.cont.comp (continuous_const.add continuous_id)

end GlobalTheory.IsoMean

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_isotropicSandwichMean_translation : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ F : WO V W → ℂ, IsThetaFunO ψ V W F → Continuous (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F) := by
  first | exact @GlobalTheory.IsoMean.continuous_meanX | exact GlobalTheory.IsoMean.continuous_meanX | (intros; apply GlobalTheory.IsoMean.continuous_meanX <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HkIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

abbrev Fib (Xo : Moduli Dw l) {K : Type} [CommRing K] (x : Sp K ⟶ Xo.X) : Over (Sp K) :=
  (Over.pullback x).obj Xo.univ.t.G

variable {Xo : Moduli Dw l} {c : Coeff l}

def Lin {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') : Prop :=
  ∀ a : 𝓞 E, (Over.pullback x).map (Xo.univ.t.act.act a) ≫ f = f ≫ (Over.pullback x').map (Xo.univ.t.act.act a)

def IsPair (N : ℕ) {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x')
    (f' : Fib Xo x' ⟶ Fib Xo x) : Prop :=
  IsMonHom f ∧ IsMonHom f' ∧ f ≫ f' = 𝟙 _ ^ N ∧ f' ≫ f = 𝟙 _ ^ N ∧ Lin f ∧ Lin f'

def HkWith (p : ℕ) {K : Type} [Field K] [Algebra c.F K] (y z : FrPt Xo c K) (f : Fib Xo y.x ⟶ Fib Xo z.x)
    (f' : Fib Xo z.x ⟶ Fib Xo y.x) : Prop :=
  IsPair (p ^ 2) f f' ∧ (∀ τ j, IsLieImageH p f.left (y.u τ j) (z.u τ j)) ∧
    IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj y.x z.x f.left) p y.s z.s

def HkOver (p : ℕ) {K : Type} [Field K] [Algebra c.F K] (y z : FrPt Xo c K) : Prop :=
  AllRat Xo y.x (p ^ 2) ∧ AllRat Xo z.x (p ^ 3) ∧ ∃ f f', HkWith p y z f f'

def IsBC {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) {x x' : Sp K ⟶ Xo.X} {w w' : Sp L ⟶ Xo.X}
    (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') : Prop :=
  w = spMap φ ≫ x ∧ w' = spMap φ ≫ x' ∧
    ∀ (π : pullback Xo.univ.t.G.hom w ⟶ pullback Xo.univ.t.G.hom x)
      (π' : pullback Xo.univ.t.G.hom w' ⟶ pullback Xo.univ.t.G.hom x'),
      π ≫ pullback.fst _ _ = pullback.fst _ _ → π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ →
      π' ≫ pullback.fst _ _ = pullback.fst _ _ → π' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ →
      (g.left : pullback Xo.univ.t.G.hom w ⟶ pullback Xo.univ.t.G.hom w') ≫ π' =
        π ≫ (f.left : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x')

def Ext {T : CDVR} {x x' : Sp T.Fr ⟶ Xo.X} {G G' : SAB H (Sp T.V)} {t t' : SAB H (Sp T.Fr)}
    (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr)))
    (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr)))
    (f : Fib Xo x ⟶ Fib Xo x') (F : G.G ⟶ G'.G) : Prop :=
  ∃ ψ : t.G ⟶ t'.G, IsMonHom ψ ∧ ψ.left ≫ n₂.φ = m₂.φ ≫ F.left ∧
    ∀ (g : t.G.left ⟶ pullback Xo.univ.t.G.hom x) (g' : t'.G.left ⟶ pullback Xo.univ.t.G.hom x'),
      g ≫ pullback.fst _ _ = m₁.φ → g ≫ pullback.snd _ _ = t.G.hom →
      g' ≫ pullback.fst _ _ = n₁.φ → g' ≫ pullback.snd _ _ = t'.G.hom →
      g ≫ (f.left : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x') = ψ.left ≫ g'

def Reg {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (I : IntData Xo c T io y.1) (M : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))) : Prop :=
  ∃ σ, PullbackSections.SecTie I (M ^ 2) (PullbackSections.zCast Xo.univ.t.G (PullbackSections.natCast_sq M) F) σ

def IsTransl (M : ℕ) {K : Type} [CommRing K] {x : Sp K ⟶ Xo.X} (s : LB.Sec (PPx x))
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk x))) : Prop :=
  ∃ a, IsVtOver Xo.univ.t.G Xo.univ.t.PP M (fun u => u ^ (M ^ 2) = 1) s a F

def IsPullOf (M : ℕ) {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') (a : K)
    (s' : LB.Sec (PPx x')) (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk x))) : Prop :=
  ∃ (β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) ((M : ℤ) ^ 2))) (s'' : LB.Sec (PPx x')),
    IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) _ β ∧ (∀ i, s''.f i = scal x' a i * s'.f i) ∧
      IsCarried Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) _ β s'' t

def IsTranslSum (M : ℕ) {K : Type} [CommRing K] {x : Sp K ⟶ Xo.X} (s : LB.Sec (PPx x))
    (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk x))) : Prop :=
  ∃ (n : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk x))),
    (∀ i, IsTransl M s (F i)) ∧ ∀ j, t.f j = ∑ i, (F i).f j

end GlobalTheory.HkIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAlg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LocWeil
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeConj

theorem continuous_cA (D : D7) : Continuous (cA D) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap
  exact this

end GlobalTheory.HeckeConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.AdjLawPf

variable {D : D7}

theorem inv_mul_gram (V : HSp D) : ((HSpace.gram V)⁻¹.map (incA D)) * ((HSpace.gram V).map (incA D)) = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.OrientedAdjoint.gram_mul_inv V)

theorem gramI_conj (V : HSp D) : (((HSpace.gram V)⁻¹.map (incA D)).map (cA D))ᵀ = ((HSpace.gram V)⁻¹.map (incA D)) :=
  GlobalTheory.OrientedAdjoint.inv_conj (cA D) _ _ (GlobalTheory.OrientedAdjoint.gram_mul_inv V) (GlobalTheory.OrientedAdjoint.gram_conj V)

theorem conjT_mul {m n k : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) (B : Matrix (Fin n) (Fin k) (AE D)) :
    ((A * B).map (cA D))ᵀ = (B.map (cA D))ᵀ * (A.map (cA D))ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem conjT_conjT {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) : (((A.map (cA D))ᵀ).map (cA D))ᵀ = A := by
  ext i j; simp [GlobalTheory.DualPairCheck.cA_cA]

theorem adjO_eq (S T : HSp D) (y : WO T S) :
    (adjO S T y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      HMul.hMul (HMul.hMul ((HSpace.gram T)⁻¹.map (incA D)) ((y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D)).transpose) ((HSpace.gram S).map (incA D)) := rfl

theorem adj_invol (S T : HSp D) (x : WO S T) : adjO S T (adjO T S x) = x := by
  rw [adjO_eq, adjO_eq, conjT_mul, conjT_mul, conjT_conjT, GlobalTheory.OrientedAdjoint.gram_conj, gramI_conj]
  simp only [← Matrix.mul_assoc]
  rw [inv_mul_gram, Matrix.one_mul, Matrix.mul_assoc, inv_mul_gram, Matrix.mul_one]

theorem adj_add (S T : HSp D) (y y' : WO T S) : adjO S T (y + y') = adjO S T y + adjO S T y' := by
  rw [adjO_eq, adjO_eq, adjO_eq]
  have e : ((y + y' : WO T S) : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D) =
      (y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D) + (y' : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D) := by
    ext i j; simp
  rw [e, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem hO_eq (S T : HSp D) (x y : WO S T) : hO S T x y = Matrix.trace (adjO T S y * x) := by
  rw [adjO_eq]
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem hO_herm (S T : HSp D) (x y : WO S T) : cA D (hO S T x y) = hO S T y x := by
  rw [hO_eq, hO_eq]
  have e : cA D (Matrix.trace (adjO T S y * x)) = Matrix.trace (((adjO T S y * x).map (cA D))ᵀ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.trace_transpose]; simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]
  rw [e, conjT_mul, adjO_eq, conjT_mul, conjT_mul, conjT_conjT, GlobalTheory.OrientedAdjoint.gram_conj, gramI_conj,
    adjO_eq, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

theorem hO_adj (S T : HSp D) (x y : WO T S) : hO S T (adjO S T x) (adjO S T y) = hO T S y x := by
  rw [hO_eq, hO_eq, adj_invol, Matrix.trace_mul_comm]

theorem adj_sympl (S T : HSp D) (y y' : WO T S) :
    symplO S T (adjO S T y) (adjO S T y') = -symplO T S y y' := by
  unfold symplO
  rw [hO_adj, ← hO_herm, ← GlobalTheory.DualPairCheck.trace_cA, map_mul, GlobalTheory.DualPairCheck.cA_cA,
    GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, neg_mul, map_neg]

theorem symplOH_adj (S T : HSp D) (y y' : WO T S) :
    symplOH S T (adjO S T y) (adjO S T y') = -symplOH T S y y' := by
  unfold symplOH; rw [adj_sympl, mul_neg]

end GlobalTheory.AdjLawPf

namespace GlobalTheory.AdjLawPf

variable {D : D7}

theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by simp [Formalism.L2.Theta.mt]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem mt_mul_inv (V : HSp D) (g : GA D V) : mt V g * mt V g⁻¹ = 1 := by
  rw [← mt_mul, mul_inv_cancel, mt_one]

theorem conjT_gram (V : HSp D) (g : GA D V) :
    ((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) = ((HSpace.gram V).map (incA D)) * mt V g⁻¹ := by
  calc ((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) = ((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) * (mt V g * mt V g⁻¹) := by
        rw [mt_mul_inv, Matrix.mul_one]
    _ = (((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) * mt V g) * mt V g⁻¹ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [GlobalTheory.DualPairCheck.mt_unit]

theorem gramI_conjT (V : HSp D) (h : GA D V) :
    ((HSpace.gram V)⁻¹.map (incA D)) * ((mt V h⁻¹).map (cA D))ᵀ = mt V h * ((HSpace.gram V)⁻¹.map (incA D)) := by
  have k : ((mt V h⁻¹).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) = ((HSpace.gram V).map (incA D)) * mt V h := by
    rw [conjT_gram, inv_inv]
  calc ((HSpace.gram V)⁻¹.map (incA D)) * ((mt V h⁻¹).map (cA D))ᵀ = ((HSpace.gram V)⁻¹.map (incA D)) * ((mt V h⁻¹).map (cA D))ᵀ * (((HSpace.gram V).map (incA D)) * ((HSpace.gram V)⁻¹.map (incA D))) := by
        rw [GlobalTheory.OrientedAdjoint.gram_mul_inv, Matrix.mul_one]
    _ = ((HSpace.gram V)⁻¹.map (incA D)) * (((mt V h⁻¹).map (cA D))ᵀ * ((HSpace.gram V).map (incA D))) * ((HSpace.gram V)⁻¹.map (incA D)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [k, ← Matrix.mul_assoc, inv_mul_gram, Matrix.one_mul]

theorem adj_act (S T : HSp D) (g : GA D S) (h : GA D T) (y : WO T S) :
    adjO S T (actO T S h g y) = actO S T g h (adjO S T y) := by
  unfold actO
  rw [adjO_eq, adjO_eq, conjT_mul, conjT_mul]
  simp only [← Matrix.mul_assoc]
  rw [gramI_conjT, Matrix.mul_assoc _ ((mt S g).map (cA D))ᵀ, conjT_gram]
  simp only [Matrix.mul_assoc]

theorem adj_ratW (S T : HSp D) (γ : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    adjO S T (ratW S T γ) = ratW T S (HMul.hMul (HMul.hMul (HSpace.gram T)⁻¹ (γ.map star)ᵀ) (HSpace.gram S)) := by
  have e : ((γ.map (incA D)).map (cA D))ᵀ = ((γ.map star)ᵀ).map (incA D) := by
    ext i j; simp [GlobalTheory.DualPairCheck.cA_incA]
  rw [adjO_eq]
  unfold ratW
  rw [e, Matrix.map_mul, Matrix.map_mul]

theorem adj_rat_of (S T : HSp D) (y : WO T S) (hy : y ∈ ratL S T) : adjO S T y ∈ ratL T S := by
  obtain ⟨γ, rfl⟩ := hy
  exact ⟨_, (adj_ratW S T γ).symm⟩

theorem adj_rat (S T : HSp D) (y : WO T S) : adjO S T y ∈ ratL T S ↔ y ∈ ratL S T :=
  ⟨fun h => by have := adj_rat_of T S _ h; rwa [adj_invol] at this, adj_rat_of S T y⟩

theorem adj_half (S T : HSp D) (e : AE D) (y : WO T S) (hy : IsHalf e y) : IsHalf (cA D e) (adjO S T y) := by
  intro i j
  have hy' : ∀ k l, cA D e * cA D (y k l) = cA D (y k l) := fun k l => by rw [← map_mul, hy]
  rw [adjO_eq]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  linear_combination (incA D ((HSpace.gram T)⁻¹ i l) * incA D (HSpace.gram S k j)) * hy' k l

theorem adj_cont (S T : HSp D) : Continuous (adjO S T) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have h : Continuous fun y : WO T S => ((y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D))ᵀ :=
    (continuous_id.matrix_map (GlobalTheory.HeckeConj.continuous_cA D)).matrix_transpose
  exact (continuous_const.matrix_mul h).matrix_mul continuous_const

set_option synthInstance.maxHeartbeats 400000 in
theorem adj_infPart (S T : HSp D) (u : WO T S) (hu : u.map (infPart D) = 0) : (adjO S T u).map (infPart D) = 0 := by
  have h0 : ∀ k l, infPart D (u k l) = 0 := fun k l => by
    have := congrFun (congrFun hu k) l
    simpa only [Matrix.map_apply, Matrix.zero_apply] using this
  refine Matrix.ext fun i j => ?_
  show infPart D (adjO S T u i j) = 0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [adjO_eq, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    GlobalTheory.PlaceIdem.infPart_cA, h0, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]

set_option synthInstance.maxHeartbeats 400000 in
theorem adj_finPart (S T : HSp D) (u : WO T S) (hu : u.map (finPart D) = 0) : (adjO S T u).map (finPart D) = 0 := by
  have h0 : ∀ k l, finPart D (u k l) = 0 := fun k l => by
    have := congrFun (congrFun hu k) l
    simpa only [Matrix.map_apply, Matrix.zero_apply] using this
  refine Matrix.ext fun i j => ?_
  show finPart D (adjO S T u i j) = 0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [adjO_eq, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    GlobalTheory.PlaceIdem.finPart_cA, h0, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]

def adjHom (S T : HSp D) : WO T S →+ WO S T := AddMonoidHom.mk' (adjO S T) (adj_add S T)

theorem conj_psi (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ a]
  simp

theorem adj_heis (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (S T : HSp D) (y : WO T S) (f : WO S T → ℂ) :
    heisO ψ T S y (dag S T f) = dag S T (heisO ψ S T (adjO S T y) f) := by
  funext w
  simp only [heisO, dag, map_mul, adj_add, symplOH_adj, conj_psi ψ hψ, neg_neg]

theorem adj_theta (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (S T : HSp D) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ T S (dag S T f) := {
  quasi γ w := by
    simp only [dag]
    rw [adj_add, adj_ratW, hf.quasi, map_mul, conj_psi ψ hψ, ← adj_ratW, symplOH_adj]
    simp only [neg_neg]
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U.comap (adjHom S T), hUo.preimage (adj_cont S T), fun u hu h0 => ?_⟩
    rw [adj_heis ψ hψ]
    exact congrArg (dag S T) (hU (adjO S T u) hu (adj_infPart S T u h0))
  cont := Complex.continuous_conj.comp (hf.cont.comp (adj_cont S T))
  smooth k L hL hfin w := by
    have h := hf.smooth k ((adjHom S T).comp L) ((adj_cont S T).comp hL) (fun t => adj_finPart S T _ (hfin t))
      (adjO S T w)
    have e : (fun t => dag S T f (w + L t)) =
        fun t => Complex.conjCLE (f (adjO S T w + (adjHom S T).comp L t)) := by
      funext t; simp [dag, adj_add, adjHom]
    rw [e]
    exact Complex.conjCLE.contDiff.comp h }

theorem adjLaw : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, AdjLaw ψ S T := by
  intro D ψ hψ S T
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  exact { invol := adj_invol S T
          add := adj_add S T
          cont := adj_cont S T
          sympl := adj_sympl S T
          act := adj_act S T
          rat := adj_rat S T
          half := adj_half S T
          Heisenberg₂ := adj_heis ψ hn S T
          theta := adj_theta ψ hn S T }

end GlobalTheory.AdjLawPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianAdjoint_laws_standardCharacter : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, AdjLaw ψ S T := by
  first | exact @GlobalTheory.AdjLawPf.adjLaw | exact GlobalTheory.AdjLawPf.adjLaw | (intros; apply GlobalTheory.AdjLawPf.adjLaw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffKAverageRight
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.AvgRightLp

end GlobalTheory.AvgRightLp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuumIsometryOfSkeletonDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuumIsometryOfSkeletonDatum
open Formalism.BasicNotions

namespace GlobalTheory

theorem vacuumFock_all_records : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D := GlobalTheory.T.fockVectors_overVacuum_isometry

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuumIsometryOfSkeletonDatumStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D := by
  first | exact @GlobalTheory.vacuumFock_all_records | exact GlobalTheory.vacuumFock_all_records | (intros; apply GlobalTheory.vacuumFock_all_records <;> assumption)
end
end
