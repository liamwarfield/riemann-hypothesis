module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentCompletionIffCharacterDual
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorOZeroEqJetP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentSemilinearOfBasis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepExponents
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceCharacterEquivariance
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNormStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingOrbitMemParabolicMulStabiliser

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataLocalRelation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.UnrWeil

theorem natCast_mem_of_isConjPl {D : D7} (n : ℕ) {PP PP' : Formalism.L2.DIV.Pl D.host.E} (h : Lev.IsConjPl PP' PP)
    (hn : ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : ((n : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  by_contra hn'
  obtain ⟨y, c, hc, hyc⟩ := PP'.isMaximal.exists_inv hn'
  obtain ⟨c', hc', e⟩ := h c hc
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have key : (1 : 𝓞 D.host.E) = RingOfIntegers.mapRingHom (starRingEnd D.host.E) y * ((n : ℕ) : 𝓞 D.host.E) + c' := by
    have h1 := congrArg (fun z : 𝓞 D.host.E => star (algebraMap (𝓞 D.host.E) D.host.E z)) hyc
    simp only [map_add (f := _), map_mul, map_natCast, map_one, star_add, star_mul', star_natCast, star_one] at h1
    have hy : algebraMap (𝓞 D.host.E) D.host.E (RingOfIntegers.mapRingHom (starRingEnd D.host.E) y) =
        star (algebraMap (𝓞 D.host.E) D.host.E y) := rfl
    have hc2 : algebraMap (𝓞 D.host.E) D.host.E c' = star (algebraMap (𝓞 D.host.E) D.host.E c) := e
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    simp only [map_add (f := _), map_mul, map_natCast, map_one, hy, hc2]
    rw [← h1]
  rw [key]
  exact PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ hn) hc'

theorem not_both_mem {D : D7} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (PP : Formalism.L2.DIV.Pl D.host.E)
    (h1 : ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (h2 : ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  obtain ⟨a, b, hab⟩ : IsCoprime ((p : ℕ) : 𝓞 D.host.E) ((q : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left a h1) (PP.asIdeal.mul_mem_left b h2)))

end GlobalTheory.Fam.UnrWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTranslatesOfValuesFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTranslatesOfValuesFrames
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm

theorem isTr_unique {ι : Type} [Fintype ι] {n : ℕ} {G : ι → Matrix (Fin n) (Fin n) ℂ} {g : ι → Matrix (Fin n) (Fin n) ℂ}
    {y₁ y₂ y' : Frames G} (h₁ : IsTr g y₁ y') (h₂ : IsTr g y₂ y') : y₁.1 = y₂.1 := by
  funext τ
  have hu : IsUnit (g τ).det := by
    have h := y'.2 τ
    rw [h₁ τ, Matrix.det_mul] at h
    exact isUnit_of_mul_isUnit_left h
  have e : g τ * y₁.1 τ = g τ * y₂.1 τ := by rw [← h₁ τ, ← h₂ τ]
  calc y₁.1 τ = (g τ)⁻¹ * (g τ * y₁.1 τ) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = (g τ)⁻¹ * (g τ * y₂.1 τ) := by rw [e]
    _ = y₂.1 τ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

theorem jOf_exists : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks), IsInfFam R.θ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), ∃ J, JOf R j J := by
  intro B X I _ _ l Z G _ _ Pl0 T F Ks _ _ _ R _ j
  refine ⟨fun v k z' => if h : ∃ z : FrN (I.rec7 l Z) (B.R.N B.R.m - 1),
      IsTr (infM R.θ _ (rankP (I.rec7 l Z)) k) z z' then j v ⟨h.choose.1, h.choose.2⟩ else 0, ?_⟩
  intro v k _ z z' hz
  have h : ∃ z : FrN (I.rec7 l Z) (B.R.N B.R.m - 1), IsTr (infM R.θ _ (rankP (I.rec7 l Z)) k) z z' := ⟨z, hz⟩
  simp only [dif_pos h]
  have e := isTr_unique h.choose_spec hz
  exact congrArg (j v) (Subtype.ext e)

end GlobalTheory.AdForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTranslatesOfValuesFramesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translates_of_values_frames : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks), IsInfFam R.θ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), ∃ J, JOf R j J := by
  first | exact @GlobalTheory.AdForm.jOf_exists | exact GlobalTheory.AdForm.jOf_exists | (intros; apply GlobalTheory.AdForm.jOf_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BcPrVMemLevelVLOfMoves
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem prV_toEAf_eq_swap (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (a : AE D) :
    Formalism.UG.prV (E := D.host.E) v (Formalism.IndefR.Datum.toEAf D a) =
      GlobalTheory.StabConjIndex.swap v (GlobalTheory.AdelicU.compFin D.host.F D.host.E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]


set_option maxHeartbeats 1000000 in
theorem bc_prV_mem_levelVL_of_moves : ∀ (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) (L : GlobalTheory.FinPl.Lat S)
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), L.FG →
    (∀ x : Fin n → D.host.E, x ∈ Λ ↔ (fun i => x (finCongr hn i)) ∈ L) →
    ∀ (κ : GA D S) (g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    GlobalTheory.AdForm.finM S hn κ = g.1 → ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    GlobalTheory.FinPl.Moves S κ L L (· = v) →
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g ∈
      Formalism.UG.levelVL (Formalism.L2.Forms.sigD D) (S.gram.reindex (finCongr hn) (finCongr hn)) v Λ := by
  intro D S n hn L Λ hL hΛ κ g hg v hm
  subst hn
  have hΛL : Λ = L := by
    ext x; rw [hΛ x]; rfl
  subst hΛL
  have h1 := (GlobalTheory.StMoves.moves_iff_stabLoc S Λ hL v κ).1 hm
  have h2 := GlobalTheory.StabConjIndex.map_stabLoc (Formalism.L2.Forms.sigD D) S.gram v Λ
  have h3 : GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram v (GlobalTheory.AdelicU.proj _ S.gram v κ) ∈
      Formalism.UG.levelVL (Formalism.L2.Forms.sigD D) S.gram v Λ := h2 ▸ ⟨_, h1, rfl⟩
  have hgram : (S.gram.reindex (finCongr (rfl : S.rank = S.rank)) (finCongr rfl)) = S.gram := by
    ext i j; simp
  have hp := GlobalTheory.AdelicU.matHom_proj (Formalism.L2.Forms.sigD D) S.gram v κ
  have hE : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g =
      GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram v (GlobalTheory.AdelicU.proj _ S.gram v κ) := by
    ext i j
    have hij := congrFun (congrFun hg i) j
    have e1 : (GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram v (GlobalTheory.AdelicU.proj _ S.gram v κ)).val i j =
        GlobalTheory.StabConjIndex.swap v ((GlobalTheory.AdelicU.matHom (Fv D.host.F v) (Formalism.L2.Forms.sigD D) S.gram
          (GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram v κ)).val i j) := rfl
    rw [e1, hp]
    show Formalism.UG.prV v (g.1 i j) = GlobalTheory.StabConjIndex.swap v (GlobalTheory.AdelicU.compFin _ _ v _)
    rw [← hij]
    exact prV_toEAf_eq_swap D v _
  rw [hgram, hE]
  exact h3

theorem levelVL_eq_of_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {Lb Λ : Submodule (𝓞 E) (Fin n → E)} {T : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} (hT : (T : 𝓞 F) ∉ v.asIdeal)
    (h1 : ∀ x ∈ Lb, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) (h2 : ∀ j, (Pi.single j (T : E) : Fin n → E) ∈ Lb)
    (h1' : ∀ x ∈ Λ, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) (h2' : ∀ j, (Pi.single j (T : E) : Fin n → E) ∈ Λ) :
    Formalism.UG.levelVL σ J v Lb = Formalism.UG.levelVL σ J v Λ := by
  have e1 := GlobalTheory.Mem.Col2.ChartLevel.latS_eq_std hT h1 h2
  have e2 := GlobalTheory.Mem.Col2.ChartLevel.latS_eq_std hT h1' h2'
  unfold Formalism.UG.levelVL
  exact congrArg _ (e1.trans e2.symm)

end GlobalTheory.FamTrace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNonzeroJetScaleTrueColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiZeroEmbeddingValue
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk
open scoped TensorProduct Classical
namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xi_zero_embedding_value (D : D7) (hc : D.host.ccK = ⊤) (τ : D.what₂.Tau) :
    tauE D τ D.host.xi0 = Complex.I * ((Real.sqrt D.host.d)⁻¹ : ℝ) := by
  have h1 : tauE D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℝ) :=
    ((Formalism.BasicNotions.factEmb D.R D.host).2 _).2 (D.eTau τ).2
  have hd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (Nat.cast_pos.2 D.host.hyp.2.1.pos)
  rw [Host.xi0, hc, Ideal.absNorm_top, map_div₀, map_mul, h1, map_natCast, map_neg, map_one]
  have : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.ne'
  push_cast
  field_simp
  simp

theorem stdPair_world {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z)) (hψ : IsStdChar (I.rec7 l Z) ψ (-1)) (hθ : IsInfFam θ)
    (i : ℕ) : StdPair θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) I.A.δ I.A.sc ψ := by
  obtain ⟨hs, hX, -⟩ := hI.spaces
  have hg : ∀ j, ((I.rec7 l Z).sp.X j).gram = 1 := fun j => by
    have e : (I.rec7 l Z).sp.X j = Formalism.BasicNotions.Examples₂.posSpace hs (B.R.N j) := hX j
    rw [e]
    refine Matrix.ext fun a b => ?_
    refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs (B.R.N j) (fun _ => false) (B.R.N j) 0 a b).trans ?_
    by_cases h : a = b
    · subst h
      rw [Matrix.one_apply_eq]
      exact (if_pos rfl).trans (by simp [Formalism.BasicNotions.Examples₂.sgn]; rfl)
    · rw [Matrix.one_apply_ne h]
      exact if_neg h
  have hr : ∀ j, ((I.rec7 l Z).sp.X j).rank = B.R.N j := fun j => by
    have e : (I.rec7 l Z).sp.X j = Formalism.BasicNotions.Examples₂.posSpace hs (B.R.N j) := hX j
    rw [e]; rfl
  have hev : ∀ j, Even (B.R.N j) := fun j =>
    B.R.k_even.add (Even.mul_left (B.R.t_odd.add_one) j)
  have hδ : I.J.δ ≠ 0 := I.J.δ_ne_zero
  have hd : 0 < Real.sqrt B.host.d := Real.sqrt_pos.2 (Nat.cast_pos.2 B.host.hyp.2.1.pos)
  refine ⟨hψ, hθ, hg _, hg _, (I.rec7 l Z).sp.X_sig _, (I.rec7 l Z).sp.X_sig _, ?_, B.ccK_top, hδ,
    xi_zero_embedding_value _ B.ccK_top, ?_⟩
  · rw [hr, hr]
    refine ⟨?_, ?_, hev _, hev _⟩
    · have := B.R.m_add_three_le_k; unfold Ranks.N; omega
    · unfold Ranks.N; nlinarith
  · have hA := Formalism.MainNotions.Ext.area_lamOf (I.rec7 l Z) ⊤ top_ne_bot I.J.δ hδ
    rw [Formalism.MainNotions.Ext.discr_K (I.rec7 l Z).host, Ideal.absNorm_top] at hA
    have hA' : Formalism.MainNotions.TaylorLogMetric.area (Th.lamOf B.host ⊤ I.J.δ) = ‖I.J.δ‖ ^ 2 * Real.sqrt B.host.d / 2 := by
      refine hA.trans ?_
      simp
      exact Or.inl rfl
    show (Formalism.MainNotions.TaylorLogMetric.area (Th.lamOf B.host ⊤ I.J.δ))⁻¹ * ‖I.J.δ‖ ^ 2 = 2 * (Real.sqrt B.host.d)⁻¹
    rw [hA']
    have : ‖I.J.δ‖ ≠ 0 := norm_ne_zero_iff.2 hδ
    field_simp

end GlobalTheory.AdForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNonzeroJetScaleTrueColumns
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.JetScales

theorem exists_jetS : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X →
    ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ →
      ∃ s, JetS I l Z ψ θ s := by
  intro B X I hI hP l Z ψ θ hψ hθ
  have hstep : ∀ j (hj : j + 1 ≤ B.R.m), ∃ s : ℂ, s ≠ 0 ∧ ∀ f, IsHol θ ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) ψ f → ∀ P,
      pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 =
        jetP _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) s (ColDat.xiS θ j hj f) P :=
    fun j hj => GlobalTheory.AdForm.JetRead.pureTensorO_zero_eq_jetP (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj))
      (rankN (I.rec7 l Z) (j + 1) hj) I.A.δ I.A.sc (stdPair_world I hI l Z ψ θ hψ hθ j)
  refine ⟨fun j => if hj : j + 1 ≤ B.R.m then (hstep j hj).choose else 1, fun j hj => ?_⟩
  simp only [dif_pos hj]
  exact (hstep j hj).choose_spec

end GlobalTheory.AdForm.JetScales
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNonzeroJetScaleTrueColumnsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_jetScale_trueColumns : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∃ s, JetS I l Z ψ θ s := by
  first | exact @GlobalTheory.AdForm.JetScales.exists_jetS | exact GlobalTheory.AdForm.JetScales.exists_jetS | (intros; apply GlobalTheory.AdForm.JetScales.exists_jetS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLiftExactConstantProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelsCommuteExplicitConst
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelsCommuteExplicitConst
open ValuativeRel IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.KernelCommTw

noncomputable section

namespace GlobalTheory.KernelCommExplicit

theorem kernelsCommuteExplicitConst : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (l' l : kˣ →* ℂˣ), IsUnram l' → IsUnram l → ∀ (P₀ : Pair k n') (Q₀ : Pair k n), ∀ (V' V : Type) [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V] (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V) (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V), (∀ (g : GL n' k) (h : GL n k) (v : V') (Ψ Ψ' : SB (Matrix n n' k)), (∀ x, Ψ'.1 x = (l' (Matrix.GeneralLinearGroup.det g) : ℂ) * (l (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (π' g v) Ψ' = π h (θ v Ψ)) → ∃ K : EqForm π' →ₗ[ℂ] EqForm π, (∀ φ, (K φ).1 Q₀ = θ (φ.1 P₀) (phiOneSB P₀ Q₀)) ∧ (∀ (s : 𝓀[k]ˣ) φ, (K ⟨dia s φ.1, dia_mem_EqForm s φ.2⟩).1 = dia s (K φ).1) ∧ ∀ φ : EqForm π', φ.1 ∈ Mram k n' V' → (K φ).1 ∈ Mram k n V ∧ (K ⟨FFStar q (resChar ψ hψ q) φ.1, FFStar_mem_EqForm q _ φ.2⟩).1 = ((l' q.unit : ℂ) * (l q.unit : ℂ)) • FFStar q (resChar ψ hψ q) (K φ).1 := by
  intro k _ _ _ _ n n' _ _ _ _ q ψ hψ l' l hl' hl P₀ Q₀ V' V _ _ _ _ π' π θ hθ
  refine ⟨LinearMap.codRestrict (EqForm π) (KK hl hθ P₀ Q₀ ∘ₗ (EqForm π').subtype)
    fun φ => KK_mem hl hθ P₀ Q₀ φ.1, fun φ => ?_, fun s φ => KK_dia hl hθ P₀ Q₀ hl' s φ.2, fun φ h =>
      ⟨KK_ram hl hθ P₀ Q₀ hl' φ.2 h, KK_FFStar hl hθ P₀ Q₀ hl' q _ φ.2 h⟩⟩
  show KK hl hθ P₀ Q₀ φ.1 Q₀ = _
  simpa using KK_smul hl hθ P₀ Q₀ φ.1 1

end GlobalTheory.KernelCommExplicit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelsCommuteExplicitConstStatement
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity ValuativeRel IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelsCommuteExplicitConstAlt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (l' l : kˣ →* ℂˣ), IsUnram l' → IsUnram l → ∀ (P₀ : Pair k n') (Q₀ : Pair k n), ∀ (V' V : Type) [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V] (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V) (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V), (∀ (g : GL n' k) (h : GL n k) (v : V') (Ψ Ψ' : SB (Matrix n n' k)), (∀ x, Ψ'.1 x = (l' (Matrix.GeneralLinearGroup.det g) : ℂ) * (l (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (π' g v) Ψ' = π h (θ v Ψ)) → ∃ K : EqForm π' →ₗ[ℂ] EqForm π, (∀ φ, (K φ).1 Q₀ = θ (φ.1 P₀) (phiOneSB P₀ Q₀)) ∧ (∀ (s : 𝓀[k]ˣ) φ, (K ⟨dia s φ.1, dia_mem_EqForm s φ.2⟩).1 = dia s (K φ).1) ∧ ∀ φ : EqForm π', φ.1 ∈ Mram k n' V' → (K φ).1 ∈ Mram k n V ∧ (K ⟨FFStar q (resChar ψ hψ q) φ.1, FFStar_mem_EqForm q _ φ.2⟩).1 = ((l' q.unit : ℂ) * (l q.unit : ℂ)) • FFStar q (resChar ψ hψ q) (K φ).1 := by
  first | exact @GlobalTheory.KernelCommExplicit.kernelsCommuteExplicitConst | exact GlobalTheory.KernelCommExplicit.kernelsCommuteExplicitConst | (intros; apply GlobalTheory.KernelCommExplicit.kernelsCommuteExplicitConst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLiftExactConstantProof
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing MeasureTheory

noncomputable section

namespace GlobalTheory.FinPl.LiftExactPf

theorem frame_card {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (α : Frame p S n) :
    Fintype.card n = S.rank := by
  have h1 := Matrix.rank_mul_le_left α.b α.b'
  have h2 := Matrix.rank_mul_le_left α.b' α.b
  rw [α.bb', Matrix.rank_one] at h1
  rw [α.b'b, Matrix.rank_one] at h2
  have h3 := Matrix.rank_le_card_width α.b
  have h4 := Matrix.rank_le_card_width α.b'
  simp only [Fintype.card_fin] at h1 h4
  omega

theorem chrPow_mul_neg {D : D7} (χ : (AE D)ˣ →* Circle) (a : (AE D)ˣ) (e : ℤ) :
    chrPow χ a e * chrPow χ a (-e) = 1 := by
  unfold chrPow
  rw [← Circle.coe_mul, ← zpow_add, add_neg_cancel, zpow_zero, Circle.coe_one]

end GlobalTheory.FinPl.LiftExactPf

namespace GlobalTheory.FinPl


open GlobalTheory.FinPl.LiftRam GlobalTheory.FinPl.LiftExactPf in
theorem liftExact : ∀ D : D7, GlobalTheory.FinPl.LiftExact D := by
  intro D k _ _ _ _ p q χ hχ
  refine ⟨-1, Or.inr rfl, ?_⟩
  intro n n' _ _ _ _ ψ S T hS vS χS χT om hW hχS hχT α β P Q a ha LS LT f₀ f hOv φ₀ hφ₀ ε
  have haq : a = p.idele q.unit := Units.ext (by rw [SplitPt.idele_val, ha]; abel)
  subst haq
  obtain ⟨lS, lT, hlS, hlT, hlSq, hlTq, hlinE⟩ := GlobalTheory.T.linearModel_splitPlace_characterEquivariance D k p q ψ S T χS χT om hW
  obtain ⟨lS₀, lT₀, -, -, hlin⟩ := GlobalTheory.T.splitPlace_linearModel_latticeVacuum_base D k p ψ S T χS χT om hW
  have hK := GlobalTheory.T.kernelsCommuteExplicitConstAlt k n n' q χ hχ lS lT (hlS hχT) (hlT hχS) P Q
  have hOv2 := hOv
  obtain ⟨hLS, hLT, hVac, -, -⟩ := hOv2
  obtain ⟨hex, hth, -⟩ := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hW.std S T α β LS LT hLS hLT f₀ hVac

  let F : SB (Matrix n n' k) → WO S T → ℂ := fun Ψ => (hex Ψ.1 Ψ.2).exists.choose
  have hF : ∀ Ψ : SB (Matrix n n' k), Over ψ α β LS LT f₀ Ψ.1 (F Ψ) := fun Ψ => (hex Ψ.1 Ψ.2).exists.choose_spec
  have hFu : ∀ (Ψ : SB (Matrix n n' k)) g, Over ψ α β LS LT f₀ Ψ.1 g → g = F Ψ :=
    fun Ψ g hg => (hex Ψ.1 Ψ.2).unique hg (hF Ψ)
  have hFth : ∀ Ψ, IsThetaFunO ψ S T (F Ψ) := fun Ψ => (hth _ _ (hF Ψ)).1
  have hFlin : ∀ (a : ℂ) (Ψ Ψ' : SB (Matrix n n' k)), F (a • Ψ + Ψ') = a • F Ψ + F Ψ' := fun a Ψ Ψ' =>
    (hFu (a • Ψ + Ψ') _ ((hlin n n' α β LS LT f₀ Ψ.1 (F Ψ) (hF Ψ)).2.2 a Ψ'.1 (F Ψ') (hF Ψ'))).symm
  have hF0 : F 0 = 0 := by
    have h1 := hFlin 1 0 0
    simp only [one_smul, add_zero] at h1
    have h2 : F 0 + F 0 = F 0 + 0 := by rw [← h1, add_zero]
    exact add_left_cancel h2
  have hFadd : ∀ Ψ Ψ' : SB (Matrix n n' k), F (Ψ + Ψ') = F Ψ + F Ψ' := fun Ψ Ψ' => by
    simpa using hFlin 1 Ψ Ψ'
  have hFsmul : ∀ (a : ℂ) (Ψ : SB (Matrix n n' k)), F (a • Ψ) = a • F Ψ := fun a Ψ => by
    simpa [hF0] using hFlin a Ψ 0
  have hint : ∀ (v : contAutSub S) (Ψ : SB (Matrix n n' k)) h,
      IntegrableOn (fun g => om (g, h) (F Ψ) 0 * v.1 g) vS.𝓕 vS.μ :=
    fun v Ψ h => (lift_facts hS vS hW (hFth Ψ) v.2).1 h

  let θ : contAutSub S →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] (GA D T → ℂ) :=
    LinearMap.mk₂ ℂ (fun v Ψ => liftT om vS.μ vS.𝓕 v.1 (F Ψ))
      (fun v₁ v₂ Ψ => by
        funext h
        simp only [liftT_apply, Pi.add_apply, Submodule.coe_add, mul_add]
        exact integral_add (hint v₁ Ψ h) (hint v₂ Ψ h))
      (fun a v Ψ => by
        funext h
        simp only [liftT_apply, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, mul_left_comm _ a]
        exact integral_const_mul a _)
      (fun v Ψ₁ Ψ₂ => by
        funext h
        simp only [liftT_apply, Pi.add_apply, hFadd, map_add (f := _), add_mul]
        exact integral_add (hint v Ψ₁ h) (hint v Ψ₂ h))
      (fun a v Ψ => by
        funext h
        simp only [liftT_apply, Pi.smul_apply, hFsmul, map_smul, smul_eq_mul, mul_assoc]
        exact integral_const_mul a _)
  have hθ : ∀ v Ψ, θ v Ψ = liftT om vS.μ vS.𝓕 v.1 (F Ψ) := fun v Ψ => rfl
  have hEq : ∀ (g : GL n' k) (h : GL n k) (v : contAutSub S) (Ψ Ψ' : SB (Matrix n n' k)),
      (∀ x, Ψ'.1 x = (lS (Matrix.GeneralLinearGroup.det g) : ℂ) * (lT (Matrix.GeneralLinearGroup.det h) : ℂ) *
        Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (repAut α g v) Ψ' = β.rep h (θ v Ψ) := by
    intro g h v Ψ Ψ' hΨ
    have e : F Ψ' = om (α.gl g, β.gl h) (F Ψ) := by
      refine (hFu Ψ' _ ?_).symm
      have := hlinE n n' α β LS LT f₀ Ψ.1 (F Ψ) (hF Ψ) g h
      convert this using 1
      funext x
      exact hΨ x
    funext h₁
    rw [hθ, hθ, rep_apply, liftT_apply, liftT_apply, e, repAut_val]
    simp only [rep_apply, LiftRam.om_mul]
    exact setIntegral_mul_right hS vS (fun x => om (x, h₁ * β.gl h) (F Ψ) 0 * v.1 x)
      (fun γ hγ x => by rw [om_left hW (hFth Ψ) hγ, v.2.1 γ hγ x]) (α.gl g)
  obtain ⟨K, hKval, hKdia, hKram⟩ := hK (contAutSub S) (GA D T → ℂ) (repAut α) β.rep θ hEq
  obtain ⟨φ, ⟨hφE, hφM, hφC⟩, rfl⟩ := hφ₀
  let φ' : EqForm (repAut α) := ⟨toAut hφC, fun g P₁ => Subtype.ext (hφE g P₁)⟩
  have hφ'M : φ'.1 ∈ Mram k n' (contAutSub S) := by
    letI := Fintype.ofFinite 𝓀[k]ˣ
    refine (mem_Mram _).2 fun P₁ => Subtype.ext ?_
    have := (mem_Mram _).1 hφM P₁
    simpa [φ', toAut, Submodule.coe_sum] using this
  have hFf : F (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOneSB P Q) = f := (hFu _ f hOv).symm
  have hfth : IsThetaFunO ψ S T f := hFf ▸ hFth _
  set φT : Form k n (GA D T → ℂ) := (K φ').1 with hφT
  have hφTQ : φT Q = liftT om vS.μ vS.𝓕 (φ P) f := by
    rw [hφT, hKval φ', hθ, hFf]
    rfl
  have hcQ : IsContAut T (φT Q) := by
    rw [hφTQ]
    exact (lift_facts hS vS hW hfth (hφC P)).2
  have hRam : IsRam β φT := by
    refine ⟨(K φ').2, (hKram φ' hφ'M).1, fun Q' => ?_⟩
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q Q'
    have e : φT (g • Q) = β.rep g (φT Q) := (K φ').2 g Q
    rw [e]
    exact isContAut_mul_right hcQ (β.gl g)
  set c : ℂ := (lS q.unit : ℂ) * (lT q.unit : ℂ) with hc
  have h1 := (hKram φ' hφ'M).2
  have h2 := hKdia ε ⟨FFStar q (resChar χ hχ q) φ'.1, FFStar_mem_EqForm q _ φ'.2⟩
  have h3 := hKval ⟨dia ε (FFStar q (resChar χ hχ q) φ'.1), dia_mem_EqForm ε (FFStar_mem_EqForm q _ φ'.2)⟩
  have key : liftT om vS.μ vS.𝓕 (FFStar q (resChar χ hχ q) φ (ε • P)) f =
      c • FFStar q (resChar χ hχ q) φT (ε • Q) := by
    calc liftT om vS.μ vS.𝓕 (FFStar q (resChar χ hχ q) φ (ε • P)) f
        = θ (dia ε (FFStar q (resChar χ hχ q) φ'.1) P) (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOneSB P Q) := by
          rw [hθ, hFf, dia_apply]
          exact congrArg (liftT om vS.μ vS.𝓕 · f) (toAut_FFStar q _ hφC (ε • P)).symm
      _ = (K ⟨dia ε (FFStar q (resChar χ hχ q) φ'.1), dia_mem_EqForm ε (FFStar_mem_EqForm q _ φ'.2)⟩).1 Q := h3.symm
      _ = dia ε (K ⟨FFStar q (resChar χ hχ q) φ'.1, FFStar_mem_EqForm q _ φ'.2⟩).1 Q := by rw [h2]
      _ = c • FFStar q (resChar χ hχ q) φT (ε • Q) := by rw [h1, dia_apply]; rfl

  have hQ : (0 : ℝ) < resCard k := by
    unfold resCard
    exact_mod_cast Nat.card_pos
  have hnT := frame_card β
  have hnS := frame_card α
  have hR : ((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2)) * ((resCard k : ℝ) ^ (-(T.rank : ℝ) / 2)) *
      ((resCard k : ℝ) ^ ((S.rank : ℝ) / 2)) = 1 := by
    rw [← Real.rpow_add hQ, ← Real.rpow_add hQ, hnT, hnS]
    convert Real.rpow_zero (resCard k : ℝ) using 2
    ring
  have hR' : (((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) *
      (((resCard k : ℝ) ^ (-(T.rank : ℝ) / 2) : ℝ) : ℂ) * (((resCard k : ℝ) ^ ((S.rank : ℝ) / 2) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hR
  have eS := chrPow_mul_neg χS (p.idele q.unit) (-1)
  have eT := chrPow_mul_neg χT (p.idele q.unit) 1
  simp only [neg_neg] at eS ⊢
  have hCc : ((((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) *
      chrPow χS (p.idele q.unit) (-1) * chrPow χT (p.idele q.unit) 1) * c = 1 := by
    rw [hc, hlSq, hlTq]
    linear_combination (chrPow χS (p.idele q.unit) (-1) * chrPow χS (p.idele q.unit) 1 *
      (chrPow χT (p.idele q.unit) 1 * chrPow χT (p.idele q.unit) (-1))) * hR' +
      (chrPow χT (p.idele q.unit) 1 * chrPow χT (p.idele q.unit) (-1)) * eS + eT
  rw [← hφTQ]
  unfold sOp
  rw [formAt_eq α hφE P, formAt_eq β hRam.1 Q, dia_apply, dia_apply, key, smul_smul, hCc, one_smul]

end GlobalTheory.FinPl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLiftExactConstantProofStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitLiftExactConstant_proof : ∀ D : D7, GlobalTheory.FinPl.LiftExact D := by
  first | exact @GlobalTheory.FinPl.liftExact | exact GlobalTheory.FinPl.liftExact | (intros; apply GlobalTheory.FinPl.liftExact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinkZeroOfChartZero
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory.MiTop

theorem besLev_per_congr {D : D7} {ρ : ℕ} {B B' : BesLev D ρ} (h : B = B') (ψ) {φ : GA D B.A → ℂ} {φ' : GA D B'.A → ℂ}
    {g : GA D B.V → ℂ} {g' : GA D B'.V → ℂ} (h1 : HEq φ φ') (h2 : HEq g g') : B.per ψ φ g = B'.per ψ φ' g' := by
  subst h
  rw [eq_of_heq h1, eq_of_heq h2]

end GlobalTheory.MiTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.ChartVal

theorem infM_fin' {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : k ∈ GfC V)
    (τ : D.what₂.Tau) : infM θ V hn k τ = 1 := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.infM_fin θ V k hk τ

end GlobalTheory.AdForm.ChartVal


open GlobalTheory.AdForm.ChartVal in
theorem GlobalTheory.AdForm.rd_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (i : ℕ) (hi : i ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi i, (∀ c, (fun z : FrN (I.rec7 l Z) (B.R.N i) => φ c ⟨z.1, z.2⟩) ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u i)) ∧ ∀ β y, ∀ γ ∈ GQ ((I.rec7 l Z).sp.X i), ∀ c, ∀ k ∈ GinfC ((I.rec7 l Z).sp.X i), ∀ (κ : A.U i β) (y' : (I.chain l u a).Y i), IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) i hi) k) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ → A.rd θ i hi β φ y (γ * (A.h i β c * k) * κ.1) = (A.chi i β κ : ℂ) * φ c.1 y' := by
  intro B X I hok hpins l Z u a Ch A hA θ hθ i hi φ hφ
  let eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hok hpins l Z u a i hi (A.bad i) (Ch i) (A.chOf i) (A.K i hi) eY
    ⟨A.kb i, hA.reads i hi⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  refine ⟨?_, ?_⟩
  · intro c
    obtain ⟨Ψ, hΨ, he⟩ := Submodule.mem_map.1 (hF (A.chOf i c))
    have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hΨ).2) ((A.K i hi (A.chOf i c)).y ⟨c, rfl⟩) (Set.mem_univ _)
    have e2 : Ψ ((A.K i hi (A.chOf i c)).y ⟨c, rfl⟩) = fun z => φ c (eY.symm z) := congrFun he ⟨c, rfl⟩
    rw [e2] at hval
    exact hval

  · intro β y γ hγ c k hk κ y' hy
    obtain ⟨Ψ, hΨ, he⟩ := Submodule.mem_map.1 (hF β)
    have hAd : Ψ ∈ AdFun (A.K i hi β).lev (embT (I.rec7 l Z)) := (Submodule.mem_inf.1 hΨ).1
    have hfun : (fun (c : {c // A.chOf i c = β}) (z : Frames (gramC (gramN (I.rec7 l Z) i hi) (embT (I.rec7 l Z)))) =>
        φ c.1 ⟨z.1, z.2⟩) = fun c => Ψ ((A.K i hi β).y c) := he.symm
    have laws := GlobalTheory.AdForm.RdLaw.rdS_laws (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X i) (B.R.N i) (rankN (I.rec7 l Z) i hi)
      (gramN (I.rec7 l Z) i hi) rfl (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev {c // A.chOf i c = β}
      (A.K i hi β).y (A.K i hi β).y_bij _ (fun c z => φ c.1 ⟨z.1, z.2⟩) (hF β) ⟨y.1, y.2⟩
    obtain ⟨hL, hK, hR, -⟩ := laws
    have hκ := (hA.U i hi β κ.1).1 κ.2
    obtain ⟨hκf, κ', hκ'⟩ := hκ
    have hchi := hA.chi i hi β κ κ' hκ'
    have hval := (GlobalTheory.AdForm.rdS_val (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X i) (B.R.N i) (rankN (I.rec7 l Z) i hi)
      (gramN (I.rec7 l Z) i hi) rfl (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev {c // A.chOf i c = β}
      (A.K i hi β).y (A.K i hi β).y_bij Ψ hAd ⟨y'.1, y'.2⟩ (A.h i β c)).2.2 ((A.K i hi β).y c) ⟨y'.1, y'.2⟩
      ((hA.h i hi β c).2.symm) (fun τ => by
        have h1 := infM_fin' θ ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (A.h i β c) (hA.h i hi β c).1 τ
        show y'.1 τ = infM θ _ _ (A.h i β c) τ * y'.1 τ
        erw [h1, Matrix.one_mul])
    show rdS θ _ (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y (fun c z => φ c.1 ⟨z.1, z.2⟩) ⟨y.1, y.2⟩
      (γ * (A.h i β c * k) * κ.1) = _
    have e1 := hL γ hγ (A.h i β c * k * κ.1)
    have e2 := hK κ.1 hκf κ' hκ' (A.h i β c * k)
    have e3 := hR k hk ⟨y'.1, y'.2⟩ hy (A.h i β c)
    have e5 := congrArg (fun F => rdS θ ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y F
      ⟨y'.1, y'.2⟩ (A.h i β c)) hfun
    have e6 : Ψ ((A.K i hi β).y c) ⟨y'.1, y'.2⟩ = φ c.1 y' := (congrFun (congrFun hfun c) ⟨y'.1, y'.2⟩).symm
    have e4 := e3.trans (e5.trans (hval.trans e6))
    rw [mul_assoc]
    exact e1.trans (e2.trans (congrArg₂ (· * ·) (congrArg (fun x : ℂˣ => (x : ℂ)) hchi.symm) e4))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTupleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (i : ℕ) (hi : i ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi i, (∀ c, (fun z : FrN (I.rec7 l Z) (B.R.N i) => φ c ⟨z.1, z.2⟩) ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u i)) ∧ ∀ β y, ∀ γ ∈ GQ ((I.rec7 l Z).sp.X i), ∀ c, ∀ k ∈ GinfC ((I.rec7 l Z).sp.X i), ∀ (κ : A.U i β) (y' : (I.chain l u a).Y i), IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) i hi) k) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ → A.rd θ i hi β φ y (γ * (A.h i β c * k) * κ.1) = (A.chi i β κ : ℂ) * φ c.1 y' := by
  first | exact @GlobalTheory.AdForm.rd_charts | exact GlobalTheory.AdForm.rd_charts | (intros; apply GlobalTheory.AdForm.rd_charts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFlatMapWeilRepresentationJoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFlatMapWeilRepresentationJoint
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.FlatCont

theorem flatAt_om_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vU : VolU D ρ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ Φ, IsThetaFunO ψ V W Φ → Continuous fun q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀ => flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) q.2.1 (om q.1 Φ) q.2.2 := by
  intro D ψ V V₀ W W₀ ρ σ dV dW vS vT χV χW om hom vU x hx Φ hΦ
  have hmaj := GlobalTheory.T.flatThetaIntegrand_locallyUniform_majorant D ψ V V₀ W W₀ ρ σ dV dW vS vT χV χW om hom vU x hx Φ hΦ
  have hmix := (GlobalTheory.T.weilMixedCoordinates_continuous_bounded_supNorm D ψ V V₀ W W₀ ρ σ dV dW vS vT χV χW om hom Φ hΦ).2
  have hψ : Continuous ψ := hom.std.1.1
  have htr : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))

  have hval : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) :=
    Units.continuous_val.comp continuous_subtype_val
  have hup : Continuous fun T : Mx D ρ ρ => upSum T := by
    unfold upSum
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact continuous_if_const _ (fun _ => (continuous_apply j).comp (continuous_apply i)) fun _ => continuous_const
  have hpsi : Continuous fun u : UX D ρ => psiUni ψ u.1 :=
    hψ.comp (htr.comp (hup.comp hval))
  have hxu : Continuous fun u : UX D ρ => (rat x : Mx D W.rank ρ) ⬝ u.1.1 :=
    continuous_const.matrix_mul hval

  have hcq : ∀ u : UX D ρ, Continuous fun q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀ =>
      flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) q.2.1 (om q.1 Φ) q.2.2 u := by
    intro u
    unfold flatFun
    refine continuous_const.mul ?_
    have hf : Continuous fun q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀ =>
        ((q.1, ((rat x : Mx D W.rank ρ) ⬝ u.1.1, q.2.1, q.2.2)) :
          (GA D V × GA D W) × Mx D W.rank ρ × Mx D V₀.rank σ × WO V₀ W₀) := by fun_prop
    have h2 := hmix.comp hf
    simp only [Function.comp_def] at h2
    exact h2

  have hcu : ∀ q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀, Continuous fun u : UX D ρ =>
      flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) q.2.1 (om q.1 Φ) q.2.2 u := by
    intro q
    unfold flatFun
    refine (continuous_star.comp hpsi).mul ?_
    have hf : Continuous fun u : UX D ρ =>
        ((q.1, ((rat x : Mx D W.rank ρ) ⬝ u.1.1, q.2.1, q.2.2)) :
          (GA D V × GA D W) × Mx D W.rank ρ × Mx D V₀.rank σ × WO V₀ W₀) :=
      continuous_const.prodMk (hxu.prodMk continuous_const)
    have h2 := hmix.comp hf
    simp only [Function.comp_def] at h2
    exact h2
  haveI : SecondCountableTopology (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.1
  haveI : ∀ m n : ℕ, SecondCountableTopology (Mx D m n) := fun m n =>
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → AE D))
  haveI : ∀ m n : ℕ, FirstCountableTopology (Mx D m n) := fun m n =>
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  haveI : ∀ S : HSp D, SecondCountableTopology (GA D S) := fun S => (Formalism.IndefR.Eqv.ga_facts D S).2.2.2.1
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  rw [continuous_iff_continuousAt]
  intro q₀
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds q₀.1
  obtain ⟨M, hMi, hM⟩ := hmaj K hK
  have hev : ∀ᶠ q in nhds q₀, q.1 ∈ K := continuous_fst.continuousAt.preimage_mem_nhds hKn
  have key : ContinuousAt (fun q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀ =>
      ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) q.2.1 (om q.1 Φ) q.2.2 u ∂vU.ν) q₀ := by
    refine continuousAt_of_dominated (bound := M) ?_ ?_ hMi ?_
    · exact Filter.Eventually.of_forall fun q => (hcu q).aestronglyMeasurable
    · exact hev.mono fun q hq => Filter.Eventually.of_forall fun u => hM q.1 hq q.2.1 q.2.2 u
    · exact Filter.Eventually.of_forall fun u => (hcq u).continuousAt
  exact key

end GlobalTheory.FlatCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFlatMapWeilRepresentationJointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_flatMap_weilRepresentation_joint : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vU : VolU D ρ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ Φ, IsThetaFunO ψ V W Φ → Continuous fun q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀ => flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) q.2.1 (om q.1 Φ) q.2.2 := by
  first | exact @GlobalTheory.FlatCont.flatAt_om_continuous | exact GlobalTheory.FlatCont.flatAt_om_continuous | (intros; apply GlobalTheory.FlatCont.flatAt_om_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstIsotropicVectorCoordinatesNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstIsotropicVectorCoordinatesNeZero
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory

theorem coord_first_isotropic_ne_zero : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : 1 ≤ D.R.rS), (fun i : Fin (D.sp.Y 0).rank => X.ιE (X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h) i))) ≠ 0 := by
  intro D X h hr hzero
  have hrepr : X.bas.repr (X.eX ⟨0, hr⟩) = 0 := by
    ext j
    have := congrFun hzero (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h).symm j)
    simpa [Formalism.L2.SG.HidaSetting.HidaSetting.eR, Formalism.L2.SG.HidaSetting.HidaSetting.crd,
      Formalism.L2.SG.HidaSetting.crdOf] using this
  have hx : X.eX ⟨0, hr⟩ = 0 := by
    simpa using hrepr
  have hef := X.ef ⟨0, hr⟩ ⟨0, hr⟩
  rw [hx] at hef
  simp at hef

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstIsotropicVectorCoordinatesNeZeroStatement
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstIsotropicVector_coordinates_ne_zero : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : 1 ≤ D.R.rS), (fun i : Fin (D.sp.Y 0).rank => X.ιE (X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h) i))) ≠ 0 := by
  first | exact @GlobalTheory.coord_first_isotropic_ne_zero | exact GlobalTheory.coord_first_isotropic_ne_zero | (intros; apply GlobalTheory.coord_first_isotropic_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzEquivariant
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.FlatEqui

variable {D : D7}

theorem levi_mem_flagN {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    d.levi u ∈ flagN d :=
  ((flag_jacobi_structure D S S₀ ρ d).1 _).2 ⟨u, hu, 0, 0, by rw [d.nB_zero, d.nC_zero, mul_one, mul_one]⟩

theorem psiUni_mul (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {u v : GL (Fin ρ) (AE D)}
    (hu : u ∈ UX D ρ) (hv : v ∈ UX D ρ) : psiUni ψ (u * v) = psiUni ψ u * psiUni ψ v := by
  have h : ∀ a, psiFlag ψ d (d.levi a) = psiUni ψ a := fun a => by
    have := psiFlag_levi_mul ψ d a (one_mem (stabX d))
    rwa [mul_one] at this
  rw [← h, ← h, ← h, map_mul, psiFlag_mul d ψ (levi_mem_flagN d hu) (levi_mem_flagN d hv)]

theorem flatBF_levi (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J)
    (om' : Om B.V₀ J.W) (hom : IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om') (Ψ : WO B.V J.W → ℂ)
    (hΨ : IsThetaFunO ψ B.V J.W Ψ) (γ : UX D ρ) :
    flatBF s (s.om (1, J.d.levi γ.1) Ψ) = star (psiUni ψ γ.1) • flatBF s Ψ := by
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := s.vU.unit.1
  funext w
  have he := (GlobalTheory.T.doubleMixedModel_baseValue_equivariant D ψ ρ B J s om' hom Ψ hΨ).2
  simp only [flatBF, flat, flatAt, flatFun, Pi.smul_apply, smul_eq_mul, he]
  rw [← integral_const_mul, ← integral_mul_left_eq_self _ γ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [inv_mul_cancel_left]
  rw [Subgroup.coe_mul, psiUni_mul ψ J.d γ.2 u.2, star_mul', mul_assoc]

theorem flatBF_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ flagN J.d, ∀ h', flatBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = star (psiFlag ψ J.d n) • s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flatBF s Ψ)) := by
  intro D ψ ρ B J s om' hom Ψ hΨ h₀ n hn h'
  obtain ⟨γ, hγ, b, c, rfl⟩ := ((flag_jacobi_structure D J.W J.W₀ ρ J.d).1 n).1 hn
  have hr : J.d.nB b * J.d.nC c ∈ radX J.d := mul_mem (nB_mem_radX J.d b) (nC_mem_radX J.d c)
  have e : s.om (embA B.d B.o h₀, J.d.levi γ * (J.d.nB b * J.d.nC c) * J.d.emb0 h') Ψ =
      s.om (1, J.d.levi γ) (s.om (embA B.d B.o h₀, J.d.nB b * J.d.nC c * J.d.emb0 h') Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_assoc]
  rw [e, flatBF_levi ψ ρ B J s om' hom _ (s.weil.om_pres _ _ hΨ) ⟨γ, hγ⟩,
    GlobalTheory.T.besselToJacobiFlat_weilRepresentation_cores D ψ ρ B J s om' hom Ψ hΨ h₀ _ hr h', psiFlag_levi_mul ψ J.d γ (radX_le_stabX J.d hr), opA, opA,
    jacT_levi_mul ψ J.d B.V₀ _ (yZero_mul B.V₀ _ hγ)]

end GlobalTheory.FlatEqui

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzEquivariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ flagN J.d, ∀ h', flatBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = star (psiFlag ψ J.d n) • s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flatBF s Ψ)) := by
  first | exact @GlobalTheory.FlatEqui.flatBF_equivariant | exact GlobalTheory.FlatEqui.flatBF_equivariant | (intros; apply GlobalTheory.FlatEqui.flatBF_equivariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinColTOfPinColL
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.AdForm.PinInhab
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def stdSp {D : D7} (V : HSp D) : DefSp V :=
  ⟨fun _ => 1, fun _ => 1, GlobalTheory.PlaceModel.latFrame V, (GlobalTheory.Unf.VolExist.nonempty_vol V).some⟩

theorem gramAt_one {D : D7} {V : HSp D} (h : V.gram = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  rw [gramAt, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem stdSp_is {D : D7} {V : HSp D} (hs : V.SigOK) (h : V.gram = 1) : (stdSp V).Is := by
  refine ⟨hs, ?_, fun τ => VacStd.cartan_of_gram h τ, fun _ => Or.inl rfl, ?_,
    GlobalTheory.PlaceModel.isSelfDualC_latFrame V⟩
  · apply (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D V).2
    intro τ
    rw [gramAt_one h]
    exact Matrix.PosDef.one
  · intro τ
    exact ⟨V.rank, fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩,
      by simp [gramAt_one h, stdSp], by simp [stdSp]⟩

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}

theorem gram_X (hI : I.Ok) (j : ℕ) : ((I.rec7 l Z).sp.X j).gram = 1 := by
  obtain ⟨hs, hX, -⟩ := hI.spaces
  exact VacStd.gram_of_eq _ hs _ (hX j)

theorem lat_X (hI : I.Ok) (j : ℕ) :
    (GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X j) : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) =
      GlobalTheory.AdForm.intVec (I.rec7 l Z) _ := by
  obtain ⟨hs, hX, -⟩ := hI.spaces
  exact VacStd.coe_latFrame_of_eq _ hs _ (hX j)

theorem exists_vac (hI : I.Ok) {ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ} {θ : InfFam (I.rec7 l Z)}
    (hψ : IsStdChar (I.rec7 l Z) ψ (-1)) (hθ : IsInfFam θ) (i : ℕ) :
    ∃ f, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) f := by
  obtain ⟨f, hf⟩ := GlobalTheory.Member.vacuum_oriented_exists (I.rec7 l Z) ψ θ hψ hθ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))
    (fun _ => 1) (fun _ => 1) ((I.rec7 l Z).sp.X_sig _) ((I.rec7 l Z).sp.X_sig _)
    (fun τ => VacStd.cartan_of_gram (gram_X hI _) τ) (fun τ => VacStd.cartan_of_gram (gram_X hI _) τ)
    _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame _) (GlobalTheory.PlaceModel.isSelfDualC_latFrame _)
  rw [lat_X hI i, lat_X hI (i + 1)] at hf
  exact ⟨f, hf⟩

theorem volLev_ne_zero (hI : I.Ok) {θ : InfFam (I.rec7 l Z)} (hθ : IsInfFam θ) {Ch : ℕ → Type}
    {A : TwDat I l Z u a Ch} (j : ℕ) (v : GlobalTheory.Unf.Vol ((I.rec7 l Z).sp.X j)) (β : Ch j)
    (hr : IsReps ((I.rec7 l Z).sp.X j) (A.U j β) (A.h j β)) : volLev v (A.U j β) ≠ 0 := by
  have hu := GlobalTheory.SeeSaw.ontoUni_inB _ θ ((I.rec7 l Z).sp.X j) (fun _ => 1) hθ fun τ => by
    rw [gramAt_one (gram_X hI j)]; simp
  obtain ⟨-, -, -, ν, -, -, h⟩ := GlobalTheory.SeeSaw.integral_eq_classSum _ θ _ _ hθ hu
  letI : Fintype {c : (I.stp u a j).Cl // A.chOf j c = β} := @Subtype.fintype _ _ _ ((I.chain l u a).clsFin j)
  exact (h v _ _ _ hr).1.ne'

end GlobalTheory.AdForm.PinInhab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColCond
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.PhiOneVal

def ColCond {E : Type} [Field E] [NumberField E] {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (t : 𝓞 E)
    (x : (Fin a → E) →ₗ[E] (Fin b → E)) : Prop :=
  ∀ r : Fin a, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ c : Fin b → 𝓞 E,
    (∀ q, algebraMap (𝓞 E) E (c q) = algebraMap (𝓞 E) E s * x (Pi.single r 1) q) ∧
    ∀ q : Fin b, q.1 + 1 = b → t * (c q - if r.1 + 1 = a then s else 0) ∈ P.asIdeal

end GlobalTheory.PhiOneVal
end
end
