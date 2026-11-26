module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RangeBesselAnisotropicEmbeddingEqSecondModelSubg

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas
noncomputable section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.SchDatum

theorem exists_datum : ∀ (D : D7) (A V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (WO A V)) (𝓨 : Set (WO A V)), IsCovolOne (ratL V A) ν 𝓨 → ∀ ω : G D A.rank →* Module.End ℂ (schwartzA θ V.rank A.rank), IsWeilSch ψ χ θ V ν ω → ∃ (ψ₀ : AddChar (AF D.host.F) ℂ) (μ : D.host.E) (lam : D.host.F) (κ : GA D (dblSp A) ≃* G D A.rank) (omh : GA D (dblSp A) × GA D V →* Module.End ℂ (WO (dblSp A) V → ℂ)), IsStdChar D ψ₀ (-1) ∧ IsSkew μ ∧ algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ ∧ ψ = shift ψ₀ lam ∧ IsChart A μ κ ∧ IsWeilDatumO ψ₀ (dblSp A) V 1 χ⁻¹ omh ∧ IsTransport ψ₀ θ A V ν 𝓨 omh κ ω := by
  intro D A V ψ hψ χ hχ hr θ hθ ν 𝓨 hν ω hω
  obtain ⟨ψ₀, h₀, lam, hlam, hψeq⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  have hsh : ψ = shift ψ₀ lam := by
    ext x
    rw [hψeq]
    rfl
  have hlamE : algebraMap D.host.F D.host.E lam ≠ 0 := (map_ne_zero _).2 hlam
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  set μ' : D.host.E := -D.host.xi0 / algebraMap D.host.F D.host.E lam with hμ'
  have hsk : IsSkew μ' := by
    refine ⟨div_ne_zero (neg_ne_zero.2 hxi) hlamE, ?_⟩
    rw [hμ', star_div₀, star_neg, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, Formalism.IndefR.Eqv.star_algebraMapF]
    ring
  have hl : algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ' := by
    rw [hμ']; field_simp
  obtain ⟨κ, hκ⟩ := GlobalTheory.StdUnn.chart_exists D A μ' hsk
  obtain ⟨hχi, hri⟩ := GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χ V.rank hχ hr
  have hr1 : ResEta D 1 (dblSp A).rank := by
    have := GlobalTheory.Eis.SimplePoleModel.resEta_one_two_mul D A.rank
    convert this using 2
    simp [GlobalTheory.Doubling.dblSp]
    omega
  obtain ⟨omh, homh⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ₀ (dblSp A) V 1 χ⁻¹ h₀
    ⟨continuous_const, fun _ => rfl⟩ hχi hr1 hri
  obtain ⟨omS, hS⟩ := GlobalTheory.StdUnn.exists_transport_std D ψ₀ A V χ⁻¹ omh homh ν 𝓨 hν θ hθ κ
  have hWS : IsWeilSch (shift ψ₀ lam) χ θ V ν omS := by
    refine ⟨?_, ?_, ?_⟩
    · intro g a hg Φ x
      have := GlobalTheory.StdUnn.transport_levi D ψ₀ A V χ⁻¹ omh homh ν 𝓨 hν θ hθ μ' hsk κ hκ omS hS lam hl g a hg Φ x
      rw [inv_inv] at this
      exact this
    · intro g b hg Φ x
      exact GlobalTheory.StdUnn.Unip.transport_unip D ψ₀ A V χ⁻¹ omh homh ν 𝓨 hν θ hθ μ' hsk κ hκ omS hS lam hl g b hg Φ x
    · intro g hg Φ x
      exact GlobalTheory.StdUnn.WeylStd.main D ψ₀ A V χ⁻¹ omh homh ν 𝓨 hν θ hθ μ' hsk κ hκ omS hS lam hl g hg Φ x
  subst hsh
  obtain rfl := GlobalTheory.SiegelWeilLitCompare.isWeilSch_unique hω hWS
  exact ⟨ψ₀, μ', lam, κ, omh, h₀, hsk, hl, rfl, hκ, homh, hS⟩

end GlobalTheory.StdUnn.SchDatum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulasStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas : ∀ (D : D7) (A V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (WO A V)) (𝓨 : Set (WO A V)), IsCovolOne (ratL V A) ν 𝓨 → ∀ ω : G D A.rank →* Module.End ℂ (schwartzA θ V.rank A.rank), IsWeilSch ψ χ θ V ν ω → ∃ (ψ₀ : AddChar (AF D.host.F) ℂ) (μ : D.host.E) (lam : D.host.F) (κ : GA D (dblSp A) ≃* G D A.rank) (omh : GA D (dblSp A) × GA D V →* Module.End ℂ (WO (dblSp A) V → ℂ)), IsStdChar D ψ₀ (-1) ∧ IsSkew μ ∧ algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ ∧ ψ = shift ψ₀ lam ∧ IsChart A μ κ ∧ IsWeilDatumO ψ₀ (dblSp A) V 1 χ⁻¹ omh ∧ IsTransport ψ₀ θ A V ν 𝓨 omh κ ω := by
  first | exact @GlobalTheory.StdUnn.SchDatum.exists_datum | exact GlobalTheory.StdUnn.SchDatum.exists_datum | (intros; apply GlobalTheory.StdUnn.SchDatum.exists_datum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealLocallyPrincipalAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealLocallyPrincipalAdelic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.FinPl.idV_principal_at : ∀ (D : D7) (v : Pl D) (𝔞 : FI D), 𝔞 ≠ 0 → ∃ g ∈ idV 𝔞 v, ∃ g' ∈ idAt D (· = v), (∀ s ∈ idAt D (· = v), g' * g * s = s) ∧ ∀ s, s ∈ idV 𝔞 v ↔ s ∈ idAt D (· = v) ∧ g' * s ∈ intAt D (· = v) := by
  intro D v 𝔞 h𝔞
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.T.fractionalIdealCompletion_locally_principal D v 𝔞 h𝔞
  obtain ⟨ε, hεε, -, hεint, hεid, -⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).1
  have hεI : ε ∈ idAt D (· = v) := hεint.1
  have hxx : incA D x⁻¹ * incA D x = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  refine ⟨incA D x * ε, ?_, incA D x⁻¹ * ε, Ideal.mul_mem_left _ _ hεI, ?_, ?_⟩
  · rw [hx]
    refine ⟨?_, Ideal.mul_mem_left _ _ hεI⟩
    rw [← mul_assoc, hxx, one_mul]; exact hεint
  · intro s hs
    have : incA D x⁻¹ * ε * (incA D x * ε) = ε * ε := by
      calc incA D x⁻¹ * ε * (incA D x * ε) = (incA D x⁻¹ * incA D x) * (ε * ε) := by ring
        _ = ε * ε := by rw [hxx, one_mul]
    rw [this, hεε]; exact (hεid s).1 hs
  · intro s
    rw [hx]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      rw [mul_assoc, (hεid s).1 h2]; exact h1
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      rw [mul_assoc, (hεid s).1 h2] at h1; exact h1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealLocallyPrincipalAdelicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdeal_locallyPrincipal_adelic : ∀ (D : D7) (v : Pl D) (𝔞 : FI D), 𝔞 ≠ 0 → ∃ g ∈ idV 𝔞 v, ∃ g' ∈ idAt D (· = v), (∀ s ∈ idAt D (· = v), g' * g * s = s) ∧ ∀ s, s ∈ idV 𝔞 v ↔ s ∈ idAt D (· = v) ∧ g' * s ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.idV_principal_at | exact GlobalTheory.FinPl.idV_principal_at | (intros; apply GlobalTheory.FinPl.idV_principal_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemScaledLatticeCompletionIffPolarisationInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemScaledLatticeCompletionIffPolarisationInverse
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LatAt

variable {D : D7}

theorem pairA_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  refine Prod.ext ?_ ?_
  · show (0 : Ainf D.host.F) * 0 = 0
    rw [zero_mul]
  · rfl

theorem pair_tmul_mul (α β : Af D.host.F) (a b : D.host.E) :
    ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] b) =
      pairA D.host.F 0 (α * β) ⊗ₜ[D.host.F] (a * b) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_mul]

def Good (v : Pl D) (α : Af D.host.F) : Prop :=
  α ∈ intAf D.host.F ∧ ∀ w, w ≠ v → evalV D.host.F w α = 0

theorem Good.mul {v : Pl D} {α β : Af D.host.F} (hα : Good v α) (hβ : Good v β) : Good v (α * β) :=
  ⟨fun w => by rw [map_mul]; exact mul_mem (hα.1 w) (hβ.1 w), fun w hw => by rw [map_mul, hα.2 w hw, zero_mul]⟩

theorem good_indP (v : Pl D) : Good v (GlobalTheory.SelfDualAt.indP (D := D) (· = v)) := by
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · rw [GlobalTheory.SelfDualAt.evalV_indP]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [GlobalTheory.SelfDualAt.evalV_indP, if_neg hw]

theorem indicatorAdele_mul_self (v : Pl D) :
    GlobalTheory.SelfDualAt.indP (D := D) (· = v) * GlobalTheory.SelfDualAt.indP (D := D) (· = v) = GlobalTheory.SelfDualAt.indP (D := D) (· = v) := by
  refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
  have h1 : evalV D.host.F w (GlobalTheory.SelfDualAt.indP (D := D) (· = v) * GlobalTheory.SelfDualAt.indP (D := D) (· = v)) =
      evalV D.host.F w (GlobalTheory.SelfDualAt.indP (D := D) (· = v)) := by
    rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP]
    split_ifs <;> simp
  exact h1

theorem gen_mem_idAt (v : Pl D) (α : Af D.host.F) (hα : ∀ w, w ≠ v → evalV D.host.F w α = 0) (x : D.host.E) :
    (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x ∈ idAt D (· = v) := by
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0
    exact TensorProduct.zero_tmul _ _
  · change (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0
    rw [hα _ w.2, TensorProduct.zero_tmul]

theorem AA_ne_zero : D.host.AA ≠ 0 :=
  (GlobalTheory.SeeSaw.LiftModel.AA_ne (D := D) Formalism.IndefR.Fin.factPrincipalDatum).1

theorem int_of_mem {c d : D.host.E} (hc : c ∈ D.host.AA) (hd : d ∈ D.host.AA⁻¹) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = d * c := by
  have h : d * c ∈ D.host.AA⁻¹ * D.host.AA := FractionalIdeal.mul_mem_mul hd hc
  rw [inv_mul_cancel₀ AA_ne_zero] at h
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h
  exact ⟨o, ho⟩

theorem smul_latV_mem_latA (S : HSp D) (L : Lat S) (v : Pl D) {ε : Af D.host.F} (hε : Good v ε) {c : D.host.E}
    (hc : c ∈ D.host.AA) {z : Fin S.rank → AE D} (hz : z ∈ latV S L (· = v)) :
    ((pairA D.host.F 0 ε) ⊗ₜ[D.host.F] c : AE D) • z ∈ latA S L (· = v) := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hz
  unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latMul
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβ1, hβ2, a, ha, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at ha
    subst ha
    apply AddSubgroup.subset_closure
    have g := hε.mul ⟨hβ1, hβ2⟩
    refine ⟨ε * β, g.1, g.2, c, hc, x, hx, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, pair_tmul_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h => rw [smul_neg]; exact neg_mem h

end GlobalTheory.SeeSaw.LatAt

namespace GlobalTheory.SeeSaw.LatAt

variable {D : D7}

theorem mem_latA_fwd (S : HSp D) (L : Lat S) (v : Pl D) (y : Fin S.rank → AE D) (hy : y ∈ latA S L (· = v)) :
    (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) := by
  unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latMul at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα1, hα2, c, hc, x, hx, rfl⟩ := hy
    refine ⟨fun i => gen_mem_idAt v α hα2 _, fun s hs => ?_⟩
    unfold idV at hs
    induction hs using AddSubgroup.closure_induction with
    | mem s hs =>
      obtain ⟨β, hβ1, hβ2, d, hd, rfl⟩ := hs
      obtain ⟨o, ho⟩ := int_of_mem hc hd
      unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
      apply AddSubgroup.subset_closure
      have g := Good.mul (v := v) ⟨hβ1, hβ2⟩ ⟨hα1, hα2⟩
      refine ⟨β * α, g.1, g.2, 1, rfl, o • x, L.smul_mem o hx, ?_⟩
      funext i
      rw [Pi.smul_apply, smul_eq_mul, pair_tmul_mul, one_mul, Pi.smul_apply, Algebra.smul_def, ← mul_assoc]
      congr 2
      exact ho.symm
    | zero => rw [zero_smul]; exact zero_mem _
    | add s t _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
    | neg s _ h => rw [neg_smul]; exact neg_mem h
  | zero => exact ⟨fun i => zero_mem _, fun s _ => by rw [smul_zero]; exact zero_mem _⟩
  | add y z _ _ h1 h2 =>
    exact ⟨fun i => add_mem (h1.1 i) (h2.1 i), fun s hs => by rw [smul_add]; exact add_mem (h1.2 s hs) (h2.2 s hs)⟩
  | neg y _ h => exact ⟨fun i => neg_mem (h.1 i), fun s hs => by rw [smul_neg]; exact neg_mem (h.2 s hs)⟩

theorem mem_latA_bwd (S : HSp D) (L : Lat S) (v : Pl D) (y : Fin S.rank → AE D) (hsupp : ∀ i, y i ∈ idAt D (· = v))
    (h : ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v)) : y ∈ latA S L (· = v) := by
  have hε : Good v (GlobalTheory.SelfDualAt.indP (D := D) (· = v)) := good_indP v
  have key : ∀ t ∈ D.host.AA * D.host.AA⁻¹,
      ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] t : AE D) • y ∈ latA S L (· = v) := by
    intro t ht
    refine FractionalIdeal.mul_induction_on ht ?_ ?_
    · intro c hc d hd
      have e : ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] (c * d) : AE D) =
          ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] c) *
            ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] d) := by
        rw [pair_tmul_mul, indicatorAdele_mul_self]
      rw [e, mul_smul]
      refine smul_latV_mem_latA S L v hε hc (h _ ?_)
      unfold idV
      exact AddSubgroup.subset_closure ⟨_, hε.1, hε.2, d, hd, rfl⟩
    · intro a b ha hb
      rw [TensorProduct.tmul_add, add_smul]
      exact add_mem ha hb
  have h1 := key 1 (by rw [mul_inv_cancel₀ AA_ne_zero]; exact FractionalIdeal.one_mem_one _)
  have e1 : ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • y = y := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul]
    exact GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul (· = v) (y i) (hsupp i)
  rwa [e1] at h1

end GlobalTheory.SeeSaw.LatAt

theorem GlobalTheory.SeeSaw.mem_latA_iff_mul_inv : ∀ (D : D7) (v : Pl D) (S : HSp D) (L : Lat S) (y : Fin S.rank → AE D), y ∈ latA S L (· = v) ↔ (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) :=
  fun _ v S L y => ⟨GlobalTheory.SeeSaw.LatAt.mem_latA_fwd S L v y, fun h => GlobalTheory.SeeSaw.LatAt.mem_latA_bwd S L v y h.1 h.2⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemScaledLatticeCompletionIffPolarisationInverseStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_scaledLatticeCompletion_iff_polarisationInverse : ∀ (D : D7) (v : Pl D) (S : HSp D) (L : Lat S) (y : Fin S.rank → AE D), y ∈ latA S L (· = v) ↔ (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) := by
  first | exact @GlobalTheory.SeeSaw.mem_latA_iff_mul_inv | exact GlobalTheory.SeeSaw.mem_latA_iff_mul_inv | (intros; apply GlobalTheory.SeeSaw.mem_latA_iff_mul_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem idV_props : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ v : Pl D, (∀ a, a ∈ idV (1 : FI D) v ↔ a ∈ intAt D (· = v)) ∧ (∀ 𝔞 𝔟 : FI D, 𝔞 ≠ 0 → 𝔟 ≠ 0 → ∀ s ∈ idAt D (· = v), (∀ a ∈ idV 𝔞 v, s * a ∈ idV 𝔟 v) ↔ s ∈ idV (𝔟 * 𝔞⁻¹) v) ∧ (∀ (𝔞 : FI D) (x : D.host.E), x ≠ 0 → ∀ s, s ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔞) v ↔ incA D x⁻¹ * s ∈ idV 𝔞 v ∧ s ∈ idAt D (· = v)) ∧ (∀ n : ℤ, ∀ s, s ∈ idV (D.host.AA ^ n) v ↔ cA D s ∈ idV (D.host.AAbar ^ n) v) ∧ (∀ s ∈ idAt D (· = v), s ∈ idV (dI D) v ↔ ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) ∧ (∀ 𝔞 : FI D, 𝔞 ≠ 0 → ∃ g ∈ idV 𝔞 v, ∃ g' ∈ idAt D (· = v), (∀ s ∈ idAt D (· = v), g' * g * s = s) ∧ ∀ s, s ∈ idV 𝔞 v ↔ s ∈ idAt D (· = v) ∧ g' * s ∈ intAt D (· = v)) ∧ ∀ (S : HSp D) (L : Lat S) (y : Fin S.rank → AE D), y ∈ latA S L (· = v) ↔ (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) := fun D ψ hψ v =>
  ⟨GlobalTheory.T.unitIdealCompletionAtPlace_eq_integralAdelesAtPlace D v, GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v, GlobalTheory.T.mem_spanSingleton_mul_idealCompletion_iff D v, fun n s => GlobalTheory.T.periodIdealZpow_completion_adeleConj_iff D v n s,
    GlobalTheory.T.inverseDifferentCompletion_iff_characterDual D ψ hψ v, GlobalTheory.T.fractionalIdeal_locallyPrincipal_adelic D v, GlobalTheory.T.mem_scaledLatticeCompletion_iff_polarisationInverse D v⟩

end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdealCompletion_properties_at_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ v : Pl D, (∀ a, a ∈ idV (1 : FI D) v ↔ a ∈ intAt D (· = v)) ∧ (∀ 𝔞 𝔟 : FI D, 𝔞 ≠ 0 → 𝔟 ≠ 0 → ∀ s ∈ idAt D (· = v), (∀ a ∈ idV 𝔞 v, s * a ∈ idV 𝔟 v) ↔ s ∈ idV (𝔟 * 𝔞⁻¹) v) ∧ (∀ (𝔞 : FI D) (x : D.host.E), x ≠ 0 → ∀ s, s ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔞) v ↔ incA D x⁻¹ * s ∈ idV 𝔞 v ∧ s ∈ idAt D (· = v)) ∧ (∀ n : ℤ, ∀ s, s ∈ idV (D.host.AA ^ n) v ↔ cA D s ∈ idV (D.host.AAbar ^ n) v) ∧ (∀ s ∈ idAt D (· = v), s ∈ idV (dI D) v ↔ ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) ∧ (∀ 𝔞 : FI D, 𝔞 ≠ 0 → ∃ g ∈ idV 𝔞 v, ∃ g' ∈ idAt D (· = v), (∀ s ∈ idAt D (· = v), g' * g * s = s) ∧ ∀ s, s ∈ idV 𝔞 v ↔ s ∈ idAt D (· = v) ∧ g' * s ∈ intAt D (· = v)) ∧ ∀ (S : HSp D) (L : Lat S) (y : Fin S.rank → AE D), y ∈ latA S L (· = v) ↔ (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) := by
  first | exact @GlobalTheory.SeeSaw.idV_props | exact GlobalTheory.SeeSaw.idV_props | (intros; apply GlobalTheory.SeeSaw.idV_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces : ∀ D : D7, GlobalTheory.FinPl.FlatLaws D := by
  first | exact @GlobalTheory.FinPl.flatLaws_all | exact GlobalTheory.FinPl.flatLaws_all | (intros; apply GlobalTheory.FinPl.flatLaws_all <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.SuppLevO

variable {D : D7}

theorem proj_eq_one_of_finHom (V : HSp D) (h : GA D V) (hh : h ∈ GinfC V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v h = 1 := by
  rw [← GlobalTheory.AdelicU.projFinLoc_projFin]
  have : GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram h = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact congrArg Units.val hh
  rw [this, map_one]

theorem proj_finPartG (V : HSp D) (g : GA D V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (GlobalTheory.LevelNbhd.finPartG V g) = GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g := by
  have h := proj_eq_one_of_finHom V _ (GlobalTheory.LevelNbhd.inv_finPartG_mul_mem_GinfC V g) v
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  exact h

theorem finE_finPartG (V : HSp D) (g : GA D V) : Lev.finE V (GlobalTheory.LevelNbhd.finPartG V g) = Lev.finE V g := by
  show (Formalism.UG.bc _) (finHom V _) = (Formalism.UG.bc _) (finHom V g)
  rw [GlobalTheory.LevelNbhd.finHom_finPartG]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem half_supp (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (e : AE D) (x : WO S T)
    (h : IsHalf e x) : ∀ i j, toEAf D e * frMapO S T βS βT x i j = frMapO S T βS βT x i j := by
  intro i j
  have hX : toEAf D e • ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D)) =
      (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) := by
    ext a b
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, ← map_mul]
    rw [h a b]
  have : toEAf D e • frMapO S T βS βT x = frMapO S T βS βT x := by
    unfold frMapO
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hX]
  exact congrFun (congrFun this i) j

theorem datum_spec (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D) (x : WO S T)
    (hx : (if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) *
      omegaQ ∅ L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) ≠ 0) :
    IsHalf e x ∧ IsIntM (frMapO S T βS βT x) ∧
    (∀ PP ∈ L.Pg, IsUnit (topL S.rank (redM PP (frMapO S T βS βT x))).det) ∧
    ∃ a : ∀ PP : ↥L.Pg, GL (Fin S.rank) (kP PP.1),
      (∀ PP : ↥L.Pg, ((a PP : GL (Fin S.rank) (kP PP.1)) : Matrix (Fin S.rank) (Fin S.rank) (kP PP.1)) =
        topL S.rank (redM PP.1 (frMapO S T βS βT x))) ∧
      (∀ PP : ↥L.Pg, a PP ∈ blockTri (blkOf L.r L.t)) ∧ (fun PP => upperLeftBlock L.hr (a PP)) ∈ L.P.H := by
  split_ifs at hx with hc
  · have hg := left_ne_zero_of_mul hx
    unfold omegaG at hg
    split_ifs at hg with hG
    · obtain ⟨-, a, ha1, ha2, ha3⟩ := hG
      refine ⟨hc.1, hc.2, fun PP hP => ?_, a, ha1, ha2, ha3⟩
      rw [← ha1 ⟨PP, hP⟩]
      exact (Matrix.isUnit_iff_isUnit_det _).1 (a ⟨PP, hP⟩).isUnit
    · exact absurd rfl hg
  · exact absurd rfl hx


set_option maxHeartbeats 1000000 in
theorem finE_mem_lev : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D), IsSelfDualC S ΛS → Formalism.L2.DIV.IsFrame βS ΛS → S.rank ≤ T.rank → L.Q = ∅ → IsIdemSum e (L.Pg ∪ ∅) → ∀ g : GA D S, (∀ v, (∀ PP ∈ L.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig S.gram ΛS v) → ∀ x, (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ ∅ L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) x ≠ 0 → (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ ∅ L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) (actO S T g 1 x) ≠ 0 → Lev.finE S g ∈ Formalism.L2.DIV.lev D.sp.cm S.gram βS L := by
  intro D S T ΛS βS βT L χ ξ e hsd hfr hrk hQ hZe g hg x hx hx'
  beta_reduce at hx hx'
  rw [Finset.union_empty] at hZe
  obtain ⟨hh, hI, hU, a, ha1, ha2, ha3⟩ := datum_spec S T βS βT L χ ξ e x hx
  obtain ⟨-, hI', hU', b, hb1, hb2, hb3⟩ := datum_spec S T βS βT L χ ξ e _ hx'
  have hu' := GlobalTheory.T.frameMatrix_weilPairAction_left_inv D S T βS βT g x
  rw [hu'] at hI' hU' hb1
  have hsupp := half_supp S T βS βT e x hh
  obtain ⟨h1, h2, hred⟩ := GlobalTheory.T.integral_idempotent_mul_of_unit_topBlock_reductions T.rank S.rank hrk L.Pg e hZe _ (βS⁻¹ * Lev.finE S g * βS) hI hI' hsupp hU hU'
  have hUA := GlobalTheory.LevSplit.finE_mem_UA S g
  obtain ⟨h3, h4⟩ := GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral S ΛS βS hsd hfr _ hUA _ rfl e h1 h2
  obtain ⟨hεε, hεc⟩ := GlobalTheory.T.idempotentSum_add_conj_idempotent_conj_fixed L.Pg e hZe
  obtain ⟨k, hk, hmt⟩ := GlobalTheory.T.exists_idempotent_component_of_group_element S (GlobalTheory.LevelNbhd.finPartG S g) (e + cA D e)
    (GlobalTheory.LevelNbhd.finPartG_mem_GfC S g) hεε hεc
  have hfk := GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame S βS _ k (e + cA D e) hmt
  rw [finE_finPartG] at hfk
  obtain ⟨hSt, hR⟩ := GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction S.rank βS _ _ L.Pg e hZe h1 h2 h3 h4 hfk

  have hcomp : ∀ PP ∈ L.Pg, GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) k =
      GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g := fun PP hP => by
    rw [← proj_finPartG S g]
    exact GlobalTheory.T.localProjection_eq_of_idempotent_patch S _ _ k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one L.Pg e hZe PP hP) hmt

  have hkloc := (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D S βS ΛS hfr k).1 hSt
  have hgSt : Lev.finE S g ∈ St βS := by
    refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D S βS ΛS hfr g).2 fun v => ?_
    by_cases hv : ∃ PP ∈ L.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v
    · obtain ⟨PP, hP, rfl⟩ := hv
      rw [← hcomp PP hP]
      exact hkloc _
    · push_neg at hv
      exact hg v hv

  have hredeq : ∀ PP ∈ L.Pg, redFn βS PP (Lev.finE S g) = redFn βS PP (Lev.finE S k) := fun PP hP => by
    have hm : Lev.finE S (g * k⁻¹) ∈ St βS := by
      rw [map_mul, map_inv]; exact Subgroup.mul_mem _ hgSt (Subgroup.inv_mem _ hSt)
    have h1' : GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (g * k⁻¹) = 1 := by
      rw [map_mul, map_inv, hcomp PP hP, mul_inv_cancel]
    have hr := GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D S βS (g * k⁻¹) PP hm h1'
    have hgk : Lev.finE S g = Lev.finE S (g * k⁻¹) * Lev.finE S k := by
      rw [map_mul, map_inv, inv_mul_cancel_right]
    rw [hgk, redFn_mul hm hSt, hr, one_mul]
  refine GlobalTheory.T.mem_level_of_type_place_reductions S βS L _ hQ hUA hgSt a b ha2 hb2 ha3 hb3 fun PP => ?_
  apply Units.ext
  rw [Units.val_mul, hredeq PP.1 PP.2, hR PP.1 PP.2, ha1, hb1]
  exact hred PP.1 PP.2

end GlobalTheory.SuppLevO
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePart_mem_level_of_thetaDatum_ne_zero : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D), IsSelfDualC S ΛS → Formalism.L2.DIV.IsFrame βS ΛS → S.rank ≤ T.rank → L.Q = ∅ → IsIdemSum e (L.Pg ∪ ∅) → ∀ g : GA D S, (∀ v, (∀ PP ∈ L.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig S.gram ΛS v) → ∀ x, (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ ∅ L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) x ≠ 0 → (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ ∅ L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) (actO S T g 1 x) ≠ 0 → Lev.finE S g ∈ Formalism.L2.DIV.lev D.sp.cm S.gram βS L := by
  first | exact @GlobalTheory.SuppLevO.finE_mem_lev | exact GlobalTheory.SuppLevO.finE_mem_lev | (intros; apply GlobalTheory.SuppLevO.finE_mem_lev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeKernel
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace.TraceFwd

open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos)
open GlobalTheory.SymBridge GlobalTheory.RootEx

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_colGroup {κ τ n : ℕ} (e : XIx (Fin κ) (Fin τ) 0 ≃ Fin n) (he : IsOrd xPos e) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hint : ∀ a b, valuation k (g.val a b) ≤ 1)
    (h : ∀ a b, e b ≤ e a → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1) : g ∈ colGroup k κ (Fin τ) := by
  have hp : ∀ c, colPos κ (Fin τ) c = (e c).val := fun c => by
    rw [he c]
    rcases c with (c | c) | c
    exacts [rfl, c.elim0, c.1.elim0]
  let M : Matrix (XIx (Fin κ) (Fin τ) 0) (XIx (Fin κ) (Fin τ) 0) 𝒪[k] := Matrix.of fun a b => ⟨g.val a b, hint a b⟩
  have hM : ∀ a b, e b ≤ e a → (residue 𝒪[k]).mapMatrix M a b = (1 : Matrix _ _ 𝓀[k]) a b := fun a b hab => by
    have h1 : (1 : Matrix _ _ 𝓀[k]) a b = residue 𝒪[k] ((1 : Matrix _ _ 𝒪[k]) a b) := by
      simp only [Matrix.one_apply, apply_ite (residue 𝒪[k]), map_one, map_zero]
    rw [h1, RingHom.mapMatrix_apply, Matrix.map_apply, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    refine Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 ?_
    convert h a b hab using 2
    simp only [M, Matrix.one_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hdet : ((residue 𝒪[k]).mapMatrix M).det = 1 := by
    rw [← Matrix.det_submatrix_equiv_self e.symm, Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      rw [Matrix.submatrix_apply, hM _ _ le_rfl, Matrix.one_apply_eq]
    · intro i j hij
      have hij' : j < i := hij
      rw [Matrix.submatrix_apply, hM _ _ (by simpa using hij'.le), Matrix.one_apply_ne (e.symm.injective.ne hij'.ne')]
  have hu : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, ← residue_ne_zero_iff_isUnit, RingHom.map_det, hdet]
    exact one_ne_zero
  refine ⟨_, ⟨hu.unit, Units.ext ?_, rfl⟩, fun a b hab => ?_⟩
  · ext a b
    rfl
  · rw [hp, hp] at hab
    exact hM a b hab

theorem embX_mem {s κ τ : ℕ} (S : SymData k s κ) (g : GL (XIx (Fin κ) (Fin τ) 0) k) (hg : g ∈ colGroup k κ (Fin τ)) :
    embX (s + 1) g ∈ ((S.T (Fin τ)).lev 0 (s + 1) (Nat.zero_add _)).J := by
  obtain ⟨-, h2, -⟩ := GlobalTheory.FirstVertexFrame.firstVertex_typeChain k S.ψ S.ϖ s (Fin τ) κ S.P
    (GlobalTheory.SymShape.sym_shape _ _ _ _ _ _ _ S.sym) S.μ S.tame (s + 1) (Nat.zero_add _)
  exact (h2 g hg).1


set_option maxHeartbeats 1000000 in
theorem colGroup_of_red {D : D7} (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (V : HSp D) {n κ τ : ℕ} (hr : V.rank = n) (hn : n = κ) (F : Frame k V.rank (XIx (Fin κ) (Fin τ) 0)) (hF : IsStdFr xPos F)
    {x : GA D V} {y : GL (Fin n) (GlobalTheory.AdForm.EF D)} (hy : GlobalTheory.AdForm.finM V hr x = y.1)
    {A : GL (Fin n) (𝓞 D.host.E ⧸ PP.asIdeal)} (hA : LevRead.IsRed (F := D.host.F) PP y A.1)
    (hU : A ∈ Formalism.L2.Col.uniUT n _ κ []) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hg : (mt V x).map q.pr = F.β * g.val * F.γ) : g ∈ colGroup k κ (Fin τ) := by
  subst hr
  obtain ⟨e, he, hβ⟩ := hF
  choose R hR hR' using hA
  have hM : ∀ i j, valuation k ((mt V x).map q.pr i j - q.pr (incA D (R i j))) < 1 := fun i j => by
    have h2 : y.1 i j = toEAf D (mt V x i j) := by
      rw [← hy]
      rfl
    have h3 := LevChi.val_pr_lt q hq (z := mt V x i j - incA D (R i j)) (by
      rw [RingHom.map_sub, ← h2, RingHom.map_sub]
      exact (congrArg (fun t => Valued.v (adAt D.host.F PP (y.1 i j) - t)) (adAt_inclE D.host.F PP _)).trans_lt (hR' i j))
    rwa [RingHom.map_sub] at h3
  have hgM : ∀ a b, g.val a b = (mt V x).map q.pr (e a) (e b) := fun a b => by
    have h1 : (mt V x).map q.pr * F.β = F.β * g.val := by rw [hg, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
    have h2 := congrFun (congrFun h1 (e a)) b
    rw [hβ] at h2
    simpa [Matrix.mul_apply, Matrix.one_apply] using h2.symm
  refine mem_colGroup e he g (fun a b => ?_) fun a b hab => ?_
  · have := (valuation k).map_add_le (hM (e a) (e b)).le (LevelTest.val_le_one q (R (e a) (e b)))
    rwa [sub_add_cancel, ← hgM] at this
  · obtain ⟨-, h1, h2⟩ := Formalism.L2.Col.mem_uniUT.1 hU
    have ha : (e a).val < κ := hn ▸ (e a).2
    rcases hab.eq_or_lt with h | h
    · obtain rfl : b = a := e.injective h
      have h3 : R (e b) (e b) - 1 ∈ PP.asIdeal := by
        rw [← Ideal.Quotient.eq, hR, h2 _ ha, map_one]
      have := (valuation k).map_add_lt (hM (e b) (e b)) ((LevelTest.val_lt_one_iff q hq _).2 h3)
      rw [← hgM] at this
      simpa using this
    · have h3 : R (e a) (e b) ∈ PP.asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, hR, h1 _ _ ha h]
      have := (valuation k).map_add_lt (hM (e a) (e b)) ((LevelTest.val_lt_one_iff q hq _).2 h3)
      rw [sub_add_cancel, ← hgM] at this
      rwa [Matrix.one_apply_ne (fun h' : a = b => h.ne' (congrArg e h')), sub_zero]

end Loc

theorem exists_red {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : TC B X) (hI : I.Ok) {u : B.Word} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {J : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) B.host.E} (hJ : J = 1)
    (S : Formalism.L2.Forms.StepLevel B.host.F B.host.E B.sp.cm.sig J T f bad) {y : (I.stp u I.mu0 0).Cl → TC.GA B (B.R.N 0)}
    {st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E} {k : Unit → TC.GA B (B.R.N 0)}
    (hR : I.Reads u I.mu0 0 (fun _ => ()) (fun _ => S.Lb) (fun _ => S.U) (fun _ => S.chi) y st k) (x : S.U)
    (w : HeightOneSpectrum (𝓞 B.host.E)) (hw : w ∈ (B.primes X).vGs) :
    ∃ A : GL (Fin (B.R.N 0)) (𝓞 B.host.E ⧸ w.asIdeal), A ∈ Formalism.L2.Col.uniUT (B.R.N 0) _ B.R.k [] ∧ LevRead.IsRed w x.1 A.1 := by
  subst hJ
  obtain ⟨h, h1, h2, -⟩ := TC.GLev0.chi_prod I S hR hI x
  exact ⟨_, inv_mem (h1 ⟨w, hw⟩), h2 ⟨w, hw⟩⟩


end GlobalTheory.FamTrace.TraceFwd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConsecutiveStep
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConsecutiveStep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepMove

section Lattices

open GlobalTheory.FinPl hiding Pl

variable {D : D7}

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

theorem mt_mul₀ (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := rfl

theorem mt_one₀ (V : HSp D) : mt V 1 = 1 := rfl

theorem mt_mul_inv (V : HSp D) (g : GA D V) (y : Fin V.rank → AE D) : mt V g *ᵥ (mt V g⁻¹ *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← mt_mul₀, mul_inv_cancel, mt_one₀, Matrix.one_mulVec]

theorem mulVec_mem_idAt {n : ℕ} (A : Matrix (Fin n) (Fin n) (AE D)) {P : GlobalTheory.FinPl.Pl D → Prop} {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ idAt D P) (i : Fin n) : (A *ᵥ y) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem moves_inv {S : HSp D} {g : GA D S} {L M : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (h : Moves S g L M P) :
    Moves S g⁻¹ M L P := by
  intro y hy
  have e := h (mt S g⁻¹ *ᵥ y) (mulVec_mem_idAt _ hy)
  rw [mt_mul_inv] at e
  exact e.symm

theorem mulVec_mem_latA {S : HSp D} {g : GA D S} {L M : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (h : Moves S g L M P)
    {z : Fin S.rank → AE D} (hz : z ∈ latA S L P) : mt S g *ᵥ z ∈ latA S M P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hy
    set y' : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hy'
    have hy'm : y' ∈ latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have hsplit : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y' := by
      funext i
      simp only [hy', Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    exact smul_mem_latA ha ((h y' (GlobalTheory.FinPl.FrameLat.latV_supp hy'm)).1 hy'm)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem actO_eq (S T : HSp D) (g : GA D S) (h : GA D T) (u : WO S T) :
    actO S T g h u = HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹) := rfl

theorem actO_mem_latO {S T : HSp D} {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {P : GlobalTheory.FinPl.Pl D → Prop} {g : GA D S} {h : GA D T}
    (hg : Moves S g Λ M P) (hh : Moves T h Λ' M' P) {u : WO S T}
    (hu : u ∈ latO S T (Λ : Set _) (Λ' : Set _) P) : actO S T g h u ∈ latO S T (M : Set _) (M' : Set _) P := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T Λ Λ' hΛ hΛ' P] at hu
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T M M' hM hM' P]
  obtain ⟨hmx, hmap⟩ := hu
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [actO_eq, Matrix.mul_apply]
    refine sum_mem fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hmx k l)
  · change (HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹)) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : mt S g⁻¹ *ᵥ y ∈ latV S Λ P :=
      (moves_inv hg y (GlobalTheory.FinPl.FrameLat.latV_supp hy)).1 hy
    exact mulVec_mem_latA hh (hmap _ h1)

theorem actO_actO_inv {S T : HSp D} (g : GA D S) (h : GA D T) (u : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := by
  rw [actO_eq, actO_eq, inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul₀, mul_inv_cancel, mt_one₀, Matrix.one_mul,
    Matrix.mul_assoc, ← mt_mul₀, mul_inv_cancel, mt_one₀, Matrix.mul_one]

end Lattices

section Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}

theorem isHalf_actO (g : GA D S) (h : GA D T) {e : AE D} {u : WO S T} (hu : IsHalf e u) : IsHalf e (actO S T g h u) := by
  intro i j
  rw [actO_eq]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hu k l]
  ring

theorem vac_move (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : GlobalTheory.FinPl.Lat S} {Λ' M' : GlobalTheory.FinPl.Lat T}
    (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M) (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M')
    {P : GlobalTheory.FinPl.Pl D → Prop} {g : GA D S} {h : GA D T} (hg : GlobalTheory.FinPl.Moves S g Λ M P) (hh : GlobalTheory.FinPl.Moves T h Λ' M' P)
    {f : WO S T → ℂ} (hf : GlobalTheory.FinPl.Vac ψ S T Λ Λ' P f) : GlobalTheory.FinPl.Vac ψ S T M M' P (om (g, h) f) := by
  have back : ∀ u : WO S T, actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := actO_actO_inv g h
  have mem : ∀ u ∈ latO S T (M : Set _) (M' : Set _) P, actO S T g⁻¹ h⁻¹ u ∈ latO S T (Λ : Set _) (Λ' : Set _) P :=
    fun u hu => actO_mem_latO hM hΛ hM' hΛ' (moves_inv hg) (moves_inv hh) hu
  refine ⟨hW.om_pres _ _ hf.1, fun u hu => ?_, fun e he u hu hh' => ?_⟩
  · have h1 := hf.2.1 _ (mem u hu)
    have h2 : (2 • actO S T g⁻¹ h⁻¹ u : WO S T) = actO S T g⁻¹ h⁻¹ (2 • u) := by
      rw [actO_eq, actO_eq, two_nsmul, two_nsmul, Matrix.mul_add, Matrix.add_mul]
    have h3 := hW.om_heis g h (actO S T g⁻¹ h⁻¹ (2 • u)) f hf.1
    rw [back, ← h2, h1] at h3
    exact h3.symm
  · have h1 := hf.2.2 e he _ (mem u hu) (isHalf_actO g⁻¹ h⁻¹ hh')
    have h3 := hW.om_heis g h (actO S T g⁻¹ h⁻¹ u) f hf.1
    rw [back, h1] at h3
    exact h3.symm

theorem vacO_ne_zero {sS sT LS LT} {f : WO S T → ℂ} (hf : IsVacO ψ θ S T sS sT LS LT f) : f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, hall⟩ := hf.2.norm
  have := hall p hp
  simp [nrm2] at this

theorem om_ne_zero (p : GA D S × GA D T) {f : WO S T → ℂ} (hf : f ≠ 0) : om p f ≠ 0 := by
  intro h0
  apply hf
  have : om p⁻¹ (om p f) = f := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  rw [← this, h0, map_zero]

theorem gen (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : GlobalTheory.FinPl.Lat S} {Λ' M' : GlobalTheory.FinPl.Lat T}
    (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M) (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M')
    {g : GA D S} {h : GA D T} (hgf : g ∈ GfC S) (hhf : h ∈ GfC T)
    (hg : GlobalTheory.FinPl.Moves S g Λ M fun _ => True) (hh : GlobalTheory.FinPl.Moves T h Λ' M' fun _ => True)
    {sS sT} (BS BT) {f : WO S T → ℂ} (hf : IsVacO ψ θ S T sS sT (Λ : Set _) (Λ' : Set _) f) :
    (∀ P, ∀ x ∈ GinfC S, ∀ x' ∈ GinfC T, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True)
      (om (x * g, x' * h) (pureTensorO ψ θ S T sS sT BS BT f P))) ∧
      om (g, h) (pureTensorO ψ θ S T sS sT BS BT f 1) ≠ 0 := by
  have hθ : IsInfFam θ := hf.2.inf
  refine ⟨fun P x hx x' hx' => ?_, ?_⟩
  · have hv : GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) (om (g, h) f) :=
      vac_move hW hΛ hM hΛ' hM' hg hh ⟨hf.2.theta, hf.2.lat⟩
    have hfin := GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT g h
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hgf, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hhf, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hgf, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hhf, Matrix.one_mul]) f hf.2.theta P
    have e1 : ((x * g, x' * h) : GA D S × GA D T) = (x, x') * (g, h) := rfl
    rw [e1, map_mul, Module.End.mul_apply, hfin.2]
    exact (GlobalTheory.FockComb.om_pureTensorO_comb D ψ θ S T χS χT om hθ hW sS sT BS BT 0 (om (g, h) f) 0 0
      (fun u hu => by simp at hu) hv.1 GlobalTheory.OrientedHeis.theta_zero 1 (one_mem _) 1 (one_mem _)
      (by rw [map_zero, zero_smul]) P x hx x' hx').2 M M' hv
  · rw [GlobalTheory.FiniteFock.pureTensorO_one]
    exact om_ne_zero _ (vacO_ne_zero hf)

end Gen

theorem fock_vac_moved : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j + 1 < D.R.m → ∀ (g : GA D (Yc D j)) (g' : GA D (Yc D (j + 1))), g ∈ GfC (Yc D j) → g' ∈ GfC (Yc D (j + 1)) → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M → IsSelfDualC (Yc D (j + 1)) M' → (∀ P, GlobalTheory.FinPl.Moves (Yc D j) g ((pk W).ΛY j) M P) → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g' ((pk W).ΛY (j + 1)) M' P) → (∀ P, ∀ x ∈ GinfC (Yc D j), ∀ x' ∈ GinfC (Yc D (j + 1)), GlobalTheory.FinPl.Vac (pk W).ψ (Yc D j) (Yc D (j + 1)) M M' (fun _ => True) ((pk W).ωY W.P.A3.A.μ0 j (x * g, x' * g') (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P))) ∧ (pk W).ωY W.P.A3.A.μ0 j (g, g') (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) 1) ≠ 0 := by
  intro D L hT Gi Gl Kc Yd cX ex W hW j hj g g' hg hg' M M' hM hM' hm hm'
  have hLev := hW.bot.hyp.2.2.2.1.lev
  have sd : ∀ i, i < D.R.m → IsSelfDualC (Yc D i) ((pk W).ΛY i) := fun i hi =>
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY i hi)
  exact gen (W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj) (sd j (by omega)) hM (sd (j + 1) hj) hM' hg hg' (hm _) (hm' _) _ _
    (W.Q.charW.base.chain.vY W.P.A3.A.μ0 j hj).1

end GlobalTheory.StepMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConsecutiveStepStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattices_consecutive_step : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j + 1 < D.R.m → ∀ (g : GA D (Yc D j)) (g' : GA D (Yc D (j + 1))), g ∈ GfC (Yc D j) → g' ∈ GfC (Yc D (j + 1)) → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M → IsSelfDualC (Yc D (j + 1)) M' → (∀ P, GlobalTheory.FinPl.Moves (Yc D j) g ((pk W).ΛY j) M P) → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g' ((pk W).ΛY (j + 1)) M' P) → (∀ P, ∀ x ∈ GinfC (Yc D j), ∀ x' ∈ GinfC (Yc D (j + 1)), GlobalTheory.FinPl.Vac (pk W).ψ (Yc D j) (Yc D (j + 1)) M M' (fun _ => True) ((pk W).ωY W.P.A3.A.μ0 j (x * g, x' * g') (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P))) ∧ (pk W).ωY W.P.A3.A.μ0 j (g, g') (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) 1) ≠ 0 := by
  exact @GlobalTheory.StepMove.fock_vac_moved
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselTranslateVector
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section

namespace GlobalTheory.MiTop

theorem fixAux {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (hId : GlobalTheory.Core.Mi.IdE X) (S : Set (Fin X.B.I.n → X.B.I.E)) (p : Fin X.B.I.n → X.B.I.E) (hp : p ∈ S)
    (g : GA D (D.sp.Y 0))
    (hg : (iotaX X h g).1 ∈ Formalism.L2.SG.PoincareInHH.HinfS X.B.I S ∧ (iotaX X h g).2 ∈ Formalism.L2.SG.PoincareInHH.HfinS X.B.I S) :
    Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) g) (fun k => Formalism.L2.Theta.incA D (X.ιE (p (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h) k)))) =
      fun k => Formalism.L2.Theta.incA D (X.ιE (p (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h) k))) := by
  have hR := (GlobalTheory.Core.SBesLevi.transport_fix D X.B.I X.ιE hId h (GlobalTheory.Core.Mi.rank_eq X h) S
    (Formalism.IndefR.RationalEmbedding.iota D g)).1 hg
  exact (GlobalTheory.Core.SBesLevi.bridge_fix D g _).2 (hR p hp)

end GlobalTheory.MiTop

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSecAddCsec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.SplitIntComp

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

theorem eq_sec_add_csec (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a = q.sec (q.pr a) + cA D (q.sec (q.pr (cA D a))) := by
  have h := (idem_iff q a).1 ha
  rw [q.sec_pr, q.sec_pr, map_mul, Formalism.L2.Theta.cA_cA]
  conv_lhs => rw [← h]
  ring

theorem mem_intAt_iff (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a ∈ intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k] := by
  constructor
  · intro h
    refine ⟨(q.int_iff _).2 ?_, (q.int_iff _).2 ?_⟩
    · rw [q.sec_pr, RingHom.map_mul]; exact mul_mem_intAE (e_mem_intAt q).2 h.2
    · rw [q.sec_pr, RingHom.map_mul]; exact mul_mem_intAE (e_mem_intAt q).2 ((cA_int_iff a).2 h.2)
  · rintro ⟨h1, h2⟩
    refine ⟨ha, ?_⟩
    rw [eq_sec_add_csec q ha, RingHom.map_add (f := _)]
    exact add_mem ((q.int_iff _).1 h1) ((cA_int_iff _).2 ((q.int_iff _).1 h2))

theorem val_xi (q : SplitPt D k) (h : q.UnitAA) : valuation k ((ofSplit q).xi) = 1 := by
  have he := e_mem_intAt q
  have hpe : q.pr q.e = 1 := by rw [← sec_one q, q.pr_sec]
  have h1 := ((mem_intAt_iff q (h.1 q.e he).1.1).1 (h.1 q.e he).1).1
  have h2 := ((mem_intAt_iff q (h.1 q.e he).2.1).1 (h.1 q.e he).2).1
  rw [map_mul, hpe, mul_one] at h1 h2
  have hne : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hprod : q.pr (incA D D.host.xi0⁻¹) * q.pr (incA D D.host.xi0) = 1 := by
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hne, map_one, map_one]
  change valuation k (q.pr (incA D D.host.xi0)) = 1
  have v1 := (Valuation.mem_integer_iff _ _).1 h1
  have v2 := (Valuation.mem_integer_iff _ _).1 h2
  have v3 := congrArg (valuation k) hprod
  rw [map_mul, map_one] at v3
  refine le_antisymm v1 ?_
  by_contra hlt
  push_neg at hlt
  have := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos v2 hlt zero_le' zero_lt_one
  rw [v3, mul_one] at this
  exact lt_irrefl _ this

end GlobalTheory.SplitIntComp
end
end
