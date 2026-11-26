module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationNormOverDegreeSmulEqAddValuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeSupWiderBandGenCentralEigenforms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOrbitConjCompactModCentralizerUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOrbitConjCompactModCentralizerUnitary
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

noncomputable section
namespace GlobalTheory.OrbitU

theorem locCpt (E : Type) [Field E] [NumberField E] (w : Pl E) : LocallyCompactSpace (w.adicCompletion E) := by
  have h : (w.adicCompletionIntegers E : Set (w.adicCompletion E)) =
      ((Valued.v : Valuation (w.adicCompletion E) _).integer : Set (w.adicCompletion E)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  have ho : IsOpen (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
    rw [h]; exact Valued.isOpen_integer _
  exact (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w).locallyCompactSpace_of_mem_nhds_of_addGroup
    (ho.mem_nhds (zero_mem _))

theorem glTop (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) : LocallyCompactSpace (GLw n w) ∧ SigmaCompactSpace (GLw n w) := by
  haveI := locCpt E w
  haveI hM : LocallyCompactSpace (Matrix (Fin n) (Fin n) (w.adicCompletion E)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → w.adicCompletion E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  haveI : ProperSpace (w.adicCompletion E) := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (w.adicCompletion E)) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → w.adicCompletion E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (GLw n w) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (GLw n w) := Units.isClosedEmbedding_embedProduct.isEmbedding.secondCountableTopology
  exact ⟨inferInstance, sigmaCompactSpace_of_locallyCompact_secondCountable⟩

def starU {K : Type} [Field K] {n : ℕ} (σ : K →+* K) (g : GL (Fin n) K) : GL (Fin n) K where
  val := cT σ (g : Matrix (Fin n) (Fin n) K)
  inv := cT σ ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  val_inv := by rw [← cT_mul, Units.inv_mul, cT_one]
  inv_val := by rw [← cT_mul, Units.mul_inv, cT_one]

theorem orbit_cpt_U : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ C : Set (UL n w), IsCompact C → ∃ Ω : Set (UL n w), IsCompact Ω ∧ ∀ g : UL n w, g⁻¹ * y * g ∈ C → ∃ t ∈ twCent (MonoidHom.id (UL n w)) y, ∃ ω ∈ Ω, g = t * ω := by
  intro E _ _ _ hE n w y hy C hC
  have hCG : IsCompact (Subtype.val '' C : Set (GLw n w)) := hC.image continuous_subtype_val
  obtain ⟨D, hD, hDg⟩ := GlobalTheory.OrbitCptW.orbit_cpt_w E hE n w y.1 hy _ hCG
  have hcl := (GlobalTheory.LocFinU.isClosed_UL n w).isClosedEmbedding_subtypeVal
  have hgC : ∀ g : UL n w, g⁻¹ * y * g ∈ C → g.1⁻¹ * y.1 * g.1 ∈ (Subtype.val '' C : Set (GLw n w)) :=
    fun g hg => ⟨_, hg, rfl⟩
  by_cases hs : IsSplitAt w
  · have hUL : ∀ g : GLw n w, g ∈ UL n w := fun g => by unfold UL; rw [if_pos hs]; trivial
    refine ⟨Subtype.val ⁻¹' D, hcl.isCompact_preimage hD, fun g hg => ?_⟩
    obtain ⟨z, hz, d, hd, hgd⟩ := hDg g.1 (hgC g hg)
    exact ⟨⟨z, hUL z⟩, Subtype.ext hz, ⟨d, hUL d⟩, hd, Subtype.ext hgd⟩
  obtain ⟨hσc, hσi, -⟩ := GlobalTheory.ConjAtPlace.main E hE w
  set σ := cj w with hσ
  have hmemU : ∀ g : GLw n w, g ∈ UL n w ↔ cT σ g.val * g.val = 1 := by
    intro g; unfold UL; rw [if_neg hs]; show cT σ _ * 1 * _ = 1 ↔ _; rw [Matrix.mul_one]
  have hcTc : Continuous fun M : Matrix (Fin n) (Fin n) (w.adicCompletion E) => cT σ M :=
    (continuous_id.matrix_map hσc).matrix_transpose
  have hcc : ∀ M : Matrix (Fin n) (Fin n) (w.adicCompletion E), cT σ (cT σ M) = M := by
    intro M; ext i j; simp [cT, hσi]
  have hstarc : Continuous (starU σ : GLw n w → GLw n w) := by
    rw [Units.continuous_iff]
    exact ⟨hcTc.comp Units.continuous_val, hcTc.comp Units.continuous_coe_inv⟩
  obtain ⟨lc, sc⟩ := glTop E w n
  let Z : Subgroup (GLw n w) := Subgroup.centralizer {y.1}
  have hZ : ∀ z : GLw n w, z ∈ Z ↔ z.val * y.1.val = y.1.val * z.val := by
    intro z
    rw [Subgroup.mem_centralizer_singleton_iff]
    change z * y.1 = y.1 * z ↔ _
    exact Units.ext_iff
  have hZc : IsClosed (Z : Set (GLw n w)) := by
    have : (Z : Set (GLw n w)) = {z | z * y.1 = y.1 * z} := by
      ext z; exact Subgroup.mem_centralizer_singleton_iff
    rw [this]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  haveI : LocallyCompactSpace Z := hZc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace Z := hZc.isClosedEmbedding_subtypeVal.sigmaCompactSpace
  have hcomm : ∀ a b : Z, a * b = b * a := fun a b => Subtype.ext (Units.ext
    (GlobalTheory.commute_of_commute_separable_charpoly _ n y.1.val a.1.val b.1.val hy ((hZ _).1 a.2) ((hZ _).1 b.2)))
  have hyU : cT σ y.1.val * y.1.val = 1 := (hmemU _).1 y.2
  have hyU' : y.1.val * cT σ y.1.val = 1 := mul_eq_one_comm.1 hyU
  have hst : ∀ z ∈ Z, starU σ z ∈ Z := by
    intro z hz
    rw [hZ] at hz ⊢
    have h1 : cT σ y.1.val * cT σ z.val = cT σ z.val * cT σ y.1.val := by rw [← cT_mul, ← cT_mul, hz]
    show cT σ z.val * y.1.val = y.1.val * cT σ z.val
    calc cT σ z.val * y.1.val = (y.1.val * cT σ y.1.val) * cT σ z.val * y.1.val := by rw [hyU', Matrix.one_mul]
      _ = y.1.val * (cT σ y.1.val * cT σ z.val) * y.1.val := by simp only [Matrix.mul_assoc]
      _ = y.1.val * (cT σ z.val * cT σ y.1.val) * y.1.val := by rw [h1]
      _ = y.1.val * cT σ z.val * (cT σ y.1.val * y.1.val) := by simp only [Matrix.mul_assoc]
      _ = y.1.val * cT σ z.val := by rw [hyU, Matrix.mul_one]
  let τ : Z →* Z :=
    { toFun := fun z => ⟨starU σ z.1, hst _ z.2⟩
      map_one' := Subtype.ext (Units.ext (cT_one σ))
      map_mul' := fun a b => by
        have : (⟨starU σ (a * b).1, hst _ (a * b).2⟩ : Z) = ⟨starU σ b.1, hst _ b.2⟩ * ⟨starU σ a.1, hst _ a.2⟩ :=
          Subtype.ext (Units.ext (by show cT σ (a.1.val * b.1.val) = cT σ b.1.val * cT σ a.1.val; exact cT_mul σ _ _))
        rw [this, hcomm] }
  have hτ : ∀ z : Z, ((τ z : Z) : GLw n w) = starU σ z.1 := fun z => rfl
  have hτc : Continuous τ := continuous_induced_rng.2 (hstarc.comp continuous_subtype_val)
  have hτi : ∀ z, τ (τ z) = z := fun z => Subtype.ext (Units.ext (hcc _))
  have hsq : ∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s := by
    obtain ⟨W, hW, hWs⟩ : ∃ W ∈ nhds (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)), ∀ s ∈ W, ∃ r : Matrix (Fin n) (Fin n) (w.adicCompletion E), r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) (w.adicCompletion E), a * s = s * a → a * r = r * a) ∧ ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by
      haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
      letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
      exact GlobalTheory.T.exists_matrix_sqrt_near_one_ultrametric (w.adicCompletion E) n σ hσc
    refine ⟨(fun z : Z => (z.1 : Matrix (Fin n) (Fin n) _)) ⁻¹' W,
      (Units.continuous_val.comp continuous_subtype_val).continuousAt.preimage_mem_nhds (by simpa using hW), ?_⟩
    intro s hs hτs
    obtain ⟨r, hrr, hrc, hrs⟩ := hWs _ hs
    have hsv : cT σ s.1.val = s.1.val := by
      have h := congrArg (fun u : Z => u.1.val) hτs
      exact h
    have hrr' : r * r = s.1.val := hrr
    have hu : IsUnit r := isUnit_of_mul_isUnit_left (hrr'.symm ▸ s.1.isUnit)
    have hrZ : hu.unit ∈ Z := (hZ _).2 (hrc _ ((hZ _).1 s.2).symm).symm
    refine ⟨⟨hu.unit, hrZ⟩, Subtype.ext (Units.ext (hrs hsv)), Subtype.ext (Units.ext hrr')⟩
  let DZ : Set Z := Subtype.val ⁻¹' ((fun d : GLw n w => starU σ d⁻¹ * d⁻¹) '' D)
  have hDZ : IsCompact DZ := hZc.isClosedEmbedding_subtypeVal.isCompact_preimage
    (hD.image ((hstarc.comp continuous_inv).mul continuous_inv))
  obtain ⟨B, hB, hBz⟩ := GlobalTheory.T.exists_compact_mod_normOneKernel_involution Z hcomm τ hτc hτi hsq DZ hDZ
  refine ⟨Subtype.val ⁻¹' ((Subtype.val '' B : Set (GLw n w)) * D),
    hcl.isCompact_preimage ((hB.image continuous_subtype_val).mul hD), fun g hg => ?_⟩
  obtain ⟨z, hz, d, hd, hgd⟩ := hDg g.1 (hgC g hg)
  have hzZ : z ∈ Z := (hZ z).2 (by simpa using congrArg Units.val hz)
  have hgU : cT σ g.1.val * g.1.val = 1 := (hmemU _).1 g.2
  have hN : τ ⟨z, hzZ⟩ * ⟨z, hzZ⟩ ∈ DZ := by
    refine ⟨d, hd, Units.ext ?_⟩
    have hg' : g.1.val = z.val * d.val := by rw [hgd, Units.val_mul]
    rw [hg', cT_mul] at hgU
    have e1 : cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * cT σ d.val = 1 := by
      rw [← cT_mul, Units.mul_inv, cT_one]
    show cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) = cT σ z.val * z.val
    calc cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _)
        = cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * (cT σ d.val * cT σ z.val * (z.val * d.val)) * ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) := by
          rw [hgU, Matrix.mul_one]
      _ = (cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * cT σ d.val) * (cT σ z.val * z.val) * (d.val * ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _)) := by
          simp only [Matrix.mul_assoc]
      _ = cT σ z.val * z.val := by rw [e1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨t, ht, b, hb, hzt⟩ := hBz _ hN
  have htU : t.1 ∈ UL n w := by
    have h := congrArg (fun u : Z => u.1.val) ht
    exact (hmemU _).2 h
  have hgt : g.1 = t.1 * (b.1 * d) := by
    rw [hgd, ← mul_assoc]; exact congrArg (· * d) (congrArg Subtype.val hzt)
  have hωU : b.1 * d ∈ UL n w := by
    have : b.1 * d = t.1⁻¹ * g.1 := by rw [hgt, inv_mul_cancel_left]
    rw [this]; exact (UL n w).mul_mem ((UL n w).inv_mem htU) g.2
  refine ⟨⟨t.1, htU⟩, Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 t.2), ⟨b.1 * d, hωU⟩,
    ⟨b.1, ⟨b, hb, rfl⟩, d, hd, rfl⟩, Subtype.ext hgt⟩

end GlobalTheory.OrbitU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOrbitConjCompactModCentralizerUnitaryStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_orbit_conj_compact_mod_centralizer_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ C : Set (UL n w), IsCompact C → ∃ Ω : Set (UL n w), IsCompact Ω ∧ ∀ g : UL n w, g⁻¹ * y * g ∈ C → ∃ t ∈ twCent (MonoidHom.id (UL n w)) y, ∃ ω ∈ Ω, g = t * ω := by
  first | exact @GlobalTheory.OrbitU.orbit_cpt_U | exact GlobalTheory.OrbitU.orbit_cpt_U | (intros; apply GlobalTheory.OrbitU.orbit_cpt_U <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdSumFixEig
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.StdSumFix

variable {D : D7}

theorem hatId_mul_left {𝔪 : Ideal (𝓞 D.host.E)} {t y : AE D} (ht : t ∈ OhE D) (hy : y ∈ hatId D 𝔪) :
    t * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, t * s, mul_mem ht hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

abbrev mat {N : ℕ} (k : GA D N) : Matrix (Fin N) (Fin N) (AE D) := ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))

theorem mat_mul {N : ℕ} (x y : GA D N) : mat (x * y) = mat x * mat y := rfl

theorem mat_inv_mul {N : ℕ} (x : GA D N) : mat x⁻¹ * mat x = 1 := by
  simp [mat]

theorem mat_mul_inv {N : ℕ} (x : GA D N) : mat x * mat x⁻¹ = 1 := by
  simp [mat]

theorem ent_mul_left {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {A B : Matrix (Fin N) (Fin N) (AE D)}
    (hA : ∀ i j, A i j ∈ OhE D) (hB : ∀ i j, B i j ∈ hatId D 𝔪) (i j : Fin N) : (A * B) i j ∈ hatId D 𝔪 := by
  rw [Matrix.mul_apply]; exact sum_mem fun l _ => hatId_mul_left (hA i l) (hB l j)

theorem ent_mul_right {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {A B : Matrix (Fin N) (Fin N) (AE D)}
    (hB : ∀ i j, B i j ∈ hatId D 𝔪) (hA : ∀ i j, A i j ∈ OhE D) (i j : Fin N) : (B * A) i j ∈ hatId D 𝔪 := by
  rw [Matrix.mul_apply]; exact sum_mem fun l _ => by rw [mul_comm]; exact hatId_mul_left (hA l j) (hB i l)

theorem ent_of_mem {N : ℕ} {k : GA D N} (hk : k ∈ intG D N) (i j : Fin N) : mat k i j ∈ OhE D :=
  ((mem_intG k).1 hk i j).1

theorem ent_inv_of_mem {N : ℕ} {k : GA D N} (hk : k ∈ intG D N) (i j : Fin N) : mat k⁻¹ i j ∈ OhE D :=
  ((mem_intG k⁻¹).1 (inv_mem hk) i j).1

variable {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ}

theorem congOne_one : CongOne D 𝔪 (1 : GA D N) := fun i j => by
  simp only [OneMemClass.coe_one, Units.val_one, sub_self, Matrix.zero_apply]; exact zero_mem _

theorem congOne_mul {x y : GA D N} (hx : x ∈ intG D N) (cx : CongOne D 𝔪 x) (cy : CongOne D 𝔪 y) :
    CongOne D 𝔪 (x * y) := fun i j => by
  have e : mat (x * y) - 1 = mat x * (mat y - 1) + (mat x - 1) := by rw [mat_mul, mul_sub, mul_one]; abel
  change (mat (x * y) - 1) i j ∈ _
  rw [e, Matrix.add_apply]
  exact add_mem (ent_mul_left (ent_of_mem hx) cy i j) (cx i j)

theorem congOne_inv {x : GA D N} (hx : x ∈ intG D N) (cx : CongOne D 𝔪 x) : CongOne D 𝔪 x⁻¹ := fun i j => by
  have e : mat x⁻¹ - 1 = -(mat x⁻¹ * (mat x - 1)) := by rw [mul_sub, mat_inv_mul, mul_one]; abel
  change (mat x⁻¹ - 1) i j ∈ _
  rw [e, Matrix.neg_apply]
  exact neg_mem (ent_mul_left (ent_inv_of_mem hx) cx i j)

theorem congOne_conj {g x : GA D N} (hg : g ∈ intG D N) (cx : CongOne D 𝔪 x) : CongOne D 𝔪 (g * x * g⁻¹) :=
  fun i j => by
  have e : mat (g * x * g⁻¹) - 1 = mat g * (mat x - 1) * mat g⁻¹ := by
    rw [mat_mul, mat_mul, mul_sub, sub_mul, mul_one, mat_mul_inv]
  change (mat (g * x * g⁻¹) - 1) i j ∈ _
  rw [e]
  exact ent_mul_right (ent_mul_left (ent_of_mem hg) cx) (ent_inv_of_mem hg) i j

end GlobalTheory.StdSumFix

namespace GlobalTheory.StdSumFix

variable {D : D7}

theorem zero_mem_TT (T : Tor D) (N N' : ℕ) : (0 : VC D N N' → ℂ) ∈ TT D T N N' :=
  ⟨differentiable_const 0, 1, one_pos, fun x _ => by funext z; simp [Wd, U]⟩

theorem add_mem_TT {T : Tor D} {N N' : ℕ} {F G : VC D N N' → ℂ} (hF : F ∈ TT D T N N') (hG : G ∈ TT D T N N') :
    F + G ∈ TT D T N N' := by
  obtain ⟨hF1, m, hm, hFm⟩ := hF
  obtain ⟨hG1, n, hn, hGn⟩ := hG
  refine ⟨hF1.add hG1, m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩
  have h1 := hFm (n • x) (AddSubgroup.nsmul_mem _ hx n)
  have h2 := hGn (m • x) (AddSubgroup.nsmul_mem _ hx m)
  rw [smul_smul] at h1 h2
  rw [mul_comm n m] at h2
  funext z
  have e1 := congrFun h1 z
  have e2 := congrFun h2 z
  simp only [Wd, U, Pi.add_apply] at e1 e2 ⊢
  linear_combination e1 + e2

theorem Om_sum {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {e0 : VC D N N' → ℂ} (W : WeilO D cc δ N N' e0)
    (g : GA D N) (g' : GA D N') {ι : Type*} (s : Finset ι) (f : ι → VC D N N' → ℂ)
    (hf : ∀ i ∈ s, f i ∈ TT D (tor0 D cc δ) N N') :
    (∑ i ∈ s, f i) ∈ TT D (tor0 D cc δ) N N' ∧ W.Om g g' (∑ i ∈ s, f i) = ∑ i ∈ s, W.Om g g' (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using zero_mem_TT (tor0 D cc δ) N N', ?_⟩
    have h := W.smul g g' 0 0 (zero_mem_TT _ N N')
    simpa using h
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hfi := hf i (Finset.mem_insert_self i s)
    obtain ⟨h1, h2⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    exact ⟨add_mem_TT hfi h1, by rw [W.add g g' _ hfi _ h1, h2]⟩

end GlobalTheory.StdSumFix

namespace GlobalTheory.StdSumFix

variable {D : D7}

section Reps

variable {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) {𝔪 : Ideal (𝓞 D.host.E)}
  {v : VC D a d → ℂ} {R : Finset (GA D a)}

theorem Om_rep (hv : v ∈ TT D (tor0 D ⊤ δ) a d) (hfix : ∀ k ∈ intG D a, CongOne D 𝔪 k → W.Om k 1 v = v)
    {x r : GA D a} (hx : x ∈ intG D a) (hr : r ∈ intG D a) (hc : CongOne D 𝔪 (r⁻¹ * x)) :
    W.Om x 1 v = W.Om r 1 v := by
  have h := W.mul r (r⁻¹ * x) 1 1 v hv
  rw [mul_inv_cancel_left, mul_one] at h
  rw [h, hfix _ (mul_mem (inv_mem hr) hx) hc]

theorem sum_reindex (hv : v ∈ TT D (tor0 D ⊤ δ) a d) (hfix : ∀ k ∈ intG D a, CongOne D 𝔪 k → W.Om k 1 v = v)
    (hRi : ∀ r ∈ R, r ∈ intG D a) (hR : ∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k))
    (φ : GA D a → GA D a) (hφ : ∀ r ∈ R, φ r ∈ intG D a)
    (inj : ∀ r₁ ∈ R, ∀ r₂ ∈ R, ∀ s ∈ R, CongOne D 𝔪 (s⁻¹ * φ r₁) → CongOne D 𝔪 (s⁻¹ * φ r₂) → r₁ = r₂)
    (surj : ∀ s ∈ R, ∃ r ∈ R, CongOne D 𝔪 (s⁻¹ * φ r)) :
    ∑ r ∈ R, W.Om (φ r) 1 v = ∑ s ∈ R, W.Om s 1 v := by
  classical
  let ψ : GA D a → GA D a := fun r => if h : r ∈ R then (hR (φ r) (hφ r h)).exists.choose else r
  have hψ : ∀ r ∈ R, ψ r ∈ R ∧ CongOne D 𝔪 ((ψ r)⁻¹ * φ r) := fun r hr => by
    simp only [ψ, dif_pos hr]; exact (hR (φ r) (hφ r hr)).exists.choose_spec
  refine Finset.sum_nbij ψ (fun r hr => (hψ r hr).1) ?_ ?_ ?_
  · intro r₁ hr₁ r₂ hr₂ e
    have h1 := (hψ r₁ hr₁).2
    have h2 := (hψ r₂ hr₂).2
    rw [e] at h1
    exact inj r₁ hr₁ r₂ hr₂ (ψ r₂) (hψ r₂ hr₂).1 h1 h2
  · intro s hs
    obtain ⟨r, hr, hc⟩ := surj s hs
    exact ⟨r, hr, (hR (φ r) (hφ r hr)).unique (hψ r hr) ⟨hs, hc⟩⟩
  · intro r hr
    exact Om_rep W hv hfix (hφ r hr) (hRi _ (hψ r hr).1) (hψ r hr).2

end Reps

theorem stdSum_fix_eig : ∀ (D : D7) (δ : ℂ) (a d : ℕ) (e0 : VC D a d → ℂ) (W : WeilO D ⊤ δ a d e0)
    (𝔪 : Ideal (𝓞 D.host.E)) (v : VC D a d → ℂ), v ∈ TT D (tor0 D ⊤ δ) a d →
    (∀ k ∈ intG D a, CongOne D 𝔪 k → W.Om k 1 v = v) → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) →
    (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) →
    (∀ k ∈ intG D a, W.Om k 1 (∑ r ∈ R, W.Om r 1 v) = ∑ r ∈ R, W.Om r 1 v) ∧
    ∀ (j : GA D d) (k : GA D a) (c : ℂ), k ∈ intG D a → W.Om 1 j v = c • W.Om k 1 v →
      W.Om 1 j (∑ r ∈ R, W.Om r 1 v) = c • ∑ r ∈ R, W.Om r 1 v := by
  intro D δ a d e0 W 𝔪 v hv hfix R hRi hR
  have hTT : ∀ r ∈ R, W.Om r 1 v ∈ TT D (tor0 D ⊤ δ) a d := fun r _ => W.maps r 1 v hv
  have uniq : ∀ r₁ ∈ R, ∀ r₂ ∈ R, CongOne D 𝔪 (r₁⁻¹ * r₂) → r₁ = r₂ := fun r₁ h₁ r₂ h₂ hc =>
    (hR r₂ (hRi r₂ h₂)).unique ⟨h₁, hc⟩ ⟨h₂, by rw [inv_mul_cancel]; exact congOne_one⟩
  refine ⟨fun k hk => ?_, fun j k c hk hj => ?_⟩
  · rw [(Om_sum W k 1 R _ hTT).2]
    have e : ∀ r ∈ R, W.Om k 1 (W.Om r 1 v) = W.Om (k * r) 1 v := fun r _ => by
      rw [← W.mul k r 1 1 v hv, mul_one]
    rw [Finset.sum_congr rfl e]
    refine sum_reindex W hv hfix hRi hR (fun r => k * r) (fun r hr => mul_mem hk (hRi r hr)) ?_ ?_
    · intro r₁ h₁ r₂ h₂ s hs c₁ c₂
      have hm : s⁻¹ * (k * r₁) ∈ intG D a := mul_mem (inv_mem (hRi s hs)) (mul_mem hk (hRi r₁ h₁))
      have h := congOne_mul (inv_mem hm) (congOne_inv hm c₁) c₂
      have e' : (s⁻¹ * (k * r₁))⁻¹ * (s⁻¹ * (k * r₂)) = r₁⁻¹ * r₂ := by group
      rw [e'] at h
      exact uniq r₁ h₁ r₂ h₂ h
    · intro s hs
      obtain ⟨r, ⟨hr, hc⟩, -⟩ := hR (k⁻¹ * s) (mul_mem (inv_mem hk) (hRi s hs))
      refine ⟨r, hr, ?_⟩
      have h := congOne_inv (mul_mem (inv_mem (hRi r hr)) (mul_mem (inv_mem hk) (hRi s hs))) hc
      have e' : (r⁻¹ * (k⁻¹ * s))⁻¹ = s⁻¹ * (k * r) := by group
      rwa [e'] at h
  · rw [(Om_sum W 1 j R _ hTT).2]
    have e : ∀ r ∈ R, W.Om 1 j (W.Om r 1 v) = c • W.Om (r * k) 1 v := fun r _ => by
      rw [← W.mul 1 r j 1 v hv, one_mul, mul_one,
        show W.Om r j v = W.Om (r * 1) (1 * j) v by rw [mul_one, one_mul], W.mul r 1 1 j v hv, hj,
        W.smul r 1 c _ (W.maps k 1 v hv), ← W.mul r k 1 1 v hv, mul_one]
    rw [Finset.sum_congr rfl e, ← Finset.smul_sum]
    congr 1
    refine sum_reindex W hv hfix hRi hR (fun r => r * k) (fun r hr => mul_mem (hRi r hr) hk) ?_ ?_
    · intro r₁ h₁ r₂ h₂ s hs c₁ c₂
      have hm₂ : s⁻¹ * (r₂ * k) ∈ intG D a := mul_mem (inv_mem (hRi s hs)) (mul_mem (hRi r₂ h₂) hk)
      have hm₁ : s⁻¹ * (r₁ * k) ∈ intG D a := mul_mem (inv_mem (hRi s hs)) (mul_mem (hRi r₁ h₁) hk)
      have h := congOne_conj (g := r₂⁻¹ * s) (mul_mem (inv_mem (hRi r₂ h₂)) (hRi s hs))
        (congOne_mul hm₁ c₁ (congOne_inv hm₂ c₂))
      have e' : r₂⁻¹ * s * (s⁻¹ * (r₁ * k) * (s⁻¹ * (r₂ * k))⁻¹) * (r₂⁻¹ * s)⁻¹ = r₂⁻¹ * r₁ := by group
      rw [e'] at h
      exact (uniq r₂ h₂ r₁ h₁ h).symm
    · intro s hs
      obtain ⟨r, ⟨hr, hc⟩, -⟩ := hR (s * k⁻¹) (mul_mem (hRi s hs) (inv_mem hk))
      refine ⟨r, hr, ?_⟩
      have hm : r⁻¹ * (s * k⁻¹) ∈ intG D a := mul_mem (inv_mem (hRi r hr)) (mul_mem (hRi s hs) (inv_mem hk))
      have h := congOne_conj (g := k⁻¹) (inv_mem hk) (congOne_inv hm hc)
      have e' : k⁻¹ * (r⁻¹ * (s * k⁻¹))⁻¹ * k⁻¹⁻¹ = s⁻¹ * (r * k) := by group
      rwa [e'] at h

end GlobalTheory.StdSumFix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFormsEquicontinuousOnBand
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFormsEquicontinuousOnBand
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology Pointwise

namespace GlobalTheory.HCF.Equi

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_infGL' : Continuous (infGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

theorem continuous_pInf' : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_mapInf : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf')

omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_mapFin : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))


omit [_root_.NumberField.IsTotallyComplex E] in
theorem absDetA_eq (g : GA E a) :
    absDetA g = (GroundTheory.Global.IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det g) : ℝ) := by
  unfold absDetA
  exact GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E) _


omit [_root_.NumberField.IsTotallyComplex E] in
theorem absDetA_mul (g h : GA E a) : absDetA (g * h) = absDetA g * absDetA h := by
  rw [absDetA_eq, absDetA_eq, absDetA_eq, map_mul, map_mul, Positive.val_mul]


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_absDetA : Continuous (absDetA (E := E) (a := a)) := by
  have e : (absDetA (E := E) (a := a)) =
      fun g => (GroundTheory.Global.IdeleGroup.ideleModule E (GroundTheory.Automorphic.AdelicGLn.det E a g) : ℝ) :=
    funext absDetA_eq
  rw [e]
  exact continuous_subtype_val.comp (GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp
    (GroundTheory.Automorphic.AdelicGLn.continuous_det E a))

theorem continuous_along (ψ : Sm E a) (g : GA E a) : Continuous fun z : GL (Fin a) (Cinf E) => ψ.1 (g * infGL E a z) := by
  have h := (ψ.2 g).continuousOn
  have h2 : Continuous fun z : GL (Fin a) (Cinf E) => chart ψ.1 g (toL z.val) :=
    h.comp_continuous (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E)) : _) fun z => val_mem_invSet z
  exact h2.congr fun z => chart_val ψ.1 g z

theorem equicontinuous_band : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ),
    FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ U ∈ 𝓝 (1 : GA E a), ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) →
      ∀ g ∈ band E a, ∀ u ∈ U, g * u ∈ band E a → ‖φ.1 (g * u) - φ.1 g‖ ≤ ε * M := by
  intro E _ _ _ a L hL W hW X hX N ε hε
  letI : MeasurableSpace (GL (Fin a) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin a) (Cinf E)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GL (Fin a) (Cinf E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  set μ : Measure (GL (Fin a) (Cinf E)) := Measure.haar
  obtain ⟨α, hαc, hαs, hα⟩ := GlobalTheory.T.harishChandra_exists_reproducing_testFunction_GL E a L hL W hW X hX N μ inferInstance
  have hint : ∀ (ψ : Sm E a) (g : GA E a), Integrable (fun y => ψ.1 (g * infGL E a y) * α y) μ := fun ψ g =>
    ((continuous_along ψ g).mul hαc).integrable_of_hasCompactSupport hαs.mul_left

  have hrep : ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ g,
      ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hα x hx
    | zero => intro g; change ∫ z, (0 : ℂ) * α z ∂μ = 0; simp
    | add x y _ _ hx hy =>
      intro g
      change ∫ z, (x.1 (g * infGL E a z) + y.1 (g * infGL E a z)) * α z ∂μ = x.1 g + y.1 g
      simp_rw [add_mul]
      rw [integral_add (hint x g) (hint y g), hx, hy]
    | smul c x _ hx =>
      intro g
      change ∫ z, (c * x.1 (g * infGL E a z)) * α z ∂μ = c * x.1 g
      simp_rw [mul_assoc]
      rw [integral_const_mul, hx]

  have hfix : ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ k ∈ L, ∀ x, φ.1 (x * finGL E a k) = φ.1 x := by
    intro φ hφ k hk x
    induction hφ using Submodule.span_induction with
    | mem ψ hψ => exact congrArg (fun f : Sm E a => f.1 x) (hψ.2.1 k hk)
    | zero => rfl
    | add ψ χ _ _ h1 h2 =>
      change ψ.1 (x * finGL E a k) + χ.1 (x * finGL E a k) = ψ.1 x + χ.1 x
      rw [h1, h2]
    | smul c ψ _ h =>
      change c * ψ.1 (x * finGL E a k) = c * ψ.1 x
      rw [h]

  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : GL (Fin a) (Cinf E))
  have hKc : IsCompact (tsupport α) := hαs
  set K' := V * tsupport α with hK'
  have hK'c : IsCompact K' := hVc.mul hKc
  have hK'm : MeasurableSet K' := hK'c.measurableSet

  have hfc : Continuous fun z : GL (Fin a) (Cinf E) => absDetA (infGL E a z) :=
    continuous_absDetA.comp continuous_infGL'
  obtain ⟨B₁, hB₁⟩ := hK'c.exists_bound_of_continuousOn hfc.continuousOn
  obtain ⟨B₂, hB₂⟩ := hK'c.exists_bound_of_continuousOn
    (hfc.inv₀ fun z => (absDetA_pos _).ne').continuousOn
  set c := max 1 (max B₁ B₂) with hc
  have hc1 : 1 ≤ c := le_max_left _ _
  have hcK : ∀ z ∈ K', c⁻¹ ≤ absDetA (infGL E a z) ∧ absDetA (infGL E a z) ≤ c := by
    intro z hz
    have hp := absDetA_pos (infGL E a z)
    have h1 := hB₁ z hz
    have h2 : ‖(absDetA (infGL E a z))⁻¹‖ ≤ B₂ := hB₂ z hz
    rw [Real.norm_of_nonneg hp.le] at h1
    rw [Real.norm_of_nonneg (inv_nonneg.2 hp.le)] at h2
    refine ⟨?_, h1.trans ((le_max_left _ _).trans (le_max_right _ _))⟩
    rw [inv_le_comm₀ (by positivity) hp]
    exact h2.trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨C, hC⟩ := GlobalTheory.T.norm_le_sup_wider_band_genCentralEigenforms E a L hL W hW X hX N c hc1
  set C' := |C| + 1 with hC'
  have hC'0 : 0 < C' := by positivity
  set m := μ.real K' with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  set δ := ε / (C' * (m + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδe : C' * δ * (m + 1) = ε := by rw [hδ]; field_simp

  obtain ⟨v, hv, hvK⟩ := hK'c.mem_uniformity_of_prod (f := fun p x => α (p⁻¹ * x)) (s := Set.univ) (q := 1)
    (by exact (hαc.comp (continuous_fst.inv.mul continuous_snd)).continuousOn) (Set.mem_univ _)
    (Metric.dist_mem_uniformity hδ0)
  rw [nhdsWithin_univ] at hv

  refine ⟨{u | Matrix.GeneralLinearGroup.map (pInf E) u ∈ v ∩ V ∧ Matrix.GeneralLinearGroup.map (pFin E) u ∈ L}, ?_, ?_⟩
  · change ((Matrix.GeneralLinearGroup.map (pInf E)) ⁻¹' (v ∩ V) ∩
      (Matrix.GeneralLinearGroup.map (pFin E)) ⁻¹' (L : Set _)) ∈ 𝓝 (1 : GA E a)
    refine Filter.inter_mem ?_ ?_
    · exact continuous_mapInf.continuousAt.preimage_mem_nhds (by rw [map_one]; exact Filter.inter_mem hv hV1)
    · exact continuous_mapFin.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hL.mem_nhds L.one_mem)
  intro φ hφ M hM g hg u hu _
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 one_mem_band)
  set y := Matrix.GeneralLinearGroup.map (pInf E) u with hy
  set k := Matrix.GeneralLinearGroup.map (pFin E) u with hk
  have hyv : y ∈ v := hu.1.1
  have hyV : y ∈ V := hu.1.2
  have hkL : k ∈ L := hu.2
  have hgu : φ.1 (g * u) = φ.1 (g * infGL E a y) := by
    rw [← infGL_mul_finGL u, ← mul_assoc, hfix φ hφ k hkL]
  rw [hgu]

  have e1 : φ.1 (g * infGL E a y) = ∫ z, φ.1 (g * infGL E a z) * α (y⁻¹ * z) ∂μ := by
    rw [← hrep φ hφ (g * infGL E a y),
      ← integral_mul_left_eq_self (fun z => φ.1 (g * infGL E a z) * α (y⁻¹ * z)) y]
    congr 1
    funext x
    simp [map_mul, mul_assoc]
  have hi1 : Integrable (fun z => φ.1 (g * infGL E a z) * α (y⁻¹ * z)) μ :=
    ((continuous_along φ g).mul (hαc.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (hαs.comp_homeomorph (Homeomorph.mulLeft y⁻¹)))
  have e2 : φ.1 (g * infGL E a y) - φ.1 g = ∫ z, φ.1 (g * infGL E a z) * (α (y⁻¹ * z) - α z) ∂μ := by
    rw [e1, ← hrep φ hφ g, ← integral_sub hi1 (hint φ g)]
    simp_rw [mul_sub]
  rw [e2]

  have hpt : ∀ z, ‖φ.1 (g * infGL E a z) * (α (y⁻¹ * z) - α z)‖ ≤ K'.indicator (fun _ => C' * M * δ) z := by
    intro z
    by_cases hz : z ∈ K'
    · rw [Set.indicator_of_mem hz, norm_mul]
      have hd := hcK z hz
      have hg' := hg
      obtain ⟨hg1, hg2⟩ := hg'
      have hb1 : c⁻¹ ≤ absDetA (g * infGL E a z) := by
        rw [absDetA_mul]
        have := absDetA_pos (infGL E a z)
        nlinarith
      have hb2 : absDetA (g * infGL E a z) ≤ 2 * c := by
        rw [absDetA_mul]
        have := absDetA_pos (infGL E a z)
        nlinarith
      have h1 : ‖φ.1 (g * infGL E a z)‖ ≤ C' * M :=
        (hC φ hφ M hM _ hb1 hb2).trans (mul_le_mul_of_nonneg_right (by rw [hC']; linarith [le_abs_self C]) hM0)
      have h2 : ‖α (y⁻¹ * z) - α z‖ ≤ δ := by
        have := hvK y hyv z hz
        simp only [inv_one, one_mul, Set.mem_setOf_eq] at this
        rw [← dist_eq_norm]; exact this.le
      exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    · rw [Set.indicator_of_notMem hz]
      have hz1 : α z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz ⟨1, mem_of_mem_nhds hV1, z, h, one_mul z⟩
      have hz2 : α (y⁻¹ * z) = 0 := image_eq_zero_of_notMem_tsupport fun h =>
        hz ⟨y, hyV, y⁻¹ * z, h, mul_inv_cancel_left y z⟩
      simp [hz1, hz2]
  have hint' : Integrable (K'.indicator (fun _ => C' * M * δ)) μ :=
    (integrableOn_const (C := C' * M * δ) hK'c.measure_lt_top.ne).integrable_indicator hK'm
  refine (norm_integral_le_of_norm_le hint' (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_indicator_const _ hK'm, smul_eq_mul, ← hm]
  have : 0 ≤ C' * M * δ := by positivity
  calc m * (C' * M * δ) ≤ (m + 1) * (C' * M * δ) := by nlinarith
    _ = ε * M := by rw [← hδe]; ring

end GlobalTheory.HCF.Equi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFormsEquicontinuousOnBandStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraForms_equicontinuous_on_band : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (1 : GA E a), ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) → ∀ g ∈ band E a, ∀ u ∈ U, g * u ∈ band E a → ‖φ.1 (g * u) - φ.1 g‖ ≤ ε * M := by
  first | exact @GlobalTheory.HCF.Equi.equicontinuous_band | exact GlobalTheory.HCF.Equi.equicontinuous_band | (intros; apply GlobalTheory.HCF.Equi.equicontinuous_band <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridBlockCongruenceTypePrimeDescription
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridBlockCongruenceTypePrimeDescription
namespace IteratedIwahori
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.IterJ

section Gen
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
theorem intM_submatrix_iff (e : a ≃ b) (M : Matrix a a k) :
    GlobalTheory.StepData.IntM (M.submatrix e.symm e.symm) ↔ GlobalTheory.StepData.IntM M :=
  ⟨fun h i j => by simpa using h (e i) (e j), fun h _ _ => h _ _⟩

theorem reGL_mem_KO_iff (e : a ≃ b) (g : GL a k) : reGL e g ∈ KO k b ↔ g ∈ KO k a := by
  rw [GlobalTheory.StepData.mem_KO, GlobalTheory.StepData.mem_KO, ← map_inv, reGL_val, reGL_val,
    intM_submatrix_iff, intM_submatrix_iff]


omit [Fintype a] [Fintype b] [DecidableEq b] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem symm_sub_one_apply [Fintype a] [Fintype b] [DecidableEq b] (e : a ≃ b) (h : GL b k) (x y : a) :
    (((reGL e).symm h).val - 1) x y = (h.val - 1) (e x) (e y) := by
  simp [reGL_symm_val, Matrix.one_apply]

end Gen

section Iter
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]

theorem blk_le {j : ℕ} (x : Ix r t j) : Ix.blk x ≤ j := by
  rcases x with x | ⟨c, s⟩
  · simp [Ix.blk]
  · simpa [Ix.blk] using c.2

theorem blk_ixSucc_inl {j : ℕ} (x : Ix r t j) : Ix.blk (ixSucc r t j (Sum.inl x)) = Ix.blk x := by
  rcases x with x | ⟨c, s⟩ <;> simp [Ix.blk, ixSucc]

theorem blk_ixSucc_inr {j : ℕ} (s : t) : Ix.blk (ixSucc r t j (Sum.inr s)) = j + 1 := by
  simp [Ix.blk, ixSucc]

theorem mem_iter_J (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (h : GL (Ix r t j) k) :
    h ∈ ((TypeDatum.principal k r).iter t μ hμ j).J ↔ h ∈ KO k (Ix r t j) ∧
      (∀ a b, Ix.blk b < Ix.blk a → valuation k (h.val a b) < 1) ∧
      ∀ a b : r, valuation k ((h.val - 1) (Sum.inl a) (Sum.inl b)) < 1 := by
  induction j with
  | zero =>
    rw [TypeDatum.iter_zero]
    have hK : (reGL (ixZero r t)).symm h ∈ KO k r ↔ h ∈ KO k (Ix r t 0) := by
      rw [← reGL_mem_KO_iff (ixZero r t), MulEquiv.apply_symm_apply]
    have mem : h ∈ ((TypeDatum.principal k r).reindex (ixZero r t)).J ↔
      (reGL (ixZero r t)).symm h ∈ KOne k r := Iff.rfl
    rw [mem, GlobalTheory.StepData.mem_KOne]
    constructor
    · intro hh
      refine ⟨hK.1 (GlobalTheory.StepData.KOne_le_KO (GlobalTheory.StepData.mem_KOne.2 hh)), fun a b hab => ?_, fun a b => ?_⟩
      · rcases a with a | ⟨c, _⟩
        · simp [Ix.blk] at hab
        · exact c.elim0
      · have := hh a b
        rwa [symm_sub_one_apply] at this
    · rintro ⟨-, -, h3⟩ a b
      rw [symm_sub_one_apply]
      exact h3 a b
  | succ j ih =>
    rw [TypeDatum.iter_succ]
    have hK : (reGL (ixSucc r t j)).symm h ∈ KO k (Ix r t j ⊕ t) ↔ h ∈ KO k (Ix r t (j + 1)) := by
      rw [← reGL_mem_KO_iff (ixSucc r t j), MulEquiv.apply_symm_apply]
    have mem : h ∈ ((((TypeDatum.principal k r).iter t μ hμ j).step t (μ (j + 1)) (hμ _)).reindex (ixSucc r t j)).J ↔
      (reGL (ixSucc r t j)).symm h ∈ ((TypeDatum.principal k r).iter t μ hμ j).stepJ t := Iff.rfl
    have ent : ∀ x y, ((reGL (ixSucc r t j)).symm h).val x y = h.val (ixSucc r t j x) (ixSucc r t j y) := fun _ _ => rfl
    rw [mem, TypeDatum.mem_stepJ_iff]
    constructor
    · rintro ⟨h0, ⟨g, hg, eg⟩, hC⟩
      obtain ⟨-, g2, g3⟩ := (ih g).1 hg
      have eg' : ∀ x y, g.val x y = h.val (ixSucc r t j (Sum.inl x)) (ixSucc r t j (Sum.inl y)) := fun x y => by
        rw [eg]; rfl
      refine ⟨hK.1 h0, fun a b hab => ?_, fun a b => ?_⟩
      · obtain ⟨x, rfl⟩ := (ixSucc r t j).surjective a
        obtain ⟨y, rfl⟩ := (ixSucc r t j).surjective b
        rcases x with x | s <;> rcases y with y | s'
        · rw [blk_ixSucc_inl, blk_ixSucc_inl] at hab
          rw [← eg']
          exact g2 x y hab
        · rw [blk_ixSucc_inl, blk_ixSucc_inr] at hab
          have := blk_le x
          omega
        · have := hC s y
          rwa [toBlocks₂₁, Matrix.of_apply, ent] at this
        · rw [blk_ixSucc_inr, blk_ixSucc_inr] at hab
          omega
      · have := g3 a b
        have e1 : ∀ c : r, (Sum.inl c : Ix r t (j + 1)) = ixSucc r t j (Sum.inl (Sum.inl c)) := fun c => rfl
        rw [e1 a, e1 b, ← symm_sub_one_apply, Matrix.sub_apply, ent]
        rw [Matrix.sub_apply, eg'] at this
        simpa [Matrix.one_apply] using this
    · rintro ⟨h1, h2, h3⟩
      have h0 := hK.2 h1
      have hC : GlobalTheory.StepData.MaxM ((reGL (ixSucc r t j)).symm h).val.toBlocks₂₁ := fun s y => by
        rw [toBlocks₂₁, Matrix.of_apply, ent]
        refine h2 _ _ ?_
        rw [blk_ixSucc_inl, blk_ixSucc_inr]
        have := blk_le y
        omega
      obtain ⟨⟨g, hg, eg⟩, -⟩ := GlobalTheory.StepData.exists_diag_blocks h0 hC
      have eg' : ∀ x y, g.val x y = h.val (ixSucc r t j (Sum.inl x)) (ixSucc r t j (Sum.inl y)) := fun x y => by
        rw [eg]; rfl
      refine ⟨h0, ⟨g, (ih g).2 ⟨hg, fun a b hab => ?_, fun a b => ?_⟩, eg⟩, hC⟩
      · rw [eg']
        refine h2 _ _ ?_
        rwa [blk_ixSucc_inl, blk_ixSucc_inl]
      · have := h3 a b
        have e1 : ∀ c : r, (Sum.inl c : Ix r t (j + 1)) = ixSucc r t j (Sum.inl (Sum.inl c)) := fun c => rfl
        rw [e1 a, e1 b, ← symm_sub_one_apply, Matrix.sub_apply, ent] at this
        rw [Matrix.sub_apply, eg']
        simpa [Matrix.one_apply] using this

end Iter

theorem blkOf_ixFin {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) (j : ℕ)
    (x : Ix (Fin D.R.r) (Fin D.R.t) j) :
    Formalism.L2.DIV.blkOf D.R.r D.R.t (ixFin G t w j x) = Ix.blk x := by
  obtain ⟨h1, h2⟩ := ixFin_val G t w j
  rcases x with a | ⟨c, b⟩
  · simp [Formalism.L2.DIV.blkOf, h1, Ix.blk]
  · have hb := b.2
    have hpos : 0 < D.R.t := by omega
    have hdiv : (b.val + D.R.t * c.val) / D.R.t = c.val := by
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hb, zero_add]
    simp [Formalism.L2.DIV.blkOf, h2, Ix.blk, hdiv]

theorem mem_stepGroup_map_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∈ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (∀ a b, Formalism.L2.DIV.blkOf D.R.r D.R.t b < Formalism.L2.DIV.blkOf D.R.r D.R.t a → valuation (Kw w) (g.1 a b) < 1) ∧ ∀ a b : Fin ((locGrid G t w).rank (0, j)), a.val < D.R.r → b.val < D.R.r → valuation (Kw w) ((g.1 - 1) a b) < 1 := by
  intro D T L sc G t w hw j g
  have hmap : g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔
      (reGL (ixFin G t w j)).symm g ∈ stepGroup L t w j := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hx
      exact ⟨_, hx, by simp⟩
  have hK : (reGL (ixFin G t w j)).symm g ∈ KO (Kw w) (Ix (Fin D.R.r) (Fin D.R.t) j) ↔
      g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) := by
    rw [← reGL_mem_KO_iff (ixFin G t w j), MulEquiv.apply_symm_apply]
  rw [hmap, stepGroup, if_pos hw, mem_iter_J, hK]
  refine and_congr_right fun _ => and_congr ?_ ?_
  · constructor
    · intro h a b hab
      obtain ⟨x, rfl⟩ := (ixFin G t w j).surjective a
      obtain ⟨y, rfl⟩ := (ixFin G t w j).surjective b
      rw [blkOf_ixFin, blkOf_ixFin] at hab
      exact h x y hab
    · intro h x y hxy
      refine h _ _ ?_
      rwa [blkOf_ixFin, blkOf_ixFin]
  · obtain ⟨h1, -⟩ := ixFin_val G t w j
    constructor
    · intro h a b ha hb
      have e : ∀ (c : Fin ((locGrid G t w).rank (0, j))) (hc : c.val < D.R.r),
          ixFin G t w j (Sum.inl ⟨c.val, hc⟩) = c := fun c hc => Fin.ext (h1 _)
      have := h ⟨a.val, ha⟩ ⟨b.val, hb⟩
      rwa [symm_sub_one_apply, e, e] at this
    · intro h a b
      rw [symm_sub_one_apply]
      exact h _ _ (by rw [h1]; exact a.2) (by rw [h1]; exact b.2)

end GlobalTheory.CompanionTheory.IterJ

end
end

end IteratedIwahori
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.Adopt.thetaGridBlockCongruence_typePrime_description : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∈ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (∀ a b, Formalism.L2.DIV.blkOf D.R.r D.R.t b < Formalism.L2.DIV.blkOf D.R.r D.R.t a → valuation (Kw w) (g.1 a b) < 1) ∧ ∀ a b : Fin ((locGrid G t w).rank (0, j)), a.val < D.R.r → b.val < D.R.r → valuation (Kw w) ((g.1 - 1) a b) < 1 := by
  first | exact @IteratedIwahori.GlobalTheory.CompanionTheory.IterJ.mem_stepGroup_map_iff | exact IteratedIwahori.GlobalTheory.CompanionTheory.IterJ.mem_stepGroup_map_iff | (intros; apply IteratedIwahori.GlobalTheory.CompanionTheory.IterJ.mem_stepGroup_map_iff <;> assumption)

end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridBlockCongruenceTypePrimeDescriptionStatement
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGridBlockCongruence_typePrime_description : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∈ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (∀ a b, Formalism.L2.DIV.blkOf D.R.r D.R.t b < Formalism.L2.DIV.blkOf D.R.r D.R.t a → valuation (Kw w) (g.1 a b) < 1) ∧ ∀ a b : Fin ((locGrid G t w).rank (0, j)), a.val < D.R.r → b.val < D.R.r → valuation (Kw w) ((g.1 - 1) a b) < 1 := by
  first | exact @GlobalTheory.Adopt.thetaGridBlockCongruence_typePrime_description | exact GlobalTheory.Adopt.thetaGridBlockCongruence_typePrime_description | (intros; apply GlobalTheory.Adopt.thetaGridBlockCongruence_typePrime_description <;> assumption)
end
end
end
