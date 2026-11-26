module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.CovolUnique
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.TupSplit
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitAtCOneIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.HOfMain
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasTop

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCovolumeFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCovolumeFormula
noncomputable section

open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermSd
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HermCov

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def ratVec {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) [FiniteDimensional F E]
    (A : Matrix (Fin n) (Fin n) E) : Idx n d → F :=
  Sum.elim (fun a => 1 / 2 * Algebra.trace F E (A a a)) fun q => b.repr (A q.1.1.1 q.1.1.2) q.2

def ofVec (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (k : Idx n d → F) :
    Matrix (Fin n) (Fin n) E := fun a c =>
  if h : a < c then ∑ l, k (Sum.inr (⟨(a, c), h⟩, l)) • b l
  else if h' : c < a then σ (∑ l, k (Sum.inr (⟨(c, a), h'⟩, l)) • b l)
  else algebraMap F E (k (Sum.inl a))

theorem ofVec_herm {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (n : ℕ) (k : Idx n d → F) (a c : Fin n) : σ (ofVec σ b n k c a) = ofVec σ b n k a c := by
  rcases lt_trichotomy a c with h | h | h
  · simp only [ofVec, dif_pos h, dif_neg (not_lt_of_gt h), hinv]
  · subst h
    simp only [ofVec, lt_irrefl, dite_false, AlgHom.commutes]
  · simp only [ofVec, dif_pos h, dif_neg (not_lt_of_gt h)]

theorem ratVec_ofVec [FiniteDimensional F E] [CharZero F] (h2 : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (k : Idx n d → F) :
    ratVec b n (ofVec σ b n k) = k := by
  funext i
  cases i with
  | inl a =>
    simp only [ratVec, Sum.elim_inl, ofVec, lt_irrefl, dite_false, Algebra.trace_algebraMap, h2]
    simp
  | inr q =>
    obtain ⟨p, l⟩ := q
    simp only [ratVec, Sum.elim_inr, ofVec, dif_pos p.2]
    rw [b.repr_sum_self]

variable (R : Type) [CommRing R] [Algebra F R]

theorem repr_inclR {d : ℕ} (b : Module.Basis (Fin d) F E) (x : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (inclR R x) k = algebraMap F R (b.repr x k) := by
  change (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] x) k = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

variable [TopologicalSpace R]

theorem hermVec_map [FiniteDimensional F E] (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) E) (S : HermR R σ n)
    (hS : (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = A.map (inclR R)) (i : Idx n d) :
    hermVec R σ b n S i = algebraMap F R (ratVec b n A i) := by
  cases i with
  | inl a =>
    simp only [hermVec, toVec, HaarCoord.hermCoord, Sum.elim_inl, ratVec, hS, Matrix.map_apply]
    change _ * Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] A a a) = _
    rw [trace_tmul, one_mul, map_mul]
  | inr q =>
    simp only [hermVec, toVec, HaarCoord.hermCoord, Sum.elim_inr, ratVec, hS, Matrix.map_apply]
    exact repr_inclR R b _ _

end Alg

section Main

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth PositivityTheory.SiegelWeilFormula.KWhit.MeasP
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_ratHerm_iff {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) (h2 : Module.finrank F E = 2)
    [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (hinj : Function.Injective (hermVec (AF F) σ b n)) (S : HermR (AF F) σ n) :
    S ∈ ratHerm F E σ n ↔ ∃ k : Idx n d → F, ∀ i, hermVec (AF F) σ b n S i = algebraMap F (AF F) (k i) := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨ratVec b n A, hermVec_map (AF F) σ b n A S hA.symm⟩
  · rintro ⟨k, hk⟩
    have hmem : (ofVec σ b n k).map (inclR (AF F)) ∈ HermR (AF F) σ n := by
      intro a c
      simp only [Matrix.map_apply]
      rw [← ofVec_herm hinv b n k a c]
      change sigR (AF F) σ ((1 : AF F) ⊗ₜ[F] _) = (1 : AF F) ⊗ₜ[F] _
      rw [HaarCoord.sigR_tmul]
    have hT : (⟨_, hmem⟩ : HermR (AF F) σ n) = S := by
      apply hinj
      funext i
      rw [hermVec_map (AF F) σ b n (ofVec σ b n k) _ rfl i, ratVec_ofVec h2, hk]
    refine ⟨ofVec σ b n k, ?_⟩
    rw [← hT]
    rfl

theorem existsUnique_sub_mem_pi {ι : Type} (x : ι → AF F) :
    ∃! k : ι → F, (fun i => x i - algebraMap F (AF F) (k i)) ∈
      Set.univ.pi fun _ : ι => fundamentalSet F := by
  choose k hk huniq using fun i => existsUnique_sub_mem_fundamentalSet F (x i)
  refine ⟨k, fun i _ => hk i, fun k' hk' => funext fun i => huniq i _ (hk' i (Set.mem_univ i))⟩

theorem hermCovol : HermCovol := by
  intro F E _ _ _ _ _ σ hCM ψ hψ n ν hν
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts hCM
  have h2 := hCM.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; omega)
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
  let e := (hermVec_isHomeomorph hCM (AF F) b n).homeomorph _
  have he : ∀ S, e S = hermVec (AF F) σ b n S := fun _ => rfl
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hψ.2.2.2
    apply hx
    rw [hξ x, map_zero, zero_mul, AddChar.map_zero_eq_one]
    simp
  have hs : (ξ • formB σ b n).IsSymm := (formB_isSymm hinv b n).smul ξ
  have hdet : (ξ • formB σ b n).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hξ0) (formB_det hinv b n)
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (HermR (AF F) σ n) := inferInstance
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  have hsd : ν.map e = adeleMeasurePi F := by
    refine GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth.selfDual_eq _ hs hdet _
      (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth.selfDual_transport e ?_ _ _ ?_ ν hν)
    · intro x y
      exact hermVec_add (AF F) b n x y
    · intro S T
      have h3 : (ξ • formB σ b n).map (algebraMap F (AF F)) =
          algebraMap F (AF F) ξ • (formB σ b n).map (algebraMap F (AF F)) := by
        ext p q
        exact map_mul (algebraMap F (AF F)) ξ (formB σ b n p q)
      rw [hξ, pair_eq (AF F) hinv h2 hδ hσδ b n S T, chiG, h3, Matrix.smul_mulVec, dotProduct_smul,
        smul_eq_mul]
      rfl
  set D : Set (Idx n 2 → AF F) := Set.univ.pi fun _ => fundamentalSet F with hD
  have hDm : MeasurableSet D := MeasurableSet.univ_pi fun _ => measurableSet_fundamentalSet F
  have hinj : Function.Injective (hermVec (AF F) σ b n) := e.injective
  refine ⟨e ⁻¹' D, IsAddFundamentalDomain.mk' (hDm.preimage e.measurable).nullMeasurableSet ?_, ?_⟩
  · intro S
    obtain ⟨k, hk, huniq⟩ := existsUnique_sub_mem_pi (e S)
    have hg : e.symm (fun i => algebraMap F (AF F) (-k i)) ∈ ratHerm F E σ n :=
      (mem_ratHerm_iff hinv h2 b n hinj _).2 ⟨fun i => -k i, fun i => by
        rw [← he, e.apply_symm_apply]⟩
    refine ⟨⟨_, hg⟩, ?_, ?_⟩
    · change e (e.symm _ + S) ∈ D
      rw [he, hermVec_add, ← he, ← he, e.apply_symm_apply]
      convert hk using 2 with i
      simp [sub_eq_add_neg, add_comm]
    · rintro ⟨g, hgm⟩ hg'
      obtain ⟨k', hk'⟩ := (mem_ratHerm_iff hinv h2 b n hinj _).1 hgm
      change e (g + S) ∈ D at hg'
      rw [he, hermVec_add, ← he] at hg'
      have hkk : (fun i => -k' i) = k := huniq _ (by
        convert hg' using 2 with i
        simp [he, hk', sub_eq_add_neg, add_comm])
      refine Subtype.ext (e.injective ?_)
      rw [e.apply_symm_apply]
      funext i
      rw [he, hk', ← hkk]
      simp
  · rw [← Measure.map_apply e.measurable hDm, hsd, adeleMeasurePi, hD, Measure.pi_pi]
    simp [adeleMeasure_fundamentalSet]

end Main

end GlobalTheory.CompanionTheory.SW.HermCov
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCovolumeFormulaStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_covolume_formula : PositivityTheory.SiegelWeilFormula.KWhit.MeasP.HermCovol := by
  first | exact @GlobalTheory.CompanionTheory.SW.HermCov.hermCovol | exact GlobalTheory.CompanionTheory.SW.HermCov.hermCovol | (intros; apply GlobalTheory.CompanionTheory.SW.HermCov.hermCovol <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupleSpaceCovolumeFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupleSpaceCovolumeFormula
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.TupCovolume

open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SiegelND.DxN PositivityTheory.SiegelWeilFormula.KWhit.MeasP
open scoped TensorProduct

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def ratCoord {d M n : ℕ} (b : Module.Basis (Fin d) F E) (Y : Fin n → Fin M → E) : Fin n × (Fin M × Fin d) → F :=
  fun p => b.repr (Y p.1 p.2.1) p.2.2

def ofCoord {d M n : ℕ} (b : Module.Basis (Fin d) F E) (c : Fin n × (Fin M × Fin d) → F) : Fin n → Fin M → E :=
  fun a i => ∑ l, c (a, (i, l)) • b l

theorem ratCoord_ofCoord {d M n : ℕ} (b : Module.Basis (Fin d) F E) (c : Fin n × (Fin M × Fin d) → F) :
    ratCoord b (ofCoord b c) = c := by
  funext p
  obtain ⟨a, i, l⟩ := p
  simp [ratCoord, ofCoord, Finsupp.single_apply]

theorem ratCoord_injective {d M n : ℕ} (b : Module.Basis (Fin d) F E) :
    Function.Injective (ratCoord (M := M) (n := n) b) := by
  intro Y Y' h
  funext a i
  refine b.repr.injective (Finsupp.ext fun l => ?_)
  exact congrFun h (a, (i, l))

theorem cvN_incl_add (R : Type) [CommRing R] [Algebra F R] {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (Y : Fin n → Fin M → E) (X : Fin n → Fin M → R ⊗[F] E) (p : Fin n × (Fin M × Fin d)) :
    cvN R b ((fun a i => inclR R (Y a i)) + X) p = algebraMap F R (ratCoord b Y p) + cvN R b X p := by
  simp [cvN, GlobalTheory.CompanionTheory.SW.BB.cv, ratCoord, inclR, Algebra.TensorProduct.basis_repr_tmul,
    Algebra.algebraMap_eq_smul_one]

end Coord

section Main

open GroundTheory.Global

attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing

theorem tupCovol : TupCovol := by
  intro F E _ _ _ _ _ σ hCM M J hJ ψ hψ n μ hμ
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let b := Module.finBasis F E
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hψ.2.2.2
    apply hx
    rw [hξ x]
    simp
  obtain ⟨e, he, hB⟩ := exists_coordHomeoN σ hCM n M b
  have hdxc := dx_coordN σ hCM J hJ b ψ ξ hξ0 hξ μ hμ e he hB
  have := hB
  have : BorelSpace (AF F) := GroundTheory.Global.borelSpace_adeleRing F
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hD : MeasurableSet (Set.univ.pi fun _ : Fin n × (Fin M × Fin (Module.finrank F E)) => fundamentalSet F) :=
    MeasurableSet.univ_pi fun _ => measurableSet_fundamentalSet F
  have hem : Measurable e := e.continuous.measurable
  have hmem : ∀ (Y : Fin n → Fin M → E) X,
      e ((fun a i => inclR (AF F) (Y a i)) + X) ∈
          (Set.univ.pi fun _ : Fin n × (Fin M × Fin (Module.finrank F E)) => fundamentalSet F) ↔
        ∀ p, algebraMap F (AF F) (ratCoord b Y p) + e X p ∈ fundamentalSet F := by
    intro Y X
    simp only [Set.mem_univ_pi, he, cvN_incl_add]
  refine ⟨e ⁻¹' (Set.univ.pi fun _ => fundamentalSet F), IsAddFundamentalDomain.mk' (hem hD).nullMeasurableSet fun X => ?_, ?_⟩
  · choose k hk huniq using fun p => existsUnique_sub_mem_fundamentalSet F (e X p)
    refine ⟨⟨_, ofCoord b (-k), rfl⟩, ?_, ?_⟩
    · refine (hmem _ X).2 fun p => ?_
      rw [ratCoord_ofCoord]
      have := hk p
      rwa [Pi.neg_apply, map_neg, neg_add_eq_sub]
    · rintro ⟨_, Y, rfl⟩ h
      have h' := (hmem Y X).1 h
      have hY : ratCoord b Y = -k := by
        funext p
        have e1 := huniq p (-(ratCoord b Y p)) (by
          change e X p - algebraMap F (AF F) (-(ratCoord b Y p)) ∈ fundamentalSet F
          rw [map_neg, sub_neg_eq_add, add_comm]; exact h' p)
        rw [Pi.neg_apply, ← e1, neg_neg]
      have : Y = ofCoord b (-k) := ratCoord_injective b (by rw [hY, ratCoord_ofCoord])
      subst this
      rfl
  · rw [← Measure.map_apply hem hD, hdxc, GroundTheory.Automorphic.GJMatrix.adeleMeasurePi, Measure.pi_pi]
    simp [adeleMeasure_fundamentalSet]

end Main

end GlobalTheory.CompanionTheory.SiegelND.TupCovolume

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupleSpaceCovolumeFormulaStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuple_space_covolume_formula : PositivityTheory.SiegelWeilFormula.KWhit.MeasP.TupCovol := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.TupCovolume.tupCovol | exact GlobalTheory.CompanionTheory.SiegelND.TupCovolume.tupCovol | (intros; apply GlobalTheory.CompanionTheory.SiegelND.TupCovolume.tupCovol <;> assumption)
end
end

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem meas_herm_top (d : SD σ) : IsTopologicalAddGroup (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧
    LocallyCompactSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧ SecondCountableTopology (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧
    BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧ Countable (MeasP.ratHerm F E σ d.n) := meas_herm_top' d

theorem meas_mx_top (d : SD σ) : IsTopologicalAddGroup (Mx F E d.m d.n) ∧ LocallyCompactSpace (Mx F E d.m d.n) ∧
    SecondCountableTopology (Mx F E d.m d.n) ∧ BorelSpace (Mx F E d.m d.n) ∧ Countable d.ratM := meas_mx_top' d

theorem meas_cm (d : SD σ) : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ := d.ok.good.cm

theorem meas_char (d : SD σ) : HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F d.B.ψ := GlobalTheory.StdCharFromIsStd.isCharAF d.ok.good.std

theorem meas_hermND (d : SD σ) {η : E} (hη : η ≠ 0) (hh : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (Jd d η) := meas_hermND' d hη hh

theorem meas_hOf {d : SD σ} {R : RD d} {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hR : Rel d R x t u T η T₀ hOf θ fr g)
    {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) :
    MeasurableEmbedding hOf ∧ (lam.map hOf).IsAddHaarMeasure ∧
      IsAddFundamentalDomain (MeasP.ratHerm F E σ d.n) (hOf '' 𝓖) (lam.map hOf) ∧ lam.map hOf (hOf '' 𝓖) = 1 :=
  PositivityTheory.SiegelWeilFormula.MeasD.meas_hOf hR hc

theorem meas_toMx (d : SD σ) (μ : Measure (Fin d.n → Fin d.m → AF F ⊗[F] E)) (𝓕 : Set (Fin d.n → Fin d.m → AF F ⊗[F] E))
    (hμ : μ.IsAddHaarMeasure) (hF : IsAddFundamentalDomain (MeasP.ratTupA F E d.n d.m) 𝓕 μ) (h1 : μ 𝓕 = 1) :
    MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) ∧ (μ.map toMx).IsAddHaarMeasure ∧
      IsAddFundamentalDomain d.ratM (toMx '' 𝓕) (μ.map toMx) ∧ μ.map toMx (toMx '' 𝓕) = 1 :=
  PositivityTheory.SiegelWeilFormula.MeasD.meas_toMx d μ 𝓕 hμ hF h1

theorem measDict_of (hH : MeasP.HermCovol) (hT : MeasP.TupCovol) : MeasDict := by
  intro F E _ _ _ _ _ σ d R x t u T η T₀ hOf θ fr g hR
  constructor
  · intro nb lam 𝓖 hc ν hν
    obtain ⟨i1, i2, i3, i4, i5⟩ := meas_herm_top d
    haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5
    obtain ⟨hemb, hH', hfd, h1⟩ := meas_hOf hR hc
    haveI := hH'
    obtain ⟨𝓕, hF, hF1⟩ := hH F E σ (meas_cm d) d.B.ψ (meas_char d) d.n ν hν
    haveI := hν.1
    exact ⟨hemb, hemb.measurable, @MeasG.covol_unique _ _ _ _ _ _ _ _ (MeasP.ratHerm F E σ d.n) _ _ _ hν.1 hH' _ _ hF hfd hF1 h1⟩
  · intro μ νc hμ hνc
    obtain ⟨i1, i2, i3, i4, i5⟩ := meas_mx_top d
    haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5
    obtain ⟨𝓕, hF, hF1⟩ := hT F E σ (meas_cm d) d.m (Jd d η) (meas_hermND d hR.ne hR.herm) d.B.ψ (meas_char d) d.n μ hμ
    obtain ⟨hemb, hH', hfd, h1⟩ := meas_toMx d μ 𝓕 hμ.1 hF hF1
    obtain ⟨hνH, 𝓖, hG, hG1⟩ := hνc
    haveI := hνH; haveI := hH'
    exact ⟨hemb, hemb.measurable, @MeasG.covol_unique _ _ _ _ _ _ _ _ d.ratM _ _ _ hνH hH' _ _ hG hfd hG1 h1⟩

theorem measDict : MeasDict := measDict_of GlobalTheory.T.hermitian_covolume_formula GlobalTheory.T.tuple_space_covolume_formula

end PositivityTheory.SiegelWeilFormula.KWhit

end
