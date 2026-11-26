module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalGramAdelicCompactFinite

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionRationalToAdelic
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicOrbitOfRationalTuple
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicOrbitOfRationalTuple
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TransUC

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem cT_map_inclR (σ : E →ₐ[F] E) {n : ℕ} (g : Matrix (Fin n) (Fin n) E) :
    cT (sigR R σ) (g.map (inclR R)) = (cT (σ : E →+* E) g).map (inclR R) := by
  ext a b
  simp [cT, sigR_inclR]

theorem gramR_ratTup (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) : gramR R σ J (ratTup R X) = (gramE σ J X).map (inclR R) := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp [gramR, hR, hform, gramE, hE, ratTup, JR, map_sum, map_mul, sigR_inclR]

theorem gramE_herm (σ : E →ₐ[F] E) (hσ : ∀ x : E, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → E) (a b : Fin n) :
    σ (gramE σ J X b a) = gramE σ J X a b := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramE, hE, hform, map_sum, map_mul, RingHom.coe_coe, AlgHom.commutes]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hσ, hJ]
  ring

theorem inclR_algebraMap (d : F) :
    inclR (E := E) R (algebraMap F E d) = algebraMap R (R ⊗[F] E) (algebraMap F R d) := by
  change (1 : R) ⊗ₜ[F] (algebraMap F E d) = (algebraMap F R d) ⊗ₜ[F] (1 : E)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

end SlopeTestRemainingChoices

theorem trans_uc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R],
    PIW.AdelicOrbitU.UnitChoice R → ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (X : Fin n → Fin M → E) (Y : Fin n → Fin M → R ⊗[F] E), (gramE σ J X).det ≠ 0 →
    gramR R σ J Y = (gramE σ J X).map (inclR R) →
    ∃ h : HA R σ J, actW R σ J h (ratTup R X) = Y := by
  intro F E _ _ _ _ _ σ hCM R _ _ uc n M J hJ X Y hdet hY
  have hσ : ∀ x : E, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]
  have hT : IsHermND σ (gramE σ J X) := ⟨gramE_herm σ hσ J hJ.1 X, hdet⟩
  obtain ⟨g, D, hg⟩ := GlobalTheory.CompanionTheory.SW.AlgDiag.diag_hermitian F E σ hCM n _ hT
  set G : Matrix (Fin n) (Fin n) (R ⊗[F] E) := (g : Matrix (Fin n) (Fin n) E).map (inclR R) with hG
  set G' : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
    ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (inclR R) with hG'
  have hGG' : G * G' = 1 := by
    have h1 : (g : Matrix (Fin n) (Fin n) E) * ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 :=
      Units.mul_inv g
    have h2 := congrArg (fun A : Matrix (Fin n) (Fin n) E => A.map (inclR (F := F) R)) h1
    simp only [Matrix.map_mul] at h2
    rw [hG, hG', h2, Matrix.map_one _ (map_zero _) (map_one _)]
  let D' : Fin n → Rˣ := fun i => Units.map (algebraMap F R).toMonoidHom (D i)
  have hdiag : cT (sigR R σ) G * (gramE σ J X).map (inclR R) * G =
      Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D' i : R)) := by
    rw [hG, cT_map_inclR, ← Matrix.map_mul, ← Matrix.map_mul, hg]
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [D', inclR_algebraMap]
    · simp [Matrix.diagonal_apply_ne _ hab, hab]
  have P := fun (Z : Fin n → Fin M → R ⊗[F] E) (H H' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =>
    GlobalTheory.T.gram_right_mul_action_laws F E σ hCM R M n J Z H H'
  have hX1 : gramR R σ J (rmul R (ratTup R X) G) =
      Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D' i : R)) := by
    rw [(P _ G G).1, gramR_ratTup, hdiag]
  have hY1 : gramR R σ J (rmul R Y G) = gramR R σ J (rmul R (ratTup R X) G) := by
    rw [hX1, (P _ G G).1, hY, hdiag]
  obtain ⟨h, hh⟩ := GlobalTheory.T.witt_extension_diagonal_gram_tuples F E σ hCM R uc M J hJ n D' _ _ hX1 hY1
  refine ⟨h, ?_⟩
  have undo : ∀ Z : Fin n → Fin M → R ⊗[F] E, rmul R (rmul R Z G) G' = Z := by
    intro Z
    rw [(P Z G G').2.1, hGG', (P Z G G').2.2.1]
  calc actW R σ J h (ratTup R X)
      = actTup R (HA.mat R σ J h) (rmul R (rmul R (ratTup R X) G) G') := by
        rw [undo]; rfl
    _ = rmul R (actTup R (HA.mat R σ J h) (rmul R (ratTup R X) G)) G' :=
        (P _ G' G').2.2.2 _
    _ = rmul R (rmul R Y G) G' := by
        rw [show actTup R (HA.mat R σ J h) (rmul R (ratTup R X) G) = rmul R Y G from hh]
    _ = Y := undo Y

end GlobalTheory.CompanionTheory.SW.TransUC
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicOrbitOfRationalTupleStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_orbit_of_rational_tuple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R], PIW.AdelicOrbitU.UnitChoice R → ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (X : Fin n → Fin M → E) (Y : Fin n → Fin M → R ⊗[F] E), (gramE σ J X).det ≠ 0 → gramR R σ J Y = (gramE σ J X).map (inclR R) → ∃ h : HA R σ J, actW R σ J h (ratTup R X) = Y := by
  first | exact @GlobalTheory.CompanionTheory.SW.TransUC.trans_uc | exact GlobalTheory.CompanionTheory.SW.TransUC.trans_uc | (intros; apply GlobalTheory.CompanionTheory.SW.TransUC.trans_uc <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionRationalToAdelic
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TransA

theorem trans_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (X : Fin n → Fin M → E) (Y : Fin n → Fin M → AF F ⊗[F] E), (gramE σ J X).det ≠ 0 →
    gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) →
    ∃ h : HA (AF F) σ J, actW (AF F) σ J h (ratTup (AF F) X) = Y :=
  fun F E _ _ _ _ _ σ hcm M J hJ n =>
    GlobalTheory.T.adelic_orbit_of_rational_tuple F E σ hcm (AF F) (PIW.AdelicOrbitU.stP F) n M J hJ

end GlobalTheory.CompanionTheory.SW.TransA
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionRationalToAdelicStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_extension_rational_to_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X : Fin n → Fin M → E) (Y : Fin n → Fin M → AF F ⊗[F] E), (gramE σ J X).det ≠ 0 → gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) → ∃ h : HA (AF F) σ J, actW (AF F) σ J h (ratTup (AF F) X) = Y := by
  first | exact @GlobalTheory.CompanionTheory.SW.TransA.trans_adelic | exact GlobalTheory.CompanionTheory.SW.TransA.trans_adelic | (intros; apply GlobalTheory.CompanionTheory.SW.TransA.trans_adelic <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompactPartClosedOrbit
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem compact_part_closed_orbit :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [SecondCountableTopology G] (V : Type) [TopologicalSpace V]
      [T2Space V] [LocallyCompactSpace V] (a : G → V → V),
      (Continuous fun p : G × V => a p.1 p.2) → (∀ y, a 1 y = y) →
      (∀ g h y, a (g * h) y = a g (a h y)) →
      ∀ (Z : Set V) (x : V), IsClosed Z → (∀ y, y ∈ Z ↔ ∃ g, a g x = y) →
      ∀ Ω : Set V, IsCompact Ω → ∃ C : Set G, IsCompact C ∧ ∀ y ∈ Ω, y ∈ Z → ∃ c ∈ C, a c x = y := by
  intro G _ _ _ _ _ _ V _ _ _ a ha h1 hmul Z x hZ hZx Ω hΩ
  have hmem : ∀ (g : G) (z : Z), a g z ∈ Z := by
    intro g z
    obtain ⟨h, hh⟩ := (hZx z).1 z.2
    exact (hZx _).2 ⟨g * h, by rw [hmul, hh]⟩
  letI : MulAction G Z :=
    { smul := fun g z => ⟨a g z, hmem g z⟩
      one_smul := fun z => Subtype.ext (h1 z)
      mul_smul := fun g h z => Subtype.ext (hmul g h z) }
  haveI : ContinuousSMul G Z :=
    ⟨Continuous.subtype_mk
      (ha.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
      (fun p => hmem p.1 p.2)⟩
  haveI : MulAction.IsPretransitive G Z := by
    refine ⟨fun z w => ?_⟩
    obtain ⟨g, hg⟩ := (hZx z).1 z.2
    obtain ⟨h, hh⟩ := (hZx w).1 w.2
    refine ⟨h * g⁻¹, Subtype.ext ?_⟩
    show a (h * g⁻¹) z = w
    rw [← hg, ← hmul, inv_mul_cancel_right, hh]
  haveI : LocallyCompactSpace Z := hZ.locallyCompactSpace
  haveI : BaireSpace Z := BaireSpace.of_t2Space_locallyCompactSpace
  have hx : x ∈ Z := (hZx x).2 ⟨1, h1 x⟩
  have hopen := isOpenMap_smul_of_sigmaCompact (G := G) (X := Z) ⟨x, hx⟩
  choose K hK hKn using fun g : G => exists_compact_mem_nhds g
  have hS : IsCompact ((Subtype.val : Z → V) ⁻¹' Ω) :=
    hZ.isClosedEmbedding_subtypeVal.isCompact_preimage hΩ
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun g => (fun h : G => h • (⟨x, hx⟩ : Z)) '' interior (K g))
    (fun g => hopen _ isOpen_interior) (by
      intro z _
      obtain ⟨g, hg⟩ := (hZx z).1 z.2
      exact Set.mem_iUnion.2 ⟨g, g, mem_interior_iff_mem_nhds.2 (hKn g), Subtype.ext hg⟩)
  refine ⟨⋃ g ∈ t, K g, t.isCompact_biUnion fun g _ => hK g, ?_⟩
  intro y hyΩ hyZ
  have hy := ht (show (⟨y, hyZ⟩ : Z) ∈ (Subtype.val : Z → V) ⁻¹' Ω from hyΩ)
  rw [Set.mem_iUnion₂] at hy
  obtain ⟨g, hgt, c, hc, hcy⟩ := hy
  exact ⟨c, Set.mem_biUnion hgt (interior_subset hc), congrArg Subtype.val hcy⟩

end GlobalTheory.CompanionTheory.Adelic
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramOrbitCompactRepresentative
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Proper

theorem compact_gram_fibre :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      ∀ (n : ℕ) (X : Fin n → Fin M → E), (gramE σ J X).det ≠ 0 →
      ∀ Ω : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact Ω →
      ∃ C : Set (HA (AF F) σ J), IsCompact C ∧
        ∀ Y ∈ Ω, gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) →
          ∃ c ∈ C, actW (AF F) σ J c (ratTup (AF F) X) = Y := by
  intro F E _ _ _ _ _ σ hσ M J hJ n X hX Ω hΩ
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hlc
  haveI := hsc
  haveI := ht2
  obtain ⟨htg, hlcH, hscH, ht2H, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  haveI := htg
  haveI := hlcH
  haveI := hscH
  haveI := ht2H
  obtain ⟨-, hlcK, -, ht2K, -, -, -, -, -, hgram⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)
  haveI := hlcK
  haveI := ht2K
  obtain ⟨hcont, h1, hmul, hinv⟩ := hact n
  obtain ⟨-, hrat, -⟩ := GlobalTheory.T.rational_gram_adelic_compact_finite F E σ hσ M J hJ
  have hZ : IsClosed {Y : Fin n → Fin M → AF F ⊗[F] E |
      gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F))} :=
    isClosed_eq (hgram n M J) continuous_const
  have hZx : ∀ Y : Fin n → Fin M → AF F ⊗[F] E,
      Y ∈ {Y : Fin n → Fin M → AF F ⊗[F] E |
        gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F))} ↔
      ∃ g : HA (AF F) σ J, actW (AF F) σ J g (ratTup (AF F) X) = Y := by
    intro Y
    constructor
    · intro hY
      exact GlobalTheory.T.witt_extension_rational_to_adelic F E σ hσ M J hJ n X Y hX hY
    · rintro ⟨g, rfl⟩
      show gramR (AF F) σ J _ = _
      rw [hinv, hrat]
  obtain ⟨C, hC, hCY⟩ := GlobalTheory.CompanionTheory.Adelic.compact_part_closed_orbit (HA (AF F) σ J)
    (Fin n → Fin M → AF F ⊗[F] E) (fun g Y => actW (AF F) σ J g Y) hcont h1 hmul _
    (ratTup (AF F) X) hZ hZx Ω hΩ
  exact ⟨C, hC, fun Y hY hg => hCY Y hY hg⟩

end GlobalTheory.CompanionTheory.SW.Proper
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramOrbitCompactRepresentativeStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_orbit_compact_representative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X : Fin n → Fin M → E), (gramE σ J X).det ≠ 0 → ∀ Ω : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact Ω → ∃ C : Set (HA (AF F) σ J), IsCompact C ∧ ∀ Y ∈ Ω, gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) → ∃ c ∈ C, actW (AF F) σ J c (ratTup (AF F) X) = Y := by
  first | exact @GlobalTheory.CompanionTheory.SW.Proper.compact_gram_fibre | exact GlobalTheory.CompanionTheory.SW.Proper.compact_gram_fibre | (intros; apply GlobalTheory.CompanionTheory.SW.Proper.compact_gram_fibre <;> assumption)
end
