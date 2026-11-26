module

public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTorusElementProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataBothAmplitudeSides
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianMassFormula
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentCoordinates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFacts
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem record_facts : ∀ (D : D7) (u : D.what₂.Word), SplitsIn D.host.E (D.mem u).A.T ∧ (∀ i, SplitsIn D.host.E (D.host.g i)) ∧ (∀ i, (D.mem u).A.T ≠ D.host.g i) ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ D.R.N 0 = D.R.k ∧ IsHerm (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ∧ (gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  intro D u
  refine ⟨(GlobalTheory.HostSplit.split_of_one_mod D.R D.host _ (D.mem u).A.T_prime (D.T_mod_cond u)).1,
    D.nd.g_split, D.T_ne_g u, ?_, D.R.N_zero, ?_,
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D 0 (Nat.zero_le _)).ne_zero⟩
  · rw [D.host.finrank_cmField, Ranks.f, Ranks.n]
    ring
  · let _ := D.host.cmStar
    have h := D.sp.baseGram_isHermitian
    refine Matrix.ext fun i j => ?_
    exact congrFun (congrFun h (Fin.cast D.R.N_zero i)) (Fin.cast D.R.N_zero j)

end GlobalTheory.St.G
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFactsStatement
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryDatum_levelPrime_split_degree_gram_facts : ∀ (D : D7) (u : D.what₂.Word), SplitsIn D.host.E (D.mem u).A.T ∧ (∀ i, SplitsIn D.host.E (D.host.g i)) ∧ (∀ i, (D.mem u).A.T ≠ D.host.g i) ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ D.R.N 0 = D.R.k ∧ IsHerm (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ∧ (gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  first | exact @GlobalTheory.St.G.record_facts | exact GlobalTheory.St.G.record_facts | (intros; apply GlobalTheory.St.G.record_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDatumEquivariantFlagIsometries
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDatumEquivariantFlagIsometries
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.DatumOf

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mem_smul_iff (g : S.GLV) (P : Submodule L.O S.V) (x : S.V) :
    x ∈ g • P ↔ ∃ b ∈ P, g b = x := by
  simp only [Submodule.mem_smul_pointwise_iff_exists, LinearEquiv.smul_def]

theorem inner_le_of_unip (Y : Submodule E S.V) (n : S.GLV) (hn : n ∈ unipOn (perp L S.Hm Y) Y)
    (Λ : Submodule L.O S.V) :
    ((n • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O ≤
      (Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O := by
  refine sup_le ?_ le_sup_right
  rintro z ⟨hz1, hz2⟩
  obtain ⟨y, hy, rfl⟩ := (mem_smul_iff S n Λ z).1 hz1
  have hyP : y ∈ perp L S.Hm Y := (hn.1 y).1 hz2
  have e : n y = y + (n y - y) := by abel
  rw [e]
  exact Submodule.add_mem_sup ⟨hy, hyP⟩ (hn.2 y hyP)

theorem inner_eq_of_unip (Y : Submodule E S.V) (n : S.GLV) (hn : n ∈ unipOn (perp L S.Hm Y) Y)
    (Λ : Submodule L.O S.V) :
    ((n • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O =
      (Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O := by
  refine le_antisymm (inner_le_of_unip S Y n hn Λ) ?_
  have h1 := inner_le_of_unip S Y n⁻¹ (inv_mem hn) (n • Λ)
  rwa [inv_smul_smul] at h1

theorem complementGroup_fixes_frameSpan {g : S.GLV} (hg : g ∈ S.H0) {x : S.V} (hx : x ∈ S.ME) : g x = x :=
  sub_eq_zero.1 ((Submodule.mem_bot E).1 (hg.2.2 x hx))

theorem X_le : S.X ≤ S.ME := by
  refine le_trans (Submodule.span_mono (Set.image_mono fun i hi => ?_)) le_sup_left
  simp only [Set.mem_setOf_eq] at hi ⊢
  omega

theorem X'_le : S.X' ≤ S.ME := by
  refine le_trans (Submodule.span_mono (Set.image_mono fun i hi => ?_)) le_sup_right
  simp only [Set.mem_setOf_eq] at hi ⊢
  omega

theorem hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer (Y : Submodule E S.V) (hY : Y ≤ S.ME) {g : S.GLV} (hg : g ∈ S.H0) {y : S.V}
    (hy : y ∈ perp L S.Hm Y) : g y ∈ perp L S.Hm Y := by
  intro w hw
  have e := hg.1 y w
  rw [complementGroup_fixes_frameSpan S hg (hY hw)] at e
  rw [e]
  exact hy w hw

theorem inTh_smul (g : S.GLV) (Λ : Submodule L.O S.V) {v : S.V} (hv : S.InTh Λ v) :
    S.InTh (g • Λ) (g v) := by
  obtain ⟨y, hy, rfl⟩ := hv
  exact ⟨g y, (mem_smul_iff S g Λ _).2 ⟨y, hy, rfl⟩, map_smul g _ y⟩

theorem smul_inner_lattice_le_of_mem_hermitianStabilizer (Y : Submodule E S.V) (hY : Y ≤ S.ME) {g : S.GLV} (hg : g ∈ S.H0)
    (Λ : Submodule L.O S.V) :
    g • ((Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O) ≤
      ((g • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O := by
  intro z hz
  obtain ⟨b, hb, rfl⟩ := (mem_smul_iff S g _ z).1 hz
  obtain ⟨y, ⟨hy1, hy2⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 hb
  rw [map_add (f := _), complementGroup_fixes_frameSpan S hg (hY hx)]
  exact Submodule.add_mem_sup ⟨(mem_smul_iff S g Λ _).2 ⟨y, hy1, rfl⟩, hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer S Y hY hg hy2⟩ hx

theorem smul_inner_lattice_eq_of_mem_hermitianStabilizer (Y : Submodule E S.V) (hY : Y ≤ S.ME) {g : S.GLV} (hg : g ∈ S.H0)
    (Λ : Submodule L.O S.V) :
    ((g • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O =
      g • ((Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O) := by
  refine le_antisymm ?_ (smul_inner_lattice_le_of_mem_hermitianStabilizer S Y hY hg Λ)
  have h1 := smul_inner_lattice_le_of_mem_hermitianStabilizer S Y hY (inv_mem hg) (g • Λ)
  rw [inv_smul_smul] at h1
  intro z hz
  have h2 := Submodule.smul_mem_pointwise_smul _ g _ (h1 (Submodule.smul_mem_pointwise_smul z g⁻¹ _ hz))
  rwa [smul_inv_smul] at h2

theorem smul_graphOf_subset_of_mem_hermitianStabilizer {g : S.GLV} (hg : g ∈ S.H0) (Λ : Submodule L.O S.V) :
    g • S.graphOf Λ ⊆ S.graphOf (g • Λ) := by
  rintro _ ⟨p, ⟨y', hy', y, hy, h1, h2, h3, h4, h5⟩, rfl⟩
  refine ⟨g y', (mem_smul_iff S g Λ _).2 ⟨y', hy', rfl⟩, g y, (mem_smul_iff S g Λ _).2 ⟨y, hy, rfl⟩,
    hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer S _ (X'_le S) hg h1, hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer S _ (X_le S) hg h2, ?_, ?_, ?_⟩
  · show g y' - g p.1 ∈ S.X'
    rw [← map_sub, complementGroup_fixes_frameSpan S hg (X'_le S h3)]
    exact h3
  · show g y - g p.2 ∈ S.X
    rw [← map_sub, complementGroup_fixes_frameSpan S hg (X_le S h4)]
    exact h4
  · rw [← map_sub]
    exact inTh_smul S g Λ h5

theorem graphOf_smul_eq_of_mem_hermitianStabilizer {g : S.GLV} (hg : g ∈ S.H0) (Λ : Submodule L.O S.V) :
    S.graphOf (g • Λ) = g • S.graphOf Λ := by
  refine subset_antisymm ?_ (smul_graphOf_subset_of_mem_hermitianStabilizer S hg Λ)
  intro p hp
  have h1 := smul_graphOf_subset_of_mem_hermitianStabilizer S (inv_mem hg) (g • Λ) ⟨p, hp, rfl⟩
  rw [inv_smul_smul] at h1
  exact ⟨g⁻¹ • p, h1, smul_inv_smul g p⟩

theorem datOf_smul_eq_of_mem_hermitianStabilizer {g : S.GLV} (hg : g ∈ S.H0) (Λ : Submodule L.O S.V) :
    S.datOf (g • Λ) = g • S.datOf Λ :=
  Prod.ext (smul_inner_lattice_eq_of_mem_hermitianStabilizer S S.X (X_le S) hg Λ)
    (Prod.ext (smul_inner_lattice_eq_of_mem_hermitianStabilizer S S.X' (X'_le S) hg Λ) (graphOf_smul_eq_of_mem_hermitianStabilizer S hg Λ))

theorem std_inner [IsNonarchimedeanLocalField F] [CharZero F] (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hgs : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (A : Submodule L.O S.V) (hA : S.IsInner g gs A) :
    (S.stdLat g gs A ⊓ (perp L S.Hm (S.spanTo g r)).restrictScalars L.O) ⊔
      (S.spanTo g r).restrictScalars L.O = A := by
  have h3 := (StdLat.stdLat_spec L r k S g gs hgs A hA).2.2
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro y ⟨hy1, hy2⟩
      exact (h3 y).2 ⟨y, hy1, hy2, by simp⟩
    · intro x hx
      exact hA.1 x hx
  · intro x hx
    obtain ⟨y, hy, hyp, hyx⟩ := (h3 x).1 hx
    have e : x = y - (y - x) := by abel
    rw [e]
    exact Submodule.sub_mem_sup ⟨hy, hyp⟩ hyx

theorem datOf_term [IsNonarchimedeanLocalField F] [CharZero F] {d : S.Datum} {Λ : Submodule L.O S.V}
    (h : S.IsTerm d Λ) : d = S.datOf Λ := by
  obtain ⟨⟨n, n'⟩, hA, hA', hn, hn', hΛ, hΛ', -, hg⟩ := h
  refine Prod.ext ?_ (Prod.ext ?_ hg)
  · show d.1 = (Λ ⊓ (perp L S.Hm S.X).restrictScalars L.O) ⊔ S.X.restrictScalars L.O
    rw [hΛ, inner_eq_of_unip S S.X n hn.2]
    exact (std_inner S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hA).symm
  · show d.2.1 = (Λ ⊓ (perp L S.Hm S.X').restrictScalars L.O) ⊔ S.X'.restrictScalars L.O
    rw [hΛ', inner_eq_of_unip S S.X' n' hn'.2]
    exact (std_inner S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hA').symm

theorem exists_unitri (g : Fin (r + 1) → S.V) (φ : S.GLV) (h : ∀ b : Fin (r + 1), φ (g b) - g b ∈ S.spanTo g b) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, φ (g j) = ∑ i, s i j • g i := by
  choose c hc0 hc using fun b : Fin (r + 1) => StdLat.exists_coef g {i | (i : ℕ) < b} (h b)
  refine ⟨fun i j => c j i + if i = j then 1 else 0, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · have hne : i ≠ j := (ne_of_lt hij).symm
    have h0 : c j i = 0 := hc0 j i fun hi => by
      have := Fin.lt_def.1 hij
      simp only [Set.mem_setOf_eq] at hi
      omega
    simp [h0, hne]
  · have h0 : c i i = 0 := hc0 i i fun hi => lt_irrefl (i : ℕ) hi
    simp [h0]
  · have e1 : ∑ i, (c j i + if i = j then (1 : E) else 0) • g i = ∑ i, c j i • g i + g j := by
      simp [add_smul, Finset.sum_add_distrib, ite_smul]
    rw [e1, ← hc j]
    abel

theorem mem_hermitianStabilizer_of_preserves_both_flags [IsNonarchimedeanLocalField F] [CharZero F] (φ : S.GLV) (hφ : φ ∈ isomG L S.Hm)
    (h1 : ∀ b : Fin (r + 1), φ (S.f b) - S.f b ∈ S.spanTo S.f b)
    (h2 : ∀ b : Fin (r + 1), φ (S.f' b) - S.f' b ∈ S.spanTo S.f' b) :
    ∃ s ∈ S.St, ∃ h ∈ S.H0, φ = s * h := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨s, hs, hsφ⟩ := exists_unitri S S.f φ h1
  obtain ⟨s', hs', hsφ'⟩ := exists_unitri S S.f' φ h2
  have hz : cT L s * S.Zh * s' = S.Zh := by
    ext a b
    rw [← FrameStab.pair_eq S s s' a b, ← hsφ, ← hsφ']
    exact hφ _ _
  obtain ⟨h, hh, hf, hf'⟩ := ((FrameStab.stab_eq L r k S).2 s s' hs hs').1 hz
  have k1 : ∀ (g : Fin (r + 1) → S.V) (m : ℕ), (∀ i, φ (g i) = h (g i)) → ∀ v ∈ S.spanTo g m, φ v = h v := by
    intro g m hg v hv
    have hle : S.spanTo g m ≤ LinearMap.eqLocus (φ : S.V →ₗ[E] S.V) (h : S.V →ₗ[E] S.V) := by
      rw [Frames.spanTo, Submodule.span_le]
      rintro _ ⟨i, -, rfl⟩
      exact hg i
    exact hle hv
  have hfix : ∀ v ∈ S.ME, φ v = h v := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _), map_add (f := _), k1 S.f _ (fun i => by rw [hsφ, hf]) a ha,
      k1 S.f' _ (fun i => by rw [hsφ', hf']) b hb]
  have hiso : h ∈ isomG L S.Hm := hh.1.1.1
  refine ⟨h, hh, h⁻¹ * φ, Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hiso) hφ, ?_⟩, (mul_inv_cancel_left h φ).symm⟩
  refine FrameStab.mem_unipOn' bot_le _ fun v hv => ?_
  show h.symm (φ v) - v ∈ (⊥ : Submodule E S.V)
  rw [hfix v hv, LinearEquiv.symm_apply_apply, sub_self]
  exact zero_mem _

end

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ d Λ, S.IsTerm d Λ → d = S.datOf Λ) ∧ (∀ h ∈ S.H0, ∀ Λ, S.datOf (h • Λ) = h • S.datOf Λ) ∧ (∀ n ∈ S.N, ∀ Λ, (S.datOf (n • Λ)).1 = (S.datOf Λ).1) ∧ (∀ n ∈ S.N', ∀ Λ, (S.datOf (n • Λ)).2.1 = (S.datOf Λ).2.1) ∧ ∀ φ ∈ isomG L S.Hm, (∀ b : Fin (r + 1), φ (S.f b) - S.f b ∈ S.spanTo S.f b) → (∀ b : Fin (r + 1), φ (S.f' b) - S.f' b ∈ S.spanTo S.f' b) → ∃ s ∈ S.St, ∃ h ∈ S.H0, φ = s * h := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  exact ⟨fun d Λ h => datOf_term S h, fun g hg Λ => datOf_smul_eq_of_mem_hermitianStabilizer S hg Λ,
    fun n hn Λ => inner_eq_of_unip S S.X n hn.2 Λ, fun n hn Λ => inner_eq_of_unip S S.X' n hn.2 Λ,
    fun φ hφ h1 h2 => mem_hermitianStabilizer_of_preserves_both_flags S φ hφ h1 h2⟩

end GlobalTheory.HL.DatumOf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDatumEquivariantFlagIsometriesStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_lattice_datum_equivariant_flag_isometries : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ d Λ, S.IsTerm d Λ → d = S.datOf Λ) ∧ (∀ h ∈ S.H0, ∀ Λ, S.datOf (h • Λ) = h • S.datOf Λ) ∧ (∀ n ∈ S.N, ∀ Λ, (S.datOf (n • Λ)).1 = (S.datOf Λ).1) ∧ (∀ n ∈ S.N', ∀ Λ, (S.datOf (n • Λ)).2.1 = (S.datOf Λ).2.1) ∧ ∀ φ ∈ isomG L S.Hm, (∀ b : Fin (r + 1), φ (S.f b) - S.f b ∈ S.spanTo S.f b) → (∀ b : Fin (r + 1), φ (S.f' b) - S.f' b ∈ S.spanTo S.f' b) → ∃ s ∈ S.St, ∃ h ∈ S.H0, φ = s * h := by
  first | exact @GlobalTheory.HL.DatumOf.main | exact GlobalTheory.HL.DatumOf.main | (intros; apply GlobalTheory.HL.DatumOf.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTuplesTopologicalFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTuplesTopologicalFacts
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalUnitaryTop

theorem linearIndependent_iff_smul_basis {K S V ι α : Type} [Field K] [CommRing S] [Algebra K S]
    [AddCommGroup V] [Module K V] [Module S V] [IsScalarTower K S V] [Fintype ι] [Fintype α]
    (b : Module.Basis ι K S) (X : α → V) :
    LinearIndependent S X ↔ LinearIndependent K fun p : ι × α => b p.1 • X p.2 := by
  refine ⟨fun h => linearIndependent_smul b.linearIndependent h, fun h => ?_⟩
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg i
  have h0 := h (fun p => b.repr (g p.2) p.1) (by
    rw [← hg, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => rw [← b.sum_repr (g j), Finset.sum_smul]
    exact Finset.sum_congr rfl fun k _ => (smul_assoc _ _ _).symm)
  exact b.ext_elem fun k => by simpa using h0 (k, i)

theorem isOpen_linearIndependent {K S ι α β : Type} [NontriviallyNormedField K] [CompleteSpace K]
    [CommRing S] [Algebra K S] [TopologicalSpace S] [IsModuleTopology K S] [IsTopologicalRing S]
    [Fintype ι] [Fintype α] [Fintype β] (b : Module.Basis ι K S) :
    IsOpen {X : α → β → S | LinearIndependent S X} := by
  let e : (β → S) ≃ₗ[K] (β → ι → K) := LinearEquiv.piCongrRight fun _ => b.equivFun
  have hb : Continuous b.equivFun :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  have hc : Continuous fun (X : α → β → S) (p : ι × α) => e (b p.1 • X p.2) := by
    refine continuous_pi fun p => continuous_pi fun j => ?_
    have : Continuous fun X : α → β → S => b p.1 * X p.2 j := by fun_prop
    exact hb.comp this
  have ho := (isOpen_setOfPred_linearIndependent (𝕜 := K) (E := β → ι → K) (ι := ι × α)).preimage hc
  convert ho using 1
  ext X
  rw [Set.mem_ofPred_eq, linearIndependent_iff_smul_basis b]
  exact (e.toLinearMap.linearIndependent_iff e.ker).symm

theorem top_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), IsTopologicalRing (Fv F v ⊗[F] E) ∧ LocallyCompactSpace (Fv F v ⊗[F] E) ∧ T2Space (Fv F v ⊗[F] E) ∧ SecondCountableTopology (Fv F v ⊗[F] E) ∧ IsTopologicalGroup (HA (Fv F v) σ J) ∧ LocallyCompactSpace (HA (Fv F v) σ J) ∧ T2Space (HA (Fv F v) σ J) ∧ SecondCountableTopology (HA (Fv F v) σ J) ∧ ∀ a : ℕ, IsOpen {X : Fin a → Fin n → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧ Continuous (fun p : HA (Fv F v) σ J × (Fin a → Fin n → Fv F v ⊗[F] E) => p.1 • p.2) := by
  intro F E _ _ _ _ _ σ _ n J _ v
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hr : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Fv F v) σ n J
  refine ⟨hr, e.isClosedEmbedding.locallyCompactSpace, e.isEmbedding.t2Space,
    e.secondCountableTopology, inferInstanceAs (IsTopologicalGroup (HR (Fv F v) σ J)), h1, h3, h2,
    fun a => ⟨?_, ?_⟩⟩
  · letI : NontriviallyNormedField (Fv F v) :=
      Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
    exact isOpen_linearIndependent (K := Fv F v)
      (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E))
  · have hm : Continuous fun g : HA (Fv F v) σ J => HA.mat (Fv F v) σ J g :=
      continuous_subtype_val
    have hv : Continuous fun g : HA (Fv F v) σ J =>
        ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := Units.continuous_val.comp hm
    refine continuous_pi fun b => ?_
    exact (hv.comp continuous_fst).matrix_mulVec ((continuous_apply b).comp continuous_snd)

end GlobalTheory.LocalUnitaryTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTuplesTopologicalFactsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localUnitaryGroup_tuples_topological_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), IsTopologicalRing (Fv F v ⊗[F] E) ∧ LocallyCompactSpace (Fv F v ⊗[F] E) ∧ T2Space (Fv F v ⊗[F] E) ∧ SecondCountableTopology (Fv F v ⊗[F] E) ∧ IsTopologicalGroup (HA (Fv F v) σ J) ∧ LocallyCompactSpace (HA (Fv F v) σ J) ∧ T2Space (HA (Fv F v) σ J) ∧ SecondCountableTopology (HA (Fv F v) σ J) ∧ ∀ a : ℕ, IsOpen {X : Fin a → Fin n → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧ Continuous (fun p : HA (Fv F v) σ J × (Fin a → Fin n → Fv F v ⊗[F] E) => p.1 • p.2) := by
  first | exact @GlobalTheory.LocalUnitaryTop.top_facts | exact GlobalTheory.LocalUnitaryTop.top_facts | (intros; apply GlobalTheory.LocalUnitaryTop.top_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionEqScalarSqNormalisedBesselTorusCon
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionEqScalarSqNormalisedBesselTorusCon
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.ThA

private lemma inv_mul_comm_of_mul_comm {n : Type*} [Fintype n] [DecidableEq n] (a h : Matrix n n ℂ)
    (hah : a * h = h * a) : h⁻¹ * a = a * h⁻¹ := by
  by_cases hh : IsUnit h.det
  · calc h⁻¹ * a = h⁻¹ * (a * h) * h⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hh, Matrix.mul_one]
      _ = h⁻¹ * (h * a) * h⁻¹ := by rw [hah]
      _ = a * h⁻¹ := by rw [← Matrix.mul_assoc h⁻¹ h a, Matrix.nonsing_inv_mul _ hh, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hh, Matrix.zero_mul, Matrix.mul_zero]

private lemma inv_mul_conj_mul_conj_eq_conj_of_commute {n : Type*} [Fintype n] [DecidableEq n] (a H M g M' H' : Matrix n n ℂ)
    (ha : IsUnit a.det) (c1 : a * H = H * a) (c2 : a * H' = H' * a) :
    H⁻¹ * (a * M * a⁻¹)⁻¹ * g * (a * M' * a⁻¹) * H' =
      a * (H⁻¹ * M⁻¹ * (a⁻¹ * g * a) * M' * H') * a⁻¹ := by
  have e1 : (a * M * a⁻¹)⁻¹ = a * M⁻¹ * a⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.mul_assoc]
  have d1 : H⁻¹ * a = a * H⁻¹ := inv_mul_comm_of_mul_comm a H c1
  have d2 : a⁻¹ * H' = H' * a⁻¹ := inv_mul_comm_of_mul_comm H' a c2.symm
  rw [e1]
  simp only [Matrix.mul_assoc]
  rw [d2, ← Matrix.mul_assoc H⁻¹ a, d1, Matrix.mul_assoc]

theorem besselJ_conj {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c c' : ℂ)
    (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (μW μN μW' : Measure (Mt k r)) [SFinite μW] [SFinite μN] [SFinite μW']
    (hW : μW (UWset k r z)ᶜ = 0) (hN : μN (Nset k r)ᶜ = 0) (hW' : μW' (UWset k r z')ᶜ = 0)
    (a : B.Mat k r) (ha : IsUnit a.det)
    (hc : ∀ h ∈ UWset k r z, a * h = h * a) (hc' : ∀ h ∈ UWset k r z', a * h = h * a)
    (hp : ∀ n ∈ Nset k r, psi k r z c (a * n * a⁻¹) = psi k r z c' n)
    (hp' : ∀ n ∈ Nset k r, psi k r z' c (a * n * a⁻¹) = psi k r z' c' n)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    besselJ k r z z' c π π' μW (μN.map (conjM a)) μW' F g =
      besselJ k r z z' c' π π' μW μN μW' (fun x => F (a * x * a⁻¹)) (a⁻¹ * g * a) := by
  have hm : Measurable (conjM (k := k) (r := r) a) := (BesselUnitaryEquiv.conjE (k := k) (r := r) a ha).measurable
  let E : Mt k r ≃ᵐ Mt k r := BesselUnitaryEquiv.conjE (k := k) (r := r) a ha
  let Φ : (Mt k r × Mt k r) × (Mt k r × Mt k r) ≃ᵐ (Mt k r × Mt k r) × (Mt k r × Mt k r) :=
    ((MeasurableEquiv.refl (Mt k r)).prodCongr E).prodCongr ((MeasurableEquiv.refl (Mt k r)).prodCongr E)
  have hpm : ∀ (ν : Measure (Mt k r)) [SFinite ν],
      (ν.prod μN).map (Prod.map id (conjM a)) = ν.prod (μN.map (conjM a)) := by
    intro ν _
    rw [← Measure.map_prod_map _ _ measurable_id hm, Measure.map_id]
  have hμ : (μW.prod (μN.map (conjM a))).prod (μW'.prod (μN.map (conjM a))) =
      ((μW.prod μN).prod (μW'.prod μN)).map Φ := by
    rw [← hpm μW, ← hpm μW', Measure.map_prod_map _ _ (measurable_id.prodMap hm) (measurable_id.prodMap hm)]
    rfl
  have aW : ∀ᵐ x ∂μW, x ∈ UWset k r z := ae_iff.2 hW
  have aN : ∀ᵐ x ∂μN, x ∈ Nset k r := ae_iff.2 hN
  have aW' : ∀ᵐ x ∂μW', x ∈ UWset k r z' := ae_iff.2 hW'
  have q1 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.1.1 ∈ UWset k r z :=
    (Measure.quasiMeasurePreserving_fst (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_fst (μ := μW) (ν := μN)).ae aW)
  have q2 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.1.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_snd (μ := μW) (ν := μN)).ae aN)
  have q3 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.2.1 ∈ UWset k r z' :=
    (Measure.quasiMeasurePreserving_snd (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_fst (μ := μW') (ν := μN)).ae aW')
  have q4 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.2.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_snd (μ := μW') (ν := μN)).ae aN)
  unfold besselJ
  rw [hμ, integral_map_equiv]
  refine integral_congr_ae ?_
  filter_upwards [q1, q2, q3, q4] with p h1 h2 h3 h4
  have hΦ : Φ p = ((p.1.1, conjM a p.1.2), (p.2.1, conjM a p.2.2)) := rfl
  have e2 : Matrix.of (conjM a p.1.2) = a * Matrix.of p.1.2 * a⁻¹ := rfl
  have e4 : Matrix.of (conjM a p.2.2) = a * Matrix.of p.2.2 * a⁻¹ := rfl
  rw [hΦ]
  dsimp only
  rw [e2, e4, hp (Matrix.of p.1.2) h2, hp' (Matrix.of p.2.2) h4,
    inv_mul_conj_mul_conj_eq_conj_of_commute a (Matrix.of p.1.1) (Matrix.of p.1.2) g (Matrix.of p.2.2) (Matrix.of p.2.1) ha
      (hc (Matrix.of p.1.1) h1) (hc' (Matrix.of p.2.1) h3)]

theorem besselJ_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (μW μN μW' : Measure (Mt k r)) [SFinite μW] [SFinite μN] [SFinite μW'] (t : ℝ≥0∞)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    besselJ k r z z' c π π' μW (t • μN) μW' F g =
      ((t.toReal ^ 2 : ℝ) : ℂ) • besselJ k r z z' c π π' μW μN μW' F g := by
  unfold besselJ
  rw [Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_left,
    Measure.prod_smul_right, smul_smul,
    integral_smul_measure, ENNReal.toReal_mul, ← pow_two, Complex.coe_smul]

theorem besselJ_changeFrame : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN : ℝ) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), IsStdOf L μsec Bs → IsRatioN k r cN → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → ∀ g : B.Mat k r, L.J F g = ((lamN L cN ^ 2 : ℝ) : ℂ) • B.JF Bs (conjF (cStd / L.c) F) ((aT k r (cStd / L.c))⁻¹ * g * aT k r (cStd / L.c)) := by
  intro k r L μsec Bs cN F hstd hR hc hκ0 hκT g
  obtain ⟨hz, hz', hπ, hπ', hμW, hμW', hμN, -⟩ := hstd
  have hα : cStd / L.c ≠ 0 := div_ne_zero (by simp [cStd]) hc
  have hcα : L.c * (cStd / L.c) = cStd := by field_simp
  set α := cStd / L.c with hαdef
  obtain ⟨-, hT, -, -⟩ := GlobalTheory.T.besselTorusElement_properties k r α hα
  obtain ⟨hcz, hnz⟩ := hT L.z L.hz.1
  obtain ⟨hcz', hnz'⟩ := hT L.z' L.hz'.1
  have hmap := GlobalTheory.T.lebesgue_rootCoordinates_map_besselTorus_conj k r α hα
  have ha : IsUnit (aT k r α).det := by
    rw [aT, Matrix.det_diagonal]
    refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    split_ifs
    · exact pow_ne_zero _ hα
    · exact one_ne_zero
    · exact inv_ne_zero (pow_ne_zero _ (star_ne_zero.mpr hα))
  have hp : ∀ w : Fin (2 * r + k + 1) → ℂ,
      (∀ n ∈ Nset k r, ell k r w (aT k r α * n * (aT k r α)⁻¹) = α * ell k r w n) →
      ∀ n ∈ Nset k r, psi k r w L.c (aT k r α * n * (aT k r α)⁻¹) = psi k r w cStd n := by
    intro w hw n hn
    simp only [psi, hw n hn, ← mul_assoc, hcα]
  haveI : IsFiniteMeasure L.μW := ⟨by rw [L.hμW.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure L.μW' := ⟨by rw [L.hμW'.2]; exact ENNReal.one_lt_top⟩
  have hNc : (D.muN k r) (Nset k r)ᶜ = 0 := by rw [← hμN]; exact Bs.haarN.conc
  haveI : IsFiniteMeasureOnCompacts (D.muN k r) :=
    ⟨fun K hK => by rw [← hμN]; exact Bs.haarN.finite_compact K hK⟩
  have hW : L.μW (UWset k r L.z)ᶜ = 0 := L.hμW.1.2.2.1
  have hW' : L.μW' (UWset k r L.z')ᶜ = 0 := L.hμW'.1.2.2.1
  have hx : 0 < ‖α‖ ^ B.kap k r := pow_pos (norm_pos_iff.mpr hα) _
  have hone : ENNReal.ofReal (‖α‖ ^ B.kap k r) * ENNReal.ofReal ((‖α‖ ^ B.kap k r)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul hx.le, mul_inv_cancel₀ hx.ne', ENNReal.ofReal_one]
  have hLμN : L.μN = (L.κN * ENNReal.ofReal cN * ENNReal.ofReal (‖α‖ ^ B.kap k r)) •
      (D.muN k r).map (conjM (aT k r α)) := by
    rw [hmap, smul_smul, mul_assoc (L.κN * ENNReal.ofReal cN), hone, mul_one, mul_smul, ← hR.2]
    simp only [Formalism.MainNotions.S.LocBessel.μN, Formalism.MainNotions.S.haarLie, one_smul]
  have ht : (L.κN * ENNReal.ofReal cN * ENNReal.ofReal (‖α‖ ^ B.kap k r)).toReal = lamN L cN := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hR.1.le, ENNReal.toReal_ofReal hx.le]
    rfl
  have step : L.J F g = ((lamN L cN ^ 2 : ℝ) : ℂ) •
      besselJ k r L.z L.z' L.c L.π L.π' L.μW ((D.muN k r).map (conjM (aT k r α))) L.μW' F g := by
    rw [← ht]
    show besselJ k r L.z L.z' L.c L.π L.π' L.μW L.μN L.μW' F g = _
    rw [hLμN]
    exact besselJ_smul k r L.z L.z' L.c L.π L.π' L.μW _ L.μW' _ F g
  rw [step, besselJ_conj k r L.z L.z' L.c cStd L.π L.π' L.μW (D.muN k r) L.μW' hW hNc hW' (aT k r α) ha
    hcz hcz' (hp L.z fun n hn => (hnz n hn).2.2) (hp L.z' fun n hn => (hnz' n hn).2.2) F g,
    Formalism.FourierDecayAlt.B.JF, hz, hz', hπ, hπ', hμW, hμW', hμN]
  rfl

end GlobalTheory.ThA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionEqScalarSqNormalisedBesselTorusConStatement
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselFunction_eq_scalar_sq_normalisedBessel_torusConjugate : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN : ℝ) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), IsStdOf L μsec Bs → IsRatioN k r cN → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → ∀ g : B.Mat k r, L.J F g = ((lamN L cN ^ 2 : ℝ) : ℂ) • B.JF Bs (conjF (cStd / L.c) F) ((aT k r (cStd / L.c))⁻¹ * g * aT k r (cStd / L.c)) := by
  first | exact @GlobalTheory.ThA.besselJ_changeFrame | exact GlobalTheory.ThA.besselJ_changeFrame | (intros; apply GlobalTheory.ThA.besselJ_changeFrame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockProjectionBessel
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockProjectionBessel
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellPieri

variable {k r : ℕ}

def withRep (L : LocBessel k r) (R : Rep k r) (mu : Fin (2 * r + k + 1) → ℝ) (hR : R.IsDS L.ε mu) :
    LocBessel k r :=
  { L with lam := mu, hlam := hR.1, Hs := R.H, hsN := R.nacg, hsI := R.ips, hsC := R.cs, σ := R.σ, hσ := hR.2 }

theorem fdegHC_pos {n : ℕ} {lam : Fin n → ℝ} (hlam : StrictAnti lam) : 0 < fdegHC lam := by
  unfold fdegHC
  apply div_pos
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    have hab : a < b := (Finset.mem_filter.mp hb).2
    exact abs_pos.mpr (sub_ne_zero.mpr (hlam hab).ne')
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    exact sub_pos.mpr (Nat.cast_lt.mpr (Finset.mem_filter.mp hb).2)

def coefR {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (R : Rep k r) (v v' : R.H) (ξ : Wp) (ξ' : Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Wq →L[ℂ] Wp :=
  (innerSL ℂ ξ').smulRight (⟪v, R.σ g v'⟫_ℂ • ξ)

theorem amp_eq_orb (hH : Hyps) (hA : AmpKF) (hC : CellConv) (L : LocBessel k r) (R : Rep k r)
    (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (l : R.H → L.Wp) (l' : R.H → L.Wq) (w : R.H)
    [CompleteSpace L.Wp] [CompleteSpace L.Wq]
    (hR : R.IsDS L.ε mu) (hgap : GapAtLeast L.ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hcell : GapCell k r h)
    (hc : L.c ≠ 0) (hκ : L.κN ≠ ⊤) (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hl : ∀ x ∈ R.sm, ∀ v ∈ R.TK,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x))
    (hl' : ∀ x ∈ R.sm, ∀ v ∈ R.TK,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))
    (hw : PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
    (ν : Measure (PairSp k r)) (hD : CellData L μG γ μR νR ν) (v v' : R.H) (hv : R.KFin v) (hv' : R.KFin v')
    (ξ : L.Wp) (ξ' : L.Wq) :
    Integrable (besselIntg L (coefR R v v' ξ ξ') γ) ν ∧
      ((PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ) * (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ)) • amp R l l' w νR γ =
        OrbInt L (coefR R v v' ξ ξ') γ ν := by
  have hKF : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨-, -, -, -, hsm, -, hKT, -, -⟩ := GlobalTheory.rep_basic_of_isDS hKF k r L.ε mu R hR
  have hwK : R.KFin w := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hw
  have hle : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, x ∈ R.TK := by
    intro x hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hg, w, hwK, rfl⟩
  have hD' : CellData (withRep L R mu hR) μG γ μR νR ν := hD
  obtain ⟨b, hb0, hb1, hb2⟩ := hC k r L h μG γ μR νR ν hκ hok hcell hD hD.2.2.1
  have hAG : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hOne : OnePlaceKF (withRep L R mu hR) h μG w l l' :=
    ⟨⟨hgap, hok, hc, hw, hG, fun x hx y hy => hl x (hsm x (hle x hx)) y (hle y hy),
      fun x hx y hy => hl' x (hsm x (hle x hx)) y (hle y hy)⟩,
      fun x hx y hy => hl x (hsm x (hle x hx)) y (hKT y hy),
      fun x hx y hy => hl' x (hsm x (hle x hx)) y (hKT y hy)⟩
  have h1 := hA hH.1 k r (withRep L R mu hR) h μG w l l' hOne γ μR νR ν hD' b hb0 hb1 hb2 v v' hv hv' ξ ξ'
  have h2 := (GlobalTheory.T.cell_data_support hH k r (withRep L R mu hR) h μG γ μR νR ν hgap hok hκ hD').2 b hb0 (by linarith)
    hb2 v v' hv hv' ξ ξ'
  refine ⟨h2, ?_⟩
  obtain ⟨c, hc0, hc1⟩ := GlobalTheory.BesselDegree.schur_fdeg hH k r L.ε μG hG
  have hw0 : w ≠ 0 := by
    obtain ⟨P, -, hn, -⟩ := hw
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  have hf : (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ) ≠ 0 := by
    rw [(hc1 mu R hR).1 w hw0]
    exact Complex.ofReal_ne_zero.mpr (mul_pos hc0 (fdegHC_pos hR.1.1)).ne'
  have h3 : (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • amp R l l' w νR γ =
      ((PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)⁻¹) • OrbInt L (coefR R v v' ξ ξ') γ ν := h1
  rw [mul_smul, h3, smul_smul, mul_inv_cancel₀ hf, one_smul]

theorem herm_inv {ι : Type} [Fintype ι] [DecidableEq ι]
    {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ} {d : ℕ}
    (hρ : IsFRep ρ Γ d) {om : ι → ℂ} {a g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ GG k r) (hg : g ∈ GG k r) (hom : ρ a *ᵥ om = om) (x : ι → ℂ) :
    herm Γ (ρ (a⁻¹ * g) *ᵥ x) om = herm Γ (ρ g *ᵥ x) om := by
  obtain ⟨-, -, -, hmul, hinv, -⟩ := hρ
  obtain ⟨hai, h1, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv ha
  have hm : a⁻¹ * g ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hai hg
  have e : ρ g = ρ a * ρ (a⁻¹ * g) := by
    rw [← hmul a ha _ hm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  unfold herm
  rw [e]
  conv_rhs => rw [← hom]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hinv a ha]

theorem one_mem_UH : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UH (Hpk k r) := by
  simp [UH]

theorem mem_Sset_of_UW {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UWset k r z) : g ∈ Sset k r z := by
  refine ⟨g, hg, 1, ⟨one_mem_UH, fun a i _ => ?_, fun i j _ _ _ => ?_⟩, (Matrix.mul_one g).symm⟩ <;>
    exact Matrix.one_apply

theorem mem_Sset_of_N (z : Fin (2 * r + k + 1) → ℂ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Nset k r) : g ∈ Sset k r z :=
  ⟨1, ⟨one_mem_UH, fun _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩, g, hg,
    (Matrix.one_mul g).symm⟩

theorem herm_cell {ι : Type} [Fintype ι] [DecidableEq ι]
    {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ} {d : ℕ}
    (hρ : IsFRep ρ Γ d) {om om' : ι → ℂ} {z z' : Fin (2 * r + k + 1) → ℂ}
    (hom : ∀ g ∈ Sset k r z, ρ g *ᵥ om = om) (hom' : ∀ g ∈ Sset k r z', ρ g *ᵥ om' = om')
    {a n γ n' a' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ GG k r)
    (ha : a ∈ UWset k r z) (hn : n ∈ Nset k r) (ha' : a' ∈ UWset k r z') (hn' : n' ∈ Nset k r) :
    a⁻¹ * n⁻¹ * γ * n' * a' ∈ GG k r ∧
      herm Γ (ρ (a⁻¹ * n⁻¹ * γ * n' * a') *ᵥ om') om = herm Γ (ρ γ *ᵥ om') om := by
  have mul : ∀ {x y}, x ∈ GG k r → y ∈ GG k r → x * y ∈ GG k r := fun hx hy => Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hx hy
  have hai := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv ha.1).1
  have hni := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hn.1).1
  have h1 := mul (mul hai hni) hγ
  have h2 := mul h1 hn'.1
  refine ⟨mul h2 ha'.1, ?_⟩
  rw [hρ.2.2.2.1 _ h2 _ ha'.1, hρ.2.2.2.1 _ h1 _ hn'.1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hom' _ (mem_Sset_of_UW ha'), hom' _ (mem_Sset_of_N z' hn'), Matrix.mul_assoc,
    herm_inv hρ ha.1 (mul hni hγ) (hom _ (mem_Sset_of_UW ha)),
    herm_inv hρ hn.1 hγ (hom _ (mem_Sset_of_N z hn))]

theorem amp_pieri : Hyps → AmpKF → CellConv → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (L : LocBessel k r) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (om om' : ι → ℂ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (lI : ∀ I, (RI I).H → L.Wp) (lI' : ∀ I, (RI I).H → L.Wq) (w : R.H) (wI : ∀ I, (RI I).H) (κ₀ κ₁ : κ → ℂ), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → (∀ I, (RI I).IsDS L.ε (muI I) ∧ GapAtLeast L.ε (muI I) h) → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → L.c ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Sset k r L.z, ρ g *ᵥ om = om) → (∀ g ∈ Sset k r L.z', ρ g *ᵥ om' = om') → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∀ I, (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π (RI I).σ L.μW L.μN x v = (innerSL ℂ (lI I v)).smulRight (lI I x)) ∧ (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' (RI I).σ L.μW' L.μN x v = (innerSL ℂ (lI' I v)).smulRight (lI' I x))) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → (∀ I, PI.UpqRep.IsLowUnitH k r L.ε (muI I) (RI I).σ (wI I)) → (∀ I, ∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ I • l v ∧ lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ I • l' v) → ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν → (herm Γ (ρ γ *ᵥ om') om * (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)) • amp R l l' w νR γ = ∑ I, ((ep I : ℂ) * κ₁ I * star (κ₀ I) * (PI.BesselPeriodGGP.fdegH μG (RI I).σ (wI I) : ℂ)) • amp (RI I) (lI I) (lI' I) (wI I) νR γ := by
  intro hH hA hC k r ι κ _ _ _ _ ρ Γ d L R RI io pr ep mu muI h μG om om' l l' lI lI' w wI κ₀ κ₁
  haveI := FiniteDimensional.complete ℂ L.Wp
  haveI := FiniteDimensional.complete ℂ L.Wq
  intro hR hgap hRI hok hcell hc hκ hG hρ hT hom hom' hl hl' hlI ⟨v, hv, hv0⟩ ⟨v', hv', hv0'⟩ hw hwI hκI γ μR νR ν hD
  have hKF : PI.KFinSmooth := hH.1.2.2.1
  have hvs : v ∈ R.sm := hKF k r L.ε mu R.H R.σ hR.1 hR.2 v hv
  have hvs' : v' ∈ R.sm := hKF k r L.ε mu R.H R.σ hR.1 hR.2 v' hv'
  obtain ⟨hK, hsplit⟩ := GlobalTheory.KFinCoefSplit.kfin_coef_mul_split hKF k r ι κ ρ Γ d R RI io pr ep L.ε mu muI om om' v v' hR
    (fun I => (hRI I).1) hρ hT hv hv'
  obtain ⟨-, e0⟩ := amp_eq_orb hH hA hC L R mu h μG l l' w hR hgap hok hcell hc hκ hG hl hl' hw γ μR νR ν hD
    v v' hv hv' (l v) (l' v')
  have eI := fun I => amp_eq_orb hH hA hC L (RI I) (muI I) h μG (lI I) (lI' I) (wI I) (hRI I).1 (hRI I).2 hok hcell
    hc hκ hG (hlI I).1 (hlI I).2 (hwI I) γ μR νR ν hD _ _ (hK I).1 (hK I).2 (l v) (l' v')
  have hae := (GlobalTheory.T.cell_data_support hH k r (withRep L R mu hR) h μG γ μR νR ν hgap hok hκ hD).1
  have hc0 : ⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ ≠ 0 :=
    mul_ne_zero (inner_self_ne_zero.mpr hv0) (inner_self_ne_zero.mpr hv0')
  have horb : herm Γ (ρ γ *ᵥ om') om • OrbInt L (coefR R v v' (l v) (l' v')) γ ν =
      ∑ I, (ep I : ℂ) • OrbInt L (coefR (RI I) (∑ c, pr I c (tm R om v c)) (∑ c, pr I c (tm R om' v' c))
        (l v) (l' v')) γ ν := by
    unfold OrbInt
    simp only [← integral_smul]
    refine Eq.trans (integral_congr_ae ?_) (integral_finsetSum _ (fun I _ => (eI I).1.smul (ep I : ℂ)))
    filter_upwards [hae] with p hp
    obtain ⟨hm, he⟩ := herm_cell hρ hom hom' hD.1 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    have hs := hsplit _ hm
    rw [he] at hs
    ext x
    simp only [besselIntg, coefR, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, map_smul, smul_smul, Pi.smul_apply,
      ← Finset.sum_smul]
    congr 1
    have key : ∀ (D A B C : ℂ) (e f : κ → ℂ), D * C = ∑ I, e I * f I →
        D * A * (B * C) = ∑ I, e I * A * (B * f I) := by
      intro D A B C e f hh
      rw [show D * A * (B * C) = D * C * (A * B) by ring, hh, Finset.sum_mul]
      exact Finset.sum_congr rfl fun I _ => by ring
    exact key _ _ _ _ _ _ hs
  apply smul_right_injective _ hc0
  simp only [Finset.smul_sum, smul_smul]
  rw [mul_comm, mul_assoc, mul_smul, e0, horb]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← (eI I).2, smul_smul, (hκI I v hvs).1, (hκI I v' hvs').2, inner_smul_left, inner_smul_right]
  congr 1
  simp only [RCLike.star_def]
  ring

end GlobalTheory.CellPieri

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockProjectionBesselStatement
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_projection_bessel : Hyps → AmpKF → CellConv → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (L : LocBessel k r) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (om om' : ι → ℂ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (lI : ∀ I, (RI I).H → L.Wp) (lI' : ∀ I, (RI I).H → L.Wq) (w : R.H) (wI : ∀ I, (RI I).H) (κ₀ κ₁ : κ → ℂ), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → (∀ I, (RI I).IsDS L.ε (muI I) ∧ GapAtLeast L.ε (muI I) h) → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → L.c ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Sset k r L.z, ρ g *ᵥ om = om) → (∀ g ∈ Sset k r L.z', ρ g *ᵥ om' = om') → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∀ I, (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π (RI I).σ L.μW L.μN x v = (innerSL ℂ (lI I v)).smulRight (lI I x)) ∧ (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' (RI I).σ L.μW' L.μN x v = (innerSL ℂ (lI' I v)).smulRight (lI' I x))) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → (∀ I, PI.UpqRep.IsLowUnitH k r L.ε (muI I) (RI I).σ (wI I)) → (∀ I, ∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ I • l v ∧ lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ I • l' v) → ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν → (herm Γ (ρ γ *ᵥ om') om * (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)) • amp R l l' w νR γ = ∑ I, ((ep I : ℂ) * κ₁ I * star (κ₀ I) * (PI.BesselPeriodGGP.fdegH μG (RI I).σ (wI I) : ℂ)) • amp (RI I) (lI I) (lI' I) (wI I) νR γ := by
  first | exact @GlobalTheory.CellPieri.amp_pieri | exact GlobalTheory.CellPieri.amp_pieri | (intros; apply GlobalTheory.CellPieri.amp_pieri <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGramFibreOfHaar
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.GramFibreRescale

theorem isFibreFamily_smul {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V}
    {ν : Measure X} {B : Set X} {fib : X → Measure V} (h : IsFibreFamily μ f ι U ν B fib)
    (c d : ℝ≥0) (hd : d ≠ 0) :
    IsFibreFamily (c • μ) f ι U (d • ν) B (fun b => (c / d) • fib b) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφ hc hU => ⟨fun b hb => ?_, ?_⟩⟩
  · rw [Measure.smul_apply, h1 b, smul_zero]
  · simp only [Measure.restrict_smul, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul,
      mul_div_cancel₀ _ hd, h2 φ hφ]
  · exact ((h3 φ hφ hc hU).1 b hb).smul_measure_nnreal
  · simp only [integral_smul_nnreal_measure]
    exact (h3 φ hφ hc hU).2.const_smul (c / d)

end GlobalTheory.GramFibreRescale
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PiUnipotentModelMeasurableFullMeasure
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PiUnipotentModelMeasurableFullMeasure
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem nset_closed (k r : ℕ) : IsClosed {y : Mt k r | Matrix.of y ∈ Nset k r} := by
  simp only [Nset, UH, Set.mem_setOf_eq, Set.setOf_and, Set.setOf_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
  · have hc : Continuous fun y : Mt k r => (Matrix.of y)ᴴ * Hpk k r * Matrix.of y := by
      have h0 : Continuous fun y : Mt k r => (Matrix.of y : Matrix _ _ ℂ) := continuous_id
      exact (h0.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h0
    exact isClosed_eq hc continuous_const
  · refine isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => ?_
    exact isClosed_eq ((continuous_apply _).comp (continuous_apply _)) continuous_const
  · refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    exact isClosed_eq ((continuous_apply _).comp (continuous_apply _)) continuous_const

theorem pi_nset_full : ∀ (ι : Type) [Fintype ι] (k r : ℕ), MeasurableSet {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} ∧ (Measure.pi fun _ : ι => haarLie (Nset k r) 1) {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ = 0 := by
  intro ι _ k r
  have hS : MeasurableSet {y : Mt k r | Matrix.of y ∈ Nset k r} := (nset_closed k r).measurableSet
  have hH := (GlobalTheory.T.haar_lie_nilpotent_coordinates k r).1
  haveI : SigmaFinite (haarLie (Nset k r) 1) := hH.1
  have hset : {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} =
      ⋂ w, Function.eval w ⁻¹' {y : Mt k r | Matrix.of y ∈ Nset k r} := by
    ext x; simp
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact MeasurableSet.iInter fun w => measurable_pi_apply w hS
  · rw [hset, Set.compl_iInter]
    refine measure_iUnion_null fun w => ?_
    rw [← Set.preimage_compl]
    exact Measure.pi_eval_preimage_null _ (by simpa [Set.compl_setOf] using hH.2.2.1)

end GlobalTheory.SnMass.VolN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PiUnipotentModelMeasurableFullMeasureStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pi_unipotentModel_measurable_full_measure : ∀ (ι : Type) [Fintype ι] (k r : ℕ), MeasurableSet {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} ∧ (Measure.pi fun _ : ι => haarLie (Nset k r) 1) {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.pi_nset_full | exact GlobalTheory.SnMass.VolN.pi_nset_full | (intros; apply GlobalTheory.SnMass.VolN.pi_nset_full <;> assumption)
end
end
