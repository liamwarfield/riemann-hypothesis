module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartFromAdelicDictionary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroApproximationTwistPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepLevelContainsUnitaryNearOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepLevelContainsUnitaryNearOne
open NumberField IsDedekindDomain
open scoped TensorProduct
open scoped Topology

noncomputable section

namespace GlobalTheory.LevelApprox

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.ColAd

theorem eq_zero_of_le_pow {γ t : WithZero (Multiplicative ℤ)} (hγ : γ < 1) (h : ∀ m : ℕ, t ≤ γ ^ m) : t = 0 := by
  by_contra ht
  by_cases hγ0 : γ = 0
  · have := h 1
    rw [hγ0, pow_one] at this
    exact ht (le_antisymm this zero_le')
  have hg : γ.log < 0 := by
    rw [← WithZero.exp_lt_exp, WithZero.exp_log hγ0]
    simpa using hγ
  set N : ℕ := (-t.log).toNat + 1 with hN
  have hm : t.log ≤ (N : ℤ) * γ.log := by
    have h3 : WithZero.exp t.log ≤ WithZero.exp (N • γ.log) := by
      rw [WithZero.exp_nsmul, WithZero.exp_log ht, WithZero.exp_log hγ0]
      exact h N
    rw [WithZero.exp_le_exp, nsmul_eq_mul] at h3
    exact h3
  have h1 : (N : ℤ) * γ.log ≤ -(N : ℤ) := by
    have : (0 : ℤ) ≤ (N : ℤ) := by positivity
    nlinarith
  have h2 := Int.self_le_toNat (-t.log)
  have h4 : (N : ℤ) = ((-t.log).toNat : ℤ) + 1 := by rw [hN]; push_cast; ring
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def SmallAt (Q : Finset (HeightOneSpectrum (𝓞 E))) (d : ℕ) : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  {a | (∀ w ∉ Q, adAt F w a = 0) ∧ ∀ w ∈ Q, Valued.v (adAt F w a) ≤ WithZero.exp (-(d : ℤ))}

theorem exists_smallAt_subset (Q : Finset (HeightOneSpectrum (𝓞 E))) {V : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (hV : letI := Formalism.BasicNotions.tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
      V ∈ 𝓝 (0 : E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    ∃ d : ℕ, SmallAt (F := F) Q d ⊆ V := by
  classical
  letI := Formalism.BasicNotions.tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
  haveI := Formalism.L2.Col.adeles_t2Space (F := F) (E := E)
  obtain ⟨β, hβ0, hβ⟩ : ∃ β : 𝓞 E, β ≠ 0 ∧ ∀ P ∈ Q, β ∈ P.asIdeal := by
    choose f hf hf0 using fun P : HeightOneSpectrum (𝓞 E) => Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    exact ⟨∏ P ∈ Q, f P, Finset.prod_ne_zero_iff.2 fun P _ => hf0 P, fun P hP =>
      Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem f hP) (hf P)⟩
  set b : E := algebraMap (𝓞 E) E β with hb
  have hb0 : b ≠ 0 := by simpa [hb] using hβ0
  let ι : E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F := Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)
  set e : E ⊗[F] FiniteAdeleRing (𝓞 F) F := ∑ P ∈ Q, PtExist.idem F P with he_def
  have he : ∀ w, adAt F w e = if w ∈ Q then 1 else 0 := by
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [he_def, map_sum]
    simp only [PtExist.adAt_idem]
    exact Finset.sum_ite_eq Q w (fun _ => (1 : w.adicCompletion E))
  have hint : ∀ y ∈ Formalism.L2.Herm.intAf F E, ∀ w, Valued.v (adAt F w y) ≤ 1 := fun y hy w =>
    (mem_rInt_iff F E y).1 hy w
  have hbw : ∀ w ∈ Q, Valued.v (adAt F w (ι b)) < 1 := fun w hw => by
    rw [adAt_inclE, valued_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 (hβ w hw)
  have hbne : ∀ w, adAt F w (ι b) ≠ 0 := fun w => by
    rw [adAt_inclE]
    exact (map_ne_zero _).2 hb0
  let c : ℕ → E ⊗[F] FiniteAdeleRing (𝓞 F) F := fun m => e * ι b ^ m
  let K : ℕ → Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := fun m => (c m * ·) '' (Formalism.L2.Herm.intAf F E : Set _)
  have hKc : ∀ m, IsCompact (K m) := fun m => Formalism.L2.Col.rlt_isCompact_intAf.image (continuous_const_mul (c m))
  have hKa : Antitone K := by
    refine antitone_nat_of_succ_le fun m => ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨ι b * y, mul_mem (Formalism.L2.Col.iA_mem β) hy, ?_⟩
    simp only [c, pow_succ]
    ring
  have hK0 : ∀ x ∈ ⋂ m, K m, V ∈ 𝓝 x := by
    intro x hx
    have : x = 0 := by
      refine PtExist.ad_ext fun w => ?_
      rw [map_zero]
      by_cases hw : w ∈ Q
      · have h0 : Valued.v (adAt F w x) = 0 := eq_zero_of_le_pow (hbw w hw) fun m => by
          obtain ⟨y, hy, hxy⟩ := Set.mem_iInter.1 hx m
          rw [← hxy]
          simp only [c, map_mul, map_pow, he, if_pos hw, one_mul]
          exact mul_le_of_le_one_right' (hint y hy w)
        exact (Valuation.zero_iff _).1 h0
      · obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.1 hx 0
        simp only [c, map_mul, he, if_neg hw, zero_mul]
    rw [this]
    exact hV
  obtain ⟨m, hm⟩ := exists_subset_nhds_of_isCompact hKa.directed_ge hKc (mem_nhdsSet_iff_forall.2 hK0)

  let D : ℕ := ∑ w ∈ Q, (-(Valued.v (adAt F w (ι b))).log).toNat
  have hD : ∀ w ∈ Q, WithZero.exp (-(D : ℤ)) ≤ Valued.v (adAt F w (ι b)) := fun w hw => by
    have h0 : Valued.v (adAt F w (ι b)) ≠ 0 := (Valuation.ne_zero_iff _).2 (hbne w)
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    have h1 : (-(Valued.v (adAt F w (ι b))).log).toNat ≤ D :=
      Finset.single_le_sum (f := fun w => (-(Valued.v (adAt F w (ι b))).log).toNat) (fun _ _ => Nat.zero_le _) hw
    have h2 := Int.self_le_toNat (-(Valued.v (adAt F w (ι b))).log)
    omega
  refine ⟨m * D, fun a ha => hm ?_⟩
  have hinv : ∀ w, adAt F w (ι b⁻¹) = (adAt F w (ι b))⁻¹ := fun w => by
    rw [adAt_inclE, adAt_inclE, map_inv₀]
  refine ⟨e * ι b⁻¹ ^ m * a, (mem_rInt_iff F E _).2 fun w => ?_, ?_⟩
  · show Valued.v (adAt F w _) ≤ 1
    by_cases hw : w ∈ Q
    · simp only [map_mul, map_pow, he, hinv, if_pos hw, one_mul, map_inv₀, inv_pow, map_one]
      have hv : 0 < Valued.v (adAt F w (ι b)) ^ m :=
        pow_pos (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (hbne w))) m
      rw [inv_mul_le_one₀ hv]
      refine (ha.2 w hw).trans ?_
      have : WithZero.exp (-((m * D : ℕ) : ℤ)) = WithZero.exp (-(D : ℤ)) ^ m := by
        rw [← WithZero.exp_nsmul]
        congr 1
        push_cast
        ring
      rw [this]
      exact pow_le_pow_left₀ zero_le' (hD w hw) m
    · rw [map_mul, ha.1 w hw, mul_zero, map_zero]
      exact zero_le'
  · refine PtExist.ad_ext fun w => ?_
    simp only [c, map_mul, map_pow, he, hinv]
    by_cases hw : w ∈ Q
    · rw [if_pos hw, one_mul, one_mul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (hbne w), one_pow, one_mul]
    · rw [ha.1 w hw, mul_zero, mul_zero]

end GlobalTheory.LevelApprox

namespace GlobalTheory.LevelApprox

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.ColAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_entry_sub_one {n : ℕ} (w : HeightOneSpectrum (𝓞 E)) (z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (i j : Fin n) :
    adAt F w ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j -
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j) = (locM w z - 1) i j := by
  rw [map_sub, Matrix.sub_apply]
  congr 1
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem entry_mem_smallAt {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))} {d : ℕ}
    {z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h1 : ∀ w ∉ Q, locM w z = 1)
    (h2 : ∀ w ∈ Q, Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM w z - 1)) (i j : Fin n) :
    (z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j -
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j ∈ SmallAt (F := F) Q d := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · rw [adAt_entry_sub_one, h1 w hw, sub_self, Matrix.zero_apply]
  · rw [adAt_entry_sub_one]
    exact h2 w hw i j

theorem mem_U_of_near_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad)
    (Q : Finset (HeightOneSpectrum (𝓞 E))), ∃ d : ℕ, ∀ z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    z ∈ Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ w ∉ Q, GlobalTheory.Mem.ColAd.locM w z = 1) →
    (∀ w ∈ Q, GlobalTheory.Mem.ColAd.Sm Valued.v (WithZero.exp (-(d : ℤ))) (GlobalTheory.Mem.ColAd.locM w z - 1) ∧
      GlobalTheory.Mem.ColAd.Sm Valued.v (WithZero.exp (-(d : ℤ))) (GlobalTheory.Mem.ColAd.locM w z⁻¹ - 1)) → z ∈ S.U := by
  intro F E _ _ _ _ _ σ n J T f bad S Q
  classical
  letI := Formalism.BasicNotions.tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
  let A : ℕ → Set (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := fun d => {z | (∀ w ∉ Q, locM w z = 1) ∧
    ∀ w ∈ Q, Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM w z - 1) ∧ Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM w z⁻¹ - 1)}
  have hexp : Antitone fun d : ℕ => WithZero.exp (-(d : ℤ)) := fun a b h =>
    WithZero.exp_le_exp.2 (by simpa using h)
  have hA : Antitone A := fun a b h z hz => ⟨hz.1, fun w hw => ⟨(hz.2 w hw).1.mono (hexp h), (hz.2 w hw).2.mono (hexp h)⟩⟩
  have hinv1 : ∀ z ∈ A 0, ∀ w ∉ Q, locM w z⁻¹ = 1 := fun z hz w hw => by
    have := locM_mul (P := w) z z⁻¹
    rw [mul_inv_cancel, locM_one, hz.1 w hw, one_mul] at this
    exact this.symm
  let G : Filter (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := ⨅ d, Filter.principal (A d)
  have hsmall : ∀ g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      (∀ d, ∀ z ∈ A d, g z ∈ SmallAt (F := F) Q d) → Filter.Tendsto g G (𝓝 0) := fun g hg V hV => by
    obtain ⟨d, hd⟩ := exists_smallAt_subset (F := F) Q hV
    exact Filter.mem_iInf_of_mem d (Filter.mem_principal.2 fun z hz => hd (hg d z hz))
  have hentry : ∀ (M : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) → Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      (∀ i j, Filter.Tendsto (fun z => M z i j - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j) G (𝓝 0)) →
      Filter.Tendsto M G (𝓝 1) := fun M hM =>
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => by
      have := (hM i j).add_const ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j)
      simpa using this
  have hT : Filter.Tendsto id G (𝓝 (1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine Filter.Tendsto.prodMk_nhds ?_ ((MulOpposite.continuous_op.tendsto _).comp ?_)
    · refine hentry _ fun i j => hsmall _ fun d z hz => entry_mem_smallAt hz.1 (fun w hw => (hz.2 w hw).1) i j
    · refine hentry (fun z => ((z⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)) fun i j => hsmall _ fun d z hz => ?_
      exact entry_mem_smallAt (fun w hw => hinv1 z (hA (Nat.zero_le d) hz) w hw) (fun w hw => (hz.2 w hw).2) i j
  have h1 : {x : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ S.U} ∈
      𝓝 (1 : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) := S.U_open.mem_nhds S.U.one_mem
  obtain ⟨t, ht, hts⟩ := (mem_nhds_subtype _ _ _).1 h1
  have hdir : Directed (· ≥ ·) fun d => Filter.principal (A d) :=
    Antitone.directed_ge (f := fun d => Filter.principal (A d)) fun a b h => Filter.principal_mono.2 (hA h)
  obtain ⟨d, hd⟩ := (Filter.mem_iInf_of_directed hdir _).1 (hT ht)
  exact ⟨d, fun z hz h1 h2 => hts (show (⟨z, hz⟩ : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) ∈ Subtype.val ⁻¹' t from
    hd ⟨h1, h2⟩)⟩

end GlobalTheory.LevelApprox

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepLevelContainsUnitaryNearOneStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepLevel_contains_unitary_near_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (Q : Finset (HeightOneSpectrum (𝓞 E))), ∃ d : ℕ, ∀ z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), z ∈ Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ w ∉ Q, GlobalTheory.Mem.ColAd.locM w z = 1) → (∀ w ∈ Q, GlobalTheory.Mem.ColAd.Sm Valued.v (WithZero.exp (-(d : ℤ))) (GlobalTheory.Mem.ColAd.locM w z - 1) ∧ GlobalTheory.Mem.ColAd.Sm Valued.v (WithZero.exp (-(d : ℤ))) (GlobalTheory.Mem.ColAd.locM w z⁻¹ - 1)) → z ∈ S.U := by
  first | exact @GlobalTheory.LevelApprox.mem_U_of_near_one | exact GlobalTheory.LevelApprox.mem_U_of_near_one | (intros; apply GlobalTheory.LevelApprox.mem_U_of_near_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroApproximationTwistPrimes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ApproxZero

section Support
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker Formalism.UG _root_.Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem exists_K1_element_local_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → ∀ (g : GL (Fin n) (AfE F E)), g ∈ UAd hc n → ∀ c : ℕ, ∃ z ∈ K1 hc n ST SG, (∀ P : Q, Sm Valued.v (dep P.1 c) (locM P.1 z - 1)) ∧ (∀ w, w ∉ Q → conjPrime₂ w ∉ Q → locM w z = 1) ∧ ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * z) p := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q hQ g hg c
  classical
  have hcc : ∀ P : HeightOneSpectrum (𝓞 E), conjPrime₂ (conjPrime₂ P) = P := fun P => by
    ext b
    rw [mem_conjP, mem_conjP, cO_cO]
  obtain ⟨p, hp⟩ := exists_near (ST := ST) (SG := SG) (Q := Q) hc c hg
  have hN : Formalism.UG.CS.globLat g (Formalism.L2.Col.stdLat E n) = p.deco.1.N := congrArg Deco.N hp.deco
  obtain ⟨g', hg', c1, c2, c3⟩ := PtExist.exists_modify (fun P hP => (hQ P hP).2.2.2.2) hg (ptFr p)
    fun P _ => hN ▸ isFr_ptFr p P
  have hoff : ∀ P, P ∈ ST ∨ P ∈ SG → P ∉ Q ∧ conjPrime₂ P ∉ Q := fun P hP => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases hP with hP | hP
      · exact (hQ P h).1 hP
      · exact (hQ P h).2.1 hP
    · have := hQ _ h
      rw [hcc] at this
      rcases hP with hP | hP
      · exact this.2.2.1 hP
      · exact this.2.2.2.1 hP
  have hpt : IsPtOf hc g' p := by
    refine ⟨hg', hN ▸ c1, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P i j => ?_⟩
    · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
      rw [← hN] at hv
      have ho := hoff P.1 (Or.inl P.2)
      rw [c3 _ ho.1 ho.2, ← hp.deco]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hv), e]
      exact PtExist.hasRes_redA _ ((mem_globLat g v).1 hv i)
    · rw [← hN] at hv
      have ho := hoff P.1 (Or.inr P.2)
      rw [c3 _ ho.1 ho.2, ← hp.deco]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hv)]
      exact PtExist.hasRes_redA _ ((mem_globLat g v).1 hv i)
    · rw [c2 _ P.2, ptFr_of_mem p (hQ P.1 P.2).2.1 P.2]
      rfl
  have hd : decoRaw ST SG g = decoRaw ST SG g' := hp.deco.trans (near_of_isPtOf hpt c).deco.symm
  refine ⟨g⁻¹ * g', mem_principal_of_same_decoration hc n ST SG hg hg' hd, fun P => ?_, fun w h1 h2 => ?_, p, by rwa [mul_inv_cancel_left]⟩
  · have e : locM P.1 g' = ratM P.1 (p.fr P) := Matrix.ext fun i j => hpt.fr P i j
    rw [locM_mul, e]
    exact hp.fr P
  · have hinv : locM w g'⁻¹ = locM w g⁻¹ := by
      refine Matrix.ext fun i j => ?_
      have := c3 w h1 h2 (Pi.single j 1) i
      simpa [GlobalTheory.Mem.Col2.pullV, Formalism.L2.Col.pullV, Matrix.mulVec, dotProduct, Pi.single_apply, locM] using this
    have hz : locM w (g⁻¹ * g')⁻¹ = 1 := by
      rw [_root_.mul_inv_rev, inv_inv, locM_mul, hinv, ← locM_mul, inv_mul_cancel, locM_one]
    calc locM w (g⁻¹ * g') = locM w (g⁻¹ * g') * locM w (g⁻¹ * g')⁻¹ := by rw [hz, Matrix.mul_one]
      _ = 1 := by rw [← locM_mul, mul_inv_cancel, locM_one]

end Support

section Conj
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker Formalism.UG _root_.Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem conj_small {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
    {n : ℕ} {z : GL (Fin n) (AfE F E)} (hz : z ∈ UAd hc n) {P : HeightOneSpectrum (𝓞 E)} {γ : WithZero (Multiplicative ℤ)}
    (h : Sm Valued.v γ (locM P z⁻¹ - 1)) : Sm Valued.v γ (locM (conjPrime₂ P) z - 1) := by
  classical
  intro i j
  have hcc : conjPrime₂ (conjPrime₂ P) = P := by
    ext b
    rw [mem_conjP, mem_conjP, cO_cO]
  have e := PtExist.inv_apply (inv_mem hz) i j
  rw [inv_inv] at e
  have h1 := h j i
  have e1 : (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j =
      Formalism.UG.sigR (CMData.sig hc) (FiniteAdeleRing (𝓞 F) F) ((1 : Matrix (Fin n) (Fin n) (AfE F E)) j i) := by
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]
  have key : (locM (conjPrime₂ P) z - 1) i j = adAt F (conjPrime₂ P) (Formalism.UG.sigR (CMData.sig hc) (FiniteAdeleRing (𝓞 F) F)
      (((z⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) j i - (1 : Matrix (Fin n) (Fin n) (AfE F E)) j i)) := by
    rw [map_sub, ← e, ← e1, map_sub, Matrix.sub_apply]
    simp [locM, Matrix.one_apply]
  have key2 : (locM P z⁻¹ - 1) j i = adAt F P
      (((z⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) j i - (1 : Matrix (Fin n) (Fin n) (AfE F E)) j i) := by
    rw [map_sub, Matrix.sub_apply]
    simp [locM, Matrix.one_apply]
  rw [key, valued_sigR, hcc]
  rw [key2] at h1
  exact h1

end Conj

section Small
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker Formalism.UG _root_.Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem val_lt_one_le {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

theorem dep_le {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (d : ℕ) :
    dep P d ≤ WithZero.exp (-(d : ℤ)) := by
  unfold dep
  rw [map_pow]
  calc _ ≤ (WithZero.exp (-1 : ℤ)) ^ d := pow_le_pow_left₀ zero_le' (val_lt_one_le val_qOf_lt) d
    _ = WithZero.exp (-(d : ℤ)) := by
      rw [← WithZero.exp_nsmul]
      congr 1
      simp

theorem mem_unitaryAdelic_of_mem_principalCongruence {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
    {n : ℕ} [NeZero n] {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {z : GL (Fin n) (AfE F E)} (hz : z ∈ K1 hc n ST SG) :
    z ∈ UAd hc n := by
  obtain ⟨⟨z', hz'⟩, -, rfl⟩ := hz
  exact hz'.1.1

theorem small_pair {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
    {n : ℕ} [NeZero n] {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {z : GL (Fin n) (AfE F E)} (hz : z ∈ K1 hc n ST SG)
    {P : HeightOneSpectrum (𝓞 E)} {d : ℕ} (h : Sm Valued.v (dep P d) (locM P z - 1)) :
    (Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM P z - 1) ∧ Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM P z⁻¹ - 1)) ∧
      (Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM (conjPrime₂ P) z - 1) ∧
        Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM (conjPrime₂ P) z⁻¹ - 1)) := by
  have hzU := mem_unitaryAdelic_of_mem_principalCongruence hz
  have hle := dep_le P d
  have hi : Sm Valued.v (dep P d) (locM P z⁻¹ - 1) := by
    have h0 : Sm Valued.v 1 (locM P z⁻¹) := fun i j => valuation_entries_le_one_of_mem_levelGroupOne (inv_mem hz) P i j
    have h1 := h0.mul h
    have e : locM P z⁻¹ * (locM P z - 1) = -(locM P z⁻¹ - 1) := by
      rw [Matrix.mul_sub, ← locM_mul, inv_mul_cancel, locM_one, Matrix.mul_one]
      abel
    rw [e, one_mul] at h1
    intro i j
    have := h1 i j
    rwa [Matrix.neg_apply, Valuation.map_neg] at this
  have h' : Sm Valued.v (dep P d) (locM P z⁻¹⁻¹ - 1) := by rw [inv_inv]; exact h
  refine ⟨⟨fun i j => (h i j).trans hle, fun i j => (hi i j).trans hle⟩, fun i j => (conj_small hzU hi i j).trans hle,
    fun i j => (conj_small (inv_mem hzU) h' i j).trans hle⟩

theorem comm_of_support {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    (Q : Finset (HeightOneSpectrum (𝓞 E))) {k z : GL (Fin n) (AfE F E)}
    (hk : ∀ w, w ∈ Q ∨ conjPrime₂ w ∈ Q → locM w k = 1) (hz : ∀ w, w ∉ Q → conjPrime₂ w ∉ Q → locM w z = 1) : z * k = k * z := by
  refine Units.ext (Matrix.ext fun i j => PtExist.ad_ext fun w => ?_)
  show locM w (z * k) i j = locM w (k * z) i j
  rw [locM_mul, locM_mul]
  by_cases h : w ∈ Q ∨ conjPrime₂ w ∈ Q
  · rw [hk w h, Matrix.one_mul, Matrix.mul_one]
  · rw [not_or] at h
    rw [hz w h.1 h.2, Matrix.one_mul, Matrix.mul_one]

end Small


set_option maxHeartbeats 800000 in
theorem approx_zero : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ (c : {c // A.chOf 0 c = β}) (x : TC.GA B (B.R.N 0)), x ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) → ∃ h : TC.GA B (B.R.N 0), h ∈ (A.K 0 (Nat.zero_le _) β).lev.U ∧ h ∈ Formalism.L2.Col.levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (Formalism.L2.Col.colLev I.Ch 0).grp ∧ ∃ q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0, TC.PtOf ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) β).y c).1) * (x * h) * TC.kStd X u (B.R.N 0)) q := by
  intro B X I hI hP l Z u a Ch A hA β hβ c x hx
  obtain ⟨c, rfl⟩ := c
  have hR := hA.reads 0 (Nat.zero_le _)
  have hpt := hR.pt c
  rw [hβ] at hpt
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hks := GlobalTheory.Mem.Col2.MemChart.kStd_spec hPr u (B.R.N 0)
  obtain ⟨p0, hp0, -⟩ := hks.1
  have hTw := (GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away I hI).2 u a
  have hsp := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 0 (Nat.zero_le _)
  have hcc : ∀ P : HeightOneSpectrum (𝓞 B.host.E), Formalism.L2.Col.conjPrime₂ (Formalism.L2.Col.conjPrime₂ P) = P := fun P => by
    ext b
    rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]
  have hkT : ∀ w : HeightOneSpectrum (𝓞 B.host.E), w ∈ I.Q a ∨ Formalism.L2.Col.conjPrime₂ w ∈ I.Q a →
      GlobalTheory.Mem.ColAd.locM w (TC.kStd X u (B.R.N 0)) = 1 := by
    intro w hw
    have hT : (B.T u : 𝓞 B.host.F) ∉ (w.under (𝓞 B.host.F)).asIdeal := by
      rcases hw with hw | hw
      · exact (hTw w hw).2.2
      · have e : (Formalism.L2.Col.conjPrime₂ w).under (𝓞 B.host.F) = w.under (𝓞 B.host.F) :=
          (GlobalTheory.Mem.Col2.under_eq_iff B.host w _).2 (Or.inr rfl)
        have := (hTw _ hw).2.2
        rwa [e] at this
    exact GlobalTheory.Mem.Col2.TopPtModel.adAt_of_prV w (hks.2.1 _ hT)
  obtain ⟨d, hd⟩ := GlobalTheory.T.stepLevel_contains_unitary_near_one (A.K 0 (Nat.zero_le _) (A.chOf 0 c)).lev (I.Q a ∪ (I.Q a).image Formalism.L2.Col.conjPrime₂)
  generalize TC.kStd X u (B.R.N 0) = k at hpt hks hp0 hkT ⊢
  have hkU : k ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := hp0.1
  have hykU : (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * k ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := hpt.1
  have hyU : (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := by
    have := mul_mem hykU (inv_mem hkU)
    rwa [mul_inv_cancel_right] at this
  have hg : (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * x * k ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := mul_mem (mul_mem hyU hx) hkU
  obtain ⟨z, hz, hsm, hsupp, p, hp⟩ := exists_K1_element_local_support _ _ B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs
    (I.Q a) (fun P hP => (hTw P hP).1) ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * x * k) hg d
  have hzU : z ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := mem_unitaryAdelic_of_mem_principalCongruence hz
  have hcomm : z * k = k * z := comm_of_support (I.Q a) hkT hsupp
  refine ⟨z, hd z ?_ ?_ ?_, Formalism.L2.Col.kOne_le_unipotentLevel _ _ _ _ _ hz, p, ?_⟩
  · rw [hsp.1]
    exact hzU
  · intro w hw
    exact hsupp w (fun h => hw (Finset.mem_union_left _ h))
      (fun h => hw (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, h, hcc w⟩)))
  · intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · exact (small_pair hz (hsm ⟨w, hw⟩)).1
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hw
      exact (small_pair hz (hsm ⟨P, hP⟩)).2
  · have e : (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * (x * z) * k = (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * x * k * z :=
      (mul_assoc (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) (x * z) k).trans ((congrArg ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * ·) ((mul_assoc x z k).trans ((congrArg (x * ·) hcomm).trans
        (mul_assoc x k z).symm))).trans ((mul_assoc (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) (x * k) z).symm.trans (congrArg (· * z) (mul_assoc (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) x k).symm)))
    show TC.PtOf ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * (x * z) * k) p
    rw [e]
    exact hp

end GlobalTheory.ApproxZero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroApproximationTwistPrimesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZero_approximation_twistPrimes : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ (c : {c // A.chOf 0 c = β}) (x : TC.GA B (B.R.N 0)), x ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) → ∃ h : TC.GA B (B.R.N 0), h ∈ (A.K 0 (Nat.zero_le _) β).lev.U ∧ h ∈ Formalism.L2.Col.levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (Formalism.L2.Col.colLev I.Ch 0).grp ∧ ∃ q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0, TC.PtOf ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) β).y c).1) * (x * h) * TC.kStd X u (B.R.N 0)) q := by
  first | exact @GlobalTheory.ApproxZero.approx_zero | exact GlobalTheory.ApproxZero.approx_zero | (intros; apply GlobalTheory.ApproxZero.approx_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroChartLevelStandardBasePointEqMember
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ZeroLevel

open _root_.Formalism.L2.Col _root_.Formalism.L2.Ker Formalism.UG GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)

theorem stepZeroReduction_of_moved_representative (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (y : TC.GA B (B.R.N 0))
    (hy : TC.PtOf (y * TC.kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1)) (x : TC.GA B (B.R.N 0))
    (κ : (I.stp u a 0).G c.1) (h1 : (I.stp u a 0).gam c.1 κ = 1)
    (h2 : TC.PtOf (y * x * TC.kStd X u (B.R.N 0)) ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1) :
    ∃ hJ : x ∈ Formalism.L2.Col.J0 B.sp.cm (B.R.N 0) ((B.primes X).vT u),
      Formalism.L2.Col.redG B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs ⟨x, hJ⟩ = κ.2.1.1⁻¹ := by
  have hg := dia_of_pt hPr u hy
  have hx := dia_of_pt hPr u h2
  have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N 0) (h1.trans (map_one _).symm)
  exact red_of_act B.sp.cm (B.R.N 0) (Formalism.L2.Col.diaT (Pr := B.primes X) u) hg.1 hx.1 κ.2.1.1 (by
    rw [hg.2, hx.2]
    show ((κ.1, κ.2.1.1) : Formalism.L2.Col.UF B.fields.E (B.R.N 0) × Formalism.L2.Col.GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) • _ = _
    rw [e1]
    rfl)

theorem stepZeroColumnLevel_eq_orbitStabilizer (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (y : TC.GA B (B.R.N 0))
    (hy : TC.PtOf (y * TC.kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1)) (x : TC.GA B (B.R.N 0))
    (q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0) (h : TC.PtOf (y * x * TC.kStd X u (B.R.N 0)) q) :
    x ∈ Formalism.L2.Col.levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (Formalism.L2.Col.colLev I.Ch 0).grp ↔
      ∃ κ : (I.stp u a 0).G c.1, (I.stp u a 0).gam c.1 κ = 1 ∧ ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1 = q ∧
        cosetIn ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)) = cosetIn ((I.stp u a 0).rep c) := by
  have hL := hI.idx_ok a
  have hy' := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  have hg := dia_of_pt hPr u hy
  have hx := dia_of_pt hPr u h
  constructor
  · intro hxU
    have h1 := act_of_mem B.sp.cm (B.R.N 0) _ (Formalism.L2.Col.diaT (Pr := B.primes X) u) hg.1 ⟨x, hxU⟩
    rw [hg.2, hx.2] at h1
    obtain ⟨p, hp⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) q
    obtain ⟨g, h2, h3⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy' hΛ hΘ c.1 ((I.stp u a 0).rep c) p
      (1, (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x, hxU⟩)⁻¹) (by rw [hp]; exact h1.symm)
    refine ⟨g, ?_, ?_, Chart0.cos0 I _ _⟩
    · show Formalism.L2.Col.ufGL B.fields.E (B.R.N 0) g.1 = 1
      rw [show g.1 = 1 from congrArg Prod.fst h2, map_one]
    · exact (congrArg (fun p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => p.1.1) h3).trans hp
  · rintro ⟨κ, h1, h2, -⟩
    obtain ⟨hJ, hr⟩ := stepZeroReduction_of_moved_representative I hPr u a c y hy x κ h1 (h2 ▸ h)
    refine (Formalism.L2.Col.mem_levU _ _ _ _ _).2 ⟨hJ, ?_⟩
    have key : ∀ (Λ' : Formalism.L2.Col.LevFam B.fields.E B.fields.K (B.R.N 0) (B.primes X).vGs), Λ' = Formalism.L2.Col.colLev I.Ch 0 →
        ∀ g : Λ'.grp, g.1 ∈ (Formalism.L2.Col.colLev I.Ch 0).grp := by
      rintro _ rfl g
      exact g.2
    have hm : κ.2.1.1 ∈ (Formalism.L2.Col.colLev I.Ch 0).grp := key _ (hΛ c.1) κ.2.1
    rw [hr]
    exact inv_mem hm

end GlobalTheory.ZeroLevel

noncomputable section
namespace GlobalTheory.ZeroLevel
open _root_.Formalism.L2.Col _root_.Formalism.L2.Ker Formalism.UG GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)


set_option maxHeartbeats 2000000 in
theorem right_lev (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z))
    (hC : I.StdC l Z C) (u : B.Word) (x : TC.GA B (B.R.N 0)) :
    x ∈ (C.forms u).to0.cls0.lev.U ↔
      x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp := by
  have hPr := l.pr
  obtain ⟨k, hR⟩ := (hC u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hyE := (hC u).yE 0 (Nat.zero_le _) (Or.inl rfl)
  obtain ⟨c, -⟩ := hR.onto ()
  haveI : NeZero (B.R.N 0) := ⟨(B.R.N_pos 0).ne'⟩
  have hQ : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
  obtain ⟨p0, hp0, -⟩ := hR.k_std ()
  have hk : k () ∈ UAd B.sp.cm (B.R.N 0) := hp0.uni
  have h1 : TC.PtOf (I.yStd u 0 c * k ()) ((I.stp u I.mu0 0).rep c).1.1 := by
    have := hR.pt c
    rw [hyE c] at this
    exact GlobalTheory.Mem.SRe.StdUnique.pt_of_deco hQ (extTo_deco _ _).symm this
  have h2 : TC.PtOf (I.yStd u 0 c * TC.kStd X u (B.R.N 0)) ((I.stp u I.mu0 0).rep c).1.1 :=
    GlobalTheory.Mem.SRe.StdUnique.pt_of_deco hQ (extTo_deco _ _).symm (yStd_spec I hI u 0 c)
  have key : x ∈ UAd B.sp.cm (B.R.N 0) → (x ∈ (C.forms u).to0.cls0.lev.U ↔
      x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp) := by
    intro hx
    have hg : I.yStd u 0 c * x * k () ∈ UAd B.sp.cm (B.R.N 0) := by
      have e : I.yStd u 0 c * x * k () = (I.yStd u 0 c * k ()) * ((k ())⁻¹ * x * k ()) := by group
      rw [e]
      exact mul_mem h1.uni (mul_mem (mul_mem (inv_mem hk) hx) hk)
    obtain ⟨q, hq⟩ := GlobalTheory.Mem.Col2.ChiFinTop.exists_isPtOf_of_mem (ST := (B.primes X).vT u) (SG := (B.primes X).vGs)
      (Q := QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) B.sp.cm hQ hg
    have hq' : TC.PtOf (I.yStd u 0 c * x * TC.kStd X u (B.R.N 0)) q := by
      have e : I.yStd u 0 c * x * TC.kStd X u (B.R.N 0) =
          I.yStd u 0 c * x * k () * ((I.yStd u 0 c * k ())⁻¹ * (I.yStd u 0 c * TC.kStd X u (B.R.N 0))) := by group
      rw [e]
      exact GlobalTheory.Mem.Col2.PtStab.isPtOf_mul_stab _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 hq
    have a1 := hR.lev c x q (by rw [hyE c]; exact hq)
    exact a1.trans (Chart0.lev0 I hI hPr u I.mu0 c x q hq').symm
  constructor
  · intro hx
    exact (key (GlobalTheory.Mem.SRe.StdUnique.lev_le I l hI hP Z u 0 _ _ hx)).1 hx
  · intro hx
    exact (key (levU_le_UAd _ _ _ _ _ hx)).2 hx


set_option maxHeartbeats 2000000 in
theorem left_lev (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type)
    (A : GlobalTheory.AdForm.TwDat I l Z u a Ch) (hA : A.Is) (β : Ch 0) (hβ : A.kb 0 β = TC.kStd X u (B.R.N 0)) (x : TC.GA B (B.R.N 0)) :
    x ∈ (A.K 0 (Nat.zero_le _) β).lev.U ↔
      x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp := by
  have hPr := l.pr
  have hR := hA.reads 0 (Nat.zero_le _)
  obtain ⟨c, rfl⟩ := hA.chOf_onto 0 (Nat.zero_le _) β
  have hy : TC.PtOf ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * TC.kStd X u (B.R.N 0))
      (extTo I.SQ ((I.stp u a 0).rep c).1.1) := by
    have := hR.pt c
    rw [hβ] at this
    exact this
  have rat : ∀ (x : TC.GA B (B.R.N 0)) (q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0), TC.PtOf ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * x * TC.kStd X u (B.R.N 0)) q →
      (x ∈ (A.K 0 (Nat.zero_le _) (A.chOf 0 c)).lev.U ↔
        x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp) := fun x q h =>
    (hR.lev c x q (by rw [hβ]; exact h)).trans (stepZeroColumnLevel_eq_orbitStabilizer I hI hPr u a c _ hy x q h).symm
  have hg1 : gramN (I.rec7 l Z) 0 (Nat.zero_le _) = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 0 (Nat.zero_le _)).1
  have eU : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      UAd B.sp.cm (B.R.N 0) := by rw [hg1]; rfl
  have hUl : ∀ x, x ∈ (A.K 0 (Nat.zero_le _) (A.chOf 0 c)).lev.U → x ∈ UAd B.sp.cm (B.R.N 0) := fun x hx =>
    eU ▸ (((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).lev.U_eq x).1 hx).1
  constructor
  · intro hx
    obtain ⟨h, h1, h2, q, hq⟩ := GlobalTheory.T.stepZero_approximation_twistPrimes I hI hP l Z u a Ch A hA (A.chOf 0 c) hβ ⟨c, rfl⟩ x (hUl x hx)
    have e := (rat _ q hq).1 (mul_mem hx h1)
    have e2 := mul_mem e (inv_mem h2)
    rwa [mul_inv_cancel_right] at e2
  · intro hx
    obtain ⟨h, h1, h2, q, hq⟩ := GlobalTheory.T.stepZero_approximation_twistPrimes I hI hP l Z u a Ch A hA (A.chOf 0 c) hβ ⟨c, rfl⟩ x (levU_le_UAd _ _ _ _ _ hx)
    have e := (rat _ q hq).2 (mul_mem hx h2)
    have e2 := mul_mem e (inv_mem h1)
    rw [show x = x * h * h⁻¹ from (mul_inv_cancel_right x h).symm]
    exact e2


set_option maxHeartbeats 2000000 in
theorem lev_zero_std : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ x, x ∈ (A.K 0 (Nat.zero_le _) β).lev.U ↔ x ∈ (C.forms u).to0.cls0.lev.U := by
  intro B X I hI hP l Z C hC u a Ch A hA β hβ x
  exact (left_lev I hI hP l Z u a Ch A hA β hβ x).trans (right_lev I hI hP l Z C hC u x).symm

end GlobalTheory.ZeroLevel
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroChartLevelStandardBasePointEqMemberStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroChartLevel_standardBasePoint_eq_member : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ x, x ∈ (A.K 0 (Nat.zero_le _) β).lev.U ↔ x ∈ (C.forms u).to0.cls0.lev.U := by
  first | exact @GlobalTheory.ZeroLevel.lev_zero_std | exact GlobalTheory.ZeroLevel.lev_zero_std | (intros; apply GlobalTheory.ZeroLevel.lev_zero_std <;> assumption)
end
