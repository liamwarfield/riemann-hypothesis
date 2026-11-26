module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointLatticeIffBaseLatticeDecorated
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicTwistDiagonalAtPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyFinOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelSmallerAtFinitePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelSmallerAtFinitePlaces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLevelShrink

theorem isCompact_of_isOpen_subgroupOf {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (H U A : Subgroup G) (hAU : A ≤ U) (hUH : U ≤ H) (hU : IsCompact (U : Set G))
    (hA : IsOpen {x : H | (x : G) ∈ A}) : IsCompact (A : Set G) := by
  haveI : ContinuousMul H := inferInstanceAs (ContinuousMul H.toSubmonoid)
  have hcl : IsClosed ((A.subgroupOf H : Subgroup H) : Set H) := Subgroup.isClosed_of_isOpen _ hA
  have hU' : IsCompact (Subtype.val ⁻¹' (U : Set G) : Set H) := by
    rw [Subtype.isCompact_iff]
    convert hU using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hUH hx⟩, hx, rfl⟩
  have h2 := hU'.inter_right hcl
  rw [Subtype.isCompact_iff] at h2
  convert h2 using 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, hUH (hAU hx)⟩, ⟨hAU hx, hx⟩, rfl⟩
  · rintro ⟨y, ⟨_, hy⟩, rfl⟩
    exact hy

end GlobalTheory.StepLevelShrink

namespace GlobalTheory.StepLevelShrink

theorem exists_stepLevel_shrink : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Qv : Finset (HeightOneSpectrum (𝓞 F))) (A : Subgroup (GL (Fin n) (AfE F E))) (ψ : A →* ℂˣ), A ≤ S.U → (∀ v ∈ Qv, (T : 𝓞 F) ∉ v.asIdeal) → (∀ x ∈ S.U, (∀ v ∈ Qv, ∃ x' ∈ A, bc (prV (E := E) v) x = bc (prV (E := E) v) x') → x ∈ A) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ A}) → (∀ x : A, (∀ v ∈ Qv, bc (prV (E := E) v) x.1 = 1) → ψ x = 1) → ∃ L : StepLevel F E σ J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))), L.Lb = S.Lb ∧ L.U = A ∧ (∀ v, v ∉ Qv → L.Uloc v = S.Uloc v) ∧ ∀ (x : L.U) (x' : S.U) (x'' : A), x.1 = x'.1 → x.1 = x''.1 → L.chi x = S.chi x' * ψ x'' := by
  intro F E _ _ _ _ _ σ n J T f bad S Qv A ψ hAU hQT hloc hopen hψ
  classical
  have hSU : ∀ y ∈ S.U, y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) y ∈ S.Uloc v :=
    fun y hy => (S.U_eq y).1 hy
  let L : StepLevel F E σ J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))) :=
    { Lb := S.Lb
      Lb_fin := S.Lb_fin
      Lb_span := S.Lb_span
      Lb_int := S.Lb_int
      Lb_dual := S.Lb_dual
      Lb_index := S.Lb_index
      Uloc := fun v => if v ∈ Qv then A.map (bc (prV (E := E) v)) else S.Uloc v
      Uloc_le := by
        intro v
        by_cases hq : v ∈ Qv
        · rw [if_pos hq]
          rintro _ ⟨y, hy, rfl⟩
          exact S.Uloc_le v ((hSU y (hAU hy)).2 v)
        · rw [if_neg hq]
          exact S.Uloc_le v
      Uloc_lev := by
        intro v
        by_cases hq : v ∈ Qv
        · rw [if_pos hq]
          rintro _ ⟨y, hy, rfl⟩
          exact S.Uloc_lev v ((hSU y (hAU hy)).2 v)
        · rw [if_neg hq]
          exact S.Uloc_lev v
      Uloc_hyp := by
        intro v hv hT
        have hb : v ∉ bad := fun h => hv (Or.inl h)
        have hq : v ∉ Qv := fun h => hv (Or.inr (Finset.mem_coe.2 h))
        simp only [if_neg hq]
        exact S.Uloc_hyp v hb hT
      fM := S.fM
      fM_acg := S.fM_acg
      fM_mod := S.fM_mod
      fT := S.fT
      fT_ne := S.fT_ne
      fT_T := S.fT_T
      fM_card := S.fM_card
      fT_L := S.fT_L
      UlocAlt := by
        intro v h
        have hq : v ∉ Qv := fun hq => hQT v hq h
        simp only [if_neg hq]
        exact S.UlocAlt v h
      U := A
      U_eq := by
        intro x
        constructor
        · intro hx
          refine ⟨(hSU x (hAU hx)).1, fun v => ?_⟩
          by_cases hq : v ∈ Qv
          · simp only [if_pos hq]
            exact ⟨x, hx, rfl⟩
          · simp only [if_neg hq]
            exact (hSU x (hAU hx)).2 v
        · rintro ⟨hP, hv⟩
          have hxS : x ∈ S.U := by
            refine (S.U_eq x).2 ⟨hP, fun v => ?_⟩
            have h1 := hv v
            by_cases hq : v ∈ Qv
            · simp only [if_pos hq] at h1
              obtain ⟨y, hy, hyx⟩ := h1
              rw [← hyx]
              exact (hSU y (hAU hy)).2 v
            · simp only [if_neg hq] at h1
              exact h1
          refine hloc x hxS fun v hq => ?_
          have h1 := hv v
          simp only [if_pos hq] at h1
          obtain ⟨y, hy, hyx⟩ := h1
          exact ⟨y, hy, hyx.symm⟩
      U_compact := by
        letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
        letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Algebra.TensorProduct.rightAlgebra
        haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
        let c : (FiniteAdeleRing (𝓞 F) F ⊗[F] E) →ₗ[FiniteAdeleRing (𝓞 F) F]
            (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
          { toFun := TensorProduct.comm F _ _
            map_add' := map_add _
            map_smul' := by
              intro a x
              induction x using TensorProduct.induction_on with
              | zero => simp
              | tmul b e =>
                simp only [TensorProduct.smul_tmul', TensorProduct.comm_tmul, RingHom.id_apply]
                change e ⊗ₜ[F] (a * b) = ((1 : E) ⊗ₜ[F] a) * (e ⊗ₜ[F] b)
                rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
              | add x y hx hy => simp [smul_add, hx, hy] }
        haveI : Module.Finite (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
          Module.Finite.of_surjective c (TensorProduct.comm F _ _).surjective
        haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
        haveI : IsTopologicalRing (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
          IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) _
        exact isCompact_of_isOpen_subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)) S.U A hAU
          (fun y hy => (hSU y hy).1) S.U_compact hopen
      U_open := hopen
      chi := (S.chi.comp (Subgroup.inclusion hAU)) * ψ
      chi_triv := by
        intro x hx
        rw [MonoidHom.mul_apply, MonoidHom.comp_apply,
          S.chi_triv (Subgroup.inclusion hAU x) (fun v hv => hx v (Or.inl hv)),
          hψ x (fun v hv => hx v (Or.inr (Finset.mem_coe.2 hv))), one_mul] }
  refine ⟨L, rfl, rfl, fun v hv => by
    show (if v ∈ Qv then A.map (bc (prV (E := E) v)) else S.Uloc v) = S.Uloc v
    exact if_neg hv, ?_⟩
  intro x x' x'' h1 h2
  show S.chi (Subgroup.inclusion hAU x) * ψ x = S.chi x' * ψ x''
  have e1 : Subgroup.inclusion hAU x = x' := Subtype.ext h1
  have e2 : x = x'' := Subtype.ext h2
  rw [e1, e2]

end GlobalTheory.StepLevelShrink
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelSmallerAtFinitePlacesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stepLevel_smaller_at_finite_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Qv : Finset (HeightOneSpectrum (𝓞 F))) (A : Subgroup (GL (Fin n) (AfE F E))) (ψ : A →* ℂˣ), A ≤ S.U → (∀ v ∈ Qv, (T : 𝓞 F) ∉ v.asIdeal) → (∀ x ∈ S.U, (∀ v ∈ Qv, ∃ x' ∈ A, bc (prV (E := E) v) x = bc (prV (E := E) v) x') → x ∈ A) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ A}) → (∀ x : A, (∀ v ∈ Qv, bc (prV (E := E) v) x.1 = 1) → ψ x = 1) → ∃ L : StepLevel F E σ J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))), L.Lb = S.Lb ∧ L.U = A ∧ (∀ v, v ∉ Qv → L.Uloc v = S.Uloc v) ∧ ∀ (x : L.U) (x' : S.U) (x'' : A), x.1 = x'.1 → x.1 = x''.1 → L.chi x = S.chi x' * ψ x'' := by
  first | exact @GlobalTheory.StepLevelShrink.exists_stepLevel_shrink | exact GlobalTheory.StepLevelShrink.exists_stepLevel_shrink | (intros; apply GlobalTheory.StepLevelShrink.exists_stepLevel_shrink <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QbKLeLocLev
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct Topology

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
attribute [local instance] rlt_top rlt_topRing

namespace GlobalTheory.Mem.Col2.TopCh

section Nhd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_nhds (P : HeightOneSpectrum (𝓞 E)) {c : E} (hc : c ≠ 0) :
    ∀ᶠ y in 𝓝 (0 : AfE F E), ∃ z ∈ P.adicCompletionIntegers E, adAt F P y = algebraMap E (P.adicCompletion E) c * z := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) c
  have hb0 : algebraMap (𝓞 E) E b ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hb
  have ha0 : algebraMap (𝓞 E) E a ≠ 0 := fun h => hc (by rw [h, zero_div])
  set A : AfE F E := inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a) with hA
  set B : AfE F E := inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a)⁻¹ with hB
  have hAB : A * B = 1 := by
    rw [hA, hB, ← map_mul, mul_inv_cancel₀ ha0, map_one]
  have hop : IsOpen ((fun y : AfE F E => B * y) ⁻¹' (Formalism.L2.Herm.intAf F E : Set (AfE F E))) :=
    rlt_isOpen_intAf.preimage (continuous_const.mul continuous_id)
  have h0 : (0 : AfE F E) ∈ (fun y : AfE F E => B * y) ⁻¹' (Formalism.L2.Herm.intAf F E : Set (AfE F E)) := by
    simp
  filter_upwards [hop.mem_nhds h0] with y hy
  have hw : ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (afIso F E (B * y) Q) ≤ 1 := (mem_rInt_iff F E (B * y)).1 hy
  have hy' : y = A * (B * y) := by rw [← mul_assoc, hAB, one_mul]
  refine ⟨algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E b) * adAt F P (B * y), ?_, ?_⟩
  · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    rw [map_mul]
    exact mul_le_one' (by rw [valued_algebraMap]; exact P.valuation_le_one b) (by rw [adAt_apply]; exact hw P)
  · have e : adAt F P y = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E a) * adAt F P (B * y) := by
      conv_lhs => rw [hy', map_mul, hA, adAt_inclE]
    rw [e, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hb0]

variable {n : ℕ}

theorem bc_adAt_sub (P : HeightOneSpectrum (𝓞 E)) (w : GL (Fin n) (AfE F E)) (i j : Fin n) :
    ((rhoP F P w : GL (Fin n) (P.adicCompletion E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E)) i j -
      (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) i j =
    adAt F P ((w : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
  have e : ((rhoP F P w : GL (Fin n) (P.adicCompletion E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E)) i j =
      adAt F P ((w : Matrix (Fin n) (Fin n) (AfE F E)) i j) := rfl
  rw [e, map_sub, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem int_of_sub {P : HeightOneSpectrum (𝓞 E)} {A : Matrix (Fin n) (Fin n) (P.adicCompletion E)}
    (h : ∀ i j, A i j - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) i j ∈ P.adicCompletionIntegers E) : qbInt A := fun i j => by
  have := Subring.add_mem _ (h i j) (qbInt_one (v := P) (F := E) (n := n) i j)
  simpa using this

theorem eventually_localComponent_mem (P : HeightOneSpectrum (𝓞 E)) {c : E} (hc : c ≠ 0) :
    ∀ᶠ u : GL (Fin n) (AfE F E) in 𝓝 1, rhoP F P u ∈ qbK (algebraMap E (P.adicCompletion E) c) := by
  have hval : ∀ (c' : E), c' ≠ 0 → ∀ i j : Fin n, ∀ᶠ u : GL (Fin n) (AfE F E) in 𝓝 1, ∃ z ∈ P.adicCompletionIntegers E,
      adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        algebraMap E (P.adicCompletion E) c' * z := by
    intro c' hc' i j
    have hcont : Continuous fun u : GL (Fin n) (AfE F E) =>
        (u : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j :=
      (Units.continuous_val.matrix_elem i j).sub continuous_const
    have ht := hcont.tendsto 1
    simp only [Units.val_one, sub_self] at ht
    exact ht.eventually (adAt_nhds P hc')
  have hinv : ∀ i j : Fin n, ∀ᶠ u : GL (Fin n) (AfE F E) in 𝓝 1, ∃ z ∈ P.adicCompletionIntegers E,
      adAt F P (((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        algebraMap E (P.adicCompletion E) 1 * z := by
    intro i j
    have ht : Filter.Tendsto (fun u : GL (Fin n) (AfE F E) => u⁻¹) (𝓝 1) (𝓝 1) := by
      have hc : Continuous (fun u : GL (Fin n) (AfE F E) => u⁻¹) :=
        Units.continuous_iff.2 ⟨Units.continuous_coe_inv, Units.continuous_val⟩
      have h := hc.tendsto 1
      rwa [inv_one] at h
    exact ht.eventually (hval 1 one_ne_zero i j)
  have h1 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hval c hc i j
  have h2 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hval 1 one_ne_zero i j
  have h3 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hinv i j
  filter_upwards [h1, h2, h3] with u a1 a2 a3
  refine ⟨int_of_sub fun i j => ?_, int_of_sub fun i j => ?_, fun i j => ?_⟩
  · obtain ⟨z, hz, e⟩ := a2 i j
    rw [bc_adAt_sub, e, map_one, one_mul]
    exact hz
  · obtain ⟨z, hz, e⟩ := a3 i j
    rw [← map_inv, bc_adAt_sub, e, map_one, one_mul]
    exact hz
  · obtain ⟨z, hz, e⟩ := a1 i j
    exact ⟨z, hz, by rw [Matrix.sub_apply, bc_adAt_sub, e]⟩

theorem rhoT_nhds (P : HeightOneSpectrum (𝓞 E)) (t : GL (Fin n) (AfE F E)) {c : E} (hc : c ≠ 0) :
    ∀ᶠ x : GL (Fin n) (AfE F E) in 𝓝 1, rhoT F P t x ∈ qbK (algebraMap E (P.adicCompletion E) c) := by
  have hcont : Continuous fun x : GL (Fin n) (AfE F E) => t⁻¹ * x * t⁻¹⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have ht := hcont.tendsto 1
  simp only [mul_one, inv_inv, inv_mul_cancel] at ht
  exact ht.eventually (eventually_localComponent_mem P hc)

end Nhd

theorem qbK_le_locLev {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
    (Θ : LevI E K n P) (d : E) : qbK (algebraMap E (P.adicCompletion E) d) ≤ locLev P Θ d := fun k hk =>
  ⟨hk.1, hk.2.1, 1, Θ.H.one_mem, by simpa using hk⟩

theorem topU_open : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (Q : Finset (HeightOneSpectrum (𝓞 E))) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E), (∀ P, d P ≠ 0) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ U}) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ topU U t Θ d}) := by
  intro F E K _ _ _ _ _ _ _ σ n J Q U t Θ d hd hU
  have hW : ∀ P : Q, IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) |
      (x : GL (Fin n) (AfE F E)) ∈ (locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t)} := by
    intro P
    let W : Subgroup (UPts σ J (FiniteAdeleRing (𝓞 F) F)) :=
      ((locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))
    have hn : (W : Set (UPts σ J (FiniteAdeleRing (𝓞 F) F))) ∈ 𝓝 (1 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) := by
      have ht : Filter.Tendsto (fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => (x : GL (Fin n) (AfE F E))) (𝓝 1) (𝓝 1) :=
        continuous_subtype_val.tendsto 1
      filter_upwards [ht.eventually (rhoT_nhds P.1 t (hd P))] with x hx
      exact qbK_le_locLev P.1 (Θ P) (d P) hx
    exact Subgroup.isOpen_of_mem_nhds W hn
  have e : {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL (Fin n) (AfE F E)) ∈ topU U t Θ d} =
      {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL (Fin n) (AfE F E)) ∈ U} ∩
        ⋂ P : Q, {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) |
          (x : GL (Fin n) (AfE F E)) ∈ (locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t)} := by
    ext x
    simp only [topU, Subgroup.mem_inf, Subgroup.mem_iInf, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  exact hU.inter (isOpen_iInter_of_finite hW)

end GlobalTheory.Mem.Col2.TopCh

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartFromAdelicDictionary
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem localComponent_congr {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)} (hP : P.under (𝓞 F) = v)
    {x x' : GL (Fin n) (AfE F E)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') : rhoP F P x = rhoP F P x' := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have h0 : prV (E := E) v ((x : Matrix (Fin n) (Fin n) (AfE F E)) i j) = prV (E := E) v ((x' : Matrix (Fin n) (Fin n) (AfE F E)) i j) :=
    congrArg (fun g : GL (Fin n) (E ⊗[F] v.adicCompletion F) => (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j) h
  have h1 : prV (E := E) v ((x : Matrix (Fin n) (Fin n) (AfE F E)) i j - (x' : Matrix (Fin n) (Fin n) (AfE F E)) i j) = 0 := by
    rw [map_sub, h0, sub_self]
  have h2 := (GlobalTheory.T.placeProjection_zero_integral_iff_components_above F E v _).1.1 h1 P hP
  rw [map_sub, sub_eq_zero] at h2
  exact h2

end SlopeTestRemainingChoices

section Dense

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
  {hc : CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem valuation_entries_le_one_of_mem_levelGroupOne {z : GL (Fin n) (AfE F E)} (hz : z ∈ K1 hc n ST SG) (P : HeightOneSpectrum (𝓞 E)) (i j : Fin n) :
    Valued.v (adAt F P ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1 := by
  obtain ⟨y, hy, -⟩ := St_one_int (congruence_subgroup_le_stabilizer hc n ST (principal_le_congruence_subgroup hc n ST SG hz))
  rw [hy]
  exact (mem_rInt_iff F E _).1 (y i j).2 P

theorem rhoP_mem_qbK {z : GL (Fin n) (AfE F E)} (hz : z ∈ K1 hc n ST SG) (P : HeightOneSpectrum (𝓞 E)) {c : E} (h0 : c ≠ 0)
    (hs : Sm Valued.v (P.valuation E c) (locM P z - 1)) : rhoP F P z ∈ qbK (algebraMap E (P.adicCompletion E) c) := by
  have hc0 : algebraMap E (P.adicCompletion E) c ≠ 0 := by
    simpa using h0
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · exact valuation_entries_le_one_of_mem_levelGroupOne hz P i j
  · rw [← map_inv]
    exact valuation_entries_le_one_of_mem_levelGroupOne (inv_mem hz) P i j
  · refine ⟨(locM P z - 1) i j / algebraMap E (P.adicCompletion E) c, ?_, ?_⟩
    · show Valued.v ((locM P z - 1) i j / algebraMap E (P.adicCompletion E) c) ≤ 1
      rw [map_div₀, valued_algebraMap]
      exact div_le_one_of_le₀ (hs i j) zero_le'
    · rw [mul_div_cancel₀ _ hc0]
      rfl

theorem topU_dense {U : Subgroup (GL (Fin n) (AfE F E))} {Λ : LevFam E K n SG} {Θ : LevQFam E K n Q} {d : Q → E} {k t : GL (Fin n) (AfE F E)}
    (e : ℕ) (hd : ∀ P, d P ≠ 0) (hQ : ∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q)
    (hdq : ∀ P : Q, d P = ((qOf P.1 : ℕ) : E) ^ e) (hk : k ∈ UAd hc n) (hrk : ∀ P : Q, rhoP F P.1 k = 1) (ht : t ∈ K1 hc n ST SG)
    (hU : ∀ x ∈ UAd hc n, x ∈ U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) :
    ∀ g ∈ UAd hc n, ∃ x ∈ topU U t Θ d, ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * x * (k * t)) p := by
  intro g hg
  have hkt : k * t ∈ UAd hc n := mul_mem hk (principal_le_adelic_unitary hc n ST SG ht)
  obtain ⟨z, hz, hsm, p, hp⟩ := GlobalTheory.T.exists_K1_point_congruent F E hc n ST SG Q hQ (g * (k * t)) (mul_mem hg hkt) e
  have hzU := principal_le_adelic_unitary hc n ST SG hz
  refine ⟨(k * t) * z * (k * t)⁻¹, ?_, p, ?_⟩
  change (k * t) * z * (k * t)⁻¹ ∈ U ∧ _
  constructor
  · refine (hU _ (mul_mem (mul_mem hkt hzU) (inv_mem hkt))).2 ?_
    have e1 : k⁻¹ * ((k * t) * z * (k * t)⁻¹) * k = t * z * t⁻¹ := by group
    rw [e1]
    have hle := kOne_le_unipotentLevel hc n ST SG Λ.grp
    exact mul_mem (mul_mem (hle ht) (hle hz)) (inv_mem (hle ht))
  · refine Subgroup.mem_iInf.2 fun P => ?_
    have e2 : rhoT F P.1 t ((k * t) * z * (k * t)⁻¹) = rhoP F P.1 z := by
      have e3 : t⁻¹ * ((k * t) * z * (k * t)⁻¹) * t⁻¹⁻¹ = t⁻¹ * k * t * z * t⁻¹ * k⁻¹ * t := by group
      show rhoP F P.1 (t⁻¹ * ((k * t) * z * (k * t)⁻¹) * t⁻¹⁻¹) = _
      rw [e3]
      simp only [map_mul, map_inv, hrk P, inv_one, mul_one, inv_mul_cancel, one_mul, mul_inv_cancel_right]
      group
    refine Subgroup.mem_comap.2 ?_
    rw [e2]
    refine qbK_le_locLev P.1 (Θ P) (d P) (rhoP_mem_qbK hz P.1 (hd P) ?_)
    rw [hdq P]
    exact hsm P
  · have e4 : g * ((k * t) * z * (k * t)⁻¹) * (k * t) = g * (k * t) * z := by group
    rw [e4]
    exact hp

end Dense


set_option maxHeartbeats 1000000 in
theorem exists_clsG_top : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E hc.sig J T f bad) (Qv : Finset (HeightOneSpectrum (𝓞 F))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (e : ℕ) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (k t : GL (Fin n) (AfE F E)) (C : Type) (s : C → DecoF E n ST SG Q) (y : C → GL (Fin n) (AfE F E)) (stab : C → Type) [∀ c, Group (stab c)] (lat : C → Submodule (𝓞 E) (Fin n → E)) (gm : ∀ c, stab c →* UF E n) (ψ : topU S.U t Θ d →* ℂˣ), J = 1 → (∀ v, v ∈ Qv ↔ ∃ P ∈ Q, P.under (𝓞 F) = v) → (∀ v ∈ Qv, (T : 𝓞 F) ∉ v.asIdeal) → (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → (∀ P : Q, d P = ((qOf P.1 : ℕ) : E) ^ e) → k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ x ∈ UAd hc n, x ∈ S.U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) → (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) → (∀ c, IsPtOf hc (y c * (k * t)) (s c)) → (∀ c c' (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = s c' → c = c') → (∀ p, ∃ c, ∃ (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = p) → (∀ c, lat c = (s c).deco.1.L) → (∀ c, Function.Injective (gm c)) → (∀ c (γ : UF E n), γ ∈ (gm c).range ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = s c) → (∀ x : topU S.U t Θ d, (∀ P : Q, rhoP F P.1 x.1 = 1) → ψ x = 1) → ∃ C' : ClsG hc.sig J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))) stab lat, C'.lev.Lb = S.Lb ∧ C'.lev.U = topU S.U t Θ d ∧ (∀ v, v ∉ Qv → C'.lev.Uloc v = S.Uloc v) ∧ (∀ (x : C'.lev.U) (x' : S.U) (x'' : topU S.U t Θ d), x.1 = x'.1 → x.1 = x''.1 → C'.lev.chi x = S.chi x' * ψ x'') ∧ (∀ c, (C'.y c).1 = y c) ∧ ∀ c s, (C'.stabI c s).1 = ufGL E n (gm c s) := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q J T f bad S Qv Λ Θ e d hd N hdN hΘ k t C s y stab _ lat gm ψ
    hJ hQv hT hQ hdq hk hrk ht hU hlatS hpt hinj hsurj hlatc hgmi hgr hψ
  subst hJ
  have hkt : k * t ∈ UAd hc n := mul_mem hk (principal_le_adelic_unitary hc n ST SG ht)
  have hover : ∀ P : Q, P.1.under (𝓞 F) ∈ Qv := fun P => (hQv _).2 ⟨P.1, P.2, rfl⟩
  have hloc : ∀ x ∈ S.U, (∀ v ∈ Qv, ∃ x' ∈ topU S.U t Θ d, bc (prV (E := E) v) x = bc (prV (E := E) v) x') → x ∈ topU S.U t Θ d := by
    intro x hx h
    refine ⟨hx, Subgroup.mem_iInf.2 fun P => ?_⟩
    obtain ⟨x', hx', e'⟩ := h _ (hover P)
    have e1 : rhoT F P.1 t x = rhoT F P.1 t x' := by
      show rhoP F P.1 (t⁻¹ * x * t⁻¹⁻¹) = rhoP F P.1 (t⁻¹ * x' * t⁻¹⁻¹)
      have e0 := localComponent_congr (P := P.1) rfl e'
      simp only [map_mul, e0]
    refine Subgroup.mem_comap.2 ?_
    rw [e1]
    exact rhoT_mem hx' P
  have hψ' : ∀ x : topU S.U t Θ d, (∀ v ∈ Qv, bc (prV (E := E) v) x.1 = 1) → ψ x = 1 := fun x h => hψ x fun P => by
    have h1 := localComponent_congr (P := P.1) rfl ((h _ (hover P)).trans (map_one (bc (prV (E := E) (P.1.under (𝓞 F))))).symm)
    rw [h1, map_one]
  obtain ⟨L, hLb, hLU, hLoc, hLchi⟩ := GlobalTheory.T.exists_stepLevel_smaller_at_finite_places F E hc.sig n 1 T f bad S Qv (topU S.U t Θ d) ψ (topU_le _ _ _ _) hT hloc
    (topU_open F E K hc.sig n 1 Q S.U t Θ d hd S.U_open) hψ'
  have hyU : ∀ c, y c ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) := fun c => by
    have h1 : y c * (k * t) * (k * t)⁻¹ ∈ UAd hc n := mul_mem (hpt c).uni (inv_mem hkt)
    rwa [mul_inv_cancel_right] at h1
  have hlev : ∀ (g x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), IsPtOf hc (g * (k * t)) p → IsPtOf hc (g * x * (k * t)) p' →
      (x ∈ topU S.U t Θ d ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p') :=
    fun g x p p' h h' => GlobalTheory.T.mem_framedLevel_iff_two_adelic_points F E K hc n ST SG Q Λ Θ d hd N hdN hΘ S.U k t g x p p' hk hrk ht hU h h'
  have hle : topU S.U t Θ d ≤ UAd hc n := fun x hx => ((S.U_eq x).1 (topU_le _ _ _ _ hx)).1
  let sI : ∀ c, stab c →* UJ (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) := fun c =>
    ((ufGL E n).comp (gm c)).codRestrict _ fun a => by
      show ufGL E n (gm c a) ∈ URat hc n
      rw [RatMove.ufGL_eq hc]
      exact ((ratEquiv hc n).symm (gm c a)).2
  refine ⟨{ lev := L, y := fun c => ⟨y c, hyU c⟩, y_bij := ?_, y_lat := ?_, stabI := sI, stabI_inj := ?_, stabI_range := ?_ },
    hLb, hLU, hLoc, hLchi, fun c => rfl, fun c a => rfl⟩
  · refine GlobalTheory.T.decoratedPointClasses_bijective_doubleCosets F E K hc n ST SG Q C Λ Θ s L.U (k * t) (fun c => ⟨y c, hyU c⟩) (hLU ▸ hle) hkt ?_ ?_ hpt hinj hsurj
    · rw [hLU]; exact hlev
    · rw [hLU]; exact topU_dense e hd hQ hdq hk hrk ht hU
  · intro c x
    rw [hlatc c, hLb]
    exact PtLat.latS_deco_iff F E hc n ST SG Q S.Lb k t (y c) (s c) ht hlatS (hpt c) x
  · intro c a b h
    have h1 : ufGL E n (gm c a) = ufGL E n (gm c b) := congrArg Subtype.val h
    exact hgmi c (Subtype.ext ((toGLm E n).injective h1))
  · intro c γ
    have e1 : ufGL E n (ratHom hc n γ) = γ.1 := by
      rw [RatMove.ufGL_eq hc]
      exact congrArg Subtype.val ((ratEquiv hc n).symm_apply_apply γ)
    have key := stab_iff_mem_conj F E K hc n ST SG Q Λ Θ (topU S.U t Θ d) (k * t) (y c) (s c) hlev (hpt c) (ratHom hc n γ)
    have e2 : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 = ratAd F (ratHom hc n γ) := by rw [ratAd, e1]
    rw [e2, hLU]
    refine Iff.trans ?_ ((hgr c _).trans key)
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, Subtype.ext ((toGLm E n).injective ?_)⟩
      exact (congrArg Subtype.val ha).trans e1.symm
    · rintro ⟨a, ha⟩
      refine ⟨a, Subtype.ext ?_⟩
      show ufGL E n (gm c a) = γ.1
      rw [ha, e1]

end GlobalTheory.Mem.Col2.TopCh

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartFromAdelicDictionaryStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framed_chart_from_adelic_dictionary : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E hc.sig J T f bad) (Qv : Finset (HeightOneSpectrum (𝓞 F))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (e : ℕ) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (k t : GL (Fin n) (AfE F E)) (C : Type) (s : C → DecoF E n ST SG Q) (y : C → GL (Fin n) (AfE F E)) (stab : C → Type) [∀ c, Group (stab c)] (lat : C → Submodule (𝓞 E) (Fin n → E)) (gm : ∀ c, stab c →* UF E n) (ψ : topU S.U t Θ d →* ℂˣ), J = 1 → (∀ v, v ∈ Qv ↔ ∃ P ∈ Q, P.under (𝓞 F) = v) → (∀ v ∈ Qv, (T : 𝓞 F) ∉ v.asIdeal) → (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → (∀ P : Q, d P = ((qOf P.1 : ℕ) : E) ^ e) → k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ x ∈ UAd hc n, x ∈ S.U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) → (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) → (∀ c, IsPtOf hc (y c * (k * t)) (s c)) → (∀ c c' (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = s c' → c = c') → (∀ p, ∃ c, ∃ (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = p) → (∀ c, lat c = (s c).deco.1.L) → (∀ c, Function.Injective (gm c)) → (∀ c (γ : UF E n), γ ∈ (gm c).range ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = s c) → (∀ x : topU S.U t Θ d, (∀ P : Q, rhoP F P.1 x.1 = 1) → ψ x = 1) → ∃ C' : ClsG hc.sig J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))) stab lat, C'.lev.Lb = S.Lb ∧ C'.lev.U = topU S.U t Θ d ∧ (∀ v, v ∉ Qv → C'.lev.Uloc v = S.Uloc v) ∧ (∀ (x : C'.lev.U) (x' : S.U) (x'' : topU S.U t Θ d), x.1 = x'.1 → x.1 = x''.1 → C'.lev.chi x = S.chi x' * ψ x'') ∧ (∀ c, (C'.y c).1 = y c) ∧ ∀ c s, (C'.stabI c s).1 = ufGL E n (gm c s) := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.exists_clsG_top | exact GlobalTheory.Mem.Col2.TopCh.exists_clsG_top | (intros; apply GlobalTheory.Mem.Col2.TopCh.exists_clsG_top <;> assumption)
end
