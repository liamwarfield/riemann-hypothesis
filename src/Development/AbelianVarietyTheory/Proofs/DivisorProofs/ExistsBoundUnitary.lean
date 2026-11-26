module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniFormula
public import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicHaar
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField Matrix
open scoped TensorProduct ComplexOrder MatrixOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteQuotient

theorem exists_bound_unitary {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) :
    ∃ R : ℝ, ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * G * g = G → ∀ i j, ‖g i j‖ ≤ R := by
  open scoped Matrix.Norms.L2Operator in
  obtain ⟨B, hB, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hG.isStrictlyPositive
  obtain ⟨B, rfl⟩ := hB
  refine ⟨∑ i, ∑ j, ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖, fun g hg i j => ?_⟩
  have hu : B.1 * g * (B⁻¹).1 ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    have : star (B.1 * g * (B⁻¹).1) * (B.1 * g * (B⁻¹).1) =
        star (B⁻¹).1 * (gᴴ * (star B.1 * B.1) * g) * (B⁻¹).1 := by
      simp only [star_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    rw [this, hg, ← Matrix.mul_assoc, ← star_mul, Units.mul_inv, star_one, Matrix.one_mul, Units.mul_inv]
  have e : g = (B⁻¹).1 * (B.1 * g * (B⁻¹).1) * B.1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  have h1 : ‖g i j‖ ≤ ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖ := by
    generalize B.1 * g * (B⁻¹).1 = u at hu e
    rw [e, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _)
      (entry_norm_bound_of_unitary hu k l)) (norm_nonneg _)
  refine h1.trans ?_
  refine (Finset.single_le_sum (f := fun j => ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖)
    (fun _ _ => by positivity) (Finset.mem_univ j)).trans ?_
  exact Finset.single_le_sum (f := fun i => ∑ j, ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖)
    (fun _ _ => by positivity) (Finset.mem_univ i)

theorem posDef_of_signature {n p : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature G p 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have h1 : Formalism.UG.Jpq p 0 = 1 := by
    ext (i | i) (j | j)
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
    · exact j.elim0
    · exact i.elim0
    · exact i.elim0
  have h2 : (star P.1 * G.reindex e e * P.1).PosDef := by
    have : star P.1 * G.reindex e e * P.1 = 1 := hP.trans h1
    rw [this]; exact Matrix.PosDef.one
  have h3 := ((Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h2).submatrix e.injective
  simpa using h3

variable {D : D7}

theorem gram_hermND (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  ⟨fun i j => V.herm.eq (V.frame j) (V.frame i), GlobalTheory.StabCompact.det_gram_ne_zero V⟩

theorem cmExt (D : D7) : IsCMExt D.host.F D.host.E D.sp.cm.sig :=
  ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, fun τ x => D.sp.cm.cmUnram.2.1 τ x⟩

theorem isTotDef_of_posDef (V : HSp D) (h : ∀ τ, (gramAt D V τ).PosDef) : Formalism.UG.IsTotDef D.sp.cm.sig V.gram := by
  refine ⟨D.sp.cm.totReal, fun ι => Or.inl fun x hx => ?_⟩
  have hτ := (cmExt D).2.2.2
  obtain ⟨τ, hι⟩ := (GlobalTheory.CMTypePlaces.places_bijective D).2 (InfinitePlace.mk (Complex.ofRealHom.comp ι))
  have hι' : (tauE D τ).comp (algebraMap D.host.F D.host.E) = Complex.ofRealHom.comp ι := by
    rcases InfinitePlace.mk_eq_iff.1 hι with h1 | h1
    · exact h1
    · ext a
      have := congrArg (starRingEnd ℂ) (RingHom.congr_fun h1 a)
      simpa using this
  have hpos : 0 < tauE D τ (Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram x x) := by
    have hx' : (fun i => tauE D τ (x i)) ≠ 0 := fun e => hx (funext fun i => (tauE D τ).injective (by
      simpa using congrFun e i))
    have := (Matrix.posDef_iff_dotProduct_mulVec.1 (h τ)).2 hx'
    convert this using 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, mulVec, Finset.mul_sum, gramAt, Pi.star_apply,
      Matrix.map_apply, mul_assoc]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hτ]; rfl
  obtain ⟨a, ha⟩ := (D.sp.cm.fixed (Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram x x)).1 (by
    apply (tauE D τ).injective
    refine (hτ (tauE D τ) _).trans ?_
    exact Complex.conj_eq_iff_im.2 (Complex.pos_iff.1 hpos).2.symm)
  refine ⟨a, ha, ?_⟩
  rw [← ha] at hpos
  have e : tauE D τ (algebraMap D.host.F D.host.E a) = (ι a : ℂ) := RingHom.congr_fun hι' a
  rw [e] at hpos
  exact_mod_cast hpos

theorem exists_compact : ∀ {D : D7} (V : HSp D), (∀ τ, (gramAt D V τ).PosDef) →
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c := by
  intro D V hV
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have hf : GlobalTheory.Mass.FiniteClasses (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) := by
    refine (GlobalTheory.Mass.finiteClasses_comap π (GlobalTheory.Mass.ratIn _ _ _) _ hπ.surjective hπ.injOn).2 ?_
    rw [hπ.map_ratIn]
    exact GlobalTheory.Mass.finiteClasses_unitary (cmExt D) (gram_hermND V) (isTotDef_of_posDef V hV)
      (GlobalTheory.Mass.isCompact_stdLevel _ _ (gram_hermND V).2) (GlobalTheory.Mass.isOpen_stdLevel _ _)
  choose R hR using fun τ => exists_bound_unitary (hV τ)
  obtain ⟨C, hC, hCe⟩ := (GlobalTheory.Mass.intTens_open_compact D.host.F D.host.E).2
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (∑ τ, |R τ|) C hC
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (gram_hermND V).2 C' hC'
  have hsub : ∀ k : GA D V, π k ∈ GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram → k ∈ K := by
    intro k hk
    refine hKe k fun i j => hCe' _ (hCe _ ?_) fun τ => ?_
    · have := ((GlobalTheory.Mass.mem_stdLevel _ _ _).1 hk i j).1
      rwa [hπ k] at this
    · have hJ : (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
        ext i j; exact GlobalTheory.FockCompare.comp_incA hθ τ _
      have hu : Formalism.UG.cT (cA D) (mt V k) * V.gram.map (incA D) * mt V k = V.gram.map (incA D) := k.2
      have e : (Formalism.UG.cT (cA D) (mt V k)).map ((θ τ).comp (infPart D)) =
          ((mt V k).map ((θ τ).comp (infPart D)))ᴴ := by
        ext i j; exact GlobalTheory.FockCompare.comp_cA hθ τ _
      have := congrArg (fun M => M.map ((θ τ).comp (infPart D))) hu
      simp only [Matrix.map_mul, e, hJ] at this
      exact ((hR τ _ this i j).trans (le_abs_self _)).trans
        (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  haveI := hf.1
  refine ⟨⋃ c : Formalism.UG.ClassSet (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π),
    (fun k => c.out * k) '' K, isCompact_iUnion fun c => hK.image (continuous_const_mul _), fun h => ?_⟩
  obtain ⟨γ, hγ, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) h
  refine ⟨γ⁻¹, inv_mem hγ, _, Set.mem_iUnion.2 ⟨DoubleCoset.mk _ _ h, k⁻¹, hsub _ (inv_mem hk), rfl⟩, ?_⟩
  simp only [e]
  group


open MeasureTheory in
theorem integrableOn_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))),
    IsWeilDatumO ψ S T χS χT om → (∀ τ, (gramAt D S τ).PosDef) →
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)),
    (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ g, F (γ * g) = F g) →
    ∀ (μ : Measure (GA D S)) (𝓕 : Set (GA D S)), μ.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 μ →
    ∀ h, IntegrableOn (fun g => thetaKO om g h (L (F g))) 𝓕 μ := by
  intro D ψ _ S T χS χT om hom hS X _ _ _ L hL F hF hinv μ 𝓕 hμ h𝓕 h
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D S) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig S.gram))
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : Countable (GQ S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  obtain ⟨C, hC, hcov⟩ := exists_compact S hS
  refine GlobalTheory.integrableOn_fundamentalDomain_of_cocompact (GA D S) (GQ S) C hC (fun g => ?_) μ hμ 𝓕 h𝓕 _ ?_ ?_
  · obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩
  · let b := Module.finBasis ℂ X
    have e : (fun g => thetaKO om g h (L (F g))) =
        fun g => ∑ k, b.coord k (F g) * om (g, h) (L (b k)) 0 := by
      funext g
      conv_lhs => rw [← b.sum_repr (F g)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
    rw [e]
    refine continuous_finsetSum _ fun k _ => Continuous.mul ?_ ?_
    · exact (b.coord k).continuous_of_finiteDimensional.comp hF
    · exact (hom.om_cont _ (hL (b k)) 0).comp (continuous_id.prodMk continuous_const)
  · intro γ hγ g
    have e : (γ * g, h) = ((γ, 1) : GA D S × GA D T) * (g, h) := by rw [Prod.mk_mul_mk, one_mul]
    simp only [thetaKO]
    rw [hinv γ hγ, e, map_mul]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ (hL _))

end GlobalTheory.DefiniteQuotient
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousWordTranslate
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology InnerProductSpace

namespace GlobalTheory.SmoothCyclic

open Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.GardingVec GlobalTheory.LowTypeRestriction

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

section Conj
variable {n : ℕ}

theorem conj_lie {J G A B X : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (h : Bᴴ * J * B = G)
    (hX : Xᴴ * J + J * X = 0) : (A * X * B)ᴴ * G + G * (A * X * B) = 0 := by
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  have hBA' : Aᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBA, conjTranspose_one]
  calc (A * X * B)ᴴ * G + G * (A * X * B)
      = Bᴴ * (Xᴴ * (Aᴴ * Bᴴ) * J + J * (B * A) * X) * B := by
        rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hBA, hBA', Matrix.mul_one, Matrix.mul_one, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem exp_conj_of_mul {A B : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (A * X * B)) = A * NormedSpace.exp (t • X) * B := by
  have hB : B = A⁻¹ := (Matrix.inv_eq_right_inv hAB).symm
  rw [hB, ← Matrix.exp_conj _ _ (IsUnit.of_mul_eq_one _ hAB)]
  simp

theorem list_prod_conj {A B : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun a => A * a * B).prod = A * l.prod * B := by
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  induction l with
  | nil => simp [hAB]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc A * a * B * (A * l.prod * B) = A * a * (B * A) * l.prod * B := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBA]; simp only [Matrix.mul_assoc, Matrix.one_mul]

theorem expProd_conj {A B : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) {k : ℕ}
    (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (t : Fin k → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (t i • (A * Xs i * B))).prod
      = A * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * B := by
  rw [← list_prod_conj hAB, List.map_ofFn]
  simp only [exp_conj_of_mul hAB, Function.comp_def]

end Conj

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def lieJ (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}
  add_mem' := fun {X Y} hX hY => by
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' := fun c X hX => by
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem exp_memJ {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieJ ε) (t : ℝ) : NormedSpace.exp (t • X) ∈ UJset ε :=
  exp_mem (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)) hX t

theorem expProd_memJ {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ} (hX : ∀ i, Xs i ∈ lieJ ε) (t : Fin k → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ UJset ε :=
  list_prod_mem (G := Formalism.REAL.Jm ε) _ fun g hg => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact exp_memJ (hX i) _

theorem rep_mul (hσ : IsURepOn (UJset ε) σ) {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε)
    (v : H) : σ a (σ b v) = σ (a * b) v := by
  rw [hσ.1.2 _ ha _ hb]; rfl

def smSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {w | SmoothVec (lieJ ε : Set _) σ w}
  add_mem' := fun ha hb k Xs hX => by simpa only [map_add (f := _)] using (ha k Xs hX).add (hb k Xs hX)
  zero_mem' := fun k Xs _ => by simpa only [map_zero] using contDiff_const
  smul_mem' := fun c w hw k Xs hX => by simpa only [map_smul] using (hw k Xs hX).const_smul c

theorem hasDerivAt_dRep {w : H} (hw : w ∈ smSub ε σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieJ ε) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) w) (dRep σ X w) 0 := by
  have h := (hw 1 (fun _ => X) fun _ => hX).comp (contDiff_pi.2 fun _ : Fin 1 => (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ)))
  have h2 : ContDiff ℝ ∞ fun t : ℝ => σ (NormedSpace.exp (t • X)) w := by
    simpa [Function.comp_def] using h
  exact (h2.differentiable (by simp) 0).hasDerivAt

theorem dRep_mem (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : w ∈ smSub ε σ) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieJ ε) : dRep σ X w ∈ smSub ε σ := by
  intro k Xs hXs
  have h := hw (k + 1) (Fin.snoc Xs X) (by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hX
    · simpa using hXs j)
  have hs : ContDiff ℝ ∞ fun z : (Fin k → ℝ) × ℝ => (Fin.snoc z.1 z.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simpa [Function.comp_def] using (contDiff_apply ℝ (fun _ => ℝ) j).comp (contDiff_fst (F := ℝ))
  have h2 : ContDiff ℝ ∞ fun z : (Fin k → ℝ) × ℝ =>
      σ ((List.ofFn fun i => NormedSpace.exp (z.1 i • Xs i)).prod) (σ (NormedSpace.exp (z.2 • X)) w) := by
    convert h.comp hs using 2 with z
    rw [rep_mul hσ (expProd_memJ hXs _) (exp_memJ hX _)]
    simp only [Function.comp_def, List.ofFn_succ_last, Fin.snoc_castSucc, Fin.snoc_last, List.prod_append,
      List.prod_singleton]
  have h3 := ContDiff.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (f := fun (t : Fin k → ℝ) (s : ℝ) =>
      σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) (σ (NormedSpace.exp (s • X)) w))
      (g := fun _ => 0) h2 contDiff_const (by simp)
  convert h3.clm_apply (contDiff_const (c := (1 : ℝ))) using 2 with t
  exact (((σ _).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_dRep hw hX)).deriv.symm

variable {φ : Matrix (Fin n) (Fin n) ℂ → ℝ}

section Transport
variable {P G : Matrix (Fin n) (Fin n) ℂ}

theorem smoothVec_transport (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (w : H) :
    SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w ↔ w ∈ smSub ε σ := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hd
  have h' : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    calc (P⁻¹)ᴴ * G * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  constructor
  · intro hw k Xs hX
    have := hw k (fun i => P⁻¹ * Xs i * P) fun i => conj_lie h2 h (hX i)
    convert this using 2 with t
    rw [expProd_conj h2]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  · intro hw k Xs hX
    simpa only [expProd_conj h1] using hw k (fun i => P * Xs i * P⁻¹) fun i => conj_lie h1 h' (hX i)

theorem sobCont_transport (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) ℓ) : Sobolev₂ (lieJ ε : Set _) σ ℓ := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h' : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    calc (P⁻¹)ᴴ * G * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  obtain ⟨S, C, hS, hb⟩ := hℓ
  have e : dRep (fun g => σ (P * g * P⁻¹)) = fun X w => dRep σ (P * X * P⁻¹) w := by
    funext X w
    simp only [dRep, exp_conj_of_mul h1]
  refine ⟨S.map fun l => l.map fun X => P * X * P⁻¹, C, fun l hl X hX => ?_, fun w hw => ?_⟩
  · obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact conj_lie h1 h' (hS l' hl' Y hY)
  · simpa only [e, List.map_map, Function.comp_def, List.foldr_map] using
      hb w ((smoothVec_transport hP h w).2 hw)

end Transport

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sm_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    M.sm τ = smSub (M.ε τ) (M.σ τ) := by
  rw [← Submodule.span_eq (smSub (M.ε τ) (M.σ τ))]
  exact congrArg (Submodule.span ℂ) (Set.ext fun w => smoothVec_transport (M.fr_unit τ) (M.fr_gram τ) w)

end GlobalTheory.SmoothCyclic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.LFun GlobalTheory.PRep Formalism.UG
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.MultiplicityOne

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem whit_mul_right (F : GA E a → ℂ) (y x : GA E a) : whit F (y * x) = whit (fun z => F (z * x)) y := by
  simp only [whit, whittaker, mul_assoc]

theorem integrableOn_whit {F : GA E a → ℂ} (hc : Continuous F) (y : GA E a) :
    IntegrableOn (fun X => F (uGL X * y) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ))
      (vecDomain E (Pos a)) (vecMeasure E (Pos a)) := by
  have hcont : Continuous fun X : Pos a → Ad E =>
      F (uGL X * y) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    (hc.comp (continuous_uGL.mul continuous_const)).mul continuous_adelicChar_neg_supSum
  exact (hcont.continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure

theorem whit_add {F G : GA E a → ℂ} (hF : Continuous F) (hG : Continuous G) (y : GA E a) :
    whit (F + G) y = whit F y + whit G y := by
  unfold whit whittaker
  rw [← integral_add (integrableOn_whit hF y) (integrableOn_whit hG y)]
  congr 1
  funext X
  simp only [Pi.add_apply, add_mul]

theorem whit_smul (c : ℂ) (F : GA E a → ℂ) (y : GA E a) : whit (c • F) y = c * whit F y := by
  unfold whit whittaker
  rw [← integral_const_mul]
  congr 1
  funext X
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

def psiLocChar (w : HeightOneSpectrum (𝓞 E)) : AddChar (w.adicCompletion E) ℂ where
  toFun := psiLoc w
  map_zero_eq_one' := by simp [psiLoc]
  map_add_eq_mul' x y := by simp only [psiLoc, map_add (f := _), AddChar.map_add_eq_mul, Circle.coe_mul]

theorem finGL_locGL_apply (w : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (w.adicCompletion E)) (i j : Fin a) :
    ((finGL E a (locGL E a w k) : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) i j =
      (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E (sLoc E w ((1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j))
        + sFin E (sLoc E w ((k : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j)) := by
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j) +
    sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j - sLoc E w ((1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j)
      + sLoc E w ((k : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j)) = _
  rw [map_add (f := _), map_sub]
  abel

end GlobalTheory.JSW

namespace GlobalTheory.JSW
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem GA_ext {x y : GA E a}
    (hinf : GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing E) (Af E)) x =
      GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing E) (Af E)) y)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 E), GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) x =
      GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) y) : x = y := by
  ext i j
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun v => ?_)
  · exact congrArg (fun m : GL (Fin a) (InfiniteAdeleRing E) => (m : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j) hinf
  · exact congrArg (fun m : GL (Fin a) (v.adicCompletion E) => (m : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) (hfin v)

theorem commute_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) {g : GA E a}
    (hg : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1) (k : GL (Fin a) (w.adicCompletion E)) :
    g * finGL E a (locGL E a w k) = finGL E a (locGL E a w k) * g := by
  have key : ∀ {R : Type} [CommRing R] (c : Ad E →+* R),
      (GeneralLinearGroup.map c g = 1 ∨ GeneralLinearGroup.map c (finGL E a (locGL E a w k)) = 1) →
      GeneralLinearGroup.map c (g * finGL E a (locGL E a w k)) =
        GeneralLinearGroup.map c (finGL E a (locGL E a w k) * g) := by
    intro R _ c h
    rw [map_mul, map_mul]
    rcases h with h | h <;> rw [h] <;> simp
  refine GA_ext (key _ (Or.inr ?_)) fun v => key _ ?_
  · exact map_cornerGL_of_zero _ _ (fun x => rfl) _
  · by_cases hv : v = w
    · subst hv; exact Or.inl hg
    · refine Or.inr ?_
      rw [finGL, map_cornerGL_of_hom (sFin E) ((pLoc E v).comp (pFin E)) (pLoc E v) (fun x => rfl)]
      exact pLoc_locGL_of_ne hv k

end GlobalTheory.JSW

namespace GlobalTheory.JSW
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem finGL_locGL_eq_uGL (w : HeightOneSpectrum (𝓞 E)) {u : GL (Fin a) (w.adicCompletion E)}
    (hu : u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a)) :
    finGL E a (locGL E a w u) =
      uGL (fun p : Pos a => sFin E (sLoc E w ((u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) p.1.1 p.1.2))) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
  ext i j
  rw [finGL_locGL_apply, coe_uGL, uMat_apply]
  by_cases hij : i = j
  · subst hij; simp [h2]
  · rw [if_neg hij, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, map_zero, sub_zero, zero_add]
    by_cases hlt : i < j
    · rw [dite_eq_left hlt]
    · rw [dite_eq_right hlt, h1 i j (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hij)), map_zero, map_zero]

theorem sum_pos_superdiag {M : Type} [AddCommMonoid M] (f : Fin a → Fin a → M) :
    ∑ p ∈ Finset.univ.filter (fun p : Pos a => (p.1.2 : ℕ) = p.1.1 + 1 ∧ 0 ≤ (p.1.2 : ℕ)), f p.1.1 p.1.2 =
      ∑ i : Fin a, ∑ j ∈ Finset.univ.filter (fun j : Fin a => (j : ℕ) = (i : ℕ) + 1), f i j := by
  classical
  have hR : ∑ i : Fin a, ∑ j ∈ Finset.univ.filter (fun j : Fin a => (j : ℕ) = (i : ℕ) + 1), f i j =
      ∑ q ∈ Finset.univ.filter (fun q : Fin a × Fin a => (q.2 : ℕ) = q.1 + 1), f q.1 q.2 := by
    simp only [Finset.sum_filter]
    exact (Fintype.sum_prod_type' (fun x y : Fin a => if (y : ℕ) = (x : ℕ) + 1 then f x y else 0)).symm
  rw [hR]
  refine Finset.sum_bij (fun p _ => p.1) (fun p hp => ?_) (fun p _ q _ h => Subtype.ext h) (fun q hq => ?_)
    (fun p _ => rfl)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hp.1
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    refine ⟨⟨q, ?_⟩, ?_, rfl⟩
    · rw [Fin.lt_def]; omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hq, Nat.zero_le _⟩

theorem supSum_sLoc (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin a) (w.adicCompletion E)) :
    supSum 0 (fun p : Pos a => sFin E (sLoc E w ((u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) p.1.1 p.1.2))) =
      sFin E (sLoc E w (GlobalTheory.Whittaker.superDiag u)) := by
  classical
  let t : w.adicCompletion E →+ Ad E := (sFin E).toAddMonoidHom.comp (sLoc E w).toAddMonoidHom
  change supSum 0 (fun p : Pos a => t ((u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) p.1.1 p.1.2)) =
    t (GlobalTheory.Whittaker.superDiag u)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.Whittaker.superDiag, map_sum, supSum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  exact sum_pos_superdiag (fun i j => t ((u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j))

end GlobalTheory.JSW

namespace GlobalTheory.JSW
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem whit_mul_locGL_diagPow_of_fixed (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (hψ : ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, psiLoc w (x * y) = 1) ↔ x ∈ Ov E w)
    (α : Fin a → ℂˣ) (hα : HasSatGL w (π.locRep w) (Finset.univ.val.map α))
    (φ : π.V) (hφ : φ ∈ fixed (π.locRep w) (KGL w (n := a)))
    (g : GA E a) (hg : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (l : Fin a → ℕ) :
    whit φ.1.1 (g * finGL E a (locGL E a w (diagPow ϖ l))) =
      sphW (qV E w) (fun i => (α i : ℂ)) l * whit φ.1.1 g := by
  classical
  have hcont : ∀ ψ : π.V, Continuous ψ.1.1 := fun ψ => (π.cusp _ ψ.2).1.continuous
  have hleft : AutomorphicForm.IsLeftInvariant φ.1.1 := fun γ y => by
    rw [show AdelicGLn.diagonal E a γ = ratGL E a γ from Units.ext (Matrix.ext fun _ _ => rfl)]
    exact (π.cusp _ φ.2).1.left γ y
  let f : π.V →ₗ[ℂ] (GL (Fin a) (w.adicCompletion E) → ℂ) :=
    { toFun := fun ψ h => whit ψ.1.1 (g * finGL E a (locGL E a w h))
      map_add' := fun ψ ψ' => funext fun h => whit_add (hcont ψ) (hcont ψ') _
      map_smul' := fun c ψ => funext fun h => whit_smul c ψ.1.1 _ }
  have hf : ∀ k (ψ : π.V), f (π.locRep w k ψ) = rightReg ℂ _ ℂ k (f ψ) := by
    intro k ψ
    funext h
    change whit (fun z => ψ.1.1 (z * finGL E a (locGL E a w k))) (g * finGL E a (locGL E a w h)) =
      whit ψ.1.1 (g * finGL E a (locGL E a w (h * k)))
    rw [map_mul, map_mul, ← mul_assoc, whit_mul_right ψ.1.1 (g * finGL E a (locGL E a w h))]
  by_cases h0 : φ = 0
  · subst h0
    have hz : ∀ y, whit ((0 : π.V) : Sm E a).1 y = 0 := fun y => by
      have e := whit_smul 0 (fun _ : GA E a => (0 : ℂ)) y
      rw [zero_mul] at e
      exact (congrArg (fun F => whit F y) (funext fun _ => (zero_mul _).symm)).trans e
    rw [hz, hz, mul_zero]
  have hsat := hα.2 φ hφ h0
  have hmain := GlobalTheory.T.shintani_formula_alt E w a (psiLocChar w) hψ (f φ) α ?_ ?_ ?_ ϖ hϖ l
  · change whit φ.1.1 (g * finGL E a (locGL E a w (diagPow ϖ l))) = _ * whit φ.1.1 (g * finGL E a (locGL E a w 1))
      at hmain
    rwa [map_one, map_one, mul_one] at hmain
  · intro u hu h
    change whit φ.1.1 (g * finGL E a (locGL E a w (u * h))) =
      psiLoc w (GlobalTheory.Whittaker.superDiag u) * whit φ.1.1 (g * finGL E a (locGL E a w h))
    rw [map_mul, map_mul, ← mul_assoc, commute_finGL_locGL w hg u, mul_assoc, finGL_locGL_eq_uGL w hu, whit,
      whittaker_uGL_mul (hcont φ) hleft, supSum_sLoc]
    rfl
  · intro h k hk
    change whit φ.1.1 (g * finGL E a (locGL E a w (h * k))) = whit φ.1.1 (g * finGL E a (locGL E a w h))
    rw [map_mul, map_mul, ← mul_assoc, whit_mul_right]
    congr 1
    funext z
    exact congrArg (fun ψ : π.V => ψ.1.1 z) (GlobalTheory.LGrp.mem_fixed.1 hφ k hk)
  · intro ϖ' hϖ' j hj
    rw [← map_heckeVec (Final.GLintComm E w a) (Tj_mem_hecke hϖ' j) f hf, hsat.2.2.2 ϖ' hϖ' j hj, map_smul]

end GlobalTheory.JSW

namespace GlobalTheory.JSW

theorem whit_mul_locGL_diagPow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (α : Fin a → ℂˣ),
    (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    HasSatGL w (π.locRep w) (Finset.univ.val.map α) → ∀ φ ∈ π.V, (∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) →
    ∀ g : GA E a, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1 → ∀ (ϖ : (w.adicCompletion E)ˣ),
    IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin a → ℕ,
    GlobalTheory.JSW.whit φ.1 (g * finGL E a (locGL E a w (GlobalTheory.JSW.diagPow ϖ l))) =
      GlobalTheory.JSW.sphW (qV E w) (fun i => (α i : ℂ)) l * GlobalTheory.JSW.whit φ.1 g := by
  intro E _ _ _ a π w α hψ hα φ hφV hφ g hg ϖ hϖ l
  exact whit_mul_locGL_diagPow_of_fixed π w hψ α hα ⟨φ, hφV⟩
    (GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (hφ k hk)) g hg ϖ hϖ l

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharacters
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilChange

variable {D : D7}

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem thetaO_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := {
  quasi γ w := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf.quasi]
    ring
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisO_smul, h u hu h0]⟩
  cont := hf.cont.const_smul c
  smooth k L hL h0 w := (hf.smooth k L hL h0 w).const_smul c }

theorem triv_of_resEta_zero {ν : (AE D)ˣ →* Circle} (h : ResEta D ν 0) (a : (AF D.host.F)ˣ) : ν (idF D a) = 1 := by
  obtain ⟨η, hη⟩ := h.1
  rw [h.2 η hη a, pow_zero]

theorem hecke_mul {χ ν : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hν : IsHeckeChar D ν) : IsHeckeChar D (χ * ν) :=
  ⟨hχ.1.mul hν.1, fun x => by rw [MonoidHom.mul_apply, hχ.2, hν.2, mul_one]⟩

theorem hecke_inv {ν : (AE D)ˣ →* Circle} (hν : IsHeckeChar D ν) : IsHeckeChar D ν⁻¹ :=
  ⟨hν.1.inv, fun x => by rw [MonoidHom.inv_apply, hν.2, inv_one]⟩

theorem exists_weilDatum_twist : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (νS νT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsHeckeChar D νS → IsHeckeChar D νT → ResEta D νS 0 → ResEta D νT 0 → ∃ om', IsWeilDatumO ψ S T (χS * νS) (χT * νT) om' ∧ ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y → om' (g, h) = ((((νT x)⁻¹ * νS y : Circle) : ℂ)) • om (g, h) := by
  intro D ψ hψ S T χS χT νS νT om ho hS hT rS rT
  obtain ⟨a, aval, amul, anorm, arat, acont⟩ :=
    GlobalTheory.Member.exists_muVal D S νT⁻¹ (hecke_inv hT) (triv_of_resEta_zero (resEta_inv rT))
  obtain ⟨b, bval, bmul, bnorm, brat, bcont⟩ := GlobalTheory.Member.exists_muVal D T νS hS (triv_of_resEta_zero rS)
  have a1 : a 1 = 1 := arat 1 (one_mem _)
  have b1 : b 1 = 1 := brat 1 (one_mem _)
  let om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ) :=
    { toFun := fun p => (a p.1 * b p.2) • om p
      map_one' := by rw [Prod.fst_one, Prod.snd_one, a1, b1, map_one, one_mul, one_smul]
      map_mul' := fun p q => by
        rw [Prod.fst_mul, Prod.snd_mul, amul, bmul, map_mul, smul_mul_smul_comm, mul_mul_mul_comm] }
  have happ : ∀ p f, om' p f = (a p.1 * b p.2) • om p f := fun p f => rfl
  have hval : ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y →
      a g * b h = (((νT x)⁻¹ * νS y : Circle) : ℂ) := by
    intro g h x y hx hy
    rw [aval.2 g x hx, bval.2 h y hy, Circle.coe_mul, MonoidHom.inv_apply]
  refine ⟨om', ⟨hψ, hecke_mul ho.hecS hS, hecke_mul ho.hecT hT, resEta_mul ho.resS rS, resEta_mul ho.resT rT,
    ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p f hf
    rw [happ]
    exact thetaO_smul _ (ho.om_pres p f hf)
  · intro g h w₀ f hf
    rw [happ, happ, heisO_smul, ho.om_heis g h w₀ f hf]
  · intro γ hγ γ' hγ' f hf
    rw [happ, arat γ hγ, brat γ' hγ', one_mul, one_smul]
    exact ho.om_aut γ hγ γ' hγ' f hf
  · intro f hf w
    exact ((acont.comp continuous_fst).mul (bcont.comp continuous_snd)).mul (ho.om_cont f hf w)
  · intro μ 𝓕 hμ h𝓕 p f hf
    rw [← ho.om_unit μ 𝓕 hμ h𝓕 p f hf]
    refine lintegral_congr fun w => ?_
    have hn : ‖om' p f w‖ = ‖om p f w‖ := by
      rw [happ, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul, anorm, bnorm, one_mul, one_mul]
    rw [← ofReal_norm, ← ofReal_norm, hn]
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := ho.om_split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    rw [happ, map_smul, H ℓ hℓ f hf,
      hval g h x y (isDetAt_root he S g hg x hx) (isDetAt_root he T h hh y hy)]
    simp only [splitFacO, MonoidHom.mul_apply, mul_inv, Circle.coe_mul, smul_eq_mul]
    ring
  · intro g h x y hx hy
    rw [← hval g h x y hx hy]
    rfl

end GlobalTheory.WeilChange

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharactersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilDatum_twist_heckeCharacters : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (νS νT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsHeckeChar D νS → IsHeckeChar D νT → ResEta D νS 0 → ResEta D νT 0 → ∃ om', IsWeilDatumO ψ S T (χS * νS) (χT * νT) om' ∧ ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y → om' (g, h) = ((((νT x)⁻¹ * νS y : Circle) : ℂ)) • om (g, h) := by
  first | exact @GlobalTheory.WeilChange.exists_weilDatum_twist | exact GlobalTheory.WeilChange.exists_weilDatum_twist | (intros; apply GlobalTheory.WeilChange.exists_weilDatum_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.HeckeOrthSum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

open Module.End
open scoped InnerProductSpace

variable {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem iSup_iInf_eigenspace_eq_top [FiniteDimensional ℂ E] (T : I → E →ₗ[ℂ] E) (hc : ∀ i k, Commute (T i) (T k))
    (hadj : ∀ i, ∃ k, ∀ x y, ⟪T i x, y⟫_ℂ = ⟪x, T k y⟫_ℂ) :
    ⨆ χ : I → ℂ, ⨅ i, eigenspace (T i) (χ i) = ⊤ := by
  choose s hs using hadj
  have hs' : ∀ i x y, ⟪T (s i) x, y⟫_ℂ = ⟪x, T i y⟫_ℂ := fun i x y => by
    rw [← inner_conj_symm, ← hs, inner_conj_symm]
  let H : I ⊕ I → E →ₗ[ℂ] E := Sum.elim (fun i => T i + T (s i)) (fun i => Complex.I • (T i - T (s i)))
  have hH : ∀ i, (H i).IsSymmetric := by
    rintro (i | i) x y
    · simp only [H, Sum.elim_inl, LinearMap.add_apply, inner_add_left, inner_add_right, hs i, hs' i]
      ring
    · simp only [H, Sum.elim_inr, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right,
        inner_sub_left, inner_sub_right, hs i, hs' i, Complex.conj_I]
      ring
  have hT : ∀ i k, Commute (H i) (T k) := by
    rintro (i | i) k
    · exact (hc _ _).add_left (hc _ _)
    · exact ((hc _ _).sub_left (hc _ _)).smul_left _
  have hHc : ∀ i k, Commute (H i) (H k) := by
    rintro i (k | k)
    · exact (hT _ _).add_right (hT _ _)
    · exact ((hT _ _).sub_right (hT _ _)).smul_right _
  have h := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hH (fun i k _ => hHc i k)
  rw [eq_top_iff, ← h]
  refine iSup_le fun χ => le_iSup_of_le (fun i => (χ (.inl i) - Complex.I * χ (.inr i)) / 2) fun x hx => ?_
  simp only [Submodule.mem_iInf, mem_eigenspace_iff] at hx ⊢
  intro i
  have h1 : T i x + T (s i) x = χ (.inl i) • x := hx (.inl i)
  have h2 : Complex.I • (T i x - T (s i) x) = χ (.inr i) • x := hx (.inr i)
  have h3 : T i x - T (s i) x = -(Complex.I * χ (.inr i)) • x := by
    rw [neg_smul, mul_smul, ← h2, smul_smul, Complex.I_mul_I]; simp
  have h4 : (2 : ℂ) • T i x = (χ (.inl i) - Complex.I * χ (.inr i)) • x := by
    rw [sub_eq_add_neg, add_smul, ← h1, ← h3, two_smul]; abel
  rw [div_eq_inv_mul, mul_smul, ← h4, smul_smul]; simp

end Abstract

section Form

variable {X I : Type} [AddCommGroup X] [Module ℂ X]

structure IsPosOn (Y : Submodule ℂ X) (B : X → X → ℂ) : Prop where
  lin : ∀ x ∈ Y, ∀ y ∈ Y, ∀ z ∈ Y, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z
  symm : ∀ x ∈ Y, ∀ y ∈ Y, B y x = star (B x y)
  pos : ∀ x ∈ Y, x ≠ 0 → 0 < (B x x).re

variable {Y : Submodule ℂ X} {B : X → X → ℂ}

theorem IsPosOn.zero_right (h : IsPosOn Y B) {x : X} (hx : x ∈ Y) : B x 0 = 0 := by
  have := h.lin x hx 0 Y.zero_mem 0 Y.zero_mem 1
  simpa using this

theorem IsPosOn.add_right (h : IsPosOn Y B) {x y z : X} (hx : x ∈ Y) (hy : y ∈ Y) (hz : z ∈ Y) :
    B x (y + z) = B x y + B x z := by
  simpa using h.lin x hx y hy z hz 1

theorem IsPosOn.smul_right (h : IsPosOn Y B) {x z : X} (hx : x ∈ Y) (hz : z ∈ Y) (c : ℂ) :
    B x (c • z) = c * B x z := by
  simpa [h.zero_right hx] using h.lin x hx 0 Y.zero_mem z hz c

@[reducible] def IsPosOn.core (h : IsPosOn Y B) : InnerProductSpace.Core ℂ Y where
  inner x y := B x y
  conj_inner_symm x y := (h.symm y y.2 x x.2).symm
  re_inner_nonneg x := by
    by_cases hx : (x : X) = 0
    · show 0 ≤ (B x x).re
      rw [hx, h.zero_right Y.zero_mem]; simp
    · exact (h.pos x x.2 hx).le
  add_left x y z := by
    show B ((x : X) + y) z = B x z + B y z
    rw [h.symm z z.2 _ (Y.add_mem x.2 y.2), h.add_right z.2 x.2 y.2, h.symm z z.2 x x.2, h.symm z z.2 y y.2, star_add]
  smul_left x y r := by
    show B (r • (x : X)) y = starRingEnd ℂ r * B x y
    rw [h.symm y y.2 _ (Y.smul_mem r x.2), h.smul_right y.2 x.2, h.symm y y.2 x x.2, star_mul']
    rfl
  definite x hx := by
    by_contra h0
    have := h.pos x x.2 (fun e => h0 (Subtype.ext e))
    have hx' : B x x = 0 := hx
    rw [hx'] at this
    simp at this

theorem IsPosOn.le_iSup_eigen [FiniteDimensional ℂ Y] (h : IsPosOn Y B) (T : I → X →ₗ[ℂ] X)
    (hT : ∀ i, ∀ x ∈ Y, T i x ∈ Y) (hc : ∀ i k, ∀ x ∈ Y, T i (T k x) = T k (T i x))
    (hadj : ∀ i, ∃ k, ∀ x ∈ Y, ∀ y ∈ Y, B (T i x) y = B x (T k y))
    (Z : Submodule ℂ X) (hZ : ∀ (χ : I → ℂ), ∀ x ∈ Y, (∀ i, T i x = χ i • x) → x ∈ Z) : Y ≤ Z := by
  letI := h.core
  letI : NormedAddCommGroup Y := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ Y := InnerProductSpace.ofCore _
  have key := iSup_iInf_eigenspace_eq_top (E := Y) (fun i => (T i).restrict (hT i))
    (fun i k => LinearMap.ext fun x => Subtype.ext (hc i k x x.2))
    (fun i => (hadj i).imp fun k hk x y => hk x x.2 y y.2)
  have : (⊤ : Submodule ℂ Y) ≤ Z.comap Y.subtype := by
    rw [← key]
    refine iSup_le fun χ x hx => hZ χ x x.2 fun i => ?_
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx
    exact congrArg Subtype.val (hx i)
  exact fun x hx => this (x := ⟨x, hx⟩) Submodule.mem_top

end Form

section Local

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
  (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
  (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))

variable {θ V S M J χ Sb e}

end Local

end GlobalTheory.HeckeOrthSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisOApplyZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilRat

theorem heisO_apply_zero {D : D7} {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  have h : hO S T 0 w = 0 := by simp [hO]
  simp [heisO, symplOH, symplO, h]

theorem om_rat_actO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → ∀ w, om (γ, γ') f (actO S T γ γ' w) = f w := by
  intro D ψ hψ S T χS χT om H γ hγ γ' hγ' f hf w
  have h1 := H.om_heis γ γ' w f hf
  have h2 := H.om_aut γ hγ γ' hγ' _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w)
  rw [← heisO_apply_zero ψ (actO S T γ γ' w) (om (γ, γ') f), ← h1]
  exact h2.trans (heisO_apply_zero _ _ _)

end GlobalTheory.WeilRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG Polynomial
open scoped TensorProduct

namespace GlobalTheory.SphPar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def HasDiv {n : ℕ} (O : Subring L) (d : List ℤ) (g : GL (Fin n) L) : Prop :=
  ∃ ϖ : L, Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ∧
    ∃ a ∈ GLint (Fin n) O, ∃ b ∈ GLint (Fin n) O,
      (g : Matrix (Fin n) (Fin n) L) =
        (a : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) * (b : Matrix (Fin n) (Fin n) L)

def divInd {n : ℕ} (O : Subring L) (d : List ℤ) : GL (Fin n) L → ℂ := Set.indicator {g | HasDiv O d g} 1

end Local

section Global

variable {E : Type} [Field E] [NumberField E]

variable [StarRing E]

end Global

variable {D : D7}

end GlobalTheory.SphPar

end
end
