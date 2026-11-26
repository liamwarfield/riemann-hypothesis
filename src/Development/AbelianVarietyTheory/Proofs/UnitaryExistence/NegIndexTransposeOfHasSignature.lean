module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameRingOverTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealDivisibleEqZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetNeZeroOfOrth
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RightInvariantOfCovolume
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LocClauseOfUnifPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtFieldPfA
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NegIndexTransposeOfHasSignature
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

noncomputable section

namespace GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix in
theorem negIndex_transpose_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature J p q) : GlobalTheory.Inertia.negIndex Jᵀ = q ∧ J.det ≠ 0 := by
  obtain ⟨e, P, hP⟩ := h
  have hd : Formalism.UG.Jpq p q = diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    rw [← fromBlocks_diagonal, Formalism.UG.Jpq]
    congr 1
    rw [← diagonal_neg]
    rfl
  have hPd : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).det ≠ 0 := P.det_ne_zero
  constructor
  · have ht := congrArg Matrix.transpose hP
    rw [hd, diagonal_transpose, transpose_mul, transpose_mul, Formalism.UG.cT, transpose_transpose,
      ← Matrix.mul_assoc] at ht
    have h1 := GlobalTheory.Inertia.negIndex_eq_card_of_congr_diagonal hPd ht
    have h2 : (J.reindex e e)ᵀ = Jᵀ.submatrix e.symm e.symm := rfl
    rw [h2, GlobalTheory.Inertia.negIndex_submatrix_equiv] at h1
    rw [h1, Finset.card_filter, Fintype.sum_sum_type]
    simp [not_lt.2 (zero_le_one' ℝ)]
  · intro h0
    have h1 := congrArg Matrix.det hP
    rw [det_mul, det_mul, det_reindex_self, h0, hd, det_diagonal] at h1
    simp only [mul_zero, zero_mul] at h1
    refine Finset.prod_ne_zero_iff.2 (fun k _ => ?_) h1.symm
    rcases k with k | k <;> simp

variable {D : D7}

theorem cc_gmW (V : HSp D) {r : ℕ} (hr : V.rank = r) (a b : Fin r) :
    cc (gmW V hr a b) = gmW V hr b a := by
  subst hr
  show IsCMField.complexConj D.host.E (-(V.hT (V.frame b) (V.frame a))) = -(V.hT (V.frame a) (V.frame b))
  rw [map_neg]
  exact congrArg Neg.neg (LinearMap.isSymm_def.1 V.herm (V.frame b) (V.frame a))

theorem herm_gmW (V : HSp D) {r : ℕ} (hr : V.rank = r) (x y : V.V) :
    herm (gmW V hr) (V.frame.equivFun x ∘ Fin.cast hr.symm) (V.frame.equivFun y ∘ Fin.cast hr.symm) =
      -V.hT y x := by
  subst hr
  rw [Formalism.L2.Pj.DatLin.sesq_repr V.hT V.frame y x, Finset.sum_comm, herm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  show V.frame.repr x a * (-(V.hT (V.frame b) (V.frame a))) * star (V.frame.repr y b) = _
  ring

theorem trace_herm_gmW (V : HSp D) {r : ℕ} (hr : V.rank = r) (x y : V.V) :
    Algebra.trace ℚ D.host.E (D.host.xi0 *
      herm (gmW V hr) (V.frame.equivFun x ∘ Fin.cast hr.symm) (V.frame.equivFun y ∘ Fin.cast hr.symm)) =
      Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT x y) := by
  rw [herm_gmW, ← Formalism.L2.Pj.trace_cc D (D.host.xi0 * V.hT x y), map_mul (IsCMField.complexConj D.host.E), conj_xi0_alt]
  have h : IsCMField.complexConj D.host.E (V.hT x y) = V.hT y x := LinearMap.isSymm_def.1 V.herm x y
  rw [h, mul_neg, neg_mul]

theorem posIndex_gmW (V : HSp D) (hV : V.SigOK) {r : ℕ} (hr : V.rank = r) (τ : D.host.E →+* ℂ) :
    GlobalTheory.Inertia.posIndex ((gmW V hr).map τ) = (V.sig τ).2 ∧ (gmW V hr).det ≠ 0 := by
  subst hr
  obtain ⟨h1, h2⟩ := negIndex_transpose_of_hasSignature (hV τ)
  have e : gmW V rfl = -V.gram.transpose := rfl
  constructor
  · rw [← h1, ← GlobalTheory.Inertia.posIndex_neg, e]
    congr 1
    ext a b
    simp
  · rw [e, Matrix.det_neg, Matrix.det_transpose]
    refine mul_ne_zero (pow_ne_zero _ (by simp)) fun h0 => h2 ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

end GlobalTheory.RecDict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniversalFrameTestRing
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniversalFrameTestRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem _root_.GlobalTheory.Frames.exists_univFrame_testRing : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (p : _root_.Formalism.L2.Pj.TRing c.F) (y₀ : _root_.Formalism.L2.Pj.FrPt Xo c p.R),
    ∃ (A : _root_.Formalism.L2.Pj.TRing c.F) (π : p.R →ₐ[c.F] A.R)
      (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R)) (s : (A.R)ˣ)
      (u : _root_.Formalism.L2.Pj.FrPt Xo c A.R), _root_.GlobalTheory.Frames.UnivFrame y₀ π X s u := by
  intro hbc E _ _ _ H Dw l Xo c p y₀
  obtain ⟨A, π, X, s, h⟩ := _root_.GlobalTheory.exists_frameRing_testRing c.F (E →+* ℂ) Dw.mult p
  obtain ⟨u₀, hu₀⟩ := _root_.GlobalTheory.Frames.FramedBaseChange.exists_frMap hbc E H Dw l Xo c p.R A.R π y₀
  obtain ⟨u, hu, -⟩ := _root_.GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c A.R u₀ X s h.1
  exact ⟨A, π, X, s, u, h, u₀, hu₀, hu⟩

end GlobalTheory.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniversalFrameTestRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universalFrame_testRing : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : TRing c.F) (y₀ : FrPt Xo c p.R), ∃ (A : TRing c.F) (π : p.R →ₐ[c.F] A.R) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R)) (s : (A.R)ˣ) (u : FrPt Xo c A.R), UnivFrame y₀ π X s u := by
  first | exact @GlobalTheory.Frames.exists_univFrame_testRing | exact GlobalTheory.Frames.exists_univFrame_testRing | (intros; apply GlobalTheory.Frames.exists_univFrame_testRing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ComponentAttainedAtBaseFrame
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

open scoped Matrix nonZeroDivisors

theorem comp_adelic_of_tower (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (ξ : E) (hξ : ξ ≠ 0)
    (A B : Type) [AddCommGroup A] [Module (𝓞 E) A] [AddCommGroup B] [Module (𝓞 E) B]
    (EA : A → A → ℤ) (EB : B → B → ℤ) (io : A →ₗ[𝓞 E] (Fin n → E)) (hio : Function.Injective io)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (φ : B ≃ₗ[𝓞 E] Λ)
    (hL : (LinearMap.range io).FG) (hLs : Submodule.span E (LinearMap.range io : Set (Fin n → E)) = ⊤)
    (hΛ : Λ.FG) (hΛs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (hA : ∀ x y, ((EA x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * ∑ a, ∑ b, io x a * G a b * c (io y b)))
    (hB : ∀ x y, ((EB x y : ℤ) : ℚ) =
      Algebra.trace ℚ E (ξ * ∑ a, ∑ b, (φ x : Fin n → E) a * G a b * c ((φ y : Fin n → E) b)))
    (f : ℕ → A →ₗ[𝓞 E] B)
    (h1 : ∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e)
    (h2 : ∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e)
    (h3 : ∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ EB (f n a) (f n a') - EA a a') :
    ∃ g : GL (Fin n) (AdLat.RA F E),
      (g : Matrix (Fin n) (Fin n) (AdLat.RA F E)).mulVec '' (AdLat.hat F (LinearMap.range io : Set (Fin n → E))) =
        (AdLat.hat F (Λ : Set (Fin n → E))) ∧
      (∀ N : ℕ, 0 < N → ∀ a : A, ∃ w ∈ (AdLat.hat F (Λ : Set (Fin n → E))),
        (g : Matrix (Fin n) (Fin n) (AdLat.RA F E)) *ᵥ AdLat.fv F (io a) =
          AdLat.fv F (φ (f N a) : Fin n → E) + N • w) ∧
      ∀ x y, AdLat.hermA c G ((g : Matrix (Fin n) (Fin n) (AdLat.RA F E)) *ᵥ x)
        ((g : Matrix (Fin n) (Fin n) (AdLat.RA F E)) *ᵥ y) = AdLat.hermA c G x y := by
  let ψ : A ≃ₗ[𝓞 E] LinearMap.range io := LinearEquiv.ofInjective io hio
  have hψ : ∀ a, (ψ a : Fin n → E) = io a := fun a => rfl
  let f' : ℕ → (LinearMap.range io →ₗ[𝓞 E] Λ) := fun N => φ.toLinearMap ∘ₗ f N ∘ₗ ψ.symm.toLinearMap
  have hf' : ∀ N a, f' N (ψ a) = φ (f N a) := fun N a => by simp [f']
  obtain ⟨g, hg1, hg2, hg3⟩ := AdLat.exists_adelic_matrix_of_tower F E n (LinearMap.range io) Λ f' hL hLs hΛ hΛs
    (fun N m hN hm a => by
      obtain ⟨a, rfl⟩ := ψ.surjective a
      obtain ⟨e, he⟩ := h1 N m hN hm a
      exact ⟨φ e, by rw [hf', hf', he, map_add (f := _), map_nsmul]⟩)
    (fun N hN => by
      refine ⟨fun a => ?_, fun a' => ?_⟩
      · obtain ⟨a, rfl⟩ := ψ.surjective a
        rw [hf']
        constructor
        · rintro ⟨v, hv⟩
          obtain ⟨v, rfl⟩ := φ.surjective v
          obtain ⟨e, he⟩ := ((h2 N hN).1 a).1 ⟨v, φ.injective (by rw [hv, map_nsmul])⟩
          exact ⟨ψ e, by rw [he, map_nsmul]⟩
        · rintro ⟨v, hv⟩
          obtain ⟨v, rfl⟩ := ψ.surjective v
          obtain ⟨e, he⟩ := ((h2 N hN).1 a).2 ⟨v, ψ.injective (by rw [hv, map_nsmul])⟩
          exact ⟨φ e, by rw [he, map_nsmul]⟩
      · obtain ⟨b, rfl⟩ := φ.surjective a'
        obtain ⟨a, e, he⟩ := (h2 N hN).2 b
        exact ⟨ψ a, φ e, by rw [hf', ← map_nsmul, ← map_add (f := _), ← he]⟩)
  refine ⟨g, hg1, fun N hN a => ?_, ?_⟩
  · obtain ⟨w, hw, h⟩ := hg2 N hN (ψ a)
    exact ⟨w, hw, by rw [← hf', ← h, hψ]⟩
  let J : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.spanSingleton _ ξ⁻¹ * FractionalIdeal.dual ℤ ℚ 1
  have hJ : ∀ z : E, (∀ s : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (ξ * ((s : E) * z)) = k) → z ∈ J := by
    intro z hz
    refine FractionalIdeal.mem_singleton_mul.2 ⟨ξ * z, ?_, by field_simp⟩
    rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)]
    intro a ha
    obtain ⟨s, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨k, hk⟩ := hz s
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast, ← hk]
    congr 1
    change ξ * ((s : E) * z) = ξ * z * (s : E)
    ring
  have hsm : ∀ (s : 𝓞 E) (x y : Fin n → E), (∑ a, ∑ b, (s • x) a * G a b * c (y b)) =
      (s : E) * ∑ a, ∑ b, x a * G a b * c (y b) := by
    intro s x y
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change ((s : E) * x a) * _ * _ = _
    ring
  refine hg3 c G J (fun x hx y hy => hJ _ fun s => ?_) (fun N hN x y => ?_)
  · obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
    obtain ⟨b, hb⟩ := φ.surjective ⟨y, hy⟩
    refine ⟨EB (s • a) b, ?_⟩
    rw [hB, map_smul, ha, hb, ← hsm]
    rfl
  · obtain ⟨a, rfl⟩ := ψ.surjective x
    obtain ⟨b, rfl⟩ := ψ.surjective y
    rw [hf', hf', hψ, hψ]
    have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have hN'' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    refine ⟨(N : E)⁻¹ * ((∑ i, ∑ j, (φ (f N a) : Fin n → E) i * G i j * c ((φ (f N b) : Fin n → E) j)) -
      ∑ i, ∑ j, io a i * G i j * c (io b j)), hJ _ fun s => ?_, ?_⟩
    · obtain ⟨k, hk⟩ := h3 N hN (s • a) b
      refine ⟨k, ?_⟩
      have hk' := congrArg (Int.cast : ℤ → ℚ) hk
      push_cast at hk'
      rw [hA, hB, map_smul, map_smul, map_smul, Submodule.coe_smul, hsm, hsm, ← map_sub] at hk'
      apply mul_left_cancel₀ hN''
      rw [← hk', ← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul]
      congr 1
      field_simp
    · rw [nsmul_eq_mul, mul_inv_cancel_left₀ hN', add_sub_cancel]

theorem comp_AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    exact D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem comp_latG (D : D7) (V : HSp D) :
    (latG V 1).FG ∧ Submodule.span D.host.E (latG V 1 : Set (Fin V.rank → D.host.E)) = ⊤ ∧ ∀ g : GA D V,
      (latG V g : Set (Fin V.rank → D.host.E)) = AdLat.latOf D.host.F (finHom V g).1 (latG V 1) ∧
      (latGHat V g : Set (Fin V.rank → AdLat.RA D.host.F D.host.E)) =
        (finHom V g).1.mulVec '' (AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E))) := by
  let e : V.V →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
    (V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map e
  have hfg : L.FG := V.standardTuple_isLattice.fg.map e
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have h := congrArg (Submodule.map (V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)))
      hfull
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h
    exact h
  have hhat : latHat V = AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    unfold latHat AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, e x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have h1 : latG V 1 = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA, ∃ x ∈ L, w = a • x} := by
    unfold latG gLat
    congr 1
    ext w
    have hc := (AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank L hfg hsp).1
    simp only [map_one, Units.val_one, Set.mem_setOf_eq, hhat, Set.mem_image, Matrix.one_mulVec, exists_eq_right,
      SetLike.mem_coe, ← hc]
    rfl
  have hs := fun g : GA D V => AdLat.scale_latOf D.host.F D.host.E V.rank L (finHom V g) D.host.AA (latG V 1)
    hfg hsp (comp_AA_ne_zero D) h1
  refine ⟨(hs 1).2.2.1, (hs 1).2.2.2, fun g => ⟨?_, ?_⟩⟩
  · rw [← (hs g).1]
    unfold latG gLat
    rw [hhat]
    rfl
  · rw [← (hs g).2.1]
    unfold latGHat gLat
    rw [hhat]

theorem comp_mem_HR (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (c : E ≃ₐ[F] E) (σ : E →ₐ[F] E) (hc : ∀ x, c x = σ x) (G : Matrix (Fin n) (Fin n) E)
    (g : GL (Fin n) (AdLat.RA F E))
    (hg : ∀ x y, AdLat.hermA c (-G.transpose) (g.1 *ᵥ x) (g.1 *ᵥ y) = AdLat.hermA c (-G.transpose) x y) :
    g ∈ HR (Af F) σ G := by
  have hc' : (c : E →ₐ[F] E) = σ := AlgHom.ext hc
  change Formalism.UG.cT _ _ * _ * _ = _
  ext i j
  have h := hg (Pi.single j 1) (Pi.single i 1)
  simp only [AdLat.hermA, AdLat.sg, hc', Matrix.mulVec_single_one, Matrix.col_apply, Matrix.neg_apply,
    Matrix.transpose_apply, TensorProduct.tmul_neg, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_inj] at h
  simp only [Pi.single_apply, apply_ite (Algebra.TensorProduct.map (AlgHom.id F (FiniteAdeleRing (𝓞 F) F)) σ),
    map_one, map_zero, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  simp only [Matrix.mul_apply, Formalism.UG.cT, JR, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  change _ * (1 ⊗ₜ _) * _ = _ * _ * sigR _ σ _
  ring

theorem comp_sub_eq {A : Type} [AddCommGroup A] (N : ℕ) (x e w : A) : x - (x + N • e + N • w) = N • -(e + w) := by
  rw [smul_neg, smul_add]
  abel

end GlobalTheory.RecDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnThetaAlgebraicGeneratorFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnThetaAlgebraicGeneratorFactor
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding Unf GoodEmb relab perFr gxFst gxSnd toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.HolGen

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem chart_iff {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (q : Sp ℂ ⟶ Gx x) (j : Xo.univ.t.PP.L.ι) :
    ⊤ ≤ q ⁻¹ᵁ (PPx x).U (fun _ => j) ↔ ⊤ ≤ (q ≫ gxFst x) ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
  rw [top_le_preimage_iff_mem, top_le_preimage_iff_mem]
  constructor
  · intro hp
    exact Set.mem_iInter.1 hp (0 : Fin 1)
  · intro hp
    exact Set.mem_iInter.2 fun _ => hp

theorem exists_pt {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (s : Sp ℂ ⟶ Sp R) (p : Sp ℂ ⟶ Xo.univ.t.G.left)
    (h : s ≫ x = p ≫ Xo.univ.t.G.hom) : ∃ q : Sp ℂ ⟶ Gx x, q ≫ gxFst x = p ∧ q ≫ gxSnd x = s :=
  ⟨pullback.lift (f := x) (g := Xo.univ.t.G.hom) s p h, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

theorem val_pull {R : Type} [CommRing R] (φ : R →+* ℂ) (x₀ : Sp R ⟶ Xo.X) (x : Sp ℂ ⟶ Xo.X)
    (s₀ : LB.Sec (PPx x₀)) (s : LB.Sec (PPx x)) (pm : Gx x ⟶ Gx x₀) (h₁ : pm ≫ gxFst x₀ = gxFst x)
    (h₂ : pm ≫ gxSnd x₀ = gxSnd x ≫ spMap φ)
    (h₃ : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x).U i ≤ pm ⁻¹ᵁ (PPx x₀).U i),
      (pm.appLE _ _ h).hom (s₀.f i) = s.f i)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (pt : Sp ℂ ⟶ Gx x) (q : Sp ℂ ⟶ Gx x₀) (e₁ : q ≫ gxFst x₀ = pt ≫ gxFst x)
    (e₂ : pt ≫ gxSnd x = 𝟙 _) (e₃ : q ≫ gxSnd x₀ = spMap φ) (hp : ⊤ ≤ pt ⁻¹ᵁ (PPx x).U i) :
    valAt' pt ((PPx x).U i) (s.f i) = valAt' q ((PPx x₀).U i) (s₀.f i) := by
  have hq : q = pt ≫ pm := SecCalc.pm_ext _ _
    (e₁.trans (show pt ≫ gxFst x = (pt ≫ pm) ≫ gxFst x₀ by rw [Category.assoc, h₁]))
    (e₃.trans (show spMap φ = (pt ≫ pm) ≫ gxSnd x₀ by
      rw [Category.assoc, h₂, ← Category.assoc, e₂, Category.id_comp]))
  rw [← h₃ i (SecCalc.ppx_le pm h₁ i), hq]
  exact valAt'_appLE pt pm _ _ _ _ hp

theorem val_mul_pull (hT : Out.SecTwistSt) {R : Type} [CommRing R] (φ : R →+* ℂ) (a : ℂ) (x₀ : Sp R ⟶ Xo.X)
    (x y : Sp ℂ ⟶ Xo.X) (hxy : y = x)
    (s₀ : LB.Sec (PPx x₀)) (s : LB.Sec (PPx x)) (t : LB.Sec (PPx y)) (pm : Gx x ⟶ Gx x₀)
    (h₁ : pm ≫ gxFst x₀ = gxFst x) (h₂ : pm ≫ gxSnd x₀ = gxSnd x ≫ spMap φ)
    (h₃ : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x).U i ≤ pm ⁻¹ᵁ (PPx x₀).U i),
      (pm.appLE _ _ h).hom (s₀.f i) = s.f i) (hst : SecBC (RingHom.id ℂ) a x y s t)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (pt : Sp ℂ ⟶ Gx y) (q : Sp ℂ ⟶ Gx x₀) (e₁ : q ≫ gxFst x₀ = pt ≫ gxFst y)
    (e₂ : pt ≫ gxSnd y = 𝟙 _) (e₃ : q ≫ gxSnd x₀ = spMap φ) (hp : ⊤ ≤ pt ⁻¹ᵁ (PPx y).U i) :
    valAt' pt ((PPx y).U i) (t.f i) = a * valAt' q ((PPx x₀).U i) (s₀.f i) := by
  subst hxy
  have hy : y = spMap (RingHom.id ℂ) ≫ y := by rw [SecCalc.spMap_id', Category.id_comp]
  have ht := ((SecCalc.sec_calc E H Dw l Xo ℂ ℂ ℂ _ _ y y y hy hy).2.1 a s t).1 hst i
  rw [ht, (sec_values_complex_fibre hT E H Dw l Xo y s).1 a i pt e₂,
    val_pull φ x₀ y s₀ s pm h₁ h₂ h₃ i pt q e₁ e₂ e₃ hp]

theorem exists_val_ne (hT : Out.SecTwistSt) {R : Type} [CommRing R] (φ : R →+* ℂ) (x₀ : Sp R ⟶ Xo.X)
    (x u : Sp ℂ ⟶ Xo.X) (hu : u = x) (s₀ : LB.Sec (PPx x₀)) (s : LB.Sec (PPx x)) (pm : Gx x ⟶ Gx x₀)
    (h₁ : pm ≫ gxFst x₀ = gxFst x) (h₂ : pm ≫ gxSnd x₀ = gxSnd x ≫ spMap φ)
    (h₃ : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x).U i ≤ pm ⁻¹ᵁ (PPx x₀).U i),
      (pm.appLE _ _ h).hom (s₀.f i) = s.f i) (hs : SecGen x s) :
    ∃ (e : Over.mk u ⟶ Xo.univ.t.G) (j : Xo.univ.t.PP.L.ι), ∀ q : Sp ℂ ⟶ Gx x₀, q ≫ gxFst x₀ = e.left →
      q ≫ gxSnd x₀ = spMap φ → valAt' q ((PPx x₀).U (fun _ => j)) (s₀.f (fun _ => j)) ≠ 0 := by
  subst hu
  obtain ⟨i, pt, hpt, hv⟩ := (sec_values_complex_fibre hT E H Dw l Xo u s).2.1.1 hs
  obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i (0 : Fin 1), funext fun k : Fin 1 => congrArg i (Subsingleton.elim _ _)⟩
  have hc : gxSnd u ≫ u = gxFst u ≫ Xo.univ.t.G.hom := pullback.condition (f := u) (g := Xo.univ.t.G.hom)
  refine ⟨Over.homMk (pt ≫ gxFst u) ?_, j, fun q e₁ e₃ => ?_⟩
  · show (pt ≫ gxFst u) ≫ Xo.univ.t.G.hom = u
    rw [Category.assoc, ← hc, ← Category.assoc, hpt, Category.id_comp]
  · rw [← val_pull φ x₀ u s₀ s pm h₁ h₂ h₃ _ pt q e₁ hpt e₃ (top_le_preimage_of_valAt'_ne_zero _ hv)]
    exact hv

end

theorem differentiableOn_generator_factor : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (R : Type) [CommRing R] [Algebra c.F R] (y₀ : FrPt Xo c R) (B : Set (Fin T.m → ℂ)) (ψ : (Fin T.m → ℂ) → (R →ₐ[c.F] CAt σ)) (κ : (Fin T.m → ℂ) → ℂ) (z y : (Fin T.m → ℂ) → FrPt Xo c (CAt σ)) (G : (Fin T.m → ℂ) → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : (Fin T.m → ℂ) → CAt σ), IsOpen B → B ⊆ T.co ⁻¹' (M.X k).dom → (∀ t : R, DifferentiableOn ℂ (fun b => toC (ψ b t)) B) → (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b) ∧ IsThetaPt T b (κ b) (y b)) → DifferentiableOn ℂ κ B → DifferentiableOn ℂ (fun b => toC (a b)) B := by
  intro hT E _ _ _ H Dw l Xo c σ g e F r M k T R _ _ y₀ B ψ κ z y G a hB hBd hψ hb hκ b₀ hb₀
  let φ : (Fin T.m → ℂ) → (R →+* ℂ) := fun b => (ψ b).toRingHom
  have hP : IsHolPeriods (F.Di k) (fun j => relab c σ (e j).1) B (fun b => T.Pf (T.co b)) :=
    ⟨fun b hb => T.holPer.1 b (hBd hb), fun x => (T.holPer.2 x).mono hBd⟩
  have hux : ∀ b ∈ B, F.u k (T.Pf (T.co b)) = (z b).x := fun b h =>
    (hb b h).2.2.1.symm.trans (hb b h).2.1.1
  obtain ⟨pm₀, p₁, p₂, p₃⟩ := (hb b₀ hb₀).1.2.2
  obtain ⟨e₀, j, hne⟩ := exists_val_ne hT (φ b₀) y₀.x (z b₀).x _ (hux b₀ hb₀) y₀.s (z b₀).s pm₀ p₁ p₂ p₃ (z b₀).gen
  obtain ⟨w₀, rfl⟩ := F.ex_onto k _ (hP.1 b₀ hb₀) e₀
  have hq₁ : ∀ b ∈ B, ∃ q : Sp ℂ ⟶ Gx y₀.x, q ≫ gxFst y₀.x = (F.ex k (T.Pf (T.co b)) w₀).left ∧
      q ≫ gxSnd y₀.x = spMap (φ b) := fun b h =>
    exists_pt _ _ _ (((hb b h).1.1.symm.trans (hux b h).symm).trans (Over.w (F.ex k (T.Pf (T.co b)) w₀)).symm)
  have hq₂ : ∀ b, ∃ q : Sp ℂ ⟶ Gx y₀.x, b ∈ B → q ≫ gxFst y₀.x = (F.ex k (T.Pf (T.co b)) w₀).left ∧
      q ≫ gxSnd y₀.x = spMap (φ b) := fun b => by
    by_cases h : b ∈ B
    · exact (hq₁ b h).imp fun _ h' _ => h'
    · exact ⟨(hq₁ b₀ hb₀).choose, fun h' => absurd h' h⟩
  choose q hq using hq₂
  have hι : Differentiable ℂ (fun b : Fin T.m → ℂ => ((b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ))) := by fun_prop
  have hol : IsHolTo B q := by
    refine HolPullback.isHolTo_of_components _ B _ _ _ _ (gxSnd y₀.x) (gxFst y₀.x) y₀.x Xo.univ.t.G.hom q
      (IsPullback.of_hasPullback y₀.x Xo.univ.t.G.hom) hB ?_ ?_
    · exact LocLift.isHolTo_congr (ThetaValueCont.isHolTo_spMap hB φ hψ) fun b h => (hq b h).2
    · exact LocLift.isHolTo_congr (LocLift.isHolTo_comp (F.hol k _ B _ hB hP).2 hB hι.differentiableOn
        fun b h => ⟨h, trivial⟩) fun b h => (hq b h).1
  have hW := (hol ((Gx y₀.x).basicOpen (y₀.s.f (fun _ => j))) 0).1
  set W := {b ∈ B | ⊤ ≤ q b ⁻¹ᵁ (Gx y₀.x).basicOpen (y₀.s.f (fun _ => j))} with hWd
  have hb₀W : b₀ ∈ W := ⟨hb₀, (top_le_preimage_basicOpen_iff _ _ _).2 (hne _ (hq b₀ hb₀).1 (hq b₀ hb₀).2)⟩
  have vnz : ∀ b ∈ W, valAt' (q b) ((PPx y₀.x).U (fun _ => j)) (y₀.s.f (fun _ => j)) ≠ 0 := fun b h =>
    (top_le_preimage_basicOpen_iff _ _ _).1 h.2
  have m₁ : ∀ b ∈ W, ⊤ ≤ q b ⁻¹ᵁ (PPx y₀.x).U (fun _ => j) := fun b h =>
    top_le_preimage_of_valAt'_ne_zero _ (vnz b h)
  have m₂ : ∀ b ∈ W, ⊤ ≤ (F.ex k (T.Pf (T.co b)) w₀).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun b h => by
    rw [← (hq b h.1).1]
    exact (chart_iff _ _ _).1 (m₁ b h)
  have hθ := (ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).2 T.m B T.h T.ta hB
    (fun b h => ⟨(T.norm b (hBd h)).2.1, (T.norm b (hBd h)).2.2.1⟩)
    (fun i i' => ⟨(T.hol i i').1.mono hBd, (T.hol i i').2.mono hBd⟩)
  have d₀ : DifferentiableOn ℂ κ W := hκ.mono fun b h => h.1
  have d₁ : DifferentiableOn ℂ (fun b => thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w₀)) W :=
    DifferentiableOn.comp (f := fun b : Fin T.m → ℂ => ((b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ)))
      (g := fun bz : (Fin T.m → ℂ) × (Fin g → ℂ) => thetaChar (T.ta bz.1) T.c₁ T.c₂ (T.h bz.1 *ᵥ bz.2))
      hθ hι.differentiableOn fun b h => ⟨h.1, trivial⟩
  have d₂ : DifferentiableOn ℂ (fun b => T.fr j (b, w₀)) W :=
    DifferentiableOn.comp (f := fun b : Fin T.m → ℂ => ((b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ))) (g := T.fr j)
      (T.fr_hol j) hι.differentiableOn fun b h => ⟨hBd h.1, m₂ b h⟩
  have d₃ : DifferentiableOn ℂ (fun b => valAt' (q b) ((PPx y₀.x).U (fun _ => j)) (y₀.s.f (fun _ => j))) W :=
    (hol _ _).2.mono fun b h => ⟨h.1, m₁ b h⟩
  have key : ∀ b ∈ W, κ b * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w₀) * T.fr j (b, w₀) =
      toC (a b) * valAt' (q b) ((PPx y₀.x).U (fun _ => j)) (y₀.s.f (fun _ => j)) := fun b h => by
    obtain ⟨⟨-, -, pm, p₁, p₂, p₃⟩, ⟨hyz, -, hbc⟩, hyu, -, hth⟩ := hb b h.1
    obtain ⟨pt, e₁, e₂⟩ := exists_pt (R := ℂ) (y b).x (𝟙 _) (F.ex k (T.Pf (T.co b)) w₀).left
      (((Category.id_comp _).trans hyu).trans (Over.w (F.ex k (T.Pf (T.co b)) w₀)).symm)
    refine (hth j w₀ pt e₁ e₂ (m₂ b h)).symm.trans ?_
    refine val_mul_pull hT (φ b) (toC (a b)) y₀.x (z b).x (y b).x hyz y₀.s (z b).s (y b).s pm p₁ p₂ p₃ hbc _ pt (q b)
      ((hq b h.1).1.trans e₁.symm) e₂ (hq b h.1).2 ((chart_iff _ _ _).2 ?_)
    rw [e₁]
    exact m₂ b h
  have d : DifferentiableOn ℂ (fun b => toC (a b)) W := (((d₀.mul d₁).mul d₂).mul (d₃.inv vnz)).congr fun b h =>
    ((mul_inv_eq_iff_eq_mul₀ (vnz b h)).2 (key b h)).symm
  exact (d.differentiableAt (hW.mem_nhds hb₀W)).differentiableWithinAt

end GlobalTheory.HolGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnThetaAlgebraicGeneratorFactorStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding Unf GoodEmb relab perFr gxFst gxSnd toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_theta_algebraic_generator_factor : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (R : Type) [CommRing R] [Algebra c.F R] (y₀ : FrPt Xo c R) (B : Set (Fin T.m → ℂ)) (ψ : (Fin T.m → ℂ) → (R →ₐ[c.F] CAt σ)) (κ : (Fin T.m → ℂ) → ℂ) (z y : (Fin T.m → ℂ) → FrPt Xo c (CAt σ)) (G : (Fin T.m → ℂ) → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : (Fin T.m → ℂ) → CAt σ), IsOpen B → B ⊆ T.co ⁻¹' (M.X k).dom → (∀ t : R, DifferentiableOn ℂ (fun b => toC (ψ b t)) B) → (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b) ∧ IsThetaPt T b (κ b) (y b)) → DifferentiableOn ℂ κ B → DifferentiableOn ℂ (fun b => toC (a b)) B := by
  first | exact @GlobalTheory.HolGen.differentiableOn_generator_factor | exact GlobalTheory.HolGen.differentiableOn_generator_factor | (intros; apply GlobalTheory.HolGen.differentiableOn_generator_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspSquareIntegrableIffUnfolded
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeterssonCompare

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2
open scoped ENNReal TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open Classical in
def archHom (V : HSp D) (τ : D.host.E →+* ℂ) : GA D V →* Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  if h : ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ then
    h.choose.mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp (infHom V))
  else 1

theorem archHom_eq (V : HSp D) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) (g : GA D V) : archHom V τ g = Pj.archM V θ g := by
  have h' : ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ := ⟨θ, h⟩
  rw [archHom, dite_eq_left h', GlobalTheory.LettersCheck.isInfEmb_unique τ _ θ h'.choose_spec h]
  rfl

theorem isHermitian_gram (V : HSp D) (τ : D.host.E →+* ℂ) : (V.gram.map τ).IsHermitian := by
  ext a b
  have h := V.herm.eq (V.frame b) (V.frame a)
  show star (τ (V.hT (V.frame b) (V.frame a))) = τ (V.hT (V.frame a) (V.frame b))
  rw [← h]
  exact (IsCMField.complexEmbedding_complexConj D.host.E τ _).symm

theorem lintegral_adelic (V : HSp D) {Comp : Type} [Fintype Comp] {r : ℕ} (X : Comp → Data D.host.E r)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) {Kf : Subgroup (GA D V)}
    {th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r} {N : ℕ} (hN : 0 < N)
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hd : Pj.DictIsUnif V dict Kf th hr) (hK : Pj.IsLevelK V N Kf)
    (hU : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1)
    (hΨ : ∀ k k', (X k).Ψ = (X k').Ψ ∧ (X k).p0 = (X k').p0) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (h0 : μ 𝓕 ≠ 0) (h1 : μ 𝓕 ≠ ⊤) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ F : ∀ k, Frame (X k).Ψ r → ℝ≥0∞, (∀ k, Measurable (F k)) →
      (∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, F k (lact γ x) = F k x) →
      (∀ k, ∀ b ∈ Bor (X k).Ψ r, ∀ x ∈ (X k).dom, F k (rmul x b) = F k x) →
      Measurable (fun g => F (dict g).1 (dict g).2) ∧
        ∫⁻ g in 𝓕, F (dict g).1 (dict g).2 ∂μ = κ * ∑ k, IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt (X k) (F k) := by
  subst hr
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  obtain ⟨_, _, _⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  haveI : μ.IsMulRightInvariant := ⟨GlobalTheory.AutQuotCheck.rightInvariant_of_covolume (GQ V) μ h𝓕 h0 h1⟩
  have hmem : ∀ h, h ∈ (Kf.map (finHom V)).comap (finHom V) ↔ ∃ a ∈ GinfC V, ∃ z ∈ Kf, h = a * z := by
    intro h
    constructor
    · rintro ⟨z, hz, e⟩
      refine ⟨h * z⁻¹, ?_, z, hz, (inv_mul_cancel_right _ _).symm⟩
      show finHom V (h * z⁻¹) = 1
      rw [map_mul, map_inv, e, mul_inv_cancel]
    · rintro ⟨a, ha, z, hz, rfl⟩
      refine ⟨z, hz, ?_⟩
      rw [map_mul, show finHom V a = 1 from ha, one_mul]
  have hopen : IsOpen (((Kf.map (finHom V)).comap (finHom V) : Subgroup (GA D V)) : Set (GA D V)) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
      (Filter.mem_of_superset (GlobalTheory.LevelOpen.level_mem_nhds D V N Kf hN hK 1) ?_)
    rintro _ ⟨z, hz, a, ha, rfl⟩
    refine ⟨z, hz, ?_⟩
    rw [one_mul, map_mul, show finHom V a = 1 from ha, mul_one]
  have hg := fun k => (GlobalTheory.UnitaryGlue.adelic_glue D V).2 (X k).Ψ (th k) (X k).cmType (hth k)
  have ha : ∀ k (τ : (X k).Ψ) g, archHom V τ.1 g = Pj.archM V (th k τ) g := fun k τ g => archHom_eq V (hth k τ) g
  have htr : ∀ (u J : Matrix (Fin V.rank) (Fin V.rank) ℂ), uᵀ * Jᵀ * u.map (starRingEnd ℂ) = Jᵀ ↔
      (u.map (starRingEnd ℂ))ᵀ * J * u = J := by
    intro u J
    rw [← Matrix.transpose_inj]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  obtain ⟨dL, dR, ⟨x0, d0, dI⟩, dD, -, dF⟩ := hd
  refine lintegral_dict X μ (GQ V) (GinfC V) Kf _ h𝓕 h0 h1 hopen.measurableSet hmem dict (archHom V)
    (fun τ => (V.gram.map τ)ᵀ) x0 hΨ (fun τ => ⟨(isHermitian_gram V τ).transpose, ?_⟩) (fun k τ => ?_)
    (fun k τ g => ?_) (fun k u hu => ?_) (fun k τ z hz => ?_) (fun k γ hγ h => ?_) dL dR d0 (fun g h hh => ?_) dD dF hU
  · rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ).2 (GlobalTheory.UnitaryGlue.gram_det_ne_zero V)
  · exact ((hg k).2.2.1 τ).congr fun g => (ha k τ g).symm
  · rw [htr, ha]
    exact GlobalTheory.RecDictModel.archM_unitary V (hth k τ) g
  · obtain ⟨h, hh, e⟩ := (hg k).2.2.2 u fun τ => (htr _ _).1 (hu τ)
    exact ⟨h, hh, fun τ => (ha k τ h).trans (e τ)⟩
  · rw [ha, Pj.archM, show infHom V z = 1 from ((hK z).1 hz).1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · obtain ⟨τ⟩ : Nonempty (X k).Ψ := by
      obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
      by_cases hτ : τ ∈ (X k).Ψ
      · exact ⟨⟨τ, hτ⟩⟩
      · exact ⟨⟨_, not_not.1 (mt ((X k).cmType τ).2 hτ)⟩⟩
    obtain ⟨γ₀, -, e0⟩ := Subgroup.mem_subgroupOf.1 hγ
    have e1 : (matHom V γ).1 = (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (AF D.host.F)) := (congrArg Units.val e0).symm
    have e2 : Pj.archM V (th k τ) γ = (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 := by
      have : ((γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Ainf D.host.F))).map (th k τ) =
          (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 := by
        ext i j
        exact (hth k τ).1 _
      rw [← this, ← GlobalTheory.UnitaryGlue.map_map_inclR (fstA D.host.F), ← e1]
      rfl
    have e3 : (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 := by
      refine Matrix.map_injective τ.1.injective ?_
      show (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 = (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1
      rw [← e2, ← ha, h τ, Matrix.map_one _ (map_zero _) (map_one _)]
    refine Subtype.ext (Units.ext (e1.trans ?_))
    rw [e3]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · simp only [ha]
    exact dI g h hh

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Pj.Unf Xo c σ r)

theorem measurable_onQ_adel (V : HSp D) {Comp : Type} {X : Comp → Data D.host.E r}
    {dict : GA D V → Σ k, Frame (X k).Ψ r} {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)}
    {th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r} {N : ℕ} (hN : 0 < N)
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hd : Pj.DictIsUnif V dict Kf th hr) (hK : Pj.IsLevelK V N Kf)
    (hm : Pj.MuUnit V dict mu) (hc : Continuous mu) (P : Pj.FDSec X) (hP : ∀ k, ContinuousOn (P k) (X k).dom)
    (hΓ : ∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = P k x) :
    Measurable (Pj.onQ V (Pj.adel V dict mu P)) := by
  have hloc := GlobalTheory.DictLocTest.locClause_of_unif_places hd (fun k hk => ((hK k).1 hk).1)
    (GlobalTheory.LevelOpen.level_mem_nhds D V N Kf hN hK) fun k τ => ⟨τ.1, hth k τ⟩
  have hC : Continuous fun g => mu g * P (dict g).1 (dict g).2 := by
    rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨M, hM, k, x, hx, hs⟩ := hloc g₀
    have h1 : ContinuousOn (fun g => mu g * P k (x g)) M :=
      hc.continuousOn.mul ((hP k).comp hx fun g hg => (hs g hg).1)
    refine (h1.continuousAt hM).congr ?_
    filter_upwards [hM] with g hg
    obtain ⟨hxd, γ, hγ, he⟩ := hs g hg
    rw [he]
    exact congrArg (mu g * ·) (hΓ k γ hγ _ hxd).symm
  have hL : ∀ g g', g * g'⁻¹ ∈ GQ V → mu g' * P (dict g').1 (dict g').2 = mu g * P (dict g).1 (dict g).2 := by
    intro g g' h4
    obtain ⟨γ, hγ, e⟩ := hd.1 _ h4 g'
    have e' := hm.1 (g * g'⁻¹) g'
    rw [inv_mul_cancel_right] at e e'
    rw [hm.2.2.1 _ h4, one_mul] at e'
    rw [e, e']
    exact congrArg (mu g' * ·) (hΓ _ γ hγ _ (hd.2.2.2.1 _)).symm
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  rw [measurable_from_quotient]
  have : (Pj.onQ V (Pj.adel V dict mu P) ∘ Quotient.mk'') = fun g => mu g * P (dict g).1 (dict g).2 :=
    funext fun g => hL g (Pj.autMk V g).out (QuotientGroup.rightRel_apply.1 (Quotient.mk_out g))
  rw [this]
  exact hC.measurable

end GlobalTheory.PeterssonCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReFrameIffReframeIntegral
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ReframeClauses

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.L2.PjFree (FrBaseChg ReFrame XoNumPt TanLin SClause IntRebase)

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

end Dual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

section Comb

variable {S S' : Type} [CommRing S] [CommRing S']

theorem isTanAt_of_isCombAt {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, IsTanAt x (v j)) {a : Fin m → S} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (h : IsCombAt x v a w) : IsTanAt x w := by
  rw [← (ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_isComb_iff x v hv a w).1 h]
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_comb_tan x _ (fun j => hv j) a

theorem isEigAt_of_isCombAt [Algebra c.F S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsTanAt x (v j)) {τ : E →+* ℂ}
    (he : ∀ j, IsEigAt c τ (v j)) {a : Fin m → S} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (h : IsCombAt x v a w) : IsEigAt c τ w := by
  rw [← (ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_isComb_iff x v hv a w).1 h]
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_comb_eig x c τ (fun j => ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_lt x (v j) (hv j)) he a

end Comb

section Gen

variable {S : Type} [CommRing S] [Algebra c.F S]

end Gen

variable (Xo c)

variable {Xo c}

end GlobalTheory.ReframeClauses
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndHalfEqPrimeProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndHalfEqPrimeProduct
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.LevelHalf

theorem map_comap_half (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H)
    (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) :
    (l.Mb.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = l.Mb := by
  refine le_antisymm Ideal.map_comap_le ?_
  have hw : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (LPb.w0K D) = H.w0 := by
    apply RingOfIntegers.ext
    have h2 : ((2 * H.w0 : 𝓞 D.host.E) : D.host.E) = ((1 + H.rt : 𝓞 D.host.E) : D.host.E) := by
      rw [H.two_weight_eq_one_add_root]
    have h3 : (2 : D.host.E) * (H.w0 : D.host.E) = 1 + (H.rt : D.host.E) := h2
    show ((1 + D.host.sqrtMinusD) / 2 : D.host.E) = (H.w0 : D.host.E)
    rw [← hrt, ← h3]
    field_simp
  conv_lhs => rw [l.fromK]
  rw [Ideal.span_le]
  rintro a ⟨ha, ha'⟩
  have hr : a ∈ (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)).toIntAlgHom.range := by
    refine Algebra.adjoin_le ?_ ha'
    rintro _ rfl
    exact ⟨LPb.w0K D, hw⟩
  obtain ⟨b, rfl⟩ := hr
  exact Ideal.mem_map_of_mem _ ha

theorem exists_prime_half (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H)
    (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) {p : ℕ} (hp : p.Prime) (hpM : p ∣ l.M) :
    ∃ pb : HeightOneSpectrum (𝓞 D.host.K), (p : 𝓞 D.host.K) ∈ pb.asIdeal ∧
      pb.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = l.Mb ⊔ Ideal.span {(p : 𝓞 D.host.E)} := by
  set I : Ideal (𝓞 D.host.K) := l.Mb.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ⊔
    Ideal.span {(p : 𝓞 D.host.K)} with hI
  have hmap : I.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = l.Mb ⊔ Ideal.span {(p : 𝓞 D.host.E)} := by
    rw [hI, Ideal.map_sup, map_comap_half D H l hrt, Ideal.map_span, Set.image_singleton, map_natCast]
  have hbar : (Ideal.span {(p : 𝓞 D.host.E)}).map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) =
      Ideal.span {(p : 𝓞 D.host.E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hnt := LPb.span_p_ne_top D hp
  have hle : Ideal.span {(p : 𝓞 D.host.K)} ≤ I := le_sup_right
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hN := congrArg Ideal.absNorm hJ
  rw [map_mul, LPb.absNorm_span_p] at hN
  obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ hN.symm)
  have hi1 : i = 1 := by
    interval_cases i
    · exfalso
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at hieq
      rw [hieq, Ideal.map_top] at hmap
      have hmap' := congrArg (Ideal.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) hmap
      rw [Ideal.map_top, Ideal.map_sup, hbar] at hmap'
      have hc := (Ideal.isCoprime_iff_sup_eq.2 hmap.symm).mul_left (Ideal.isCoprime_iff_sup_eq.2 hmap'.symm)
      rw [l.prod, Ideal.isCoprime_iff_sup_eq, sup_eq_right.2
        (Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hpM))] at hc
      exact hnt hc
    · rfl
    · exfalso
      rw [hieq] at hN
      have hJ1 : Ideal.absNorm J = 1 :=
        Nat.eq_of_mul_eq_mul_left (by have := hp.pos; positivity) (hN.symm.trans (mul_one _).symm)
      rw [Ideal.absNorm_eq_one_iff] at hJ1
      rw [hJ1, Ideal.mul_top] at hJ
      rw [← hJ, Ideal.map_span, Set.image_singleton, map_natCast] at hmap
      have h1 : l.Mb ≤ Ideal.span {(p : 𝓞 D.host.E)} := hmap ▸ le_sup_left
      have h2 : l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ Ideal.span {(p : 𝓞 D.host.E)} :=
        hbar ▸ Ideal.map_mono h1
      exact hnt (top_le_iff.1 (l.coprime ▸ sup_le h1 h2))
  rw [hi1, pow_one] at hieq
  have hprime : I.IsPrime :=
    Ideal.isPrime_of_irreducible_absNorm (by rw [hieq]; exact hp.prime.irreducible)
  have hne : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hieq
    exact hp.ne_zero hieq.symm
  exact ⟨⟨I, hprime, hne⟩, hle (Ideal.subset_span rfl), hmap⟩

theorem eq_mul_sup {R : Type*} [CommRing R] (I : Ideal R) {a b : R} (hab : IsCoprime a b) (h : a * b ∈ I) :
    I = (I ⊔ Ideal.span {a}) * (I ⊔ Ideal.span {b}) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u, v, huv⟩ := hab
    have e : x = (u * a) * x + x * (v * b) := by linear_combination (-x) * huv
    rw [e]
    exact Ideal.add_mem _
      (Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
        (Ideal.mem_sup_left hx))
      (Ideal.mul_mem_mul (Ideal.mem_sup_left hx)
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))))
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton]
    exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left)
      (sup_le Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h))

theorem good_and_half_eq_prod : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H), (H.rt : D.host.E) = D.host.sqrtMinusD → l.M = D.host.g 0 * D.host.g 1 → (∀ p : ℕ, p.Prime → l.GoodAt p) ∧ ∃ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) ∧ l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  intro D H l hrt hM
  refine ⟨fun p _ => GlobalTheory.PinNum.goodAt_of_two_primes l (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne hM p, ?_⟩
  have hd : ∀ k : Fin 2, D.host.g k ∣ l.M := by
    intro k
    rw [hM]
    fin_cases k
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  choose pb h1 h2 using fun k => exists_prime_half D H l hrt (D.host.g_prime k) (hd k)
  refine ⟨pb, h1, ?_⟩
  rw [Fin.prod_univ_two, h2 0, h2 1]
  apply eq_mul_sup
  · exact Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
  · rw [← Nat.cast_mul, ← hM]
    have : Ideal.span {((l.M : ℕ) : 𝓞 D.host.E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact this (Ideal.subset_span rfl)

end GlobalTheory.LevelHalf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndHalfEqPrimeProductStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_good_and_half_eq_prime_product : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H), (H.rt : D.host.E) = D.host.sqrtMinusD → l.M = D.host.g 0 * D.host.g 1 → (∀ p : ℕ, p.Prime → l.GoodAt p) ∧ ∃ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) ∧ l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  first | exact @GlobalTheory.LevelHalf.good_and_half_eq_prod | exact GlobalTheory.LevelHalf.good_and_half_eq_prod | (intros; apply GlobalTheory.LevelHalf.good_and_half_eq_prod <;> assumption)
end
end
