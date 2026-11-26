module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPair

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionDegreeDvdCardInvariants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionDegreeDvdCardInvariants
open Polynomial

namespace GlobalTheory.InvariantSpecialisation

theorem exists_extension {A B Ω : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B))
    [Field Ω] [IsAlgClosed Ω] (e : A →+* Ω) :
    ∃ φ : B →+* Ω, φ.comp (algebraMap A B) = e := by
  haveI hP : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B) (RingHom.ker e) ⊥
    (by
      intro a ha
      have : a = 0 := hinj (by simpa using ha)
      simp [this])
  haveI : Q.LiesOver (RingHom.ker e) := ⟨hQP.symm⟩
  letI : Algebra (A ⧸ RingHom.ker e) Ω := (RingHom.kerLift e).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker e) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective e)
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker e) (B ⧸ Q) := inferInstance
  haveI : IsDomain (A ⧸ RingHom.ker e) := Ideal.Quotient.isDomain _
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain _
  haveI : FaithfulSMul (A ⧸ RingHom.ker e) (B ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker e) (B ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker e) Ω :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective e)
  haveI : Algebra.IsAlgebraic (A ⧸ RingHom.ker e) (B ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let l : (B ⧸ Q) →ₐ[A ⧸ RingHom.ker e] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(l : (B ⧸ Q) →+* Ω).comp (Ideal.Quotient.mk Q), ?_⟩
  ext a
  have h := l.commutes (Ideal.Quotient.mk _ a)
  exact h

theorem exists_smul_of_comp_eq {A B Ω : Type} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
    [Field Ω] [CharZero Ω] (φ ψ : B →+* Ω)
    (h : ψ.comp (algebraMap A B) = φ.comp (algebraMap A B)) :
    ∃ g : G, ∀ b, ψ b = φ (g • b) := by
  classical
  letI := Fintype.ofFinite G
  have h1 : ∀ b, ∃ g : G, ψ b = φ (g • b) := by
    intro b
    obtain ⟨p, hp⟩ := Algebra.IsInvariant.charpoly_mem_lifts A B G b
    have hp' : p.map (algebraMap A B) = MulSemiringAction.charpoly G b := hp
    have e1 : (MulSemiringAction.charpoly G b).map ψ = (MulSemiringAction.charpoly G b).map φ := by
      rw [← hp', Polynomial.map_map, Polynomial.map_map, h]
    have e2 : ((MulSemiringAction.charpoly G b).map ψ).eval (ψ b) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom, MulSemiringAction.eval_charpoly, map_zero]
    rw [e1, MulSemiringAction.charpoly_eq, Polynomial.map_prod, Polynomial.eval_prod,
      Finset.prod_eq_zero_iff] at e2
    obtain ⟨g, -, hg⟩ := e2
    refine ⟨g, ?_⟩
    simpa [sub_eq_zero] using hg
  let H : G → AddSubgroup B := fun g =>
    { carrier := {b | ψ b = φ (g • b)}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add (f := _), smul_add, map_add (f := _), ha, hb]
      neg_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_neg, smul_neg, map_neg, ha] }
  obtain ⟨g, -, hg⟩ := AddSubgroup.exists_finiteIndex_of_leftCoset_cover
    (H := H) (g := fun _ => 0) (s := Finset.univ) (by
      rw [Set.eq_univ_iff_forall]
      intro b
      obtain ⟨g, hg⟩ := h1 b
      simp only [Set.mem_iUnion]
      exact ⟨g, Finset.mem_univ _, b, hg, zero_add b⟩)
  refine ⟨g, fun b => ?_⟩
  have h2 : ψ ((H g).index • b) = φ (g • ((H g).index • b)) := (H g).nsmul_index_mem b
  rw [smul_comm g, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at h2
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hg.index_ne_zero) h2

theorem exists_finite_extension_finrank_dvd :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G] [Finite G]
      [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G],
      Function.Injective (algebraMap A B) → ∀ (k : Type) [Field k] [CharZero k] (ev : A →+* k),
      ∃ (K' : Type) (_ : Field K') (_ : Algebra k K') (β : B →+* K'), FiniteDimensional k K' ∧
        Module.finrank k K' ∣ Nat.card G ∧
        β.comp (algebraMap A B) = (algebraMap k K').comp ev := by
  intro A B _ _ _ G _ _ _ _ _ hinj k _ _ ev
  haveI := Algebra.IsInvariant.isIntegral A B G
  let Ω := AlgebraicClosure k
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  obtain ⟨φ, hφ⟩ := exists_extension hinj ((algebraMap k Ω).comp ev)
  let K : IntermediateField k Ω := IntermediateField.adjoin k (Set.range φ)
  let P : Subgroup ((Ω ≃ₐ[k] Ω) × G) :=
    { carrier := {x | ∀ b, x.1 (φ b) = φ (x.2 • b)}
      one_mem' := by intro b; simp
      mul_mem' := by
        intro x y hx hy b
        simp only [Prod.fst_mul, Prod.snd_mul, AlgEquiv.mul_apply]
        rw [hy, hx, mul_smul]
      inv_mem' := by
        intro x hx b
        apply x.1.injective
        rw [hx]
        simp }
  let p₁ : P →* (Ω ≃ₐ[k] Ω) := (MonoidHom.fst _ _).comp P.subtype
  let p₂ : P →* G := (MonoidHom.snd _ _).comp P.subtype
  have hsurj : Function.Surjective p₁ := by
    intro σ
    obtain ⟨g, hg⟩ := exists_smul_of_comp_eq (A := A) G φ ((σ : Ω →+* Ω).comp φ) (by
      rw [RingHom.comp_assoc, hφ]
      ext a
      simp)
    exact ⟨⟨(σ, g), hg⟩, rfl⟩
  have hle : p₂.ker ≤ K.fixingSubgroup.comap p₁ := by
    rintro ⟨⟨σ, g⟩, hx⟩ hg
    have hg1 : g = 1 := hg
    subst hg1
    change σ ∈ K.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hxK
    induction hxK using IntermediateField.adjoin_induction with
    | mem x hx' =>
      obtain ⟨b, rfl⟩ := hx'
      simpa using hx b
    | algebraMap c => exact σ.commutes c
    | add x y _ _ h1 h2 => rw [map_add (f := _), h1, h2]
    | inv x _ h1 => rw [map_inv₀, h1]
    | mul x y _ _ h1 h2 => rw [map_mul, h1, h2]
  have hdvd : Module.finrank k K ∣ Nat.card G := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      ← Subgroup.index_comap_of_surjective _ hsurj]
    refine (Subgroup.index_dvd_of_le hle).trans ?_
    rw [Subgroup.index_ker]
    exact Subgroup.card_subgroup_dvd_card _
  refine ⟨K, inferInstance, inferInstance,
    φ.codRestrict K (fun b => IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩), ?_, hdvd, ?_⟩
  · exact Module.finite_of_finrank_pos (Nat.pos_of_dvd_of_pos hdvd Nat.card_pos)
  · ext a
    exact RingHom.congr_fun hφ a

end GlobalTheory.InvariantSpecialisation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionDegreeDvdCardInvariantsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_degree_dvd_card_invariants : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G], Function.Injective (algebraMap A B) → ∀ (k : Type) [Field k] [CharZero k] (ev : A →+* k), ∃ (K' : Type) (_ : Field K') (_ : Algebra k K') (β : B →+* K'), FiniteDimensional k K' ∧ Module.finrank k K' ∣ Nat.card G ∧ β.comp (algebraMap A B) = (algebraMap k K').comp ev := by
  first | exact @GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd | exact GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd | (intros; apply GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeMapConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.TripleCplxAt

variable {m n : Type} [Fintype m] [Fintype n]

theorem map_conj_conj {m n : Type} (M : Matrix m n ℂ) : (M.map conj).map conj = M := by
  ext; simp

theorem smul_map_conj {m n : Type} (c : ℂ) (M : Matrix m n ℂ) : (c • M).map conj = conj c • M.map conj := by
  ext; simp

theorem transpose_map_conj {k : Type} (M : Matrix k k ℂ) : (M.map conj)ᵀ = Mᴴ := by
  ext; simp [Matrix.conjTranspose_apply]

theorem cartan_comm {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : sᴴ * G = G * s := by
  obtain ⟨h1, h2, -⟩ := h
  calc sᴴ * G = sᴴ * G * (s * s) := by rw [h1, Matrix.mul_one]
    _ = G * s := by rw [← Matrix.mul_assoc, h2]

theorem mul_cols {a b d k : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (X : Matrix (Fin b) (Fin d) ℂ) (f : Fin k → Fin d) :
    (A * X).submatrix id f = A * X.submatrix id f := by
  ext; simp [Matrix.mul_apply]

theorem smul_cols {a d k : ℕ} (c : ℂ) (X : Matrix (Fin a) (Fin d) ℂ) (f : Fin k → Fin d) :
    (c • X).submatrix id f = c • X.submatrix id f := by
  ext; simp

theorem conj_hyp {a p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (X X' : Matrix (Fin a) (Fin d) ℂ)
    (sW : Matrix (Fin a) (Fin a) ℂ) (cV : Matrix (Fin p) (Fin p) ℂ) (cV₁ : Matrix (Fin q) (Fin q) ℂ)
    (hX : X'.map conj = Complex.I • (sW * X.map conj * ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e cV cV₁).map conj)ᵀ)) :
    X' = (-Complex.I) • (sW.map conj * X * (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e cV cV₁)ᵀ) := by
  have h := congrArg (fun M => M.map (starRingEnd ℂ)) hX
  simp only [map_conj_conj, smul_map_conj, Matrix.map_mul, Complex.conj_I] at h
  rw [h, ← Matrix.transpose_map, map_conj_conj]

theorem algV {a p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (X X' : Matrix (Fin a) (Fin d) ℂ)
    (sW G : Matrix (Fin a) (Fin a) ℂ) (cV : Matrix (Fin p) (Fin p) ℂ) (cV₁ : Matrix (Fin q) (Fin q) ℂ)
    (hX : X'.map conj = Complex.I • (sW * X.map conj * ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e cV cV₁).map conj)ᵀ))
    (hs : sWᴴ * G = G * sW) :
    (X'.submatrix id fun k => e (.inl k))ᵀ * (-G) =
      Complex.I • (cV * ((X.submatrix id fun k => e (.inl k))ᵀ * (-G)) * (-sW)) := by
  rw [conj_hyp e X X' sW cV cV₁ hX, smul_cols, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose,
    GlobalTheory.RouteCoords.submatrix_mul_blk_inl, mul_cols, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, transpose_map_conj]
  simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg, smul_neg, neg_smul, neg_neg, hs]

theorem algW {a p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (X X' : Matrix (Fin a) (Fin d) ℂ)
    (sW : Matrix (Fin a) (Fin a) ℂ) (cV : Matrix (Fin p) (Fin p) ℂ) (cV₁ G₁ : Matrix (Fin q) (Fin q) ℂ)
    (hX : X'.map conj = Complex.I • (sW * X.map conj * ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e cV cV₁).map conj)ᵀ))
    (hs : cV₁ᴴ * G₁ = G₁ * cV₁) :
    -((X'.submatrix id fun k => e (.inr k)).map conj * G₁) =
      Complex.I • (sW * (-((X.submatrix id fun k => e (.inr k)).map conj * G₁)) * cV₁) := by
  rw [conj_hyp e X X' sW cV cV₁ hX, smul_cols, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose,
    GlobalTheory.RouteCoords.submatrix_mul_blk_inr, mul_cols, smul_map_conj, Matrix.map_mul, Matrix.map_mul, map_conj_conj,
    Matrix.transpose_map, transpose_map_conj]
  simp only [map_neg, Complex.conj_I, neg_neg, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul,
    Matrix.mul_neg, smul_neg, neg_smul, hs]

end GlobalTheory.TripleCplxAt

namespace GlobalTheory.TripleCplxAt

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (blk)

section Adelic

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem compAt_mul' (θ : InfFam D) (τ : D.what₂.Tau) {a b c : ℕ} (A : Mx D a b) (B : Mx D b c) :
    compAt θ τ (A * B) = compAt θ τ A * compAt θ τ B :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_neg' (θ : InfFam D) (τ : D.what₂.Tau) {a b : ℕ} (A : Mx D a b) :
    compAt θ τ (-A) = -compAt θ τ A :=
  Matrix.map_neg _ (fun a => map_neg ((θ τ).comp (infPart D)) a) A

theorem compAt_inc (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) {a b : ℕ} (A : Matrix (Fin a) (Fin b) D.host.E) :
    compAt θ τ (A.map (incA D)) = A.map (tauE D τ) := by
  ext x y; exact (hθ τ).1 (A x y)

theorem compAt_conj (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) {a b : ℕ} (A : Mx D a b) :
    compAt θ τ (A.map (cA D)) = (compAt θ τ A).map conj := by
  ext x y; exact (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.1 _ _

theorem compAt_mapV (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : Num G i j) (u : Pt G i j) :
    compAt θ τ (mapV e u) = ((compAt θ τ u).submatrix id fun k => e (.inl k))ᵀ * (-gramAt D (spW G i j) τ) := by
  show compAt θ τ (HMul.hMul (colV e u)ᵀ ((negSp (spW G i j)).gram.map (incA D))) = _
  rw [compAt_mul', compAt_inc θ hθ, negSp_gram, Matrix.map_neg _ (map_neg _)]
  rfl

theorem compAt_mapW (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : Num G i j) (u : Pt G i j) :
    compAt θ τ (mapW e u) = -(((compAt θ τ u).submatrix id fun k => e (.inr k)).map conj * gramAt D (spV₁ G i j) τ) := by
  show compAt θ τ (-HMul.hMul ((u.submatrix id fun k => e (.inr k)).map (cA D)) ((spV₁ G i j).gram.map (incA D))) = _
  rw [compAt_neg', compAt_mul', compAt_inc θ hθ, compAt_conj θ hθ]
  rfl

end Adelic

theorem cplx_pair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E), IsTripleOf W M t i j e Bs Γ X →
    ∀ u u' : Pt G i j, (∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
      Complex.I • (Γ.V.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Γ.W.θ w)ᵀ)) → ∀ τ,
      compAt W.θ τ (mapV e u') = cplxO (-W.cart (.grid (i + 1) (j + 1)) τ) (W.cart (.grid i (j + 1)) τ) (compAt W.θ τ (mapV e u)) ∧
      compAt W.θ τ (mapW e u') = cplxO (W.cart (.grid (i + 1) j) τ) (W.cart (.grid (i + 1) (j + 1)) τ) (compAt W.θ τ (mapW e u)) := by
  intro D T L sc G W M t i j e Bs Γ X h u u' hu τ
  obtain ⟨w, hpi, hV, hWW⟩ : ∃ w, (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w) y = conj (W.θ τ (infPart D y))) ∧
      Γ.V.θ w = W.cart (.grid (i + 1) (j + 1)) τ ∧
      Γ.W.θ w = (blk e (W.cart (.grid i (j + 1)) τ) (W.cart (.grid (i + 1) j) τ)).map conj := by
    obtain ⟨w, hw⟩ : ∃ w : InfinitePlace D.host.F, w = InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)) :=
      ⟨_, rfl⟩
    obtain ⟨τ', hemb, hV, -, hWW⟩ := h.cart w
    have h1 : (Bs.emb w).1.comp (algebraMap D.host.F D.host.E) = w.embedding := (Bs.emb w).2
    have h2 : (tauE D τ').comp (algebraMap D.host.F D.host.E) = NumberField.ComplexEmbedding.conjugate w.embedding := by
      ext x
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← h1]
      simp [hemb]
    have hh : ((starRingEnd ℂ).comp (tauE D τ')).comp (algebraMap D.host.F D.host.E) = w.embedding := by
      rw [← h1]; ext x; simp [hemb]
    have hb : Bs.emb w = ⟨_, hh⟩ := Subtype.ext (RingHom.ext hemb)
    have hτ : τ' = τ := (GlobalTheory.CMTypePlaces.places_bijective D).1 (by
      show InfinitePlace.mk ((tauE D τ').comp _) = InfinitePlace.mk ((tauE D τ).comp _)
      rw [h2, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, hw])
    subst hτ
    exact ⟨w, fun y => by rw [hb]; exact GlobalTheory.ConjInfExp.piInf_eq W.θ W.θ_is _ w hh y, hV, hWW⟩
  have hmap : ∀ v : Pt G i j, v.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) = (compAt W.θ τ v).map conj :=
    fun v => Matrix.ext fun a b => hpi _
  have hX := hu w
  rw [hmap, hmap, hV, hWW] at hX
  have cW := W.cart_is (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨by omega, by omega⟩ τ
  have cV₁ := W.cart_is (.grid ((i : ℕ) + 1) (j : ℕ)) ⟨by omega, by omega⟩ τ
  refine ⟨?_, ?_⟩
  · rw [compAt_mapV W.θ W.θ_is, compAt_mapV W.θ W.θ_is]
    exact algV e _ _ _ _ _ _ hX (cartan_comm cW)
  · rw [compAt_mapW W.θ W.θ_is, compAt_mapW W.θ W.θ_is]
    exact algW e _ _ _ _ _ _ hX (cartan_comm cV₁)

end GlobalTheory.TripleCplxAt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumThetaFunctionDerivativeComplexStructur
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumThetaFunctionDerivativeComplexStructur
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section
namespace GlobalTheory.FockLineJ

variable {D : D7}

theorem theta_realAd {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (t : ℝ) :
    θ τ (fstA D.host.F (realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E)) = t := by
  have h2 : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm := by
    have : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm = ⇑(GroundTheory.Global.homeomorphMixedSpace D.host.F).symm :=
      funext fun y => by
        rw [Homeomorph.eq_symm_apply]
        exact (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).apply_symm_apply y
    rw [this]
    exact (GroundTheory.Global.homeomorphMixedSpace D.host.F).symm.continuous
  let φ : ℝ →+* ℂ := ((θ τ).comp Algebra.TensorProduct.includeLeftRingHom).comp
    ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm.toRingHom.comp
      (algebraMap ℝ (mixedEmbedding.mixedSpace D.host.F)))
  have hφ : Continuous φ :=
    (hθ τ).2.comp (h2.comp (continuous_algebraMap ℝ (mixedEmbedding.mixedSpace D.host.F)))
  have e : ∀ s, φ s = θ τ (fstA D.host.F (realAd D.host.F s) ⊗ₜ[D.host.F] (1 : D.host.E)) := fun s => rfl
  rw [← e]
  have h1 : φ t = t * φ 1 := GlobalTheory.WeilVacMove.additive_real φ.toAddMonoidHom hφ t
  rw [h1, map_one, mul_one]

theorem realAd_smul_eq (t : ℝ) (a : AE D) :
    realAd D.host.F t • a = (realAd D.host.F t ⊗ₜ[D.host.F] (1 : D.host.E)) * a := by
  rw [Algebra.smul_def]; rfl

theorem finPart_realAd_smul (t : ℝ) (a : AE D) : finPart D (realAd D.host.F t • a) = 0 := by
  rw [realAd_smul_eq, map_mul]
  have : finPart D (realAd D.host.F t ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 := by
    show sndA D.host.F (realAd D.host.F t) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E 1) = 0
    rw [show sndA D.host.F (realAd D.host.F t) = 0 from rfl, TensorProduct.zero_tmul]
  rw [this, zero_mul]

theorem theta_realAd_smul {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (t : ℝ) (a : AE D) :
    θ τ (infPart D (realAd D.host.F t • a)) = t * θ τ (infPart D a) := by
  rw [realAd_smul_eq, map_mul, map_mul]
  have : infPart D (realAd D.host.F t ⊗ₜ[D.host.F] (1 : D.host.E)) =
      fstA D.host.F (realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [this, theta_realAd hθ]


set_option synthInstance.maxHeartbeats 400000 in
theorem realAd_smul_eq_sum {m n : ℕ} {θ : InfFam D} (hθ : IsInfFam θ) {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (y : Mx D m n)
    (hy : ∀ τ, compAt θ τ y = z τ) (t : ℝ) :
    realAd D.host.F t • y = (∑ τ, lineAt θ τ (z τ)) t := by
  classical
  ext i j
  rw [← sub_eq_zero]
  have hl := fun τ => GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (z τ)
  have hs : ((∑ τ, lineAt θ τ (z τ)) t) i j = ∑ τ, lineAt θ τ (z τ) t i j := by
    generalize (Finset.univ : Finset D.what₂.Tau) = s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.sum_insert ha, AddMonoidHom.add_apply, Matrix.add_apply, ih]
  refine hσ.ext _ ?_ fun τ' => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sub, hs, map_sum, Matrix.smul_apply, finPart_realAd_smul, zero_sub, neg_eq_zero]
      exact Finset.sum_eq_zero fun τ _ => congrFun (congrFun ((hl τ).2.1 t) i) j
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sub, map_sub, hs, map_sum, map_sum, Matrix.smul_apply, theta_realAd_smul hθ, sub_eq_zero]
      have e1 : θ τ' (infPart D (y i j)) = z τ' i j := congrFun (congrFun (hy τ') i) j
      have e2 : ∀ τ, θ τ' (infPart D (lineAt θ τ (z τ) t i j)) = if τ' = τ then (t : ℂ) * z τ i j else 0 := by
        intro τ
        have h := congrFun (congrFun ((hl τ).2.2 t τ') i) j
        rw [compAt, Matrix.map_apply] at h
        rw [h]
        split_ifs <;> simp
      rw [e1, Finset.sum_congr rfl fun τ _ => e2 τ, Finset.sum_ite_eq]
      simp

theorem dLine_sum {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ι : Type} (s : Finset ι)
    (N : ι → ℝ →+ WO S T) (hN : ∀ i, Continuous (N i)) (hN0 : ∀ i t, (N i t).map (finPart D) = 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Continuous (⇑(∑ i ∈ s, N i) : ℝ → WO S T) ∧ (∀ t, ((∑ i ∈ s, N i) t).map (finPart D) = 0) ∧
      GlobalTheory.WeilVacMove.dLine ψ S T (∑ i ∈ s, N i) f = ∑ i ∈ s, GlobalTheory.WeilVacMove.dLine ψ S T (N i) f := by
  classical
  refine Finset.induction_on s ?_ ?_
  · refine ⟨?_, fun t => ?_, ?_⟩
    · rw [Finset.sum_empty]
      show Continuous fun _ : ℝ => (0 : WO S T)
      exact continuous_const
    · rw [Finset.sum_empty, AddMonoidHom.zero_apply]; ext i j; simp
    · rw [Finset.sum_empty, Finset.sum_empty]
      funext w
      simp [GlobalTheory.WeilVacMove.dLine]
  · intro a s ha ih
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨?_, fun t => ?_, ?_⟩
    · show Continuous fun t => N a t + (∑ x ∈ s, N x) t
      exact (hN a).add h1
    · rw [AddMonoidHom.add_apply]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, map_add]
      have ha := congrFun (congrFun (hN0 a t) i) j
      have hs := congrFun (congrFun (h2 t) i) j
      simpa only [Matrix.map_apply, Matrix.zero_apply, add_zero] using congrArg₂ (· + ·) ha hs
    · rw [GlobalTheory.BiJoinDeriv.dLine_add_line hψ (hN a) (hN0 a) h1 h2 hf, h3]

theorem fock_line_J : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ),
    IsStdChar D ψ (-1) → IsInfFam θ → IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
    ∀ x x' : WO S T, (∀ τ, compAt θ τ x' = cplxO (sS τ) (sT τ) (compAt θ τ x)) → ∀ w : WO S T, ∃ a : ℂ,
      HasDerivAt (fun t : ℝ => heisO ψ S T (realAd D.host.F t • x) f w) a 0 ∧
      HasDerivAt (fun t : ℝ => heisO ψ S T (realAd D.host.F t • x') f w) (Complex.I * a) 0 := by
  intro D ψ θ S T sS sT f hψ hθ hf hvac x x' hx' w
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hl := fun τ (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) => GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  let c : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun τ => compAt θ τ x
  let c' : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun τ => cplxO (sS τ) (sT τ) (c τ)
  obtain ⟨L1, L2, L3⟩ := dLine_sum hψ Finset.univ (fun τ => lineAt θ τ (c τ)) (fun τ => (hl τ _).1)
    (fun τ => (hl τ _).2.1) hf
  obtain ⟨M1, M2, M3⟩ := dLine_sum hψ Finset.univ (fun τ => lineAt θ τ (c' τ)) (fun τ => (hl τ _).1)
    (fun τ => (hl τ _).2.1) hf
  have e : ∀ t, realAd D.host.F t • x = (∑ τ, lineAt θ τ (c τ)) t :=
    realAd_smul_eq_sum hθ hσ c x (fun τ => rfl)
  have e' : ∀ t, realAd D.host.F t • x' = (∑ τ, lineAt θ τ (c' τ)) t :=
    realAd_smul_eq_sum hθ hσ c' x' hx'
  have hd := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ L1 L2 hf).1 w
  have hd' := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ M1 M2 hf).1 w
  refine ⟨GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c τ)) f w, ?_, ?_⟩
  · simp only [e]
    exact hd
  · have key : GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c' τ)) f w =
        Complex.I * GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c τ)) f w := by
      rw [L3, M3, Finset.sum_apply, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have h : GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c τ)) f w +
          Complex.I * GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c' τ)) f w = 0 := congrFun (hvac τ (c τ)) w
      linear_combination (-Complex.I) * h + GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c' τ)) f w * Complex.I_sq
    simp only [e']
    rw [← key]
    exact hd'

end GlobalTheory.FockLineJ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumThetaFunctionDerivativeComplexStructurStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacuum_thetaFunction_derivative_complex_structure : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ),
    IsStdChar D ψ (-1) → IsInfFam θ → IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
    ∀ x x' : WO S T, (∀ τ, compAt θ τ x' = cplxO (sS τ) (sT τ) (compAt θ τ x)) → ∀ w : WO S T, ∃ a : ℂ,
      HasDerivAt (fun t : ℝ => heisO ψ S T (realAd D.host.F t • x) f w) a 0 ∧
      HasDerivAt (fun t : ℝ => heisO ψ S T (realAd D.host.F t • x') f w) (Complex.I * a) 0 := by
  first | exact @GlobalTheory.FockLineJ.fock_line_J | exact GlobalTheory.FockLineJ.fock_line_J | (intros; apply GlobalTheory.FockLineJ.fock_line_J <;> assumption)
end
end
