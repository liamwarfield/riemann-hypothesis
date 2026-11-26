module

public import Development.AutomorphicArithmetic.AdelicQuotients.MemNhdsOneOfCongruenceLatticeOrder
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkFacArch

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.UnitaryLatticeExistsFrame
open scoped Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels UpperTheory.TP.BA

open scoped TensorProduct
open PositivityTheory.ThKH.Iwas (at_sg ev_sg mul_sg)

private theorem e0 {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (a : AF F) (x : E) :
    a • inclR (F := F) (AF F) x = a ⊗ₜ[F] x := by
  change (a * 1) ⊗ₜ[F] x = _
  rw [mul_one]

private theorem unit_at {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {s : 𝓞 F} (hs : s ∉ v.asIdeal) :
    ∃ t : Fv F v, t ∈ v.adicCompletionIntegers F ∧ (s : F) • sg v t = sg v 1 := by
  have hs0 : (s : F) ≠ 0 := fun h => hs (by
    rw [show s = 0 from RingOfIntegers.coe_injective (by simpa using h)]; exact zero_mem _)
  refine ⟨algebraMap F (Fv F v) (s : F)⁻¹, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h1 : v.valuation F (s : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) v).2 hs
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (s : F)⁻¹
    exact (h2.trans ((map_inv₀ _ _).trans ((congrArg _ h1).trans inv_one))).le
  · rw [← map_smul, Algebra.smul_def, ← map_mul, mul_inv_cancel₀ hs0, map_one]

private theorem key {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : Pl (F := F)) {s : F} {t : Fv F v}
    (h : s • sg v t = sg v 1) (x : E) :
    sg v t • inclR (F := F) (AF F) (algebraMap F E s * x) = sg v 1 • inclR (F := F) (AF F) x := by
  rw [e0, e0, ← Algebra.smul_def, ← TensorProduct.smul_tmul, h]

private theorem at_one {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {M : Type} [AddCommGroup M] [Module (AF F) M] (m : M) :
    At (evFin F v) (sg v 1 • m) := fun u hu => by
  rw [smul_smul, mul_sg, hu, zero_mul, map_zero, zero_smul]

theorem UpperTheory.unitaryLattice_exists_frame :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (X : Spc F E n) (v : Pl (F := F)), X.L.IsFullLattice E → ∃ b c, IsFr X v b c := by
  intro F E _ _ _ _ _ n X v hL
  haveI := hL
  obtain ⟨P, h1, h2⟩ := GlobalTheory.AdelicU.Frames.exists_rational_frame (F := F) X.L v
  have hss : sg v 1 * sg v 1 = sg v 1 := by rw [mul_sg, ev_sg, mul_one]
  have hPQ : incM F P.1 * incM F (P⁻¹).1 = 1 := by
    rw [incM, incM, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP : incM F (P⁻¹).1 * incM F P.1 = 1 := by
    rw [incM, incM, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨sg v 1 • incM F P.1, sg v 1 • incM F (P⁻¹).1, ⟨at_one v _, at_one v _, ?_, ?_, ?_, ?_⟩⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss, hPQ]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss, hQP]
  · intro j
    obtain ⟨s, hs, hy⟩ := h1 j
    obtain ⟨t, ht, hst⟩ := unit_at v hs
    refine AddSubgroup.subset_closure ⟨sg v t, at_sg t, by rwa [ev_sg], _, hy, funext fun i => ?_⟩
    exact (key v hst (P.1 i j)).symm
  · intro z hz i
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, ha', x, hx, rfl⟩ := hy
      obtain ⟨s, hs, hsx⟩ := h2 x hx
      obtain ⟨t, ht, hst⟩ := unit_at v hs
      obtain ⟨o, ho⟩ := hsx i (Set.mem_univ i)
      refine AddSubgroup.subset_closure ⟨a * sg v t, ?_, ?_, o, ?_⟩
      · exact fun u hu => by rw [smul_eq_mul, mul_comm u, mul_assoc, mul_comm _ u, ← smul_eq_mul u, at_sg t u hu, mul_zero]
      · rw [map_mul, ev_sg]
        exact mul_mem ha' ht
      · have ho' : ((o : 𝓞 E) : E) = algebraMap F E (s : F) * ((P⁻¹).1 *ᵥ x) i := by
          simpa using ho
        rw [ho', mul_smul, key v hst]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Matrix.mulVec, dotProduct, map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, Matrix.smul_apply, smul_mul_assoc, mul_smul_comm, smul_comm]
        rfl
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
    | neg y _ hy => rw [Matrix.mulVec_neg]; exact neg_mem hy
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.LatticeOrderExistsInverseOneAddUniformizerSmul
open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels UpperTheory.TP.BA

noncomputable section

namespace UpperTheory.AdelicOrderPrincipalUnitInverse

open PositivityTheory.ThKH.Iwas (ev_sg mul_sg at_sg)

private theorem unit_abs {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] (φ : O →+* A) (S : Subring A)
    (hφ : ∀ t, φ t ∈ S) (hint : ∀ x ∈ S, φ.IsIntegralElem x) {ϖ : O} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal O) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ S) :
    ∃ N : Matrix (Fin n) (Fin n) A, (∀ i j, N i j ∈ S) ∧ (1 + φ ϖ • M) * N = 1 := by
  let φS : O →+* S := φ.codRestrict S hφ
  letI : Algebra O S := φS.toAlgebra
  have hI : Algebra.IsIntegral O S := ⟨fun x => by
    obtain ⟨P, hP, h⟩ := hint x.1 x.2
    refine ⟨P, hP, ?_⟩
    apply Subtype.ext
    have : S.subtype (Polynomial.eval₂ φS x P) = Polynomial.eval₂ (S.subtype.comp φS) (S.subtype x) P :=
      Polynomial.hom_eval₂ P φS S.subtype x
    exact this.trans h⟩
  let M' : Matrix (Fin n) (Fin n) S := fun i j => ⟨M i j, hM i j⟩
  let Q : Matrix (Fin n) (Fin n) S := 1 + φS ϖ • M'
  have hdet : IsUnit Q.det := by
    by_contra h
    obtain ⟨m, hm, hq⟩ := exists_max_ideal_of_mem_nonunits h
    have hmax : (m.comap (algebraMap O S)).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) m
    have heq : m.comap (algebraMap O S) = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hmax
    have hϖm : φS ϖ ∈ m := by
      have : ϖ ∈ m.comap (algebraMap O S) := heq ▸ hϖ
      exact this
    have hmap : (Ideal.Quotient.mk m).mapMatrix Q = 1 := by
      ext i j
      have h0 : Ideal.Quotient.mk m (φS ϖ) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hϖm
      simp [Q, Matrix.one_apply, apply_ite, h0]
    have h1 : Ideal.Quotient.mk m Q.det = 1 := by
      rw [RingHom.map_det, hmap, Matrix.det_one]
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hq] at h1
    haveI := Ideal.Quotient.nontrivial_iff.2 hm.ne_top
    exact zero_ne_one h1
  have hQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hdet
  refine ⟨S.subtype.mapMatrix Q⁻¹, fun i j => (Q⁻¹ i j).2, ?_⟩
  have hQ' : S.subtype.mapMatrix Q = 1 + φ ϖ • M := by
    ext i j
    simp [Q, M', φS, Matrix.one_apply, apply_ite]
    rfl
  rw [← hQ', ← map_mul, hQ, map_one]

open PositivityTheory.ThKH.Iwas (sgE comp_sgE at_sgE sgE_comp eq_zero_of_at)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem oh_induct {v : Pl (F := F)} {P : AE F E → Prop}
    (hg : ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ o : 𝓞 E,
      P (a • inclR (F := F) (AF F) (o : E)))
    (h0 : P 0) (ha : ∀ x y, P x → P y → P (x + y)) (hn : ∀ x, P x → P (-x)) {x : AE F E} (hx : x ∈ Oh E v) : P x := by
  refine AddSubgroup.closure_induction (p := fun x _ => P x) ?_ h0 (fun x y _ _ => ha x y) (fun x _ => hn x) hx
  rintro z ⟨a, h1, h2, o, rfl⟩
  exact hg a h1 h2 o

private theorem e_smul {v : Pl (F := F)} {M : Type} [AddCommGroup M] [Module (AF F) M] {z : M} (h : At (evFin F v) z) :
    sg v 1 • z = z := by
  have h1 := h (1 - sg v 1) (by rw [map_sub, map_one, ev_sg, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1.symm

private theorem gen_mem {v : Pl (F := F)} (t : Fv F v) (ht : t ∈ v.adicCompletionIntegers F) : sg v t • (1 : AE F E) ∈ Oh E v :=
  AddSubgroup.subset_closure ⟨sg v t, at_sg t, by rw [ev_sg]; exact ht, 1, by simp⟩

private theorem oh_at {v : Pl (F := F)} {x : AE F E} (hx : x ∈ Oh E v) : At (evFin F v) x := by
  refine oh_induct (P := fun x => At (evFin F v) x) ?_ ?_ ?_ ?_ hx
  · intro a h1 _ o u hu
    rw [← smul_assoc, h1 u hu, zero_smul]
  · intro u _; exact smul_zero u
  · intro x y hx hy u hu; rw [smul_add, hx u hu, hy u hu, add_zero]
  · intro x hx u hu; rw [smul_neg, hx u hu, neg_zero]

private theorem oh_mul {v : Pl (F := F)} {x y : AE F E} (hx : x ∈ Oh E v) (hy : y ∈ Oh E v) : x * y ∈ Oh E v := by
  refine oh_induct (P := fun x => x * y ∈ Oh E v) ?_ (by simp [zero_mem]) ?_ ?_ hx
  · intro a h1 h2 o
    refine oh_induct (P := fun y => a • inclR (F := F) (AF F) (o : E) * y ∈ Oh E v) ?_ (by simp [zero_mem]) ?_ ?_ hy
    · intro a' h1' h2' o'
      refine AddSubgroup.subset_closure ⟨a * a', ?_, ?_, o * o', ?_⟩
      · intro u hu
        rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u a, h1 u hu, zero_mul]
      · rw [map_mul]; exact mul_mem h2 h2'
      · rw [smul_mul_smul_comm]; simp
    · intro x y hx hy; rw [mul_add]; exact add_mem hx hy
    · intro x hx; rw [mul_neg]; exact neg_mem hx
  · intro x z hx hz; rw [add_mul]; exact add_mem hx hz
  · intro x hx; rw [neg_mul]; exact neg_mem hx

private theorem sgE_mul {v : Pl (F := F)} (x y : TensorProduct F (Fv F v) E) : sgE E v (x * y) = sgE E v x * sgE E v y := by
  have h : compFin F E v (sgE E v x * sgE E v y) = x * y := by rw [map_mul, comp_sgE, comp_sgE]
  rw [← h, sgE_comp]
  refine e_smul (v := v) fun u hu => ?_
  rw [← smul_mul_assoc, at_sgE x u hu, zero_mul]

private theorem sgE_one {v : Pl (F := F)} : sgE E v 1 = sg v 1 • (1 : AE F E) := by
  simpa using sgE_comp (E := E) (v := v) (1 : AE F E)

private def phi (E : Type) [Field E] [Algebra F E] (v : Pl (F := F)) : v.adicCompletionIntegers F →+* TensorProduct F (Fv F v) E :=
  (algebraMap (Fv F v) (TensorProduct F (Fv F v) E)).comp (v.adicCompletionIntegers F).subtype

private def SS (E : Type) [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) : Subring (TensorProduct F (Fv F v) E) where
  carrier := {x | sgE E v x ∈ Oh E v ∧ (phi E v).IsIntegralElem x}
  mul_mem' := fun {x y} hx hy => ⟨by rw [sgE_mul]; exact oh_mul hx.1 hy.1, RingHom.IsIntegralElem.mul _ hx.2 hy.2⟩
  one_mem' := ⟨by rw [sgE_one]; exact gen_mem 1 (one_mem _), by
    simpa using (phi E v).isIntegralElem_map (x := 1)⟩
  add_mem' := fun {x y} hx hy => ⟨by rw [(sgE E v).map_add]; exact add_mem hx.1 hy.1, RingHom.IsIntegralElem.add _ hx.2 hy.2⟩
  zero_mem' := ⟨by rw [map_zero]; exact zero_mem _, RingHom.isIntegralElem_zero _⟩
  neg_mem' := fun {x} hx => ⟨by rw [map_neg]; exact neg_mem hx.1, RingHom.IsIntegralElem.neg _ hx.2⟩

private theorem phi_mem {v : Pl (F := F)} (t : v.adicCompletionIntegers F) : phi E v t ∈ SS E v := by
  refine ⟨?_, (phi E v).isIntegralElem_map⟩
  have h : sgE E v (phi E v t) = sg v (t : Fv F v) • (1 : AE F E) := by
    change sg v (t : Fv F v) ⊗ₜ[F] (1 : E) = sg v (t : Fv F v) • ((1 : AF F) ⊗ₜ[F] (1 : E))
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h]
  exact gen_mem _ t.2

private theorem comp_mem {v : Pl (F := F)} {x : AE F E} (hx : x ∈ Oh E v) : compFin F E v x ∈ SS E v := by
  refine ⟨by rw [sgE_comp, e_smul (oh_at hx)]; exact hx, ?_⟩
  refine oh_induct (P := fun x => (phi E v).IsIntegralElem (compFin F E v x)) ?_ ?_ ?_ ?_ hx
  · intro a _ h2 o
    have h : compFin F E v (a • inclR (F := F) (AF F) (o : E)) =
        phi E v ⟨evFin F v a, h2⟩ * (1 ⊗ₜ[F] (o : E)) := by
      have e1 : a • inclR (F := F) (AF F) (o : E) = a ⊗ₜ[F] (o : E) := by
        change a • ((1 : AF F) ⊗ₜ[F] (o : E)) = _
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e1]
      change evFin F v a ⊗ₜ[F] (o : E) = (evFin F v a ⊗ₜ[F] (1 : E)) * ((1 : Fv F v) ⊗ₜ[F] (o : E))
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h]
    refine RingHom.IsIntegralElem.mul _ (phi E v).isIntegralElem_map ?_
    obtain ⟨P, hP, h0⟩ := NumberField.RingOfIntegers.isIntegral_coe o
    refine ⟨P.map (Int.castRingHom _), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    let incl : E →+* TensorProduct F (Fv F v) E := inclR (F := F) (Fv F v)
    have hh : (phi E v).comp (Int.castRingHom _) = incl.comp (algebraMap ℤ E) := RingHom.ext_int _ _
    rw [hh]
    exact (Polynomial.hom_eval₂ P (algebraMap ℤ E) incl (o : E)).symm.trans (by rw [h0, map_zero])
  · rw [map_zero]; exact RingHom.isIntegralElem_zero _
  · intro x y hx hy; rw [map_add (f := _)]; exact RingHom.IsIntegralElem.add _ hx hy
  · intro x hx; rw [map_neg]; exact RingHom.IsIntegralElem.neg _ hx

private theorem smul_comp {v : Pl (F := F)} (a : AF F) (z : AE F E) : compFin F E v (a • z) = evFin F v a • compFin F E v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    change evFin F v (a * b) ⊗ₜ[F] x = evFin F v a • (evFin F v b ⊗ₜ[F] x)
    rw [TensorProduct.smul_tmul', smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

private theorem at_entry {v : Pl (F := F)} {ι κ : Type} {A : Matrix ι κ (AE F E)} (h : At (evFin F v) A) (i : ι) (j : κ) :
    At (evFin F v) (A i j) := fun u hu => congrFun (congrFun (h u hu) i) j

private theorem mat_eq {v : Pl (F := F)} {ι κ : Type} {A B : Matrix ι κ (AE F E)} (hA : At (evFin F v) A) (hB : At (evFin F v) B)
    (h : A.map (compFin F E v) = B.map (compFin F E v)) : A = B := by
  ext i j
  have h1 : compFin F E v (A i j - B i j) = 0 := by
    rw [map_sub, sub_eq_zero]; exact congrFun (congrFun h i) j
  have h2 : At (evFin F v) (A i j - B i j) := fun u hu => by
    rw [smul_sub, at_entry hA i j u hu, at_entry hB i j u hu, sub_zero]
  exact sub_eq_zero.1 (eq_zero_of_at h2 h1)

private theorem at_eM {v : Pl (F := F)} {n : ℕ} : At (evFin F v) (eM (E := E) v n) := fun u hu => by
  rw [eM, ← smul_assoc, at_sg 1 u hu, zero_smul]

private theorem eM_mul {v : Pl (F := F)} {n : ℕ} {A : Matrix (Fin n) (Fin n) (AE F E)} (h : At (evFin F v) A) : eM v n * A = A := by
  rw [eM, Matrix.smul_mul, one_mul, e_smul h]

private theorem mul_eM {v : Pl (F := F)} {n : ℕ} {A : Matrix (Fin n) (Fin n) (AE F E)} (h : At (evFin F v) A) : A * eM v n = A := by
  rw [eM, Matrix.mul_smul, mul_one, e_smul h]

private theorem max_mem {v : Pl (F := F)} {ϖ : Fv F v} (hϖ : ϖ ∈ v.adicCompletionIntegers F) (hlt : Valued.v ϖ < 1) :
    (⟨ϖ, hϖ⟩ : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h1 : ϖ * (w : Fv F v) = 1 := congrArg Subtype.val hw
  have h2 : Valued.v (w : Fv F v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).1 w.2
  have h3 : Valued.v ϖ * Valued.v (w : Fv F v) = 1 := by rw [← map_mul, h1, map_one]
  have h4 : Valued.v ϖ * Valued.v (w : Fv F v) ≤ Valued.v ϖ := mul_le_of_le_one_right' h2
  exact absurd (h3 ▸ h4) (not_le.2 hlt)

end UpperTheory.AdelicOrderPrincipalUnitInverse

open UpperTheory.AdelicOrderPrincipalUnitInverse in
theorem UpperTheory.latticeOrder_exists_inverse_one_add_uniformizer_smul :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (X : Spc F E n) (v : Pl (F := F)) (b c : Matrix (Fin n) (Fin n) (AE F E)), IsFr X v b c → ∀ ϖ : Fv F v, ϖ ∈ v.adicCompletionIntegers F → Valued.v ϖ < 1 → ∀ p ∈ abelian₂ (E := E) v b c, ∃ q ∈ abelian₂ (E := E) v b c, (eM v n + sg v ϖ • p) * q = eM v n := by
  intro F E _ _ _ _ _ n X v b c hX ϖ hϖ hlt p hp
  have hpat : At (evFin F v) (c * p * b) := fun u hu => by
    rw [← Matrix.smul_mul, ← Matrix.smul_mul, hX.at_c u hu, Matrix.zero_mul, Matrix.zero_mul]
  obtain ⟨N, hN, hQ⟩ := unit_abs (phi E v) (SS E v) phi_mem (fun x hx => hx.2) (max_mem hϖ hlt)
    ((c * p * b).map (compFin F E v)) (fun i j => comp_mem (hp.2 i j))
  let N' : Matrix (Fin n) (Fin n) (AE F E) := N.map (PositivityTheory.ThKH.Iwas.sgE E v)
  have hN' : ∀ i j, N' i j ∈ Oh E v := fun i j => (hN i j).1
  have hNat : At (evFin F v) N' := fun u hu => by
    ext i j
    exact PositivityTheory.ThKH.Iwas.at_sgE _ u hu
  have hQt : (eM v n + sg v ϖ • (c * p * b)) * N' = eM v n := by
    refine mat_eq (v := v) ?_ at_eM ?_
    · exact fun u hu => by rw [← Matrix.mul_smul, hNat u hu, Matrix.mul_zero]
    · let Φ := (compFin F E v).mapMatrix (m := Fin n)
      have hsm : ∀ (a : AF F) (A : Matrix (Fin n) (Fin n) (AE F E)), Φ (a • A) = evFin F v a • Φ A := fun a A => by
        ext i j
        exact smul_comp a (A i j)
      have he : Φ (eM v n) = 1 := by
        rw [eM, hsm, PositivityTheory.ThKH.Iwas.ev_sg, one_smul, map_one]
      have hN2 : Φ N' = N := by
        ext i j
        exact PositivityTheory.ThKH.Iwas.comp_sgE _
      have hs : ϖ • Φ (c * p * b) = phi E v ⟨ϖ, hϖ⟩ • Φ (c * p * b) := by
        ext i j
        exact Algebra.smul_def ϖ (Φ (c * p * b) i j)
      change Φ _ = Φ _
      rw [map_mul, map_add (f := _), he, hN2, hsm, PositivityTheory.ThKH.Iwas.ev_sg, hs]
      exact hQ
  have hb1 : b * eM v n = b := mul_eM hX.at_b
  have hb2 : eM v n * b = b := eM_mul hX.at_b
  have hD : (eM v n + sg v ϖ • p) * b = b * (eM v n + sg v ϖ • (c * p * b)) := by
    rw [Matrix.add_mul, Matrix.mul_add, hb1, hb2, Matrix.smul_mul (sg v ϖ) p b, Matrix.mul_smul b (sg v ϖ)]
    congr 2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hX.bc, eM_mul hp.1]
  refine ⟨b * N' * c, ⟨?_, ?_⟩, ?_⟩
  · intro u hu
    rw [← Matrix.smul_mul, ← Matrix.smul_mul, hX.at_b u hu, Matrix.zero_mul, Matrix.zero_mul]
  · intro i j
    have h : c * (b * N' * c) * b = N' := by
      calc c * (b * N' * c) * b = (c * b) * N' * (c * b) := by simp only [Matrix.mul_assoc]
        _ = N' := by rw [hX.cb, eM_mul hNat, mul_eM hNat]
    rw [h]
    exact hN' i j
  · calc (eM v n + sg v ϖ • p) * (b * N' * c) = ((eM v n + sg v ϖ • p) * b) * N' * c := by simp only [Matrix.mul_assoc]
      _ = b * ((eM v n + sg v ϖ • (c * p * b)) * N') * c := by rw [hD]; simp only [Matrix.mul_assoc]
      _ = eM v n := by rw [hQt, hb1, hX.bc]
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.InertofProofK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThK
open NumberField IsDedekindDomain GlobalTheory.AdelicU
theorem inertof_proof_k : _root_.PositivityTheory.ThK.InertOf_k := by
  intro F E _ _ _ _ _ σ B hB v he
  haveI := hB.unram
  haveI := v.isMaximal
  have h1 := ncard_primesOver_le_two hB.cm v
  have h2 : (v.asIdeal.primesOver (𝓞 E)).ncard ≠ 2 := fun h =>
    not_nonempty_iff.2 he ((nonempty_split_iff hB.cm).2 h)
  have h3 : 0 < (v.asIdeal.primesOver (𝓞 E)).ncard := Nat.pos_of_ne_zero (IsDedekindDomain.primesOver_ncard_ne_zero _ _)
  exact map_eq_of_ncard_eq_one v (by omega)
end PositivityTheory.ThK
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsIsotropicSplittingAtInertPrime
set_option synthInstance.maxHeartbeats 200000

section
open scoped Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels UpperTheory.TP.BA
section
open PositivityTheory.ThKH.Iwas GlobalTheory.LFun GlobalTheory.LFun.InertChart Formalism.UG PositivityTheory.ThK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
  {w : HeightOneSpectrum (𝓞 E)}
private theorem sgE_mem_Oh_pk {y : TensorProduct F (Fv F v) E} (hy : y ∈ intLoc F E v) : sgE E v y ∈ Oh E v := by
  refine intLoc_induction (p := fun y => sgE E v y ∈ Oh E v) (fun a ha x => ?_) ?_ (fun y z hy hz => ?_)
    (fun y hy => ?_) hy
  · refine AddSubgroup.subset_closure ⟨PositivityTheory.ThKH.Iwas.sg v a, at_sg a, by rwa [ev_sg], x, ?_⟩
    change TensorProduct.tmul F (PositivityTheory.ThKH.Iwas.sg v a) (x : E) = TensorProduct.tmul F (PositivityTheory.ThKH.Iwas.sg v a * 1) (x : E)
    rw [mul_one]
  · rw [map_zero]; exact zero_mem _
  · rw [map_add]; exact add_mem hy hz
  · rw [map_neg]; exact neg_mem hy
private theorem sg_one_smul_pk {x : AE F E} (hx : At (evFin F v) x) : PositivityTheory.ThKH.Iwas.sg v 1 • x = x := by
  have h1 := hx (1 - PositivityTheory.ThKH.Iwas.sg v 1) (by rw [map_sub, map_one, ev_sg, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1.symm
private theorem mem_Oh_pk (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) {x : AE F E} (hx : At (evFin F v) x)
    (hi : piE h x ∈ Ov E w) : x ∈ Oh E v := by
  rw [← sg_one_smul_pk hx, ← sgE_comp]
  exact sgE_mem_Oh_pk ((mem_intLoc_iff hw h _).2 hi)
private theorem piE_sg_smul_pk (h : w.under (𝓞 F) = v) (x : AE F E) : piE h (PositivityTheory.ThKH.Iwas.sg v 1 • x) = piE h x := by
  rw [← sgE_comp]
  change toCompl h (compFin F E v (sgE E v _)) = _
  rw [comp_sgE]
  rfl
private theorem piE_eM_pk (h : w.under (𝓞 F) = v) (n : ℕ) : (eM (E := E) v n).map (piE h) = 1 := by
  refine Matrix.ext fun i j => ?_
  change piE h (PositivityTheory.ThKH.Iwas.sg v 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) = _
  rw [piE_sg_smul_pk, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp
private theorem at_eM_pk (n : ℕ) : At (evFin F v) (eM (E := E) v n) := fun u hu => by
  change u • (PositivityTheory.ThKH.Iwas.sg v 1 • (1 : Matrix (Fin n) (Fin n) (AE F E))) = 0
  rw [smul_smul, ← smul_eq_mul, at_sg 1 u hu, zero_smul]
theorem exists_isoW_k {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {W : Spc F E d} {r s : ℕ} (hB : _root_.UpperTheory.TP.W.GoodK σ B)
    (hW : W.IsSkew σ B r s) (h2 : 2 * n ≤ d) (hw : IsInertAt F E v w) : ∃ Y R, IsIsoW σ W v (n := n) Y R := by
  have h : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw h
  obtain ⟨a, ha, l, -, hg⟩ := exists_frame hB.cm hw h hc hW
  let f : Fin n → Fin d := Fin.castLE (by omega)
  have hf : Function.Injective f := Fin.castLE_injective _
  obtain ⟨Y, hY, eY⟩ := mat_surj h (a.1ᵀ.submatrix f id)
  obtain ⟨R, hR, eR⟩ := mat_surj h ((a⁻¹).1ᵀ.submatrix id f)
  refine ⟨Y, R, fun i => ?_, ?_, ?_, fun z hz j => ?_⟩
  · refine (mem_latW_iff hw h W _).2 ⟨fun u hu => congrFun (hY u hu) i, ?_⟩
    have e : piE h ∘ Y i = a.1 *ᵥ fun k => (1 : Matrix (Fin d) (Fin d) (w.adicCompletion E)) k (f i) := by
      funext k
      have e1 : piE h (Y i k) = a.1 k (f i) := congrFun (congrFun eY i) k
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply, e1]
    rw [e]
    exact (ha _).1 fun k => one_int k (f i)
  · refine mat_inj hw h (at_sub (at_mul_left hY _) (at_eM_pk n)) ?_
    rw [Matrix.map_mul, eY, eR, piE_eM_pk]
    have e : a.1ᵀ.submatrix f id * (a⁻¹).1ᵀ.submatrix id f = (a.1ᵀ * (a⁻¹).1ᵀ).submatrix f f := rfl
    rw [e, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.submatrix_one _ hf]
  · refine mat_inj hw h (at_sub (at_mul_left (at_mul_left hY _) _) at_zero) ?_
    have e := map_gram hc W.J Yᵀ Yᵀ
    rw [Matrix.transpose_transpose] at e
    have e2 : Yᵀ.map (piE h) = a.1.submatrix id f := by
      rw [Matrix.transpose_map, eY]; rfl
    rw [e2] at e
    refine e.trans (Matrix.ext fun i j => ?_)
    have e3 := congrFun (congrFun hg (f i)) (f j)
    refine e3.trans ?_
    have := i.2; have := j.2
    have e4 : (f i : ℕ) = i := rfl
    have e5 : (f j : ℕ) = j := rfl
    rw [Matrix.smul_apply]
    simp only [antiJ, Matrix.of_apply]
    rw [if_neg (by omega)]
    simp
  · obtain ⟨h3, h4⟩ := (mem_latW_iff hw h W z).1 hz
    rw [← Matrix.mulVec_transpose]
    refine mem_Oh_pk hw h (fun u hu => congrFun (at_mulVec_left (at_transpose hR) z u hu) j) ?_
    have e := congrFun (piE_mulVec h Rᵀ z) j
    rw [Function.comp_apply] at e
    rw [e]
    have e2 : Rᵀ.map (piE h) = (a⁻¹).1.submatrix f id := by
      rw [Matrix.transpose_map, eR]; rfl
    rw [e2]
    exact coord_int ha h4 (f j)
end
theorem UpperTheory.exists_isotropic_splitting_at_inert_prime :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (W : Spc F E d) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → W.IsSkew σ B r s → 2 * n ≤ d → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∃ Y R, IsIsoW σ W v (n := n) Y R := by
  intro F E _ _ _ _ _ σ B n d W r s hB hW h2 v w hw
  exact _root_.exists_isoW_k hB hW h2 hw
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels UpperTheory.TP.BA
namespace UpperTheory.LatD
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} {v : Pl F}
private theorem at_self_pk {M : Type} [AddCommGroup M] [Module (AF F) M] {x : M} (hx : At (evFin F v) x) :
    sg v 1 • x = x := by
  have h1 := hx (1 - sg v 1) (by rw [map_sub, map_one, PositivityTheory.ThKH.Iwas.ev_sg, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1.symm
private theorem at_mulA_pk {a : AF F} (ha : At (evFin F v) a) (a' : AF F) : At (evFin F v) (a * a') := fun u hu => by
  have h := ha u hu
  rw [smul_eq_mul] at h ⊢
  rw [← mul_assoc, h, zero_mul]
private theorem sg_one_int_pk : evFin F v (sg v 1) ∈ v.adicCompletionIntegers F := by
  rw [PositivityTheory.ThKH.Iwas.ev_sg]; exact one_mem _
private theorem oh_gen_pk {a : AF F} (h1 : At (evFin F v) a) (h2 : evFin F v a ∈ v.adicCompletionIntegers F) (o : 𝓞 E) :
    a • inclR (F := F) (AF F) (o : E) ∈ Oh E v :=
  AddSubgroup.subset_closure ⟨a, h1, h2, o, rfl⟩
private theorem oh_ind_pk {p : AE F E → Prop}
    (gen : ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ o : 𝓞 E, p (a • inclR (F := F) (AF F) (o : E)))
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y)) (neg : ∀ x, p x → p (-x)) {x : AE F E} (hx : x ∈ Oh E v) : p x := by
  refine AddSubgroup.closure_induction (p := fun x _ => p x) ?_ zero (fun x y _ _ h h' => add x y h h') (fun x _ h => neg x h) hx
  rintro _ ⟨a, h1, h2, o, rfl⟩
  exact gen a h1 h2 o
private theorem oh_mul_pk {x y : AE F E} (hx : x ∈ Oh E v) (hy : y ∈ Oh E v) : x * y ∈ Oh E v := by
  refine oh_ind_pk (p := fun x => x * y ∈ Oh E v) ?_ (by simp [zero_mem]) (fun x y h h' => by rw [add_mul]; exact add_mem h h')
    (fun x h => by rw [neg_mul]; exact neg_mem h) hx
  intro a h1 h2 o
  refine oh_ind_pk (p := fun y => a • inclR (F := F) (AF F) (o : E) * y ∈ Oh E v) ?_ (by simp [zero_mem])
    (fun x y h h' => by rw [mul_add]; exact add_mem h h') (fun x h => by rw [mul_neg]; exact neg_mem h) hy
  intro a' h1' h2' o'
  have e : a • inclR (F := F) (AF F) (o : E) * a' • inclR (F := F) (AF F) (o' : E) =
      (a * a') • inclR (F := F) (AF F) ((o * o' : 𝓞 E) : E) := by
    rw [smul_mul_smul_comm, ← map_mul]; rfl
  rw [e]
  exact oh_gen_pk (at_mulA_pk h1 a') (by rw [map_mul]; exact mul_mem h2 h2') _
private theorem oh_sg_pk {t : Fv F v} (ht : t ∈ v.adicCompletionIntegers F) : sg v t • (1 : AE F E) ∈ Oh E v := by
  have := oh_gen_pk (E := E) (PositivityTheory.ThKH.Iwas.at_sg t) (by rw [PositivityTheory.ThKH.Iwas.ev_sg]; exact ht) (1 : 𝓞 E)
  simpa using this
private theorem oh_smul_pk {t : Fv F v} (ht : t ∈ v.adicCompletionIntegers F) {x : AE F E} (hx : x ∈ Oh E v) :
    sg v t • x ∈ Oh E v := by
  have := oh_mul_pk (oh_sg_pk (E := E) ht) hx
  rwa [smul_mul_assoc, one_mul] at this
private theorem oh_matmul_pk {P Q : Matrix (Fin n) (Fin n) (AE F E)} (hP : ∀ i j, P i j ∈ Oh E v) (hQ : ∀ i j, Q i j ∈ Oh E v) (i j : Fin n) :
    (P * Q) i j ∈ Oh E v := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => oh_mul_pk (hP i k) (hQ k j)
private theorem oh_mulVec_pk {P : Matrix (Fin n) (Fin n) (AE F E)} {w : Fin n → AE F E} (hP : ∀ i j, P i j ∈ Oh E v) (hw : ∀ i, w i ∈ Oh E v) (i : Fin n) :
    (P *ᵥ w) i ∈ Oh E v := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun k _ => oh_mul_pk (hP i k) (hw k)
private theorem lat_ind_pk {m : ℕ} {X : Spc F E m} {p : (Fin m → AE F E) → Prop}
    (gen : ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ y ∈ X.L, p (fun i => a • inclR (F := F) (AF F) (y i)))
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y)) (neg : ∀ x, p x → p (-x)) {x : Fin m → AE F E} (hx : x ∈ PositivityTheory.ThK.latW X v) : p x := by
  refine AddSubgroup.closure_induction (p := fun x _ => p x) ?_ zero (fun x y _ _ h h' => add x y h h') (fun x _ h => neg x h) hx
  rintro _ ⟨a, h1, h2, y, hy, rfl⟩
  exact gen a h1 h2 y hy
private theorem lat_smul_pk {m : ℕ} {X : Spc F E m} {o : AE F E} (ho : o ∈ Oh E v) {z : Fin m → AE F E} (hz : z ∈ PositivityTheory.ThK.latW X v) :
    (fun i => o * z i) ∈ PositivityTheory.ThK.latW X v := by
  refine oh_ind_pk (p := fun o => (fun i => o * z i) ∈ PositivityTheory.ThK.latW X v) ?_ (by simp only [zero_mul]; exact zero_mem _)
    (fun x y h h' => by simp only [add_mul]; exact add_mem h h') (fun x h => by simp only [neg_mul]; exact neg_mem h) ho
  intro a h1 h2 o
  refine lat_ind_pk (p := fun z => (fun i => a • inclR (F := F) (AF F) (o : E) * z i) ∈ PositivityTheory.ThK.latW X v) ?_ (by simp only [Pi.zero_apply, mul_zero]; exact zero_mem _)
    (fun x y h h' => by simp only [Pi.add_apply, mul_add]; exact add_mem h h')
    (fun x h => by simp only [Pi.neg_apply, mul_neg]; exact neg_mem h) hz
  intro a' h1' h2' y hy
  refine AddSubgroup.subset_closure ⟨a * a', at_mulA_pk h1 a', by rw [map_mul]; exact mul_mem h2 h2', o • y, X.L.smul_mem o hy, ?_⟩
  funext i
  rw [smul_mul_smul_comm, ← map_mul]
  rfl
private theorem lat_mulVec_pk {m : ℕ} {X : Spc F E m} {P : Matrix (Fin m) (Fin n) (AE F E)} {w : Fin n → AE F E}
    (hP : ∀ j, (fun i => P i j) ∈ PositivityTheory.ThK.latW X v) (hw : ∀ j, w j ∈ Oh E v) : P *ᵥ w ∈ PositivityTheory.ThK.latW X v := by
  have e : P *ᵥ w = ∑ j, fun i => w j * P i j := by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [e]
  exact sum_mem fun j _ => lat_smul_pk (hw j) (hP j)
private theorem vmv_mem_pk {X : Spc F E n} {W : Spc F E d} {z : Fin n → AE F E} {y : Fin d → AE F E}
    (hz : z ∈ PositivityTheory.ThK.latW X v) (hy : y ∈ PositivityTheory.ThK.latW W v) : Matrix.vecMulVec z y ∈ latAtV X W v := by
  refine lat_ind_pk (p := fun z => Matrix.vecMulVec z y ∈ latAtV X W v) ?_ ?_ ?_ ?_ hz
  · intro a h1 h2 x hx
    refine lat_ind_pk (p := fun y => Matrix.vecMulVec (fun i => a • inclR (F := F) (AF F) (x i)) y ∈ latAtV X W v) ?_ ?_ ?_ ?_ hy
    · intro a' h1' h2' y hy
      refine AddSubgroup.subset_closure ⟨a * a', at_mulA_pk h1 a', by rw [map_mul]; exact mul_mem h2 h2', x, hx, y, hy, ?_⟩
      ext i j
      simp [Matrix.vecMulVec_apply, incM, smul_mul_smul_comm]
      rw [mul_comm a a', mul_smul]
    · have e : Matrix.vecMulVec (fun i => a • inclR (F := F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by
        ext i j; simp [Matrix.vecMulVec_apply]
      rw [e]; exact zero_mem _
    · intro x y h h'
      have := add_mem h h'
      rwa [show ∀ u (p q : Fin d → AE F E), Matrix.vecMulVec u p + Matrix.vecMulVec u q = Matrix.vecMulVec u (p + q) from fun u p q => by
        ext i j; simp [Matrix.vecMulVec_apply, mul_add]] at this
    · intro x h
      have := neg_mem h
      rwa [show ∀ u (p : Fin d → AE F E), -Matrix.vecMulVec u p = Matrix.vecMulVec u (-p) from fun u p => by
        ext i j; simp [Matrix.vecMulVec_apply]] at this
  · have e : Matrix.vecMulVec (0 : Fin n → AE F E) y = 0 := by
      ext i j; simp [Matrix.vecMulVec_apply]
    rw [e]; exact zero_mem _
  · intro x y h h'
    have := add_mem h h'
    rwa [show ∀ (p q : Fin n → AE F E) u, Matrix.vecMulVec p u + Matrix.vecMulVec q u = Matrix.vecMulVec (p + q) u from fun p q u => by
      ext i j; simp [Matrix.vecMulVec_apply, add_mul]] at this
  · intro x h
    have := neg_mem h
    rwa [show ∀ (p : Fin n → AE F E) u, -Matrix.vecMulVec p u = Matrix.vecMulVec (-p) u from fun p u => by
      ext i j; simp [Matrix.vecMulVec_apply]] at this
private theorem gam_ind_pk {X : Spc F E n} {W : Spc F E d} {p : Matrix (Fin n) (Fin d) (AE F E) → Prop}
    (gen : ∀ z ∈ PositivityTheory.ThK.latW X v, ∀ y ∈ PositivityTheory.ThK.latW W v, p (Matrix.vecMulVec z y))
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y)) (neg : ∀ x, p x → p (-x)) {γ : Matrix (Fin n) (Fin d) (AE F E)}
    (hγ : γ ∈ latAtV X W v) : p γ := by
  refine AddSubgroup.closure_induction (p := fun x _ => p x) ?_ zero (fun x y _ _ h h' => add x y h h') (fun x _ h => neg x h) hγ
  rintro _ ⟨a, h1, h2, x, hx, y, hy, rfl⟩
  have e : a • incM F (Matrix.vecMulVec x y) = Matrix.vecMulVec (fun i => a • inclR (F := F) (AF F) (x i))
      (fun j => sg v 1 • inclR (F := F) (AF F) (y j)) := by
    ext i j
    have e1 : a * sg v 1 = a := by rw [mul_comm]; exact at_self_pk h1
    simp [Matrix.vecMulVec_apply, incM, smul_mul_smul_comm, e1]
    rw [← mul_smul, mul_comm (sg v 1) a, e1]
  rw [e]
  exact gen _ (AddSubgroup.subset_closure ⟨a, h1, h2, x, hx, rfl⟩) _
    (AddSubgroup.subset_closure ⟨sg v 1, PositivityTheory.ThKH.Iwas.at_sg 1, sg_one_int_pk, y, hy, rfl⟩)
private theorem mul_eM_pk {M : Matrix (Fin n) (Fin n) (AE F E)} (h : At (evFin F v) M) : M * eM v n = M := by
  rw [Matrix.mul_smul, Matrix.mul_one]; exact at_self_pk h
private theorem eM_mul_pk {M : Matrix (Fin n) (Fin n) (AE F E)} (h : At (evFin F v) M) : eM v n * M = M := by
  rw [Matrix.smul_mul, Matrix.one_mul]; exact at_self_pk h
private theorem eM_mem_pk (i j : Fin n) : (eM (E := E) v n) i j ∈ Oh E v := by
  by_cases h : i = j
  · subst h
    simpa [eM] using oh_sg_pk (E := E) (v := v) (one_mem _)
  · simp [eM, h, zero_mem]
private theorem eM_at_pk : At (evFin F v) (eM (E := E) v n) := fun u hu => by
  rw [smul_smul, show u * sg v 1 = 0 from PositivityTheory.ThKH.Iwas.at_sg 1 u hu, zero_smul]
end UpperTheory.LatD
theorem UpperTheory.exists_weilLatticeDatum :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B r s → W.IsSkew σ B r' s' → 2 * n ≤ d → ∀ v : Pl F, ∃ Λ x₁ R ϖ, LatData σ X W v Λ x₁ R ϖ := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW hnd v
  have hYR : ∃ Y R, IsIsoW σ W v (n := n) Y R := by
    by_cases ht : Nonempty (E →ₐ[F] Fv F v)
    · obtain ⟨t⟩ := ht
      exact _root_.UpperTheory.exists_isotropic_splitting_of_two_mul_le F E σ B n d W r' s' hB hW hnd v t
    · obtain ⟨w, hw⟩ := _root_.PositivityTheory.ThK.inertof_proof_k F E σ B hB v (not_nonempty_iff.1 ht)
      exact _root_.UpperTheory.exists_isotropic_splitting_at_inert_prime F E σ B n d W r' s' hB hW hnd v w hw
  obtain ⟨Y, R, hY⟩ := hYR
  obtain ⟨b, c, hF⟩ := UpperTheory.unitaryLattice_exists_frame F E n X v hX.lat
  obtain ⟨ϖ, hϖ0, hϖ1⟩ : ∃ ϖ : Fv F v, ϖ ≠ 0 ∧ Valued.v ϖ < 1 := by
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    have e : Valued.v ((π : F) : v.adicCompletion F) = v.valuation F π := v.valuedAdicCompletion_eq_valuation' π
    refine ⟨((π : F) : v.adicCompletion F), ?_, ?_⟩
    · intro h0
      rw [h0, map_zero, hπ] at e
      exact absurd e.symm (by simp)
    · rw [e, hπ]
      exact compareOfLessAndEq_eq_lt.mp rfl
  have hϖm : ϖ ∈ v.adicCompletionIntegers F := hϖ1.le
  have hmul : ∀ a ∈ abelian₂ (E := E) v b c, ∀ a' ∈ abelian₂ (E := E) v b c, a * a' ∈ abelian₂ (E := E) v b c := by
    intro a ha a' ha'
    refine ⟨PositivityTheory.ThKH.Iwas.at_mul_left ha.1 a', fun i j => ?_⟩
    have e : c * (a * a') * b = (c * a * b) * (c * a' * b) := by
      calc c * (a * a') * b = c * (a * eM v n * a') * b := by rw [UpperTheory.LatD.mul_eM_pk ha.1]
        _ = c * (a * (b * c) * a') * b := by rw [hF.bc]
        _ = (c * a * b) * (c * a' * b) := by simp only [Matrix.mul_assoc]
    rw [e]
    exact UpperTheory.LatD.oh_matmul_pk ha.2 ha'.2 i j
  have hact : ∀ a ∈ abelian₂ (E := E) v b c, ∀ z ∈ PositivityTheory.ThK.latW X v, a *ᵥ z ∈ PositivityTheory.ThK.latW X v := by
    intro a ha z hz
    have e : a *ᵥ z = b *ᵥ ((c * a * b) *ᵥ (c *ᵥ z)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      calc a = eM v n * a * eM v n := by rw [UpperTheory.LatD.mul_eM_pk (PositivityTheory.ThKH.Iwas.at_mul_right _ ha.1), UpperTheory.LatD.eM_mul_pk ha.1]
        _ = (b * c) * a * (b * c) := by rw [hF.bc]
        _ = b * (c * a * b) * c := by simp only [Matrix.mul_assoc]
    rw [e]
    exact UpperTheory.LatD.lat_mulVec_pk hF.col (UpperTheory.LatD.oh_mulVec_pk ha.2 (hF.coord z hz))
  refine ⟨abelian₂ (E := E) v b c, b * Y, R * c, ϖ, ?_⟩
  refine
    { at_mem := fun a ha => ha.1
      one_mem := ⟨UpperTheory.LatD.eM_at_pk, fun i j => ?_⟩
      mul_mem := hmul
      smul_mem := fun t ht a ha => ⟨fun u hu => by rw [smul_comm, ha.1 u hu, smul_zero], fun i j => ?_⟩
      act := ?_
      x_mem := ?_
      gram := ?_
      right := ?_
      r_mem := ?_
      ϖ_ne := hϖ0
      ϖ_mem := hϖm
      unit := UpperTheory.latticeOrder_exists_inverse_one_add_uniformizer_smul F E n X v b c hF ϖ hϖm hϖ1
      small := (UpperTheory.mem_nhds_one_of_congruence_latticeOrder F E σ n X v b c hF ϖ hϖ0 hϖ1).1
      nbhd := (UpperTheory.mem_nhds_one_of_congruence_latticeOrder F E σ n X v b c hF ϖ hϖ0 hϖ1).2 }
  · rw [UpperTheory.LatD.mul_eM_pk hF.at_c, hF.cb]
    exact UpperTheory.LatD.eM_mem_pk i j
  · rw [Matrix.mul_smul, Matrix.smul_mul]
    exact UpperTheory.LatD.oh_smul_pk ht (ha.2 i j)
  · intro a ha γ hγ
    refine UpperTheory.LatD.gam_ind_pk (p := fun γ => a * γ ∈ latAtV X W v) ?_ (by simp [zero_mem]) ?_ ?_ hγ
    · intro z hz y hy
      rw [Matrix.mul_vecMulVec]
      exact UpperTheory.LatD.vmv_mem_pk (hact a ha z hz) hy
    · intro x y h h'
      rw [Matrix.mul_add]; exact add_mem h h'
    · intro x h
      rw [Matrix.mul_neg]; exact neg_mem h
  · have e : b * Y = ∑ k, Matrix.vecMulVec (fun i => b i k) (Y k) := by
      ext i j
      simp [Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]
    rw [e]
    exact sum_mem fun k _ => UpperTheory.LatD.vmv_mem_pk (hF.col k) (hY.what₂ k)
  · have hm : (b * Y).map (cA σ) = b.map (cA σ) * Y.map (cA σ) := Matrix.map_mul (f := (cA σ).toRingHom)
    rw [hm, Matrix.transpose_mul]
    have e : b * Y * incM F W.J * ((Y.map (cA σ))ᵀ * (b.map (cA σ))ᵀ) =
        b * (Y * incM F W.J * (Y.map (cA σ))ᵀ) * (b.map (cA σ))ᵀ := by simp only [Matrix.mul_assoc]
    rw [e, hY.gram, Matrix.mul_zero, Matrix.zero_mul]
  · have e : b * Y * (R * c) = b * (Y * R) * c := by simp only [Matrix.mul_assoc]
    rw [e, hY.right, UpperTheory.LatD.mul_eM_pk hF.at_b, hF.bc]
  · intro γ hγ
    refine ⟨PositivityTheory.ThKH.Iwas.at_mul_right _ (PositivityTheory.ThKH.Iwas.at_mul_right _ hF.at_c), ?_⟩
    refine UpperTheory.LatD.gam_ind_pk (p := fun γ => ∀ i j, (c * (γ * (R * c)) * b) i j ∈ Oh E v) ?_ (by simp [zero_mem]) ?_ ?_ hγ
    · intro z hz y hy i j
      have e : c * (Matrix.vecMulVec z y * (R * c)) * b = Matrix.vecMulVec (c *ᵥ z) (sg v 1 • (y ᵥ* R)) := by
        have e1 : c * (Matrix.vecMulVec z y * (R * c)) * b = c * Matrix.vecMulVec z y * R * (c * b) := by
          simp only [Matrix.mul_assoc]
        rw [e1, hF.cb, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mul_smul, Matrix.mul_one]
        ext i j
        simp [Matrix.vecMulVec_apply]
      rw [e, Matrix.vecMulVec_apply]
      exact UpperTheory.LatD.oh_mul_pk (hF.coord z hz i) (UpperTheory.LatD.oh_smul_pk (one_mem _) (hY.coord y hy j))
    · intro x y h h' i j
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.add_mul]
      exact add_mem (h i j) (h' i j)
    · intro x h i j
      rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_mul]
      exact neg_mem (h i j)
end
