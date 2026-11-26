module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.AwAvg
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CayleyHamiltonSymmetric
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsAdjoinCoeffCharacterSubMemMaximalIdealPow

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Factor
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem factor_chi {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (h : H) : (D.comap φ).chi (MonoidAlgebra.single h 1) = D.chi (MonoidAlgebra.single (φ h) 1) := by
  change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
  congr 1
  rw [map_sub]
  simp

private theorem factor_abs {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (hφ : Function.Surjective φ) (ρ : H →* GL (Fin n) A) (hn : 1 ≤ n) (hF : Full ρ)
    (hD : D.comap φ = W.GDet.ofRep (W.mat ρ)) :
    ∃ ρ₀ : G →* GL (Fin n) A, ρ₀.comp φ = ρ ∧ Full ρ₀ ∧ D = W.GDet.ofRep (W.mat ρ₀) := by
  have repAlg_single {K : Type} [Group K] (R : K →* Matrix (Fin n) (Fin n) A) (B : Type) [CommRing B] [Algebra A B]
      (g : K) (r : B) : W.GDet.repAlg R B (MonoidAlgebra.single g r) = r • (R g).map (algebraMap A B) := by
    unfold W.GDet.repAlg
    rw [MonoidAlgebra.lift_single]
    rfl
  have repAlg_map {K : Type} [Group K] (R : K →* Matrix (Fin n) (Fin n) A) (B : Type) [CommRing B] [Algebra A B]
      (y : MonoidAlgebra A K) :
      W.GDet.repAlg R B (MonoidAlgebra.mapRingHom K (algebraMap A B) y) = (W.GDet.repAlg R A y).map (algebraMap A B) := by
    induction y using MonoidAlgebra.induction_on with
    | of g => simp [MonoidAlgebra.of_apply, repAlg_single]
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
      ext i j
      simp
    | smul r x hx =>
      have hr : r • x = MonoidAlgebra.single 1 r * x := by rw [Algebra.smul_def]; rfl
      have hm : MonoidAlgebra.mapRingHom K (algebraMap A B) (MonoidAlgebra.single 1 r)
          = MonoidAlgebra.single 1 (algebraMap A B r) := by
        ext g
        simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]
      rw [hr, map_mul, map_mul, map_mul, hx, Matrix.map_mul, hm, repAlg_single, repAlg_single, map_one]
      congr 1
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have chi_eq {K : Type} [Group K] (R : K →* Matrix (Fin n) (Fin n) A) (y : MonoidAlgebra A K) :
      (W.GDet.ofRep R).chi y = (W.GDet.repAlg R A y).charpoly := by
    unfold W.GDet.chi
    change (W.GDet.repAlg R A[X] _).det = _
    rw [← Polynomial.algebraMap_eq, map_sub, repAlg_single, repAlg_map, map_one]
    rw [Matrix.charpoly]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [Matrix.charmatrix_apply, Matrix.one_apply, h]
  have tr_eq (y : MonoidAlgebra A H) :
      (W.GDet.ofRep (W.mat ρ)).tr y = (W.GDet.repAlg (W.mat ρ) A y).trace := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    unfold W.GDet.tr W.GDet.lam
    rw [chi_eq, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
    ring
  have chi_single {K : Type} [Group K] (R : K →* Matrix (Fin n) (Fin n) A) (g : K) :
      (W.GDet.ofRep R).chi (MonoidAlgebra.single g 1) = (R g).charpoly := by
    rw [chi_eq, repAlg_single]; simp
  have hchi : ∀ h, D.chi (MonoidAlgebra.single (φ h) 1) = (W.GDet.ofRep (W.mat ρ)).chi (MonoidAlgebra.single h 1) :=
    fun h => by rw [← hD, factor_chi]
  have hker : φ.ker ≤ ρ.ker := fun g hg => by
    have h0 := (trPlus ρ hF).1 (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1) fun h => by
      have e : (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single (h * g) 1) =
          (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single h 1) := by
        unfold W.GDet.tr W.GDet.lam
        rw [← hchi, ← hchi, map_mul, MonoidHom.mem_ker.1 hg, mul_one]
      rw [tr_eq _, tr_eq _] at e
      rw [tr_eq _, mul_sub, map_sub, Matrix.trace_sub,
        MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one, e, sub_self]
    rw [map_sub, sub_eq_zero] at h0
    refine Units.ext ?_
    simpa [W.GDet.repAlg, W.mat] using h0
  let ρ₀ : G →* GL (Fin n) A := φ.liftOfSurjective hφ ⟨ρ, hker⟩
  have h0 : ∀ h, ρ₀ (φ h) = ρ h := fun h => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ h
  have hm : ∀ h, W.mat ρ₀ (φ h) = W.mat ρ h := fun h => congrArg Units.val (h0 h)
  refine ⟨ρ₀, MonoidHom.ext h0, ?_, CA.d_gext _ _ fun g i _ _ => ?_⟩
  · refine top_le_iff.1 (le_trans (le_of_eq (Eq.symm hF)) (Submodule.span_mono ?_))
    rintro _ ⟨h, rfl⟩
    exact ⟨φ h, hm h⟩
  · obtain ⟨h, rfl⟩ := hφ g
    unfold W.GDet.lam
    rw [hchi, chi_single, chi_single, hm]

theorem UpperTheory.V.Ws.Eb.factor :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l)), 1 ≤ n → x.IsRep ρ → Af.IsIrr (ρ.comp (cycBar L Ω l).ker.subtype) →
        ∃ ρ₀ : V.frame.G₀ →* GL (Fin n) (PadicAlgCl l), ρ₀.comp V.pr = ρ ∧ Full ρ₀ ∧ B.u.D.map (x : B.B →+* PadicAlgCl l) = W.GDet.ofRep (W.mat ρ₀) := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B x ρ hn hx hirr
  have hs : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  have hF : Full ρ := (AlgebraTools.Det.irrIffSpan (W.mat ρ)).1 fun N hN => hirr.2.2 N le_top fun g v hv => hN g v hv
  exact factor_abs x.D V.pr hs ρ hn hF hx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RelKill
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.Eb.relKill_single {A G : Type} [CommRing A] [Group G] {n : ℕ} (ρ : G →* GL (Fin n) A)
    (g : G) (a : A) : W.GDet.repAlg (W.mat ρ) A (MonoidAlgebra.single g a) = a • W.mat ρ g := by
  ext i j
  simp [W.GDet.repAlg]

private theorem UpperTheory.V.Ws.Eb.relKill_push {R A G : Type} [CommRing R] [CommRing A] [Group G] {n : ℕ}
    (D : W.GDet n R G) (f : R →+* A) (ρ : G →* GL (Fin n) A) (hρ : Full ρ) (hD : D.map f = W.GDet.ofRep (W.mat ρ))
    (z : MonoidAlgebra R G) (hz : ∀ h : G, D.tr (MonoidAlgebra.single h 1 * z) = 0) :
    W.GDet.repAlg (W.mat ρ) A (MonoidAlgebra.mapRingHom G f z) = 0 := by
  refine (trPlus ρ hρ).1 (MonoidAlgebra.mapRingHom G f z) (fun g' => ?_)
  rw [← hD]
  have e : MonoidAlgebra.single g' (1 : A) * MonoidAlgebra.mapRingHom G f z =
      MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g' 1 * z) := by
    rw [map_mul]
    congr 1
    simp [MonoidAlgebra.mapRingHom]
  have hchi : ∀ y, (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f := by
    intro y
    have he : MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (MonoidAlgebra.mapRingHom G f y) =
        MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y) := by
      rw [map_sub, MonoidAlgebra.mapRingHom_single, Polynomial.coe_mapRingHom, Polynomial.map_X,
        ← RingHom.comp_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp,
        ← MonoidAlgebra.mapRingHom_comp, Polynomial.mapRingHom_comp_C]
    show (D.map f).D A[X] _ = _
    rw [he]
    let : Algebra R A[X] := ((algebraMap A A[X]).comp f).toAlgebra
    have hc : ∀ a : R, Polynomial.mapRingHom f (algebraMap R R[X] a) = algebraMap R A[X] a := by
      intro a
      change Polynomial.map f (C a) = C (f a)
      exact Polynomial.map_C f
    exact D.nat R[X] A[X] { Polynomial.mapRingHom f with commutes' := hc } _
  have hmap : ∀ i y, (D.map f).lam i (MonoidAlgebra.mapRingHom G f y) = f (D.lam i y) := by
    intro i y
    simp only [W.GDet.lam, hchi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]
  rw [e, W.GDet.tr.eq_1, hmap 1, ← W.GDet.tr.eq_1, hz g', map_zero]

theorem UpperTheory.V.Ws.Eb.relKill :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) {A : Type} [CommRing A] [Algebra c.O A] (f : B.B →ₐ[c.O] A) (ρ : F.G₀ →* GL (Fin n) A), Full ρ → B.u.D.map (f : B.B →+* A) = W.GDet.ofRep (W.mat ρ) →
        (∀ v (g : Fin n → F.Gv v), (List.ofFn fun i => W.mat ρ (F.φ v (g i)) - algebraMap A _ (f (B.u.ψ v i (g i) : B.Bˣ))).prod = 0) ∧ ∀ u, ∀ g ∈ r.Ip u, ρ g = 1 := by
  intro l _ F c n r B A _ _ f ρ hρ hD
  have key : ∀ z : MonoidAlgebra B.B F.G₀, (∀ h : F.G₀, B.u.D.tr (MonoidAlgebra.single h 1 * z) = 0) →
      W.GDet.repAlg (W.mat ρ) A (MonoidAlgebra.mapRingHom F.G₀ (f : B.B →+* A) z) = 0 :=
    fun z hz => relKill_push B.u.D (f : B.B →+* A) ρ hρ hD z hz
  have hsing : ∀ (x : F.G₀) (b : B.B), W.GDet.repAlg (W.mat ρ) A
      (MonoidAlgebra.mapRingHom F.G₀ (f : B.B →+* A) (MonoidAlgebra.single x b)) = (f b) • W.mat ρ x := by
    intro x b
    rw [← relKill_single]
    congr 1
    simp [MonoidAlgebra.mapRingHom]
  refine ⟨fun v g => ?_, fun u g hg => ?_⟩
  · have h0 := key _ (B.u.Ord v g)
    rw [W.GFrame.oEl.eq_1, map_list_prod, map_list_prod, List.map_map, List.map_ofFn] at h0
    simpa only [Function.comp_def, map_sub, hsing, map_one, one_smul,
      Algebra.algebraMap_eq_smul_one] using h0
  · have h0 := key _ (fun h => B.u.I u g hg h)
    simp only [map_sub, hsing, map_one, one_smul, sub_eq_zero] at h0
    exact Units.ext h0
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.LiftRep
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.EbSMul
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private def ebS {K : Type} [CommRing K] {n : ℕ} (X : Matrix (Fin n) (Fin n) (DualNumber K)) :
    Matrix (Fin n) (Fin n) K := Matrix.of fun i j => (X i j).snd

private theorem ebS_mul {K : Type} [CommRing K] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) (DualNumber K)) :
    ebS (X * Y) = X.map (dF K) * ebS Y + ebS X * Y.map (dF K) := by
  ext i j
  simp only [ebS, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.add_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [dF, smul_eq_mul, MulOpposite.smul_eq_mul_unop, mul_comm]

theorem UpperTheory.V.Ws.Eb.tanOf :
    ∀ {K G : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ} (ρ' : G →* GL (Fin n) (DualNumber K)), Continuous ρ' →
        Continuous (W.pushRep (dF K) ρ') ∧ ∃ y ∈ Z1 (Loc.adGL (W.pushRep (dF K) ρ')), IsTan (W.pushRep (dF K) ρ') y ρ' := by
  intro K G _ _ _ _ _ _ n ρ' hρ'
  set ρ := W.pushRep (dF K) ρ' with hρ
  have hdF : Continuous (dF K) := TrivSqZeroExt.continuous_fst
  have hv : Continuous fun g => (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) :=
    Units.continuous_val.comp hρ'
  have hi : Continuous fun g => (↑((ρ' g)⁻¹) : Matrix (Fin n) (Fin n) (DualNumber K)) :=
    Units.continuous_coe_inv.comp hρ'
  have hc : Continuous ρ := by
    rw [Units.continuous_iff]
    exact ⟨hv.matrix_map hdF, hi.matrix_map hdF⟩
  have hci : Continuous fun g => (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) :=
    Units.continuous_coe_inv.comp hc
  have e : ∀ g, (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)).map (dF K) = (↑(ρ g) : Matrix (Fin n) (Fin n) K) :=
    fun g => rfl
  have hS : Continuous fun g => ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) :=
    continuous_matrix fun i j => TrivSqZeroExt.continuous_snd.comp (hv.matrix_elem i j)
  refine ⟨hc, fun g => ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K),
    ⟨hS.matrix_mul hci, ?_⟩, ?_⟩
  · intro g h
    show ebS (↑(ρ' (g * h)) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ (g * h))⁻¹) : Matrix (Fin n) (Fin n) K) =
      ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) +
        (↑(ρ g) : Matrix (Fin n) (Fin n) K) * (ebS (↑(ρ' h) : Matrix (Fin n) (Fin n) (DualNumber K)) *
          (↑((ρ h)⁻¹) : Matrix (Fin n) (Fin n) K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K)
    rw [map_mul, map_mul, Units.val_mul, ebS_mul, e, e, _root_.mul_inv_rev, Units.val_mul, add_mul]
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
    exact add_comm _ _
  · intro g i j
    show _ = (_, (ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) *
      (↑(ρ g) : Matrix (Fin n) (Fin n) K)) i j)
    rw [Units.inv_mul_cancel_right]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DetRep
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.detRep :
    ∀ {A k G : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [Field k] (f : A →+* k) [IsLocalHom f] [Group G] {n : ℕ} (D : W.GDet n A G) (ρ : G →* GL (Fin n) k), 1 ≤ n → Function.Surjective f → Full ρ → D.map f = W.GDet.ofRep (W.mat ρ) →
        ∃ ρ' : G →* GL (Fin n) A, D = W.GDet.ofRep (W.mat ρ') ∧ W.pushRep f ρ' = ρ ∧ Full ρ' :=
  _root_.UpperTheory.Reformulated.B.CayleyHamiltonSymmetric.detRep
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem lr_cont {Γ R E : Type} [TopologicalSpace Γ] [CommRing R] [NormedAddCommGroup E] (I : Ideal R) (f : Γ → R)
    (hf : AdicCont I f) (y : R →+ E) (hy : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ x ∈ I ^ n, ‖y x‖ ≤ ε) :
    Continuous fun g => y (f g) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := hy (ε / 2) (half_pos hε)
  filter_upwards [(hf n).eventually_eq g₀] with g hg
  have h1 := hn _ (Ideal.Quotient.eq.1 hg)
  rw [map_sub] at h1
  rw [dist_eq_norm]
  exact h1.trans_lt (half_lt_self hε)

private theorem lr_cont2 {l : ℕ} [Fact l.Prime] (c : Coef l) {Γ R : Type} [TopologicalSpace Γ] [CommRing R] [Algebra c.O R]
    [IsCO c.O R] (f : Γ → R) (hf : AdicCont (maximalIdeal R) f) (x : R →ₐ[c.O] DualNumber (PadicAlgCl l)) :
    Continuous fun g => x (f g) := by
  obtain ⟨-, a, ha1, ha0, ha⟩ := (coPt c R).1 ((TrivSqZeroExt.fstHom c.O (PadicAlgCl l) (PadicAlgCl l)).comp x)
  have h1 : Continuous fun g => (x (f g)).fst := by
    refine lr_cont _ f hf
      ((TrivSqZeroExt.fstHom c.O (PadicAlgCl l) (PadicAlgCl l)).comp x).toRingHom.toAddMonoidHom fun ε hε => ?_
    obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).eventually (gt_mem_nhds hε)).exists
    exact ⟨k, fun z hz => (ha k z hz).trans hk.le⟩
  have h2 : Continuous fun g => (x (f g)).snd :=
    lr_cont _ f hf ((TrivSqZeroExt.sndHom (PadicAlgCl l) (PadicAlgCl l)).toAddMonoidHom.comp x.toRingHom.toAddMonoidHom)
      ((coPt c R).2 x).2
  exact h1.prodMk h2

theorem UpperTheory.V.Ws.Eb.liftRep :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x' : B.B →ₐ[c.O] DualNumber (PadicAlgCl l)) (ρ : F.G₀ →* GL (Fin n) (PadicAlgCl l)), 1 ≤ n → Full ρ → B.u.D.map ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) = W.GDet.ofRep (W.mat ρ) →
        ∃ (ρ' : F.G₀ →* GL (Fin n) (DualNumber (PadicAlgCl l))) (y : F.G₀ → Matrix (Fin n) (Fin n) (PadicAlgCl l)), B.u.D.map (x' : B.B →+* DualNumber (PadicAlgCl l)) = W.GDet.ofRep (W.mat ρ') ∧ W.pushRep (dF _) ρ' = ρ ∧ Full ρ' ∧ Continuous ρ ∧ y ∈ Z1 (Loc.adGL ρ) ∧ IsTan ρ y ρ' := by
  intro l _ F c n r B x' ρ hn hρ hD
  haveI : Module.Finite (PadicAlgCl l) (DualNumber (PadicAlgCl l)) :=
    inferInstanceAs (Module.Finite (PadicAlgCl l) (PadicAlgCl l × PadicAlgCl l))
  haveI : IsArtinianRing (DualNumber (PadicAlgCl l)) := IsArtinianRing.of_finite (PadicAlgCl l) _
  haveI : IsAdicComplete (maximalIdeal (DualNumber (PadicAlgCl l))) (DualNumber (PadicAlgCl l)) := inferInstance
  haveI : IsLocalHom (dF (PadicAlgCl l)) := ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
  obtain ⟨ρ', h1, h2, h3⟩ := detRep (dF (PadicAlgCl l)) (B.u.D.map (x' : B.B →+* DualNumber (PadicAlgCl l))) ρ hn
    (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩) hρ (((AlgebraTools.Det.mapApi B.u.D _).2.2.2.2.2.2.1 _).trans hD)
  have htr : ∀ g, (W.mat ρ' g).trace = x' (B.u.D.lam 1 (MonoidAlgebra.single g 1)) := fun g => by
    have e1 := (AlgebraTools.Det.mapApi B.u.D (x' : B.B →+* DualNumber (PadicAlgCl l))).2.2.1 1 g
    have e2 := (AlgebraTools.Det.repApi (W.mat ρ')).2.2.1 hn (MonoidAlgebra.single g 1)
    have e3 : W.GDet.repAlg (W.mat ρ') _ (MonoidAlgebra.single g 1) = W.mat ρ' g := by
      refine Matrix.ext fun i j => ?_
      simp [W.GDet.repAlg]
    rw [h1] at e1
    rw [e3] at e2
    exact e2.symm.trans e1
  have hc : Continuous ρ' := (trPlus ρ' h3).2 (by
    simp only [htr]
    exact lr_cont2 c _ (B.u.cont 1) x')
  obtain ⟨h4, y, h5, h6⟩ := tanOf ρ' hc
  rw [h2] at h4 h5 h6
  exact ⟨ρ', y, h1, h2, h3, h4, h5, h6⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.ConstOf
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.FlagCharsUnique
open Polynomial Matrix IsLocalRing TensorProduct

private theorem exists_invariant_flag_mod_l {R : Type} [CommRing R] {n : ℕ} (P P' V : Matrix (Fin n) (Fin n) R)
    (hP : ∀ i j, j < i → P i j = 0) (hP' : ∀ i j, j < i → P' i j = 0)
    (hu : ∀ i j, j < i → IsUnit (P i i - P' j j)) (hE : P * V = V * P') :
    ∀ i j, j < i → V i j = 0 := by
  have key : ∀ j i : Fin n, j < i → V i j = 0 := by
    intro j
    induction j using WellFoundedLT.induction with
    | ind j ihj =>
      intro i
      induction i using WellFoundedGT.induction with
      | ind i ihi =>
        intro hji
        have h := congrFun (congrFun hE i) j
        rw [Matrix.mul_apply, Matrix.mul_apply] at h
        have hL : ∑ k, P i k * V k j = P i i * V i j := by
          refine Finset.sum_eq_single i ?_ (by simp)
          intro k _ hk
          rcases lt_or_gt_of_ne hk with h1 | h1
          · rw [hP i k h1, zero_mul]
          · rw [ihi k h1 (hji.trans h1), mul_zero]
        have hR : ∑ k, V i k * P' k j = V i j * P' j j := by
          refine Finset.sum_eq_single j ?_ (by simp)
          intro k _ hk
          rcases lt_or_gt_of_ne hk with h1 | h1
          · rw [ihj k h1 i (h1.trans hji), zero_mul]
          · rw [hP' k j h1, mul_zero]
        rw [hL, hR] at h
        have h0 : (P i i - P' j j) * V i j = 0 := by
          linear_combination h
        exact ((hu i j hji).mul_right_eq_zero).1 h0
  intro i j h
  exact key j i h

private theorem diag_mul {R : Type} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R)
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) :
    (A * B) i i = A i i * B i i :=
  _root_.UpperTheory.Reformulated.B.S8.diag_mul A B hA hB i

theorem UpperTheory.V.AlgebraTools.flag_chars_unique :
    ∀ {R Γ : Type} [CommRing R] [IsLocalRing R] [Group Γ] {n : ℕ} (r : Γ →* GL (Fin n) R) (ψ ψ' : Fin n → Γ →* Rˣ) (g g' : GL (Fin n) R), (n : Cardinal) ≤ Cardinal.mk (ResidueField R) → Function.Injective (fun i => (residue R : R →* ResidueField R).comp ((Units.coeHom R).comp (ψ i))) → (∀ i s, residue R (ψ i s) = residue R (ψ' i s)) → (∀ s, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) R) i j = 0) ∧ ∀ i, (g * r s * g⁻¹ : GL (Fin n) R) i i = (ψ i s : R)) → (∀ s, (∀ i j, j < i → (g' * r s * g'⁻¹ : GL (Fin n) R) i j = 0) ∧ ∀ i, (g' * r s * g'⁻¹ : GL (Fin n) R) i i = (ψ' i s : R)) → ψ = ψ' ∧ ∀ i j, j < i → (g * g'⁻¹ : GL (Fin n) R) i j = 0 := by
  intro R Γ _ _ _ n r ψ ψ' g g' hn hinj hres h1 h2
  obtain ⟨z, hz⟩ := UpperTheory.V.AlgebraTools.sep_chars (fun i => (Units.coeHom R).comp (ψ i)) hn hinj
  have hcomm : ∀ s, ((g * r s * g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *
      ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *
      ((g' * r s * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
    intro s
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have key : ∀ w : MonoidAlgebra R Γ, ∃ P P' : Matrix (Fin n) (Fin n) R,
      (∀ i j, j < i → P i j = 0) ∧ (∀ i j, j < i → P' i j = 0) ∧
      P * ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
        ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * P' ∧
      (∀ i, P i i = MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) w) ∧
      (∀ i, residue R (P' i i) = residue R (P i i)) := by
    intro w
    induction w using MonoidAlgebra.induction_on with
    | of s =>
      refine ⟨_, _, (h1 s).1, (h2 s).1, hcomm s, fun i => ?_, fun i => ?_⟩
      · rw [MonoidAlgebra.lift_of]; exact (h1 s).2 i
      · rw [(h1 s).2 i, (h2 s).2 i, hres]
    | add a b ha hb =>
      obtain ⟨P, P', a1, a2, a3, a4, a5⟩ := ha
      obtain ⟨Q, Q', b1, b2, b3, b4, b5⟩ := hb
      refine ⟨P + Q, P' + Q', fun i j h => ?_, fun i j h => ?_, ?_, fun i => ?_, fun i => ?_⟩
      · rw [Matrix.add_apply, a1 i j h, b1 i j h, add_zero]
      · rw [Matrix.add_apply, a2 i j h, b2 i j h, add_zero]
      · rw [add_mul, mul_add, a3, b3]
      · rw [Matrix.add_apply, map_add (f := _), a4, b4]
      · rw [Matrix.add_apply, Matrix.add_apply, map_add (f := _), map_add (f := _), a5, b5]
    | smul c a ha =>
      obtain ⟨P, P', a1, a2, a3, a4, a5⟩ := ha
      refine ⟨c • P, c • P', fun i j h => ?_, fun i j h => ?_, ?_, fun i => ?_, fun i => ?_⟩
      · rw [Matrix.smul_apply, a1 i j h, smul_zero]
      · rw [Matrix.smul_apply, a2 i j h, smul_zero]
      · rw [Matrix.smul_mul, Matrix.mul_smul, a3]
      · rw [Matrix.smul_apply, map_smul, a4]
      · rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, a5]
  obtain ⟨P, P', a1, a2, a3, a4, a5⟩ := key z
  have hV := exists_invariant_flag_mod_l P P' _ a1 a2 (fun i j h => by
    have hu := hz i j h.ne'
    rw [← a4, ← a4, ← residue_ne_zero_iff_isUnit, map_sub] at hu
    rw [← residue_ne_zero_iff_isUnit, map_sub, a5]
    exact hu) a3
  refine ⟨?_, hV⟩
  have hdet : IsUnit (((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  rw [Matrix.det_of_upperTriangular (fun i j h => hV i j h)] at hdet
  funext i
  ext s
  have hu : IsUnit (((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i i) :=
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem
      (fun k => ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) k k) (Finset.mem_univ i)) hdet
  have h := congrFun (congrFun (hcomm s) i) i
  rw [diag_mul _ _ (h1 s).1 hV, diag_mul _ _ hV (h2 s).1, (h1 s).2 i, (h2 s).2 i, mul_comm] at h
  exact hu.mul_left_cancel h
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem res_iff {K : Type} [Field K] (a b : DualNumber K) :
    residue (DualNumber K) a = residue (DualNumber K) b ↔ a.fst = b.fst := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not, TrivSqZeroExt.fst_sub, sub_eq_zero]

private theorem flag_const {K H : Type} [Field K] [Infinite K] [Group H] {n : ℕ} (ρ : H →* GL (Fin n) K)
    (ρ' : H →* GL (Fin n) (DualNumber K)) (Q : GL (Fin n) (DualNumber K))
    (hQ : ∀ g, ρ' g = Q * W.pushRep (algebraMap _ (DualNumber K)) ρ g * Q⁻¹) (ψ : Fin n → H →* (DualNumber K)ˣ)
    (hinj : Function.Injective fun i => W.pushCh (dF K) (ψ i)) (h0 : W.HasFlag ρ fun i => W.pushCh (dF K) (ψ i))
    (h1 : W.HasFlag ρ' ψ) (i : Fin n) (s : H) : (ψ i s : DualNumber K).snd = 0 := by
  obtain ⟨g, hg⟩ := h0
  obtain ⟨g', hg'⟩ := h1
  let ι : K →+* DualNumber K := algebraMap _ _
  have hinf : Infinite (ResidueField (DualNumber K)) :=
    Infinite.of_injective _ ((residue (DualNumber K)).comp ι).injective
  have e : ∀ s, GeneralLinearGroup.map ι g * Q⁻¹ * ρ' s * (GeneralLinearGroup.map ι g * Q⁻¹)⁻¹ =
      GeneralLinearGroup.map ι (g * ρ s * g⁻¹) := fun s => by
    rw [hQ, map_mul, map_mul, map_inv]
    show _ * (_ * GeneralLinearGroup.map ι (ρ s) * _) * _ = _
    group
  have := (AlgebraTools.flag_chars_unique ρ' ψ (fun i => W.pushCh ι (W.pushCh (dF K) (ψ i))) g'
    (GeneralLinearGroup.map ι g * Q⁻¹) ((Cardinal.natCast_lt_aleph0).le.trans (Cardinal.aleph0_le_mk _))
    (fun a b hab => hinj (MonoidHom.ext fun t => Units.ext ((res_iff _ _).1 (DFunLike.congr_fun hab t))))
    (fun a t => (res_iff _ _).2 rfl) hg' (fun t => by
      rw [e]
      refine ⟨fun a b hab => ?_, fun a => ?_⟩
      · show ι ((g * ρ t * g⁻¹ : GL (Fin n) K) a b) = 0
        rw [(hg t).1 a b hab, map_zero]
      · show ι ((g * ρ t * g⁻¹ : GL (Fin n) K) a a) = _
        rw [(hg t).2 a]
        rfl)).1
  rw [congrFun this i]
  rfl

theorem UpperTheory.V.Ws.Eb.constOf :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x' : B.B →ₐ[c.O] DualNumber (PadicAlgCl l)) (ρ : F.G₀ →* GL (Fin n) (PadicAlgCl l)) (ρ' : F.G₀ →* GL (Fin n) (DualNumber (PadicAlgCl l))) (Q : GL (Fin n) (DualNumber (PadicAlgCl l))), B.u.D.map (x' : B.B →+* DualNumber (PadicAlgCl l)) = W.GDet.ofRep (W.mat ρ') → (∀ g, ρ' g = Q * W.pushRep (algebraMap _ (DualNumber (PadicAlgCl l))) ρ g * Q⁻¹) →
        (∀ v, Function.Injective fun i => W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i)) → (∀ v, W.HasFlag (ρ.comp (F.φ v)) fun i => W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i)) →
        (∀ v, W.HasFlag (ρ'.comp (F.φ v)) fun i => W.pushCh (x' : B.B →+* DualNumber (PadicAlgCl l)) (B.u.ψ v i)) → ∀ b, (x' b).snd = 0 := by
  intro l hl F c n r B x' ρ ρ' Q hD hQ hinj h0 h1
  obtain ⟨-, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : Finite (ResidueField c.O) := hfin
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  refine derZero c B.B x' _ (CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow r B) ?_
  rintro a (⟨i, g, -, -, rfl⟩ | ⟨v, i, g, rfl⟩)
  · have e1 := (AlgebraTools.Det.mapApi B.u.D (x' : B.B →+* DualNumber (PadicAlgCl l))).2.2.1 i g
    have e2 : W.GDet.ofRep (W.mat ρ') =
        (W.GDet.ofRep (W.mat ρ)).map (algebraMap _ (DualNumber (PadicAlgCl l))) := by
      rw [(AlgebraTools.Det.repApi _).2.2.2.2.2.1]
      refine (AlgebraTools.Det.repApi _).2.2.2.2.2.2.2 _ Q⁻¹ fun y => ?_
      have : Q⁻¹ * ρ' y = W.pushRep (algebraMap _ (DualNumber (PadicAlgCl l))) ρ y * Q⁻¹ := by
        rw [hQ]; group
      exact congrArg Units.val this
    rw [hD, e2, (AlgebraTools.Det.mapApi _ _).2.2.1] at e1
    exact (congrArg TrivSqZeroExt.snd e1).symm
  · exact flag_const (ρ.comp (F.φ v)) (ρ'.comp (F.φ v)) Q (fun g => hQ _)
      (fun i => W.pushCh (x' : B.B →+* DualNumber (PadicAlgCl l)) (B.u.ψ v i)) (hinj v) (h0 v) (h1 v) i g
end
