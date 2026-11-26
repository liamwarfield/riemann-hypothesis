module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.ExistsPlaceAbovePrime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsCmFieldTwistH1
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdjointVanishingGsp4RigidPoint
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWPtAut
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Ws.Pt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp
theorem UpperTheory.GalN.V.point_automorphy_w_of_gsp_cusp_sub_rank_four :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (ι : PadicAlgCl l ≃+* ℂ) (r : G T.F Ω →* M4 (PadicAlgCl l)), (∀ g, IsGSp (algebraMap c'.O (PadicAlgCl l) (inc h (D.th (resQ T.F g)))) (r g)) → ∀ (κ : G T.L Ω →* (PadicAlgCl l)ˣ) (π : CuspSub T.L 4) (a : ℤ) (k : ℕ), Continuous κ → 0 < k → Even (a + n) → (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := T.L) A, (κ s ^ 2 * cycBar T.L Ω l s ^ (-a)) ^ k = 1) → (CG.mk π).IsRegAlg → Af.AttC ι (Af.tw (r.comp (resLe T.F_le)).toHomUnits κ) π → _root_.UpperTheory.V.Z.Win.WitA ι (Af.tw (r.comp (resLe T.F_le)).toHomUnits κ) → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (K.rhoQ n r) := by
  intro hP Ω _ _ _ l _ c D T c' h K n ι r hr κ π a k hκ hk ha hw hreg hatt hW
  have h1 := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP T.L Ω l ι 4 _).2.1.2 ⟨π, hreg, hatt⟩
  have h2 : Af.IsAlgChar ι (K.twc n * κ⁻¹) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hP T.L Ω l ι).1 _ ((twc_cont K n).mul hκ.inv) fun w hlw => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    have hl : A.valuation (l : Ω) < 1 := by
      have h1 := (hA ((l : ℕ) : 𝓞 T.L)).2 hlw
      have e : algebraMap T.L Ω (((l : ℕ) : 𝓞 T.L) : T.L) = (l : Ω) := by simp
      rwa [e] at h1
    obtain ⟨e, k', hk', he, H⟩ := twWts K n A hl
    obtain ⟨m, hm⟩ : Even (e - a) := by
      have := he.sub ha
      rwa [add_sub_add_right_eq_sub] at this
    have half_pow {M : Type} [CommGroup M] {x y u : M} {a e m : ℤ} {k k' : ℕ}
        (hm : e - a = m + m) (hx : (x ^ 2 * u ^ (-e)) ^ k' = 1)
        (hy : (y ^ 2 * u ^ (-a)) ^ k = 1) :
        (x * y⁻¹ * u ^ (-m)) ^ (2 * (k * k')) = 1 := by
      obtain rfl : e = a + m + m := by omega
      have hsq : (x * y⁻¹ * u ^ (-m)) ^ 2 =
          (x ^ 2 * u ^ (-(a + m + m))) * (y ^ 2 * u ^ (-a))⁻¹ := by
        rw [mul_inv, mul_mul_mul_comm, mul_pow, mul_pow, inv_pow]
        congr 1
        group
      have hx' : (x ^ 2 * u ^ (-(a + m + m))) ^ (k * k') = 1 := by
        rw [mul_comm k k', pow_mul, hx, one_pow]
      have hy' : (y ^ 2 * u ^ (-a)) ^ (k * k') = 1 := by
        rw [pow_mul, hy, one_pow]
      rw [pow_mul, hsq, mul_pow, inv_pow, hx', hy', inv_one, mul_one]
    exact ⟨A, hA, m, 2 * (k * k'), by positivity, fun s hs => half_pow hm (H s hs) (hw A hl s hs)⟩
  have h3 := _root_.UpperTheory.V.Af.twist_invariance_automorphic hP T.L Ω l ι 4 _ _ h1 h2
  have h4 : Af.tw (Af.tw (r.comp (resLe T.F_le)).toHomUnits κ) (K.twc n * κ⁻¹) = K.rhoQ n r := by
    ext g : 2
    rw [Af.tw_val, Af.tw_val, smul_smul, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
      Units.inv_mul_cancel_right, K.rho_val]
    rfl
  rw [h4] at h3
  obtain ⟨P, hPair⟩ := ptPair K n r hr
  exact _root_.UpperTheory.GalN.V.mkCsd'_alt (_root_.UpperTheory.GalN.V.csdOf0_alt hP (W.Lp T.L) T.L Ω inferInstance l ι 4 (by norm_num) _ K.s.c P K.s.hc h3 hPair) fun _ =>
    h4 ▸ _root_.UpperTheory.V.Z.Win.WitA.witness_twist_algebraic_character hP.toClassicalTheorems h2 ((twc_cont K n).mul hκ.inv) ⟨π, hreg, hatt⟩ hW
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
section Alg
open Matrix
end Alg
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
end Gal
section Core
open scoped Matrix

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
theorem adjoint_vanishing_gsp4_rigid_point (hU : _root_.UpperTheory.V.Ws.UnramifiedInputs) (hAd : _root_.UpperTheory.V.Th.AdjointLiftingTheorem) {D : Raw Ω c} (hG : D.Good) {T : Tower D} (hF : T.Fit) (hD : T.Deep) {c' : Coef l}
    {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (y : X.A →ₐ[c'.O] PadicAlgCl l) (ι : PadicAlgCl l ≃+* ℂ)
    (r r₁ : G ℚ Ω →* M4 (PadicAlgCl l)) (hconj : IsConj4 r r₁)
    (hres : r₁.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r)
    (hw : T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l))) (hc : Continuous r) (hm : D.Mult r)
    (hi : Irr (r.comp T.L.fixingSubgroup.subtype)) (haut : Af.IsAut ι (r.toHomUnits.comp (resQ T.L)))
    (hWit : _root_.UpperTheory.V.Z.Win.WitA ι (r.toHomUnits.comp (resQ T.L))) (hf : FreeAt l (r.toHomUnits.comp (resQ T.K))) :
    ∃ ρ : K.V.frame.G₀ →* GL (Fin 4) (Qbar l), ρ.comp K.V.pr = K.rhoQ 0 (r.comp (resQ T.F)) ∧ AdZero K.V ρ := by
  obtain ⟨⟨B, -⟩, hB⟩ := _root_.UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link hU D T hF hD c' h K X 0
  obtain ⟨φ, hφ⟩ := hB B
  obtain ⟨u, hu⟩ := hconj
  have hcj : ∀ g, K.rhoQ 0 (X.P.map (y : X.A →+* PadicAlgCl l)).r g = u * K.rhoQ 0 (r.comp (resQ T.F)) g * u⁻¹ := fun g => by
    apply Units.ext
    rw [← hres, Units.val_mul, Units.val_mul, K.rho_val, K.rho_val, MonoidHom.comp_apply, MonoidHom.comp_apply, hu,
      Matrix.mul_smul, Matrix.smul_mul]
  have hrep₁ : (Link.pt φ y).IsRep (K.rhoQ 0 _) := auRep D T c' h K X B 0 φ hφ y _ fun _ => rfl
  have hrep : (Link.pt φ y).IsRep (K.rhoQ 0 (r.comp (resQ T.F))) := by
    refine Eq.trans hrep₁ ((AlgebraTools.Det.repApi _).2.2.2.2.2.2.2 _ u fun g => ?_).symm
    exact congrArg Units.val (eq_mul_inv_iff_mul_eq.1 (hcj g)).symm
  have hcρ := Pt.rho_cont K 0 (r := r.comp (resQ T.F)) (hc.comp (Af.continuous_restrictScalarsHom ℚ T.F Ω))
  have hirr : Af.IsIrr (K.rhoQ 0 (r.comp (resQ T.F))) :=
    (auIrr _ (r.comp (resQ T.L)) hi fun g => ⟨IntermediateField.fixingSubgroupEquiv T.L g, rfl⟩).2 (K.twc 0)
  have hfull : Eb.Full (K.rhoQ 0 (r.comp (resQ T.F))) :=
    (AlgebraTools.Det.irrIffSpan (W.mat _)).1 fun N hN => hirr.2.2 N le_top fun g v hv => hN g v hv
  obtain ⟨hs, hq, -⟩ := phiKer K.V
  let τ := K.rhoQ 0 (r.comp (resQ T.F))
  have hchi (g : G T.L Ω) :
      (Link.pt φ y).D.chi (MonoidAlgebra.single (K.V.pr g) 1) =
        (W.GDet.ofRep (W.mat τ)).chi (MonoidAlgebra.single g 1) := by
    rw [← hrep]
    change (Link.pt φ y).D.D (PadicAlgCl l)[X] _ =
      (Link.pt φ y).D.D (PadicAlgCl l)[X] (MonoidAlgebra.mapDomainRingHom (PadicAlgCl l)[X] K.V.pr _)
    congr 1
    rw [map_sub]
    simp
    let pg : K.V.frame.G₀ := K.V.pr g
    change MonoidAlgebra.single (1 : K.V.frame.G₀) Polynomial.X -
        MonoidAlgebra.mapRingHom K.V.frame.G₀ C (MonoidAlgebra.single pg (1 : Qbar l)) =
      MonoidAlgebra.single (1 : K.V.frame.G₀) Polynomial.X - MonoidAlgebra.single pg 1
    rw [MonoidAlgebra.mapRingHom_single, map_one]
    exact Eq.refl _
  have hker : K.V.pr.ker ≤ τ.ker := fun g hg => by
    have htrace := (AlgebraTools.Det.repApi (W.mat τ)).2.2.1 (by decide)
    have hzero := (Eb.trPlus τ hfull).1 (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1) fun a => by
      have e : (W.GDet.ofRep (W.mat τ)).tr (MonoidAlgebra.single (a * g) 1) =
          (W.GDet.ofRep (W.mat τ)).tr (MonoidAlgebra.single a 1) := by
        unfold W.GDet.tr W.GDet.lam
        rw [← hchi, ← hchi, map_mul, MonoidHom.mem_ker.1 hg, mul_one]
      rw [htrace, htrace] at e
      rw [htrace, mul_sub, map_sub, Matrix.trace_sub, MonoidAlgebra.single_mul_single,
        MonoidAlgebra.single_mul_single, mul_one, mul_one, e, sub_self]
    rw [map_sub, sub_eq_zero] at hzero
    refine Units.ext ?_
    simpa [W.GDet.repAlg, W.mat] using hzero
  let ρ := K.V.pr.liftOfSurjective hs ⟨τ, hker⟩
  have hρ : ρ.comp K.V.pr = K.rhoQ 0 (r.comp (resQ T.F)) :=
    MonoidHom.liftOfRightInverse_comp K.V.pr (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨τ, hker⟩
  have hfull' : Eb.Full ρ := by
    refine top_le_iff.1 (le_trans (le_of_eq hfull.symm) (Submodule.span_mono ?_))
    rintro _ ⟨g, rfl⟩
    exact ⟨K.V.pr g, congrArg Units.val (DFunLike.congr_fun hρ g)⟩
  refine ⟨ρ, hρ, ?_⟩
  have hanti : StrictAnti fun i => (D.wts4 i : ℤ) := by
    have := hG.two_le
    refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
    fin_cases i <;> simp [Raw.wts4]
    omega
  obtain ⟨m, hmm, k, hk, hmk⟩ := Pt.ptWts K X B 0 φ hφ y _ (fun i => by simp) hw
  obtain ⟨π, hreg, hatt⟩ := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hU.pr T.L Ω l ι 4 _).2.1.1 haut
  have haut' : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (K.rhoQ 0 (r.comp (resQ T.F))) := by
    have e : Af.tw ((r.comp (resQ T.F)).comp (resLe T.F_le)).toHomUnits 1 = r.toHomUnits.comp (resQ T.L) := by
      ext g : 2
      rw [Af.tw_val, MonoidHom.one_apply, Units.val_one, one_smul]
      rfl
    refine _root_.UpperTheory.GalN.V.point_automorphy_w_of_gsp_cusp_sub_rank_four hU.pr K 0 ι _ (fun g => hm _) 1 π 0 1 continuous_const one_pos (by simp) (fun A _ s _ => by simp) hreg ?_ ?_ <;>
      rwa [e]
  have hunr := Pt.ptUnr K 0 (X.P.map (y : X.A →+* PadicAlgCl l)).r fun g hg => by
    change (y : X.A →+* PadicAlgCl l).mapMatrix (X.P.r g) = 1
    rw [X.pair.kill g hg, map_one]
  have hfl : ∀ v : W.Vl l T.L, W.HasFlag ((K.rhoQ 0 (r.comp (resQ T.F))).comp (Dec (F := T.L) (K.s.A v)).subtype)
      ((Link.pt φ y).psi v) := fun v => by
    obtain ⟨a, ha⟩ := Pt.ptFlag K X B 0 φ hφ y v
    refine ⟨a * u, fun s => ?_⟩
    have h1 := ha s
    rw [MonoidHom.comp_apply, hcj] at h1
    simpa only [mul_inv_rev, mul_assoc, MonoidHom.comp_apply] using h1
  have hapt : _root_.UpperTheory.V.Th.AutomorphicPointGalois ι (Link.pt φ y) ρ := by
    refine ⟨hq.continuous_iff.2 ?_, hρ ▸ hrep, ?_, hρ ▸ haut', ?_, fun v => ?_⟩
    · have e : (ρ : _ → _) ∘ K.V.pr = K.rhoQ 0 (r.comp (resQ T.F)) := congrArg DFunLike.coe hρ
      exact e ▸ hcρ
    · exact auArith hU.pr.toClassicalTheorems.litN.aut.art D T c' h K X B φ hφ y _ (fun _ => rfl) (Pt.psi_cont _) _ hanti hw
    · rintro _ ⟨g, hg, rfl⟩
      have h1 := hunr g hg
      rw [hcj, mul_inv_eq_one, mul_eq_left] at h1
      exact (DFunLike.congr_fun hρ g).trans h1
    · have h1 := hfl v
      rw [← hρ] at h1
      exact h1
  have hirr₀ : U3.MatIrr ⊤ (W.mat ρ) := fun N hN => (AlgebraTools.Det.irrIffSpan (W.mat ρ)).2 hfull' N fun g v hv => hN g trivial v hv
  have hfree : Free K.V.frame fun v => (Link.pt φ y).psi v := fun v : W.Vl l T.L => by
    have : IsGalois ℚ Ω := {}
    obtain ⟨g, hg, hc, α, hα, hcp⟩ := hf (K.s.A v) (by simpa using (K.s.hA v _).2 v.2)
    have hi : T.L.fixingSubgroup.index ≠ 0 := by
      rw [← IntermediateField.finrank_eq_fixingSubgroup_index Ω T.L]
      exact Module.finrank_pos.ne'
    obtain ⟨m, hm, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hi (resQ T.K g)
    let σ : G T.L Ω := IntermediateField.fixingSubgroupEquiv T.L ⟨_, hmem⟩
    have hσ : resQ T.L σ = resQ T.K (g ^ m) := by rw [map_pow]; rfl
    have hdec : σ ∈ Dec (F := T.L) (K.s.A v) := by
      have hpow : resQ T.K (g ^ m) ∈ Dec (F := ℚ) (K.s.A v) :=
        (pow_mem hg m : g ^ m ∈ Dec (F := T.K) (K.s.A v))
      rw [← hσ] at hpow
      exact hpow
    let s : Dec (F := T.L) (K.s.A v) := ⟨σ, hdec⟩
    refine ⟨s, ?_, ?_⟩
    · have hcyc : cycZ ℚ Ω l (resQ T.K (g ^ m)) = 1 := by
        show cycZ T.K Ω l (g ^ m) = 1
        rw [map_pow, hc, one_pow]
      rw [← hσ] at hcyc
      exact (DFunLike.congr_fun K.V.hε _).trans hcyc
    · let M := W.mat (r.toHomUnits.comp (resQ T.K)) g
      let κ := K.twc 0 σ
      let ψ := fun i => (Link.pt φ y).psi v i s
      have hcp' : ((κ : Qbar l) • M ^ m).charpoly = ∏ i, (Polynomial.X - C (ψ i : Qbar l)) := by
        obtain ⟨a, ha⟩ := hfl v
        have htri : ((a * τ σ * a⁻¹ : GL (Fin 4) (Qbar l)) : M4 (Qbar l)).IsUpperTriangular :=
          fun i j hij => (ha s).1 i j hij
        have hconjChar : ((a * τ σ * a⁻¹ : GL (Fin 4) (Qbar l)) : M4 (Qbar l)).charpoly =
            (τ σ : M4 (Qbar l)).charpoly := by
          simpa only [Units.val_mul, Matrix.coe_units_inv] using
            Matrix.charpoly_units_conj a (τ σ : M4 (Qbar l))
        have hmat : (τ σ : M4 (Qbar l)) = (κ : Qbar l) • M ^ m := by
          rw [show τ = K.rhoQ 0 (r.comp (resQ T.F)) from rfl, K.rho_val]
          change (κ : Qbar l) • r (resQ T.L σ) = (κ : Qbar l) • (r (resQ T.K g)) ^ m
          rw [hσ, map_pow, map_pow]
        rw [← hmat, ← hconjChar, Matrix.charpoly_of_isUpperTriangular _ htri]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [show ((a * τ σ * a⁻¹ : GL (Fin 4) (Qbar l)) : M4 (Qbar l)) i i = ψ i from (ha s).2 i]
      have hmatch (i : Fin 4) : ∃ j, ψ j = κ * α i ^ m := by
        have hdet : (Matrix.scalar (Fin 4) (α i : Qbar l) - M).det = 0 := by
          rw [← Matrix.eval_charpoly, hcp, eval_prod]
          exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
        obtain ⟨x, hx, hMx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
        have heig : M *ᵥ x = (α i : Qbar l) • x := by
          rw [Matrix.sub_mulVec, sub_eq_zero] at hMx
          rw [← hMx]
          ext j
          simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
        have hpow (k : ℕ) : M ^ k *ᵥ x = (α i : Qbar l) ^ k • x := by
          induction k with
          | zero => simp
          | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
        have hdet' : (Matrix.scalar (Fin 4) ((κ : Qbar l) * (α i : Qbar l) ^ m) -
            (κ : Qbar l) • M ^ m).det = 0 := by
          refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hx, ?_⟩
          rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hpow, smul_smul, sub_eq_zero]
          ext j
          simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
        rw [← Matrix.eval_charpoly, hcp', eval_prod] at hdet'
        obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 hdet'
        refine ⟨j, Units.ext ?_⟩
        simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hj
        simpa using hj.symm
      choose p hp using hmatch
      have hinj : Function.Injective p := fun i j hij => by
        by_contra hne
        exact hα i j hne m hm (mul_left_cancel ((hp i).symm.trans (hij ▸ hp j)))
      have hsurj := Finite.surjective_of_injective hinj
      intro i j hij k hk e
      obtain ⟨i, rfl⟩ := hsurj i
      obtain ⟨j, rfl⟩ := hsurj j
      change ψ (p i) ^ k = ψ (p j) ^ k at e
      rw [hp, hp, mul_pow, mul_pow, ← pow_mul, ← pow_mul] at e
      exact hα i j (fun h => hij (congrArg p h)) _ (mul_pos hm hk) (mul_left_cancel e)
  exact hAd l T.L Ω K.s K.V K.hV K.noMu c' K.large 4 (by omega) le_rfl K.r K.v0 B ι _ ρ
    (_root_.UpperTheory.V.Th.nice0four_alt ι _ ρ hapt hirr₀ hfree (P1.condC D T hF hD c' h K) (P1.condD D T hF hD c' h K))
    (by
      intro v
      refine ⟨m v, k, ?_, hk, fun i j g hg => ?_⟩
      · intro i j hij
        have h1 := hmm v i j
        have h2 := hanti hij
        simp only at h1 h2
        omega
      · let ψ := (Link.pt φ y).psi v
        change (ψ i g / ψ j g * cycBar T.L Ω l g ^ (m v j - m v i)) ^ k = 1
        have e : ψ i g / ψ j g * cycBar T.L Ω l g ^ (m v j - m v i) =
            (ψ i g * cycBar T.L Ω l g ^ (-m v i)) / (ψ j g * cycBar T.L Ω l g ^ (-m v j)) := by
          rw [mul_div_mul_comm, div_eq_mul_inv (_ ^ (-m v i)), ← zpow_neg, ← zpow_add]
          congr 2
          ring
        rw [e, div_pow, hmk v i g hg, hmk v j g hg, div_one])
end Core
section Rg
open scoped Matrix TensorProduct
section BK
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
  {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
end BK
end Rg
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicOfGsp4RigidSolvableGalois
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
section Alg
open Matrix
end Alg
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
theorem automorphic_of_gsp4_rigid_solvable_galois (H : _root_.UpperTheory.V.Af.HypothesesH') (K L : IntermediateField ℚ Ω) [NumberField K] [NumberField L] [IsCMField K] [IsCMField L]
    (hle : K ≤ L) (hK : Module.finrank ℚ K = 2) (hgal : IsGalois ℚ L) (hsol : IsSolvable (L ≃ₐ[ℚ] L)) (ι : Qbar l ≃+* ℂ)
    (r : G ℚ Ω →* M4 (Qbar l)) (θ : G ℚ Ω →* (Qbar l)ˣ) (hr : Continuous r.toHomUnits) (hθ : Af.IsAlgChar ι θ)
    (hm : ∀ g, IsGSp (θ g : Qbar l) (r g)) (cc : G ℚ Ω) (hc : Af.IsConjEl cc) (hirr : Af.IsIrr (r.toHomUnits.comp (resQ L)))
    (haut : Af.IsAut ι (r.toHomUnits.comp (resQ K))) : Af.IsAut ι (r.toHomUnits.comp (resQ L)) := by
  letI : Algebra K L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[ℚ] L) := hsol
  have s2 : IsSolvable (L ≃ₐ[K] L) :=
    Group.isSolvable_of_isSolvable_injective (f := (AlgEquiv.restrictScalarsHom ℚ : (L ≃ₐ[K] L) →* (L ≃ₐ[ℚ] L)))
      (AlgEquiv.restrictScalars_injective ℚ)
  obtain ⟨P, hP⟩ := auPair r θ hm cc
  have hp : Af.IsPairing cc (r.toHomUnits.comp (Af.resG ℚ K Ω)) (θ.comp (Af.resG ℚ K Ω)) P := fun s s' h => by
    have h' : Af.resG ℚ K Ω s' = cc * Af.resG ℚ K Ω s * cc⁻¹ := h
    have h1 := hP (Af.resG ℚ K Ω s)
    rw [← h'] at h1
    exact h1
  exact (Z.Bc.solQ (_root_.UpperTheory.V.Z.Bc.solC_alt H H.cyc) ℚ K L Ω s2 ⟨inferInstance, Or.inr ⟨hK, inferInstance⟩⟩
    inferInstance inferInstance l ι 4 (by norm_num) (r.toHomUnits.comp (Af.resG ℚ K Ω)) θ
    (hr.comp (Af.continuous_restrictScalarsHom ℚ K Ω)) hirr hθ (auSign _) ⟨cc, _, hc, hp⟩).1 haut
end Gal
section Core
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
end Core
section Rg
open scoped Matrix TensorProduct
section BK
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
  {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
end BK
end Rg
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLinkEx
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk
private theorem pre_ex {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
    (T : Tower D) (hO : T.Ok) (hG : D.Good) (hC : Ctx2 D ∨ Ctx3 D) : Nonempty (Pre T) := by
  obtain ⟨η, N, m, hN, hK, hm, hη, hcc, hun, hv⟩ := etaEx hC
  obtain ⟨κ₀, m', h1, h2, h3, h4, h5⟩ := Tw.kap0 Ω l hG.l_odd T.K T.degK (hO.split 2 hG.two_mem) η N m hN hK hm hη hcc
    (fun A => by
      by_cases hA : Raw.Away D.S A
      · exact Or.inl (hun A hA)
      · simp only [Raw.Away, not_forall, not_not] at hA
        obtain ⟨p, hp, hA⟩ := hA
        exact Or.inr (hO.split p hp A hA))
  obtain ⟨γ, g1, g2, g3, g4⟩ := halfEx hG
  have hl := hG.pl_over l Fact.out
  obtain ⟨t, β, c₁, b1, b2, b3, b4, b5, b6, b7, U, hU, b8⟩ :=
    Tw.bt0 Ω l hG.l_odd T.K T.degK (D.pl l) hl (hO.split l hG.l_mem _ hl)
  exact ⟨{ κ₀ := κ₀, γ := γ, β := β, t := t, κ₀_open := h1, κ₀_ord := ⟨m', h2, h3⟩,
           κ₀_conj := fun σ hσ s s' e hs => by rw [h4 σ hσ s s' e]; exact hv _ hs
           κ₀_unr := fun A hA => h5 A (hun A hA), γ_cont := g1, γ_red := g2, γ_sq := g3, γ_ker := g4,
           β_cont := b3, t_cont := b1, β_t := b2, β_red := fun s => (b4 s).2,
           conj := fun σ hσ s s' e => ⟨b6 σ hσ s s' e, b5 σ hσ s s' e⟩, t_unr := b7,
           cyc := betaCyc Ω l T.K T.degK (D.pl l) hl β b6 U hU b8 }⟩
theorem UpperTheory.V.Ws.nonempty_link_of_fit_deep_unramified :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∃ c₁ : Coef l, ∀ (c' : Coef l) (h : c.O ≤ c'.O), c₁.O ≤ c'.O → Nonempty (Link T c' h) := by
  intro hU Ω _ _ _ l _ c D T hF hD
  have hC : Ctx2 D ∨ Ctx3 D := hF.2.imp And.left And.left
  have hG : D.Good := hC.elim And.left And.left
  have hO := hF.1
  obtain ⟨P⟩ := pre_ex T hO hG hC
  obtain ⟨k1, k2, k3⟩ := kapCont P
  obtain ⟨u1, u2, u3⟩ := kapUnr P hG
  let Q : QCh T :=
    { κ := P.κ, β := P.βL, t := P.tL, κ_cont := k1, β_cont := k2, t_cont := k3, β_t := fun _ hg => P.β_t hg,
      β_red := fun _ => P.β_red _, conj := kapConj P hD, t_unr := u1, unr := u2, tame := u3, mu := kapMu P hG,
      cyc := kapCyc P hG }
  obtain ⟨c₁, -, hL, hκ, hβ, -⟩ := Pr.coefEx l c T.L Ω Q.κ Q.β Q.κ_cont Q.β_cont
  refine ⟨c₁, fun c' h h₁ => ?_⟩
  obtain ⟨κ, a1, a2, -⟩ := liftO c' Q.κ Q.κ_cont fun g => h₁ (hκ g)
  obtain ⟨β, b1, b2, b3⟩ := liftO c' Q.β Q.β_cont fun g => h₁ (hβ g)
  obtain ⟨X⟩ := ochOf Q c' h κ β a1 b1 a2 b2 fun g => b3 g (Q.β_red g)
  obtain ⟨Y⟩ := setEx T hG hO
  obtain ⟨V, hV⟩ := hU.lev l T.L Ω Y.s Y.s.S Y.fin subset_rfl Y.s.split
  obtain ⟨r, r1, r2, r3⟩ := residEx X Y V hG hO hV
  obtain ⟨σ, hσ, hc⟩ := Y.cc
  obtain ⟨g₀, -, hg₀⟩ := Y.om0
  exact ⟨{ s := Y.s, V := V, hV := hV, noMu := noMu hG T.L g₀ hg₀, large := fun τ x => h₁ (hL τ x), e := Y.e, hA := Y.hA,
           κ := X.κ, β := X.β, t := X.t, κ_cont := X.κ_cont, β_cont := X.β_cont, t_cont := X.t_cont, β_t := X.β_t,
           β_red := X.β_red, conj := fun g g' e => X.conj σ hσ g g' (hc g g' e), t_unr := X.t_unr,
           unr := fun A v hA hv g hg =>
             ⟨X.unr A (Y.away A v hA hv) hg, (((Lk.barFacts hG).2.2 A (Y.away A v hA hv) _ ⟨hg.1, hg.2⟩)).2⟩
           tame := X.tame
           mu := fun v g hg => by
             obtain ⟨a, ha⟩ := (prFacts l T.L Ω Y.s V).2.2.2 v g hg
             exact X.mu g a ha
           cyc := X.cyc, r := r, chib := fun i g => by rw [r1]; rfl
           psib := r2, th := r3, v0 := v0ok X Y V hG r r1 }⟩
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
open UpperTheory.V.Z.Win in
theorem UpperTheory.V.Z.Win.Dn.exists_cm_field_twist_h1 (hU : _root_.UpperTheory.V.Ws.UnramifiedInputs) (hAd : _root_.UpperTheory.V.Th.AdjointLiftingTheorem) (D : Raw Ω c) (hD : Ctx2 D ∨ Ctx3 D) (N : ℕ) (hN : 1 ≤ N) (h1 : Af.KillsMu N D.ψ)
    (h2 : Af.KillsMu N D.ξ) (h3 : Af.KillsMu N D.om) (ι : PadicAlgCl l ≃+* ℂ) (r : G ℚ Ω →* M4 (PadicAlgCl l)) (hr : D.EPt r)
    (hirr : Irr r) (haut : _root_.UpperTheory.V.Aut.IsAut4Alt ι r) :
    ∃ (K : IntermediateField ℚ Ω) (_ : NumberField K) (_ : IsCMField K) (θ : G ℚ Ω →* (Qbar l)ˣ), Module.finrank ℚ K = 2 ∧
      (∀ g, IsGSp (θ g : PadicAlgCl l) (r g)) ∧
      ∀ R : Representation (Qbar l) (G ℚ Ω) (M4 (Qbar l)),
        Af.IsAdOf (r.toHomUnits.comp (resQ K)) (θ.comp (resQ K)) R → Af.BlochKatoSelmerVanishes l R := by
  have hG : D.Good := hD.elim (·.1) (·.1)
  obtain ⟨hlev, θ, hθ, hdual, hθv⟩ := level D hG N hN h1 h2 h3 r hr
  have hmul : D.Mult r := (ptIn D hG _ r hr).1
  have hm : ∀ g, IsGSp (θ g : PadicAlgCl l) (r g) := fun g => by
    rw [hθv]
    exact hmul g
  obtain ⟨T, hF, hDp, hT⟩ := spPt hU.coh Ω l c D hD r hr hirr
  obtain ⟨c₁, hc₁⟩ := _root_.UpperTheory.V.Ws.nonempty_link_of_fit_deep_unramified hU D T hF hDp
  obtain ⟨c', h, X, y, r₁, hle, hconj, -, hres, hw, hi₁⟩ := hT c₁
  obtain ⟨K⟩ := hc₁ c' h hle
  have hKL : T.K ≤ T.L := T.hL ▸ le_sup_right
  have hi : Irr (r.comp T.L.fixingSubgroup.subtype) := by
    have irr_of_conj {H F : Type} [Group H] [Field F] {s s' : H →* M4 F}
        (hs : IsConj4 s s') (hirrₛ : Irr s) : Irr s' := by
      obtain ⟨v, hv⟩ := hs
      rw [Irr, eq_top_iff]
      intro X _
      have hspan (Y : M4 F) (hY : Y ∈ Submodule.span F (Set.range s)) :
          (v : M4 F) * Y * (v⁻¹ : (M4 F)ˣ) ∈ Submodule.span F (Set.range s') := by
        induction hY using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨g, rfl⟩ := hx
          exact Submodule.subset_span ⟨g, hv g⟩
        | zero => simp
        | add x y _ _ hx hy => rw [mul_add, add_mul]; exact add_mem hx hy
        | smul a x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ a hx
      have hX := hspan ((v⁻¹ : (M4 F)ˣ) * X * v) (hirrₛ ▸ Submodule.mem_top)
      simpa [mul_assoc] using hX
    obtain ⟨u, hu⟩ := hconj
    refine irr_of_conj ⟨u⁻¹, fun g => ?_⟩ hi₁
    simp only [MonoidHom.comp_apply, hu, inv_inv, ← mul_assoc, Units.inv_mul, one_mul, Units.inv_mul_cancel_right]
  have hiL : Af.IsIrr (r.toHomUnits.comp (resQ T.L)) :=
    (auIrr _ (r.comp (resQ T.L)) hi fun g => ⟨IntermediateField.fixingSubgroupEquiv T.L g, rfl⟩).1
  have hiK : Af.IsIrr (r.toHomUnits.comp (resQ T.K)) :=
    (auIrr _ (r.comp (resQ T.K)) hi fun g =>
      ⟨IntermediateField.fixingSubgroupEquiv T.K ⟨g, IntermediateField.fixingSubgroup_le hKL g.2⟩, rfl⟩).1
  have hanti : StrictAnti ![(D.e : ℤ) + 1, D.e, 1, 0] := by
    have := hG.two_le
    refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
    fin_cases i <;> simp <;> omega
  have hcK : Continuous (r.toHomUnits.comp (resQ T.K)) := hlev.cont.comp (Af.continuous_restrictScalarsHom ℚ T.K Ω)
  have hP := _root_.UpperTheory.GalN.V.autKQ0_alt hU.pr T.K Ω T.degK l ι 4 (by norm_num) r.toHomUnits _ hlev.cont (_root_.UpperTheory.GalN.V.isAutomorphicOverImagQuad_of_isAutQA haut) ⟨θ, hθ, hdual⟩ hiK
  have hf := _root_.UpperTheory.V.Z.Win.RR.freePUA_alt hU.pr T.K Ω T.degK l hG.l_odd ι 4 (by norm_num) _ N _ hN hanti hcK hP
    (_root_.UpperTheory.GalN.V.autQN'_alt hU.pr.toClassicalTheorems (by norm_num) ⟨θ, hθ, hdual⟩ haut hlev.cont T.K T.degK hiK).2
    ((unlRes T.K Ω l 4 N _ r.toHomUnits hN).1 (fun A hA g hg =>
      ⟨IntermediateField.fixingSubgroupEquiv T.K ⟨g, hF.1.split l hG.l_mem A hA hg⟩, rfl⟩) (spUnl D hG N hN h1 h2 h3 r hr))
  obtain ⟨π, hreg, -, hatt⟩ := hP
  obtain ⟨hgal, hsol⟩ := auGal D T
  have hL := _root_.automorphic_of_gsp4_rigid_solvable_galois hU.pr T.K T.L hKL T.degK hgal hsol ι r _ hlev.cont (_root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good hU.pr D hG ι) hmul D.cc hG.isCC hiL
    ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hU.pr T.K Ω l ι 4 _).2.1.2 ⟨π, hreg, hatt⟩)
  have hWit : _root_.UpperTheory.V.Z.Win.WitA ι (r.toHomUnits.comp (resQ T.L)) := by
    letI : Algebra T.K T.L := (IntermediateField.inclusion hKL).toAlgebra
    haveI : IsScalarTower T.K T.L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsGalois T.K T.L := IsGalois.tower_top_of_isGalois ℚ T.K T.L
    have hsol' : IsSolvable (T.L ≃ₐ[T.K] T.L) :=
      @solvable_of_solvable_injective _ _ _ _ (hf := (AlgEquiv.restrictScalarsHom_injective ℚ)) hsol
        (f := (AlgEquiv.restrictScalarsHom ℚ : (T.L ≃ₐ[T.K] T.L) →* (T.L ≃ₐ[ℚ] T.L)))
    obtain ⟨Q, hQ⟩ := auPair r (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th) hmul D.cc
    have hpol : Af.Sol.Pol ι (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) :=
      ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, _, D.cc, Q, _root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good hU.pr D hG ι, auSign _, hG.isCC, fun s s' h => by
          have h' : Af.resG ℚ T.K Ω s' = D.cc * Af.resG ℚ T.K Ω s * D.cc⁻¹ := h
          rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h']
          exact hQ _⟩
    exact _root_.UpperTheory.V.Z.Win.Dn.automorphy_up_base_change (r := r.toHomUnits.comp (resQ T.K)) T.L hU.pr hsol' (by norm_num) hcK hiL hpol ⟨π, hreg, hatt⟩
      (((flagLaws ℚ Ω l 4 r.toHomUnits).2.2.2 T.K).2.1 ((flagLaws ℚ Ω l 4 r.toHomUnits).2.2.1 N _ hN hlev).2)
      (_root_.UpperTheory.GalN.V.autQN'_alt hU.pr.toClassicalTheorems (by norm_num) ⟨θ, hθ, hdual⟩ haut hlev.cont T.K T.degK hiK).2
  obtain ⟨ρ, hρ, hz⟩ := _root_.adjoint_vanishing_gsp4_rigid_point hU hAd hG hF hDp K X y ι r r₁ hconj hres hw (Units.continuous_val.comp hlev.cont) hmul hi hL hWit hf
  refine ⟨T.K, inferInstance, inferInstance, θ, T.degK, hm, fun R hR => ?_⟩
  refine adDown Ω l T.K T.L T.degK (fun σ hσ x => hσ ⟨x.1, hKL x.2⟩) K.s K.V 4 _ _ R hcK hR ρ (K.twc 0)
    (fun g t e => ?_) (fun g g' t e e' => ?_) hz
  · refine (congrArg Units.val (DFunLike.congr_fun hρ g)).trans ((K.rho_val _ _ _).trans ?_)
    exact congrArg (fun σ => (K.twc 0 g : PadicAlgCl l) • r σ) e
  · have a1 := congrArg (algebraMap c'.O (PadicAlgCl l)) (K.conj g g' e).1
    rw [map_mul, map_mul, map_mul, map_pow, map_one] at a1
    have a2 : (θ.comp (resQ T.K) t : PadicAlgCl l) = algebraMap c'.O (PadicAlgCl l) (inc h (D.th (resQ T.L g))) :=
      (congrArg (fun σ => (θ σ : PadicAlgCl l)) e'.symm).trans (hθv _)
    have a3 : (cycBar T.L Ω l g : PadicAlgCl l) = algebraMap c'.O (PadicAlgCl l) (chiO T.L Ω l c'.O g) := rfl
    have a4 : K.twc 0 g * K.twc 0 g' * θ.comp (resQ T.K) t * cycBar T.L Ω l g ^ 3 = 1 := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, K.twc_val, pow_zero, mul_one, Units.val_one]
      rw [a2, a3]
      exact a1
    rw [eq_inv_of_mul_eq_one_left a4, ← zpow_natCast, ← zpow_neg]
    rfl
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
section Alg
open Matrix
end Alg
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
end Gal
section Core
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
end Core
section Rg
open scoped Matrix TensorProduct
private theorem rg_twist {Γ k V : Type} [Group Γ] [CommRing k] [AddCommGroup V] [Module k V] (A : Representation k Γ V)
    (p : V →ₗ[k] V) (hp : ∀ x, p (p x) = p x) (hA : ∀ g x, p (A g x) = A g (p x)) (η : Γ →* kˣ) :
    ∃ ρ : Representation k Γ V, ∀ g x, ρ g x = A g (p x) + (η g : k) • A g (x - p x) := by
  refine ⟨{ toFun := fun g => A g ∘ₗ p + (η g : k) • (A g ∘ₗ (LinearMap.id - p))
            map_one' := ?_
            map_mul' := fun g h => ?_ }, fun g x => rfl⟩
  · ext x
    simp
  · ext x
    simp only [map_mul, Units.val_mul, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.id_apply, Module.End.mul_apply, map_add, map_smul, map_sub, hA, hp, sub_self, smul_zero, add_zero,
      mul_smul, smul_sub, smul_add, map_zero]
    module
private theorem rg_sign {K Ω : Type} [Field K] [NumberField K] [IsCMField K] (h : Module.finrank ℚ K = 2) [Field Ω]
    [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] (k : Type) [Field k] :
    ∃ η : G ℚ Ω →* kˣ, (∀ s : G K Ω, η (s.restrictScalars ℚ) = 1) ∧
      ∀ c : G ℚ Ω, (∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)) → η c = -1 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : K, IsCMField.complexConj K x ≠ x := by
    by_contra hc
    push Not at hc
    exact IsCMField.complexConj_ne_one K (AlgEquiv.ext hc)
  set δ : K := x - IsCMField.complexConj K x with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 hx.symm
  have hδc : IsCMField.complexConj K δ = -δ := by simp [hδ]
  have hsq : δ * δ ∈ maximalRealSubfield K := (IsCMField.complexConj_eq_self_iff K _).1 (by rw [map_mul, hδc]; ring)
  obtain ⟨q, hq⟩ := Af.surjective_algebraMap_real K h ⟨_, hsq⟩
  have hq' : algebraMap ℚ K q = δ * δ := by
    have := congrArg (fun y : maximalRealSubfield K => (y : K)) hq
    simpa using this
  set d : Ω := algebraMap K Ω δ with hd
  have hd0 : d ≠ 0 := by simpa [hd] using hδ0
  have hdd : d * d = algebraMap ℚ Ω q := by rw [IsScalarTower.algebraMap_apply ℚ K Ω, hq', map_mul]
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hne : -d ≠ d := fun e => hd0 (by linear_combination (-1 / 2 : Ω) * e)
  have hpm : ∀ g : G ℚ Ω, g d = d ∨ g d = -d := fun g => by
    have : g d * g d = d * d := by rw [← map_mul, hdd, AlgEquiv.commutes]
    exact mul_self_eq_mul_self_iff.1 this
  refine ⟨{ toFun := fun g => if g d = d then 1 else -1
            map_one' := by simp
            map_mul' := fun g g' => ?_ }, fun s => ?_, fun c ⟨j, hj⟩ => ?_⟩
  · rcases hpm g with h1 | h1 <;> rcases hpm g' with h2 | h2 <;> simp [AlgEquiv.mul_apply, h1, h2, hne]
  · have : (s.restrictScalars ℚ) d = d := s.commutes δ
    simp [this]
  · have : c d = -d := by
      apply j.injective
      rw [hj, hd, ← map_neg (algebraMap K Ω), ← hδc]
      exact (IsCMField.complexEmbedding_complexConj K (j.comp (algebraMap K Ω)) δ).symm
    simp [this, hne]
section BK
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
  {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
private theorem rg_bk {ρ ρ' : Representation C (G F Ω) V} (f : V →ₗ[C] V) (hf : ∀ g x, f (ρ g x) = ρ' g (f x))
    {z : G F Ω → V} (hz : ∀ g, f (z g) = z g) (h1 : z ∈ Z1 ρ) (h2 : Af.IsBK l ρ z) : z ∈ Z1 ρ' ∧ Af.IsBK l ρ' z := by
  have hc : ∀ g h, z (g * h) = z g + ρ' g (z h) := fun g h => by
    rw [← hz (g * h), h1.2, map_add (f := _), hf, hz, hz]
  refine ⟨⟨h1.1, hc⟩, fun w hw => ?_, fun τ => ?_⟩
  · obtain ⟨A, hA, x, hx⟩ := h2.away w hw
    exact ⟨A, hA, f x, fun s hs => by rw [← hz, hx s hs, map_sub, hf]⟩
  · obtain ⟨j, hj, ⟨hc1, -⟩, x, hx⟩ := h2.above τ
    refine ⟨j, hj, ⟨hc1, fun g h => hc g.1.1 h.1.1⟩,
      LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) x, fun g => ?_⟩
    have key : ∀ y : V ⊗[ℚ_[l]] Loc.Bcr l, LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l])
        (Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype) (ρ.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g y) =
        Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype) (ρ'.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g
          (LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Loc.actC, hf]
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
    simp [hz]
end BK
private def rgJ (k : Type) [CommRing k] : GL (Fin 4) k where
  val := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
  inv := !![0, 0, 0, -1; 0, 0, -1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
private theorem rgJ_adj {k : Type} [CommRing k] (X : M4 k) : Xᵀ * (rgJ k : M4 k) = (rgJ k : M4 k) * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rgJ, Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev]
private noncomputable def rgP (k : Type) [Field k] : M4 k →ₗ[k] M4 k where
  toFun X := (2 : k)⁻¹ • (X - adj X)
  map_add' X Y := by rw [(grp k).2.2.1, ← smul_add]; congr 1; abel
  map_smul' a X := by rw [(grp k).2.2.2.1, ← smul_sub, smul_comm]; rfl
private theorem rgP_apply {k : Type} [Field k] (X : M4 k) : rgP k X = (2 : k)⁻¹ • (X - adj X) := rfl
private theorem rgP_mem {k : Type} [Field k] (X : M4 k) : rgP k X ∈ sp4 k := by
  have h1 : adj (-adj X) = -X := by
    rw [← neg_one_smul k, (grp k).2.2.2.1, (grp k).2.1, neg_one_smul]
  show adj _ = -_
  rw [rgP_apply, (grp k).2.2.2.1, sub_eq_add_neg, (grp k).2.2.1, h1, ← smul_neg]
  congr 1
  abel
private theorem rgP_of_mem {k : Type} [Field k] [CharZero k] {X : M4 k} (h : X ∈ sp4 k) : rgP k X = X := by
  have h' : adj X = -X := h
  rw [rgP_apply, h', sub_neg_eq_add, ← two_smul k, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
private theorem rg_adjConj {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (θ : Γ →* kˣ) (hm : ∀ g, IsGSp (θ g : k) (r g))
    (g : Γ) (X : M4 k) : adj (r g * X * r g⁻¹) = r g * adj X * r g⁻¹ := by
  have h1 : adj (r g) = (θ g : k) • r g⁻¹ := (grp k).2.2.2.2.2.2.1 _ _ _ (hm g) (by rw [← map_mul]; simp)
  have h2 : adj (r g⁻¹) = (θ g⁻¹ : k) • r g := (grp k).2.2.2.2.2.2.1 _ _ _ (hm g⁻¹) (by rw [← map_mul]; simp)
  rw [(grp k).1, (grp k).1, h1, h2]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc, ← Units.val_mul, ← map_mul]
  simp
private theorem rg_ad {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (g : Γ) (X : M4 k) :
    Loc.adGL r.toHomUnits g X = r g * X * r g⁻¹ := rfl
private theorem rg_pair {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (θ : Γ →* kˣ) (hm : ∀ g, IsGSp (θ g : k) (r g))
    (c s s' : Γ) (hs : s' = c * s * c⁻¹) :
    (r.toHomUnits s : M4 k)ᵀ * (rgJ k * (r.toHomUnits c)⁻¹ : GL (Fin 4) k) * (r.toHomUnits s' : M4 k) =
      (θ s : k) • ((rgJ k * (r.toHomUnits c)⁻¹ : GL (Fin 4) k) : M4 k) := by
  show (r s)ᵀ * ((rgJ k : M4 k) * r c⁻¹) * r s' = (θ s : k) • ((rgJ k : M4 k) * r c⁻¹)
  have h := hm s
  unfold IsGSp at h
  have e : r c⁻¹ * r s' = r s * r c⁻¹ := by
    rw [← map_mul, ← map_mul, hs]
    congr 1
    group
  rw [mul_assoc, mul_assoc, e, ← mul_assoc, rgJ_adj, mul_assoc, ← mul_assoc (adj _), h, smul_mul_assoc, one_mul, mul_smul_comm]
private theorem rg_alg {Γ k : Type} [Group Γ] [Field k] [CharZero k] (r : Γ →* M4 k) (θ : Γ →* kˣ)
    (hm : ∀ g, IsGSp (θ g : k) (r g)) (η : Γ →* kˣ) :
    ∃ ρ : Representation k Γ (M4 k),
      (∀ g X, η g = 1 → ρ g X = (r.toHomUnits g : M4 k) * X * ((r.toHomUnits g)⁻¹ : GL (Fin 4) k)) ∧
      (∀ g X, η g = -1 → ρ g X = -((((rgJ k * (r.toHomUnits g)⁻¹)⁻¹ : GL (Fin 4) k) : M4 k) * Xᵀ *
        (rgJ k * (r.toHomUnits g)⁻¹ : GL (Fin 4) k))) ∧
      (∀ g X, rgP k (Loc.adGL r.toHomUnits g X) = ρ g (rgP k X)) ∧
      ∀ g X Z, Z * r g⁻¹ ∈ sp4 k → Z * r g⁻¹ = ρ g X - X → Z = -rgP k X * r g - r g * -rgP k X := by
  have hpp : ∀ X, rgP k (rgP k X) = rgP k X := fun X => rgP_of_mem (rgP_mem X)
  have hpA : ∀ g X, rgP k (Loc.adGL r.toHomUnits g X) = Loc.adGL r.toHomUnits g (rgP k X) := fun g X => by
    rw [rgP_apply, rgP_apply, map_smul, map_sub, rg_ad, rg_ad, rg_adjConj r θ hm]
  obtain ⟨ρ, hρ⟩ := rg_twist (Loc.adGL r.toHomUnits) (rgP k) hpp hpA η
  refine ⟨ρ, fun g X h => ?_, fun g X h => ?_, fun g X => ?_, fun g X Z h1 h2 => ?_⟩
  · rw [hρ, h, Units.val_one, one_smul, ← map_add (f := _), add_sub_cancel]
    rfl
  · rw [mul_inv_rev, inv_inv]
    show _ = -((r g * ((rgJ k)⁻¹ : GL _ _)) * Xᵀ * ((rgJ k : M4 k) * r g⁻¹))
    have e : rgP k X - (X - rgP k X) = -adj X := by
      rw [rgP_apply]
      match_scalars <;> field_simp <;> ring
    rw [hρ, h, Units.val_neg, Units.val_one, neg_one_smul, ← sub_eq_add_neg, ← map_sub, e, map_neg, rg_ad,
      mul_assoc _ Xᵀ, ← mul_assoc Xᵀ, rgJ_adj]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  · rw [hρ, hpp, sub_self, map_zero, smul_zero, add_zero, hpA]
  · have e1 : Z * r g⁻¹ = r g * rgP k X * r g⁻¹ - rgP k X := by
      rw [← rgP_of_mem h1, h2, map_sub, hρ, map_add (f := _), map_smul, hpA, hpA, map_sub, hpp, sub_self, map_zero, smul_zero,
        add_zero, rg_ad]
    have := congrArg (· * r g) e1
    simp only [sub_mul, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at this
    rw [this]
    noncomm_ring
end Rg
theorem UpperTheory.V.Th.rigSp4_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → _root_.UpperTheory.V.Th.RigiditySymplecticFour := by
  intro hU hAd Ω _ _ _ l _ c D hD N hN h1 h2 h3 ι r hr hirr haut r' hr' hfst
  have hG : D.Good := hD.elim (·.1) (·.1)
  obtain ⟨K, _, _, θ, hK, hm, hAd⟩ := _root_.UpperTheory.V.Z.Win.Dn.exists_cm_field_twist_h1 hU hAd D hD N hN h1 h2 h3 ι r hr hirr haut
  obtain ⟨hz, hbk, hsp⟩ := tanBK D hG hU.coh.loc r hr r' hr' hfst
  obtain ⟨η, hη1, hη2⟩ := rg_sign (Ω := Ω) hK (PadicAlgCl l)
  obtain ⟨ρ, ha, hb, hf, hd⟩ := rg_alg r θ hm η
  have hcc : ∃ j : Ω →+* ℂ, ∀ x, j (D.cc x) = starRingEnd ℂ (j x) := hG.isCC
  have hv := hAd ρ ⟨D.cc, rgJ _ * (r.toHomUnits D.cc)⁻¹, hcc, fun s s' hs => rg_pair r θ hm D.cc _ _ hs,
    fun s X => ha _ X (hη1 s), fun X => hb _ X (hη2 _ hcc)⟩
  obtain ⟨hz', hbk'⟩ := rg_bk (rgP _) hf (fun g => rgP_of_mem (hsp g)) hz hbk
  obtain ⟨X, hX⟩ := (mem_coboundaries1 _ _).1 (hv _ hz' hbk')
  exact ⟨-rgP (PadicAlgCl l) X, (sp4 (PadicAlgCl l)).neg_mem (rgP_mem (k := PadicAlgCl l) X), fun g i j => congrFun (congrFun (hd g X _ (hsp g) (hX g)) i) j⟩
end
