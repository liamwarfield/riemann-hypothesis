module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairOverAlgebraicIntegers
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.AlgCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.OfForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaCyc

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.UniversalMapsPointOfPolarizedFlaggedRep
set_option linter.overlappingInstances false

section SlopeTestRemainingChoices

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.W UpperTheory.V.CA UpperTheory.V.AlgebraTools.Det

namespace UpperTheory.V.Pr

private theorem tr_single {n : ℕ} {A G K : Type} [CommRing A] [Group G] [CommRing K] (hn : 0 < n) (D : GDet n A G)
    (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ) (g : G) :
    f (D.tr (MonoidAlgebra.single g 1)) = (ρ g).trace := by
  have h1 := ((d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 1
  rw [h, MonoidAlgebra.mapRingHom_single, map_one] at h1
  have hs (B : Type) [CommRing B] [Algebra K B] (g : G) (r : B) :
      GDet.repAlg ρ B (MonoidAlgebra.single g r) = r • (ρ g).map (algebraMap K B) := by
    unfold GDet.repAlg
    rw [MonoidAlgebra.lift_single]
    rfl
  have hm (B : Type) [CommRing B] [Algebra K B] (y : MonoidAlgebra K G) :
      GDet.repAlg ρ B (MonoidAlgebra.mapRingHom G (algebraMap K B) y) = (GDet.repAlg ρ K y).map (algebraMap K B) := by
    induction y using MonoidAlgebra.induction_on with
    | of g => simp [MonoidAlgebra.of_apply, hs]
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
      ext i j; simp
    | smul r x hx =>
      have hr : r • x = MonoidAlgebra.single 1 r * x := by rw [Algebra.smul_def]; rfl
      have hmap : MonoidAlgebra.mapRingHom G (algebraMap K B) (MonoidAlgebra.single 1 r) = MonoidAlgebra.single 1 (algebraMap K B r) := by
        ext g; simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]
      rw [hr, map_mul, map_mul, map_mul, hx, Matrix.map_mul, hmap, hs, hs, map_one]
      congr 1
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hc : (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
    have hc' (y : MonoidAlgebra K G) : (GDet.ofRep ρ).chi y = (GDet.repAlg ρ K y).charpoly := by
      unfold GDet.chi
      change (GDet.repAlg ρ (Polynomial K) _).det = _
      rw [← Polynomial.algebraMap_eq, map_sub, hs, hm, map_one]
      rw [Matrix.charpoly]
      congr 1
      ext i j
      by_cases h : i = j <;> simp [Matrix.charmatrix_apply, Matrix.one_apply, h]
    rw [hc', hs]; simp
  unfold GDet.tr GDet.lam at *
  rw [← h1, hc, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
  ring

private theorem prod_smul {K : Type} [CommRing K] {M : Type} [Ring M] [Algebra K M] :
    ∀ {m : ℕ} (c : Fin m → K) (x : Fin m → M), (List.ofFn fun i => c i • x i).prod = (∏ i, c i) • (List.ofFn x).prod
  | 0, _, _ => by simp
  | m + 1, c, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Fin.prod_univ_succ,
      prod_smul (fun i => c i.succ) (fun i => x i.succ), smul_mul_smul_comm]

section Cont

variable {Γ Γ' R R' : Type} [TopologicalSpace Γ] [TopologicalSpace Γ'] [CommRing R] [CommRing R']

private theorem ac_mul {I : Ideal R} {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) :
    AdicCont I fun x => f x * g x := fun N => by
  simp only [map_mul]
  exact (hf N).mul (hg N)

private theorem ac_comp {I : Ideal R} {f : Γ → R} (hf : AdicCont I f) {u : Γ' → Γ} (hu : Continuous u) :
    AdicCont I fun x => f (u x) := fun N => (hf N).comp_continuous hu

private theorem ac_map [IsLocalRing R] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ] {f : Γ → R}
    (hf : AdicCont (maximalIdeal R) f) : AdicCont (maximalIdeal R') fun x => φ (f x) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap φ :=
    le_trans (Ideal.pow_right_mono (fun y hy => map_nonunit φ y hy) N) (Ideal.le_comap_pow _ N)
  exact (hf N).comp (Ideal.quotientMap _ φ hle)

private theorem ac_desc {I : Ideal R} {f : Γ → R} {u : Γ' → Γ} (hu : Topology.IsQuotientMap u)
    (hf : AdicCont I fun x => f (u x)) : AdicCont I f := fun N s =>
  hu.isOpen_preimage.1 (hf N s)

end Cont

section Tw

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Frame l (ResidueField O)} {n : ℕ} {G : GFrame l} {r : Resid G O n} (L : TwLink F r)

private theorem κ_map {C K : Type} [CommRing C] [Algebra O C] [CommRing K] [Algebra O K] (j : C →ₐ[O] K) (g : G.G₀) :
    j ((L.κA C g : Cˣ) : C) = (L.κA K g : Kˣ) := j.commutes _

private theorem κ_map_inv {C K : Type} [CommRing C] [Algebra O C] [CommRing K] [Algebra O K] (j : C →ₐ[O] K)
    (g : G.G₀) : j (((L.κA C g)⁻¹ : Cˣ) : C) = ((L.κA K g)⁻¹ : Kˣ) := by
  rw [← map_inv, ← map_inv, κ_map]

variable {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (p : Pair r C)

private noncomputable def tt (g : G.G₀) : C := (((L.κA C g)⁻¹ : Cˣ) : C) * p.D.tr (MonoidAlgebra.single g 1)

private theorem κinv_cont : AdicCont (maximalIdeal C) fun g : G.G₀ => (((L.κA C g)⁻¹ : Cˣ) : C) := by
  have := ac_map (algebraMap O C) (ac_comp L.κ_cont continuous_inv)
  simp only [← map_inv]
  exact this

private theorem tt_cont : AdicCont (maximalIdeal C) (tt L p) := ac_mul (κinv_cont L) (p.cont 1)

private theorem tt_map (hn : 0 < n) {K : Type} [CommRing K] [Algebra O K] (j : C →ₐ[O] K)
    (r0 : G.G₀ →* Matrix (Fin n) (Fin n) K) (h : p.D.map (j : C →+* K) = GDet.ofRep r0) (g : G.G₀) :
    j (tt L p g) = (((L.κA K g)⁻¹ : Kˣ) : K) * (r0 g).trace := by
  rw [tt, map_mul, κ_map_inv, ← tr_single hn p.D _ r0 h]
  rfl

private theorem tt_res (hn : 0 < n) (g : G.G₀) :
    res O C (tt L p g) = ∑ i, ((F.Ψ (L.π g) ^ w n i : (ResidueField O)ˣ) : ResidueField O) := by
  rw [tt_map L p hn (res O C) _ p.red]
  show _ * (diagonal _).trace = _
  rw [trace_diagonal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [L.chib, ← Units.val_mul]
  congr 1
  show (L.κA _ g)⁻¹ * (_ * L.κA _ g) = _
  rw [mul_comm _ (L.κA _ g), inv_mul_cancel_left]

private theorem π_quot : Topology.IsQuotientMap L.π := by
  haveI : CompactSpace G.G₀ := isCompact_iff_compactSpace.1 (G.η.ker.isClosed_of_isOpen G.η_open).isCompact
  exact L.π_cont.isClosedMap.isQuotientMap L.π_cont L.π_surj

private theorem chi_ex : ∃ χ : ∀ v, Fin n → F.Gv v →* Cˣ, IsPsi O F n (fun v i g => (χ v i g : C)) ∧
    ∀ v i g, χ (L.e v) i (L.lam v g) * L.κA C (G.φ v g) = p.ψ v i g := by
  have key : ∀ v : F.V, ∃ χ : Fin n → F.Gv v →* Cˣ, (∀ i, AdicCont (maximalIdeal C) (fun g => (χ i g : C)) ∧
      ∀ g, res O C (χ i g) = ((F.Ψ (F.loc v g) ^ w n i : (ResidueField O)ˣ) : ResidueField O)) ∧
      ∀ u (h : L.e u = v) i g, χ i (h ▸ L.lam u g) * L.κA C (G.φ u g) = p.ψ u i g := fun v => by
    obtain ⟨u, rfl⟩ := L.e.surjective v
    refine ⟨fun i => (p.ψ u i * ((L.κA C).comp (G.φ u))⁻¹).comp (L.lam u).symm.toMulEquiv.toMonoidHom,
      fun i => ⟨?_, fun g => ?_⟩, fun u' h i g => ?_⟩
    · exact ac_comp (ac_mul (p.psi u i).cont (ac_comp (κinv_cont L) (G.φ_cont u))) (L.lam u).symm.continuous
    · obtain ⟨g, rfl⟩ := (L.lam u).surjective g
      have h1 : (L.lam u).symm.toMulEquiv.toMonoidHom (L.lam u g) = g := (L.lam u).symm_apply_apply g
      rw [MonoidHom.comp_apply, h1]
      show res O C ((p.ψ u i g : Cˣ) * (((L.κA C (G.φ u g))⁻¹ : Cˣ) : C)) = _
      rw [map_mul, κ_map_inv, (p.psi u i).red, L.psib, L.chib, ← Units.val_mul, ← L.lam_loc]
      congr 1
      exact mul_inv_cancel_right _ _
    · obtain rfl := L.e.injective h
      have h1 : (L.lam u').symm.toMulEquiv.toMonoidHom (L.lam u' g) = g := (L.lam u').symm_apply_apply g
      rw [MonoidHom.comp_apply, h1]
      exact inv_mul_cancel_right _ _
  choose χ h1 h2 using key
  exact ⟨χ, h1, fun v i g => h2 _ v rfl i g⟩

end Tw

private theorem irr_conj {G K : Type} [Group G] [Field K] {n : ℕ} (r : G →* GL (Fin n) K)
    (a : G → Matrix (Fin n) (Fin n) K) (h : GL (Fin n) K) (H : ∀ g, a g = h * mat r g * h⁻¹) (hr : Af.IsIrr r) :
    MatIrr ⊤ a := by
  intro W hW
  have e : ∀ g, (h : Matrix (Fin n) (Fin n) K) * (r g : Matrix (Fin n) (Fin n) K) = a g * h := fun g => by
    rw [H, Units.inv_mul_cancel_right]; rfl
  rcases hr.2.2 (W.comap (Matrix.toLin' (h : Matrix (Fin n) (Fin n) K))) le_top (fun g v hv => by
    rw [Submodule.mem_comap, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
    exact hW g (Subgroup.mem_top g) _ hv) with h0 | h0
  · refine Or.inl (eq_bot_iff.2 fun v hv => ?_)
    have h1 : ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈
        W.comap (Matrix.toLin' (h : Matrix (Fin n) (Fin n) K)) := by
      rw [Submodule.mem_comap, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact hv
    rw [h0, Submodule.mem_bot] at h1
    have h2 := congrArg ((h : Matrix (Fin n) (Fin n) K) *ᵥ ·) h1
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    exact h2
  · refine Or.inr (eq_top_iff.2 fun v _ => ?_)
    have h1 : ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈
        W.comap (Matrix.toLin' (h : Matrix (Fin n) (Fin n) K)) := h0 ▸ Submodule.mem_top
    rwa [Submodule.mem_comap, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h1

private theorem main {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsCoef l O] [Algebra ℤ_[l] O] {F : Frame l (ResidueField O)} {n : ℕ} (T : Setup F n)
    {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (p : Pair T.r C) {K : Type} [Field K]
    [IsAlgClosed K] [Algebra O K] (j : C →ₐ[O] K) (hj : Function.Injective j)
    (r : F.G0 →* GL (Fin n) K) (Q : GL (Fin n) K) (hQ : (Q : Matrix (Fin n) (Fin n) K)ᵀ = Q)
    (hform : ∀ g, (r g : Matrix (Fin n) (Fin n) K)ᵀ * (Q : Matrix (Fin n) (Fin n) K) *
      (r (F.conj g) : Matrix (Fin n) (Fin n) K) = Q)
    (h0 : p.D.map (j : C →+* K) = GDet.ofRep (mat (Af.tw (r.comp T.K.π) (T.K.κA K))))
    (hfl : ∀ v, HasFlag ((Af.tw (r.comp T.K.π) (T.K.κA K)).comp (T.G.φ v)) fun i => pushCh (j : C →+* K) (p.ψ v i))
    (hirr : Af.IsIrr r) :
    ∃ ρ' : NRep F n K, MatIrr ⊤ ρ'.r ∧ p.D.map (j : C →+* K) = GDet.ofRep (T.K.tw ρ') := by
  have hn : 0 < n := by have := T.n23; omega
  letI : Algebra C K := (j : C →+* K).toAlgebra
  have hv : ∀ g, mat (Af.tw (r.comp T.K.π) (T.K.κA K)) g = ((T.K.κA K g : Kˣ) : K) • mat r (T.K.π g) :=
    fun g => Af.tw_val _ _ g
  obtain ⟨χ, hχ, hψ⟩ := chi_ex T.K p
  have hb : ∀ g, j (tt T.K p g) = (mat r (T.K.π g)).trace := fun g => by
    rw [tt_map T.K p hn j _ h0, hv, trace_smul, smul_eq_mul, Units.inv_mul_cancel_left]
  let t : F.G0 → C := fun x => tt T.K p (Function.surjInv T.K.π_surj x)
  have ht0 : ∀ x, j (t x) = (mat r x).trace := fun x => by
    have := hb (Function.surjInv T.K.π_surj x)
    rwa [Function.surjInv_eq T.K.π_surj] at this
  have ht : ∀ g, t (T.K.π g) = tt T.K p g := fun g => hj (by rw [ht0, hb])
  have hψ' : ∀ v i g, j (p.ψ v i g : Cˣ) =
      (T.K.κA K (T.G.φ v g) : Kˣ) * j (χ (T.K.e v) i (T.K.lam v g) : Cˣ) := fun v i g => by
    rw [← hψ, Units.val_mul, map_mul, mul_comm, ← κ_map T.K j]
  refine Exists.elim (of_form T.ok T.n23 C K hj (mat r) Q t χ Q.isUnit hQ hform ⟨?_, fun x => ?_⟩ ht0 hχ
    (fun v g => ?_)) fun ρ H => ?_
  · refine ac_desc (π_quot T.K) ?_
    simp only [ht]
    exact tt_cont T.K p
  · obtain ⟨g, rfl⟩ := T.K.π_surj x
    rw [ht, tt_res T.K p hn]
  · obtain ⟨u, rfl⟩ := T.K.e.surjective v
    obtain ⟨g, rfl⟩ : ∃ g' : Fin n → T.G.Gv u, g = fun i => T.K.lam u (g' i) :=
      ⟨fun i => (T.K.lam u).symm (g i), funext fun i => ((T.K.lam u).apply_symm_apply _).symm⟩
    have h1 := (flagRel _ _ (hfl u)).2 g
    have h2 := prod_smul (fun i => ((T.K.κA K (T.G.φ u (g i)) : Kˣ) : K))
      (fun i => mat r (F.loc0 _ (T.K.lam u (g i))) -
        j (χ (T.K.e u) i (T.K.lam u (g i)) : Cˣ) • (1 : Matrix (Fin n) (Fin n) K))
    have h3 := h2.symm.trans (Eq.trans (congrArg (fun f => (List.ofFn f).prod) (funext fun i => by
      rw [smul_sub, T.K.lam_loc, ← hv, smul_smul, ← hψ']
      rfl)) h1)
    exact (IsUnit.smul_eq_zero (IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _))).1 h3
  · obtain ⟨h, H1, -, -⟩ := H
    have heq : GDet.ofRep (mat (Af.tw (r.comp T.K.π) (T.K.κA K))) = GDet.ofRep (T.K.tw ρ) := by
      let ρ₁ := mat (Af.tw (r.comp T.K.π) (T.K.κA K))
      let ρ₂ := T.K.tw ρ
      have hp : ∀ g, (h : Matrix (Fin n) (Fin n) K) * ρ₁ g = ρ₂ g * h := fun g => by
        show _ = (((T.K.κA K g : Kˣ) : K) • ρ.r (T.K.π g)) * _
        rw [hv, H1, mul_smul_comm, smul_mul_assoc, Units.inv_mul_cancel_right]
      refine GDet.ext fun B _ _ x => ?_
      have hs (σ : T.G.G₀ →* Matrix (Fin n) (Fin n) K) (g : T.G.G₀) (r : B) :
          GDet.repAlg σ B (MonoidAlgebra.single g r) = r • (σ g).map (algebraMap K B) := by
        unfold GDet.repAlg
        rw [MonoidAlgebra.lift_single]
        rfl
      have key : ∀ y : MonoidAlgebra B T.G.G₀,
          (h : Matrix (Fin n) (Fin n) K).map (algebraMap K B) * GDet.repAlg ρ₁ B y =
            GDet.repAlg ρ₂ B y * (h : Matrix (Fin n) (Fin n) K).map (algebraMap K B) := by
        intro y
        induction y using MonoidAlgebra.induction_on with
        | of g =>
          rw [MonoidAlgebra.of_apply, hs, hs, one_smul, one_smul, ← Matrix.map_mul, ← Matrix.map_mul, hp]
        | add y z hy hz =>
          rw [map_add (f := _), map_add (f := _), Matrix.mul_add, Matrix.add_mul, hy, hz]
        | smul r y hy =>
          rw [map_smul, map_smul, Matrix.mul_smul, Matrix.smul_mul, hy]
      have hd := congrArg Matrix.det (key x)
      rw [Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det (GDet.repAlg ρ₂ B x))] at hd
      have hu : IsUnit (Matrix.det ((h : Matrix (Fin n) (Fin n) K).map (algebraMap K B))) := by
        rw [show ((h : Matrix (Fin n) (Fin n) K).map (algebraMap K B)).det = algebraMap K B (h : Matrix (Fin n) (Fin n) K).det from (RingHom.map_det _ _).symm]
        exact (Matrix.isUnits_det_units h).map _
      change (GDet.repAlg ρ₁ B x).det = (GDet.repAlg ρ₂ B x).det
      exact hu.mul_left_cancel hd
    exact ⟨ρ, irr_conj r _ h H1 hirr, h0.trans heq⟩

end UpperTheory.V.Pr

end SlopeTestRemainingChoices

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
open scoped Matrix

theorem UpperTheory.universalMaps_point_of_polarized_flagged_rep :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fr.IsCoef l O] [Algebra ℤ_[l] O] {F : Fr.Frame l (ResidueField O)} {n : ℕ} (T : Setup F n) (K' : Type) [Field K'] [IsAlgClosed K'] [Algebra O K'] (x : T.B.B →ₐ[O] K') (r : F.G0 →* GL (Fin n) K') (ρ : T.G.G₀ →* GL (Fin n) K') (Q : GL (Fin n) K') (ψ : ∀ v, Fin n → T.G.Gv v →* K'ˣ), (Q : Matrix (Fin n) (Fin n) K')ᵀ = Q → (∀ g, (r g : Matrix (Fin n) (Fin n) K')ᵀ * (Q : Matrix (Fin n) (Fin n) K') * (r (F.conj g) : Matrix (Fin n) (Fin n) K') = Q) → ρ = tw (r.comp T.K.π) (T.K.κA K') → T.B.u.Maps (x : T.B.B →+* K') (W.GDet.ofRep (W.mat ρ)) ψ → (∀ v, W.HasFlag (ρ.comp (T.G.φ v)) (ψ v)) → IsIrr r → ∃ ρ' : Fr.NRep F n K', MatIrr ⊤ ρ'.r ∧ T.B.u.D.map (x : T.B.B →+* K') = W.GDet.ofRep (T.K.tw ρ') := by
  intro l _ O _ _ _ _ _ F n T K' _ _ _ x r ρ Q ψ hQ hform hρ hx hfl hirr
  subst hρ
  haveI : Alg.IsCO O x.range := Alg.co_quot O _ _ x.rangeRestrict x.rangeRestrict_surjective
  obtain ⟨p, hp⟩ := W.exists_determinantPair_map_of_algHom l T.G O n T.r T.B.B x.range x.rangeRestrict T.B.u
  have hD : p.D.map (x.range.val : x.range →+* K') = T.B.u.D.map (x : T.B.B →+* K') := by
    rw [← hp.1, (CA.d_gmap _).2.1]; rfl
  rw [← hD]
  refine main T p x.range.val Subtype.val_injective r Q hQ hform (hD.trans hx.1) (fun v => ?_) hirr
  have : (fun i => W.pushCh (x.range.val : x.range →+* K') (p.ψ v i)) = ψ v := funext fun i => by
    rw [← hp.2 v i, ← hx.2 v i]; rfl
  rw [this]
  exact hfl v
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.DiagonalCharactersRegularAlgebraicOfInertiaWeigh
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
open scoped Matrix

private theorem cyc_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {v : W.Plc F} {A : ValuationSubring Ω} (hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)
    (hA : IsPlaceOver A v) {n : ℤ} (hn : n ≠ 0) : ∃ g ∈ Ine (F := F) A, cycBar F Ω l g ^ n ≠ 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans ℚ F Ω⟩
  have hval : A.valuation (l : Ω) < 1 := by
    have h1 := (hA (l : 𝓞 F)).2 hl
    simpa only [map_natCast] using h1
  obtain ⟨u, hu⟩ := GlobalTheory.CycDec.exists_unit_infinite_order l
  obtain ⟨σ, hσI, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hval u
  let f : ℕ → (F →ₐ[ℚ] Ω) := fun k =>
    ((σ ^ k : Ω ≃ₐ[ℚ] Ω) : Ω →ₐ[ℚ] Ω).comp (IsScalarTower.toAlgHom ℚ F Ω)
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : ∀ a b : ℕ, a < b → f a = f b →
      ∃ k : ℕ, 0 < k ∧ ∀ x : F, (σ ^ k) (algebraMap F Ω x) = algebraMap F Ω x := by
    intro a b hlt he
    refine ⟨b - a, by omega, fun x => ?_⟩
    have hx : (σ ^ a) (algebraMap F Ω x) = (σ ^ b) (algebraMap F Ω x) :=
      congrArg (fun φ : F →ₐ[ℚ] Ω => φ x) he
    have hb : σ ^ b = σ ^ a * σ ^ (b - a) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hb, AlgEquiv.mul_apply] at hx
    exact ((σ ^ a).injective hx).symm
  obtain ⟨k, hk0, hk⟩ : ∃ k : ℕ, 0 < k ∧ ∀ x : F, (σ ^ k) (algebraMap F Ω x) = algebraMap F Ω x := by
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · exact key a b h hfab
    · exact key b a h hfab.symm
  let g : G F Ω := { (σ ^ k : Ω ≃ₐ[ℚ] Ω) with commutes' := hk }
  have hgI : g ∈ Ine (F := F) A := pow_mem hσI k
  refine ⟨g, hgI, fun heq => ?_⟩
  have hr : MulSemiringAction.toRingAut (G F Ω) Ω g =
      MulSemiringAction.toRingAut (G ℚ Ω) Ω (σ ^ k) := RingEquiv.ext fun x => rfl
  have hz : cycZ F Ω l g = u ^ k := by
    show cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G F Ω) Ω g) = u ^ k
    rw [hr, ← hσu, ← map_pow]
    rfl
  have hinj : Function.Injective
      (Units.map (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom : ℤ_[l] →+* Qbar l) : ℤ_[l] →* Qbar l)) :=
    Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)
  have h1 : (u ^ k) ^ n = 1 := by
    apply hinj
    rw [map_zpow, map_one]
    have : cycBar F Ω l g = Units.map (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom : ℤ_[l] →+* Qbar l) : ℤ_[l] →* Qbar l) (cycZ F Ω l g) := rfl
    rw [← hz, ← this]
    exact heq
  rw [← zpow_natCast, ← zpow_mul] at h1
  exact hu _ (mul_ne_zero (by exact_mod_cast hk0.ne') hn) h1

private theorem w_anti (n : ℕ) : StrictAnti (Fr.w n) := by
  intro i j hij
  have : (i : ℕ) < j := hij
  unfold Fr.w
  split_ifs <;> omega

theorem UpperTheory.diagonal_characters_regular_algebraic_of_inertia_weights :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : W.Plc L} (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∀ (ka : G L Ω →* (Qbar l)ˣ), Sd.IsAlgChar ι ka → ∀ (n m : ℕ), 2 ≤ m → ∀ κ : Fin n → ↥(Dec (F := L) A) →* (Qbar l)ˣ, (∀ i (s : ↥(Dec (F := L) A)), (s : G L Ω) ∈ Ine (F := L) A → κ i s = cycBar L Ω l s ^ ((m : ℤ) * Fr.w n i)) → (∃ wt : Fin n → W.Emb l w → ℤ, (∀ τ, StrictMono fun j => wt j τ) ∧ ∀ j, W.IsLocAlg h (κ j * ka.comp (Dec (F := L) A).subtype) (wt j)) ∧ ∀ i j, κ i * ka.comp (Dec (F := L) A).subtype ≠ κ j * ka.comp (Dec (F := L) A).subtype * (cycBar L Ω l).comp (Dec (F := L) A).subtype := by
  intro hGAR L Ω _ _ _ _ _ l _ ι A w h hl ka hka n m hm κ hκ
  let cyc : ↥(Dec (F := L) A) →* (Qbar l)ˣ := (cycBar L Ω l).comp (Dec (F := L) A).subtype
  let kaD : ↥(Dec (F := L) A) →* (Qbar l)ˣ := ka.comp (Dec (F := L) A).subtype
  obtain ⟨_, art, χ, a, hart, _, hlad⟩ := hka
  let wk : W.Emb l w → ℤ := fun τ =>
    -a ((ι.toRingHom.comp ↑τ).comp (algebraMap L (IsDedekindDomain.HeightOneSpectrum.adicCompletion L w)))
  have hone : IsOpen (((1 : ↥(Ine (F := L) A) →* (Qbar l)ˣ).ker : Set ↥(Ine (F := L) A))) := by
    rw [MonoidHom.ker_one, Subgroup.coe_top]
    exact isOpen_univ
  have hkaW : W.IsLocAlg h kaD wk := by
    by_cases hex : ∃ a, GlobalTheory.LocLanglands.IsLocalArtin h a
    · exact Loc.laHecke h art hart ι χ a ka hlad hex
    · exact ⟨1, hone, fun a' ha' => absurd ⟨a', ha'⟩ hex⟩
  obtain ⟨phk, hphk⟩ := hkaW
  have hc := Loc.laCyc hGAR h hl
  obtain ⟨hmul, hpow, hzero⟩ := Loc.laMul (l := l) h
  have hm0 : (0 : ℤ) < m := by exact_mod_cast (show 0 < m by omega)
  have hwt : ∀ j, W.IsLocAlg h (κ j * kaD) (fun τ => -((m : ℤ) * Fr.w n j) + wk τ) := by
    intro j
    let x : ℤ := (m : ℤ) * Fr.w n j
    have h0 : W.IsWtPart h (κ j * cyc ^ (-x)) 0 1 := by
      refine hzero _ _ hone fun σ => ?_
      have hs := hκ j (Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h σ)) σ.2
      rw [MonoidHom.one_apply, mul_one, MonoidHom.mul_apply, MonoidHom.zpow_apply, hs]
      show cycBar L Ω l σ ^ x * cycBar L Ω l σ ^ (-x) = 1
      rw [← zpow_add, add_neg_cancel, zpow_zero]
    have h1 := (hmul _ _ _ _ _ _ h0 (hpow _ _ _ x hc)).1
    have h2 := (hmul _ _ _ _ _ _ h1 hphk).1
    have he : κ j * cyc ^ (-x) * cyc ^ x * kaD = κ j * kaD := by
      rw [mul_assoc (κ j), ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
    rw [he] at h2
    refine ⟨1 * 1 ^ x * phk, ?_⟩
    convert h2 using 2
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, x]
    ring
  refine ⟨⟨fun j τ => -((m : ℤ) * Fr.w n j) + wk τ, fun τ i j hij => ?_, hwt⟩, ?_⟩
  · have := w_anti n hij
    simp only
    nlinarith
  · intro i j heq
    have hcomm : κ j * kaD * cyc = κ j * cyc * kaD := by
      rw [mul_assoc, mul_comm kaD, ← mul_assoc]
    rw [hcomm] at heq
    have heq' : κ i = κ j * cyc := mul_right_cancel heq
    have hN : (m : ℤ) * Fr.w n i - (m : ℤ) * Fr.w n j - 1 ≠ 0 := by
      intro h0
      have h1 : (m : ℤ) * (Fr.w n i - Fr.w n j) = 1 := by linarith
      have := Int.eq_one_of_mul_eq_one_right hm0.le h1
      omega
    obtain ⟨g, hg, hne⟩ := cyc_ine hl h hN
    apply hne
    let s := Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h ⟨g, hg⟩)
    have hi := hκ i s hg
    have hj := hκ j s hg
    have hs := congrArg (fun f => f s) heq'
    simp only [MonoidHom.mul_apply] at hs
    rw [hi, hj] at hs
    have hs' : cycBar L Ω l g ^ ((m : ℤ) * Fr.w n i) = cycBar L Ω l g ^ ((m : ℤ) * Fr.w n j) * cycBar L Ω l g := hs
    rw [zpow_sub, zpow_sub, hs', zpow_one]
    group
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsFrameFactorizationOfTrivialOnInertia
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
open scoped Matrix
set_option linter.overlappingInstances false

private theorem fac_conj {Ω : Type} [Field Ω] [CharZero Ω] (l : ℕ) (A : ValuationSubring Ω) (g x : G ℚ Ω)
    (hl : ¬ A.valuation (l : Ω) < 1) (hx : x ∈ Ine (F := ℚ) A) :
    ∃ A' : ValuationSubring Ω, ¬ A'.valuation (l : Ω) < 1 ∧ g * x * g⁻¹ ∈ Ine (F := ℚ) A' := by
  have h : IsLift (RingEquiv.refl ℚ) ((g.symm : Ω ≃ₐ[ℚ] Ω) : Ω ≃+* Ω) := fun q => g.symm.commutes q
  let σ : Ω ≃+* Ω := ((g.symm : Ω ≃ₐ[ℚ] Ω) : Ω ≃+* Ω)
  have hA : ∀ y : Ω, σ y ∈ A ↔ y ∈ A.comap (σ : Ω →+* Ω) := fun y => by
    rw [ValuationSubring.mem_comap]
    rfl
  refine ⟨A.comap (σ : Ω →+* Ω), ?_, ?_⟩
  · rw [← val_lt_one hA (l : Ω), map_natCast]
    exact hl
  · have hc := conjGal_mem_Ine h hA hx
    convert hc using 1
    ext z
    rfl

theorem UpperTheory.exists_frame_factorization_of_trivial_on_inertia :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ} {L : Type} [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ) {n : ℕ} (r : G L Ω →* GL (Fin n) (Qbar l)), Continuous r → (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := L) A, Ψ (galEmb ℚ L Ω s) = 1 → r s = 1) → ∃ r' : Φ.G0 →* GL (Fin n) (Qbar l), Continuous r' ∧ (∀ s, r' (k.p0 s) = r s) ∧ ∀ P : GL (Fin n) (Qbar l), Sd.IsPair σ r 1 P → ∀ g, (r' g).valᵀ * P.val * (r' (Φ.conj g)).val = P.val := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ Φ k n r hr hine
  have hgal : ∀ s : G L Ω, galEmb ℚ L Ω s ∈ upl Ω L ⊓ η.ker := fun s => by
    have h := galEmb_mem ℚ L Ω s
    rwa [k.gal] at h
  have hmem : ∀ s : G L Ω, galEmb ℚ L Ω s ∈ upl Ω L := fun s => (hgal s).1
  have hq : ∀ s, (k.p0 s : Φ.Γ) = k.p ⟨galEmb ℚ L Ω s, hmem s⟩ := fun s => rfl
  let q : G L Ω →* Φ.G0 :=
    { toFun := k.p0
      map_one' := by
        apply Subtype.ext
        rw [hq]
        rw [show (⟨galEmb ℚ L Ω 1, hmem 1⟩ : upl Ω L) = 1 from Subtype.ext (map_one _), map_one]
        rfl
      map_mul' := fun s t => by
        apply Subtype.ext
        rw [Subgroup.coe_mul, hq, hq, hq, ← map_mul]
        exact congrArg k.p (Subtype.ext (map_mul _ _ _)) }
  have hqv : ∀ s, ((q s : Φ.G0) : Φ.Γ) = k.p ⟨galEmb ℚ L Ω s, hmem s⟩ := fun s => rfl
  have hqs : Function.Surjective q := by
    intro x
    obtain ⟨u, hu⟩ := k.p_surj x.val
    have hu1 : (u : G ℚ Ω) ∈ galOf ℚ L Ω := by
      rw [k.gal]
      refine ⟨u.2, MonoidHom.mem_ker.mpr ?_⟩
      rw [← k.del u, hu]
      exact MonoidHom.mem_ker.mp x.2
    rw [← range_galEmb ℚ L Ω] at hu1
    obtain ⟨s, hs⟩ := hu1
    refine ⟨s, Subtype.ext ?_⟩
    rw [hqv, ← hu]
    exact congrArg k.p (Subtype.ext hs)
  have hgc : Continuous (galEmb ℚ L Ω) := (galEmbTop ℚ L Ω).1.continuous
  have hqc : Continuous q := by
    refine continuous_induced_rng.2 ?_
    exact k.p_cont.comp (hgc.subtype_mk hmem)
  have hinj : Function.Injective (galEmb ℚ L Ω) := (galEmbTop ℚ L Ω).1.injective
  have hker : ∀ s, q s = 1 → r s = 1 := by
    intro s hs
    have h1 : (⟨galEmb ℚ L Ω s, hmem s⟩ : upl Ω L) ∈ k.p.ker := by
      rw [MonoidHom.mem_ker, ← hqv, hs]
      rfl
    rw [k.p_ker] at h1
    let H' : Subgroup (upl Ω L) := (r.ker.map (galEmb ℚ L Ω)).comap (upl Ω L).subtype
    have hcl : IsClosed (H' : Set (upl Ω L)) := by
      have hk : IsClosed (r.ker : Set (G L Ω)) := by
        haveI : T2Space (Qbar l) := inferInstance
        haveI : T2Space (Matrix (Fin n) (Fin n) (Qbar l)) :=
          (inferInstance : T2Space (Fin n → Fin n → Qbar l))
        haveI h2 : T2Space (GL (Fin n) (Qbar l)) := inferInstance
        haveI : T1Space (GL (Fin n) (Qbar l)) := @T2Space.t1Space _ _ h2
        exact isClosed_singleton.preimage hr
      have hi : IsClosed ((galEmb ℚ L Ω) '' (r.ker : Set (G L Ω))) :=
        (hk.isCompact.image hgc).isClosed
      exact hi.preimage continuous_subtype_val
    have hX : Subgroup.normalClosure
        {s : upl Ω L | ∃ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 ∧ (s : G ℚ Ω) ∈ Ine B' ∧
          η s = 1 ∧ barChar O Ψ s = 1} ≤ H' := by
      unfold Subgroup.normalClosure
      refine (Subgroup.closure_le _).2 ?_
      intro c hc
      rw [Group.mem_conjugatesOfSet_iff] at hc
      obtain ⟨x, ⟨B', hB'l, hxI, hxη, hxbar⟩, hconj⟩ := hc
      obtain ⟨u, hu⟩ := isConj_iff.mp hconj
      have hcv : (c : G ℚ Ω) = u * x * (u : G ℚ Ω)⁻¹ := by
        rw [← hu, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      obtain ⟨A', hA'l, hcI⟩ := fac_conj l B' u x hB'l hxI
      rw [← hcv] at hcI
      have hcη : η c = 1 := by
        rw [hcv, map_mul, map_mul, hxη, mul_one, ← map_mul, mul_inv_cancel, map_one]
      have hcbar : barChar O Ψ c = 1 := by
        rw [hcv, map_mul, map_mul, hxbar, mul_one, ← map_mul, mul_inv_cancel, map_one]
      have hcgal : (c : G ℚ Ω) ∈ galOf ℚ L Ω := by
        rw [k.gal]
        exact ⟨c.2, hcη⟩
      rw [← range_galEmb ℚ L Ω] at hcgal
      obtain ⟨t, ht⟩ := hcgal
      have hΨ : Ψ c = 1 := k.teich A' hA'l c ⟨hcI, c.2⟩ hcbar
      show (c : G ℚ Ω) ∈ r.ker.map (galEmb ℚ L Ω)
      refine ⟨t, ?_, ht⟩
      show r t = 1
      refine hine A' hA'l t ?_ ?_
      · show galEmb ℚ L Ω t ∈ Ine (F := ℚ) A'
        rw [ht]
        exact hcI
      · rw [ht]
        exact hΨ
    have h2 := (Subgroup.topologicalClosure_minimal _ hX hcl) h1
    obtain ⟨t, ht, hts⟩ := h2
    rw [hinj hts] at ht
    exact ht
  have hle : q.ker ≤ r.ker := fun s hs => hker s hs
  let e := QuotientGroup.quotientKerEquivOfSurjective q hqs
  let r' : Φ.G0 →* GL (Fin n) (Qbar l) := (QuotientGroup.lift q.ker r hle).comp e.symm.toMonoidHom
  have hr'q : ∀ s, r' (q s) = r s := by
    intro s
    have he : e.symm (q s) = (s : G L Ω ⧸ q.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift q.ker r hle (e.symm (q s)) = r s
    rw [he]
    rfl
  have hqq : Topology.IsQuotientMap q := Topology.IsQuotientMap.of_surjective_continuous hqs hqc
  have hr'c : Continuous r' := by
    rw [hqq.continuous_iff]
    convert hr using 1
    funext s
    exact hr'q s
  refine ⟨r', hr'c, fun s => hr'q s, ?_⟩
  intro P hP g
  obtain ⟨s, rfl⟩ := hqs g
  obtain ⟨hσ, hσc⟩ := k.c
  have hs'gal : σ * galEmb ℚ L Ω s * σ⁻¹ ∈ galOf ℚ L Ω := by
    rw [k.gal]
    refine ⟨(upl Ω L).mul_mem ((upl Ω L).mul_mem hσ (hmem s)) ((upl Ω L).inv_mem hσ),
      MonoidHom.mem_ker.mpr ?_⟩
    rw [map_mul, map_mul, MonoidHom.mem_ker.mp (hgal s).2, mul_one, ← map_mul, mul_inv_cancel, map_one]
  rw [← range_galEmb ℚ L Ω] at hs'gal
  obtain ⟨s', hs'⟩ := hs'gal
  have hconj : Φ.conj (q s) = q s' := by
    apply Subtype.ext
    rw [show ((Φ.conj (q s) : Φ.G0) : Φ.Γ) = Φ.c * (q s : Φ.Γ) * Φ.c⁻¹ from
      MulAut.conjNormal_apply _ _]
    rw [hqv, hqv, ← hσc, ← map_inv, ← map_mul, ← map_mul]
    apply congrArg k.p
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hs'.symm
  rw [hconj, hr'q, hr'q]
  have h := hP s s' hs'
  rw [MonoidHom.one_apply, Units.val_one, one_smul] at h
  exact h
end

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
open Polynomial
open scoped Matrix

set_option linter.overlappingInstances false

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime]

private theorem tri {a b c : Qbar l} (h : ‖a - b‖ < 1) (h' : ‖b - c‖ < 1) : ‖a - c‖ < 1 := by
  rw [← sub_add_sub_cancel a b c]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h h')

private theorem near_of_res {c : Coef l} {a b : c.O} (h : residue c.O a = residue c.O b) : ‖a.1 - b.1‖ < 1 := by
  have h1 : a - b ∈ maximalIdeal c.O := by
    rw [← residue_eq_zero_iff, map_sub, h, sub_self]
  have h2 := (Fr.sc_norm l c _).2.1 h1
  rwa [Subalgebra.coe_sub] at h2

private theorem norm_unit {c : Coef l} (a : c.Oˣ) : ‖a.val.1‖ = 1 :=
  le_antisymm (Fr.sc_norm l c _).1 (not_lt.1 fun h => (Fr.sc_norm l c _).2.2 h a.isUnit)

private theorem norm_of_near {a b : Qbar l} (h : ‖a - b‖ < 1) (hb : ‖b‖ = 1) : ‖a‖ = 1 := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := a - b) (y := b) (by rw [hb]; exact h.ne)
  rwa [sub_add_cancel, hb, max_eq_right h.le] at this

private theorem near_mul {a b a' b' : Qbar l} (h : ‖a - b‖ < 1) (h' : ‖a' - b'‖ < 1) (hb : ‖b‖ = 1) (hb' : ‖b'‖ = 1) :
    ‖a * a' - b * b'‖ < 1 := by
  refine tri (b := b * a') ?_ ?_
  · rwa [← sub_mul, norm_mul, norm_of_near h' hb', mul_one]
  · rwa [← mul_sub, norm_mul, hb, one_mul]

private theorem near_zpow {a b : Qbar l} (h : ‖a - b‖ < 1) (hb : ‖b‖ = 1) (w : ℤ) : ‖a ^ w - b ^ w‖ < 1 := by
  have ha := norm_of_near h hb
  have hn : ∀ k : ℕ, ‖a ^ k - b ^ k‖ < 1 := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_succ]; exact near_mul ih h (by rw [norm_pow, hb, one_pow]) hb
  obtain ⟨k, rfl | rfl⟩ := w.eq_nat_or_neg
  · simpa using hn k
  · have ha0 : a ^ k ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [ha]; exact one_ne_zero))
    have hb0 : b ^ k ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [hb]; exact one_ne_zero))
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, inv_sub_inv ha0 hb0, norm_div, norm_mul, norm_pow, norm_pow, ha, hb,
      norm_sub_rev]
    simpa using hn k

private theorem eq_one_of_near {u : Qbar l} {m : ℕ} (hm : ¬ l ∣ m) (hu : u ^ m = 1) (h : ‖u - 1‖ < 1) : u = 1 :=
  _root_.UpperTheory.Reformulated.B.S7.eq_one_of_near hm hu h

private theorem one_of_diag {Γ : Type} [Group Γ] {n : ℕ} {r : Γ →* GL (Fin n) (Qbar l)} {H : Subgroup Γ}
    {χ : Fin n → Γ →* (Qbar l)ˣ} (h : IsDiagOn r H χ) {s : Γ} (hs : s ∈ H) (h1 : ∀ i, χ i s = 1) : r s = 1 := by
  obtain ⟨g, hg⟩ := h
  have : g * r s * g⁻¹ = 1 := Units.ext (by rw [hg s hs]; simp [h1])
  rwa [mul_inv_eq_one, mul_eq_left] at this

private theorem flag_cont {Γ : Type} [Group Γ] [TopologicalSpace Γ] {n : ℕ} {r : Γ →* GL (Fin n) (Qbar l)}
    {κ : Fin n → Γ →* (Qbar l)ˣ} (hr : ∀ a b, Continuous fun g => (r g).val a b) (h : W.HasFlag r κ) (i : Fin n) :
    Continuous fun g => (κ i g).val := by
  obtain ⟨P, hP⟩ := h
  have : ∀ g, (κ i g).val = ∑ b, (∑ a, P.val i a * (r g).val a b) * (P⁻¹).val b i := fun g => by
    rw [← (hP g).2 i]
    simp only [Units.val_mul, Matrix.mul_apply]
  simp only [this]
  exact continuous_finsetSum _ fun b _ => (continuous_finsetSum _ fun a _ =>
    continuous_const.mul (hr a b)).mul continuous_const

private theorem comm_one {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {κ : Γ →* (Qbar l)ˣ}
    (h : Continuous fun g => (κ g).val) {g : Γ} (hg : g ∈ (commutator Γ).topologicalClosure) : κ g = 1 := by
  refine Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker κ) ?_ hg
  have : (κ.ker : Set Γ) = {g | (κ g).val = 1} := by ext; simp
  rw [this]
  exact isClosed_eq h continuous_const

private theorem pt_ex {c : Coef l} [Fr.IsCoef l c.O] {F : Fr.Frame l (ResidueField c.O)} {n : ℕ} (T : Setup F n)
    (r : F.G0 →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (hP : ∀ g, (r g).valᵀ * P.val * (r (F.conj g)).val = P.val)
    (ρ : T.G.G₀ →* GL (Fin n) (Qbar l)) (hρ : ρ = tw (r.comp T.K.π) (T.K.κA (Qbar l)))
    (hc : ∀ a b, Continuous fun g => (ρ g).val a b)
    (ψ : ∀ v, Fin n → T.G.Gv v →* (Qbar l)ˣ) (hf : ∀ v, W.HasFlag (ρ.comp (T.G.φ v)) (ψ v))
    (h1 : ∀ g, ∃ b : Fin n → c.O, (∀ i, residue c.O (b i) = T.r.chib i g) ∧
      ∀ k, ‖(ρ g).val.charpoly.coeff k - (∏ i, (X - C (b i).1)).coeff k‖ < 1)
    (h2 : ∀ u, ∀ g ∈ T.r.Ip u, ρ g = 1)
    (h3 : ∀ v i g, ∃ b : c.O, residue c.O b = T.r.chib i (T.G.φ v g) ∧ ‖(ψ v i g).val - b.1‖ < 1) :
    ∃ x : T.B.B →ₐ[c.O] Qbar l, T.B.u.Maps (x : T.B.B →+* Qbar l) (W.GDet.ofRep (W.mat ρ)) ψ := by
  have chi_single : ∀ {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G),
      (W.GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
    intro A G _ _ ρ g
    change (W.GDet.repAlg ρ A[X] _).det = _
    rw [map_sub]
    rw [Matrix.charpoly]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [W.GDet.repAlg, h, Matrix.charmatrix_apply, Matrix.one_apply]
  refine (W.exists_determinantPair_over_algebraicIntegers l T.G c.O n T.r T.B ρ ψ hc ⟨P, fun g => ?_⟩ (fun i g a ha => ?_) h2 (fun v i g a ha => ?_)
    (fun v i g => ?_) hf).exists
  · have h := congrArg (fun u : c.Oˣ => algebraMap c.O (Qbar l) u) (T.K.κ_conj g)
    have e : ((T.G.eps c.O (Qbar l) g ^ (1 - (n : ℤ)) : (Qbar l)ˣ) : Qbar l) =
        algebraMap c.O (Qbar l) (T.G.eps c.O c.O g ^ (1 - (n : ℤ)) : c.Oˣ) :=
      congrArg Units.val (map_zpow (Units.map (algebraMap c.O (Qbar l) : c.O →* Qbar l)) (T.G.eps c.O c.O g) _).symm
    rw [e, ← h, hρ]
    change (Af.tw _ _ g).valᵀ * _ * (Af.tw _ _ _).val = _
    rw [tw_val, tw_val, MonoidHom.comp_apply, MonoidHom.comp_apply, T.K.π_conj, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, hP, smul_smul, Units.val_mul, map_mul]
    rfl
  · obtain ⟨b, hb, hk⟩ := h1 g
    have e : residue c.O ((-1) ^ i * (∏ j, (X - C (b j))).coeff (n - i)) = residue c.O a := by
      rw [ha, W.Resid.Dbar, W.GDet.lam, chi_single _ _, map_mul, ← coeff_map, Polynomial.map_prod]
      change _ = _ * (Matrix.diagonal _).charpoly.coeff _
      rw [Matrix.charpoly_diagonal]
      simp only [map_pow, map_neg, map_one, Polynomial.map_sub, map_X, map_C, hb]
    refine tri ?_ (near_of_res e)
    rw [W.GDet.lam, chi_single _ _]
    have e' : ((-1) ^ i * (∏ j, (X - C (b j))).coeff (n - i) : c.O).1 =
        (-1) ^ i * (∏ j, (X - C (b j).1)).coeff (n - i) := by
      have e0 : ∀ y : c.O, y.1 = algebraMap c.O (Qbar l) y := fun _ => rfl
      rw [e0 (_ * _), map_mul, ← coeff_map, Polynomial.map_prod, map_pow, map_neg, map_one]
      simp only [Polynomial.map_sub, map_X, map_C]
      rfl
    rw [e', ← mul_sub, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact hk (n - i)
  · obtain ⟨b, hb, hk⟩ := h3 v i g
    exact tri hk (near_of_res (by rw [hb, ha, T.K.psib]))
  · rw [T.r.th_comm v i g (T.K.mu v g.2), comm_one (flag_cont (r := ρ.comp (T.G.φ v)) (fun a b => (hc a b).comp (T.G.φ_cont v)) (hf v) i)
      (T.K.mu v g.2)]
    simp

private theorem t2_space_open_subgroup (F : W.GFrame l) : T2Space F.G₀ :=
  haveI : T3Space F.Γ := {}
  inferInstance

private theorem pr_surj {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {s : W.HidaSetting l L Ω} (V : s.Lev) : Function.Surjective V.pr := by
  rintro ⟨g, hg⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
  obtain ⟨t, rfl⟩ := (V.hη g).1 hg
  exact ⟨t, rfl⟩

private theorem val_iff {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] {A : ValuationSubring Ω} {v : W.Plc L}
    (h : IsPlaceOver A v) : A.valuation (l : Ω) < 1 ↔ ((l : ℕ) : 𝓞 L) ∈ v.asIdeal := by
  convert h (l : 𝓞 L) using 1 <;> simp only [map_natCast]

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
  {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O}
  {n : ℕ} {ka : G L Ω →* (Qbar l)ˣ}

private def prT (R : CReal k c₁ f n ka) : G L Ω →* R.T.G.G₀ := R.V.pr

private theorem beta_ex (R : CReal k c₁ f n ka) : ∃ β : Fin n → G L Ω →* c₁.Oˣ,
    (∀ i s, residue c₁.O (β i s) = R.T.r.chib i (prT R s)) ∧
      ∀ i s, (β i s).val.1 = (Ψ (galEmb ℚ L Ω s)).val.1 ^ Fr.w n i * (ka s).val := by
  let j : c.O →+* c₁.O := (Subalgebra.inclusion R.le).toRingHom
  refine ⟨fun i => (W.pushCh j (Ψ.comp (galEmb ℚ L Ω))) ^ Fr.w n i * R.K.κ.comp R.V.pr, fun i s => ?_, fun i s => ?_⟩
  · have h : (Φ.ext f).Ψ (R.K.π (R.V.pr s)) = W.pushCh (residue c₁.O) (W.pushCh j (Ψ.comp (galEmb ℚ L Ω))) s := by
      rw [R.π_pr]
      apply Units.ext
      change f (Φ.Ψ (k.p _)) = _
      rw [k.psi]
      exact R.hf _ _ rfl
    refine Eq.trans ?_ (congrArg Units.val (R.K.chib i (R.V.pr s)).symm)
    rw [h]
    exact congrArg Units.val ((map_mul (Units.map (residue c₁.O : c₁.O →* ResidueField c₁.O)) _ _).trans
      (congrArg (· * _) (map_zpow _ _ _)))
  · rw [← R.κ_pr]
    refine (congrArg Units.val ((map_mul (Units.map (c₁.O.val : c₁.O →* Qbar l)) _ _).trans
      (congrArg (· * _) (map_zpow _ _ _)))).trans ?_
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
    rfl

private theorem main (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) (hM : l ∣ M) (R : CReal k c₁ f n ka)
    (hka : IsKa σ M ι n ka) (χ' : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ) (hχ : ¬ l ∣ orderOf χ')
    (hc : ∀ s, ‖((cycBar ℚ Ω l ^ j * χ') s).val - (Ψ s).val.1‖ < 1) (m : ℕ) (hm : 2 ≤ m) (r : G L Ω →* GL (Fin n) (Qbar l))
    (hr : Sd.IsSeed ι σ (fun i => ((cycBar ℚ Ω l ^ j * χ') ^ Fr.w n i).comp (galEmb ℚ L Ω))
      (fun i => (χ' ^ Fr.w n i).comp (galEmb ℚ L Ω)) (fun i => m * Fr.w n i) ka r)
    (J : Ideal R.B₀.B) (hJ : R.B₀.PT ι J) : R.T.IdealSpecializationPoint J := by
  have hε : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := L) A,
      ‖(χ' (galEmb ℚ L Ω s)).val - (Ψ (galEmb ℚ L Ω s)).val.1‖ < 1 := fun A hA s hs => by
    have h1 : cycZ ℚ Ω l (galEmb ℚ L Ω s) = 1 := (places L Ω l A).2.2.2 hA hs
    have h2 := hc (galEmb ℚ L Ω s)
    simpa [cycBar, h1] using h2
  have hχo : ∀ s, (χ' s).val ^ orderOf χ' = 1 := fun s => by
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, pow_orderOf_eq_one]; rfl
  obtain ⟨r', hr'c, hr', hform⟩ := UpperTheory.exists_frame_factorization_of_trivial_on_inertia k r hr.cont fun A hA s hs h1 =>
    one_of_diag (hr.away A hA) hs fun i => by
      have h2 : χ' (galEmb ℚ L Ω s) = 1 := Units.ext (eq_one_of_near hχ (hχo _) (by simpa [h1] using hε A hA s hs))
      simp [h2]
  obtain ⟨P, hPs, hP⟩ := hr.pair
  obtain ⟨β, hβ1, hβ2⟩ := beta_ex R
  have hκ : ∀ s, R.T.K.κA (Qbar l) (prT R s) = ka s := fun s => Units.ext (R.κ_pr s)
  have hkn : ∀ s, ‖(ka s).val‖ = 1 := fun s => R.κ_pr s ▸ norm_unit _
  have hzn : ∀ s (w : ℤ), ‖(Ψ s).val.1 ^ w‖ = 1 := fun s w => by rw [norm_zpow, norm_unit, one_zpow]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : R.T.G.G₀ →* GL (Fin n) (Qbar l), ρ = tw (r'.comp R.T.K.π) (R.T.K.κA (Qbar l)) := ⟨_, rfl⟩
  have hρr : ∀ s, ρ (prT R s) = tw r ka s := fun s => Units.ext (by
    rw [hρ, tw_val, tw_val, hκ, ← hr' s, ← R.π_pr s]; rfl)
  obtain ⟨hS1, -, hS3, hS4, -⟩ := Sd.shapeFacts l (G L Ω) n r ka
  have hS5' := (Sd.shapeFacts l (G L Ω) n (tw r ka) ka).2.2.2.2.1
  have htw : Continuous (tw r ka) := by
    have h1 : ∀ {r : G L Ω →* GL (Fin n) (Qbar l)} {ka : G L Ω →* (Qbar l)ˣ}, Continuous r → Continuous ka →
        Continuous fun s => (tw r ka s).val := fun h h' => by
      simp only [tw_val]
      exact (Units.continuous_val.comp h').smul (Units.continuous_val.comp h)
    refine Units.continuous_iff.2 ⟨h1 hr.cont hka.alg.1, ?_⟩
    simp only [← map_inv]
    exact (h1 hr.cont hka.alg.1).comp continuous_inv
  have hρc : ∀ a b, Continuous fun g => (ρ g).val a b := fun a b => by
    haveI := t2_space_open_subgroup R.T.G
    have hp : Continuous (prT R) := R.V.pr_cont W.continuous_resP
    have hq : Topology.IsQuotientMap (prT R) := hp.isClosedMap.isQuotientMap hp (pr_surj R.V)
    rw [hq.continuous_iff]
    simp only [Function.comp_def, hρr]
    exact (Units.continuous_val.comp htw).matrix_elem a b
  have hX : ∀ i s, ‖(((cycBar ℚ Ω l ^ j * χ') ^ Fr.w n i).comp (galEmb ℚ L Ω) s).val -
      (Ψ (galEmb ℚ L Ω s)).val.1 ^ Fr.w n i‖ < 1 := fun i s => by
    rw [MonoidHom.comp_apply, MonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val]
    exact near_zpow (hc _) (norm_unit _) _
  have htame : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := L) A,
      (∀ i, R.T.r.chib i (prT R s) = 1) → tw r ka s = 1 := fun A hA s hs h1 => by
    obtain ⟨o, ho, hko⟩ := hka.ord
    refine one_of_diag (hS1 _ _ (hr.away A hA)) hs fun i => Units.ext ?_
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.zpow_apply, Units.val_mul, Units.val_zpow_eq_zpow_val]
    refine eq_one_of_near (m := orderOf χ' * o) (fun h => ((Fact.out : l.Prime).dvd_mul.1 h).elim hχ ho) ?_ ?_
    · rw [mul_pow, ← zpow_natCast, ← zpow_mul, mul_comm (Fr.w n i), zpow_mul, zpow_natCast, pow_mul, hχo, one_pow, one_zpow,
        one_mul, pow_mul', ← Units.val_pow_eq_pow_val, hko A hA s hs, Units.val_one, one_pow]
    · refine tri (near_mul (near_zpow (hε A hA s hs) (norm_unit _) _) (by simp) (hzn _ _) (hkn s)) ?_
      rw [← hβ2]
      exact near_of_res (b := 1) (by rw [hβ1, h1, map_one, Units.val_one])
  choose κ hκf hκi hκc using fun v : W.Vl l L => hr.above (R.s.A v) ((val_iff (R.s.hA v)).2 v.2)
  let ψ : ∀ v : W.Vl l L, Fin n → Dec (F := L) (R.s.A v) →* (Qbar l)ˣ := fun v i =>
    κ v i * ka.comp (Dec (F := L) (R.s.A v)).subtype
  have hfl : ∀ v : W.Vl l L, W.HasFlag ((tw r ka).comp (Dec (F := L) (R.s.A v)).subtype) (ψ v) := fun v => hS3 _ _ (hκf v)
  have hfl' : ∀ v, W.HasFlag (ρ.comp (R.T.G.φ v)) (ψ v) := fun v => by
    have : ρ.comp (R.T.G.φ v) = (tw r ka).comp (Dec (F := L) (R.s.A v.1)).subtype := MonoidHom.ext fun s => hρr s.1
    exact this ▸ hfl v
  refine (pt_ex R.T r' P (hform P hP) ρ hρ hρc ψ hfl' (fun g => ?_) (fun u g hg => ?_) (fun v i g => ?_)).elim
    fun x hx => ?_
  rotate_right
  · obtain ⟨ρ', h1, h2⟩ := UpperTheory.universalMaps_point_of_polarized_flagged_rep R.T (Qbar l) x r' ρ P ψ hPs (hform P hP) hρ hx hfl'
      ⟨hr.irr.1, fun _ _ _ => trivial, fun U hU hi => hr.irr.2.2 U hU fun s => hr' s ▸ hi (k.p0 s)⟩
    refine ⟨Qbar l, inferInstance, inferInstance, inferInstance, x, ρ', h1, ?_, h2⟩
    have hA := fun v : W.Vl l L => UpperTheory.diagonal_characters_regular_algebraic_of_inertia_weights H ι (R.s.hw v)
      ((val_iff (R.s.hw v)).1 ((val_iff (R.s.hA v)).2 v.2)) ka hka.alg n m hm (κ v) (hκi v)
    choose wt hwt1 hwt2 using fun v => (hA v).1
    have hψ : ∀ v i, W.UniversalOrdinaryDeterminantRing.Pt.psi (B := R.B₀) x v i = ψ v i := hx.2
    refine hJ x wt (tw r ka) (by have := R.n23; omega) (by have := R.n23; omega) ⟨hwt1, fun v i => hψ v i ▸ hwt2 v i⟩
      ?_ htw hr.aut (fun s hs => htame _ ?_ s hs fun i => ?_)
      fun v => ⟨?_, fun a b => ?_⟩
    · have hcomap : (W.GDet.ofRep (W.mat ρ)).comap (prT R) = W.GDet.ofRep ((W.mat ρ).comp (prT R)) := by
        refine W.GDet.ext fun B _ _ x => ?_
        change (W.GDet.repAlg (W.mat ρ) B (MonoidAlgebra.mapDomainRingHom B (prT R) x)).det =
          (W.GDet.repAlg ((W.mat ρ).comp (prT R)) B x).det
        congr 1
        induction x using MonoidAlgebra.induction_linear with
        | zero => simp
        | add a b ha hb => simp only [map_add (f := _), ha, hb]
        | single g r => simp [W.GDet.repAlg]
      refine (congrArg (W.GDet.comap · (prT R)) hx.1).trans (hcomap.trans ?_)
      exact congrArg _ (MonoidHom.ext fun s => congrArg Units.val (hρr s))
    · obtain ⟨d, rfl⟩ := hM
      refine fun h => R.v0M ?_
      rw [Nat.cast_mul, map_mul]
      exact mul_lt_one_of_lt_of_le h ((ValuationSubring.valuation_le_one_iff _ _).2 (natCast_mem _ d))
    · exact R.v0.1 i ⟨s, hs, rfl⟩
    · exact (funext (hψ v) : _ = ψ v) ▸ hfl v
    · rw [hψ, hψ]
      exact (hA v).2 a b
  · obtain ⟨s, rfl⟩ : ∃ s, prT R s = g := pr_surj R.V g
    refine ⟨fun i => β i s, fun i => hβ1 i s, fun a => ?_⟩
    rw [hρr]
    refine hS5' _ (fun i => W.pushCh (c₁.O.val : c₁.O →+* Qbar l) (β i)) 1 (fun i t => ?_) (hS4 _ hkn hr.res) (fun i t => ?_) s a
    · rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hkn, mul_one]
      exact norm_of_near (hX i t) (hzn _ _)
    · change ‖(β i t).val.1 - _‖ < 1
      rw [hβ2, norm_sub_rev]
      exact near_mul (hX i t) (by simp) (hzn _ _) (hkn _)
  · obtain ⟨⟨s, hs, rfl⟩, h2⟩ := hg
    exact (hρr s).trans (htame _ (fun h => R.s.St_l u.1 u.2 ((val_iff (R.s.hA u.1)).1 h)) s hs fun i =>
      Subgroup.mem_iInf.1 h2 i)
  · refine ⟨β i g.1, hβ1 i g.1, ?_⟩
    rw [hβ2]
    exact near_mul (a' := (ka g.1).val) (tri (hκc v i g) (hX i g.1)) (by simp) (hzn _ _) (hkn _)

end SlopeTestRemainingChoices
