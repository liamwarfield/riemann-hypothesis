module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharsOfReading
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTerMore
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemOfPrimeDvdAbsNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLogOnePlusKerThetaDeRhamPlus
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorIdentificationNatural
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SepOfHausdorff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleResidualPointDescendsCoefficientExten
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LiveDescent

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

theorem isLocalHom_of_nonunit {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B]
    [IsLocalRing B] (f : A →+* B) {a : A} (ha : a ≠ 0) (hf : f a ∈ IsLocalRing.maximalIdeal B) : IsLocalHom f := by
  have hne : (IsLocalRing.maximalIdeal B).comap f ≠ ⊥ := fun h => ha (by
    have : a ∈ (IsLocalRing.maximalIdeal B).comap f := hf
    rwa [h, Ideal.mem_bot] at this)
  have hm : ((IsLocalRing.maximalIdeal B).comap f).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  have he := IsLocalRing.eq_maximalIdeal hm
  refine ⟨fun x hx => ?_⟩
  by_contra h
  have : x ∈ (IsLocalRing.maximalIdeal B).comap f := by rw [he]; exact h
  exact this hx

theorem continuous_of_isLocalHom {A B : Type} [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [IsLocalRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (IsLocalRing.maximalIdeal A)) (hB : IsAdic (IsLocalRing.maximalIdeal B)) (f : A →+* B)
    [IsLocalHom f] : Continuous f := by
  have hm : Ideal.map f (IsLocalRing.maximalIdeal A) ≤ IsLocalRing.maximalIdeal B :=
    Ideal.map_le_iff_le_comap.2 fun x hx => map_nonunit f x hx
  refine continuous_of_continuousAt_zero f.toAddMonoidHom ?_
  intro s hs
  rw [map_zero] at hs
  obtain ⟨n, hn⟩ := (isAdic_iff.1 hB).2 s hs
  refine Filter.mem_map.2 (Filter.mem_of_superset (((isAdic_iff.1 hA).1 n).mem_nhds (Ideal.zero_mem _))
    fun x hx => hn ?_)
  have h1 : f x ∈ Ideal.map f (IsLocalRing.maximalIdeal A ^ n) := Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono hm n h1

theorem span_eq_top_of_map {ι k K : Type} [Field k] [Field K] (f : k →+* K) {r : ℕ}
    (M : ι → Matrix (Fin r) (Fin r) k) (h : Submodule.span K (Set.range fun g => (M g).map f) = ⊤) :
    Submodule.span k (Set.range M) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨l, hl0, hl⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  have hexp : ∀ Y : Matrix (Fin r) (Fin r) k, l Y = ∑ p, ∑ q, Y p q * l (Matrix.single p q 1) := by
    intro Y
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have key : ∀ Y : Matrix (Fin r) (Fin r) K, ∑ p, ∑ q, Y p q * f (l (Matrix.single p q 1)) = 0 := by
    intro Y
    have hY : Y ∈ Submodule.span K (Set.range fun g => (M g).map f) := h ▸ Submodule.mem_top
    induction hY using Submodule.span_induction with
    | mem Y hY =>
      obtain ⟨g, rfl⟩ := hY
      have h0 : l (M g) = 0 := hl (Submodule.subset_span ⟨g, rfl⟩)
      have := congrArg f ((hexp (M g)).symm.trans h0)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum] using this
    | zero => simp
    | add Y Z _ _ hY hZ => simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, hY, hZ, add_zero]
    | smul a Y _ hY => simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hY, mul_zero]
  apply hl0
  refine LinearMap.ext fun Y => ?_
  rw [hexp, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  have h1 := key (Matrix.single p q 1)
  rw [Finset.sum_eq_single p (fun a _ ha => by simp [Matrix.single_apply_of_row_ne (Ne.symm ha)]) (by simp),
    Finset.sum_eq_single q (fun a _ ha => by simp [Matrix.single_apply_of_col_ne _ _ (Ne.symm ha)]) (by simp)] at h1
  simp only [Matrix.single_apply_same, one_mul, map_eq_zero] at h1
  rw [h1, mul_zero]

theorem trace_of_isDecomp {Γ A : Type} [Group Γ] [CommRing A] [IsDomain A] [IsLocalRing A] {n r t : ℕ}
    (σ : Γ →* GL (Fin n) A) (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (h : ∃ e, IsDecomp (t := t) σ ρ χ e)
    (g : Γ) : (mat σ g).trace = (mat ρ g).trace + ∑ c : Fin t, ((χ ((c : ℕ) + 1) g : Aˣ) : A) := by
  obtain ⟨e, he⟩ := h
  apply IsFractionRing.injective A (FractionRing A)
  let d : Fin t → FractionRing A := fun c => toFr A ((χ ((c : ℕ) + 1) g : Aˣ) : A)
  have h1 : Matrix.toLin' ((mat σ g).map (toFr A)) =
      e.symm.conj ((Matrix.toLin' ((mat ρ g).map (toFr A))).prodMap (Matrix.toLin' (Matrix.diagonal d))) := by
    apply LinearMap.ext
    intro u
    apply e.injective
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm,
      LinearMap.prodMap_apply]
    refine (he g u).trans ?_
    ext c
    · rfl
    · simp [Matrix.mulVec_diagonal, d]
  have h2 := congrArg (LinearMap.trace _ _) h1
  rw [LinearMap.trace_conj', LinearMap.trace_prodMap', Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq,
    Matrix.trace_toLin'_eq, Matrix.trace_diagonal] at h2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum, AddMonoidHom.map_trace, AddMonoidHom.map_trace]
  exact h2

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem charZero_O (N : NData R H what₂) (A : NAut N) (i : N.Loc) : CharZero (N.O i) :=
  (iotaO N A i).charZero

theorem l_mem_maximalIdeal (N : NData R H what₂) (A : NAut N) (i : N.Loc) :
    ((N.l i : ℕ) : N.O i) ∈ IsLocalRing.maximalIdeal (N.O i) := by
  have hinj : Function.Injective (algebraMap ℤ_[N.l i] (N.O i)) := by
    intro x y h
    have hx := A.iotaQ_alg i x
    rw [h, A.iotaQ_alg i y] at hx
    exact (Subtype.ext ((algebraMap ℚ_[N.l i] (Qbar (N.l i))).injective hx)).symm
  have : FaithfulSMul ℤ_[N.l i] (N.O i) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have h : ((N.l i : ℕ) : ℤ_[N.l i]) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := PadicInt.p_nonunit
  have := map_nonunit (algebraMap ℤ_[N.l i] (N.O i)) _ h
  rwa [map_natCast] at this

variable {N₀ N₁ : NData R H what₂} {A₀ : NAut N₀} {A₁ : NAut N₁} {i₀ : N₀.Loc} {i₁ : N₁.Loc}

theorem isLocalHom_φ (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : IsLocalHom a.φ := by
  have := charZero_O N₀ A₀ i₀
  have hl : (N₁.l i₁).Prime := Fact.out
  refine isLocalHom_of_nonunit a.φ (a := ((N₁.l i₁ : ℕ) : N₀.O i₀)) (Nat.cast_ne_zero.2 hl.ne_zero) ?_
  rw [map_natCast]
  exact l_mem_maximalIdeal N₁ A₁ i₁

theorem continuous_φ (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : Continuous a.φ :=
  haveI := isLocalHom_φ a
  continuous_of_isLocalHom (N₀.O_adic i₀) (N₁.O_adic i₁) a.φ

theorem trace_eq (hC : GlobalTheory.TwSys.Cheb) (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) (x : N₁.X i₁)
    (r₀ : GE N₀ →* GL (Fin R.nV) (N₀.O i₀)) (r₁ : GE N₁ →* GL (Fin R.nV) (N₁.O i₁))
    (h₀ : IsHeckeGalois N₀ i₀ (a.e x) r₀) (h₁ : IsHeckeGalois N₁ i₁ x r₁) (g : GE N₁) :
    a.φ (mat r₀ (a.γ g)).trace = (mat r₁ g).trace := by
  haveI := (N₁.O_complete i₁).toIsHausdorff
  haveI : T2Space (N₁.O i₁) := (N₁.O_adic i₁).isHausdorff_iff.1 inferInstance
  refine congrFun (GlobalTheory.BlockComplement.AE.eq_of_continuous (N := N₁) hC
    (f := fun g => a.φ (mat r₀ (a.γ g)).trace) (f' := fun g => (mat r₁ g).trace)
    ((continuous_φ a).comp (h₀.1.matrix_trace.comp a.γ_cont)) h₁.1.matrix_trace ?_) g
  filter_upwards [GlobalTheory.BlockComplement.eventually_out i₁] with w h hw B σ hB hσ
  obtain ⟨B₀, hB₀, hσ₀⟩ := (a.frob w σ).1 ⟨B, hB, hσ⟩
  have e₀ := h₀.2.2 w ((a.out w).1 (h hw)) B₀ _ hB₀ hσ₀
  have e₁ := h₁.2.2 w (h hw) B σ hB hσ
  rw [GlobalTheory.CoefDuty.Model.heckePol_map a x w (h hw), ← e₀, ← Matrix.charpoly_map] at e₁
  rw [AddMonoidHom.map_trace, Matrix.trace_eq_neg_charpoly_nextCoeff, Matrix.trace_eq_neg_charpoly_nextCoeff, e₁]

end Record

theorem live_of_locExt : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N₀ N₁ : NData R H what₂) (A₀ : NAut N₀) (A₁ : NAut N₁) (i₀ : N₀.Loc) (i₁ : N₁.Loc), LocExt N₀ N₁ A₀ A₁ i₀ i₁ → (∃ r, GoodR N₀ i₀ r) → ZDecomp N₀ i₀ → Live N₁ i₁ → Live N₀ i₀ := by
  rintro hC R H what₂ N₀ N₁ A₀ A₁ i₀ i₁ a ⟨r₀, hr₀⟩ hZ ⟨π, hπ, r, ρ, hr, hd, habs⟩
  have hπ₀ := (a.Z π).1 hπ
  obtain ⟨ρ₀, hd₀⟩ := hZ _ hπ₀ _ (hr₀ _)
  refine ⟨_, hπ₀, _, ρ₀, hr₀ _, hd₀, ?_⟩
  have htr : ∀ g, a.φ (mat ρ₀ (a.γ g)).trace = (mat ρ g).trace := by
    intro g
    have h := trace_eq hC a π _ r (hr₀ _) hr g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [trace_of_isDecomp _ _ _ hd₀, trace_of_isDecomp _ _ _ hd, map_add (f := _), map_sum,
      Finset.sum_congr rfl fun (c : Fin R.t) _ => a.chi ((c : ℕ) + 1) (by omega) c.2 g] at h
    exact add_right_cancel h
  haveI := isLocalHom_φ a
  have hpos := pos_of_absIrrSub _ habs
  haveI : Nonempty (Fin R.r) := ⟨⟨0, hpos⟩⟩
  refine absIrrSub_of_span_eq_top hpos _ (span_eq_top_of_map (IsLocalRing.ResidueField.map a.φ) _ ?_)
  have h := span_eq_top_of_trace_eq
    ((mapRep (IsLocalRing.ResidueField.map a.φ) (mapRep (IsLocalRing.residue (N₀.O i₀)) ρ₀)).comp a.γ.toMonoidHom)
    (mapRep (IsLocalRing.residue (N₁.O i₁)) ρ) (fun g => ?_) (GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ habs)
  · rw [eq_top_iff, ← h]
    refine Submodule.span_mono ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨a.γ g, (mat_mapRep _ _ _).symm⟩
  · change (mat (mapRep (IsLocalRing.ResidueField.map a.φ) (mapRep (IsLocalRing.residue (N₀.O i₀)) ρ₀))
      (a.γ g)).trace = _
    rw [mat_mapRep, mat_mapRep, mat_mapRep, ← AddMonoidHom.map_trace, ← AddMonoidHom.map_trace,
      ← AddMonoidHom.map_trace, ← htr, IsLocalRing.ResidueField.map_residue]

end GlobalTheory.LiveDescent

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantLogSemistableToDeRham
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogTiltKummerCoboundaryBdR
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogTiltKummerCoboundaryBdR
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exists_log_tilt_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ u : P.R.BdR, ∀ g : GQ l, P.actQdR g u = u + P.ιB ((kummer P g : ℚ_[l]) • P.tB) := by
  intro l _ P AI T
  obtain ⟨Co, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨ϖ, hr⟩ := exists_tilt (lRoot l) (lRoot_succ l) l (lRoot_zero l)
  have hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l) := Subtype.ext (by
    have := hr 0
    rw [lRoot_zero, map_natCast] at this
    exact this.trans (SubringClass.coe_natCast _ _).symm)
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_logOnePlus_kerTheta_deRhamPlus l (beta ϖ) (by
    rw [GlobalTheory.T.kerP_eq_span_beta_of_untilt_eq l ϖ hϖ]; exact Ideal.mem_span_singleton_self _)
  have hg := GlobalTheory.T.galois_logTeichmullerRatio_eq_add_kummer l P Co hC.ζ ϖ hr hϖ u hu
  have hct : ∀ g : GQ l, T.eD (P.ιB ((kummer P g : ℚ_[l]) • P.tB)) =
      algebraMap (Per.BdRp l) (Per.BdR l)
        (Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t)) := by
    intro g
    rw [hC.ι, Algebra.smul_def, map_mul, T.zB, hC.t, ← Co.ι_j]
    simp only [Core.tB, GlobalTheory.RingIface.zB_alg, map_mul]
  refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) u), fun g => ?_⟩
  apply T.eD.injective
  rw [T.actD, RingEquiv.apply_symm_apply, map_add (f := _), RingEquiv.apply_symm_apply, hct]
  rw [show Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) u) =
    algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g u) from GlobalTheory.MemLoc.ActLaws.σD_alg _ _, hg, map_add]

end GlobalTheory.PMon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogTiltKummerCoboundaryBdRStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_log_tilt_kummerCoboundary_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ u : P.R.BdR, ∀ g : GQ l, P.actQdR g u = u + P.ιB ((kummer P g : ℚ_[l]) • P.tB) := by
  first | exact @GlobalTheory.PMon.exists_log_tilt_BdR | exact GlobalTheory.PMon.exists_log_tilt_BdR | (intros; apply GlobalTheory.PMon.exists_log_tilt_BdR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantLogSemistableToDeRham
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BstLog

theorem iota_exists : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ ι : Bst P →ₐ[ℚ_[l]] P.R.BdR, (∀ b, ι (Polynomial.C b) = P.ιB b) ∧
      (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) := by
  intro l _ P AI T
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_log_tilt_kummerCoboundary_BdR l P AI T
  have hcomm : ∀ (g : GQ l) (z : P.R.B), P.ιB (P.actQ g z) = P.actQdR g (P.ιB z) := by
    intro g z
    have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ z
    rwa [P.PD_ι, P.PD_actB, P.PD_ι, P.PD_actdR] at this
  let ι : Bst P →ₐ[ℚ_[l]] P.R.BdR := Polynomial.eval₂AlgHom P.ιB u (fun _ => Commute.all _ _)
  refine ⟨ι, fun b => Polynomial.eval₂_C _ _, fun g x => ?_⟩
  have h : ι.comp (actSt P g) = ((P.actQdR g : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →ₐ[ℚ_[l]] P.R.BdR).comp ι := by
    apply Polynomial.algHom_ext'
    · ext b
      show Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (actSt P g (Polynomial.C b)) =
        P.actQdR g (Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (Polynomial.C b))
      rw [actSt_C, Polynomial.eval₂_C, Polynomial.eval₂_C]
      exact hcomm g b
    · show Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (actSt P g Polynomial.X) =
        P.actQdR g (Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u Polynomial.X)
      rw [actSt_X, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, hu]
      rfl
  exact congrArg (fun F : Bst P →ₐ[ℚ_[l]] P.R.BdR => F x) h

end GlobalTheory.BstLog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantLogSemistableToDeRhamStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_log_semistable_to_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ ι : Bst P →ₐ[ℚ_[l]] P.R.BdR, (∀ b, ι (Polynomial.C b) = P.ιB b) ∧ (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) := by
  first | exact @GlobalTheory.BstLog.iota_exists | exact GlobalTheory.BstLog.iota_exists | (intros; apply GlobalTheory.BstLog.iota_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAtAll
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTwistRepDualOfPairing
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DualOne

theorem isTwistRep_dual_of_pairing {G L : Type} [Group G] [Field L]
    {V : Type} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    {V' : Type} [AddCommGroup V'] [Module L V'] [FiniteDimensional L V']
    (ρ : Representation L G V) (ρ' : Representation L G V') (χ : G →* Lˣ)
    (m : V →ₗ[L] V' →ₗ[L] L)
    (h1 : ∀ g x y, m (ρ g x) (ρ' g y) = ((χ g : Lˣ) : L) * m x y)
    (h2 : ∀ y, (∀ x, m x y = 0) → y = 0) (h3 : finrank L V = finrank L V') :
    IsTwistRep χ ρ.dual ρ' := by
  have hinj : Function.Injective m.flip := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    exact h2 y fun x => by simpa using LinearMap.congr_fun hy x
  have hdim : finrank L V' = finrank L (Module.Dual L V) := by
    rw [Subspace.dual_finrank_eq, h3]
  let f : V' ≃ₗ[L] Module.Dual L V := m.flip.linearEquivOfInjective hinj hdim
  have hf : ∀ y x, f y x = m x y := fun y x => rfl
  refine ⟨f.symm, fun g φ => ?_⟩
  obtain ⟨y, rfl⟩ := f.surjective φ
  apply f.injective
  rw [map_smul, f.apply_symm_apply, f.symm_apply_apply]
  ext x
  have hx : ρ g (ρ g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have := h1 g (ρ g⁻¹ x) y
  rw [hx] at this
  rw [hf, this, LinearMap.smul_apply, Representation.dual_apply, smul_eq_mul]
  congr 1

theorem isCrys_of_isDual1 : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (m : V →ₗ[↥LL.1] V' →ₗ[↥LL.1] ↥LL.1), IsDual1 (P.PD K) ρ ρ' m → IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ' := by
  intro l _ P AI hT K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' m hD hρ
  obtain ⟨h1, -, h2, h3⟩ := hD
  have htw := isTwistRep_dual_of_pairing ρ ρ' _ m h1 h2 h3
  have hreg := (GlobalTheory.MemLoc.tied_regular_and_onto l P AI hT).1
  have hdual := GlobalTheory.Per.TiedDual.tied_isCrys_dual l P AI hT hreg K LL V ρ hρ
  have hcyc := (GlobalTheory.CycPow.cyc_zpow_crys_dR_jump l P AI hT K LL 1).1
  rw [zpow_one] at hcyc
  exact (GlobalTheory.T.crystalline_twist_crystallineCharacter_jumps_shift l P AI hT K LL _ ρ.dual V' ρ' _ htw hcyc hdual).1

end GlobalTheory.DualOne
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineAll

theorem split_equiv {G L V₀ V₁ V₂ : Type} [Group G] [Field L] [AddCommGroup V₀] [Module L V₀]
    [AddCommGroup V₁] [Module L V₁] [AddCommGroup V₂] [Module L V₂]
    (ρ₀ : Representation L G V₀) (ρ₁ : Representation L G V₁) (ρ₂ : Representation L G V₂)
    (ι : V₀ →ₗ[L] V₁) (π : V₁ →ₗ[L] V₂) (hι : ∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x))
    (hi : Function.Injective ι) (hk : LinearMap.range ι = LinearMap.ker π)
    (s : V₂ →ₗ[L] V₁) (hs : ∀ g x, s (ρ₂ g x) = ρ₁ g (s x)) (hps : ∀ x, π (s x) = x) :
    ∃ e : V₁ ≃ₗ[L] (V₀ × V₂), ∀ g v, e (ρ₁ g v) = (ρ₀ g (e v).1, ρ₂ g (e v).2) := by
  let f : V₀ × V₂ →ₗ[L] V₁ := ι.coprod s
  have hf : ∀ a b, f (a, b) = ι a + s b := fun a b => rfl
  have hπι : ∀ a, π (ι a) = 0 := fun a => by
    have : ι a ∈ LinearMap.ker π := hk ▸ LinearMap.mem_range_self ι a
    exact this
  have hbij : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨a, b⟩ h
      rw [hf] at h
      have hb : b = 0 := by
        have := congrArg π h
        rwa [map_add, hπι, hps, zero_add, map_zero] at this
      subst hb
      rw [map_zero, add_zero] at h
      have ha : a = 0 := hi (by rw [h, map_zero])
      rw [ha]; rfl
    · intro z
      have hz : z - s (π z) ∈ LinearMap.range ι := by
        rw [hk, LinearMap.mem_ker, map_sub, hps, sub_self]
      obtain ⟨a, ha⟩ := hz
      exact ⟨(a, π z), by rw [hf, ha, sub_add_cancel]⟩
  let e := (LinearEquiv.ofBijective f hbij).symm
  refine ⟨e, fun g v => ?_⟩
  apply (LinearEquiv.ofBijective f hbij).injective
  change f (e (ρ₁ g v)) = f (ρ₀ g (e v).1, ρ₂ g (e v).2)
  have h1 : ∀ w, f (e w) = w := fun w => (LinearEquiv.ofBijective f hbij).apply_symm_apply w
  rw [h1, hf, hι, hs, ← map_add (f := _), ← hf]
  have : ((e v).1, (e v).2) = e v := rfl
  rw [this, h1]

theorem fontaineAt_all : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K LL : FinExt l),
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt ((D.loc l).PD K) ↥LL.1 ↥(OL LL) := by
  intro D l _ K LL
  have T := D.locT l
  unfold Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A₀ A₁ A₂ ι π hι hπ hi hs hk
    refine ⟨?_, ?_⟩
    · intro h1
      have c0 := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL A₀.V A₀.ρ A₁.V A₁.ρ ι hι).1 hi h1
      have c2 := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL A₁.V A₁.ρ A₂.V A₂.ρ π hπ).2 hs h1).1
      have d1 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) T K LL A₁.V A₁.ρ h1).1
      obtain ⟨-, -, hm⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l (D.loc l) (D.locA l) T K LL A₀.V A₀.ρ A₁.V A₁.ρ
        A₂.V A₂.ρ ι π hι hπ hi hs hk d1
      exact ⟨c0, c2, fun τ a => (hm τ a).2.1⟩
    · rintro ⟨s, hs', hps⟩ h0 h2
      obtain ⟨e, he⟩ := split_equiv A₀.ρ A₁.ρ A₂.ρ ι π hι hi hk s hs' hps
      exact ((GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l (D.loc l) (D.locA l) T K LL A₁.V A₁.ρ A₀.V A₀.ρ
        A₂.V A₂.ρ e he).2.1).2 ⟨h0, h2⟩
  · intro A A' χ htw hχ hA
    exact GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l (D.loc l) (D.locA l) T K LL A.V A.ρ A'.V A'.ρ χ htw hχ hA
  · intro A A' P hD hA
    exact GlobalTheory.DualOne.isCrys_of_isDual1 l (D.loc l) (D.locA l) T K LL A.V A.ρ A'.V A'.ρ P hD hA
  · intro A hA
    exact (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) T K LL A.V A.ρ hA).1

end GlobalTheory.FontaineAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
noncomputable section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Polynomial
open Formalism.MainNotions.N (GRep)

namespace GlobalTheory.FullCharpoly

section Lat
variable {G LL O V W : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W]
  {ρ : Representation LL G V} {σ : Representation LL G W}

def mapLat (e : V ≃ₗ[LL] W) (he : ∀ g x, e (ρ g x) = σ g (e x)) (L : Lattice (O := O) ρ) :
    Lattice (O := O) σ where
  T := L.T.map ((e.restrictScalars O : V ≃ₗ[O] W) : V →ₗ[O] W)
  stable := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, L.stable g x hx, he g x⟩
  fg := L.fg.map _
  free := by
    have := L.free
    exact Module.Free.of_equiv ((e.restrictScalars O).submoduleMap L.T)
  span := by
    have h : ((L.T.map ((e.restrictScalars O : V ≃ₗ[O] W) : V →ₗ[O] W) : Submodule O W) : Set W) =
        (e : V →ₗ[LL] W) '' (L.T : Set V) := rfl
    rw [h, Submodule.span_image, L.span, Submodule.map_top, LinearEquiv.range]

variable {E M : Type} [AddCommGroup E] [Module O E] [AddCommGroup M] [Module O M]

theorem quot_equiv_iff (L₁ L₂ : Lattice (O := O) ρ) (act : G → E → E) (π : Representation O G M)
    (p : E →ₗ[O] M) (hp : Function.Surjective p) (hact : ∀ g x, p (act g x) = π g (p x)) :
    (∃ e : (E ⧸ LinearMap.ker p) ≃ₗ[O] (↥L₁.T ⧸ L₂.T.comap L₁.T.subtype),
      ∀ (g : G) (x : E) (y : ↥L₁.T), e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
        e (Submodule.Quotient.mk (act g x)) = Submodule.Quotient.mk ⟨ρ g y, L₁.stable g y y.2⟩) ↔
    ∃ q : ↥L₁.T →ₗ[O] M, Function.Surjective q ∧ (∀ g x, q (latRep L₁ g x) = π g (q x)) ∧
      ∀ x, q x = 0 ↔ (x : V) ∈ L₂.T := by
  constructor
  · rintro ⟨e, he⟩
    let Φ := p.quotKerEquivOfSurjective hp
    refine ⟨(Φ.toLinearMap.comp e.symm.toLinearMap).comp (L₂.T.comap L₁.T.subtype).mkQ, ?_, ?_, ?_⟩
    · exact Φ.surjective.comp (e.symm.surjective.comp (Submodule.mkQ_surjective _))
    · intro g y
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk y))
      have h1 : e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
        rw [hx, LinearEquiv.apply_symm_apply]
      have h3 : latRep L₁ g y = ⟨ρ g y, L₁.stable g y y.2⟩ := Subtype.ext (latRep_apply L₁ g y)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply]
      rw [h3, ← he g x y h1, LinearEquiv.symm_apply_apply, ← hx]
      simp only [Φ, LinearMap.quotKerEquivOfSurjective_apply_mk]
      exact hact g x
    · intro y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply,
        LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.coe_subtype]
  · rintro ⟨q, hq, hqe, hqk⟩
    have hker : LinearMap.ker q = L₂.T.comap L₁.T.subtype := by
      ext y
      simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype, hqk]
    let ψ : M ≃ₗ[O] (↥L₁.T ⧸ L₂.T.comap L₁.T.subtype) :=
      (q.quotKerEquivOfSurjective hq).symm.trans (Submodule.quotEquivOfEq _ _ hker)
    have hψ : ∀ y, ψ (q y) = Submodule.Quotient.mk y := by
      intro y
      simp only [ψ, LinearEquiv.trans_apply]
      rw [(LinearEquiv.symm_apply_eq _).2 (LinearMap.quotKerEquivOfSurjective_apply_mk q hq y).symm]
      rfl
    have hΦ : ∀ x, p.quotKerEquivOfSurjective hp (Submodule.Quotient.mk x) = p x :=
      LinearMap.quotKerEquivOfSurjective_apply_mk p hp
    refine ⟨(p.quotKerEquivOfSurjective hp).trans ψ, fun g x y h => ?_⟩
    simp only [LinearEquiv.trans_apply, hΦ] at h ⊢
    have hxy : p x = q y := ψ.injective (h.trans (hψ y).symm)
    have h3 : latRep L₁ g y = ⟨ρ g y, L₁.stable g y y.2⟩ := Subtype.ext (latRep_apply L₁ g y)
    rw [hact, hxy, ← hqe, h3, hψ]

end Lat

section Sum
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL] {n : ℕ}
    {emb : ZMod n → (K₀ →ₐ[Qp] LL)} {lam : O} {jT : ZMod n → ℤ → ℤ} {cT : G → Polynomial LL}

def ofFull (F : tableLineDegreeTwo.FullRep PD emb lam jT cT) : GRep G Qp LL O where
  V := F.V
  cadd := IsModuleTopology.toContinuousAdd LL F.V
  csmul := by have := IsModuleTopology.toContinuousSMul LL F.V; infer_instance
  ρ := F.ρ
  cont := F.full.1

def sumFull {m : ℕ} (F : Fin m → tableLineDegreeTwo.FullRep PD emb lam jT cT) : GRep G Qp LL O where
  V := ∀ j, (F j).V
  cadd := IsModuleTopology.toContinuousAdd LL _
  csmul := by have := IsModuleTopology.toContinuousSMul LL (∀ j, (F j).V); infer_instance
  ρ := tableLineDegreeTwo.piRep F
  cont := fun x => continuous_pi fun j => (F j).full.1 (x j)

def toFull (A : GRep G Qp LL O) (h : tableLineDegreeTwo.IsFull PD emb lam jT cT A.ρ) : tableLineDegreeTwo.FullRep PD emb lam jT cT where
  V := A.V
  ρ := A.ρ
  full := h

private theorem mapLattice_quotient_of_equivariant_equiv {G LL O V W M : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W]
    {ρ : Representation LL G V} {σ : Representation LL G W} [AddCommGroup M] [Module O M]
    (π : Representation O G M) (e : V ≃ₗ[LL] W) (he : ∀ g x, e (ρ g x) = σ g (e x))
    (L₁ L₂ : Lattice (O := O) ρ) (q : ↥L₁.T →ₗ[O] M) (hq : Function.Surjective q)
    (hqe : ∀ g x, q (latRep L₁ g x) = π g (q x)) (hqk : ∀ x, q x = 0 ↔ (x : V) ∈ L₂.T) :
    ∃ q' : ↥(mapLat e he L₁).T →ₗ[O] M, Function.Surjective q' ∧
      (∀ g x, q' (latRep (mapLat e he L₁) g x) = π g (q' x)) ∧
      ∀ x, q' x = 0 ↔ (x : W) ∈ (mapLat e he L₂).T := by
  let s : ↥L₁.T ≃ₗ[O] ↥(mapLat e he L₁).T := (e.restrictScalars O).submoduleMap L₁.T
  have hsx : ∀ x, (s x : W) = e x := fun x => rfl
  refine ⟨q.comp s.symm.toLinearMap, hq.comp s.symm.surjective, ?_, ?_⟩
  · intro g y
    obtain ⟨x, rfl⟩ := s.surjective y
    have hs : latRep (mapLat e he L₁) g (s x) = s (latRep L₁ g x) := by
      apply Subtype.ext
      rw [latRep_apply, hsx, hsx, latRep_apply, he]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hs, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact hqe g x
  · intro y
    obtain ⟨x, rfl⟩ := s.surjective y
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hqk, hsx]
    change (x : V) ∈ L₂.T ↔ e x ∈ L₂.T.map ((e.restrictScalars O : V ≃ₗ[O] W) : V →ₗ[O] W)
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨z, hz, hze⟩
      have hzx : z = (x : V) := e.injective hze
      rwa [← hzx]


omit [IsTopologicalRing LL] in
theorem admissible_quotient_ker_iff_full_lattices {E M : Type} [AddCommGroup E] [Module O E] [AddCommGroup M] [Module O M]
    (act : G → E → E) (π : Representation O G M)
    (p : E →ₗ[O] M) (hp : Function.Surjective p) (hact : ∀ g x, p (act g x) = π g (p x)) :
    tableLineDegreeTwo.AdmQ PD emb lam jT cT act (LinearMap.ker p) ↔
      ∃ (μ : ℕ) (F : Fin μ → GRep G Qp LL O) (A : GRep G Qp LL O)
      (e : A.V ≃ₗ[LL] (∀ j, (F j).V)) (L₁ L₂ : Lattice (O := O) A.ρ) (q : ↥L₁.T →ₗ[O] M),
      (∀ j, tableLineDegreeTwo.IsFull PD emb lam jT cT (F j).ρ) ∧ (∀ g x j, e (A.ρ g x) j = (F j).ρ g (e x j)) ∧ L₂.T ≤ L₁.T ∧
      Function.Surjective q ∧ (∀ g x, q (latRep L₁ g x) = π g (q x)) ∧ ∀ x, q x = 0 ↔ (x : A.V) ∈ L₂.T := by
  constructor
  · rintro ⟨m, F, L₁, L₂, hle, e, he⟩
    obtain ⟨q, hq, hqe, hqk⟩ := (quot_equiv_iff L₁ L₂ act π p hp hact).1 ⟨e, he⟩
    exact ⟨m, fun j => ofFull (F j), sumFull F, LinearEquiv.refl LL _, L₁, L₂, q,
      fun j => (F j).full, fun g x j => rfl, hle, hq, hqe, hqk⟩
  · rintro ⟨μ, F, A, e, L₁, L₂, q, hF, he, hle, hq, hqe, hqk⟩
    let F' : Fin μ → tableLineDegreeTwo.FullRep PD emb lam jT cT := fun j => toFull (F j) (hF j)
    let e' : A.V ≃ₗ[LL] (∀ j, (F' j).V) := e
    have he' : ∀ g x, e' (A.ρ g x) = tableLineDegreeTwo.piRep F' g (e' x) := fun g x => funext fun j => he g x j
    obtain ⟨q', hq', hqe', hqk'⟩ := mapLattice_quotient_of_equivariant_equiv π e' he' L₁ L₂ q hq hqe hqk
    exact ⟨μ, F', mapLat e' he' L₁, mapLat e' he' L₂, Submodule.map_mono hle,
      (quot_equiv_iff _ _ act π p hp hact).2 ⟨q', hq', hqe', hqk'⟩⟩


omit [TopologicalSpace G] [TopologicalSpace LL] [IsTopologicalRing LL] in
theorem resPoly_eq {V : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (χ : ℕ → G →* Oˣ) (t : ℕ) :
    tableLineDegreeTwo.resPoly ρ χ t = fun g => LinearMap.charpoly (ρ g) *
      ∏ c : Fin t, (X - C (algebraMap O LL (χ (c.val + 1) g))) := by
  funext g
  simp only [tableLineDegreeTwo.resPoly]
  congr 1
  symm
  refine Finset.prod_bij (fun (c : Fin t) _ => c.val + 1) ?_ ?_ ?_ ?_
  · intro c _
    simp only [Finset.mem_Icc]
    omega
  · intro a _ b _ hab
    exact Fin.ext (by simpa using hab)
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    exact ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, by simp only; omega⟩
  · intro c _
    simp [tableLineDegreeTwo.charL]

end Sum

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

theorem isFull_iff_polyFull (jT : ZMod S.n → ℤ → ℤ) (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O) :
    tableLineDegreeTwo.IsFull (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) A.ρ ↔ PolyFull S jT A := by
  unfold tableLineDegreeTwo.IsFull PolyFull
  rw [resPoly_eq]
  simp only [tableLineDegreeTwo.Over, AlgHom.ext_iff, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  exact ⟨fun h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨A.cont, h.1, h.2.1, h.2.2⟩⟩

theorem admissibleQuotient_iff_admissible_module : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (jT : ZMod S.n → ℤ → ℤ), (∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a) → ∀ (E M : Type) [AddCommGroup E] [Module S.O E] [AddCommGroup M] [Module S.O M] (act : S.G → E → E) (π : Representation S.O S.G M) (p : E →ₗ[S.O] M), Function.Surjective p → (∀ g x, p (act g x) = π g (p x)) → (tableLineDegreeTwo.AdmQ (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) act (LinearMap.ker p) ↔ S.admitted π) := by
  intro l _ P S jT hj E M _ _ _ _ act π p hp hact
  refine (admissible_quotient_ker_iff_full_lattices act π p hp hact).trans (Iff.trans ?_ (admissibleModule_iff_lattice_quotients S hj π).symm)
  constructor
  · rintro ⟨μ, F, A, e, L₁, L₂, q, hF, h⟩
    exact ⟨μ, F, A, e, L₁, L₂, q, fun j => (isFull_iff_polyFull S jT (F j)).1 (hF j), h⟩
  · rintro ⟨μ, F, A, e, L₁, L₂, q, hF, h⟩
    exact ⟨μ, F, A, e, L₁, L₂, q, fun j => (isFull_iff_polyFull S jT (F j)).2 (hF j), h⟩

end GlobalTheory.FullCharpoly
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixCrystallineModuleOverWitt
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixCrystallineModuleOverWitt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SeedF

variable {l : ℕ} [Fact l.Prime]

theorem aw_injective (C : Core l) (a : ℕ) [NeZero a] :
    Function.Injective ((Per.aB l).comp (wA l a).toRingHom) := by
  haveI : Nontrivial (Per.BdR l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1.nontrivial
  haveI : Nontrivial (Per.Bcris l) := C.ι.domain_nontrivial
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨m, b, rfl⟩ := WittVector.exists_eq_pow_p_mul' x h0
  rw [map_mul, map_pow, map_natCast] at hx
  have hu : IsUnit (((l : ℕ) : Per.Bcris l) ^ m * ((Per.aB l).comp (wA l a).toRingHom) (b : Wq l a)) :=
    ((isUnit_l_Bcris l).pow m).mul (b.isUnit.map _)
  exact hu.ne_zero hx

theorem clear_den {d : ℕ} {R : Type} [CommRing R] (f : R →+* Per.Bcris l)
    (G : Matrix (Fin d) (Fin d) (Per.Bcris l))
    (h : ∀ i j, ∃ (n : ℕ) (w : R), ((l : ℕ) : Per.Bcris l) ^ n * G i j = f w) :
    ∃ (k : ℕ) (F : Matrix (Fin d) (Fin d) R), ((l : ℕ) : Per.Bcris l) ^ k • G = F.map f := by
  choose n w hw using h
  refine ⟨Finset.univ.sup (fun p : Fin d × Fin d => n p.1 p.2),
    Matrix.of fun i j => ((l : ℕ) : R) ^ (Finset.univ.sup (fun p : Fin d × Fin d => n p.1 p.2) - n i j) * w i j, ?_⟩
  ext i j
  have hle : n i j ≤ Finset.univ.sup (fun p : Fin d × Fin d => n p.1 p.2) :=
    Finset.le_sup (f := fun p : Fin d × Fin d => n p.1 p.2) (Finset.mem_univ (i, j))
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, map_mul, map_pow, map_natCast, smul_eq_mul,
    ← hw]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem inv_entries {K : FinExt l} {d : ℕ} (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l]))
    (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)) (hUU : U * U' = 1)
    (hρ : ∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) (g : ↥(GK K)) :
    (U' * U.map (Per.φB l)).map (Per.σB (g : GQ l)) = U' * U.map (Per.φB l) ∧
    (U'.map (Per.φB l) * U).map (Per.σB (g : GQ l)) = U'.map (Per.φB l) * U := by
  have hU'U : U' * U = 1 := mul_eq_one_comm.1 hUU
  have hR : (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U := hρ g
  have hσ1 : U.map (Per.σB (g : GQ l)) * U'.map (Per.σB (g : GQ l)) = 1 := by
    rw [← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _)]
  have hσU' : U'.map (Per.σB (g : GQ l)) = U' * (ρ g).map (Per.zB l) := by
    calc U'.map (Per.σB (g : GQ l))
        = (U' * (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l))) * U'.map (Per.σB (g : GQ l)) := by
          rw [mul_assoc U', hR, hU'U, one_mul]
      _ = U' * (ρ g).map (Per.zB l) := by rw [mul_assoc, hσ1, mul_one]
  have hφR : ((ρ g).map (Per.zB l)).map (Per.φB l) = (ρ g).map (Per.zB l) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [GlobalTheory.RingIface.zB_eq_aB_zA, (ActLaws.act_laws l).2.2.2.2.2.2.1, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1]
  have hcomm : ∀ M : Matrix (Fin d) (Fin d) (Per.Bcris l),
      (M.map (Per.φB l)).map (Per.σB (g : GQ l)) = (M.map (Per.σB (g : GQ l))).map (Per.φB l) := by
    intro M
    ext i j
    simp only [Matrix.map_apply]
    exact ((ActLaws.act_laws l).2.2.2.2.1 _ _).symm
  constructor
  · calc (U' * U.map (Per.φB l)).map (Per.σB (g : GQ l))
        = U'.map (Per.σB (g : GQ l)) * (U.map (Per.σB (g : GQ l))).map (Per.φB l) := by
          rw [Matrix.map_mul, hcomm]
      _ = U' * (((ρ g).map (Per.zB l)).map (Per.φB l) * (U.map (Per.σB (g : GQ l))).map (Per.φB l)) := by
          rw [hσU', hφR, mul_assoc]
      _ = U' * U.map (Per.φB l) := by rw [← Matrix.map_mul, hR]
  · calc (U'.map (Per.φB l) * U).map (Per.σB (g : GQ l))
        = (U'.map (Per.σB (g : GQ l))).map (Per.φB l) * U.map (Per.σB (g : GQ l)) := by
          rw [Matrix.map_mul, hcomm]
      _ = U'.map (Per.φB l) * ((ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l))) := by
          rw [hσU', Matrix.map_mul, hφR, mul_assoc]
      _ = U'.map (Per.φB l) * U := by rw [hR]

theorem frob_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), C.InvB →
    ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)),
    U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) →
    ∃ (c₁ c₃ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)),
      F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧
      (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) := by
  intro l _ K bk C hC d ρ U U' hUU hρ
  have hU'U : U' * U = 1 := mul_eq_one_comm.1 hUU
  have hent : ∀ G : Matrix (Fin d) (Fin d) (Per.Bcris l), (∀ g : ↥(GK K), G.map (Per.σB (g : GQ l)) = G) →
      ∀ i j, ∃ (n : ℕ) (w : Wq l bk.a),
        ((l : ℕ) : Per.Bcris l) ^ n * G i j = ((Per.aB l).comp (wA l bk.a).toRingHom) w := by
    intro G hG i j
    obtain ⟨x, hxK, hx⟩ := hC K (G i j) fun g hg => by
      have := congrFun (congrFun (hG ⟨g, hg⟩) i) j
      simpa only [Matrix.map_apply] using this
    obtain ⟨n, w, hw⟩ := GlobalTheory.T.exists_pow_mul_unramified_eq_witt_bcris l K bk C x hxK
    exact ⟨n, w, by rw [← hx, hw]; rfl⟩
  obtain ⟨k, F, hF⟩ := clear_den _ _ (hent _ fun g => (inv_entries ρ U U' hUU hρ g).1)
  obtain ⟨k', F', hF'⟩ := clear_den _ _ (hent _ fun g => (inv_entries ρ U U' hUU hρ g).2)
  have hGG : (U' * U.map (Per.φB l)) * (U'.map (Per.φB l) * U) = 1 := by
    rw [mul_assoc, ← mul_assoc (U.map _), ← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _),
      one_mul, hU'U]
  refine ⟨k, k + k', F, F', ?_, ?_⟩
  · apply Matrix.map_injective (aw_injective C bk.a)
    change (F * F').map ((Per.aB l).comp (wA l bk.a).toRingHom) =
      (((l : ℕ) : Wq l bk.a) ^ (k + k') • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a))).map
        ((Per.aB l).comp (wA l bk.a).toRingHom)
    rw [Matrix.map_mul, ← hF, ← hF', Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, hGG]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  · rw [← hF, Matrix.mul_smul, ← mul_assoc, hUU, one_mul]

end GlobalTheory.SeedF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixCrystallineModuleOverWittStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobeniusMatrix_crystallineModule_over_witt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), C.InvB → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → ∃ (c₁ c₃ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)), F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧ (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) := by
  first | exact @GlobalTheory.SeedF.frob_matrix | exact GlobalTheory.SeedF.frob_matrix | (intros; apply GlobalTheory.SeedF.frob_matrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XNygaardExtComesFromBaseField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XNygaardExtComesFromBaseField
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

noncomputable section

namespace GlobalTheory.NL.XNTransfer

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n}

theorem exists_aN_iff (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (a : LetA O n)
    (r : RA) (hr : E.io a = r) (w : TW RW T) :
    (∃ z ∈ aN W T a, E.jD T z = w) ↔ ∃ y ∈ E.jD T '' (W.N T : Set (W.DD T)), w = inclR r • y := by
  have hs : ∀ x : W.DD T, E.jD T (a • x) = inclR r • E.jD T x := fun x => by
    rw [← algebraMap_smul W.EE a x, E.jD_smul, E.ioE_ext, hr]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, hs x⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a • x, ⟨x, hx, rfl⟩, hs x⟩

end Generic

theorem image_map_refl {O R M : Type} [CommRing O] [AddCommGroup R] [Module O R] [AddCommGroup M]
    [Module O M] (S : Set (R ⊗[O] M)) :
    (TensorProduct.map (LinearMap.id : R →ₗ[O] R) (LinearEquiv.refl O M).toLinearMap) '' S = S := by
  have : TensorProduct.map (LinearMap.id : R →ₗ[O] R) (LinearEquiv.refl O M).toLinearMap = LinearMap.id :=
    TensorProduct.map_id
  rw [this]
  exact Set.image_id S


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)), z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X → ∃ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, ((F l).E K s LL h).tie.jD T z = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) z') := by
  intro D HW F l _ K s LL h K' h' hle hK0 T hT z' hz'
  have hN := ((GlobalTheory.NL.BaseField.base_indep D HW F l K s LL h K' h' hle hK0).2.2 T
    (resLt (K := K) (K' := K') (LL := LL) hle T) (LinearEquiv.refl ↥(OL LL) ↥T.L.T) (fun _ _ => rfl)).2 hT
    (restrict_crys D hle T hT)
  have hN2 := (image_map_refl (O := ↥(OL LL)) (R := RW LL) (M := ↥T.L.T) _).symm.trans hN
  have h1 := (exists_aN_iff ((F l).E K' s LL h').tie (resLt (K := K) (K' := K') (LL := LL) hle T) _ _
    (GlobalTheory.NL.IoXQ.main D HW F l K' s LL h').1 _).1 ⟨z', hz', rfl⟩
  refine (exists_aN_iff ((F l).E K s LL h).tie T _ _ (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).1 _).2 ?_
  refine h1.elim fun y hy => ⟨toTW hle T y, ?_, hy.2⟩
  exact hN2.subset hy.1

end GlobalTheory.NL.XNTransfer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XNygaardExtComesFromBaseFieldStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.X_nygaard_ext_comes_from_base_field : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)), z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X → ∃ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, ((F l).E K s LL h).tie.jD T z = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) z') := by
  first | exact @GlobalTheory.NL.XNTransfer.main | exact GlobalTheory.NL.XNTransfer.main | (intros; apply GlobalTheory.NL.XNTransfer.main <;> assumption)
end
end
