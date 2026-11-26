module

public import Development.WeilBound.ThetaLifts.LatticeBasics.ThetaBox
public import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasMain
public import Development.WeilBound.CoreStatements.LocalThetaKernels.LocpairAlg

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.FinLevel
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Automorphic.GJMatrix GroundTheory.Global GlobalTheory.HeisSchA

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}


variable (F) in
def epsF : AF F := mk 0 1

theorem epsF_mul (t : AF F) : epsF F * t = mk 0 (p2 t) := Prod.ext (zero_mul _) (one_mul _)

theorem epsF_sq : epsF F * epsF F = epsF F := epsF_mul _

theorem evI_epsF (t : AF F) : evI F (epsF F * t) = 0 := by
  rw [epsF_mul]; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem epsF_of {t : AF F} (h : evI F t = 0) : epsF F * t = t := by
  rw [epsF_mul]
  exact Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).injective ((map_zero _).trans h.symm)) rfl

theorem level (hψ : Continuous ψ) {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) :
    ∀ᶠ w : (κ → AF F) × (κ → AF F) in 𝓝 0, schr ψ (epsF F • w) Φ = Φ := by
  rw [sch_eq, schwartzBruhatPi_eq_cosetSpanPi] at h
  induction h using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, J, b, rfl⟩ := hG
    have m := finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J (b i)
    have c := continuous_finPartPi (K := F) (ι := κ)
    have h1 : ∀ᶠ w : (κ → AF F) × (κ → AF F) in 𝓝 0, ∀ i, finPartPi w.1 i ∈ idealFiniteAdeles J :=
      eventually_all.2 fun i => ((continuous_apply i).comp (c.comp continuous_fst)).continuousAt.preimage_mem_nhds
        ((isOpen_idealFiniteAdeles J).mem_nhds (zero_mem _))
    have h2 : ∀ᶠ w : (κ → AF F) × (κ → AF F) in 𝓝 0, ∀ z ∈ tsupport (finiteTensor fun i => cosetIndicator J (b i)),
        finChar ψ (z ⬝ᵥ finPartPi w.2 + p2 ⅟(2 : AF F) * (finPartPi w.1 ⬝ᵥ finPartPi w.2)) = 1 :=
      m.2.isCompact.eventually_forall_of_forall_eventually fun z _ => by
        have := ((finChar_isLocallyConstant ψ hψ).comp_continuous (f := fun y : ((κ → AF F) × (κ → AF F)) × (κ → Af F) =>
          y.2 ⬝ᵥ finPartPi y.1.2 + p2 ⅟(2 : AF F) * (finPartPi y.1.1 ⬝ᵥ finPartPi y.1.2)) (by fun_prop)).eventually_eq (0, z)
        simpa [show finPartPi (0 : κ → AF F) = 0 from rfl] using this
    filter_upwards [h1, h2] with w h1 h2
    funext x
    have e1 : infPartPi (x + epsF F • w.1) = infPartPi x := funext fun i => by
      have := evI_epsF (w.1 i)
      exact (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _).trans ((congrArg _ this).trans (add_zero _))
    have e2 : finiteTensor (fun i => cosetIndicator J (b i)) (finPartPi (x + epsF F • w.1)) =
        finiteTensor (fun i => cosetIndicator J (b i)) (finPartPi x) := Finset.prod_congr rfl fun i _ => by
      beta_reduce
      rw [cosetIndicator_apply, cosetIndicator_apply,
        show finPartPi (x + epsF F • w.1) i - b i = finPartPi x i - b i + finPartPi w.1 i from by
          rw [sub_add_eq_add_sub]; exact congrArg (finPartPi x i + · - b i) (one_mul _)]
      simp only [AddSubgroup.add_mem_cancel_right _ (h1 i)]
    simp only [schr, schwartzBruhatTensorPi, Prod.smul_fst, Prod.smul_snd, e1, e2]
    by_cases h0 : finiteTensor (fun i => cosetIndicator J (b i)) (finPartPi x) = 0
    · simp [h0]
    · rw [dotProduct_smul, dotProduct_smul, smul_dotProduct, smul_smul, epsF_sq, smul_eq_mul, smul_eq_mul, mul_left_comm ⅟(2 : AF F),
        ← mul_add, epsF_mul, ← finChar_apply, map_add, map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct]
      exact (congrArg (· * _) (h2 _ (subset_tsupport _ h0))).trans (one_mul _)
  | zero => exact .of_forall fun w => funext fun x => mul_zero _
  | add G H _ _ hG hH =>
    filter_upwards [hG, hH] with w hG hH
    funext x
    exact (mul_add _ _ _).trans (congrArg₂ _ (congrFun hG x) (congrFun hH x))
  | smul c G _ hG =>
    filter_upwards [hG] with w hG
    funext x
    exact (mul_left_comm _ _ _).trans (congrArg _ (congrFun hG x))

theorem finite_values (hψ : IsStd ψ) {N : Set ((κ → AF F) × (κ → AF F))} (hN : N ∈ 𝓝 0) :
    ∃ s : Finset (κ → AF F), (∀ y ∈ s, ∀ i, evI F (y i) = 0) ∧ ∀ Ψ : (κ → AF F) → ℂ, (∀ w ∈ N, schr ψ (epsF F • w) Ψ = Ψ) →
      ∀ x : κ → AF F, At (evI F) x → (∀ y ∈ s, Ψ (x + y) = 0) → ∀ y : κ → AF F, (∀ i, evI F (y i) = 0) → Ψ (x + y) = 0 := by
  obtain ⟨ξ, hξ, e⟩ := std_eq hψ
  obtain ⟨N₁, h₁, N₂, h₂, hN⟩ := mem_nhds_prod_iff.1 hN
  have cm : Continuous fun a : Af F => (mk 0 a : AF F) := continuous_const.prodMk continuous_id
  have : ∀ᶠ a : Af F in 𝓝 0, ∀ i, (Pi.single i (mk 0 a) : κ → AF F) ∈ N₂ := eventually_all.2 fun i =>
    ((continuous_single i).comp cm).continuousAt.preimage_mem_nhds (by
      rwa [Function.comp_apply, show (mk 0 0 : AF F) = 0 from rfl, Pi.single_zero])
  obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset this
  have hC := (isCompact_univ_pi fun _ : κ => isCompact_idealFiniteAdeles (traceDualIdeal F J)).image
    (f := fun y i => (mk 0 (algebraMap F (Af F) ξ⁻¹ * y i) : AF F))
    (continuous_pi fun i => cm.comp (continuous_const.mul (continuous_apply i)))
  obtain ⟨s, hs, hc⟩ := hC.elim_nhds_subcover (fun t => {y | y - t ∈ N₁}) fun t _ =>
    (continuous_sub_right t).continuousAt.preimage_mem_nhds (by rwa [sub_self])
  have hs' : ∀ y ∈ s, ∀ i, evI F (y i) = 0 := fun y hy i => by
    obtain ⟨z, -, rfl⟩ := hs y hy
    exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  refine ⟨s, hs', fun Ψ hΨ x hx h0 y hy => by_contra fun hn => ?_⟩
  have hx0 : epsF F • x = 0 := hx _ (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
  refine (fun hm => ?_ : y ∈ _ → False) (hc ⟨fun i => algebraMap F (Af F) ξ * p2 (y i), fun i _ => ?_, ?_⟩)
  · obtain ⟨t, ht, hty⟩ := Set.mem_iUnion₂.1 hm
    have := congrFun (hΨ (y - t, 0) (hN ⟨hty, mem_of_mem_nhds h₂⟩)) (x + t)
    have e : epsF F • (y - t) = y - t := funext fun i => by
      rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub, epsF_of (hy i), epsF_of (hs' t ht i)]
    simp [schr, e, h0 t ht, hn] at this
  · refine (forall_finiteAdelicChar_mul_eq_one_iff J _).1 fun a ha => Circle.ext ?_
    have := congrFun (hΨ (0, Pi.single i (mk 0 a)) (hN ⟨mem_of_mem_nhds h₁, hJ ha i⟩)) (x + y)
    simp only [schr, Prod.smul_fst, Prod.smul_snd, smul_zero, zero_dotProduct, mul_zero, add_zero] at this
    rw [mul_eq_right₀ hn, dotProduct_smul, ← smul_dotProduct, smul_add, hx0, zero_add, dotProduct_single, e] at this
    refine Eq.trans (congrArg (fun z => ((adelicChar F z : Circle) : ℂ)) (Prod.ext ?_ ?_)) this
    · exact (mul_zero _).symm.trans (congrArg _ (mul_zero _).symm)
    · show a * (algebraMap F (Af F) ξ * p2 (y i)) = algebraMap F (Af F) ξ * (1 * p2 (y i) * a)
      ring
  · funext i
    beta_reduce
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hξ, map_one, one_mul, ← epsF_mul, epsF_of (hy i)]

theorem finLevel : FinLevel := by
  intro F E _ _ _ _ _ σ B m n A Y hB κ _ dd K hK Φ hΦ
  have lin : ∀ (k : G2 σ Y) (u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)),
      actB (cA σ) k (epsF F • u) = epsF F • actB (cA σ) k u := fun k u => Matrix.smul_mul _ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : ∀ {α β : Type} [Finite α] [Finite β], IsModuleTopology (AF F) (Matrix α β (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (_ → _ → AE F E))
  have c : Continuous fun y : ((κ → AF F) × (κ → AF F)) × G2 σ Y => dd.e (actB (cA σ) y.2 (dd.e.symm y.1)) :=
    (IsModuleTopology.continuous_of_linearMap dd.e.toLinearMap).comp
      (((IsModuleTopology.continuous_of_linearMap dd.e.symm.toLinearMap).comp continuous_fst).matrix_mul
        (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose)
  obtain ⟨s, hs, h⟩ := finite_values hB.std (hK.eventually_forall_of_forall_eventually
    (P := fun w k => schr B.ψ (epsF F • dd.e (actB (cA σ) k (dd.e.symm w))) Φ = Φ) fun k _ =>
      (c.tendsto' (0, k) 0 (by simp [actB])).eventually (level hB.std.1 hΦ))
  refine ⟨{u | epsF F • u = u ∧ ∀ k ∈ K, dd.rho B.ψ (actB (cA σ) k u) Φ = Φ}, fun u hu => ⟨fun i => ?_, fun i => ?_,
    fun k hk => ⟨by rw [← lin, hu.1], fun k' hk' => ?_⟩⟩, fun u hu => ?_, s, hs, fun Ψ hΨ => h Ψ fun w hw => ?_⟩
  · rw [← hu.1, map_smul]; exact evI_epsF _
  · rw [← hu.1, map_smul]; exact evI_epsF _
  · have := hu.2 _ (mul_mem hk' hk)
    simpa [actB, Matrix.mul_assoc] using this
  · simpa [actB] using hu.2 1 (one_mem _)
  · have := hΨ (epsF F • dd.e.symm w) ⟨by rw [smul_smul, epsF_sq], fun k hk => by
      rw [lin, Darboux.rho, map_smul]; exact hw k hk⟩
    rwa [Darboux.rho, map_smul, LinearEquiv.apply_symm_apply] at this

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.RatEquiv
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Emb

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {β : Type} [Fintype β] [DecidableEq β]

def dgM : Matrix β β A →* Matrix (β ⊕ β) (β ⊕ β) A where
  toFun g := Matrix.fromBlocks g 0 0 g
  map_one' := Matrix.fromBlocks_one
  map_mul' g h := by simp [Matrix.fromBlocks_multiply]

def dgU (J : Matrix β β A) : UG c J →* UG c (dbl J) :=
  ((Units.map dgM).comp (UG c J).subtype).codRestrict _ fun g => by
    have hg : g.1.1ᵀ * J * g.1.1.map c = J := g.2
    show (Matrix.fromBlocks g.1.1 0 0 g.1.1)ᵀ * dbl J * (Matrix.fromBlocks g.1.1 0 0 g.1.1).map c = dbl J
    rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero c), Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp [hg]

theorem dgU_val (J : Matrix β β A) (g : UG c J) : (dgU c J g).1.1 = Matrix.fromBlocks g.1.1 0 0 g.1.1 := rfl

theorem dgU_cont [TopologicalSpace A] (J : Matrix β β A) : Continuous (dgU c J) :=
  continuous_induced_rng.2 ((Continuous.units_map (dgM (A := A) (β := β))
    (continuous_id.matrix_fromBlocks continuous_const continuous_const continuous_id)).comp continuous_subtype_val)

theorem actB_dgU {α : Type} (J : Matrix β β A) (g : UG c J) (w w' : Matrix α β A) :
    actB c (dgU c J g) (Matrix.fromCols w w') = Matrix.fromCols (actB c g w) (actB c g w') := by
  simp [actB, dgU_val, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]

theorem actB_mul {α : Type} {J : Matrix β β A} (g h : UG c J) (w : Matrix α β A) :
    actB c (g * h) w = actB c g (actB c h w) := by
  simp [actB, Matrix.mul_assoc]

end Emb

theorem det_ne_of_sig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply]
  have h2 := congrArg Matrix.det h1
  intro h0
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul, h0] at h2
  simpa [Matrix.det_neg] using h2.symm

theorem herm_det {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsHerm σ B r s) : X.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact det_ne_of_sig (h.sig w) (by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])

theorem skew_det {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsSkew σ B r s) : X.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact det_ne_of_sig (h.sig w) (by rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero])

theorem modu_det {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) (f : (AF F)ˣ →* ℝ≥0) (g : UA σ J) :
    f (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det g.1)) = 1 := by
  have h := congrArg Matrix.det (show g.1.1ᵀ * incM F J * g.1.1.map (cA σ) = incM F J from g.2)
  have u : IsUnit (incM F J).det := by
    rw [incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hJ.isUnit.map _
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show (g.1.1.map (cA σ)).det = sigR (AF F) σ g.1.1.det from ((cA σ).toRingHom.map_det _).symm] at h
  have h1 : g.1.1.det * sigR (AF F) σ g.1.1.det = 1 := u.mul_left_cancel (by linear_combination h)
  have h2 := congrArg (Algebra.norm (AF F)) h1
  rw [map_mul, GlobalTheory.Doubling.norm_sigR, map_one] at h2
  refine (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 ?_
  rw [sq, ← map_mul, ← map_one f]
  exact congrArg f (Units.ext h2)

section Member

variable {a b : ℕ} {JA : Matrix (Fin a) (Fin a) E} {JB : Matrix (Fin b) (Fin b) E} {κ : Type} [Fintype κ]
  {d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ}
  {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ)} {ψ : AddChar (AF F) ℂ}
  {χ : Chr F E} {om : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ)}
  {omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)}

theorem dbl_kill (hψ : IsStd ψ) (h : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd) (z : Matrix (Fin a) (Fin b) (AE F E)) :
    ∀ Φ ∈ schA F (κ ⊕ κ), lD F κ (dd.rho ψ (z * (diagCols (Fin b))ᵀ) Φ) = lD F κ Φ := fun Φ hΦ => by
  rw [show z * (diagCols (Fin b))ᵀ = Matrix.fromCols z z by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.transpose_one]
      exact (Matrix.mul_fromCols z 1 1).trans (by rw [Matrix.mul_one]),
    Darboux.rho, h]
  exact lD_kill hψ hΦ _ _

theorem dbl_fix (hψ : IsStd ψ) (hJ : JB.det ≠ 0) (h : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd)
    (hw : IsUWeilSplit (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd)
    (g : UA σ JB) {Φ} (hΦ : Φ ∈ schA F (κ ⊕ κ)) :
    lD F κ (omd (dgU _ _ g) Φ) = χ (Matrix.GeneralLinearGroup.det g.1) * lD F κ Φ := by
  rw [hw.2.2 _ lD_adm (dbl_kill hψ h) _ g.1 (by simp [dgU_val, diagCols, Matrix.fromBlocks_mul_fromRows]) Φ hΦ, modu_det hJ]
  simp

theorem dbl_box (hψ : IsStd ψ) (hJ : JB.det ≠ 0) (h : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd)
    (hw : IsUWeilSplit (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd)
    (ho : IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om) (g : UA σ JB) {φ φ'} (hφ : φ ∈ schA F κ) (hφ' : φ' ∈ schA F κ) :
    omd (dgU _ _ g) (boxFun φ (star φ')) =
      (χ (Matrix.GeneralLinearGroup.det g.1) : ℂ) • boxFun (om g φ) (star (om g φ')) := by
  have m1 := hw.2.1.pres (dgU _ _ g) _ (box_mem hφ hφ')
  have m2 := box_mem (ho.pres g φ hφ) (ho.pres g φ' hφ')
  have rb : ∀ w ϕ ϕ', dd.rho ψ (Matrix.fromCols w 0) (boxFun ϕ ϕ') = boxFun (d.rho ψ w ϕ) ϕ' := fun w ϕ ϕ' => by
    funext x
    rw [Darboux.rho, h, ← Sum.elim_comp_inl_inr x]
    simp [schr, boxFun, Darboux.rho, elim_dot, mul_assoc, Function.comp_def, Pi.add_def]
  refine sub_eq_zero.1 (lD_inj hψ (sub_mem m1 (Submodule.smul_mem _ _ m2)) fun x y => ?_)
  obtain ⟨w, hw'⟩ := d.e.surjective (x, y)
  obtain ⟨w, rfl⟩ : ∃ w', w = actB (cA σ) g w' := ⟨actB (cA σ) g⁻¹ w, by rw [← actB_mul]; simp [actB]⟩
  have e : ∀ (Φ Ψ) (c : ℂ), schr ψ (Sum.elim x 0, Sum.elim y 0) (Φ - c • Ψ) =
      dd.rho ψ (Matrix.fromCols (actB (cA σ) g w) 0) Φ - c • dd.rho ψ (Matrix.fromCols (actB (cA σ) g w) 0) Ψ := fun Φ Ψ c => by
    funext z
    rw [Darboux.rho, h, hw']
    simp [schr]; ring
  have m3 : d.rho ψ w φ ∈ schA F κ := GlobalTheory.HeisSchA.schr_mem_schA ψ hψ (d.e w) φ hφ
  rw [e, map_sub, map_smul, rb, ← ho.impl g w φ hφ, lD_unit ho.unit ho.pres g m3 hφ',
    show Matrix.fromCols (actB (cA σ) g w) 0 = actB (cA σ) (dgU _ _ g) (Matrix.fromCols w 0) by rw [actB_dgU]; simp [actB],
    ← hw.2.1.impl _ _ _ (box_mem hφ hφ'), rb, dbl_fix hψ hJ h hw g (box_mem m3 hφ')]
  exact sub_self _

theorem dbl_emb (hψ : IsStd ψ) (hJ : JB.det ≠ 0) (h : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd)
    (hw : IsUWeilSplit (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd)
    (ho : IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om)
    (hr : ∀ (g : UA σ JB) (gd : UG (cA σ) (dbl (incM F JB))), gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
      ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omd gd (boxFun φ₁ φ₂) = boxFun (om g φ₁) φ₂)
    {g g' : UA σ JB} {x : UG (cA σ) (dbl (incM F JB))} (hx : x.1.1 = Matrix.fromBlocks g.1.1 0 0 g'.1.1)
    {φ φ'} (hφ : φ ∈ schA F κ) (hφ' : φ' ∈ schA F κ) :
    (((χ (Matrix.GeneralLinearGroup.det g'.1))⁻¹ : Circle) : ℂ) • omd x (boxFun φ (star φ')) =
      boxFun (om g φ) (star (om g' φ')) := by
  have e : x = x * dgU _ _ g'⁻¹ * dgU _ _ g' := by rw [map_inv, inv_mul_cancel_right]
  rw [e, map_mul, Module.End.mul_apply, dbl_box hψ hJ h hw ho g' hφ hφ', map_smul, smul_smul, ← Circle.coe_mul, inv_mul_cancel,
    Circle.coe_one, one_smul, hr (g * g'⁻¹) _ ?_ _ (ho.pres g' φ hφ) _ (star_mem (ho.pres g' φ' hφ')),
    ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  show x.1.1 * (dgU _ _ g'⁻¹).1.1 = _
  rw [hx, dgU_val, Matrix.fromBlocks_multiply]
  simp

theorem rat_equiv (h2 : Module.finrank F E = 2) (hκ : Fintype.card κ = a * b)
    (c : Matrix (Fin a) (Fin b) (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F))
    (hc : ∀ x, ∃ y z, c (incM F x) = (rt y, rt z)) :
    ∃ e : Matrix (Fin a) (Fin b) E ≃ (κ → F) × (κ → F), ∀ x, c (incM F x) = (rt (e x).1, rt (e x).2) := by
  have hi : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective (𝓞 F) F
  let r : (κ → F) →ₗ[F] (κ → AF F) := (Algebra.linearMap F (AF F)).compLeft _
  have hr : Function.Injective r := fun x y e => funext fun i => hi (congrFun e i)
  let j : Matrix (Fin a) (Fin b) E →ₗ[F] (κ → AF F) × (κ → AF F) :=
    (c.toLinearMap.restrictScalars F) ∘ₗ (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).toLinearMap.mapMatrix
  have hj : Function.Injective j := c.injective.comp fun x y e => Matrix.ext fun i k =>
    Algebra.TensorProduct.includeRight_injective hi (congrFun (congrFun e i) k)
  have : LinearMap.range j = LinearMap.range (r.prodMap r) := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, z, e⟩ := hc x
      exact ⟨(y, z), e.symm⟩
    · rw [LinearMap.finrank_range_of_inj hj, LinearMap.finrank_range_of_inj (hr.prodMap hr), Module.finrank_matrix, h2]
      simp [mul_two, hκ]
  choose y z e using hc
  refine ⟨Equiv.ofBijective (fun x => (y x, z x)) ⟨fun x x' h => hj ?_, fun p => ?_⟩, e⟩
  · exact (e x).trans (by rw [(Prod.mk.inj h).1, (Prod.mk.inj h).2]; exact (e x').symm)
  · obtain ⟨x, hx⟩ := this.ge ⟨p, rfl⟩
    exact ⟨x, hr.prodMap hr ((e x).symm.trans hx)⟩

theorem dbl_main {A : Spc F E a} {Y : Spc F E b} {d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (incM F Y.J)) κ}
    {d' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F Y.J) (incM F A.J)) κ} {χ χ' : Chr F E} {om om'}
    (hψ : IsStd ψ) (h2 : Module.finrank F E = 2) (hκ : Fintype.card κ = a * b) (hA : A.J.det ≠ 0) (hY : Y.J.det ≠ 0)
    (hχ : Continuous χ') (hc : ∀ x, ∃ y z, d.e (incM F x) = (rt y, rt z)) (ht : ∀ x, d'.e xᵀ = d.e x)
    (hw : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F A.J) (incM F Y.J) d χ om)
    (hw' : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F Y.J) (incM F A.J) d' χ' om') :
    ∃ dd om₂ S, IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ ⊕ κ) ψ dd χ om₂ S (lD F κ) ∧
      IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) d dd ∧ ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ,
        (∀ g, S g (boxFun φ (star φ')) = boxFun (om' g φ) (star (om' g φ'))) ∧ ∀ h h' x, IsEmb h h' x →
          detInv χ h' • om₂ x (boxFun φ (star φ')) = boxFun (om h φ) (star (om h' φ')) := by
  obtain ⟨ho, dd, omd, h, hw, hr⟩ := hw
  obtain ⟨ho', dd', omd', h', hw', -⟩ := hw'
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e, he⟩ := rat_equiv h2 hκ d.e hc
  let S : UA σ A.J →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ) :=
    { toFun g := detInv χ' g • omd' (dgU _ _ g)
      map_one' := by simp [detInv]
      map_mul' g g' := by simp [detInv, smul_smul, mul_comm] }
  have hS : ∀ g Φ, S g Φ = detInv χ' g • omd' (dgU _ _ g) Φ := fun _ _ => rfl
  have c1 : ∀ g : UA σ A.J, detInv χ' g * χ' (Matrix.GeneralLinearGroup.det g.1) = 1 := fun g => by simp [detInv]
  have r : ∀ w w', dd.rho ψ (Matrix.fromCols w w') = dd'.rho ψ (Matrix.fromCols wᵀ w'ᵀ) := fun w w' => by
    rw [Darboux.rho, Darboux.rho, h, h', ht, ht]
  refine ⟨dd, omd, S, ⟨fun x => ?_, hw, ⟨⟨fun g Φ hΦ => ?_, fun g w Φ hΦ => ?_, fun g l hl f hf => ?_⟩, fun μ hμ g Φ hΦ => ?_,
    fun l hl Φ hΦ => ?_⟩, lD_adm, dbl_kill hψ h, fun g Φ hΦ => ?_, fun Φ hΦ => ?_⟩, h,
    fun φ hφ φ' hφ' => ⟨fun g => ?_, fun g g' x hx => dbl_emb hψ hY h hw ho hr hx hφ hφ'⟩⟩
  · refine ⟨Sum.elim (e x.toCols₁).1 (e x.toCols₂).1, Sum.elim (e x.toCols₁).2 (-(e x.toCols₂).2), ?_⟩
    rw [show incM F x = Matrix.fromCols (incM F x.toCols₁) (incM F x.toCols₂) from (Matrix.fromCols_toCols _).symm, h, he, he]
    congr 1 <;> funext i <;> cases i <;> simp
  · exact Submodule.smul_mem _ _ (hw'.2.1.pres _ Φ hΦ)
  · rw [← Matrix.fromCols_toCols w, Matrix.mul_fromCols, r, r, hS, hS, hw'.2.1.impl _ _ _ hΦ, actB_dgU]
    funext z
    simp [actB, mat, Darboux.rho, schr, mul_left_comm]
  · obtain ⟨T, hT⟩ := hw'.2.1.adm (dgU _ _ g) l hl f hf
    exact ⟨detInv χ' g • T, fun f => by simp [hS, ← hT]⟩
  · rw [← hw'.2.1.unit μ hμ (dgU _ _ g) Φ hΦ]
    simp only [hS, Pi.smul_apply, enorm_smul, detInv, ← ofReal_norm_eq_enorm (_ : Circle).1, Circle.norm_coe,
      ENNReal.ofReal_one, one_mul]
  · simp only [hS, map_smul, smul_eq_mul]
    exact (continuous_subtype_val.comp ((hχ.comp (Matrix.GeneralLinearGroup.continuous_det.comp
      continuous_subtype_val)).inv)).mul ((hw'.2.1.cont l hl Φ hΦ).comp (dgU_cont _ _))
  · rw [hS, map_smul, dbl_fix hψ hA h' hw' g hΦ, smul_eq_mul, ← mul_assoc, c1, one_mul]
  · convert e.hasSum_iff.2 (lD_theta hψ hΦ) using 3 with y
    rw [show incM F (Matrix.fromCols y (-y)) = Matrix.fromCols (incM F y) (-incM F y) by
      ext i (j | j) <;> simp [incM], Darboux.rho, h, map_neg, he]
    simp
  · rw [hS, dbl_box hψ hA h' hw' ho' g hφ hφ', smul_smul, c1, one_smul]

end Member

theorem dblW : DblW := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  obtain ⟨hw, ⟨d', ht, hw'⟩, -⟩ := h.weil
  obtain ⟨dd, om₂, S, h1, h2, h3⟩ := dbl_main h.base.std h.base.cm.2.2.1 (by simp) (herm_det h.herm) (skew_det h.skew) h.hW.1
    h.good.rat ht hw hw'
  refine ⟨dd, om₂, S, _, h1, fun φ hφ φ' hφ' => ⟨box_mem hφ hφ', fun g k k' x hx =>
    ⟨?_, (h3 φ hφ φ' hφ').2 k k' x hx⟩⟩, h2, lD_haar⟩
  have p := h.weil.isUSplitting.pres
  have e : ∀ (k : UA σ W.J) ϕ, om.comp (MonoidHom.inr _ _) k (om.comp (MonoidHom.inl _ _) g ϕ) = om (g, k) ϕ := fun k ϕ => by
    rw [← Module.End.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]; simp
  rw [(h3 φ hφ φ' hφ').1, ← thetaSum_smul, (h3 _ (hw'.1.pres g φ hφ) _ (hw'.1.pres g φ' hφ')).2 k k' x hx, e, e,
    theta_box (p _ φ hφ) (p _ φ' hφ')]
  rfl

theorem dblX : DblX := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  obtain ⟨hw, ⟨d', ht, hw'⟩, -⟩ := h.weil
  have ht' : ∀ x, M.co.e xᵀ = d'.e x := fun x => (ht xᵀ).symm
  obtain ⟨dd, om₂, S, h1, h2, h3⟩ := dbl_main h.base.std h.base.cm.2.2.1 (by simp [mul_comm]) (skew_det h.skew) (herm_det h.herm)
    h.hX.1 (fun x => by rw [← ht']; exact h.good.rat xᵀ) ht' hw' hw
  refine ⟨dd, om₂, S, _, h1, fun φ hφ φ' hφ' => ⟨box_mem hφ hφ', fun k g g' x hx =>
    ⟨?_, (h3 φ hφ φ' hφ').2 g g' x hx⟩⟩, ⟨d', ht, h2⟩, lD_haar⟩
  have p := h.weil.isUSplitting.pres
  have e : ∀ (g : UA σ X.J) ϕ, om.comp (MonoidHom.inl _ _) g (om.comp (MonoidHom.inr _ _) k ϕ) = om (g, k) ϕ := fun g ϕ => by
    rw [← Module.End.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]; simp
  rw [(h3 φ hφ φ' hφ').1, ← thetaSum_smul, (h3 _ (hw.1.pres k φ hφ) _ (hw.1.pres k φ' hφ')).2 g g' x hx, e, e,
    theta_box (p _ φ hφ) (p _ φ' hφ')]
  rfl

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.SchrUnit
noncomputable section

namespace GlobalTheory.ThK.Dbl.Bad

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open PositivityTheory.ThKG.Loc (idem)
open PositivityTheory.ThKG.Loc.Cone

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing in
theorem sq_ne (ν : @Measure (κ → AF F) (borel _)) (hν : @Measure.IsAddHaarMeasure _ _ _ (borel _) ν) {Φ : (κ → AF F) → ℂ}
    (h : Φ ∈ schA F κ) (h0 : Φ ≠ 0) : ∫ u, Φ u * star (Φ u) ∂ν ≠ 0 := fun z => by
  obtain ⟨c, -, hc⟩ := lD_haar ν hν
  have e := hc Φ h Φ h
  have i := (sl_int (box_mem h h) 0).norm
  have ct := GroundTheory.Automorphic.GJMatrix.continuous_of_mem_schwartzBruhatPi h
  have : ∀ u, boxFun Φ (star Φ) (Sum.elim u u) = ((‖Φ u‖ ^ 2 : ℝ) : ℂ) := fun u => by simp [boxFun, Complex.mul_conj']
  rw [z, mul_zero, lD_int (box_mem h h)] at e
  simp only [sl, add_zero, this, Complex.norm_real, norm_pow, norm_norm] at e i
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero, integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) i,
    Continuous.ae_eq_iff_eq _ (show Continuous fun x => ‖Φ x‖ ^ 2 from ct.norm.pow 2) continuous_zero] at e
  exact h0 (funext fun u => by simpa using congrFun e u)

theorem norm_eig {G : Type} [Group G] {om : G →* Module.End ℂ ((κ → AF F) → ℂ)} (hu : IsUnitaryOn (adeleClass F) om)
    (hp : ∀ g, ∀ φ ∈ schA F κ, om g φ ∈ schA F κ) {g : G} {Φ} (h : Φ ∈ schA F κ) (h0 : Φ ≠ 0) {c : ℂ} (hc : om g Φ = c • Φ) :
    ‖c‖ = 1 := by
  letI : MeasurableSpace (κ → AF F) := borel _
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨a, a0, ha⟩ := lD_haar (F := F) (κ := κ) Measure.addHaar inferInstance
  have e := lD_unit hu hp g h h
  rw [hc, star_smul, GlobalTheory.SchwartzBox.boxFun_smul_left, GlobalTheory.SchwartzBox.boxFun_smul_right, smul_smul, map_smul, smul_eq_mul,
    mul_eq_right₀ (ha Φ h Φ h ▸ mul_ne_zero (Complex.ofReal_ne_zero.2 a0.ne') (sq_ne _ inferInstance h h0)), Complex.star_def,
    Complex.mul_conj'] at e
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 (by exact_mod_cast e)

theorem schr_unit {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (ν : @Measure (κ → AF F) (borel _))
    (hν : @Measure.IsAddHaarMeasure _ _ _ (borel _) ν) (w) (A C : (κ → AF F) → ℂ) :
    ∫ u, schr ψ w A u * star (schr ψ w C u) ∂ν = ∫ u, A u * star (C u) ∂ν := by
  letI : MeasurableSpace (κ → AF F) := borel _
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  rw [← integral_add_right_eq_self (fun u => A u * star (C u)) w.1]
  refine integral_congr_ae (.of_forall fun u => ?_)
  simp only [schr, star_mul']
  rw [mul_mul_mul_comm, Complex.star_def, Complex.mul_conj', GlobalTheory.StdCharFromIsStd.norm_psi hψ]
  simp

open scoped Classical in
theorem ev_adm (x : κ → AF F) : (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := fun g _ =>
  ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => mul_comm _ _⟩

variable {f : SInf F κ} {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hS : ∀ v, φ v ∈ SB _)
  (hs : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
include hS hs

theorem rest_ex (v : Pl F) : ∃ r, Rest (evFin F v) (φ v) r ∧ tens (evFin F v) (φ v) r = pure f φ := by
  classical
  obtain ⟨r, h1, h2⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hs
  have e := h2 (φ v)
  rw [Function.update_eq_self] at e
  exact ⟨r, ⟨h1, e ▸ GlobalTheory.TensUniq.pure_mem_schA f φ hS hs⟩, e⟩

theorem eig {v : Pl F} {S} {c : ℂ} (h : Acts (evFin F v) S (φ v) (c • φ v)) : S (pure f φ) = c • pure f φ := by
  obtain ⟨r, h1, h2⟩ := rest_ex (f := f) hS hs v
  rw [← h2, h r h1]
  exact funext fun x => mul_assoc _ _ _

theorem fix_real {S} (h : Acts (evI F) S f f) : S (pure f φ) = pure f φ := by
  refine h (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f φ hS hs⟩
  refine finprod_congr fun v => congrArg _ (funext fun i => ?_)
  have := congrArg (evFin F v) (congrFun (hz (idem F v) (evI_idem v)) i)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, evFin_idem_self, one_mul, Pi.zero_apply, map_zero] at this
  rw [Pi.add_apply, map_add (f := _), this, add_zero]

theorem fix_box {v : Pl F} {S} (h : Acts (evFin F v) S (boxFun (φ v) (star (φ v))) (boxFun (φ v) (star (φ v)))) :
    S (boxFun (pure f φ) (star (pure f φ))) = boxFun (pure f φ) (star (pure f φ)) := by
  obtain ⟨r, h1, h2⟩ := rest_ex (f := f) hS hs v
  have e : tens (evFin F v) (boxFun (φ v) (star (φ v))) (boxFun r (star r)) = boxFun (pure f φ) (star (pure f φ)) := by
    rw [← h2]
    funext x
    simp only [tens, boxFun, Pi.star_apply, star_mul', Function.comp_def]
    ring
  have m := GlobalTheory.TensUniq.pure_mem_schA f φ hS hs
  rw [← e]
  refine h _ ⟨fun x z hz => ?_, e ▸ box_mem m m⟩
  exact congrArg₂ (fun a b => a * star b) (h1.1 (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => congrArg (· ∘ Sum.inl) (hz u hu))
    (h1.1 (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => congrArg (· ∘ Sum.inr) (hz u hu))

end GlobalTheory.ThK.Dbl.Bad

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrInertA
noncomputable section

namespace GlobalTheory.ThK.Dbl.Inert

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.LFun.InertChart PositivityTheory.ThK PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locpair PositivityTheory.ThKH.Locrep
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right tensAt)
open GlobalTheory.Doubling (absE)

section Alg

variable {L : Type} [CommRing L] {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

def conjM {A : Matrix β γ L} {A' : Matrix γ β L} (h1 : A * A' = 1) (h2 : A' * A = 1) : Matrix γ γ L →* Matrix β β L where
  toFun m := A * m * A'
  map_one' := by rw [Matrix.mul_one, h1]
  map_mul' a b := by
    rw [show A * a * A' * (A * b * A') = A * (a * (A' * A) * b) * A' by simp only [Matrix.mul_assoc], h2, Matrix.mul_one]

theorem iso_iff (c : L →+* L) {A : Matrix β γ L} {A' : Matrix γ β L} (h1 : A * A' = 1) {J : Matrix β β L} {H : Matrix γ γ L}
    (hH : cT c A * Jᵀ * A = H) (M : Matrix β β L) :
    Mᵀ * J * M.map c = J ↔ cT c (A' * M * A) * H * (A' * M * A) = H := by
  have e : cT c (A' * M * A) * H * (A' * M * A) = cT c A * (Mᵀ * J * M.map c)ᵀ * A := by
    have : A * (A' * M * A) = M * A := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    calc _ = cT c (A * (A' * M * A)) * Jᵀ * (A * (A' * M * A)) := by rw [← hH, cT_mul c A]; simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [this, cT_mul]
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, cT]
  have k : ∀ X : Matrix β β L, cT c A' * (cT c A * X * A) * A' = X := fun X => by
    calc _ = cT c (A * A') * X * (A * A') := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, cT_one, Matrix.one_mul, Matrix.mul_one]
  rw [e, ← hH]
  exact ⟨fun h => by rw [h], fun h => Matrix.transpose_injective ((k _).symm.trans ((congrArg (cT c A' * · * A') h).trans (k _)))⟩

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} {Y : Spc F E n}

omit [NumberField E] in
theorem latW_le : latW Y v ≤ latHat Y := AddSubgroup.closure_mono (by
  rintro _ ⟨a, ha, hi, x, hx, rfl⟩
  have e : a = atPlace v (evFin F v a) := by simpa [atPlace_mul_right] using (idem_smul ha).symm
  refine ⟨a, by rw [e]; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), fun u => ?_, x, hx, rfl⟩
  by_cases hu : u = v
  · exact hu ▸ hi
  · rw [e, show evFin F u (atPlace v (evFin F v a)) = 0 from evalV_singleFin_ne hu _]; exact zero_mem _)

omit [NumberField E] in
theorem idem_mem {z : Fin n → AE F E} (hz : z ∈ latHat Y) : atPlace v (1 : Fv F v) • z ∈ latW Y v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, hi, x, hx, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨atPlace v 1 • a, at_smul_idem v a, by
      rw [smul_eq_mul, map_mul, evFin_atPlace, one_mul]; exact hi v, x, hx, by rw [smul_smul]; rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | neg a _ ha => rw [smul_neg]; exact neg_mem ha

omit [NumberField E] in
theorem stab_latW {g : Matrix (Fin n) (Fin n) (AE F E)} (hat : ∀ z ∈ latW Y v, At (evFin F v) z) :
    (∀ z ∈ latHat Y, At (evFin F v) z → g *ᵥ z ∈ latHat Y) ↔ ∀ z ∈ latW Y v, g *ᵥ z ∈ latW Y v :=
  ⟨fun h z hz => idem_smul (at_mulVec_right g (hat z hz)) ▸ idem_mem (h z (latW_le hz) (hat z hz)),
    fun h z hz ha => latW_le (h z (idem_smul ha ▸ idem_mem hz))⟩

omit [NumberField E] in
theorem mulVec_latHat {N : Matrix (Fin n) (Fin n) (AE F E)} (hN : At (evFin F v) N) (h : ∀ z ∈ latW Y v, N *ᵥ z ∈ latW Y v)
    {z : Fin n → AE F E} (hz : z ∈ latHat Y) : N *ᵥ z ∈ latHat Y := by
  have := latW_le (h _ (idem_mem hz))
  rwa [Matrix.mulVec_smul, idem_smul (at_mulVec_left hN z)] at this

omit [NumberField E] in
theorem piInf_at {u : InfinitePlace F} (τ : EmbOver E u) {z : AE F E} (hz : At (evFin F v) z) : piInf τ z = 0 := by
  have h0 : compInf F E u (algebraMap (AF F) (AE F E) (atPlace v 1)) = 0 :=
    (congrArg (· ⊗ₜ[F] _) (show evInf F u (atPlace v 1) = 0 from rfl)).trans (TensorProduct.zero_tmul _ _)
  rw [← idem_smul hz, Algebra.smul_def, piInf, RingHom.comp_apply, map_mul, h0, zero_mul, map_zero]

theorem mem_K {B : Base F E} {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K) {k : G2 σ Y}
    (h : ∀ x ∈ ({k, k⁻¹} : Set (G2 σ Y)), At (evFin F v) (mat2 x - 1) ∧ ∀ i j : Fin n → Fin n ⊕ Fin n, i ∈ ({.inl, .inr} : Set _) →
      j ∈ ({.inl, .inr} : Set _) → ∀ z ∈ latW Y v, (mat2 x - 1).submatrix i j *ᵥ z ∈ latW Y v) : k ∈ K := by
  refine (hK k).2 ⟨fun u => ?_, fun z z' hz hz' x hx => ?_⟩
  · have : (mat2 k).map (piInf (B.emb u)) = 1 := Matrix.ext fun i j => by
      have := piInf_at (B.emb u) (z := (mat2 k - 1) i j) fun a ha => congrFun (congrFun ((h k (by simp)).1 a ha) i) j
      rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
      simpa [Matrix.one_apply, apply_ite] using this
    rw [this]; exact Commute.one_left _
  · obtain ⟨h1, h2⟩ := h x hx
    have key : ∀ i : Fin n → Fin n ⊕ Fin n, i ∈ ({.inl, .inr} : Set _) → Sum.elim z z' ∘ i ∈ latHat Y →
        (mat2 x *ᵥ Sum.elim z z') ∘ i ∈ latHat Y := fun i hi h3 => by
      have b : ∀ j : Fin n → Fin n ⊕ Fin n, At (evFin F v) ((mat2 x - 1).submatrix i j) := fun j a ha =>
        Matrix.ext fun _ _ => congrFun (congrFun (h1 a ha) _) _
      convert add_mem h3 (add_mem (mulVec_latHat (b .inl) (h2 i _ hi (by simp)) hz) (mulVec_latHat (b .inr) (h2 i _ hi (by simp)) hz'))
      have : mat2 x *ᵥ Sum.elim z z' = Sum.elim z z' + (mat2 x - 1) *ᵥ Sum.elim z z' := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
      rw [this]
      ext l
      simp [Matrix.mulVec, dotProduct]
    exact ⟨key _ (by simp) hz, key _ (by simp) hz'⟩

variable (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]


variable (β) in
def up : Matrix β β (w.adicCompletion E) →* Matrix β β (AE F E) :=
  (liftM E v β).comp (RingHom.mapMatrix (complEquiv hw h).symm.toRingHom).toMonoidHom

theorem up_pi (m : Matrix β β (w.adicCompletion E)) : (up hw h β m).map (piE h) = m := Matrix.ext fun i j =>
  (congrArg (toCompl h) (congrFun (congrFun (comp_liftM v _) i) j)).trans ((complEquiv hw h).apply_symm_apply _)

theorem up_aw (m : Matrix β β (w.adicCompletion E)) : (up hw h β m).map (aw E v) = 1 := aw_liftM v _

theorem up_at (m : Matrix β β (w.adicCompletion E)) : At (evFin F v) (up hw h β m - 1) := at_liftM v _

include hw in
theorem extW {ι κ : Type} {a b : Matrix ι κ (AE F E)} (h1 : a.map (piE h) = b.map (piE h)) (h2 : a.map (aw E v) = b.map (aw E v)) :
    a = b := extM v (Matrix.ext fun i j => (toCompl_bijective hw h).1 (congrFun (congrFun h1 i) j)) h2

theorem continuous_tensAt : Continuous (tensAt E v : Ev E v → AE F E) := by
  haveI : IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  let b := Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)
  have e : (tensAt E v : Ev E v → AE F E) = fun y => ∑ i, atPlace v (b.coord i y) • tensAt E v (b i) := by
    funext y
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr y, map_sum]
    exact Finset.sum_congr rfl fun i _ => smul_tensAt v _ _
  rw [e]
  exact continuous_finsetSum _ fun i _ => ((GlobalTheory.VacAny.continuous_atPlace v).comp
    (IsModuleTopology.continuous_of_linearMap (b.coord i))).smul continuous_const

theorem continuous_up : Continuous (up hw h β) := by
  haveI : IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : IsTopologicalAddGroup (Ev E v) := IsModuleTopology.topologicalAddGroup (Fv F v) _
  have c1 : Continuous (liftM E v β) :=
    continuous_const.add ((continuous_id.sub continuous_const).matrix_map continuous_tensAt)
  exact c1.comp (continuous_id.matrix_map (continuous_complEquiv hw h).2)

include hw in
theorem continuous_piE : Continuous (piE h) := (continuous_complEquiv hw h).1.comp
  (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v))
    ((RestrictedProduct.continuous_eval v).comp continuous_snd))

variable {h} {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) {J : Matrix β β (AE F E)}
  {A : Matrix β γ (w.adicCompletion E)} {A' : Matrix γ β (w.adicCompletion E)} (h1 : A * A' = 1) (h2 : A' * A = 1)
  {H : Matrix γ γ (w.adicCompletion E)} (hH : cT c A * (J.map (piE h))ᵀ * A = H)

omit [DecidableEq β] in
include hc in
theorem pi_gram (M : Matrix β β (AE F E)) :
    (Mᵀ * J * M.map (cA σ)).map (piE h) = (M.map (piE h))ᵀ * J.map (piE h) * (M.map (piE h)).map c := by
  rw [Matrix.map_mul, Matrix.map_mul]
  exact congrArg _ (Matrix.ext fun i j => piE_cA hc _)

def liftW : UJ c H →* UG (cA σ) J :=
  ((Units.map ((up hw h β).comp (conjM h1 h2))).comp (UJ c H).subtype).codRestrict _ fun g => by
    change (up hw h β (A * g.1.1 * A'))ᵀ * J * (up hw h β (A * g.1.1 * A')).map (cA σ) = J
    refine extW hw h ?_ ?_
    · rw [pi_gram hc, up_pi, iso_iff c h1 hH, show A' * (A * g.1.1 * A') * A = A' * A * g.1.1 * (A' * A) by
        simp only [Matrix.mul_assoc], h2, Matrix.one_mul, Matrix.mul_one]
      exact g.2
    · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, awM_cA, up_aw, Matrix.transpose_one,
        Matrix.map_one _ (map_zero _) (map_one _), one_mul, mul_one]

def downW : UG (cA σ) J →* UJ c H :=
  ((Units.map ((conjM h2 h1).comp (piE h).mapMatrix.toMonoidHom)).comp (UG (cA σ) J).subtype).codRestrict _ fun g =>
    (iso_iff c h1 hH _).1 ((pi_gram hc g.1.1).symm.trans (congrArg (·.map (piE h)) g.2))

theorem continuous_liftW : Continuous (liftW hw hc h1 h2 hH) :=
  ((Units.continuous_map ((continuous_up hw h).comp ((continuous_const.matrix_mul continuous_id).matrix_mul
    continuous_const))).comp continuous_subtype_val).subtype_mk _

include hw in
theorem continuous_downW : Continuous (downW hc h1 h2 hH) :=
  ((Units.continuous_map ((continuous_const.matrix_mul (continuous_id.matrix_map (continuous_piE hw h))).matrix_mul
    continuous_const)).comp continuous_subtype_val).subtype_mk _

theorem down_lift (x : UJ c H) : downW hc h1 h2 hH (liftW hw hc h1 h2 hH x) = x := Subtype.ext (Units.ext (by
  change A' * (up hw h β (A * x.1.1 * A')).map (piE h) * A = x.1.1
  rw [up_pi, show A' * (A * x.1.1 * A') * A = A' * A * x.1.1 * (A' * A) by simp only [Matrix.mul_assoc], h2, Matrix.one_mul,
    Matrix.mul_one]))

theorem lift_down {g : UG (cA σ) J} (hg : At (evFin F v) (g.1.1 - 1)) : liftW hw hc h1 h2 hH (downW hc h1 h2 hH g) = g :=
  Subtype.ext (Units.ext (mat_inj hw h (sub_sub_sub_cancel_right _ _ (1 : Matrix β β (AE F E)) ▸ at_sub (up_at hw h _) hg) (by
    refine (up_pi hw h _).trans ?_
    change A * (A' * g.1.1.map (piE h) * A) * A' = _
    rw [show ∀ M, A * (A' * M * A) * A' = A * A' * M * (A * A') from fun M => by simp only [Matrix.mul_assoc], h1, Matrix.one_mul,
      Matrix.mul_one])))

end GlobalTheory.ThK.Dbl.Inert

end
end
