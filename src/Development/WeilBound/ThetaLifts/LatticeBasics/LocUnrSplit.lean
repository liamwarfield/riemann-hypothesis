module

public import Development.WeilBound.ThetaLifts.LatticeBasics.FinLevel
public import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.ExistsSelfDual
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegrandEqOnPiece
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NormalSubgroupLeUnramifiedFixing

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrSplitA
noncomputable section

namespace GlobalTheory.ThK.Dbl.Split

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open PositivityTheory.ThK PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locpair PositivityTheory.ThKH.Locrep
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right tensAt)
open GlobalTheory.Doubling (absE)
open GlobalTheory.SplitFlip (invT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {v : Pl F} {Y : Spc F E n} (hσ : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v)

omit [NumberField E] in
theorem mem_latW (y : Fin n → AE F E) : y ∈ latW Y v ↔ At (evFin F v) y ∧ compFin F E v ∘ y ∈ latLoc F Y.L v := by
  have e0 : ∀ (a : AF F) (x : E), a • inclR (F := F) (AF F) x = a ⊗ₜ[F] x := fun a x => by
    change (a * 1) ⊗ₜ[F] x = _
    rw [mul_one]
  have key : ∀ y ∈ latW Y v, At (evFin F v) y ∧ compFin F E v ∘ y ∈ latLoc F Y.L v := fun y hy => by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, ha', x, hx, rfl⟩ := hy
      refine ⟨fun u hu => funext fun i => ?_, ?_⟩
      · change u • a • inclR (F := F) (AF F) (x i) = 0
        rw [smul_smul, show u * a = 0 from ha u hu, zero_smul]
      · convert tmul_mem_latLoc ha' hx using 1
        exact funext fun i => congrArg (compFin F E v) (e0 a (x i))
    | zero => exact ⟨at_zero, by convert zero_mem (latLoc F Y.L v) using 1; exact funext fun i => map_zero _⟩
    | add y z _ _ hy hz => exact ⟨at_add hy.1 hz.1, by convert add_mem hy.2 hz.2 using 1; exact funext fun i => map_add _ _ _⟩
    | neg y _ hy =>
      exact ⟨by simpa using at_sub at_zero hy.1, by convert neg_mem hy.2 using 1; exact funext fun i => map_neg _ _⟩
  refine ⟨key y, fun hy => ?_⟩
  have : ∀ z ∈ latLoc F Y.L v, (fun i => sgE E v (z i)) ∈ latW Y v := fun z hz => by
    refine latLoc_induction (p := fun z => (fun i => sgE E v (z i)) ∈ latW Y v) (fun a ha x hx => ?_) ?_
      (fun y z hy hz => ?_) (fun y hy => ?_) hz
    · exact AddSubgroup.subset_closure ⟨sg v a, at_sg a, by rwa [ev_sg], x, hx, funext fun i => (e0 _ _).symm⟩
    · convert zero_mem (latW Y v) using 1; exact funext fun i => map_zero _
    · convert add_mem hy hz using 1; exact funext fun i => map_add _ _ _
    · convert neg_mem hy using 1; exact funext fun i => map_neg _ _
  convert this _ hy.2 using 1
  exact (idem_smul hy.1).symm.trans (funext fun i => (sgE_comp (y i)).symm)

theorem int_iff {m : Matrix (Fin n) (Fin n) (Fv F v)} {L : Submodule (𝓞 E) (Fin n → E)} {b : GL (Fin n) (Fv F v)}
    (hb : IsSplitBasis τ L b) : (∀ u ∈ splitLat τ L, m *ᵥ u ∈ splitLat τ L) ↔
      ∀ i j, ((b⁻¹).1 * m * b.1) i j ∈ v.adicCompletionIntegers F := by
  simp only [hb.mem_iff]
  refine ⟨fun H i j => ?_, fun H u hu i => ?_⟩
  · have := H (b.1 *ᵥ Pi.single j 1) (fun l => by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]; split_ifs; exacts [one_mem _, zero_mem _]) i
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
  · have : (b⁻¹).1 *ᵥ m *ᵥ u = ((b⁻¹).1 * m * b.1) *ᵥ (b⁻¹).1 *ᵥ u := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [this]
    exact sum_mem fun j _ => mul_mem (H i j) (hu j)

include hσ in
theorem stab_iff {b b' : GL (Fin n) (Fv F v)} (hb : IsSplitBasis τ Y.L b) (hb' : IsSplitBasis (τ.comp σ) Y.L b')
    (g : Matrix (Fin n) (Fin n) (AE F E)) : (∀ y ∈ latW Y v, g *ᵥ y ∈ latW Y v) ↔
      (∀ i j, ((b⁻¹).1 * g.map (piW τ) * b.1) i j ∈ v.adicCompletionIntegers F) ∧
        ∀ i j, ((b'⁻¹).1 * g.map (piW (τ.comp σ)) * b'.1) i j ∈ v.adicCompletionIntegers F := by
  have e : ∀ (t : E →ₐ[F] Fv F v) y, splitVec t (compFin F E v ∘ (g *ᵥ y)) = g.map (piW t) *ᵥ splitVec t (compFin F E v ∘ y) :=
    fun t y => funext fun i => RingHom.map_mulVec (piW t) g y i
  rw [← int_iff τ hb, ← int_iff _ hb']
  refine ⟨fun H => ?_, fun H y hy => ?_⟩
  · have k : ∀ t : E →ₐ[F] Fv F v, ∀ u ∈ splitLat t Y.L, g.map (piW t) *ᵥ u ∈ splitLat t Y.L := by
      rintro t _ ⟨z, hz, rfl⟩
      have c : compFin F E v ∘ (fun i => sgE E v (z i)) = z := funext fun i => comp_sgE _
      have := ((mem_latW _).1 (H _ ((mem_latW _).2 ⟨fun a ha => funext fun i => at_sgE (z i) a ha, c.symm ▸ hz⟩))).2
      exact ⟨_, this, by rw [e, c]⟩
    exact ⟨k _, k _⟩
  · obtain ⟨h1, h2⟩ := (mem_latW _).1 hy
    refine (mem_latW _).2 ⟨at_mulVec_right _ h1, (mem_latLoc_iff_split τ hσ).2 ?_⟩
    rw [e, e]
    exact ⟨H.1 _ ⟨_, h2, rfl⟩, H.2 _ ⟨_, h2, rfl⟩⟩

omit [NumberField E] in
theorem piW_cA (z : AE F E) : piW τ (cA σ z) = piW (τ.comp σ) z :=
  (congrArg (splitProj τ) (comp_cA v z)).trans (splitProj_comp τ σ _).symm

include hσ in
theorem extS {ι κ : Type} {a b : Matrix ι κ (AE F E)} (h1 : a.map (piW τ) = b.map (piW τ))
    (h2 : a.map (piW (τ.comp σ)) = b.map (piW (τ.comp σ))) (h3 : a.map (aw E v) = b.map (aw E v)) : a = b :=
  extM v (Matrix.ext fun i j => split_ext hσ τ (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)) h3

variable {β : Type} [Fintype β] [DecidableEq β]

def up (m m' : Matrix β β (Fv F v)) : Matrix β β (AE F E) :=
  liftM E v β (Matrix.of fun i j => (splitAlgEquiv hσ τ).symm (m i j, m' i j))

theorem up_fst (m m' : Matrix β β (Fv F v)) : (up hσ τ m m').map (piW τ) = m := Matrix.ext fun i j =>
  (congrArg (splitProj τ) (congrFun (congrFun (comp_liftM v _) i) j)).trans (splitProj_symm hσ τ _)

theorem up_snd (m m' : Matrix β β (Fv F v)) : (up hσ τ m m').map (piW (τ.comp σ)) = m' := Matrix.ext fun i j =>
  (congrArg (splitProj (τ.comp σ)) (congrFun (congrFun (comp_liftM v _) i) j)).trans (splitProj_comp_symm hσ τ _)

theorem up_aw (m m' : Matrix β β (Fv F v)) : (up hσ τ m m').map (aw E v) = 1 := aw_liftM v _

theorem up_at (m m' : Matrix β β (Fv F v)) : At (evFin F v) (up hσ τ m m' - 1) := at_liftM v _

def upH : Matrix β β (Fv F v) × Matrix β β (Fv F v) →* Matrix β β (AE F E) where
  toFun m := up hσ τ m.1 m.2
  map_one' := extS hσ τ (by rw [up_fst, Matrix.map_one _ (map_zero _) (map_one _)]; rfl)
    (by rw [up_snd, Matrix.map_one _ (map_zero _) (map_one _)]; rfl) (by rw [up_aw, Matrix.map_one _ (map_zero _) (map_one _)])
  map_mul' a b := extS hσ τ (by simp only [Matrix.map_mul, up_fst]; rfl) (by simp only [Matrix.map_mul, up_snd]; rfl)
    (by simp only [Matrix.map_mul, up_aw, mul_one])

theorem continuous_upH : Continuous (upH (β := β) hσ τ) := by
  haveI : IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : IsTopologicalAddGroup (Ev E v) := IsModuleTopology.topologicalAddGroup (Fv F v) _
  have c1 : Continuous (liftM E v β) :=
    continuous_const.add ((continuous_id.sub continuous_const).matrix_map Inert.continuous_tensAt)
  exact c1.comp (continuous_matrix fun i j => (continuous_splitAlgEquiv_symm hσ τ).comp (by fun_prop))

theorem continuous_piW : Continuous (piW τ) := (continuous_splitProj τ).comp
  (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v))
    ((RestrictedProduct.continuous_eval v).comp continuous_snd))

def upG : GL β (Fv F v) × GL β (Fv F v) →* GL β (AE F E) :=
  (Units.map (upH hσ τ)).comp (MulEquiv.prodUnits (M := Matrix β β (Fv F v)) (N := Matrix β β (Fv F v))).symm.toMonoidHom

theorem upG_val (x y : GL β (Fv F v)) : (upG hσ τ (x, y)).1 = up hσ τ x.1 y.1 := rfl

def dual (J : GL β (Fv F v)) : GL β (Fv F v) →* GL β (Fv F v) := (MulAut.conj J⁻¹).toMonoidHom.comp invT

theorem dual_val (J x : GL β (Fv F v)) : (dual J x).1 = (J⁻¹).1 * (x⁻¹).1ᵀ * J.1 := rfl

variable {J : Matrix β β (AE F E)} {Jp : GL β (Fv F v)} (h1 : J.map (piW τ) = Jp.1) (h2 : J.map (piW (τ.comp σ)) = Jp.1ᵀ)

omit [NumberField E] [DecidableEq β] in
theorem pi_gram (M : Matrix β β (AE F E)) :
    (Mᵀ * J * M.map (cA σ)).map (piW τ) = (M.map (piW τ))ᵀ * J.map (piW τ) * M.map (piW (τ.comp σ)) := by
  rw [Matrix.map_mul, Matrix.map_mul]
  exact congrArg _ (Matrix.ext fun i j => piW_cA τ _)

def liftS : GL β (Fv F v) →* UG (cA σ) J :=
  ((upG hσ τ).comp ((MonoidHom.id _).prod (dual Jp))).codRestrict _ fun g => by
    change (up hσ τ g.1 (dual Jp g).1)ᵀ * J * (up hσ τ g.1 (dual Jp g).1).map (cA σ) = J
    have k : g.1ᵀ * Jp.1 * (dual Jp g).1 = Jp.1 := by
      rw [dual_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv_cancel_right, ← Matrix.transpose_mul, Units.inv_mul,
        Matrix.transpose_one, Matrix.one_mul]
    refine extS hσ τ ?_ ?_ ?_
    · rw [pi_gram, up_fst, up_snd, h1, k]
    · rw [pi_gram, comp_conj_conj hσ, up_fst, up_snd, h2]
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using congrArg Matrix.transpose k
    · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, awM_cA, up_aw, Matrix.transpose_one,
        Matrix.map_one _ (map_zero _) (map_one _), one_mul, mul_one]

include h1 in
theorem snd_eq (g : UG (cA σ) J) : g.1.1.map (piW (τ.comp σ)) = (dual Jp (Matrix.GeneralLinearGroup.map (piW τ) g.1)).1 := by
  have := (pi_gram τ g.1.1).symm.trans (congrArg (·.map (piW τ)) g.2)
  rw [h1] at this
  set x := Matrix.GeneralLinearGroup.map (piW τ) g.1
  rw [dual_val, ← this, show g.1.1.map (piW τ) = x.1 from rfl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (Jp⁻¹).1,
    ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one, Units.inv_mul, Matrix.one_mul]

theorem lift_down {g : UG (cA σ) J} (hg : At (evFin F v) (g.1.1 - 1)) :
    liftS hσ τ h1 h2 (Matrix.GeneralLinearGroup.map (piW τ) g.1) = g := by
  refine Subtype.ext (Units.ext (extS hσ τ (up_fst _ _ _ _) ((up_snd _ _ _ _).trans (snd_eq τ h1 g).symm) ?_))
  have := awM_of_at v hg
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), sub_eq_zero] at this
  exact (up_aw _ _ _ _).trans this.symm

theorem continuous_liftS : Continuous (liftS hσ τ h1 h2) := by
  have c0 : Continuous fun g : GL β (Fv F v) => (g.1, (dual Jp g).1) := by
    simp only [dual_val]
    exact Units.continuous_val.prodMk
      ((continuous_const.matrix_mul Units.continuous_coe_inv.matrix_transpose).matrix_mul continuous_const)
  have c : Continuous fun g : GL β (Fv F v) => (liftS hσ τ h1 h2 g).1.1 := by
    have := (continuous_upH hσ τ).comp c0
    exact this
  have c' : Continuous fun g : GL β (Fv F v) => ((liftS hσ τ h1 h2 g).1⁻¹).1 :=
    (c.comp continuous_inv).congr fun g => congrArg (·.1.1) (map_inv (liftS hσ τ h1 h2) g)
  exact continuous_induced_rng.2 (Units.continuous_iff.2 ⟨c, c'⟩)

include hσ in
theorem above_iff (u : HeightOneSpectrum (𝓞 E)) : u.under (𝓞 F) = v ↔ u = splitPrime τ ∨ u = splitPrime (τ.comp σ) := by
  refine ⟨fun h => ?_, by rintro (rfl | rfl) <;> exact splitPrime_under _⟩
  obtain ⟨t, rfl⟩ := SplitChart.exists_splitPrime_eq hσ (SplitChart.isSplit_of_algHom hσ τ) h
  exact (eq_or_eq_comp_conj hσ τ t).imp (congrArg _) (congrArg _)

include hσ in
theorem chi_at (χ : Chr F E) {x : (AE F E)ˣ} (hx : At (evFin F v) (x.1 - 1)) {a b : (Fv F v)ˣ} (ha : piW τ x.1 = a)
    (hb : piW (τ.comp σ) x.1 = b) : (χ x : ℂ) = chrW χ τ a * chrW χ (τ.comp σ) b := by
  have m : ∀ t : E →ₐ[F] Fv F v, splitPrime t ∈ (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset := fun t =>
    (Set.Finite.mem_toFinset _).2 (splitPrime_under t)
  rw [GlobalTheory.InertChars.eq_ideleAt_of_at x hx, ideleAt_eq_prod_locIdele, Finset.prod_eq_mul_of_mem ⟨_, m τ⟩ ⟨_, m (τ.comp σ)⟩
    (Finset.mem_attach _ _) (Finset.mem_attach _ _) (fun h => splitPrime_comp_ne hσ τ (congrArg Subtype.val h).symm)
    fun c _ hc => absurd ((above_iff hσ τ c.1).1 ((Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.1 c.2))
      (not_or.2 ⟨fun h => hc.1 (Subtype.ext h), fun h => hc.2 (Subtype.ext h)⟩), map_mul, Circle.coe_mul]
  congr 1
  · exact congrArg (fun y => (χ (locIdele F _ y) : ℂ)) (Units.ext ((ConjPlace.toCompl_eq hσ _ rfl _).trans (congrArg _ ha)))
  · exact congrArg (fun y => (χ (locIdele F _ y) : ℂ)) (Units.ext ((ConjPlace.toCompl_eq hσ _ rfl _).trans (congrArg _ hb)))

include hσ in
theorem abs_at {x : (AE F E)ˣ} (hx : At (evFin F v) (x.1 - 1)) : (absE F E x : ℝ) = ‖piW τ x.1‖ * ‖piW (τ.comp σ) x.1‖ := by
  have := congrArg (splitProj τ) (GlobalTheory.Doubling.algebraMap_norm_eq hσ (compFin F E v x.1))
  rw [AlgHom.commutes, map_mul, ← splitProj_comp] at this
  conv_lhs => rw [GlobalTheory.InertChars.eq_ideleAt_of_at x hx, GlobalTheory.Doubling.absE_ideleAt, GlobalTheory.Doubling.absEv_apply, coe_nnnorm]
  exact (congrArg norm this).trans (norm_mul _ _)

include hσ in
theorem chrW_mul {χ : Chr F E} (hr : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 0) (a : (Fv F v)ˣ) :
    (chrW χ τ a : ℂ) * chrW χ (τ.comp σ) a = 1 := by
  let j : Fv F v →* AF F :=
    { toFun := fun t => 1 + atPlace v (t - 1)
      map_one' := by simp
      map_mul' := fun s t => extF v (by simp [evFin_atPlace, -map_sub]) (by simp [awF_at, -map_sub]) }
  have e : ∀ t : E →ₐ[F] Fv F v, piW t (algebraMap (AF F) (AE F E) (j a)) = a := fun t => by
    change splitProj t (evFin F v (1 + atPlace v (a.1 - 1)) ⊗ₜ[F] 1) = _
    simp [evFin_atPlace, -map_sub]
  rw [← chi_at hσ τ χ (x := Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) (Units.map j a)) ?_ (e _) (e _),
    hr.triv_of_even (by simp), Circle.coe_one]
  change At _ (algebraMap (AF F) (AE F E) (1 + atPlace v (a.1 - 1)) - 1)
  rw [map_add (f := _), map_one, add_sub_cancel_left]
  exact at_tensAt v ((a.1 - 1) ⊗ₜ[F] 1)

theorem selfDual {B : Base F E} {r s : ℕ} (hY : Y.IsHerm σ B r s) (hd : ((1 : E) • Y.Jᵀ).det ≠ 0) :
    IsSelfDualAt σ ((1 : E) • Y.Jᵀ) Y.L v :=
  PositivityTheory.ThKG.Loc.Iwa.selfDual_of hd hY.lat.toIsLattice (fun y hy x hx => SelfDual.inclR_mem_intLoc v (by
    rw [PositivityTheory.ThKG.Loc.Iwa.hE_smul, one_mul]; exact ⟨⟨_, (hY.dual y).1 hy x hx⟩, rfl⟩)) (s := 1)
    ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top) fun y hy => by
      simp only [OneMemClass.coe_one, map_one, one_smul]
      refine (hY.dual y).2 fun x hx => ?_
      obtain ⟨o, ho⟩ := hy x hx
      rw [PositivityTheory.ThKG.Loc.Iwa.hE_smul, one_mul] at ho
      rw [← ho]; exact o.isIntegral_coe

omit [NumberField E] in
theorem piW_incM (J : Matrix (Fin n) (Fin n) E) : (incM F J).map (piW τ) = J.map τ := Matrix.ext fun i j => by
  change splitProj τ (evFin F v 1 ⊗ₜ[F] J i j) = τ (J i j)
  rw [splitProj_tmul, map_one, one_mul]

theorem frames {B : Base F E} {r s : ℕ} (hσ : IsCMExt F E σ) (hY : Y.IsHerm σ B r s) : ∃ J b b' : GL (Fin n) (Fv F v),
    (incM F Y.J).map (piW τ) = J.1 ∧ (incM F Y.J).map (piW (τ.comp σ)) = J.1ᵀ ∧ IsSplitBasis τ Y.L b ∧
      IsSplitBasis (τ.comp σ) Y.L b' ∧ b.1ᵀ * J.1 * b'.1 = 1 := by
  have hd : ((1 : E) • Y.Jᵀ).det ≠ 0 := by rw [one_smul, Matrix.det_transpose]; exact (Vac.herm_det hY).ne_zero
  have hJ : IsHermND σ ((1 : E) • Y.Jᵀ) := ⟨fun i j => by simp [hY.herm], hd⟩
  have := hY.lat
  obtain ⟨b, hb⟩ := exists_isSplitBasis τ Y.L hσ
  have h1 := IsSplitBasis.dual hσ hJ (selfDual hY hd) hb
  have h2 := splitGram_val hJ τ
  generalize splitGram hJ τ = G at h1 h2
  rw [one_smul] at h2
  have e : ((invT G)⁻¹).1 = G.1ᵀ := GlobalTheory.SplitFlip.invT_inv_val G
  refine ⟨(invT G)⁻¹, b, _, ?_, ?_, hb, h1, ?_⟩
  · rw [e, h2, piW_incM]; rfl
  · rw [e, h2, piW_incM]
    exact Matrix.ext fun i j => congrArg τ (hY.herm j i)
  · rw [e, dualConj_one_val, ← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Units.val_mul, Units.inv_mul, Matrix.transpose_one]

end GlobalTheory.ThK.Dbl.Split

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrSplitL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL

namespace GlobalTheory.ThK.Dbl.Split


variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {O : Subring k} {ϖ : kˣ}
  {nrm : AbsoluteValue k ℝ} {q n : ℕ}

theorem zeta (h : LF O (ϖ : k) nrm q) {A : kˣ →* ℂ} (hA : ∀ u : kˣ, nrm u = 1 → A u = 1)
    (hb : ∀ i < n, ‖A ϖ‖ * (q : ℝ) ^ i < 1) (κ : Measure (GL (Fin n) k)) [hκ : κ.IsMulLeftInvariant]
    (h1 : κ (GLint O n : Set (GL (Fin n) k)) = 1) :
    IntegrableOn (fun g => A (GeneralLinearGroup.det g)) (Mint O n) κ ∧
      ∫ g in Mint O n, A (GeneralLinearGroup.det g) ∂κ = ∏ i ∈ Finset.range n, (1 - A ϖ * (q : ℂ) ^ i)⁻¹ := by
  classical
  have hq : (0 : ℝ) < q := by exact_mod_cast zero_lt_one.trans (GlobalTheory.CompanionTheory.QL.NormalisedValue.main h).1
  have hϖ : A ϖ ≠ 0 := left_ne_zero_of_mul_eq_one (b := A ϖ⁻¹) (by rw [← map_mul, mul_inv_cancel, map_one])
  let a : Fin n → ℝ := fun i => ((n : ℝ) - 1) / 2 - (i : ℕ)
  have e : ∀ i : Fin n, (q : ℝ) ^ a i * (q : ℝ) ^ (((n : ℝ) - 1) / 2 - 0) = (q : ℝ) ^ (n - 1 - i : ℕ) := fun i => by
    have := i.2
    rw [← Real.rpow_add hq, ← Real.rpow_natCast, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    congr 1; simp only [a]; push_cast; ring
  have := GlobalTheory.CompanionTheory.ZetaSph.zeta_spherical h (fun i x => if hx : x = 0 then 0 else A (Units.mk0 x hx) * (nrm x ^ (-a i) : ℝ))
    (fun i => A ϖ * ((q : ℝ) ^ a i : ℝ)) ⟨fun i => mul_ne_zero hϖ
      (by exact_mod_cast (Real.rpow_pos_of_pos hq _).ne'), fun i x m hx => ?_⟩ (fun g => A (GeneralLinearGroup.det g))
    (fun b hb κ hκ => ?_) κ hκ h1 0 fun i => ?_
  · simp only [Real.rpow_zero, Complex.ofReal_one, mul_one] at this
    refine ⟨this.1, this.2.trans ?_⟩
    rw [← Finset.prod_range_reflect, ← Fin.prod_univ_eq_prod_range fun i => (1 - A ϖ * (q : ℂ) ^ (n - 1 - i))⁻¹]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_assoc, ← Complex.ofReal_mul, e]; simp
  · have h0 : x ≠ 0 := fun h0 => by rw [h0, map_zero] at hx; exact (zpow_pos hq _).ne hx
    have : A (Units.mk0 x h0 * (ϖ ^ m)⁻¹) = 1 := hA _ (by
      simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀,
        map_zpow₀, hx, h.nrm_pi, _root_.inv_zpow', ne_eq]
      exact mul_inv_cancel₀ (zpow_pos hq _).ne')
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one₀ (zpow_ne_zero _ hϖ)] at this
    beta_reduce
    rw [dite_eq_right h0, this, mul_zpow, hx, ← Complex.ofReal_zpow, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le,
      ← Real.rpow_mul hq.le]
    congr 3; push_cast; ring
  · have hd : b.1.det = ∏ i, b.1 i i := det_of_upperTriangular hb
    have h0 : ∀ i, b.1 i i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 (hd.symm.trans_ne b.det_ne_zero) i (Finset.mem_univ _)
    have : GeneralLinearGroup.det b = ∏ i, Units.mk0 _ (h0 i) := Units.ext (by simp [hd])
    beta_reduce
    rw [map_mul, map_mul, hA (GeneralLinearGroup.det κ) ((GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff h n κ).1 hκ).2, mul_one, this, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [dite_eq_right (h0 i), mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (nrm.pos (h0 i))]
    simp [a]
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq.le _), mul_assoc, e]
    exact hb _ (by have := i.2; omega)

def IsGcd (O : Subring k) (g t : GL (Fin n) k) : Prop := ∀ a, a ∈ Mint O n ∧ g⁻¹ * a ∈ Mint O n ↔ t⁻¹ * a ∈ Mint O n

theorem doubling (h : LF O (ϖ : k) nrm q) {A B : kˣ →* ℂ} (hA : ∀ u : kˣ, nrm u = 1 → A u = 1)
    (hB : ∀ u : kˣ, nrm u = 1 → B u = 1) (bA : ∀ i < n, ‖A ϖ‖ * (q : ℝ) ^ i < 1) (bB : ∀ i < n, ‖B ϖ‖ * (q : ℝ) ^ i < 1)
    (bC : ∀ i < n, ‖(A * B) ϖ‖ * (q : ℝ) ^ i < 1) (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure]
    (h1 : μ (GLint O n : Set (GL (Fin n) k)) = 1) {φ : GL (Fin n) k → ℂ}
    (hφ : ∀ g, ∃ t, IsGcd O g t ∧ φ g = B (GeneralLinearGroup.det g⁻¹) * (A * B) (GeneralLinearGroup.det t)) :
    Integrable φ μ ∧ (∫ g, φ g ∂μ) * ∏ i ∈ Finset.range n, (1 - (A * B) ϖ * (q : ℂ) ^ i)⁻¹ =
      (∏ i ∈ Finset.range n, (1 - A ϖ * (q : ℂ) ^ i)⁻¹) * ∏ i ∈ Finset.range n, (1 - B ϖ * (q : ℂ) ^ i)⁻¹ := by
  obtain ⟨-, -, _, _, _, hM, -⟩ := GlobalTheory.CompanionTheory.QLTop.gl_topology h n
  obtain ⟨-, _⟩ := (GlobalTheory.CompanionTheory.QL.HaarGL.exists_haar_unimodular h n).2 μ inferInstance
  obtain ⟨iA, zA⟩ := zeta h hA bA μ h1
  obtain ⟨iB, zB⟩ := zeta h hB bB μ h1
  obtain ⟨-, zC⟩ := zeta h (A := A * B) (fun u hu => by simp [hA u hu, hB u hu]) bC μ h1
  rw [← integral_indicator hM.measurableSet] at zA zB zC
  rw [← integrable_indicator_iff hM.measurableSet] at iA iB
  set a := (Mint O n).indicator fun g => A (GeneralLinearGroup.det g)
  set b := (Mint O n).indicator fun g => B (GeneralLinearGroup.det g)
  set Z := ∏ i ∈ Finset.range n, (1 - (A * B) ϖ * (q : ℂ) ^ i)⁻¹
  have hZ : Z ≠ 0 := Finset.prod_ne_zero_iff.2 fun i hi => inv_ne_zero (sub_ne_zero.2 fun e => by
    have := bC i (Finset.mem_range.1 hi)
    rw [← Complex.norm_natCast q, ← norm_pow, ← norm_mul, ← e, norm_one] at this
    exact this.false)
  have key : ∀ g, ∫ x, a x * b (g⁻¹ * x) ∂μ = φ g * Z := fun g => by
    obtain ⟨t, ht, e⟩ := hφ g
    rw [← zC, ← integral_mul_left_eq_self _ t, ← integral_const_mul]
    congr 1; ext x
    have := ht (t * x)
    rw [inv_mul_cancel_left] at this
    by_cases hx : x ∈ Mint O n
    · obtain ⟨h2, h3⟩ := this.2 hx
      simp only [a, b, Set.indicator_of_mem, hx, h2, h3, e, map_mul, MonoidHom.mul_apply]; ring
    · rw [Set.indicator_of_notMem hx, mul_zero]
      by_cases h2 : t * x ∈ Mint O n
      · rw [show b _ = 0 from Set.indicator_of_notMem (fun h3 => hx (this.1 ⟨h2, h3⟩)) _, mul_zero]
      · rw [show a _ = 0 from Set.indicator_of_notMem h2 _, zero_mul]
  let e : GL (Fin n) k × GL (Fin n) k ≃ᵐ GL (Fin n) k × GL (Fin n) k := MeasurableEquiv.shearMulRight _
  have he : MeasurePreserving e (μ.prod μ) (μ.prod μ) := measurePreserving_prod_mul μ μ
  let H : GL (Fin n) k × GL (Fin n) k → ℂ := fun z => a z.1 * b (z.2⁻¹ * z.1)
  have hH : H ∘ e = fun z => a z.1 * b z.2⁻¹ := by ext z; simp [H, e, MeasurableEquiv.shearMulRight]
  have iH : Integrable H (μ.prod μ) :=
    (he.integrable_comp_emb e.measurableEmbedding).1 (hH ▸ iA.mul_prod iB.comp_inv)
  have i2 : Integrable (fun g => φ g * Z) μ := by simpa only [H, key] using iH.integral_prod_right
  refine ⟨(integrable_mul_const_iff hZ.isUnit _).1 i2, ?_⟩
  rw [← integral_mul_const, ← zA, ← zB, ← integral_inv_eq_self b, ← integral_prod_mul, ← hH]
  refine Eq.trans ?_ (he.integral_comp' H).symm
  rw [integral_prod_symm _ iH]
  simp only [H, key]

theorem exists_frame (h : LF O (ϖ : k) nrm q) (g : GL (Fin n) k) : ∃ (t : GL (Fin n) k) (κ : GL (Fin n ⊕ Fin n) k),
    (∀ i j, κ.1 i j ∈ O) ∧ (∀ i j, (κ⁻¹).1 i j ∈ O) ∧ IsGcd O g t ∧
      (κ⁻¹).1 * fromRows (m₂ := Fin n) (1 : Matrix (Fin n) (Fin n) k) 1 =
        fromRows ((g⁻¹).1 * t.1) t.1 := by
  let r := (reindexAlgEquiv k k (finSumFinEquiv (m := n) (n := n))).toMulEquiv
  let N : GL (Fin n ⊕ Fin n) k := ⟨fromBlocks g.1 0 (-g.1) 1, fromBlocks (g⁻¹).1 0 1 1,
    by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩
  obtain ⟨b', hb, κ', hκ, e⟩ := GlobalTheory.CompanionTheory.QL.Iwasawa.exists_upper_mul_int h _ (Units.mapEquiv r N)
  let b := (Units.mapEquiv r).symm b'
  let c := (Units.mapEquiv r).symm κ'
  have e' : N = b * c := by rw [← map_mul, ← e, MulEquiv.symm_apply_apply]
  have c1 : ∀ i j, c.1 i j ∈ O := fun i j => hκ.1 _ _
  have c2 : ∀ i j, (c⁻¹).1 i j ∈ O := fun i j => hκ.2 _ _
  have b0 : b.1.toBlocks₂₁ = 0 := Matrix.ext fun i j => hb (show finSumFinEquiv (.inl j) < finSumFinEquiv (.inr i) by
    simp [Fin.lt_def]; omega)
  have bb : b.1 = fromBlocks b.1.toBlocks₁₁ b.1.toBlocks₁₂ 0 b.1.toBlocks₂₂ := by rw [← b0, fromBlocks_toBlocks]
  have ht : b.1.toBlocks₁₁.det ≠ 0 := left_ne_zero_of_mul (b := b.1.toBlocks₂₂.det) (by rw [← det_fromBlocks_zero₂₁, ← bb]; exact GeneralLinearGroup.det_ne_zero b)
  let t : GL (Fin n) k := GeneralLinearGroup.mkOfDetNeZero _ ht
  have key : (c⁻¹).1 * fromRows (m₂ := Fin n) (1 : Matrix (Fin n) (Fin n) k) 0 =
      fromRows ((g⁻¹).1 * t.1) t.1 := by
    rw [show c⁻¹ = N⁻¹ * b by rw [e']; group, Units.val_mul, Matrix.mul_assoc, bb, fromBlocks_mul_fromRows]
    exact (fromBlocks_mul_fromRows _ _ _ _ _ _).trans (by simp; rfl)
  let C : GL (Fin n ⊕ Fin n) k := ⟨fromBlocks 1 0 1 1, fromBlocks 1 0 (-1) 1,
    by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩
  have o : ∀ i j : Fin n, (1 : Matrix (Fin n) (Fin n) k) i j ∈ O := fun i j => by
    rw [Matrix.one_apply]; split_ifs; exacts [O.one_mem, O.zero_mem]
  have mul : ∀ {α β γ : Type} [Fintype β] (x : Matrix α β k) (y : Matrix β γ k), (∀ i j, x i j ∈ O) → (∀ i j, y i j ∈ O) →
      ∀ i j, (x * y) i j ∈ O := fun x y hx hy i j => O.sum_mem fun l _ => O.mul_mem (hx i l) (hy l j)
  refine ⟨t, C * c, mul _ _ ?_ c1, ?_, fun a => ?_, ?_⟩
  · rintro (i | i) (j | j); exacts [o i j, O.zero_mem, o i j, o i j]
  · rw [_root_.mul_inv_rev]
    refine mul _ _ c2 ?_
    rintro (i | i) (j | j); exacts [o i j, O.zero_mem, O.neg_mem (o i j), o i j]
  · have k2 : (c⁻¹).1 * fromRows (m₂ := Fin n) (t⁻¹ * a).1 0 = fromRows (g⁻¹ * a).1 a.1 := by
      have := congrArg (· * (t⁻¹ * a).1) key
      simpa only [Matrix.mul_assoc, fromRows_mul, Matrix.one_mul, Matrix.zero_mul, Units.val_mul,
        Units.mul_inv_cancel_left] using this
    refine ⟨fun ⟨h1, h2⟩ i j => ?_, fun h1 => ?_⟩
    · have := mul c.1 (fromRows (g⁻¹ * a).1 a.1) c1 (by rintro (i | i) j; exacts [h2 i j, h1 i j]) (.inl i) j
      rwa [← k2, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at this
    · have := mul _ (fromRows (m₂ := Fin n) (t⁻¹ * a).1 0) c2 (by rintro (i | i) j; exacts [h1 i j, O.zero_mem])
      rw [k2] at this
      exact ⟨fun i j => this (.inr i) j, fun i j => this (.inl i) j⟩
  · rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← key]
    congr 1
    exact (fromBlocks_mul_fromRows _ _ _ _ _ _).trans (by simp)


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem exists_dual (J : GL (Fin n) k) {p J₂ : GL (Fin n ⊕ Fin n) k} (hJ : J₂.1 = fromBlocks J.1 0 0 (-J.1)) {t : GL (Fin n) k}
    (h : p.1 * fromRows (m₂ := Fin n) (1 : Matrix (Fin n) (Fin n) k) 1 =
      fromRows (m₂ := Fin n) (1 : Matrix (Fin n) (Fin n) k) 1 * t.1) : ∃ t' : GL (Fin n) k,
      (J₂⁻¹).1 * (p⁻¹).1ᵀ * J₂.1 * fromRows (m₂ := Fin n) (1 : Matrix (Fin n) (Fin n) k) 1 =
        fromRows (m₂ := Fin n) (1 : Matrix (Fin n) (Fin n) k) 1 * t'.1 ∧
        GeneralLinearGroup.det t' = GeneralLinearGroup.det t * (GeneralLinearGroup.det p)⁻¹ := by
  obtain ⟨A, B, C, D, e⟩ : ∃ A B C D, p.1 = fromBlocks A B C D := ⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩
  rw [e, fromBlocks_mul_fromRows, fromRows_mul] at h
  simp only [Matrix.mul_one, Matrix.one_mul, fromRows_ext_iff] at h
  have hA : A = t.1 - B := eq_sub_of_add_eq h.1
  have hC : C = t.1 - D := eq_sub_of_add_eq h.2
  have d : p.1.det = t.1.det * (D - B).det := by
    have : p.1 * fromBlocks 1 0 1 1 = fromBlocks 1 0 1 1 * fromBlocks t.1 B 0 (D - B) := by
      simp [e, fromBlocks_multiply, hA, hC]
    simpa [det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] using congrArg det this
  have hs : (D - B)ᵀ.det ≠ 0 := by
    rw [det_transpose]; exact right_ne_zero_of_mul (d.symm.trans_ne (GeneralLinearGroup.det_ne_zero p))
  let s := GeneralLinearGroup.mkOfDetNeZero _ hs
  have k1 : p.1ᵀ * fromRows (m₂ := Fin n) (1 : Matrix (Fin n) (Fin n) k) (-1) =
      fromRows (m₂ := Fin n) (1 : Matrix (Fin n) (Fin n) k) (-1) * s.1 := by
    rw [e, fromBlocks_transpose, fromBlocks_mul_fromRows, fromRows_mul, hA, hC]
    change _ = fromRows (1 * (D - B)ᵀ) (-1 * (D - B)ᵀ)
    congr 1 <;> simp [transpose_sub] <;> abel
  have k2 : (p⁻¹).1ᵀ * fromRows (m₂ := Fin n) (1 : Matrix (Fin n) (Fin n) k) (-1) =
      fromRows (m₂ := Fin n) (1 : Matrix (Fin n) (Fin n) k) (-1) * (s⁻¹).1 := by
    have := congrArg (fun x => (p⁻¹).1ᵀ * x * (s⁻¹).1) k1
    simp only [← Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.one_mul] at this
    rw [this, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have k3 : J₂.1 * fromRows (m₂ := Fin n) (1 : Matrix (Fin n) (Fin n) k) 1 =
      fromRows (m₂ := Fin n) (1 : Matrix (Fin n) (Fin n) k) (-1) * J.1 := by
    rw [hJ, fromBlocks_mul_fromRows, fromRows_mul]; simp
  refine ⟨J⁻¹ * s⁻¹ * J, ?_, Units.ext ?_⟩
  · rw [Matrix.mul_assoc, k3, ← Matrix.mul_assoc, Matrix.mul_assoc (J₂⁻¹).1, k2, Units.val_mul, Units.val_mul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    congr 2
    have := congrArg (fun x => (J₂⁻¹).1 * x * (J⁻¹).1) k3
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this
    rw [this, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  · have := GeneralLinearGroup.det_ne_zero t
    have := GeneralLinearGroup.det_ne_zero J
    rw [det_transpose] at hs
    simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply, d]
    rw [show s.1.det = (D - B).det from det_transpose _]
    field_simp

end GlobalTheory.ThK.Dbl.Split
end

noncomputable section

namespace GlobalTheory.ThK.Dbl.Split

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open PositivityTheory.ThK PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locpair PositivityTheory.ThKH.Locrep
open GlobalTheory.Doubling (absE)
open GlobalTheory.SplitFlip (invT)
open Matrix (fromBlocks fromRows GeneralLinearGroup)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {v : Pl F} {Y : Spc F E n}

open ValuativeRel in
theorem val_equiv (v : Pl F) : (valuation (Fv F v)).IsEquiv (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))) :=
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  isEquiv _ _

theorem norm_unif (v : Pl F) : ‖(unifAt v : Fv F v)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  simpa using congrArg NNReal.toReal (GlobalTheory.norm_uniformiser_eq_inv_absNorm F v _ (GlobalTheory.ChrWUnif.valued_unifAt v))

open ValuativeRel in
theorem lf (v : Pl F) : GlobalTheory.CompanionTheory.QL.LF (v.adicCompletionIntegers F).toSubring (unifAt v : Fv F v)
    (NormedField.toAbsoluteValue (Fv F v)) (Ideal.absNorm v.asIdeal) := by
  have he := val_equiv v
  have hu : valuation (Fv F v) (unifAt v : Fv F v) = uniformizer _ := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have hO : ∀ y, y ∈ (v.adicCompletionIntegers F).toSubring ↔ valuation (Fv F v) y ≤ 1 := fun y => he.le_one_iff_le_one.symm
  refine ⟨Subring.ext hO, Units.ne_zero _, fun x => ?_, (GlobalTheory.LFun.SatBoundGL.resCard_completion v).symm, fun x hx => ?_, norm_unif v⟩
  · rw [← le_uniformizer_iff, ← hu]
    refine ⟨fun h => ⟨x / unifAt v, (hO _).2 ?_, (mul_div_cancel₀ _ (Units.ne_zero _)).symm⟩, ?_⟩
    · rw [map_div₀]; exact div_le_one_of_le₀ h zero_le'
    · rintro ⟨o, ho, rfl⟩; rw [map_mul]; exact mul_le_of_le_one_right' ((hO _).1 ho)
  · change ‖x‖ = 1
    rw [FinitePlace.norm_def, he.eq_one_iff_eq_one.1 hx]; simp

def chS (χ : Chr F E) (τ : E →ₐ[F] Fv F v) (s : ℂ) : (Fv F v)ˣ →* ℂ where
  toFun a := chrW χ τ a * ((‖a.1‖ : ℝ) : ℂ) ^ s
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, Units.val_mul, Units.val_mul, norm_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]; ring

theorem chS_apply (χ : Chr F E) (τ : E →ₐ[F] Fv F v) (s : ℂ) (a : (Fv F v)ˣ) :
    chS χ τ s a = chrW χ τ a * ((‖a.1‖ : ℝ) : ℂ) ^ s := rfl

theorem chS_unit {χ : Chr F E} {τ : E →ₐ[F] Fv F v} (h : UnrAt χ (splitPrime τ)) (s : ℂ) (u : (Fv F v)ˣ)
    (hu : NormedField.toAbsoluteValue (Fv F v) u = 1) : chS χ τ s u = 1 := by
  have : chrW χ τ u = 1 := h _ ((SplitTie.valued_complMap τ _ _).trans ((val_equiv v).eq_one_iff_eq_one.1
    (((GlobalTheory.CompanionTheory.QL.NormalisedValue.main (lf v)).2.2.2.2.2.2 _).1 hu)))
  change _ * ((‖u.1‖ : ℝ) : ℂ) ^ s = 1
  rw [this, show ‖u.1‖ = 1 from hu]; simp

theorem norm_unif_cpow (s : ℂ) : ((‖(unifAt v : Fv F v)‖ : ℝ) : ℂ) ^ s = npow v (-s) := by
  rw [norm_unif, Complex.ofReal_inv, Complex.ofReal_natCast, npow, Complex.cpow_neg,
    Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)]

theorem chS_unif {χ : Chr F E} {τ : E →ₐ[F] Fv F v} (h : UnrAt χ (splitPrime τ)) (s : ℂ) :
    chS χ τ s (unifAt v) = val χ (splitPrime τ) * npow v (-s) := by
  rw [← GlobalTheory.ChrWUnif.chrW_unifAt F E χ v τ h, ← norm_unif_cpow]; rfl

theorem npow_nat (s : ℂ) (i : ℕ) : npow v (-s) * (Ideal.absNorm v.asIdeal : ℂ) ^ i = npow v (-(s - i)) := by
  rw [neg_sub', sub_neg_eq_add, LFun.npow_add, npow, npow, Complex.cpow_natCast]

theorem npow_lt {s : ℂ} {i : ℕ} (h : i < s.re) : ‖npow v (-s)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ i < 1 := by
  rw [← Complex.norm_natCast, ← norm_pow, ← norm_mul, npow_nat, norm_npow]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_absNorm v) (by simpa using h)

section Alg

variable {k : Type} [Field k]

def bd (x y : GL (Fin n) k) : GL (Fin n ⊕ Fin n) k :=
  ⟨fromBlocks x.1 0 0 y.1, fromBlocks (x⁻¹).1 0 0 (y⁻¹).1, by simp [Matrix.fromBlocks_multiply], by simp [Matrix.fromBlocks_multiply]⟩

theorem bd_val (x y : GL (Fin n) k) : (bd x y).1 = fromBlocks x.1 0 0 y.1 := rfl

theorem bd_inv (x y : GL (Fin n) k) : ((bd x y)⁻¹).1 = fromBlocks (x⁻¹).1 0 0 (y⁻¹).1 := rfl

theorem bd_sub (x : GL (Fin n) k) (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) {i j : Fin n → Fin n ⊕ Fin n}
    (hi : i ∈ ({.inl, .inr} : Set _)) (hj : j ∈ ({.inl, .inr} : Set _)) :
    (x⁻¹).1 * (N - 1).submatrix i j * x.1 = (((bd x x)⁻¹).1 * N * (bd x x).1 - 1).submatrix i j := by
  rw [show ((bd x x)⁻¹).1 * N * (bd x x).1 - 1 = ((bd x x)⁻¹).1 * (N - 1) * (bd x x).1 by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul]]
  generalize N - 1 = N
  rw [← Matrix.fromBlocks_toBlocks N]
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
    simp only [bd_val, bd_inv, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] <;> rfl

end Alg

theorem dual_conj {β : Type} [Fintype β] [DecidableEq β] {J a a' ε : GL β (Fv F v)} (h : a.1ᵀ * J.1 * a'.1 = ε.1) (x : GL β (Fv F v)) :
    (a'⁻¹).1 * (dual J (a * x * a⁻¹)).1 * a'.1 = (ε⁻¹).1 * (x⁻¹).1ᵀ * ε.1 := by
  have : ε = (invT a)⁻¹ * J * a' := Units.ext h.symm
  rw [← dual_val, ← Units.val_mul, ← Units.val_mul, this]
  congr 1
  simp only [dual, MonoidHom.comp_apply, map_mul invT, map_inv invT, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end GlobalTheory.ThK.Dbl.Split

namespace GlobalTheory.ThK.Dbl

open Split
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open PositivityTheory.ThK PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locpair
open Matrix (fromBlocks fromRows GeneralLinearGroup)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem locUnrSplit : LocUnrSplit := by
  rintro F E _ _ _ _ _ σ B n Y r s hB hY χ - hr K e hK he v ⟨τ⟩ hu μ hμ hμ1 z f hz hf
  have hσ := hB.cm
  obtain ⟨J, b, b', h1, h2, hb, hb', hg⟩ := frames τ hσ hY
  have g1 : (dbl (incM F Y.J)).map (piW τ) = (bd J (-J)).1 := by
    simp [dbl, bd_val, Matrix.fromBlocks_map, Matrix.map_neg, h1]
  have g2 : (dbl (incM F Y.J)).map (piW (τ.comp σ)) = (bd J (-J)).1ᵀ := by
    simp [dbl, bd_val, Matrix.fromBlocks_map, Matrix.map_neg, h2, Matrix.fromBlocks_transpose]
  have gg : (bd b b).1ᵀ * (bd J (-J)).1 * (bd b' b').1 = (bd 1 (-1 : GL (Fin n) (Fv F v))).1 := by
    simp [bd_val, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hg]
  let Λ : GL (Fin n) (Fv F v) →* UA σ Y.J := liftS hσ τ h1 h2
  let Λ₂ : GL (Fin n ⊕ Fin n) (Fv F v) →* G2 σ Y := liftS hσ τ g1 g2
  have a1 : ∀ x, (mat (Λ x)).map (piW τ) = x.1 := fun x => up_fst hσ τ x.1 (dual J x).1
  have a2 : ∀ x, (mat (Λ x)).map (piW (τ.comp σ)) = (dual J x).1 := fun x => up_snd hσ τ x.1 (dual J x).1
  have a3 : ∀ x, (mat (Λ x)).map (aw E v) = 1 := fun x => up_aw hσ τ x.1 (dual J x).1
  have l1 : ∀ x, (mat2 (Λ₂ x)).map (piW τ) = x.1 := fun x => up_fst hσ τ x.1 (dual (bd J (-J)) x).1
  have l2 : ∀ x, (mat2 (Λ₂ x)).map (piW (τ.comp σ)) = (dual (bd J (-J)) x).1 := fun x => up_snd hσ τ x.1 (dual (bd J (-J)) x).1
  have l3 : ∀ x, (mat2 (Λ₂ x)).map (aw E v) = 1 := fun x => up_aw hσ τ x.1 (dual (bd J (-J)) x).1
  have l4 : ∀ x, At (evFin F v) (mat2 (Λ₂ x) - 1) := fun x => up_at hσ τ x.1 (dual (bd J (-J)) x).1
  have one : ∀ {ι R : Type} [DecidableEq ι] [CommRing R] (φ : AE F E →+* R), (1 : Matrix ι ι _).map φ = 1 :=
    fun φ => Matrix.map_one _ (map_zero _) (map_one _)
  have zero : ∀ {R : Type} [CommRing R] (φ : AE F E →+* R), (0 : Matrix (Fin n) (Fin n) _).map φ = 0 :=
    fun φ => Matrix.map_zero _ (map_zero _)
  have emb : ∀ x, e (Λ x, 1) = Λ₂ (bd x 1) := fun x => Subtype.ext (Units.ext ((he _ _).trans (extS hσ τ ?_ ?_ ?_)))
  rotate_left
  · refine Eq.trans ?_ (l1 _).symm
    rw [Matrix.fromBlocks_map, zero, a1, show (mat 1).map (piW τ) = 1 from one _]
    rfl
  · refine Eq.trans ?_ (l2 _).symm
    rw [Matrix.fromBlocks_map, zero, a2,
      show (mat 1).map (piW (τ.comp σ)) = 1 from one _, dual_val, dual_val, bd_inv, bd_inv, bd_val]
    simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, inv_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one, Units.inv_mul]
  · refine Eq.trans ?_ (l3 _).symm
    rw [Matrix.fromBlocks_map, zero, a3, show (mat 1).map (aw E v) = 1 from one _,
      Matrix.fromBlocks_one]
  have o : ∀ {ι : Type} [DecidableEq ι] (i j : ι), (1 : Matrix ι ι (Fv F v)) i j ∈ v.adicCompletionIntegers F := fun i j => by
    rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _]
  have key : ∀ x : GL (Fin n ⊕ Fin n) (Fv F v), (∀ i j, x.1 i j ∈ v.adicCompletionIntegers F) →
      (∀ i j, (x⁻¹).1 i j ∈ v.adicCompletionIntegers F) → At (evFin F v) (mat2 (Λ₂ (bd b b * x * (bd b b)⁻¹)) - 1) ∧
      ∀ i j : Fin n → Fin n ⊕ Fin n, i ∈ ({.inl, .inr} : Set _) → j ∈ ({.inl, .inr} : Set _) →
        ∀ z ∈ latW Y v, (mat2 (Λ₂ (bd b b * x * (bd b b)⁻¹)) - 1).submatrix i j *ᵥ z ∈ latW Y v := fun x hx hx' => by
    refine ⟨l4 _, fun i j hi hj => (stab_iff hσ τ hb hb' _).2 ⟨fun l m => ?_, fun l m => ?_⟩⟩
    · rw [← Matrix.submatrix_map, Matrix.map_sub _ (map_sub _), one, bd_sub _ _ hi hj,
        l1, ← Units.val_mul, ← Units.val_mul,
        show (bd b b)⁻¹ * (bd b b * x * (bd b b)⁻¹) * bd b b = x by group]
      exact sub_mem (hx _ _) (o _ _)
    · rw [← Matrix.submatrix_map, Matrix.map_sub _ (map_sub _), one, bd_sub _ _ hi hj,
        l2, dual_conj gg]
      refine sub_mem (sum_mem fun c _ => mul_mem (sum_mem fun d _ => mul_mem ?_ (hx' _ _)) ?_) (o _ _)
      · generalize i l = a
        rcases a with a | a <;> rcases d with d | d
        exacts [o a d, zero_mem _, zero_mem _, neg_mem (o a d)]
      · generalize j m = a
        rcases a with a | a <;> rcases c with c | c
        exacts [o c a, zero_mem _, zero_mem _, neg_mem (o c a)]
  have u1 := hu _ (splitPrime_under τ)
  have u2 := hu _ (splitPrime_under (τ.comp σ))
  have hφ : ∀ y : GL (Fin n) (Fv F v), ∃ t, IsGcd (v.adicCompletionIntegers F).toSubring y t ∧ f (e (Λ (b * y * b⁻¹), 1)) =
      chS χ (τ.comp σ) (z + n / 2) (GeneralLinearGroup.det y⁻¹) *
        (chS χ τ (z + n / 2) * chS χ (τ.comp σ) (z + n / 2)) (GeneralLinearGroup.det t) := fun y => by
    obtain ⟨t, κ, k1, k2, ht, hκ⟩ := GlobalTheory.ThK.Dbl.Split.exists_frame (lf v) y
    refine ⟨t, ht, ?_⟩
    let p := bd b b * (bd y 1 * κ⁻¹) * (bd b b)⁻¹
    have hp : p.1 * (fromRows (1 : Matrix (Fin n) (Fin n) (Fv F v)) 1 : Matrix (Fin n ⊕ Fin n) (Fin n) (Fv F v)) = (fromRows (1 : Matrix (Fin n) (Fin n) (Fv F v)) 1 : Matrix (Fin n ⊕ Fin n) (Fin n) (Fv F v)) * (b * t * b⁻¹).1 := by
      have : ((bd b b)⁻¹).1 * (fromRows (1 : Matrix (Fin n) (Fin n) (Fv F v)) 1 : Matrix (Fin n ⊕ Fin n) (Fin n) (Fv F v)) = (fromRows (1 : Matrix (Fin n) (Fin n) (Fv F v)) 1 : Matrix (Fin n ⊕ Fin n) (Fin n) (Fv F v)) * (b⁻¹).1 := by
        simp only [bd_inv, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul,
          add_zero, zero_add]
      simp only [p, Units.val_mul, Matrix.mul_assoc, this]
      rw [← Matrix.mul_assoc (κ⁻¹).1, hκ]
      simp only [bd_val, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul,
        add_zero, zero_add, Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.val_one]
    obtain ⟨t', hp', dt⟩ := exists_dual J (J₂ := bd J (-J)) rfl hp
    let T := upG hσ τ (b * t * b⁻¹, t')
    have dg : ∀ {R : Type} [CommRing R] (φ : AE F E →+* R), (diagCols (Fin n) : Matrix _ _ (AE F E)).map φ =
        fromRows (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin n) (Fin n) R) :=
      fun φ => by rw [diagCols, Matrix.fromRows_map, one]
    have par : mat2 (Λ₂ p) * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
        (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * T.1 := extS hσ τ
      (by rw [Matrix.map_mul, Matrix.map_mul, dg, l1, upG_val, up_fst, hp])
      (by rw [Matrix.map_mul, Matrix.map_mul, dg, l2, upG_val, up_snd,
        dual_val, hp'])
      (by rw [Matrix.map_mul, Matrix.map_mul, l3, upG_val, up_aw,
        Matrix.one_mul, Matrix.mul_one])
    have at1 : At (evFin F v) ((GeneralLinearGroup.det T).1 - 1) := by
      rw [show (GeneralLinearGroup.det T).1 = _ from det_liftM v _]
      change At _ (1 + GlobalTheory.EmbChart.tensAt E v _ - 1)
      rw [add_sub_cancel_left]; exact at_tensAt v _
    have d1 : piW τ (GeneralLinearGroup.det T).1 = (GeneralLinearGroup.det (b * t * b⁻¹)).1 :=
      (RingHom.map_det _ _).trans (congrArg Matrix.det (up_fst hσ τ (b * t * b⁻¹).1 t'.1))
    have d2 : piW (τ.comp σ) (GeneralLinearGroup.det T).1 = (GeneralLinearGroup.det t').1 :=
      (RingHom.map_det _ _).trans (congrArg Matrix.det (up_snd hσ τ (b * t * b⁻¹).1 t'.1))
    have e1 : bd (b * y * b⁻¹) 1 = p * (bd b b * κ * (bd b b)⁻¹) := by
      rw [show p * (bd b b * κ * (bd b b)⁻¹) = bd b b * bd y 1 * (bd b b)⁻¹ by simp only [p]; group]
      exact Units.ext (by simp only [Units.val_mul, bd_val, bd_inv, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
        add_zero, zero_add, Units.val_one, Matrix.mul_one, Units.mul_inv])
    have dκ : chS χ (τ.comp σ) (z + n / 2) (GeneralLinearGroup.det κ) = 1 := by
      have int : ∀ x : GL (Fin n ⊕ Fin n) (Fv F v), (∀ i j, x.1 i j ∈ (v.adicCompletionIntegers F).toSubring) →
          ‖(GeneralLinearGroup.det x).1‖ ≤ 1 := fun x hx => ((GlobalTheory.CompanionTheory.QL.NormalisedValue.main (lf v)).2.2.1 _).2 (by
        rw [GeneralLinearGroup.val_det_apply, Matrix.det_apply']
        exact sum_mem fun _ _ => mul_mem (intCast_mem _ _) (prod_mem fun _ _ => hx _ _))
      refine chS_unit u2 _ _ (le_antisymm (int κ k1) ?_)
      have := int _ k2
      rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at this
      exact (inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))).1 this
    have dp : GeneralLinearGroup.det t' = GeneralLinearGroup.det t * (GeneralLinearGroup.det y⁻¹ * GeneralLinearGroup.det κ) := by
      have : GeneralLinearGroup.det (bd y 1) = GeneralLinearGroup.det y := Units.ext (by
        simp [bd_val, Matrix.det_fromBlocks_zero₂₁])
      rw [dt]
      simp only [p, map_mul, map_inv, this, mul_inv_cancel_comm, mul_inv, inv_inv]
    have hk : Λ₂ (bd b b * κ * (bd b b)⁻¹) ∈ K := Inert.mem_K hK (by
      rintro x (rfl | rfl)
      · exact key κ k1 k2
      · rw [← map_inv, show (bd b b * κ * (bd b b)⁻¹)⁻¹ = bd b b * κ⁻¹ * (bd b b)⁻¹ by group]
        exact key _ k2 k1)
    have dt' : GeneralLinearGroup.det (b * t * b⁻¹) = GeneralLinearGroup.det t := by
      rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [emb, e1, map_mul, hf _ T par (l4 _) _ hk (l4 _), chi_at hσ τ χ at1 d1 d2,
      abs_at hσ τ at1, d1, d2, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _),
      mul_mul_mul_comm]
    change chS χ τ _ _ * chS χ (τ.comp σ) _ _ = _
    rw [dt', dp, map_mul, map_mul, dκ, MonoidHom.mul_apply]
    ring
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  let dn : UA σ Y.J →* GL (Fin n) (Fv F v) := (GeneralLinearGroup.map (piW τ)).comp (Subgroup.subtype _)
  let φ : locGrp σ Y v ≃ₜ* GL (Fin n) (Fv F v) :=
    { toFun := fun g => b⁻¹ * dn g.1 * b
      invFun := fun x => ⟨Λ (b * x * b⁻¹), Subgroup.subset_closure (up_at _ _ _ _)⟩
      left_inv := fun g => Subtype.ext ((congrArg Λ (show b * (b⁻¹ * dn g.1 * b) * b⁻¹ = dn g.1 by group)).trans (lift_down hσ τ h1 h2 (((USub σ Y v).closure_eq).le g.2)))
      right_inv := fun x => by
        change b⁻¹ * dn (Λ (b * x * b⁻¹)) * b = x
        rw [show dn (Λ (b * x * b⁻¹)) = b * x * b⁻¹ from Units.ext (a1 _)]; group
      map_mul' := fun _ _ => by simp only [Subgroup.coe_mul, map_mul]; group
      continuous_toFun := (continuous_const.mul (((Units.continuous_map (continuous_id.matrix_map (continuous_piW τ))).comp
        continuous_subtype_val).comp continuous_subtype_val)).mul continuous_const
      continuous_invFun := ((continuous_liftS hσ τ h1 h2).comp (by fun_prop)).subtype_mk _ }
  let m := φ.toHomeomorph.toMeasurableEquiv
  haveI : (μ.map m).IsHaarMeasure := φ.isHaarMeasure_map μ
  have hat : ∀ z ∈ latW Y v, At (evFin F v) z := fun z hz => ((mem_latW z).1 hz).1
  have st : ∀ g : UA σ Y.J, (∀ z ∈ latHat Y, At (evFin F v) z → mat g *ᵥ z ∈ latHat Y) ↔
      b⁻¹ * dn g * b ∈ GlobalTheory.CompanionTheory.QL.GLint (v.adicCompletionIntegers F).toSubring n := fun g => by
    have := dual_conj (ε := 1) hg (b⁻¹ * dn g * b)
    rw [show b * (b⁻¹ * dn g * b) * b⁻¹ = dn g by group, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at this
    rw [Inert.stab_latW hat, stab_iff hσ τ hb hb', show (mat g).map (piW (τ.comp σ)) = _ from snd_eq τ h1 g]
    exact and_congr Iff.rfl ((Iff.of_eq (congrArg (fun M : Matrix _ _ _ => ∀ i j, M i j ∈ v.adicCompletionIntegers F) this)).trans
      ⟨fun h i j => h j i, fun h i j => h j i⟩)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have bb : ∀ t : E →ₐ[F] Fv F v, UnrAt χ (splitPrime t) → ∀ i < n,
      ‖chS χ t (z + n / 2) (unifAt v)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ i < 1 := fun t ht i hi => by
    rw [chS_unif ht, norm_mul, norm_val, one_mul]
    have : (i : ℝ) < n := by exact_mod_cast hi
    exact npow_lt (by simp; linarith)
  have hC : (chS χ τ (z + n / 2) * chS χ (τ.comp σ) (z + n / 2)) (unifAt v) = npow v (-(2 * z + n)) := by
    rw [MonoidHom.mul_apply, chS_apply, chS_apply, mul_mul_mul_comm, chrW_mul hσ τ hr, norm_unif_cpow, ← LFun.npow_add, one_mul]
    congr 1; ring
  obtain ⟨i1, i2⟩ := doubling (lf v) (chS_unit u1 _) (chS_unit u2 _) (bb _ u1) (bb _ u2) (fun i hi => by
    have : (i : ℝ) < n := by exact_mod_cast hi
    rw [hC]; exact npow_lt (by simp; linarith)) (μ.map m) (by
    rw [m.map_apply, ← hμ1]
    congr 1
    ext g
    refine Iff.trans ?_ (show (_ ∧ _) ↔ IntAt v g.1 by simp only [IntAt, imp_and, forall_and]; rfl)
    rw [st, st, map_inv, show b⁻¹ * (dn g.1)⁻¹ * b = (b⁻¹ * dn g.1 * b)⁻¹ by group, inv_mem_iff, and_self]
    rfl) hφ
  have e2 : ∀ u : locGrp σ Y v, f (e (Λ (b * m u * b⁻¹), 1)) = f (e (u.1, 1)) := fun u =>
    congrArg (fun x : locGrp σ Y v => f (e (x.1, 1))) (φ.left_inv u)
  rw [integrable_map_equiv, Function.comp_def] at i1
  rw [integral_map_equiv] at i2
  simp only [e2] at i1 i2
  refine ⟨i1, ?_⟩
  rw [hC, ← Finset.prod_range_reflect, ← Finset.prod_mul_distrib] at i2
  rw [locD, if_pos ⟨τ⟩]
  convert i2 using 2
  · refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    rw [npow_nat, one_pow, one_mul, npow, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    congr 3; push_cast; ring
  · classical
    rw [Lv, show Formalism.L2.Host.aboveF (L := E) F v = {splitPrime τ, splitPrime (τ.comp σ)} by
      ext u; simp [mem_aboveF, above_iff hσ τ], Finset.prod_pair (splitPrime_comp_ne hσ τ).symm, locL, locL, charFam_of_unrAt u1,
      charFam_of_unrAt u2, eulerFac_singleton, eulerFac_singleton, chS_unif u1, chS_unif u2, mul_assoc, mul_assoc, npow_nat]
    simp only [npow, SplitChart.absNorm_splitPrime]

end GlobalTheory.ThK.Dbl

end
