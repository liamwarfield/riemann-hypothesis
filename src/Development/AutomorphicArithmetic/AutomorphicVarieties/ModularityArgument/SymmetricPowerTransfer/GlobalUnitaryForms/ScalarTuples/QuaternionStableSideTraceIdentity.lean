module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibCon
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricFiberMasterFormula
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.ResidualAutomorphyOfLinkedEnds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIwahoriTorusProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.BaseSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ProdChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ExIota
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.CommOfConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ClassRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FinMulSupp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.JstdTrace

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberSupportFinite
theorem UpperTheory.orbitalFiber_support_finite :
    UpperTheory.V.Z.Sym.Glob.Fib.SuppFin := by
  intro Γ G V _ _ _ _ B hB h0 f hf g
  have hK : Finite ((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι) := by
    have h := hB.stab g
    rw [h0, Subgroup.relIndex_bot_left] at h
    exact Nat.finite_of_card_ne_zero h
  have hKs : (((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι : Subgroup Γ) : Set Γ).Finite := Set.toFinite _
  have hfib : ∀ x : G ⧸ B.U, ((fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) ⁻¹' {x}).Finite := by
    intro x
    rcases Set.eq_empty_or_nonempty ((fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) ⁻¹' {x}) with he | ⟨γ₀, h₀⟩
    · rw [he]; exact Set.finite_empty
    · refine (hKs.image (fun k => γ₀ * k)).subset fun γ hγ => ⟨γ₀⁻¹ * γ, ?_, by simp⟩
      have e : ((g⁻¹ * B.ι γ₀ * g : G) : G ⧸ B.U) = ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U) :=
        (Set.mem_singleton_iff.1 h₀).trans (Set.mem_singleton_iff.1 hγ).symm
      refine ⟨_, QuotientGroup.eq.1 e, ?_⟩
      simp [mul_assoc]
  refine (hf.fin.preimage' (f := fun γ => ((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U)) fun x _ => hfib x).subset ?_
  intro γ hγ h
  apply hγ
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U (g⁻¹ * B.ι γ * g)
  have hr := hf.right u (g⁻¹ * B.ι γ * g)
  change f (((g⁻¹ * B.ι γ * g : G) : G ⧸ B.U).out) = 0 at h
  change f (g⁻¹ * B.ι γ * g * u) = _ at hr
  rw [hu, hr] at h
  exact (mul_eq_zero.1 h).resolve_left (Units.ne_zero _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricFiberTraceKernel
open MulAction UpperTheory.V.Z.Sym

private theorem smul_quotient_eq_self_iff_exists_conj_out (G : Type) [Group G] (U : Subgroup G) (y : G ⧸ U) (a : G) :
    a • y = y ↔ ∃ u ∈ U, (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out y))) u = a := by
  set g := Quotient.out y with hg
  have hy : ((g : G) : G ⧸ U) = y := Quotient.out_eq y
  rw [← hy, MulAction.Quotient.smul_mk, QuotientGroup.eq]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, smul_eq_mul]
  constructor
  · intro h
    refine ⟨g⁻¹ * a * g, ?_, by group⟩
    have := inv_mem h
    simpa [mul_assoc] using this
  · rintro ⟨u, hu, rfl⟩
    have : (g * u * g⁻¹ * g)⁻¹ * g = u⁻¹ := by group
    rw [this]; exact inv_mem hu

theorem UpperTheory.symmetric_fiber_trace_kernel :
    UpperTheory.V.Z.Sym.Glob.Fib.TrKer := by
  intro Γ G V _ _ _ _ _ B hFin hω hΓ₀ f hf
  classical
  set s := Base.Tw.one B with hs
  let δ : ConjClasses Γ → Γ := fun i => Classical.choose (ConjClasses.exists_rep i)
  have hδ : ∀ i, ConjClasses.mk (δ i) = i := fun i => Classical.choose_spec (ConjClasses.exists_rep i)
  have hRel : ∀ a b : Γ, s.Rel a b ↔ IsConj a b := by
    intro a b
    simp only [Base.Tw.Rel, hs, Base.Tw.one, hΓ₀, Subgroup.mem_bot, MulEquiv.refl_apply, exists_eq_left, mul_one, isConj_iff]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x⁻¹, by group⟩
    · rintro ⟨c, rfl⟩; exact ⟨c⁻¹, by group⟩
  have hCent : ∀ (a x : Γ), x ∈ s.Cent a ↔ x * a = a * x := by
    intro a x
    show (∃ z ∈ B.Γ₀, x⁻¹ * a * (MulEquiv.refl Γ) x = a * z) ↔ _
    simp only [hΓ₀, Subgroup.mem_bot, exists_eq_left, mul_one, MulEquiv.refl_apply]
    constructor
    · intro h; calc x * a = x * (x⁻¹ * a * x) := by rw [h]
        _ = a * x := by group
    · intro h; calc x⁻¹ * a * x = x⁻¹ * (x * a) := by rw [mul_assoc, h]
        _ = a := by group
  have h2 : ∀ z ∈ (⊥ : Subgroup Γ), ∀ y : G ⧸ B.U, B.ι z • y = y := fun z hz y => by
    rw [Subgroup.mem_bot.mp hz, map_one, one_smul]
  have h3 : ∀ h γ : Γ, LinearMap.trace ℂ V (B.W (h * γ * h⁻¹)) = LinearMap.trace ℂ V (B.W γ) := fun h γ => by
    rw [map_mul, LinearMap.trace_mul_comm, ← map_mul, inv_mul_cancel_left]
  have h4 : ∀ u ∈ B.U, ∀ g : G, f (u⁻¹ * g * u) = f g := fun u hu g => by
    have hl := hf.left ⟨u⁻¹, inv_mem hu⟩ (g * u)
    have hr := hf.right ⟨u, hu⟩ g
    simp only [hs, Base.Tw.one, MulEquiv.refl_apply, hω, MonoidHom.one_apply, Units.val_one, inv_one, one_mul] at hl hr
    rw [mul_assoc, hl, hr]
  have h5 : ∀ g : G, {γ | LinearMap.trace ℂ V (B.W γ) * f (g⁻¹ * B.ι γ * g) ≠ 0}.Finite := fun g =>
    (UpperTheory.orbitalFiber_support_finite Γ G V B hFin hΓ₀ f hf g).subset (fun γ h => right_ne_zero_of_mul h)
  have h8 : ∀ i x, x ∈ ((s.Cent (δ i)).subtype).range ↔ x * δ i = δ i * x := fun i x => by
    rw [Subgroup.range_subtype, hCent]
  have h9 : ∀ (i i' : ConjClasses Γ) (h : Γ), δ i' = h * δ i * h⁻¹ → i = i' := fun i i' h e => by
    rw [← hδ i, ← hδ i', ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]; exact ⟨h, e.symm⟩
  have h10 : ∀ (γ : Γ) (g : G), LinearMap.trace ℂ V (B.W γ) * f (g⁻¹ * B.ι γ * g) ≠ 0 →
      ∃ i h, γ = h * δ i * h⁻¹ := fun γ g _ => by
    obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp (hδ (ConjClasses.mk γ)))
    exact ⟨ConjClasses.mk γ, c, hc.symm⟩
  have h7 : ∀ y : G ⧸ B.U, (⊥ : Subgroup Γ).relIndex (Subgroup.comap B.ι (stabilizer G y)) ≠ 0 := fun y => by
    have := hFin.stab (Quotient.out y)
    rw [hΓ₀] at this
    convert this using 2
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, mem_stabilizer_iff, Subgroup.mem_map]
    exact smul_quotient_eq_self_iff_exists_conj_out G B.U y (B.ι x)
  have hT := (Tf.trace Γ G V B hFin s f hf (ConjClasses Γ) δ (fun i j h => by
      rw [← hδ i, ← hδ j, ConjClasses.mk_eq_mk_iff_isConj]; exact (hRel _ _).mp h)
    (fun γ _ => ⟨ConjClasses.mk γ, (hRel _ _).mpr (ConjClasses.mk_eq_mk_iff_isConj.mp (hδ _))⟩)).2
  have hP := UpperTheory.orbitalFiber_pair_correspondence Γ G (ConjClasses Γ) B.ι ⊥ B.U (fun γ => LinearMap.trace ℂ V (B.W γ)) f δ
    (fun i => ↥(s.Cent (δ i))) (fun i => (s.Cent (δ i)).subtype) bot_le h2 h3 h4 h5
    hFin.cls h7 h8 h9 h10
  rw [hT, hP]
  refine finsum_congr fun i => ?_
  simp only [Base.Tw.term, hs, Base.Tw.one, LinearMap.comp_id]
  congr 2
  rw [hΓ₀]; rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberFixedSetSupport
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob Matrix

private theorem hasTr_conj {K : Type} [Field K] {Δ : K} (γ h : DX Δ) (s : K) (hs : HasTr γ s) :
    HasTr (h⁻¹ * γ * h) s := by
  have e : Glob.mt (h⁻¹ * γ * h) = ((h : GL (Fin 2) (Lsq K Δ))⁻¹ : GL (Fin 2) (Lsq K Δ)) * Glob.mt γ * Glob.mt h := by
    rfl
  have e1 : Glob.mt h * (((h : GL (Fin 2) (Lsq K Δ))⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = 1 :=
    Units.mul_inv _
  refine ⟨?_, ?_⟩
  · rw [e, det_mul_comm, ← mul_assoc, e1, one_mul, hs.1]
  · rw [e, trace_mul_comm, ← mul_assoc, e1, one_mul, hs.2]

private theorem hasTr_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ : K} (γ : DX Δ) (γ' : DX (f Δ)) (s : K)
    (h : Glob.mt γ' = (Glob.mt γ).map (lmap f Δ)) (hs : HasTr γ s) : HasTr γ' (f s) := by
  refine ⟨?_, ?_⟩
  · rw [h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hs.1, map_one]
  · rw [h, ← AddMonoidHom.map_trace, hs.2]
    ext <;> simp [lmap]

private theorem ne_zero_of_finprod {I : Type} (f : I → ℂ) (hf : (Function.mulSupport f).Finite) (h : ∏ᶠ i, f i ≠ 0) (i : I) :
    f i ≠ 0 := by
  intro h0
  apply h
  rw [finprod_eq_prod _ hf]
  refine Finset.prod_eq_zero (i := i) ?_ h0
  simp [h0]

theorem UpperTheory.orbitalFiber_fixedSet_support :
    UpperTheory.V.Z.Sym.Glob.Fib.FSSupp := by
  intro F _ _ Δ D hD ι hι t ht γ s g hs hne v hv
  have hconj : HasTr ((g⁻¹ * ι γ * g).1 v) (cv v s) :=
    hasTr_conj ((ι γ).1 v) (g.1 v) _ (hasTr_map (cv v) γ _ s (hι γ v) hs)
  generalize g⁻¹ * ι γ * g = x at hconj hne
  have hfin : (Function.mulSupport fun w => D.fSv t w (x.1 w)).Finite := by
    have h1 : {w | ¬ x.1 w ∈ KD (cv w Δ) (Ov w)}.Finite := Filter.eventually_cofinite.1 x.2
    refine (h1.union D.Sg.finite_toSet).subset fun w hw => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Finset.mem_coe] at hc
    apply hw
    simp only [Dat.fSv, if_neg hc.2, Glob.one, if_pos hc.1]
  have h := ne_zero_of_finprod _ hfin hne v
  simp only [Dat.fSv, if_pos hv] at h
  exact (hD.sig v hv).S_supp _ (ht v hv) _ _ hconj h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberFixedSetConj
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

private lemma zd_comm {K : Type} [Field K] {Δ : K} {z : DX Δ} (hz : z ∈ ZD Δ) (g : DX Δ) : z * g = g * z := by
  obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.1 hz
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha]
  apply Units.ext
  simp only [MonoidHom.comp_apply, Units.val_mul]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ _) _).eq

private lemma conj_sup {G : Type} [Group G] (Z J : Subgroup G) (f : G → ℂ)
    (hZ : ∀ z ∈ Z, ∀ g, z * g = g * z) (hJ : ∀ u ∈ J, ∀ g, f (u⁻¹ * g * u) = f g) :
    ∀ u ∈ Z ⊔ J, ∀ g, f (u⁻¹ * g * u) = f g := by
  let S : Subgroup G :=
    { carrier := {u | ∀ g, f (u⁻¹ * g * u) = f g}
      one_mem' := by intro g; simp
      mul_mem' := by
        intro a b ha hb g
        have : (a * b)⁻¹ * g * (a * b) = b⁻¹ * (a⁻¹ * g * a) * b := by group
        rw [this, hb, ha]
      inv_mem' := by
        intro a ha g
        rw [← ha]
        congr 1
        group }
  have h : Z ⊔ J ≤ S := by
    refine sup_le (fun z hz g => ?_) (fun u hu => hJ u hu)
    rw [mul_assoc, ← hZ z hz, inv_mul_cancel_left]
  exact fun u hu => h hu

theorem UpperTheory.orbitalFiber_fixedSet_conj :
    UpperTheory.V.Z.Sym.Glob.Fib.FSConj := by
  intro F _ _ Δ D hD t ht u hu g
  unfold Dat.FS
  refine finprod_congr fun v => ?_
  have huv : u.1 v ∈ ZD _ ⊔ D.J2v v := by
    simp only [Dat.UZ, RPG.box, Subgroup.mem_iInf, Subgroup.mem_comap] at hu
    exact hu v
  show D.fSv t v ((u.1 v)⁻¹ * g.1 v * u.1 v) = D.fSv t v (g.1 v)
  refine conj_sup _ _ (D.fSv t v) (fun z hz => zd_comm hz) ?_ _ huv _
  intro k hk y
  unfold Dat.fSv
  unfold Dat.J2v at hk
  by_cases hv : v ∈ D.Sg
  · simp only [if_pos hv] at hk ⊢
    have H := (hD.sig v hv).S_inv (t v) (ht v hv)
    rw [(H k hk _).2, (H _ (inv_mem hk) _).1]
  · simp only [if_neg hv] at hk ⊢
    congr 1
    apply propext
    rw [Subgroup.mul_mem_cancel_right _ hk, Subgroup.mul_mem_cancel_left _ (inv_mem hk)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberLevelFinite
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberDetEqOne
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc Matrix

private theorem scal_mem {O L : Type} [CommRing O] [CommRing L] [Algebra O L] (u : Lˣ)
    (d : (integralClosure O L)ˣ)
    (h : u ^ 2 * Units.map ((integralClosure O L).val : integralClosure O L →* L) d = 1) :
    ∃ w : (integralClosure O L)ˣ, Units.map ((integralClosure O L).val : integralClosure O L →* L) w = u := by
  have h1 : u ^ 2 = Units.map ((integralClosure O L).val : integralClosure O L →* L) d⁻¹ := by
    rw [map_inv]; exact eq_inv_of_mul_eq_one_left h
  have h2 : u⁻¹ ^ 2 = Units.map ((integralClosure O L).val : integralClosure O L →* L) d := by
    rw [inv_pow, h1, map_inv, inv_inv]
  have i1 : IsIntegral O (u : L) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [← Units.val_pow_eq_pow_val, h1]
    exact ((d⁻¹ : (integralClosure O L)ˣ) : integralClosure O L).2
  have i2 : IsIntegral O ((u⁻¹ : Lˣ) : L) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [← Units.val_pow_eq_pow_val, h2]
    exact (d : integralClosure O L).2
  exact ⟨⟨⟨u, i1⟩, ⟨(u⁻¹ : Lˣ), i2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩, Units.ext rfl⟩

theorem UpperTheory.orbitalFiber_det_eq_one :
    UpperTheory.V.Z.Sym.Glob.Fib.DetOne := by
  intro O K _ _ _ Δ g hg hs
  have hn : (ZD Δ).Normal := by
    refine ⟨fun n hn x => ?_⟩
    have : x * n * x⁻¹ = n := by
      obtain ⟨z, hz⟩ := Subgroup.mem_subgroupOf.1 hn
      rw [mul_inv_eq_iff_eq_mul]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hz]
      apply Units.ext
      exact ((Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).symm).eq
    rwa [this]
  obtain ⟨s, hsz, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
  refine mul_mem ?_ hk
  obtain ⟨z, hz⟩ := Subgroup.mem_subgroupOf.1 hsz
  obtain ⟨k₀, hk₀⟩ := Subgroup.mem_subgroupOf.1 hk
  have hd : GeneralLinearGroup.det ((s : GL (Fin 2) (Lsq K Δ)) * (k : GL (Fin 2) (Lsq K Δ))) = 1 := hs
  rw [map_mul, ← hz, ← hk₀] at hd
  obtain ⟨w, hw⟩ := scal_mem (O := O) (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ) z)
    (GeneralLinearGroup.det k₀) (by
      rw [← hd]
      congr 1
      · apply Units.ext
        simp [pow_two])
  refine Subgroup.mem_subgroupOf.2 ⟨GeneralLinearGroup.scalar (Fin 2) w, ?_⟩
  rw [← hz, MonoidHom.comp_apply, ← hw]
  apply Units.ext
  ext i j : 1
  by_cases hij : i = j <;> simp [hij, Matrix.diagonal_apply]
end

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc

private theorem comap_relIndex_ne_zero {G H : Type} [Group G] [Group H] (p : G →* H) (A B : Subgroup H)
    (T : Subgroup G) (hAB : A.relIndex B ≠ 0) (hT : ∀ g ∈ T, p g ∈ B) : (A.comap p).relIndex T ≠ 0 := by
  rw [Subgroup.relIndex_comap]
  intro h
  exact hAB (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_le_iff_le_comap.mpr hT) h)

private theorem finset_relIndex_ne_zero {G I : Type} [Group G] (H : I → Subgroup G) (T : Subgroup G) (S : Finset I)
    (h : ∀ v ∈ S, (H v).relIndex T ≠ 0) : ∃ W : Subgroup G, W.relIndex T ≠ 0 ∧ ∀ v ∈ S, W ≤ H v := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨W, hW, hWS⟩ := ih (fun v hv => h v (Finset.mem_insert_of_mem hv))
    refine ⟨H a ⊓ W, Subgroup.relIndex_inf_ne_zero (h a (Finset.mem_insert_self a S)) hW, ?_⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact inf_le_left
    · exact inf_le_right.trans (hWS v hv)

theorem UpperTheory.orbitalFiber_level_finite :
    UpperTheory.V.Z.Sym.Glob.Fib.LevFin := by
  unfold Fib.LevFin
  intro F _ _ Δ D hD
  have hDet : Fib.DetOne := UpperTheory.orbitalFiber_det_eq_one
  unfold Fib.DetOne at hDet
  set P := rpg (fun v => ↥(DX ((cv v) Δ))) (fun v => KD ((cv v) Δ) (Ov v)) with hP
  have hle : ∀ v, D.J2v v ≤ KD ((cv v) Δ) (Ov v) := by
    intro v
    rw [Dat.J2v.eq_1]
    split_ifs with hv
    · exact SigOk.levelTwoLeIntegral (hD.sig v hv)
    · exact le_rfl
  have hT : ∀ v, ∀ g ∈ D.UZ ⊓ SA Δ, P.p v g ∈ KD ((cv v) Δ) (Ov v) := by
    intro v g hg
    have h1 : g ∈ D.UZ := hg.1
    have h2 : g ∈ SA Δ := hg.2
    rw [Dat.UZ.eq_1, RPG.box.eq_1, Subgroup.mem_iInf] at h1
    rw [SA.eq_1, Subgroup.mem_iInf] at h2
    have a := h1 v
    have b := h2 v
    rw [Subgroup.mem_comap] at a b
    exact hDet _ _ _ _ (sup_le_sup_left (hle v) _ a) b
  have hfin : ∀ v ∈ D.Sg, ((D.J2v v).comap (P.p v)).relIndex (D.UZ ⊓ SA Δ) ≠ 0 := by
    intro v hv
    apply comap_relIndex_ne_zero (P.p v) (D.J2v v) (KD ((cv v) Δ) (Ov v))
    · rw [Dat.J2v.eq_1, if_pos hv]
      exact SigOk.levelTwoFiniteIndex (hD.sig v hv)
    · exact hT v
  obtain ⟨W, hW, hWS⟩ := finset_relIndex_ne_zero (fun v => (D.J2v v).comap (P.p v)) _ D.Sg hfin
  have hsub : W ⊓ (D.UZ ⊓ SA Δ) ≤ D.U2 := by
    intro g hg
    rw [Dat.U2.eq_1, RPG.box.eq_1, Subgroup.mem_iInf]
    intro v
    rw [Subgroup.mem_comap]
    by_cases hv : v ∈ D.Sg
    · exact hWS v hv hg.1
    · have e := hT v g hg.2
      rw [Dat.J2v.eq_1, if_neg hv]
      exact e
  refine ⟨?_, ?_⟩
  · rw [Dat.U2.eq_1, Dat.UZ.eq_1, RPG.box.eq_1, RPG.box.eq_1]
    exact iInf_mono fun v => Subgroup.comap_mono le_sup_right
  · intro h
    apply hW
    rw [← Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_eq_zero_of_le_left hsub h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberHasTraceLaw
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob Matrix in
private theorem UpperTheory.star_diagonal_entry_eq {K : Type} [Field K] {Δ : K} (γ : DX Δ) :
    star (mt γ 0 0) = mt γ 1 1 := by
  have h : GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) (γ : GL (Fin 2) (Lsq K Δ)) =
      (wJ Δ)⁻¹ * (γ : GL (Fin 2) (Lsq K Δ)) * ((wJ Δ)⁻¹)⁻¹ := γ.2
  have h1 := congrArg (fun g : GL (Fin 2) (Lsq K Δ) => (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0) h
  have hw : (((wJ Δ)⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![0, -1; 1, 0] := rfl
  have hw' : ((wJ Δ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![0, 1; -1, 0] := rfl
  simp only [inv_inv, Units.val_mul, hw, hw'] at h1
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, starRingEnd_apply] using h1

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob Matrix in
theorem UpperTheory.orbitalFiber_hasTraceLaw :
    UpperTheory.V.Z.Sym.Glob.Fib.HasTrLaw := by
  intro K _ Δ γ
  have hmem : γ ∈ SU Δ ↔ (mt γ).det = 1 := by
    rw [SU, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hmem]
    constructor
    · intro hd
      refine ⟨(mt γ).trace.re, hd, ?_⟩
      have := UpperTheory.star_diagonal_entry_eq γ
      ext
      · simp
      · rw [Matrix.trace_fin_two, ← this]
        simp
    · rintro ⟨s, hs, _⟩
      exact hs
  · intro s s' hs hs'
    have := congrArg QuadraticAlgebra.re (hs.2.symm.trans hs'.2)
    simpa using this
  · intro h s
    have e : mt (h * γ * h⁻¹) = ((h : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * mt γ *
        (((h : GL (Fin 2) (Lsq K Δ))⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) := rfl
    unfold HasTr
    rw [e, Matrix.det_units_conj, Matrix.trace_units_conj]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberRepresentatives
private theorem reps_setoid {G : Type} (r : Setoid G) (Y : Finset G) (x₀ : G)
    (hY : ∀ g, ∃ y ∈ Y, r y g) :
    ∃ (n : ℕ) (x : Fin (n + 1) → G), x 0 = x₀ ∧ (∀ i, x i = x₀ ∨ x i ∈ Y) ∧
      (∀ i j, r (x i) (x j) → i = j) ∧ ∀ g, ∃ i, r (x i) g := by
  classical
  have hσ : ∀ q : Quotient r, ∃ y ∈ Y, Quotient.mk r y = q := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨y, hy, h⟩ := hY g
      exact ⟨y, hy, Quotient.sound h⟩
  choose σ hσY hσ using hσ
  haveI : Finite (Quotient r) := by
    refine Finite.of_injective (fun q => (⟨σ q, hσY q⟩ : Y)) ?_
    intro a b h
    have h' : σ a = σ b := congrArg Subtype.val h
    rw [← hσ a, ← hσ b, h']
  haveI : Nonempty (Quotient r) := ⟨Quotient.mk r x₀⟩
  obtain ⟨n, hn⟩ : ∃ n, Nat.card (Quotient r) = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := Quotient r)).ne'
  let e₀ : Fin (n + 1) ≃ Quotient r := (Finite.equivFinOfCardEq hn).symm
  let e : Fin (n + 1) ≃ Quotient r := e₀.trans (Equiv.swap (e₀ 0) (Quotient.mk r x₀))
  have he : e 0 = Quotient.mk r x₀ := by simp [e]
  let x : Fin (n + 1) → G := fun i => if i = 0 then x₀ else σ (e i)
  have hx : ∀ i, Quotient.mk r (x i) = e i := by
    intro i
    by_cases h : i = 0
    · subst h; simp [x, he]
    · simp [x, h, hσ]
  refine ⟨n, x, by simp [x], ?_, ?_, ?_⟩
  · intro i
    by_cases h : i = 0
    · left; simp [x, h]
    · right; simp [x, h, hσY]
  · intro i j h
    apply e.injective
    rw [← hx, ← hx]
    exact Quotient.sound h
  · intro g
    refine ⟨e.symm (Quotient.mk r g), Quotient.exact ?_⟩
    rw [hx]; simp

theorem UpperTheory.orbitalFiber_representatives :
    UpperTheory.V.Z.Sym.Glob.Fib.Reps := by
  intro Γ G _ _ ι S U' Y x₀ hS hY
  let r : Setoid G :=
    { r := fun a b => ∃ γ, ∃ s ∈ S, ∃ u ∈ U', b = ι γ * s * a * u
      iseqv :=
        { refl := fun a => ⟨1, 1, S.one_mem, 1, U'.one_mem, by simp⟩
          symm := by
            rintro a b ⟨γ, s, hs, u, hu, rfl⟩
            refine ⟨γ⁻¹, ι γ * s⁻¹ * (ι γ)⁻¹, hS.conj_mem _ (S.inv_mem hs) _, u⁻¹, U'.inv_mem hu, ?_⟩
            rw [map_inv]; group
          trans := by
            rintro a b c ⟨γ, s, hs, u, hu, rfl⟩ ⟨γ', s', hs', u', hu', rfl⟩
            refine ⟨γ' * γ, (ι γ)⁻¹ * s' * (ι γ)⁻¹⁻¹ * s,
              S.mul_mem (hS.conj_mem _ hs' _) hs, u * u', U'.mul_mem hu hu', ?_⟩
            rw [map_mul]; group } }
  obtain ⟨n, x, h0, h1, h2, h3⟩ := reps_setoid r Y x₀ (by
    intro g
    obtain ⟨γ, s, hs, y, hy, u, hu, h⟩ := hY g
    exact ⟨y, hy, γ, s, hs, u, hu, h⟩)
  refine ⟨n, x, h0, h1, fun i j γ s hs u hu h => h2 i j ⟨γ, s, hs, u, hu, h⟩, fun g => ?_⟩
  obtain ⟨i, γ, s, hs, u, hu, h⟩ := h3 g
  exact ⟨i, γ, s, hs, u, hu, h⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.NormalOfCenter
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open MulAction Fib

private lemma normal_of_center {Γ : Type} [Group Γ] {A : Subgroup Γ} (h : A ≤ Subgroup.center Γ) : A.Normal := ⟨fun n hn g => by
  rw [Subgroup.mem_center_iff.mp (h hn) g, mul_inv_cancel_right]
  exact hn⟩

private lemma stab_mk {G : Type} [Group G] (U : Subgroup G) (g : G) :
    stabilizer G (g : G ⧸ U) = U.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_stabilizer_iff, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, MulAction.Quotient.smul_coe, eq_comm,
    QuotientGroup.eq]
  simp [mul_assoc]

private lemma triv_act {Γ G : Type} [Group Γ] [Group G] (ι : Γ →* G) (U : Subgroup G) (z : Γ)
    (h1 : ι z ∈ Subgroup.center G) (h2 : ι z ∈ U) (y : G ⧸ U) : ι z • y = y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rw [MulAction.Quotient.smul_coe, QuotientGroup.eq, smul_eq_mul, ← Subgroup.mem_center_iff.mp h1 g]
  simpa [mul_assoc] using U.inv_mem h2

private theorem glue (hM : Master) (hTr : TrKer) (hPair : Pair)
    {Γ G : Type} [Group Γ] [Group G] (ι : Γ →* G) (S U U' : Subgroup G) (Γ₁ Γ₀ : Subgroup Γ) (ι₁ : Γ₁ →* S)
    (h1 : ∀ γ, (ι₁ γ : G) = ι γ) (h2 : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S) (h3 : Γ₁.Normal) (h4 : Γ₀ ≤ Subgroup.center Γ)
    (h5' : ∀ z ∈ Γ₀, ι z ∈ Subgroup.center G ∧ ι z ∈ U') (h6 : U ≤ U') (h7 : U.relIndex (U' ⊓ S) ≠ 0)
    (h8 : ∀ x : G, ∃ T : Finset S, ∀ s, ∃ h, ∃ t ∈ T, ∃ u : S, x⁻¹ * u * x ∈ U ∧ s = ι₁ h * t * u)
    (h9 : ∀ x : G, {h | x⁻¹ * ι₁ h * x ∈ U}.Finite)
    (h10 : ∃ T : Finset G, ∀ g, ∃ γ, ∃ s ∈ T, ∃ u ∈ U', g = ι γ * s * u)
    (h11' : ∀ g, Γ₀.relIndex ((U'.map (MulAut.conj g).toMonoidHom).comap ι) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (x : Fin (n + 1) → G),
      (∀ i j γ, ∀ s ∈ S, ∀ u ∈ U', x j = ι γ * s * x i * u → i = j) → (∀ g, ∃ i γ, ∃ s ∈ S, ∃ u ∈ U', g = ι γ * s * x i * u) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (f : G → ℂ) (B : Fin (n + 1) → Base Γ₁ S V)
        (cl : Γ → ℂ) (I : Type) (δ : I → Γ) (Hi : I → Type) [∀ i, Group (Hi i)] (φ : ∀ i, Hi i →* Γ),
      (∀ u ∈ U', ∀ g, f (u⁻¹ * g * u) = f g) → (∀ g, {γ : Γ₁ | f (g⁻¹ * ι γ * g) ≠ 0}.Finite) →
      (∀ i, (B i).ι = ι₁) → (∀ i (s : S), s ∈ (B i).U ↔ (x i)⁻¹ * s * x i ∈ U) → (∀ i, (B i).ω = 1) → (∀ i, (B i).Γ₀ = ⊥) →
      (∀ i, (B i).Fin) → (∀ i, (Base.Tw.one (B i)).IsTest fun g : S => f ((x i)⁻¹ * g * x i)) →
      (∀ h γ, cl (h * γ * h⁻¹) = cl γ) → (∀ g, cl g ≠ 0 → g ∈ Γ₁) → (∀ i (γ : Γ₁), LinearMap.trace ℂ V ((B i).W γ) = cl γ) →
      (∀ i x, x ∈ (φ i).range ↔ x * δ i = δ i * x) → (∀ i i' h, δ i' = h * δ i * h⁻¹ → i = i') →
      (∀ γ g, cl γ * f (g⁻¹ * ι γ * g) ≠ 0 → ∃ i h, γ = h * δ i * h⁻¹) →
      ∑ i, LinearMap.trace ℂ (B i).Forms ((Base.Tw.one (B i)).R fun g : S => f ((x i)⁻¹ * g * x i)) =
        c * ∑ᶠ i, cl (δ i) * gqOn (ι.comp (φ i)) (Γ₀.comap (φ i)) U' fun y => f (y.out⁻¹ * ι (δ i) * y.out) := by
  classical
  have hΓ₀n : Γ₀.Normal := normal_of_center h4
  have htriv : ∀ z ∈ Γ₀, ∀ y : G ⧸ U', ι z • y = y := fun z hz y =>
    triv_act ι U' z (h5' z hz).1 (h5' z hz).2 y
  have hstab : ∀ y : G ⧸ U', Γ₀.relIndex ((stabilizer G y).comap ι) ≠ 0 := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [stab_mk]
    exact h11' g
  obtain ⟨c, hc, hmain⟩ := hM Γ G ι S U U' Γ₁ Γ₀ ι₁ h1 h2 h3 hΓ₀n htriv h6 h7 h8 h9 h10 hstab
  refine ⟨c, hc, ?_⟩
  intro n x hdis hcov V _ _ _ f B cl I δ Hi _ φ hf hfin hBι hBU hω hΓ hBF hT hcl hcl1 htr hφ hδ hsupp
  let Φ : G → ℂ := fun g => ∑ᶠ γ : Γ, cl γ * f (g⁻¹ * ι γ * g)
  have hsub : ∀ g : G, ∑ᶠ γ : Γ₁, cl γ * f (g⁻¹ * ι γ * g) = Φ g := by
    intro g
    have hs : Function.support (fun γ => cl γ * f (g⁻¹ * ι γ * g)) ⊆ (Γ₁ : Set Γ) := by
      intro γ hγ
      exact hcl1 γ (left_ne_zero_of_mul hγ)
    show _ = ∑ᶠ γ : Γ, cl γ * f (g⁻¹ * ι γ * g)
    refine (finsum_set_coe_eq_finsum_mem (f := fun γ => cl γ * f (g⁻¹ * ι γ * g)) (Γ₁ : Set Γ)).trans ?_
    rw [finsum_mem_def, Set.indicator_eq_self.2 hs]
  have hΦl : ∀ (h : Γ) (g : G), Φ (ι h * g) = Φ g := by
    intro h g
    show ∑ᶠ γ : Γ, cl γ * f ((ι h * g)⁻¹ * ι γ * (ι h * g)) = ∑ᶠ γ : Γ, cl γ * f (g⁻¹ * ι γ * g)
    rw [← finsum_comp_equiv (MulAut.conj h).toEquiv]
    apply finsum_congr
    intro γ
    show cl (h * γ * h⁻¹) * f ((ι h * g)⁻¹ * ι (h * γ * h⁻¹) * (ι h * g)) = cl γ * f (g⁻¹ * ι γ * g)
    rw [hcl]
    congr 2
    simp only [map_mul, map_inv]
    group
  have hΦr : ∀ u ∈ U', ∀ g : G, Φ (g * u) = Φ g := by
    intro u hu g
    show ∑ᶠ γ : Γ, cl γ * f ((g * u)⁻¹ * ι γ * (g * u)) = ∑ᶠ γ : Γ, cl γ * f (g⁻¹ * ι γ * g)
    apply finsum_congr
    intro γ
    rw [← hf u hu (g⁻¹ * ι γ * g)]
    congr 2
    group
  have hM' := hmain (Fin (n + 1)) x (fun i => (B i).U) Φ hdis hcov hBU hΦl hΦr
  beta_reduce at hM'
  have hL : ∀ i, LinearMap.trace ℂ (B i).Forms ((Base.Tw.one (B i)).R fun g : S => f ((x i)⁻¹ * g * x i)) =
      gqOn ι₁ ⊥ (B i).U (fun s => Φ (↑(Quotient.out s) * x i)) := by
    intro i
    rw [hTr _ _ _ (B i) (hBF i) (hω i) (hΓ i) _ (hT i), hBι i]
    congr 1
    funext y
    rw [← hsub]
    apply finsum_congr
    intro γ
    rw [htr i γ]
    beta_reduce
    congr 2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, h1]
    group
  have hfinP : ∀ g : G, {γ | cl γ * f (g⁻¹ * ι γ * g) ≠ 0}.Finite := by
    intro g
    refine ((hfin g).image Subtype.val).subset ?_
    intro γ hγ
    have hγ1 := hcl1 γ (left_ne_zero_of_mul hγ)
    exact ⟨⟨γ, hγ1⟩, right_ne_zero_of_mul hγ, rfl⟩
  have hP := hPair Γ G I ι Γ₀ U' cl f δ Hi φ h4 htriv hcl hf hfinP h10 hstab hφ hδ hsupp
  rw [Finset.sum_congr rfl (fun i _ => hL i), hM']
  exact congrArg (fun z => (c : ℂ) * z) hP

end UpperTheory.V.Z.Sym.Glob

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc MulAction Fib

private lemma dx_ext' {K : Type} [Field K] {Δ : K} {g g' : DX Δ} (h : mt g = mt g') : g = g' :=
  Subtype.ext (Units.ext h)

private lemma comm_abs {G A : Type} [Group G] [CommGroup A] (d : G →* A) (a b : G) : a * b * a⁻¹ * b⁻¹ ∈ d.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_right_comm (d a), mul_inv_cancel, one_mul,
    mul_inv_cancel]

private lemma comm_mem {F : Type} [Field F] [NumberField F] {Δ : F} (a b : DA Δ) : a * b * a⁻¹ * b⁻¹ ∈ SA Δ := by
  refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 ?_
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  exact comm_abs (GeneralLinearGroup.det.comp (DX (cv v Δ)).subtype) _ _

private lemma trz {A : Type} [Group A] (g : A) : LinearMap.trace ℂ PUnit ((1 : Representation ℂ A PUnit) g) = 0 := by
  rw [Subsingleton.elim ((1 : Representation ℂ A PUnit) g) 0, map_zero]

section
variable {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ)

private lemma delta_ne (ok : D.Ok) : Δ ≠ 0 := by
  intro h0
  have w : NumberField.InfinitePlace F := Classical.arbitrary _
  have σ : F →+* ℝ := NumberField.InfinitePlace.embedding_of_isReal (ok.real.isReal w)
  have := ok.neg σ
  rw [h0, map_zero] at this
  exact lt_irrefl _ this

private lemma conK (bK : BaseK) (fK : FinK) (ok : D.Ok) (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) :
    ZD Δ ≤ Subgroup.center (DX Δ) ∧ (∀ z ∈ ZD Δ, ι z ∈ Subgroup.center (DA Δ) ∧ ι z ∈ D.UZ) ∧
    (∃ T : Finset (DA Δ), ∀ g, ∃ γ, ∃ s ∈ T, ∃ u ∈ D.UZ, g = ι γ * s * u) ∧
    ∀ g, (ZD Δ).relIndex ((D.UZ.map (MulAut.conj g).toMonoidHom).comap ι) ≠ 0 := by
  obtain ⟨B, hB, -⟩ := bK F Δ D ok PUnit 1 0 (fun _ _ _ _ => Subsingleton.elim _ _) (fun g _ _ _ => trz g)
  have hF := (fK F Δ D ok PUnit 0 B hB).1
  have hBι : B.ι = ι := by
    ext γ : 1
    apply Subtype.ext
    funext v
    apply dx_ext
    rw [hB.ι γ v, hι γ v]
  have hU := hB.U
  have hΓ := hB.Γ₀
  refine ⟨?_, fun z hz => ?_, ?_, fun g => ?_⟩
  · have := B.cenΓ
    rwa [hΓ] at this
  · rw [← hΓ] at hz
    have h1 := B.cenG z hz
    have h2 := B.memU z hz
    rw [hBι] at h1 h2
    rw [hU] at h2
    exact ⟨h1, h2⟩
  · obtain ⟨T, hT⟩ := hF.cls
    refine ⟨T, fun g => ?_⟩
    have := hT g
    rwa [hU, hBι] at this
  · have := hF.stab g
    rwa [hU, hBι, hΓ] at this

private lemma bι {V : Type} [AddCommGroup V] [Module ℂ V] (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) (ch : F → ℂ) (x : DA Δ)
    (B : Base (SU Δ) (SA Δ) V) (hB : D.IsBS ch x B) (γ : SU Δ) : ((B.ι γ : SA Δ) : DA Δ) = ι γ := by
  refine Subtype.ext (funext fun v => dx_ext ?_)
  rw [hB.ι, hι]

private lemma baseP (bS : BaseS) (ok : D.Ok) (x : DA Δ) : ∃ B : Base (SU Δ) (SA Δ) PUnit, D.IsBS 0 x B := by
  obtain ⟨B, hB, -⟩ := bS F Δ D ok PUnit 1 0 (fun γ _ _ => trz γ) x
  exact ⟨B, hB⟩

private lemma conS (bS : BaseS) (fS : FinS) (ok : D.Ok) (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) :
    ∃ ι₁ : SU Δ →* SA Δ, (∀ γ, ((ι₁ γ : SA Δ) : DA Δ) = ι (γ : DX Δ)) ∧
    (∀ x : DA Δ, ∃ T : Finset (SA Δ), ∀ s, ∃ h, ∃ t ∈ T, ∃ u : SA Δ, x⁻¹ * u * x ∈ D.U2 ∧ s = ι₁ h * t * u) ∧
    ∀ x : DA Δ, {h : SU Δ | x⁻¹ * (ι₁ h : DA Δ) * x ∈ D.U2}.Finite := by
  obtain ⟨B0, hB0⟩ := baseP D bS ok 1
  have hι' : ∀ (x : DA Δ) (B : Base (SU Δ) (SA Δ) PUnit), D.IsBS 0 x B → B.ι = B0.ι := fun x B hB => by
    ext h : 1
    apply Subtype.ext
    rw [bι D ι hι 0 x B hB h, bι D ι hι 0 1 B0 hB0 h]
  refine ⟨B0.ι, fun γ => bι D ι hι 0 1 B0 hB0 γ, fun x => ?_, fun x => ?_⟩
  · obtain ⟨B, hB⟩ := baseP D bS ok x
    obtain ⟨T, hT⟩ := (fS F Δ D ok PUnit 0 x B hB).1.cls
    refine ⟨T, fun s => ?_⟩
    obtain ⟨h, t, ht, u, hu, rfl⟩ := hT s
    exact ⟨h, t, ht, u, (hB.U u).mp hu, by rw [hι' x B hB]⟩
  · obtain ⟨B, hB⟩ := baseP D bS ok x
    have hfin := (fS F Δ D ok PUnit 0 x B hB).1.stab 1
    rw [hB.Γ₀, Subgroup.relIndex_bot_left] at hfin
    have hK := Nat.finite_of_card_ne_zero hfin
    refine (Set.finite_coe_iff.mp hK).subset ?_
    intro h hh
    have hm : B.ι h ∈ B.U := by
      rw [hB.U, hι' x B hB]
      exact hh
    have he : (MulAut.conj (1 : SA Δ)).toMonoidHom (B.ι h) = B.ι h := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, one_mul, inv_one, mul_one]
    exact ⟨B.ι h, hm, he⟩

private lemma conN : (SA Δ).Normal := by
  unfold SA
  exact Subgroup.normal_iInf_normal fun v => Subgroup.Normal.comap (by unfold SU; infer_instance) _

private lemma conF (hSF : SuppFin) (bS : BaseS) (fS : FinS) (ok : D.Ok) (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) (t : Dat.Par F)
    (ht : D.Cone t) (g : DA Δ) : {γ : SU Δ | D.FS t (g⁻¹ * ι γ * g) ≠ 0}.Finite := by
  obtain ⟨B, hB⟩ := baseP D bS ok g
  have h1 := fS F Δ D ok PUnit 0 g B hB
  have h2 := hSF _ _ _ B h1.1 hB.Γ₀ _ (h1.2 t ht) 1
  refine h2.subset ?_
  intro γ hγ
  simp only [Set.mem_setOf_eq, Dat.FSx, inv_one, mul_one, one_mul]
  rw [bι D ι hι 0 g B hB γ]
  exact hγ

private lemma clEx (hH : HasTrLaw) (ch : F → ℂ) : ∃ cl : DX Δ → ℂ, (∀ g s, HasTr g s → cl g = ch s) ∧ (∀ g, cl g ≠ 0 → g ∈ SU Δ) ∧
    ∀ h g, cl (h * g * h⁻¹) = cl g := by
  classical
  let cl : DX Δ → ℂ := fun g => if h : ∃ s, HasTr g s then ch h.choose else 0
  have key : ∀ g s, HasTr g s → cl g = ch s := by
    intro g s hs
    have he : ∃ s, HasTr g s := ⟨s, hs⟩
    show (if h : ∃ s, HasTr g s then ch h.choose else 0) = ch s
    rw [dite_eq_left he, (hH F Δ g).2.1 _ _ he.choose_spec hs]
  have zero : ∀ g, ¬ (∃ s, HasTr g s) → cl g = 0 := fun g he => dif_neg he
  refine ⟨cl, key, ?_, ?_⟩
  · intro g hg
    by_contra hn
    exact hg (zero g (fun he => hn ((hH F Δ g).1.mpr he)))
  · intro h g
    by_cases he : ∃ s, HasTr g s
    · obtain ⟨s, hs⟩ := he
      rw [key g s hs, key _ s (((hH F Δ g).2.2 h s).mpr hs)]
    · rw [zero g he, zero]
      rintro ⟨s, hs⟩
      exact he ⟨s, ((hH F Δ g).2.2 h s).mp hs⟩

end

set_option maxHeartbeats 3000000 in
private theorem fibre_of (hM : Master) (hTr : TrKer) (hSF : SuppFin) (hPair : Pair) (hReps : Reps) (hLev : LevFin) (hC : FSConj)
    (hSu : FSSupp) (hH : HasTrLaw) (bS : BaseS) (bK : BaseK) (fS : FinS) (fK : FinK) (cR : ClassRep) (eA : EmbAlg) : Fibre := by
  intro F _ _ Δ D ok ι hι x₀ hx₀
  have hΔ := delta_ne D ok
  obtain ⟨hU, hr⟩ := hLev F Δ D ok
  obtain ⟨hZ, hZt, hcls, hstab⟩ := conK D bK fK ok ι hι
  obtain ⟨ι₁, hι₁, hSc, hSf⟩ := conS D bS fS ok ι hι
  have hN1 : (SU Δ).Normal := MonoidHom.normal_ker _
  obtain ⟨c, hc, hall⟩ := glue hM hTr hPair ι (SA Δ) D.U2 D.UZ (SU Δ) (ZD Δ) ι₁ hι₁ comm_mem hN1 hZ hZt hU hr hSc hSf hcls hstab
  obtain ⟨Y, hY, hYc⟩ := cR F Δ D ok ι hι
  obtain ⟨n, x, hx0, hxY, hsep, hcov⟩ := hReps (DX Δ) (DA Δ) ι (SA Δ) D.UZ Y x₀ conN (fun g => by
    obtain ⟨γ, s, hs, y, hy, u, hu, e⟩ := hYc g
    exact ⟨γ, s, hs, y, hy, u, hU hu, e⟩)
  refine ⟨n, x, c, hx0, fun i => ?_, hc, ?_⟩
  · rcases hxY i with h | h
    · rw [h]; exact hx₀
    · exact hY _ h
  intro V _ _ _ ch B hB t ht I τ γ j hinj hi hcv
  obtain ⟨cl, hcl, hcl0, hclc⟩ := clEx hH ch
  have hE := fun i => eA F Δ (τ i) hΔ (hi i).1 (γ i) (hi i).2.1
  have key := hall n x hsep hcov V (D.FS t) B cl I γ (fun i => (Etau F (τ i))ˣ) j
    (fun u hu g => hC F Δ D ok t ht u hu g) (fun g => conF D hSF bS fS ok ι hι t ht g)
    (fun i => by
      ext1 γ'
      exact Subtype.ext ((bι D ι hι ch (x i) (B i) (hB i) γ').trans (hι₁ γ').symm))
    (fun i => (hB i).U) (fun i => (hB i).ω) (fun i => (hB i).Γ₀) (fun i => (fS F Δ D ok V ch (x i) (B i) (hB i)).1)
    (fun i => (fS F Δ D ok V ch (x i) (B i) (hB i)).2 t ht) hclc hcl0
    (fun i γ' => by
      obtain ⟨s, hs⟩ := (hH F Δ γ').1.1 γ'.2
      rw [(hB i).tr γ' s hs, hcl _ s hs])
    (fun i y => ((hE i).2.1 (j i) (hi i).2.2).2.1 y)
    (fun i i' h e => by
      have h1 : HasTr (γ i) (τ i') := ((hH F Δ (γ i)).2.2 h _).1 (e ▸ (hi i').2.1)
      exact hinj ((hH F Δ (γ i)).2.1 _ _ (hi i).2.1 h1))
    (fun γ' g hne => by
      obtain ⟨s, hs⟩ := (hH F Δ γ').1.1 (hcl0 γ' (left_ne_zero_of_mul hne))
      obtain ⟨i, rfl⟩ := hcv γ' s hs (hSu F Δ D ok ι hι t ht γ' s g hs (right_ne_zero_of_mul hne))
      obtain ⟨y, hy⟩ := (hE i).2.2 γ' hs
      exact ⟨i, y⁻¹, by rw [hy, inv_inv]⟩)
  refine key.trans (congrArg _ (finsum_congr fun i => ?_))
  rw [hcl _ _ (hi i).2.1, ((hE i).2.1 (j i) (hi i).2.2).2.2]

end UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Glob.fibre :
    UpperTheory.V.Z.Sym.Glob.Fibre :=
  UpperTheory.V.Z.Sym.Glob.fibre_of UpperTheory.symmetric_fiber_master_formula UpperTheory.symmetric_fiber_trace_kernel UpperTheory.orbitalFiber_support_finite UpperTheory.orbitalFiber_pair_correspondence UpperTheory.orbitalFiber_representatives
    UpperTheory.orbitalFiber_level_finite UpperTheory.orbitalFiber_fixedSet_conj UpperTheory.orbitalFiber_fixedSet_support UpperTheory.orbitalFiber_hasTraceLaw UpperTheory.V.Z.Sym.Glob.baseS UpperTheory.V.Z.Sym.Glob.baseK
    UpperTheory.V.Z.Sym.Glob.finS UpperTheory.V.Z.Sym.Glob.finK UpperTheory.V.Z.Sym.Glob.classRep UpperTheory.V.Z.Sym.Glob.embAlg
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.GqS
open NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Glob.gqS :
    UpperTheory.V.Z.Sym.Glob.GqS := by
  intro F _ _ Δ D hD ι hι t ht τ hτ γ j hγ hj
  haveI := hD.real
  have hreg : τ ^ 2 - 4 ≠ 0 := cm_ne hτ
  have htr : ∀ (g : DX Δ) (v : Pl F), HasTr g τ → HasTr ((ι g).1 v) (cv v τ) :=
    fun g v hg => hasTr_map (cv v) (hι g v) hg
  by_cases hA : D.admitted t τ
  · rw [show one (D.admitted t τ) = 1 from if_pos hA, one_mul]
    refine gqD D hD ι hι t ht τ hτ hA γ j hγ hj γ (D.fSv t) ?_ (fun v => ((D.S v).cS : ℂ))
      (fun v => gOrb (Ov v) (jstd ((cv v) τ)) 1 (toUnit QuadraticAlgebra.omega)) ?_
    · intro v u hu x
      by_cases hv : v ∈ D.Sg
      · have hS := hD.sig v hv
        have hu' : u ∈ (D.S v).J2 := by simpa [Dat.J2v, hv] using hu
        simp only [Dat.fSv, if_pos hv]
        rw [(hS.S_inv (t v) (ht v hv) u hu' _).2, (hS.S_inv (t v) (ht v hv) u⁻¹ (inv_mem hu') _).1]
      · have hu' : u ∈ KD ((cv v) Δ) (Ov v) := by simpa [Dat.J2v, hv] using hu
        have hiff : u⁻¹ * x * u ∈ KD ((cv v) Δ) (Ov v) ↔ x ∈ KD ((cv v) Δ) (Ov v) := by
          rw [(KD ((cv v) Δ) (Ov v)).mul_mem_cancel_right hu',
            (KD ((cv v) Δ) (Ov v)).mul_mem_cancel_left (inv_mem hu')]
        simp only [Dat.fSv, if_neg hv, one]
        by_cases hx : x ∈ KD ((cv v) Δ) (Ov v)
        · rw [if_pos hx, if_pos (hiff.2 hx)]
        · rw [if_neg hx, if_neg (fun h => hx (hiff.1 h))]
    · intro v jv hjv
      have hgv : HasTr ((ι γ).1 v) (cv v τ) := htr γ v hγ
      have hrv := cv_reg hreg v
      obtain ⟨z, hz⟩ := zEx hrv
      refine ⟨emb_comm hjv, ?_⟩
      by_cases hv : v ∈ D.Sg
      · have hS := hD.sig v hv
        obtain ⟨hF, -, hO, -, -⟩ := hS.D_orb (t v) (ht v hv) _ _ jv hrv hgv hjv z hz
        have e1 : D.fSv t v = (D.S v).fS (t v) := by
          funext g
          simp [Dat.fSv, hv]
        have e2 : D.J2v v = (D.S v).J2 := by simp [Dat.J2v, hv]
        rw [e1, e2]
        refine ⟨hF, fun _ => ?_, fun h => absurd hv h⟩
        rw [hO, show one (Ind _ _ _) = 1 from if_pos (hA v hv), mul_one]
      · have hL := hD.off v hv
        have e1 : D.fSv t v = fun g => one (g ∈ KD ((cv v) Δ) (Ov v)) := by
          funext g
          simp [Dat.fSv, hv]
        have e2 : D.J2v v = KD ((cv v) Δ) (Ov v) := by simp [Dat.J2v, hv]
        rw [e1, e2]
        refine ⟨(finD _ _ _ _ hL hrv _ jv hgv hjv).1, fun h => absurd h hv, fun _ =>
          ⟨(locD _ _ _ _ hL hrv _ jv hgv hjv (D.χ v) (hD.chi v).1 z hz).1, fun hK hu =>
            ⟨if_pos hK, fun y hy => ?_⟩⟩⟩
        have hy' : y⁻¹ * (ι γ).1 v * y ∈ ZD ((cv v) Δ) ⊔ KD ((cv v) Δ) (Ov v) := by
          by_contra hn
          exact hy (if_neg (fun h => hn (le_sup_right (a := ZD ((cv v) Δ)) h)))
        exact (oneD _ _ _ _ hL hrv _ jv hgv hjv hK hu).2.1 y hy'
  · rw [show one (D.admitted t τ) = 0 from if_neg hA, zero_mul, mul_zero]
    apply gqOn_zero
    intro y
    obtain ⟨v, hv, hI⟩ : ∃ v ∈ D.Sg, ¬ Ind (D.S v).H ((cv v) τ) (t v) := by
      simpa [Dat.admitted] using hA
    have heq : ((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v =
        ((Quotient.out y).1 v)⁻¹ * (ι γ).1 v * (Quotient.out y).1 v := rfl
    have hgtr : HasTr (((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v) (cv v τ) := by
      rw [heq]
      exact hasTr_conj (htr γ v hγ) _
    have hz : D.fSv t v (((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v) = 0 := by
      simp only [Dat.fSv, if_pos hv]
      by_contra hne
      exact hI ((hD.sig v hv).S_supp (t v) (ht v hv) _ _ hgtr hne)
    exact fin_mulSupp (D.fSv t) D.Sg (fun w hw k hk => by simp [Dat.fSv, hw, one, hk]) _ hz
end

namespace UpperTheory.V.Z.Sym.Glob

open NumberField Loc

private theorem aux_statement_10 {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (hD : D.Ok) (t : Dat.Par F)
    (ht : D.Cone t) (τ : F) (h : D.admitted t τ) : τ ^ 2 - 4 ≠ 0 := by
  intro h0
  obtain ⟨v, hv⟩ := hD.ne
  refine ((hD.sig v hv).reg (t v) (ht v hv) _ (h v hv)).2 ?_
  have h2 : IsIntegral (Ov v) (2 : Kv v) := by
    have := isIntegral_algebraMap (R := Ov v) (A := Kv v) (x := 2)
    rwa [map_ofNat] at this
  have h1 : (τ - 2) * (τ + 2) = 0 := by rw [← h0]; ring
  rcases mul_eq_zero.mp h1 with h1 | h1
  · rw [sub_eq_zero.mp h1, map_ofNat]; exact h2
  · rw [eq_neg_of_add_eq_zero_left h1, map_neg, map_ofNat]; exact h2.neg

private theorem sum_sub {α : Type} (p : α → Prop) (f : α → ℂ) (c : ℂ) :
    ∑ᶠ i : {a // p a}, c * f i.1 = c * ∑ᶠ a, one (p a) * f a := by
  classical
  have h1 : ∑ᶠ i : {a // p a}, c * f i.1 = ∑ᶠ (a) (_ : p a), c * f a :=
    finsum_subtype_eq_finsum_cond (f := fun a => c * f a) p
  rw [h1]
  have h2 : ∀ a, ∑ᶠ (_ : p a), c * f a = c • (one (p a) * f a) := by
    intro a
    rw [finsum_eq_if, smul_eq_mul]
    unfold one
    split_ifs <;> simp
  simp_rw [h2]
  rw [← smul_finsum, smul_eq_mul]

set_option maxHeartbeats 1600000 in
theorem split_side_identity_unitary : QuaternionStableSideTraceIdentity := by
  intro F _ _ Δ D hD x₀ hx₀
  obtain ⟨-, ⟨ι, hι⟩, -⟩ := iotaEx F Δ
  obtain ⟨n, x, c, hx0, hoff, hc, hsum⟩ := fibre F Δ D hD ι hι x₀ hx₀
  have hΔ : Δ ≠ 0 := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    obtain ⟨σ⟩ : Nonempty (F →+* ℝ) := ⟨InfinitePlace.embedding_of_isReal (hD.real.isReal w)⟩
    have hneg : σ Δ < 0 := hD.neg σ
    intro h0
    rw [h0, map_zero] at hneg
    exact lt_irrefl _ hneg
  refine ⟨n, x, c * ∏ v ∈ D.Sg, (D.S v).cS, hx0, hoff, ?_, ?_⟩
  · exact mul_pos hc (Finset.prod_pos fun v hv => (hD.sig v hv).cS)
  · intro V _ _ _ ch B hB t ht
    classical
    have hG : ∀ a, D.Good t a ↔ IsCM a ∧ D.admitted t a := fun a => Iff.rfl
    have hex : ∀ s : {a // D.Good t a}, ∃ g : DX Δ, HasTr g s.1 :=
      fun s => (embEx F Δ D hD s.1).1 ((hG _).1 s.2).1
    choose γ hγ using hex
    have hreg : ∀ s : {a // D.Good t a}, s.1 ^ 2 - 4 ≠ 0 :=
      fun s => aux_statement_10 D hD t ht s.1 ((hG _).1 s.2).2
    have hj : ∀ s : {a // D.Good t a}, ∃ j : (Etau F s.1)ˣ →* DX Δ, IsEmb s.1 (γ s) j :=
      fun s => (embAlg F Δ s.1 hΔ (hreg s) (γ s) (hγ s)).1
    choose j hjj using hj
    rw [hsum V ch B hB t ht {a // D.Good t a} (fun s => s.1) γ j Subtype.val_injective
      (fun s => ⟨hreg s, hγ s, hjj s⟩) ?_]
    · have hterm : ∀ s : {a // D.Good t a},
          ch s.1 * gqOn (ι.comp (j s)) (scalE s.1) D.UZ
            (fun y => D.FS t ((Quotient.out y)⁻¹ * ι (γ s) * Quotient.out y)) =
            (∏ v ∈ D.Sg, ((D.S v).cS : ℂ)) * (ch s.1 * ms s.1 * D.nS s.1) := by
        intro s
        rw [gqS F Δ D hD ι hι t ht s.1 ((hG _).1 s.2).1 (γ s) (j s) (hγ s) (hjj s)]
        have h1 : one (D.admitted t s.1) = 1 := if_pos ((hG _).1 s.2).2
        rw [h1]
        ring
      rw [finsum_congr hterm, sum_sub (fun a => D.Good t a) (fun a => ch a * ms a * D.nS a)]
      unfold Dat.sumS
      push_cast
      ring
    · intro g s hg hs
      exact ⟨⟨s, (hG s).2 ⟨(embEx F Δ D hD s).2 g hg (aux_statement_10 D hD t ht s hs), hs⟩⟩, rfl⟩

end UpperTheory.V.Z.Sym.Glob
