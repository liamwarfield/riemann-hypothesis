module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDual2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.RtWMem
noncomputable section

open NumberField Matrix Neutral.B1 GlobalTheory.CuspRep Formalism.L2.Host

namespace UpperTheory.V.Sd.Wc

private def wGL (R : Type) [CommRing R] : GL (Fin 2) R :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

private theorem map_wGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    GeneralLinearGroup.map f (wGL R) = wGL S := by
  ext i j
  change f ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) R) i j) = (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) S) i j
  fin_cases i <;> fin_cases j <;> simp

private theorem invT_eq {R : Type} [CommRing R] (g : GL (Fin 2) R) :
    invT 2 R g = GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det g)⁻¹ * (wGL R * (g * (wGL R)⁻¹)) := by
  rw [map_inv, eq_inv_mul_iff_mul_eq, ← eq_mul_inv_iff_mul_eq]
  apply Units.ext
  change Matrix.scalar (Fin 2) g.val.det = !![0, 1; -1, 0] * (g.val * !![0, -1; 1, 0]) * g.valᵀ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.det_fin_two, Fin.sum_univ_two] <;> ring

private theorem rt_w_mem {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2)
    {φ : TR.Sm F 2} (hφ : φ ∈ π.V) : TR.rt F 2 (wGL (Ad F))⁻¹ φ ∈ π.V := by
  let k : TR.Kinf F 2 := ⟨!![0, -1; 1, 0], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  have hk : Unitary.toUnits k = (wGL (TR.Rinf F))⁻¹ := Units.ext rfl
  rw [← TR.infGL_mul_finGL (wGL (Ad F))⁻¹, map_inv, map_wGL, ← hk, map_mul]
  exact π.stable (.cpt k) _ (π.stable (.fin _) _ hφ)

end UpperTheory.V.Sd.Wc

open UpperTheory.V UpperTheory.V.Sd.Wc in
theorem UpperTheory.V.Sd.Wc.polGL2 :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Sd.Wc.PolGL2 := by
  intro P F _ _ _ π ω h
  obtain ⟨B, hl, hr, hf, hc, hX⟩ := P.gkR F 2 π
  refine TR.CuspSub.isSelfDualBy_of_iso B hl hr hf hc hX ?_
  have hle : (π.dual.twist ω).V ≤ π.V := by
    rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    convert rt_w_mem π hφ using 1
    refine Subtype.ext (funext fun g => ?_)
    change φ.1 (invT 2 (Ad F) g) * ((ω.1 (GeneralLinearGroup.det g) : ℂˣ) : ℂ) = φ.1 (g * (wGL (Ad F))⁻¹)
    have e : wGL (Ad F) = ratGL F 2 (wGL F) := (map_wGL _).symm
    rw [invT_eq, h _ φ hφ, map_inv, mul_right_comm, Units.inv_mul, one_mul]
    conv_lhs => rw [e]
    rw [(π.cusp φ hφ).1.left, ← e]
  have e : π.dual.twist ω = π :=
    TR.CuspSub.ext ((π.irred _ hle (π.dual.twist ω).stable).resolve_left (π.dual.twist ω).ne_bot)
  rw [e]
  exact TR.CuspSub.Iso.refl π
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.MemParahoricTimesPrincipalCongruenceIff
open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af Matrix

namespace UpperTheory.V.Sd.Wc

variable {F : Type} [Field F] [NumberField F]

private noncomputable def mP (w : Pl F) (c : ℕ) : AddSubgroup (w.adicCompletion F) :=
  (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c).toAddSubgroup.map
    (w.adicCompletionIntegers F).subtype.toAddMonoidHom

private theorem isOpen_mP (w : Pl F) (c : ℕ) : IsOpen (mP w c : Set (w.adicCompletion F)) := by
  have h0 : IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c ≠ ⊥ :=
    pow_ne_zero c (IsDiscreteValuationRing.not_a_field _)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have ha1 : (a : w.adicCompletion F) ≠ 0 := fun e => ha0 (Subtype.ext e)
  have ho : IsOpen ((fun x : w.adicCompletion F => (a : w.adicCompletion F)⁻¹ * x) ⁻¹'
      (w.adicCompletionIntegers F : Set (w.adicCompletion F))) :=
    (Valued.isOpen_valuationSubring _).preimage (continuous_const.mul continuous_id)
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun x hx => ?_)
  refine ⟨a * ⟨_, hx⟩, Ideal.mul_mem_right _ _ ha, ?_⟩
  change (a : w.adicCompletion F) * ((a : w.adicCompletion F)⁻¹ * x) = x
  rw [mul_inv_cancel_left₀ ha1]

private theorem mem_parahoricTimesPrincipalCongruence_iff {w : Pl F} {c : ℕ} {g : GL (Fin 2) (w.adicCompletion F)} :
    g ∈ K1 w c ↔ (∀ a b, g a b ∈ w.adicCompletionIntegers F) ∧
      (∀ a b, (g⁻¹ : GL (Fin 2) (w.adicCompletion F)) a b ∈ w.adicCompletionIntegers F) ∧
      g 1 0 ∈ mP w c ∧ g 1 1 - 1 ∈ mP w c := by
  have key : ∀ k : GL (Fin 2) (w.adicCompletionIntegers F),
      k ∈ ((mirab _).comap (Matrix.GeneralLinearGroup.map (n := Fin 2)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)))) ↔
      k 1 0 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c ∧
        k 1 1 - 1 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c := fun k => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq, map_one]
    change ![0, 1] ᵥ* _ = ![0, 1] ↔ _
    rw [funext_iff, Fin.forall_fin_two]
    simp [Matrix.vecMul, dotProduct]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h1, h2⟩ := (key k).1 hk
    refine ⟨fun a b => (k a b).2, fun a b => ?_, ⟨_, h1, rfl⟩, ⟨_, h2, rfl⟩⟩
    rw [← map_inv]; exact ((k⁻¹ : GL (Fin 2) (w.adicCompletionIntegers F)) a b).2
  · rintro ⟨ha, hb, ⟨y, hy, e⟩, ⟨y', hy', e'⟩⟩
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin 2) (w.adicCompletionIntegers F).subtype) := fun x y h =>
      Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
    let k : GL (Fin 2) (w.adicCompletionIntegers F) :=
      ⟨Matrix.of fun a b => ⟨g a b, ha a b⟩, Matrix.of fun a b => ⟨(g⁻¹ : GL (Fin 2) (w.adicCompletion F)) a b, hb a b⟩,
        inj (by rw [map_mul, map_one]; exact g.mul_inv), inj (by rw [map_mul, map_one]; exact g.inv_mul)⟩
    refine ⟨k, (key k).2 ⟨?_, ?_⟩, Units.ext rfl⟩
    · rw [show k 1 0 = y from Subtype.ext e.symm]; exact hy
    · rw [show k 1 1 - 1 = y' from Subtype.ext e'.symm]; exact hy'

private theorem mem_mP_zero {w : Pl F} {x : w.adicCompletion F} (hx : x ∈ w.adicCompletionIntegers F) : x ∈ mP w 0 :=
  ⟨⟨x, hx⟩, by simp, rfl⟩

private theorem mem_Oh {x : Af F} :
    x ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F ↔ ∀ w : Pl F, pLoc F w x ∈ w.adicCompletionIntegers F := by
  rw [← mem_Ohat]; simp [Ohat, Subring.mem_iInf]

private theorem mem_Kc {c : Pl F → ℕ} {g : GF F} :
    g ∈ Kc c ↔ g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL F 2 ∧
      ∀ w, c w ≠ 0 → pLoc F w (g 1 0) ∈ mP w (c w) ∧ pLoc F w (g 1 1) - 1 ∈ mP w (c w) := by
  simp only [Kc, Subgroup.mem_iInf, Subgroup.mem_comap, mem_parahoricTimesPrincipalCongruence_iff, ← map_inv,
    GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff, mem_Oh]
  constructor
  · exact fun h => ⟨⟨fun a b w => (h w).1 a b, fun a b w => (h w).2.1 a b⟩, fun w _ => (h w).2.2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩ w
    refine ⟨fun a b => h1 a b w, fun a b => h2 a b w, ?_⟩
    by_cases hw : c w = 0
    · rw [hw]
      exact ⟨mem_mP_zero (h1 1 0 w), mem_mP_zero (sub_mem (h1 1 1 w) (one_mem _))⟩
    · exact h3 w hw

private theorem isOpen_Kc {c : Pl F → ℕ} (hc : {w | c w ≠ 0}.Finite) : IsOpen (Kc c : Set (GF F)) := by
  have e : (Kc c : Set (GF F)) = (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL F 2 : Set (GF F)) ∩
      ⋂ w ∈ {w | c w ≠ 0}, ((fun g : GF F => pLoc F w (g 1 0)) ⁻¹' mP w (c w) ∩
        (fun g : GF F => pLoc F w (g 1 1) - 1) ⁻¹' mP w (c w)) := by
    ext g
    simp only [SetLike.mem_coe, mem_Kc, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
  have ct : ∀ w a b, Continuous fun g : GF F => pLoc F w (g a b) := fun w a b =>
    (show Continuous (pLoc F w) from RestrictedProduct.continuous_eval w).comp
      (Continuous.matrix_elem Units.continuous_val a b)
  rw [e]
  exact (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL F 2).inter (hc.isOpen_biInter fun w _ =>
    ((isOpen_mP w _).preimage (ct w 1 0)).inter ((isOpen_mP w _).preimage ((ct w 1 1).sub continuous_const)))

private theorem range_zc : ((zc F).range : Set (GF F)) =
    {g : GF F | g 0 1 = 0} ∩ {g : GF F | g 1 0 = 0} ∩ {g : GF F | g 0 0 = g 1 1} := by
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    simp [zc]
  · rintro ⟨⟨h1, h2⟩, h3⟩
    simp only [Set.mem_setOf_eq] at h1 h2 h3
    have hm : g 0 0 * (g⁻¹ : GF F) 0 0 = 1 := by
      have := congrFun (congrFun g.mul_inv 0) 0
      rw [Matrix.mul_apply, Fin.sum_univ_two, h1, zero_mul, add_zero] at this
      exact this
    refine ⟨Units.mkOfMulEqOne _ _ hm, Units.ext (Matrix.ext fun i j => ?_)⟩
    fin_cases i <;> fin_cases j <;> simp [zc, h1, h2, h3]

end UpperTheory.V.Sd.Wc

open UpperTheory.V.Sd.Wc in
theorem UpperTheory.V.Sd.Wc.kcTop :
    UpperTheory.V.Sd.Wc.KcTop := by
  intro F _ _
  have ct : ∀ a b, Continuous fun g : GF F => g a b := fun a b => Continuous.matrix_elem Units.continuous_val a b
  refine ⟨fun c hc => ⟨isOpen_Kc hc, ?_⟩, fun U hU => ?_, fun z => ?_, ?_, ?_, fun c w k hk => ?_⟩
  · exact (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL F 2).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ (isOpen_Kc hc)) fun g hg => (mem_Kc.1 hg).1
  · obtain ⟨H, -, hH⟩ := (GroundTheory.Automorphic.AdelicGLn.finite_hasBasis_nhds_one F 2).mem_iff.1 hU
    exact ⟨H.toSubgroup, H.isOpen, hH⟩
  · refine Subgroup.mem_center_iff.2 fun g => Units.ext ?_
    exact ((Matrix.scalar_commute (z : Af F) (fun _ => Commute.all _ _) g.val).eq).symm
  · rw [range_zc]
    exact ((isClosed_eq (ct 0 1) continuous_const).inter (isClosed_eq (ct 1 0) continuous_const)).inter
      (isClosed_eq (ct 0 0) (ct 1 1))
  · refine Continuous.units_map _ ?_
    exact (continuous_pi fun _ => continuous_id : Continuous fun x : Af F => fun _ : Fin 2 => x).matrix_diagonal
  · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 ?_
    by_cases h : v = w
    · subst h; rwa [pLoc_locGL]
    · rw [pLoc_locGL_of_ne h]; exact one_mem _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.HkReps
open NumberField IsDedekindDomain IsLocalRing UpperTheory.V UpperTheory.V.Sd Formalism.L2.Host

theorem UpperTheory.V.Sd.Wc.hkReps :
    UpperTheory.V.Sd.UopSum → UpperTheory.V.Sd.Wc.HkReps := by
  intro hU F _ _ w c
  classical
  haveI : Fintype (ResidueField (HeightOneSpectrum.adicCompletionIntegers F w)) := Fintype.ofFinite _
  let sec := Function.surjInv (residue_surjective (R := HeightOneSpectrum.adicCompletionIntegers F w))
  have hsec : ∀ r, residue _ (sec r) = r :=
    Function.surjInv_eq (residue_surjective (R := HeightOneSpectrum.adicCompletionIntegers F w))
  let S := Finset.univ.image sec
  have hS : Set.BijOn (residue (HeightOneSpectrum.adicCompletionIntegers F w)) (↑S) Set.univ := by
    refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
      obtain ⟨r, rfl⟩ := hx
      obtain ⟨s, rfl⟩ := hy
      rw [hsec, hsec] at hxy
      rw [hxy]
    · intro r _
      exact ⟨sec r, by simp [S], hsec r⟩
  let e : Fin S.card ≃ S := S.equivFin.symm
  let b : Fin S.card → GL (Fin 2) (HeightOneSpectrum.adicCompletion F w) :=
    fun i => aff ((atFin w) (unif w)) ↑((e i : HeightOneSpectrum.adicCompletionIntegers F w))
  have hsum : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion F w)) V) (x : V),
      ∑ u ∈ S, (ρ (aff ((atFin w) (unif w)) ↑u)) x = ∑ i, (ρ (b i)) x := by
    intro V _ _ ρ x
    rw [← Finset.sum_coe_sort S]
    exact (Equiv.sum_comp e (fun u : S => (ρ (aff ((atFin w) (unif w)) ↑(u : HeightOneSpectrum.adicCompletionIntegers F w))) x)).symm
  by_cases hc : c = 0
  · refine ⟨S.card + 1, Fin.cons ((Matrix.GeneralLinearGroup.scalar (Fin 2)) ((atFin w) (unif w)) * (aff ((atFin w) (unif w)) 0)⁻¹) b, fun h => absurd hc h, ?_⟩
    intro V _ _ ρ x hx
    obtain ⟨h1, h2⟩ := hU F w V ρ c x hx
    refine ⟨h1, ?_⟩
    rw [h2 S hS, if_pos hc, Fin.sum_univ_succ, hsum, Fin.cons_zero, add_comm]
    simp only [Fin.cons_succ]
  · refine ⟨S.card, b, fun _ i => ⟨(e i : HeightOneSpectrum.adicCompletionIntegers F w), rfl⟩, ?_⟩
    intro V _ _ ρ x hx
    obtain ⟨h1, h2⟩ := hU F w V ρ c x hx
    refine ⟨h1, ?_⟩
    rw [h2 S hS, if_neg hc, add_zero, hsum]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.HkComm
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.CuspRep UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Sd.Wc

variable {F : Type} [Field F] [NumberField F]

private theorem ext_loc {g h : GL (Fin 2) (Af F)}
    (e : ∀ w, Matrix.GeneralLinearGroup.map (pLoc F w) g = Matrix.GeneralLinearGroup.map (pLoc F w) h) : g = h := by
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun w => congrArg (fun x : GL (Fin 2) (w.adicCompletion F) => x i j) (e w)

private theorem comm_of_triv {w : Pl F} (g : GL (Fin 2) (w.adicCompletion F)) {k : GL (Fin 2) (Af F)}
    (hk : Matrix.GeneralLinearGroup.map (pLoc F w) k = 1) : k * locGL F 2 w g = locGL F 2 w g * k := by
  refine ext_loc fun x => ?_
  rw [map_mul, map_mul]
  by_cases hx : x = w
  · subst hx; rw [hk, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hx, mul_one, one_mul]

private theorem fix_loc (hK : KcTop) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GF F) V) (c : Pl F → ℕ)
    {x : V} (hx : x ∈ Hi.fixd ρ (Kc c)) (w : Pl F) : x ∈ Hi.fixd (ρ.comp (locGL F 2 w)) (K1 w (c w)) :=
  fun k hk => hx _ ((hK F).2.2.2.2.2 c w k hk)

private theorem uop_mem (hR : HkReps) (hK : KcTop) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GF F) V) (c : Pl F → ℕ)
    {x : V} (hx : x ∈ Hi.fixd ρ (Kc c)) (w : Pl F) : Uop w (ρ.comp (locGL F 2 w)) (c w) x ∈ Hi.fixd ρ (Kc c) := by
  obtain ⟨N, a, -, ha⟩ := hR F w (c w)
  obtain ⟨h1, h2⟩ := ha V _ x (fix_loc hK ρ c hx w)
  intro k hk
  have hkw : Matrix.GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w) := (Subgroup.mem_iInf.1 hk) w
  set kw := Matrix.GeneralLinearGroup.map (pLoc F w) k with hkwe
  have hm : k * (locGL F 2 w kw)⁻¹ ∈ Kc c := mul_mem hk (inv_mem ((hK F).2.2.2.2.2 c w kw hkw))
  have ht : Matrix.GeneralLinearGroup.map (pLoc F w) (k * (locGL F 2 w kw)⁻¹) = 1 := by
    rw [map_mul, map_inv, pLoc_locGL, ← hkwe, mul_inv_cancel]
  have e : k = k * (locGL F 2 w kw)⁻¹ * locGL F 2 w kw := by rw [inv_mul_cancel_right]
  have h3 : ρ (locGL F 2 w kw) (Uop w (ρ.comp (locGL F 2 w)) (c w) x) = Uop w (ρ.comp (locGL F 2 w)) (c w) x := h1 kw hkw
  have h4 : ρ (k * (locGL F 2 w kw)⁻¹) x = x := hx _ hm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_mul, Module.End.mul_apply, h3, h2, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ρ _ (ρ (locGL F 2 w (a i)) x) = ρ (locGL F 2 w (a i)) x
  rw [← Module.End.mul_apply, ← map_mul, comm_of_triv _ ht, map_mul, Module.End.mul_apply, h4]

end UpperTheory.V.Sd.Wc

open UpperTheory.V.Sd.Wc in
theorem UpperTheory.V.Sd.Wc.hkComm :
    UpperTheory.V.Sd.Wc.HkReps → UpperTheory.V.Sd.Wc.KcTop → UpperTheory.V.Sd.Wc.HkComm := by
  intro hR hK F _ _ V _ _ ρ c x hx w
  refine ⟨uop_mem hR hK ρ c hx w, fun w' => ?_⟩
  by_cases hw : w' = w
  · subst hw; rfl
  obtain ⟨N, a, -, ha⟩ := hR F w (c w)
  obtain ⟨N', a', -, ha'⟩ := hR F w' (c w')
  rw [(ha V _ _ (fix_loc hK ρ c (uop_mem hR hK ρ c hx w') w)).2, (ha' V _ _ (fix_loc hK ρ c (uop_mem hR hK ρ c hx w) w')).2,
    (ha V _ _ (fix_loc hK ρ c hx w)).2, (ha' V _ _ (fix_loc hK ρ c hx w')).2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  change ρ (locGL F 2 w (a i)) (ρ (locGL F 2 w' (a' j)) x) = ρ (locGL F 2 w' (a' j)) (ρ (locGL F 2 w (a i)) x)
  rw [← Module.End.mul_apply, ← map_mul, comm_of_triv (a' j) (pLoc_locGL_of_ne hw (a i)), map_mul, Module.End.mul_apply]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.ExChi
theorem UpperTheory.V.Sd.Wc.exChi :
    UpperTheory.V.Sd.Wc.ExChi := by
  intro G Z _ _ K ζ ω hc hK
  have hcomm : ∀ (z : Z) (g : G), g * ζ z = ζ z * g := fun z g =>
    Subgroup.mem_center_iff.mp (hc z) g
  have hN : ζ.range.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨z, rfl⟩ g
    refine ⟨z, ?_⟩
    rw [hcomm z g, mul_assoc, mul_inv_cancel, mul_one]
  have hrep : ∀ x ∈ K ⊔ ζ.range, ∃ k ∈ K, ∃ z : Z, x = k * ζ z := by
    intro x hx
    obtain ⟨k, hk, y, ⟨z, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    exact ⟨k, hk, z, rfl⟩
  have hwd : ∀ k ∈ K, ∀ k' ∈ K, ∀ z z' : Z, k * ζ z = k' * ζ z' → ω z = ω z' := by
    intro k hk k' hk' z z' h
    have h1 : ζ (z' * z⁻¹) = k'⁻¹ * k := by
      rw [map_mul, map_inv]
      calc ζ z' * (ζ z)⁻¹ = k'⁻¹ * (k' * ζ z') * (ζ z)⁻¹ := by group
        _ = k'⁻¹ * (k * ζ z) * (ζ z)⁻¹ := by rw [h]
        _ = k'⁻¹ * k := by group
    have h2 : ω (z' * z⁻¹) = 1 := hK _ (by rw [h1]; exact K.mul_mem (K.inv_mem hk') hk)
    rw [map_mul, map_inv] at h2
    exact (mul_inv_eq_one.mp h2).symm
  choose kf hkf zf hzf using fun h : ↥(K ⊔ ζ.range) => hrep h.1 h.2
  have hval : ∀ (h : ↥(K ⊔ ζ.range)) (k : G), k ∈ K → ∀ z : Z,
      (h : G) = k * ζ z → ω (zf h) = ω z := by
    intro h k hk z hz
    exact hwd _ (hkf h) _ hk _ _ ((hzf h).symm.trans hz)
  refine ⟨{ toFun := fun h => ω (zf h), map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · exact (hval 1 1 K.one_mem 1 (by simp)).trans (map_one ω)
  · intro a b
    show ω (zf (a * b)) = ω (zf a) * ω (zf b)
    rw [← map_mul]
    refine hval _ (kf a * kf b) (K.mul_mem (hkf a) (hkf b)) _ ?_
    rw [Subgroup.coe_mul, hzf a, hzf b, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (ζ (zf a)), ← hcomm (zf a) (kf b), mul_assoc]
  · intro h
    exact ⟨⟨kf h, hkf h, zf h, hzf h⟩, fun k hk z hz => hval h k hk z hz⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.FixGlob
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Wc UpperTheory.V.Af.GlobalFixedVectors Matrix

private theorem mem_Kc' {F : Type} [Field F] [NumberField F] {c : Pl F → ℕ} {k : GF F} :
    k ∈ Kc c ↔ ∀ w, GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w) := by
  simp [Kc, Subgroup.mem_iInf]

private theorem entry_Kc {F : Type} [Field F] [NumberField F] {c : Pl F → ℕ} {k : GF F} (hk : k ∈ Kc c) (i j : Fin 2) :
    k i j ∈ UpperTheory.V.Af.Ohat F := by
  refine UpperTheory.V.Af.GlobalFixedVectors.mem_Ohat.2 fun w => ?_
  obtain ⟨g, -, hg⟩ := mem_Kc'.1 hk w
  have e := congrArg (fun x : GL (Fin 2) (w.adicCompletion F) => x i j) hg
  change ((g i j : w.adicCompletionIntegers F) : w.adicCompletion F) = pLoc F w (k i j) at e
  rw [← e]
  exact (g i j).2

private theorem Kc_le {F : Type} [Field F] [NumberField F] {c : Pl F → ℕ} {k : GF F} (hk : k ∈ Kc c) : k ∈ KLev F 2 1 := by
  let A : Matrix (Fin 2) (Fin 2) (UpperTheory.V.Af.Ohat F) := fun i j => ⟨k i j, entry_Kc hk i j⟩
  let B : Matrix (Fin 2) (Fin 2) (UpperTheory.V.Af.Ohat F) := fun i j => ⟨(k⁻¹ : GF F) i j, entry_Kc (inv_mem hk) i j⟩
  have hA : (UpperTheory.V.Af.Ohat F).subtype.mapMatrix A = k.val := rfl
  have hB : (UpperTheory.V.Af.Ohat F).subtype.mapMatrix B = (k⁻¹ : GF F).val := rfl
  have hinj : Function.Injective ((UpperTheory.V.Af.Ohat F).subtype.mapMatrix (m := Fin 2)) :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, ?_, ?_⟩
  · rw [map_mul, map_one, hA, hB, Units.mul_inv]
  · rw [map_mul, map_one, hA, hB, Units.inv_mul]
  · haveI : Subsingleton (UpperTheory.V.Af.Ohat F ⧸ Ideal.span {((1 : ℕ) : ↥(UpperTheory.V.Af.Ohat F))}) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    ext i j
    exact Subsingleton.elim _ _
  · exact Units.ext hA

theorem UpperTheory.V.Sd.Wc.fixGlob :
    UpperTheory.V.Sd.Wc.FixGlob := by
  classical
  intro F _ _ V _ _ ρ hρ c x hc
  have key : ∀ S : Finset (Pl F),
      (∀ k ∈ KAway 2 1 S, k ∈ Kc c → ρ k x = x) → (∀ k ∈ KAway 2 1 ∅, k ∈ Kc c → ρ k x = x) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      intro h
      refine ih fun k hk hl => ?_
      rw [mem_Kc'] at hl
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway 2 1 (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 : ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) x = x := hc w _ (hl w)
      have h4 := h _ h2 (mem_Kc'.2 fun v => by
        by_cases hv : v = w
        · subst hv; simp [pLoc_locGL]
        · simpa [pLoc_locGL_of_ne hv] using hl v)
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := 1) ((hρ x).mem_nhds (by simp))
  intro k hk
  exact key S (fun k hk _ => hS hk) k (mem_KAway.2 ⟨Kc_le hk, by simp⟩) hk
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.LocTwo
open NumberField IsDedekindDomain IsLocalRing UpperTheory.V UpperTheory.V.Sd Formalism.ConjugateSelfDual

private theorem sq_two {O : Type} [CommRing O] (M : Matrix (Fin 2) (Fin 2) O) :
    M * M = (M 0 0 + M 1 1) • M - (M 0 0 * M 1 1 - M 0 1 * M 1 0) • (1 : Matrix (Fin 2) (Fin 2) O) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem pow_two_dim {O k : Type} [CommRing O] [CommRing k] (r : O →+* k) (M : Matrix (Fin 2) (Fin 2) O)
    (ht : r (M 0 0 + M 1 1) = 2) (hd : r (M 0 0 * M 1 1 - M 0 1 * M 1 0) = 1) (n : ℕ) :
    ∃ U V : O, M ^ n = U • M + V • (1 : Matrix (Fin 2) (Fin 2) O) ∧ r U = n ∧ r V = 1 - n := by
  induction n with
  | zero => exact ⟨0, 1, by simp, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨U, V, h, hU, hV⟩ := ih
    refine ⟨U * (M 0 0 + M 1 1) + V, -(U * (M 0 0 * M 1 1 - M 0 1 * M 1 0)), ?_, ?_, ?_⟩
    · rw [pow_succ, h, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, sq_two M]
      module
    · rw [map_add (f := _), map_mul, ht, hU, hV]; push_cast; ring
    · rw [map_neg, map_mul, hd, hU]; push_cast; ring

private theorem field_two {k : Type} [Field k] (hk : Nat.card k = 2) :
    (∀ x : k, x ≠ 0 → x = 1) ∧ (2 : k) = 0 := by
  have h1 : ∀ x : k, x ≠ 0 → x = 1 := by
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : k)).1 hk
    intro x hx
    rw [hy x hx, hy 1 one_ne_zero]
  refine ⟨h1, ?_⟩
  by_contra h
  have := h1 2 h
  have h2 : (1 : k) = 0 := by linear_combination this
  exact one_ne_zero h2

private theorem gen {O K : Type} [CommRing O] [IsLocalRing O] [Field K] (φ : O →+* K)
    (hk : Nat.card (ResidueField O) = 2) (h : GL (Fin 2) O)
    (hc : residue O (h 1 0) = 0) (hd : residue O (h 1 1) = 1) (n : ℕ) (hn : Odd n)
    (hz : (Matrix.GeneralLinearGroup.map φ h) ^ n ∈ Subgroup.center (GL (Fin 2) K)) :
    Matrix.GeneralLinearGroup.map φ h ∈ Subgroup.center (GL (Fin 2) K) := by
  obtain ⟨h1, h2⟩ := field_two hk
  have hu := (Matrix.GeneralLinearGroup.det h).isUnit
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at hu
  have hdet : residue O (h 0 0 * h 1 1 - h 0 1 * h 1 0) = 1 := h1 _ (hu.map (residue O)).ne_zero
  have ha : residue O (h 0 0) = 1 := by
    rw [map_sub, map_mul, map_mul, hc, hd] at hdet
    simpa using hdet
  obtain ⟨U, V, hp, hU, -⟩ := pow_two_dim (residue O) (h : Matrix (Fin 2) (Fin 2) O)
    (by rw [map_add (f := _), ha, hd]; norm_num) hdet n
  have hUu : IsUnit U := by
    by_contra hU'
    have h0 : residue O U = 0 := (residue_eq_zero_iff U).2 hU'
    obtain ⟨m, rfl⟩ := hn
    rw [h0] at hU
    push_cast at hU
    rw [h2] at hU
    simp at hU
  have hU0 : φ U ≠ 0 := (hUu.map φ).ne_zero
  set k := Matrix.GeneralLinearGroup.map φ h with hkdef
  have hkp : ((k ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      φ U • (k : Matrix (Fin 2) (Fin 2) K) + φ V • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [hkdef, ← map_pow]
    change ((h ^ n : GL (Fin 2) O) : Matrix (Fin 2) (Fin 2) O).map φ =
      φ U • (h : Matrix (Fin 2) (Fin 2) O).map φ + φ V • (1 : Matrix (Fin 2) (Fin 2) K)
    rw [Units.val_pow_eq_pow_val, hp]
    ext i j
    simp [Matrix.one_apply, apply_ite φ]
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  have hg := congrArg Units.val (hz g)
  rw [Units.val_mul, Units.val_mul, hkp, mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc,
    smul_mul_assoc, mul_one, one_mul, add_left_inj] at hg
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact smul_right_injective _ hU0 hg

theorem UpperTheory.V.Sd.Wc.locTwo :
    UpperTheory.V.Sd.Wc.LocTwo := by
  intro F _ _ u c hc hN k hk n hn hz
  obtain ⟨h, hh, rfl⟩ := hk
  have hle : maximalIdeal (u.adicCompletionIntegers F) ^ c ≤ maximalIdeal _ := Ideal.pow_le_self hc
  refine gen _ ?_ h ?_ ?_ n hn hz
  · rw [Formalism.UG.P.tjcosets_card_residue, ← hN]
    simp [normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · have h0 := congrFun hh 0
    rw [residue_eq_zero_iff]
    apply hle
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h0
  · have h0 := congrFun hh 1
    rw [← map_one (residue (u.adicCompletionIntegers F)), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    apply hle
    rw [← Ideal.Quotient.eq, map_one]
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h0
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.GlFacts
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V.Af
open scoped Matrix NNReal

namespace UpperTheory.V.Sd.Wc

section

variable {F : Type} [Field F] [NumberField F]

private theorem congruence_subgroup_one_entry_bounds (w : Pl F) {g : GL (Fin 2) (w.adicCompletion F)} (hg : g ∈ K1 w 1) :
    (∀ i j, Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j) ≤ 1) ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 0) < 1 ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 1 - 1) < 1 ∧
      Valued.v (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)).det = 1 := by
  obtain ⟨k, hk, rfl⟩ := hg
  have hk' := hk
  change ![0, 1] ᵥ* _ = ![0, 1] at hk'
  have hm : ∀ x : w.adicCompletionIntegers F, x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 1 →
      Valued.v (x : w.adicCompletion F) < 1 := by
    intro x hx
    rw [pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hx
    exact lt_of_le_of_ne x.2 hx
  have h0 := congrFun hk' 0
  have h1 := congrFun hk' 1
  refine ⟨fun i j => (k i j).2, hm (k 1 0) ?_, hm (k 1 1 - 1) ?_, ?_⟩
  · simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Ideal.Quotient.eq_zero_iff_mem] using h0
  · refine Ideal.Quotient.eq.1 ?_
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ] using h1
  · have hu : IsUnit (k : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers F)).det :=
      (Matrix.GeneralLinearGroup.det k).isUnit
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hu
    rw [← hu]
    exact congrArg Valued.v ((w.adicCompletionIntegers F).subtype.map_det _).symm

private def low {R : Type} [CommRing R] (x : R) : GL (Fin 2) R where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

private theorem low_mem (w : Pl F) (x : w.adicCompletion F) (hx : Valued.v x < 1) : low x ∈ K1 w 1 := by
  let y : w.adicCompletionIntegers F := ⟨x, hx.le⟩
  have hy : y ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 1 := by
    rw [pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hx.ne
  refine ⟨low y, ?_, ?_⟩
  · change ![0, 1] ᵥ* _ = ![0, 1]
    ext j
    fin_cases j
    · simpa [low, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Ideal.Quotient.eq_zero_iff_mem] using hy
    · simp [low, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [low, y]

private theorem loc_mem_Kc (c : Pl F → ℕ) (w : Pl F) {k : GL (Fin 2) (w.adicCompletion F)} (hk : k ∈ K1 w (c w)) :
    locGL F 2 w k ∈ Kc c := by
  refine Subgroup.mem_iInf.2 fun u => Subgroup.mem_comap.2 ?_
  by_cases h : u = w
  · subst h; rwa [pLoc_locGL]
  · rw [pLoc_locGL_of_ne h]; exact one_mem _

variable {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} (D : LDat F ι)

private theorem gl_apply (k : GF F) (v : InfinitePlace F) :
    D.gl k v = Matrix.GeneralLinearGroup.map (D.em v) (Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) k) := by
  ext i j; rfl

private theorem nu_eq_one (v : InfinitePlace F) {x : (D.pl v).adicCompletion F} (hx : Valued.v x = 1) : nu ι (D.em v x) = 1 :=
  le_antisymm ((D.le v x).2 hx.le) (not_lt.1 fun h => ((D.lt v x).1 h).ne hx)

open Classical in
private theorem gl_loc (v : InfinitePlace F) (a : GL (Fin 2) ((D.pl v).adicCompletion F)) :
    D.gl (locGL F 2 (D.pl v) a) = Pi.mulSingle v (Matrix.GeneralLinearGroup.map (D.em v) a) := by
  funext u
  rw [gl_apply]
  by_cases h : u = v
  · subst h; rw [pLoc_locGL, Pi.mulSingle_eq_same]
  · rw [pLoc_locGL_of_ne (fun e => h (D.inj e)), Pi.mulSingle_eq_of_ne h, map_one]

private theorem unit_val (v : InfinitePlace F) : ∃ x : (D.pl v).adicCompletion F, Valued.v x = 1 ∧
    D.em v x = v.embedding (unif (D.pl v) : Fˣ) / (l : ℂ) := by
  have hp : Valued.v ((atFin (D.pl v) (unif (D.pl v)) : ((D.pl v).adicCompletion F)ˣ) : (D.pl v).adicCompletion F) =
    WithZero.exp (-1 : ℤ) := unif_spec _
  refine ⟨((atFin (D.pl v) (unif (D.pl v)) : ((D.pl v).adicCompletion F)ˣ) : (D.pl v).adicCompletion F) / (l : _), ?_, ?_⟩
  · rw [map_div₀, hp, D.unif, div_self WithZero.exp_ne_zero]
  · rw [map_div₀, map_natCast, ← D.em_alg]; rfl

end

private theorem val_mul_sub {ν : Valuation ℂ ℝ≥0} {x y : ℂ} (hx : ν (x - 1) < 1) (hy : ν (y - 1) < 1) : ν (x * y - 1) < 1 := by
  have e : x * y - 1 = (x - 1) * (y - 1) + ((x - 1) + (y - 1)) := by ring
  rw [e]
  refine ν.map_add_lt ?_ (ν.map_add_lt hx hy)
  rw [map_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hx hy.le

private theorem val_zpow_sub {ν : Valuation ℂ ℝ≥0} {x : ℂ} (h1 : ν x = 1) (hx : ν (x - 1) < 1) (m : ℤ) : ν (x ^ m - 1) < 1 := by
  have hn : ∀ y : ℂ, ν (y - 1) < 1 → ∀ n : ℕ, ν (y ^ n - 1) < 1 := by
    intro y hy n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; exact val_mul_sub ih hy
  have h0 : x ≠ 0 := by rintro rfl; simp at h1
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · rw [zpow_natCast]; exact hn x hx n
  · rw [zpow_neg, zpow_natCast, ← inv_pow]
    refine hn _ ?_ n
    have e : x⁻¹ - 1 = -(x⁻¹ * (x - 1)) := by field_simp; ring
    rwa [e, Valuation.map_neg, map_mul, map_inv₀, h1, inv_one, one_mul]

end UpperTheory.V.Sd.Wc

open UpperTheory.V.Sd.Wc in
theorem UpperTheory.V.Sd.Wc.glFacts :
    UpperTheory.V.Sd.Wc.GlFacts := by
  classical
  intro F _ _ l _ ι D
  have huf : ∀ e w, nu ι (D.uf e w) = 1 := by
    intro e w
    rw [LDat.uf, map_prod]
    refine Finset.prod_eq_one fun v _ => ?_
    split_ifs with h
    · subst h
      obtain ⟨x, hx, e⟩ := unit_val D v
      rw [← e, map_zpow₀, nu_eq_one D v hx, one_zpow]
    · exact map_one _
  refine ⟨fun c hc => ⟨fun k hk v => ?_, fun a => ?_⟩, fun w hw a => ?_, gl_loc D, fun n e z x => ?_, huf, fun e e' he w => ?_⟩
  · have h1 := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hk (D.pl v))
    rw [hc] at h1
    obtain ⟨ha, hb, hd, he⟩ := congruence_subgroup_one_entry_bounds _ h1
    have hdet : (D.gl k v : Matrix (Fin 2) (Fin 2) ℂ).det = D.em v
        (Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) k : Matrix (Fin 2) (Fin 2) ((D.pl v).adicCompletion F)).det :=
      ((D.em v).map_det _).symm
    refine ⟨fun i j => (D.le v _).2 (ha i j), (D.lt v _).2 hb, ?_, ?_, ?_⟩
    · have := (D.lt v _).2 hd
      rwa [map_sub, map_one] at this
    · rw [hdet]; exact nu_eq_one D v he
    · rw [hdet]; exact D.res v _ he
  · have key : ∀ s : Finset (InfinitePlace F), ∃ k ∈ Kc c, ∀ v,
        D.gl k v = if v ∈ s then low ((l * a v : ℕ) : ℂ) else 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨1, one_mem _, fun v => by simp⟩
      | insert u s hu ih =>
        obtain ⟨k, hk, hv⟩ := ih
        have hl : Valued.v ((l * a u : ℕ) : (D.pl u).adicCompletion F) < 1 := by
          rw [Nat.cast_mul, map_mul, D.unif]
          have h2 : Valued.v ((a u : ℕ) : (D.pl u).adicCompletion F) ≤ 1 :=
            natCast_mem ((D.pl u).adicCompletionIntegers F) (a u)
          refine mul_lt_one_of_nonneg_of_lt_one_left zero_le ?_ h2
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
        refine ⟨locGL F 2 (D.pl u) (low ((l * a u : ℕ) : (D.pl u).adicCompletion F)) * k,
          mul_mem (loc_mem_Kc c _ (by rw [hc]; exact low_mem _ _ hl)) hk, fun v => ?_⟩
        rw [map_mul, Pi.mul_apply, gl_loc, hv]
        by_cases h : v = u
        · subst h
          rw [Pi.mulSingle_eq_same, if_neg hu, mul_one, if_pos (Finset.mem_insert_self _ _)]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [low]
        · rw [Pi.mulSingle_eq_of_ne h, one_mul]
          simp [h]
    obtain ⟨k, hk, hv⟩ := key Finset.univ
    exact ⟨k, hk, fun v => by rw [hv, if_pos (Finset.mem_univ _)]; rfl⟩
  · funext v
    rw [gl_apply, pLoc_locGL_of_ne (fun e : D.pl v = w => hw (e ▸ D.mem v)), map_one, Pi.one_apply]
  · refine Subtype.ext (MvPolynomial.funext fun y => ?_)
    have hg : ∀ v, (D.gl (zc F z) v : Matrix (Fin 2) (Fin 2) ℂ) = !![D.ea v z, 0; 0, D.ea v z] := by
      intro v
      ext i j
      change D.ea v ((zc F z : Matrix (Fin 2) (Fin 2) (Af F)) i j) = _
      fin_cases i <;> fin_cases j <;> simp [zc]
    have h0 : ∀ v, D.ea v z ≠ 0 := fun v => (z.isUnit.map (D.ea v)).ne_zero
    have ha : act (D.gl (zc F z)) y = fun p => D.ea p.1 z * y p := by
      funext p
      obtain ⟨v, i⟩ := p
      fin_cases i <;> simp [act, hg, mul_comm]
    have hd : (detE e (D.gl (zc F z)) : ℂ) = ∏ v, D.ea v z ^ (2 * e v) := by
      change ((∏ v, Matrix.GeneralLinearGroup.det (D.gl (zc F z) v) ^ e v : ℂˣ) : ℂ) = _
      rw [Units.coe_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, hg, zpow_mul, zpow_two]
      simp
    change MvPolynomial.eval y (wRep n e (D.gl (zc F z)) x).1 = MvPolynomial.eval y (_ • x.1)
    rw [eval_wRep, ha, x.2 (fun v => D.ea v z) y, MvPolynomial.smul_eval, hd, ← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [zpow_add₀ (h0 v), zpow_natCast, mul_comm]
  · by_cases hw : ∃ v, D.pl v = w
    · obtain ⟨v, rfl⟩ := hw
      obtain ⟨x, hx, ex⟩ := unit_val D v
      have hs : ∀ e, D.uf e (D.pl v) = D.em v x ^ e v := by
        intro e
        rw [LDat.uf, Finset.prod_eq_single v (fun u _ hu => if_neg fun h => hu (D.inj h)) (by simp), if_pos rfl, ex]
      have h1 := nu_eq_one D v hx
      have h0 : D.em v x ≠ 0 := by intro h; rw [h] at h1; simp at h1
      obtain ⟨m, hm⟩ := he v
      have hl : ((l - 1 : ℕ) : ℤ) = (l : ℤ) - 1 := by
        rw [Nat.cast_sub (Fact.out : l.Prime).one_le, Nat.cast_one]
      have e1 : D.em v x ^ e' v - D.em v x ^ e v = D.em v x ^ e v * ((D.em v x ^ (l - 1)) ^ m - 1) := by
        rw [← zpow_natCast, ← zpow_mul, hl, ← hm, mul_sub, ← zpow_add₀ h0, mul_one, add_sub_cancel]
      rw [hs, hs, e1, map_mul, map_zpow₀, h1, one_zpow, one_mul]
      exact val_zpow_sub (by rw [map_pow, h1, one_pow]) (D.res v x hx) m
    · have hs : ∀ e, D.uf e w = 1 := fun e => Finset.prod_eq_one fun v _ => if_neg fun h => hw ⟨v, h⟩
      rw [hs, hs, sub_self, map_zero]
      exact zero_lt_one
end
