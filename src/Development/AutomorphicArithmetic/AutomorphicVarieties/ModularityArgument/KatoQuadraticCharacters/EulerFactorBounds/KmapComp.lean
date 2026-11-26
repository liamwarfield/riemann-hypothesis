module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
public import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleNewformZetaData

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem ev_map {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M] (f : M →ₗ[R] M)
    (n : ℕ) (x : AdicCompletion I M) (h : AdicCompletion.eval I M n x = 0) :
    AdicCompletion.eval I M n (AdicCompletion.map I f x) = 0 := by
  change (AdicCompletion.map I f x).val n = 0
  rw [AdicCompletion.map_val_apply]
  change (f.reduceModIdeal (I ^ n)) (AdicCompletion.eval I M n x) = 0
  rw [h, map_zero]

private theorem ev_succ {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]
    (n : ℕ) (x : AdicCompletion I M) (h : AdicCompletion.eval I M (n + 1) x = 0) :
    AdicCompletion.eval I M n x = 0 := by
  change x.val n = 0
  rw [← x.property (Nat.le_succ n)]
  change (AdicCompletion.transitionMap I M (Nat.le_succ n)) (AdicCompletion.eval I M (n + 1) x) = 0
  rw [h, map_zero]

private theorem ev_zero {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]
    (x : AdicCompletion I M) : AdicCompletion.eval I M 0 x = 0 := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I M 0 x)
  rw [← hy, Submodule.Quotient.mk_eq_zero]
  simp

private theorem ev_smul {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]
    (n : ℕ) (c : R) (hc : c ∈ I ^ n) (x : AdicCompletion I M) : AdicCompletion.eval I M n (c • x) = 0 := by
  rw [map_smul]
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I M n x)
  rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hc Submodule.mem_top

private theorem kmap_comp (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ ψ χ : X.K ≃+* X.K) (h : ∀ f, χ f = ψ (φ f))
    (x : X.Khat l) : X.kmap l χ x = X.kmap l ψ (X.kmap l φ x) := by
  have hl : (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap =
      (MonoidHom.toAdditive (Units.map ψ.toMonoidHom)).toIntLinearMap ∘ₗ
        (MonoidHom.toAdditive (Units.map φ.toMonoidHom)).toIntLinearMap := by
    ext u
    exact h _
  change AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
      (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap) x =
    AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
      (MonoidHom.toAdditive (Units.map ψ.toMonoidHom)).toIntLinearMap)
      (AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
        (MonoidHom.toAdditive (Units.map φ.toMonoidHom)).toIntLinearMap) x)
  rw [AdicCompletion.map_comp_apply, ← LinearMap.baseChange_comp, hl]

private theorem kmap_id (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (χ : X.K ≃+* X.K) (h : ∀ f, χ f = f)
    (x : X.Khat l) : X.kmap l χ x = x := by
  have hl : (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap = LinearMap.id := by
    ext u
    exact h _
  change AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
      (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap) x = x
  rw [hl, LinearMap.baseChange_id, AdicCompletion.map_id]
  rfl

theorem sApi : SApi := by
  intro Ω _ _ _ ε X l _ n
  refine ⟨⟨fun a u => ?_, fun {a b} hab u => ?_, fun {a b c} hab hbc u => ?_⟩,
    fun a b a' b' h h' => ⟨fun u => ?_, fun u => ?_⟩, fun k a b h u => ?_,
    fun ι S a b h u => ?_, fun k k' a hk => ?_, fun m a b h u => ?_, fun s a b h u => ?_,
    fun a b h u => ev_succ _ _ _ (h u), fun a b u => ev_zero _ _, fun s t a => ?_, fun a => ?_⟩
  · rw [sub_self, map_zero]
  · rw [← neg_sub, map_neg, hab u, neg_zero]
  · rw [← sub_add_sub_cancel (a u) (b u) (c u), map_add (f := _), hab u, hbc u, add_zero]
  · rw [Pi.add_apply, Pi.add_apply, add_sub_add_comm, map_add (f := _), h u, h' u, add_zero]
  · rw [Pi.sub_apply, Pi.sub_apply, sub_sub_sub_comm, map_sub, h u, h' u, sub_zero]
  · rw [Pi.smul_apply, Pi.smul_apply, ← smul_sub, map_smul, h u, smul_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib, map_sum]
      exact Finset.sum_eq_zero (fun i hi => h i hi u)
  · rw [← sub_smul]
    apply ev_smul
    rw [idl, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hk
  · simp only [Tower.act, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← map_sub]
    exact ev_map (idl l) _ n _ (h _)
  · simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← map_sub]
    exact ev_map (idl l) _ n _ (h _)
  · funext u
    simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    have hst : (s * t).toRingEquiv = s.toRingEquiv * t.toRingEquiv := rfl
    rw [hst, map_mul, Units.val_mul,
      show ((cyclotomicCharacter Ω l) s.toRingEquiv : ℤ_[l]) * ((cyclotomicCharacter Ω l) t.toRingEquiv) * u 1 =
        ((cyclotomicCharacter Ω l) t.toRingEquiv) * (((cyclotomicCharacter Ω l) s.toRingEquiv) * u 1) by ring]
    exact kmap_comp X l _ _ _ (GlobalTheory.K4.gal_mul_apply X s t) _
  · funext u
    simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]
    have h1 : (AlgEquiv.toRingEquiv (1 : Gal(Ω/ℚ))) = 1 := rfl
    have hu : ![u 0, u 1] = u := by
      ext i
      fin_cases i <;> rfl
    rw [h1, map_one, Units.val_one, one_mul, hu]
    exact kmap_id X l _ (GlobalTheory.K4.gal_one_apply X) _

end UpperTheory.V.Z.Kato.Nb

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.SymmetricSquareCoefficients

private theorem coeQ (m : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) :
    (((toGQ m : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = m.map (Int.castRingHom ℚ) := by
  unfold toGQ
  rw [dite_eq_left h]
  rfl

private theorem mulQ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (h' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have hmm : 0 < (m * m').det := by
    rw [Matrix.det_mul]
    exact mul_pos h h'
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coeQ _ hmm, coeQ _ h, coeQ _ h', Matrix.map_mul]

private theorem slQ (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  apply Subtype.ext
  apply Units.ext
  rw [coeQ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num)]
  rfl

private theorem detD {N : ℕ} (hN : 0 < N) : (0 : ℤ) < (!![(N : ℤ), 0; 0, 1]).det := by
  simpa [Matrix.det_fin_two_of] using hN

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem eOm_zero : eOm ε 0 = 1 := by
  simp only [eOm, Rat.cast_zero, mul_zero, Complex.exp_zero]
  rw [← map_one ε]
  exact Function.leftInverse_invFun ε.injective 1

private theorem coeff_slD (X : Tower Ω ε) {N : ℕ} (hN : 0 < N) (f : X.K) (r : ℚ) :
    (X.exp (slD X N f)).coeff r = (X.exp f).coeff (r / N) := by
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hg : (((toGQ !![(N : ℤ), 0; 0, 1] : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(N : ℚ), 0; 0, 1] := by
    rw [coeQ _ (detD hN)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h10 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 1 0 = 0 := by simp [ent, hg]
  have h00 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 0 0 = N := by simp [ent, hg]
  have h01 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 0 1 = 0 := by simp [ent, hg]
  have h11 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 1 1 = 1 := by simp [ent, hg]
  have key := X.exp_upper _ h10 f (r / N)
  rw [h00, h01, h11, div_one, div_one, mul_zero, div_mul_cancel₀ _ hN', eOm_zero, one_mul] at key
  exact key

private theorem gal_slD (X : Tower Ω ε) {N : ℕ} (hN : 0 < N) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal s (slD X N f) = slD X N (X.gal s f) := by
  apply X.exp.toRingHom.injective
  ext r
  change (X.exp _).coeff r = (X.exp _).coeff r
  rw [X.gal_exp, coeff_slD X hN, coeff_slD X hN, X.gal_exp]

private theorem sl_slD (X : Tower Ω ε) {N : ℕ} (hN : 0 < N) (h h' : Matrix (Fin 2) (Fin 2) ℤ) (hh : 0 < h.det)
    (e : !![(N : ℤ), 0; 0, 1] * h = h' * !![(N : ℤ), 0; 0, 1]) (f : X.K) :
    X.sl (toGQ h) (slD X N f) = slD X N (X.sl (toGQ h') f) := by
  have hD := detD hN
  have hh' : 0 < h'.det := by
    have key := congrArg Matrix.det e
    rw [Matrix.det_mul, Matrix.det_mul] at key
    exact (mul_pos_iff_of_pos_right hD).1 (key ▸ mul_pos hD hh)
  unfold slD
  rw [← X.sl_mul, ← X.sl_mul, ← mulQ _ _ hD hh, ← mulQ _ _ hh' hD, e]

private theorem un_group (X : Tower Ω ε) (m : ℕ) :
    1 ∈ X.Un m ∧ ∀ f ∈ X.Un m, ∀ f' ∈ X.Un m, f * f' ∈ X.Un m ∧ f⁻¹ ∈ X.Un m := by
  refine ⟨fun W _ => ⟨1, by simp⟩, fun f hf f' hf' => ⟨fun W hW => ?_, fun W hW => ?_⟩⟩
  · obtain ⟨g, hg⟩ := hf W hW
    obtain ⟨g', hg'⟩ := hf' W hW
    refine ⟨g * g', ?_⟩
    have key : ((f * f' : X.Kˣ) : X.K) / ((g * g' : X.Kˣ) : X.K) ^ m = ((f : X.K) / (g : X.K) ^ m) * ((f' : X.K) / (g' : X.K) ^ m) := by
      rw [Units.val_mul, Units.val_mul]
      ring
    rw [key, map_mul, hg, hg', one_mul]
  · obtain ⟨g, hg⟩ := hf W hW
    refine ⟨g⁻¹, ?_⟩
    have key : ((f⁻¹ : X.Kˣ) : X.K) / ((g⁻¹ : X.Kˣ) : X.K) ^ m = ((f : X.K) / (g : X.K) ^ m)⁻¹ := by
      rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_div]
      simp only [inv_pow, div_inv_eq_mul]
      ring
    rw [key, map_inv₀, hg, inv_one]

variable [IsAlgClosure ℚ Ω]

private theorem exPrim (M : ℕ) [NeZero M] : ∃ ζ : Ω, IsPrimitiveRoot ζ M := by
  haveI := IsAlgClosure.isAlgClosed ℚ (K := Ω)
  haveI := algebraRat.charZero Ω
  haveI : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.2 (NeZero.ne M)⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic M Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 (NeZero.pos M)).ne')
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.1 hζ⟩

private theorem uniq (M : ℕ) [NeZero M] (a b : ℕ) (h : ∀ z : Ω, z ^ M = 1 → z ^ a = z ^ b) :
    (a : ZMod M) = b := by
  obtain ⟨ζ, hζ⟩ := exPrim (Ω := Ω) M
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨M, NeZero.pos M, hζ.pow_eq_one⟩
  have key := hfin.pow_eq_pow_iff_modEq.1 (h ζ hζ.pow_eq_one)
  rw [← hζ.eq_orderOf] at key
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 key

private theorem cyc_app (M : ℕ) [NeZero M] (s : Ω ≃ₐ[ℚ] Ω) (z : Ω) (hz : z ^ M = 1) :
    s z = z ^ (cycM M s : ZMod M).val := by
  refine cycM_spec M s ?_ z hz
  obtain ⟨ζ, hζ⟩ := exPrim (Ω := Ω) M
  have hsζ : IsPrimitiveRoot (s ζ) M := hζ.map_of_injective s.injective
  obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one hsζ.pow_eq_one
  have hcop : i.Coprime M := (hζ.pow_iff_coprime (NeZero.pos M) i).1 (hi' ▸ hsζ)
  refine ⟨ZMod.unitOfCoprime i hcop, fun w hw => ?_⟩
  obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hw
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, map_pow, ← hi', ← pow_mul, ← pow_mul, mul_comm]

private theorem cyc_eq (M : ℕ) [NeZero M] (s : Ω ≃ₐ[ℚ] Ω) (a : ℕ) (h : ∀ z : Ω, z ^ M = 1 → s z = z ^ a) :
    (cycM M s : ZMod M) = a := by
  have key := uniq (Ω := Ω) M (cycM M s : ZMod M).val a (fun z hz => by rw [← cyc_app M s z hz, h z hz])
  rwa [ZMod.natCast_zmod_val] at key

private theorem rep_app (M : ℕ) [NeZero M] (y : (ZMod M)ˣ) (z : Ω) (hz : z ^ M = 1) :
    repM (Ω := Ω) M y z = z ^ (y : ZMod M).val := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  obtain ⟨ζ, hζ⟩ := exPrim (Ω := Ω) M
  have hm : ∀ {ξ : Ω}, IsPrimitiveRoot ξ M → Polynomial.cyclotomic M ℚ = minpoly ℚ ξ := fun hξ =>
    minpoly.eq_of_irreducible_of_monic (Polynomial.cyclotomic.irreducible_rat (NeZero.pos M))
      (by rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
          exact hξ.isRoot_cyclotomic (NeZero.pos M)) (Polynomial.cyclotomic.monic M ℚ)
  obtain ⟨s, hs⟩ := (Normal.minpoly_eq_iff_mem_orbit Ω).1
    ((hm (hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime y))).symm.trans (hm hζ))
  have hs' : s ζ = ζ ^ (y : ZMod M).val := hs
  refine repM_spec M y ⟨s, fun w hw => ?_⟩ z hz
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hw
  rw [map_pow, hs', ← pow_mul, ← pow_mul, mul_comm]

end UpperTheory.V.Z.Kato.Nb.SymmetricSquareCoefficients

open UpperTheory.V.Z.Kato.Nb.SymmetricSquareCoefficients in
theorem UpperTheory.V.Z.Kato.Nb.sSlD :
    UpperTheory.V.Z.Kato.Nb.SSlD := by
  intro Ω _ _ _ ε X N hN
  obtain ⟨φ, hφ1, hφ2⟩ := X.j_hol
  have hover := GlobalTheory.T.overAffineJLine_comap_sl_gal ε X ε.injective ⟨φ, hφ2, hφ1⟩
  refine ⟨fun s f => gal_slD X hN s f, fun h h' hh e f => sl_slD X hN h h' hh e f, slQ,
    fun h h' hh hh' => mulQ h h' hh hh', fun m q f hf => ?_, fun m s f hf => ?_, un_group X, fun M _ s => ?_⟩
  · exact KmapA.un_map X (X.sl q).toRingEquiv (fun W hW => (hover W hW).1 q) m f hf
  · exact KmapA.un_map X (X.gal s) (fun W hW => (hover W hW).2 s) m f hf
  refine ⟨?_, fun t => ?_, fun y => ?_, ?_, fun M' _ hM' => ?_⟩
  · have hspec : ∀ z : Ω, z ^ M = 1 → s z = z ^ (cycM M s : ZMod M).val := fun z hz => cyc_app M s z hz
    have heps : ∀ z : Ω, z ^ M = 1 → s z = z ^ (cyc M s).val := by
      unfold cyc
      exact Classical.epsilon_spec (p := fun y : ZMod M => ∀ z : Ω, z ^ M = 1 → s z = z ^ y.val) ⟨_, hspec⟩
    have key := uniq (Ω := Ω) M (cyc M s).val (cycM M s : ZMod M).val (fun z hz => by rw [← heps z hz, hspec z hz])
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at key
  · apply Units.ext
    rw [Units.val_mul, cyc_eq M (s * t) ((cycM M s : ZMod M).val * (cycM M t : ZMod M).val)
      (fun z hz => by rw [AlgEquiv.mul_apply, cyc_app M t z hz, map_pow, cyc_app M s z hz, ← pow_mul]),
      Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  · apply Units.ext
    rw [cyc_eq M (repM M y) (y : ZMod M).val (fun z hz => rep_app M y z hz), ZMod.natCast_zmod_val]
  · rw [mem_fixMu_iff]
    constructor
    · intro hs
      apply Units.ext
      rw [cyc_eq M s 1 (fun z hz => by rw [pow_one]; exact hs z hz), Nat.cast_one, Units.val_one]
    · intro hs z hz
      rw [cyc_app M s z hz, hs, Units.val_one, ZMod.val_one_eq_one_mod]
      have key : z ^ (1 % M) = z ^ 1 := by
        conv_rhs => rw [← Nat.mod_add_div 1 M]
        rw [pow_add, pow_mul, hz, one_pow, mul_one]
      rw [key, pow_one]
  · apply Units.ext
    rw [Units.coe_map, cyc_eq M' s (cycM M s : ZMod M).val
      (fun z hz => cyc_app M s z (by obtain ⟨k, hk⟩ := hM'; rw [hk, pow_mul, hz, one_pow]))]
    simp [ZMod.castHom_apply, ZMod.natCast_val]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls
noncomputable section

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

theorem sCls : SCls := by
  intro Ω _ _ _ ε X l _ n
  obtain ⟨hsurj, hinj, hmul, hone, hsmul, hmap, hsucc⟩ := H3.cls_props Ω ε X l n
  have hdiv : ∀ f f' : X.Kˣ, X.cls l n (f / f') = X.cls l n f - X.cls l n f' := by
    intro f f'
    have h := hmul (f / f') f'
    rw [div_mul_cancel] at h
    rw [h]
    abel
  have hpow : ∀ (f : X.Kˣ) (k : ℕ), X.cls l n (f ^ k) = k • X.cls l n f := by
    intro f k
    induction k with
    | zero => simp [hone]
    | succ k ih => rw [pow_succ, hmul, ih, succ_nsmul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    have hf : (f : X.K) ≠ 0 := f.ne_zero
    show (AdicCompletion.eval (idl l) (X.Kl l) n) (clsK X l n (f : X.K)) = X.cls l n f
    unfold clsK
    rw [dite_eq_left hf, Units.mk0_val]
    unfold liftK
    exact Classical.epsilon_spec (p := fun b => (AdicCompletion.eval (idl l) (X.Kl l) n) b = X.cls l n f)
      (AdicCompletion.eval_surjective (idl l) (X.Kl l) n (X.cls l n f))
  · intro f f' a a' ha ha'
    refine ⟨?_, ?_⟩
    · show (AdicCompletion.eval (idl l) (X.Kl l) n) (a + a') = X.cls l n (f * f')
      rw [map_add (f := _), hmul]
      rw [ha, ha']
    · show (AdicCompletion.eval (idl l) (X.Kl l) n) (a - a') = X.cls l n (f / f')
      rw [map_sub, hdiv]
      rw [ha, ha']
  · intro f a k ha
    show (AdicCompletion.eval (idl l) (X.Kl l) n) (k • a) = X.cls l n (f ^ k)
    rw [map_nsmul, hpow]
    rw [ha]
  · intro f f' a a' ha ha' hc
    obtain ⟨g, hg⟩ := hc
    rw [map_sub]
    rw [ha, ha', (hinj f f').2 ⟨g, hg⟩, sub_self]
  · intro φ f a ha
    exact hmap φ a f ha
  · intro f a ha
    exact hsucc a f ha
  · intro f k a ha
    refine ⟨((PadicInt.toZModPow n) k).val, ?_⟩
    show (AdicCompletion.eval (idl l) (X.Kl l) n) (k • a) = X.cls l n (f ^ ((PadicInt.toZModPow n) k).val)
    rw [map_smul]
    rw [ha, hsmul]

end UpperTheory.V.Z.Kato.Nb

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCycZ
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sCycZ :
    UpperTheory.V.Z.Kato.Nb.SCycZ := by
  intro Ω _ _ _ l _ r s
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hl.ne_zero⟩
    infer_instance
  have hval : ((ReciprocityTheory.Gal.cycMod ℚ Ω l r s : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) =
      PadicInt.toZModPow r (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) := rfl
  have hspec : ∀ z : Ω, z ^ (l ^ r) = 1 →
      s z = z ^ ((ReciprocityTheory.Gal.cycMod ℚ Ω l r s : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
    intro z hz
    rw [hval]
    exact cyclotomicCharacter.spec l s.toRingEquiv z hz
  have hM := cycM_spec (l ^ r) s ⟨_, hspec⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  have heq : ReciprocityTheory.Gal.cycMod ℚ Ω l r s = cycM (l ^ r) s := by
    apply Units.ext
    apply ZMod.val_injective
    exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
      ((hspec ζ hζ.pow_eq_one).symm.trans (hM ζ hζ.pow_eq_one))
  refine ⟨heq, ?_⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
    ZMod.natCast_zmod_val, ← heq, hval, sub_self]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CdFacts
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

private theorem cd_red (N M₀ : ℕ) [NeZero (N * M₀)] (a : ℤ) :
    (((a : ZMod (N * M₀)).val : ℕ) : ZMod M₀) = (a : ZMod M₀) := by
  rw [ZMod.natCast_val, ZMod.cast_intCast (dvd_mul_left M₀ N)]

private theorem cd_div (N M₀ : ℕ) [NeZero N] [NeZero (N * M₀)] (k : ℤ) :
    ((((((N : ℤ) * k : ℤ) : ZMod (N * M₀)).val / N : ℕ)) : ZMod M₀) = (k : ZMod M₀) := by
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h1 : (((((N : ℤ) * k : ℤ) : ZMod (N * M₀)).val / N : ℕ) : ℤ) = k % (M₀ : ℤ) := by
    rw [Int.natCast_div, ZMod.val_intCast, Nat.cast_mul, Int.mul_emod_mul_of_pos _ _ hN,
      Int.mul_ediv_cancel_left _ hN.ne']
  rw [← Int.cast_natCast, h1, ZMod.intCast_mod]

private theorem cd_int (N M₀ : ℕ) [NeZero N] [NeZero (N * M₀)] (h h' : Matrix (Fin 2) (Fin 2) ℤ)
    (e : !![(N : ℤ), 0; 0, 1] * h = h' * !![(N : ℤ), 0; 0, 1]) :
    cD N M₀ (h.map (Int.castRingHom (ZMod (N * M₀)))) = h'.map (Int.castRingHom (ZMod M₀)) := by
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e10 := congrFun (congrFun e 1) 0
  have e11 := congrFun (congrFun e 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, mul_zero, add_zero, zero_add, one_mul, mul_one]
    at e00 e01 e10 e11
  have f00 : h 0 0 = h' 0 0 := mul_left_cancel₀ hN (e00.trans (mul_comm _ _))
  have f10 : h 1 0 = (N : ℤ) * h' 1 0 := e10.trans (mul_comm _ _)
  ext i j
  fin_cases i <;> fin_cases j
  · show ((((h 0 0 : ℤ) : ZMod (N * M₀)).val : ℕ) : ZMod M₀) = ((h' 0 0 : ℤ) : ZMod M₀)
    rw [cd_red, f00]
  · show ((N * ((h 0 1 : ℤ) : ZMod (N * M₀)).val : ℕ) : ZMod M₀) = ((h' 0 1 : ℤ) : ZMod M₀)
    rw [Nat.cast_mul, cd_red, ← e01, Int.cast_mul, Int.cast_natCast]
  · show ((((h 1 0 : ℤ) : ZMod (N * M₀)).val / N : ℕ) : ZMod M₀) = ((h' 1 0 : ℤ) : ZMod M₀)
    rw [f10, cd_div]
  · show ((((h 1 1 : ℤ) : ZMod (N * M₀)).val : ℕ) : ZMod M₀) = ((h' 1 1 : ℤ) : ZMod M₀)
    rw [cd_red, e11]

private theorem cd_lift (N M : ℕ) [NeZero M] (m : Matrix (Fin 2) (Fin 2) (ZMod M))
    (hm : ((m 1 0).val : ZMod N) = 0) :
    ∃ h h' : Matrix (Fin 2) (Fin 2) ℤ, h.map (Int.castRingHom (ZMod M)) = m ∧
      !![(N : ℤ), 0; 0, 1] * h = h' * !![(N : ℤ), 0; 0, 1] := by
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ _).1 hm
  refine ⟨m.map fun a => (a.val : ℤ),
    !![((m 0 0).val : ℤ), N * ((m 0 1).val : ℤ); (k : ℤ), ((m 1 1).val : ℤ)], ?_, ?_⟩
  · ext i j
    show (((m i j).val : ℤ) : ZMod M) = m i j
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  · have hk' : ((m 1 0).val : ℤ) = (k : ℤ) * N := by rw [hk]; push_cast; ring
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, mul_zero, add_zero, zero_add, one_mul, mul_one,
        Matrix.map_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue, hk', mul_comm]

private theorem cd_mul (N M₀ : ℕ) [NeZero N] [NeZero (N * M₀)] (m m' : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀)))
    (hm : ((m 1 0).val : ZMod N) = 0) (hm' : ((m' 1 0).val : ZMod N) = 0) :
    cD N M₀ (m * m') = cD N M₀ m * cD N M₀ m' := by
  obtain ⟨a, a', rfl, ha⟩ := cd_lift N _ m hm
  obtain ⟨b, b', rfl, hb⟩ := cd_lift N _ m' hm'
  have hab : !![(N : ℤ), 0; 0, 1] * (a * b) = (a' * b') * !![(N : ℤ), 0; 0, 1] := by
    rw [← Matrix.mul_assoc, ha, Matrix.mul_assoc, hb, Matrix.mul_assoc]
  rw [← Matrix.map_mul, cd_int N M₀ _ _ hab, cd_int N M₀ _ _ ha, cd_int N M₀ _ _ hb, Matrix.map_mul]

private theorem cd_one (N M₀ : ℕ) [NeZero N] [NeZero (N * M₀)] :
    cD N M₀ (1 : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀))) = 1 := by
  have h := cd_int N M₀ 1 1 (by rw [Matrix.mul_one, Matrix.one_mul])
  rwa [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)] at h

private theorem cd_inv (N M₀ : ℕ) [NeZero (N * M₀)] (m n : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀)))
    (e : n * m = 1) (hm : ((m 1 0).val : ZMod N) = 0) : ((n 1 0).val : ZMod N) = 0 := by
  let φ := ZMod.castHom (dvd_mul_right N M₀) (ZMod N)
  have hφ : ∀ a : ZMod (N * M₀), ((a.val : ℕ) : ZMod N) = φ a := fun a => by
    rw [ZMod.natCast_val, ZMod.castHom_apply]
  rw [hφ] at hm ⊢
  have e0 := congrArg φ (congrFun (congrFun e 0) 0)
  have e1 := congrArg φ (congrFun (congrFun e 1) 0)
  rw [Matrix.mul_apply, Fin.sum_univ_two, map_add (f := _), map_mul, map_mul, hm] at e0 e1
  rw [Matrix.one_apply_eq, map_one] at e0
  rw [Matrix.one_apply_ne (by decide), map_zero] at e1
  linear_combination φ (n 0 0) * e1 - φ (n 1 0) * e0

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sCdFacts :
    UpperTheory.V.Z.Kato.Nb.SCdFacts := by
  intro N M₀ M _ _ _ hM
  subst hM
  refine ⟨cd_mul N M₀, cd_one N M₀, ?_, cd_int N M₀⟩
  intro m hm x y hxy
  have hn := cd_inv N M₀ _ _ m.inv_mul hm
  have key : ∀ z : Row M₀, (2 : ZMod M₀) • z ≠ 0 →
      (2 : ZMod M₀) • (z ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀)))) ≠ 0 := by
    intro z hz h0
    apply hz
    have h1 := congrArg (fun v => v ᵥ* cD N M₀ ((m⁻¹ : GL (Fin 2) (ZMod (N * M₀))) :
      Matrix (Fin 2) (Fin 2) (ZMod (N * M₀)))) h0
    simp only [Matrix.zero_vecMul] at h1
    rwa [Matrix.smul_vecMul, Matrix.vecMul_vecMul, ← cd_mul N M₀ _ _ hm hn, m.mul_inv, cd_one,
      Matrix.vecMul_one] at h1
  exact ⟨key x hxy.1, key y hxy.2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb

def Rel {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l)
    (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l) (N : ℕ) (cf : Coef l) (c n : ℕ) {T : Type} [Mul T] (κ : (Ω ≃ₐ[ℚ] Ω) → T)
    (Y : (Ω ≃ₐ[ℚ] Ω) → T → Fin 2 → Qbar l) (z : (Ω ≃ₐ[ℚ] Ω) → T → X.Fn l) : Prop :=
  ∃ (β : (Ω ≃ₐ[ℚ] Ω) → T → X.Fn l) (b : T → Fin 2 → Qbar l), (∀ s y, LiftB X l N (2 * e - 1) n c (z s y) (β s y)) ∧
    (∀ y i, b y i ∈ cf.O) ∧ ∀ s y, Cv n (Y s y) (pr (β s y) + (rhoK W e ψ s *ᵥ b (y * κ s) - b y))

def eul (l : ℕ) [Fact l.Prime] (e p : ℕ) (a δ : Qbar l) : Qbar l := 1 - a * ((p : Qbar l) ^ (e + 1))⁻¹ + δ * ((p : Qbar l) ^ 2)⁻¹

def SRel0 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → ∀ (c₀ : ℕ) Y, IsZetaSystemFixedExponent X l pr W e ψ N x c d (2 * e + 1) gm cf c₀ Y → ∀ r n : ℕ,
    Rel X l pr W e ψ N cf c₀ n (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) (Y r) fun s y => ∑ r₀, Y0 X l n r N x c d (2 * e - 1) (gm r₀) s y

def SRelT : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → ∀ (p : ℕ) [NeZero p], Nat.Coprime p l → ∀ (c₀ : ℕ) Y, IsZTc X l pr W e ψ N p x c d (2 * e + 1) gm cf c₀ Y → ∀ r n : ℕ,
    Rel X l pr W e ψ N cf c₀ n (kT l r p) (Y r) fun s y => ∑ r₀, YT X l n r N p x c d (2 * e - 1) (gm r₀) s y

def SN2rho : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → (∀ s i k, mat W s i k ∈ cf.O) → ∃ m : ℕ, ∀ (p : ℕ) [NeZero p], p.Prime → Nat.Coprime p (l * N) → ∀ a δ : Qbar l, a ∈ cf.O → δ ∈ cf.O →
    (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeT N l p b) = a • pr b ∧ pr (X.diam N l p b) = δ • pr b) →
    ∀ (c₀ c₁ r n : ℕ) (Y : (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (Y' : (Ω ≃ₐ[ℚ] Ω) → (ZMod p)ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) z z',
      Rel X l pr W e ψ N cf c₀ n (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) Y z → Rel X l pr W e ψ N cf (c₀ + c₁) n (kT l r p) Y' z' →
      CohB X l N (2 * e - 1) n (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) (fun s y => (p : ℤ_[l]) • ∑ t, z' s (t, y))
        (fun s y => (p : ℤ_[l]) • z s y - X.heckeT N l p (z s (y * inv1 (l ^ r) p)) +
          (p : ℤ_[l]) ^ (2 * e - 1) • X.diam N l p (z s (y * inv1 (l ^ r) p ^ 2))) →
      ∃ b : (ZMod (l ^ r))ˣ → Fin 2 → Qbar l, (∀ y i, b y i ∈ cf.O) ∧ ∀ s y,
        Cv n ((((l : ℕ) : Qbar l) ^ m * (p : Qbar l)) • ∑ t, Y' s (t, y))
          (((l : ℕ) : Qbar l) ^ (m + c₁) • ((p : Qbar l) • Y s y - a • Y s (y * inv1 (l ^ r) p) +
            ((p : Qbar l) ^ (2 * e - 1) * δ) • Y s (y * inv1 (l ^ r) p ^ 2)) +
            (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y))

def SInteg : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → (∀ s i k, mat W s i k ∈ cf.O) → (∀ s : G ℚ Ω, ‖thK l e ψ s‖ = 1) ∧ ψ 1 = 1 ∧ (∀ u v : (ZMod l)ˣ, ψ ((u * v : (ZMod l)ˣ) : ZMod l) = ψ u * ψ v) ∧
    (∀ u : (ZMod l)ˣ, ψ u ∈ cf.O) ∧ (∀ s i k, rhoK W e ψ s i k ∈ cf.O) ∧ (∀ s t, rhoK W e ψ (s * t) = rhoK W e ψ s * rhoK W e ψ t) ∧
    ∀ (c₀ : ℕ) Y, IsZetaSystemFixedExponent X l pr W e ψ N x c d (2 * e + 1) gm cf c₀ Y → ∀ r s y i, ‖Y r s y i‖ ≤ 1

def SSpec : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → (∀ s i k, mat W s i k ∈ cf.O) → ∀ (p r : ℕ), p.Prime → l ∣ p - 1 → ∀ (a δ k : Qbar l), ‖a‖ ≤ 1 → ‖δ‖ ≤ 1 → ‖k‖ ≤ 1 →
    ∀ (Y V : (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (b : (ZMod (l ^ r))ˣ → Fin 2 → Qbar l), (∀ s y i, ‖Y s y i‖ ≤ 1) → (∀ y i, b y i ∈ cf.O) →
      (∀ s y, Cv r ((p : Qbar l) • V s y) (k • ((p : Qbar l) • Y s y - a • Y s (y * inv1 (l ^ r) p) +
          ((p : Qbar l) ^ (2 * e - 1) * δ) • Y s (y * inv1 (l ^ r) p ^ 2)) +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y))) →
      ∃ b' : Fin 2 → Qbar l, (∀ i, b' i ∈ cf.O) ∧ ∀ s, Cv r (spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x) V s)
        (eul l e p a δ • (k • spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x) Y s) + (mat W s *ᵥ b' - b'))

def SDetChar : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (χ : G ℚ Ω →* (Qbar l)ˣ),
    Continuous ρ → Continuous χ → (∃ s, ∀ t : Qbar l, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) ≠ t • 1) → ∀ S : Finset ℕ,
    (∀ (v : Pl) (B : ValuationSubring Ω) (σ : G ℚ Ω), normV v ∉ S → IsPlaceOver B v → IsFrob B (normV v) σ → ∃ a : Qbar l,
      (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)) ^ 2 - a • (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)) + (χ σ : Qbar l) • 1 = 0) →
    ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = χ s

def SDiamChar : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → Nat.Coprime l N → (∃ b ∈ X.B N l (2 * e - 1), pr b ≠ 0) → ∃ δ : (ZMod N)ˣ →* (Qbar l)ˣ, ∀ (q : ℕ) (u : (ZMod N)ˣ), q.Prime → ¬ q ∣ l * N →
    (u : ZMod N) = q → ∀ b ∈ X.B N l (2 * e - 1), pr (X.diam N l q b) = (δ u : Qbar l) • pr b

def SEuler : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → Nat.Coprime l N → ∀ S : Finset Pl, Nf e S A W → (∀ s i k, mat W s i k ∈ cf.O) → ∃ S' : Finset Pl, S ⊆ S' ∧ ∀ w : Pl, w ∉ S' →
    (normV w).Prime ∧ Nat.Coprime (normV w) (l * N * c * d) ∧ ∃ a δ : Qbar l, a ∈ cf.O ∧ δ ∈ cf.O ∧
      (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeT N l (normV w) b) = a • pr b ∧ pr (X.diam N l (normV w) b) = δ • pr b) ∧
      ∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ →
        eps l σ = (normV w : Qbar l) ∧ (rhoK W e ψ σ).trace = a ∧ (rhoK W e ψ σ).det = (normV w : Qbar l) ^ (2 * e) * δ

def SEulCg : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → ∀ (p n : ℕ), p.Prime → 1 ≤ n → l ^ n ∣ p - 1 → ∀ a δ : Qbar l, a ∈ cf.O → δ ∈ cf.O → eul l e p a δ ∈ cf.O ∧
    ∀ σ : G ℚ Ω, ψ 1 = 1 → eps l σ = (p : Qbar l) → (rhoK W e ψ σ).trace = a → (rhoK W e ψ σ).det = (p : Qbar l) ^ (2 * e) * δ →
      Cg n (eul l e p a δ) (1 * (mat W σ - 1).det)

def SPushPsi : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (cf : Coef l) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l))
    (p n : ℕ) [NeZero p] (ψw : G ℚ Ω →* Multiplicative (ZMod (l ^ n))), KillsMu p ψw →
    ∀ Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod p)ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
      (∀ r s s' y, Y r (s * s') y = Y r s y + ρ s *ᵥ Y r s' (y * cycT l r p s)) →
      (∀ r, Y r = GlobalTheory.KA.push (Prod.map id (redL l r)) (Y (r + 1))) → (∀ r y i, Continuous fun s => Y r s y i) → (∀ r s u i, Y r s u i ∈ cf.O) →
      ∃ Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
        (∀ r, ShCoc ρ (ψw.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) ∧ (∀ r x i, Continuous fun s => Yw r s x i) ∧ (∀ r s x i, Yw r s x i ∈ cf.O) ∧
        (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) ∧
        ∀ r s y, ∑ a, Yw r s (a, y) = ∑ t, Y r s (t, y)

def KatoTameRelationProjected : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
  (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
  (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
  (ψ : ZMod l → Qbar l) (cf : Coef l) (S : Finset Pl),
  Nf e S A W → (∀ s i k, mat W s i k ∈ cf.O) → (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → Nat.Coprime l N → l ≠ 2 → 1 ≤ e → (∃ x, cw x ≠ 0) →
  (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → AdmWn ι e gN A W X pr N cw c d gm ψ cf →
  ∀ (c₀ : ℕ) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l), IsZWc X l pr W e ψ N cw c d (2 * e + 1) gm cf c₀ Y →
  ∃ (k : ℕ) (S' : Finset Pl), (∀ w : Pl, w ∉ S' → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) ∧
  ∀ n : ℕ, 1 ≤ n → ∀ w : Pl, w ∉ S' → l ^ n ∣ normV w - 1 → ∀ ψw : G ℚ Ω →* Multiplicative (ZMod (l ^ n)),
    KillsMu (normV w) ψw → Function.Surjective ψw →
    ∃ (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (P u : Qbar l)
      (b : ℕ → Fin 2 → Qbar l),
      (∀ r, ShCoc (rhoK W e ψ) (ψw.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) ∧ (∀ r x i, Continuous fun s => Yw r s x i) ∧
      (∀ r s x i, Yw r s x i ∈ cf.O) ∧
      (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) ∧
      P ∈ cf.O ∧ ‖u‖ = 1 ∧ (∀ r i, b r i ∈ cf.O) ∧
      (∀ r s i, ‖(∑ a, spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x) (fun s x => Yw r s (a, x)) s) i -
          (P • (((l : ℕ) : Qbar l) ^ k • spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x) (Y r) s) + (mat W s *ᵥ b r - b r)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) ∧
      (∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ → Cg n P (u * (mat W σ - 1).det))

end UpperTheory.V.Z.Kato.Nb

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DiamEx
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

private theorem diam_ex (N l p : ℕ) (h : Nat.Coprime p (l * N)) : IsDiam N l p (sgD N l p) := by
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) ((l * N : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr h
  refine Classical.epsilon_spec (p := IsDiam N l p)
    ⟨⟨!![a, -b; ((l * N : ℕ) : ℤ), (p : ℤ)], by rw [Matrix.det_fin_two_of]; linear_combination hab⟩, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩ <;> refine CongruenceSubgroup.Gamma0_mem.mpr ?_ <;>
      show (Int.cast ((l * N : ℕ) : ℤ) : ZMod _) = 0 <;> simp
  · simp [en]

private theorem conj_mem (N l : ℕ) (σ γ : SL(2, ℤ))
    (hσ : σ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) (hγ : γ ∈ Gam N l) :
    σ * γ * σ⁻¹ ∈ Gam N l := by
  obtain ⟨hN, hl⟩ := Subgroup.mem_inf.mp hσ
  rw [CongruenceSubgroup.Gamma0_mem] at hN hl
  have h1 : (N : ℤ) ∣ σ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hN
  have h2 : (l : ℤ) ∣ σ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hl
  have h4 : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := σ.2; rw [Matrix.det_fin_two] at this; exact this
  have hP := StabHecke.congruenceCondition_of_mem hγ
  have hg : ((σ * γ * σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) =
      (σ : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
  have e00 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 = σ 0 0 * γ 0 0 + σ 0 1 * γ 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = σ 1 0 * γ 0 0 + σ 1 1 * γ 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine StabHecke.mem_Gam_of_mul N l _ _ _ hg h1 h2 (StabHecke.isCoprime_of_det h4 h1)
    (StabHecke.isCoprime_of_det h4 h2) ?_ ?_ ?_
  · rw [e00, show σ 0 0 * γ 0 0 + σ 0 1 * γ 1 0 - σ 0 0 = σ 0 0 * (γ 0 0 - 1) + σ 0 1 * γ 1 0 by ring]
    exact dvd_add (dvd_mul_of_dvd_right hP.1 _) (dvd_mul_of_dvd_right hP.2.1 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right hP.2.1 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_right hP.2.2.1 _)

theorem UpperTheory.V.Z.Kato.Nb.sBStab :
    UpperTheory.V.Z.Kato.Nb.SBStab := by
  intro Ω _ _ _ ε X l _ N w hN b hb
  obtain ⟨hA, hG⟩ := GlobalTheory.T.modular_function_tower_integrality ε X ε.injective (X.j_hol.imp fun _ h => h.symm) l
  have key : ∀ f : X.Fn l →ₗ[ℤ_[l]] X.Fn l, (∀ c ∈ X.BSet N l w, f c ∈ X.BSet N l w) → f b ∈ X.B N l w := by
    intro f hf
    have hle : X.B N l w ≤ (X.B N l w).comap f :=
      Submodule.span_le.mpr fun x hx => Submodule.subset_span (hf x hx)
    exact hle hb
  have hdet : ∀ h : SL(2, ℤ), 0 < (h : Matrix (Fin 2) (Fin 2) ℤ).det := fun h => by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos
  refine ⟨fun s => key _ fun c hc => ⟨StabGal.galB_mem_Pol X l w s (hG s) c hc.1,
    fun γ hγ => StabGal.inv_galB X N l w hN s c hc γ hγ⟩, fun σ hσ => key _ fun c hc => ?_,
    fun p hp hc' => key _ fun c hc => ?_⟩
  · refine ⟨StabHecke.polAct X l w _ (hA _) c hc.1, fun γ hγ => ?_⟩
    have hg : (σ : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
        ((σ * γ * σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
    rw [StabHecke.act_act X l _ _ (hdet γ) (hdet σ), hg, ← StabHecke.act_act X l _ _ (hdet σ) (hdet _),
      hc.2 _ (conj_mem N l σ γ hσ hγ)]
  · have hσ := diam_ex N l p hc'
    have hpl : IsCoprime (p : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.coprime_mul_right_right hc')
    refine ⟨?_, fun γ hγ => ?_⟩
    · rw [StabHecke.heckeT_eq]
      exact StabHecke.Pol_sum X l w _ _ fun o _ => StabHecke.polAct X l w _ (hA _) c hc.1
    · rw [StabHecke.heckeT_eq]
      exact StabHecke.sum_act_inv X l N (StabHecke.repT p (sgD N l p))
        (fun o => by rw [StabHecke.det_repT]; exact_mod_cast hp.pos) γ
        (StabHecke.map_T hp hσ hpl γ hγ) (StabHecke.coset_representatives_hecke_disjoint hp _) c hc.2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.XiScal
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

private theorem xs_cast {d M : ℕ} [NeZero M] (h : d ∣ M) (z : ZMod M) :
    ((z.val : ℕ) : ZMod d) = ZMod.castHom h (ZMod d) z := by
  rw [ZMod.castHom_apply, ZMod.natCast_val]

private theorem xs_eval {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (k k' : ℤ_[l]) (a : X.Khat l) (h : PadicInt.toZModPow n k = PadicInt.toZModPow n k') :
    AdicCompletion.eval (idl l) (X.Kl l) n (k • a - k' • a) = 0 := by
  have h1 : k - k' ∈ (idl l) ^ n := by
    rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h, sub_self]
  rw [← sub_smul, map_smul]
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n a)
  rw [← hv, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul h1 Submodule.mem_top

private theorem xs_cD (N M₀ M : ℕ) [NeZero N] [NeZero M] (hM : M = N * M₀) (c : ZMod M)
    (m : Matrix (Fin 2) (Fin 2) (ZMod M)) (h : ((m 1 0).val : ZMod N) = 0) :
    cD N M₀ (c • m) = ((c.val : ℕ) : ZMod M₀) • cD N M₀ m := by
  have hM₀ : M₀ ∣ M := ⟨N, by rw [hM, mul_comm]⟩
  have key : ∀ z : ZMod M, ((c * z).val : ZMod M₀) = (c.val : ZMod M₀) * (z.val : ZMod M₀) := by
    intro z
    rw [xs_cast hM₀, xs_cast hM₀, xs_cast hM₀, map_mul]
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff _ _).1 h
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h10 : (c * m 1 0).val / N = c.val * q % M₀ := by
    rw [ZMod.val_mul, hq]
    generalize c.val = cv
    rw [hM, mul_left_comm, Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ hN]
  have hq' : (m 1 0).val / N = q := by
    rw [hq, Nat.mul_div_cancel_left _ hN]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [cD, Matrix.smul_apply, smul_eq_mul, key, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue]
  · simp only [cD, Matrix.smul_apply, smul_eq_mul, key, Nat.cast_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue, Fin.mk_one]
    ring
  · simp only [cD, Matrix.smul_apply, smul_eq_mul, h10, hq', ZMod.natCast_mod, Nat.cast_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue, Fin.mk_one]
  · simp only [cD, Matrix.smul_apply, smul_eq_mul, key, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue, Fin.mk_one]

private theorem xs_Cnd (l N M : ℕ) [Fact l.Prime] [NeZero M] (hN : N ∣ M) (hl : l ∣ M) (g : SL(2, ℤ)) (ν : (ZMod M)ˣ)
    (hν : ((ν : ZMod M).val : ZMod N) = 1) (m : Matrix (Fin 2) (Fin 2) (ZMod M)) :
    Cnd l N g ((ν : ZMod M) • m) ↔ Cnd l N g m := by
  have key : ∀ z : ZMod M, (((ν : ZMod M) * z).val : ZMod N) = (z.val : ZMod N) := by
    intro z
    rw [xs_cast hN, xs_cast hN, map_mul, ← xs_cast hN, hν, one_mul]
  have key' : ∀ z : ZMod M, (((ν : ZMod M) * z).val : ZMod l) = ZMod.castHom hl (ZMod l) (ν : ZMod M) * (z.val : ZMod l) := by
    intro z
    rw [xs_cast hl, xs_cast hl, map_mul]
  have hu : IsUnit (ZMod.castHom hl (ZMod l) (ν : ZMod M)) := (ν.isUnit).map _
  simp only [Cnd, Matrix.smul_apply, smul_eq_mul, key, key']
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  rw [mul_left_comm, mul_left_comm (↑(en g 0 0) : ZMod l)]
  exact hu.mul_right_inj

private theorem xs_sum {R ι A B : Type} [CommRing R] [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (L : A →ₗ[R] B) (e : ι ≃ ι) (s t : Finset ι) (f g : ι → A) (h : ∀ i, i ∈ s ↔ e i ∈ t)
    (h' : ∀ i ∈ s, L (f i - g (e i)) = 0) : L (∑ i ∈ s, f i - ∑ i ∈ t, g i) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.sum_equiv e (t := t) (g := g) h (fun _ _ => rfl), ← Finset.sum_sub_distrib, map_sum]
  exact Finset.sum_eq_zero h'

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sXiScal :
    UpperTheory.V.Z.Kato.Nb.SXiScal := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL x y P a ν hν
  have hM := hL.eq
  have hNM : N ∣ M := ⟨M₀, hM⟩
  have hM₀M : M₀ ∣ M := ⟨N, by rw [hM, mul_comm]⟩
  have hlM₀ : l ^ n ∣ M₀ := hL.dl
  have hlM : l ∣ M := (dvd_pow_self l (by have := hL.pos; omega)).trans (hlM₀.trans hM₀M)
  have hlnM : l ^ n ∣ M := hlM₀.trans hM₀M
  let U : GL (Fin 2) (ZMod M) := Units.map (Matrix.scalar (Fin 2) : ZMod M →+* Matrix (Fin 2) (Fin 2) (ZMod M)).toMonoidHom ν
  have hU : ∀ m : GL (Fin 2) (ZMod M), ((U * m : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) = (ν : ZMod M) • (m : Matrix _ _ _) := by
    intro m
    ext i j
    simp [U]
  have hdet : ∀ m : GL (Fin 2) (ZMod M), Matrix.GeneralLinearGroup.det (U * m) = ν ^ 2 * Matrix.GeneralLinearGroup.det m := by
    intro m
    ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hU, Matrix.det_smul, Fintype.card_fin]
  unfold CgF
  intro u
  simp only [Xi, Pi.smul_apply, Finset.smul_sum, smul_smul]
  refine xs_sum (AdicCompletion.eval (idl l) (X.Kl l) n) (Equiv.mulLeft U) _ _ _ _ ?_ ?_
  · intro m
    have hP : ν ^ 2 * Matrix.GeneralLinearGroup.det m * ν⁻¹ ^ 2 = Matrix.GeneralLinearGroup.det m := by
      rw [inv_pow, mul_right_comm, mul_inv_cancel, one_mul]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulLeft, hU, hdet, hP, xs_Cnd l N M hNM hlM g ν hν]
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    simp only [Equiv.coe_mulLeft, hU, hdet]
    rw [xs_cD N M₀ M hM _ _ hm.1.1, Matrix.vecMul_smul, Matrix.vecMul_smul, Matrix.smul_vecMul, Matrix.smul_vecMul]
    apply xs_eval
    simp only [map_mul, map_pow, map_add (f := _), map_natCast, Matrix.smul_apply, smul_eq_mul, xs_cast hlnM]
    rw [mul_inv, Units.val_mul, map_mul, ← inv_pow, Units.val_pow_eq_pow_val, map_pow]
    have hee : ZMod.castHom hlnM (ZMod (l ^ n)) (ν : ZMod M) * ZMod.castHom hlnM (ZMod (l ^ n)) ((ν⁻¹ : (ZMod M)ˣ) : ZMod M) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    set e := ZMod.castHom hlnM (ZMod (l ^ n)) (ν : ZMod M)
    set e' := ZMod.castHom hlnM (ZMod (l ^ n)) ((ν⁻¹ : (ZMod M)ˣ) : ZMod M)
    rw [mul_assoc e, mul_assoc e, ← mul_add, mul_pow]
    set D := ZMod.castHom hlnM (ZMod (l ^ n)) ((Matrix.GeneralLinearGroup.det m)⁻¹ : (ZMod M)ˣ)
    set A := ZMod.castHom hlnM (ZMod (l ^ n)) ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 0) * PadicInt.toZModPow n (u 0) + ZMod.castHom hlnM (ZMod (l ^ n)) ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1) * PadicInt.toZModPow n (u 1)
    linear_combination (-(e ^ w * D * A ^ w * (e * e' + 1))) * hee
end
