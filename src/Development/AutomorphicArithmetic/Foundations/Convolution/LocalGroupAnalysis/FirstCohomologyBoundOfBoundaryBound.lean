module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.SeparableOfMap

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NmCent
open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

private theorem cent_sg_up (σ : R ≃ₐ[k] R) (γ : GL (Fin n) k) : sg σ (up R γ) = up R γ := by
  ext a b
  simp [sg, up, Matrix.GeneralLinearGroup.map_apply]

private theorem cent_nm_sg (σ : R ≃ₐ[k] R) (q : ℕ) (d : GL (Fin n) R) :
    nm σ q (sg σ d) = sg σ (nm σ q d) := by
  unfold nm
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  ext a b
  change (σ ^ m) (σ _) = σ ((σ ^ m) _)
  rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← pow_succ, ← pow_succ']

private theorem cent_up_inj (h : Function.Injective (algebraMap k R)) :
    Function.Injective (up R : GL (Fin n) k → GL (Fin n) R) := by
  intro s t hst
  ext a b
  exact h (congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) a b) hst)

private theorem cent_descend {σ : R ≃ₐ[k] R} {q : ℕ} (hσ : IsGal σ q) (x : GL (Fin n) R) (hx : sg σ x = x) :
    ∃ t : GL (Fin n) k, x = up R t := by
  have key : ∀ y : GL (Fin n) R, sg σ y = y → ∃ M : Matrix (Fin n) (Fin n) k,
      M.map (algebraMap k R) = (y : Matrix (Fin n) (Fin n) R) := by
    intro y hy
    have h : ∀ a b, ∃ c, algebraMap k R c = (y : Matrix (Fin n) (Fin n) R) a b := fun a b =>
      hσ.fix _ (congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) a b) hy)
    choose M hM using h
    exact ⟨Matrix.of M, by ext a b; exact hM a b⟩
  obtain ⟨M, hM⟩ := key x hx
  obtain ⟨N, hN⟩ := key x⁻¹ (by rw [map_inv, hx])
  have inj := Matrix.map_injective (m := Fin n) (n := Fin n) hσ.inj
  refine ⟨⟨M, N, inj ?_, inj ?_⟩, Units.ext hM.symm⟩
  · dsimp only
    rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _), Units.mul_inv]
  · dsimp only
    rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _), Units.inv_mul]

end

end UpperTheory.ConvolutionTheory.D

theorem UpperTheory.ConvolutionTheory.D.nmCent :
    UpperTheory.ConvolutionTheory.D.NmCent := by
  intro k R _ _ _ _ σ q hσ n a γ hsep ha x
  haveI : Module.Finite k R := (galBase k R k σ q hσ).1
  have hs : ((up R γ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpoly.Separable := by
    have h := hsep.map (f := algebraMap k R)
    rw [cp, ← Matrix.charpoly_map] at h
    exact h
  have hc := (conjSep k R n _ hs).2.1
  have hfix : ∀ y, nm σ q (sgConj σ y a) = up R γ → y * up R γ = up R γ * y := by
    intro y hy
    rw [(nmPoly k R σ q hσ n a).2 y, ha, mul_assoc, inv_mul_eq_iff_eq_mul] at hy
    exact hy.symm
  have hag : a * up R γ = up R γ * a := by
    apply hfix
    rw [sgConj, inv_mul_cancel, one_mul, cent_nm_sg, ha, cent_sg_up]
  have hcomm : ∀ y : GL (Fin n) R, y * up R γ = up R γ * y → a * y = y * a := by
    intro y hy
    obtain ⟨p, hp⟩ := hc a.val (by simpa using congrArg Units.val hag)
    obtain ⟨p', hp'⟩ := hc y.val (by simpa using congrArg Units.val hy)
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hp, hp', ← map_mul, ← map_mul, mul_comm]
  constructor
  · intro hx
    have h1 := hfix x (by rw [hx, ha])
    have h2 := hcomm x h1
    have h3 : sg σ x = x := by
      rw [sgConj, mul_assoc, inv_mul_eq_iff_eq_mul, ← h2] at hx
      exact mul_left_cancel hx
    obtain ⟨t, rfl⟩ := cent_descend hσ x h3
    refine ⟨t, cent_up_inj hσ.inj ?_, rfl⟩
    rw [map_mul, map_mul, h1]
  · rintro ⟨t, ht, rfl⟩
    have h2 := hcomm (up R t) (by rw [← map_mul, ← map_mul, ht.eq])
    rw [sgConj, cent_sg_up, mul_assoc, h2, inv_mul_cancel_left]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.PowComp
open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

private theorem cp_map {S R : Type} [CommRing S] [CommRing R] {n : ℕ} (j : S →+* R) (g : GL (Fin n) S) :
    cp (Matrix.GeneralLinearGroup.map j g) = (cp g).map j := by
  unfold cp
  rw [← Matrix.charpoly_map]
  rfl

private theorem cp_conj {R : Type} [CommRing R] {n : ℕ} (x g : GL (Fin n) R) :
    cp (x⁻¹ * g * x) = cp g := by
  unfold cp
  rw [Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, ← mul_assoc, mul_inv_cancel, one_mul]

section
variable {O S k R : Type} [CommRing O] [CommRing S] [Algebra O S] [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

private theorem map_sg (j : S →+* R) (s : S ≃ₐ[O] S) (σ : R ≃ₐ[k] R) (h : ∀ x, j (s x) = σ (j x))
    (g : GL (Fin n) S) :
    Matrix.GeneralLinearGroup.map j (sg s g) = sg σ (Matrix.GeneralLinearGroup.map j g) := by
  ext a b
  exact h _

private theorem pow_comp (j : S →+* R) (s : S ≃ₐ[O] S) (σ : R ≃ₐ[k] R) (h : ∀ x, j (s x) = σ (j x))
    (m : ℕ) : ∀ x, j ((s ^ m) x) = (σ ^ m) (j x) := by
  induction m with
  | zero => intro x; rfl
  | succ m ih => intro x; rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih, h]

private theorem map_nm (j : S →+* R) (s : S ≃ₐ[O] S) (σ : R ≃ₐ[k] R) (h : ∀ x, j (s x) = σ (j x))
    (q : ℕ) (g : GL (Fin n) S) :
    Matrix.GeneralLinearGroup.map j (nm s q g) = nm σ q (Matrix.GeneralLinearGroup.map j g) := by
  unfold nm
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  exact map_sg j (s ^ m) (σ ^ m) (pow_comp j s σ h m) g

private theorem map_up (i : O →+* k) (j : S →+* R) (h : ∀ x, j (algebraMap O S x) = algebraMap k R (i x))
    (g : GL (Fin n) O) :
    Matrix.GeneralLinearGroup.map j (up S g) = up R (Matrix.GeneralLinearGroup.map i g) := by
  ext a b
  exact h _

end

end UpperTheory.ConvolutionTheory.D

theorem UpperTheory.ConvolutionTheory.D.nmInt :
    UpperTheory.ConvolutionTheory.D.NmInt := by
  intro O S k R _ _ _ _ _ _ _ i j s σ q hs hσ hj hjs hji n a a' γ hγ ha x hx
  have h1 : cp (nm s q a') = cp (nm s q a) := by
    apply Polynomial.map_injective j hj
    rw [← cp_map, ← cp_map, map_nm j s σ hjs, map_nm j s σ hjs, ← hx,
      (nmPoly k R σ q hσ n _).2, cp_conj]
  have h2 : (cp (nm s q a)).Separable := by
    rw [ha, up, cp_map]
    exact hγ.map
  obtain ⟨u, hu⟩ := nmInj O S s q hs n a a' h2 h1
  have h3 : (cp (Matrix.GeneralLinearGroup.map i γ)).Separable := by
    rw [cp_map]
    exact hγ.map
  have h4 : nm σ q (Matrix.GeneralLinearGroup.map j a) = up R (Matrix.GeneralLinearGroup.map i γ) := by
    rw [← map_nm j s σ hjs, ha, map_up i j hji]
  have h5 : sgConj σ (x * (Matrix.GeneralLinearGroup.map j u)⁻¹) (Matrix.GeneralLinearGroup.map j a) =
      Matrix.GeneralLinearGroup.map j a := by
    rw [hu, sgConj, sgConj, map_mul, map_mul, map_inv, map_sg j s σ hjs] at hx
    rw [sgConj, map_mul, map_inv]
    calc _ = Matrix.GeneralLinearGroup.map j u * (x⁻¹ * Matrix.GeneralLinearGroup.map j a * sg σ x) *
          (sg σ (Matrix.GeneralLinearGroup.map j u))⁻¹ := by group
      _ = _ := by rw [hx]; group
  obtain ⟨t, ht, hxt⟩ := (nmCent k R σ q hσ n _ _ h3 h4 _).1 h5
  exact ⟨t, u, ht, by rw [← hxt]; group⟩
end

open PositivityTheory.Rg.Tf.Geo

open Polynomial NumberField IsDedekindDomain UpperTheory.ConvolutionTheory.D
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.G

section Abstract

variable {n : ℕ}

private def IntGL {R : Type} [CommRing R] (S : Subring R) (g : GL (Fin n) R) : Prop :=
  (∀ i j, g i j ∈ S) ∧ ∀ i j, (g⁻¹ : GL (Fin n) R) i j ∈ S

private theorem intGL_iff {R : Type} [CommRing R] (S : Subring R) (g : GL (Fin n) R) :
    IntGL S g ↔ ∃ u : GL (Fin n) S, Matrix.GeneralLinearGroup.map S.subtype u = g := by
  constructor
  · rintro ⟨h1, h2⟩
    let A : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨g i j, h1 i j⟩
    let B : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨(g⁻¹ : GL (Fin n) R) i j, h2 i j⟩
    have hinj : Function.Injective (RingHom.mapMatrix (m := Fin n) S.subtype) :=
      fun M N h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
    have hA : RingHom.mapMatrix S.subtype A = (g : Matrix (Fin n) (Fin n) R) := rfl
    have hB : RingHom.mapMatrix S.subtype B = ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := rfl
    exact ⟨⟨A, B, hinj (by rw [map_mul, map_one, hA, hB, Units.mul_inv]),
      hinj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])⟩, Units.ext hA⟩
  · rintro ⟨u, rfl⟩
    refine ⟨fun i j => (u i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((u⁻¹ : GL (Fin n) S) i j).2

variable {k R : Type} [Field k] [CommRing R] [Algebra k R]

private theorem isGal_equiv {R' : Type} [CommRing R'] [Algebra k R'] (e : R ≃ₐ[k] R') {σ : R ≃ₐ[k] R} {q : ℕ}
    (h : IsGal σ q) : IsGal (e.symm.trans (σ.trans e)) q := by
  have hp : ∀ (j : ℕ) x, ((e.symm.trans (σ.trans e)) ^ j) (e x) = e ((σ ^ j) x) := by
    intro j x
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih]; simp
  obtain ⟨s, x, y, hxy⟩ := h.sep
  refine ⟨h.pos, AlgEquiv.ext fun z => ?_, fun a b hab => h.inj (e.injective (by rw [e.commutes, e.commutes, hab])),
    fun z hz => ?_, s, fun i => e (x i), fun i => e (y i), fun j hj => ?_⟩
  · obtain ⟨z, rfl⟩ := e.surjective z
    rw [hp, h.pow]; rfl
  · obtain ⟨z, rfl⟩ := e.surjective z
    obtain ⟨c, rfl⟩ := h.fix z (e.injective (by simpa using hz))
    exact ⟨c, (e.commutes c).symm⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [hp, ← map_mul, ← map_sum, hxy j hj]
      split_ifs <;> simp

private theorem abstract_hilbert90 (σ : R ≃ₐ[k] R) (q : ℕ) (hσ : IsGal σ q) (O : Subring k) [IsLocalRing O] (S : Subring R)
    (hOS : ∀ x, algebraMap k R x ∈ S ↔ x ∈ O) (hS : ∀ r ∈ S, σ r ∈ S)
    (hsep : ∃ (s : ℕ) (x y : Fin s → R), (∀ i, x i ∈ S ∧ y i ∈ S) ∧
      ∀ j < q, ∑ i, x i * (σ ^ j) (y i) = if j = 0 then 1 else 0)
    (a : GL (Fin n) R) (γ : GL (Fin n) k) (ha : IntGL S a) (hγ : IntGL O γ)
    (hs : ∃ u w : k[X], u ∈ lifts O.subtype ∧ w ∈ lifts O.subtype ∧ u * cp γ + w * derivative (cp γ) = 1)
    (hN : nm σ q a = up R γ) (x : GL (Fin n) R) :
    IntGL S (sgConj σ x a) ↔ ∃ t : GL (Fin n) k, t * γ = γ * t ∧ ∃ y, IntGL S y ∧ x = up R t * y := by
  have hpow : ∀ (m : ℕ), ∀ r ∈ S, (σ ^ m) r ∈ S := by
    intro m r hr
    induction m with
    | zero => exact hr
    | succ m ih => rw [pow_succ', AlgEquiv.mul_apply]; exact hS _ ih
  have hinv : ∀ r ∈ S, σ.symm r ∈ S := by
    intro r hr
    have h1 : σ ^ (q - 1) * σ = 1 := by rw [← pow_succ, Nat.sub_add_cancel hσ.pos, hσ.pow]
    have h2 : σ.symm r = (σ ^ (q - 1)) r := by
      rw [eq_inv_of_mul_eq_one_left h1]; rfl
    rw [h2]; exact hpow _ _ hr
  letI : Algebra O S := (((algebraMap k R).comp O.subtype).codRestrict S fun c => (hOS _).2 c.2).toAlgebra
  have hji : ∀ c : O, S.subtype (algebraMap O S c) = algebraMap k R (O.subtype c) := fun _ => rfl
  let s : S ≃ₐ[O] S :=
    { toFun := fun r => ⟨σ r, hS _ r.2⟩
      invFun := fun r => ⟨σ.symm r, hinv _ r.2⟩
      left_inv := fun r => Subtype.ext (σ.symm_apply_apply _)
      right_inv := fun r => Subtype.ext (σ.apply_symm_apply _)
      map_mul' := fun r r' => Subtype.ext (map_mul σ _ _)
      map_add' := fun r r' => Subtype.ext (map_add σ _ _)
      commutes' := fun c => Subtype.ext (σ.commutes _) }
  have hjs : ∀ r, S.subtype (s r) = σ (S.subtype r) := fun _ => rfl
  have hjp : ∀ (m : ℕ) r, S.subtype ((s ^ m) r) = (σ ^ m) (S.subtype r) := by
    intro m r
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, hjs, ih]
  have hj := S.subtype_injective
  have hsG : IsGal s q := by
    obtain ⟨m, x, y, hm, hxy⟩ := hsep
    refine ⟨hσ.pos, AlgEquiv.ext fun r => hj (by rw [hjp, hσ.pow]; rfl),
      fun c c' h => Subtype.ext (hσ.inj (congrArg S.subtype h)), fun r hr => ?_,
      m, fun i => ⟨x i, (hm i).1⟩, fun i => ⟨y i, (hm i).2⟩, fun j hj' => hj ?_⟩
    · obtain ⟨c, hc⟩ := hσ.fix r (congrArg S.subtype hr)
      exact ⟨⟨c, (hOS c).1 (hc ▸ r.2)⟩, Subtype.ext hc⟩
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [map_sum, map_mul, hjp]
        refine (hxy j hj').trans ?_
        split_ifs <;> simp
  obtain ⟨a, rfl⟩ := (intGL_iff S a).1 ha
  obtain ⟨γ, rfl⟩ := (intGL_iff O γ).1 hγ
  have hcp : cp (Matrix.GeneralLinearGroup.map O.subtype γ) = (cp γ).map O.subtype := by
    unfold cp
    rw [← Matrix.charpoly_map]
    rfl
  obtain ⟨u, w, hu, hw, huw⟩ := hs
  have hsep0 : (cp γ).Separable := by
    obtain ⟨u, rfl⟩ := (mem_lifts _).1 hu
    obtain ⟨w, rfl⟩ := (mem_lifts _).1 hw
    refine ⟨u, w, map_injective _ O.subtype_injective ?_⟩
    rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, ← derivative_map, ← hcp, huw, Polynomial.map_one]
  have hsg : ∀ (m : ℕ) (g : GL (Fin n) S), Matrix.GeneralLinearGroup.map S.subtype (sg (s ^ m) g) =
      sg (σ ^ m) (Matrix.GeneralLinearGroup.map S.subtype g) := fun m g => by
    ext a b
    exact hjp m _
  have hN0 : nm s q a = up S γ := by
    have h1 : Matrix.GeneralLinearGroup.map S.subtype (nm s q a) = Matrix.GeneralLinearGroup.map S.subtype (up S γ) := by
      refine Eq.trans ?_ (hN.trans (by ext; rfl))
      unfold nm
      rw [map_list_prod, List.map_map]
      congr 1
      exact List.map_congr_left fun m _ => hsg m a
    ext b c
    exact congrArg (fun g : GL (Fin n) R => g b c) h1
  constructor
  · intro h
    obtain ⟨a', ha'⟩ := (intGL_iff S _).1 h
    obtain ⟨t, u, ht, hx⟩ := nmInt O S k R O.subtype S.subtype s σ q hsG hσ hj hjs hji n a a' γ hsep0 hN0 x ha'.symm
    exact ⟨t, ht, _, (intGL_iff S _).2 ⟨u, rfl⟩, hx⟩
  · rintro ⟨t, ht, y, hy, rfl⟩
    obtain ⟨y, rfl⟩ := (intGL_iff S y).1 hy
    have h1 := (nmCent k R σ q hσ n _ _ ⟨u, w, huw⟩ hN (up R t)).2 ⟨t, ht, rfl⟩
    refine (intGL_iff S _).2 ⟨sgConj s y a, ?_⟩
    have h2 := hsg 1 y
    rw [pow_one, pow_one] at h2
    rw [sgConj] at h1
    rw [sgConj, sgConj, map_mul, map_mul, map_inv, h2, map_mul, mul_inv_rev]
    conv_lhs => rw [← h1]
    group

end Abstract

section Concrete

open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open PositivityTheory.Rg.Tf.Loc ValuativeRel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem mem_O {w : HeightOneSpectrum (𝓞 E)} (x : w.adicCompletion E) :
    x ∈ 𝒪[w.adicCompletion E] ↔ Valued.v x ≤ 1 := by
  have h : valuation (w.adicCompletion E) x ≤ valuation (w.adicCompletion E) 1 ↔
      Valued.v x ≤ Valued.v (1 : w.adicCompletion E) := by
    rw [← Valuation.Compatible.vle_iff_le]
    exact Iff.rfl
  change valuation _ x ≤ 1 ↔ _
  simpa using h

omit [NumberField F] in
private theorem galHom_mem (σ : E ≃ₐ[F] E) (w w' : HeightOneSpectrum (𝓞 E)) (h : w' = σ • w)
    (y : w.adicCompletion E) (hy : y ∈ 𝒪[w.adicCompletion E]) : galHom σ w w' h y ∈ 𝒪[w'.adicCompletion E] := by
  have h1 : ‖galHom σ w w' h y‖ = ‖y‖ := by
    have := (HeightOneSpectrum.denseRange_algebraMap E w).equalizer
      (continuous_norm.comp (continuous_galHom σ w w' h)) continuous_norm
      (funext fun x ↦ by
        subst h
        simp only [Function.comp_apply, galHom_algebraMap, norm_algebraMap_smul])
    exact congrFun this y
  rw [mem_O, ← Valued.toNormedField.norm_le_one_iff] at hy ⊢
  exact h1.trans_le hy


variable (E) in
private noncomputable def intOver (v : HeightOneSpectrum (𝓞 F)) : Subring (CompletionsOver E v) :=
  ⨅ w : PlacesOver E v, (𝒪[w.1.adicCompletion E]).comap
    (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)

private theorem mem_intOver {v : HeightOneSpectrum (𝓞 F)} (y : CompletionsOver E v) :
    y ∈ intOver E v ↔ ∀ w, y w ∈ 𝒪[w.1.adicCompletion E] := by
  simp [intOver, Subring.mem_iInf]

private theorem mem_unitSet {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} (g : GL (Fin n) (CompletionsOver E v)) :
    g ∈ unitSet E n v ↔ IntGL (intOver E v) g := by
  simp only [unitSet, Set.mem_setOf_eq, GLnLocal.mem_integralGL_iff, IntGL, mem_intOver, ← map_inv]
  exact ⟨fun h => ⟨fun i j w => (h w).1 i j, fun i j w => (h w).2 i j⟩,
    fun h w => ⟨fun i j => h.1 i j w, fun i j => h.2 i j w⟩⟩

private noncomputable def sigLoc (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    CompletionsOver E v ≃ₐ[v.adicCompletion F] CompletionsOver E v :=
  (tensorEquiv E v).symm.trans ((ext (v.adicCompletion F) σ).trans (tensorEquiv E v))

private theorem sigLoc_eq_piGal (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (y : CompletionsOver E v) :
    sigLoc σ v y = piGal v σ y := by
  obtain ⟨x, rfl⟩ := (tensorEquiv E v).surjective y
  rw [← tensorEquiv_map_gal, sigLoc, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  rfl

private theorem sigLoc_algebraMap (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    sigLoc σ v (algebraMap E _ x) = algebraMap E _ (σ x) := by
  rw [← tensorEquiv_one_tmul, ← tensorEquiv_one_tmul, sigLoc, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  rfl

private theorem sigLoc_pow (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) (x : E) :
    (sigLoc σ v ^ m) (algebraMap E _ x) = algebraMap E _ ((σ ^ m) x) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih, sigLoc_algebraMap]

private theorem galFin_eq (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    galFin σ v = (sigLoc σ v : CompletionsOver E v →+* CompletionsOver E v) := by
  refine RingHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (tensorEquiv' E v).surjective y
  have h : galFin σ v (tensorEquiv' E v x) =
      tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F _) x) := by
    simp [galFin, galOf]
  rw [h]
  clear h
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, tensorEquiv'_tmul, tensorEquiv'_tmul, map_mul]
    congr 1
    · exact (sigLoc_algebraMap σ v a).symm
    · exact ((sigLoc σ v).commutes b).symm
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]

private theorem ev_elt (t : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    algebraMap F (v.adicCompletion F) t ∈ 𝒪[v.adicCompletion F] := by
  refine (HeightOneSpectrum.Support.finite (𝓞 F) t).subset fun v hv => ?_
  by_contra h
  refine hv ((mem_O _).2 ?_)
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t).trans_le (not_lt.1 h)

private theorem ev_poly (p : F[X]) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    p.map (algebraMap F (v.adicCompletion F)) ∈ lifts (𝒪[v.adicCompletion F]).subtype := by
  filter_upwards [(Filter.eventually_all_finset p.support).2 fun i _ => ev_elt (p.coeff i)] with v hv
  rw [lifts_iff_coeff_lifts]
  intro i
  rw [coeff_map]
  by_cases hi : i ∈ p.support
  · exact ⟨⟨_, hv i hi⟩, rfl⟩
  · rw [notMem_support_iff.1 hi]
    exact ⟨0, by simp⟩

private theorem ev_over (t : E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    algebraMap E (CompletionsOver E v) t ∈ intOver E v := by
  refine ((Filter.eventually_cofinite.1 (ev_elt t)).image (below F)).subset fun v hv => ?_
  rw [Set.mem_compl_iff, Set.mem_setOf_eq, mem_intOver, not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w.1, hw, (below_eq_iff _ _).2 w.2⟩

private theorem alg_mem {v : HeightOneSpectrum (𝓞 F)}
    (hinj : Function.Injective (algebraMap (v.adicCompletion F) (CompletionsOver E v))) (c : v.adicCompletion F) :
    algebraMap _ (CompletionsOver E v) c ∈ intOver E v ↔ c ∈ 𝒪[v.adicCompletion F] := by
  have hv : ∀ w : PlacesOver E v, algebraMap _ (CompletionsOver E v) c w ∈ 𝒪[w.1.adicCompletion E] ↔
      c ∈ 𝒪[v.adicCompletion F] := fun w => by
    rw [mem_O, mem_O, Pi.algebraMap_apply, algebraMap_completion_eq, valued_completionMap,
      pow_le_one_iff (Ideal.ramificationIdx_pos (R := 𝓞 F) w.1.asIdeal).ne']
  rw [mem_intOver]
  refine ⟨fun h => ?_, fun h w => (hv w).2 h⟩
  rcases isEmpty_or_nonempty (PlacesOver E v) with h0 | ⟨⟨w⟩⟩
  · exact absurd (hinj (Subsingleton.elim _ _)) (zero_ne_one (α := v.adicCompletion F))
  · exact (hv w).1 (h w)

private theorem sigLoc_mem (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    ∀ r ∈ intOver E v, sigLoc σ v r ∈ intOver E v := by
  intro r hr
  rw [mem_intOver] at hr ⊢
  intro w
  rw [sigLoc_eq_piGal, piGal_apply, galEquiv_apply]
  exact galHom_mem _ _ _ _ _ (hr _)

private theorem nm_loc (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (δ : GL (Fin n) E) (γ : GL (Fin n) F)
    (hN : normGL σ δ = incl γ) :
    nm (sigLoc σ v) (Module.finrank F E) (mapGL n (algebraMap E (CompletionsOver E v)) δ) =
      up (CompletionsOver E v) (mapGL n (algebraMap F (v.adicCompletion F)) γ) := by
  have h := congrArg (mapGL n (algebraMap E (CompletionsOver E v))) hN
  rw [normGL, twNorm, map_list_prod, List.map_map] at h
  refine Eq.trans ?_ (h.trans ?_)
  · unfold nm
    refine congrArg List.prod (List.map_congr_left fun m _ => ?_)
    rw [Function.comp_apply, ← sigmaGL_pow]
    refine Units.ext (Matrix.ext fun a b => ?_)
    exact sigLoc_pow σ v m _
  · refine Units.ext (Matrix.ext fun a b => ?_)
    exact (IsScalarTower.algebraMap_apply F E (CompletionsOver E v) _).symm.trans
      (IsScalarTower.algebraMap_apply F (v.adicCompletion F) (CompletionsOver E v) _)

private theorem cp_map {S R : Type} [CommRing S] [CommRing R] {n : ℕ} (j : S →+* R) (g : GL (Fin n) S) :
    cp (mapGL n j g) = (g : Matrix (Fin n) (Fin n) S).charpoly.map j := by
  unfold cp
  rw [← Matrix.charpoly_map]
  rfl

private theorem intGL_map {S R : Type} [CommRing S] [CommRing R] {n : ℕ} (j : S →+* R) (T : Subring R)
    (g : GL (Fin n) S) (h : ∀ a b, j (g a b) ∈ T) (h' : ∀ a b, j ((g⁻¹ : GL (Fin n) S) a b) ∈ T) :
    IntGL T (mapGL n j g) :=
  ⟨h, by rw [← map_inv]; exact h'⟩

end Concrete

end UpperTheory.ConvolutionTheory.G

open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic GroundTheory.Automorphic.Reduction PositivityTheory.Rg.Tf.Loc ValuativeRel in
theorem UpperTheory.ConvolutionTheory.G.firstCohomologyBound_of_boundaryBound :
    K1 := by
  intro F E _ _ _ _ _ _ σ hgen n _ δ γ hγ hN
  have hG := galField F E σ hgen
  obtain ⟨s, x, y, hxy⟩ := hG.sep
  obtain ⟨u, w, huw⟩ := hγ
  filter_upwards [Filter.eventually_all.2 fun i => ev_over (F := F) (x i),
    Filter.eventually_all.2 fun i => ev_over (F := F) (y i),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_over (F := F) (δ i j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_over (F := F) ((δ⁻¹ : GL (Fin n) E) i j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_elt (γ i j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_elt ((γ⁻¹ : GL (Fin n) F) i j),
    ev_poly u, ev_poly w] with v hx hy hδ hδ' hγ hγ' hu hw z
  have hσ : IsGal (sigLoc σ v) (Module.finrank F E) :=
    isGal_equiv (tensorEquiv E v) (galExt F E _ σ _ hG)
  have e1 : mapGL n (atFin v) (AdelicGLn.diagonal E n δ) = mapGL n (algebraMap E (CompletionsOver E v)) δ :=
    Units.ext (Matrix.ext fun _ _ => rfl)
  have e2 : finAt v (AdelicGLn.diagonal F n γ) = mapGL n (algebraMap F (v.adicCompletion F)) γ :=
    Units.ext (Matrix.ext fun _ _ => rfl)
  have e3 : mapGL n (galFin σ v) = sg (sigLoc σ v) := by rw [galFin_eq, sg]
  have e4 : mapGL n (incFin E v) = up (k := v.adicCompletion F) (CompletionsOver E v) := by
    rw [up]
    exact congrArg (mapGL n) (RingHom.ext fun _ => rfl)
  have key := abstract_hilbert90 (sigLoc σ v) _ hσ 𝒪[v.adicCompletion F] (intOver E v) (alg_mem hσ.inj) (sigLoc_mem σ v)
    ⟨s, fun i => algebraMap E _ (x i), fun i => algebraMap E _ (y i), fun i => ⟨hx i, hy i⟩, fun j hj => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [sigLoc_pow, ← map_mul, ← map_sum, hxy j hj]
      split_ifs <;> simp⟩ _ _
    (intGL_map _ _ δ hδ hδ') (intGL_map _ _ γ hγ hγ') ⟨_, _, hu, hw, by
      rw [cp_map, derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add (f := _), huw,
        Polynomial.map_one]⟩ (nm_loc σ v δ γ hN) z
  rw [sgConj] at key
  rw [e1, e2, e3, e4]
  simp only [mem_unitSet]
  exact key
