module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDiag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsTorusLiftToNilpotentThickening
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DualCr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineTriangularIffMemFiniteCocyclesOfCha

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ConjugateRestrictionOpenNormal
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem isCr_comp {l : ℕ} [Fact l.Prime] {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A]
    [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l) (c : G →* G)
    (hc : Function.Surjective c) (ρ : Representation A G V) :
    IsCr (φ.comp c) (ρ.comp c : Representation A G V) ↔ IsCr φ ρ := by
  have hr : (φ.comp c).range = φ.range := by
    ext σ
    refine ⟨fun ⟨g, hg⟩ => ⟨c g, hg⟩, fun ⟨g, hg⟩ => ?_⟩
    obtain ⟨g, rfl⟩ := hc g
    exact ⟨g, hg⟩
  have hd : Dcr (φ.comp c) (resCoef ℚ_[l] (ρ.comp c : Representation A G V)) = Dcr φ (resCoef ℚ_[l] ρ) := by
    unfold Dcr
    exact hc.iInf_comp (fun g => LinearMap.ker (actC φ (resCoef ℚ_[l] ρ) g - LinearMap.id))
  unfold IsCr
  rw [hr, hd]

private theorem conj_left {B : Type} [CommRing B] (w : GG (m := 3) (R := B)) (x y : GL (Fin 3) B)
    (h : GG.ofGL y = w * GG.ofGL x * w⁻¹) : y = w.left * sgnAct 3 B w.right x * w.left⁻¹ := by
  have := congrArg SemidirectProduct.left h
  have e : sgnAct 3 B w.right (sgnAct 3 B w.right w.left) = w.left := by
    rw [← MulAut.mul_apply, ← map_mul, Int.units_mul_self, map_one, MulAut.one_apply]
  simpa [e] using this

private theorem dot_inv {B : Type} [CommRing B] (a m : GL (Fin 3) B) (u x : Fin 3 → B) :
    dotProduct ((Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)).mulVec
      (((a * theta m * a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B).mulVec u))
      ((m : Matrix (Fin 3) (Fin 3) B).mulVec x) =
    dotProduct ((Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)).mulVec u) x := by
  have e : Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) *
      ((a * theta m * a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) =
      ((m⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B).transpose *
        (Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)) := by
    rw [Matrix.mul_assoc, ← Units.val_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, Units.val_mul,
      theta_val]
    simp only [← Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec x, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem UpperTheory.conjugate_restriction_open_normal :
    ∀ {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (H : Subgroup (GQ l)) [H.Normal], IsOpen (H : Set (GQ l)) → ∀ (ρ ρ' : ↥H →* GL (Fin 3) B), Continuous (fun g => (ρ g : Matrix (Fin 3) (Fin 3) B)) → ∀ (s : GQ l) (w : GG (m := 3) (R := B)), (∀ g g' : H, (g' : GQ l) = s⁻¹ * g * s → GG.ofGL (ρ' g) = w * GG.ofGL (ρ g') * w⁻¹) → IsCr H.subtype (colRep ρ) → IsCr H.subtype (colRep ρ') := by
  intro l _ B _ _ _ _ _ _ H hN hH ρ ρ' hρ s w hw hcr
  have hψ : IsOpenEmbedding H.subtype := hH.isOpenEmbedding_subtypeVal
  let c : H →* H := (MulAut.conjNormal (H := H) s⁻¹).toMonoidHom
  have hc : ∀ g : H, (c g : GQ l) = s⁻¹ * g * s := fun g => by
    change ((MulAut.conjNormal (H := H) s⁻¹ g : H) : GQ l) = _
    rw [MulAut.conjNormal_apply, inv_inv]
  have hcc : Continuous c := by
    refine continuous_induced_rng.2 ?_
    have : Subtype.val ∘ c = fun g : H => s⁻¹ * (g : GQ l) * s := funext hc
    rw [this]
    fun_prop
  let σ : H →* GL (Fin 3) B := ρ.comp c
  have hσ : Continuous (fun g => (σ g : Matrix (Fin 3) (Fin 3) B)) := hρ.comp hcc
  have hσi : Continuous (fun g => (((σ g)⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)) := by
    simp only [← map_inv]
    exact hσ.comp continuous_inv
  have hσcr : IsCr H.subtype (colRep σ) := by
    have h1 := (isCr_comp H.subtype c (MulAut.conjNormal (H := H) s⁻¹).surjective (colRep ρ)).2 hcr
    have h2 : H.subtype.comp c = (MulAut.conj s⁻¹).toMonoidHom.comp H.subtype := by
      refine MonoidHom.ext fun g => ?_
      change (c g : GQ l) = s⁻¹ * g * s⁻¹⁻¹
      rw [hc, inv_inv]
    rw [h2] at h1
    exact (admissible_conjugate H.subtype hψ (colRep σ) s⁻¹).1.1 h1
  have he : ∀ g, ρ' g = w.left * sgnAct 3 B w.right (σ g) * w.left⁻¹ := fun g =>
    conj_left w _ _ (hw g (c g) (hc g))
  generalize w.left = a at he
  rcases Int.units_eq_one_or w.right with h | h
  · simp only [h, sgnAct_one] at he
    have hρ' : Continuous (fun g => (ρ' g : Matrix (Fin 3) (Fin 3) B)) := by
      simp only [he, Units.val_mul]
      exact (continuous_const.matrix_mul hσ).matrix_mul continuous_const
    refine ((isCrys_isDR_sub_quot H.subtype hψ (colRep σ) (colRep ρ') (contAction_colRep hσ) (contAction_colRep hρ')
      ((Matrix.toLin' (a : Matrix (Fin 3) (Fin 3) B)).restrictScalars ℚ_[l]) (fun g x => ?_)).2
      (fun v => ?_)).1 hσcr
    · simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply, colRep_apply, Matrix.mulVec_mulVec, he,
        ← Units.val_mul, inv_mul_cancel_right]
    · refine ⟨((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B).mulVec v, ?_⟩
      simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  · simp only [h, sgnAct_neg_one] at he
    have hρ' : Continuous (fun g => (ρ' g : Matrix (Fin 3) (Fin 3) B)) := by
      simp only [he, Units.val_mul, theta_val]
      exact (continuous_const.matrix_mul ((continuous_const.matrix_mul hσi.matrix_transpose).matrix_mul
        continuous_const)).matrix_mul continuous_const
    have c1 : ContAction (chRep (1 : H →* Bˣ)) := contAction_chRep continuous_const
    have cr1 : IsCr H.subtype (chRep (1 : H →* Bˣ)) :=
      crUnr (A := ℚ_[l]) H.subtype hψ (resCoef ℚ_[l] (chRep (1 : H →* Bˣ))) c1 0
        (fun g _ x => by simp [resCoef, chRep])
    let N : Matrix (Fin 3) (Fin 3) B := Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)
    refine (isCrys_isDR_internalHom H.subtype hψ (colRep σ) (chRep (1 : H →* Bˣ)) (colRep ρ') (contAction_colRep hσ) c1
      (contAction_colRep hρ')
      (LinearMap.mk₂ ℚ_[l] (fun (u x : Fin 3 → B) => dotProduct (N.mulVec u) x)
        (fun _ _ _ => by rw [Matrix.mulVec_add, add_dotProduct])
        (fun _ _ _ => by rw [Matrix.mulVec_smul, smul_dotProduct])
        (fun _ _ _ => dotProduct_add _ _ _) (fun _ _ _ => dotProduct_smul _ _ _))
      (fun g u x => ?_) (fun u u' huu => ?_)).1 hσcr cr1
    · simp only [LinearMap.mk₂_apply, colRep_apply, chRep_apply, MonoidHom.one_apply, Units.val_one, one_mul]
      rw [he]
      exact dot_inv a (σ g) u x
    · have h1 : N.mulVec u = N.mulVec u' := by
        funext i
        have := LinearMap.congr_fun huu (Pi.single i 1)
        simpa only [LinearMap.mk₂_apply, dotProduct_single, mul_one] using this
      have h2 : ((a : Matrix (Fin 3) (Fin 3) B) * Jmat B 3) * N = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Jmat B 3), Jmat_mul_Jmat, Matrix.one_mul, Units.mul_inv]
      have h3 := congrArg ((a : Matrix (Fin 3) (Fin 3) B) * Jmat B 3).mulVec h1
      simpa only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] using h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCocycleExtensionOfConjugationInvariantRest
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem zm_mem {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    (g • q).out⁻¹ * (g * q.out) ∈ H := by
  rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rfl

private noncomputable def zm_h {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) : H :=
  ⟨(g • q).out⁻¹ * (g * q.out), zm_mem H g q⟩

private theorem zm_h_mul {G : Type} [Group G] (H : Subgroup G) (g g' : G) (q : G ⧸ H) :
    zm_h H (g * g') q = zm_h H g (g' • q) * zm_h H g' q := by
  apply Subtype.ext
  simp only [zm_h, Subgroup.coe_mul, mul_smul]
  group

private theorem zm_out {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    (g • q).out * (zm_h H g q : G) = g * q.out := by
  simp only [zm_h]
  group

private theorem zm_fix {G : Type} [Group G] (H : Subgroup G) [hN : H.Normal] (h : H) (q : G ⧸ H) :
    (h : G) • q = q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, eq_comm, QuotientGroup.eq]
    have := hN.conj_mem _ h.2 x⁻¹
    simpa [mul_assoc] using this

private theorem zm_sum {G : Type} [Group G] (H : Subgroup G) [Fintype (G ⧸ H)] {V : Type} [AddCommGroup V]
    (g : G) (f : G ⧸ H → V) : ∑ q, f (g • q) = ∑ q, f q :=
  Equiv.sum_comp (MulAction.toPerm g) f

private theorem zm_cont {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (q : G ⧸ H) : Continuous fun g : G => (g • q).out := by
  haveI : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  have h1 : Continuous fun g : G => g • q := by fun_prop
  exact (continuous_of_discreteTopology (f := fun x : G ⧸ H => x.out)).comp h1

theorem UpperTheory.exists_cocycle_extension_of_conjugation_invariant_restriction :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V), ContAction ρ → ∀ (H : Subgroup G) [H.Normal] [H.FiniteIndex], IsOpen (H : Set G) → ∀ (N : Submodule A (H → V)), ∀ c ∈ Z1 (ρ.comp H.subtype : Representation A H V), (∀ (s : G) (c' : H → V), (∀ g g' : H, (g' : G) = s⁻¹ * g * s → c' g = ρ s (c g')) → c' - c ∈ N) → ∃ b ∈ Z1 ρ, (fun g : H => b g) - c ∈ N := by
  intro l _ G _ _ _ A _ _ V _ _ _ _ _ _ _ _ _ ρ hρ H hHN _ hH N c hc hs
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set n : ℕ := Fintype.card (G ⧸ H) with hn
  have hn0 : (n : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  obtain ⟨a, ha⟩ : ∃ a : A, ∀ x : V, a • (n • x) = x :=
    ⟨algebraMap ℚ_[l] A (n : ℚ_[l])⁻¹, fun x => by
      rw [algebraMap_smul, ← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, inv_mul_cancel₀ hn0, one_smul]⟩
  have hmul : ∀ g g' x, ρ g (ρ g' x) = ρ (g * g') x := fun g g' x => by
    rw [map_mul, Module.End.mul_apply]
  rw [mem_Z1_iff_cocycle] at hc
  have hc2 : ∀ h h' : H, c (h * h') = c h + ρ h (c h') := hc.2
  let cor : G → V := fun g => ∑ q : G ⧸ H, ρ (g • q).out (c (zm_h H g q))
  have hcor : cor ∈ Z1 ρ := by
    refine ⟨continuous_finsetSum _ fun q _ => ?_, fun g g' => ?_⟩
    · have h1 := zm_cont H hH q
      have h2 : Continuous fun g : G => zm_h H g q :=
        Continuous.subtype_mk (h1.inv.mul (continuous_id.mul continuous_const)) _
      exact hρ.comp (h1.prodMk (hc.1.comp h2))
    · simp only [cor]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← zm_sum H g' (fun q => ρ (g • q).out (c (zm_h H g q))), map_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [zm_h_mul, hc2, map_add (f := _), hmul, hmul, mul_smul, zm_out]
  let c' : G ⧸ H → H → V := fun q h => ρ q.out (c (zm_h H h q))
  have hc' : ∀ q, c' q - c ∈ N := fun q => hs q.out (c' q) fun g g' hg => by
    have : zm_h H g q = g' := by
      apply Subtype.ext
      simp only [zm_h, zm_fix, hg, mul_assoc]
    simp only [c', this]
  refine ⟨a • cor, (Z1 ρ).smul_mem a hcor, ?_⟩
  have e : (fun g : H => (a • cor) g) - c = a • ∑ q : G ⧸ H, (c' q - c) := by
    funext h
    have e1 : cor h = ∑ q : G ⧸ H, c' q h := by
      simp only [cor, c', zm_fix]
    simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, e1, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, ← hn, smul_sub, ha]
  rw [e]
  exact N.smul_mem a (N.sum_mem fun q _ => hc' q)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUnipotentFromTorusCoords
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private def triGL {B : Type} [CommRing B] (t : Fin 3 → Bˣ) (x y z : B) : GL (Fin 3) B where
  val := triM t x y z
  inv := !![((t 0)⁻¹ : Bˣ), -x * ((t 0)⁻¹ : Bˣ), (x * y - z) * ((t 0)⁻¹ : Bˣ);
    0, ((t 1)⁻¹ : Bˣ), -y * ((t 1)⁻¹ : Bˣ); 0, 0, ((t 2)⁻¹ : Bˣ)]
  val_inv := by
    have h0 := (t 0).mul_inv
    have h1 := (t 1).mul_inv
    have h2 := (t 2).mul_inv
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, Matrix.mul_apply, Fin.sum_univ_three, -Units.mul_inv, -Units.inv_mul] <;>
      first
        | assumption
        | linear_combination (-x) * h0
        | linear_combination (x * y - z) * h0 - x * y * h1
        | linear_combination (-y) * h1
  inv_val := by
    have h0 := (t 0).inv_mul
    have h1 := (t 1).inv_mul
    have h2 := (t 2).inv_mul
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, Matrix.mul_apply, Fin.sum_univ_three, -Units.mul_inv, -Units.inv_mul] <;>
      first
        | assumption
        | ring

private theorem triGL_val {B : Type} [CommRing B] (t : Fin 3 → Bˣ) (x y z : B) :
    (triGL t x y z : Matrix (Fin 3) (Fin 3) B) = triM t x y z := rfl

private theorem triGL_congr {B : Type} [CommRing B] {t s : Fin 3 → Bˣ} {x y z x' y' z' : B}
    (ht : t = s) (hx : x = x') (hy : y = y') (hz : z = z') : triGL t x y z = triGL s x' y' z' := by
  subst ht hx hy hz
  rfl

private theorem theta_triGL {B : Type} [CommRing B] (t : Fin 3 → Bˣ) (x y z : B) :
    theta (triGL t x y z) = triGL (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) := by
  apply Units.ext
  rw [theta_val, triGL_val]
  have hinv : ((triGL t x y z)⁻¹ : GL (Fin 3) B).val =
      !![(((t 0)⁻¹ : Bˣ) : B), -x * (((t 0)⁻¹ : Bˣ) : B), (x * y - z) * (((t 0)⁻¹ : Bˣ) : B);
        0, (((t 1)⁻¹ : Bˣ) : B), -y * (((t 1)⁻¹ : Bˣ) : B); 0, 0, (((t 2)⁻¹ : Bˣ) : B)] := rfl
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jmat, triM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Fin.rev] <;> ring

private theorem triGL_mul {B : Type} [CommRing B] (t s : Fin 3 → Bˣ) (x y z x' y' z' : B) :
    triGL t x y z * triGL s x' y' z' = triGL (fun i => t i * s i)
      (x + ((t 0 / t 1 : Bˣ) : B) * x') (y + ((t 1 / t 2 : Bˣ) : B) * y')
      (z + ((t 0 / t 2 : Bˣ) : B) * z' + x * (((t 1 / t 2 : Bˣ) : B) * y')) := by
  apply Units.ext
  rw [Units.val_mul, triGL_val, triGL_val, triGL_val]
  have h1 := (t 1).inv_mul
  have h2 := (t 2).inv_mul
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, triM, div_eq_mul_inv, -Units.mul_inv, -Units.inv_mul] <;>
    first
      | linear_combination (-((t 0 : B) * x' * s 1)) * h1
      | linear_combination (-((t 1 : B) * y' * s 2)) * h2
      | linear_combination (-((t 0 : B) * z' * s 2 + x * t 1 * y' * s 2)) * h2

theorem UpperTheory.exists_unipotent_from_torus_coords :
    ∀ {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} (T : Tor η B) (h : B), 2 * h = 1 →
      ∀ (β : G → B × B) (γ : G → B), (∀ g g', β (g * g') = β g + T.M1 g (β g')) →
        T.IsGam h β γ → ∃ u : G →* GG (m := 3) (R := B), T.Coord h β γ u := by
  intro G B _ _ η T h hh β γ hβ hγ
  let F : G → GG (m := 3) (R := B) := fun g =>
    ⟨triGL (T.t g) (β g).1 (β g).2 (γ g + h * (β g).1 * (β g).2), η g⟩
  have hmul : ∀ g g' : G, F (g * g') = F g * F g' := by
    intro g g'
    have hab : (((T.t g 0 / T.t g 2 : Bˣ)) : B) =
        ((T.t g 0 / T.t g 1 : Bˣ) : B) * ((T.t g 1 / T.t g 2 : Bˣ) : B) := by
      rw [← Units.val_mul, div_mul_div_cancel]
    have hb := hβ g g'
    have hc := hγ g g'
    apply SemidirectProduct.ext
    · simp only [F, SemidirectProduct.mul_left]
      rcases Int.units_eq_one_or (η g) with he | he
      · rw [he, sgnAct_one, triGL_mul]
        rw [Tor.adjointSuperdiagRep_apply, if_pos he] at hb
        rw [Tor.adjointSuperdiagRep_apply, if_pos he, Tor.χ2_apply, he] at hc
        apply triGL_congr
        · funext i
          rw [T.mul, if_pos he]
        · rw [hb]; rfl
        · rw [hb]; rfl
        · rw [hc, hb, hab]
          simp only [omg, Prod.fst_add, Prod.snd_add, Units.val_one, Int.cast_one, one_mul]
          linear_combination ((β g).1 * ((T.t g 1 / T.t g 2 : Bˣ) : B) * (β g').2) * hh
      · have hne : η g ≠ 1 := by rw [he]; decide
        rw [he, sgnAct_neg_one, theta_triGL, triGL_mul]
        rw [Tor.adjointSuperdiagRep_apply, if_neg hne] at hb
        rw [Tor.adjointSuperdiagRep_apply, if_neg hne, Tor.χ2_apply, he] at hc
        apply triGL_congr
        · funext i
          rw [T.mul, if_neg hne]
        · rw [hb]
          simp only [Prod.fst_add]
          ring
        · rw [hb]
          simp only [Prod.snd_add]
          ring
        · rw [hc, hb, hab]
          simp only [omg, Prod.fst_add, Prod.snd_add, Units.val_neg, Units.val_one, Int.cast_neg,
            Int.cast_one]
          linear_combination (((T.t g 0 / T.t g 1 : Bˣ) : B) * ((T.t g 1 / T.t g 2 : Bˣ) : B) *
            (β g').1 * (β g').2 - ((T.t g 1 / T.t g 2 : Bˣ) : B) * (β g).1 * (β g').1) * hh
    · simp only [F, SemidirectProduct.mul_right, map_mul]
  refine ⟨MonoidHom.mk' F hmul, ?_⟩
  exact Tor.Coord.mk (fun g => rfl) (fun g => rfl)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsTorusCoordsOfUnipotent
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

section

variable {B : Type} [CommRing B]

private theorem triM_mul (t s : Fin 3 → Bˣ) (x y z x' y' z' : B) :
    triM t x y z * triM s x' y' z' =
      triM (fun i => t i * s i) (x + ((t 0 / t 1 : Bˣ) : B) * x') (y + ((t 1 / t 2 : Bˣ) : B) * y')
        (z + x * (((t 1 / t 2 : Bˣ) : B) * y') + ((t 0 / t 2 : Bˣ) : B) * z') := by
  have h1 := Units.inv_mul (t 1)
  have h2 := Units.inv_mul (t 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triM, Matrix.mul_apply, Fin.sum_univ_three, div_eq_mul_inv] <;>
    first
    | ring1
    | linear_combination (-((t 0 : B) * x' * (s 1 : B))) * h1
    | linear_combination (-((t 0 : B) * z' * (s 2 : B)) - (s 2 : B) * x * (t 1 : B) * y') * h2
    | linear_combination (-((t 1 : B) * y' * (s 2 : B))) * h2

private theorem triM_inj {t s : Fin 3 → Bˣ} {x y z x' y' z' : B} (h : triM t x y z = triM s x' y' z') :
    t = s ∧ x = x' ∧ y = y' ∧ z = z' := by
  have e : ∀ i j, triM t x y z i j = triM s x' y' z' i j := fun i j => by rw [h]
  have a0 := e 0 0
  have a1 := e 1 1
  have a2 := e 2 2
  have b1 := e 0 1
  have b2 := e 1 2
  have b3 := e 0 2
  simp [triM] at a0 a1 a2 b1 b2 b3
  have ht : t = s := by
    funext i
    fin_cases i
    · exact Units.ext a0
    · exact Units.ext a1
    · exact Units.ext a2
  subst ht
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simpa using congrArg (· * ((t 1)⁻¹ : Bˣ).val) b1
  · simpa using congrArg (· * ((t 2)⁻¹ : Bˣ).val) b2
  · simpa using congrArg (· * ((t 2)⁻¹ : Bˣ).val) b3

private theorem theta_triM {A : GL (Fin 3) B} {t : Fin 3 → Bˣ} {x y z : B}
    (h : (A : Matrix (Fin 3) (Fin 3) B) = triM t x y z) :
    (theta A : Matrix (Fin 3) (Fin 3) B) = triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) := by
  have h1 := Units.inv_mul (t 1)
  have h2 := Units.inv_mul (t 2)
  have key : triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) * ((theta A)⁻¹ : GL (Fin 3) B) = 1 := by
    rw [theta_inv_val, h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [triM, Jmat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Fin.rev] <;>
      first
      | linear_combination y * h2
      | linear_combination z * h2 - x * y * h1
      | linear_combination x * h1
  calc (theta A : Matrix (Fin 3) (Fin 3) B)
      = 1 * (theta A : Matrix (Fin 3) (Fin 3) B) := (one_mul _).symm
    _ = triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) * ((theta A)⁻¹ : GL (Fin 3) B) *
          (theta A : Matrix (Fin 3) (Fin 3) B) := by rw [key]
    _ = triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) := by
      rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

private theorem exists_triM (A : GL (Fin 3) B)
    (h : ∀ a b, wt a b < 0 → (A : Matrix (Fin 3) (Fin 3) B) a b = 0) :
    ∃ (t : Fin 3 → Bˣ) (x y z : B), (A : Matrix (Fin 3) (Fin 3) B) = triM t x y z := by
  have z10 := h 1 0 (by decide)
  have z20 := h 2 0 (by decide)
  have z21 := h 2 1 (by decide)
  have hd : IsUnit (A : Matrix (Fin 3) (Fin 3) B).det := Matrix.isUnits_det_units A
  rw [Matrix.det_fin_three, z10, z20, z21] at hd
  simp only [mul_zero, zero_mul, sub_zero, add_zero, zero_sub, neg_zero, IsUnit.mul_iff] at hd
  obtain ⟨⟨h0, h1⟩, h2⟩ := hd
  refine ⟨![h0.unit, h1.unit, h2.unit], (A : Matrix (Fin 3) (Fin 3) B) 0 1 * ↑h1.unit⁻¹,
    (A : Matrix (Fin 3) (Fin 3) B) 1 2 * ↑h2.unit⁻¹, (A : Matrix (Fin 3) (Fin 3) B) 0 2 * ↑h2.unit⁻¹, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [triM, z10, z20, z21, mul_assoc]

end

theorem UpperTheory.exists_torus_coords_of_unipotent :
    ∀ {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} (h : B),
      2 * h = 1 → ∀ u : G →* GG (m := 3) (R := B), HasMult η u →
        (∀ g a b, wt a b < 0 → (u g).mat a b = 0) →
        ∃ (T : Tor η B) (β : G → B × B) (γ : G → B),
          T.Coord h β γ u ∧ (∀ g g', β (g * g') = β g + T.M1 g (β g')) ∧ T.IsGam h β γ := by
  intro G B _ _ η h h2 u hm hu
  have ex : ∀ g, ∃ (t : Fin 3 → Bˣ) (x y z : B), (u g).mat = triM t x y z :=
    fun g => exists_triM (u g).left (hu g)
  choose t x y z hA using ex
  have step : ∀ g g', ∃ (t' : Fin 3 → Bˣ) (x' y' z' : B),
      (u (g * g')).mat = triM (t g) (x g) (y g) (z g) * triM t' x' y' z' ∧
      ((η g = 1 ∧ t' = t g' ∧ x' = x g' ∧ y' = y g' ∧ z' = z g') ∨
       (η g = -1 ∧ t' = (fun i => (t g' i.rev)⁻¹) ∧ x' = -y g' ∧ y' = -x g' ∧ z' = x g' * y g' - z g')) := by
    intro g g'
    have hmul : (u (g * g')).mat = (u g).mat * (((sgnAct 3 B) (u g).right) (u g').left : Matrix (Fin 3) (Fin 3) B) := by
      rw [map_mul]
      show (((u g * u g').left : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) = _
      rw [SemidirectProduct.mul_left, Units.val_mul]
      rfl
    rw [hm g] at hmul
    rcases Int.units_eq_one_or (η g) with e | e
    · rw [e, sgnAct_one] at hmul
      exact ⟨_, _, _, _, by rw [hmul, hA g]; exact congrArg _ (hA g'), Or.inl ⟨e, rfl, rfl, rfl, rfl⟩⟩
    · rw [e, sgnAct_neg_one] at hmul
      exact ⟨_, _, _, _, by rw [hmul, hA g]; exact congrArg _ (theta_triM (hA g')), Or.inr ⟨e, rfl, rfl, rfl, rfl⟩⟩
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have hab : ∀ g, ((t g 0 / t g 1 : Bˣ) : B) * ((t g 1 / t g 2 : Bˣ) : B) = ((t g 0 / t g 2 : Bˣ) : B) := by
    intro g
    rw [← Units.val_mul, div_mul_div_cancel]
  refine ⟨⟨t, ?_⟩, fun g => (x g, y g), fun g => z g - h * x g * y g, ⟨hm, fun g => ?_⟩, ?_, ?_⟩
  · intro g g' i
    obtain ⟨t', x', y', z', he, hc⟩ := step g g'
    rw [triM_mul, hA (g * g')] at he
    obtain ⟨ht, -, -, -⟩ := triM_inj he
    rcases hc with ⟨e, rfl, -, -, -⟩ | ⟨e, rfl, -, -, -⟩
    · rw [ht]
      simp [e]
    · rw [ht]
      simp [e, hne]
  · rw [hA g]
    congr 1
    ring
  · intro g g'
    obtain ⟨t', x', y', z', he, hc⟩ := step g g'
    rw [triM_mul, hA (g * g')] at he
    obtain ⟨-, hx, hy, -⟩ := triM_inj he
    rcases hc with ⟨e, -, rfl, rfl, -⟩ | ⟨e, -, rfl, rfl, -⟩
    · ext <;> simp [Tor.adjointSuperdiagRep_apply, e, hx, hy]
    · ext <;> simp [Tor.adjointSuperdiagRep_apply, e, hne, hx, hy]
  · intro g g'
    obtain ⟨t', x', y', z', he, hc⟩ := step g g'
    rw [triM_mul, hA (g * g')] at he
    obtain ⟨-, hx, hy, hz⟩ := triM_inj he
    have hg := hab g
    simp only [Tor.χ2_apply, Tor.adjointSuperdiagRep_apply, omg]
    rcases hc with ⟨e, -, rfl, rfl, rfl⟩ | ⟨e, -, rfl, rfl, rfl⟩
    · simp only [e, if_true]
      rw [hx, hy, hz]
      push_cast
      linear_combination (-(x g * ((t g 1 / t g 2 : Bˣ) : B) * y g')) * h2 - (h * x g' * y g') * hg
    · simp only [e, hne, if_false]
      rw [hx, hy, hz]
      push_cast
      linear_combination (((t g 1 / t g 2 : Bˣ) : B) * x g * x g' - ((t g 0 / t g 2 : Bˣ) : B) * x g' * y g') * h2 - (h * x g' * y g') * hg
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemFiniteCocyclesIffRestrictSubgroupMem
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.mem_finiteCocycles_iff_restrict_subgroup_mem :
    ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (T : Tor η B), T.Good π Ψ → ∀ β ∈ Z1 T.M1, (β ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) T.M1 ↔ (fun g : H => (β g).1) ∈ UpperTheory.V.Loc.finiteCocycles H.subtype (chRep (T.ch H hD.ηH 0 / T.ch H hD.ηH 1)) ∧ (fun g : H => (β g).2) ∈ UpperTheory.V.Loc.finiteCocycles H.subtype (chRep (T.ch H hD.ηH 1 / T.ch H hD.ηH 2))) := by
  intro l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ T hT β hβ
  haveI := hD.normal
  haveI := hD.fin
  have hM : ∀ (g : H) (v : B × B), (T.M1.comp H.subtype : Representation B H (B × B)) g v =
      (chRep (T.ch H hD.ηH 0 / T.ch H hD.ηH 1) g v.1, chRep (T.ch H hD.ηH 1 / T.ch H hD.ηH 2) g v.2) := by
    intro g v
    change T.M1 g v = _
    rw [Tor.adjointSuperdiagRep_apply, if_pos (hD.ηH g g.2)]
    rfl
  rw [z1fDesc (MonoidHom.id (GQ l)) T.M1 H β hβ, MonoidHom.id_comp]
  constructor
  · intro h
    exact ⟨(z1fMap H.subtype _ _).2 (LinearMap.fst ℚ_[l] B B) (fun g x => by rw [hM]; rfl) _ h,
      (z1fMap H.subtype _ _).2 (LinearMap.snd ℚ_[l] B B) (fun g x => by rw [hM]; rfl) _ h⟩
  · rintro ⟨h1, h2⟩
    have k1 := (z1fMap H.subtype _ (T.M1.comp H.subtype : Representation B H (B × B))).2
      (LinearMap.inl ℚ_[l] B B) (fun g x => by rw [hM]; simp) _ h1
    have k2 := (z1fMap H.subtype _ (T.M1.comp H.subtype : Representation B H (B × B))).2
      (LinearMap.inr ℚ_[l] B B) (fun g x => by rw [hM]; simp) _ h2
    have k := add_mem k1 k2
    convert k using 1
    ext g <;> simp
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

namespace UpperTheory.V.Loc.TriangularDeformation
open Topology

private def resH {G B : Type} [Group G] [CommRing B] (u : G →* GG (m := 3) (R := B)) (H : Subgroup G)
    (h : ∀ g ∈ H, (u g).right = 1) : H →* GL (Fin 3) B where
  toFun g := (u g).left
  map_one' := by simp
  map_mul' g g' := by simp [h g g.2]

private theorem lcr_iff {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] (H : Subgroup (GQ l))
    (u : GQ l →* GG (m := 3) (R := B)) (h : ∀ g ∈ H, (u g).right = 1) : LCr H u ↔ IsCr H.subtype (colRep (resH u H h)) := by
  refine ⟨fun ⟨ρ, hρ, hc⟩ => ?_, fun hc => ⟨_, fun _ => rfl, hc⟩⟩
  have : resH u H h = ρ := MonoidHom.ext fun g => (hρ g).symm
  rwa [this]

private theorem chi_res {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} (T : Tor η B) (H : Subgroup G)
    (hH : ∀ g ∈ H, η g = 1) :
    ((chRep T.χ2).comp H.subtype : Representation B H B) = chRep (T.ch H hH 0 / T.ch H hH 2) := by
  refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
  change (T.χ2 g : B) * v = ((T.t g 0 / T.t g 2 : Bˣ) : B) * v
  rw [Tor.χ2_apply, hH g g.2]
  simp

private theorem gam_sub {G B : Type} [Group G] [CommRing B] [TopologicalSpace G] [TopologicalSpace B]
    [IsTopologicalRing B] {η : G →* ℤˣ} {T : Tor η B} {h : B} {β : G → B × B} {γ γ' : G → B}
    (cγ : Continuous γ) (cγ' : Continuous γ') (g1 : T.IsGam h β γ) (g2 : T.IsGam h β γ') :
    γ' - γ ∈ Z1 (chRep T.χ2) := by
  refine ⟨cγ'.sub cγ, fun g g' => ?_⟩
  simp only [Pi.sub_apply, chRep_apply, g1 g g', g2 g g']
  ring

private theorem gam_add {G B : Type} [Group G] [CommRing B] [TopologicalSpace G] [TopologicalSpace B]
    [IsTopologicalRing B] {η : G →* ℤˣ} {T : Tor η B} {h : B} {β : G → B × B} {γ δ : G → B}
    (g1 : T.IsGam h β γ) (hδ : δ ∈ Z1 (chRep T.χ2)) : T.IsGam h β (γ + δ) := by
  intro g g'
  simp only [Pi.add_apply, chRep_apply, g1 g g', hδ.2 g g']
  ring

private theorem gamDiff : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (T : Tor η B), T.Good π Ψ → ∀ (h : B) (β : GQ l → B × B) (γ γ' : GQ l → B) (u u' : GQ l →* GG (m := 3) (R := B)), Continuous β → Continuous γ → Continuous γ' → (∀ g, π (β g).1 = 0) → T.IsGam h β γ → T.IsGam h β γ' → T.Coord h β γ u → T.Coord h β γ' u' → LCr H u → (LCr H u' ↔ γ' - γ ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) (chRep T.χ2)) := by
  intro hP l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ T hT h β γ γ' u u' cβ cγ cγ' hβ g1 g2 c1 c2 hu
  haveI := hD.normal
  haveI := hD.fin
  have hφ : IsOpenEmbedding H.subtype := hD.isOpen.isOpenEmbedding_subtypeVal
  have r1 : ∀ g ∈ H, (u g).right = 1 := fun g hg => (c1.right g).trans (hD.ηH g hg)
  have r2 : ∀ g ∈ H, (u' g).right = 1 := fun g hg => (c2.right g).trans (hD.ηH g hg)
  rw [lcr_iff H u r1] at hu
  have key := (UpperTheory.isCrystalline_triangular_iff_mem_finiteCocycles_of_charData hP H.subtype hφ π hπ (hT.chars hD) (fun g => (β g).1) (fun g => (β g).2)
    (fun g => γ g + h * (β g).1 * (β g).2) (resH u H r1) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun g => c1.mat g) (fun g => hβ g) hu (fun g => γ' g + h * (β g).1 * (β g).2) (resH u' H r2) (by fun_prop)
    (fun g => c2.mat g)).2
  rw [lcr_iff H u' r2, key, z1fDesc (MonoidHom.id _) (chRep T.χ2) H _ (gam_sub cγ cγ' g1 g2), chi_res T H hD.ηH]
  have : ((fun g : H => γ' g + h * (β g).1 * (β g).2) - fun g : H => γ g + h * (β g).1 * (β g).2) =
      fun g : H => (γ' - γ) g := by
    funext g
    simp
  rw [this]
  rfl

private def nE {B : Type} [CommRing B] (c : B) : GL (Fin 3) B where
  val := !![1, 0, c; 0, 1, 0; 0, 0, 1]
  inv := !![1, 0, -c; 0, 1, 0; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem nE_mul {B : Type} [CommRing B] (c : B) (t : Fin 3 → Bˣ) (x y z : B) :
    (nE c : Matrix (Fin 3) (Fin 3) B) * triM t x y z = triM t x y (z + c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nE, triM, Matrix.mul_apply, Fin.sum_univ_three]
  ring

private theorem theta_nE {B : Type} [CommRing B] (c : B) : theta (nE c) = nE (-c) := by
  apply Units.ext
  rw [theta_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nE, Jmat, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev]

private theorem triM_nE {B : Type} [CommRing B] (c : B) (t : Fin 3 → Bˣ) (x y z : B) :
    triM t x y z * (nE c : Matrix (Fin 3) (Fin 3) B) =
      (nE (((t 0 / t 2 : Bˣ) : B) * c) : Matrix (Fin 3) (Fin 3) B) * triM t x y z := by
  have e : ((t 0 / t 2 : Bˣ) : B) * t 2 = t 0 := by rw [← Units.val_mul, div_mul_cancel]
  rw [nE_mul]
  generalize ((t 0 / t 2 : Bˣ) : B) = q at e
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nE, triM, Matrix.mul_apply, Fin.sum_univ_three]
  rw [← e]
  ring

private theorem conj_nE {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} {T : Tor η B} {h : B} {β : G → B × B}
    {γ : G → B} {u : G →* GG (m := 3) (R := B)} (hu : T.Coord h β γ u) (s : G) (c : B) :
    u s * GG.ofGL (nE c) = GG.ofGL (nE (T.χ2 s * c)) * u s := by
  refine SemidirectProduct.ext ?_ (by simp)
  have hm : ((u s).left : Matrix (Fin 3) (Fin 3) B) = _ := hu.mat s
  apply Units.ext
  rcases Int.units_eq_one_or (η s) with hs | hs <;>
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, hu.right, hs,
      sgnAct_one, sgnAct_neg_one, theta_nE, Units.val_mul, hm, triM_nE, Tor.χ2_apply] <;> simp

private theorem gamCr : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (T : Tor η B), T.Good π Ψ → ∀ (h : B), 2 * h = 1 → ∀ β ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) T.M1, (∀ g, π (β g).1 = 0) → ∃ (γ : GQ l → B) (u : GQ l →* GG (m := 3) (R := B)), Continuous γ ∧ T.IsGam h β γ ∧ T.Coord h β γ u ∧ LCr H u := by
  intro hP l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ T hT h hh β hβ hβ0
  haveI := hD.normal
  haveI := hD.fin
  have hφ : IsOpenEmbedding H.subtype := hD.isOpen.isOpenEmbedding_subtypeVal
  have cβ : Continuous β := hβ.1.1
  obtain ⟨γ, cγ, gγ⟩ := UpperTheory.exists_continuous_isGam_of_torus_cocycle hP hD π hπ T hT h β hβ.1
  obtain ⟨u, cu⟩ := UpperTheory.exists_unipotent_from_torus_coords T h hh β γ hβ.1.2 gγ
  have r1 : ∀ g ∈ H, (u g).right = 1 := fun g hg => (cu.right g).trans (hD.ηH g hg)
  obtain ⟨hx, hy⟩ := (UpperTheory.mem_finiteCocycles_iff_restrict_subgroup_mem hD π hπ T hT β hβ.1).1 hβ
  have hch := hT.chars hD
  obtain ⟨z, ρ, cz, hρ, hcr⟩ := UpperTheory.exists_crystalline_triangular_lift_of_mem_finiteCocycles hP H.subtype hφ π hπ hch _ hx _ hy (fun g => hβ0 g)
  have cx : Continuous fun g : H => (β g).1 := by fun_prop
  have cy : Continuous fun g : H => (β g).2 := by fun_prop
  have diff := UpperTheory.isCrystalline_triangular_iff_mem_finiteCocycles_of_charData hP H.subtype hφ π hπ hch _ _ z ρ cx cy cz hρ (fun g => hβ0 g) hcr
  set z₀ : H → B := fun g => γ g + h * (β g).1 * (β g).2 with hz₀
  have cz₀ : Continuous z₀ := by fun_prop
  have hc : z - z₀ ∈ Z1 ((chRep T.χ2).comp H.subtype : Representation B H B) := by
    rw [chi_res T H hD.ηH, ← neg_sub]
    exact Submodule.neg_mem _ (diff z₀ (resH u H r1) cz₀ (fun g => cu.mat g)).1
  have cχ := T.continuous_χ2 hD.ηlc hT.cont hT.cont_inv
  have cρ : Continuous fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) := by
    simp only [hρ]
    exact continuous_triM hch.cont cx cy cz
  have fac : ∀ g : H, GG.ofGL (ρ g) = GG.ofGL (nE ((z - z₀) g)) * u g := by
    intro g
    refine SemidirectProduct.ext (Units.ext ?_) (by simp [r1 g g.2])
    have hm : ((u g).left : Matrix (Fin 3) (Fin 3) B) = _ := cu.mat g
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one,
      Units.val_mul, hm, nE_mul, hρ, Pi.sub_apply, hz₀, add_sub_cancel]
    rfl
  obtain ⟨b, hb, hbN⟩ := UpperTheory.exists_cocycle_extension_of_conjugation_invariant_restriction (l := l) (chRep T.χ2) (contAction_chRep cχ) H hD.isOpen
    (UpperTheory.V.Loc.finiteCocycles H.subtype (chRep (T.ch H hD.ηH 0 / T.ch H hD.ηH 2))) (z - z₀) hc (by
      intro s c' hc'
      let τ : H →* H := (MulAut.conjNormal s⁻¹ : MulAut H).toMonoidHom
      have hτ : ∀ g : H, ((τ g : H) : GQ l) = s⁻¹ * g * s := fun g => by simp [τ]
      have cτ : Continuous τ := by
        refine continuous_induced_rng.2 ?_
        have : (Subtype.val ∘ τ) = fun g : H => s⁻¹ * (g : GQ l) * s := funext hτ
        rw [this]
        fun_prop
      have hw : ∀ g : H, u s * GG.ofGL (ρ (τ g)) * (u s)⁻¹ = GG.ofGL (nE (c' g)) * u g := by
        intro g
        rw [fac, hτ, hc' g (τ g) (hτ g), chRep_apply, ← mul_assoc, conj_nE cu]
        simp only [map_mul, map_inv, mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
      let ρ' : H →* GL (Fin 3) B :=
        { toFun := fun g => nE (c' g) * (u g).left
          map_one' := by
            have := congrArg SemidirectProduct.left (hw 1)
            simpa using this.symm
          map_mul' := fun g g' => by
            have e : GG.ofGL (nE (c' (g * g'))) * u (g * g' : H) =
                (GG.ofGL (nE (c' g)) * u g) * (GG.ofGL (nE (c' g')) * u g') := by
              rw [← hw, ← hw, ← hw]
              simp only [map_mul, mul_assoc, inv_mul_cancel_left]
            have := congrArg SemidirectProduct.left e
            simpa [r1 g g.2] using this }
      have hρ' : ∀ g : H, GG.ofGL (ρ' g) = GG.ofGL (nE (c' g)) * u g := fun g =>
        SemidirectProduct.ext (by simp [ρ']) (by simp [r1 g g.2])
      have cr' := UpperTheory.conjugate_restriction_open_normal H hD.isOpen ρ ρ' cρ s (u s) (fun g g' e => by
        have : g' = τ g := Subtype.ext (e.trans (hτ g).symm)
        rw [hρ', this, hw]) hcr
      have cc' : Continuous c' := by
        have : c' = fun g => (T.χ2 s : B) * (z - z₀) (τ g) := funext fun g => hc' g (τ g) (hτ g)
        rw [this]
        exact continuous_const.mul ((cz.sub cz₀).comp cτ)
      have := (diff (z₀ + c') ρ' (cz₀.add cc') (fun g => by
        have hm : ((u g).left : Matrix (Fin 3) (Fin 3) B) = _ := cu.mat g
        change ((nE (c' g) * (u g).left : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) = _
        rw [Units.val_mul, hm, nE_mul]
        rfl)).2.1 cr'
      convert this using 1
      abel)
  obtain ⟨u', cu'⟩ := UpperTheory.exists_unipotent_from_torus_coords T h hh β (γ + b) hβ.1.2 (gam_add gγ hb)
  refine ⟨γ + b, u', cγ.add hb.1, gam_add gγ hb, cu', ?_⟩
  have r2 : ∀ g ∈ H, (u' g).right = 1 := fun g hg => (cu'.right g).trans (hD.ηH g hg)
  have cb : Continuous b := hb.1
  rw [lcr_iff H u' r2]
  refine (diff (fun g : H => (γ + b) g + h * (β g).1 * (β g).2) (resH u' H r2) (by fun_prop)
    (fun g => cu'.mat g)).2.2 ?_
  convert hbN using 1
  ext g
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, hz₀]
  ring

private theorem triM_map {B B' : Type} [CommRing B] [CommRing B'] (p : B →+* B') (t : Fin 3 → Bˣ) (t' : Fin 3 → B'ˣ)
    (ht : ∀ i, p (t i) = t' i) (x y z : B) : (triM t x y z).map p = triM t' (p x) (p y) (p z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [triM, ht]

private theorem gg_ext {B : Type} [CommRing B] {a b : GG (m := 3) (R := B)} (h1 : a.mat = b.mat) (h2 : a.right = b.right) : a = b :=
  SemidirectProduct.ext (Units.ext h1) h2

private theorem lcr_map {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B]
    [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B]
    {B' : Type} [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B']
    [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B'] (p : B →ₐ[ℚ_[l]] B')
    (hp : Function.Surjective p) {H : Subgroup (GQ l)} (hH : IsOpen (H : Set (GQ l))) {u : GQ l →* GG (m := 3) (R := B)}
    (cu : Continuous fun g => (u g).mat) (hu : LCr H u) : LCr H ((GG.map (p : B →+* B')).comp u) := by
  obtain ⟨ρ, hρ, hc⟩ := hu
  have cp : Continuous p := IsModuleTopology.continuous_of_linearMap p.toLinearMap
  have cρ : Continuous fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) := by
    simp only [hρ]
    exact cu.comp continuous_subtype_val
  refine ⟨(Matrix.GeneralLinearGroup.map (p : B →+* B')).comp ρ, fun g => ?_, ?_⟩
  · rw [MonoidHom.comp_apply, hρ]
    rfl
  · refine ((isCrys_isDR_sub_quot H.subtype hH.isOpenEmbedding_subtypeVal _ _ (contAction_colRep cρ)
      (contAction_colRep (cρ.matrix_map cp)) (p.toLinearMap.compLeft (Fin 3)) (fun g x => ?_)).2 fun v => ?_).1 hc
    · funext i
      exact RingHom.map_mulVec (p : B →+* B') _ x i
    · exact ⟨fun i => (hp (v i)).choose, funext fun i => (hp (v i)).choose_spec⟩

private theorem triDat {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O)
    (E : Type) [Field E] [Algebra ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E]
    (hc : QCont l fun g => algebraMap O E (D.Ψ g)) :
    TriDat D.η ((Units.map (algebraMap O E : O →* E)).comp D.Ψ) D.HL D.e := by
  have hη : IsOpen (D.η.ker : Set (GQ l)) := by
    have : D.η.ker = GK D.Kv := Subgroup.ext fun g => D.η_ker g
    rw [this]
    haveI := D.Kv.2
    exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  have ho : IsOpen (D.HL : Set (GQ l)) := hη.inter D.τ_open
  refine ⟨inferInstanceAs (D.η.ker ⊓ D.τ.ker).Normal, ho, ?_, fun g hg => hg.1, D.η_unr, ?_, D.e_pos, fun g hg hi => ?_, hc⟩
  · haveI := Subgroup.quotient_finite_of_isOpen _ ho
    exact Subgroup.finiteIndex_of_finite_quotient
  · refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
    have : IsOpen {y : GQ l | g⁻¹ * y ∈ D.η.ker} := hη.preimage (by fun_prop)
    filter_upwards [this.mem_nhds (by simp)] with y hy
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hy
    exact hy.symm
  · have ht : D.τ g = 1 := hg.2
    rw [MonoidHom.comp_apply, D.Ψ_I g hi, ht, mul_one, map_pow]
    congr 1
    exact Units.ext (IsScalarTower.algebraMap_apply ℤ_[l] O E _).symm

end UpperTheory.V.Loc.TriangularDeformation

open UpperTheory.V.Loc.TriangularDeformation in
theorem UpperTheory.V.Loc.triLift :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (B' : Type) [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra O B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] O B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower O E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ u' : GQ l →* GG (m := 3) (R := B'), D.InDtri (π' : B' →+* E) u' → ∃ u : GQ l →* GG (m := 3) (R := B), D.InDtri (π : B →+* E) u ∧ (GG.map (p : B →+* B')).comp u = u' := by
  intro hP l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hpπ u' hu'
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  letI : TopologicalSpace B' := moduleTopology ℚ_[l] B'
  haveI : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩
  haveI : IsTopologicalRing B' := IsModuleTopology.isTopologicalRing ℚ_[l] B'
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  have cp : Continuous p := IsModuleTopology.continuous_of_linearMap (p.restrictScalars ℚ_[l]).toLinearMap
  have cπ' : Continuous π' := IsModuleTopology.continuous_of_linearMap (π'.restrictScalars ℚ_[l]).toLinearMap
  have hππ : ∀ b, π' (p b) = π b := fun b => AlgHom.congr_fun hpπ b
  set Ψ : GQ l →* Eˣ := (Units.map (algebraMap O E : O →* E)).comp D.Ψ with hΨ
  have hpow : ∀ g i, algebraMap O E ((D.Ψ g ^ wt1 i : Oˣ) : O) = ((Ψ g ^ wt1 i : Eˣ) : E) := fun g i => by
    rw [hΨ, MonoidHom.comp_apply, ← map_zpow (Units.map (algebraMap O E : O →* E))]
    rfl
  have red' : ∀ g a b, π' ((u' g).mat a b) = if a = b then ((Ψ g ^ wt1 a : Eˣ) : E) else 0 := fun g a b => by
    have := congrFun (congrFun (congrArg GG.mat (DFunLike.congr_fun hu'.red g)) a) b
    refine this.trans ?_
    change algebraMap O E (Matrix.diagonal (fun i => ((D.Ψ g ^ wt1 i : Oˣ) : O)) a b) = _
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact hpow g a
    · exact map_zero _
  have cu' : ∀ a b, Continuous fun g => (u' g).mat a b := hu'.cont
  have hD : TriDat D.η Ψ D.HL D.e := triDat D E (by
    have : (fun g => algebraMap O E (D.Ψ g)) = fun g => π' ((u' g).mat 0 0) := funext fun g => by
      rw [red', if_pos rfl, ← hpow]
      simp [wt1]
    rw [this]
    exact cπ'.comp (cu' 0 0))
  haveI := hD.normal
  set h : B := algebraMap E B 2⁻¹ with hh0
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  have hh : 2 * h = 1 := by
    rw [hh0, ← map_ofNat (algebraMap E B) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have hh' : 2 * p h = 1 := by
    have := congrArg p hh
    rwa [map_mul, map_ofNat, map_one] at this
  obtain ⟨T', β', γ', c', zβ', gγ'⟩ := UpperTheory.exists_torus_coords_of_unipotent (p h) hh' u' hu'.mult hu'.tri
  have d' : ∀ g i, (T'.t g i : B') = (u' g).mat i i := fun g i => by
    rw [c'.mat]
    fin_cases i <;> rfl
  have ct' : ∀ i, Continuous fun g => (T'.t g i : B') := fun i => by
    simp only [d']
    exact cu' i i
  have hT' : T'.Good π' Ψ :=
    { cont := ct'
      cont_inv := fun i => UpperTheory.continuous_units_inv_of_continuous_coe_finite_Qp_algebra (l := l) (fun g => T'.t g i) (ct' i)
      ine := fun g hg i => by
        rw [d', triDiag D E B' π' hπ' u' hu' g hg i, IsScalarTower.algebraMap_apply O E B', ← hpow]
        rfl
      red := fun g i => by rw [d', red', if_pos rfl] }
  have e1 : ∀ g, (β' g).1 = (u' g).mat 0 1 * ((T'.t g 1)⁻¹ : B'ˣ) := fun g => by
    rw [c'.mat]
    simp [triM]
  have e2 : ∀ g, (β' g).2 = (u' g).mat 1 2 * ((T'.t g 2)⁻¹ : B'ˣ) := fun g => by
    rw [c'.mat]
    simp [triM]
  have e3 : ∀ g, γ' g = (u' g).mat 0 2 * ((T'.t g 2)⁻¹ : B'ˣ) - p h * (β' g).1 * (β' g).2 := fun g => by
    rw [c'.mat]
    simp [triM]
  have c1 : Continuous fun g => (β' g).1 := by
    simp only [e1]
    exact (cu' 0 1).mul (hT'.cont_inv 1)
  have c2 : Continuous fun g => (β' g).2 := by
    simp only [e2]
    exact (cu' 1 2).mul (hT'.cont_inv 2)
  have cβ' : Continuous β' := c1.prodMk c2
  have cγ' : Continuous γ' := by
    rw [funext e3]
    exact ((cu' 0 2).mul (hT'.cont_inv 2)).sub ((continuous_const.mul c1).mul c2)
  have β0' : ∀ g, π' (β' g).1 = 0 := fun g => by
    rw [e1, map_mul, red', if_neg (by decide), zero_mul]
  have fβ' : β' ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) T'.M1 := by
    obtain ⟨ρ, hρ, hcr⟩ := hu'.cr
    refine (UpperTheory.mem_finiteCocycles_iff_restrict_subgroup_mem hD π' hπ' T' hT' β' ⟨cβ', zβ'⟩).2 ?_
    refine UpperTheory.isCrystalline_triangular_iff_of_charData D.HL.subtype hD.isOpen.isOpenEmbedding_subtypeVal π' hπ' (hT'.chars hD) _ _
      (fun g => γ' g + p h * (β' g).1 * (β' g).2) ρ (by fun_prop) (by fun_prop) (by fun_prop) (fun g => ?_) hcr
    rw [hρ]
    exact c'.mat g
  obtain ⟨T, hT, hTp⟩ := UpperTheory.exists_torus_lift_to_nilpotent_thickening hD π hπ π' hπ' p hp hpπ T' hT'
  obtain ⟨β, fβ, hβp⟩ := UpperTheory.torsionDatum_finiteCocycles_baseChange hP hD π hπ π' hπ' p hp T T' hT hT' hTp β' fβ'
  have cβ : Continuous β := fβ.1.1
  have β0 : ∀ g, π (β g).1 = 0 := fun g => by rw [← hππ, (hβp g).1, β0']
  obtain ⟨γ, u, cγ, gγ, cu, hu⟩ := gamCr hP hD π hπ T hT h hh β fβ β0
  have push : ∀ (γ : GQ l → B) (u : GQ l →* GG (m := 3) (R := B)), T.Coord h β γ u →
      T'.Coord (p h) β' (fun g => p (γ g)) ((GG.map (p : B →+* B')).comp u) := fun γ u c =>
    ⟨fun g => c.right g, fun g => by
      rw [MonoidHom.comp_apply, GG.map_mat, c.mat, triM_map (p : B →+* B') _ _ (hTp g)]
      simp only [RingHom.coe_coe, map_add (f := _), map_mul, (hβp g).1, (hβp g).2]⟩
  have hq : ∀ g i j, p ((T.t g i / T.t g j : Bˣ) : B) = ((T'.t g i / T'.t g j : B'ˣ) : B') := fun g i j => by
    have : ∀ i, Units.map (p : B →* B') (T.t g i) = T'.t g i := fun i => Units.ext (hTp g i)
    rw [← this, ← this, ← _root_.map_div]
    rfl
  have gp : T'.IsGam (p h) β' (fun g => p (γ g)) := fun g g' => by
    simp only [gγ g g', omg, Tor.adjointSuperdiagRep_apply, Tor.χ2_apply]
    split_ifs <;> simp only [map_add (f := _), map_mul, map_sub, map_neg, map_intCast, hq, (hβp _).1, (hβp _).2]
  have cmat : ∀ (γ : GQ l → B) (u : GQ l →* GG (m := 3) (R := B)), Continuous γ → T.Coord h β γ u →
      Continuous fun g => (u g).mat := fun γ u cγ c => by
    simp only [c.mat]
    exact continuous_triM hT.cont (by fun_prop) (by fun_prop) (by fun_prop)
  have hδ' := (gamDiff hP hD π' hπ' T' hT' (p h) β' (fun g => p (γ g)) γ' _ u' cβ' (cp.comp cγ) cγ' β0' gp gγ'
    (push γ u cu) c' (lcr_map (p.restrictScalars ℚ_[l]) hp hD.isOpen (cmat γ u cγ cu) hu)).1 hu'.cr
  obtain ⟨δ, fδ, hδp⟩ := UpperTheory.torsionDatum_finiteCocycles_compare hP hD π hπ π' hπ' p hp T T' hT hT' hTp _ hδ'
  have g2 := gam_add gγ fδ.1
  obtain ⟨v, cv⟩ := UpperTheory.exists_unipotent_from_torus_coords T h hh β (γ + δ) fβ.1.2 g2
  have c2 : Continuous (γ + δ) := cγ.add fδ.1.1
  have hv : (GG.map (p : B →+* B')).comp v = u' := by
    refine MonoidHom.ext fun g => gg_ext ?_ ?_
    · rw [(push _ v cv).mat, c'.mat]
      simp [hδp]
    · rw [(push _ v cv).right, c'.right]
  refine ⟨v, ⟨⟨cv.right, ?_, fun a b => (cmat _ v c2 cv).matrix_elem a b, ?_⟩, fun g a b hab => ?_⟩, hv⟩
  · rw [← hu'.red, ← hv]
    refine MonoidHom.ext fun g => gg_ext ?_ rfl
    ext a b
    exact (hππ _).symm
  · exact (gamDiff hP hD π hπ T hT h β γ (γ + δ) u v cβ cγ c2 β0 gγ g2 cu cv hu).2 (by simpa using fδ)
  · rw [cv.mat]
    revert hab
    fin_cases a <;> fin_cases b <;> simp [triM, wt, wt1]
