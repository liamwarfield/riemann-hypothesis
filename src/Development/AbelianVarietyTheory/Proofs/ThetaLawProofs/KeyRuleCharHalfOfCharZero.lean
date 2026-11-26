module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ValueAtNormalForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsThetaLawZeroOfEven
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaSqCongrModTwo
noncomputable section

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.KeyPow

theorem theta_sq_congr_mod_two {g : ℕ} {k k' m m' : Fin g → ℤ} (h : ∀ i, k i % 2 = m i % 2)
    (h' : ∀ i, k' i % 2 = m' i % 2) (z : Fin g → ℂ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    theta (halfVec k) (halfVec k') z τ ^ 2 = theta (halfVec m) (halfVec m') z τ ^ 2 := by
  rw [theta_sq_red k k', theta_sq_red m m', funext h, funext h']

theorem ThetaLaw.congr_target {g : ℕ} {sp : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    {n n' k k' m m' : Fin g → ℤ} (hl : ThetaLaw g sp n n' k k') (h : ∀ i, m i % 2 = k i % 2)
    (h' : ∀ i, m' i % 2 = k' i % 2) : ThetaLaw g sp n n' m m' := by
  obtain ⟨c, hc, hlaw⟩ := hl
  exact ⟨c, hc, fun τ hτ z => by rw [theta_sq_congr_mod_two h h']; exact hlaw τ hτ z⟩

theorem thetaLaw_spTransl {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) (hS : S.IsSymm) (n n' : Fin g → ℤ) :
    ThetaLaw g (spTransl S) n n' n (n' - S *ᵥ n - fun i => S i i) := by
  set X : ℂ := -(ofRealVec (halfVec n) ⬝ᵥ (S.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec (halfVec n))) / 2 -
      ofRealVec (halfVec n) ⬝ᵥ (fun i => ((S i i : ℤ) : ℂ) / 2) with hX
  refine ⟨eC X ^ 2, ?_, fun τ _ z => ?_⟩
  · rw [← pow_mul, eC_pow]
    have h8 : ((2 * 4 : ℕ) : ℂ) * X = ((-(n ⬝ᵥ (S *ᵥ n)) - 2 * (n ⬝ᵥ fun i => S i i) : ℤ) : ℂ) := by
      have hd : ofIntVec n ⬝ᵥ (fun i => ((S i i : ℤ) : ℂ)) = ((n ⬝ᵥ fun i => S i i : ℤ) : ℂ) := by
        simp [dotProduct, ofIntVec]
      have hd2 : (fun i => ((S i i : ℤ) : ℂ) / 2) = (1 / 2 : ℂ) • fun i => ((S i i : ℤ) : ℂ) := by
        ext i; simp; ring
      rw [hX, ofRealVec_halfVec, Matrix.mulVec_smul, ← ofIntVec_mulVec, smul_dotProduct,
        dotProduct_smul, ofIntVec_dot, hd2, smul_dotProduct, dotProduct_smul, hd]
      simp only [smul_eq_mul]
      push_cast; ring
    rw [h8, eC_int]
  · have hb : halfVec (n' - S *ᵥ n - fun i => S i i) + S.map (fun x : ℤ => (x : ℝ)) *ᵥ halfVec n +
        (fun i => ((S i i : ℤ) : ℝ) / 2) = halfVec n' := by
      rw [mulVec_halfVec]
      ext i; simp only [halfVec, Pi.add_apply, Pi.sub_apply]; push_cast; ring
    have hz : zAct (spTransl S) τ z = z := by simp [zAct, jAut_spTransl]
    have he : expArg (spTransl S) τ z = 0 := by simp [expArg, jAut_spTransl, cMat_spTransl]
    rw [hz, he, spAct_spTransl, jAut_spTransl, thetaTranslTau_holds (Fin g) _ _ _ _ S hS, hb,
      mul_pow, det_one, eC_zero]
    ring

theorem thetaLaw_J {g : ℕ} (hInv : InversionStatement) (n n' : Fin g → ℤ) :
    ThetaLaw g (Matrix.J (Fin g) ℤ) n n' (-n') n := by
  set F : ℂ := 2 * (ofRealVec (halfVec (-n')) ⬝ᵥ ofRealVec (halfVec n))
  refine ⟨(-I) ^ g * eC F, ?_, fun τ hτ z => ?_⟩
  · rw [mul_pow, ← pow_mul, mul_comm g 4, pow_mul, eC_pow]
    have hI : (-I : ℂ) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]; simp
    have hF : ((4 : ℕ) : ℂ) * F = ((-(2 * (n' ⬝ᵥ n)) : ℤ) : ℂ) := by
      simp only [F, ofRealVec_halfVec, smul_dotProduct, dotProduct_smul, ofIntVec_dot, smul_eq_mul]
      simp [dotProduct]; ring
    rw [hI, one_pow, one_mul, hF, eC_int]
  · have hsym : τ.IsSymm := hτ.1
    have hs : spAct (Matrix.J (Fin g) ℤ) τ = -τ⁻¹ := by
      rw [spAct_eq, jAut_J, nAut_eq, cMat_J]; simp [Matrix.J]
    have htinv : (τ⁻¹)ᵀ = τ⁻¹ := by rw [Matrix.transpose_nonsing_inv, hsym.eq]
    have hz : zAct (Matrix.J (Fin g) ℤ) τ z = τ⁻¹ *ᵥ z := by rw [zAct, jAut_J, htinv]
    have he : expArg (Matrix.J (Fin g) ℤ) τ z = z ⬝ᵥ (τ⁻¹ *ᵥ z) := by
      rw [expArg, jAut_J, cMat_J]; simp [Matrix.J]
    have hneg : -halfVec (-n') = halfVec n' := by ext i; simp [halfVec]; ring
    rw [hs, hz, he, jAut_J, hInv g _ _ τ hτ z, hneg]
    ring

theorem thetaLaw_generators (hInv : InversionStatement) (g : ℕ) (k k' : Fin g → ℤ) :
    (∀ (S : Matrix (Fin g) (Fin g) ℤ) (n' : Fin g → ℤ), S.IsSymm →
      (∀ i, (2 : ℤ) ∣ (S.mulVec k) i + S i i + k' i - n' i) → ThetaLaw g (spTransl S) k n' k k') ∧
    ThetaLaw g (Matrix.J (Fin g) ℤ) k' k k k' := by
  refine ⟨fun S n' hS hd => (thetaLaw_spTransl S hS k n').congr_target (fun _ => rfl) fun i => ?_,
    (thetaLaw_J hInv k' k).congr_target (fun i => ?_) fun _ => rfl⟩
  · have := hd i
    simp only [Pi.sub_apply]
    omega
  · simp only [Pi.neg_apply]
    omega

end GlobalTheory.KeyPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaLawMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyPow


open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi in
theorem thetaLaw_mul : ∀ (g : ℕ) (sp sq : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (n n' m m' k k' : Fin g → ℤ), sp ∈ Matrix.symplecticGroup (Fin g) ℤ → sq ∈ Matrix.symplecticGroup (Fin g) ℤ → GlobalTheory.KeyPow.ThetaLaw g sq n n' m m' → GlobalTheory.KeyPow.ThetaLaw g sp m m' k k' → GlobalTheory.KeyPow.ThetaLaw g (sp * sq) n n' k k' := by
  intro g x y n n' m m' k k' hx hy Hy Hx
  obtain ⟨c₁, hc₁, h₁⟩ := Hy
  obtain ⟨c₂, hc₂, h₂⟩ := Hx
  refine ⟨c₂ * c₁, by rw [mul_pow, hc₁, hc₂, _root_.one_mul], fun τ hτ z => ?_⟩
  have hjy := jAut_isUnit hy hτ
  have hτ₂ := spAct_mem hy hτ
  have hjx := jAut_isUnit hx hτ₂
  rw [spAct_mul x y τ hjy, zAct_mul x y τ hjy z, h₂ _ hτ₂, h₁ τ hτ z, det_jAut_mul x y τ hjy,
    expArg_mul x y τ hjy hjx (sp_A hy hτ.1 hjy) z, eC_add]
  ring

end GlobalTheory.KeyPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsSymmMulVecAddDiagModTwo
namespace GlobalTheory

theorem exists_isSymm_mulVec_add_diag_mod_two :
    ∀ (g : ℕ) (n n' : Fin g → ℤ), Even (n ⬝ᵥ n') →
      ∃ S : Matrix (Fin g) (Fin g) ℤ, S.IsSymm ∧
        ∀ i, (2 : ℤ) ∣ (S.mulVec n) i + S i i - n' i := by
  intro g n n' h
  by_cases hall : ∀ i, Even (n i)
  · refine ⟨Matrix.diagonal n', Matrix.isSymm_diagonal _, fun i => ?_⟩
    obtain ⟨k, hk⟩ := hall i
    rw [Matrix.mulVec_diagonal, Matrix.diagonal_apply_eq, hk]
    exact ⟨n' i * k, by ring⟩
  · obtain ⟨p, hp⟩ := not_forall.mp hall
    obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hp
    obtain ⟨m, hm⟩ := h
    refine ⟨Matrix.of fun i j => (if i = p then n' j else 0) + (if j = p then n' i else 0),
      ?_, fun i => ?_⟩
    · ext i j
      simp only [Matrix.transpose_apply, Matrix.of_apply]
      ring
    · have hm' : ∑ j, n' j * n j = m + m := by
        rw [← hm]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      have h2 : ∑ j, (if j = p then n' i else 0) * n j = n' i * n p := by
        simp
      by_cases hi : i = p
      · subst hi
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
          if_true, hm', h2, hk]
        exact ⟨m + n' i * k + n' i, by ring⟩
      · simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
          if_neg hi, h2, hk, zero_mul, Finset.sum_const_zero]
        exact ⟨n' i * k, by ring⟩

end GlobalTheory
end

namespace GlobalTheory.KeyPow


open Matrix ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi in
theorem exists_thetaLaw_zero_of_even (hInv : ReciprocityTheory.ChartRestriction.G.Key.Chi.InversionStatement) (g : ℕ)
    (n n' : Fin g → ℤ) (h : Even (n ⬝ᵥ n')) :
    ∃ sp ∈ Matrix.symplecticGroup (Fin g) ℤ, GlobalTheory.KeyPow.ThetaLaw g sp n n' 0 0 := by
  obtain ⟨S, hS, hd⟩ := GlobalTheory.exists_isSymm_mulVec_add_diag_mod_two g n n' h
  have h1 : ThetaLaw g (spTransl S) n n' n 0 :=
    (thetaLaw_generators hInv g n 0).1 S n' hS fun i => by simpa using hd i
  have h2 : ThetaLaw g (Matrix.J (Fin g) ℤ) n 0 0 n := (thetaLaw_generators hInv g 0 n).2
  have hD : (Matrix.diagonal n).IsSymm := Matrix.isSymm_diagonal _
  have h3 : ThetaLaw g (spTransl (Matrix.diagonal n)) 0 n 0 0 :=
    (thetaLaw_generators hInv g 0 0).1 _ n hD fun i => by simp
  have m1 : spTransl S ∈ Matrix.symplecticGroup (Fin g) ℤ := spTransl_mem_sp hS
  have m2 : Matrix.J (Fin g) ℤ ∈ Matrix.symplecticGroup (Fin g) ℤ := SymplecticGroup.J_mem _ _
  have m3 : spTransl (Matrix.diagonal n) ∈ Matrix.symplecticGroup (Fin g) ℤ := spTransl_mem_sp hD
  exact ⟨_, mul_mem m3 (mul_mem m2 m1), thetaLaw_mul g _ _ _ _ _ _ _ _ m3 (mul_mem m2 m1)
    (thetaLaw_mul g _ _ _ _ _ _ _ _ m2 m1 h1 h2) h3⟩

end GlobalTheory.KeyPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NonzeroLocusConstMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PowChange

open GlobalTheory.PowLie

variable {R : Type} [CommRing R]

theorem sc_zero_comp {G : Over (Sp R)} [GrpObj G] {v : epsR R ⟶ G} (hv : IsTangent v) :
    sc 0 ≫ v = 1 := by
  have h : sc (0 : R) = toUnit _ ≫ zeroPt R := by
    refine Over.OverMorphism.ext ?_
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  rw [h, Category.assoc, (isTangent_iff v).1 hv, Hom.one_def]

theorem exists_block_basis {G' G : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    {j g n : ℕ} (p : Out.IsPowGrp G' G j) (hg : j * g = n) {v v' : Fin g → (epsR R ⟶ G)}
    (hv : IsLieBasis v) (hv' : IsLieBasis v') (M : Matrix (Fin g) (Fin g) R)
    (hM : ∀ i, IsLieComb (M i) v (v' i)) (u : Fin n → (epsR R ⟶ G'))
    (hu : ∀ (i i' : Fin j) (k : Fin g),
      u ((finProdFinEquiv (i, k)).cast hg) ≫ p.pr i' = if i = i' then v k else 1) :
    ∃ (w : Fin n → (epsR R ⟶ G')) (M' : Matrix (Fin n) (Fin n) R), IsLieBasis w ∧
      (∀ (i i' : Fin j) (k : Fin g),
        w ((finProdFinEquiv (i, k)).cast hg) ≫ p.pr i' = if i = i' then v' k else 1) ∧
      (∀ i, IsLieComb (M' i) u (w i)) ∧ M'.det = M.det ^ j := by
  subst hg
  obtain ⟨w, hw, hw'⟩ := isLieBasis_pow R G' G j g p v' hv'
  let e : Fin g × Fin j ≃ Fin (j * g) := (Equiv.prodComm _ _).trans finProdFinEquiv
  refine ⟨w, Matrix.reindex e e (Matrix.blockDiagonal fun _ => M), hw, hw', fun m => ?_, ?_⟩
  · obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective m
    rw [isLieComb_iff_prod]
    refine p.lim.hom_ext fun ⟨i'⟩ => ?_
    have := p.hom i'
    change _ ≫ p.pr i' = _ ≫ p.pr i'
    refine Eq.trans ?_ (map_prod (IsMonHom.monoidHom (p.pr i') (epsR R)) _ _).symm
    have hu' : ∀ (i : Fin j) (k : Fin g), u (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1 :=
      fun i k => hu i i' k
    rw [hw', ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type, Finset.prod_eq_single i']
    · have h₁ : ∀ k', (IsMonHom.monoidHom (p.pr i') (epsR R))
          (sc (Matrix.reindex e e (Matrix.blockDiagonal fun _ => M) (finProdFinEquiv (i, k))
            (finProdFinEquiv (i', k'))) ≫ u (finProdFinEquiv (i', k'))) =
          sc (if i = i' then M k k' else 0) ≫ v k' := fun k' => by
        change (sc _ ≫ u _) ≫ p.pr i' = _
        rw [Category.assoc, hu', if_pos rfl]
        congr 2
        simp [e, Matrix.blockDiagonal_apply]
      rw [Finset.prod_congr rfl fun k' _ => h₁ k']
      split_ifs with h
      · exact (isLieComb_iff_prod _ _ _).1 (hM k)
      · exact (Finset.prod_eq_one fun k' _ => sc_zero_comp (hv.1 k')).symm
    · intro i'' _ hi
      refine Finset.prod_eq_one fun k' _ => ?_
      change (sc _ ≫ u _) ≫ p.pr i' = _
      rw [Category.assoc, hu', if_neg hi, comp_one]
    · simp
  · rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal]
    simp

theorem appLE_constFn {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R) (f : Y ⟶ X) (hf : f ≫ q = q')
    (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V h).hom (constFn q U a) = constFn q' V a := by
  subst hf
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ U V (fun _ _ => trivial) h)

theorem res_constFn {X : Scheme.{0}} (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn q U a) = constFn q V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem constFn_pow {X : Scheme.{0}} (q : X ⟶ Sp R) (U : X.Opens) (a : R) (n : ℕ) :
    constFn q U (a ^ n) = constFn q U a ^ n := by
  simp only [constFn, map_pow]

def constMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} (a : R) (s : L.Sec) : L.Sec where
  f i := constFn q _ a * s.f i
  compat i j := by
    rw [map_mul, map_mul, res_constFn, res_constFn, s.compat, mul_left_comm]

theorem nonzeroLocus_constMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} {a : R} (ha : IsUnit a) (s : L.Sec) :
    Out.nonzeroLocus (constMul q a s) = Out.nonzeroLocus s := by
  refine iSup_congr fun i => ?_
  have h : IsUnit (constFn q (L.U i) a) := (ha.map _).map _
  change X.basicOpen (constFn q _ a * s.f i) = _
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ h]
  exact inf_eq_right.2 (X.basicOpen_le _)

theorem isKeyPow_change : ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K) (M : Matrix (Fin P.g) (Fin P.g) K) (j : ℕ) (y : KeyIn K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → GlobalTheory.KeyPow.IsKeyPow y ⟨P, hg, rig, hr, th, hth, v, hv⟩ j → ∃ (t : y.P.L.Sec) (ht : _) (w : _) (hw : _) (M' : Matrix (Fin y.P.g) (Fin y.P.g) K), GlobalTheory.KeyPow.IsKeyPow ⟨y.P, y.g_pos, y.rig, y.rig_gen, t, ht, w, hw⟩ ⟨P, hg, rig, hr, th', hth', v', hv'⟩ j ∧ (∀ i, t.f i = constFn y.P.A.hom _ (a ^ j) * y.th.f i) ∧ (∀ i, IsLieComb (M' i) y.v (w i)) ∧ M'.det = M.det ^ j := by
  intro K _ P hg rig hr th hth v hv th' hth' v' hv' a M j y ha hM ⟨p, hj, h₁, h₂, h₃⟩
  have h0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨x, -, hx⟩ := hth' (default : PrimeSpectrum K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    rw [ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  haveI := y.P.isAb.comm
  haveI := P.isAb.comm
  obtain ⟨w, M', hw, hw', hM', hdet⟩ := exists_block_basis p.toIsPowGrp hj hv hv' M hM y.v h₃
  refine ⟨constMul y.P.A.hom (a ^ j) y.th, fun s => ?_, w, hw, M', ⟨p, hj, h₁, fun jj b h => ?_, hw'⟩,
    fun _ => rfl, hM', hdet⟩
  · rw [nonzeroLocus_constMul _ (pow_ne_zero j h0).isUnit]
    exact y.th_ne s
  · have h₄ := h₂ jj b h
    have h₅ : ∀ i, ((p.pr i).left.appLE _ _ (h i)).hom (th'.f (jj i)) =
        constFn y.P.A.hom _ a * ((p.pr i).left.appLE _ _ (h i)).hom (th.f (jj i)) := fun i => by
      rw [ha, map_mul, appLE_constFn _ _ _ (Over.w (p.pr i))]
    refine (Finset.prod_congr rfl fun i _ => h₅ i).trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (congrArg (_ * ·) h₄).trans ?_
    have h₆ : resG _ (inf_le_right : (Out.boxLB P.L p.pr).U jj ⊓ y.P.L.U b ≤ _)
        ((constMul y.P.A.hom (a ^ j) y.th).f b) =
        constFn y.P.A.hom _ a ^ j * resG _ inf_le_right (y.th.f b) := by
      rw [← constFn_pow, ← res_constFn y.P.A.hom (inf_le_right : (Out.boxLB P.L p.pr).U jj ⊓ y.P.L.U b ≤ _)]
      exact map_mul _ _ _
    exact (mul_left_comm _ _ _).trans (congrArg (_ * ·) h₆.symm)

end GlobalTheory.PowChange
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KeyPow

theorem IsKeyPow.dim_eq {R : Type} [CommRing R] {y x : KeyIn R} {j : ℕ} (h : IsKeyPow y x j) :
    y.P.g = j * x.P.g := by
  obtain ⟨_, hg, -⟩ := h
  exact hg.symm

theorem exists_int_half {g : ℕ} {a : Fin g → ℂ} (h : ∀ i, a i = 0 ∨ a i = 1 / 2) :
    ∃ n : Fin g → ℤ, a = fun i => (((n i : ℝ) / 2 : ℝ) : ℂ) := by
  have : ∀ i, ∃ m : ℤ, a i = (((m : ℝ) / 2 : ℝ) : ℂ) := fun i => by
    rcases h i with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  choose n hn using this
  exact ⟨n, funext hn⟩

theorem even_dot_double {g g' : ℕ} (e : Fin 2 × Fin g ≃ Fin g') (n n' : Fin g → ℤ) :
    Even ((fun p => n (e.symm p).2) ⬝ᵥ (fun p => n' (e.symm p).2)) := by
  refine ⟨n ⬝ᵥ n', ?_⟩
  unfold dotProduct
  rw [← e.sum_comp]
  simp [Fintype.sum_prod_type, two_mul]

end GlobalTheory.KeyPow
end
