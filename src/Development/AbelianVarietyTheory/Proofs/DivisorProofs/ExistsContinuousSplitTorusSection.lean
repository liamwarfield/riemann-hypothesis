module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryCongruentLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixDetNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoprimeScalarForEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedLatticeColumnLatticeMulIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLeviFlagOfMemParabolic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCoefficientCompatibility
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSplitTorusSection
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.IdTorus

def frameTorMat {A : Type} [CommRing A] (s : A →+* A) {n r : ℕ} (J : Matrix (Fin n) (Fin n) A)
    (X Y : Matrix (Fin n) (Fin r) A) (d : Fin r → Aˣ) : Matrix (Fin n) (Fin n) A :=
  1 + X * diagonal (fun i => (d i : A) - 1) * (cT s Y * J) +
    Y * diagonal (fun i => s ((d i)⁻¹ : Aˣ) - 1) * (cT s X * J)

section Alg

variable {A : Type} [CommRing A] {s : A →+* A} {n r : ℕ} {J : Matrix (Fin n) (Fin n) A}
  {X Y : Matrix (Fin n) (Fin r) A}

theorem diagonal_sub_one' (a : Fin r → A) : diagonal (fun i => a i - 1) = diagonal a - 1 := by
  rw [← diagonal_one, diagonal_sub]

theorem frameTorMat_mul_X (xx : cT s X * J * X = 0) (yx : cT s Y * J * X = 1) (d : Fin r → Aˣ) :
    frameTorMat s J X Y d * X = X * diagonal fun i => (d i : A) := by
  simp only [frameTorMat, Matrix.add_mul, Matrix.mul_assoc _ (cT s Y * J), Matrix.mul_assoc _ (cT s X * J), xx, yx,
    diagonal_sub_one', Matrix.mul_sub]
  simp

theorem frameTorMat_mul_Y (yy : cT s Y * J * Y = 0) (xy : cT s X * J * Y = 1) (d : Fin r → Aˣ) :
    frameTorMat s J X Y d * Y = Y * diagonal fun i => s ((d i)⁻¹ : Aˣ) := by
  simp only [frameTorMat, Matrix.add_mul, Matrix.mul_assoc _ (cT s Y * J), Matrix.mul_assoc _ (cT s X * J), yy, xy,
    diagonal_sub_one', Matrix.mul_sub]
  simp

theorem frameTorMat_mulVec {z : Fin n → A} (hx : (cT s X * J) *ᵥ z = 0) (hy : (cT s Y * J) *ᵥ z = 0)
    (d : Fin r → Aˣ) : frameTorMat s J X Y d *ᵥ z = z := by
  rw [frameTorMat, add_mulVec, add_mulVec, ← mulVec_mulVec, hy, mulVec_zero, ← mulVec_mulVec, hx, mulVec_zero]
  simp

theorem frameTorMat_mul_inv (xx : cT s X * J * X = 0) (yy : cT s Y * J * Y = 0) (xy : cT s X * J * Y = 1)
    (yx : cT s Y * J * X = 1) (d : Fin r → Aˣ) : frameTorMat s J X Y d * frameTorMat s J X Y d⁻¹ = 1 := by
  conv_lhs => rw [show frameTorMat s J X Y d⁻¹ = 1 + _ + _ from rfl, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one]
  simp only [← Matrix.mul_assoc (frameTorMat s J X Y d), frameTorMat_mul_X xx yx, frameTorMat_mul_Y yy xy,
    Matrix.mul_assoc _ (diagonal _) (diagonal _), diagonal_mul_diagonal]
  have h1 : ∀ i, (d i : A) * (((d⁻¹) i : Aˣ) - 1) = 1 - d i := fun i => by
    rw [Pi.inv_apply, mul_sub, Units.mul_inv, mul_one]
  have h2 : ∀ i, s ((d i)⁻¹ : Aˣ) * (s (((d⁻¹) i)⁻¹ : Aˣ) - 1) = 1 - s ((d i)⁻¹ : Aˣ) := fun i => by
    rw [Pi.inv_apply, inv_inv, mul_sub, ← map_mul, Units.inv_mul, map_one, mul_one]
  simp only [h1, h2, frameTorMat, ← diagonal_sub, diagonal_one, Matrix.mul_sub, Matrix.sub_mul]
  abel

theorem frameTorMat_unitary (hs : ∀ a, s (s a) = a) (hJ : cT s J = J) (xx : cT s X * J * X = 0)
    (yy : cT s Y * J * Y = 0) (xy : cT s X * J * Y = 1) (yx : cT s Y * J * X = 1) (d : Fin r → Aˣ) :
    cT s (frameTorMat s J X Y d) * J * frameTorMat s J X Y d = J := by
  have cc : ∀ Z : Matrix (Fin n) (Fin r) A, cT s (cT s Z) = Z := fun Z => Matrix.ext fun i j => hs _
  have cd : ∀ a : Fin r → A, cT s (diagonal a) = diagonal fun i => s (a i) := fun a => by
    ext i j; by_cases h : i = j <;> simp [cT, diagonal, h, eq_comm]
  have ca : ∀ P Q : Matrix (Fin n) (Fin n) A, cT s (P + Q) = cT s P + cT s Q := fun P Q =>
    Matrix.ext fun i j => map_add s _ _
  have hU : cT s (frameTorMat s J X Y d) * J = J * frameTorMat s J X Y d⁻¹ := by
    simp only [frameTorMat, ca, Formalism.UG.cT_mul, Formalism.UG.cT_one, cc, hJ, cd, map_sub, map_one, hs, Pi.inv_apply, inv_inv,
      Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]
    abel
  have hM' : frameTorMat s J X Y d⁻¹ * frameTorMat s J X Y d = 1 := by
    simpa only [inv_inv] using frameTorMat_mul_inv xx yy xy yx d⁻¹
  rw [hU, Matrix.mul_assoc, hM', Matrix.mul_one]

end Alg

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in
theorem continuous_frameTorMat {B : Type} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] {s : B →+* B}
    (hs : Continuous s) {n r : ℕ} (J : Matrix (Fin n) (Fin n) B) (X Y : Matrix (Fin n) (Fin r) B) :
    Continuous (frameTorMat s J X Y) := by
  have h1 : Continuous fun d : Fin r → Bˣ => diagonal fun i => (d i : B) - 1 :=
    Continuous.matrix_diagonal (continuous_pi fun i => (Units.continuous_val.comp (continuous_apply i)).sub continuous_const)
  have h2 : Continuous fun d : Fin r → Bˣ => diagonal fun i => s ((d i)⁻¹ : Bˣ) - 1 :=
    Continuous.matrix_diagonal (continuous_pi fun i =>
      (hs.comp (Units.continuous_coe_inv.comp (continuous_apply i))).sub continuous_const)
  exact (continuous_const.add ((continuous_const.matrix_mul h1).matrix_mul continuous_const)).add
    ((continuous_const.matrix_mul h2).matrix_mul continuous_const)

theorem exists_continuous_isIdTorusElt {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
    {X Y : Matrix (Fin n) (Fin r) E} (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    ∃ t : (Fin r → (AF F ⊗[F] E)ˣ) → GAd σ J, Continuous t ∧ ∀ l, IsIdTorusElt σ J X Y l (t l) := by
  obtain ⟨_, _⟩ := ring_facts (F := F) (E := E)
  set s := sigR (AF F) σ
  have hs : ∀ a, s (s a) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma h x)
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT s (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have c3 : ∀ {a : ℕ} (Z : Matrix (Fin n) (Fin a) E),
      (cT s (adMat F Z) * JR (AF F) J : Matrix (Fin a) (Fin n) (AF F ⊗[F] E)) = adMat F (cT (σ : E →+* E) Z * J) :=
    fun Z => by rw [c1]; simp only [adMat, JR, Matrix.map_mul] <;> rfl
  have c2 : ∀ Z Z' : Matrix (Fin n) (Fin r) E,
      (cT s (adMat F Z) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Z' =
        adMat F (cT (σ : E →+* E) Z * J * Z') := fun Z Z' => by
    rw [c3]; simp only [adMat, Matrix.map_mul]
  have hJ' : cT s (JR (AF F) J) = JR (AF F) J :=
    (c1 J).trans (congrArg (adMat F) (Matrix.ext fun i j => hJ.1 i j))
  have xx : (cT s (adMat F X) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F X = 0 := by
    rw [c2, hW.xx]; exact Matrix.map_zero _ (map_zero _)
  have yy : (cT s (adMat F Y) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Y = 0 := by
    rw [c2, hW.yy]; exact Matrix.map_zero _ (map_zero _)
  have xy : (cT s (adMat F X) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Y = 1 := by
    rw [c2, hW.xy]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have yx : (cT s (adMat F Y) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F X = 1 := by
    rw [c2, GlobalTheory.StdPar.yx h hJ hW]; exact Matrix.map_one _ (map_zero _) (map_one _)
  let M := frameTorMat s (JR (AF F) J) (adMat F X) (adMat F Y)
  have hinv : ∀ d, M d * M d⁻¹ = 1 := frameTorMat_mul_inv xx yy xy yx
  have hinv' : ∀ d, M d⁻¹ * M d = 1 := fun d => by simpa only [inv_inv] using hinv d⁻¹
  let t : (Fin r → (AF F ⊗[F] E)ˣ) → GAd σ J := fun l =>
    ⟨⟨M l, M l⁻¹, hinv l, hinv' l⟩, frameTorMat_unitary hs hJ' xx yy xy yx l⟩
  have hc : Continuous M := continuous_frameTorMat (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ) _ _ _
  refine ⟨t, ?_, fun l => ⟨frameTorMat_mul_X xx yx l, ?_, fun z hz => ?_⟩⟩
  · refine Continuous.subtype_mk ((Units.continuous_iff (f := fun l => (⟨M l, M l⁻¹, hinv l, hinv' l⟩ : GL (Fin n) (AF F ⊗[F] E)))).2 ⟨hc, hc.comp continuous_inv⟩) _
  · refine (frameTorMat_mul_Y yy xy l).trans (congrArg (fun D => adMat F Y * diagonal D) (funext fun k => ?_))
    rw [← map_inv]; rfl
  · have key : ∀ C : Matrix (Fin n) (Fin r) E, z ∈ colPerp σ J C Set.univ →
        (cT s (adMat F C) * JR (AF F) J) *ᵥ z = 0 := fun C hC => by
      rw [c3]
      funext i
      have := (Submodule.mem_iInf _).1 hC i
      simpa using this
    exact frameTorMat_mulVec (key X hz.1) (key Y hz.2) l

end Main

end GlobalTheory.IdTorus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalUnitaryMoveSelfDualToSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalUnitaryMoveSelfDualToSplit
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SplitMove

section General

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.UnRep.FullReps GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
open scoped TensorProduct Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conj_conj (v : Fin n → E) :
    (fun j => IsCMField.complexConj E (IsCMField.complexConj E (v j))) = v :=
  funext fun j => IsCMField.complexConj_apply_apply E (v j)

theorem unimod_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {Λ : GenLat E n} (hU : Λ.Unimod) :
    (conjLat H Λ.La).Unimod := by
  have hr : ∀ x : E, x ∈ (algebraMap (𝓞 E) E).range → IsCMField.complexConj E x ∈ (algebraMap (𝓞 E) E).range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨H.bar a, H.bar_eq a⟩
  intro v
  rw [mem_conjLat, hU]
  constructor
  · intro hv w hw
    have := hr _ (hv _ hw)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_mul, IsCMField.complexConj_apply_apply] using this
  · intro hv w hw
    have := hr _ (hv (fun j => IsCMField.complexConj E (w j)) (by rw [mem_conjLat, conj_conj]; exact hw))
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_mul, IsCMField.complexConj_apply_apply] using this

theorem trivAt_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {Λ : GenLat E n} {N : ℕ} (hT : Λ.TrivAt N) :
    (conjLat H Λ.La).TrivAt N := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  exact ⟨k, hk, conjLat_le H (by rw [← H.bar_eq, map_natCast])
    ⟨(Move.span_smul_le _ _ _).1 h1, (Move.span_smul_le _ _ _).1 h2⟩⟩

theorem congAt_of_congAtA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    {N M : ℕ} (hM : 0 < M) {γ : Matrix (Fin n) (Fin n) E} (h : CongAtA F L N M (fm F γ)) :
    GlobalTheory.UnRep.CongAt L N M γ := by
  obtain ⟨t, ht, h⟩ := h
  have hrat := (hat_rational_points_and_approx F E n L hfg hsp).1
  refine ⟨t, ht, fun v hv => ?_⟩
  obtain ⟨w, hw, e⟩ := h _ ((hrat v).2 hv)
  have hME : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
  have key : t • (γ *ᵥ v - v) = M • ((M : E)⁻¹ • (t • (γ *ᵥ v - v))) := by
    rw [← Nat.cast_smul_eq_nsmul E M, smul_smul, mul_inv_cancel₀ hME, one_smul]
  refine ⟨_, ?_, key⟩
  rw [← hrat]
  have e' : fv F ((M : E)⁻¹ • (t • (γ *ᵥ v - v))) = w := by
    refine Move.nsmul_cancel _ hM ?_
    rw [← cap_fv_nsmul, ← key, cap_fv_nsmul, Move.fv_sub, Move.fv_mulVec, e]
  rw [e']
  exact hw

theorem exists_move_matrix (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (N : ℕ) (hN : 0 < N) (Λ : GenLat E n)
    (hU : Λ.Unimod) (hT : Λ.TrivAt N) :
    ∃ (γ : Matrix (Fin n) (Fin n) E) (h : GL (Fin n) (RA (maximalRealSubfield E) E))
      (Lh : Submodule (𝓞 E) (Fin n → E)), IsUnitaryM γ ∧
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt N (fun i => γ i j) fun i => (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) ∧
      IsUnA (IsCMField.complexConj E) 1 h.1 ∧ SuppSplit (IsCMField.complexConj E) N h.1 ∧
      (Lh : Set (Fin n → E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield E) h.1 (stdLat E n) ∧
      actLat γ Λ = conjLat H Lh := by
  obtain ⟨hherm, hrk, hfg, hsp, -, -, -, hun⟩ := StdInhab.main E H n
  obtain ⟨g, hg, hΛ, hgc⟩ := GlobalTheory.AdelTranslate.exists_adelic_translate E H n N _ hN (unimod_conj H hU)
    (trivAt_conj H hT)
  obtain ⟨γ, h, k, hγ, hh, -, e, hs, hk, hk'⟩ := GlobalTheory.UnRep.exists_rep_suppSplit (maximalRealSubfield E) E
    (IsCMField.complexConj E) n 1 hherm hrk (stdLat E n) hfg hsp g N hg hN
  obtain ⟨Lh, hLh, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf (maximalRealSubfield E) E n (stdLat E n) h hfg hsp
  have hu : adjM γ.1 * γ.1 = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply, ← (hun _).1 hγ i j]
    rfl
  have hu' : γ.1 * adjM γ.1 = 1 := mul_eq_one_comm.1 hu
  have hδ : adjM γ.1ᵀ * γ.1ᵀ = 1 := by
    rw [show adjM γ.1ᵀ = (adjM γ.1)ᵀ from rfl, ← Matrix.transpose_mul, hu', Matrix.transpose_one]
  have hδ' : γ.1ᵀ * adjM γ.1ᵀ = 1 := mul_eq_one_comm.1 hδ
  have ck : CongAtA (maximalRealSubfield E) (stdLat E n) N N (k⁻¹).1 := by
    refine ⟨1, Nat.coprime_one_left _, fun z hz => ?_⟩
    obtain ⟨w, hw, e⟩ := hk _ (hk' z hz)
    refine ⟨-w, neg_mem hw, ?_⟩
    rw [one_smul, smul_neg, ← e, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, neg_sub]
  have ch : CongAtA (maximalRealSubfield E) (stdLat E n) N N (h⁻¹).1 := by
    obtain ⟨ε, -, -, he, hcut⟩ := hs
    obtain ⟨t, ht, hb⟩ := (idempotent_adeles_small_matrices (maximalRealSubfield E) E n (stdLat E n) hfg hsp).2.2.2.1
      N N ε ((h⁻¹).1 - 1) hN fun v hv => by
        by_contra h0
        exact (he v h0).2 hv
    refine ⟨t, ht, fun z hz => ?_⟩
    obtain ⟨w, hw, e⟩ := hb z hz
    rw [cut_inv h _ hcut, Matrix.sub_mulVec, Matrix.one_mulVec] at e
    exact ⟨w, hw, e⟩
  have eγ : fm (maximalRealSubfield E) γ.1 = g.1 * (k⁻¹).1 * (h⁻¹).1 := by
    rw [e, Units.mul_inv_cancel_right, Units.mul_inv_cancel_right]
  have cγ : GlobalTheory.UnRep.CongAt (stdLat E n) N N γ.1 := by
    refine congAt_of_congAtA (F := maximalRealSubfield E) _ hfg hsp hN ?_
    rw [eγ]
    exact LatForm.congAtA_mul _ _ _ _ _ (LatForm.congAtA_mul _ _ _ _ _ (hgc N hN) ck) ch
  have hmove : ∀ u, u ∈ Lh ↔ γ.1 *ᵥ u ∈ (conjLat H Λ.La).La := by
    intro u
    rw [← SetLike.mem_coe, ← SetLike.mem_coe (p := (conjLat H Λ.La).La), hΛ, hLh]
    constructor
    · rintro ⟨z, hz, ez⟩
      refine ⟨_, hk' z hz, ?_⟩
      rw [Move.fv_mulVec, ← ez, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e, Units.mul_inv_cancel_right]
    · rintro ⟨z, hz, ez⟩
      refine ⟨k.1 *ᵥ z, ?_, ?_⟩
      · obtain ⟨w, hw, e⟩ := hk z hz
        rw [sub_eq_iff_eq_add.1 e]
        exact add_mem (nsmul_mem hw _) hz
      · have := congrArg (fun x => fm (maximalRealSubfield E) (γ⁻¹).1 *ᵥ x) ez
        rw [← Move.fv_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, e,
          ← mul_assoc, ← mul_assoc, ← FullReps.fm_mul, Units.inv_mul, FullReps.fm_one, one_mul] at this
        rw [Matrix.mulVec_mulVec, this]
  refine ⟨γ.1ᵀ, h, Lh, hδ, fun j => ?_, hh, hs, hLh, congrArg GenLat.mk (Submodule.ext fun v => ?_)⟩
  · obtain ⟨t, ht, hc⟩ := cγ
    refine ⟨t, ht, fun i => ?_⟩
    obtain ⟨w, hw, ew⟩ := hc _ (StdInhab.single_mem n i)
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hw j trivial)
    refine ⟨b, ?_⟩
    have := congrFun ew j
    rw [Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul, ← hb, Pi.sub_apply,
      Matrix.mulVec_single_one] at this
    refine Eq.trans ?_ this
    congr 2
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Pi.single_apply, Ne.symm hij]
  · have hc : (fun j => IsCMField.complexConj E ((γ.1 *ᵥ fun j => IsCMField.complexConj E (v j)) j)) =
        adjM γ.1ᵀ *ᵥ v := by
      funext j
      simp [Matrix.mulVec, dotProduct, adjM]
    change v ∈ (actLat γ.1ᵀ Λ).La ↔ v ∈ (conjLat H Lh).La
    rw [mem_conjLat, hmove, mem_conjLat, hc]
    constructor
    · rintro ⟨u, hu, rfl⟩
      change adjM γ.1ᵀ *ᵥ (γ.1ᵀ *ᵥ u) ∈ Λ.La
      rw [Matrix.mulVec_mulVec, hδ, Matrix.one_mulVec]
      exact hu
    · intro hv
      refine ⟨_, hv, ?_⟩
      change γ.1ᵀ *ᵥ (adjM γ.1ᵀ *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, hδ', Matrix.one_mulVec]

end General

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_move_to_split : ∀ (D : D7) (V : HSp D), V.gram = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (H : Geo.Tor.Host D.host.E) (N : ℕ), 0 < N → ∀ Λ : GenLat D.host.E V.rank, Λ.Unimod → Λ.TrivAt N → ∃ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (h : GA D V), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.IsUnitaryM γ ∧ (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt N (fun i => γ i j) fun i => (((1 : Matrix (Fin V.rank) (Fin V.rank) (𝓞 D.host.E)) i j : 𝓞 D.host.E) : D.host.E)) ∧ h ∈ GfC V ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V h).1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.actLat γ Λ = GlobalTheory.UnRep.FullReps.conjLat H (Bridge.hLat V (fin V h)) := by
  intro D V hg hL H N hN Λ hU hT
  obtain ⟨γ, h', Lh, h1, h2, h3, h4, h5, h6⟩ := exists_move_matrix H N hN Λ hU hT
  have hc : GlobalTheory.Member.cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨h, hh, eh⟩ := lift h' (by
    rw [show (HSpace.gram V)ᵀ = 1 by rw [hg, Matrix.transpose_one], hc]
    exact h3)
  refine ⟨γ, h, h1, h2, hh, ?_, ?_⟩
  · rw [eh, hc]; exact h4
  · rw [GlobalTheory.SplitReps.hLat_one] at hL
    rw [GlobalTheory.SplitReps.hLat_eq V (FWT.fin V h) Lh (by
      rw [hL]
      change _ = GlobalTheory.AdLat.latOf D.host.F (finHom V h).1 _
      rw [eh]
      exact h5)]
    exact h6

end GlobalTheory.SplitMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalUnitaryMoveSelfDualToSplitStatement
open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalUnitary_move_selfDual_to_split : ∀ (D : D7) (V : HSp D), V.gram = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (H : Geo.Tor.Host D.host.E) (N : ℕ), 0 < N → ∀ Λ : GenLat D.host.E V.rank, Λ.Unimod → Λ.TrivAt N → ∃ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (h : GA D V), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.IsUnitaryM γ ∧ (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt N (fun i => γ i j) fun i => (((1 : Matrix (Fin V.rank) (Fin V.rank) (𝓞 D.host.E)) i j : 𝓞 D.host.E) : D.host.E)) ∧ h ∈ GfC V ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V h).1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.actLat γ Λ = GlobalTheory.UnRep.FullReps.conjLat H (Bridge.hLat V (fin V h)) := by
  first | exact @GlobalTheory.SplitMove.exists_move_to_split | exact GlobalTheory.SplitMove.exists_move_to_split | (intros; apply GlobalTheory.SplitMove.exists_move_to_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFiniteFlat
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IwLevel.HTTorsionFF

theorem exists_gen_idem {R : Type} [CommRing R] [IsDedekindDomain R] (w : Ideal R) (hw : w ≠ ⊥) :
    ∃ α x : R, α ≠ 0 ∧ α ∈ w ∧ x ∈ w ∧ x * x - x ∈ Ideal.span {α} ∧ w = Ideal.span {α, x} := by
  have hw2 : w ^ 2 ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot, pow_eq_zero_iff two_ne_zero, Ideal.zero_eq_bot]; exact hw
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.pow_le_self two_ne_zero : w ^ 2 ≤ w) hw2
  obtain ⟨α, hα0, hα⟩ : ∃ α : R, α ≠ 0 ∧ w ^ 2 ⊔ Ideal.span {α} = w := by
    by_cases h0 : y = 0
    · subst h0
      rw [Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq] at hy
      obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw2
      exact ⟨z, hz0, by rw [sup_eq_left.2 ((Ideal.span_singleton_le_iff_mem _).2 hz), hy]⟩
    · exact ⟨y, h0, hy⟩
  have hαw : α ∈ w := by
    rw [← hα]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self α)
  have hidem : IsIdempotentElem (w.map (Ideal.Quotient.mk (Ideal.span {α}))) := by
    unfold IsIdempotentElem
    conv_rhs => rw [← hα]
    rw [Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq, sq, Ideal.map_mul]
  have hfg : (w.map (Ideal.Quotient.mk (Ideal.span {α}))).FG := Ideal.FG.map (IsNoetherian.noetherian w) _
  obtain ⟨e, he, hwe⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hfg).1 hidem
  have he_mem : e ∈ w.map (Ideal.Quotient.mk (Ideal.span {α})) := by
    rw [hwe]; exact Submodule.mem_span_singleton_self e
  obtain ⟨x, hxw, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 he_mem
  refine ⟨α, x, hα0, hαw, hxw, ?_, le_antisymm (fun c hc => ?_) ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, he.eq, sub_self]
  · have hc' : Ideal.Quotient.mk (Ideal.span {α}) c ∈
        (R ⧸ Ideal.span {α}) ∙ (Ideal.Quotient.mk (Ideal.span {α}) x) := by
      rw [← hwe]; exact Ideal.mem_map_of_mem _ hc
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hc'
    obtain ⟨d', rfl⟩ := Ideal.Quotient.mk_surjective d
    have h1 : c - d' * x ∈ Ideal.span {α} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← smul_eq_mul, hd, sub_self]
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
    have h2 : c = a * α + d' * x := by rw [ha]; ring
    rw [h2]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact hαw
    · exact hxw

theorem ringHom_flat_of_retract {A B C : CommRingCat.{0}} (ψ : A ⟶ C) (σ : C ⟶ B) (π : B ⟶ C)
    (h : σ ≫ π = 𝟙 C) (hf : (ψ ≫ σ).hom.Flat) : ψ.hom.Flat := by
  letI := ψ.hom.toAlgebra
  letI := (ψ ≫ σ).hom.toAlgebra
  have hB : Module.Flat A B := hf
  have hπσ : ∀ z, π.hom (σ.hom z) = z := fun z => by
    rw [← CommRingCat.comp_apply, h, CommRingCat.id_apply]
  show Module.Flat A C
  let s : C →ₗ[A] B :=
    { toFun := σ.hom
      map_add' := map_add _
      map_smul' := fun a c => by
        simp only [Algebra.smul_def, RingHom.id_apply, map_mul, RingHom.algebraMap_toAlgebra,
          CommRingCat.hom_comp, RingHom.comp_apply] }
  let q : B →ₗ[A] C :=
    { toFun := π.hom
      map_add' := map_add _
      map_smul' := fun a c => by
        simp only [Algebra.smul_def, RingHom.id_apply, map_mul, RingHom.algebraMap_toAlgebra,
          CommRingCat.hom_comp, RingHom.comp_apply, hπσ] }
  exact Module.Flat.of_retract s q (LinearMap.ext fun z => hπσ z)

theorem flat_of_retract {X Y S : Scheme.{0}} (f : X ⟶ S) (i : X ⟶ Y) (r : Y ⟶ X) (h : i ≫ r = 𝟙 X)
    [Flat (r ≫ f)] : Flat f := by
  refine Flat.of_stalkMap f fun x => ?_
  have hx : r (i x) = x := by
    rw [← Scheme.Hom.comp_apply, h]; rfl
  haveI : IsIso (i ≫ r) := by rw [h]; infer_instance
  haveI : IsOpenImmersion (i ≫ r) := inferInstance
  haveI : IsIso ((i ≫ r).stalkMap x) := inferInstance
  have key : (f.stalkMap (r (i x))).hom.Flat := by
    have e1 : r.stalkMap (i x) ≫ i.stalkMap x = (i ≫ r).stalkMap x := (Scheme.Hom.stalkMap_comp i r x).symm
    haveI hg : IsIso (r.stalkMap (i x) ≫ i.stalkMap x) := by rw [e1]; exact this
    have e2 : r.stalkMap (i x) ≫ (i.stalkMap x ≫ CategoryTheory.inv (r.stalkMap (i x) ≫ i.stalkMap x)) = 𝟙 _ := by
      rw [← Category.assoc, IsIso.hom_inv_id]
    refine ringHom_flat_of_retract (f.stalkMap (r (i x))) (r.stalkMap (i x)) _ e2 ?_
    · rw [← Scheme.Hom.stalkMap_comp]
      exact Flat.stalkMap (r ≫ f) (i x)
  rwa [hx] at key


open GlobalTheory.UPel.HT in
theorem oActN_natCast {S : Scheme.{0}} {O : Type} [Ring O] {G : Over S} [GrpObj G] (act : OActN O G) (n : ℕ) :
    act.act (n : O) = 𝟙 G ^ n := by
  induction n with
  | zero =>
    have h := act.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    exact left_eq_mul.1 h
  | succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, pow_succ]


open GlobalTheory.UPel.HT in
theorem act_finite_flat {S : Scheme.{0}} [IsLocallyNoetherian S] {F O : Type} [Field F] [NumberField F] [Ring O]
    [Algebra (𝓞 F) O] (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) (act : OActN O A)
    (c : 𝓞 F) (hc : c ≠ 0) :
    IsFinite (act.act (algebraMap (𝓞 F) O c)).left ∧ Flat (act.act (algebraMap (𝓞 F) O c)).left := by
  have he : Ideal.absNorm (Ideal.span {c}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
  have hcomp : act.act (algebraMap (𝓞 F) O c) ≫ act.act (algebraMap (𝓞 F) O a) =
      𝟙 A ^ Ideal.absNorm (Ideal.span {c}) := by
    rw [← act.mul, ← map_mul, ha, map_natCast, oActN_natCast]
  obtain ⟨hfe, -⟩ := GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul S A hA _ (Nat.one_le_iff_ne_zero.2 he)
  have hpr := hA.proper
  have hsm := hA.smooth
  haveI : IsSeparated ((act.act (algebraMap (𝓞 F) O a)).left ≫ A.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated (act.act (algebraMap (𝓞 F) O a)).left := IsSeparated.of_comp _ A.hom
  haveI : IsFinite ((act.act (algebraMap (𝓞 F) O c)).left ≫ (act.act (algebraMap (𝓞 F) O a)).left) := by
    rw [← Over.comp_left, hcomp]; exact hfe
  have hf : IsFinite (act.act (algebraMap (𝓞 F) O c)).left := IsFinite.of_comp _ (act.act (algebraMap (𝓞 F) O a)).left
  refine ⟨hf, GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres S A A _ inferInstance inferInstance hf fun K _ _ t => ?_⟩
  have hm := act.hom (algebraMap (𝓞 F) O c)
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    (Out.TLinPf.isAb_pullback t A hA) _ inferInstance
    (MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) hf)).1


open KerGrp in
theorem exists_torsion_finite_flat : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (w : Ideal (𝓞 D.F)) (S : Scheme.{0}) [IsLocallyNoetherian S]
    (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s), w ≠ ⊥ → ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ o.A),
      IsMonHom i ∧ Mono i ∧ IsFinite K.hom ∧ Flat K.hom ∧ ∀ (T : Over S) (x : T ⟶ o.A),
        GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x := by
  intro p _ D R _ b N w S _ s o hw
  obtain ⟨α, x, hα0, -, -, hxx, hwx⟩ := exists_gen_idem w hw
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hxx
  have hA := o.ab
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O α)
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O x)
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O t)
  have comm : o.act.act (algebraMap (𝓞 D.F) D.O α) ≫ o.act.act (algebraMap (𝓞 D.F) D.O x) =
      o.act.act (algebraMap (𝓞 D.F) D.O x) ≫ o.act.act (algebraMap (𝓞 D.F) D.O α) := by
    rw [← o.act.mul, ← o.act.mul, ← map_mul, ← map_mul, mul_comm]
  have idem : o.act.act (algebraMap (𝓞 D.F) D.O x) ≫ o.act.act (algebraMap (𝓞 D.F) D.O x) =
      o.act.act (algebraMap (𝓞 D.F) D.O x) *
        (o.act.act (algebraMap (𝓞 D.F) D.O α) ≫ o.act.act (algebraMap (𝓞 D.F) D.O t)) := by
    rw [← o.act.mul, ← o.act.mul, ← o.act.add, ← map_mul, ← map_mul, ← map_add (f := _), ht]
    congr 2; ring

  set fα := o.act.act (algebraMap (𝓞 D.F) D.O α) with hfα
  set fx := o.act.act (algebraMap (𝓞 D.F) D.O x) with hfx
  set ft := o.act.act (algebraMap (𝓞 D.F) D.O t) with hft
  obtain ⟨hfinα, hflα⟩ := act_finite_flat o.A hA o.act α hα0
  letI gH : GrpObj (ker fα) := grp fα
  haveI : IsMonHom (pullback.fst fα η[o.A]) := isMonHom_fst fα
  have hPB := (IsPullback.of_hasPullback fα η[o.A]).map (Over.forget S)
  have hHfin : IsFinite (ker fα).hom := by
    rw [← Over.w (pullback.snd fα η[o.A])]
    haveI : IsFinite (pullback.snd fα η[o.A]).left := MorphismProperty.of_isPullback (P := @IsFinite) hPB hfinα
    exact inferInstanceAs (IsFinite (_ ≫ 𝟙 S))
  have hHflat : Flat (ker fα).hom := by
    rw [← Over.w (pullback.snd fα η[o.A])]
    haveI : Flat (pullback.snd fα η[o.A]).left := MorphismProperty.of_isPullback (P := @Flat) hPB hflα
    exact inferInstanceAs (Flat (_ ≫ 𝟙 S))

  set jH := pullback.fst fα η[o.A] with hjH
  have hj : jH ≫ fα = 1 := fst_comp fα
  let g : ker fα ⟶ ker fα := lift fα (jH ≫ fx) (by
    rw [Category.assoc, ← comm, ← Category.assoc, hj, MonObj.one_comp])
  have hg : g ≫ jH = jH ≫ fx := lift_fst _ _ _
  have hxx' : jH ≫ fx ≫ fx = jH ≫ fx := by
    rw [idem, MonObj.comp_mul, ← Category.assoc jH fα ft, hj, MonObj.one_comp, _root_.mul_one]
  letI gK : GrpObj (ker (jH ≫ fx)) := grp (jH ≫ fx)
  haveI : IsMonHom (pullback.fst (jH ≫ fx) η[o.A]) := isMonHom_fst (jH ≫ fx)
  set iK := pullback.fst (jH ≫ fx) η[o.A] with hiK
  have hk : iK ≫ jH ≫ fx = 1 := fst_comp (jH ≫ fx)
  have hrk : (𝟙 (ker fα) / g) ≫ jH ≫ fx = 1 := by
    rw [← Category.assoc, GrpObj.div_comp, Category.id_comp, hg, GrpObj.div_comp, Category.assoc, hxx',
      div_self']
  let r : ker fα ⟶ ker (jH ≫ fx) := lift (jH ≫ fx) (𝟙 (ker fα) / g) hrk
  have hr : r ≫ iK = 𝟙 (ker fα) / g := lift_fst _ _ _
  have hiKg : iK ≫ g = 1 := hom_ext fα (by
    rw [Category.assoc, hg, hk, MonObj.one_comp])
  have hir : iK ≫ r = 𝟙 _ := hom_ext (jH ≫ fx) (by
    rw [Category.assoc, hr, GrpObj.comp_div, Category.comp_id, hiKg, div_one, Category.id_comp])
  have hirl : iK.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, hir, Over.id_left]

  have hKfin : IsFinite (ker (jH ≫ fx)).hom := by
    haveI : IsFinite (r.left ≫ (ker (jH ≫ fx)).hom) := by rw [Over.w r]; exact hHfin
    haveI : IsSeparated (r.left ≫ (ker (jH ≫ fx)).hom) := by rw [Over.w r]; infer_instance
    haveI : IsSeparated r.left := IsSeparated.of_comp _ (ker (jH ≫ fx)).hom
    haveI : IsFinite (iK.left ≫ r.left) := by rw [hirl]; infer_instance
    haveI : IsFinite iK.left := IsFinite.of_comp _ r.left
    rw [← Over.w iK]; infer_instance
  have hKflat : Flat (ker (jH ≫ fx)).hom := by
    haveI : Flat (r.left ≫ (ker (jH ≫ fx)).hom) := by rw [Over.w r]; exact hHflat
    exact flat_of_retract _ iK.left r.left hirl
  refine ⟨ker (jH ≫ fx), gK, iK ≫ jH, inferInstance, inferInstance, hKfin, hKflat, fun T z => ?_⟩
  rw [hwx, Ideal.map_span, Set.image_pair, GlobalTheory.IwLevel.killedBy_span]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, GlobalTheory.IwLevel.htAct_act]
  refine ⟨?_, fun ⟨h1, h2⟩ => ?_⟩
  · rintro ⟨y, rfl⟩
    refine ⟨?_, ?_⟩
    · show ((y ≫ iK) ≫ jH) ≫ fα = 1
      rw [Category.assoc, hj, MonObj.comp_one]
    · show ((y ≫ iK) ≫ jH) ≫ fx = 1
      rw [Category.assoc, Category.assoc, hk, MonObj.comp_one]
  · refine ⟨lift (jH ≫ fx) (lift fα z h1) (by rw [← Category.assoc, KerGrp.lift_fst, h2]), ?_⟩
    rw [← Category.assoc, KerGrp.lift_fst, KerGrp.lift_fst]

end GlobalTheory.IwLevel.HTTorsionFF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsymptoticRiemannRochAmpleCoherent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsymptoticRiemannRochAmpleCoherent
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem abs_factorial_mul_hdim_zero_twist_sub_le_of_isAmpleLB :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ L : LB X, IsAmpleLB L → ∃ C m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → |(d.factorial : ℤ) * (hdim k (twist F (lbPow L m)) 0 : ℤ) - interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  intro k _ _ X _ hp d F _ hd L hL
  obtain ⟨C, hC⟩ := GlobalTheory.T.abs_factorial_mul_eulerChar_twist_pow_sub_le k X hp d F hd L hL.isLB
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1
    (hL.eventually_subsingleton_coh_twist (algebraMap_eq_strHom k X) F)
  refine ⟨C, m₀, fun m hm => ?_⟩
  rw [← chi_eq_hdim_zero k (hm₀ m hm)]
  exact hC m

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsymptoticRiemannRochAmpleCoherentStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.asymptotic_riemannRoch_ample_coherent : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ L : LB X, IsAmpleLB L → ∃ C m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → |(d.factorial : ℤ) * (hdim k (twist F (lbPow L m)) 0 : ℤ) - interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  first | exact @GlobalTheory.abs_factorial_mul_hdim_zero_twist_sub_le_of_isAmpleLB | exact GlobalTheory.abs_factorial_mul_hdim_zero_twist_sub_le_of_isAmpleLB | (intros; apply GlobalTheory.abs_factorial_mul_hdim_zero_twist_sub_le_of_isAmpleLB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGLAdelicProjectionsInclusions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGLAdelicProjectionsInclusions
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory Matrix

namespace GlobalTheory.GLProj

theorem continuous_proj_incl : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pInf E) g) ∧
    Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pFin E) g) ∧
    Continuous (infGL E a) ∧ Continuous (finGL E a) := by
  intro E _ _ _ a
  have hInf : Continuous (pInf E) :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
        ((continuous_apply w).comp continuous_fst)
  have hFin : Continuous (pFin E) := continuous_snd
  refine ⟨Continuous.units_map _ (continuous_id.matrix_map hInf),
    Continuous.units_map _ (continuous_id.matrix_map hFin), continuous_infGL, ?_⟩
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact (continuous_const.add (continuous_id.matrix_map hs) :
    Continuous fun x : Matrix (Fin a) (Fin a) (Af E) => 1 - matN a (sFin E) 1 + x.map (sFin E))

end GlobalTheory.GLProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGLAdelicProjectionsInclusionsStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_GL_adelic_projections_inclusions : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pInf E) g) ∧ Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pFin E) g) ∧ Continuous (infGL E a) ∧ Continuous (finGL E a) := by
  first | exact @GlobalTheory.GLProj.continuous_proj_incl | exact GlobalTheory.GLProj.continuous_proj_incl | (intros; apply GlobalTheory.GLProj.continuous_proj_incl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionIffLocalQuotients
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionIffLocalQuotients
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem le_iff_local : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ A B : HermLB p, Le B A ↔ ∃ (r : A.B.ι → X.functionFieldˣ) (r' : B.B.ι → X.functionFieldˣ), IsRatSec A.B r ∧ IsRatSec B.B r' ∧ (∀ (x : X) i j, x ∈ A.B.U i → x ∈ B.B.U j → RegAt x ((r i : X.functionField) / (r' j : X.functionField))) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (A.B.U i) → y ∈ ptsIn p σ (B.B.U j) → ‖ratVal ((r i : X.functionField) / (r' j : X.functionField)) y‖ * Real.exp (-((A.φ σ).φ i y - (B.φ σ).φ j y) / 2) ≤ 1 := by
  intro k _ X _ p A B
  have hloc : ∀ (P : Pair p) i j, P.loc 1 (-1) 1 i j = (P.r i : X.functionField) / (P.r' j : X.functionField) := by
    intro P i j
    simp [Pair.loc, div_eq_mul_inv]
  have hexp : ∀ s t : ℝ, -(((1 : ℤ) : ℝ) * s + ((-1 : ℤ) : ℝ) * t) / 2 = -(s - t) / 2 := by
    intro s t
    push_cast
    ring
  constructor
  · rintro ⟨P, rfl, rfl, hH, hnu⟩
    refine ⟨P.r, P.r', P.hr, P.hr', fun x i j hi hj => ?_, fun σ y i j hi hj => ?_⟩
    · rw [← hloc]
      exact hH x i j hi hj
    · have e := hnu σ y
      rw [nu_eq k X p P 1 (-1) 1 hH σ y i j hi hj, hloc, hexp] at e
      exact e
  · rintro ⟨r, r', hr, hr', hreg, hnu⟩
    refine ⟨⟨A, B, r, r', hr, hr'⟩, rfl, rfl, fun x i j hi hj => ?_, fun σ y => ?_⟩
    · rw [hloc]
      exact hreg x i j hi hj
    · rw [Pair.nu, hloc, hexp]
      exact hnu σ y _ _ (mem_pick _ y) (mem_pick _ y)

end GlobalTheory.HSNef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionIffLocalQuotientsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ A B : HermLB p, Le B A ↔ ∃ (r : A.B.ι → X.functionFieldˣ) (r' : B.B.ι → X.functionFieldˣ), IsRatSec A.B r ∧ IsRatSec B.B r' ∧ (∀ (x : X) i j, x ∈ A.B.U i → x ∈ B.B.U j → RegAt x ((r i : X.functionField) / (r' j : X.functionField))) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (A.B.U i) → y ∈ ptsIn p σ (B.B.U j) → ‖ratVal ((r i : X.functionField) / (r' j : X.functionField)) y‖ * Real.exp (-((A.φ σ).φ i y - (B.φ σ).φ j y) / 2) ≤ 1 := by
  first | exact @GlobalTheory.HSNef.le_iff_local | exact GlobalTheory.HSNef.le_iff_local | (intros; apply GlobalTheory.HSNef.le_iff_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtAddSmulOfLcAt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtAddSmulOfLcAt
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem kltAt_add_smul_of_lcAt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D : X → ℚ) (δ : ℚ) (x : X), IsQCart D → KltAt p n Δ x → LcAt p n (Δ + D) x → 0 < δ →
      δ ≤ 1 → KltAt p n (Δ + (1 - δ) • D) x := by
  intro X _ _ _ p n hp hn Δ D δ x hD hk hl hδ hδ1
  obtain ⟨η, m, g, hη, hm, hg, hkl⟩ := hk
  obtain ⟨m', f, hm', -, hf⟩ := GlobalTheory.T.exists_localEquation_effectiveQCartierDivisor X p D hD x
  obtain ⟨m₁, g₁, hm₁, h₁, e₁⟩ := GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Δ D η x m m' g f 1 hm hm' hg hf
  obtain ⟨m₂, g₂, hm₂, h₂, e₂⟩ := GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Δ D η x m m' g f (1 - δ) hm hm' hg hf
  rw [one_smul] at h₁
  have hlc := (GlobalTheory.T.logCanonicalAt_iff_of_isLogCanonicalLocalEquation X p n hp hn (Δ + D) η x m₁ g₁ hη hm₁ h₁).1 hl
  refine ⟨η, m₂, g₂, hη, hm₂, h₂, fun E hE => ?_⟩
  have a := hkl E hE
  have b := hlc E hE
  rw [e₁] at b
  rw [e₂]
  set t : ℚ := (E.ord f : ℚ) / m'
  set d := discrep E η m g
  have h1 : -δ < δ * d := by nlinarith
  have h2 : -(1 - δ) ≤ (1 - δ) * (d - 1 * t) := by nlinarith
  nlinarith

end GlobalTheory.PairStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtAddSmulOfLcAtStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kltAt_add_one_sub_smul_of_kltAt_of_lcAt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (δ : ℚ) (x : X), IsQCart D → KltAt p n Δ x → LcAt p n (Δ + D) x → 0 < δ → δ ≤ 1 → KltAt p n (Δ + (1 - δ) • D) x := by
  first | exact @GlobalTheory.PairStep.kltAt_add_smul_of_lcAt | exact GlobalTheory.PairStep.kltAt_add_smul_of_lcAt | (intros; apply GlobalTheory.PairStep.kltAt_add_smul_of_lcAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionFramedPointsIsAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionFramedPointsIsAction
noncomputable section

namespace GlobalTheory.LevelActFromLevel

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem actLev_of_levIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) , R.toLevCh.Is A.μ0 → LawsJ T → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff T.Q.l) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La), LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) c' (fun g => (lev g, (LinearMap.id : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))) := by
  intro D G _ _ Pl0 T0 A T _ R hL hT hO i c' lev hlev
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hpq : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    have h1 := (hT.pins.2.2.2 _ hj).1
    have h2 := D.R.m_add_three_le_k
    rw [h1]
    simp only [Ranks.sigW]
    omega
  have hA : T.Q.l.A.Coprime T.Q.l.M := by rw [hT.pins.2.1.2]; exact Nat.coprime_one_left _
  have hprod := T.Q.l.prod
  have hMb : T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal := by
    refine GlobalTheory.CoverHalf.eq_prod_of_squarefree ?_ _ fun PP => ?_
    · rw [hT.pins.2.1.1] at hprod
      exact (hprod ▸ GlobalTheory.CoverHalf.squarefree_span_g D : Squarefree (T.Q.l.Mb * _)).of_mul_left
    · rw [hL.Pg, hT.half.2, GlobalTheory.CoverHalf.prod_map_le_iff, hO]
      rfl
  have hι : LatEmb (Wc D i) (iotaW T i) := by
    obtain ⟨hr, _, _, _, _, _, _, h, _⟩ := hT.adPin _ hj _ T.good_σ₀
    exact GlobalTheory.LevelActAnyField.latEmb_cast (hT.spaceW _ hj _ T.good_σ₀) hr (rank_Wc i) _ h
  have hM : T.Q.l.M ≠ 0 := by have := T.Q.l.three_le; omega
  obtain ⟨h1, hm⟩ := GlobalTheory.LevelActAnyField.mul_on_half (hL.βW i) (R.datWp i R.triv) (rank_Wc i) (J := Mfr T.Q.l)
    (hMb ▸ hprod) hM hι R.eG.toMonoidHom lev hlev
  exact GlobalTheory.LevelActAnyField.actLaws_of_action_mod hpq hA _ c' lev
    (GlobalTheory.LevelActAnyField.mem_of_half (lev 1 - LinearMap.id) h1)
    fun g g' => GlobalTheory.LevelActAnyField.mem_of_half (lev (g * g') - lev g ∘ₗ lev g') (hm g g')

end GlobalTheory.LevelActFromLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionFramedPointsIsActionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAction_framedPoints_isAction : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) , R.toLevCh.Is A.μ0 → LawsJ T → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff T.Q.l) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La), LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) c' (fun g => (lev g, (LinearMap.id : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))) := by
  first | exact @GlobalTheory.LevelActFromLevel.actLev_of_levIs | exact GlobalTheory.LevelActFromLevel.actLev_of_levIs | (intros; apply GlobalTheory.LevelActFromLevel.actLev_of_levIs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterProjectionFormulaOfHeightProjectionForStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterProjectionFormulaOfHeightProjectionFor
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.Published

theorem arProj_of_heightProjection (H : HeightProjection) : ArProj := by
  intro k _ X Y _ _ p q D hX hY π hπ hg hm
  have key (L : HermLB p) (a : ℝ) (ha : L.IsSelfInter a) :
      (L.pull π hπ).IsSelfInter ((π.residueDegree (genericPoint Y) : ℝ) * a) := by
    obtain ⟨h, hh, rfl⟩ := ha
    have := H k X Y p q D D hX hY π hπ (by
      rw [hg, (genericPoint_spec X).def]
      exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph).trans hX.dim_eq) hm L h hh
    exact (congrArg (fun x => (π.residueDegree (genericPoint Y) : ℝ) * h x) hg) ▸ this
  refine ⟨key, fun ι _ L Φ hΦ => ⟨fun n => ?_, fun P d hd hP => ?_⟩⟩
  · exact (ArInt.isometric_comb_pull L n π hπ).symm.isSelfInter hY (key _ _ (hΦ.1 n))
  · rw [LinearMap.smul_apply, hΦ.2 P d hd hP, smul_zero]

end GlobalTheory.Published
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithInterProjectionFormula_of_heightProjectionFormula : GlobalTheory.Published.HeightProjection → GlobalTheory.Published.ArProj := by
  first | exact @GlobalTheory.Published.arProj_of_heightProjection | exact GlobalTheory.Published.arProj_of_heightProjection | (intros; apply GlobalTheory.Published.arProj_of_heightProjection <;> assumption)
end
