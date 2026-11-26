module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalProductFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConvergenceOfSiegelSet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsRelevantSpace
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.MajTransport

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Groups

variable {n : ℕ} {X : Spc F E n}

theorem mat_mul (a b : UA σ X.J) : mat (a * b) = mat a * mat b := rfl

theorem mat_one : mat (1 : UA σ X.J) = 1 := rfl

theorem mat_inv_mul (a : UA σ X.J) : mat a⁻¹ * mat a = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_mul_inv (a : UA σ X.J) : mat a * mat a⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

theorem at_add {m p : Type} {y z : Matrix m p (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hy : At (evI F) y) (hz : At (evI F) z) :
    At (evI F) (y + z) := by
  intro u hu; rw [smul_add, hy u hu, hz u hu, add_zero]

theorem at_neg {m p : Type} {z : Matrix m p (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hz : At (evI F) z) : At (evI F) (-z) := by
  intro u hu; rw [smul_neg, hz u hu, neg_zero]

theorem at_mul_left {m p q : Type} [Fintype p] (A : Matrix m p (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) {z : Matrix p q (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (hz : At (evI F) z) : At (evI F) (A * z) := by
  intro u hu; rw [← Matrix.mul_smul, hz u hu, Matrix.mul_zero]

theorem at_mul_right {m p q : Type} [Fintype p] {z : Matrix m p (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hz : At (evI F) z)
    (A : Matrix p q (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : At (evI F) (z * A) := by
  intro u hu; rw [← Matrix.smul_mul, hz u hu, Matrix.zero_mul]

theorem uat_mul {a b : UA σ X.J} (ha : a ∈ UAt σ X (evI F)) (hb : b ∈ UAt σ X (evI F)) :
    a * b ∈ UAt σ X (evI F) := by
  have e : mat (a * b) - 1 = (mat a - 1) * mat b + (mat b - 1) := by rw [mat_mul]; noncomm_ring
  show At (evI F) (mat (a * b) - 1)
  rw [e]; exact at_add (at_mul_right ha _) hb

theorem uat_inv {a : UA σ X.J} (ha : a ∈ UAt σ X (evI F)) : a⁻¹ ∈ UAt σ X (evI F) := by
  have e : mat a⁻¹ - 1 = -(mat a⁻¹ * (mat a - 1)) := by
    rw [Matrix.mul_sub, mat_inv_mul, Matrix.mul_one]; abel
  show At (evI F) (mat a⁻¹ - 1)
  rw [e]; exact at_neg (at_mul_left _ ha)

theorem uat_conj {a k : UA σ X.J} (ha : a ∈ UAt σ X (evI F)) (hk : k ∈ UAt σ X (evI F)) :
    a * k * a⁻¹ ∈ UAt σ X (evI F) :=
  uat_mul (uat_mul ha hk) (uat_inv ha)

theorem lines_conj (hσ : ∀ x, σ (σ x) = x) {γ : Multiplicative ℝ →* UA σ X.J} (hγ : γ ∈ Lines σ X)
    {a : UA σ X.J} (ha : a ∈ UAt σ X (evI F)) : (MulAut.conj a).toMonoidHom.comp γ ∈ Lines σ X := by
  let e : UA σ X.J ≃* GAd σ ((1 : E) • X.J.map σ) :=
    MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := X.J) hσ (one_ne_zero : (1 : E) ≠ 0))
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  haveI : ContinuousMul (UA σ X.J) := ⟨by
    have h3 : (fun p : UA σ X.J × UA σ X.J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2) :=
      funext fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]
    rw [h3]
    exact he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))⟩
  refine ⟨?_, fun t => ?_⟩
  · show Continuous fun t => a * γ t * a⁻¹
    exact (continuous_const.mul hγ.1).mul continuous_const
  · exact uat_conj ha (hγ.2 t)

theorem map_mul_inv (π : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* ℂ) (a : UA σ X.J) : (mat a).map π * (mat a⁻¹).map π = 1 := by
  rw [← Matrix.map_mul, mat_mul_inv, Matrix.map_one _ (map_zero π) (map_one π)]

theorem map_inv_mul (π : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* ℂ) (a : UA σ X.J) : (mat a⁻¹).map π * (mat a).map π = 1 := by
  rw [← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero π) (map_one π)]

end Groups

section Mat

variable {m : Type} [Fintype m] [DecidableEq m]

theorem comm_conj {A A' K θ θ' : Matrix m m ℂ} (h1 : A * A' = 1) (h2 : A' * A = 1) (h : A * θ = θ' * A)
    (hk : Commute K θ) : Commute (A * K * A') θ' := by
  have e : θ' = A * θ * A' := by rw [h, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [e]
  show A * K * A' * (A * θ * A') = A * θ * A' * (A * K * A')
  calc A * K * A' * (A * θ * A') = A * (K * θ) * A' := by
        simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc A' A, h2, Matrix.one_mul]
    _ = A * (θ * K) * A' := by rw [hk.eq]
    _ = A * θ * A' * (A * K * A') := by
        simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc A' A, h2, Matrix.one_mul]

theorem rev_conj {A A' θ θ' : Matrix m m ℂ} (h1 : A * A' = 1) (h2 : A' * A = 1) (h : A * θ = θ' * A) :
    A' * θ' = θ * A' := by
  calc A' * θ' = A' * θ' * (A * A') := by rw [h1, Matrix.mul_one]
    _ = A' * (θ' * A) * A' := by simp only [Matrix.mul_assoc]
    _ = (A' * A) * θ * A' := by rw [← h]; simp only [Matrix.mul_assoc]
    _ = θ * A' := by rw [h2, Matrix.one_mul]

end Mat

section KInf

variable {n : ℕ} {X Y : Spc F E n}

theorem kinf_conj (τ : ∀ w : InfinitePlace F, EmbOver E w) {a : UA σ X.J} (ha : a ∈ UAt σ X (evI F))
    (hθ : ∀ w, (mat a).map (piInf (τ w)) * X.θ w = Y.θ w * (mat a).map (piInf (τ w))) {k : UA σ X.J}
    (hk : k ∈ KInf σ X τ) : a * k * a⁻¹ ∈ KInf σ (reS X Y) τ := by
  refine ⟨uat_conj ha hk.1, fun w => ?_⟩
  show Commute ((mat (a * k * a⁻¹)).map (piInf (τ w))) (Y.θ w)
  rw [mat_mul, mat_mul, Matrix.map_mul, Matrix.map_mul]
  exact comm_conj (map_mul_inv _ a) (map_inv_mul _ a) (hθ w) (hk.2 w)

end KInf

section Acts

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem pres_of {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E} {om : Rep σ X W}
    (h : M.IsWeil ψ χX χW om) : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) :=
  fun x Φ hΦ => (IsUWeilPair.isUSplitting h).pres x Φ hΦ

theorem acts_conj {om : Rep σ X W}
    (pres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d))
    {p : UA σ X.J × UA σ W.J} {T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d)}
    (hT : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om p) f (T f))
    (hT' : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om p⁻¹) f (T.symm f))
    {q : UA σ X.J × UA σ W.J} {f f₁ : SInf F (Fin n × Fin d)} (h : Acts (evI F) (om q) f f₁) :
    Acts (evI F) (om (p * q * p⁻¹)) (T f) (T f₁) := by
  intro r hr
  have e0 : om p⁻¹ (tens (evI F) (T f) r) = tens (evI F) f r := by
    have := hT' (T f) r hr
    rwa [LinearEquiv.symm_apply_apply] at this
  have hr0 : Rest (evI F) (⇑f) r := ⟨hr.1, e0 ▸ pres _ _ hr.2⟩
  have e1 := h r hr0
  have hr1 : Rest (evI F) (⇑f₁) r := ⟨hr.1, e1 ▸ pres _ _ hr0.2⟩
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e0, e1]
  exact hT f₁ r hr1

end Acts

section Pol

variable {n d : ℕ} {X₁ X₂ : Spc F E n} {W₁ W₂ : Spc F E d}

theorem gauss_mem {M : Model σ X₁ W₁} {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w}
    {f₀ : SInf F (Fin n × Fin d)} (h : M.IsGauss ψ τ f₀) : f₀ ∈ M.Pol ψ τ :=
  Submodule.mem_sInf.2 fun _ hN => hN.1 f₀ h

theorem pol_stab {M : Model σ X₁ W₁} {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w} {u}
    (hu : At (evI F) u) {f f₁ : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ)
    (h : ActsD (evI F) (M.heisLine ψ u) f f₁) : f₁ ∈ M.Pol ψ τ :=
  Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h

theorem pol_le (M₁ : Model σ X₁ W₁) (M₂ : Model σ X₂ W₂) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))
    (φ : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (AE F E))
    (hAt : ∀ u, At (evI F) u → At (evI F) (φ u))
    (hD : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M₁.heisLine ψ u) f f₁ →
      ActsD (evI F) (M₂.heisLine ψ (φ u)) (T f) (T f₁))
    (hG : ∀ f₀, M₁.IsGauss ψ τ f₀ → M₂.IsGauss ψ τ (T f₀)) :
    M₁.Pol ψ τ ≤ (M₂.Pol ψ τ).comap T :=
  sInf_le ⟨fun f₀ hf₀ => gauss_mem (hG f₀ hf₀),
    fun u hu f hf f₁ hf₁ => pol_stab (hAt u hu) hf (hD u hu f f₁ hf₁)⟩

theorem gauss_transport (M₁ : Model σ X₁ W₁) (M₂ : Model σ X₂ W₂) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d))
    (A : Matrix (Fin n) (Fin n) (AE F E)) (C : Matrix (Fin d) (Fin d) (AE F E))
    (hD : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M₂.heisLine ψ u) f f₁ →
      ActsD (evI F) (M₁.heisLine ψ (A * u * C.transpose)) (T.symm f) (T.symm f₁))
    (hX : ∀ w, A.map (piInf (τ w)) * X₂.θ w = X₁.θ w * A.map (piInf (τ w)))
    (hW : ∀ w, C.map (piInf (τ w)) * W₂.θ w = W₁.θ w * C.map (piInf (τ w)))
    {f₀ : SInf F (Fin n × Fin d)} (hf₀ : M₁.IsGauss ψ τ f₀) : M₂.IsGauss ψ τ (T f₀) := by
  obtain ⟨ε, hε⟩ := hf₀
  refine ⟨ε, fun u u' hu hu' huu f f' hf hf' => ?_⟩
  have h1 := hD u hu _ _ hf
  have h2 := hD u' hu' _ _ hf'
  rw [LinearEquiv.symm_apply_apply] at h1 h2
  have key := hε (A * u * C.transpose) (A * u' * C.transpose) (at_mul_right (at_mul_left _ hu) _)
    (at_mul_right (at_mul_left _ hu') _) (fun w => ?_) _ _ h1 h2
  · have := congrArg T key
    simpa using this
  · have eA := hX w
    have eC := hW w
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map,
      Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc A.map (piInf (τ w)) * (X₂.θ w * u.map (piInf (τ w)) * (W₂.θ w).transpose) * (C.map (piInf (τ w))).transpose
        = (A.map (piInf (τ w)) * X₂.θ w) * u.map (piInf (τ w)) * (C.map (piInf (τ w)) * W₂.θ w).transpose := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [eA, eC, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]

end Pol

section Pair

variable {n d : ℕ} {X Y : Spc F E n} {W Z : Spc F E d}

def reM (M : Model σ X W) (Y : Spc F E n) (Z : Spc F E d) : Model σ (reS X Y) (reS W Z) :=
  ⟨M.co, M.vac, M.μ, M.dom⟩

theorem rest_pure {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ)
    (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    Rest (evI F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  refine ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
  have hz0 : ∀ v i, evFin F v (z i) = 0 := fun v i => by
    have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
    have h2 : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
    rw [one_mul] at h2
    rw [evFin, AlgHom.comp_apply]
    convert map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)
    exact h2
  simp only [Pi.add_apply, map_add (f := _), hz0, add_zero]

theorem pair_pol {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ)
    (hw : M.IsWeil B.ψ χX χW om) {g : UA σ X.J} {h : UA σ W.J} (hg : g ∈ UAt σ X (evI F))
    (hh : h ∈ UAt σ W (evI F)) {T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d)}
    (hT1 : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f))
    (hT2 : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f))
    (hθX : ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)))
    (hθW : ∀ w, (mat h).map (piInf (B.emb w)) * W.θ w = Z.θ w * (mat h).map (piInf (B.emb w))) :
    (M.Pol B.ψ B.emb).map (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) = (reM M Y Z).Pol B.ψ B.emb := by
  have hfw := GlobalTheory.T.archimedeanWeilOperator_transports_heisenbergLineDerivative F E σ B n d X W M χX χW om r s r' s' hB hX hW hM hw g hg h hh T hT1 hT2
  have hbw := GlobalTheory.T.archimedeanWeilOperator_transports_heisenbergLineDerivative F E σ B n d X W M χX χW om r s r' s' hB hX hW hM hw g⁻¹ (uat_inv hg) h⁻¹ (uat_inv hh) T.symm
    hT2 (fun f => by simpa only [inv_inv, LinearEquiv.symm_symm] using hT1 f)
  have hX' : ∀ w, (mat g⁻¹).map (piInf (B.emb w)) * Y.θ w = X.θ w * (mat g⁻¹).map (piInf (B.emb w)) :=
    fun w => rev_conj (map_mul_inv _ g) (map_inv_mul _ g) (hθX w)
  have hW' : ∀ w, (mat h⁻¹).map (piInf (B.emb w)) * Z.θ w = W.θ w * (mat h⁻¹).map (piInf (B.emb w)) :=
    fun w => rev_conj (map_mul_inv _ h) (map_inv_mul _ h) (hθW w)
  have le1 : M.Pol B.ψ B.emb ≤ ((reM M Y Z).Pol B.ψ B.emb).comap (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) :=
    pol_le M (reM M Y Z) B.ψ B.emb T (fun u => mat g * u * (mat h).transpose)
      (fun u hu => at_mul_right (at_mul_left _ hu) _) hfw
      (fun f₀ hf₀ => gauss_transport M (reM M Y Z) B.ψ B.emb T (mat g⁻¹) (mat h⁻¹) hbw hX' hW' hf₀)
  have le2 : (reM M Y Z).Pol B.ψ B.emb ≤ (M.Pol B.ψ B.emb).comap (T.symm : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) :=
    pol_le (reM M Y Z) M B.ψ B.emb T.symm (fun u => mat g⁻¹ * u * (mat h⁻¹).transpose)
      (fun u hu => at_mul_right (at_mul_left _ hu) _) hbw
      (fun f₀ hf₀ => gauss_transport (reM M Y Z) M B.ψ B.emb T.symm (mat g) (mat h)
        (fun u hu f f₁ hf => hfw u hu f f₁ hf)
        hθX hθW hf₀)
  refine le_antisymm (Submodule.map_le_iff_le_comap.2 le1) fun f' hf' => ⟨T.symm f', le2 hf', by simp⟩

end Pair

end GlobalTheory.MajTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowCharacterTimesInverseUnitary
open NumberField

noncomputable section

namespace GlobalTheory.CovTop

open Formalism.L2.DIV

theorem prod_hom_pow_eq_one {H M ι : Type} [Group H] [CommMonoid M] (s : Finset ι) (f : ι → H →* M) (N : ℕ)
    (h : ∀ i x, f i x ^ N = 1) (x : H) : (∏ i ∈ s, f i) x ^ N = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have ih' : (∏ i ∈ s, f i x) ^ N = 1 := by simpa using ih
    simp [hi, mul_pow, h, ih']

theorem ofLocal_chi_pow {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]
    (Hl : (PP : Pg) → Subgroup (GL (Fin r) (kP PP.1))) (cl : (PP : Pg) → Hl PP →* LLˣ) (N : ℕ)
    (h : ∀ PP x, cl PP x ^ N = 1) (g : (LevelP.ofLocal Hl cl).H) : (LevelP.ofLocal Hl cl).chi g ^ N = 1 :=
  prod_hom_pow_eq_one (H := Subgroup.pi Set.univ Hl) Finset.univ _ N (fun PP x => h PP _) g

theorem unipotentTypeLevel_char_pow_eq_one {E : Type} [Field E] [NumberField E] {LL : Type} [CommRing LL] (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : (PP : Pl E) → AddChar (kP PP) LL) (N : ℕ) (hN : ∀ PP : Pg, (N : kP PP.1) = 0)
    (g : (P0 Pg r ψ).H) : (P0 Pg r ψ).chi g ^ N = 1 := by
  refine ofLocal_chi_pow _ _ N (fun PP x => ?_) g
  apply Units.ext
  simp only [addCharHom, Units.val_pow_eq_pow_val, MonoidHom.coe_toHomUnits, Units.val_one, MonoidHom.comp_apply,
    AddChar.toMonoidHom_apply]
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hN PP, zero_mul, AddChar.map_zero_eq_one]

theorem det_of_mem_unip {κ : Type} [CommRing κ] {r : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unip κ r) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
    Matrix.det_of_upperTriangular (fun i j hij => hg.1 hij)]
  exact Finset.prod_eq_one fun i _ => hg.2 i

variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

end GlobalTheory.CovTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtWAtPlSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.BigDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

noncomputable def atW (w : Pl D.host.E) : AE D →+* Kw w := (cpt w).comp (toEAf D)

theorem atW_apply (w : Pl D.host.E) (a : AE D) : atW w a = cpt w (toEAf D a) := rfl

theorem atW_atPl_self (w : Pl D.host.E) (x : Kw w) : atW w (atPl w x) = x := by
  classical
  rw [atW_apply, (atPl_spec w x).2 w, Pi.single_eq_same]

theorem atW_atPl_ne {w w' : Pl D.host.E} (h : w ≠ w') (x : Kw w') : atW w (atPl w' x) = 0 := by
  classical
  rw [atW_apply, (atPl_spec w' x).2 w, Pi.single_eq_of_ne h]

theorem atPl_one_mul (w : Pl D.host.E) (z : Kw w) : atPl w 1 * atPl w z = atPl w z := by
  classical
  refine ae_ext (by rw [map_mul, (atPl_spec w 1).1, zero_mul, (atPl_spec w z).1]) fun Q => ?_
  rw [map_mul, map_mul, (atPl_spec w 1).2 Q, (atPl_spec w z).2 Q]
  by_cases h : Q = w
  · subst h; rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, zero_mul]

namespace CoordinateMaps

variable (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m)
  (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m)

theorem coord_add (y y' : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (Kw w)) :
    B.coord t w hX hY (y + y') = B.coord t w hX hY y + B.coord t w hX hY y' := by
  unfold Frames.coord
  rw [Matrix.mul_add, Matrix.add_mul]
  rfl

theorem coord_zero : B.coord t w hX hY 0 = 0 := by
  unfold Frames.coord
  rw [Matrix.mul_zero, Matrix.zero_mul]
  rfl

theorem coord_surj (z : Matrix (Fin ((locGrid G t w).rank Y)) (Fin ((locGrid G t w).rank X)) (Kw w)) :
    ∃ y, B.coord t w hX hY y = z := by
  refine ⟨(loc w (B.β X.1 X.2)).val * (zᵀ.submatrix (Fin.cast (rank_vertex G t w hX).symm)
    (Fin.cast (rank_vertex G t w hY).symm)) * ((loc w (B.β Y.1 Y.2))⁻¹).val, ?_⟩
  unfold Frames.coord
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
    Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  ext a b
  simp only [transpose_apply, submatrix_apply, Fin.cast_cast, Fin.cast_eq_self]

end CoordinateMaps

end GlobalTheory.BigDat

namespace GlobalTheory.BigDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem map_atW_smul (w : Pl D.host.E) {m n : Type} (M : Matrix m n (AE D)) :
    (atPl w 1 • M).map (atW w) = M.map (atW w) := by
  refine Matrix.ext fun a b => ?_
  rw [map_apply, map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, atW_atPl_self, one_mul]

theorem mixCo_eq (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E) (u : Pt G i j) :
    mixCo B t e w u = fromCols (B.coord t w (X := (i, j + 1)) (Y := (i + 1, j + 1)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩
      ((mapV e u).map (atW w)))
      (B.coord t w (X := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩ ((mapW e u).map (atW w)))ᵀ := rfl

theorem mixCo_spec : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (B : Frames G) (t : T)
    (i j : Fin D.R.m) (e : Num G i j) (w : Pl D.host.E),
    (∀ u x : Pt G i j, mixCo B t e w (u + x) = mixCo B t e w u + mixCo B t e w x) ∧
    (∀ z, ∃ x ∈ mixHalf e (atPl w 1), mixCo B t e w x = z) ∧
    (∀ u : Pt G i j, mixCo B t e w (ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u)) = mixCo B t e w u) ∧
    ∀ w' : Pl D.host.E, w' ≠ w → ∀ x ∈ mixHalf e (atPl w' 1), mixCo B t e w x = 0 := by
  intro D T L sc G B t i j e w
  refine ⟨fun u x => ?_, fun z => ?_, fun u => ?_, fun w' hw x hx => ?_⟩
  · rw [mixCo_eq, mixCo_eq, mixCo_eq, mapV_add, mapW_add, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _),
      CoordinateMaps.coord_add, CoordinateMaps.coord_add, transpose_add]
    exact Matrix.ext fun a b => by rcases b with b | b <;> rfl
  · obtain ⟨y₁, hy₁⟩ := CoordinateMaps.coord_surj B t w (X := (i, j + 1)) (Y := (i + 1, j + 1)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩
      z.toCols₁
    obtain ⟨y₂, hy₂⟩ := CoordinateMaps.coord_surj B t w (X := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
      z.toCols₂ᵀ
    let x₁ : HomV G i j := y₁.map (atPl w)
    let x₂ : HomW G i j := y₂.map (atPl w)
    have k₁ : mapV e (ofMaps e (x₁, x₂)) = x₁ := mapV_ofMaps e _
    have k₂ : mapW e (ofMaps e (x₁, x₂)) = x₂ := mapW_ofMaps e _
    have m₁ : x₁.map (atW w) = y₁ := Matrix.ext fun a b => atW_atPl_self w _
    have m₂ : x₂.map (atW w) = y₂ := Matrix.ext fun a b => atW_atPl_self w _
    refine ⟨ofMaps e (x₁, x₂), ⟨?_, ?_⟩, ?_⟩
    · show IsHalf _ (mapV e _)
      rw [k₁]
      intro a b
      exact atPl_one_mul w _
    · show IsHalf _ (mapW e _)
      rw [k₂]
      intro a b
      exact atPl_one_mul w _
    · rw [mixCo_eq, k₁, k₂, m₁, m₂, hy₁, hy₂, transpose_transpose, fromCols_toCols]
  · have k₁ : mapV e (ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u)) = atPl w 1 • mapV e u := mapV_ofMaps e _
    have k₂ : mapW e (ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u)) = atPl w 1 • mapW e u := mapW_ofMaps e _
    rw [mixCo_eq, mixCo_eq, k₁, k₂, map_atW_smul, map_atW_smul]
  · have h₁ : (mapV e x).map (atW w) = 0 := by
      refine Matrix.ext fun a b => ?_
      calc atW w (mapV e x a b) = atW w (atPl w' 1 * mapV e x a b) := congrArg _ (hx.1 a b).symm
        _ = 0 := by rw [map_mul, atW_atPl_ne hw.symm, zero_mul]
    have h₂ : (mapW e x).map (atW w) = 0 := by
      refine Matrix.ext fun a b => ?_
      calc atW w (mapW e x a b) = atW w (atPl w' 1 * mapW e x a b) := congrArg _ (hx.2 a b).symm
        _ = 0 := by rw [map_mul, atW_atPl_ne hw.symm, zero_mul]
    rw [mixCo_eq, h₁, h₂, CoordinateMaps.coord_zero, CoordinateMaps.coord_zero, transpose_zero, fromCols_zero]

end GlobalTheory.BigDat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenSeparating
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Topology

namespace GlobalTheory.FinSepChar

variable {F : Type} [Field F] [NumberField F]

theorem pairA_zero_zero : pairA F 0 (0 : Af F) = 0 := Prod.ext rfl rfl

theorem pairA_zero_neg (b : Af F) : pairA F 0 (-b) = -pairA F 0 b :=
  Prod.ext (neg_zero (G := Ainf F)).symm rfl

theorem algebraMap_mul_inv {a : F} (ha : a ≠ 0) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) a * algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ ha, map_one]

def ann (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) :
    AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1}
  zero_mem' := fun y _ => by
    show ψ (pairA F 0 (0 ⬝ᵥ y)) = 1
    rw [zero_dotProduct, pairA_zero_zero, AddChar.map_zero_eq_one]
  add_mem' := fun {a b} ha hb y hy => by
    show ψ (pairA F 0 ((a + b) ⬝ᵥ y)) = 1
    rw [add_dotProduct, GlobalTheory.AnnCompactStd.pairA_zero_add, AddChar.map_add_eq_mul, ha y hy, hb y hy, mul_one]
  neg_mem' := fun {a} ha y hy => by
    show ψ (pairA F 0 ((-a) ⬝ᵥ y)) = 1
    rw [neg_dotProduct, pairA_zero_neg, AddChar.map_neg_eq_inv, ha y hy, inv_one]

theorem mem_ann {ψ : AddChar (AF F) ℂ} {κ : Type} [Fintype κ] {L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)}
    {x : κ → FiniteAdeleRing (𝓞 F) F} : x ∈ ann ψ κ L ↔ ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1 := Iff.rfl

def scaledInt (κ : Type) (a : FiniteAdeleRing (𝓞 F) F) : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {y | ∀ i, a * y i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F}
  zero_mem' := fun i => by
    show a * 0 ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F
    rw [mul_zero]; exact Subring.zero_mem _
  add_mem' := fun {u v} hu hv i => by
    show a * (u i + v i) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F
    rw [mul_add]; exact Subring.add_mem _ (hu i) (hv i)
  neg_mem' := fun {u} hu i => by
    show a * (-u i) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F
    rw [mul_neg]; exact Subring.neg_mem _ (hu i)

theorem isOpen_scaledInt (κ : Type) [Fintype κ] (a : FiniteAdeleRing (𝓞 F) F) :
    IsOpen (scaledInt κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have h : (scaledInt κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      ⋂ i, (fun y : κ → FiniteAdeleRing (𝓞 F) F => a * y i) ⁻¹'
        (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) := by
    ext y; simp only [Set.mem_iInter, Set.mem_preimage]; exact Iff.rfl
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    GroundTheory.Global.isOpen_integralFiniteAdeles.preimage (continuous_const.mul (continuous_apply i))

end GlobalTheory.FinSepChar

namespace GlobalTheory.FinSepChar

variable {F : Type} [Field F] [NumberField F]

theorem exists_compact_open_separating {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (κ : Type) [Fintype κ]
    {N : Set (κ → Af F)} (hN : N ∈ 𝓝 (0 : κ → Af F)) : ∃ U : AddSubgroup (κ → Af F),
      IsOpen (U : Set (κ → Af F)) ∧ IsCompact (U : Set (κ → Af F)) ∧ (U : Set (κ → Af F)) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ y : κ → Af F, (∀ u ∈ U, ψ (pairA F 0 (u ⬝ᵥ y)) = 1) ∧ ψ (pairA F 0 (x₀ ⬝ᵥ y)) ≠ 1 := by
  classical
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hsub⟩ := hN
  have hW : (⋂ i, t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.mpr ht
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.AnnCompactStd.exists_mul_mem_of_forall hψ
  obtain ⟨e, he0, he⟩ := GlobalTheory.AnnCompactStd.exists_psi_fin_trivial hψ
  have hinj : ∀ a : 𝓞 F, a ≠ 0 → algebraMap (𝓞 F) F a ≠ 0 := fun a ha =>
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ha
  set cc := algebraMap (𝓞 F) F c with hcc
  set dd := algebraMap (𝓞 F) F d with hdd
  set ee := algebraMap (𝓞 F) F e with hee
  have hC := algebraMap_mul_inv (F := F) (hinj c hc0)
  have hD := algebraMap_mul_inv (F := F) (hinj d hd0)
  have hE := algebraMap_mul_inv (F := F) (hinj e he0)
  set ι := algebraMap F (FiniteAdeleRing (𝓞 F) F) with hι
  set O := GroundTheory.Global.integralFiniteAdeles (𝓞 F) F with hO

  set L := scaledInt (F := F) κ (ι cc * ι dd) with hL
  have hLo : IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) := isOpen_scaledInt κ _
  refine ⟨ann ψ κ L, ?_, ?_, ?_, ?_⟩
  ·
    set δ := ι ee⁻¹ * (ι cc⁻¹ * ι dd⁻¹) with hδ
    have hVo : IsOpen (scaledInt (F := F) κ δ : Set (κ → FiniteAdeleRing (𝓞 F) F)) := isOpen_scaledInt κ _
    have hVU : (scaledInt (F := F) κ δ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ ann ψ κ L := by
      intro x hx y hy
      have hsum : x ⬝ᵥ y = ι ee * ∑ i, (δ * x i) * ((ι cc * ι dd) * y i) := by
        rw [dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hδ]
        linear_combination (-(x i * y i * (ι cc * ι dd) * (ι cc⁻¹ * ι dd⁻¹))) * hE
          + (-(x i * y i * ι dd * ι dd⁻¹)) * hC + (-(x i * y i)) * hD
      rw [hsum]
      exact he _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hx i) (hy i))
    exact AddSubgroup.isOpen_of_mem_nhds _
      (Filter.mem_of_superset (hVo.mem_nhds (scaledInt (F := F) κ δ).zero_mem) hVU)
  · exact GlobalTheory.AnnCompactStd.isCompact_annihilator F ψ hψ κ L hLo
  · intro x hx
    apply hsub
    intro i _
    have hz : ∀ s ∈ O, ψ (pairA F 0 ((ι cc⁻¹ * ι dd⁻¹ * x i) * s)) = 1 := by
      intro s hs
      have hy : (Pi.single i (ι cc⁻¹ * ι dd⁻¹ * s) : κ → FiniteAdeleRing (𝓞 F) F) ∈ L := by
        intro k
        by_cases hk : k = i
        · subst hk
          rw [Pi.single_eq_same]
          have : ι cc * ι dd * (ι cc⁻¹ * ι dd⁻¹ * s) = s := by
            linear_combination (ι dd * ι dd⁻¹ * s) * hC + s * hD
          rw [this]; exact hs
        · rw [Pi.single_eq_of_ne hk, mul_zero]; exact Subring.zero_mem _
      have h1 := hx _ hy
      rw [dotProduct_single] at h1
      rw [show ι cc⁻¹ * ι dd⁻¹ * x i * s = x i * (ι cc⁻¹ * ι dd⁻¹ * s) by ring]
      exact h1
    have h2 := hc _ hz
    have h3 := hd _ h2
    have h4 : ι dd * (ι cc * (ι cc⁻¹ * ι dd⁻¹ * x i)) = x i := by
      linear_combination (ι dd * ι dd⁻¹ * x i) * hC + x i * hD
    rw [h4] at h3
    exact Set.mem_iInter.mp h3 i
  · intro x₀ hx₀
    rw [mem_ann] at hx₀
    push_neg at hx₀
    obtain ⟨y, hy, hne⟩ := hx₀
    exact ⟨y, fun u hu => hu y hy, hne⟩

end GlobalTheory.FinSepChar

theorem GlobalTheory.FinSepChar.finite_chars_separate : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ], ∀ N ∈ nhds (0 : κ → Af F), ∃ U : AddSubgroup (κ → Af F),
      IsOpen (U : Set (κ → Af F)) ∧ IsCompact (U : Set (κ → Af F)) ∧ (U : Set (κ → Af F)) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ y : κ → Af F, (∀ u ∈ U, ψ (pairA F 0 (u ⬝ᵥ y)) = 1) ∧ ψ (pairA F 0 (x₀ ⬝ᵥ y)) ≠ 1 :=
  fun _ _ _ _ hψ κ _ _ hN => GlobalTheory.FinSepChar.exists_compact_open_separating hψ κ hN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatPtLeClosureAndSelfDual
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.BigDatLat

open GlobalTheory.LatVac

variable {D : D7}

theorem smul_eq_of_at {M : Type} [AddCommGroup M] [Module (AF D.host.F) M] {v : Pl D.host.F} {z : M}
    (h : At (evFin D.host.F v) z) : liftV v (1 : Fv D.host.F v) • z = z := by
  have h1 := h (1 - liftV v 1) (by rw [map_sub, map_one, evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1.symm

theorem at_smul {M : Type} [AddCommGroup M] [Module (AF D.host.F) M] (v : Pl D.host.F) (z : M) :
    At (evFin D.host.F v) (liftV v (1 : Fv D.host.F v) • z) := fun u hu => by
  rw [smul_smul, ← smul_eq_mul u, at_liftV v 1 u hu, zero_smul]

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z :=
  map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) c z

theorem symplO_swap (S T : HSp D) (c : AF D.host.F) (x y : WO S T) : symplO S T x (c • y) = symplO S T (c • x) y := by
  have h : hO S T x (c • y) = hO S T (c • x) y := by
    unfold hO
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_
    rw [Matrix.smul_apply, Matrix.smul_apply, cA_smul, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
  unfold symplO
  rw [h]

theorem infPart_smul (v : Pl D.host.F) (z : AE D) : infPart D (liftV v (1 : Fv D.host.F v) • z) = 0 := by
  rw [Algebra.smul_def, RingHom.map_mul]
  have : infPart D (algebraMap (AF D.host.F) (AE D) (liftV v (1 : Fv D.host.F v))) = 0 := infPart_pair _ _
  rw [this, zero_mul]

theorem smul_mem {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} (v : Pl D.host.F)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    liftV v (1 : Fv D.host.F v) • u ∈ latO S T LS LT fun _ => True := by
  refine latO_induction (p := fun u => liftV v (1 : Fv D.host.F v) • u ∈ latO S T LS LT fun _ => True) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    have h : liftV v (1 : Fv D.host.F v) • finTens α M = finTens (singleFin v 1 * α) M := by
      ext i j
      change (pairA D.host.F 0 (singleFin v 1) * pairA D.host.F 0 α) ⊗ₜ[D.host.F] M i j = _
      rw [pair_mul]
      rfl
    rw [h]
    refine finTens_mem_latO (mul_mem_intAf (fun w => ?_) hα) hM
    by_cases hw : w = v
    · subst hw
      rw [evalV_singleFin_self]
      exact one_mem _
    · rw [evalV_singleFin_ne hw]
      exact zero_mem _
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

theorem isHalf_smul {m n : ℕ} {ε : AE D} (c : AF D.host.F) {u : Mx D m n} (hu : IsHalf ε u) : IsHalf ε (c • u) :=
  fun i j => by rw [Matrix.smul_apply, mul_smul_comm, hu]

theorem isHalf_zero {m n : ℕ} (ε : AE D) : IsHalf ε (0 : Mx D m n) := fun _ _ => mul_zero _

section Pair

variable {S T S' T' : HSp D} {P : Type} [AddCommGroup P] [Module (AF D.host.F) P]
  (m : P ≃ₗ[AF D.host.F] WO S T × WO S' T') (v : Pl D.host.F) (Λ : AddSubgroup P)

theorem le_of_gen {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {LS' : Set (Fin S'.rank → D.host.E)} {LT' : Set (Fin T'.rank → D.host.E)}
    (hΛ : ∀ u, u ∈ Λ ↔ At (evFin D.host.F v) u ∧ (m u).1 ∈ latO S T LS LT (fun _ => True) ∧
      (m u).2 ∈ latO S' T' LS' LT' fun _ => True) (H : AddSubgroup P) (h2 : ∀ u ∈ Λ, 2 • u ∈ H)
    (hh : ∀ ε, IsSplitIdem D ε → ∀ u ∈ Λ, IsHalf ε (m u).1 → IsHalf ε (m u).2 → u ∈ H) : Λ ≤ H := by
  let f : WO S T × WO S' T' →ₗ[AF D.host.F] P := liftV v (1 : Fv D.host.F v) • m.symm.toLinearMap
  have hf : ∀ x, f x = liftV v (1 : Fv D.host.F v) • m.symm x := fun _ => rfl
  have hm : ∀ x, m (f x) = liftV v (1 : Fv D.host.F v) • x := fun x => by rw [hf, map_smul, m.apply_symm_apply]
  have hin : ∀ x : WO S T × WO S' T', x.1 ∈ latO S T LS LT (fun _ => True) →
      x.2 ∈ latO S' T' LS' LT' (fun _ => True) → f x ∈ Λ := fun x h1 h2 =>
    (hΛ _).2 ⟨at_smul v _, by rw [hm]; exact smul_mem v h1, by rw [hm]; exact smul_mem v h2⟩
  intro u hu
  obtain ⟨ha, h1, h1'⟩ := (hΛ u).1 hu
  have e : u = f ((m u).1, 0) + f (0, (m u).2) := by
    rw [← map_add (f := _), Prod.mk_add_mk, add_zero, zero_add, hf, Prod.mk.eta, m.symm_apply_apply, smul_eq_of_at ha]
  rw [e]
  refine add_mem ?_ ?_
  · refine le_of_two_of_half (H.comap (f ∘ₗ LinearMap.inl _ _ _).toAddMonoidHom) (fun x hx => ?_) (fun ε hε x hx hx' => ?_) h1
    · rw [AddSubgroup.mem_comap, map_nsmul]
      exact h2 _ (hin (x, 0) hx (zero_mem _))
    · exact hh ε hε (f (x, 0)) (hin (x, 0) hx (zero_mem _)) (by rw [hm]; exact isHalf_smul _ hx')
        (by rw [hm]; exact isHalf_smul _ (isHalf_zero ε))
  · refine le_of_two_of_half (H.comap (f ∘ₗ LinearMap.inr _ _ _).toAddMonoidHom) (fun x hx => ?_) (fun ε hε x hx hx' => ?_) h1'
    · rw [AddSubgroup.mem_comap, map_nsmul]
      exact h2 _ (hin (0, x) (zero_mem _) hx)
    · exact hh ε hε (f (0, x)) (hin (0, x) (zero_mem _) hx) (by rw [hm]; exact isHalf_smul _ (isHalf_zero ε))
        (by rw [hm]; exact isHalf_smul _ hx')

theorem mem_iff_char {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)} {ΛT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hS' : IsSelfDualC S' ΛS') (hT' : IsSelfDualC T' ΛT')
    (hΛ : ∀ u, u ∈ Λ ↔ At (evFin D.host.F v) u ∧ (m u).1 ∈ latO S T ΛS ΛT (fun _ => True) ∧
      (m u).2 ∈ latO S' T' ΛS' ΛT' fun _ => True) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (B : P → P → AF D.host.F) (hB : ∀ x y, B x y = symplO S T (m x).1 (m y).1 + symplO S' T' (m x).2 (m y).2)
    {z : P} (hz : At (evFin D.host.F v) z) : z ∈ Λ ↔ ∀ γ ∈ Λ, ψ (B z γ) = 1 := by
  constructor
  · intro h γ hγ
    obtain ⟨-, a, b⟩ := (hΛ z).1 h
    obtain ⟨-, a', b'⟩ := (hΛ γ).1 hγ
    rw [hB, AddChar.map_add_eq_mul, char_sympl_eq_one hψ hS hT a a', char_sympl_eq_one hψ hS' hT' b b', one_mul]
  · intro h
    have hm : ∀ x, m (liftV v (1 : Fv D.host.F v) • m.symm x) = liftV v (1 : Fv D.host.F v) • x := fun x => by
      rw [map_smul, m.apply_symm_apply]
    have hz' : liftV v (1 : Fv D.host.F v) • m z = m z := by rw [← map_smul, smul_eq_of_at hz]
    have hz1 : liftV v (1 : Fv D.host.F v) • (m z).1 = (m z).1 := congrArg Prod.fst hz'
    have hz2 : liftV v (1 : Fv D.host.F v) • (m z).2 = (m z).2 := congrArg Prod.snd hz'
    have key : ∀ x : WO S T × WO S' T', x.1 ∈ latO S T ΛS ΛT (fun _ => True) →
        x.2 ∈ latO S' T' ΛS' ΛT' (fun _ => True) → ψ (symplO S T (m z).1 x.1 + symplO S' T' (m z).2 x.2) = 1 := fun x h1 h2 => by
      have := h _ ((hΛ (liftV v (1 : Fv D.host.F v) • m.symm x)).2
        ⟨at_smul v _, by rw [hm]; exact smul_mem v h1, by rw [hm]; exact smul_mem v h2⟩)
      rwa [hB, hm, Prod.smul_fst, Prod.smul_snd, symplO_swap, symplO_swap, hz1, hz2] at this
    refine (hΛ z).2 ⟨hz, mem_of_char hψ hS hT ?_ fun x hx => ?_, mem_of_char hψ hS' hT' ?_ fun x hx => ?_⟩
    · rw [← hz1]
      exact Matrix.ext fun _ _ => infPart_smul v _
    · have h0 : symplO S' T' (m z).2 0 = 0 := (symplHom S' T' (m z).2).map_zero
      have := key (x, 0) hx (zero_mem _)
      rwa [h0, add_zero] at this
    · rw [← hz2]
      exact Matrix.ext fun _ _ => infPart_smul v _
    · have h0 : symplO S T (m z).1 0 = 0 := (symplHom S T (m z).1).map_zero
      have := key (0, x) (zero_mem _) hx
      rwa [h0, zero_add] at this

end Pair

theorem latPt_le_closure_and_selfDual : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e → ∀ v : Pl D.host.F, latPt e v ≤ AddSubgroup.closure (genPt e v) ∧
      ∀ z : Pt G i j, At (evFin D.host.F v) z → (z ∈ latPt e v ↔ ∀ γ ∈ latPt e v, W.ψ (sympPt Γ z γ) = 1) := by
  intro D T L sc G μ₀ hL W i j e Γ hW hWW v
  have a := (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).sd
  refine ⟨le_of_gen (maps e) v _ (fun _ => Iff.rfl) _ (fun u hu => AddSubgroup.subset_closure (Or.inl ⟨u, hu, rfl⟩))
    fun ε hε u hu h1 h2 => AddSubgroup.subset_closure (Or.inr ⟨hu, ε, hε, h1, h2⟩), fun z hz => ?_⟩
  exact mem_iff_char (maps e) v _ (isSelfDualC_neg a) (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd
    (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd a (fun _ => Iff.rfl) W.ψ_std (sympPt Γ) (symp_eq e Γ hW hWW) hz

end GlobalTheory.BigDatLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleKernelIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StageConv

theorem m_le_of_size {D : D7} {large₂ : SizeData₂ D} (h : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) : D.R.m ≤ D.R.r + 1 := by
  have h4 : D.R.m ^ 4 ≤ D.R.f := h.2.2.1
  have hm : 44 ≤ D.R.m := h.2.2.2.1
  have hfm : D.R.f * D.R.m ≤ (D.R.r + 1) ^ 3 := h.2.2.2.2.2.2.1
  by_contra hc
  push_neg at hc
  have h1 : (D.R.r + 1) ^ 3 < D.R.m ^ 3 := Nat.pow_lt_pow_left hc (by norm_num)
  have h2 : D.R.m ^ 3 ≤ D.R.m ^ 4 * D.R.m := by
    calc D.R.m ^ 3 ≤ D.R.m ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ = D.R.m ^ 4 * D.R.m := by ring
  have h3 : D.R.m ^ 4 * D.R.m ≤ D.R.f * D.R.m := Nat.mul_le_mul_right _ h4
  omega

theorem rank_lt {D : D7} {i j : Fin D.R.m} {p q : ℕ} {A A' WW : HSp D} (hmr : D.R.m ≤ D.R.r + 1)
    (hp : p ≤ pp D j) (hq : q ≤ qq D j) (hA : A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p)
    (hA' : A'.rank + 2 * qq D j = rankV D i j + 2 * q) (hd : A.rank + A'.rank = WW.rank) :
    WW.rank < 2 * (A.rank - p) := by
  have e1 : rankV D ((i : ℕ) + 1) ((j : ℕ) + 1) = rankV D i j + D.R.t + sLen D := by
    simp only [rankV]; ring
  have hpp : 2 * pp D j ≤ D.R.m - 1 := by
    simp only [pp]; have := j.2; omega
  have hs : sLen D = D.R.r + 6 := rfl
  rw [e1] at hA
  omega

end GlobalTheory.StageConv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteValuationCentredCompleteNormal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteValuationCentredCompleteNormal
open IsLocalRing GlobalTheory.TorRef

namespace GlobalTheory.DivVal

theorem exists_valuation_centre (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : IsCN V) :
    ∃ ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ)),
      (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) ∧
        ∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1 := by
  classical
  haveI : IsNoetherianRing V := hV.1
  by_cases hm : maximalIdeal V = ⊥
  · refine ⟨1, fun v => ?_, fun v hv => ?_⟩
    · by_cases h : algebraMap V (FractionRing V) v = 0
      · simp [h]
      · simp [Valuation.one_apply_of_ne_zero h]
    · rw [hm, Ideal.mem_bot] at hv
      simp [hv]
  · obtain ⟨T, hT, g, hg, hc⟩ := GlobalTheory.GoodVal.exists_dvr_centre (R := V) (K := FractionRing V)
      (L := FractionRing V) (maximalIdeal V) hm
    have hg' : ∀ v : V, algebraMap T (FractionRing V) (g v) = algebraMap V (FractionRing V) v := fun v => by
      simpa using congrArg (fun f => f v) hg
    have hne : maximalIdeal T ≠ ⊥ := IsDiscreteValuationRing.not_a_field T
    let P : IsDedekindDomain.HeightOneSpectrum T := ⟨maximalIdeal T, inferInstance, hne⟩
    refine ⟨P.valuation (FractionRing V), fun v => ?_, fun v hv => ?_⟩
    · rw [← hg']
      exact P.valuation_le_one (g v)
    · rw [← hg']
      refine (P.valuation_lt_one_iff_mem (g v)).2 ?_
      show g v ∈ maximalIdeal T
      rw [← Ideal.mem_comap, hc]
      exact hv

end GlobalTheory.DivVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteValuationCentredCompleteNormalStatement
open IsLocalRing GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_discreteValuation_centred_completeNormal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∃ ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ)), (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) ∧ ∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1 := by
  first | exact @GlobalTheory.DivVal.exists_valuation_centre | exact GlobalTheory.DivVal.exists_valuation_centre | (intros; apply GlobalTheory.DivVal.exists_valuation_centre <;> assumption)
end
end
