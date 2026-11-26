module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.ZuckDualTOfZuckDual
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.CoefEig
section -- merged from CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.FunAct
section -- merged from CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.Transport
open Matrix Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace CompanionTheory.CapEig

section rel

variable {n : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem foldr_rel
    {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    {Eop' : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E') → (Matrix (Fin n) (Fin n) ℂ → E')}
    (Rel : (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E') → Prop)
    (hT : ∀ u a b f f', Rel f f' → Rel (Top Eop u a b f) (Top Eop' u a b f'))
    {f : Matrix (Fin n) (Fin n) ℂ → E} {f' : Matrix (Fin n) (Fin n) ℂ → E'} (h : Rel f f') :
    ∀ (t : ℕ) (u : Fin t → ℂ) (a b : Fin t → Fin n),
      Rel ((List.ofFn fun k => Top Eop (u k) (a k) (b k)).foldr (fun T h => T h) f)
        ((List.ofFn fun k => Top Eop' (u k) (a k) (b k)).foldr (fun T h => T h) f')
  | 0, _, _, _ => by simpa using h
  | t + 1, u, a, b => by
    rw [List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.foldr_cons]
    exact hT _ _ _ _ _ (foldr_rel Rel hT h t (fun k => u k.succ) (fun k => a k.succ) (fun k => b k.succ))

theorem qminorOp_rel
    {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    {Eop' : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E') → (Matrix (Fin n) (Fin n) ℂ → E')}
    (Rel : (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E') → Prop)
    (hT : ∀ u a b f f', Rel f f' → Rel (Top Eop u a b f) (Top Eop' u a b f'))
    (φ : E →L[ℂ] E') (g : Matrix (Fin n) (Fin n) ℂ) (hg : ∀ f f', Rel f f' → φ (f g) = f' g)
    {f : Matrix (Fin n) (Fin n) ℂ → E} {f' : Matrix (Fin n) (Fin n) ℂ → E'} (h : Rel f f')
    {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) :
    φ (qminorOp Eop a b u f g) = qminorOp Eop' a b u f' g := by
  unfold qminorOp
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  exact hg _ _ (foldr_rel Rel hT h t (fun k => u - ((k : ℕ) : ℂ)) (fun k => a (σ k)) b)

end rel

section uj

variable {n : ℕ} {ε : Fin n → Bool} {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem ec_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    (Z : Matrix (Fin n) (Fin n) ℂ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : EcV ε Z f g = EcV ε Z f' g := by
  obtain ⟨h1, h2, -, -⟩ := cpartMem n ε Z
  unfold EcV
  rw [io_rd_congr h h1 hg, io_rd_congr h h2 hg]

theorem top_smooth {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (u : ℂ) (a b : Fin n) :
    SmoothOnGV ε (Top (EabV ε) u a b f) := by
  unfold Formalism.QuantumDeterminants.Top
  by_cases hab : a = b
  · simp only [if_pos hab]
    exact io_smooth_add (io_smooth_smul u hf) (io_eab_smooth hf a b)
  · simp only [if_neg hab]
    exact io_smooth_add io_smooth_zero (io_eab_smooth hf a b)

theorem eab_clm (φ : E →L[ℂ] E') {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : φ (EabV ε a b f g) = EabV ε a b (fun x => φ (f x)) g := by
  obtain ⟨h1, h2, -, -⟩ := cpartMem n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [map_add (f := _), map_smul, (rdVPair n ε E E' φ f _ g hf h1 hg).2, (rdVPair n ε E E' φ f _ g hf h2 hg).2]

theorem capelli_clm (φ : E →L[ℂ] E') {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (u : ℂ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : φ (capelli ε u f g) = capelli ε u (fun x => φ (f x)) g := by
  unfold capelli qdetOp
  refine qminorOp_rel (fun f f' => SmoothOnGV ε f ∧ ∀ x, inUJ ε x → φ (f x) = f' x) ?_ φ g
    (fun _ _ h => h.2 g hg) ⟨hf, fun _ _ => rfl⟩ id id u
  rintro u a b f f' ⟨hs, he⟩
  refine ⟨top_smooth hs u a b, fun x hx => ?_⟩
  unfold Formalism.QuantumDeterminants.Top
  rw [map_add (f := _), eab_clm φ hs a b hx, io_eab_congr he a b hx]
  congr 1
  split_ifs
  · rw [map_smul, he x hx]
  · exact map_zero φ

end uj

theorem capelli_localization : PI.UnitaryGroupMassFormula.CapelliEig.Loc := by
  intro n ε E _ _ H P Q F₁ F₂ u g hQP hPQ hH hF hg
  unfold capelliH qdetOp
  rw [ioh_qminor ε H P Q hQP hPQ hH, ioh_qminor ε H P Q hQP hPQ hH]
  have hg' := ioh_inUJ ε H P Q g hPQ hH hg
  refine qminorOp_rel (fun f f' => ∀ x, inUJ ε x → f x = f' x) ?_ (ContinuousLinearMap.id ℂ E) _
    (fun _ _ h => h _ hg') (fun x hx => hF _ (ioh_inUH ε H P Q x hPQ hH hx)) id id u
  intro u a b f f' he x hx
  unfold Formalism.QuantumDeterminants.Top
  beta_reduce
  rw [he x hx, ec_congr he _ hx]

theorem capelli_transport : PI.UnitaryGroupMassFormula.CapelliEig.CapTransport := by
  intro n ε E _ _ H P Q F u g hQP hPQ hH hsm hg
  have hg' := ioh_inUJ ε H P Q g hPQ hH hg
  let x : _root_.Formalism.QuantumDeterminants.ioS ε E := ⟨fun y => F (Q * y.1 * P), by
    exact io_smooth_congr (fun y hy => (ioExt_at (φ := fun z => F (Q * z.1 * P)) hy).symm) hsm⟩
  have hx : IORep (fun y => F (Q * y * P)) x.1 := fun y hy => rfl
  have h1 := ioh_qminor_rep (ioh_repr (ε := ε) (E := E) P Q) id id u hx _ hg'
  have h2 := io_qminor_rep id id u hx _ hg'
  have hc := (Formalism.FourierDecayAlt.P.contractions_covariant (Module.End ℂ (ioS ε E)) n (ioE ε E) P Q (io_gl ε E)
    hQP hPQ u 0 0 0 0).1
  unfold capelliH capelli qdetOp
  rw [ioh_qminor ε H P Q hQP hPQ hH, h1, h2]
  exact congrArg (fun T : Module.End ℂ (ioS ε E) => (T x).1 ⟨_, hg'⟩) hc

end CompanionTheory.CapEig

end
end

open Matrix Formalism.REAL Formalism.QuantumDeterminants PI.DSInfCharCap

noncomputable section

namespace CompanionTheory.CapEig

theorem algHom_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) : φ (qdet E u) = qdet (fun a b => φ (E a b)) u := by
  have hT : ∀ v a b, φ (Tm E v a b) = Tm (fun a b => φ (E a b)) v a b := by
    intro v a b
    by_cases hab : a = b <;> simp [Tm, hab]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [qdet, qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def, hT]

theorem lift_eq_sum {X A : Type} [Ring A] [Algebra ℂ A] (f : X → A) (p : FreeAlgebra ℂ X) :
    FreeAlgebra.lift ℂ f p = (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).coeff.sum
      fun w c => c • (w.toList.map f).prod := by
  have e : FreeAlgebra.lift ℂ f = (MonoidAlgebra.lift ℂ A (FreeMonoid X) (FreeMonoid.lift f)).comp
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := X)).toAlgHom := by
    ext x
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  rw [e]
  show MonoidAlgebra.lift ℂ A (FreeMonoid X) (FreeMonoid.lift f) (FreeAlgebra.equivMonoidAlgebraFreeMonoid p) = _
  rw [MonoidAlgebra.lift_apply]
  simp only [FreeMonoid.lift_apply]

section vec

variable {n : ℕ} {ε : Fin n → Bool} {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {σ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs)}

theorem inUJ_one : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp [inUJ]

theorem rd_vec (hm : ∀ a b, inUJ ε a → inUJ ε b → σ (a * b) = (σ a).comp (σ b)) {v : Hs}
    (hv : SmoothOnGV ε fun x => σ x v) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) :
    RdV X (fun x => σ x v) g = σ g (PI.PhMeasCore.dsig σ X v) := by
  have e0 : PI.PhMeasCore.dsig σ X v = RdV X (fun x => σ x v) 1 := by
    unfold PI.PhMeasCore.dsig RdV
    simp only [Matrix.one_mul]
  rw [e0, (rdVPair n ε Hs Hs (σ g) _ X 1 hv hX inUJ_one).2,
    io_rd_congr (f' := fun x => σ (g * x) v) (fun x hx => by rw [hm g x hg hx]; rfl) hX inUJ_one,
    rdLeftV n Hs (fun x => σ x v) X g 1, Matrix.mul_one]

theorem eab_vec (hm : ∀ a b, inUJ ε a → inUJ ε b → σ (a * b) = (σ a).comp (σ b)) {v : Hs}
    (hv : SmoothOnGV ε fun x => σ x v) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    EabV ε a b (fun x => σ x v) g = σ g (dsigC ε σ (unitM (a, b)) v) := by
  obtain ⟨h1, h2, -, -⟩ := cpartMem n ε (Matrix.single a b 1)
  unfold EabV EcV dsigC
  rw [rd_vec hm hv h1 hg, rd_vec hm hv h2 hg, map_add (f := _), map_smul]
  simp only [cpart1, cpart2, thetaJ, unitM, sub_neg_eq_add, ← sub_eq_add_neg]

theorem word_rep (hm : ∀ a b, inUJ ε a → inUJ ε b → σ (a * b) = (σ a).comp (σ b)) {v : Hs}
    {x : _root_.Formalism.QuantumDeterminants.ioS ε Hs}
    (hx : IORep (fun y => σ y v) x.1) : ∀ w : List (Fin n × Fin n),
    IORep (fun y => σ y (dsigCW ε σ (w.map unitM) v))
      ((w.map fun ab => _root_.Formalism.QuantumDeterminants.ioE ε Hs ab.1 ab.2).prod x).1
  | [] => by simpa [dsigCW] using hx
  | ab :: w => by
    have ih := word_rep hm hx w
    have hs : SmoothOnGV ε fun y => σ y (dsigCW ε σ (w.map unitM) v) :=
      io_smooth_congr (fun g hg => (io_rep_ext _ g hg).trans (ih g hg).symm) (io_mem_smooth _)
    intro g hg
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp, dsigCW]
    rw [← ioE_rep ih ab.1 ab.2 g hg, eab_vec hm hs ab.1 ab.2 hg]

theorem actU_rep (hm : ∀ a b, inUJ ε a → inUJ ε b → σ (a * b) = (σ a).comp (σ b)) {v : Hs}
    {x : _root_.Formalism.QuantumDeterminants.ioS ε Hs}
    (hx : IORep (fun y => σ y v) x.1) (p : FreeAlgebra ℂ (Fin n × Fin n)) :
    IORep (fun y => σ y (actU ε σ p v))
      (FreeAlgebra.lift ℂ (fun ab : Fin n × Fin n => _root_.Formalism.QuantumDeterminants.ioE ε Hs ab.1 ab.2) p x).1 := by
  intro g hg
  rw [lift_eq_sum]
  unfold actU Finsupp.sum
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← word_rep hm hx w.toList g hg]

theorem capelli_vec (hm : ∀ a b, inUJ ε a → inUJ ε b → σ (a * b) = (σ a).comp (σ b)) {v : Hs}
    (hv : SmoothOnGV ε fun x => σ x v) (u : ℂ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    capelli ε u (fun x => σ x v) g = σ g (actU ε σ (qdet (Egl n) u) v) := by
  obtain ⟨x, hx⟩ := io_rep_mk hv
  have h1 := io_qminor_rep id id u hx g hg
  have h2 := actU_rep hm hx (qdet (Egl n) u) g hg
  rw [algHom_qdet] at h2
  simp only [Egl, FreeAlgebra.lift_ι_apply] at h2
  unfold capelli qdetOp
  rw [h1]
  exact h2.symm

end vec

end CompanionTheory.CapEig

end
end

open Matrix PI.UpqRep Formalism.FourierDecayAlt
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.CapEig

theorem capC_vec (hI : PI.DSInfCharCap.DSInfCharCap) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {lam : Fin (2 * r + k + 1) → ℝ} {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs →L[ℂ] Hs)}
    (hlam : IsHCParam lam) (hσ : IsDSHpk k r ε lam σ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : Hs →L[ℂ] E) {v : Hs} (hv : v ∈ smoothVecs (k := k) (r := r) σ)
    {F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E} (hF : ∀ x ∈ UH (Hpk k r), F x = L (σ x v))
    (Y : ℂ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    PI.CapelliEig.capC (k := k) (r := r) Y F g = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • F g := by
  obtain ⟨P₀, hP₀, hds⟩ := hσ
  have hdet : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det _).mp hP₀.1.1
  have hPQ : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hQP : P₀⁻¹ * P₀ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hH : Formalism.QuantumDeterminants.Hpk k r = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := hP₀.1.2.symm
  have hv' : Formalism.REAL.SmoothOnGV ε (fun x => σ (P₀⁻¹ * x * P₀) v) :=
    Formalism.QuantumDeterminants.ioh_smooth ε _ P₀ P₀⁻¹ (fun x => σ x v) hPQ hH hv
  have hg' : Formalism.REAL.inUJ ε (P₀ * g * P₀⁻¹) := Formalism.QuantumDeterminants.ioh_inUJ ε _ P₀ P₀⁻¹ g hPQ hH hg
  have hsm : Formalism.REAL.SmoothOnGV ε (fun x => L (σ (P₀⁻¹ * x * P₀) v)) :=
    (Formalism.REAL.rdVPair _ ε Hs E L _ 0 1 hv' (by simp [Formalism.REAL.inG]) inUJ_one).1
  have hm : ∀ a b, Formalism.REAL.inUJ ε a → Formalism.REAL.inUJ ε b →
      σ (P₀⁻¹ * (a * b) * P₀) = (σ (P₀⁻¹ * a * P₀)).comp (σ (P₀⁻¹ * b * P₀)) :=
    fun a b ha hb => hds.2.2.1.1.2 a ha b hb
  have hu : (Y + ((2 * r + k : ℕ) : ℂ) / 2) = Y + (((2 * r + k + 1 : ℕ) : ℂ) - 1) / 2 := by
    push_cast; ring
  unfold PI.CapelliEig.capC
  rw [capelli_localization _ ε _ _ P₀ P₀⁻¹ F (fun x => L (σ x v)) _ g hQP hPQ hH hF hg,
    capelli_transport _ ε _ _ P₀ P₀⁻¹ _ _ g hQP hPQ hH hsm hg, ← capelli_clm L hv' _ hg',
    capelli_vec (σ := fun x => σ (P₀⁻¹ * x * P₀)) hm hv' _ hg', hu, hI _ ε lam Hs _ hlam hds v hv' Y,
    Formalism.QuantumDeterminants.ioh_QP P₀ P₀⁻¹ g hQP, hF g hg, map_smul, map_smul]

theorem qminorOp_cast {n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)) (h : m = n)
    (a : Fin m → Fin n) (ha : ∀ j, (a j).val = j.val) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Formalism.QuantumDeterminants.qminorOp Eop a a u f = Formalism.QuantumDeterminants.qminorOp Eop id id u f := by
  subst h
  have : a = id := funext fun j => Fin.ext (ha j)
  rw [this]

theorem capelli_eigenvalue_transfer : CompanionTheory.LimBd.Main.CVBridge := by
  intro k r E _ _ Y F
  unfold Q.CV Q.capL PI.CapelliEig.capC Formalism.QuantumDeterminants.capelliH Formalism.QuantumDeterminants.qdetOp
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  have hu : Q.uC k r 0 Y = Y + ((2 * r + k : ℕ) : ℂ) / 2 := by
    unfold Q.uC; rw [hm]; push_cast; ring
  rw [hu]
  exact qminorOp_cast _ hm _ (fun j => by simp [Q.posL]) _ _

theorem coefEig_of (hI : PI.DSInfCharCap.DSInfCharCap) (hK : PI.KFinSmooth) : CompanionTheory.LimBd.Main.CoefEig := by
  intro k r ε μ φ Wp Wq _ _ _ _ _ _ T hφ Y g hg
  obtain ⟨H, _, _, _, σ, v, w, hμ, hσ, hv, -, he⟩ := hφ
  rw [capelli_eigenvalue_transfer]
  exact capC_vec hI hμ hσ ((innerSL ℂ w).smulRight T) (hK k r ε μ H σ hμ hσ v hv)
    (F := fun x => φ x • T) (fun x hx => by simp [he x hx]) Y hg

end CompanionTheory.CapEig

end
end

namespace CompanionTheory.CapEig

theorem coefEig_of_infChar (hI : PI.DSInfCharCap.DSInfCharCap) : CompanionTheory.LimBd.Main.CoefEig :=
  coefEig_of hI CompanionTheory.D.gk.admitted.k_finite_smooth

end CompanionTheory.CapEig
