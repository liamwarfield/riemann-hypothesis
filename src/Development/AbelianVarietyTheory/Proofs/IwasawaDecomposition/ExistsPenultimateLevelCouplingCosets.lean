module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevOffType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherPlacesGroupContainsChartLevels

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevJCosetsOfFurther
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RedMLevJ
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.LevJRed

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {gp : Fin 2 → ℕ}

theorem mat_one (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    (fr : GL (Fin n) (v.adicCompletion F)) : G.mat j v h fr 1 = 1 := by
  unfold GLoc.mat
  rw [map_one, mul_one, inv_mul_cancel, Units.val_one]

theorem mat_mul (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    (fr : GL (Fin n) (v.adicCompletion F)) (x y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    G.mat j v h fr (x * y) = G.mat j v h fr x * G.mat j v h fr y := by
  unfold GLoc.mat
  rw [map_mul, ← Units.val_mul]
  congr 1
  group

theorem mat_int (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    {J : Matrix (Fin n) (Fin n) E} {Lb : Submodule (𝓞 E) (Fin n → E)} (fr : GL (Fin n) (v.adicCompletion F))
    (hfr : ∀ x : Fin n → v.adicCompletion F,
      (∃ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb, ∀ b, G.phi j v h (y b) = x b) ↔
        ∀ b, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈
          v.adicCompletionIntegers F)
    {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (hx : x ∈ levelVL σ J v Lb) (a b : Fin n) :
    G.mat j v h fr x a b ∈ v.adicCompletionIntegers F := by
  classical
  set w : Fin n → v.adicCompletion F := (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ Pi.single b 1 with hw
  have hinv : ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ w = Pi.single b 1 := by
    rw [hw, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  obtain ⟨y, hy, hyw⟩ := (hfr w).2 fun c => by
    rw [hinv]
    by_cases e : c = b
    · subst e
      rw [Pi.single_eq_same]
      exact one_mem _
    · rw [Pi.single_eq_of_ne e]
      exact zero_mem _
  have hst : x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) Lb) := hx.2
  have hxy : (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈
      latS (F := F) (v.adicCompletion F) (intV E v) Lb := (hst y).1 hy
  have hphi : ∀ c, G.phi j v h (((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) c) =
      (((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)).map (G.phi j v h)) *ᵥ w) c := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hyw]
  have key := (hfr _).1 ⟨_, hxy, hphi⟩ a
  convert key using 1
  unfold GLoc.mat
  rw [hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, Matrix.mulVec_single_one]
  rfl

end Gen

theorem redM_levJ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) 1) = 1 ∧ ∀ x ∈ F.levJ.Uloc v, ∀ y ∈ F.levJ.Uloc v, redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) (x * y)) = redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) x) * redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) y) := by
  intro B X I _ _ l Z u Ch0 chOf0 F _ j v hv
  have hint : ∀ x ∈ F.levJ.Uloc v, ∀ a b, F.gl.mat j v hv (F.glevJ.fr j v hv) x a b ∈
      v.adicCompletionIntegers (I.rec7 l Z).host.F := fun x hx =>
    mat_int F.gl j v hv (F.glevJ.fr j v hv) (F.glevJ.fr_lat j v hv) (F.levJ.Uloc_lev v hx)
  refine ⟨?_, fun x hx y hy => ?_⟩
  · rw [mat_one]
    exact ChartLevel.redM_one v
  · rw [mat_mul]
    exact ChartLevel.redM_mul v (hint x hx) (hint y hy)

end GlobalTheory.Mem.Col2.TC.LevJRed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReGLMemLevelVL
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.TwistLevel

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem reGL_rfl_apply {a : ℕ} {R : Type} [CommRing R] (x : GL (Fin a) R) : reGL (rfl : a = a) R x = x := by
  ext i j
  rfl

theorem reL_rfl' {a : ℕ} (L : Submodule (𝓞 E) (Fin a → E)) : reL (rfl : a = a) L = L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem reGL_mem_UPts (σ : E →ₐ[F] E) {a b : ℕ} (h : a = b) (G : Matrix (Fin a) (Fin a) E) (J : Matrix (Fin b) (Fin b) E)
    (hJ : J = G.reindex (finCongr h) (finCongr h)) (R : Type) [CommRing R] [Algebra F R] (x : GL (Fin a) (E ⊗[F] R)) :
    reGL h _ x ∈ UPts σ J R ↔ x ∈ UPts σ G R := by
  subst h
  subst hJ
  rw [reGL_rfl_apply]
  simp only [finCongr_refl, Matrix.reindex_refl_refl]

theorem reGL_mem_levelVL (σ : E →ₐ[F] E) {a b : ℕ} (h : a = b) (G : Matrix (Fin a) (Fin a) E) (J : Matrix (Fin b) (Fin b) E)
    (hJ : J = G.reindex (finCongr h) (finCongr h)) (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin a → E))
    (x : GL (Fin a) (E ⊗[F] v.adicCompletion F)) :
    reGL h _ x ∈ levelVL σ J v (reL h L) ↔ x ∈ levelVL σ G v L := by
  subst h
  subst hJ
  rw [reGL_rfl_apply, reL_rfl']
  simp only [finCongr_refl, Matrix.reindex_refl_refl]

theorem exists_off (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hκ : κ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ∃ y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), (∀ v ∈ Q, bc (prV (E := E) v) y = 1) ∧
      ∀ v, v ∉ Q → bc (prV (E := E) v) y = bc (prV (E := E) v) κ := by
  classical

  have key : ∀ (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v w : HeightOneSpectrum (𝓞 F)), w ≠ v →
      bc (prV (E := E) w) (Formalism.UG.P.afsplitU v 1 y) = bc (prV (E := E) w) y := by
    intro y v w hw
    apply Units.ext
    rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe,
      Formalism.UG.P.afsplitC_prV_ne v w hw]
  induction Q using Finset.induction_on with
  | empty => exact ⟨κ, hκ, by simp, fun v _ => rfl⟩
  | @insert v Q hv ih =>
    obtain ⟨y, hy, h1, h2⟩ := ih
    refine ⟨Formalism.UG.P.afsplitU v 1 y, Formalism.UG.P.afsplitU_mem v σ J _ _ (one_mem _) hy, ?_, ?_⟩
    · intro w hw
      by_cases hwv : w = v
      · subst hwv
        exact Formalism.UG.P.afsplit_right1 w 1 y
      · rw [key y v w hwv]
        exact h1 w ((Finset.mem_insert.mp hw).resolve_left hwv)
    · intro w hw
      have hwv : w ≠ v := fun e => hw (e ▸ Finset.mem_insert_self v Q)
      rw [key y v w hwv]
      exact h2 w (fun h => hw (Finset.mem_insert_of_mem h))

end Gen

section Lev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {hc : CMData F E} {S : HSpace E} {gp : Fin 2 → ℕ} {T f : ℕ}


open Classical in
def ulocQ (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))) (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)) :=
  if h : v ∈ Q then W v h else H0.Uloc v

theorem ulocQ_pos (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))) {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ Q) :
    ulocQ H0 Q W v = W v h := by
  unfold ulocQ
  exact dif_pos h

theorem ulocQ_neg (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))) {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ Q) :
    ulocQ H0 Q W v = H0.Uloc v := by
  unfold ulocQ
  exact dif_neg h

def uQ (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))) :
    Subgroup (GL (Fin S.rank) (E ⊗[F] Formalism.L2.Herm.Af F)) where
  carrier := {x | x ∈ Formalism.L2.Herm.UAf hc S ∧ ∀ v, bc (prV (E := E) v) x ∈ ulocQ H0 Q W v}
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, fun v => by rw [map_mul]; exact mul_mem (hx.2 v) (hy.2 v)⟩
  one_mem' := ⟨one_mem _, fun v => by rw [map_one]; exact one_mem _⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, fun v => by rw [map_inv]; exact inv_mem (hx.2 v)⟩

def mkLevQ (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)))
    (hWl : ∀ v hv, W v hv ≤ levelVL hc.sig S.gram v H0.Lb)
    (hWQ : ∀ v hv, ∃ N : ℕ, 0 < N ∧ ∀ x, Formalism.L2.Herm.InPrinc hc S v N H0.Lb x → x ∈ W v hv)
    (hQg : ∀ v ∈ Q, ∀ i, (gp i : 𝓞 F) ∉ v.asIdeal) (hQT : ∀ v ∈ Q, (T : 𝓞 F) ∉ v.asIdeal) :
    Formalism.L2.Herm.StepLevelQ hc S gp T f Q where
  Lb := H0.Lb
  Lb_fin := H0.Lb_fin
  Lb_span := H0.Lb_span
  Lb_int := H0.Lb_int
  Lb_dual := H0.Lb_dual
  Lb_index := H0.Lb_index
  Uloc := ulocQ H0 Q W
  Uloc_lev v := by
    by_cases h : v ∈ Q
    · rw [ulocQ_pos H0 Q W h]; exact hWl v h
    · rw [ulocQ_neg H0 Q W h]; exact H0.Uloc_lev v
  Uloc_hyp v h0 h1 hT hQ := by rw [ulocQ_neg H0 Q W hQ]; exact H0.Uloc_hyp v h0 h1 hT
  Uloc_g i v h x hx := by
    rw [ulocQ_neg H0 Q W (fun hq => hQg v hq i h)]; exact H0.Uloc_g i v h x hx
  UlocAlt v h x := by
    rw [ulocQ_neg H0 Q W (fun hq => hQT v hq h)]; exact H0.UlocAlt v h x
  Uloc_Q v hv := by
    obtain ⟨N, hN, h⟩ := hWQ v hv
    exact ⟨N, hN, fun x hx => by rw [ulocQ_pos H0 Q W hv]; exact h x hx⟩
  U := uQ H0 Q W
  U_eq _ := Iff.rfl

end Lev

end GlobalTheory.Mem.Col2.TwistLevel

end

namespace GlobalTheory.Mem.Col2.TwistLevel

section Abs

def actOfRed {G : Type} [Group G] {ι : Type} {n : ℕ} {k : ι → Type} [∀ i, CommRing (k i)]
    (ρ : G → ∀ i, Matrix (Fin n) (Fin n) (k i)) (h1 : ρ 1 = 1) (hm : ∀ a b, ρ (a * b) = ρ a * ρ b) :
    MulAction G (∀ i, Fin n → k i) where
  smul a y i := ρ a i *ᵥ y i
  one_smul y := by
    funext i
    show ρ 1 i *ᵥ y i = y i
    rw [h1, Pi.one_apply, Matrix.one_mulVec]
  mul_smul a b y := by
    funext i
    show ρ (a * b) i *ᵥ y i = ρ a i *ᵥ (ρ b i *ᵥ y i)
    rw [hm, Pi.mul_apply, Matrix.mulVec_mulVec]

theorem assemble {G : Type} [Group G] {Ch : Type} [Finite Ch] {Qt : Type} [Finite Qt] (Wq : Qt → Type) [∀ q, Group (Wq q)]
    (zQ : G →* ∀ q, Wq q) (Kc : Ch → ∀ q, Subgroup (Wq q)) (hfi : ∀ β q, (Kc β q).FiniteIndex) {V : Type} [Finite V]
    [MulAction G V] (w : Ch → V) (H : Ch → Subgroup G)
    (hH : ∀ β κ, κ ∈ H β ↔ (∀ q, zQ κ q ∈ Kc β q) ∧ κ • w β = w β) :
    ∃ (Yb : Type) (_ : Finite Yb) (_ : MulAction G Yb) (yb : Ch → Yb) (yG : Yb → V) (YQ : Type) (yQ : Yb → YQ),
      (∀ y, ∃! β, ∃ κ : G, κ • yb β = y) ∧ (∀ β (κ : G), κ ∈ H β ↔ κ • yb β = yb β) ∧ (∀ (κ : G) y, yG (κ • y) = κ • yG y) ∧
      (∀ y y', yG y = yG y' → yQ y = yQ y' → y = y') ∧ (∀ (κ : G) y, zQ κ = 1 → yQ (κ • y) = yQ y) := by
  classical
  have hfq : ∀ β q, Finite (Wq q ⧸ Kc β q) := fun β q => by
    haveI := hfi β q
    infer_instance

  let fQ : ∀ β, G ⧸ H β → ∀ q, Wq q ⧸ Kc β q := fun β c =>
    Quotient.liftOn' c (fun g q => ((zQ g q : Wq q) : Wq q ⧸ Kc β q)) (by
      intro a b hab
      have hm := ((hH β (a⁻¹ * b)).mp (QuotientGroup.leftRel_apply.mp hab)).1
      funext q
      apply QuotientGroup.eq.mpr
      simpa [map_mul, map_inv] using hm q)

  let fG : ∀ β, G ⧸ H β → V := fun β c =>
    Quotient.liftOn' c (fun g => g • w β) (by
      intro a b hab
      have hs := ((hH β (a⁻¹ * b)).mp (QuotientGroup.leftRel_apply.mp hab)).2
      rw [mul_smul, inv_smul_eq_iff] at hs
      exact hs.symm)
  have hinj : ∀ (y y' : Σ β, G ⧸ H β), fG y.1 y.2 = fG y'.1 y'.2 →
      (⟨y.1, fQ y.1 y.2⟩ : Σ β, ∀ q, Wq q ⧸ Kc β q) = ⟨y'.1, fQ y'.1 y'.2⟩ → y = y' := by
    rintro ⟨β, c⟩ ⟨β', c'⟩ hG hQ
    obtain rfl : β = β' := congrArg Sigma.fst hQ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective c'
    have hQ' : fQ β g = fQ β g' := eq_of_heq (Sigma.mk.inj hQ).2
    have hG' : g • w β = g' • w β := hG
    have hmem : g⁻¹ * g' ∈ H β := by
      refine (hH β _).mpr ⟨fun q => ?_, ?_⟩
      · have hq : ((zQ g q : Wq q) : Wq q ⧸ Kc β q) = ((zQ g' q : Wq q) : Wq q ⧸ Kc β q) := congrFun hQ' q
        have := QuotientGroup.eq.mp hq
        simpa [map_mul, map_inv] using this
      · rw [mul_smul, ← hG', inv_smul_smul]
    exact congrArg (Sigma.mk β) (QuotientGroup.eq.mpr hmem)
  refine ⟨Σ β, G ⧸ H β,
    Finite.of_injective (fun y => (fG y.1 y.2, (⟨y.1, fQ y.1 y.2⟩ : Σ β, ∀ q, Wq q ⧸ Kc β q)))
      (fun y y' h => hinj y y' (congrArg Prod.fst h) (congrArg Prod.snd h)),
    inferInstance, fun β => ⟨β, ((1 : G) : G ⧸ H β)⟩, fun y => fG y.1 y.2,
    Σ β, ∀ q, Wq q ⧸ Kc β q, fun y => ⟨y.1, fQ y.1 y.2⟩, ?_, ?_, ?_, hinj, ?_⟩
  · rintro ⟨β, c⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    refine ⟨β, ⟨g, ?_⟩, ?_⟩
    · show (⟨β, g • ((1 : G) : G ⧸ H β)⟩ : Σ β, G ⧸ H β) = ⟨β, (g : G ⧸ H β)⟩
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    · rintro β' ⟨κ, hκ⟩
      exact congrArg Sigma.fst hκ
  · intro β κ
    have e : κ • (⟨β, ((1 : G) : G ⧸ H β)⟩ : Σ β, G ⧸ H β) = ⟨β, (κ : G ⧸ H β)⟩ := by
      show (⟨β, κ • ((1 : G) : G ⧸ H β)⟩ : Σ β, G ⧸ H β) = ⟨β, (κ : G ⧸ H β)⟩
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    show κ ∈ H β ↔ κ • (⟨β, ((1 : G) : G ⧸ H β)⟩ : Σ β, G ⧸ H β) = ⟨β, ((1 : G) : G ⧸ H β)⟩
    rw [e]
    constructor
    · intro hk
      exact congrArg (Sigma.mk β) (QuotientGroup.eq.mpr (by simpa using hk))
    · intro hk
      have h2 : (κ : G ⧸ H β) = ((1 : G) : G ⧸ H β) := eq_of_heq (Sigma.mk.inj hk).2
      simpa using QuotientGroup.eq.mp h2
  · rintro κ ⟨β, c⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    show fG β (κ • (g : G ⧸ H β)) = κ • fG β g
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    exact mul_smul κ g (w β)
  · rintro κ ⟨β, c⟩ hk
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    show (⟨β, fQ β (κ • (g : G ⧸ H β))⟩ : Σ β, ∀ q, Wq q ⧸ Kc β q) = ⟨β, fQ β g⟩
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    refine congrArg (Sigma.mk β) (funext fun q => ?_)
    show ((zQ (κ * g) q : Wq q) : Wq q ⧸ Kc β q) = ((zQ g q : Wq q) : Wq q ⧸ Kc β q)
    rw [map_mul, hk, one_mul]

end Abs

end GlobalTheory.Mem.Col2.TwistLevel
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.Mem.Col2.TwistLevel


set_option maxHeartbeats 64000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_levJ_cosets_of_further : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → (∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∃ (W : ∀ v, v ∈ Q → Subgroup (GL (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))) (ψ : (∀ v : Q, ↥(W v.1 v.2)) →* ℂˣ), (∀ v hv, W v hv ≤ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0) ∧ (∀ v hv, ∃ n : ℕ, 0 < n ∧ ∀ x, Formalism.L2.Herm.InPrinc (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) v n Lb0 x → x ∈ W v hv) ∧ (∀ β v hv, (K β).lev.Uloc v ≤ (W v hv).map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) ∧ (∀ β v hv, ((((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom).subgroupOf (W v hv)).FiniteIndex) ∧ (∀ β (κ : (K β).lev.U) (z : ∀ v : Q, ↥(W v.1 v.2)), (∀ v : Q, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (z v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) → (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ψ z)) → Nonempty (TwLevJ I l Z F Q u a chOf K) := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hUl hchi hFur
  classical
  have hQb : ∀ v ∈ Q, ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal ∧ ∀ j, ((B.host.g j : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal :=
    fun v hv => underQ_prime_to_bad I hOk l u a v ((hQ v).1 hv)
  obtain ⟨H0, hH0L, hH0U⟩ := GlobalTheory.Mem.Col2.TC.levJ_herm_level I hOk hPins l Z u (F u) (hStd u) h1
  obtain ⟨W, ψ, hWl, hWQ, hWle, hWfi, hψ⟩ := hFur H0.Lb hH0L
  choose w hw using fun β0 : Ch0 u (B.R.m - 1) => GlobalTheory.Mem.Col2.TC.chartLev_stab_vec I hOk hPins l Z u (F u) (hStd u) (hfr u) h1 β0
  have hRed := GlobalTheory.Mem.Col2.TC.LevJRed.redM_levJ I hOk hPins l Z u (F u) (hStd u)
  obtain ⟨J, hJLb, hmemU, hJUl⟩ : ∃ J : Formalism.L2.Herm.StepLevelQ (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) (I.rec7 l Z).host.g (B.T u) B.R.f Q,
      J.Lb = H0.Lb ∧ (∀ x, x ∈ J.U ↔ x ∈ Formalism.L2.Herm.UAf (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) ∧
      ∀ v, bc (prV (E := (I.rec7 l Z).host.E) v) x ∈ ulocQ H0 Q W v) ∧ ∀ v, J.Uloc v = ulocQ H0 Q W v :=
    ⟨mkLevQ H0 Q W hWl hWQ (fun v hv i => (hQb v hv).2 i) (fun v hv => (hQb v hv).1), rfl, fun x => Iff.rfl, fun v => rfl⟩
  have hUP : ∀ x, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ x ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) ↔
      x ∈ Formalism.L2.Herm.UAf (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) := fun x =>
    reGL_mem_UPts _ (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ _ rfl _ x
  have hbc : ∀ v (y : GL (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)),
      bc (prV (E := (I.rec7 l Z).host.E) v) (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ y) = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v) y) :=
    fun v y => Formalism.L2.G.bc_reGL _ _ y
  have hmap : ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (H : Subgroup (GL (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))) y,
      reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ y ∈ H.map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom ↔ y ∈ H := fun v H y => by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hgQ : ∀ j v, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → v ∉ Q := fun j v hv hq => (hQb v hq).2 j hv
  have hJoff : ∀ (κ : J.U) v, v ∉ Q → reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v) κ.1) ∈ (F u).levJ.Uloc v := fun κ v hv => by
    have := ((hmemU _).1 κ.2).2 v
    rw [ulocQ_neg H0 Q W hv] at this
    rw [hH0U v]
    exact (hmap v _ _).2 this

  obtain ⟨k, hRd, -⟩ := id hR
  obtain ⟨k0, hR0⟩ := (hStd u).mid (B.R.m - 1) h1 (succ_pred_m B.R)
  let ι : Type := Σ j : Fin 2, {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}
  haveI : Finite ι := by
    haveI : ∀ j : Fin 2, Finite {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal} := fun j => by
      have hne : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ≠ 0 := Nat.cast_ne_zero.2 (l.pr.g_prime j).ne_zero
      have hfin := Ideal.finite_factors (I := Ideal.span {((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F)}) (by
        rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hne)
      have hf : Set.Finite {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) | ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal} := hfin.subset (by
        intro v hv
        exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv))
      exact hf.to_subtype
    exact Finite.instSigma
  haveI : ∀ p : ι, Finite (kv (I.rec7 l Z).host.F p.2.1) := fun p => Formalism.UG.P.glint_finite_residueField p.2.1
  haveI hfinV : Finite (∀ p : ι, Fin ((I.rec7 l Z).R.N ((I.rec7 l Z).R.m - 1)) → kv (I.rec7 l Z).host.F p.2.1) := Pi.finite
  have hTy : ∀ (κ : J.U) j v (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal),
      reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v) κ.1) ∈ (F u).levJ.Uloc v := fun κ j v hv => hJoff κ v (hgQ j v hv)
  let φ : ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), J.U →* GL (Fin (B.R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F) :=
    fun v => (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom.comp ((bc (prV (E := (I.rec7 l Z).host.E) v)).comp J.U.subtype)
  let ρ : J.U → ∀ p : ι, Matrix (Fin ((I.rec7 l Z).R.N ((I.rec7 l Z).R.m - 1))) (Fin ((I.rec7 l Z).R.N ((I.rec7 l Z).R.m - 1))) (kv (I.rec7 l Z).host.F p.2.1) :=
    fun κ p => redJS F u p.1 p.2.1 p.2.2 (bc (prV (E := (I.rec7 l Z).host.E) p.2.1) κ.1)
  have hρ1 : ρ 1 = 1 := by
    funext p
    show redM _ _ ((F u).gl.mat p.1 p.2.1 p.2.2 _ (φ p.2.1 1)) = 1
    rw [map_one (φ p.2.1)]
    exact (hRed p.1 p.2.1 p.2.2).1
  have hρm : ∀ a b, ρ (a * b) = ρ a * ρ b := fun a b => by
    funext p
    show redM _ _ ((F u).gl.mat p.1 p.2.1 p.2.2 _ (φ p.2.1 (a * b))) =
      redM _ _ ((F u).gl.mat p.1 p.2.1 p.2.2 _ (φ p.2.1 a)) * redM _ _ ((F u).gl.mat p.1 p.2.1 p.2.2 _ (φ p.2.1 b))
    rw [map_mul (φ p.2.1)]
    exact (hRed p.1 p.2.1 p.2.2).2 _ (hTy a p.1 p.2.1 p.2.2) _ (hTy b p.1 p.2.1 p.2.2)
  letI actV : MulAction J.U (∀ p : ι, Fin ((I.rec7 l Z).R.N ((I.rec7 l Z).R.m - 1)) → kv (I.rec7 l Z).host.F p.2.1) := actOfRed ρ hρ1 hρm

  have hWmem : ∀ (κ : J.U) (v : Q), bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1 ∈ W v.1 v.2 := fun κ v => by
    have := ((hmemU _).1 κ.2).2 v.1
    rwa [ulocQ_pos H0 Q W v.2] at this
  have hzQ1 : ∀ v : Q, bc (prV (E := (I.rec7 l Z).host.E) v.1) (1 : J.U).1 = 1 := fun v => by
    rw [OneMemClass.coe_one, map_one]
  have hzQm : ∀ (κ κ' : J.U) (v : Q), bc (prV (E := (I.rec7 l Z).host.E) v.1) (κ * κ').1 =
      bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1 * bc (prV (E := (I.rec7 l Z).host.E) v.1) κ'.1 := fun κ κ' v => by
    rw [Subgroup.coe_mul, map_mul]
  obtain ⟨zQ, hzQ⟩ : ∃ zQ : J.U →* (∀ v : Q, ↥(W v.1 v.2)), ∀ κ v, (zQ κ v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1 :=
    ⟨{ toFun := fun κ v => ⟨bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1, hWmem κ v⟩
       map_one' := funext fun v => Subtype.ext (hzQ1 v)
       map_mul' := fun κ κ' => funext fun v => Subtype.ext (hzQm κ κ' v) }, fun _ _ => rfl⟩
  let Kc : Ch → ∀ v : Q, Subgroup ↥(W v.1 v.2) := fun β v =>
    (((K β).lev.Uloc v.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom).subgroupOf (W v.1 v.2)
  let Hs : Ch → Subgroup J.U := fun β => (K β).lev.U.comap ((reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom.comp J.U.subtype)
  let wv : Ch → ∀ p : ι, Fin ((I.rec7 l Z).R.N ((I.rec7 l Z).R.m - 1)) → kv (I.rec7 l Z).host.F p.2.1 := fun β p => w (g β) p.1 p.2.1 p.2.2
  have hH : ∀ β (κ : J.U), κ ∈ Hs β ↔ (∀ q, zQ κ q ∈ Kc β q) ∧ κ • wv β = wv β := by
    intro β κ
    have e1 : κ ∈ Hs β ↔ ∀ v, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v) κ.1) ∈ (K β).lev.Uloc v := by
      show reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 ∈ (K β).lev.U ↔ _
      rw [(K β).lev.U_eq]
      refine ⟨fun h v => (hbc v κ.1) ▸ h.2 v, fun h => ⟨(hUP _).2 ((hmemU _).1 κ.2).1, fun v => (hbc v κ.1).symm ▸ h v⟩⟩
    have e2 : ∀ q : Q, zQ κ q ∈ Kc β q ↔ reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) q.1) κ.1) ∈ (K β).lev.Uloc q.1 := fun q => by
      show (zQ κ q).1 ∈ ((K β).lev.Uloc q.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom ↔ _
      rw [Subgroup.mem_comap, hzQ]
      rfl
    rw [e1]
    constructor
    · intro h
      refine ⟨fun q => (e2 q).2 (h q.1), ?_⟩
      funext p
      obtain ⟨j, v, hv⟩ := p
      have := h v
      rw [hUl β v (hgQ j v hv), hw (g β) v] at this
      exact this.2 j hv
    · rintro ⟨hq, hvv⟩ v
      by_cases hvQ : v ∈ Q
      · exact (e2 ⟨v, hvQ⟩).1 (hq ⟨v, hvQ⟩)
      · rw [hUl β v hvQ, hw (g β) v]
        exact ⟨hJoff κ v hvQ, fun j hvj => congrFun hvv ⟨j, v, hvj⟩⟩
  obtain ⟨Yb, hYf, aY, yb, yG, YQ, yQ, hA1, hA2, hA3, hA4, hA5⟩ :=
    assemble (fun q : Q => ↥(W q.1 q.2)) zQ Kc (fun β q => hWfi β q.1 q.2) wv Hs hH

  have hLbK : ∀ β, (K β).lev.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) J.Lb := fun β => by
    rw [hJLb, ← hH0L]
    refine Eq.trans ?_ ((F u).levJ_Lb h1 (g β))
    ext x
    exact (hRd.lb β x).trans (hR0.lb (g β) x).symm

  have hle : ∀ β, (K β).lev.U ≤ J.U.map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom := by
    intro β x hx
    have hx' := ((K β).lev.U_eq x).1 hx
    refine ⟨(reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).symm x, (hmemU _).2 ⟨(hUP _).1 (by rw [MulEquiv.apply_symm_apply]; exact hx'.1), fun v => ?_⟩,
      MulEquiv.apply_symm_apply _ _⟩
    have hv' : reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v) ((reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).symm x)) ∈ (K β).lev.Uloc v := by
      rw [← hbc, MulEquiv.apply_symm_apply]; exact hx'.2 v
    by_cases hvQ : v ∈ Q
    · rw [ulocQ_pos H0 Q W hvQ]; exact (hmap v _ _).1 (hWle β v hvQ hv')
    · rw [ulocQ_neg H0 Q W hvQ]
      rw [hUl β v hvQ, hw (g β) v] at hv'
      have h2 := hv'.1
      rw [hH0U v] at h2
      exact (hmap v _ _).1 h2

  have hJg : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal),
      ∀ x ∈ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v J.Lb,
        x ∈ J.Uloc v ↔ ∃ M ∈ HSym (I.rec7 l Z) (B.R.N (B.R.m - 1)) false v,
          (M : Matrix (Fin (B.R.N (B.R.m - 1))) (Fin (B.R.N (B.R.m - 1))) (kv (I.rec7 l Z).host.F v)) = redJS F u j v hv x := by
    intro j v hv x hx
    rw [hJLb] at hx
    rw [hJUl v, ulocQ_neg H0 Q W (hgQ j v hv)]
    have hx' : reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ x ∈ levelVL (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) v (F u).levJ.Lb := by
      rw [hH0L]; exact (reGL_mem_levelVL _ (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ _ rfl v _ x).2 hx
    have e1 : x ∈ H0.Uloc v ↔ reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ x ∈ (F u).levJ.Uloc v := by rw [hH0U v]; exact (hmap v _ _).symm
    exact e1.trans ((F u).glevJ.mem j v hv _ hx')
  have hJo : ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), v ∉ Q → v ∉ badG (I.rec7 l Z) →
      (J.Uloc v).map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom = (F u).levJ.Uloc v := by
    intro v hvQ _
    rw [hJUl v, ulocQ_neg H0 Q W hvQ]
    exact (hH0U v).symm

  have hoff : ∀ κ : J.U, ∃ y ∈ (F u).levJ.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) y = 1) ∧
      ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) y = φ v κ := by
    intro κ
    obtain ⟨y, hy, h1y, h2y⟩ := exists_off (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Q (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1)
      ((hUP _).2 ((hmemU _).1 κ.2).1)
    refine ⟨y, ((F u).levJ.U_eq y).2 ⟨hy, fun v => ?_⟩, h1y, fun v hv => (h2y v hv).trans (hbc v κ.1)⟩
    by_cases hv : v ∈ Q
    · exact (congrArg (· ∈ (F u).levJ.Uloc v) (h1y v hv)).mpr (one_mem _)
    · exact (congrArg (· ∈ (F u).levJ.Uloc v) ((h2y v hv).trans (hbc v κ.1))).mpr (hJoff κ v hv)
  choose off hoffU hoff1 hoff2 using hoff
  let ψv : ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), (F u).levJ.U →* GL (Fin (B.R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F) :=
    fun v => (bc (prV (E := (I.rec7 l Z).host.E) v)).comp (F u).levJ.U.subtype
  have htriv : ∀ a : (F u).levJ.U, (∀ v, ψv v a = 1) → (F u).levJ.chi a = 1 := fun a ha => (F u).levJ.chi_triv a (fun v _ => ha v)
  have hoffm : ∀ κ κ' : J.U, (F u).levJ.chi ⟨off (κ * κ'), hoffU _⟩ = (F u).levJ.chi ⟨off κ, hoffU κ⟩ * (F u).levJ.chi ⟨off κ', hoffU κ'⟩ := by
    intro κ κ'
    have h := htriv (⟨off (κ * κ'), hoffU _⟩ * (⟨off κ, hoffU κ⟩ * ⟨off κ', hoffU κ'⟩)⁻¹) (fun v => by
      rw [map_mul (ψv v), map_inv (ψv v), map_mul (ψv v)]
      by_cases hv : v ∈ Q
      · have e1 : ψv v ⟨off (κ * κ'), hoffU _⟩ = 1 := hoff1 _ v hv
        have e2 : ψv v ⟨off κ, hoffU κ⟩ = 1 := hoff1 _ v hv
        have e3 : ψv v ⟨off κ', hoffU κ'⟩ = 1 := hoff1 _ v hv
        rw [e1, e2, e3, mul_one, inv_one, mul_one]
      · have e1 : ψv v ⟨off (κ * κ'), hoffU _⟩ = φ v (κ * κ') := hoff2 _ v hv
        have e2 : ψv v ⟨off κ, hoffU κ⟩ = φ v κ := hoff2 _ v hv
        have e3 : ψv v ⟨off κ', hoffU κ'⟩ = φ v κ' := hoff2 _ v hv
        rw [e1, e2, e3, map_mul (φ v), mul_inv_cancel])
    rw [map_mul, map_inv, mul_inv_eq_one, map_mul] at h
    exact h
  have hoff1' : (F u).levJ.chi ⟨off 1, hoffU 1⟩ = 1 := htriv _ fun v => by
    by_cases hv : v ∈ Q
    · exact hoff1 1 v hv
    · exact (hoff2 1 v hv).trans (map_one (φ v))
  let χoff : J.U →* ℂˣ :=
    { toFun := fun κ => (F u).levJ.chi ⟨off κ, hoffU κ⟩
      map_one' := hoff1'
      map_mul' := hoffm }
  let chiJ : J.U →* ℂˣ := χoff * ψ.comp zQ
  have hchiJ : ∀ β (κ : J.U) (κ' : (K β).lev.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (K β).lev.chi κ' = chiJ κ := by
    intro β κ κ' h
    have hκ'v : ∀ v, bc (prV (E := (I.rec7 l Z).host.E) v) κ'.1 = φ v κ := fun v => by rw [h]; exact hbc v κ.1
    have hκ'U := ((K β).lev.U_eq _).1 κ'.2
    have hoK : off κ ∈ (K β).lev.U := ((K β).lev.U_eq _).2 ⟨(((F u).levJ.U_eq _).1 (hoffU κ)).1, fun v => by
      by_cases hv : v ∈ Q
      · exact (congrArg (· ∈ (K β).lev.Uloc v) (hoff1 κ v hv)).mpr (one_mem _)
      · exact (congrArg (· ∈ (K β).lev.Uloc v) ((hoff2 κ v hv).trans (hκ'v v).symm)).mpr (hκ'U.2 v)⟩
    have hoC : off κ ∈ ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U :=
      (((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U_eq _).2 ⟨(((F u).levJ.U_eq _).1 (hoffU κ)).1, fun v => by
        by_cases hv : v ∈ Q
        · exact (congrArg (· ∈ ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) (hoff1 κ v hv)).mpr (one_mem _)
        · rw [← hUl β v hv]
          exact (congrArg (· ∈ (K β).lev.Uloc v) ((hoff2 κ v hv).trans (hκ'v v).symm)).mpr (hκ'U.2 v)⟩
    obtain ⟨ψK, hψK⟩ : ∃ ψK : ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), (K β).lev.U →* GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] (v).adicCompletion (I.rec7 l Z).host.F),
        ∀ v x, ψK v x = bc (prV (E := (I.rec7 l Z).host.E) v) x.1 :=
      ⟨fun v => (bc (prV (E := (I.rec7 l Z).host.E) v)).comp (K β).lev.U.subtype, fun _ _ => rfl⟩
    have hq : ∀ v, ψK v (κ' * ⟨off κ, hoK⟩⁻¹) = ψK v κ' * (ψK v ⟨off κ, hoK⟩)⁻¹ := fun v =>
      (map_mul (ψK v) _ _).trans (congrArg (ψK v κ' * ·) (map_inv (ψK v) _))
    have hq_off : ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) (κ' * ⟨off κ, hoK⟩⁻¹).1 = 1 := fun v hv => by
      have e2 : ψK v ⟨off κ, hoK⟩ = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v) κ.1) := (hψK v _).trans (hoff2 κ v hv)
      have e3 : ψK v κ' = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v) κ.1) :=
        (hψK v κ').trans ((congrArg (bc (prV (E := (I.rec7 l Z).host.E) v)) h).trans (hbc v κ.1))
      have e4 : ψK v κ' * (ψK v ⟨off κ, hoK⟩)⁻¹ = 1 :=
        (congrArg₂ (fun a b : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] (v).adicCompletion (I.rec7 l Z).host.F) => a * b⁻¹) e3 e2).trans (mul_inv_cancel _)
      exact (hψK v _).symm.trans ((hq v).trans e4)
    have hq_Q : ∀ v : Q, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (zQ κ v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) (κ' * ⟨off κ, hoK⟩⁻¹).1 := fun v => by
      have e2 : ψK v.1 ⟨off κ, hoK⟩ = 1 := (hψK v.1 _).trans (hoff1 κ v.1 v.2)
      have e4 : ψK v.1 κ' * (ψK v.1 ⟨off κ, hoK⟩)⁻¹ = ψK v.1 κ' :=
        (congrArg (fun b : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] (v.1).adicCompletion (I.rec7 l Z).host.F) => ψK v.1 κ' * b⁻¹) e2).trans ((congrArg (ψK v.1 κ' * ·) inv_one).trans (mul_one _))
      have e : ψK v.1 (κ' * ⟨off κ, hoK⟩⁻¹) = ψK v.1 κ' := (hq v.1).trans e4
      have e5 : reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (zQ κ v).1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) := congrArg (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _) (hzQ κ v)
      have e6 : ψK v.1 κ' = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) :=
        (hψK v.1 κ').trans ((congrArg (bc (prV (E := (I.rec7 l Z).host.E) v.1)) h).trans (hbc v.1 κ.1))
      exact e5.trans (e6.symm.trans (e.symm.trans (hψK v.1 _)))
    calc (K β).lev.chi κ' = (K β).lev.chi ((κ' * ⟨off κ, hoK⟩⁻¹) * ⟨off κ, hoK⟩) := congrArg _ (inv_mul_cancel_right κ' _).symm
      _ = (K β).lev.chi (κ' * ⟨off κ, hoK⟩⁻¹) * (K β).lev.chi ⟨off κ, hoK⟩ := map_mul _ _ _
      _ = ψ (zQ κ) * (F u).levJ.chi ⟨off κ, hoffU κ⟩ := congrArg₂ (· * ·) (hψ β _ (zQ κ) hq_Q hq_off)
        ((hchi β ⟨off κ, hoK⟩ ⟨off κ, hoC⟩ rfl (fun v hv => hoff1 κ v hv)).trans
          ((F u).levJ_chi h1 (g β) ⟨off κ, hoC⟩ ⟨off κ, hoffU κ⟩ rfl))
      _ = chiJ κ := mul_comm _ _
  have hyGs : ∀ (κ : J.U) y (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal),
      yG (κ • y) ⟨j, v, hv⟩ = redJS F u j v hv (bc (prV (E := (I.rec7 l Z).host.E) v) κ.1) *ᵥ yG y ⟨j, v, hv⟩ := by
    intro κ y j v hv
    exact congrFun (hA3 κ y) ⟨j, v, hv⟩
  have hyI : ∀ y y', (fun j v hv => yG y ⟨j, v, hv⟩) = (fun (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) => yG y' ⟨j, v, hv⟩) →
      yQ y = yQ y' → y = y' := by
    intro y y' hG hQ'
    refine hA4 y y' (funext fun p => ?_) hQ'
    obtain ⟨j, v, hv⟩ := p
    exact congrFun (congrFun (congrFun hG j) v) hv
  have hyQ : ∀ (κ : J.U) y, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → yQ (κ • y) = yQ y := by
    intro κ y hκ
    exact hA5 κ y (funext fun q => Subtype.ext ((hzQ κ q).trans (hκ q.1 q.2)))
  exact ⟨{
    levJ := J, Yb := Yb, YbFin := hYf, YbAct := aY, yb := yb, yb_orbit := hA1, lb := hLbK, «le» := hle,
    stab := fun β κ => hA2 β κ, chiJ := chiJ, chiJ_eq := hchiJ, J_g := hJg, J_off := hJo,
    yG := fun y j v hv => yG y ⟨j, v, hv⟩, yG_smul := hyGs,
    YQ := YQ, yQ := yQ, y_inj := hyI, yQ_off := hyQ }⟩

end GlobalTheory.Mem.Col2.TwistLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPenultimateLevelCouplingCosets
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.Mem.Col2.TwistLevel


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_levJ_cosets : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → Nonempty (TwLevJ I l Z F Q u a chOf K) := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hFin hUl hchi
  exact exists_levJ_cosets_of_further I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hUl hchi
    (GlobalTheory.T.furtherPlaces_group_contains_chart_levels I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hFin hUl hchi)

end GlobalTheory.Mem.Col2.TwistLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPenultimateLevelCouplingCosetsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_penultimateLevel_couplingCosets : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → Nonempty (TwLevJ I l Z F Q u a chOf K) := by
  first | exact @GlobalTheory.Mem.Col2.TwistLevel.exists_levJ_cosets | exact GlobalTheory.Mem.Col2.TwistLevel.exists_levJ_cosets | (intros; apply GlobalTheory.Mem.Col2.TwistLevel.exists_levJ_cosets <;> assumption)
end
