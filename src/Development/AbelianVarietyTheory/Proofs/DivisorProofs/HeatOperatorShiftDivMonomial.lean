module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BinomialFlagDimensionDegreeBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermIdentityDescendsGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermIdentityDescendsGenericFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TermDescend

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ₀ σ₁ σ₂ : Q.SecB k α) (τ₀ τ₁ τ₂ : SecM Y.q.left Q.P.L k) (a b : R), IsTerm Y k α σ₀ τ₀ → IsTerm Y k α σ₁ τ₁ → IsTerm Y k α σ₂ τ₂ → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ₀ r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval τ₁ r z J + gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * sval τ₂ r z J) → ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ₀ (DegPre.prB Q (FractionRing R)).left z J = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval σ₁ (DegPre.prB Q (FractionRing R)).left z J + gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * sval σ₂ (DegPre.prB Q (FractionRing R)).left z J := by
  intro R _ _ Q O _ _ _ oa Y k α σ₀ σ₁ σ₂ τ₀ τ₁ τ₂ a b h₀ h₁ h₂ H z J hJ
  obtain ⟨Z, p, w, y, hw, hp, hinj, hy⟩ := GlobalTheory.RayLift.exists_flat_lift R Q O oa Y z
  subst hw
  obtain ⟨J', hJ', hJJ⟩ := exists_good Q.P.L Q.P.isLB w (K := (DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left)
    (fun ψ => p ≫ ψ) J (fun ψ ψ' e => by rw [(cancel_epi p).1 e]) (fun ψ => by
      rw [Scheme.Hom.comp_apply]; exact hJ ψ)
  have hfun : (fun ψ => J' (p ≫ ψ)) = J := funext hJJ
  let T : Over (Sp R) := Over.mk (y ≫ Y.H.hom)
  let x : T ⟶ Y.H := Over.homMk y rfl
  let v : (Z.presheaf.stalk w)ˣ := val ((Y.Φ T x).s α) (𝟙 _) w J'
  have e₀ : sval τ₀ y w J' = sval σ₀ (y ≫ Y.q.left) w J' * v.val := h₀ T x w J' hJ'
  have e₁ : sval τ₁ y w J' = sval σ₁ (y ≫ Y.q.left) w J' * v.val := h₁ T x w J' hJ'
  have e₂ : sval τ₂ y w J' = sval σ₂ (y ≫ Y.q.left) w J' * v.val := h₂ T x w J' hJ'
  have E := H Z y w J' hJ'
  have hH : y ≫ Y.H.hom = p ≫ ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) := by
    rw [← Category.assoc, ← hy, Category.assoc, Over.w Y.q]
  rw [e₀, e₁, e₂, ← _root_.mul_assoc, ← _root_.mul_assoc, ← add_mul] at E
  have E' := (Units.mul_left_inj _).1 E
  rw [hH, hy, GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ', GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ',
    GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ', GlobalTheory.HeatDefect.gs_comp_stalk p _ w ⊤ trivial,
    GlobalTheory.HeatDefect.gs_comp_stalk p _ w ⊤ trivial, hfun, ← map_mul, ← map_mul, ← map_add] at E'
  exact hinj E'

end GlobalTheory.TermDescend
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermIdentityDescendsGenericFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierTerm_identity_descends_genericFibre : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ₀ σ₁ σ₂ : Q.SecB k α) (τ₀ τ₁ τ₂ : SecM Y.q.left Q.P.L k) (a b : R), IsTerm Y k α σ₀ τ₀ → IsTerm Y k α σ₁ τ₁ → IsTerm Y k α σ₂ τ₂ → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ₀ r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval τ₁ r z J + gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * sval τ₂ r z J) → ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ₀ (DegPre.prB Q (FractionRing R)).left z J = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval σ₁ (DegPre.prB Q (FractionRing R)).left z J + gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * sval σ₂ (DegPre.prB Q (FractionRing R)).left z J := by
  first | exact @GlobalTheory.TermDescend.main | exact GlobalTheory.TermDescend.main | (intros; apply GlobalTheory.TermDescend.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConstMulDerivationTerm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConstMulDerivationTerm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatOpConst

open GlobalTheory.HeatGlue

section General

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}

theorem op_constFn_mul {vv : Fin n → TanM (𝟙 (Sp R)) G} {dd : Fin n → Fld G.left} (hinv : ∀ a, IsInv G (vv a) (dd a))
    {D : R → R} (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R) {d : Fld G.left} {W : G.left.Opens}
    (hd : IsLift G D W d) (p p' : Γ(G.left, W)) (k : ℕ) {O : G.left.Opens} (hO : O ≤ W) (c : R) (f : Γ(G.left, O)) :
    op G dd Θ u d p p' k O (constFn G.hom O c * f) =
      constFn G.hom O c * op G dd Θ u d p p' k O f + constFn G.hom O (2 * (k : R) * D c) * f := by
  have e1 : ∀ a (g : Γ(G.left, O)), dd a O (constFn G.hom O c * g) = constFn G.hom O c * dd a O g := fun a g => by
    rw [(isDer_of_isField (hinv a).1 le_top).2, IsInv.apply_constFn G (vv a) (dd a) (hinv a) O c, mul_zero, add_zero]
  have e2 : d O (constFn G.hom O c * f) = constFn G.hom O c * d O f + f * constFn G.hom O (D c) := by
    rw [(isDer_of_isField hd.1 hO).2, hd.2 O hO c]
  have e3 : constFn G.hom O (k : R) = (k : Γ(G.left, O)) := by simp [constFn]
  have e4 : ∀ a b : Γ(G.left, O), a * (constFn G.hom O c * b) = constFn G.hom O c * (a * b) := fun a b => by ring
  unfold op
  rw [e2, constFn_mul, constFn_mul, constFn_two, e3]
  simp only [e1, e4, ← Finset.mul_sum]
  ring

variable {X Y Z : Scheme.{0}}

theorem gs_rsT (r : Z ⟶ Y) (z : Z) {U V : Y.Opens} (hle : V ≤ U) (h : r z ∈ V) (a : Γ(Y, U)) :
    gs r z V (rsT a V) = gs r z U a := by
  rw [GlobalTheory.KS.rsT_of_le hle]
  exact gs_res r z hle h a

theorem gs_constFn_of_mem (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) {V : Y.Opens} (h : r z ∈ V) (e : R) :
    gs r z V (constFn p V e) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom e) := by
  rw [← GlobalTheory.HeatTermLin.gs_constFn, ← resG_constFn p (le_top : V ≤ ⊤)]
  exact gs_res r z le_top h _

theorem le_wchart {m : Y ⟶ X} {L : LB X} {V : Y.Opens} {j : L.ι} (h : V ≤ m ⁻¹ᵁ L.U j) :
    V ≤ LB.wchart L (K := Fin 1) (fun _ => m) (fun _ => j) := fun _ hy => Set.mem_iInter.2 fun _ => h hy

end General

theorem heat_const_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (vv : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vv a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Q.P.L dd ⇑D) (k : ℕ) (c : R) (τ τ' τu τu' : SecM Y.q.left Q.P.L k), h.Acts k τ τ' → h.Acts k τu τu' → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval τu r z J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ' r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval τu' r z J + gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (2 * (k : R) * D c)) * sval τu r z J := by
  intro R _ _ Q O _ _ _ oa Y n vv dd hinv D h k c τ τ' τu τu' a₁ a₂ hτ Z r z J hJ
  have hle : ∀ i, h.W i ≤ LB.wchart Q.P.L (K := Fin 1) (fun _ => Y.q.left) (fun _ => h.j i) := fun i =>
    le_wchart (h.le i)
  have s₁ : ∀ i, rsT (τ.f fun _ => h.j i) (h.W i) = constFn Y.H.hom (h.W i) c * rsT (τu.f fun _ => h.j i) (h.W i) := by
    intro i
    refine fn_ext fun y hy => ?_
    obtain ⟨I, hI, eI⟩ := exists_good Q.P.L Q.P.isLB y (K := Unit) (fun _ => 𝟙 _ ≫ Y.q.left) (fun _ => h.j i)
      (fun _ _ _ => rfl) (fun _ => h.le i hy)
    have e := hτ _ (𝟙 _) y I hI
    rw [sval_of τ _ y I (fun _ => h.j i) (fun _ => eI ()), sval_of τu _ y I (fun _ => h.j i) (fun _ => eI ())] at e
    refine (gs_rsT (𝟙 _) y (hle i) hy _).trans (e.trans (Eq.symm ?_))
    exact (gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_constFn_of_mem _ _ y hy c)
      (gs_rsT (𝟙 _) y (hle i) hy _))
  have s₂ : ∀ i, rsT (τ'.f fun _ => h.j i) (h.W i) = constFn Y.H.hom (h.W i) c * rsT (τu'.f fun _ => h.j i) (h.W i) +
      constFn Y.H.hom (h.W i) (2 * (k : R) * D c) * rsT (τu.f fun _ => h.j i) (h.W i) := by
    intro i
    rw [a₁ i, a₂ i, s₁ i]
    exact op_constFn_mul hinv h.Θ h.u (h.lift i) (h.p i) (h.p' i) k le_rfl c _
  obtain ⟨i, hi⟩ : ∃ i, r z ∈ h.W i := TopologicalSpace.Opens.mem_iSup.1 (h.cover.ge trivial)
  have t : ∀ s : SecM Y.q.left Q.P.L k, sval s r z J =
      (trF (K := Fin 1) (fun _ => Y.q.left) (fun _ => (k : ℤ)) r z (fun _ => J (r ≫ Y.q.left)) (fun _ => h.j i)).val *
        gs r z (h.W i) (rsT (s.f fun _ => h.j i) (h.W i)) := fun s =>
    (sec_trans s r z (hJ.mem _ r) (hle i hi)).trans (congrArg _ (gs_rsT r z (hle i) hi _).symm)
  rw [t τ', t τu', t τu, s₂ i, gs_add r z _ hi, gs_mul r z _ hi, gs_mul r z _ hi, gs_constFn_of_mem _ r z hi,
    gs_constFn_of_mem _ r z hi]
  ring

end GlobalTheory.HeatOpConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConstMulDerivationTermStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperator_const_mul_derivation_term : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (vv : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vv a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Q.P.L dd ⇑D) (k : ℕ) (c : R) (τ τ' τu τu' : SecM Y.q.left Q.P.L k), h.Acts k τ τ' → h.Acts k τu τu' → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval τu r z J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ' r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval τu' r z J + gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (2 * (k : R) * D c)) * sval τu r z J := by
  first | exact @GlobalTheory.HeatOpConst.heat_const_mul | exact GlobalTheory.HeatOpConst.heat_const_mul | (intros; apply GlobalTheory.HeatOpConst.heat_const_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecBEqEverywhereOfGenericAgreeConst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecBEqEverywhereOfGenericAgreeConst
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecBGenericAgree

variable {R : Type} [CommRing R] [IsDomain R]

theorem isUnit_jK_app (c : R) (hc : c ≠ 0) :
    IsUnit ((jK R).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := by
  have h := congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  have hu : IsUnit (algebraMap R (FractionRing R) c) :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)).isUnit
  have := hu.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
  rw [h] at this
  exact this

theorem isUnit_gs (Q : DegPre R) (c : R) (hc : c ≠ 0) (z : (DegPre.BF Q (FractionRing R)).left) :
    IsUnit (gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := by
  have e1 : (DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom =
      ((fst (TF (R := R) (FractionRing R)) Q.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
    rw [Over.w (DegPre.prB Q (FractionRing R)), Category.assoc]
    exact (Over.w (fst (TF (R := R) (FractionRing R)) Q.P.A)).symm
  rw [e1, ← gs_pull ((fst (TF (R := R) (FractionRing R)) Q.P.A).left ≫ jFK (R := R) (FractionRing R)) (jK R) z ⊤ trivial,
    gs_eq _ z (jK R ⁻¹ᵁ ⊤) trivial]
  exact ((isUnit_jK_app c hc).map _).map _

theorem f_eq (Q : DegPre R) (k : ℕ) (β : Q.X) (s s' : Q.SecB k β) (c : R) (hc : c ≠ 0)
    (H : ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι),
      Good Q.P.L z J →
      gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) *
          sval s (DegPre.prB Q (FractionRing R)).left z J =
        gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) *
          sval s' (DegPre.prB Q (FractionRing R)).left z J)
    (j : Fin 4 → Q.P.L.ι) : s.f j = s'.f j := by
  set p := (DegPre.prB Q (FractionRing R)).left
  have H' : ∀ z J, Good Q.P.L z J → sval s p z J = sval s' p z J := fun z J hJ =>
    (isUnit_gs Q c hc z).mul_left_cancel (H z J hJ)
  refine GlobalTheory.IntegralExpansion.prB_app_injective Q _ (fn_ext fun y hy => ?_)
  choose I hI using fun χ : (DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left => exists_chart Q.P.isLB (χ y)
  have hI' : Good Q.P.L y I := hI
  have m := hI'.mem (DegPre.famφB Q β) p
  rw [gs_pull (𝟙 _) p y _ hy, gs_pull (𝟙 _) p y _ hy, Category.id_comp]
  exact (sec_trans s p y hy m).trans ((congrArg _ (H' y I hI')).trans (sec_trans s' p y hy m).symm)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (β : Q.X) (s s' : Q.SecB k β) (c : R), c ≠ 0 → (∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval s (DegPre.prB Q (FractionRing R)).left z J = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval s' (DegPre.prB Q (FractionRing R)).left z J) → ∀ (Z : Scheme.{0}) (x : Z ⟶ Q.P.A.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval s x z J = sval s' x z J := by
  intro R _ _ Q k β s s' c hc H Z x z J _
  have hf : s.f = s'.f := funext (f_eq Q k β s s' c hc H)
  show gs x z _ (s.f _) = gs x z _ (s'.f _)
  rw [hf]

end GlobalTheory.SecBGenericAgree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecBEqEverywhereOfGenericAgreeConstStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secB_eq_everywhere_of_generic_agree_const : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (β : Q.X) (s s' : Q.SecB k β) (c : R), c ≠ 0 → (∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval s (DegPre.prB Q (FractionRing R)).left z J = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval s' (DegPre.prB Q (FractionRing R)).left z J) → ∀ (Z : Scheme.{0}) (x : Z ⟶ Q.P.A.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval s x z J = sval s' x z J := by
  first | exact @GlobalTheory.SecBGenericAgree.main | exact GlobalTheory.SecBGenericAgree.main | (intros; apply GlobalTheory.SecBGenericAgree.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorShiftDivMonomial
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.Heat

theorem heat_div_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ (e : ℕ), 1 ≤ e → ∀ (mu α : P.D.toPre.X) (N : Fin m → ℕ) (σ σ' : P.D.toPre.SecB e α) (σ₁ σ₁u σ₁' σ₁u' : P.D.toPre.SecB e (α + e • mu)), TActs Y h e α σ σ' → ShiftEq P.D.toPre e mu α σ σ₁ 0 σ₁ → ShiftEq P.D.toPre e mu α σ' σ₁' 0 σ₁' → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁ x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u x z J) → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁' x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u' x z J) → ∃ σ₁u'' : P.D.toPre.SecB e (α + e • mu), TActs Y h e (α + e • mu) σ₁u σ₁u'' ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁u'' x z J = sval σ₁u' x z J - gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (2 * (e : ChartRing k m d) * ∑ i, (N i : ChartRing k m d) * q i)) * sval σ₁u x z J := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ B' _ π₁ π₂ c' h1 h2 h3 h4 e he mu α N σ σ' σ₁ σ₁u σ₁' σ₁u' hT hS hS' hv hv'
  letI := H.starRing
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _

  clear hρ h1 h2 h3 h4 hΘ hmon hli hab
  have f1 : ∀ x y, D (x + y) = D x + D y := D.map_add
  have f2 : ∀ (z : ℤ) (x : ChartRing k m d), D (z • x) = z • D x := fun z x => map_zsmul D z x
  have f3 : D 1 = 0 := D.map_one_eq_zero
  have f4 : ∀ x y, D (x * y) = x • D y + y • D x := D.leibniz
  generalize (⇑D : ChartRing k m d → ChartRing k m d) = f at f1 f2 f3 f4 hq h hb hdef ⊢
  letI : Algebra ℤ (ChartRing k m d) := Ring.toIntAlgebra _
  let D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d) :=
    { toFun := f, map_add' := f1, map_smul' := fun z x => f2 z x, map_one_eq_zero' := f3, leibniz' := f4 }
  have hA1 := heat_acts_on_terms (ChartRing k m d) P.D (𝓞 E) P.oD Y n' v' dd hdd D' h hb e (α + e • mu) σ₁
  have hA2 := heat_acts_on_terms (ChartRing k m d) P.D (𝓞 E) P.oD Y n' v' dd hdd D' h hb e (α + e • mu) σ₁u
  obtain ⟨σ₁'', hA1⟩ := hA1
  obtain ⟨σ₁u'', hA2⟩ := hA2
  refine ⟨σ₁u'', hA2, ?_⟩
  have hd : ShiftEq P.D.toPre e mu α σ' σ₁'' 0 σ₁ := hdef e mu α σ σ' σ₁ σ₁'' he hS hT hA1
  obtain ⟨⟨u, hu, hc⟩, -⟩ := ReciprocityTheory.ChartRestriction.G.DVR.gen_fe (D := P.D.toPre) (F := FractionRing (ChartRing k m d))
    GlobalTheory.SemiRigid.globalFns e mu α
  have hU : ∀ z J, Good P.D.toPre.P.L z J → sval σ₁'' (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z J =
      sval σ₁' (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z J := by
    intro z J hJ
    have E1 := GlobalTheory.HeatDefect.shiftEq_at hd u hu hc (𝟙 _) z J hJ
    have E2 := GlobalTheory.HeatDefect.shiftEq_at hS' u hu hc (𝟙 _) z J hJ
    simp only [Category.id_comp, GlobalTheory.HeatDefect.scal_zero, zero_mul, add_zero] at E1 E2
    rw [E1, E2]
  obtain ⟨τ₁, τ₁'', t1, t1'', a1⟩ := hA1
  obtain ⟨τu, τu'', tu, tu'', a2⟩ := hA2
  have hτ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι),
      Good P.D.toPre.P.L z J → sval τ₁ r z J = gs (r ≫ Y.H.hom) z ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval τu r z J := by
    intro Z r z J hJ
    let x : Over.mk (r ≫ Y.H.hom) ⟶ Y.H := Over.homMk r rfl
    have e1 := t1 _ x z J hJ
    have e2 := tu _ x z J hJ
    have e3 := hv Z (r ≫ Y.q.left) z J hJ
    have hw : (r ≫ Y.q.left) ≫ P.D.toPre.P.A.hom = r ≫ Y.H.hom := by rw [Category.assoc, Over.w]
    rw [hw] at e3
    change sval τ₁ r z J = _ at e1
    change sval τu r z J = _ at e2
    rw [Over.comp_left] at e1 e2
    change _ = sval σ₁ (r ≫ Y.q.left) z J * _ at e1
    change _ = sval σ₁u (r ≫ Y.q.left) z J * _ at e2
    rw [e1, e2, e3, _root_.mul_assoc]

  have hτ'' := GlobalTheory.T.heatOperator_const_mul_derivation_term (ChartRing k m d) P.D.toPre (𝓞 E) P.oD Y n' (fun a => v' a) dd hdd D' h e
    (∏ i, bdParam k m d i ^ N i) τ₁ τ₁'' τu τu'' a1 a2 hτ
  have hP := GlobalTheory.T.fourierTerm_identity_descends_genericFibre (ChartRing k m d) P.D.toPre (𝓞 E) P.oD Y e (α + e • mu) σ₁'' σ₁u'' σ₁u τ₁'' τu'' τu
    (∏ i, bdParam k m d i ^ N i) (2 * (e : ChartRing k m d) * D' (∏ i, bdParam k m d i ^ N i)) t1'' tu'' tu hτ''
  have hpow : ∀ (x c : ChartRing k m d), D' x = c * x → ∀ n : ℕ, D' (x ^ n) = (n : ChartRing k m d) * c * x ^ n := by
    intro x c hx n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Derivation.leibniz, ih, hx, smul_eq_mul, smul_eq_mul]
      push_cast; ring
  have hDt : ∀ s : Finset (Fin m), D' (∏ i ∈ s, bdParam k m d i ^ N i) =
      (∑ i ∈ s, (N i : ChartRing k m d) * q i) * ∏ i ∈ s, bdParam k m d i ^ N i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz, ih,
        hpow _ (q a) (hq a) (N a), smul_eq_mul, smul_eq_mul]
      ring
  have hne0 : ∀ i, bdParam k m d i ≠ 0 := fun i h => by
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1)) h
    simp [MvPowerSeries.coeff_X] at this
  have hne : (∏ i, bdParam k m d i ^ N i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hne0 i)
  have hg : ∀ {Z : Scheme.{0}} (r : Z ⟶ P.D.toPre.P.A.left) (z : Z) (c : ChartRing k m d),
      gs (r ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom c) =
        GlobalTheory.HeatMod.germConstHom (r ≫ P.D.toPre.P.A.hom) z c := fun r z c =>
    (GlobalTheory.HeatTermLin.gs_constFn _ r z c).symm.trans (GlobalTheory.HeatMod.gs_constFn_eq_germConstHom _ r z c)
  have key := GlobalTheory.T.secB_eq_everywhere_of_generic_agree_const (ChartRing k m d) P.D.toPre e (α + e • mu) σ₁u''
    (σ₁u' - constFn P.D.toPre.P.A.hom ⊤ (2 * (e : ChartRing k m d) * ∑ i, (N i : ChartRing k m d) * q i) • σ₁u)
    (∏ i, bdParam k m d i ^ N i) hne (by
      intro z J hJ
      have a1 := hP z J hJ
      have a2 := hU z J hJ
      have a3 := hv' _ (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z J hJ
      rw [GlobalTheory.HeatMod.sval_sub_constFn_smul _ _ _ _ _ _ hJ]
      rw [hDt] at a1
      simp only [hg] at a1 a3 ⊢
      simp only [map_mul, map_natCast, map_ofNat] at a1 ⊢
      linear_combination a2 + a3 - a1)
  intro Z x z J hJ
  rw [key Z x z J hJ, GlobalTheory.HeatMod.sval_sub_constFn_smul _ _ _ _ _ _ hJ, hg]

end GlobalTheory.Heat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorShiftDivMonomialStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperator_shift_div_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ (e : ℕ), 1 ≤ e → ∀ (mu α : P.D.toPre.X) (N : Fin m → ℕ) (σ σ' : P.D.toPre.SecB e α) (σ₁ σ₁u σ₁' σ₁u' : P.D.toPre.SecB e (α + e • mu)), TActs Y h e α σ σ' → ShiftEq P.D.toPre e mu α σ σ₁ 0 σ₁ → ShiftEq P.D.toPre e mu α σ' σ₁' 0 σ₁' → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁ x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u x z J) → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁' x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u' x z J) → ∃ σ₁u'' : P.D.toPre.SecB e (α + e • mu), TActs Y h e (α + e • mu) σ₁u σ₁u'' ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁u'' x z J = sval σ₁u' x z J - gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (2 * (e : ChartRing k m d) * ∑ i, (N i : ChartRing k m d) * q i)) * sval σ₁u x z J := by
  first | exact @GlobalTheory.Heat.heat_div_monomial | exact GlobalTheory.Heat.heat_div_monomial | (intros; apply GlobalTheory.Heat.heat_div_monomial <;> assumption)
end
