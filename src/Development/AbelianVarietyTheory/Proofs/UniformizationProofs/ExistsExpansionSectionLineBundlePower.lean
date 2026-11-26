module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactTermAfterTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThickTorusLevelWeightExpansion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueTwistedSectionOfCompatibleLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueLimit
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.SecLimit

section Algebra

universe u

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {W W' W'' : Type u} [CommRing W] [CommRing W']
  [CommRing W''] {m : ℕ}

def comb (c : R →+* W) (b : Fin m → W) (z : Fin m → R) : W := ∑ i, c (z i) * b i

def IsBas (c : R →+* W) (S : Set W) (b : Fin m → W) : Prop :=
  (∀ i, b i ∈ S) ∧ ∀ s ∈ S, ∃! z : Fin m → R, s = comb c b z

theorem map_comb {c : R →+* W} {c' : R' →+* W'} {ρ : W →+* W'} {g : R →+* R'} (h : ∀ a, ρ (c a) = c' (g a))
    (b : Fin m → W) (z : Fin m → R) : ρ (comb c b z) = comb c' (fun i => ρ (b i)) (fun i => g (z i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, map_sum, map_mul, h]

theorem comb_vecMul {c : R →+* W} {b v : Fin m → W} {a : Matrix (Fin m) (Fin m) R} (h : ∀ i, v i = comb c b (a i))
    (z : Fin m → R) : comb c v z = comb c b (Matrix.vecMul z a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, h, Matrix.vecMul, dotProduct, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

theorem comb_single (c : R →+* W) (b : Fin m → W) (i : Fin m) : b i = comb c b (Pi.single i 1) := by
  rw [comb, Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, zero_mul])
    (fun h => (h (Finset.mem_univ _)).elim), Pi.single_eq_same, map_one, _root_.one_mul]

theorem IsBas.transfer {c : R →+* W} {c' : R →+* W'} {ρ : W →+* W'} (h : ∀ a, ρ (c a) = c' a)
    (hρ : Function.Injective ρ) (U : W'ˣ) {S : Set W} {S' : Set W'}
    (hS : ∀ s', s' ∈ S' ↔ ∃ s ∈ S, s' = ρ s * U) {b : Fin m → W} (hb : IsBas c S b) :
    IsBas c' S' (fun i => ρ (b i) * U) := by
  refine ⟨fun i => (hS _).2 ⟨_, hb.1 i, rfl⟩, fun s' hs' => ?_⟩
  obtain ⟨s, hs, rfl⟩ := (hS _).1 hs'
  refine (existsUnique_congr fun z => ?_).1 (hb.2 s hs)
  have e : comb c' (fun i => ρ (b i) * U) z = ρ (comb c b z) * U := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [comb, map_sum, map_mul, h, Finset.sum_mul, _root_.mul_assoc]
  rw [e, Units.mul_left_inj, hρ.eq_iff]

theorem IsBas.reduce {c : R →+* W} {c' : R' →+* W'} {c'' : R'' →+* W''} {ρ : W →+* W'} {ρ' : W' →+* W''}
    {g : R →+* R'} {g' : R' →+* R''} [IsLocalHom g'] (h : ∀ a, ρ (c a) = c' (g a)) (h' : ∀ a, ρ' (c' a) = c'' (g' a))
    {S : Set W} {S' : Set W'} {S'' : Set W''} (hS : ∀ s ∈ S, ρ s ∈ S') (hS' : ∀ s ∈ S', ρ' s ∈ S'')
    (hl : ∀ s ∈ S'', ∃ t ∈ S, s = ρ' (ρ t)) {b : Fin m → W} {b' : Fin m → W'} {b'' : Fin m → W''}
    (hb : IsBas c S b) (hb' : IsBas c' S' b') (hb'' : IsBas c'' S'' b'') : IsBas c' S' (fun i => ρ (b i)) := by
  choose a ha _ using fun i => hb'.2 _ (hS _ (hb.1 i))
  choose e he _ using fun i => hb''.2 _ (hS' _ (hb'.1 i))
  choose t ht ht' using fun i => hl _ (hb''.1 i)
  choose d hd _ using fun i => hb.2 _ (ht i)
  let A : Matrix (Fin m) (Fin m) R' := Matrix.of a
  let E : Matrix (Fin m) (Fin m) R'' := Matrix.of e
  let D : Matrix (Fin m) (Fin m) R'' := Matrix.of fun l i => g' (g (d l i))
  have h₁ : D * (A.map g' * E) = 1 := by
    ext l j
    have e₁ : b'' l = comb c'' b'' (Matrix.vecMul (D l) (A.map g' * E)) := by
      rw [← Matrix.vecMul_vecMul, ← comb_vecMul (a := E) he, ← comb_vecMul (v := fun i => ρ' (ρ (b i)))
        (a := A.map g') fun i => by rw [ha i, map_comb h']; rfl]
      rw [ht' l, hd l, map_comb h, map_comb h']; rfl
    have := congrFun ((hb''.2 _ (hb''.1 l)).unique e₁ (comb_single c'' b'' l)) j
    rw [Matrix.one_apply, ← Matrix.mul_apply_eq_vecMul] at *
    rw [this, Pi.single_apply]
    simp only [eq_comm]
  have hA : IsUnit A.det := by
    have := congrArg Matrix.det h₁
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one, mul_left_comm] at this
    have h₂ : IsUnit (A.map g').det := IsUnit.of_mul_eq_one _ this
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h₂
    exact IsUnit.of_map g' _ h₂
  refine ⟨fun i => hS _ (hb.1 i), fun s hs => ?_⟩
  obtain ⟨y, hy, hy'⟩ := hb'.2 s hs
  refine ⟨Matrix.vecMul y A⁻¹, ?_, fun z hz => ?_⟩
  · beta_reduce
    rw [comb_vecMul (a := A) ha, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]
    exact hy
  · beta_reduce at hz
    rw [comb_vecMul (a := A) ha] at hz
    rw [← hy' _ hz, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hA, Matrix.vecMul_one]

theorem existsUnique_limit (I : Ideal R) [IsAdicComplete I R] {T : ℕ → Type u} [∀ e, CommRing (T e)]
    {c : R →+* W} {c' : ∀ e, R ⧸ I ^ (e + 1) →+* T e} {ρ : ∀ e, W →+* T e} {τ : ∀ e, T (e + 1) →+* T e}
    (h : ∀ e a, ρ e (c a) = c' e (Ideal.Quotient.mk _ a)) (hτ : ∀ e s, τ e (ρ (e + 1) s) = ρ e s)
    {S : Set W} {S' : ∀ e, Set (T e)} {b : Fin m → W} (hS : ∀ z, comb c b z ∈ S)
    (hb : IsBas c S b) (hb' : ∀ e, IsBas (c' e) (S' e) (fun i => ρ e (b i)))
    (f : ∀ e, T e) (hf : ∀ e, f e ∈ S' e) (hc : ∀ e, τ e (f (e + 1)) = f e) : ∃! s, s ∈ S ∧ ∀ e, ρ e s = f e := by
  choose z hz hz' using fun e => (hb' e).2 _ (hf e)
  choose y hy using fun e i => Ideal.Quotient.mk_surjective (z e i)
  have key : ∀ e (x : Fin m → R), ρ e (comb c b x) = f e ↔ ∀ i, x i - y e i ∈ I ^ (e + 1) := fun e x => by
    rw [map_comb (h e)]
    simp only [← Ideal.Quotient.eq, hy]
    exact ⟨fun H => congrFun (hz' e _ H.symm), fun H => by rw [funext H]; exact (hz e).symm⟩
  have step : ∀ e i, y (e + 1) i - y e i ∈ I ^ (e + 1) := fun e => (key e _).1 (by
    rw [← hτ, (key (e + 1) _).2 fun i => by rw [sub_self]; exact zero_mem _, hc])
  have hL : ∀ i, ∃ L : R, ∀ e, L - y e i ∈ I ^ (e + 1) := fun i => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := R) inferInstance (f := fun e => y e i)
      ((AdicCompletion.isAdicCauchy_iff I R _).2 fun n => by
        rw [smul_eq_mul, Ideal.mul_top]
        exact (SModEq.sub_mem.2 (Ideal.pow_le_pow_right n.le_succ (step n i))).symm)
    refine ⟨L, fun e => ?_⟩
    have := hL (e + 1)
    rw [smul_eq_mul, Ideal.mul_top] at this
    have := add_mem (SModEq.sub_mem.1 this.symm) (step e i)
    rwa [sub_add_sub_cancel] at this
  choose L hL using hL
  refine ⟨comb c b L, ⟨hS L, fun e => (key e L).2 fun i => hL i e⟩, fun s ⟨hs, hs'⟩ => ?_⟩
  obtain ⟨x, rfl, -⟩ := hb.2 s hs
  congr 1
  funext i
  refine sub_eq_zero.1 (IsHausdorff.haus (I := I) (M := R) inferInstance _ fun n => ?_)
  rw [smul_eq_mul, Ideal.mul_top, SModEq.zero]
  have := sub_mem ((key n x).1 (hs' n) i) (hL i n)
  rw [sub_sub_sub_cancel_right] at this
  exact Ideal.pow_le_pow_right n.le_succ this

end Algebra

section Values

variable {X Y Y' Y'' : Scheme.{0}} (L : LB X) {K K' K₃ : Type} [Fintype K] [Fintype K'] [Fintype K₃]

abbrev Vals (Y : Scheme.{0}) : Type 1 :=
  ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z) (_ : {J // Good L z J}), Z.presheaf.stalk z

def pull (h : Y' ⟶ Y) : Vals L Y →+* Vals L Y' where
  toFun w Z r z J := w Z (r ≫ h) z J
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def fn (Y : Scheme.{0}) : Γ(Y, ⊤) →+* Vals L Y where
  toFun a Z r z _ := gs r z ⊤ a
  map_one' := by funext Z r z J; rw [gs_eq r z ⊤ trivial, map_one, map_one]; rfl
  map_mul' _ _ := by funext Z r z J; exact gs_mul r z ⊤ trivial _ _
  map_zero' := by funext Z r z J; rw [gs_eq r z ⊤ trivial, map_zero, map_zero]; rfl
  map_add' _ _ := by funext Z r z J; exact gs_add r z ⊤ trivial _ _

def cst {R : Type} [CommRing R] (f : Y ⟶ Spec (CommRingCat.of R)) : R →+* Vals L Y :=
  (fn L Y).comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

variable {L}

theorem pull_pull (h : Y' ⟶ Y) (h' : Y'' ⟶ Y') (w : Vals L Y) : pull L h' (pull L h w) = pull L (h' ≫ h) w := by
  funext Z r z J
  exact congrArg (fun q => w Z q z J) (Category.assoc _ _ _)

theorem pull_id (w : Vals L Y) : pull L (𝟙 Y) w = w := by
  funext Z r z J
  exact congrArg (fun q => w Z q z J) (Category.comp_id _)

theorem pull_cst {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') {π : Y' ⟶ Y}
    {f : Y ⟶ Spec (CommRingCat.of R)} {f' : Y' ⟶ Spec (CommRingCat.of R')}
    (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) (a : R) : pull L π (cst L f a) = cst L f' (g a) := by
  have e₁ := congrArg (fun Q => Q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  have e₂ := congrArg (fun q => q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) w
  funext Z r z J
  exact (gs_pull r π z ⊤ trivial _).symm.trans (congrArg (gs r z ⊤) ((congrArg f'.appTop.hom e₁).trans e₂.symm).symm)

def ev {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) : Vals L Y := fun _ r z J => sval s r z J.1

def evU {φ : K → (Y ⟶ X)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb L φ ε)) : (Vals L Y)ˣ where
  val _ r z J := (val u r z J.1).val
  inv _ r z J := (val u r z J.1).inv
  val_inv := by funext Z r z J; exact (val u r z J.1).val_inv
  inv_val := by funext Z r z J; exact (val u r z J.1).inv_val


variable (L) in
def secVals (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Set (Vals L Y) := Set.range (ev (L := L) (φ := φ) (ε := ε))

variable {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem eq_of_val (hL : L.IsLB) {s s' : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ y J, ev s Y (𝟙 Y) y J = ev s' Y (𝟙 Y) y J) : s = s' :=
  DVR.SecOps.sec_ext (sec_ext_val hL fun y J hJ => h y ⟨J, hJ⟩)

theorem secVals_ext (hL : L.IsLB) {w w' : Vals L Y} (hw : w ∈ secVals L φ ε) (hw' : w' ∈ secVals L φ ε)
    (h : ∀ y J, w Y (𝟙 Y) y J = w' Y (𝟙 Y) y J) : w = w' := by
  obtain ⟨s, rfl⟩ := hw
  obtain ⟨s', rfl⟩ := hw'
  rw [eq_of_val hL h]

theorem ev_pullSec (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) : ev (DVR.pullSec L φ ε s h) = pull L h (ev s) := by
  funext Z r z J
  exact DVR.SectionScalarValuation.sval_pullSec φ ε s h r z J.2

theorem pull_mem {w : Vals L Y} (hw : w ∈ secVals L φ ε) (h : Y' ⟶ Y) {ψ : K → (Y' ⟶ X)} (e : ∀ k, ψ k = h ≫ φ k) :
    pull L h w ∈ secVals L ψ ε := by
  obtain ⟨s, rfl⟩ := hw
  obtain rfl : ψ = fun k => h ≫ φ k := funext e
  exact ⟨_, ev_pullSec s h⟩

theorem ev_comb {R : Type} [CommRing R] {m : ℕ} (g : R →+* Γ(Y, ⊤)) (a : Fin m → R)
    (b : Fin m → LB.Sec (LB.LinComb L φ ε)) {s : LB.Sec (LB.LinComb L φ ε)}
    (hs : ∀ j, s.f j = ∑ i, resTop _ (g (a i)) * (b i).f j) : ev s = comb ((fn L Y).comp g) (fun i => ev (b i)) a := by
  funext Z r z J
  simp only [comb, Finset.sum_apply]
  exact DVR.SectionScalarValuation.sval_lin (fun i => g (a i)) b hs r z J.2

theorem exists_comb {M : LB Y} {m : ℕ} (a : Fin m → Γ(Y, ⊤)) (b : Fin m → LB.Sec M) :
    ∃ s : LB.Sec M, ∀ j, s.f j = ∑ i, resTop _ (a i) * (b i).f j :=
  ⟨⟨fun j => ∑ i, resTop _ (a i) * (b i).f j, fun j j' => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (DVR.SecOps.secScale (a i) (b i)).compat j j'⟩, fun _ => rfl⟩

theorem comb_mem {R : Type} [CommRing R] {m : ℕ} (g : R →+* Γ(Y, ⊤)) (a : Fin m → R) {b : Fin m → Vals L Y}
    (hb : ∀ i, b i ∈ secVals L φ ε) : comb ((fn L Y).comp g) b a ∈ secVals L φ ε := by
  choose t ht using hb
  obtain rfl : (fun i => ev (t i)) = b := funext ht
  obtain ⟨s, hs⟩ := exists_comb (fun i => g (a i)) t
  exact ⟨s, ev_comb g a t hs⟩

theorem isBas_of_comb (hL : L.IsLB) {R : Type} [CommRing R] {m : ℕ} (g : R →+* Γ(Y, ⊤))
    (b : Fin m → LB.Sec (LB.LinComb L φ ε))
    (hb : ∀ s : LB.Sec (LB.LinComb L φ ε), ∃! a : Fin m → R, ∀ j, s.f j = ∑ i, resTop _ (g (a i)) * (b i).f j) :
    IsBas ((fn L Y).comp g) (secVals L φ ε) (fun i => ev (b i)) := by
  refine ⟨fun i => ⟨_, rfl⟩, ?_⟩
  rintro _ ⟨s, rfl⟩
  refine (existsUnique_congr fun a => ⟨ev_comb g a b, fun H => ?_⟩).1 (hb s)
  obtain ⟨t, ht⟩ := exists_comb (fun i => g (a i)) b
  rw [← ev_comb g a b ht] at H
  rw [eq_of_val hL fun y J => congrFun (congrFun (congrFun (congrFun H _) _) y) J]
  exact ht

theorem mul_mem_iff (hL : L.IsLB) {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {φ₃ : K₃ → (Y ⟶ X)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen) (h : FormEq (Sum.elim φ φ₃) (Sum.elim ε ε₃) φ' ε')
    (w : Vals L Y) : w * evU u ∈ secVals L φ' ε' ↔ w ∈ secVals L φ ε := by
  constructor
  · rintro ⟨s, hs⟩
    have hu' := DVR.invGen_isGen L _ _ u hu
    obtain ⟨t, ht⟩ := exists_sec (φ' := φ) (ε' := ε) hL (fun U _ q => by
      have := h U q
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp] at this ⊢
      rw [← this]
      simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]) (pullMulSec s (𝟙 Y) (LB.invGen L _ _ u) hu')
    refine ⟨t, ?_⟩
    funext Z r z J
    refine (ht Z r z J.1 J.2).trans ?_
    rw [sval_pullMulSec _ _ _ hu' _ z J.2, val_inv, Category.comp_id, Units.mul_inv_eq_iff_eq_mul]
    exact congrFun (congrFun (congrFun (congrFun hs Z) r) z) J
  · rintro ⟨s, rfl⟩
    obtain ⟨t, ht⟩ := exists_sec (φ' := φ') (ε' := ε') hL (fun U _ q => by
      simpa only [Category.id_comp] using h U q) (pullMulSec s (𝟙 Y) u hu)
    refine ⟨t, ?_⟩
    funext Z r z J
    refine (ht Z r z J.1 J.2).trans ?_
    rw [sval_pullMulSec _ _ _ hu _ z J.2, Category.comp_id]
    rfl

theorem pull_evU (u : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) :
    (evU (LB.pullGen L φ ε u h)).val = pull L h (evU u).val := by
  funext Z r z J
  exact congrArg Units.val (val_pull J.2 u h r)

end Values

end GlobalTheory.SecLimit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueTwistedSectionOfCompatibleLevels
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.SecLimit

section Twist

variable {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (k : ℕ) (α : D.X)

abbrev twφ (T : Over (Spec (CommRingCat.of V))) : Fin 2 → ((T ⊗ D.P.A).left ⟶ D.P.A.left) :=
  ![(snd T D.P.A).left, (translPt D.P.A (toUnit T ≫ D.c α)).left]

abbrev ptφ : Fin 2 → (Spec (CommRingCat.of V) ⟶ D.P.A.left) := ![(D.c α).left, (η[D.P.A]).left]

abbrev famVals {Y : Scheme.{0}} (π : Y ⟶ D.P.A.left) : Set (Vals D.P.L Y) :=
  secVals D.P.L (fun i => π ≫ D.famφB α i) (DegPre.famε k)

variable {D k α}

theorem mul_mem_famVals (u : LB.Gen (LB.LinComb D.P.L (ptφ D α) ![-1, 1])) (hu : u.IsGen)
    (T : Over (Spec (CommRingCat.of V))) {Y : Scheme.{0}} (h : Y ⟶ (T ⊗ D.P.A).left) {π : Y ⟶ D.P.A.left}
    (hπ : h ≫ (snd T D.P.A).left = π) (w : Vals D.P.L Y) :
    w * evU (LB.pullGen D.P.L _ _ u (π ≫ D.P.A.hom)) ∈ famVals D k α π ↔
      w ∈ secVals D.P.L (fun j => h ≫ twφ D α T j) ![(k : ℤ) - 1, 1] := by
  have hZ : h ≫ (T ⊗ D.P.A).hom = π ≫ D.P.A.hom := by
    rw [← Over.w (snd T D.P.A), ← Category.assoc, hπ]
  let Z : Over (Spec (CommRingCat.of V)) := Over.mk (π ≫ D.P.A.hom)
  let hO : Z ⟶ T ⊗ D.P.A := Over.homMk h hZ
  let πO : Z ⟶ D.P.A := Over.homMk π
  have h1 : hO ≫ snd T D.P.A = πO := by
    ext
    simpa [hO, πO] using hπ
  have e1 : hO ≫ translPt D.P.A (toUnit T ≫ D.c α) = πO ≫ padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c α) := by
    unfold translPt padd
    simp only [comp_lift_assoc, comp_toUnit_assoc, h1, Category.comp_id]
    exact mul_comm (toUnit Z ≫ D.c α) πO
  have hmor : h ≫ (translPt D.P.A (toUnit T ≫ D.c α)).left =
      π ≫ (padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c α)).left := by
    have e2 := congrArg Over.Hom.left e1
    simpa [hO, πO] using e2
  refine mul_mem_iff D.P.isLB _ (DVR.pullGen_isGen _ _ _ u hu _) ?_ w
  intro U _ g
  have hπ' : h ≫ pullback.snd T.hom D.P.A.hom = π := hπ
  simp [Fintype.prod_sum_type, Fin.prod_univ_four, twφ, ptφ, DegPre.famφB, DegPre.famε, hmor, hπ',
    Over.toUnit_left]
  exact (mul_assoc _ _ _).symm

theorem isPullback_snd (T : Over (Spec (CommRingCat.of V))) :
    IsPullback (snd T D.P.A).left (fst T D.P.A).left D.P.A.hom T.hom := by
  rw [Over.snd_left, Over.fst_left]
  exact (IsPullback.of_hasPullback T.hom D.P.A.hom).flip

set_option maxHeartbeats 1600000 in
private theorem exists_isBas_famVals_of_isPullback [IsLocalRing V] (hT : SecTwistSt) (hk : 1 ≤ k) {R : Type} [CommRing R] [IsLocalRing R]
    {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of V)} {Y : Scheme.{0}} {π : Y ⟶ D.P.A.left}
    {f : Y ⟶ Spec (CommRingCat.of R)} (H : IsPullback π f D.P.A.hom t) :
    ∃ b : Fin (k ^ D.P.g) → Vals D.P.L Y, IsBas (cst D.P.L f) (famVals D k α π) b := by
  obtain ⟨b0, hb0⟩ := (hT _ D.P k hk R t (toUnit (Over.mk t) ≫ D.c α)).1
  obtain ⟨u, hu⟩ := DVR.exists_gen_of_local D.P.L D.P.isLB (ptφ D α) ![-1, 1]
  let e := H.flip.isoPullback
  have hπ : e.hom ≫ (snd (Over.mk t) D.P.A).left = π := H.flip.isoPullback_hom_snd
  have hf : e.hom ≫ (fst (Over.mk t) D.P.A).left = f := H.flip.isoPullback_hom_fst
  let gR : R →+* Γ((Over.mk t ⊗ D.P.A).left, ⊤) :=
    (fst (Over.mk t) D.P.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hb1 : IsBas ((fn D.P.L _).comp gR) (secVals D.P.L (twφ D α (Over.mk t)) ![(k : ℤ) - 1, 1])
      (fun i => ev (b0 i)) := by
    refine isBas_of_comb D.P.isLB gR b0 (fun s => ?_)
    obtain ⟨r, hr, hru⟩ := hb0 s
    refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (r i), fun j => ?_, fun a ha => ?_⟩
    · rw [hr j]
      simp [gR, resTop]
      try rfl
    · have h2 := hru (fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a i))
        (fun j => by rw [ha j]; simp [gR, resTop]; try rfl)
      funext i
      rw [← h2]
      simp
  have key := fun w => mul_mem_famVals (k := k) u hu (Over.mk t) e.hom hπ w
  have hinj : Function.Injective (pull D.P.L e.hom) :=
    Function.LeftInverse.injective (g := pull D.P.L e.inv) (fun w => by rw [pull_pull, Iso.inv_hom_id, pull_id])
  have hS : ∀ s', s' ∈ famVals D k α π ↔
      ∃ s ∈ secVals D.P.L (twφ D α (Over.mk t)) ![(k : ℤ) - 1, 1], s' = pull D.P.L e.hom s * (evU (LB.pullGen D.P.L _ _ u (π ≫ D.P.A.hom))) := by
    intro s'
    constructor
    · intro hs'
      refine ⟨pull D.P.L e.inv (s' * ↑(evU (LB.pullGen D.P.L _ _ u (π ≫ D.P.A.hom)))⁻¹), pull_mem ((key _).1 (by rw [Units.inv_mul_cancel_right]; exact hs')) e.inv (fun j => by simp), ?_⟩
      rw [pull_pull, Iso.hom_inv_id, pull_id, Units.inv_mul_cancel_right]
    · rintro ⟨s, hs, rfl⟩
      exact (key _).2 (pull_mem hs e.hom (fun j => rfl))
  exact ⟨_, IsBas.transfer (fun a => pull_cst (RingHom.id R) (by simpa using hf) a) hinj (evU (LB.pullGen D.P.L _ _ u (π ≫ D.P.A.hom))) hS hb1⟩

variable [IsLocalRing V]

theorem exists_isBas (hT : SecTwistSt) (hk : 1 ≤ k) {R : Type} [CommRing R] [IsLocalRing R]
    {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of V)} {Y : Scheme.{0}} {π : Y ⟶ D.P.A.left}
    {f : Y ⟶ Spec (CommRingCat.of R)} (H : IsPullback π f D.P.A.hom t) :
    ∃ b : Fin (k ^ D.P.g) → Vals D.P.L Y, IsBas (cst D.P.L f) (famVals D k α π) b := exists_isBas_famVals_of_isPullback hT hk H

abbrev resPt (V : Type) [CommRing V] [IsLocalRing V] : Over (Spec (CommRingCat.of V)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) ≫ 𝟙 _)

theorem exists_lift (hT : SecTwistSt) (hk : 1 ≤ k) (w : Vals D.P.L (resPt V ⊗ D.P.A).left)
    (hw : w ∈ famVals D k α (snd (resPt V) D.P.A).left) :
    ∃ s ∈ famVals D k α (𝟙 _), w = pull D.P.L (snd (resPt V) D.P.A).left s := by
  obtain ⟨u, hu⟩ := DVR.exists_gen_of_local D.P.L D.P.isLB (ptφ D α) ![-1, 1]
  have keyX := fun v => mul_mem_famVals (k := k) u hu (resPt V) (𝟙 _) (π := (snd (resPt V) D.P.A).left)
    (Category.id_comp _) v
  have hw1 := (keyX (w * ↑(evU (LB.pullGen D.P.L _ _ u ((snd (resPt V) D.P.A).left ≫ D.P.A.hom)))⁻¹)).1
    (by rw [Units.inv_mul_cancel_right]; exact hw)
  let whisk : resPt V ⊗ D.P.A ⟶ Over.mk (𝟙 (Spec (CommRingCat.of V))) ⊗ D.P.A :=
    Over.homMk (V := Over.mk (𝟙 (Spec (CommRingCat.of V)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
      rfl ▷ D.P.A
  have ht0 : whisk ≫ snd _ D.P.A = snd (resPt V) D.P.A := whiskerRight_snd _ _
  have ht1 : whisk ≫ translPt D.P.A (toUnit _ ≫ D.c α) = translPt D.P.A (toUnit (resPt V) ≫ D.c α) := by
    simp only [whisk, translPt, comp_lift_assoc, whiskerRight_snd, comp_toUnit_assoc]
  have hφ : (fun j => 𝟙 _ ≫ twφ D α (resPt V) j) = fun j => whisk.left ≫
      ![(snd (Over.mk (𝟙 (Spec (CommRingCat.of V)))) D.P.A).left,
        (translPt D.P.A (toUnit (Over.mk (𝟙 (Spec (CommRingCat.of V)))) ≫ D.c α)).left] j := by
    funext j
    match j with
    | 0 =>
      simp only [twφ, Matrix.cons_val_zero, Category.id_comp]
      rw [← Over.comp_left, ht0]
    | 1 =>
      simp only [twφ, Matrix.cons_val_one, Matrix.cons_val_zero, Category.id_comp]
      rw [← Over.comp_left, ht1]
  rw [hφ] at hw1
  obtain ⟨sbar, hsbar⟩ := hw1
  obtain ⟨s, hs⟩ := (hT _ D.P k hk V (𝟙 _) (toUnit _ ≫ D.c α)).2 sbar
  have hps : sbar = DVR.pullSec D.P.L _ _ s whisk.left := DVR.SecOps.sec_ext (fun j => hs j)
  have hev : ev sbar = pull D.P.L whisk.left (ev s) := by
    rw [hps]
    exact ev_pullSec _ _
  let i : D.P.A.left ⟶ (Over.mk (𝟙 (Spec (CommRingCat.of V))) ⊗ D.P.A).left :=
    pullback.lift D.P.A.hom (𝟙 _) (by simp)
  have hi : i ≫ (snd (Over.mk (𝟙 (Spec (CommRingCat.of V)))) D.P.A).left = 𝟙 _ := pullback.lift_snd _ _ _
  have key0 := fun v => mul_mem_famVals (k := k) u hu (Over.mk (𝟙 (Spec (CommRingCat.of V)))) i hi v
  refine ⟨pull D.P.L i (ev s) * ↑(evU (LB.pullGen D.P.L _ _ u (𝟙 _ ≫ D.P.A.hom))),
    (key0 _).2 (pull_mem ⟨s, rfl⟩ i (fun j => rfl)), ?_⟩
  have hc := pullback.condition (f := (resPt V).hom) (g := D.P.A.hom)
  have hsi : (snd (resPt V) D.P.A).left ≫ i = whisk.left := by
    apply pullback.hom_ext
    · simp only [Category.assoc, i, pullback.lift_fst, whisk, Over.whiskerRight_left_fst]
      simpa using hc.symm
    · simp only [Category.assoc, i, pullback.lift_snd, Category.comp_id, whisk, Over.whiskerRight_left_snd]
      rfl
  rw [map_mul, pull_pull, hsi, ← hev, hsbar, pull_evU, pull_pull, Category.id_comp, ← pull_evU,
    Units.inv_mul_cancel_right]

theorem isBas_thick (hT : SecTwistSt) (hk : 1 ≤ k) {b : Fin (k ^ D.P.g) → Vals D.P.L D.P.A.left}
    (hb : IsBas (cst D.P.L D.P.A.hom) (famVals D k α (𝟙 _)) b) (e : ℕ) :
    IsBas (cst D.P.L (pullback.snd D.P.A.hom (thick V (IsLocalRing.maximalIdeal V) e)))
      (famVals D k α (pullback.fst D.P.A.hom (thick V (IsLocalRing.maximalIdeal V) e)))
      (fun i => pull D.P.L (pullback.fst D.P.A.hom (thick V (IsLocalRing.maximalIdeal V) e)) (b i)) := by
  have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal V).ne_top
      (Ideal.pow_le_self (Nat.succ_ne_zero e)))
  have : IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let g' : V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1) →+* IsLocalRing.ResidueField V :=
    Ideal.Quotient.lift _ (IsLocalRing.residue V) (fun a ha => (IsLocalRing.residue_eq_zero_iff a).2
      (Ideal.pow_le_self (Nat.succ_ne_zero e) ha))
  have hg' : ∀ v, g' (Ideal.Quotient.mk _ v) = IsLocalRing.residue V v := fun v => rfl
  have : IsLocalHom g' := ⟨fun a ha => by
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hg'] at ha
    exact (isUnit_of_map_unit (IsLocalRing.residue V) v ha).map _⟩
  have hm : (snd (resPt V) D.P.A).left ≫ D.P.A.hom =
      ((fst (resPt V) D.P.A).left ≫ Spec.map (CommRingCat.ofHom g')) ≫ thick V (IsLocalRing.maximalIdeal V) e := by
    rw [Over.w (snd (resPt V) D.P.A)]
    change pullback.fst _ _ ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) ≫ 𝟙 _) =
      (pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom g')) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))
    rw [Category.comp_id, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let m := pullback.lift (snd (resPt V) D.P.A).left ((fst (resPt V) D.P.A).left ≫ Spec.map (CommRingCat.ofHom g')) hm
  obtain ⟨b', hb'⟩ := exists_isBas (α := α) hT hk
    (IsPullback.of_hasPullback D.P.A.hom (thick V (IsLocalRing.maximalIdeal V) e))
  obtain ⟨b'', hb''⟩ := exists_isBas (α := α) hT hk (isPullback_snd (D := D) (resPt V))
  refine IsBas.reduce (ρ' := pull D.P.L m) (g' := g') (fun a => pull_cst _ pullback.condition a)
    (fun a => pull_cst g' (pullback.lift_snd _ _ _) a) ?_ ?_ ?_ hb hb' hb''
  · intro s hs
    exact pull_mem hs _ (fun i => by simp)
  · intro s hs
    exact pull_mem hs m (fun i => (pullback.lift_fst_assoc _ _ _ _).symm)
  · intro s hs
    obtain ⟨s0, hs0, rfl⟩ := exists_lift hT hk s hs
    exact ⟨s0, hs0, by rw [pull_pull]; exact congrArg (fun x => pull D.P.L x s0) (pullback.lift_fst _ _ _).symm⟩

set_option maxHeartbeats 1000000 in
private theorem existsUnique_sec_of_isBas_lemma {X B : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (B ⟶ X)} {ε : K → ℤ} {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {p : B ⟶ Spec (CommRingCat.of R)} {Y : ℕ → Scheme.{0}} {π : ∀ e, Y e ⟶ B}
    {q : ∀ e, Y e ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))} {θ : ∀ e, Y e ⟶ Y (e + 1)}
    (hθ : ∀ e, θ e ≫ π (e + 1) = π e) (hq : ∀ e, π e ≫ p = q e ≫ thick R I e) {m : ℕ} {b : Fin m → Vals L B}
    (hb : IsBas (cst L p) (secVals L (fun i => 𝟙 B ≫ φ i) ε) b)
    (hb' : ∀ e, IsBas (cst L (q e)) (secVals L (fun i => π e ≫ φ i) ε) (fun i => pull L (π e) (b i)))
    (f : ∀ e, LB.Sec (LB.LinComb L (fun i => π e ≫ φ i) ε))
    (hf : ∀ e z J, Good L z J → sval (f (e + 1)) (θ e) z J = sval (f e) (𝟙 _) z J) :
    ∃! s : LB.Sec (LB.LinComb L φ ε), ∀ e z J, Good L z J → sval s (π e) z J = sval (f e) (𝟙 _) z J := by
  simp only [Category.id_comp] at hb
  have hmem : ∀ e, ev (f e) ∈ secVals L (fun i => π e ≫ φ i) ε := fun e => ⟨f e, rfl⟩
  have hlim := existsUnique_limit I (T := fun e => Vals L (Y e)) (c := cst L p)
    (c' := fun e => cst L (q e)) (ρ := fun e => pull L (π e)) (τ := fun e => pull L (θ e))
    (fun e a => pull_cst (Ideal.Quotient.mk (I ^ (e + 1))) (by rw [hq e]) a)
    (fun e w => by simp only [pull_pull, hθ])
    (S := secVals L φ ε) (S' := fun e => secVals L (fun i => π e ≫ φ i) ε)
    (fun z => comb_mem (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) z hb.1) hb hb'
    (fun e => ev (f e)) hmem
    (fun e => secVals_ext hL (pull_mem (hmem (e + 1)) (θ e) (fun j => by simp only [← Category.assoc, hθ]))
      (hmem e) (fun y J => by
        change sval (f (e + 1)) (𝟙 _ ≫ θ e) y J.1 = sval (f e) (𝟙 _) y J.1
        rw [Category.id_comp]; exact hf e y J.1 J.2))
  obtain ⟨w, ⟨⟨s, rfl⟩, hwf⟩, hwu⟩ := hlim
  refine ⟨s, fun e z J hJ => ?_, fun s' hs' => ?_⟩
  · have h1 := congrFun (congrFun (congrFun (congrFun (hwf e) (Y e)) (𝟙 _)) z) ⟨J, hJ⟩
    change sval s (𝟙 _ ≫ π e) z J = sval (f e) (𝟙 _) z J at h1
    rwa [Category.id_comp] at h1
  · have hev : ev s' = ev s := hwu (ev s') ⟨⟨s', rfl⟩, fun e => secVals_ext hL
      (pull_mem ⟨s', rfl⟩ (π e) (fun j => rfl)) (hmem e) (fun y J => by
        change sval s' (𝟙 _ ≫ π e) y J.1 = sval (f e) (𝟙 _) y J.1
        rw [Category.id_comp]; exact hs' e y J.1 J.2)⟩
    exact eq_of_val hL (fun y J => by rw [hev])

end Twist

theorem existsUnique_sec_of_isBas {X B : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (B ⟶ X)} {ε : K → ℤ} {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {p : B ⟶ Spec (CommRingCat.of R)} {Y : ℕ → Scheme.{0}} {π : ∀ e, Y e ⟶ B}
    {q : ∀ e, Y e ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))} {θ : ∀ e, Y e ⟶ Y (e + 1)}
    (hθ : ∀ e, θ e ≫ π (e + 1) = π e) (hq : ∀ e, π e ≫ p = q e ≫ thick R I e) {m : ℕ} {b : Fin m → Vals L B}
    (hb : IsBas (cst L p) (secVals L (fun i => 𝟙 B ≫ φ i) ε) b)
    (hb' : ∀ e, IsBas (cst L (q e)) (secVals L (fun i => π e ≫ φ i) ε) (fun i => pull L (π e) (b i)))
    (f : ∀ e, LB.Sec (LB.LinComb L (fun i => π e ≫ φ i) ε))
    (hf : ∀ e z J, Good L z J → sval (f (e + 1)) (θ e) z J = sval (f e) (𝟙 _) z J) :
    ∃! s : LB.Sec (LB.LinComb L φ ε), ∀ e z J, Good L z J → sval s (π e) z J = sval (f e) (𝟙 _) z J := existsUnique_sec_of_isBas_lemma hL I hθ hq hb hb' f hf

theorem existsUnique_sec_of_compatible : Laws → Laws2 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (k : ℕ), 1 ≤ k → ∀ (α : D.X) (f : ∀ e, LB.Sec (LB.LinComb D.P.L (fun i => (D.prBe (IsLocalRing.maximalIdeal V) e).left ≫ D.famφB α i) (DegPre.famε k))), (∀ e z J, Good D.P.L z J → sval (f (e + 1)) (thickMap V _ e D.P.A) z J = sval (f e) (𝟙 _) z J) → ∃! s : D.SecB k α, ∀ e z J, Good D.P.L z J → sval s (D.prBe (IsLocalRing.maximalIdeal V) e).left z J = sval (f e) (𝟙 _) z J) := by
  intro _ hL2 V _ _ _ hV D k hk α f hf
  have hT : SecTwistSt := by
    obtain ⟨⟩ := hL2
    assumption
  have : IsAdicComplete (IsLocalRing.maximalIdeal V) V := hV.2.1
  obtain ⟨b, hb⟩ := exists_isBas (α := α) (R := V) (t := 𝟙 _) hT hk
    (IsPullback.of_horiz_isIso (fst := 𝟙 D.P.A.left) (snd := D.P.A.hom) ⟨by simp⟩)
  exact existsUnique_sec_of_isBas D.P.isLB (IsLocalRing.maximalIdeal V) (p := D.P.A.hom)
    (π := fun e => (D.prBe (IsLocalRing.maximalIdeal V) e).left)
    (q := fun e => (thickObj V (IsLocalRing.maximalIdeal V) e D.P.A).hom)
    (θ := fun e => thickMap V (IsLocalRing.maximalIdeal V) e D.P.A)
    (fun e => by
      simp [thickMap, DegPre.prBe]) (fun e => pullback.condition) hb
    (fun e => isBas_thick hT hk hb e) f hf

end GlobalTheory.SecLimit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueTwistedSectionOfCompatibleLevelsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_twistedSection_of_compatible_levels : Laws → Laws2 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (k : ℕ), 1 ≤ k → ∀ (α : D.X) (f : ∀ e, LB.Sec (LB.LinComb D.P.L (fun i => (D.prBe (IsLocalRing.maximalIdeal V) e).left ≫ D.famφB α i) (DegPre.famε k))), (∀ e z J, Good D.P.L z J → sval (f (e + 1)) (thickMap V _ e D.P.A) z J = sval (f e) (𝟙 _) z J) → ∃! s : D.SecB k α, ∀ e z J, Good D.P.L z J → sval s (D.prBe (IsLocalRing.maximalIdeal V) e).left z J = sval (f e) (𝟙 _) z J) := by
  first | exact @GlobalTheory.SecLimit.existsUnique_sec_of_compatible | exact GlobalTheory.SecLimit.existsUnique_sec_of_compatible | (intros; apply GlobalTheory.SecLimit.existsUnique_sec_of_compatible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpansionSectionLineBundlePower
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.BaseExpansionExists

section General
variable {X X₁ X₂ Y Y' Z : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {K : Type} [Fintype K]

theorem exists_pull {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (e : ∀ i, φ' i = h ≫ φ i)
    (s : LB.Sec (LB.LinComb L φ ε)) : ∃ s' : LB.Sec (LB.LinComb L φ' ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J, Good L z J → sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : φ' = fun i => h ≫ φ i := funext e
  exact ⟨_, fun Z r z J hJ => H1.SectionArithmetic.sval_pullSec s h r z hJ⟩

theorem exists_carry (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (k : ℕ)
    (s : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => f₁) (fun _ => (k : ℤ)))) :
    ∃ τ : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J₁ J₂, Good L₁ z J₁ → Good L₂ z J₂ →
        sval τ r z J₂ = (gw w r z (J₂ (r ≫ f₂)) (fun _ => J₁ (r ≫ f₁))).val ^ k * sval s r z J₁ := by
  obtain ⟨τ, hτ⟩ := GenericFibreSections.exists_transfer hL₁ hL₂ f₁ f₂ k
    (fun i j => (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i))
    (fun i j y hi hj => ⟨mem_pull.2 hj, mem_pull.2 hi⟩)
    (fun i j => (show Γ(Y, (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i))ˣ from
      w.s (fun _ => j, fun _ => i)) ^ k) (fun y i i' j j' hi hi' hj hj' => by
      have e := GenericFibreSections.gw_trans hw y hi hi' hj hj'
      rw [map_pow, map_pow, zpow_natCast, zpow_natCast, ← mul_pow, ← mul_pow]
      exact congrArg (· ^ k) e) s
  refine ⟨τ, fun Z r z J₁ J₂ h₁ h₂ => ?_⟩
  rw [hτ Z r z J₁ J₂ h₁ h₂, map_pow, Units.val_pow_eq_pow_val]
  rfl

theorem sval_zero {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, s.f j = 0)
    (r : Z ⟶ Y) {z : Z} {J} (hJ : Good L z J) : sval s r z J = 0 :=
  (congrArg (gs r z _) (h _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans
    ((congrArg _ (map_zero _)).trans (map_zero _)))

theorem zero_of_sval (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0) (j) : s.f j = 0 := by
  refine fn_ext fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
  rw [h y J hJ, mul_zero] at e
  exact e.trans ((gs_eq (𝟙 Y) y _ hy _).trans ((congrArg _ (map_zero _)).trans (map_zero _))).symm

theorem sval_eq_of_id {Y₁ : Scheme.{0}} {K' : Type} [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y₁ ⟶ X)} {ε' : K' → ℤ} {s : LB.Sec (LB.LinComb L φ ε)} {s' : LB.Sec (LB.LinComb L φ' ε')}
    {p : Y' ⟶ Y} {p' : Y' ⟶ Y₁} (h : ∀ y J, Good L y J → sval s p y J = sval s' p' y J)
    (r : Z ⟶ Y') (z : Z) {J} (hJ : Good L z J) : sval s (r ≫ p) z J = sval s' (r ≫ p') z J := by
  obtain ⟨h₀, h₁, -⟩ := values_natural X Y Y' Z L K φ ε p r z J hJ
  obtain ⟨-, h₂, -⟩ := values_natural X Y₁ Y' Z L K' φ' ε' p' r z J hJ
  rw [h₁, h₂, h _ _ h₀]

theorem sum_of_id {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {N : Type} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ₁ : N → K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {φ₂ : N → K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    {τ : LB.Sec (LB.LinComb L φ ε)} {f : ∀ α, LB.Sec (LB.LinComb L (φ₁ α) ε₁)}
    {t : ∀ α, LB.Gen (LB.LinComb L (φ₂ α) ε₂)} {q : Y ⟶ Y'} {S : Finset N}
    (h : ∀ y J, Good L y J → sval τ (𝟙 Y) y J = ∑ α ∈ S, sval (f α) q y J * (val (t α) (𝟙 Y) y J).val)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval τ r z J = ∑ α ∈ S, sval (f α) (r ≫ q) z J * (val (t α) r z J).val := by
  obtain ⟨h₀, h₁, -⟩ := values_natural X Y Y Z L K φ ε (𝟙 Y) r z J hJ
  have a := h₁ τ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Category.comp_id, h _ _ h₀, map_sum] at a
  refine a.trans (Finset.sum_congr rfl fun α _ => ?_)
  have b := (values_natural X Y' Y Z L K₁ (φ₁ α) ε₁ q r z J hJ).2.1 (f α)
  have c := (values_natural X Y Y Z L K₂ (φ₂ α) ε₂ (𝟙 Y) r z J hJ).2.2.1 (t α)
  rw [Category.comp_id] at c
  rw [map_mul, b, c]

end General

section Levels
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

omit [GrpObj G] [IsCommMonObj G] in
theorem thickMap_fst (e : ℕ) : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem thickMap_prBe (e : ℕ) : thickMap R I e D.P.A ≫ (D.prBe I (e + 1)).left = (D.prBe I e).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem q_thickMap (U : PreU I D A G) (e : ℕ) :
    (U.gt e).q.left ≫ thickMap R I e D.P.A = thickMap R I e G ≫ (U.gt (e + 1)).q.left := by
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg ((U.gt e).q.left ≫ ·) (thickMap_prBe e)).trans
      ((U.gt_q e).symm.trans (Category.assoc _ _ _).symm))
  · have a : (U.gt e).q.left ≫ pullback.snd D.P.A.hom (thick R I e) = pullback.snd G.hom (thick R I e) :=
      Over.w (U.gt e).q
    have b : (U.gt (e + 1)).q.left ≫ pullback.snd D.P.A.hom (thick R I (e + 1)) =
      pullback.snd G.hom (thick R I (e + 1)) := Over.w (U.gt (e + 1)).q
    have c : ∀ H : Over (Spec (CommRingCat.of R)), thickMap R I e H ≫ pullback.snd H.hom (thick R I (e + 1)) =
      pullback.snd H.hom (thick R I e) ≫ thickTrans R I e := fun H => pullback.lift_snd _ _ _
    exact (Category.assoc _ _ _).trans ((congrArg ((U.gt e).q.left ≫ ·) (c _)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ thickTrans R I e) a).trans ((c G).symm.trans
        ((congrArg (thickMap R I e G ≫ ·) b.symm).trans (Category.assoc _ _ _).symm)))))

theorem famφT_eq (T : Over (Spec (CommRingCat.of R))) (α : D.X) (i : Fin 4) :
    famφT D T α i = (snd T D.P.A).left ≫ D.famφB α i := by
  fin_cases i
  · exact (Category.comp_id _).symm
  · show (padd D.P.A (snd T D.P.A) (toUnit _ ≫ D.c α)).left =
      (snd T D.P.A ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    congr 1
    rw [padd, padd, ← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
  · show (toUnit (T ⊗ D.P.A) ≫ D.c α).left = (snd T D.P.A ≫ toUnit D.P.A ≫ D.c α).left
    congr 1
    simp
  · show (toUnit (T ⊗ D.P.A) ≫ η[D.P.A]).left = (snd T D.P.A ≫ toUnit D.P.A ≫ η[D.P.A]).left
    congr 1
    simp

end Levels

theorem main : Laws → Laws2 → (AllPre fun U => ∀ k, 1 ≤ k → ∀ σ, ∃ f, U.ExpT (𝟙_ _) k σ f) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U k hk σ
  have hB := D.P.isLB
  have hG := U.P.L.isLB
  have lam : (snd (𝟙_ _) G).left ≫ (λ_ G).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
  have lam' : (λ_ G).inv.left ≫ (snd (𝟙_ _) G).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]

  have lev : ∀ e : ℕ, ∃ τ : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => (U.gt e).pG.left) (fun _ => (k : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left) (z : Z) JG J,
        Good U.P.L.L z JG → Good D.P.L z J →
        sval τ r z J = (gw (U.w e) r z (J (r ≫ (U.gt e).pG.left))
          (fun _ => JG (r ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left))).val ^ k *
          sval σ ((r ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left) ≫ (λ_ G).inv.left) z JG := fun e => by
    obtain ⟨s, hs⟩ := exists_pull (φ' := fun _ : Fin 1 => (fstG (IsLocalRing.maximalIdeal V) e G).left)
      ((fstG (IsLocalRing.maximalIdeal V) e G).left ≫ (λ_ G).inv.left)
      (fun _ => by rw [Category.assoc, lam', Category.comp_id]) σ
    obtain ⟨τ, hτ⟩ := exists_carry hG hB (U.w e) (U.w_gen e) k s
    refine ⟨τ, fun Z r z JG J hJG hJ => (hτ Z r z JG J hJG hJ).trans (congrArg _ ((hs Z r z JG hJG).trans ?_))⟩
    exact congrArg (fun p => sval σ p z JG) (Category.assoc _ _ _).symm
  choose τ hτ using lev
  have ex := fun e => GlobalTheory.T.existsUnique_thickTorus_level_weight_expansion V _ D e G (U.gt e) k (τ e)
  choose f hf hu using ex
  choose S hS hsum using hf

  have compat : ∀ α e z J, Good D.P.L z J →
      sval (f (e + 1) α) (thickMap V _ e D.P.A) z J = sval (f e α) (𝟙 _) z J := by
    intro α e
    choose f' hf' using fun β => exists_pull
      (φ' := fun i => (D.prBe (IsLocalRing.maximalIdeal V) e).left ≫ D.famφB β i) (thickMap V _ e D.P.A)
      (fun i => ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ D.famφB β i) (thickMap_prBe e))).symm) (f (e + 1) β)
    have E : f' = f e := by
      refine hu e f' ⟨S (e + 1), fun β hβ => zero_of_sval hB fun y J hJ =>
        (hf' β _ _ y J hJ).trans (sval_zero (hS _ β hβ) _ hJ), fun z J hJ => ?_⟩
      obtain ⟨JG, hJG⟩ := exists_good_pt hG z
      have a := sum_of_id (hsum (e + 1)) (thickMap V _ e G) z hJ
      have b : sval (τ e) (𝟙 (thickObj V (IsLocalRing.maximalIdeal V) e G).left) z J =
          sval (τ (e + 1)) (thickMap V _ e G) z J := by
        refine (hτ e _ _ z JG J hJG hJ).trans (Eq.trans ?_ (hτ (e + 1) _ _ z JG J hJG hJ).symm)
        have c := U.w_compat e _ (𝟙 _) z _ _ (hJ (U.gt e).pG.left) (hJG (fstG (IsLocalRing.maximalIdeal V) e G).left)
        rw [Category.id_comp] at c
        rw [U.gt_q, thickMap_fst, c]
        simp only [Category.id_comp]
      refine b.trans (a.trans (Finset.sum_congr rfl fun β _ => congrArg₂ (· * ·) ?_ (congrArg Units.val ?_)))
      · exact (congrArg (fun p => sval (f (e + 1) β) p z J) (q_thickMap U e).symm).trans (hf' β _ _ z J hJ).symm
      · exact ((congrArg (fun p => val ((U.gt (e + 1)).t β) p z J) (Category.id_comp _).symm).trans
          (val_pull hJ _ _ _).symm).trans (val_corr hJ (U.gt_t e β) _)
    intro z J hJ
    rw [← E]
    exact ((hf' α _ _ z J hJ).trans (congrArg (fun p => sval (f (e + 1) α) p z J) (Category.id_comp _))).symm
  choose s hs _ using fun α => GlobalTheory.T.existsUnique_twistedSection_of_compatible_levels h1 h2 V hV D k hk α (fun e => f e α) (compat α)
  choose F hF using fun α => exists_pull (snd (𝟙_ _) D.P.A).left (famφT_eq (𝟙_ _) α) (s α)
  refine ⟨F, fun e => ⟨S e, fun Z x rG rB hrG hrB _ z JG J hJG hJ => ?_⟩⟩
  have v : ∀ α, sval (F α) rB z J = sval (f e α) (x ≫ (U.gt e).q.left) z J := fun α => by
    refine (hF α _ _ z J hJ).trans ?_
    have a := sval_eq_of_id (hs α e) (x ≫ (U.gt e).q.left) z hJ
    refine Eq.trans (congrArg (fun p => sval (s α) p z J) (hrB.trans (Category.assoc _ _ _).symm)) (a.trans ?_)
    exact congrArg (fun p => sval (f e α) p z J) (Category.comp_id _)
  refine ⟨fun α hα => (v α).trans (sval_zero (hS e α hα) _ hJ), ?_⟩
  have r : rG = (x ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left) ≫ (λ_ G).inv.left := by
    rw [← hrG, Category.assoc, lam, Category.comp_id]
  rw [r]
  refine (hτ e _ x z JG J hJG hJ).symm.trans ((sum_of_id (hsum e) x z hJ).trans ?_)
  exact Finset.sum_congr rfl fun α _ => congrArg (· * _) (v α).symm

end GlobalTheory.BaseExpansionExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpansionSectionLineBundlePowerStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_expansion_section_lineBundle_power : Laws → Laws2 → (AllPre fun U => ∀ k, 1 ≤ k → ∀ σ, ∃ f, U.ExpT (𝟙_ _) k σ f) := by
  first | exact @GlobalTheory.BaseExpansionExists.main | exact GlobalTheory.BaseExpansionExists.main | (intros; apply GlobalTheory.BaseExpansionExists.main <;> assumption)
end
