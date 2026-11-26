module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CatCoh GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

@[reducible] def Charts.std {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] (F : Fam I g Λ)
    (Q : Opens (Tot I g) → Prop) : Charts F where
  K := {W : Opens (Tot I g) // (∀ p ∈ W, p.1 ∈ F.V) ∧ Q W}
  W k := k.1
  base k := k.2.1
  le l k' k := ∀ p ∈ k'.1, F.shift l p ∈ k.1
  le_refl k p hp := by rwa [F.shift_zero]
  le_trans h h' p hp := by rw [F.shift_add]; exact h _ (h' p hp)
  maps h := h

section Fibre

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

@[reducible] def fibFam (u : HolUnif A L g) : Fam Empty g u.Λ where
  V := ⊤
  τ := { toFun x := fun _ ↦ (x : Fin g → ℂ), map_zero' := rfl, map_add' _ _ := rfl }
  hol _ := analyticOnNhd_const

def fibUnif (u : HolUnif A L g) : Unif (fibFam u) (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol (fibFam u).V)) where
  E p := (u.ex p.2).left
  w p hp := by
    have e : (Hol.ev p.1 hp).toRingHom.comp (algebraMap ℂ (Hol (fibFam u).V)) = RingHom.id ℂ :=
      RingHom.ext fun c ↦ (Hol.ev p.1 hp).commutes c
    rw [e, Cris.spMap_id, Category.comp_id]
    exact Over.w (u.ex p.2)
  per l p _ := by
    change (u.ex (p.2 + (l : Fin g → ℂ))).left = _
    rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
  hol U f := ⟨by
    have := (u.hol U f).1.preimage (continuous_snd (X := Empty → ℂ))
    convert this using 1
    exact Set.ext fun p ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨trivial, h⟩⟩,
    (u.hol U f).2.comp differentiableOn_snd fun _ h ↦ h.2⟩

def IsPeriodHom (u : HolUnif A L g) (P : u.Λ →+ HdR A) : Prop :=
  ∀ c : primDR A, IsPeriod (fibUnif u) c.1
    { toFun x := algebraMap ℂ (Hol (fibFam u).V) (P x c)
      map_zero' := by rw [map_zero, LinearMap.zero_apply, map_zero]
      map_add' x y := by
        rw [map_add P x y, LinearMap.add_apply]
        exact (algebraMap ℂ (Hol (fibFam u).V)).map_add _ _ }

end Fibre

def PExist : Prop :=
  ∀ (I : Type) [Fintype I] (g : ℕ) (Λ : Type) [AddCommGroup Λ] (F : Fam I g Λ) (B : Type) [CommRing B] (X : Scheme.{0})
    (s : X ⟶ Sp B) [IsSeparated s] (σ : B →+* Hol F.V) (u : Unif F s σ), u.Based → ∀ c : FirstDeRham s, ∃ per, IsPeriod u c per

def PUniq : Prop :=
  ∀ (I : Type) [Fintype I] (g : ℕ) (Λ : Type) [AddCommGroup Λ] (F : Fam I g Λ) (B : Type) [CommRing B] (X : Scheme.{0})
    (s : X ⟶ Sp B) [IsSeparated s] (σ : B →+* Hol F.V) (u : Unif F s σ) (c : FirstDeRham s) (per per' : Λ →+ Hol F.V),
    IsPeriod u c per → IsPeriod u c per' → per = per'

def PHom : Prop :=
  ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → ∀ (L : LB A.left) (u : HolUnif A L g), ∃ P, IsPeriodHom u P

def PLie : Prop :=
  ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (L : LB A.left) (u : HolUnif A L g) (P : u.Λ →+ HdR A), IsPeriodHom u P →
    ∀ x : u.Λ, ∃ v, IsLieImage (P x) v ∧ u.IsDiff x v

def PEnd : Prop :=
  ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    ∀ (L : LB A.left) (u : HolUnif A L g) (P : u.Λ →+ HdR A), IsPeriodHom u P →
    ∀ (α : A ⟶ A) [IsMonHom α] (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ w, u.ex (M w) = u.ex w ≫ α) →
      ∀ x x' : u.Λ, (x' : Fin g → ℂ) = M x → push (dp0 ℂ) (𝟙 _) α (P x) = P x'

def PChern (ε : ℤˣ) : Prop :=
  ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    ∀ (L : LB A.left) (u : HolUnif A L g) (P : u.Λ →+ HdR A), IsPeriodHom u P →
    ∀ (M : LB A.left) (u' : HolUnif A M g), M.IsLB → u'.ex = u.ex →
    ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u'.Λ → ℂ) (ψ : LinearMap.BilinForm ℂ (HdR A)), u'.IsAH H χ →
      IsPolForm (dp0 ℂ) (𝟙 _) A M ψ → ∀ x x' : u.Λ,
        ψ (P x) (P x') = ((ε : ℤ) : ℂ) * (2 * Real.pi * Complex.I) *
          (((x : Fin g → ℂ) ⬝ᵥ H.mulVec (star (x' : Fin g → ℂ))).im : ℂ)

def PSpan : Prop :=
  ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (L : LB A.left) (u : HolUnif A L g) (P : u.Λ →+ HdR A), IsPeriodHom u P →
    Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (HdR A) = 2 * g

def PFix : Prop :=
  ∀ (I : Type) [Fintype I] (g : ℕ) (Λ : Type) [AddCommGroup Λ] (F : Fam I g Λ) (B : Type) [CommRing B]
    (𝒜 : Over (Sp B)) [GrpObj 𝒜], IsAbelianScheme 𝒜 → ∀ (σ : B →+* Hol F.V) (e : Unif F (𝒜.hom ≫ 𝟙 _) σ)
    (z : I → ℂ), z ∈ F.V → ∀ (y : B →+* ℂ), (∀ b, y b = (σ b).fn z) →
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (φ : A.left ⟶ 𝒜.left)
      (m : GrpMor (dp0 B) (𝟙 _) 𝒜 (dp0 ℂ) (𝟙 _) A y (spMap y) φ) (L : LB A.left) (u : HolUnif A L g),
      (∀ w, e.E (z, w) = (u.ex w).left ≫ φ) → ∀ τ : Λ →+ u.Λ, (∀ l, (τ l : Fin g → ℂ) = F.τ l z) →
    ∀ (P : u.Λ →+ HdR A), IsPeriodHom u P → ∀ (c : primDR 𝒜) (per : Λ →+ Hol F.V), IsPeriod e c.1 per →
      ∀ l, P (τ l) (m.pull c) = (per l).fn z

def PTaylor : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (g : ℕ) (B : Type) [CommRing B] [Algebra ℂ B]
    (𝒜 : Over (Sp B)) [GrpObj 𝒜], IsAbelianScheme 𝒜 → SmoothOfRelativeDimension g 𝒜.hom →
    ∀ (y₀ : B →ₐ[ℂ] ℂ) (A₀ : Over (Sp ℂ)) [GrpObj A₀] (φ₀ : A₀.left ⟶ 𝒜.left),
      IsGrpPullback A₀ 𝒜 (spMap (y₀ : B →+* ℂ)) φ₀ → ∀ (L₀ : LB A₀.left) (u₀ : HolUnif A₀ L₀ g)
      (F : Fam I g u₀.Λ) (σ : B →ₐ[ℂ] Hol F.V) (e : Unif F (𝒜.hom ≫ 𝟙 _) (σ : B →+* Hol F.V)), 0 ∈ F.V →
      (∀ b, y₀ b = (σ b).fn 0) → (∀ w, e.E (0, w) = (u₀.ex w).left ≫ φ₀) → (∀ x, F.τ x 0 = x) →
    ∀ (P₀ : u₀.Λ →+ HdR A₀), IsPeriodHom u₀ P₀ →
    ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ →
      (∀ a : ℂ, π (algebraMap ℂ D a) = a) →
      ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) →
      ∀ (j : B →ₐ[ℂ] D), (∀ b, j b = taylor N t (σ b).fn) →
      ∀ (A' : Over (Sp D)) [GrpObj A'] (φ' : A'.left ⟶ 𝒜.left), IsGrpPullback A' 𝒜 (spMap (j : B →+* D)) φ' →
      ∀ (m' : GrpMor (dp0 B) (𝟙 _) 𝒜 (dp0 D) (𝟙 _) A' (j : B →+* D) (spMap (j : B →+* D)) φ')
        (i : A₀.left ⟶ A'.left) (h : IsGrpPullback A₀ A' (spMap π) i), i ≫ φ' = φ₀ →
      ∀ (k : GrpMor (dp0 ℂ) (𝟙 _) A₀ κ (spMap π) A₀ (algebraMap ℂ D) (𝟙 _) (Over.Hom.left (𝟙 A₀)))
        (x : u₀.Λ) (d : Crys κ (spMap π) A₀), k.Corr (P₀ x) d → ∀ (c : primDR 𝒜) (per : u₀.Λ →+ Hol F.V),
        IsPeriod e c.1 per → crysToDR κ h d (m'.pull c) = taylor N t (per x).fn

end GlobalTheory.AnPer
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
set_option autoImplicit false

noncomputable section

open TopologicalSpace CategoryTheory AlgebraicGeometry GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AnPer

section Tay

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {R : Type} [CommRing R] [Algebra ℂ R]

abbrev evT {W : Opens E} (R : Type) [CommRing R] [Algebra ℂ R] (p : E) (hp : p ∈ W) : R ⊗[ℂ] Hol W →ₐ[ℂ] R :=
  Algebra.TensorProduct.lift (AlgHom.id ℂ R) ((Algebra.ofId ℂ R).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _)

def IsTay {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} (N : ℕ) (t : I → R) {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    (ρ : Hol W →+* R ⊗[ℂ] Hol W₀) : Prop :=
  ∀ (h : Hol W) (p : Tot Empty g) (hp : p ∈ W₀), evT R p hp (ρ h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)

end Tay

namespace Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
  {R : Type} [CommRing R]

def shA {l : Λ} {k k' : K.K} (h : K.le l k' k) : Hol (K.W k) →ₐ[ℂ] Hol (K.W k') :=
  Hol.comap (F.shift l) (F.shift_analytic l (K.base k')) (K.maps h)

theorem shA_apply {l : Λ} {k k' : K.K} (h : K.le l k' k) (x : Hol (K.W k)) : shA h x = sh h x := rfl


variable (K) in
structure DObj (η : Hol F.V →+* R) (M : Ideal R) : Type 1 where

  T : K.Obj
  [alg : Algebra R T.C]
  compat : ∀ f, algebraMap (Hol F.V) T.C f = algebraMap R T.C (η f)
  mem : ∀ d ∈ M, algebraMap R T.C d ∈ T.J

attribute [instance] DObj.alg

variable {η : Hol F.V →+* R} {M : Ideal R}

instance : Category (K.DObj η M) where
  Hom S S' := {f : S.T ⟶ S'.T // ∀ d, f.φ (algebraMap R S.T.C d) = algebraMap R S'.T.C d}
  id S := ⟨𝟙 _, fun _ ↦ rfl⟩
  comp f f' := ⟨f.1 ≫ f'.1, fun d ↦ by rw [comp_φ, f.2, f'.2]⟩
  id_comp f := Subtype.ext (Category.id_comp _)
  comp_id f := Subtype.ext (Category.comp_id _)
  assoc f f' f'' := Subtype.ext (Category.assoc _ _ _)


variable (K η M) in
@[reducible] def OD : K.DObj η M ⥤ CommAlgCat.{0} R where
  obj S := CommAlgCat.of _ S.T.C
  map f := CommAlgCat.ofHom { (f.1.φ : _ →+* _) with commutes' := f.2 }


variable (K η M) in
def perZD (q : Λ →+ R) : Z1 (K.OD η M) :=
  ⟨fun _ S' f ↦ algebraMap R S'.T.C (q f.1.deg), fun S S' S'' f f' ↦ by
    change algebraMap _ S''.T.C (q (f.1.deg + f'.1.deg)) = f'.1.φ (algebraMap _ _ _) + algebraMap _ S''.T.C _
    rw [f'.2, map_add (f := _), map_add (f := _)]⟩


variable (K η M) in
def perClD (q : Λ →+ R) : CatCoh.H1 (K.OD η M) := H1.mk _ (K.perZD η M q)


end Charts

section Theta

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
  {R : Type} [CommRing R] {η : Hol F.V →+* R} {M : Ideal R}
  {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V}
  {D : Type} [CommRing D] {J : Ideal D}

structure IsOver (η : Hol F.V →+* R) (M : Ideal R) (s : X ⟶ Sp B) (σ : B →+* Hol F.V) (J : Ideal D) (s' : X ⟶ Sp D)
    (π : D →+* B) (ι : D →+* R) : Prop where
  w : s' = s ≫ spMap π
  mem : ∀ d ∈ J, ι d ∈ M
  red : ∀ d, ι d - η (σ (π d)) ∈ M

variable (r : Real K s σ) (κ : DividedPowers J) {s' : X ⟶ Sp D} {π : D →+* B} {ι : D →+* R} (H : IsOver η M s σ J s' π ι)

def Real.objD (S : K.DObj η M) : Thick κ s' where
  B := S.T.C
  alg := ((algebraMap R S.T.C).comp ι).toAlgebra
  J := S.T.J
  δ := S.T.δ
  nil := letI := S.T.ratAlg; isPDNilpotent_of_rat _ S.T.nil
  dp := letI := S.T.ratAlg; isDPMorphism_of_rat κ S.T.δ _ fun d hd ↦ S.mem _ (H.mem d hd)
  B₀ := S.T.C ⧸ S.T.J
  π := Ideal.Quotient.mk S.T.J
  surj := Ideal.Quotient.mk_surjective
  ker _ := Ideal.Quotient.eq_zero_iff_mem
  x := spMap ((Ideal.Quotient.mk S.T.J).comp S.T.ρ) ≫ r.x S.T.k
  w := by
    rw [H.w, Category.assoc, ← Category.assoc (r.x _), r.w, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 1
    refine RingHom.ext fun d ↦ (Ideal.Quotient.eq.2 ?_).symm
    have := S.mem _ (H.red d)
    rw [map_sub, ← S.compat, ← S.T.ρ_cst] at this
    exact this

def Real.coefD : CoefMap ι (O κ s') (K.OD η M) where
  G :=
    { obj := r.objD κ H
      map {S S'} f :=
        { φ := { (f.1.φ : S.T.C →+* S'.T.C) with commutes' := fun d ↦ f.2 (ι d) }
          φ₀ := Ideal.quotientMap S'.T.J (f.1.φ : S.T.C →+* S'.T.C) f.1.mem
          comm := fun _ ↦ rfl
          dp := letI := S'.T.ratAlg; isDPMorphism_of_rat S.T.δ S'.T.δ (f.1.φ : S.T.C →+* S'.T.C) f.1.mem
          pt := r.analyticChartsRealization_comp_point_eq f.1 }
      map_id _ := Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl)
      map_comp _ _ := Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl) }
  α S := RingHom.id S.T.C
  naturality _ _ := rfl
  smul S d c := (Algebra.smul_def (A := S.T.C) (ι d) c).symm

end Theta

section Inhabitants

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}

def jetAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} (v p : E) (hp : p ∈ W) :
    Hol W →+* DualNumber ℂ where
  toFun h := TrivSqZeroExt.inl (Hol.ev p hp h) + TrivSqZeroExt.inr (Hol.ev p hp (Hol.der v h))
  map_one' := by simp
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [Derivation.leibniz, mul_comm]
  map_zero' := by simp
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp

def Charts.dualD (K : Charts F) (k : K.K) (v : I → ℂ) (p : Tot I g) (hp : p ∈ K.W k) :
    K.DObj (jetAt v p.1 (K.base k p hp)) (Ideal.span {DualNumber.eps}) where
  T :=
    { k := k
      C := DualNumber ℂ
      alg := (jetAt v p.1 (K.base k p hp)).toAlgebra
      J := Ideal.span {DualNumber.eps}
      nil := ⟨2, by rw [Ideal.span_singleton_pow, sq, DualNumber.eps_mul_eps]; simp⟩
      ρ := jetAt ((v, 0) : Tot I g) p hp
      ρ_cst := fun f ↦ by
        have e1 : Hol.ev p hp (K.cst k f) = Hol.ev p.1 (K.base k p hp) f := by
          rw [Hol.ev_apply, Hol.ev_apply, K.fn_cst k f hp]
        have e2 : Hol.ev p hp (Hol.der ((v, 0) : Tot I g) (K.cst k f)) =
            Hol.ev p.1 (K.base k p hp) (Hol.der v f) := by
          rw [Hol.ev_apply, Hol.ev_apply, Hol.fn_der _ _ (K.base k p hp)]
          refine (Hol.fn_der_comap _ _ _ _ f hp).trans ?_
          rw [fderiv_fst]; rfl
        change (TrivSqZeroExt.inl _ + TrivSqZeroExt.inr _ : DualNumber ℂ) = TrivSqZeroExt.inl _ + TrivSqZeroExt.inr _
        rw [e1, e2] }
  alg := Algebra.id (DualNumber ℂ)
  compat _ := rfl
  mem _ h := h

theorem Charts.dualD_J_ne_bot (K : Charts F) (k : K.K) (v : I → ℂ) (p : Tot I g) (hp : p ∈ K.W k) :
    (K.dualD k v p hp).T.J ≠ ⊥ := by
  intro h
  have h' : (DualNumber.eps : DualNumber ℂ) = 0 := Ideal.span_singleton_eq_bot.1 h
  simpa using congrArg TrivSqZeroExt.snd h'

def Charts.Obj.toD {K : Charts F} (T : K.Obj) : K.DObj (RingHom.id _) ⊥ where
  T := T
  alg := T.alg
  compat _ := rfl
  mem d h := by rw [Ideal.mem_bot.1 h, map_zero]; exact T.J.zero_mem

end Inhabitants

end GlobalTheory.AnPer
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.SubRedMem
set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology TensorProduct

namespace GlobalTheory.AnPer

open CategoryTheory AlgebraicGeometry GlobalTheory.CatCoh GlobalTheory.Cris DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}

@[reducible] def Charts.Obj.cAlg (T : K.Obj) : Algebra ℂ T.C :=
  ((algebraMap (Hol F.V) T.C).comp (algebraMap ℂ (Hol F.V))).toAlgebra

attribute [local instance] Charts.Obj.cAlg

def Charts.Hom.φc {T T' : K.Obj} (f : T ⟶ T') : T.C →ₐ[ℂ] T'.C :=
  { (f.φ : T.C →+* T'.C) with commutes' := fun c ↦ f.φ.commutes (algebraMap ℂ (Hol F.V) c) }

def Charts.Obj.ρc (T : K.Obj) : Hol (K.W T.k) →ₐ[ℂ] T.C :=
  { T.ρ with
    commutes' := fun c ↦ by
      have e : K.cst T.k (algebraMap ℂ (Hol F.V) c) = algebraMap ℂ _ c := rfl
      exact (congrArg T.ρ e.symm).trans (T.ρ_cst _) }

variable (D : Type) [CommRing D] [Algebra ℂ D]

abbrev Charts.Obj.ten (T : K.Obj) : Type := D ⊗[ℂ] T.C

def Charts.Hom.ten {T T' : K.Obj} (f : T ⟶ T') : T.ten D →ₐ[D] T'.ten D :=
  Algebra.TensorProduct.map (AlgHom.id D D) (Charts.Hom.φc f)

theorem Charts.Hom.ten_tmul {T T' : K.Obj} (f : T ⟶ T') (d : D) (c : T.C) :
    Charts.Hom.ten D f (d ⊗ₜ c) = d ⊗ₜ f.φ c := rfl


variable (K) in
@[reducible] def Charts.Ten : K.Obj ⥤ CommAlgCat.{0} D where
  obj T := CommAlgCat.of D (T.ten D)
  map f := CommAlgCat.ofHom (Charts.Hom.ten D f)
  map_id T := CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun _ _ ↦ rfl)
  map_comp f f' := CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun _ _ ↦ rfl)

variable {D}


variable (K) in
def Charts.tenZ (p : Λ →+ D) : Z1 (K.Ten D) :=
  ⟨fun _ T' f ↦ algebraMap D (T'.ten D) (p f.deg), fun T T' T'' f f' ↦ by
    change algebraMap D (T''.ten D) (p (f.deg + f'.deg)) =
      Charts.Hom.ten D f' (algebraMap D _ _) + algebraMap D (T''.ten D) _
    rw [AlgHom.commutes, map_add (f := _), map_add (f := _)]⟩

variable (π : D →ₐ[ℂ] ℂ)

def Charts.Obj.red (T : K.Obj) : T.ten D →ₐ[ℂ] T.C :=
  Algebra.TensorProduct.lift ((Algebra.ofId ℂ T.C).comp π) (AlgHom.id ℂ T.C) fun _ _ ↦ Commute.all _ _

theorem Charts.Obj.red_tmul (T : K.Obj) (d : D) (c : T.C) : T.red π (d ⊗ₜ c) = algebraMap ℂ T.C (π d) * c := rfl

def Charts.Obj.tenJ (T : K.Obj) : Ideal (T.ten D) := T.J.comap (T.red π)


set_option autoImplicit false in
open TopologicalSpace Filter Topology TensorProduct in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : _root_.GlobalTheory.AnPer.Fam I g Λ}
  {K : _root_.GlobalTheory.AnPer.Charts F} in
attribute [local instance] _root_.GlobalTheory.AnPer.Charts.Obj.cAlg in
variable (D : Type) [CommRing D] [Algebra ℂ D] in
variable {D} in
variable (π : D →ₐ[ℂ] ℂ) in
theorem _root_.GlobalTheory.AnPer.Charts.Hom.red_ten
    {T T' : K.Obj} (f : T ⟶ T') (x : T.ten D) :
    T'.red π
        (_root_.GlobalTheory.AnPer.Charts.Hom.ten D f x) =
      f.φ (T.red π x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d c =>
    rw [_root_.GlobalTheory.AnPer.Charts.Hom.ten_tmul,
      _root_.GlobalTheory.AnPer.Charts.Obj.red_tmul,
      _root_.GlobalTheory.AnPer.Charts.Obj.red_tmul, map_mul]
    congr 1
    exact ((_root_.GlobalTheory.AnPer.Charts.Hom.φc f).commutes
      (π d)).symm
  | add x y hx hy => simp only [map_add (f := _), hx, hy]


set_option autoImplicit false in
open TopologicalSpace Filter Topology TensorProduct in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : _root_.GlobalTheory.AnPer.Fam I g Λ}
  {K : _root_.GlobalTheory.AnPer.Charts F} in
attribute [local instance] _root_.GlobalTheory.AnPer.Charts.Obj.cAlg in
variable (D : Type) [CommRing D] [Algebra ℂ D] in
variable {D} in
variable (π : D →ₐ[ℂ] ℂ) in
theorem _root_.GlobalTheory.AnPer.Charts.Hom.ten_mem {T T' : K.Obj}
    (f : T ⟶ T') {x : T.ten D} (h : x ∈ T.tenJ π) :
    _root_.GlobalTheory.AnPer.Charts.Hom.ten D f x ∈
      T'.tenJ π := by
  change T'.red π _ ∈ T'.J
  rw [_root_.GlobalTheory.AnPer.Charts.Hom.red_ten]
  exact f.mem _ h

set_option autoImplicit false in
open TopologicalSpace Filter Topology TensorProduct in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : _root_.GlobalTheory.AnPer.Fam I g Λ}
  {K : _root_.GlobalTheory.AnPer.Charts F} in
attribute [local instance] _root_.GlobalTheory.AnPer.Charts.Obj.cAlg in
variable (D : Type) [CommRing D] [Algebra ℂ D] in
variable {D} in
variable (π : D →ₐ[ℂ] ℂ) in
private theorem sub_one_tmul_red_mem_map_ker (T : K.Obj) (x : T.ten D) :
    x - (1 : D) ⊗ₜ T.red π x ∈
      (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] T.C) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d c =>
    rw [_root_.GlobalTheory.AnPer.Charts.Obj.red_tmul,
      ← Algebra.smul_def]
    have e : d ⊗ₜ[ℂ] c - (1 : D) ⊗ₜ (π d • c) =
        (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] T.C) (d - algebraMap ℂ D (π d)) *
          ((1 : D) ⊗ₜ c) := by
      rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
        sub_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [e]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  | add x y hx hy =>
    rw [map_add (f := _), tmul_add, add_sub_add_comm]
    exact add_mem hx hy


set_option autoImplicit false in
open TopologicalSpace Filter Topology TensorProduct in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : _root_.GlobalTheory.AnPer.Fam I g Λ}
  {K : _root_.GlobalTheory.AnPer.Charts F} in
attribute [local instance] _root_.GlobalTheory.AnPer.Charts.Obj.cAlg in
variable (D : Type) [CommRing D] [Algebra ℂ D] in
variable {D} in
variable (π : D →ₐ[ℂ] ℂ) in
theorem _root_.GlobalTheory.AnPer.Charts.Obj.tenJ_nil
    (hπ : IsNilpotent (RingHom.ker π)) (T : K.Obj) : IsNilpotent (T.tenJ π) := by
  obtain ⟨m, hm⟩ := hπ
  obtain ⟨n, hn⟩ := T.nil
  have hle : T.tenJ π ≤
      (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] T.C) ⊔
        T.J.map (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] D ⊗[ℂ] T.C) := by
    intro x hx
    have hx' : T.red π x ∈ T.J := hx
    have e : x = (x - (1 : D) ⊗ₜ T.red π x) +
        (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] D ⊗[ℂ] T.C)
          (T.red π x) := by
      rw [Algebra.TensorProduct.includeRight_apply, sub_add_cancel]
    rw [e]
    exact add_mem (Ideal.mem_sup_left (sub_one_tmul_red_mem_map_ker π T x))
      (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hx'))
  refine ⟨m + n, eq_bot_iff.2 ?_⟩
  calc T.tenJ π ^ (m + n)
      ≤ ((RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] T.C) ⊔
          T.J.map (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] D ⊗[ℂ] T.C)) ^ (m + n) :=
        Ideal.pow_right_mono hle _
    _ ≤ (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] T.C) ^ m ⊔
          T.J.map (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] D ⊗[ℂ] T.C) ^ n :=
        Ideal.sup_pow_add_le_pow_sup_pow
    _ = ⊥ := by
        rw [← Ideal.map_pow, ← Ideal.map_pow, hm, hn]
        simp only [Ideal.zero_eq_bot, Ideal.map_bot, sup_bot_eq]

@[reducible] def Charts.Obj.tenRat (T : K.Obj) : Algebra ℚ (T.ten D) :=
  ((algebraMap ℂ (T.ten D)).comp (algebraMap ℚ ℂ)).toAlgebra


open Classical in
def Charts.Obj.tenδ (T : K.Obj) : DividedPowers (T.tenJ π) :=
  letI := T.tenRat (D := D)
  RatAlgebra.dividedPowers (T.tenJ π)

variable {X : Scheme.{0}} {s : X ⟶ Sp ℂ} {σ : ℂ →+* Hol F.V} (r : Real K s σ) (hσ : σ = algebraMap ℂ (Hol F.V))
  {D₀ : Type} [CommRing D₀] {π₀ : D₀ →+* ℂ} (κ : DividedPowers (RingHom.ker π₀)) {s' : X ⟶ Sp D₀}
  (hs : s' = s ≫ spMap π₀) (ι : D₀ →+* D) (hι : ∀ d, π (ι d) = π₀ d) (hπ : IsNilpotent (RingHom.ker π))

def Real.tenObj (T : K.Obj) : Thick κ s' where
  B := T.ten D
  alg := ((algebraMap D (T.ten D)).comp ι).toAlgebra
  J := T.tenJ π
  δ := T.tenδ π
  nil := letI := T.tenRat (D := D); isPDNilpotent_of_rat _ (T.tenJ_nil π hπ)
  dp := letI := T.tenRat (D := D); isDPMorphism_of_rat κ _ ((algebraMap D (T.ten D)).comp ι) fun d hd ↦ by
    change T.red π (ι d ⊗ₜ 1) ∈ T.J
    rw [Charts.Obj.red_tmul, hι, (RingHom.mem_ker).1 hd, map_zero, zero_mul]
    exact T.J.zero_mem
  B₀ := T.C ⧸ T.J
  π := (Ideal.Quotient.mk T.J).comp (T.red π)
  surj c := by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨1 ⊗ₜ c, congrArg (Ideal.Quotient.mk T.J) (by
      change T.red π _ = c
      rw [Charts.Obj.red_tmul, map_one, map_one, one_mul])⟩
  ker _ := Ideal.Quotient.eq_zero_iff_mem
  x := (r.obj T).x
  w := by
    refine (congrArg ((r.obj T).x ≫ ·) hs).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ spMap π₀) (r.obj T).w).trans ((Cris.spMap_comp _ _).symm.trans (congrArg spMap ?_))))
    refine RingHom.ext fun d ↦ congrArg (Ideal.Quotient.mk T.J) ?_
    change algebraMap (Hol F.V) T.C (σ (π₀ d)) = T.red π (ι d ⊗ₜ 1)
    rw [Charts.Obj.red_tmul, hι, mul_one, hσ]
    rfl

def Real.tenFunctor : K.Obj ⥤ Thick κ s' where
  obj := r.tenObj π hσ κ hs ι hι hπ
  map {T T'} f :=
    { φ := { (Charts.Hom.ten D f : T.ten D →+* T'.ten D) with commutes' := fun d ↦ (Charts.Hom.ten D f).commutes (ι d) }
      φ₀ := Ideal.quotientMap T'.J (f.φ : T.C →+* T'.C) f.mem
      comm := fun x ↦ congrArg (Ideal.Quotient.mk T'.J) (Charts.Hom.red_ten π f x).symm
      dp := letI := T'.tenRat (D := D); isDPMorphism_of_rat (T.tenδ π) (T'.tenδ π)
        (Charts.Hom.ten D f : T.ten D →+* T'.ten D) fun _ h ↦ Charts.Hom.ten_mem π f h
      pt := r.analyticChartsRealization_comp_point_eq f }
  map_id T := Thick.Hom.ext' (AlgHom.ext fun b ↦ mp_id (K.Ten D) T b)
  map_comp f f' := Thick.Hom.ext' (AlgHom.ext fun b ↦ mp_comp (K.Ten D) f f' b)

def Real.tenCoef : CoefMap ι (O κ s') (K.Ten D) where
  G := r.tenFunctor π hσ κ hs ι hι hπ
  α T := RingHom.id (T.ten D)
  naturality _ _ := rfl
  smul T b c := (Algebra.smul_def (A := T.ten D) (ι b) c).symm

end GlobalTheory.AnPer
end
end
