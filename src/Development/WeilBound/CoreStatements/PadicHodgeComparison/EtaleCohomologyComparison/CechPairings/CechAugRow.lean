module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CxPairing
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

universe w w' w''

namespace CrystallineSemistableComparison

variable {R : Type} [CommRing R]

structure Cos (R : Type) [CommRing R] : Type (w + 1) where
  X : ℕ → Type w
  [ab : ∀ n, AddCommGroup (X n)]
  [md : ∀ n, Module R (X n)]
  δ : ∀ n, Fin (n + 2) → (X n →ₗ[R] X (n + 1))
  rel : ∀ n (j : Fin (n + 3)) (i : Fin (n + 2)) x,
    δ (n + 1) (j.succAbove i) (δ n (i.predAbove j) x) = δ (n + 1) j (δ n i x)

attribute [instance] Cos.ab Cos.md

def Cos.d (K : Cos.{w} R) (n : ℕ) : K.X n →ₗ[R] K.X (n + 1) := ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • K.δ n i

theorem Cos.d_apply (K : Cos.{w} R) (n : ℕ) (x : K.X n) : K.d n x = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • K.δ n i x := by
  simp only [Cos.d, LinearMap.sum_apply, LinearMap.smul_apply]

theorem Cos.dd (K : Cos.{w} R) (n : ℕ) (x : K.X n) : K.d (n + 1) (K.d n x) = 0 := by
  rw [Cos.d_apply, Cos.d_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, Finset.smul_sum, smul_smul]
  rw [← Fintype.sum_prod_type']
  refine Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨j, i⟩ _
    dsimp only
    rw [K.rel, GlobalTheory.CatH.DSq.sign_swap, neg_smul, add_neg_cancel]
  · rintro ⟨j, i⟩ _ _ h
    exact Fin.succAbove_ne j i (congrArg Prod.fst h)
  · intro _ _; exact Finset.mem_univ _
  · rintro ⟨j, i⟩ _
    simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

abbrev Cos.cx (K : Cos.{w} R) : Cx.{w} R where
  X := K.X
  d := K.d
  dd := K.dd

abbrev Cx.sub (K : Cx.{w} R) (S : ∀ n, Submodule R (K.X n)) (h : ∀ n x, x ∈ S n → K.d n x ∈ S (n + 1)) : Cx.{w} R where
  X n := S n
  d n := (K.d n).restrict (h n)
  dd n x := Subtype.ext (K.dd n x.1)

structure DCx (R : Type) [CommRing R] : Type (w + 1) where
  X : ℕ → ℕ → Type w
  [ab : ∀ p q, AddCommGroup (X p q)]
  [md : ∀ p q, Module R (X p q)]
  dh : ∀ p q, X p q →ₗ[R] X (p + 1) q
  dv : ∀ p q, X p q →ₗ[R] X p (q + 1)
  hh : ∀ p q x, dh (p + 1) q (dh p q x) = 0
  vv : ∀ p q x, dv p (q + 1) (dv p q x) = 0
  hv : ∀ p q x, dh p (q + 1) (dv p q x) = dv (p + 1) q (dh p q x)

attribute [instance] DCx.ab DCx.md

namespace DCx

variable (K : DCx.{w} R)

abbrev row (q : ℕ) : Cx.{w} R where
  X p := K.X p q
  d p := K.dh p q
  dd p := K.hh p q

abbrev col (p : ℕ) : Cx.{w} R where
  X q := K.X p q
  d q := K.dv p q
  dd q := K.vv p q

abbrev flip : DCx.{w} R where
  X p q := K.X q p
  dh p q := K.dv q p
  dv p q := K.dh q p
  hh p q := K.vv q p
  vv p q := K.hh q p
  hv p q x := (K.hv q p x).symm

def Dh (x : ∀ p q, K.X p q) : ∀ p q, K.X p q
  | 0, _ => 0
  | p + 1, q => K.dh p q (x p q)

def Dv (x : ∀ p q, K.X p q) : ∀ p q, K.X p q
  | _, 0 => 0
  | p, q + 1 => K.dv p q (x p q)

def D : (∀ p q, K.X p q) →ₗ[R] (∀ p q, K.X p q) where
  toFun x p q := K.Dh x p q + (-1 : ℤ) ^ p • K.Dv x p q
  map_add' x y := by
    funext p q
    rcases p with _ | p <;> rcases q with _ | q <;> simp [Dh, Dv] <;> abel
  map_smul' r x := by
    funext p q
    rcases p with _ | p <;> rcases q with _ | q <;> simp [Dh, Dv, smul_comm r]

theorem D_apply (x : ∀ p q, K.X p q) (p q : ℕ) : K.D x p q = K.Dh x p q + (-1 : ℤ) ^ p • K.Dv x p q := rfl

theorem DD (x : ∀ p q, K.X p q) : K.D (K.D x) = 0 := by
  funext p q
  rcases p with _ | _ | p <;> rcases q with _ | _ | q <;>
    simp [D_apply, Dh, Dv, K.hh, K.vv, K.hv, pow_succ]

def T (n : ℕ) : Submodule R (∀ p q, K.X p q) where
  carrier := {x | ∀ p q, p + q ≠ n → x p q = 0}
  add_mem' ha hb p q h := by simp [ha p q h, hb p q h]
  zero_mem' p q h := rfl
  smul_mem' c x hx p q h := by simp [hx p q h]

theorem D_mem (n : ℕ) (x : ∀ p q, K.X p q) (hx : x ∈ K.T n) : K.D x ∈ K.T (n + 1) := by
  intro p q h
  rcases p with _ | p <;> rcases q with _ | q
  · simp [D_apply, Dh, Dv]
  · simp [D_apply, Dh, Dv, hx 0 q (by omega)]
  · simp [D_apply, Dh, Dv, hx p 0 (by omega)]
  · simp [D_apply, Dh, Dv, hx p (q + 1) (by omega), hx (p + 1) q (by omega)]

abbrev tot : Cx.{w} R where
  X n := K.T n
  d n := K.D.restrict (K.D_mem n)
  dd n x := Subtype.ext (K.DD x.1)

def sgl (p q : ℕ) : K.X p q →ₗ[R] (∀ p q, K.X p q) :=
  (LinearMap.single R (fun p => ∀ q, K.X p q) p).comp (LinearMap.single R (fun q => K.X p q) q)

theorem sgl_self (p q : ℕ) (x : K.X p q) : K.sgl p q x p q = x := by simp [sgl]

theorem sgl_ne {p q p' q' : ℕ} (x : K.X p q) (h : p' ≠ p ∨ q' ≠ q) : K.sgl p q x p' q' = 0 := by
  by_cases hp : p' = p
  · subst hp
    simp [sgl, Pi.single_eq_of_ne (h.resolve_left fun h => h rfl)]
  · simp [sgl, Pi.single_eq_of_ne hp]

theorem D_sgl (p q : ℕ) (x : K.X p q) :
    K.D (K.sgl p q x) = K.sgl (p + 1) q (K.dh p q x) + (-1 : ℤ) ^ p • K.sgl p (q + 1) (K.dv p q x) := by
  have h1 : K.Dh (K.sgl p q x) = K.sgl (p + 1) q (K.dh p q x) := by
    funext a b
    rcases a with _ | a
    · rw [K.sgl_ne _ (Or.inl (by omega))]; rfl
    · by_cases h : a = p ∧ b = q
      · obtain ⟨rfl, rfl⟩ := h
        simp only [Dh, sgl_self]
      · rw [K.sgl_ne _ (by omega)]; simp only [Dh]; rw [K.sgl_ne _ (by omega), map_zero]
  have h2 : K.Dv (K.sgl p q x) = K.sgl p (q + 1) (K.dv p q x) := by
    funext a b
    rcases b with _ | b
    · rw [K.sgl_ne _ (Or.inr (by omega))]; cases a <;> rfl
    · by_cases h : a = p ∧ b = q
      · obtain ⟨rfl, rfl⟩ := h
        simp only [Dv, sgl_self]
      · rw [K.sgl_ne _ (by omega)]; simp only [Dv]; rw [K.sgl_ne _ (by omega), map_zero]
  funext a b
  rw [D_apply, h1, h2, Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
  by_cases h : a = p
  · rw [h]
  · rw [K.sgl_ne (K.dv p q x) (Or.inl h), smul_zero, smul_zero]

def inj (p q n : ℕ) (h : p + q = n) : K.X p q →ₗ[R] K.tot.X n :=
  (K.sgl p q).codRestrict (K.T n) fun x a b hab => K.sgl_ne x (by omega)

structure AugRow (A : Cx.{w'} R) (K : DCx.{w} R) where
  ε : ∀ q, A.X q →ₗ[R] K.X 0 q
  hε : ∀ q x, K.dh 0 q (ε q x) = 0
  comm : ∀ q x, K.dv 0 q (ε q x) = ε (q + 1) (A.d q x)

structure AugCol (A : Cx.{w'} R) (K : DCx.{w} R) where
  η : ∀ p, A.X p →ₗ[R] K.X p 0
  hη : ∀ p x, K.dv p 0 (η p x) = 0
  comm : ∀ p x, K.dh p 0 (η p x) = η (p + 1) (A.d p x)

variable {K} {A : Cx.{w'} R}

def AugRow.edge (e : AugRow A K) : Cx.Hom A K.tot (RingHom.id R) where
  f n := (K.inj 0 n n (Nat.zero_add n)).comp (e.ε n)
  comm n x := Subtype.ext (by
    change K.D (K.sgl 0 n (e.ε n x)) = K.sgl 0 (n + 1) (e.ε (n + 1) (A.d n x))
    rw [D_sgl, e.hε, e.comm]; simp)

def AugCol.edge (e : AugCol A K) : Cx.Hom A K.tot (RingHom.id R) where
  f n := (K.inj n 0 n rfl).comp (e.η n)
  comm n x := Subtype.ext (by
    change K.D (K.sgl n 0 (e.η n x)) = K.sgl (n + 1) 0 (e.η (n + 1) (A.d n x))
    rw [D_sgl, e.hη, e.comm]; simp)

variable {R' : Type} [CommRing R']

structure Hom (K : DCx.{w} R) (L : DCx.{w'} R') (σ : R →+* R') where
  f : ∀ p q, K.X p q →ₛₗ[σ] L.X p q
  ch : ∀ p q x, L.dh p q (f p q x) = f (p + 1) q (K.dh p q x)
  cv : ∀ p q x, L.dv p q (f p q x) = f p (q + 1) (K.dv p q x)

variable {L : DCx.{w'} R'} {σ : R →+* R'}

def Hom.row (φ : Hom K L σ) (q : ℕ) : Cx.Hom (K.row q) (L.row q) σ := ⟨fun p => φ.f p q, fun p => φ.ch p q⟩

def Hom.col (φ : Hom K L σ) (p : ℕ) : Cx.Hom (K.col p) (L.col p) σ := ⟨fun q => φ.f p q, fun q => φ.cv p q⟩

def Hom.tot (φ : Hom K L σ) : Cx.Hom K.tot L.tot σ where
  f n :=
    { toFun := fun x => ⟨fun p q => φ.f p q (x.1 p q), fun p q h => by
        change φ.f p q (x.1 p q) = 0
        rw [x.2 p q h, map_zero]⟩
      map_add' := fun x y => Subtype.ext (funext fun p => funext fun q => map_add (φ.f p q) _ _)
      map_smul' := fun c x => Subtype.ext (funext fun p => funext fun q => LinearMap.map_smulₛₗ (φ.f p q) _ _) }
  comm n x := Subtype.ext (by
    funext p q
    change L.D (fun p q => φ.f p q (x.1 p q)) p q = φ.f p q (K.D x.1 p q)
    rcases p with _ | p <;> rcases q with _ | q <;> simp [D_apply, Dh, Dv, φ.ch, φ.cv])

end DCx

structure CosCx (R : Type) [CommRing R] : Type (w + 1) where
  K : ℕ → Cx.{w} R
  δ : ∀ n, Fin (n + 2) → Cx.Hom (K n) (K (n + 1)) (RingHom.id R)
  rel : ∀ n (j : Fin (n + 3)) (i : Fin (n + 2)) q x,
    (δ (n + 1) (j.succAbove i)).f q ((δ n (i.predAbove j)).f q x) = (δ (n + 1) j).f q ((δ n i).f q x)

abbrev CosCx.cos (S : CosCx.{w} R) (q : ℕ) : Cos.{w} R where
  X p := (S.K p).X q
  δ p i := (S.δ p i).f q
  rel p j i := S.rel p j i q

abbrev CosCx.dcx (S : CosCx.{w} R) : DCx.{w} R where
  X p q := (S.K p).X q
  dh p q := (S.cos q).d p
  dv p q := (S.K p).d q
  hh p q := (S.cos q).dd p
  vv p q := (S.K p).dd q
  hv p q x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Cos.d_apply, Cos.d_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul]; exact congrArg _ ((S.δ p i).comm q x).symm

structure CxPairing (K : Cx.{w} R) (L : Cx.{w'} R) (M : Cx.{w''} R) where
  μ : ∀ {p q n : ℕ}, p + q = n → (K.X p →ₗ[R] L.X q →ₗ[R] M.X n)
  leib : ∀ {p q n : ℕ} (h : p + q = n) x y, M.d n (μ h x y) =
    μ (p := p + 1) (q := q) (by omega) (K.d p x) y + (-1 : ℤ) ^ p • μ (p := p) (q := q + 1) (by omega) x (L.d q y)

def CxPairing.cup {K : Cx.{w} R} {L : Cx.{w'} R} {M : Cx.{w''} R} (P : CxPairing K L M) {p q n : ℕ} (h : p + q = n)
    (x : K.H p) (y : L.H q) : M.H n :=
  M.cls (P.μ h (Quotient.out x).1 (Quotient.out y).1) (by
    rw [P.leib, show K.d p (Quotient.out x).1 = 0 from (Quotient.out x).2,
      show L.d q (Quotient.out y).1 = 0 from (Quotient.out y).2]; simp)

end CrystallineSemistableComparison
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Opposite

universe w w' t t' v u v' u'

namespace CrystallineSemistableComparison.CH

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

abbrev elF (E : C ⥤ Type t) (F : C ⥤ ModuleCat.{w} R) : E.Elements ⥤ ModuleCat.{w} R := CategoryOfElements.π E ⋙ F

def elMor {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R) : Mor (elF E F) (elF E' F) (RingHom.id R) where
  G := CategoryOfElements.map p
  τ _ := LinearMap.id
  nat _ _ := rfl

def elCoef (E : C ⥤ Type t) {F F' : C ⥤ ModuleCat.{w} R} (α : F ⟶ F') : Mor (elF E F) (elF E F') (RingHom.id R) :=
  Mor.ofNatTrans (Functor.whiskerLeft _ α)

def cech {E' E : C ⥤ Type t} (p : E' ⟶ E) (n : ℕ) : C ⥤ Type t where
  obj T := {y : Fin (n + 1) → E'.obj T // ∀ i j, p.app T (y i) = p.app T (y j)}
  map {T T'} φ := TypeCat.ofHom fun y => ⟨fun i => E'.map φ (y.1 i), fun i j => by
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, y.2 i j]⟩
  map_id T := by ext y i; simp
  map_comp φ ψ := by ext y i; simp

def cechMap {E' E : C ⥤ Type t} (p : E' ⟶ E) {m n : ℕ} (g : Fin (m + 1) → Fin (n + 1)) : cech p n ⟶ cech p m where
  app T := TypeCat.ofHom fun y => ⟨fun i => y.1 (g i), fun i j => y.2 _ _⟩

def cechAug {E' E : C ⥤ Type t} (p : E' ⟶ E) (n : ℕ) : cech p n ⟶ E where
  app T := TypeCat.ofHom fun y => p.app T (y.1 0)
  naturality T T' φ := by
    ext y
    exact NatTrans.naturality_apply p φ (y.1 0)

abbrev cechCos {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R) : CosCx.{max u v w t} R where
  K n := cx (elF (cech p n) F)
  δ n i := (elMor (cechMap p i.succAbove) F).hom
  rel n j i q x := by
    have e : (cechMap p (j.succAbove i).succAbove ≫ cechMap p (i.predAbove j).succAbove : cech p (n + 2) ⟶ cech p n) =
        cechMap p j.succAbove ≫ cechMap p i.succAbove := by
      ext T y
      exact Subtype.ext (funext fun k => congrArg y.1 (Fin.succAbove_succAbove_succAbove_predAbove j i k))
    exact congrArg (fun a => (elMor a F).pullC q x) e

def cechAugRow {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R) :
    DCx.AugRow (cx (elF E F)) (cechCos p F).dcx where
  ε q := (elMor (cechAug p 0) F).pullC q
  hε q x := by
    have e : (cechMap p (0 : Fin 2).succAbove ≫ cechAug p 0 : cech p 1 ⟶ E) = cechMap p (1 : Fin 2).succAbove ≫ cechAug p 0 := by
      ext T y
      exact y.2 _ _
    have e' : (elMor (cechMap p (0 : Fin 2).succAbove) F).pullC q ((elMor (cechAug p 0) F).pullC q x) =
        (elMor (cechMap p (1 : Fin 2).succAbove) F).pullC q ((elMor (cechAug p 0) F).pullC q x) :=
      congrArg (fun a => (elMor a F).pullC q x) e
    refine (Cos.d_apply ((cechCos p F).cos q) 0 _).trans ?_
    rw [Fin.sum_univ_two]
    change (-1 : ℤ) ^ 0 • (elMor (cechMap p (0 : Fin 2).succAbove) F).pullC q ((elMor (cechAug p 0) F).pullC q x) +
      (-1 : ℤ) ^ 1 • (elMor (cechMap p (1 : Fin 2).succAbove) F).pullC q ((elMor (cechAug p 0) F).pullC q x) = 0
    rw [e']; simp
  comm q x := (elMor (cechAug p 0) F).d_pullC q x

structure CxF (C : Type u) [Category.{v} C] (R : Type) [CommRing R] where
  F : ℕ → (C ⥤ ModuleCat.{w} R)
  δ : ∀ q, F q ⟶ F (q + 1)
  dd : ∀ q T x, ((δ (q + 1)).app T).hom (((δ q).app T).hom x) = 0

abbrev CxF.obj (K : CxF.{w} C R) (T : C) : Cx.{w} R where
  X q := (K.F q).obj T
  d q := ((K.δ q).app T).hom
  dd q := K.dd q T

abbrev CxF.dcx (K : CxF.{w} C R) : DCx.{max u v w} R where
  X p q := Cn (K.F q) p
  dh p q := d (K.F q) p
  dv p q := (Mor.ofNatTrans (K.δ q)).pullC p
  hh p q := d_d (K.F q) p
  vv p q x := funext fun s => K.dd q _ _
  hv p q x := (Mor.ofNatTrans (K.δ q)).d_pullC p x

section Rel

variable {I : Type t} [Category.{t'} I] (π : C ⥤ I)

abbrev relF (F : C ⥤ ModuleCat.{w} R) (i : I) : StructuredArrow i π ⥤ ModuleCat.{w} R := StructuredArrow.proj i π ⋙ F

def relRes (F : C ⥤ ModuleCat.{w} R) {i i' : I} (a : i ⟶ i') : Mor (relF π F i) (relF π F i') (RingHom.id R) where
  G := StructuredArrow.map a
  τ _ := LinearMap.id
  nat _ _ := rfl

def relAug (F : C ⥤ ModuleCat.{w} R) (i : I) : Mor F (relF π F i) (RingHom.id R) := Mor.restrict F _

def relMor {R' : Type} [CommRing R'] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'}
    {σ : R →+* R'} (m : Mor F F' σ) (i : I) : Mor (relF π F i) (relF (m.G ⋙ π) F' i) σ where
  G := StructuredArrow.pre i m.G π
  τ x := m.τ x.right
  nat φ x := m.nat φ.right x

end Rel

section Ind

variable {T : Type u'} [Category.{v'} T] (j : T ⥤ C)

abbrev pts (A : C) : T ⥤ Type v := j ⋙ coyoneda.obj (op A)

def ptsAug (F : C ⥤ ModuleCat.{w} R) (A : C) : F.obj A →ₗ[R] Cn (elF (pts j A) (j ⋙ F)) 0 :=
  aug (elF (pts j A) (j ⋙ F)) fun x => (F.map (show A ⟶ j.obj x.1 from x.2)).hom

structure Powers (A : C) where
  B : C
  f : A ⟶ B
  K : ℕ → C
  a : ∀ n, A ⟶ K n
  ι : ∀ n, Fin n → (B ⟶ K n)
  w : ∀ n i, f ≫ ι n i = a n
  δ : ∀ n, Fin (n + 1) → (K n ⟶ K (n + 1))
  aδ : ∀ n k, a n ≫ δ n k = a (n + 1)
  ιδ : ∀ n k i, ι n i ≫ δ n k = ι (n + 1) (k.succAbove i)
  rel : ∀ n (k : Fin (n + 2)) (i : Fin (n + 1)), δ n (i.predAbove k) ≫ δ (n + 1) (k.succAbove i) = δ n i ≫ δ (n + 1) k
  iso0 : IsIso (a 0)
  iso1 : IsIso (ι 1 0)
  univ : ∀ n (t : T) (x : A ⟶ j.obj t) (y : Fin n → (B ⟶ j.obj t)), (∀ i, f ≫ y i = x) →
    ∃! z : K n ⟶ j.obj t, a n ≫ z = x ∧ ∀ i, ι n i ≫ z = y i

def Powers.dK {A : C} (P : Powers j A) (F : C ⥤ ModuleCat.{w} R) (n : ℕ) : F.obj (P.K n) →ₗ[R] F.obj (P.K (n + 1)) :=
  ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • (F.map (P.δ n k)).hom

def Powers.Good {A : C} (P : Powers j A) (F : C ⥤ ModuleCat.{w} R) (I : Ideal R) : Prop :=
  (∀ (t : T) (x : A ⟶ j.obj t), ∃ y : P.B ⟶ j.obj t, P.f ≫ y = x) ∧
  (∀ s ∈ I, InjUpTo s (P.dK j F 0) ∧ ∀ n, ExactUpTo s (P.dK j F n) (P.dK j F (n + 1))) ∧
  ∃ (t₀ : T) (g : P.B ⟶ j.obj t₀), (∀ (t : T) (y : P.B ⟶ j.obj t), ∃! φ : t₀ ⟶ t, g ≫ j.map φ = y) ∧ Almost I (F.map g).hom

end Ind

end CrystallineSemistableComparison.CH

namespace CrystallineSemistableComparison

variable (R : Type) [CommRing R] (G : Type) [TopologicalSpace G] (M : Type w) [AddCommGroup M] [Module R M]

abbrev lcCos : Cos.{w} R where
  X n := LocallyConstant (Fin (n + 1) → G) M
  δ n i := LocallyConstant.comapₗ R ⟨fun x k => x (i.succAbove k), by fun_prop⟩
  rel n j i f := by
    ext x
    exact congrArg f (funext fun k => congrArg x (Fin.succAbove_succAbove_succAbove_predAbove j i k))

variable {R G M} [AddCommGroup G]

def eqv (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) (n : ℕ) : Submodule R ((lcCos R G M).cx.X n) where
  carrier := {f | ∀ g ∈ S, ∀ x : Fin (n + 1) → G, f (fun i => g + x i) = ρ (Multiplicative.ofAdd g) (f x)}
  add_mem' {a b} ha hb g hg x := by
    change a _ + b _ = ρ _ (a x + b x)
    rw [ha g hg, hb g hg, map_add (f := _)]
  zero_mem' g hg x := (map_zero _).symm
  smul_mem' c a ha g hg x := by
    change c • a _ = ρ _ (c • a x)
    rw [ha g hg, map_smul]

end CrystallineSemistableComparison
