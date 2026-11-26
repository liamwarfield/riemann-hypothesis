module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.LatticeComparisonCompatible
noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def embFr (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) :
    ((D.fm u).lat 0).V →ₛₗ[D.what₂.embLL] ((D.mem u).C.cls 0 → Fr D 0 (Nat.zero_le _) → ℂ) where
  toFun x := fun cl z => (D.fm u).emb 0 x cl (((T u).val0).eY.symm z)
  map_add' x y := by funext cl z; rw [map_add (f := _)]; rfl
  map_smul' a x := by funext cl z; rw [LinearMap.map_smulₛₗ]; rfl

structure CmpIn (D : D7) (X : Formalism.L2.Herm.Herm0 D) where
  embW : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.LL →+* (D.gat u w hg).Kf
  embW_int : ∀ u w hg (x : D.what₂.LL), (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔
    embW u w hg x ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf)
  B : GL (Fin D.R.k) D.host.E
  B_std : StdB D B
  fr_B : ∀ u w hg, FrRat X u w hg B

variable {X : Formalism.L2.Herm.Herm0 D}

def cmpRec (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ((D.fm u).lat 0).V → (D.gat u w hg).Fn :=
  cmpC ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg) (I.embW u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y

structure CmpHyp (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) : Prop where

  ex : ∀ u w hg, ValEx ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y

  uniq : ∀ u w hg, ValUniq ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y

  pos : ∀ u w hg v (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E),
    I.embW u w hg (tEL D (Gt.gat_pos u w hg ⟨v, s⟩) (if Even s.val then x else sigD D x)) =
      (D.gat u w hg).P.ι v (((D.gat u w hg).P.σ v ^ s.val) ((locAt X u w hg I.B).iw v x))

  chi : ∀ u w hg i (γ : ((D.gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U),
    (locAt X u w hg I.B).IsAway i γ κ.1 →
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (((D.gat u w hg).lev i).χ γ : (D.gat u w hg).O) * I.embW u w hg r = 1

  li : ∀ u w hg, LinearIndependent (D.gat u w hg).Kf (fun a => cmpRec T Gt I u w hg (((D.fm u).lat 0).b a))

  latM : ∀ u w hg, Submodule.span (D.gat u w hg).O
    (cmpRec T Gt I u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) = (D.gat u w hg).M

def latCmpC (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) (H : CmpHyp T Gt I) : LatCmp D where
  embW := I.embW
  embW_int := I.embW_int
  cmp := fun u w hg => (cmpL (e := I.embW u w hg) (H.ex u w hg) (H.uniq u w hg)).toAddMonoidHom
  cmp_smul := fun u w hg a x => (cmpL (e := I.embW u w hg) (H.ex u w hg) (H.uniq u w hg)).map_smulₛₗ a x
  cmp_li := H.li
  cmp_M := H.latM

def latticeComparisonCompatible (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) (H : CmpHyp T Gt I) :
    CmpTied D X T Gt (latCmpC T Gt I H) where
  B := I.B
  B_std := I.B_std
  fr_B := I.fr_B
  tie := fun u w hg => cmpC_tie (tEL D) (H.ex u w hg) (H.pos u w hg) (H.chi u w hg)

end Formalism.L2.G.Cmp

end
end

section -- merged from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsStab
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Cmp

attribute [local irreducible] Formalism.L2.G.repP

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}

def StabU (L : ColLevel R F E sp gp C A clsLat) (x : GA sp) : Type :=
  {γ : UJ (sp.cm.sig : E →+* E) sp.gram0 // x⁻¹ * ratA sp γ * x ∈ KA L}

def TrivStabU (L : ColLevel R F E sp gp C A clsLat) : Prop :=
  ∀ (x : GA sp) (γ : UJ (sp.cm.sig : E →+* E) sp.gram0), x⁻¹ * ratA sp γ * x ∈ KA L → γ = 1

def stabConj (x x' : GA sp) (h0 : UJ (sp.cm.sig : E →+* E) sp.gram0) (κ : GA sp) (hκ : κ ∈ KA L)
    (e : x' = ratA sp h0 * x * κ) : StabU L x ≃ StabU L x' where
  toFun γ := ⟨h0 * γ.1 * h0⁻¹, by
    have : x'⁻¹ * ratA sp (h0 * γ.1 * h0⁻¹) * x' = κ⁻¹ * (x⁻¹ * ratA sp γ.1 * x) * κ := by
      rw [e, map_mul, map_mul, map_inv]; group
    rw [this]
    exact (KA L).mul_mem ((KA L).mul_mem ((KA L).inv_mem hκ) γ.2) hκ⟩
  invFun γ := ⟨h0⁻¹ * γ.1 * h0, by
    have key : ∀ γ0 : UJ (sp.cm.sig : E →+* E) sp.gram0,
        x⁻¹ * ratA sp (h0⁻¹ * γ0 * h0) * x = κ * (x'⁻¹ * ratA sp γ0 * x') * κ⁻¹ := by
      intro γ0
      rw [e, map_mul, map_mul, map_inv]; group
    rw [key]
    exact (KA L).mul_mem ((KA L).mul_mem hκ γ.2) ((KA L).inv_mem hκ)⟩
  left_inv γ := Subtype.ext (by show h0⁻¹ * (h0 * γ.1 * h0⁻¹) * h0 = γ.1; group)
  right_inv γ := Subtype.ext (by show h0 * (h0⁻¹ * γ.1 * h0) * h0⁻¹ = γ.1; group)

def stabRec (c : C.cls 0) : C.stab 0 c ≃ StabU L (L.y c) :=
  Equiv.ofBijective (fun s => ⟨L.stabI c s, by
      have h := (L.stabI_range c (L.stabI c s : GL (Fin R.k) E) (L.stabI c s).2).1 ⟨s, rfl⟩
      exact (mem_map_conj L.U _ _).1 h⟩)
    ⟨fun a b hab => L.stabI_inj c (congrArg Subtype.val hab), fun γ => by
      obtain ⟨s, hs⟩ := (L.stabI_range c (γ.1 : GL (Fin R.k) E) γ.1.2).2 ((mem_map_conj L.U _ _).2 γ.2)
      exact ⟨s, Subtype.ext hs⟩⟩

def clsOf (L : ColLevel R F E sp gp C A clsLat) (c : ClassSet (HA sp) (KA L)) : C.cls 0 :=
  (Equiv.ofBijective _ L.y_bij).symm c

theorem clsOf_spec (c : ClassSet (HA sp) (KA L)) : Fib.mkC (HA sp) (KA L) (L.y (clsOf L c)) = c :=
  (Equiv.ofBijective _ L.y_bij).apply_symm_apply c

theorem clsOf_inj : Function.Injective (clsOf L) := (Equiv.ofBijective _ L.y_bij).symm.injective

theorem clsOf_surj : Function.Surjective (clsOf L) := (Equiv.ofBijective _ L.y_bij).symm.surjective

theorem card_stabU (x : GA sp) : Nat.card (StabU L x) = Nat.card (C.stab 0 (clsOf L (Fib.mkC (HA sp) (KA L) x))) := by
  obtain ⟨h, hh, κ, hκ, e⟩ := (Fib.mk_eq_iff (HA sp) (KA L) _ _).1 (clsOf_spec (L := L) (Fib.mkC (HA sp) (KA L) x))
  obtain ⟨h0, rfl⟩ := exists_ratA h hh
  exact (Nat.card_congr ((stabRec _).trans (stabConj _ x h0 κ hκ e))).symm

variable (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (e : ℕ) (hdet : IsUnit sp.gram0.det) (hH : HypAtP I)


include hH in
theorem fix_iff (i : compL L p) (g : Fin nV → GL (Fin (m + 1)) Qq) (γ : UJ (sp.cm.sig : E →+* E) sp.gram0) :
    (repP L p i * jQ I hdet hk g)⁻¹ * ratA sp γ * (repP L p i * jQ I hdet hk g) ∈ KA L ↔
      γ ∈ gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) (repP L p i).1 ∧
        (fun v => gMap W (prP I hk (ratA sp γ) v) (tupOf W g v)) = tupOf W g := by
  refine ((fibP I hdet hk hH).stab_iff (HA sp) (repP L p) (prP_repP I hk) i g (ratA sp γ) (prP_repP I hk)).trans
    (and_congr (mem_gamC_iff (repP L p i) γ).symm ?_)
  show g⁻¹ * (prP I hk (ratA sp γ) * g) ∈ _ ↔ _
  rw [← tupOf_eq_iff]
  have : tupOf W (prP I hk (ratA sp γ) * g) = fun v => gMap W (prP I hk (ratA sp γ) v) (tupOf W g v) := by
    funext v
    exact gMap_mul W _ _ _
  rw [this]


include hH in
def fixEquiv (i : compL L p) (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hy : y = (repP L p i).1)
    (g : Fin nV → GL (Fin (m + 1)) Qq) :
    {γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) y //
      (levC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y).smul γ (tupOf W g) = tupOf W g} ≃
      StabU L (repP L p i * jQ I hdet hk g) where
  toFun γ := ⟨γ.1.1, (fix_iff hk I hdet hH i g γ.1.1).2 ⟨hy ▸ γ.1.2, by
    have := γ.2
    rwa [level_action_lattice_eq] at this⟩⟩
  invFun γ := ⟨⟨γ.1, hy ▸ ((fix_iff hk I hdet hH i g γ.1).1 γ.2).1⟩, by
    rw [level_action_lattice_eq]
    exact ((fix_iff hk I hdet hH i g γ.1).1 γ.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Formalism.L2.G.Cmp
end
end
