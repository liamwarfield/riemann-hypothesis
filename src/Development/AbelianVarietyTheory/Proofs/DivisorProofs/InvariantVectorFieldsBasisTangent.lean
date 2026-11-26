module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeStructureSheafCohomologyNoetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechCmp

instance instSupNE (I : Type) : SemilatticeSup {S : Set I // S.Nonempty} :=
  Subtype.semilatticeSup fun _ _ h _ => h.mono Set.subset_union_left

abbrev NE (I : Type) : Type := {S : Set I // S.Nonempty}ᵒᵈ

variable {I : Type} {X : Scheme.{0}}

def NE.set (S : NE I) : Set I := (OrderDual.ofDual S).1

theorem NE.le_iff {S T : NE I} : S ≤ T ↔ T.set ⊆ S.set := Iff.rfl

theorem NE.set_inf (S T : NE I) : (S ⊓ T).set = S.set ∪ T.set := rfl

theorem NE.nonempty (S : NE I) : S.set.Nonempty := (OrderDual.ofDual S).2

def NE.single (i : I) : NE I := OrderDual.toDual ⟨{i}, Set.singleton_nonempty i⟩

def NE.pair (i j : I) : NE I := OrderDual.toDual ⟨{i, j}, Set.insert_nonempty i {j}⟩

theorem NE.set_single (i : I) : (NE.single i).set = {i} := rfl

theorem NE.set_pair (i j : I) : (NE.pair i j).set = {i, j} := rfl

theorem NE.pair_le_single_left (i j : I) : NE.pair i j ≤ NE.single i :=
  NE.le_iff.2 (Set.singleton_subset_iff.2 (Set.mem_insert i {j}))

theorem NE.pair_le_single_right (i j : I) : NE.pair i j ≤ NE.single j :=
  NE.le_iff.2 (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem i rfl))

def NE.pt (S : NE I) : I := S.nonempty.some

theorem NE.pt_mem (S : NE I) : S.pt ∈ S.set := S.nonempty.some_mem

def cap (U : I → X.Opens) (S : NE I) : X.Opens := ⨅ i ∈ S.set, U i

theorem cap_le (U : I → X.Opens) {S : NE I} {i : I} (h : i ∈ S.set) : cap U S ≤ U i := iInf₂_le i h

theorem cap_mono (U : I → X.Opens) : Monotone (cap U) := fun _ _ h => le_iInf₂ fun i hi => iInf₂_le i (h hi)

theorem cap_inf (U : I → X.Opens) (S T : NE I) : cap U (S ⊓ T) = cap U S ⊓ cap U T := by
  simp only [cap, NE.set_inf, iInf_union]

theorem cap_single (U : I → X.Opens) (i : I) : cap U (NE.single i) = U i := by
  simp [cap, NE.set_single]

theorem cap_pair (U : I → X.Opens) (i j : I) : cap U (NE.pair i j) = U i ⊓ U j := by
  rw [cap, NE.set_pair, iInf_insert, iInf_singleton]

theorem cap_iSup (U : I → X.Opens) (hU : ⨆ i, U i = ⊤) : ⨆ S, cap U S = ⊤ :=
  eq_top_iff.2 (hU ▸ iSup_le fun i => (cap_single U i).symm.le.trans (le_iSup (cap U) (NE.single i)))

theorem isAffineOpen_cap [Finite I] (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)) (S : NE I) :
    IsAffineOpen (cap U S) := by
  have key : ∀ s : Set I, s.Finite → s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i) := by
    intro s hs
    obtain ⟨t, rfl⟩ := hs.exists_finset_coe
    classical
    induction t using Finset.induction_on with
    | empty => intro h; simp at h
    | insert a t _ ih =>
      intro _
      rw [Finset.coe_insert]
      rcases (t : Set I).eq_empty_or_nonempty with ht | ht
      · rw [ht, iInf_insert, iInf_emptyset, inf_top_eq]; exact hU a
      · rw [iInf_insert]; exact hinf _ _ (hU a) (ih (Set.toFinite _) ht)
  exact key _ (Set.toFinite _) S.nonempty

def capAff [Finite I] (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)) (S : NE I) : X.affineOpens :=
  ⟨cap U S, isAffineOpen_cap U hU hinf S⟩

theorem capAff_mono [Finite I] (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)) :
    Monotone (capAff U hU hinf) := fun _ _ h => cap_mono U h

section Maps

variable {R : Type} [CommRing R] [Finite I] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))

abbrev capF : (NE I)ᵒᵖ ⥤ CommAlgCat.{0} R := (capAff_mono U hU hinf).functor.op ⋙ OAff s

def cv (T : (NE I)ᵒᵖ) : (capF s U hU hinf).obj T ≃+* Γ(X, cap U T.unop) := RingEquiv.refl _

theorem cv_mp {T T' : (NE I)ᵒᵖ} (a : T ⟶ T') (b : (capF s U hU hinf).obj T) :
    cv s U hU hinf T' (mp (capF s U hU hinf) a b) = rsT (cv s U hU hinf T b) (cap U T'.unop) :=
  (GlobalTheory.KS.rsT_of_le (O₀ := cap U T.unop) (cap_mono U (leOfHom a.unop)) b).symm

theorem cv_smul {T : (NE I)ᵒᵖ} (r : R) (b : (capF s U hU hinf).obj T) :
    cv s U hU hinf T (r • b) = constFn s (cap U T.unop) r * cv s U hU hinf T b :=
  Algebra.smul_def r b

def toPos (c : C1 U) : CatCoh.C1 (capF s U hU hinf) :=
  fun T T' _ => (cv s U hU hinf T').symm (rsT (c T.unop.pt T'.unop.pt) (cap U T'.unop))

def toCech (f : CatCoh.C1 (capF s U hU hinf)) : C1 U := fun i j =>
  rsT (cv s U hU hinf (op (NE.pair i j)) (f (op (NE.single i)) (op (NE.pair i j)) (homOfLE (NE.pair_le_single_left i j)).op))
      (U i ⊓ U j) -
    rsT (cv s U hU hinf (op (NE.pair i j)) (f (op (NE.single j)) (op (NE.pair i j)) (homOfLE (NE.pair_le_single_right i j)).op))
      (U i ⊓ U j)

theorem cv_toPos (c : C1 U) {T T' : (NE I)ᵒᵖ} (a : T ⟶ T') :
    cv s U hU hinf T' (toPos s U hU hinf c T T' a) = rsT (c T.unop.pt T'.unop.pt) (cap U T'.unop) :=
  RingEquiv.apply_symm_apply _ _

theorem toCech_apply (f : CatCoh.C1 (capF s U hU hinf)) (i j : I) :
    toCech s U hU hinf f i j =
      rsT (cv s U hU hinf (op (NE.pair i j)) (f (op (NE.single i)) (op (NE.pair i j)) (homOfLE (NE.pair_le_single_left i j)).op))
        (U i ⊓ U j) -
      rsT (cv s U hU hinf (op (NE.pair i j)) (f (op (NE.single j)) (op (NE.pair i j)) (homOfLE (NE.pair_le_single_right i j)).op))
        (U i ⊓ U j) := rfl

theorem restrict_capF_bijective (hcov : ⨆ i, U i = ⊤) :
    Function.Bijective (CoefMap.restrict (OAff s) (capAff_mono U hU hinf).functor.op).pull1 :=
  GlobalTheory.CoverO.restrict_bijective R X s (NE I) (capAff U hU hinf) (capAff_mono U hU hinf)
    (fun S T => cap_inf U S T) (cap_iSup U hcov)

end Maps

end GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

variable {I : Type} {X : Scheme.{0}} {R : Type} [CommRing R] [Finite I] (s : X ⟶ Sp R) (U : I → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))

theorem NE.pt_single (i : I) : (NE.single i).pt = i := Set.mem_singleton_iff.1 (NE.pt_mem (NE.single i))

theorem toPos_lc {n : ℕ} (cc : Fin n → R) (b : Fin n → C1 U) :
    toPos s U hU hinf (fun i j => ∑ a, constFn s (U i ⊓ U j) (cc a) * b a i j) =
      ∑ a, cc a • toPos s U hU hinf (b a) := by
  funext T T' φ
  have hle : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt :=
    le_inf (cap_le U ((NE.le_iff.1 (leOfHom φ.unop)) T.unop.pt_mem)) (cap_le U T'.unop.pt_mem)
  apply (cv s U hU hinf T').injective
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cv_toPos, Finset.sum_apply, Pi.smul_apply, map_sum, cv_smul, GlobalTheory.KS.rsT_sum, GlobalTheory.KS.rsT_mul,
    GlobalTheory.KS.rsT_constFn s hle]

theorem toCech_sub (f f' : CatCoh.C1 (capF s U hU hinf)) :
    toCech s U hU hinf (f - f') = toCech s U hU hinf f - toCech s U hU hinf f' := by
  funext i j
  simp only [toCech_apply, Pi.sub_apply, map_sub, GlobalTheory.KS.rsT_sub]
  abel

theorem toCech_lc {n : ℕ} (cc : Fin n → R) (f : Fin n → CatCoh.C1 (capF s U hU hinf)) :
    toCech s U hU hinf (∑ a, cc a • f a) =
      fun i j => ∑ a, constFn s (U i ⊓ U j) (cc a) * toCech s U hU hinf (f a) i j := by
  funext i j
  have hle : U i ⊓ U j ≤ cap U (NE.pair i j) := (cap_pair U i j).ge
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [toCech_apply, Finset.sum_apply, Pi.smul_apply, map_sum, cv_smul, GlobalTheory.KS.rsT_sum, GlobalTheory.KS.rsT_mul,
    GlobalTheory.KS.rsT_constFn s hle, mul_sub, Finset.sum_sub_distrib]
  refine congrArg₂ _ (Finset.sum_congr rfl fun a _ => ?_) (Finset.sum_congr rfl fun a _ => ?_) <;>
    rw [cv_smul, GlobalTheory.KS.rsT_mul, GlobalTheory.KS.rsT_constFn s hle]

end GlobalTheory.CechCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianCechH1BasisCocycles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCocyclePosetOneCochainToCechCochain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCocyclePosetOneCochainToCechCochain
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechCmp

variable {I : Type} [Finite I] {X : Scheme.{0}} {R : Type} [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))

theorem toCech_cocycle_read (f : GlobalTheory.CatCoh.C1 (capF s U hU hinf)) (hf : f ∈ Z1 (capF s U hU hinf))
    (x : I) (P K : NE I) (hxP : P ≤ NE.single x) (hPK : K ≤ P) (hxK : K ≤ NE.single x)
    (W : X.Opens) (hW : W ≤ cap U K) :
    rsT (cv s U hU hinf (op P) (f (op (NE.single x)) (op P) (homOfLE hxP).op)) W =
      rsT (cv s U hU hinf (op K) (f (op (NE.single x)) (op K) (homOfLE hxK).op)) W -
        rsT (cv s U hU hinf (op K) (f (op P) (op K) (homOfLE hPK).op)) W := by
  have e := Z1.comp ⟨f, hf⟩ (homOfLE hxP).op (homOfLE hPK).op
  have hc : (homOfLE hxP).op ≫ (homOfLE hPK).op = (homOfLE hxK).op := Subsingleton.elim _ _
  rw [hc] at e
  have e' := congrArg (fun b => rsT (cv s U hU hinf (op K) b) W) e
  simp only [map_add (f := _), GlobalTheory.KS.rsT_add] at e'
  rw [cv_mp s U hU hinf (homOfLE hPK).op] at e'
  rw [GlobalTheory.KS.rsT_rsT (O₁ := cap U (op K).unop) (cap_mono U hPK) hW] at e'
  rw [e']
  abel

theorem toCech_isCoc (f : GlobalTheory.CatCoh.C1 (capF s U hU hinf)) (hf : f ∈ Z1 (capF s U hU hinf)) :
    IsCoc U (toCech s U hU hinf f) := by
  intro i j k
  let K : NE I := OrderDual.toDual ⟨{i, j, k}, Set.insert_nonempty i {j, k}⟩
  have hi : i ∈ K.set := Set.mem_insert i _
  have hj : j ∈ K.set := Set.mem_insert_of_mem i (Set.mem_insert j _)
  have hk : k ∈ K.set := Set.mem_insert_of_mem i (Set.mem_insert_of_mem j rfl)
  have sgl : ∀ {a : I}, a ∈ K.set → K ≤ NE.single a := fun ha => NE.le_iff.2 (Set.singleton_subset_iff.2 ha)
  have pr : ∀ {a b : I}, a ∈ K.set → b ∈ K.set → K ≤ NE.pair a b :=
    fun ha hb => NE.le_iff.2 (Set.insert_subset ha (Set.singleton_subset_iff.2 hb))
  have hW : U i ⊓ U j ⊓ U k ≤ cap U K := le_iInf₂ fun x hx => by
    rcases hx with rfl | rfl | rfl
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right
  have hij : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j := inf_le_left
  have hjk : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hik : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  simp only [toCech_apply, GlobalTheory.KS.rsT_sub]
  rw [GlobalTheory.KS.rsT_rsT (cap_pair U i j).ge hij, GlobalTheory.KS.rsT_rsT (cap_pair U i j).ge hij,
    GlobalTheory.KS.rsT_rsT (cap_pair U j k).ge hjk, GlobalTheory.KS.rsT_rsT (cap_pair U j k).ge hjk,
    GlobalTheory.KS.rsT_rsT (cap_pair U i k).ge hik, GlobalTheory.KS.rsT_rsT (cap_pair U i k).ge hik]
  rw [toCech_cocycle_read s U hU hinf f hf i _ K _ (pr hi hj) (sgl hi) _ hW,
    toCech_cocycle_read s U hU hinf f hf j _ K _ (pr hi hj) (sgl hj) _ hW,
    toCech_cocycle_read s U hU hinf f hf j _ K _ (pr hj hk) (sgl hj) _ hW,
    toCech_cocycle_read s U hU hinf f hf k _ K _ (pr hj hk) (sgl hk) _ hW,
    toCech_cocycle_read s U hU hinf f hf i _ K _ (pr hi hk) (sgl hi) _ hW,
    toCech_cocycle_read s U hU hinf f hf k _ K _ (pr hi hk) (sgl hk) _ hW]
  abel

theorem isCoc_toCech : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ f : GlobalTheory.CatCoh.C1 (capF s U hU hinf), f ∈ Z1 (capF s U hU hinf) → IsCoc U (toCech s U hU hinf f) :=
  fun _ _ _ _ _ s U hU hinf f hf => toCech_isCoc s U hU hinf f hf

end GlobalTheory.CechCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCocyclePosetOneCochainToCechCochainStatement
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCechOneCocycle_posetOneCochainToCechCochain : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ f : GlobalTheory.CatCoh.C1 (capF s U hU hinf), f ∈ Z1 (capF s U hU hinf) → IsCoc U (toCech s U hU hinf f) := by
  first | exact @GlobalTheory.CechCmp.isCoc_toCech | exact GlobalTheory.CechCmp.isCoc_toCech | (intros; apply GlobalTheory.CechCmp.isCoc_toCech <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCochainToPosetCochainMemCocycles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCochainToPosetCochainMemCocycles
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem cechOneCochainToPosetCochain_mem_cocycles : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCoc U c → toPos s U hU hinf c ∈ Z1 (capF s U hU hinf) := by
  intro I _ X R _ s U hU hinf c hc T T' T'' φ ψ
  have h1 : T.unop.set ⊆ T'.unop.set := NE.le_iff.1 (leOfHom φ.unop)
  have h2 : T'.unop.set ⊆ T''.unop.set := NE.le_iff.1 (leOfHom ψ.unop)
  have ha : T.unop.pt ∈ T''.unop.set := h2 (h1 T.unop.pt_mem)
  have hb : T'.unop.pt ∈ T''.unop.set := h2 T'.unop.pt_mem
  have ha' : T.unop.pt ∈ T'.unop.set := h1 T.unop.pt_mem
  have hW : cap U T''.unop ≤ U T.unop.pt ⊓ U T'.unop.pt ⊓ U T''.unop.pt :=
    le_inf (le_inf (cap_le U ha) (cap_le U hb)) (cap_le U T''.unop.pt_mem)
  have hT' : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt := le_inf (cap_le U ha') (cap_le U T'.unop.pt_mem)
  have h23 : cap U T''.unop ≤ cap U T'.unop := cap_mono U (leOfHom ψ.unop)
  have key := congrArg (fun x => rsT x (cap U T''.unop)) (hc T.unop.pt T'.unop.pt T''.unop.pt)
  simp only [GlobalTheory.KS.rsT_add] at key
  have e1 : U T.unop.pt ⊓ U T'.unop.pt ⊓ U T''.unop.pt ≤ U T.unop.pt ⊓ U T'.unop.pt := inf_le_left
  have e2 : U T.unop.pt ⊓ U T'.unop.pt ⊓ U T''.unop.pt ≤ U T'.unop.pt ⊓ U T''.unop.pt :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have e3 : U T.unop.pt ⊓ U T'.unop.pt ⊓ U T''.unop.pt ≤ U T.unop.pt ⊓ U T''.unop.pt :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  rw [GlobalTheory.KS.rsT_rsT e1 hW, GlobalTheory.KS.rsT_rsT e2 hW, GlobalTheory.KS.rsT_rsT e3 hW] at key
  apply (cv s U hU hinf T'').injective
  rw [map_add (f := _), cv_toPos, cv_mp, cv_toPos, cv_toPos, GlobalTheory.KS.rsT_rsT hT' h23]
  exact key.symm

end GlobalTheory.CechCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCochainToPosetCochainMemCocyclesStatement
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toPos_mem_Z1_of_isCoc : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCoc U c → toPos s U hU hinf c ∈ Z1 (capF s U hU hinf) := by
  first | exact @GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles | exact GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles | (intros; apply GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetToCechCechToPosetCocycleEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetToCechCechToPosetCocycleEq
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

set_option autoImplicit false

namespace GlobalTheory.CechCmp

theorem toCech_toPos : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCoc U c → toCech s U hU hinf (toPos s U hU hinf c) = c := by
  intro I _ X R _ s U hU hinf c hc
  funext i j
  rw [toCech_apply, cv_toPos, cv_toPos]
  simp only [unop_op]
  rw [NE.pt_single, NE.pt_single]
  have hk : (NE.pair i j).pt = i ∨ (NE.pair i j).pt = j := by
    have := NE.pt_mem (NE.pair i j)
    rw [NE.set_pair] at this
    simpa using this
  have hi : i ∈ (NE.pair i j).set := by simp [NE.set_pair]
  have hj : j ∈ (NE.pair i j).set := by simp [NE.set_pair]
  have hcap : U i ⊓ U j ≤ cap U (NE.pair i j) := (cap_pair U i j).ge
  rw [GlobalTheory.KS.rsT_rsT (le_inf (cap_le U hi) (cap_le U (NE.pt_mem _))) hcap,
    GlobalTheory.KS.rsT_rsT (le_inf (cap_le U hj) (cap_le U (NE.pt_mem _))) hcap]
  generalize (NE.pair i j).pt = k at hk ⊢
  have hle : U i ⊓ U j ≤ U i ⊓ U j ⊓ U k := by
    refine le_inf le_rfl ?_
    rcases hk with h | h <;> subst h
    exacts [inf_le_left, inf_le_right]
  have h := congrArg (fun t => rsT t (U i ⊓ U j)) (hc i j k)
  simp only [GlobalTheory.KS.rsT_add] at h
  have e₁ : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k := inf_le_inf_right _ inf_le_right
  have e₂ : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k := inf_le_inf_right _ inf_le_left
  rw [GlobalTheory.KS.rsT_rsT inf_le_left hle, GlobalTheory.KS.rsT_self, GlobalTheory.KS.rsT_rsT e₁ hle, GlobalTheory.KS.rsT_rsT e₂ hle] at h
  rw [← h]
  abel

end GlobalTheory.CechCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetToCechCechToPosetCocycleEqStatement
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posetToCech_cechToPoset_cocycle_eq : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCoc U c → toCech s U hU hinf (toPos s U hU hinf c) = c := by
  first | exact @GlobalTheory.CechCmp.toCech_toPos | exact GlobalTheory.CechCmp.toCech_toPos | (intros; apply GlobalTheory.CechCmp.toCech_toPos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechToPosetPosetToCechSubCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechToPosetPosetToCechSubCoboundary
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechCmp

theorem cechToPoset_posetToCech_sub_coboundary : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R]
    (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)),
    ∀ f : GlobalTheory.CatCoh.C1 (capF s U hU hinf), f ∈ Z1 (capF s U hU hinf) →
      ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf (toCech s U hU hinf f) - f := by
  intro I _ X R _ s U hU hinf f hf
  have hm : ∀ {S T : NE I}, S.set ⊆ T.set → ((op S : (NE I)ᵒᵖ) ⟶ op T) :=
    fun h => (homOfLE (NE.le_iff.2 h)).op
  have hsg : ∀ T : NE I, (NE.single T.pt).set ⊆ T.set := fun T => by
    rw [NE.set_single]; exact Set.singleton_subset_iff.2 T.pt_mem
  have sub : ∀ {S T : (NE I)ᵒᵖ} (u v : S ⟶ T), u = v := fun u v =>
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  refine ⟨fun T => -f (op (NE.single T.unop.pt)) T (hm (hsg T.unop)), ?_⟩
  funext T T' φ
  have hTT : T.unop.set ⊆ T'.unop.set := NE.le_iff.1 (leOfHom φ.unop)
  have ha' : T.unop.pt ∈ T'.unop.set := hTT T.unop.pt_mem
  have hab : (NE.pair T.unop.pt T'.unop.pt).set ⊆ T'.unop.set := by
    rw [NE.set_pair]; exact Set.insert_subset ha' (Set.singleton_subset_iff.2 T'.unop.pt_mem)
  let χ : op (NE.pair T.unop.pt T'.unop.pt) ⟶ T' := hm hab
  let ψa : op (NE.single T.unop.pt) ⟶ op (NE.pair T.unop.pt T'.unop.pt) :=
    (homOfLE (NE.pair_le_single_left T.unop.pt T'.unop.pt)).op
  let ψb : op (NE.single T'.unop.pt) ⟶ op (NE.pair T.unop.pt T'.unop.pt) :=
    (homOfLE (NE.pair_le_single_right T.unop.pt T'.unop.pt)).op
  have c1 := Z1.comp ⟨f, hf⟩ (hm (hsg T.unop)) φ
  have c2 := Z1.comp ⟨f, hf⟩ ψa χ
  have c3 := Z1.comp ⟨f, hf⟩ ψb χ
  rw [sub (hm (hsg T.unop) ≫ φ) (ψa ≫ χ)] at c1
  have e3 : (hm (hsg T'.unop) : op (NE.single T'.unop.pt) ⟶ T') = ψb ≫ χ := sub _ _
  have key : toPos s U hU hinf (toCech s U hU hinf f) T T' φ =
      mp (capF s U hU hinf) χ (f _ _ ψa) - mp (capF s U hU hinf) χ (f _ _ ψb) := by
    apply (cv s U hU hinf T').injective
    have h1 : U T.unop.pt ⊓ U T'.unop.pt ≤ cap U (NE.pair T.unop.pt T'.unop.pt) :=
      (cap_pair U _ _).ge
    have h2 : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt :=
      le_inf (cap_le U ha') (cap_le U T'.unop.pt_mem)
    rw [cv_toPos, toCech_apply, map_sub, cv_mp, cv_mp, GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_rsT h1 h2,
      GlobalTheory.KS.rsT_rsT h1 h2]
  simp only [amitsur_d0_apply, Pi.sub_apply, map_neg, key]
  rw [e3]
  simp only at c1 c2 c3
  linear_combination -c3 + c2 - c1

end GlobalTheory.CechCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechToPosetPosetToCechSubCoboundaryStatement
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_d0_eq_toPos_toCech_sub_of_mem_Z1 : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ f : GlobalTheory.CatCoh.C1 (capF s U hU hinf), f ∈ Z1 (capF s U hU hinf) → ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf (toCech s U hU hinf f) - f := by
  first | exact @GlobalTheory.CechCmp.cechToPoset_posetToCech_sub_coboundary | exact GlobalTheory.CechCmp.cechToPoset_posetToCech_sub_coboundary | (intros; apply GlobalTheory.CechCmp.cechToPoset_posetToCech_sub_coboundary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCochainToPosetCochainCoboundaryExists
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCochainToPosetCochainCoboundaryExists
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem cechOneCochainToPosetCochain_coboundary_exists : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R)
    (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)),
    ∀ c : GlobalTheory.KS.C1 U, IsCob U c → ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf c := by
  intro I _ X R _ s U hU hinf c hc
  obtain ⟨b, hb⟩ := hc
  refine ⟨fun T => (cv s U hU hinf T).symm (rsT (b T.unop.pt) (cap U T.unop)), ?_⟩
  funext T T' φ
  apply (cv s U hU hinf T').injective
  have hTT' : cap U T'.unop ≤ cap U T.unop := cap_mono U (leOfHom φ.unop)
  have hp : cap U T.unop ≤ U T.unop.pt := cap_le U T.unop.pt_mem
  have hp' : cap U T'.unop ≤ U T'.unop.pt := cap_le U T'.unop.pt_mem
  have hle : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt := le_inf (hTT'.trans hp) hp'
  rw [amitsur_d0_apply, map_sub, cv_mp, cv_toPos, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hb,
    GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_rsT inf_le_right hle, GlobalTheory.KS.rsT_rsT inf_le_left hle, GlobalTheory.KS.rsT_rsT hp hTT']

end GlobalTheory.CechCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCochainToPosetCochainCoboundaryExistsStatement
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_d0_eq_toPos_of_isCob : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCob U c → ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf c := by
  first | exact @GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists | exact GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists | (intros; apply GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetOneCochainToCechCochainCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetOneCochainToCechCochainCoboundary
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

noncomputable section

namespace GlobalTheory.CechCmp

theorem posetOneCochainToCechCochain_coboundary : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ g : C0 (capF s U hU hinf), IsCob U (toCech s U hU hinf (d0 (capF s U hU hinf) g)) := by
  intro I _ X R _ s U hU hinf g
  refine ⟨fun i => rsT (cv s U hU hinf (op (NE.single i)) (g (op (NE.single i)))) (U i), fun i j => ?_⟩
  have hp : U i ⊓ U j ≤ cap U (NE.pair i j) := (cap_pair U i j).ge
  have key : ∀ k, k ∈ ({i, j} : Set I) →
      rsT (rsT (cv s U hU hinf (op (NE.single k)) (g (op (NE.single k)))) (cap U (NE.pair i j))) (U i ⊓ U j) =
        rsT (rsT (cv s U hU hinf (op (NE.single k)) (g (op (NE.single k)))) (U k)) (U i ⊓ U j) := by
    intro k hk
    have hk' : U i ⊓ U j ≤ U k := by
      rcases hk with rfl | hk
      · exact inf_le_left
      · rw [Set.mem_singleton_iff.1 hk]; exact inf_le_right
    rw [GlobalTheory.KS.rsT_rsT (cap_mono U (a := NE.pair i j) (b := NE.single k) (NE.le_iff.2 (by rw [NE.set_single, NE.set_pair]; exact Set.singleton_subset_iff.2 hk))) hp,
      GlobalTheory.KS.rsT_rsT (cap_single U k).ge hk']
  rw [toCech_apply, amitsur_d0_apply, amitsur_d0_apply, map_sub, map_sub, cv_mp, cv_mp, GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_sub]
  have e1 := key i (Set.mem_insert i {j})
  have e2 := key j (Set.mem_insert_of_mem i rfl)
  simp only [unop_op] at e1 e2 ⊢
  rw [e1, e2]
  abel

end GlobalTheory.CechCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetOneCochainToCechCochainCoboundaryStatement
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCob_toCech_d0 : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ g : C0 (capF s U hU hinf), IsCob U (toCech s U hU hinf (d0 (capF s U hU hinf) g)) := by
  first | exact @GlobalTheory.CechCmp.posetOneCochainToCechCochain_coboundary | exact GlobalTheory.CechCmp.posetOneCochainToCechCochain_coboundary | (intros; apply GlobalTheory.CechCmp.posetOneCochainToCechCochain_coboundary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianCechH1BasisCocycles
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechDR (HO1)

namespace GlobalTheory.CechFree

theorem cech_free : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (I : Type) [Finite I] (U : I → B.left.Opens), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ⨆ i, U i = ⊤ → (∀ i, IsAffineOpen (U i)) → ∃ b : Fin g → C1 U, (∀ a, IsCoc U (b a)) ∧ ∀ c : C1 U, IsCoc U c → ∃! cc : Fin g → A, IsCob U (fun i j => c i j - ∑ a, constFn B.hom _ (cc a) * b a i j) := by
  intro A _ _ _ B _ _ g I _ U hA hg hcov hU
  classical
  have hinf : ∀ V W : B.left.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W) := by
    haveI := hA.proper
    have : B.left.IsSeparated := ⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩
    exact fun V W hV hW => hV.inf hW
  obtain ⟨hfin, hproj, hrk⟩ := (GlobalTheory.T.abelianScheme_structureSheafCohomology_noetherian A B g hA hg).1
  haveI := hfin
  haveI := hproj
  haveI : Module.Free A (HO1 B.hom) := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank A (HO1 B.hom) = g := by
    rw [← hrk (IsLocalRing.closedPoint A), Module.rankAtStalk_eq_finrank_tensorProduct, Module.finrank_baseChange]
  let bH := Module.finBasisOfFinrankEq A (HO1 B.hom) hr
  let F := GlobalTheory.CechCmp.capF B.hom U hU hinf
  let e : HO1 B.hom ≃ₗ[A] CatCoh.H1 F :=
    LinearEquiv.ofBijective (CatCoh.CoefMap.restrict (GlobalTheory.CechDR.OAff B.hom)
      (GlobalTheory.CechCmp.capAff_mono U hU hinf).functor.op).pull1 (GlobalTheory.CechCmp.restrict_capF_bijective B.hom U hU hinf hcov)
  let bP := bH.map e
  choose f hf using fun a => CatCoh.H1.mk_surjective F (bP a)
  let b : Fin g → C1 U := fun a => GlobalTheory.CechCmp.toCech B.hom U hU hinf (f a).1
  have hb : ∀ a, IsCoc U (b a) := fun a => GlobalTheory.T.isCechOneCocycle_posetOneCochainToCechCochain I B.left A B.hom U hU hinf _ (f a).2
  have hbP : ∀ a, CatCoh.H1.mk F ⟨GlobalTheory.CechCmp.toPos B.hom U hU hinf (b a),
      GlobalTheory.T.toPos_mem_Z1_of_isCoc I B.left A B.hom U hU hinf _ (hb a)⟩ = bP a := by
    intro a
    rw [← hf a, CatCoh.H1.mk_eq_mk]
    exact GlobalTheory.T.exists_d0_eq_toPos_toCech_sub_of_mem_Z1 I B.left A B.hom U hU hinf _ (f a).2
  have hbb : ∀ a, GlobalTheory.CechCmp.toCech B.hom U hU hinf (GlobalTheory.CechCmp.toPos B.hom U hU hinf (b a)) = b a :=
    fun a => GlobalTheory.T.posetToCech_cechToPoset_cocycle_eq I B.left A B.hom U hU hinf _ (hb a)

  have hlc : ∀ (cc : Fin g → A) (hm : GlobalTheory.CechCmp.toPos B.hom U hU hinf
      (fun i j => ∑ a, constFn B.hom (U i ⊓ U j) (cc a) * b a i j) ∈ CatCoh.Z1 F),
      CatCoh.H1.mk F ⟨_, hm⟩ = ∑ a, cc a • bP a := by
    intro cc hm
    have : (⟨_, hm⟩ : CatCoh.Z1 F) = ∑ a, cc a • ⟨GlobalTheory.CechCmp.toPos B.hom U hU hinf (b a),
        GlobalTheory.T.toPos_mem_Z1_of_isCoc I B.left A B.hom U hU hinf _ (hb a)⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact GlobalTheory.CechCmp.toPos_lc B.hom U hU hinf cc b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, hbP]
  have hmem : ∀ cc : Fin g → A, GlobalTheory.CechCmp.toPos B.hom U hU hinf
      (fun i j => ∑ a, constFn B.hom (U i ⊓ U j) (cc a) * b a i j) ∈ CatCoh.Z1 F := by
    intro cc
    rw [GlobalTheory.CechCmp.toPos_lc]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (GlobalTheory.T.toPos_mem_Z1_of_isCoc I B.left A B.hom U hU hinf _ (hb a))
  refine ⟨b, hb, fun c hc => ?_⟩
  have hcm := GlobalTheory.T.toPos_mem_Z1_of_isCoc I B.left A B.hom U hU hinf c hc
  let x := CatCoh.H1.mk F ⟨_, hcm⟩
  have hex : IsCob U (fun i j => c i j - ∑ a, constFn B.hom (U i ⊓ U j) (bP.repr x a) * b a i j) := by
    let l : C1 U := fun i j => ∑ a, constFn B.hom (U i ⊓ U j) (bP.repr x a) * b a i j
    have hl : GlobalTheory.CechCmp.toCech B.hom U hU hinf (GlobalTheory.CechCmp.toPos B.hom U hU hinf l) = l := by
      rw [GlobalTheory.CechCmp.toPos_lc, GlobalTheory.CechCmp.toCech_lc]
      simp only [hbb, l]
    have h0 : CatCoh.H1.mk F ⟨_, hcm⟩ = CatCoh.H1.mk F ⟨_, hmem (bP.repr x)⟩ := by
      rw [hlc _ (hmem _)]
      exact (bP.sum_repr x).symm
    obtain ⟨g0, hg0⟩ := CatCoh.H1.mk_eq_mk.1 h0
    have key : (fun i j => c i j - l i j) = GlobalTheory.CechCmp.toCech B.hom U hU hinf (CatCoh.d0 F g0) := by
      rw [hg0, GlobalTheory.CechCmp.toCech_sub, GlobalTheory.T.posetToCech_cechToPoset_cocycle_eq I B.left A B.hom U hU hinf c hc, hl]
      rfl
    show IsCob U (fun i j => c i j - l i j)
    rw [key]
    exact GlobalTheory.T.isCob_toCech_d0 I B.left A B.hom U hU hinf g0
  refine ⟨bP.repr x, hex, fun cc hcc => ?_⟩
  have hcs : ∀ (O : B.left.Opens) (y z : A), constFn B.hom O (y - z) = constFn B.hom O y - constFn B.hom O z :=
    fun O y z => by simp only [constFn, map_sub]
  let δ : Fin g → A := fun a => bP.repr x a - cc a
  have hcob : IsCob U (fun i j => ∑ a, constFn B.hom (U i ⊓ U j) (δ a) * b a i j) := by
    obtain ⟨β₁, h₁⟩ := hcc
    obtain ⟨β₂, h₂⟩ := hex
    refine ⟨fun i => β₁ i - β₂ i, fun i j => ?_⟩
    have e₁ := h₁ i j
    have e₂ := h₂ i j
    simp only [δ, hcs, sub_mul, Finset.sum_sub_distrib, GlobalTheory.KS.rsT_sub] at e₁ e₂ ⊢
    linear_combination e₁ - e₂
  obtain ⟨g1, hg1⟩ := GlobalTheory.T.exists_d0_eq_toPos_of_isCob I B.left A B.hom U hU hinf _ hcob
  have hz : ∑ a, δ a • bP a = 0 := by
    rw [← hlc δ (hmem δ)]
    exact CatCoh.H1.mk_eq_zero.2 ⟨g1, hg1⟩
  have hδ := Fintype.linearIndependent_iff.1 bP.linearIndependent δ hz
  funext a
  exact (sub_eq_zero.1 (hδ a)).symm

end GlobalTheory.CechFree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianCechH1BasisCocyclesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_cech_h1_basis_cocycles : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (I : Type) [Finite I] (U : I → B.left.Opens), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ⨆ i, U i = ⊤ → (∀ i, IsAffineOpen (U i)) → ∃ b : Fin g → C1 U, (∀ a, IsCoc U (b a)) ∧ ∀ c : C1 U, IsCoc U c → ∃! cc : Fin g → A, IsCob U (fun i j => c i j - ∑ a, constFn B.hom _ (cc a) * b a i j) := by
  first | exact @GlobalTheory.CechFree.cech_free | exact GlobalTheory.CechFree.cech_free | (intros; apply GlobalTheory.CechFree.cech_free <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldsBasisTangent
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DlogBasis

section Coch

variable {A : Type} [CommRing A] {Y : Scheme.{0}} {I : Type} (q : Y ⟶ Sp A) (U : I → Y.Opens)

def kap (r : A) : C1 U := fun i j => constFn q (U i ⊓ U j) r

theorem rsT_le {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) : rsT s O = resG Y h s := by simp [rsT, h]

theorem resG_constFn' {O₀ O : Y.Opens} (h : O ≤ O₀) (r : A) : resG Y h (constFn q O₀ r) = constFn q O r := by
  simp only [constFn, resG]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
  first
    | (erw [Scheme.Hom.appLE_map])
    | (simp only [Scheme.Hom.appLE, Category.assoc, ← Functor.map_comp]; rfl)

theorem rsT_add' {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Y.Opens) : rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_neg' {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Y.Opens) : rsT (-s) O = -rsT s O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_mulc {O₀ O : Y.Opens} (h : O ≤ O₀) (r : A) (s : Γ(Y, O₀)) :
    rsT (constFn q O₀ r * s) O = constFn q O r * rsT s O := by
  rw [rsT_le h, rsT_le h, map_mul, resG_constFn' q h]

theorem kap_add (r s : A) : kap q U (r + s) = kap q U r + kap q U s := by funext i j; simp [kap, constFn]

theorem kap_mul (r s : A) : kap q U (r * s) = kap q U r * kap q U s := by funext i j; simp [kap, constFn]

theorem kap_zero : kap q U 0 = 0 := by funext i j; simp [kap, constFn]

variable {q U}

theorem isCob_zero : IsCob U 0 := ⟨0, fun i j => by simp only [Pi.zero_apply]; unfold rsT; split_ifs <;> simp⟩

theorem isCob_add {c d : C1 U} (hc : IsCob U c) (hd : IsCob U d) : IsCob U (c + d) := by
  obtain ⟨b, hb⟩ := hc
  obtain ⟨b', hb'⟩ := hd
  refine ⟨b + b', fun i j => ?_⟩
  simp only [Pi.add_apply, hb, hb', rsT_add']
  ring

theorem isCob_neg {c : C1 U} (hc : IsCob U c) : IsCob U (-c) := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨-b, fun i j => ?_⟩
  simp only [Pi.neg_apply, hb, rsT_neg']
  ring

theorem isCob_sub {c d : C1 U} (hc : IsCob U c) (hd : IsCob U d) : IsCob U (c - d) := by simpa [sub_eq_add_neg] using isCob_add hc (isCob_neg hd)

theorem isCob_kap_mul (r : A) {c : C1 U} (hc : IsCob U c) : IsCob U (kap q U r * c) := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨fun i => constFn q (U i) r * b i, fun i j => ?_⟩
  simp only [Pi.mul_apply, hb, kap, rsT_mulc q inf_le_right, rsT_mulc q inf_le_left]
  ring

theorem isCob_sum {n : ℕ} (c : Fin n → C1 U) (hc : ∀ a, IsCob U (c a)) : IsCob U (∑ a, c a) := Finset.sum_induction _ (fun x => IsCob U x) (fun _ _ => isCob_add) isCob_zero (fun a _ => hc a)

theorem isCob_congr {c d : C1 U} (h : c = d) (hc : IsCob U c) : IsCob U d := h ▸ hc

end Coch

section Coc

theorem pbT_id {X : Scheme.{0}} {O₀ : X.Opens} (s : Γ(X, O₀)) {O : X.Opens} (h : O ≤ O₀) :
    pbT (𝟙 X) s O = resG X h s := by
  unfold pbT
  rw [dite_eq_left (show O ≤ 𝟙 X ⁻¹ᵁ O₀ from h)]
  simp [resG, Scheme.Hom.appLE]
  (erw [Category.id_comp]) <;> rfl

theorem dlg_res {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) (i j : L.ι) {T : B.left.Opens} (hT : T ≤ L.U i ⊓ L.U j) :
    rsT (dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) T =
      δ T (res hT (L.g i j)).val * (res hT (L.g i j))⁻¹.val := by
  have e : ∀ s : Γ(B.left, L.U i ⊓ L.U j), pbT (𝟙 _) s (L.U i ⊓ L.U j) = s := fun s => by
    rw [pbT_id s le_rfl]; simp [resG]
  simp only [dlg, e]
  rw [rsT_le hT, map_mul, ← hδ.2.2 _ _ hT le_top]
  rfl

theorem s1 : ∀ (A : Type) [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left), L.IsLB → ∀ δ : Fld B.left, IsField ⊤ δ → IsCoc L.U (fun i j => dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) := by
  intro A _ B _ _ L hL δ hδ i j k
  have h1 : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j := inf_le_left
  have h2 : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have h3 : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  dsimp only
  rw [dlg_res B L δ hδ i j h1, dlg_res B L δ hδ j k h2, dlg_res B L δ hδ i k h3, ← hL.cocycle i j k]
  generalize res h1 (L.g i j) = a
  generalize res h2 (L.g j k) = b
  simp only [Units.val_mul, mul_inv_rev, hδ.2.1 _ le_top]
  linear_combination (-(δ _ ↑b * ↑b⁻¹)) * a.mul_inv + (-(δ _ ↑a * ↑a⁻¹)) * b.mul_inv

end Coc

theorem s2 : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (I : Type) [Finite I] (U : I → B.left.Opens), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ⨆ i, U i = ⊤ → (∀ i, IsAffineOpen (U i)) → ∃ b : Fin g → C1 U, (∀ a, IsCoc U (b a)) ∧ ∀ c : C1 U, IsCoc U c → ∃! cc : Fin g → A, IsCob U (fun i j => c i j - ∑ a, constFn B.hom _ (cc a) * b a i j) := GlobalTheory.T.abelian_cech_h1_basis_cocycles

theorem s3 : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∀ i, IsAffineOpen (L.U i)) → Finite L.ι → ∀ (v : Fin g → TanM (𝟙 (Sp A)) B) (dd : Fin g → Fld B.left), (∀ a, IsInv B (v a) (dd a)) → (∀ w : TanM (𝟙 (Sp A)) B, ∃! cf : Fin g → A, w = ∑ a, cf a • v a) → ∀ (c : Fin g → A) (N : ℕ) (t : Fin N → A) (z : Fin N → C1 L.U), (∀ k, t k ∈ maximalIdeal A) → IsCob L.U (fun i j => ∑ a, constFn B.hom _ (c a) * dlg B (𝟙 _) L (dd a) i j (L.U i ⊓ L.U j) - ∑ k, constFn B.hom _ (t k) * z k i j) → ∀ a, c a ∈ maximalIdeal A := GlobalTheory.T.logDerivatives_coboundary_coeffs_mem_maximalIdeal

section Main

variable {A : Type} [CommRing A] {Y : Scheme.{0}} {I : Type} (q : Y ⟶ Sp A) (U : I → Y.Opens)

def kapH : A →+* C1 U where
  toFun := kap q U
  map_one' := by funext i j; simp [kap, constFn]
  map_mul' := kap_mul q U
  map_zero' := kap_zero q U
  map_add' := kap_add q U

theorem kapH_apply (r : A) (i j : I) : kapH q U r i j = constFn q (U i ⊓ U j) r := rfl

theorem lin_eq {n : ℕ} (c : C1 U) (cc : Fin n → A) (b : Fin n → C1 U) :
    (fun i j => c i j - ∑ a, constFn q (U i ⊓ U j) (cc a) * b a i j) = c - ∑ a, kapH q U (cc a) * b a := by funext i j; simp [Finset.sum_apply, kapH_apply]

theorem cechCochain_sum_sub_sum_constFn_eq_ringHom {n N : ℕ} (c : Fin n → A) (φ : Fin n → C1 U) (t : Fin N → A) (z : Fin N → C1 U) :
    (fun i j => ∑ a, constFn q (U i ⊓ U j) (c a) * φ a i j - ∑ k, constFn q (U i ⊓ U j) (t k) * z k i j) =
      ∑ a, kapH q U (c a) * φ a - ∑ k, kapH q U (t k) * z k := by funext i j; simp [Finset.sum_apply, kapH_apply]

theorem comb_eq {n : ℕ} (φ b : Fin n → C1 U) (P : Matrix (Fin n) (Fin n) A) (c : Fin n → A) :
    ∑ a, kapH q U (c a) * φ a - ∑ k, kapH q U ((c ᵥ* P) k) * b k =
      ∑ a, kapH q U (c a) * (φ a - ∑ k, kapH q U (P a k) * b k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, Finset.sum_mul, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => mul_assoc _ _ _

end Main


open Classical in
theorem main : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∀ i, IsAffineOpen (L.U i)) → Finite L.ι → ∀ (v : Fin g → TanM (𝟙 (Sp A)) B) (dd : Fin g → Fld B.left), (∀ a, IsInv B (v a) (dd a)) → (∀ w : TanM (𝟙 (Sp A)) B, ∃! cf : Fin g → A, w = ∑ a, cf a • v a) → ∀ c : C1 L.U, IsCoc L.U c → ∃! cc : Fin g → A, IsCob L.U (fun i j => c i j - ∑ a, constFn B.hom _ (cc a) * dlg B (𝟙 _) L (dd a) i j (L.U i ⊓ L.U j)) := by
  intro A _ _ _ B _ _ g L hab hsm hL hamp hK haff hfin v dd hinv hbasis c hc
  haveI := hfin
  let φ : Fin g → C1 L.U := fun a i j => dlg B (𝟙 _) L (dd a) i j (L.U i ⊓ L.U j)
  obtain ⟨b, -, hb⟩ := s2 A B g L.ι L.U hab hsm hL.cover haff
  have hφ : ∀ a, IsCoc L.U (φ a) := fun a => s1 A B L hL (dd a) (hinv a).1
  choose P hP using fun a => (hb (φ a) (hφ a)).exists
  have key : ∀ y : Fin g → A, IsCob L.U
      (∑ a, kapH B.hom L.U (y a) * φ a - ∑ k, kapH B.hom L.U ((y ᵥ* Matrix.of P) k) * b k) := by
    intro y
    rw [comb_eq]
    exact isCob_sum _ fun a => isCob_kap_mul _ (isCob_congr (lin_eq B.hom L.U (φ a) (P a) b) (hP a))
  have hmem : ∀ y : Fin g → A, (∀ k, (y ᵥ* Matrix.of P) k ∈ maximalIdeal A) → ∀ a, y a ∈ maximalIdeal A := by
    intro y hy
    exact s3 A B g L hab hsm hL hamp hK haff hfin v dd hinv hbasis y g (y ᵥ* Matrix.of P) b hy
      (isCob_congr (cechCochain_sum_sub_sum_constFn_eq_ringHom B.hom L.U y φ (y ᵥ* Matrix.of P) b).symm (key y))
  have hdet : IsUnit (Matrix.of P).det := by
    by_contra hnd
    have h0 : IsLocalRing.residue A (Matrix.of P).det = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnd))
    rw [RingHom.map_det] at h0
    obtain ⟨ybar, hy0, hyP⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    obtain ⟨y, rfl⟩ : ∃ y : Fin g → A, (fun a => IsLocalRing.residue A (y a)) = ybar :=
      ⟨fun a => (IsLocalRing.residue_surjective (ybar a)).choose,
        funext fun a => (IsLocalRing.residue_surjective (ybar a)).choose_spec⟩
    apply hy0
    funext a
    have hk : ∀ k, (y ᵥ* Matrix.of P) k ∈ maximalIdeal A := by
      intro k
      rw [← IsLocalRing.residue_eq_zero_iff]
      have := congrFun hyP k
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [Matrix.vecMul, dotProduct, map_sum, RingHom.mapMatrix_apply, Matrix.map_apply] using this
    simpa [IsLocalRing.residue_eq_zero_iff] using hmem y hk a
  obtain ⟨e, he, heu⟩ := hb c hc
  refine ⟨e ᵥ* (Matrix.of P)⁻¹, ?_, ?_⟩
  · have h1 := key (e ᵥ* (Matrix.of P)⁻¹)
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one] at h1
    have h2 := isCob_sub (isCob_congr (lin_eq B.hom L.U c e b) he) h1
    exact isCob_congr (lin_eq B.hom L.U c _ φ).symm (isCob_congr (sub_sub_sub_cancel_right _ _ _) h2)
  · intro cc' hcc'
    have h3 := isCob_add (isCob_congr (lin_eq B.hom L.U c cc' φ) hcc') (key cc')
    have h4 : IsCob L.U (fun i j => c i j - ∑ a, constFn B.hom (L.U i ⊓ L.U j) ((cc' ᵥ* Matrix.of P) a) * b a i j) :=
      isCob_congr (lin_eq B.hom L.U c _ b).symm (isCob_congr (sub_add_sub_cancel _ _ _) h3)
    have h5 := heu _ h4
    rw [← h5, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]

end GlobalTheory.DlogBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldsBasisTangentStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_vector_fields_basis_tangent : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∀ i, IsAffineOpen (L.U i)) → Finite L.ι → ∀ (v : Fin g → TanM (𝟙 (Sp A)) B) (dd : Fin g → Fld B.left), (∀ a, IsInv B (v a) (dd a)) → (∀ w : TanM (𝟙 (Sp A)) B, ∃! cf : Fin g → A, w = ∑ a, cf a • v a) → ∀ c : C1 L.U, IsCoc L.U c → ∃! cc : Fin g → A, IsCob L.U (fun i j => c i j - ∑ a, constFn B.hom _ (cc a) * dlg B (𝟙 _) L (dd a) i j (L.U i ⊓ L.U j)) := by
  first | exact @GlobalTheory.DlogBasis.main | exact GlobalTheory.DlogBasis.main | (intros; apply GlobalTheory.DlogBasis.main <;> assumption)
end
