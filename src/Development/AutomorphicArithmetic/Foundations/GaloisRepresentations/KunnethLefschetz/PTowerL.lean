module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
public import Development.EtaleCohomology.EtaleTrace.LPdCut
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClasses

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProjTrans
private def UpperTheory.Reformulated.B.Qi50.proj {P : ℕ → Type 1} (t : (j : ℕ) → P (j + 1) → P j)
    {i j : ℕ} (h : i ≤ j) : P j → P i :=
  Nat.leRec (motive := fun j _ => P j → P i) id (fun k _ f => f ∘ t k) h

private theorem UpperTheory.Reformulated.B.Qi50.proj_self {P : ℕ → Type 1} (t : (j : ℕ) → P (j + 1) → P j)
    {i : ℕ} (h : i ≤ i) (a : P i) : UpperTheory.Reformulated.B.Qi50.proj t h a = a := by
  unfold UpperTheory.Reformulated.B.Qi50.proj
  rw [Nat.leRec_self]
  rfl

private theorem UpperTheory.Reformulated.B.Qi50.proj_succ {P : ℕ → Type 1} (t : (j : ℕ) → P (j + 1) → P j)
    {i j : ℕ} (h : i ≤ j) (h' : i ≤ j + 1) (a : P (j + 1)) :
    UpperTheory.Reformulated.B.Qi50.proj t h' a = UpperTheory.Reformulated.B.Qi50.proj t h (t j a) := by
  unfold UpperTheory.Reformulated.B.Qi50.proj
  rw [Nat.leRec_succ _ _ h]
  rfl

private theorem UpperTheory.Reformulated.B.Qi50.proj_trans {P : ℕ → Type 1} (t : (j : ℕ) → P (j + 1) → P j)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (a : P k) :
    UpperTheory.Reformulated.B.Qi50.proj t hij (UpperTheory.Reformulated.B.Qi50.proj t hjk a)
      = UpperTheory.Reformulated.B.Qi50.proj t (hij.trans hjk) a := by
  induction k, hjk using Nat.le_induction with
  | base => rw [UpperTheory.Reformulated.B.Qi50.proj_self]
  | succ k hk ih =>
    rw [UpperTheory.Reformulated.B.Qi50.proj_succ t hk, UpperTheory.Reformulated.B.Qi50.proj_succ t (hij.trans hk), ih]

theorem UpperTheory.Reformulated.B.Qi50.seq_sec :
    ∀ (P : ℕ → Type 1),
    (∀ (j : ℕ), Finite (P j)) →
      (∀ (j : ℕ), Nonempty (P j)) →
        ∀ (t : (j : ℕ) → P (j + (1 : ℕ)) → P j), ∃ (s : (j : ℕ) → P j), ∀ (j : ℕ), t j (s (j + (1 : ℕ))) = s j := by
  intro P hfin hne t
  obtain ⟨s, hs⟩ := exists_seq_forall_proj_of_forall_finite (α := P)
    (fun h => UpperTheory.Reformulated.B.Qi50.proj t h)
    (fun _ a => UpperTheory.Reformulated.B.Qi50.proj_self t _ a)
    (fun _ _ _ hij hjk a => UpperTheory.Reformulated.B.Qi50.proj_trans t hij hjk a)
    (fun _ _ => Set.toFinite _)
  refine ⟨s, fun j => ?_⟩
  have h := hs (Nat.le_succ j)
  rwa [UpperTheory.Reformulated.B.Qi50.proj_succ t le_rfl, UpperTheory.Reformulated.B.Qi50.proj_self] at h
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace LateralTheory.EtaleTrace.LRingPf

namespace UpperTheory.Gal.KunnethLefschetz

private theorem seq_sec (P : ℕ → Type 1) (hf : ∀ j, Finite (P j)) (hn : ∀ j, Nonempty (P j))
    (t : ∀ j, P (j + 1) → P j) : ∃ s : ∀ j, P j, ∀ j, t j (s (j + 1)) = s j :=
  _root_.UpperTheory.Reformulated.B.Qi50.seq_sec P hf hn t

private theorem cast_root {q : ℕ} {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (a : ℤ) (ha : a = 0) (h0 : (0 : ℤ) = 0) :
    Ht.cast h0 ha (rootClass a ζ) = rootClass 0 ζ := by
  subst ha; rfl

theorem towerL_holds : TowerL := by
  unfold TowerL Tower
  intro hI l _ k _ _ hl i
  have hp : ∀ j : ℕ, IsUnit (((l ^ j : ℕ)) : k) := fun j => by
    push_cast
    exact (IsUnit.mk0 _ hl).pow j
  have hinv : ∀ j : ℕ, Inv (l ^ j) (sch.obj (S k)) := fun j U hU => by
    obtain ⟨x⟩ := hU
    exact LPdCut.unit_of x (hp j)
  let P : ℕ → Type 1 := fun j => {w : Ht (l ^ j) (sch.obj (S k)) 0 i × Ht (l ^ j) (sch.obj (S k)) 0 (-i) //
    (cup (l ^ j) w.1 w.2).cast (add_zero 0) (add_neg_cancel i) = one (l ^ j) (sch.obj (S k))}
  have hf : ∀ j, Finite (P j) := fun j => by
    have := hI.e4 (l ^ j) k (hp j) (𝟙 (S k)) 0 i
    have := hI.e4 (l ^ j) k (hp j) (𝟙 (S k)) 0 (-i)
    infer_instance
  have hn : ∀ j, Nonempty (P j) := fun j => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ j) k) (by
      rw [Polynomial.degree_cyclotomic]
      exact_mod_cast (Nat.totient_pos.2 (NeZero.pos (l ^ j))).ne')
    let z0 : Prim (l ^ j) k := ⟨z, hp j, by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
      exact hz⟩
    let ζ : Prim (l ^ j) Γ(S k, ⊤) := z0.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    obtain ⟨h1, h2⟩ := (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes (l ^ j)).2 (S k) ζ i (-i)
    refine ⟨⟨(rootClass i ζ, rootClass (-i) ζ), ?_⟩⟩
    change Ht.cast _ _ (cup (l ^ j) (rootClass i ζ) (rootClass (-i) ζ)) = _
    rw [h1, LRingPf.cast_cast]
    exact (cast_root ζ _ _ _).trans h2
  let t : ∀ j, P (j + 1) → P j := fun j w =>
    ⟨(red (l ^ (j + 1)) (l ^ j) _ 0 i w.1.1, red (l ^ (j + 1)) (l ^ j) _ 0 (-i) w.1.2), by
      have hA := hI.a11 (l ^ (j + 1)) (l ^ j) (pow_dvd_pow l (Nat.le_succ j)) (sch.obj (S k))
      have h := congrArg (red (l ^ (j + 1)) (l ^ j) (sch.obj (S k)) 0 0) w.2
      rw [red_cast, hA.1, (hA.2.1 (hinv (j + 1))).1] at h
      exact h⟩
  obtain ⟨s, hs⟩ := seq_sec P hf hn t
  exact ⟨⟨fun j => (s j).1.1, fun j => congrArg (fun w : P j => w.1.1) (hs j)⟩,
    ⟨fun j => (s j).1.2, fun j => congrArg (fun w : P j => w.1.2) (hs j)⟩, fun j => (s j).2⟩

end UpperTheory.Gal.KunnethLefschetz
