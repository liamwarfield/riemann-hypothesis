module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstTypePrimeLargeOfRecord

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfRootsBarEq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSeriesVectorMulOfParahoricBlockCharVector
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesEqOfOpposite
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

noncomputable section

namespace GlobalTheory.SerSys.Opp

open GlobalTheory.GLq.Opp



variable {g : ℕ} [Fact g.Prime] {k l n : ℕ}

theorem blk_eq (x : Gn g k) (y : Gn g l) : blk k l (k + l) x y = par finSumFinEquiv x 0 y := by
  have h : (fun i j : Fin (k + l) => if (i : ℕ) < k ∧ (j : ℕ) < k then entN (x : Mt g k) i j
      else if k ≤ (i : ℕ) ∧ k ≤ (j : ℕ) then entN (y : Mt g l) (i - k) (j - k) else 0) =
      ((par finSumFinEquiv x 0 y : Gn g (k + l)) : Mt g (k + l)) := by
    funext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rw [par_apply]
    rcases i with i | i <;> rcases j with j | j
    · simp [entN]
    · have := i.2
      simp [entN]
    · have := j.2
      simp [entN]
    · simp [entN]
  unfold blk
  rw [h, toG, dite_eq_left (Units.isUnit _), IsUnit.unit_of_val_units]

theorem eq_par (z : Gn g (k + l)) (h0 : InPar k (z : Mt g (k + l))) (h1 : tl k (z : Mt g (k + l)) = 1)
    (h2 : br k l (z : Mt g (k + l)) = 1) : ∃ B, z = par finSumFinEquiv 1 B 1 := by
  have e1 : ∀ (M : Mt g (k + l)) (i j : Fin k), tl k M i j = M (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inl j)) := by
    intro M i j
    have hi := i.2
    have hj := j.2
    rw [GLq.tl, entN, dite_eq_left ⟨by omega, by omega⟩]
    rfl
  have e2 : ∀ (M : Mt g (k + l)) (i j : Fin l), br k l M i j = M (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j)) := by
    intro M i j
    have hi := i.2
    have hj := j.2
    rw [br, entN, dite_eq_left ⟨by omega, by omega⟩]
    rfl
  refine ⟨Matrix.of fun i j => (z : Mt g (k + l)) (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j)), ?_⟩
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [par_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [← e1 (z : Mt g (k + l)) i j, h1]; simp
  · simp
  · rw [h0 _ _ (by simp) (by simp)]; simp
  · rw [← e2 (z : Mt g (k + l)) i j, h2]; simp

end GlobalTheory.SerSys.Opp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSeriesVectorMulOfParahoricBlockCharVector
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

noncomputable section

namespace GlobalTheory.SerSys.ParVec

open GlobalTheory.GLq.Opp GlobalTheory.SerSys.Opp MonoidAlgebra

private theorem inPar_tl_br_par_one {g : ℕ} [Fact g.Prime] {a b : ℕ} (B : Matrix (Fin a) (Fin b) (ZMod g)) :
    InPar a ((par finSumFinEquiv (1 : Gn g a) B 1 : Gn g (a + b)) : Mt g (a + b)) ∧
    tl a ((par finSumFinEquiv (1 : Gn g a) B 1 : Gn g (a + b)) : Mt g (a + b)) = 1 ∧
    br a b ((par finSumFinEquiv (1 : Gn g a) B 1 : Gn g (a + b)) : Mt g (a + b)) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hj hi
    obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
    rw [par_apply]
    rcases i' with i' | i'
    · have := i'.isLt
      simp at hi
      omega
    · rcases j' with j' | j'
      · simp
      · simp at hj
  · ext i j
    show entN _ i j = _
    rw [(entN_par (1 : Gn g a) B 1 i j).1 i.isLt j.isLt]
    simp [entN]
  · ext i j
    show entN _ (a + i) (a + j) = _
    rw [(entN_par (1 : Gn g a) B 1 i j).2.2.1]
    simp [entN]

theorem has_mul_of_isParVec : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : ℕ) (χ : (ZMod g)ˣ →* ℂˣ) (h f : (ZMod g)[X]) (v : V), n = a + b → CharIn S χ b h → IsParVec π a b χ v → actTop π a b (S.e a f) v ≠ 0 → Has S π (f * h) := by
  intro g _ S n V _ _ π a b χ h f v hn hχ hv hne
  subst hn
  obtain ⟨hvK, hrad, hy⟩ := hv
  let v' : fixK1 π := ⟨v, hvK⟩
  have hA : ∀ x : Gn g a, blk a b (a + b) x 1 = inA finSumFinEquiv x := fun x => blk_eq x 1
  have hB : ∀ y : Gn g b, blk a b (a + b) 1 y = inB finSumFinEquiv y := fun y => blk_eq 1 y
  let ρA : Representation ℂ (Gn g a) (fixK1 π) := (repK π).comp (inA (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)))
  let ρB : Representation ℂ (Gn g b) (fixK1 π) := (repK π).comp (inB (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)))
  let u : fixK1 π := ρA.asAlgebraHom (S.e a f) v'
  have hu : (u : V) = actTop π a b (S.e a f) v := by
    show ((ρA.asAlgebraHom (S.e a f) v' : fixK1 π) : V) = _
    rw [alg_apply, actTop, Submodule.coe_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hA]
    rfl
  have hv1 : ρB.asAlgebraHom (S.e b h) v' = v' := by
    rw [alg_apply]
    have hyv : ∀ y : Gn g b, ρB y v' = ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • v' := by
      intro y
      apply Subtype.ext
      show π (lift g (a + b) (inB finSumFinEquiv y)) v = _
      rw [← hB]
      exact hy y
    simp_rw [hyv, smul_smul, ← Finset.sum_smul]
    have hev := (Loc.charIn_iff S χ b h).1 hχ
    simp only [Loc.ev] at hev
    rw [hev, one_smul]
  have key : (repK π).asAlgebraHom (S.e (a + b) (f * h)) u = u := by
    apply S.mul a b (a + b) rfl f h (fixK1 π) (repK π) u
    · intro u0 h0 h1 h2
      obtain ⟨B, rfl⟩ := eq_par (k := a) (l := b) u0 h0 h1 h2
      show (repK π) _ (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'
      set_option synthInstance.maxHeartbeats 100000 in
        rw [alg_apply, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul]
      congr 1
      have hconj : par finSumFinEquiv 1 B 1 * inA finSumFinEquiv x =
          inA finSumFinEquiv x * par finSumFinEquiv 1 (((x⁻¹ : Gn g a) : Mt g a) * B) 1 := by
        show par finSumFinEquiv 1 B 1 * par finSumFinEquiv x 0 1 =
          par finSumFinEquiv x 0 1 * par finSumFinEquiv 1 (((x⁻¹ : Gn g a) : Mt g a) * B) 1
        rw [par_mul, par_mul]
        simp [← Matrix.mul_assoc]
      show (repK π) (par finSumFinEquiv 1 B 1) ((repK π) (inA finSumFinEquiv x) v') = (repK π) (inA finSumFinEquiv x) v'
      rw [← Module.End.mul_apply, ← map_mul, hconj, map_mul, Module.End.mul_apply]
      congr 1
      obtain ⟨r0, r1, r2⟩ := inPar_tl_br_par_one (g := g) (((x⁻¹ : Gn g a) : Mt g a) * B)
      exact Subtype.ext (hrad _ r0 r1 r2)
    · simp_rw [hA]
      have e2 : ∑ x, (S.e a f).coeff x • (repK π) (inA finSumFinEquiv x) u = ρA.asAlgebraHom (S.e a f) u := by
        rw [alg_apply]
        rfl
      rw [e2]
      show ρA.asAlgebraHom (S.e a f) (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'
      rw [← Module.End.mul_apply, ← map_mul, S.idem]
    · simp_rw [hB]
      have e3 : ∑ y, (S.e b h).coeff y • (repK π) (inB finSumFinEquiv y) u = ρB.asAlgebraHom (S.e b h) u := by
        rw [alg_apply]
        rfl
      rw [e3]
      show ρB.asAlgebraHom (S.e b h) (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'
      have hc : ρB.asAlgebraHom (S.e b h) (ρA.asAlgebraHom (S.e a f) v') =
          ρA.asAlgebraHom (S.e a f) (ρB.asAlgebraHom (S.e b h) v') := by
        simp only [ρA, ρB, comp_alg]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
          (commute_AB finSumFinEquiv (S.e a f) (S.e b h)).eq]
      rw [hc, hv1]
  refine ⟨(u : V), u.2, ?_⟩
  rw [← repK_alg, key, hu]
  exact hne

end GlobalTheory.SerSys.ParVec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSeriesVectorMulOfParahoricBlockCharVectorStatement
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSeriesVector_mul_of_parahoricBlockCharVector : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : ℕ) (χ : (ZMod g)ˣ →* ℂˣ) (h f : (ZMod g)[X]) (v : V), n = a + b → CharIn S χ b h → IsParVec π a b χ v → actTop π a b (S.e a f) v ≠ 0 → Has S π (f * h) := by
  first | exact @GlobalTheory.SerSys.ParVec.has_mul_of_isParVec | exact GlobalTheory.SerSys.ParVec.has_mul_of_isParVec | (intros; apply GlobalTheory.SerSys.ParVec.has_mul_of_isParVec <;> assumption)
end
end

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.SerLocal

variable (D : D7)

theorem inePol_zero (w : PlE D.host) (s) (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (D.naut.lpZero w) s = 1 := by
  rw [((D.naut.unr_iff_ine _).1 (D.naut.lpZero_unr w)).2 s hs, D.naut.lpDim_zero, pow_zero]

theorem inePol_foldr {ι : Type} {w : PlE D.host} (F : ι → D.naut.LP w) (l : List ι) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (l.foldr (fun x acc => D.naut.lpSum (F x) acc) (D.naut.lpZero _)) s =
      (l.map fun x => D.naut.inePol (F x) s).prod := by
  induction l with
  | nil => simpa using inePol_zero D w s hs
  | cons x l ih => rw [List.foldr_cons, D.naut.inePol_sum, ih, List.map_cons, List.prod_cons]

theorem inePol_speh (p : Part D.naut.CG) (w : PlE D.host) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (spehLoc D.nd D.naut p w) s = D.naut.inePol (D.naut.locG p.π w) s ^ p.d := by
  have e : spehLoc D.nd D.naut p w = (List.range p.d).foldr (fun (j : ℕ) acc =>
      D.naut.lpSum (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - j)) acc) (D.naut.lpZero w) := by
    simp only [spehLoc, bind_pure_comp, List.map_eq_map, List.foldr_map]
  rw [e, inePol_foldr D (fun k : ℕ => D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) _ s hs]
  simp [D.naut.inePol_tw _ _ s hs]

theorem inePol_iso (P : List (Part D.naut.CG)) (w : PlE D.host) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (isoLoc D.nd D.naut P w) s =
      (P.map fun p => D.naut.inePol (D.naut.locG p.π w) s ^ p.d).prod := by
  rw [isoLoc, inePol_foldr D (fun p => spehLoc D.nd D.naut p w) _ s hs]
  simp only [inePol_speh D _ w s hs]

theorem inePol_twist (hU : IneUnr D) (i : D.nd.Loc) (Sig : List (Part D.naut.CG)) (w : PlE D.host) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (isoLoc D.nd D.naut
      (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) w) s =
      D.naut.inePol (isoLoc D.nd D.naut Sig w) s * D.naut.inePol (D.naut.locG (D.naut.muC i) w) s ^ D.R.t := by
  rw [inePol_iso D _ w s hs, inePol_iso D _ w s hs, twistIso, List.map_map]
  have e : ∀ {a} (π : D.naut.CG a), D.naut.inePol (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) s =
      D.naut.inePol (D.naut.locG π w) s := fun π => by
    rw [D.naut.locG_tw]
    exact hU w _ _ (D.naut.locG_dim _ w) (D.naut.etaTinv_def w).1 s hs
  simp [Function.comp_def, e, muPart]

section Roots

variable {g : ℕ} [Fact g.Prime]

theorem eq_of_rootsBar_eq {f f' : (ZMod g)[X]} (hf : f.Monic) (hf' : f'.Monic)
    (h : Formalism.CyclotomicNorms.rootsBar f = Formalism.CyclotomicNorms.rootsBar f') : f = f' := by
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (RingHom.injective _)
  rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (f'.map _)).eq_prod_roots_of_monic (hf'.map _)]
  exact congrArg (fun m => (Multiset.map (fun x => X - C x) m).prod) h

theorem rootsBar_pow (c : ZMod g) (t : ℕ) :
    Formalism.CyclotomicNorms.rootsBar ((X - C c) ^ t) = t • {algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c} := by
  rw [Formalism.CyclotomicNorms.rootsBar, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, roots_pow, roots_X_sub_C]

theorem eq_of_teich (τ : Formalism.CyclotomicNorms.Fbar g →* ℂ) (hτ : Function.Injective τ) {f f' : (ZMod g)[X]} (hf : f.Monic)
    (hf' : f'.Monic) (c : ZMod g) (t : ℕ)
    (h : ((Formalism.CyclotomicNorms.rootsBar (f * (X - C c) ^ t)).map fun x => X - C (τ x)).prod =
      ((Formalism.CyclotomicNorms.rootsBar f').map fun x => X - C (τ x)).prod *
        (X - C (τ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c))) ^ t) : f = f' := by
  have h0 : f * (X - C c) ^ t ≠ 0 := (hf.mul ((monic_X_sub_C c).pow t)).ne_zero
  have hm : Formalism.CyclotomicNorms.rootsBar (f * (X - C c) ^ t) = Formalism.CyclotomicNorms.rootsBar f + Formalism.CyclotomicNorms.rootsBar ((X - C c) ^ t) := by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [Polynomial.map_mul, roots_mul]
    rw [← Polynomial.map_mul]
    exact Polynomial.map_ne_zero h0
  rw [hm, rootsBar_pow, Multiset.map_add (f := _), Multiset.prod_add, Multiset.map_nsmul, Multiset.prod_nsmul,
    Multiset.map_singleton, Multiset.prod_singleton] at h
  have h2 := mul_right_cancel₀ (pow_ne_zero t (X_sub_C_ne_zero _)) h
  have h3 := congrArg Polynomial.roots h2
  have e : ∀ m : Multiset (Formalism.CyclotomicNorms.Fbar g),
      ((m.map fun x => X - C (τ x)).prod).roots = m.map τ := fun m => by
    rw [← roots_multiset_prod_X_sub_C (m.map τ), Multiset.map_map]; rfl
  rw [e, e] at h3
  exact eq_of_rootsBar_eq hf hf' (Multiset.map_injective hτ h3)

end Roots

theorem serLoc : ∀ (D : D7) (S : ∀ k, @Sys (D.host.g k) ⟨D.host.g_prime k⟩),
    (∀ k f, D.ntypes.eSer k f = @Sys.e _ ⟨D.host.g_prime k⟩ (S k) D.R.r f) → IneUnr D → LocType D S →
    SerLoc D := by
  intro D S hS hU hL i σ' k v f F hF hne
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hex : ∃ P Sig, (∀ w, isoLoc D.nd D.naut Sig w = D.ntypes.locPar σ' w) ∧
      IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) ∧
      ∃ F' ∈ D.naut.typeV i P,
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v (D.ntypes.eSer k f)) F' ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hne
    rw [D.mtpar_tie i σ'] at hF
    have hle : (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc D.nd D.naut Sig w = D.ntypes.locPar σ' w) ∧
        IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv)},
        D.naut.typeV i P) ≤
        LinearMap.ker (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v (D.ntypes.eSer k f))) :=
      iSup₂_le fun P ⟨Sig, h1, h2⟩ F' hF' => hno P Sig h1 h2 F' hF'
    exact hle hF
  obtain ⟨P, Sig, hSig, hBC, F', hF', hne'⟩ := hex
  obtain ⟨π, χ, c, h1, h2, h3, h4⟩ := hL i P k v
  obtain ⟨u, hu, hu'⟩ := h1 F' hF' (D.ntypes.eSer k f)
    (Subalgebra.mem_center_iff.2 fun b => (D.ntypes.eSer_central k f b).symm) hne'
  rw [hS] at hu'
  have hmon : f.Monic := ((S k).label D.R.r f (fun h0 => hu' (by rw [h0]; simp [actTop]))).1
  have hHas := GlobalTheory.T.hasSeriesVector_mul_of_parahoricBlockCharVector _ (S k) _ _ π.ρ D.R.r D.R.t χ _ f u rfl h2 hu hu'
  have h5 := h4 _ hHas
  have hs := D.ntypes.tg_mem k v
  rw [← hBC.2.2.2.1 _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v), inePol_twist D hU i Sig _ _ hs, hSig, h3,
    D.ntypes.inertiaCharpoly_type k v _ (by
      rw [← D.ntypes.labPar_def, (D.ntypes.labPar_monic k σ' v).2, D.ntypes.locPar_dim]),
    ← D.ntypes.labPar_def] at h5
  exact eq_of_teich _ (GlobalTheory.TameLabels.teich_injective _ (D.ntypes.teichC_inj k)) hmon (D.ntypes.labPar_monic k σ' v).1 c _ h5.symm

end GlobalTheory.SerLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharInOfIsCharLab
noncomputable section

namespace GlobalTheory.SerSys.OfLabel

open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq.Opp MonoidAlgebra
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem blk_eq_par {a b : ℕ} (x : Gn g a) (y : Gn g b) : blk a b (a + b) x y = par finSumFinEquiv x 0 y := by
  refine Supp.ext_entN fun i j hi hj => ?_
  rw [ParInd.blk_val, entN, dite_eq_left ⟨hi, hj⟩, ParInd.dg]
  dsimp only
  by_cases h1 : i < a <;> by_cases h2 : j < a
  · rw [(Supp.entN_par _ _ _ i j).1 h1 h2, if_pos ⟨h1, h2⟩]
  · rw [(Supp.entN_par _ _ _ i j).2.2.2 rfl h1 (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [(Supp.entN_par _ _ _ i j).2.1 (by omega) h2, if_neg (by omega), if_neg (by omega)]
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h1)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h2)
    rw [(Supp.entN_par _ _ _ i j).2.2.1, if_neg (by omega), if_pos (by omega)]
    simp

def ofLabel (L : LabelDatum g) (h5 : 5 ≤ g) (hG : Green) : Sys g where
  e := eSerC L
  idem n := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).1
  central n := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).2.1
  orth n := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).2.2.1
  label n f h := by by_contra h'; exact h ((GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).2.2.2.1 f h')
  sum n := by obtain ⟨S, -, h⟩ := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).2.2.2.2; exact ⟨S, h⟩
  mul a b n hn f f' V _ _ ρ v h0 h1 h2 := by
    subst hn
    have hN : ρ.asAlgebraHom (eN g (finSumFinEquiv (m := a) (n := b))) v = v := eN_right _ ρ v fun B => by
      refine h0 _ (fun i j hj hi => ?_) ?_ ?_
      · rw [← ParInd.entN_self (par finSumFinEquiv (1 : Gn g a) B (1 : Gn g b)).val]
        exact (Supp.entN_par _ _ _ i j).2.1 hi hj
      · ext i j
        rw [tl, (Supp.entN_par _ _ _ i j).1 i.2 j.2, ParInd.entN_self]; rfl
      · ext i j
        rw [br, (Supp.entN_par _ _ _ i j).2.2.1, ParInd.entN_self]; rfl
    have hA : ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inA finSumFinEquiv) (eSerC L a f)) v = v := by
      rw [← comp_alg, Supp.alg_apply]; simp only [blk_eq_par] at h1; exact h1
    have hB : ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inB finSumFinEquiv) (eSerC L b f')) v = v := by
      rw [← comp_alg, Supp.alg_apply]; simp only [blk_eq_par] at h2; exact h2
    obtain ⟨S, -, hS⟩ := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG (a + b)).2.2.2.2
    have hz : ∀ F, F ≠ f * f' → ρ.asAlgebraHom (eSerC L (a + b) F) v = 0 := fun F hF => by
      have hv := ser_vanish' L h5 hG (finSumFinEquiv (m := a) (n := b)) F f f' hF
      have := congrArg (fun z => ρ.asAlgebraHom z v) hv
      simpa only [map_mul, Module.End.mul_apply, hN, hA, hB, map_zero, LinearMap.zero_apply] using this
    have e : v = ∑ F ∈ S, ρ.asAlgebraHom (eSerC L (a + b) F) v := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← LinearMap.sum_apply, ← map_sum, hS, map_one, Module.End.one_apply]
    by_cases hm : f * f' ∈ S
    · rw [Finset.sum_eq_single_of_mem _ hm fun F _ hF => hz F hF] at e; exact e.symm
    · rw [Finset.sum_eq_zero fun F hF => hz F (by rintro rfl; exact hm hF)] at e; rw [e]; simp

end GlobalTheory.SerSys.OfLabel
end
end

noncomputable section

namespace GlobalTheory.SerSys.Bridge

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.TypeLeaf
open scoped Classical

local instance factT (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

theorem trace_alg {G : Type} [Group G] [Fintype G] (τ : FDRep ℂ G) (a : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ τ (Representation.asAlgebraHom τ.ρ a) = tr a τ.character := by
  have e : Representation.asAlgebraHom τ.ρ a = ∑ x, a.coeff x • τ.ρ x :=
    LinearMap.ext fun w => by rw [alg_apply, LinearMap.sum_apply]; rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum, tr]
  exact Finset.sum_congr rfl fun x _ => map_smul _ _ _

section Finite

variable {g : ℕ} [Fact g.Prime]

theorem tr_eSerC_eq (L : LabelDatum g) {n : ℕ} {χ : Gn g n → ℂ} {f : (ZMod g)[X]} (hχ : IsIrr χ)
    (hf : HasLabel L χ f) : tr (eSerC L n f) χ = χ 1 ∧ χ 1 ≠ 0 := by
  have hfin := (GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)).1
  have hz : eSerC L n f * zOf χ = 1 * zOf χ := by
    rw [eSerC_eq_sum L n hfin, Finset.sum_mul, Finset.sum_eq_single_of_mem χ (by simp [hχ, hf]), one_mul]
    · simpa using (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ χ χ hχ hχ).1
    · intro b hb hne
      have hb' : IsIrr b := by simpa using (Finset.mem_filter.1 hb).1
      rw [(GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ b χ hb' hχ).1, if_neg hne]
  have h := congrArg (fun a : MonoidAlgebra ℂ (Gn g n) => a.coeff 1) hz
  simp only [(GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree _ _ χ).2.2] at h
  obtain ⟨d, hd, e⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree _ 1 χ).2.1 hχ
  have h1 : χ 1 ≠ 0 := e ▸ Nat.cast_ne_zero.2 hd.ne'
  rw [MonoidAlgebra.one_def, Opp.tr_single, one_mul] at h
  exact ⟨mul_left_cancel₀ (div_ne_zero h1 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) h, h1⟩

theorem hasLabel_of_isCuspOf (L : LabelDatum g) {d : ℕ} {P : (ZMod g)[X]} {χ : Gn g d → ℂ} (h : IsCuspOf L P χ) :
    HasLabel L χ P := by
  have hχ : IsIrr χ := h.2.1.2.1
  refine ⟨[(P, ⟨d, χ⟩)], fun p hp => by rw [List.mem_singleton.1 hp]; exact h, by simp [degL], by simp, ?_⟩
  have hc : IsClass χ := fun x y => by
    obtain ⟨V, -, hV⟩ := hχ
    rw [← hV, ← hV, FDRep.char_conj]
  have e : hcL ([(P, (⟨d, χ⟩ : Pc g))].map Prod.snd) d = χ := GLq.Model.hc_full χ hc
  rw [e, (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ χ χ hχ hχ).2.2, if_pos rfl]
  exact one_ne_zero

theorem labelsCusp (L : LabelDatum g) (h5 : 5 ≤ g) (hG : Green) :
    TameGen.LabelsCusp (OfLabel.ofLabel L h5 hG) L := fun d τ P hP h0 => by
  obtain ⟨h1, h2⟩ := tr_eSerC_eq L hP.2.1.2.1 (hasLabel_of_isCuspOf L hP)
  rw [← trace_alg] at h1
  exact h2 (h1.symm.trans ((congrArg _ h0).trans (map_zero _)))

end Finite

theorem five_le (D : D7) (k : Fin 2) : 5 ≤ D.host.g k := by
  have hc := D.ntypes.g_cond k
  have h4 : D.host.g k % 4 = 1 := by
    rw [← Nat.mod_mod_of_dvd (D.host.g k)
      (show 4 ∣ D.host.QS * D.host.q * D.host.d from
        ((((show (4 : ℕ) ∣ 2 ^ (D.R.e + 2) from ⟨2 ^ D.R.e, by ring⟩).trans D.host.tower_dvd).mul_right _).mul_right _)), hc]
  have := (D.host.g_prime k).two_le
  omega

end GlobalTheory.SerSys.Bridge
