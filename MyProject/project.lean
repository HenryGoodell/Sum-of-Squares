import Mathlib
import Lean.Parser.Term
open Polynomial
open Complex
open ComplexConjugate
open Finset

set_option linter.unusedVariables false

theorem SOS1 {s : Finset ℝ[X]}{x : ℝ}:
(s.sum (fun g => g*g)).eval x ≥ 0 := by
have h1 : (s.sum (fun g => g*g)).eval x=(s.sum (fun g => (g*g).eval x))
exact eval_finset_sum s (fun i ↦ i * i) x
rw [h1]
apply Finset.sum_nonneg
simp
intro i hi
exact mul_self_nonneg (eval x i)

noncomputable def inductiveRootSetList {f : ℂ[X]}(g1: ∃(n : ℕ), f.degree = 2*n)(g2: ∀(a: ℕ), (f.coeff a).im=0) : Finset ℂ :=
  let rootset := f.roots.toFinset
  let rec build (remaining : Finset ℂ) (acc : Finset ℂ) : Finset ℂ :=
    match remaining.toList.head? with
    | none => acc
    | some z =>
      let newRemaining := remaining.erase z
      let newRemaining := newRemaining.erase (conj z)
      build newRemaining (acc ∪ {z})
    termination_by remaining.card
    decreasing_by
    calc
      _ ≤ ((remaining.erase z)).card := by
        exact card_erase_le
      _ < _ := by
        have h1: z ∈ remaining := by
          sorry
        exact card_erase_lt_of_mem h1
  build rootset ∅

theorem SOS2 {f : ℂ[X]}{x : ℂ}(g1: ∃(n : ℕ), f.degree = 2*n)(g2: ∀(a: ℕ), (f.coeff a).im=0)(g3:0 < f.degree ):
(∀(z : ℂ), z.im=0 → (f.eval z).re ≥ 0) → ∃(s : Finset ℂ[X]),(f = s.sum (fun g => g*g) ∧ (∀ (p : ℂ[X]), p ∈ s → ∀ (n : ℕ), (p.coeff n).im = 0)) := by
have h3: map conj f = f := by
      ext a
      simp
      apply conj_eq_iff_real.mpr
      use (f.coeff a).re
      exact ext rfl (g2 a)

have h1 : f.eval x =0 ↔ f.eval (conj x) =0 := by
    have mp: ∀ x, eval x f = 0 → eval ((starRingEnd ℂ) x) f = 0 := by
      intro x h2
      calc
        eval ((starRingEnd ℂ) x) f = eval ((starRingEnd ℂ) x) (map conj f) := by
          rw[h3]
        _ = starRingEnd ℂ (eval x f) := by
          rw[← eval₂_at_apply (starRingEnd ℂ) x]
          apply eval_map
        _ = 0 := by
          rw[h2]
          simp
    constructor
    exact mp x
    intro h2
    have := mp ((starRingEnd ℂ) x) h2
    simp at this
    exact this
have h4: (Polynomial.monomial 0 (f.coeff (f.natDegree)))*((inductiveRootSetList g1 g2).prod fun z => (Polynomial.monomial 1 1 - Polynomial.monomial 0 z)*(Polynomial.monomial 1 1 - Polynomial.monomial 0 (conj z))) = f := by
    simp
    refine Eq.symm (Polynomial.funext ?ext)
    intro a
    have h5: eval a f =0 ∨ ¬(eval a f =0) := by
      exact Classical.em (eval a f =0)
    cases h5
    have h6: eval a f =0
    trivial
    rw[h6]
    have h7: a ∈ f.roots.toFinset
    refine Multiset.mem_toFinset.mpr ?h7.a
    simp
    apply And.intro
    refine zero_le_degree_iff.mp ?h7.a.left.a
    rotate_left
    exact h6
    rotate_right
    exact le_of_lt g3
    have h8: eval a ((Polynomial.monomial 0 (f.coeff (f.natDegree)))*((inductiveRootSetList g1 g2).prod (fun z => (Polynomial.monomial 1 1 - Polynomial.monomial 0 z)*(Polynomial.monomial 1 1 - Polynomial.monomial 0 (conj z))))) = 0
    refine IsRoot.eq_zero ?h7.h
    have h9: a ∈ (inductiveRootSetList g1 g2) ∨ conj a ∈ (inductiveRootSetList g1 g2)
    apply or_iff_not_imp_left.mpr
    sorry
    simp
    refine Or.intro_right (f = 0) ?h7.h.h
    have h10: eval a (((monomial 1) 1 - C a)*((monomial 1) 1 - C ((starRingEnd ℂ) a))) = 0
    simp
    have h11: (((monomial 1) 1 - C a)*((monomial 1) 1 - C ((starRingEnd ℂ) a)))∣((inductiveRootSetList g1 g2).prod (fun z => (Polynomial.monomial 1 1 - Polynomial.monomial 0 z)*(Polynomial.monomial 1 1 - Polynomial.monomial 0 (conj z))))
    simp
    sorry
    exact eval_eq_zero_of_dvd_of_eval_eq_zero h11 h10
    exact id (Eq.symm h8)
    sorry
have h12:
  (fun y => eval y ((Polynomial.monomial 0 (f.coeff f.natDegree)) *
            ((inductiveRootSetList g1 g2).prod (fun z =>
              ((Polynomial.monomial 1 1 - Polynomial.monomial 0 z) *
              (Polynomial.monomial 1 1 - Polynomial.monomial 0 (conj z))))))) =
  (fun y =>(ofReal (((Complex.abs (eval y ((C (ofReal ((f.coeff f.natDegree).re.sqrt)))*((f.roots.toFinset).prod (fun z => (monomial 1 1 - C z)))))))^2)))
simp
sorry
rw[h4] at h12
--at this point I have to build polynomials with coefficients equal to the real and imaginary parts of the polynomial I squared in h12, there is probably a good way to do this with local definitions.
