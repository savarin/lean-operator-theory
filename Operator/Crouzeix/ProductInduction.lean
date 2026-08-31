/-
# Induction along the Crouzeix product remainder

The recursive product-contour decomposition replaces a positive-degree
polynomial `p` by the explicit polynomial
`crouzeixProductRemainderPolynomial Omega p`, whose natural degree is strictly
smaller.  This file packages that decrease both as the induction principle
needed by a future sharp product-bound proof and as a well-founded iteration
that reaches a degree-zero terminal remainder.

## Main declarations

* `polynomial_induction_on_crouzeixProductRemainder` -- a degree-zero base and
  a remainder-to-parent step prove a property of every polynomial;
* `crouzeixProductTerminalRemainder` -- repeatedly take the product remainder
  until its degree is zero;
* `natDegree_crouzeixProductTerminalRemainder` -- termination has degree zero;
* `crouzeixProductTerminalRemainder_eq_terminalRemainder_of_pos` -- the
  positive-degree one-step equation.
-/
import Operator.Crouzeix.ProductContour

open Polynomial

/-- To prove a property of every polynomial, it suffices to prove the
degree-zero case and to pass from the Crouzeix product remainder back to a
positive-degree polynomial. -/
theorem polynomial_induction_on_crouzeixProductRemainder
    (Omega : SmoothJordanDomain) (P : Polynomial ℂ → Prop)
    (hzero : ∀ p, p.natDegree = 0 → P p)
    (hstep : ∀ p, 0 < p.natDegree →
      P (crouzeixProductRemainderPolynomial Omega p) → P p) :
    ∀ p, P p := by
  intro p
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
      by_cases hp : p.natDegree = 0
      · exact hzero p hp
      · apply hstep p (Nat.pos_of_ne_zero hp)
        apply ih (crouzeixProductRemainderPolynomial Omega p).natDegree
        · simpa only [← hn] using
            natDegree_crouzeixProductRemainderPolynomial_lt Omega p
              (Nat.pos_of_ne_zero hp)
        · rfl

/-- The terminal result of repeatedly taking the Crouzeix product remainder.
The recursion stops exactly when the current polynomial has degree zero. -/
noncomputable def crouzeixProductTerminalRemainder
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) : Polynomial ℂ :=
  if _hp : p.natDegree = 0 then p
  else crouzeixProductTerminalRemainder Omega
    (crouzeixProductRemainderPolynomial Omega p)
termination_by p.natDegree
decreasing_by
  exact natDegree_crouzeixProductRemainderPolynomial_lt Omega p
    (Nat.pos_of_ne_zero _hp)

/-- Iterated descent along the Crouzeix product remainder always terminates
at a degree-zero polynomial. -/
theorem natDegree_crouzeixProductTerminalRemainder
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    (crouzeixProductTerminalRemainder Omega p).natDegree = 0 := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
      rw [crouzeixProductTerminalRemainder]
      split_ifs with hp
      · exact hp
      · apply ih (crouzeixProductRemainderPolynomial Omega p).natDegree
        · simpa only [← hn] using
            natDegree_crouzeixProductRemainderPolynomial_lt Omega p
              (Nat.pos_of_ne_zero hp)
        · rfl

/-- A degree-zero polynomial is already its own terminal product remainder. -/
theorem crouzeixProductTerminalRemainder_eq_self_of_natDegree_eq_zero
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (hp : p.natDegree = 0) :
    crouzeixProductTerminalRemainder Omega p = p := by
  rw [crouzeixProductTerminalRemainder, dif_pos hp]

/-- On a positive-degree input, terminal descent first takes exactly one
Crouzeix product-remainder step. -/
theorem crouzeixProductTerminalRemainder_eq_terminalRemainder_of_pos
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (hp : 0 < p.natDegree) :
    crouzeixProductTerminalRemainder Omega p =
      crouzeixProductTerminalRemainder Omega
        (crouzeixProductRemainderPolynomial Omega p) := by
  rw [crouzeixProductTerminalRemainder, dif_neg (Nat.ne_of_gt hp)]
