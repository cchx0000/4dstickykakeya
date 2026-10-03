# Zero Hausdorff dimension of the finite-class exceptional time set

Status: elementary strengthening of the polynomial-minor input. It applies to the stationary full-grid, fixed finite-alphabet autonomous, and fixed finite-state models once their respective projection arguments are in place. It makes no packing-dimension claim.

At depth n and exterior degree j in {1,2,3}, each tested polynomial has leading coefficient at least B^(-jn). For a threshold B^(-Cn), factorization over C covers its real sublevel set by at most j intervals, each of length at most

    2 B^[-(C/j-1)n].

There are at most M^n B^[3n(j+1)] polynomial tests in the finite-alphabet case. For one stationary map take M=1. For a fixed finite-state model use M=1 and an additional fixed multiplicative state count.

Let E_C be the set of times lying in infinitely many of these depth-n sublevel events, for one or more j. The Hausdorff covering criterion gives, for C>3,

    dim_H E_C <= max_(j=1,2,3)
         [3(j+1)+log_B M]/(C/j-1).

Indeed the sum of s-powers of covering lengths converges whenever s exceeds that maximum. Define E_infinity as the intersection of E_C over sufficiently large positive integers C. The displayed upper bounds tend to zero, so dim_H E_infinity=0.

If t is outside E_infinity, some finite integer C has only finitely many exceptional depths. The corresponding eventual minor lower bound and a finer projected-cell scale imply the uniform prefix occupancy estimate. The stationary or uniform-family fine-prefix argument only needs SOME fixed finite exponential scale; it does not require the particular exponent 42. Therefore all the full-dimensional projection conclusions hold outside E_infinity.

The good-time set is still selected before all spatial projections and q values. For a fixed finite alphabet it is also selected before every autonomous sequence, and for a fixed finite-state transducer before every initial state.

Limsup sets of very small intervals can have positive packing dimension despite Hausdorff dimension zero. This argument does not justify taking products of exceptional sets as if they had zero packing dimension. The exterior-minor construction avoids that product step entirely.
