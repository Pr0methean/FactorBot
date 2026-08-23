## Finishing the unfinished entries on FactorDB

This program in this repository helps the field of pure mathematics by factorizing large integers or establishing that 
they're prime, and publishing the results to factordb.com. You can run it on GitHub Actions and/or your own Linux x86-64
computer. It makes use of:

* `yamaquasi` SIQS for in-process numerical factorization up to 128 bits
* `yafu` for larger numerical factorizations
* Custom algebraic factorization
** Like-powers factorization (a^x +/- b^x)
** Last-digit check for factors of 2 and 5
** Sum-of-digits check for factors of 3
** Expression evaluation modulo small primes
** Algebraic factors listed in `frame_moreinfo.php`
** A known-divisibility graph to prevent repeatedly reporting false positives or already-known factors
* Server-side checks