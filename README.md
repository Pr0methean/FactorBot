## Currently broken

This tool was broken by a change to factordb.com on 2026-10-06, and I don't know if I'll have time to fix it any time
soon due to my work on [zip](https://github.com/zip-rs/zip2) and my ongoing job hunt. HTML pages no longer follow the
previous template, and there seems to be no backward-compatibility option.
I'll gladly review a pull request if someone else wants to update this tool.

## Finishing the unfinished entries on FactorDB

This program in this repository helps the field of pure mathematics by factorizing large integers or establishing that 
they're prime, and publishing the results to factordb.com. You can run it on GitHub Actions and/or your own Linux x86-64
computer. It makes use of:

* `yamaquasi` SIQS for in-process numerical factorization up to 128 bits
* `yafu` for larger numerical factorizations
* Custom algebraic factorization
  * Like-powers factorization (a^x +/- b^x)
  * Last-digit check for factors of 2 and 5
  * Sum-of-digits check for factors of 3
  * Factors 2 and 3 of P-1 and P+1 for probable primes P, since probable primality implies P must be 1 or 5 mod 6
  * Expression evaluation modulo small primes
  * Algebraic factors listed in `frame_moreinfo.php`
  * A known-divisibility graph to prevent repeatedly reporting false positives or already-known factors
* Server-side checks
