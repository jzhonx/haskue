packages: .

package *
  optimization: 2
  library-vanilla: False

package haskue
  profiling: True
  profiling-detail: late-toplevel
  ghc-options:
    -ddump-simpl
    -dsuppress-all
    -ddump-to-file
