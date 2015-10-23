(TeX-add-style-hook
 "coqpl16-stability"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("sigplanconf" "preprint" "nocopyrightspace")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("xcolor" "usenames")))
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (TeX-run-style-hooks
    "latex2e"
    "asymp_viz"
    "exp_viz"
    "sigplanconf"
    "sigplanconf10"
    "amsmath"
    "latexsym"
    "listings"
    "xcolor"
    "lstcoq"
    "tikz")
   (TeX-add-symbols
    '("greg" 1))
   (LaTeX-add-labels
    "sec:veridrone"
    "fig:system-visualization"
    "fig:stability"
    "sec:graphical"
    "fig:graphical-proof"
    "sec:lyapunov-functions")
   (LaTeX-add-bibitems
    "smith02")))

