(add-to-list 'load-path (substitute-in-file-name "${HOLBA_OPT_DIR}/hol_k13_holba/tools"))

(cua-mode)

(load "hol-mode.el")

; the following simplifies typing of unicode characters
; - note: unicode is against HolBA code rules
;(load "hol-unicode.el")

(defun my-sml-mode-hook ()
  "Local defaults for SML mode"
  (setq electric-indent-chars '()))

(add-hook 'sml-mode-hook 'my-sml-mode-hook)

