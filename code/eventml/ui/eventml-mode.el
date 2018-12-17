;; eventml.el
;;
;; Many of these come from coq.el

(defvar eventml-mode-hook nil)

(defvar eventml-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\t" 'eventml-indent-command)
    map)
  "Keymap for E# major mode.")

(defvar E-sharp-keywords
  `("let" "letrec" "in" "Prior" "self" "if" "then" "else"
    "or" "Output" "until" "Once" "OnLoc" "Skip" "class" "classrec"
    "State" "Memory"
    "any" "eqof" "case" "of"
    "constant" "import" "export" "assume" "with" "parameter" "type"
    "infix" "infixr"
    "typeof" "op" "struct" "specification" "main" "where" "include"
    "internal" "output" "input" "interface"
    "base" "send" "msg" "broadcast" "forall" "exists" "on" "wait"
    "invariant" "progress" "ordering" "consistency" "memory" "and"
    "data" "abstype" "o" "O" "variable" "options" "observes" "guarantee"
    "external"
    "%locations" "%connections" "%parameters" "%messages"
    "%databases" "%tobroadcast")
  "E# keywords.")

(defvar E-sharp-constants
  `("true" "false" "nil" "inl" "inr" "isl" "fst" "snd"
    "not" "fix" "before" "l-before" "location")
  "E# constants.")

(defvar E-sharp-types
  `("List" "Class" "Bag" "Deq" "Int" "Bool" "Atom" "Real" "Msg"
    "Type" "Prop" "Event" "Unit" "Nat" "Loc" "Tok")
  "E# types.")

;;(defvar E-sharp-comments-regexp  "(\\*\\([^*]\\|\\*[^)]\\)*\\*)")
(defvar E-sharp-keywords-regexp  (regexp-opt E-sharp-keywords  `words))
(defvar E-sharp-constants-regexp (regexp-opt E-sharp-constants `words))
(defvar E-sharp-types-regexp     (regexp-opt E-sharp-types     `words))
(defvar E-sharp-headers-regexp   "``\\(\\\\`\\|`[^`]\\|[^`]\\)*``")
(defvar E-sharp-header-regexp    "`[^`]\\(\\\\`\\|[^`]\\)*`")

(setq E-sharp-keywords  nil)
(setq E-sharp-constants nil)
(setq E-sharp-types     nil)

(setq E-sharp-font-lock-keywords
      `(
;;	(,E-sharp-comments-regexp  . font-lock-comment-face)
	(,E-sharp-headers-regexp   . font-lock-string-face)
	(,E-sharp-header-regexp    . font-lock-string-face)
	(,E-sharp-types-regexp     . font-lock-type-face)
	(,E-sharp-constants-regexp . font-lock-constant-face)
	(,E-sharp-keywords-regexp  . font-lock-keyword-face)
	)
      )

;; (save-excursion
;;   (while not-indented
;;     (forward-line -1)
;;     (if (looking-at "^[ \t]*END_") ; Check for rule 3
;; 	(progn
;; 	  (setq cur-indent (current-indentation))
;; 	  (setq not-indented nil))
;; 					; Check for rule 4
;;       (if (looking-at "^[ \t]*\\(PARTICIPANT\\|MODEL\\|APPLICATION\\|WORKFLOW\\|ACTIVITY\\|DATA\\|TOOL_LIST\\|TRANSITION\\)")
;; 	  (progn
;; 	    (setq cur-indent (+ (current-indentation) default-tab-width))
;; 	    (setq not-indented nil))
;; 	;; if first list then ident at 0
;; 	(if (bobp)
;; 	    (setq not-indented nil)
;; 	  )
;; 	)
;;       )
;;     )
;;   )
;; )

(defvar eventml-mode-syntax-table nil
  "E#'s syntax table.")

(if eventml-mode-syntax-table ()
  (setq eventml-mode-syntax-table (make-syntax-table))
  (modify-syntax-entry ?\( "()1"   eventml-mode-syntax-table)
  (modify-syntax-entry ?*  ". 23n" eventml-mode-syntax-table)
  (modify-syntax-entry ?\) ")(4"   eventml-mode-syntax-table)
  ;;(modify-syntax-entry ?`  "\""    eventml-mode-syntax-table)
  (modify-syntax-entry ?_  "w"     eventml-mode-syntax-table)
  (modify-syntax-entry ?-  "w"     eventml-mode-syntax-table)
  )

(defvar eventml-mode-indentation 2
  "Indentation for each extra tab in E# mode.")

(defun eventml-in-indentation ()
  "Tests whether all characters between beginning of line and point are blanks."
  (save-excursion
    (skip-chars-backward " \t")
    (bolp)
    )
  )

(defun eventml-indent-command ()
  "Indent current line in E# mode."
  (interactive)
  (let* ((begline
          (save-excursion
            (beginning-of-line)
            (point)))
         (current-offset
          (- (point) begline))
         (previous-indentation
          (save-excursion
            (if (eq (forward-line -1) 0) (current-indentation) 0))))
    (cond ((and (bolp)
                (looking-at "[ \t]*$")
                (> previous-indentation 0))
           (indent-to previous-indentation))
          ((eventml-in-indentation)
           (indent-to (+ current-offset eventml-mode-indentation)))
          (t
           (insert-tab))
	  )
    )
  )

(defun eventml-mode-variables ()
  (set-syntax-table eventml-mode-syntax-table)
  (make-local-variable 'paragraph-start)
  (setq paragraph-start (concat "^$\\|" page-delimiter))
  (make-local-variable 'paragraph-separate)
  (setq paragraph-separate paragraph-start)
  (make-local-variable 'paragraph-ignore-fill-prefix)
  (setq paragraph-ignore-fill-prefix t)
  (make-local-variable 'require-final-newline)
  (setq require-final-newline t)
  (make-local-variable 'comment-start)
  (setq comment-start "(* ")
  (make-local-variable 'comment-end)
  (setq comment-end " *)")
  (make-local-variable 'comment-column)
  (setq comment-column 40)
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip "(\\*+ *")
  (make-local-variable 'parse-sexp-ignore-comments)
  (setq parse-sexp-ignore-comments nil)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'eventml-indent-command)
  )

(defun eventml-mode ()
  "E# mode"
  (interactive)
  (kill-all-local-variables)
  (setq major-mode 'eventml-mode)
  (setq mode-name "EventML")
  (use-local-map eventml-mode-map)
  (eventml-mode-variables)
  (setq font-lock-defaults `(E-sharp-font-lock-keywords))
  ;;(setq E-sharp-comments-regexp  nil)
  (setq E-sharp-keywords-regexp  nil)
  (setq E-sharp-constants-regexp nil)
  (setq E-sharp-types-regexp     nil)
  (setq E-sharp-headers-regexp   nil)
  (setq E-sharp-header-regexp    nil)
  (run-hooks 'eventml-mode-hook)
)

;; (define-derived-mode E-sharp-mode fundamental-mode
;;   "E# mode"
;;   (setq font-lock-defaults `(E-sharp-font-lock-keywords))
;;   (setq E-sharp-comments-regexp  nil)
;;   (setq E-sharp-keywords-regexp  nil)
;;   (setq E-sharp-constants-regexp nil)
;;   (setq E-sharp-types-regexp     nil)
;;   (setq major-mode 'eventml-mode)
;;   (setq mode-name "E#")
;;   (run-hooks 'eventml-mode-hook)
;; )

(setq auto-mode-alist
      (cons `("\\.esharp$" . eventml-mode)
	    (cons `("\\.esh$" . eventml-mode)
		  (cons `("\\.eml$" . eventml-mode)
			(cons `("\\.emlc$" . eventml-mode)
			      auto-mode-alist)))))

(provide 'eventml-mode)
