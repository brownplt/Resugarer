
; TRICKY: let
; UNENCODABLE (3): case, letrec*, let-values-helper2
; ALMOST (3): and, or, letrec
; DISJOINT (6): cond, let*, letrec-helper, let-values,
;               let-values-helper1, let*-values

; TRICKY!!!
(define-syntax let
  (syntax-rules ()
	((let ((name val) ...) body1 body2 ...)
	 ((lambda (name ...) body1 body2 ...)
	  val ...))
	((let tag ((name val) ...) body1 body2 ...)
	 ((letrec ((tag (lambda (name ...)
					  body1 body2 ...)))
		tag)
	  val ...))))

; TRICKY!!!
(define-syntax let-values-helper2
  ;; create temporaries for the formals
  (syntax-rules ()
	((let-values-helper2
	  ()
	  temp-formals
	  expr1
	  assocs
	  bindings
	  body1 body2 ...)
	 (call-with-values
		 (lambda () expr1)
	   (lambda temp-formals
		 (let-values-helper1
		  assocs
		  bindings
		  body1 body2 ...))))
	((let-values-helper2
	  (first . rest)
	  (temp ...)
	  expr1
	  (assoc ...)
	  bindings
	  body1 body2 ...)
	 (let-values-helper2
	  rest
	  (temp ... newtemp)
	  expr1
	  (assoc ... (first newtemp))
	  bindings
	  body1 body2 ...))
	((let-values-helper2
	  rest-formal
	  (temp ...)
	  expr1
	  (assoc ...)
	  bindings
	  body1 body2 ...)
	 (call-with-values
		 (lambda () expr1)
	   (lambda (temp ... . newtemp)
		 (let-values-helper1
		  (assoc ... (rest-formal newtemp))
		  bindings
		  body1 body2 ...))))))

; ALMOST DISJOINT
(define-syntax and
  (syntax-rules ()
    ((and) #t)
    ((and test) test)
    ((and test1 test2 ...)
     (if test1 (and test2 ...) #f))))

; ALMOST DISJOINT
(define-syntax or
  (syntax-rules ()
    ((or) #f)
    ((or test) test)
    ((or test1 test2 ...)
     (let ((x test1))
	   (if x x (or test2 ...))))))

; ALMOST DISJOINT
(define-syntax case
  (syntax-rules (else)
	((case expr0
	   ((key ...) res1 res2 ...)
	   ...
	   (else else-res1 else-res2 ...))
	 (let ((tmp expr0))
	   (cond
		((memv tmp ’(key ...)) res1 res2 ...)
		...
		(else else-res1 else-res2 ...))))
	((case expr0
	   ((keya ...) res1a res2a ...)
	   ((keyb ...) res1b res2b ...)
	   ...)
	 (let ((tmp expr0))
	   (cond
		((memv tmp ’(keya ...)) res1a res2a ...)
		((memv tmp ’(keyb ...)) res1b res2b ...)
		...)))))

; ALMOST DISJOINT
(define-syntax letrec
  (syntax-rules ()
	((letrec () body1 body2 ...)
	 (let () body1 body2 ...))
	((letrec ((var init) ...) body1 body2 ...)
	 (letrec-helper
	  (var ...)
	  ()
	  ((var init) ...)
	  body1 body2 ...))))

; DISJOINT?
(define-syntax cond
  (syntax-rules (else =>)
    ((cond (else result1 result2 ...))
     (begin result1 result2 ...))
    ((cond (test => result))
     (let ((temp test))
       (if temp (result temp))))
    ((cond (test => result) clause1 clause2 ...)
     (let ((temp test))
       (if temp
           (result temp)
           (cond clause1 clause2 ...))))
	((cond (test)) test)
	((cond (test) clause1 clause2 ...)
	 (let ((temp test))
	   (if temp
		   temp
		   (cond clause1 clause2 ...))))
	((cond (test result1 result2 ...))
	 (if test (begin result1 result2 ...)))
	((cond (test result1 result2 ...)
		   clause1 clause2 ...)
	 (if test
		 (begin result1 result2 ...)
		 (cond clause1 clause2 ...)))))

; DISJOINT
(define-syntax let*
  (syntax-rules ()
	((let* () body1 body2 ...)
	 (let () body1 body2 ...))
	((let* ((name1 expr1) (name2 expr2) ...)
	   body1 body2 ...)
	 (let ((name1 expr1))
	   (let* ((name2 expr2) ...)
		 body1 body2 ...)))))

; DISJOINT
(define-syntax letrec-helper
  (syntax-rules ()
	((letrec-helper
	  ()
	  (temp ...)
	  ((var init) ...)
	  body1 body2 ...)
	 (let ((var <undefined>) ...)
	   (let ((temp init) ...)
		 (set! var temp)
		 ...)
	   (let () body1 body2 ...)))
	((letrec-helper
	  (x y ...)
	  (temp ...)
	  ((var init) ...)
	  body1 body2 ...)
	 (letrec-helper
	  (y ...)
	  (newtemp temp ...)
	  ((var init) ...)
	  body1 body2 ...))))

; DISJOINT
(define-syntax letrec*
  (syntax-rules ()
	((letrec* ((var1 init1) ...) body1 body2 ...)
	 (let ((var1 <undefined>) ...)
	   (set! var1 init1)
	   ...
	   (let () body1 body2 ...)))))

; DISJOINT
(define-syntax let-values
  (syntax-rules ()
	((let-values (binding ...) body1 body2 ...)
	 (let-values-helper1
	  ()
	  (binding ...)
	  body1 body2 ...))))

; DISJOINT
(define-syntax let-values-helper1
  ;; map over the bindings
  (syntax-rules ()
	((let-values
		 ((id temp) ...)
	   ()
	   body1 body2 ...)
	 (let ((id temp) ...) body1 body2 ...))
	((let-values
		 assocs
	   ((formals1 expr1) (formals2 expr2) ...)
	   body1 body2 ...)
	 (let-values-helper2
	  formals1
	  ()
	  expr1
	  assocs
	  ((formals2 expr2) ...)
	  body1 body2 ...))))

; DISJOINT
(define-syntax let*-values
  (syntax-rules ()
	((let*-values () body1 body2 ...)
	 (let () body1 body2 ...))
	((let*-values (binding1 binding2 ...)
	   body1 body2 ...)
	 (let-values (binding1)
	   (let*-values (binding2 ...)
		 body1 body2 ...)))))
