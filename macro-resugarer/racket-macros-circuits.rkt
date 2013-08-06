#lang racket

(require "resugar.rkt")
(require "resugar-racket.rkt")
(require data/queue)
(require scheme/mpair)

;; The circuit simulation from SICP, as macros.
;; http://mitpress.mit.edu/sicp/full-text/sicp/book/node64.html

(define (inverter input output)
  (define (invert-input)
    (let ((new-value (logical-not (get-signal input))))
      (after-delay inverter-delay
                   (lambda ()
                     (set-signal! output new-value)))))
  (add-action! input invert-input)
  'ok)

(define (logical-not s)
  (cond ((= s 0) 1)
        ((= s 1) 0)
        (else (error "Invalid signal" s))))

(define (logical-and x y)
  (cond ((= x 0) 0)
        ((= y 0) 0)
        ((and (= x 1) (= y 1)) 1)
        (else (error "Invalid signal" x y))))

(define (logical-or x y)
  (cond ((= x 1) 1)
        ((= y 1) 1)
        ((and (= x 0) (= y 0)) 0)
        (else (error "Invalid signal" x y))))

(define (and-gate a1 a2 output)
  (define (and-action-procedure)
    (let ((new-value
           (logical-and (get-signal a1) (get-signal a2))))
      (after-delay and-gate-delay
                   (lambda ()
                     (set-signal! output new-value)))))
  (add-action! a1 and-action-procedure)
  (add-action! a2 and-action-procedure)
  'ok)

(define (or-gate a1 a2 output) 
  (define (or-action-procedure) 
    (let ((new-value  
           (logical-or (get-signal a1) (get-signal a2)))) 
      (after-delay or-gate-delay 
                   (lambda () 
                     (set-signal! output new-value))))) 
  (add-action! a1 or-action-procedure) 
  (add-action! a2 or-action-procedure)
  'ok)

(define (make-wire)
  (let ((signal-value 0) (action-procedures '()))
    (define (set-my-signal! new-value)
      (if (not (= signal-value new-value))
          (begin (set! signal-value new-value)
                 (call-each action-procedures))
          'done))

    (define (accept-action-procedure! proc)
      (set! action-procedures (mcons proc action-procedures))
      (proc))

    (define (dispatch m)
      (cond ((eq? m 'get-signal) signal-value)
            ((eq? m 'set-signal!) set-my-signal!)
            ((eq? m 'add-action!) accept-action-procedure!)
            (else (error "Unknown operation - WIRE" m))))
    dispatch))

(define (call-each procedures)
  (if (null? procedures)
      'done
      (begin
        ((mcar procedures))
        (call-each (mcdr procedures)))))

(define (get-signal wire)
  (wire 'get-signal))

(define (set-signal! wire new-value)
  ((wire 'set-signal!) new-value))

(define (add-action! wire action-procedure)
  ((wire 'add-action!) action-procedure))

(define (after-delay delay action)
  (add-to-agenda! (+ delay (current-time the-agenda))
                  action
                  the-agenda))

(define (make-time-segment time queue)
  (mcons time queue))

(define (segment-time s) (mcar s))

(define (segment-queue s) (mcdr s))

(define (make-agenda) (mlist 0))

(define (current-time agenda) (mcar agenda))

(define (set-current-time! agenda time)
  (set-mcar! agenda time))

(define (segments agenda) (mcdr agenda))

(define (set-segments! agenda segments)
  (set-mcdr! agenda segments))

(define (first-segment agenda) (mcar (segments agenda)))

(define (rest-segments agenda) (mcdr (segments agenda)))

(define (empty-agenda? agenda)
  (null? (segments agenda)))

(define (add-to-agenda! time action agenda)
  (define (belongs-before? segments)
    (or (null? segments)
        (< time (segment-time (mcar segments)))))
  (define (make-new-time-segment time action)
    (let ((q (make-queue)))
      (enqueue! q action)
      (make-time-segment time q)))
  (define (add-to-segments! segments)
    (if (= (segment-time (mcar segments)) time)
        (enqueue! (segment-queue (mcar segments))
                  action)
        (let ((rest (mcdr segments)))
          (if (belongs-before? rest)
              (set-mcdr!
               segments
               (mcons (make-new-time-segment time action)
                     (mcdr segments)))
              (add-to-segments! rest)))))
  (let ((segments (segments agenda)))
    (if (belongs-before? segments)
        (set-segments!
         agenda
         (mcons (make-new-time-segment time action)
               segments))
        (add-to-segments! segments))))

(define (remove-first-agenda-item! agenda)
  (let ((q (segment-queue (first-segment agenda))))
    (dequeue! q)
    (when (queue-empty? q)
      (set-segments! agenda (rest-segments agenda)))))

(define (first-agenda-item agenda)
  (if (empty-agenda? agenda)
      (error "Agenda is empty - FIRST-AGENDA-ITEM")
      (let ((first-seg (first-segment agenda)))
        (set-current-time! agenda (segment-time first-seg))
        (peek-queue (segment-queue first-seg)))))

(define (peek-queue q)
  (car (queue->list q)))

(define (propagate)
  (if (empty-agenda? the-agenda)
      'done
      (let ((first-item (first-agenda-item the-agenda)))
        (first-item)
        (remove-first-agenda-item! the-agenda)
        (propagate))))

(define (probe name wire)
  (add-action! wire
               (lambda ()        
                 (newline)
                 (display name)
                 (display " ")
                 (display (current-time the-agenda))
                 (display "  New-value = ")
                 (display (get-signal wire)))))

(define the-agenda (make-agenda))
(define inverter-delay 2)
(define and-gate-delay 3)
(define or-gate-delay 5)

(define input-1 (make-wire))
(define input-2 (make-wire))
(define sum (make-wire))
(define carry (make-wire))

(define-macro MakeCircuit
  [(MakeCircuit (^ wires ...) (^ gate args ...) ...)
   (Let [^ [^ wires (make-wire)] ...]
        (begin
          (gate args ...)
          ...
          "ok"))])

(define-macro Let
  [(Let [^ [^ x e]] b)
   ((lambda (x) b) e)]
  [(Let [^ [^ x e] y ys ...] b)
   ((lambda (x) (! Let [^ y ys ...] b)) e)])

(define (half-adder a b s c)
  (let ((d (make-wire)) (e (make-wire)))
    (or-gate a b d)
    (and-gate a b c)
    (inverter c e)
    (and-gate d e s)
    'ok))

(test-eval (
  (LetRec [^ [^ input-1 (make-wire)]
           [^ input-2 (make-wire)]
           [^ sum (make-wire)]
           [^ carry (make-wire)]
           [^ half-adder
         (lambda (a b s c)
           (MakeCircuit (^ e d)
             (^ or-gate  a b d)
             (^ and-gate a b c)
             (^ inverter c   e)
             (^ and-gate d e s)))]]
       (begin
         (half-adder input-1 input-2 sum carry)
         (set-signal! input-1 1)
         (propogate)))))

(probe 'sum sum)

(probe 'carry carry)

(half-adder input-1 input-2 sum carry)

(set-signal! input-1 1)

(propagate)

(set-signal! input-2 1)

(propagate)