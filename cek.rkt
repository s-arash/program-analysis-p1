#lang racket
;; Project 1 -- CIS 700
;; Implementing an ANF-style lambda calculus
;; 
;; Kris Micinski, Syracuse University, Fall 2019.  Please send
;; corrections and comments to kkmicins@syr.edu.
;; 
;; DESCRIPTION: 
;;
;; For this project, you will implement a CEK-style interpreter for
;; the ANF-converted lambda calculus.
;;
;; This project has three parts:
;; 
;; - Part 1. Complete each section that is marked TODO. None of these
;; should take more than a few lines of code, so feel free to write
;; email if you find yourself getting lost.
;; 
;; - Part 2. Extend the language with one of the following forms:
;; `letrec`, `if`, or `call/cc`. Of these, `if` is fairly easy,
;; `letrec` is not too much harder (but you may have to email me to
;; talk about it) and `call/cc` is a bit trickier (requires extending
;; the kinds of continuations and then defining how to apply a
;; continuation). If you want to get a lot out of the project, I would
;; recommend you implement all three, but only one is required (so if
;; you don't want to do as much work, just implement `if`). As you
;; extend the language, you should ensure that you extend the
;; predicates defined below. 
;; 
;; Make sure you make life easy on yourself by assuming that the
;; language has been ANF converted. For example, assume you don't have
;; to handle something like `(if (let ([x ((lambda (x) x) #t)]) x) 1
;; 2), feel free to require the language to be in ANF.
;; 
;; - Part 3. This part is optional. I have a few questions below. You
;; can answer these in comments if you would like.
;; 
;; By the way, please see if you can figure out how to use the
;; `grapify` function. It will produce output which can be visualized
;; using graphviz. If you don't want to set up graphviz, there are a
;; few graphviz visualizers online:
;; 
;;     https://dreampuf.github.io/GraphvizOnline

;; ANF Lambda calculus
;; Definition of core language

;; Atomic expressions
(define (aexpr? ae)
  (match ae
    ;; Variables
    [(? symbol? x) #t]
    ;; Literals
    [(? number? n) #t]
    ;; Booleans
    [(? boolean? b) #t]
    ;; Lambdas
    [`(lambda (,(? symbol? xs) ...) ,(? expr?)) #t]
    [else #f]))

;; Expression language
(define (expr? e)
  (match e
    ;; if expressions
    [`(if ,(? aexpr? ae-cond) ,(? expr? e-then) ,(? expr? e-else)) #t]
    ;; Function calls
    [`(,(? aexpr? ae0) ,(? aexpr? aes) ...) #t]
    ;; Let forms
    [`(let ([,x ,(? expr? e)]) ,(? expr? let-body)) #t]
    ;; letrec
    [`(letrec ([,x ,(? expr? e)]) ,(? expr? body)) #t]
    ;; call/cc
    [`(call/cc ,(? aexpr?)) #t]
    ;; Returns
    [(? aexpr? ae) #t]
    [else #f]))

;; Literals
(define (lit? l)
  (or (number? l) (boolean? l)))

;; ρ ∈ Env, Environments
(define (env? e)
  (and (andmap (lambda (key) (symbol? key)) (hash-keys e))
       (andmap value? (hash-values e))))

;; Values are either literals or closures
(define (value? v)
  (match v
    [(? lit?) #t]
    [`(clo (lambda (,x) ,(? expr?)) ,(? env?)) #t]
    [`(clo-rec (lambda (,x) ,(? expr?)) ,(? symbol? f-var) ,(? env?)) #t]
    [`(kont ,(? kont?)) #t]))

;; Continuations forms
(define (kont? k)
  (match k
    ['mt #t]
    [`(let ,(? symbol? x) ,(? env? ρ) ,(? expr? let-body) ,(? kont? k)) #t]))

;; Definition of ς ∈ Σ ::= ⟨ C, E, K ⟩
(define (state? state)
  (match state
    [`(,(? expr?) ,(? env?) ,(? kont?)) #t]
    [else #f]))

;; Create a CEK state from a term e
;; 
;; TODO:✓ You should specify how to construct a sensible initial state
;; for the machine.
(define (inject e)
  `(,e ,(hash) mt))

;; Examples
(define id-id '(let ([x (lambda (x) x)]) (x x)))
(define omega '(let ([x (lambda (x) (x x))]) (x x)))
(define id-id-id-id '(let ([x (lambda (x) x)]) (let ([y (x x)]) (y y))))
(define example-4 '(letrec ([f (lambda (x) (if x f (lambda (y) y)))])
                    (let ([ft (f #t)])
                      (let ([ftf (ft #f)])
                      (ftf 42)))))
(define example-5
  '(letrec ([fac (lambda (n)
                   (let ([n=0 (= n 0)])
                     (if n=0 1
                         (let ([n-1 (- n 1)])
                           (let ([facn-1 (fac n-1)])
                           (* n facn-1))))))])
     (fac 3)))

;; TODO:✓ You should define the atomic expression evaluator. This is
;; AEval(ae,ρ) : AExpr × Env → Value.
(define (aeval ae ρ)
  (match ae
    [(? number? n) n]
    [(? boolean? b) b]
    [(? symbol? x) (hash-ref ρ x)]
    [`(lambda (,x) ,e) `(clo ,ae ,ρ)]))

(define (val->λ-ρ v)
  (match v
    [`(clo (lambda ,xs ,e) ,ρ) (cons `(lambda ,xs ,e) ρ)]
    [`(clo-rec (lambda ,xs ,e) ,f ,ρ) (cons `(lambda ,xs ,e) (hash-set ρ f v))])) 

;; Adding builtins to help with testing, not part of the assignmnet!
(define builtins
  (hash 'add1 add1
        'sub1 sub1
        'zero? zero?
        '= =
        '+ +
        '- -
        '* *
        '/ /))
(define (builtin? b) (hash-has-key? builtins b))

;; Step relation: Σ → Σ
;; TODO: Complete the implementation for each case.
(define (step state)
  (match state
    ;; Handle a let: step into `e` while remembering (via the `let`
    ;; continuation) to go back and bind x within ρ before proceeding
    ;; to body and continuation k.
    [`((let ([,x ,e]) ,body) ,ρ ,k)
     `(,e ,ρ (let ,x ,ρ ,body ,k))]

    [`((letrec ([,f (lambda (,x) ,e)]) ,body) ,ρ ,k)
     `(,body ,(hash-set ρ f `(clo-rec (lambda (,x) ,e) ,f ,ρ)) ,k)]

    ;; Returns. You should specify how to handle when an atomic
    ;; expression is in return position. Because this is an A-Normal
    ;; Form language, the only return position will be the `let`
    ;; continuation.
    [`(,(? aexpr? ae) ,ρ (let ,x ,ρ-prime ,e ,k))
     `(,e ,(hash-set ρ-prime x (aeval ae ρ)) ,k)]

    ;; if expressions
    [`((if ,ae-cond ,e-then ,e-else) ,ρ ,k)
     `(,(if (aeval ae-cond ρ) e-then e-else) ,ρ ,k)]

    ;; call/cc
    [`((call/cc ,(? aexpr? f)) ,ρ ,k)
     (match (aeval f ρ)
       [`(kont ,k-prime)
        ;; This is the weird case, where we have (call/cc [some continuation])
        ;; Here, we have a problem, we wanna put k in the control string position,
        ;; but k is not an expression, and we don't have return states. So, one
        ;; workaround is to make up a variable κp, put it in the control string position,
        ;; and update ρ to map κp to k
        (let ([κp (gensym)])
          `(,κp ,(hash-set ρ κp `(kont ,k)) ,k-prime))]
       [clo
        ;; The normal case
        (match-let ([(cons `(lambda (,x) ,e) ρ-prime) (val->λ-ρ clo)])
          `(,e ,(hash-set ρ-prime x `(kont ,k)) ,k))])]

    ;; Builtins
    [`((,(? builtin? b) ,aes ...) ,ρ ,k)
     (let ([v (apply (hash-ref builtins b) (map (λ (ae) (aeval ae ρ)) aes))])
       `(,v ,ρ ,k))]
    
    ;; Application. Each is an atomic expression. Assume that ae0 will
    ;; evaluate to a closure. This means that `(aeval ae0 ρ) will
    ;; evaluate to something that matches something like `(clo (lambda
    ;; (,xs ...) ,e-body) ,ρ-prime).
    [`((,ae0 ,aes ...) ,ρ ,k)
     (match (aeval ae0 ρ)
       [`(kont ,k-prime)
        `(,(car aes) ,ρ ,k-prime)]
       [clo
        (match-let* ([(cons `(lambda (,xs ...) ,e-body) ρ-prime) (val->λ-ρ clo)]
                     [new-ρ (foldl (λ (x_i ae_i res-ρ) (hash-set res-ρ x_i (aeval ae_i ρ))) ρ-prime xs aes)])
          `(,e-body ,new-ρ ,k))])]
    ))

;; TODO:✓ Is this state at a done configuration?
(define (done? state)
  (match state
    [`(,(? aexpr? ae) ,ρ mt) #t]
    [else #f]))

;; Iterate the state to a final answer, build up a transition graph.
(define (iterate state)
  (define (h state state-graph last-state)
    (if (done? state)
        (begin (displayln "Done!") (pretty-print state) state-graph)
        (let* ([next-state (step state)]
               ;; Add to the state graph by adding an edge between the
               ;; last state and this state.
               [next-state-graph
                (if (null? last-state)
                    (hash-set state-graph next-state (set))
                    (hash-set state-graph
                              last-state
                              (set-add (hash-ref state-graph last-state (set)) next-state)))])
          (displayln (format "--> ~a" (pretty-format state)))
          (h next-state next-state-graph next-state))))
  (h state (hash) null))

;; Render h as a DOT graph
(define (graphify h)
  (define lines
    (flatten (hash-map h (lambda (key value) (map (lambda (v) (format "\"~a\" -> \"~a\"" key v)) (set->list value))))))
  (displayln "digraph {")
  (for ([line lines])
    (displayln (format "  ~a" line)))
  (displayln "}"))

;;
;; REPL
;;

;; Run a REPL
(define (repl)
  (displayln "Type an expression...")
  (display "> ")
  (let ([input (read)])
    (if (expr? input)
        ;; Execute the expression
        (graphify (iterate (inject input)))
        (displayln "Input expression does not satisfy expr?"))
    (repl)))

;; Top level entry point to the program
(repl)

;; Part 3:
;; 
;; Answer the following questions in as much detail as you think is
;; helpful to you understanding. These questions are meant to address
;; broad knowledge about the project and its relation to other
;; material in the course. Please try to give precise examples in your
;; explanations.
;; 
;; - Compared to Continuation-Passing Style, A-Normal Form allows us
;; just *one* continuation, a `let` continuation. Why might this be
;; desirable, in terms of using CPS vs. ANF as an intermediate
;; language for compilation or analysis of (say) Scheme? Hint: there's
;; no single correct answer here, but when you code things in CPS
;; every call is a tail call. This is a little silly. Think about CPS
;; as an intermediate language versus, say, basic-block-based
;; representations from C compilers or disassemblers. Viewed through
;; that lens, CPS is roughly analogous to having every instruction
;; labeled and manually go to the next one, which defeats the entire
;; point of having basic blocks.

;; ANSWER: CPS makes intra-procedural analysis more difficult, as the body of
;; every function is just a call to another function. By CPS converting
;; source code, we lose information about what operations were bundled
;; together inside a procedure, and we lose the ability to inspect, and
;; optimize the code (because the operations are signle threaded), so for
;; example, in a call like (f e1 e2), in a pure language, the compiler
;; could decide to generate code that computes e1 and e2 in parallel, but
;; in the CPS converted version of the code (that is similar to something
;; like this: 
;; ([f] (λ fk. ([e1] (λ e1k. ([e2] λ e2k. (fk e1k e2k))))))
;; everything is explicitly sequenced, and so a simple analysis like the
;; one mentioned above becomes much more difficult.
 
;; - Sketch out, either via modifying the predicates above or in
;; ASCII/Unicode-based math how the machine would look if it were to
;; handle the CPS lambda calculus.

;; ANSWER: the language definition would be different:
(define (cps-ae? e)
  (match e
    [(? symbol?) #t]
    [`(lambda (,xs ...) (,(? cps-ae? aes) ...)) #t]
    [else #f]))
;; and we could do without continuations in the machine.


;; - If you were to convert the language to CPS, your interpreter
;; rules would change. How would they change? Hint: think about
;; whether you truly need the continuation in that case.

;; ANSWER: continuations would not be needed, because, as you put it,
;; every function body is just a tail call. So a CE machine (without K)
;; would be sufficient to interpret CPS terms.

;; - Elaborate upon the following observation with a few examples: in
;; CPS, every expression is a tail-call, while in ANF every expression
;; is either a tail call or a return.

;; ANSWER: A term like (f (g h)) might be CPS converted to something
;; like this:
#;([f] (λ (fk) ((λ (k) ([g] k h)) (λ (ghk) (fk ghk)))))
;; In the term above, the body of every function is a call where the
;; receiver and the arguments are all atomic expressions. This makes
;; the body of every function a tail call.
;;The same expression will be ANF converted to:
#;(let ([gh (g h)]) (f gh))
;; In this expression, (g h) is a return expression and (f gh) is a
;; tail call
