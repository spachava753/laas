; A proof that accepts a sample in the search for an input of get's contract (errors.go someInput), at 35dca07: unknown at the limit, 4,001,810 units, 18 s, asked twice. Without its quantified facts it is sat in 7,525 units.
(set-option :rlimit 4000000)
(declare-sort Err 0)
(declare-const nil Err)
(declare-const some-error Err)
(assert (not (= some-error nil)))
(declare-fun error-is (Err Err) Bool)
(declare-const c1 Err) ; some error 0
(assert (not (= c1 nil)))
(declare-const c2 Err) ; some error 1
(assert (not (= c2 nil)))
(assert (not (= c2 c1)))
(declare-const c3 Err) ; some error 2
(assert (not (= c3 nil)))
(assert (not (= c3 c1)))
(assert (not (= c3 c2)))
(declare-const c4 Err) ; some error 3
(assert (not (= c4 nil)))
(assert (not (= c4 c1)))
(assert (not (= c4 c2)))
(assert (not (= c4 c3)))
(declare-const c5 Err) ; some error 4
(assert (not (= c5 nil)))
(assert (not (= c5 c1)))
(assert (not (= c5 c2)))
(assert (not (= c5 c3)))
(assert (not (= c5 c4)))
(declare-const c6 Err) ; some error 5
(assert (not (= c6 nil)))
(assert (not (= c6 c1)))
(assert (not (= c6 c2)))
(assert (not (= c6 c3)))
(assert (not (= c6 c4)))
(assert (not (= c6 c5)))
(assert (<= 1 1))
(declare-datatype SeqInt ((SeqInt.mk (SeqInt.at (Array Int Int)) (SeqInt.raw Int))))
(define-fun SeqInt.len ((s SeqInt)) Int (ite (< (SeqInt.raw s) 0) 0 (SeqInt.raw s)))
(define-fun SeqInt.store ((s SeqInt) (i Int) (v Int)) SeqInt (SeqInt.mk (store (SeqInt.at s) i v) (SeqInt.raw s)))
(define-fun SeqInt.fill ((n Int) (v Int)) SeqInt (SeqInt.mk ((as const (Array Int Int)) v) n))
(define-fun SeqInt.push ((s SeqInt) (v Int)) SeqInt (SeqInt.mk (store (SeqInt.at s) (SeqInt.len s) v) (+ (SeqInt.len s) 1)))
(define-fun SeqInt.concat ((a SeqInt) (b SeqInt)) SeqInt (SeqInt.mk (lambda ((j Int)) (ite (< j (SeqInt.len a)) (select (SeqInt.at a) j) (select (SeqInt.at b) (- j (SeqInt.len a))))) (+ (SeqInt.len a) (SeqInt.len b))))
(define-fun SeqInt.sub ((s SeqInt) (lo Int) (hi Int)) SeqInt (SeqInt.mk (lambda ((j Int)) (select (SeqInt.at s) (+ lo j))) (- hi lo)))
(define-fun t7 () SeqInt (SeqInt.fill 0 0))
(assert (<= (SeqInt.len t7) 281474976710656))
(declare-const c8 Int) ; brk@1
(assert (<= 1 c8))
(declare-const c9 Int) ; out#ptr@1
(declare-const c10 Int) ; out#at@1
(assert (and (<= 0 c9) (< c9 c8) (<= 0 c10) (<= c10 281474976710656)))
(declare-datatype SeqSeqInt ((SeqSeqInt.mk (SeqSeqInt.at (Array Int SeqInt)) (SeqSeqInt.raw Int))))
(define-fun SeqSeqInt.len ((s SeqSeqInt)) Int (ite (< (SeqSeqInt.raw s) 0) 0 (SeqSeqInt.raw s)))
(define-fun SeqSeqInt.store ((s SeqSeqInt) (i Int) (v SeqInt)) SeqSeqInt (SeqSeqInt.mk (store (SeqSeqInt.at s) i v) (SeqSeqInt.raw s)))
(define-fun SeqSeqInt.fill ((n Int) (v SeqInt)) SeqSeqInt (SeqSeqInt.mk ((as const (Array Int SeqInt)) v) n))
(define-fun SeqSeqInt.push ((s SeqSeqInt) (v SeqInt)) SeqSeqInt (SeqSeqInt.mk (store (SeqSeqInt.at s) (SeqSeqInt.len s) v) (+ (SeqSeqInt.len s) 1)))
(define-fun SeqSeqInt.concat ((a SeqSeqInt) (b SeqSeqInt)) SeqSeqInt (SeqSeqInt.mk (lambda ((j Int)) (ite (< j (SeqSeqInt.len a)) (select (SeqSeqInt.at a) j) (select (SeqSeqInt.at b) (- j (SeqSeqInt.len a))))) (+ (SeqSeqInt.len a) (SeqSeqInt.len b))))
(define-fun SeqSeqInt.sub ((s SeqSeqInt) (lo Int) (hi Int)) SeqSeqInt (SeqSeqInt.mk (lambda ((j Int)) (select (SeqSeqInt.at s) (+ lo j))) (- hi lo)))
(declare-datatype SeqSeqSeqInt ((SeqSeqSeqInt.mk (SeqSeqSeqInt.at (Array Int SeqSeqInt)) (SeqSeqSeqInt.raw Int))))
(define-fun SeqSeqSeqInt.len ((s SeqSeqSeqInt)) Int (ite (< (SeqSeqSeqInt.raw s) 0) 0 (SeqSeqSeqInt.raw s)))
(define-fun SeqSeqSeqInt.store ((s SeqSeqSeqInt) (i Int) (v SeqSeqInt)) SeqSeqSeqInt (SeqSeqSeqInt.mk (store (SeqSeqSeqInt.at s) i v) (SeqSeqSeqInt.raw s)))
(define-fun SeqSeqSeqInt.fill ((n Int) (v SeqSeqInt)) SeqSeqSeqInt (SeqSeqSeqInt.mk ((as const (Array Int SeqSeqInt)) v) n))
(define-fun SeqSeqSeqInt.push ((s SeqSeqSeqInt) (v SeqSeqInt)) SeqSeqSeqInt (SeqSeqSeqInt.mk (store (SeqSeqSeqInt.at s) (SeqSeqSeqInt.len s) v) (+ (SeqSeqSeqInt.len s) 1)))
(define-fun SeqSeqSeqInt.concat ((a SeqSeqSeqInt) (b SeqSeqSeqInt)) SeqSeqSeqInt (SeqSeqSeqInt.mk (lambda ((j Int)) (ite (< j (SeqSeqSeqInt.len a)) (select (SeqSeqSeqInt.at a) j) (select (SeqSeqSeqInt.at b) (- j (SeqSeqSeqInt.len a))))) (+ (SeqSeqSeqInt.len a) (SeqSeqSeqInt.len b))))
(define-fun SeqSeqSeqInt.sub ((s SeqSeqSeqInt) (lo Int) (hi Int)) SeqSeqSeqInt (SeqSeqSeqInt.mk (lambda ((j Int)) (select (SeqSeqSeqInt.at s) (+ lo j))) (- hi lo)))
(declare-const c11 SeqSeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Status
(define-fun t12 () SeqInt (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c11) c9)) (+ c10 0)))
(declare-const c13 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.StatusCode
(define-fun t14 () Int (select (SeqInt.at (select (SeqSeqInt.at c13) c9)) (+ c10 16)))
(declare-const c15 SeqSeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Proto
(define-fun t16 () SeqInt (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c15) c9)) (+ c10 24)))
(declare-const c17 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.ProtoMajor
(define-fun t18 () Int (select (SeqInt.at (select (SeqSeqInt.at c17) c9)) (+ c10 40)))
(declare-const c19 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.ProtoMinor
(define-fun t20 () Int (select (SeqInt.at (select (SeqSeqInt.at c19) c9)) (+ c10 48)))
(declare-const c21 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Header
(define-fun t22 () Int (select (SeqInt.at (select (SeqSeqInt.at c21) c9)) (+ c10 56)))
(declare-const c23 SeqInt) ; home
(declare-const c24 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Body
(define-fun t25 () Int (select (SeqInt.at (select (SeqSeqInt.at c24) c9)) (+ c10 64)))
(define-fun t26 () Int (select (SeqInt.at c23) t25))
(declare-const c27 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.ContentLength
(define-fun t28 () Int (select (SeqInt.at (select (SeqSeqInt.at c27) c9)) (+ c10 80)))
(declare-const c29 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#ref
(define-fun t30 () Int (select (SeqInt.at (select (SeqSeqInt.at c29) c9)) (+ c10 88)))
(declare-const c31 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#off
(define-fun t32 () Int (select (SeqInt.at (select (SeqSeqInt.at c31) c9)) (+ c10 88)))
(declare-const c33 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#len
(define-fun t34 () Int (select (SeqInt.at (select (SeqSeqInt.at c33) c9)) (+ c10 88)))
(declare-const c35 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#cap
(define-fun t36 () Int (select (SeqInt.at (select (SeqSeqInt.at c35) c9)) (+ c10 88)))
(declare-const c37 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Trailer
(define-fun t38 () Int (select (SeqInt.at (select (SeqSeqInt.at c37) c9)) (+ c10 120)))
(declare-const c39 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Request#ptr
(define-fun t40 () Int (select (SeqInt.at (select (SeqSeqInt.at c39) c9)) (+ c10 128)))
(declare-const c41 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Request#at
(define-fun t42 () Int (select (SeqInt.at (select (SeqSeqInt.at c41) c9)) (+ c10 128)))
(declare-const c43 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TLS#ptr
(define-fun t44 () Int (select (SeqInt.at (select (SeqSeqInt.at c43) c9)) (+ c10 136)))
(declare-const c45 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TLS#at
(define-fun t46 () Int (select (SeqInt.at (select (SeqSeqInt.at c45) c9)) (+ c10 136)))
(declare-const c50 SeqSeqInt) ; mem map map[string][]string#1#val#ref
(declare-const c51 SeqSeqInt) ; mem map map[string][]string#1#val#off
(declare-const c52 SeqSeqInt) ; mem map map[string][]string#1#val#len
(declare-const c53 SeqSeqInt) ; mem map map[string][]string#1#val#cap
(declare-const c55 SeqSeqSeqInt) ; mem elem string#2
(assert (and (<= 0 c9) (< c9 c8) (<= 0 c10) (<= c10 281474976710656) (<= (SeqInt.len t12) 281474976710656) (<= (- 9223372036854775808) t14) (<= t14 9223372036854775807) (<= (SeqInt.len t16) 281474976710656) (<= (- 9223372036854775808) t18) (<= t18 9223372036854775807) (<= (- 9223372036854775808) t20) (<= t20 9223372036854775807) (<= 0 t22) (< t22 c8) (<= 0 t26) (< t26 c8) (< 0 (select (SeqInt.at c23) t25)) (<= (- 9223372036854775808) t28) (<= t28 9223372036854775807) (<= 0 t30) (< t30 c8) (<= 0 t32) (<= 0 t34) (<= t34 t36) (<= (+ (* t32 16) (* t36 16)) 281474976710656) (<= (- 9223372036854775808) t36) (<= t36 9223372036854775807) (<= 0 t38) (< t38 c8) (<= 0 t40) (< t40 c8) (<= 0 t42) (<= t42 281474976710656) (<= 0 t44) (< t44 c8) (<= 0 t46) (<= t46 281474976710656) (forall ((b47 Int)) (=> (and (<= 0 b47) (< b47 (SeqInt.len t12))) (and (<= 0 (select (SeqInt.at t12) b47)) (<= (select (SeqInt.at t12) b47) 255)))) (forall ((b48 Int)) (=> (and (<= 0 b48) (< b48 (SeqInt.len t16))) (and (<= 0 (select (SeqInt.at t16) b48)) (<= (select (SeqInt.at t16) b48) 255)))) (forall ((b49 Int)) (and (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c50) t22)) b49)) (< (select (SeqInt.at (select (SeqSeqInt.at c50) t22)) b49) c8) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c51) t22)) b49)) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c52) t22)) b49)) (<= (select (SeqInt.at (select (SeqSeqInt.at c52) t22)) b49) (select (SeqInt.at (select (SeqSeqInt.at c53) t22)) b49)) (<= (+ (* (select (SeqInt.at (select (SeqSeqInt.at c51) t22)) b49) 16) (* (select (SeqInt.at (select (SeqSeqInt.at c53) t22)) b49) 16)) 281474976710656) (<= (- 9223372036854775808) (select (SeqInt.at (select (SeqSeqInt.at c53) t22)) b49)) (<= (select (SeqInt.at (select (SeqSeqInt.at c53) t22)) b49) 9223372036854775807))) (and (forall ((b54 Int)) (=> (and (<= 0 b54) (< b54 t34)) (<= (SeqInt.len (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c55) t30)) (+ (+ t32 (* b54 1)) 0))) 281474976710656))) (forall ((b57 Int)) (! (=> (and (<= 0 (+ b57 (- (+ t32 0)))) (< (+ b57 (- (+ t32 0))) t34)) (<= (SeqInt.len (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c55) t30)) b57)) 281474976710656)) :pattern ((select (SeqSeqInt.at (select (SeqSeqSeqInt.at c55) t30)) b57))))) (forall ((b58 Int)) (=> (and (<= 0 b58) (< b58 t34)) (forall ((b59 Int)) (=> (and (<= 0 b59) (< b59 (SeqInt.len (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c55) t30)) (+ (+ t32 (* b58 1)) 0))))) (and (<= 0 (select (SeqInt.at (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c55) t30)) (+ (+ t32 (* b58 1)) 0))) b59)) (<= (select (SeqInt.at (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c55) t30)) (+ (+ t32 (* b58 1)) 0))) b59) 255)))))) (forall ((b60 Int)) (and (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c50) t38)) b60)) (< (select (SeqInt.at (select (SeqSeqInt.at c50) t38)) b60) c8) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c51) t38)) b60)) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c52) t38)) b60)) (<= (select (SeqInt.at (select (SeqSeqInt.at c52) t38)) b60) (select (SeqInt.at (select (SeqSeqInt.at c53) t38)) b60)) (<= (+ (* (select (SeqInt.at (select (SeqSeqInt.at c51) t38)) b60) 16) (* (select (SeqInt.at (select (SeqSeqInt.at c53) t38)) b60) 16)) 281474976710656) (<= (- 9223372036854775808) (select (SeqInt.at (select (SeqSeqInt.at c53) t38)) b60)) (<= (select (SeqInt.at (select (SeqSeqInt.at c53) t38)) b60) 9223372036854775807)))))
(assert (and (<= (SeqInt.len t7) 281474976710656) (forall ((b61 Int)) (=> (and (<= 0 b61) (< b61 (SeqInt.len t7))) (and (<= 0 0) (<= 0 255))))))
(define-fun t62 () Int (select (SeqInt.at (select (SeqSeqInt.at c24) c9)) (+ c10 64)))
(define-fun t63 () Int (select (SeqInt.at c23) t62))
(assert (and (<= 0 t63) (< t63 c8) (< 0 (select (SeqInt.at c23) t62))))
(declare-const c64 Err) ; out@1
(declare-datatype SeqBool ((SeqBool.mk (SeqBool.at (Array Int Bool)) (SeqBool.raw Int))))
(define-fun SeqBool.len ((s SeqBool)) Int (ite (< (SeqBool.raw s) 0) 0 (SeqBool.raw s)))
(define-fun SeqBool.store ((s SeqBool) (i Int) (v Bool)) SeqBool (SeqBool.mk (store (SeqBool.at s) i v) (SeqBool.raw s)))
(define-fun SeqBool.fill ((n Int) (v Bool)) SeqBool (SeqBool.mk ((as const (Array Int Bool)) v) n))
(define-fun SeqBool.push ((s SeqBool) (v Bool)) SeqBool (SeqBool.mk (store (SeqBool.at s) (SeqBool.len s) v) (+ (SeqBool.len s) 1)))
(define-fun SeqBool.concat ((a SeqBool) (b SeqBool)) SeqBool (SeqBool.mk (lambda ((j Int)) (ite (< j (SeqBool.len a)) (select (SeqBool.at a) j) (select (SeqBool.at b) (- j (SeqBool.len a))))) (+ (SeqBool.len a) (SeqBool.len b))))
(define-fun SeqBool.sub ((s SeqBool) (lo Int) (hi Int)) SeqBool (SeqBool.mk (lambda ((j Int)) (select (SeqBool.at s) (+ lo j))) (- hi lo)))
(declare-datatype SeqSeqBool ((SeqSeqBool.mk (SeqSeqBool.at (Array Int SeqBool)) (SeqSeqBool.raw Int))))
(define-fun SeqSeqBool.len ((s SeqSeqBool)) Int (ite (< (SeqSeqBool.raw s) 0) 0 (SeqSeqBool.raw s)))
(define-fun SeqSeqBool.store ((s SeqSeqBool) (i Int) (v SeqBool)) SeqSeqBool (SeqSeqBool.mk (store (SeqSeqBool.at s) i v) (SeqSeqBool.raw s)))
(define-fun SeqSeqBool.fill ((n Int) (v SeqBool)) SeqSeqBool (SeqSeqBool.mk ((as const (Array Int SeqBool)) v) n))
(define-fun SeqSeqBool.push ((s SeqSeqBool) (v SeqBool)) SeqSeqBool (SeqSeqBool.mk (store (SeqSeqBool.at s) (SeqSeqBool.len s) v) (+ (SeqSeqBool.len s) 1)))
(define-fun SeqSeqBool.concat ((a SeqSeqBool) (b SeqSeqBool)) SeqSeqBool (SeqSeqBool.mk (lambda ((j Int)) (ite (< j (SeqSeqBool.len a)) (select (SeqSeqBool.at a) j) (select (SeqSeqBool.at b) (- j (SeqSeqBool.len a))))) (+ (SeqSeqBool.len a) (SeqSeqBool.len b))))
(define-fun SeqSeqBool.sub ((s SeqSeqBool) (lo Int) (hi Int)) SeqSeqBool (SeqSeqBool.mk (lambda ((j Int)) (select (SeqSeqBool.at s) (+ lo j))) (- hi lo)))
(declare-const c65 SeqSeqBool) ; mem iface state
(assert (=> (= c64 nil) (and (not (= c9 0)) (not (= t62 0)) (not (select (SeqBool.at (select (SeqSeqBool.at c65) (select (SeqInt.at c23) (select (SeqInt.at (select (SeqSeqInt.at c24) c9)) (+ c10 64))))) (+ 2997695091990504928268101341469504234022244 0))) (<= 1 (select (SeqInt.at c23) (select (SeqInt.at (select (SeqSeqInt.at c24) c9)) (+ c10 64)))))))
(assert (not (= c64 nil)))
(check-sat-using (then simplify propagate-values ctx-simplify simplify elim-uncnstr smt))
