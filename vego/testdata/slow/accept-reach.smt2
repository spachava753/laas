; A proof that accepts a sample in canReach's search after the call of get in Fetch (errors.go someInput), at 35dca07: unknown at the limit, 4,001,853 units, 9 s. Without its quantified facts it is sat in 8,074 units.
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
(declare-const c9 Int) ; get#ptr@1
(declare-const c10 Int) ; get#at@1
(assert (and (<= 0 c9) (< c9 c8) (<= 0 c10) (<= c10 281474976710656)))
(declare-const c11 SeqInt) ; home
(declare-datatype SeqSeqInt ((SeqSeqInt.mk (SeqSeqInt.at (Array Int SeqInt)) (SeqSeqInt.raw Int))))
(define-fun SeqSeqInt.len ((s SeqSeqInt)) Int (ite (< (SeqSeqInt.raw s) 0) 0 (SeqSeqInt.raw s)))
(define-fun SeqSeqInt.store ((s SeqSeqInt) (i Int) (v SeqInt)) SeqSeqInt (SeqSeqInt.mk (store (SeqSeqInt.at s) i v) (SeqSeqInt.raw s)))
(define-fun SeqSeqInt.fill ((n Int) (v SeqInt)) SeqSeqInt (SeqSeqInt.mk ((as const (Array Int SeqInt)) v) n))
(define-fun SeqSeqInt.push ((s SeqSeqInt) (v SeqInt)) SeqSeqInt (SeqSeqInt.mk (store (SeqSeqInt.at s) (SeqSeqInt.len s) v) (+ (SeqSeqInt.len s) 1)))
(define-fun SeqSeqInt.concat ((a SeqSeqInt) (b SeqSeqInt)) SeqSeqInt (SeqSeqInt.mk (lambda ((j Int)) (ite (< j (SeqSeqInt.len a)) (select (SeqSeqInt.at a) j) (select (SeqSeqInt.at b) (- j (SeqSeqInt.len a))))) (+ (SeqSeqInt.len a) (SeqSeqInt.len b))))
(define-fun SeqSeqInt.sub ((s SeqSeqInt) (lo Int) (hi Int)) SeqSeqInt (SeqSeqInt.mk (lambda ((j Int)) (select (SeqSeqInt.at s) (+ lo j))) (- hi lo)))
(declare-const c12 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Body
(define-fun t13 () Int (select (SeqInt.at (select (SeqSeqInt.at c12) c9)) (+ c10 64)))
(define-fun t14 () Int (select (SeqInt.at c11) t13))
(assert (and (<= 0 t14) (< t14 c8) (< 0 (select (SeqInt.at c11) t13))))
(declare-const c15 Err) ; get@1
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
(declare-const c16 SeqSeqBool) ; mem iface state
(assert (=> true (=> (= c15 nil) (and (not (= c9 0)) (not (= t13 0)) (not (select (SeqBool.at (select (SeqSeqBool.at c16) (select (SeqInt.at c11) (select (SeqInt.at (select (SeqSeqInt.at c12) c9)) (+ c10 64))))) (+ 2997695091990504928268101341469504234022244 0))) (<= 1 (select (SeqInt.at c11) (select (SeqInt.at (select (SeqSeqInt.at c12) c9)) (+ c10 64))))))))
(declare-datatype SeqSeqSeqInt ((SeqSeqSeqInt.mk (SeqSeqSeqInt.at (Array Int SeqSeqInt)) (SeqSeqSeqInt.raw Int))))
(define-fun SeqSeqSeqInt.len ((s SeqSeqSeqInt)) Int (ite (< (SeqSeqSeqInt.raw s) 0) 0 (SeqSeqSeqInt.raw s)))
(define-fun SeqSeqSeqInt.store ((s SeqSeqSeqInt) (i Int) (v SeqSeqInt)) SeqSeqSeqInt (SeqSeqSeqInt.mk (store (SeqSeqSeqInt.at s) i v) (SeqSeqSeqInt.raw s)))
(define-fun SeqSeqSeqInt.fill ((n Int) (v SeqSeqInt)) SeqSeqSeqInt (SeqSeqSeqInt.mk ((as const (Array Int SeqSeqInt)) v) n))
(define-fun SeqSeqSeqInt.push ((s SeqSeqSeqInt) (v SeqSeqInt)) SeqSeqSeqInt (SeqSeqSeqInt.mk (store (SeqSeqSeqInt.at s) (SeqSeqSeqInt.len s) v) (+ (SeqSeqSeqInt.len s) 1)))
(define-fun SeqSeqSeqInt.concat ((a SeqSeqSeqInt) (b SeqSeqSeqInt)) SeqSeqSeqInt (SeqSeqSeqInt.mk (lambda ((j Int)) (ite (< j (SeqSeqSeqInt.len a)) (select (SeqSeqSeqInt.at a) j) (select (SeqSeqSeqInt.at b) (- j (SeqSeqSeqInt.len a))))) (+ (SeqSeqSeqInt.len a) (SeqSeqSeqInt.len b))))
(define-fun SeqSeqSeqInt.sub ((s SeqSeqSeqInt) (lo Int) (hi Int)) SeqSeqSeqInt (SeqSeqSeqInt.mk (lambda ((j Int)) (select (SeqSeqSeqInt.at s) (+ lo j))) (- hi lo)))
(declare-const c17 SeqSeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Status
(define-fun t18 () SeqInt (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c17) c9)) (+ c10 0)))
(declare-const c19 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.StatusCode
(define-fun t20 () Int (select (SeqInt.at (select (SeqSeqInt.at c19) c9)) (+ c10 16)))
(declare-const c21 SeqSeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Proto
(define-fun t22 () SeqInt (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c21) c9)) (+ c10 24)))
(declare-const c23 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.ProtoMajor
(define-fun t24 () Int (select (SeqInt.at (select (SeqSeqInt.at c23) c9)) (+ c10 40)))
(declare-const c25 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.ProtoMinor
(define-fun t26 () Int (select (SeqInt.at (select (SeqSeqInt.at c25) c9)) (+ c10 48)))
(declare-const c27 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Header
(define-fun t28 () Int (select (SeqInt.at (select (SeqSeqInt.at c27) c9)) (+ c10 56)))
(define-fun t29 () Int (select (SeqInt.at (select (SeqSeqInt.at c12) c9)) (+ c10 64)))
(define-fun t30 () Int (select (SeqInt.at c11) t29))
(declare-const c31 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.ContentLength
(define-fun t32 () Int (select (SeqInt.at (select (SeqSeqInt.at c31) c9)) (+ c10 80)))
(declare-const c33 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#ref
(define-fun t34 () Int (select (SeqInt.at (select (SeqSeqInt.at c33) c9)) (+ c10 88)))
(declare-const c35 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#off
(define-fun t36 () Int (select (SeqInt.at (select (SeqSeqInt.at c35) c9)) (+ c10 88)))
(declare-const c37 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#len
(define-fun t38 () Int (select (SeqInt.at (select (SeqSeqInt.at c37) c9)) (+ c10 88)))
(declare-const c39 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#cap
(define-fun t40 () Int (select (SeqInt.at (select (SeqSeqInt.at c39) c9)) (+ c10 88)))
(declare-const c41 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Trailer
(define-fun t42 () Int (select (SeqInt.at (select (SeqSeqInt.at c41) c9)) (+ c10 120)))
(declare-const c43 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Request#ptr
(define-fun t44 () Int (select (SeqInt.at (select (SeqSeqInt.at c43) c9)) (+ c10 128)))
(declare-const c45 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Request#at
(define-fun t46 () Int (select (SeqInt.at (select (SeqSeqInt.at c45) c9)) (+ c10 128)))
(declare-const c47 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TLS#ptr
(define-fun t48 () Int (select (SeqInt.at (select (SeqSeqInt.at c47) c9)) (+ c10 136)))
(declare-const c49 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TLS#at
(define-fun t50 () Int (select (SeqInt.at (select (SeqSeqInt.at c49) c9)) (+ c10 136)))
(declare-const c54 SeqSeqInt) ; mem map map[string][]string#1#val#ref
(declare-const c55 SeqSeqInt) ; mem map map[string][]string#1#val#off
(declare-const c56 SeqSeqInt) ; mem map map[string][]string#1#val#len
(declare-const c57 SeqSeqInt) ; mem map map[string][]string#1#val#cap
(declare-const c59 SeqSeqSeqInt) ; mem elem string#2
(assert (and (<= 0 c9) (< c9 c8) (<= 0 c10) (<= c10 281474976710656) (<= (SeqInt.len t18) 281474976710656) (<= (- 9223372036854775808) t20) (<= t20 9223372036854775807) (<= (SeqInt.len t22) 281474976710656) (<= (- 9223372036854775808) t24) (<= t24 9223372036854775807) (<= (- 9223372036854775808) t26) (<= t26 9223372036854775807) (<= 0 t28) (< t28 c8) (<= 0 t30) (< t30 c8) (< 0 (select (SeqInt.at c11) t29)) (<= (- 9223372036854775808) t32) (<= t32 9223372036854775807) (<= 0 t34) (< t34 c8) (<= 0 t36) (<= 0 t38) (<= t38 t40) (<= (+ (* t36 16) (* t40 16)) 281474976710656) (<= (- 9223372036854775808) t40) (<= t40 9223372036854775807) (<= 0 t42) (< t42 c8) (<= 0 t44) (< t44 c8) (<= 0 t46) (<= t46 281474976710656) (<= 0 t48) (< t48 c8) (<= 0 t50) (<= t50 281474976710656) (forall ((b51 Int)) (=> (and (<= 0 b51) (< b51 (SeqInt.len t18))) (and (<= 0 (select (SeqInt.at t18) b51)) (<= (select (SeqInt.at t18) b51) 255)))) (forall ((b52 Int)) (=> (and (<= 0 b52) (< b52 (SeqInt.len t22))) (and (<= 0 (select (SeqInt.at t22) b52)) (<= (select (SeqInt.at t22) b52) 255)))) (forall ((b53 Int)) (and (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c54) t28)) b53)) (< (select (SeqInt.at (select (SeqSeqInt.at c54) t28)) b53) c8) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c55) t28)) b53)) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c56) t28)) b53)) (<= (select (SeqInt.at (select (SeqSeqInt.at c56) t28)) b53) (select (SeqInt.at (select (SeqSeqInt.at c57) t28)) b53)) (<= (+ (* (select (SeqInt.at (select (SeqSeqInt.at c55) t28)) b53) 16) (* (select (SeqInt.at (select (SeqSeqInt.at c57) t28)) b53) 16)) 281474976710656) (<= (- 9223372036854775808) (select (SeqInt.at (select (SeqSeqInt.at c57) t28)) b53)) (<= (select (SeqInt.at (select (SeqSeqInt.at c57) t28)) b53) 9223372036854775807))) (and (forall ((b58 Int)) (=> (and (<= 0 b58) (< b58 t38)) (<= (SeqInt.len (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c59) t34)) (+ (+ t36 (* b58 1)) 0))) 281474976710656))) (forall ((b61 Int)) (! (=> (and (<= 0 (+ b61 (- (+ t36 0)))) (< (+ b61 (- (+ t36 0))) t38)) (<= (SeqInt.len (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c59) t34)) b61)) 281474976710656)) :pattern ((select (SeqSeqInt.at (select (SeqSeqSeqInt.at c59) t34)) b61))))) (forall ((b62 Int)) (=> (and (<= 0 b62) (< b62 t38)) (forall ((b63 Int)) (=> (and (<= 0 b63) (< b63 (SeqInt.len (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c59) t34)) (+ (+ t36 (* b62 1)) 0))))) (and (<= 0 (select (SeqInt.at (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c59) t34)) (+ (+ t36 (* b62 1)) 0))) b63)) (<= (select (SeqInt.at (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c59) t34)) (+ (+ t36 (* b62 1)) 0))) b63) 255)))))) (forall ((b64 Int)) (and (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c54) t42)) b64)) (< (select (SeqInt.at (select (SeqSeqInt.at c54) t42)) b64) c8) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c55) t42)) b64)) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c56) t42)) b64)) (<= (select (SeqInt.at (select (SeqSeqInt.at c56) t42)) b64) (select (SeqInt.at (select (SeqSeqInt.at c57) t42)) b64)) (<= (+ (* (select (SeqInt.at (select (SeqSeqInt.at c55) t42)) b64) 16) (* (select (SeqInt.at (select (SeqSeqInt.at c57) t42)) b64) 16)) 281474976710656) (<= (- 9223372036854775808) (select (SeqInt.at (select (SeqSeqInt.at c57) t42)) b64)) (<= (select (SeqInt.at (select (SeqSeqInt.at c57) t42)) b64) 9223372036854775807)))))
(assert true)
(assert (and (<= (SeqInt.len t7) 281474976710656) (forall ((b65 Int)) (=> (and (<= 0 b65) (< b65 (SeqInt.len t7))) (and (<= 0 0) (<= 0 255))))))
(assert (and (<= (SeqInt.len t7) 281474976710656) (forall ((b66 Int)) (=> (and (<= 0 b66) (< b66 (SeqInt.len t7))) (and (<= 0 0) (<= 0 255))))))
(check-sat-using (then simplify propagate-values ctx-simplify simplify elim-uncnstr smt))
