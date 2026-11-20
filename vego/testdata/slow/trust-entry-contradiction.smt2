; The contradiction check of the trust entry of get (trust.go checkTrusted), at 35dca07: unknown at the limit, 4,001,702 units, 11 s. Without its quantified facts it is sat in 6,843 units.
(set-option :rlimit 4000000)
(declare-const c1 Int) ; brk
(assert (<= 1 c1))
(declare-datatype SeqInt ((SeqInt.mk (SeqInt.at (Array Int Int)) (SeqInt.raw Int))))
(define-fun SeqInt.len ((s SeqInt)) Int (ite (< (SeqInt.raw s) 0) 0 (SeqInt.raw s)))
(define-fun SeqInt.store ((s SeqInt) (i Int) (v Int)) SeqInt (SeqInt.mk (store (SeqInt.at s) i v) (SeqInt.raw s)))
(define-fun SeqInt.fill ((n Int) (v Int)) SeqInt (SeqInt.mk ((as const (Array Int Int)) v) n))
(define-fun SeqInt.push ((s SeqInt) (v Int)) SeqInt (SeqInt.mk (store (SeqInt.at s) (SeqInt.len s) v) (+ (SeqInt.len s) 1)))
(define-fun SeqInt.concat ((a SeqInt) (b SeqInt)) SeqInt (SeqInt.mk (lambda ((j Int)) (ite (< j (SeqInt.len a)) (select (SeqInt.at a) j) (select (SeqInt.at b) (- j (SeqInt.len a))))) (+ (SeqInt.len a) (SeqInt.len b))))
(define-fun SeqInt.sub ((s SeqInt) (lo Int) (hi Int)) SeqInt (SeqInt.mk (lambda ((j Int)) (select (SeqInt.at s) (+ lo j))) (- hi lo)))
(declare-const c2 SeqInt) ; $url
(assert (<= (SeqInt.len c2) 281474976710656))
(declare-const c3 Int) ; brk@1
(assert (<= c1 c3))
(declare-const c4 Int) ; out#ptr@1
(declare-const c5 Int) ; out#at@1
(assert (and (<= 0 c4) (< c4 c3) (<= 0 c5) (<= c5 281474976710656)))
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
(declare-const c6 SeqSeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Status
(define-fun t7 () SeqInt (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c6) c4)) (+ c5 0)))
(declare-const c8 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.StatusCode
(define-fun t9 () Int (select (SeqInt.at (select (SeqSeqInt.at c8) c4)) (+ c5 16)))
(declare-const c10 SeqSeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Proto
(define-fun t11 () SeqInt (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c10) c4)) (+ c5 24)))
(declare-const c12 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.ProtoMajor
(define-fun t13 () Int (select (SeqInt.at (select (SeqSeqInt.at c12) c4)) (+ c5 40)))
(declare-const c14 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.ProtoMinor
(define-fun t15 () Int (select (SeqInt.at (select (SeqSeqInt.at c14) c4)) (+ c5 48)))
(declare-const c16 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Header
(define-fun t17 () Int (select (SeqInt.at (select (SeqSeqInt.at c16) c4)) (+ c5 56)))
(declare-const c18 SeqInt) ; home
(declare-const c19 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Body
(define-fun t20 () Int (select (SeqInt.at (select (SeqSeqInt.at c19) c4)) (+ c5 64)))
(define-fun t21 () Int (select (SeqInt.at c18) t20))
(declare-const c22 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.ContentLength
(define-fun t23 () Int (select (SeqInt.at (select (SeqSeqInt.at c22) c4)) (+ c5 80)))
(declare-const c24 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#ref
(define-fun t25 () Int (select (SeqInt.at (select (SeqSeqInt.at c24) c4)) (+ c5 88)))
(declare-const c26 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#off
(define-fun t27 () Int (select (SeqInt.at (select (SeqSeqInt.at c26) c4)) (+ c5 88)))
(declare-const c28 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#len
(define-fun t29 () Int (select (SeqInt.at (select (SeqSeqInt.at c28) c4)) (+ c5 88)))
(declare-const c30 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#cap
(define-fun t31 () Int (select (SeqInt.at (select (SeqSeqInt.at c30) c4)) (+ c5 88)))
(declare-const c32 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Trailer
(define-fun t33 () Int (select (SeqInt.at (select (SeqSeqInt.at c32) c4)) (+ c5 120)))
(declare-const c34 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Request#ptr
(define-fun t35 () Int (select (SeqInt.at (select (SeqSeqInt.at c34) c4)) (+ c5 128)))
(declare-const c36 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Request#at
(define-fun t37 () Int (select (SeqInt.at (select (SeqSeqInt.at c36) c4)) (+ c5 128)))
(declare-const c38 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TLS#ptr
(define-fun t39 () Int (select (SeqInt.at (select (SeqSeqInt.at c38) c4)) (+ c5 136)))
(declare-const c40 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TLS#at
(define-fun t41 () Int (select (SeqInt.at (select (SeqSeqInt.at c40) c4)) (+ c5 136)))
(declare-const c45 SeqSeqInt) ; mem map map[string][]string#1#val#ref
(declare-const c46 SeqSeqInt) ; mem map map[string][]string#1#val#off
(declare-const c47 SeqSeqInt) ; mem map map[string][]string#1#val#len
(declare-const c48 SeqSeqInt) ; mem map map[string][]string#1#val#cap
(declare-const c50 SeqSeqSeqInt) ; mem elem string#2
(assert (and (<= 0 c4) (< c4 c3) (<= 0 c5) (<= c5 281474976710656) (<= (SeqInt.len t7) 281474976710656) (<= (- 9223372036854775808) t9) (<= t9 9223372036854775807) (<= (SeqInt.len t11) 281474976710656) (<= (- 9223372036854775808) t13) (<= t13 9223372036854775807) (<= (- 9223372036854775808) t15) (<= t15 9223372036854775807) (<= 0 t17) (< t17 c3) (<= 0 t21) (< t21 c3) (< 0 (select (SeqInt.at c18) t20)) (<= (- 9223372036854775808) t23) (<= t23 9223372036854775807) (<= 0 t25) (< t25 c3) (<= 0 t27) (<= 0 t29) (<= t29 t31) (<= (+ (* t27 16) (* t31 16)) 281474976710656) (<= (- 9223372036854775808) t31) (<= t31 9223372036854775807) (<= 0 t33) (< t33 c3) (<= 0 t35) (< t35 c3) (<= 0 t37) (<= t37 281474976710656) (<= 0 t39) (< t39 c3) (<= 0 t41) (<= t41 281474976710656) (forall ((b42 Int)) (=> (and (<= 0 b42) (< b42 (SeqInt.len t7))) (and (<= 0 (select (SeqInt.at t7) b42)) (<= (select (SeqInt.at t7) b42) 255)))) (forall ((b43 Int)) (=> (and (<= 0 b43) (< b43 (SeqInt.len t11))) (and (<= 0 (select (SeqInt.at t11) b43)) (<= (select (SeqInt.at t11) b43) 255)))) (forall ((b44 Int)) (and (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c45) t17)) b44)) (< (select (SeqInt.at (select (SeqSeqInt.at c45) t17)) b44) c3) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c46) t17)) b44)) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c47) t17)) b44)) (<= (select (SeqInt.at (select (SeqSeqInt.at c47) t17)) b44) (select (SeqInt.at (select (SeqSeqInt.at c48) t17)) b44)) (<= (+ (* (select (SeqInt.at (select (SeqSeqInt.at c46) t17)) b44) 16) (* (select (SeqInt.at (select (SeqSeqInt.at c48) t17)) b44) 16)) 281474976710656) (<= (- 9223372036854775808) (select (SeqInt.at (select (SeqSeqInt.at c48) t17)) b44)) (<= (select (SeqInt.at (select (SeqSeqInt.at c48) t17)) b44) 9223372036854775807))) (and (forall ((b49 Int)) (=> (and (<= 0 b49) (< b49 t29)) (<= (SeqInt.len (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c50) t25)) (+ (+ t27 (* b49 1)) 0))) 281474976710656))) (forall ((b52 Int)) (! (=> (and (<= 0 (+ b52 (- (+ t27 0)))) (< (+ b52 (- (+ t27 0))) t29)) (<= (SeqInt.len (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c50) t25)) b52)) 281474976710656)) :pattern ((select (SeqSeqInt.at (select (SeqSeqSeqInt.at c50) t25)) b52))))) (forall ((b53 Int)) (=> (and (<= 0 b53) (< b53 t29)) (forall ((b54 Int)) (=> (and (<= 0 b54) (< b54 (SeqInt.len (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c50) t25)) (+ (+ t27 (* b53 1)) 0))))) (and (<= 0 (select (SeqInt.at (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c50) t25)) (+ (+ t27 (* b53 1)) 0))) b54)) (<= (select (SeqInt.at (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c50) t25)) (+ (+ t27 (* b53 1)) 0))) b54) 255)))))) (forall ((b55 Int)) (and (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c45) t33)) b55)) (< (select (SeqInt.at (select (SeqSeqInt.at c45) t33)) b55) c3) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c46) t33)) b55)) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c47) t33)) b55)) (<= (select (SeqInt.at (select (SeqSeqInt.at c47) t33)) b55) (select (SeqInt.at (select (SeqSeqInt.at c48) t33)) b55)) (<= (+ (* (select (SeqInt.at (select (SeqSeqInt.at c46) t33)) b55) 16) (* (select (SeqInt.at (select (SeqSeqInt.at c48) t33)) b55) 16)) 281474976710656) (<= (- 9223372036854775808) (select (SeqInt.at (select (SeqSeqInt.at c48) t33)) b55)) (<= (select (SeqInt.at (select (SeqSeqInt.at c48) t33)) b55) 9223372036854775807)))))
(assert (and (<= (SeqInt.len c2) 281474976710656) (forall ((b56 Int)) (=> (and (<= 0 b56) (< b56 (SeqInt.len c2))) (and (<= 0 (select (SeqInt.at c2) b56)) (<= (select (SeqInt.at c2) b56) 255))))))
(define-fun t57 () Int (select (SeqInt.at (select (SeqSeqInt.at c19) c4)) (+ c5 64)))
(define-fun t58 () Int (select (SeqInt.at c18) t57))
(assert (and (<= 0 t58) (< t58 c3) (< 0 (select (SeqInt.at c18) t57))))
(declare-sort Err 0)
(declare-const nil Err)
(declare-const some-error Err)
(assert (not (= some-error nil)))
(declare-fun error-is (Err Err) Bool)
(declare-const c59 Err) ; out@1
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
(declare-const c60 SeqSeqBool) ; mem iface state
(assert (=> (= c59 nil) (and (not (= c4 0)) (not (= t57 0)) (not (select (SeqBool.at (select (SeqSeqBool.at c60) (select (SeqInt.at c18) (select (SeqInt.at (select (SeqSeqInt.at c19) c4)) (+ c5 64))))) (+ 2997695091990504928268101341469504234022244 0))) (<= c1 (select (SeqInt.at c18) (select (SeqInt.at (select (SeqSeqInt.at c19) c4)) (+ c5 64)))))))
(check-sat-using (then simplify propagate-values ctx-simplify simplify elim-uncnstr smt))
