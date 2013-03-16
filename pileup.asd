;;;; Copyright (c) 2010-2013 Nikodemus Siivola <nikodemus@random-state.net>
;;;;
;;;; Permission is hereby granted, free of charge, to any person obtaining
;;;; a copy of this software and associated documentation files (the
;;;; "Software"), to deal in the Software without restriction, including
;;;; without limitation the rights to use, copy, modify, merge, publish,
;;;; distribute, sublicense, and/or sell copies of the Software, and to
;;;; permit persons to whom the Software is furnished to do so, subject to
;;;; the following conditions:
;;;;
;;;; The above copyright notice and this permission notice shall be included
;;;; in all copies or substantial portions of the Software.
;;;;
;;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;;;; IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
;;;; CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
;;;; TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
;;;; SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

(defsystem :pileup
  :depends-on (:alexandria #-sbcl :bordeaux-threads)
  :description
  "A portable, performant, and thread-safe binary heap / priority queue."
  :licence "MIT"
  :version "1.0"
  :author "Nikodemus Siivola <nikodemus@random-state.net>"
  :serial t
  :components ((:file "package")
               (:file "pileup")
               (:static-file "README")
               (:static-file "LICENCE")))

(defsystem :pileup-tests
  :depends-on (:pileup :hu.dwim.stefil)
  :components ((:file "tests")))

(defmethod perform ((o test-op) (c (eql (find-system :pileup))))
  (load-system :pileup-tests)
  (funcall (intern (string '#:test-pileup) :pileup-tests)))
