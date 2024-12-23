(defmacro while (expr &body body)
  (let ((n (gensym)))
    `(labels ((,n ()
                (if ,expr
                  (progn ,@body (,n))
                  nil)))
       (,n))))

(defmacro unless (cnd &body body)
  `(while (not ,cnd) ,@body))

(defun 1+ (n)
  (+ n 1))

(defun 1- (n)
  (- n 1))

(defun length (l)
  (labels ((len (acc l)
                (if l
                  (len (1+ acc) (cdr l))
                  acc)))
           (len 0 l)))

(defun not (e)
  (if e nil t))

(defun caar (l) (car (car l)))
(defun cadr (l) (car (cdr l)))
(defun cdar (l) (cdr (car l)))
(defun cddr (l) (cdr (cdr l)))

(defun reverse (l)
  (labels ((impl (acc l)
                 (if l
                   (impl (cons (car l) acc) (cdr l))
                   acc)))
    (impl '() l)))

(defun > (&rest l)
  (apply #'< (reverse l)))
(defun >= (&rest l)
  (apply #'<= (reverse l)))

(defun assoc (k alist)
  (labels ((searcher (k alist)
                     (if alist
                       (if (and (car alist) (eql k (caar alist)))
                         (car alist)
                         (searcher k (cdr alist)))
                       nil)))
    (searcher k alist)))

(defun max (&rest l)
  (labels ((impl (acc l)
                 (if l
                   (if (> (car l) acc)
                     (impl (car l) (cdr l))
                     (impl acc (cdr l)))
                   acc)))
    (impl (car l) (cdr l))))

(defun min (&rest l)
  (labels ((impl (acc l)
                 (if l
                   (if (< (car l) acc)
                     (impl (car l) (cdr l))
                     (impl acc (cdr l)))
                   acc)))
    (impl (car l) (cdr l))))

(defun nth (n l)
  (if (< n 0)
    nil ; TODO: raise error?
    (if (eql n 0)
      (car l)
      (nth (1- n) (cdr l)))))
