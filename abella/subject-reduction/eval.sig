sig eval.

kind tm, ty   type.
type i        ty.
type arrow    ty -> ty -> ty.

type app      tm -> tm -> tm.
type abs      (tm -> tm) -> tm.

type eval     tm -> tm -> o.
type typeof       tm -> ty -> o.
