int main1(int a){
  int z0, qro, p9x2, mzj;
  z0=62;
  qro=0;
  p9x2=-3;
  mzj=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p9x2 == -3;
  loop invariant 0 <= qro;
  loop invariant qro <= z0;
  loop invariant (qro % 2) == 0;
  loop invariant z0 == 62;
  loop invariant a == \at(a, Pre);
  loop invariant mzj == -4;
  loop assigns qro, mzj, p9x2;
*/
while (qro<z0) {
      qro += 2;
      if (!(!(qro<=mzj))) {
          mzj = qro;
      }
      p9x2 = p9x2+mzj-mzj;
  }
}