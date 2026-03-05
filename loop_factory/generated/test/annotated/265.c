int main1(int d){
  int kx, fc, p9d;
  kx=d-3;
  fc=kx;
  p9d=10;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == \at(d, Pre);
  loop invariant kx == d - 3;
  loop invariant fc <= kx;
  loop invariant p9d == 10 + 6*(fc - kx);
  loop invariant p9d == 10 + 6*(fc - (d - 3));
  loop invariant p9d - 6*fc == 10 - 6*(d - 3);
  loop invariant kx == \at(d, Pre) - 3;
  loop invariant fc >= \at(d, Pre) - 3;
  loop assigns p9d, fc;
*/
while (fc<kx) {
      p9d += 6;
      fc = fc + 1;
  }
}