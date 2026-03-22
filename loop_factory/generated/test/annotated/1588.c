int main1(){
  int nm, x2, is, k, jl, bdk4, yl, ybdg;
  nm=137;
  x2=0;
  is=0;
  k=x2;
  jl=-5;
  bdk4=nm;
  yl=0;
  ybdg=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant is % 2 == 0;
  loop invariant ybdg == k*k*k;
  loop invariant jl == -5;
  loop invariant 0 <= is;
  loop invariant is <= nm + 1;
  loop invariant k == yl + x2;
  loop invariant yl % 3 == 0;
  loop invariant nm == 137;
  loop invariant x2 == 0;
  loop invariant bdk4 >= 137;
  loop invariant yl >= 0;
  loop invariant k >= 0;
  loop assigns is, jl, k, bdk4, yl, ybdg;
*/
while (1) {
      if (!(is<=nm-1)) {
          break;
      }
      is += 2;
      if (bdk4<=jl) {
          jl = bdk4;
      }
      if (x2*x2<=nm+6) {
          ybdg = ybdg*bdk4;
      }
      k = k+(jl%7);
      k = k + bdk4;
      bdk4 = bdk4 + yl;
      bdk4 = bdk4*2;
      yl = yl + 3;
      k = yl+x2;
      ybdg = k*k;
      ybdg = ybdg*k;
  }
}