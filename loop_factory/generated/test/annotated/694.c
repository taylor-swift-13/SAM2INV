int main1(){
  int v, f5j, hi, cq, i, wse, yk;
  v=1+17;
  f5j=0;
  hi=4;
  cq=4;
  i=0;
  wse=5;
  yk=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yk == f5j;
  loop invariant 0 <= f5j <= v;
  loop invariant 0 <= hi <= wse;
  loop invariant 0 <= i <= (f5j + 2) / 3;
  loop invariant v == 18;
  loop invariant wse == 5;
  loop invariant cq >= 4;
  loop assigns hi, i, cq, f5j, yk;
*/
while (f5j<v) {
      if (!(!(f5j%3==0))) {
          if (hi>0) {
              hi = hi - 1;
              i = i + 1;
          }
      }
      else {
          if (hi<wse) {
              hi += 1;
              cq += 1;
          }
      }
      f5j = f5j + 1;
      yk = yk + 1;
  }
}