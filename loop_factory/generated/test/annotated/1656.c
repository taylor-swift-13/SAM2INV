int main1(){
  int w, ve, udy, n5;
  w=5;
  ve=0;
  udy=0;
  n5=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant udy == ve * (ve + 1) / 2;
  loop invariant n5 == w * ve - (ve * (ve + 1)) / 2;
  loop invariant ve >= 0;
  loop invariant ve <= w;
  loop assigns ve, udy, n5;
*/
while (1) {
      if (!(ve < w)) {
          break;
      }
      ve = ve + 1;
      udy = udy + ve;
      n5 = n5 + (w - ve);
  }
}