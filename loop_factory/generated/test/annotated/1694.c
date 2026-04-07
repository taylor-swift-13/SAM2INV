int main1(){
  int x, x0l, wsa, qs8;
  x=1+14;
  x0l=0;
  wsa=0;
  qs8=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qs8 == x * x0l;
  loop invariant 0 <= x0l <= x;
  loop invariant wsa == (x0l > 0);
  loop assigns x0l, wsa, qs8;
*/
while (x0l < x) {
      x0l = x0l + 1;
      if (!(wsa!=0)) {
          wsa = 1;
      }
      qs8 += x;
  }
}