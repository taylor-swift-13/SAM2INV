int main1(int y){
  int x, sohf, a, r, k9x1, sg9, ot, jaq;
  x=y;
  sohf=x;
  a=3;
  r=3;
  k9x1=0;
  sg9=7;
  ot=0;
  jaq=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ot == sohf - x;
  loop invariant 0 <= a;
  loop invariant a <= sg9;
  loop invariant sohf == \at(y,Pre) + ot;
  loop invariant sg9 == 7 + ot*(ot+1)/2;
  loop invariant x == \at(y,Pre);
  loop invariant 0 <= ot;
  loop invariant 0 <= k9x1;
  loop invariant sg9 == jaq + 4;
  loop invariant sohf <= x;
  loop invariant (0 <= k9x1 && k9x1 <= ot);
  loop invariant (r >= 3 && (r - 3) <= ot);
  loop invariant (y >= \at(y, Pre));
  loop invariant a + k9x1 - r == 0;
  loop assigns a, k9x1, r, sg9, sohf, ot, jaq, y;
*/
while (sohf<x) {
      if (!(!(sohf%3==0))) {
          if (a>0) {
              a -= 1;
              k9x1 = k9x1 + 1;
          }
      }
      else {
          if (a<sg9) {
              a++;
              r = r + 1;
          }
      }
      sohf = sohf + 1;
      ot += 1;
      y = y + a;
      jaq = jaq + ot;
      sg9 = sg9 + ot;
  }
}