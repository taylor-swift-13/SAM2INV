int main1(){
  int hm, a36, bn, n, f26;
  hm=1+21;
  a36=0;
  bn=0;
  n=25;
  f26=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bn == f26;
  loop invariant (f26 == 0) || (f26 == 1);
  loop invariant n == 25;
  loop invariant hm == 22;
  loop invariant ((a36 == 0) <==> (bn == 0 && f26 == 0));
  loop invariant (a36 == hm*hm) || (f26 == 0);
  loop invariant ((a36 == 0 && bn == 0 && f26 == 0)
                    || (a36 == (hm*hm) && (bn == 0 || bn == 1) && (f26 == 0 || f26 == 1)));
  loop assigns f26, bn, a36, n;
*/
while (1) {
      if (!(a36 < hm*hm)) {
          break;
      }
      f26 = f26 + (a36++, (bn = 1 - bn), bn);
      bn = bn+f26-f26;
      n = n+f26-f26;
      a36 = hm*hm;
  }
}