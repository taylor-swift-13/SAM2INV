int main1(){
  int ox, cqzo, t8a, pr;
  ox=12;
  cqzo=ox;
  t8a=0;
  pr=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= t8a);
  loop invariant (t8a <= ox);
  loop invariant (0 <= pr);
  loop invariant (pr <= ox + cqzo);
  loop invariant (t8a == 0 ==> pr == 0) && (t8a > 0 ==> pr + t8a == cqzo + ox);
  loop invariant cqzo == ox;
  loop assigns t8a, pr;
*/
while (1) {
      if (!(t8a<ox)) {
          break;
      }
      t8a += 1;
      pr = ox-t8a;
      pr = pr + cqzo;
  }
}