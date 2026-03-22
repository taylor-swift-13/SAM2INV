int main1(){
  int i5x, dl, o, jg, t;
  i5x=1+11;
  dl=i5x;
  o=0;
  jg=i5x;
  t=i5x;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jg - (dl * (o / 2)) == 12;
  loop invariant o % 2 == 0;
  loop invariant jg == i5x + dl * (o/2);
  loop invariant 0 <= t;
  loop invariant t <= i5x;
  loop invariant jg == i5x + 6*o;
  loop invariant 0 <= o <= i5x;
  loop assigns o, t, jg;
*/
while (o<=i5x-1) {
      o += 2;
      if (o<=t) {
          t = o;
      }
      jg += dl;
  }
}