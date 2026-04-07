int main1(){
  int i80, e3lu, g3, d, l5, rqds;
  i80=1;
  e3lu=0;
  g3=e3lu;
  d=-1;
  l5=i80;
  rqds=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (e3lu == 0) || (e3lu == i80);
  loop invariant e3lu <= i80;
  loop invariant (d == -1);
  loop invariant i80 == 1;
  loop invariant 0 <= e3lu;
  loop invariant l5 <= i80;
  loop invariant rqds >= l5;
  loop assigns g3, rqds, l5, e3lu;
*/
while (1) {
      if (!(e3lu < i80)) {
          break;
      }
      g3 = d;
      rqds = l5;
      l5 = l5+(g3%2);
      e3lu = i80;
  }
}