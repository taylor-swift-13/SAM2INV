int main1(){
  int t3, el, i, u;
  t3=1;
  el=0;
  i=0;
  u=t3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == el;
  loop invariant t3 == 1;
  loop invariant u >= 2*i + 1;
  loop invariant 0 <= i <= t3;
  loop invariant el >= 0;
  loop assigns i, el, u;
*/
while (1) {
      if (!(i<t3)) {
          break;
      }
      i = i + 1;
      el += 1;
      u = u + el;
      u = u*2;
  }
}