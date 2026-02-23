int main1(int m){
  int e, v, r;

  e=30;
  v=e;
  r=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v + 4*r == 34;
  loop invariant e == 30;
  loop invariant m == \at(m, Pre);
  loop invariant r <= 8;
  loop invariant v >= 2;
  loop invariant v == 34 - 4*r;
  loop invariant r >= 1;
  loop invariant v >= 0;
  loop invariant v <= e;
  loop invariant v + 4*(r - 1) == e;
  loop assigns r, v;
*/
while (v>3) {
      r = r+1;
      v = v-4;
  }

}
