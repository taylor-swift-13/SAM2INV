int main1(int v){
  int s0, ug5p;
  s0=0;
  ug5p=-14320;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s0 == 0;
  loop invariant v == \at(v, Pre);
  loop invariant ug5p <= -14320;
  loop invariant (ug5p + 1) % 14319 == 0;
  loop assigns ug5p, v;
*/
while (ug5p+4<0) {
      ug5p = ug5p+ug5p-2;
      ug5p = ug5p + 3;
      v = v + s0;
  }
}