int main1(int b,int p,int q){
  int k, t, v;

  k=73;
  t=0;
  v=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant k == 73;
  loop invariant v >= -5;

  loop invariant (v - 1) % 3 == 0;
  loop invariant (v + 2) % 3 == 0;
  loop assigns v;
*/
while (1) {
      v = v+4;
      v = v+v;
  }

}
