int main1(int n,int p){
  int h, k, v;

  h=(n%33)+20;
  k=0;
  v=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == (\at(n,Pre) % 33) + 20 && n == \at(n,Pre) && p == \at(p,Pre);
  loop invariant h == (\at(n, Pre) % 33) + 20;
  loop invariant n == \at(n, Pre) && p == \at(p, Pre) && v >= -4;
  loop invariant h == (\at(n,Pre) % 33) + 20;
  loop invariant v >= -4;
  loop invariant n == \at(n,Pre);
  loop invariant p == \at(p,Pre);
  loop invariant v >= -4 && v % 4 == 0;
  loop invariant v >= -4 && v % 2 == 0;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (v + 8) % 4 == 0;
  loop invariant v % 4 == 0;
  loop invariant h == \at(n, Pre) % 33 + 20 && n == \at(n, Pre) && p == \at(p, Pre);
  loop invariant v % 4 == 0 && v >= -8;
  loop assigns v;
*/
while (1) {
      v = v+4;
      v = v*2;
  }

}
