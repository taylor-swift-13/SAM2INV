int main1(int m,int n){
  int h, x, v, f;

  h=66;
  x=2;
  v=4;
  f=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == 0;
  loop invariant h == 66;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v >= 4;
  loop invariant v % 2 == 0;
  loop invariant (v - 4) % (2 + 2*f) == 0;
  loop assigns v;
*/
while (1) {
      v = v+2;
      v = v+f+f;
  }

}
