int main1(int m,int n){
  int r, w, v, u;

  r=(n%8)+8;
  w=0;
  v=-5;
  u=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre) &&
                   n == \at(n, Pre) &&
                   -5 <= v &&
                   v <= r &&
                   r == (\at(n, Pre) % 8) + 8;

  loop invariant r == (\at(n,Pre) % 8) + 8;
  loop invariant v <= r;
  loop invariant v >= -5;
  loop invariant u >= 4;
  loop invariant m == \at(m,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant r == (n % 8) + 8;
  loop invariant r == (n % 8) + 8 &&
                   -5 <= v &&
                   v <= r &&
                   m == \at(m, Pre) &&
                   n == \at(n, Pre) &&
                   u >= 0;
  loop invariant r == ((\at(n, Pre) % 8) + 8);
  loop assigns v, u;
*/
while (v<r) {
      if (v<r) {
          v = v+1;
      }
      u = u+u;
      u = u+v;
  }

}
