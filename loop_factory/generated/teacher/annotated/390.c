int main1(int m,int n){
  int r, w, v, u;

  r=(n%8)+8;
  w=0;
  v=-5;
  u=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == (n % 8) + 8;
  loop invariant -5 <= v <= r;
  loop invariant u >= 4;
  loop invariant (u % 2 == 0);
  loop invariant 1 <= r <= 15;
  loop invariant n == \at(n, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant v <= r;
  loop invariant u > 0;
  loop invariant -5 <= v;
  loop invariant u % 4 == 0;
  loop invariant v >= -5;
  loop assigns v, u;
*/
while (v<r) {
      if (v<r) {
          v = v+1;
      }
      u = u+u;
  }

}
