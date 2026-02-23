int main1(int m,int n){
  int r, w, v, u;

  r=(n%8)+8;
  w=0;
  v=-5;
  u=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == -5 + (2*u + 1) * w;
  loop invariant 0 <= w;
  loop invariant w <= r;
  loop invariant r == (n % 8) + 8;
  loop invariant u == 4;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v == -5 + w * (2 * u + 1);
  loop invariant v == -5 + 9*w;
  loop invariant w >= 0;
  loop assigns v, w;
*/
while (w<=r-1) {
      v = v+u+u;
      v = v+1;
      w = w+1;
  }

}
