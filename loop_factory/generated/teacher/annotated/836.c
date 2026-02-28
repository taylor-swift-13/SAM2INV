int main1(int b,int p,int q){
  int r, j, k, t, x, v;

  r=b+18;
  j=3;
  k=q;
  t=p;
  x=p;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(p, Pre);
  loop invariant r == b + 18;
  loop invariant j >= 3;
  loop invariant x == p + (j - 3) * (2*k + v);
  loop invariant t == p*(j - 2) + 3*(j - 3) + ((2*k + v + 1) * (j - 3) * (j - 4)) / 2;
  loop invariant 2 * (t - p) == (j - 3) * (2 * (p + 3) + (j - 4) * (2 * k + v + 1));
  loop invariant k == q;
  loop invariant v == q;
  loop invariant x == p + 3*q*(j - 3);
  loop invariant t == p*(j - 2) + 3*(j - 3) + ((3*q + 1) * (j - 3) * (j - 4)) / 2;
  loop invariant x == p + 3*(j - 3)*q;
  loop assigns t, x, j;
*/
while (1) {
      t = t+x;
      x = x+k;
      t = t+j;
      x = x+v;
      x = x+k;
      j = j+1;
  }

}
