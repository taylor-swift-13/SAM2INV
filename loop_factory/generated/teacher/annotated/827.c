int main1(int k,int n,int q){
  int r, u, t, j, d;

  r=k+4;
  u=3;
  t=n;
  j=-5;
  d=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == n + (((j+5)*(j+6)*(2*(j+5)+1))/6) - 5*(j+5)*(j+6) + 28*(j+5);
  loop invariant j >= -5;
  loop invariant t >= n;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant r == k + 4;
  loop invariant t - n == ((j + 5) * (2 * j * j - 7 * j + 54)) / 6;

  loop invariant t >= \at(n, Pre);
  loop invariant t >= n + 3*(j + 5);
  loop invariant -5 <= j;
  loop invariant t >= n + 3*j + 15;
  loop assigns j, t;
*/
while (1) {
      j = j+1;
      t = t+j*j;
      t = t+3;
  }

}
