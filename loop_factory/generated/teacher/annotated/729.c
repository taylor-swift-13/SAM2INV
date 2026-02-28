int main1(int b,int n,int p,int q){
  int r, u, x, i, h;

  r=(n%28)+9;
  u=3;
  x=q;
  i=u;
  h=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x - u*(n + 4) == q - 3*(n + 4);
  loop invariant u >= 3;
  loop invariant i == 3;
  loop invariant h == n;

  loop invariant x == q + (u - 3) * (n + 4);
  loop invariant r == (n % 28) + 9;
  loop invariant x == q + (u - 3) * (i + h + 1);
  loop invariant q == \at(q, Pre);

  loop invariant x - (i + h + 1) * u == q - (i + h + 1) * 3;
  loop invariant x - q == (i + h + 1) * (u - 3);
  loop assigns x, u;
*/
while (1) {
      x = x+i+h;
      x = x+1;
      u = u+1;
  }

}
