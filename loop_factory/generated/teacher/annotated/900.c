int main1(int n,int p){
  int t, j, r, l;

  t=n;
  j=3;
  r=0;
  l=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == n;
  loop invariant r == (j - 3) * (2 * l + 1);
  loop invariant j >= 3;
  loop invariant l == \at(n, Pre) && j >= 3 && n == \at(n, Pre) && p == \at(p, Pre);
  loop invariant r == (2 * l + 1) * (j - 3);
  loop invariant l == n && j >= 3;
  loop invariant r == (2*l + 1) * (j - 3);
  loop invariant r == (j - 3) * (2*l + 1);
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant l == t;
  loop invariant l == \at(n, Pre);
  loop invariant t == n;
  loop invariant r == (j - 3) * (2 * n + 1);

  loop invariant l == n && t == n && j >= 3;
  loop assigns r, j;
*/
while (1) {
      r = r+l+l;
      r = r+1;
      j = j+1;
  }

}
