int main1(int n,int p){
  int t, i, w;

  t=n-4;
  i=t+1;
  w=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == n - 3;
  loop invariant t == n - 4;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant w >= n;
  loop invariant i == (\at(n,Pre) - 3);
  loop invariant t == (\at(n,Pre) - 4);
  loop invariant n == \at(n,Pre);
  loop invariant p == \at(p,Pre);
  loop invariant w >= \at(n,Pre);
  loop invariant i == t + 1 && w >= n && w > i && n == \at(n, Pre) && p == \at(p, Pre);
  loop invariant i == \at(n, Pre) - 3;
  loop invariant t == \at(n, Pre) - 4;
  loop invariant w >= \at(n, Pre);
  loop invariant i == t + 1;
  loop invariant w - i >= 3;
  loop invariant i == \at(n,Pre) - 3;
  loop invariant t == \at(n,Pre) - 4;
  loop invariant w >= i + 3;

  loop invariant i <= n;
  loop assigns w;
*/
while (i>=1) {
      w = w+2;
      w = w*w+w;
  }

}
