int main1(int k,int m){
  int l, j, t, n;

  l=47;
  j=l;
  t=0;
  n=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n <= l && m == \at(m, Pre) && l == 47;
  loop invariant t == k * n;
  loop invariant n <= l;
  loop invariant n >= 0;
  loop invariant l == 47;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant t == n * k;
  loop invariant 0 <= n;
  loop invariant 0 <= n && n <= l;
  loop invariant k == \at(k, Pre) && m == \at(m, Pre);
  loop assigns t, n;
*/
while (n<l) {
      t = t+k;
      n = n+1;
  }

}
