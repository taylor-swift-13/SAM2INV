int main1(int a,int m,int n,int q){
  int b, u, w;

  b=m+12;
  u=0;
  w=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == m || w == n - a;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant b == m + 12;
  loop invariant (w == m) || (w == n - a);
  loop invariant q == \at(q, Pre);
  loop assigns w;
*/
while (1) {
      w = w+3;
      w = n-a;
  }

}
