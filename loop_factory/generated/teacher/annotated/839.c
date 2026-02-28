int main1(int m,int n,int q){
  int l, a, k, p, w;

  l=27;
  a=l;
  k=m;
  p=q;
  w=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a + 3*w == 33;
  loop invariant k - 5*w == m - 10;
  loop invariant a >= 0;
  loop invariant a <= 27;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant l == 27;
  loop invariant a % 3 == 0;
  loop invariant a == 33 - 3*w;
  loop invariant k == m + 5*w - 10;
  loop invariant k - 5*w == \at(m,Pre) - 10;
  loop invariant 0 <= a;
  loop invariant w >= 2;
  loop invariant w <= 11;
  loop assigns a, k, w;
*/
while (a>=3) {
      k = k+4;
      w = w+1;
      k = k+1;
      a = a-3;
  }

}
