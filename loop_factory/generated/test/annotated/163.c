int main1(int a,int m,int n,int q){
  int l, i, v, u, e;

  l=14;
  i=l;
  v=i;
  u=a;
  e=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 28 - i;
    loop invariant u == a + (14 - i) * (14 + m) + (14 - i) * ((14 - i) + 1) / 2;
    loop invariant i >= 0;
    loop invariant i <= 14;
    loop invariant a == \at(a, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant u == a + (14 - i) * (14 + m) + ((14 - i) * (15 - i)) / 2;
    loop invariant n == \at(n, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i + v == 28;

    loop invariant u == a + (l - i) * (l + 1 + m) + ((l - i) * (l - i - 1)) / 2;
    loop invariant i <= l;
    loop invariant v + i == 28;
    loop invariant u == a + (14 - i) * m + 14 * (14 - i) + ((14 - i) * (15 - i)) / 2;
    loop assigns v, u, i;
  */
  while (i>0) {
      v = v+1;
      u = u+v;
      u = u+m;
      i = i-1;
  }

}