int main1(int a,int m,int n,int q){
  int l, i, v, c;

  l=17;
  i=l;
  v=m;
  c=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i && i <= 17;
    loop invariant c == i - 21;
    loop invariant v == m + 17 - i;
    loop invariant a == \at(a, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant a == \at(a, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && q == \at(q, Pre);
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant l == 17;
    loop invariant v == \at(m, Pre) + (l - i);
    loop invariant c == -4 - (l - i);
    loop invariant i <= 17;
    loop invariant v + i == m + 17;
    loop invariant q == \at(q, Pre);
    loop invariant i + v == 17 + m;
    loop invariant i + v == 17 + \at(m, Pre);
    loop invariant 0 <= i;
    loop invariant v >= \at(m, Pre);
    loop invariant c <= -4;
    loop assigns v, c, i;
  */
  while (i>0) {
      v = v+1;
      c = c-1;
      i = i-1;
  }

}