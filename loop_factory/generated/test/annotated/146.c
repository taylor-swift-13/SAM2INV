int main1(int a,int n,int p,int q){
  int l, i, v, g, m;

  l=48;
  i=l;
  v=-1;
  g=i;
  m=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant (g + m*i) == (l*(m+1));
    loop invariant 0 <= i <= l;
    loop invariant m == l;
    loop invariant g - m*(l - i) == l;
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant a == \at(a, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i <= 48;
    loop invariant g == 2352 - 48*i;
    loop invariant l == 48;
    loop invariant m == 48;
    loop invariant g == l + m*(l - i);
    loop assigns g, i;
  */
  while (i>0) {
      g = g+m;
      i = i-1;
  }

}