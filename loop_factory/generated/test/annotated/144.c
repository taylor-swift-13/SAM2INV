int main1(int a,int k,int n,int p){
  int l, i, v, g;

  l=54;
  i=0;
  v=-2;
  g=n;

  
  /*@

    loop invariant i <= l;

    loop invariant v == i - 2;

    loop invariant g == n - i;

    loop invariant l == 54;

    loop invariant n == \at(n, Pre);

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant v == -2 + i;

    loop invariant a == \at(a, Pre) && k == \at(k, Pre) && n == \at(n, Pre) && p == \at(p, Pre);

    loop invariant i >= 0;

    loop invariant 0 <= i && i <= l;

    loop assigns v, g, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+1;
      g = g-1;
      i = i+1;
  }

}