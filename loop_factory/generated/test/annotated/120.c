int main1(int a,int n,int p,int q){
  int l, i, v, y, z;

  l=13;
  i=0;
  v=l;
  y=a;
  z=6;

  
  /*@

    loop invariant v == l + i*(i - 1)/2;

    loop invariant i <= l;

    loop invariant a == \at(a, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant v == 13 + i*(i-1)/2;

    loop invariant q == \at(q, Pre);

    loop invariant v == l + i*(i-1)/2;

    loop invariant 0 <= i && i <= l;

    loop invariant l == 13;

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+i;
      i = i+1;
  }

}