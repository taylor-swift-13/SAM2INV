int main1(int a,int m,int n){
  int l, i, v, h, u, o, j, z, p;

  l=43;
  i=1;
  v=4;
  h=-6;
  u=l;
  o=8;
  j=a;
  z=i;
  p=a;

  
  /*@

    loop invariant a == \at(a, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant l == 43;

    loop invariant i > 0;

    loop invariant v > 0;

    loop invariant v % 4 == 0;

    loop invariant i <= 3 * l;

    loop assigns i, v;

    loop variant 3 * l - i;

  */
  while (i<l) {
      v = v*4;
      i = i*3;
  }

}