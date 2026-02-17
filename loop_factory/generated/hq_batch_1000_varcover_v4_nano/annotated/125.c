int main1(int a,int k,int n){
  int l, i, v, j, d, e, y, f;

  l=73;
  i=0;
  v=5;
  j=l;
  d=n;
  e=k;
  y=i;
  f=n;

  
  /*@

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant 0 <= i;

    loop invariant i % 3 == 0;

    loop invariant v % 5 == 0;

    loop invariant i <= l + 2;

    loop invariant v >= 5;

    loop assigns i, v;

  */
while (i<l) {
      v = v*2;
      i = i+3;
  }

}