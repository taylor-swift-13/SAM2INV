int main1(int a,int k,int m,int n){
  int l, i, v, f, e;

  l=64;
  i=0;
  v=n;
  f=k;
  e=4;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant v == n + i*(k + 5);

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant v == n + i*(f + e + 1);

    loop invariant f == k;

    loop invariant l == 64;

    loop invariant v == n + i*(k+5);

    loop invariant 0 <= i <= l;

    loop invariant v == \at(n, Pre) + i*(k + 5);

    loop invariant e == 4;

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+f+e;
      v = v+1;
      i = i+1;
  }

}