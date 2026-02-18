int main1(int a,int b,int n,int q){
  int l, i, v, k, x;

  l=n+18;
  i=0;
  v=a;
  k=i;
  x=l;

  
  /*@

    loop invariant v == a + i;

    loop invariant k == i*a + i*(i+1)/2;

    loop invariant 0 <= i;

    loop invariant (i <= l) || (l < 0);

    loop invariant l == n + 18;

    loop invariant k == i * a + (i * (i + 1)) / 2;


    loop invariant a == \at(a,Pre);

    loop invariant l == \at(n,Pre) + 18;


    loop invariant k == i*(a+1) + i*(i-1)/2;

    loop invariant a == \at(a, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant l == \at(n, Pre) + 18;

    loop invariant b == \at(b, Pre);

    loop invariant q == \at(q, Pre);

    loop assigns v, k, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+1;
      k = k+v;
      i = i+1;
  }

}