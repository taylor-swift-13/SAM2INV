int main1(int a,int m,int n,int p){
  int l, i, v, s;

  l=(m%7)+17;
  i=0;
  v=a;
  s=m;

  
  /*@

    loop invariant i >= 0;


    loop invariant i % 2 == 0;

    loop invariant v == a + i/2;

    loop invariant a == \at(a, Pre);

    loop invariant l == (m % 7) + 17;

    loop invariant 0 <= i;

    loop invariant i <= l + 1;

    loop invariant l == (\at(m,Pre) % 7) + 17;

    loop invariant a == \at(a,Pre);

    loop invariant 2*(v - \at(a, Pre)) == i;

    loop invariant l == (\at(m, Pre) % 7) + 17;

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant 2*v == 2*\at(a, Pre) + i;

    loop invariant l == m % 7 + 17;

    loop assigns i, v;

  */
  while (i<l) {
      v = v+1;
      i = i+2;
  }

}