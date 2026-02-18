int main1(int a,int m,int n,int p){
  int l, i, v;

  l=33;
  i=0;
  v=l;

  
  /*@

    loop invariant a == \at(a, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant i % 3 == 0;

    loop invariant v % 2 == 1;

    loop invariant i <= l;

    loop invariant v >= 33;


    loop invariant l == 33;

    loop invariant v >= l;

    loop invariant a == \at(a, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre);

    loop invariant (v + 1) % 34 == 0;

    loop invariant 0 <= i;

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v+v;
      v = v+1;
      i = i+3;
  }

}