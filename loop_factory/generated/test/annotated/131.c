int main1(int a,int m,int n,int p){
  int l, i, v;

  l=55;
  i=0;
  v=n;

  
  /*@

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant l == 55;

    loop invariant a == \at(a, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant (i > 0) ==> (v >= 0);

    loop invariant v >= \at(n, Pre);

    loop invariant (i == 0) ==> (v == \at(n, Pre));

    loop invariant a == \at(a, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre);

    loop invariant (i == 0) ==> (v == n);


    loop invariant 0 <= i <= l;

    loop invariant n == \at(n,Pre);

    loop invariant a == \at(a,Pre);

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v+i;
      v = v*v+v;
      i = i+1;
  }

}