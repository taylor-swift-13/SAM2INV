int main1(int m,int n){
  int l, i, v;

  l=n;
  i=0;
  v=m;

  
  /*@

    loop invariant l == \at(n, Pre);


    loop invariant (i == 0) ==> (v == \at(m, Pre));

    loop invariant (i >= 2) ==> (v == 0 || v == 1);

    loop invariant (i == 0) ==> (v == m);


    loop invariant i >= 0;

    loop invariant l == n;

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant (i > 0) ==> (v == 0 || v == 1 || v == 4 || v == 9);

    loop invariant (l < 0) || (i <= l);

    loop invariant (i >= 1) ==> (v >= 0);

    loop invariant (i >= 1) ==> (v == 0 || v == 1 || v == 4 || v == 9);

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v%4;
      v = v*v;
      i = i+1;
  }

}