int main1(int a,int m,int n,int q){
  int l, i, v;

  l=(m%40)+14;
  i=0;
  v=m;

  
  /*@

    loop invariant 0 <= i;



    loop invariant m == \at(m, Pre);

    loop invariant a == \at(a, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant i >= 0;

    loop invariant l == (m % 40) + 14;

    loop invariant (i > 0) ==> (v % 2 == 0);

    loop invariant m == \at(m,Pre);

    loop invariant l == (\at(m,Pre) % 40) + 14;

    loop invariant a == \at(a,Pre);

    loop invariant (l >= 0) ==> (i <= l);

    loop invariant (i == 0) ==> (v == \at(m, Pre));

    loop invariant n == \at(n,Pre);

    loop invariant q == \at(q,Pre);

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v+v;
      i = i+1;
  }

}