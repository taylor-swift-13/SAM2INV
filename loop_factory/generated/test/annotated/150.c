int main1(int a,int m,int n,int p){
  int l, i, v, u, q;

  l=a+7;
  i=0;
  v=a;
  u=3;
  q=5;

  
  /*@

    loop invariant i >= 0;


    loop invariant l == a + 7;

    loop invariant a == \at(a, Pre);



    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant (l < 0) || (i <= l);

    loop invariant (i == 0) ==> (v == a && u == 3 && q == 5);

    loop invariant a == \at(a,Pre);

    loop invariant m == \at(m,Pre);

    loop invariant n == \at(n,Pre);

    loop invariant p == \at(p,Pre);

    loop invariant a == \at(a, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre);

    loop assigns i, v, u, q;

  */
  while (i<l) {
      v = v+1;
      u = u+v;
      q = q+u;
      v = v+q;
      u = q-u;
      i = i+1;
  }

}