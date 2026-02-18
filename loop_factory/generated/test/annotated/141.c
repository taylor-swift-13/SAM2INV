int main1(int b,int m,int n,int p){
  int l, i, v, g;

  l=80;
  i=0;
  v=b;
  g=-3;

  
  /*@

    loop invariant i <= l;

    loop invariant 0 <= i;

    loop invariant l == 80;

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant 0 <= i <= l;

    loop invariant n == \at(n,Pre);

    loop invariant b == \at(b,Pre);

    loop invariant m == \at(m,Pre);

    loop invariant p == \at(p,Pre);

    loop invariant (i == 0) ==> (v == b);

    loop invariant (i == 0) ==> (g == -3);

    loop assigns v, g, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+g+g;
      v = v+1;
      g = n-5;
      v = v+g;
      if (g+1<l) {
          g = g+v;
      }
      i = i+1;
  }

}