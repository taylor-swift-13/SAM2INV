int main1(int b,int n,int p,int q){
  int l, i, v, y;

  l=54;
  i=0;
  v=l;
  y=p;

  
  /*@


    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant l == 54;

    loop invariant (i > 0) ==> (v == n);

    loop invariant b == \at(b, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant y == p + i * (n + 4);

    loop invariant 0 <= i && i <= l;

    loop invariant y == p + i*(4 + n);

    loop invariant (i == 0) ==> (v == 54);

    loop invariant 0 <= i <= l;

    loop invariant y == \at(p,Pre) + i*(n + 4);

    loop invariant b == \at(b,Pre);

    loop invariant n == \at(n,Pre);

    loop invariant p == \at(p,Pre);

    loop invariant q == \at(q,Pre);

    loop assigns v, y, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+3;
      y = y+4;
      if (i+2<=b+l) {
          v = v+i;
      }
      else {
          v = y-v;
      }
      v = n;
      y = y+v;
      i = i+1;
  }

}