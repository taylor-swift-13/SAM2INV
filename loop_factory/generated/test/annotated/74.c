int main1(int b,int n,int p,int q){
  int l, i, v, y;

  l=54;
  i=0;
  v=l;
  y=p;

  
  /*@

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant y == p + 4*i;

    loop invariant v == 54 + i*p + 2*i*i + 5*i;

    loop invariant v == l + i*p + 2*i*i + 5*i;

    loop invariant b == \at(b, Pre) && n == \at(n, Pre) && p == \at(p, Pre) && q == \at(q, Pre);

    loop invariant 0 <= i;

    loop invariant v == 54 + p*i + 2*i*i + 5*i;

    loop invariant p == \at(p, Pre);

    loop invariant l == 54;

    loop invariant b == \at(b, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant q == \at(q, Pre);


    loop assigns v, y, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+3;
      y = y+4;
      v = v+y;
      i = i+1;
  }

}