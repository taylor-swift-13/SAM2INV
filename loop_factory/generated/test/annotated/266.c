int main1(int p,int q){
  int l, i, v, d;

  l=p;
  i=0;
  v=i;
  d=l;

  
  /*@

    loop invariant v == 0;

    loop invariant d == p;

    loop invariant l == p;

    loop invariant i >= 0;

    loop invariant l == \at(p, Pre);


    loop invariant d == l;

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant (l < 0) || (i <= l);

    loop invariant d == \at(p,Pre);

    loop invariant l == \at(p,Pre);

    loop invariant 0 <= i;

    loop assigns v, d, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v*2;
      d = d+v;
      i = i+1;
  }

}