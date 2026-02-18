int main1(int p,int q){
  int l, i, v, w, r;

  l=50;
  i=l;
  v=i;
  w=l;
  r=i;

  
  /*@

    loop invariant l == 50;

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant i >= 0;

    loop invariant i <= 50;

    loop invariant v % 50 == 0;

    loop invariant v >= 50;

    loop invariant i * v <= 2500;

    loop invariant i <= l;

    loop invariant v >= i;

    loop invariant v >= l;

    loop invariant v >= 0;

    loop invariant i * v <= l * l;

    loop assigns i, v;

    loop variant i;

  */
  while (i>0) {
      v = v*2;
      i = i/2;
  }

}