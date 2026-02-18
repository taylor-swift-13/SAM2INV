int main1(int b,int m,int p,int q){
  int l, i, v;

  l=52;
  i=1;
  v=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 52;
    loop invariant i <= 2 * l;
    loop invariant v >= -1;
    loop invariant b == \at(b, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i > 0;

    loop invariant v <= v*v;
    loop invariant (i == 1) ==> (v == -1);
    loop invariant (i != 1) ==> (v >= 0);
    loop invariant i >= 1;
    loop invariant v != 0;
    loop assigns i, v;
  */
  while (i<l) {
      v = v*v;
      v = v*v+v;
      i = i*2;
  }

}