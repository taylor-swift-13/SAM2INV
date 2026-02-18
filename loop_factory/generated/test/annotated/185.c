int main1(int b,int n,int p,int q){
  int l, i, v, s;

  l=42;
  i=0;
  v=p;
  s=p;

  /*>>> LOOP INVARIANT TO FILL <<<*/
    /*@
    loop invariant 0 <= i <= l;
    loop invariant (i == 0) ==> (v == p && s == p);

    loop invariant l == 42;
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant p == \at(p,Pre);
    loop invariant n == \at(n,Pre);
    loop invariant b == \at(b,Pre);
    loop invariant q == \at(q,Pre);
    loop invariant 0 <= i && i <= l;
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop assigns i, v, s;
  */
  while (i<l) {
      v = v+2;
      s = s+v;
      s = s+s;
      v = v+s;
      if (i+2<=n+l) {
          s = s+i;
      }
      i = i+1;
  }

}