int main1(int m,int n,int p,int q){
  int l, i, v;

  l=57;
  i=l;
  v=l;

  
  /*@

    loop invariant l == 57;

    loop invariant 0 <= i <= 57;

    loop invariant 0 <= v <= 57;

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant i >= 0;

    loop invariant (v == 57) || (v == 6) || (v == 0);

    loop invariant 0 <= i;

    loop invariant v >= 0;

    loop invariant 0 <= i && i <= 57;

    loop invariant i <= 57;

    loop invariant m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre) && q == \at(q, Pre);

    loop assigns v, i;

    loop variant i;

  */
  while (i>0) {
      v = v*2;
      if (v+1<l) {
          v = v*v;
      }
      v = v%9;
      i = i-1;
  }

}