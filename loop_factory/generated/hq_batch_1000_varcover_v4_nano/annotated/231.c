int main1(int n,int p,int q){
  int l, i, v, a, z, r;

  l=(p%39)+16;
  i=1;
  v=q;
  a=q;
  z=q;
  r=i;

  
  /*@

    loop invariant i > 0;

    loop invariant v == \at(q, Pre) * i * i;

    loop invariant ( \at(q, Pre) >= 0 ==> a * i * i <= \at(q, Pre) )
                   && ( \at(q, Pre) <= 0 ==> a * i * i >= \at(q, Pre) );

    loop invariant l == (\at(p, Pre) % 39) + 16;

    loop invariant p == \at(p, Pre) && q == \at(q, Pre);

    loop assigns v, a, i;

    loop variant l - i;

  */
while (i<l) {
      v = v*4;
      a = a/4;
      i = i*2;
  }

}