int main1(int k,int n,int p){
  int l, i, v, t, f, u, z, q, b;

  l=63;
  i=0;
  v=p;
  t=k;
  f=i;
  u=-4;
  z=k;
  q=n;
  b=p;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant p == \at(p,Pre) && k == \at(k,Pre) && n == \at(n,Pre);

    loop invariant (\at(p,Pre) + 3 == 0) ==> (v + 3 == 0);


    loop assigns i, v;

    loop variant l - i;

  */
while (i<l) {
      v = v*2+3;
      i = i+1;
  }

}