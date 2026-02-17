int main1(int a,int b,int n){
  int l, i, v, t, k, q, o, y, s, w;

  l=64;
  i=l;
  v=n;
  t=n;
  k=i;
  q=4;
  o=l;
  y=n;
  s=-4;
  w=a;

  
  /*@

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant \at(n,Pre) > 0 ==> v > 0;

    loop invariant \at(n,Pre) > 0 ==> t > 0;

    loop invariant \at(n,Pre) > 0 ==> v != 0 && t != 0;

    loop assigns v, t;

  */
  while (v!=0&&t!=0) {
      if (v>t) {
          v = v-t;
      }
      else {
          t = t-v;
      }
      v = v*2+1;
      t = t*v+1;
  }

}