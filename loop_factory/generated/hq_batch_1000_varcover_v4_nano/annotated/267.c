int main1(int a,int k,int n,int p){
  int l, i, v, w, z, q, b;

  l=41;
  i=l;
  v=1;
  w=l;
  z=-2;
  q=l;
  b=-3;

  
  /*@

    loop invariant a == \at(a, Pre);

    loop invariant z == -2;

    loop invariant w == 2*v + 39;

    loop invariant 0 <= i && i <= l;

    loop invariant v >= 1;

    loop assigns v, w, z, i;

    loop variant i;

  */
  while (i>0) {
      v = v*2;
      w = w+v;
      z = z%4;
      i = i-1;
  }

}