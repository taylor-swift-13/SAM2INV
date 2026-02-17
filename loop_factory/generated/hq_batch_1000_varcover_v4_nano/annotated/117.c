int main1(int a,int m,int q){
  int l, i, v, w, u, f, n;

  l=71;
  i=0;
  v=a;
  w=0;
  u=1;
  f=a;
  n=8;

  
  /*@

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant l == 71;

    loop invariant w == 2*v - 2*a;

    loop invariant a == \at(a, Pre);

    loop assigns v, w, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v*2;
      w = w+v;
      i = i+1;
  }

}