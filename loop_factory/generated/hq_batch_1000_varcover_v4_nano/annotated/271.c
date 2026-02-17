int main1(int a,int n,int p,int q){
  int l, i, v, f, e, x, z;

  l=26;
  i=0;
  v=-4;
  f=a;
  e=q;
  x=i;
  z=-5;

  
  /*@

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant i % 2 == 0;

    loop invariant 2*v == -8 + 3*i;

    loop invariant 2*e == 2*q + 3*i;

    loop invariant i == 2*x;

    loop assigns v, e, x, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+3;
      e = e+3;
      x = x+1;
      i = i+2;
  }

}