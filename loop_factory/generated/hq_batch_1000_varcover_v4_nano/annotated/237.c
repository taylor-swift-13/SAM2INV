int main1(int k,int m,int p){
  int l, i, v, r, z, e, d;

  l=(p%10)+9;
  i=0;
  v=-3;
  r=-5;
  z=i;
  e=l;
  d=i;

  
  /*@

    loop invariant i % 3 == 0;

    loop invariant 0 <= i;

    loop invariant i <= l + 2;

    loop invariant v == -3;

    loop invariant d == 0;

    loop invariant i == 0 || e == d*d;

    loop assigns e, v, i;

    loop variant l - i;

  */
while (i<l) {
      e = e*e+v;
      v = v%5;
      e = d*d;
      i = i+3;
  }

}