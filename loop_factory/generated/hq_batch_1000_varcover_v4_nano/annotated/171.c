int main1(int b,int n,int q){
  int l, i, v, d, h, e, x;

  l=55;
  i=0;
  v=i;
  d=-2;
  h=i;
  e=n;
  x=1;

  
  /*@

    loop invariant v == 4*i;

    loop invariant d == 2*i*i + 2*i - 2;

    loop invariant h == (2*i*i*i + 6*i*i - 2*i)/3;

    loop invariant 0 <= i <= l;

    loop assigns v, d, h, i;

  */
while (i<l) {
      v = v+4;
      d = d+v;
      h = h+d;
      i = i+1;
  }

}