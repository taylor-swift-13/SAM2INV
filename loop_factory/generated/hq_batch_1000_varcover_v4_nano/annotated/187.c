int main1(int b,int k,int m){
  int l, i, v, g, t, x;

  l=20;
  i=0;
  v=i;
  g=b;
  t=i;
  x=l;

  
  /*@

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant v == 2*i;

    loop invariant g == b + i*(i+1);

    loop invariant t == i*b + i*(i+1)*(i+2)/3;

    loop assigns v, g, t, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+2;
      g = g+v;
      t = t+g;
      i = i+1;
  }

}