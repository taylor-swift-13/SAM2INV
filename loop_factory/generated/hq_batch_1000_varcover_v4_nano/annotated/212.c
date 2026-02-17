int main1(int m,int p,int q){
  int l, i, v, h;

  l=72;
  i=0;
  v=m;
  h=-5;

  
  /*@

    loop invariant l == 72;

    loop invariant h == -5;

    loop invariant i % 4 == 0;

    loop invariant 0 <= i && i <= l;

    loop invariant v == m + (i/4) * (2*h + 1);

    loop assigns i, v;

    loop variant l - i;

  */
while (i<l) {
      v = v+h+h;
      v = v+1;
      i = i+4;
  }

}