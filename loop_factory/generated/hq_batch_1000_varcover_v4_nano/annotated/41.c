int main1(int b,int p,int q){
  int l, i, v, r, x, s, f, u;

  l=12;
  i=0;
  v=-8;
  r=0;
  x=p;
  s=-1;
  f=l;
  u=5;

  
  /*@

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant v == -8 + 5*i;

    loop invariant x == p + 3*i;

    loop invariant r == i*(i-1)/2;

    loop invariant 5 <= u <= 5 + i;

    loop assigns v, x, r, i, u;

    loop variant l - i;

  */
  while (i<l) {
      v = v+5;
      x = x+3;
      r = r+i;
      if (i+7<=b+l) {
          u = u+1;
      }
      i = i+1;
  }

}