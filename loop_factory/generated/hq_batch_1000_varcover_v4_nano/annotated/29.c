int main1(int m,int n,int p){
  int l, i, v, s, f, c, x, h;

  l=80;
  i=0;
  v=m;
  s=-3;
  f=p;
  c=i;
  x=1;
  h=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i <= l;
    loop invariant (i == 0) ==> (c == 0);
    loop assigns i, c;
    loop variant l - i;
  */
  while (i<l) {
      c = c*c+v;
      i = i+1;
  }

}