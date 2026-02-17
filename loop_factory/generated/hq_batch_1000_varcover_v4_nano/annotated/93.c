int main1(int b,int n,int p){
  int l, i, v, h, o, a, r, x;

  l=50;
  i=l;
  v=l;
  h=-5;
  o=-8;
  a=l;
  r=p;
  x=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i + v == 2*l;
    loop invariant l <= v && v <= 2*l;
    loop invariant h == -5 + (v - l)*l + ((v - l)*(v - l + 1))/2;
    loop invariant 0 <= i && i <= l;
    loop assigns v, h, i;
    loop variant i;
  */
  while (i>0) {
      v = v+1;
      h = h+v;
      i = i-1;
  }

}