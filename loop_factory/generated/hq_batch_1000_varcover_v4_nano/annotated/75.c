int main1(int b,int m,int p){
  int l, i, v, x, e, g, y, a;

  l=21;
  i=0;
  v=i;
  x=-6;
  e=i;
  g=l;
  y=m;
  a=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 21;
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant v == i;
    loop invariant e == 3*i;
    loop invariant a == 21 + i*(i-1)/2;
    loop assigns v, e, a, i;
    loop variant l - i;
  */
while (i<l) {
      v = v+1;
      e = e+3;
      a = a+i;
      i = i+1;
  }

}