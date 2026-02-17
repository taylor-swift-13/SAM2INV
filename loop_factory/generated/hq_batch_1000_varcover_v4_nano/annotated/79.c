int main1(int a,int b,int p){
  int l, i, v, e, x, h, k, j;

  l=34;
  i=l;
  v=b;
  e=l;
  x=p;
  h=5;
  k=b;
  j=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant e == 34 + 2*v - 2*\at(b,Pre);
    loop invariant i >= 0;
    loop invariant i <= 34;
    loop invariant a == \at(a,Pre);
    loop invariant b == \at(b,Pre);
    loop invariant p == \at(p,Pre);
    loop assigns v, e, i;
  */
  while (i>0) {
      v = v*2;
      e = e+v;
      i = i/2;
  }

}