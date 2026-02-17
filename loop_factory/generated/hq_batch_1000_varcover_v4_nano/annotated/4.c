int main1(int b,int m,int p){
  int l, i, v, k, t, r;

  l=66;
  i=0;
  v=-1;
  k=p;
  t=m;
  r=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i <= l;
    loop invariant l == 66;
    loop invariant b == \at(b, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant p == \at(p, Pre);
    loop assigns i;
    loop variant l - i;
  */
  while (i<l) {
      i = i+1;
  }

}