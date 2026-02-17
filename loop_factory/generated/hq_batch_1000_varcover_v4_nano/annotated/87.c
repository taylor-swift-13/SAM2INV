int main1(int a,int b,int q){
  int l, i, v, e, t, o;

  l=32;
  i=0;
  v=-1;
  e=a;
  t=l;
  o=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 2*i - 1;
    loop invariant t == l + 3*i;
    loop invariant 0 <= i;
    loop invariant i <= l;
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant q == \at(q, Pre);
    loop assigns i, v, t;
    loop variant l - i;
  */
  while (i<l) {
      v = v+2;
      t = t+3;
      i = i+1;
  }

}