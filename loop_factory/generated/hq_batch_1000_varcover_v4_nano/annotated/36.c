int main1(int k,int n,int q){
  int l, i, v, o, x, t, a;

  l=31;
  i=0;
  v=i;
  o=q;
  x=-1;
  t=q;
  a=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i && i <= l;
    loop invariant l == 31;
    loop invariant v == 0;
    loop invariant (i == 0) ==> (t == \at(q, Pre));
    loop assigns i, t;
  */
  while (i<l) {
      t = t*t+v;
      i = i+1;
  }

}