int main1(int a,int k,int q){
  int l, i, v, m, h, w, r, f, g;

  l=62;
  i=l;
  v=0;
  m=k;
  h=4;
  w=1;
  r=a;
  f=-8;
  g=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant w == 1;
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant q == \at(q, Pre);
    loop assigns i, w;
    loop variant i;
  */
  while (i>0) {
      w = w*w+v;
      i = i/2;
  }

}