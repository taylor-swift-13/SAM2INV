int main1(int a,int b,int p,int q){
  int l, i, v, w, u, t;

  l=58;
  i=0;
  v=i;
  w=i;
  u=a;
  t=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a, Pre);
    loop invariant i <= l;
    loop invariant v == i*(i-1)/2;
    loop invariant w == 0;
    loop invariant u == a;
    loop invariant i >= 0;
    loop assigns v, w, u, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+i;
      w = w*w;
      u = u+v*w;
      i = i+1;
  }

}