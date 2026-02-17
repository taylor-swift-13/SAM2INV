int main1(int k,int n,int q){
  int l, i, v, d, o, b, r, a;

  l=(n%6)+20;
  i=l;
  v=6;
  d=q;
  o=k;
  b=-8;
  r=i;
  a=2;

  
  /*@

    loop invariant ((v - o) == (6 - k));

    loop invariant ((v + 2*i) == (6 + 2*l));

    loop invariant (i >= 0);

    loop invariant (i <= l);

    loop invariant (k == \at(k, Pre));

    loop assigns v, o, i;

    loop variant i;

  */
  while (i>0) {
      v = v+2;
      o = o+2;
      i = i-1;
  }

}