int main1(int k,int p,int q){
  int l, i, v, o, d;

  l=37;
  i=0;
  v=-4;
  o=p;
  d=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == -4 + 2*i;
    loop invariant o == p + i*i - 4*i;
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant k == \at(k, Pre);
    loop invariant p == \at(p, Pre);
    loop assigns v, o, i;
  */
  while (i<l) {
      v = v+1;
      o = o+v;
      v = v+1;
      i = i+1;
  }

}