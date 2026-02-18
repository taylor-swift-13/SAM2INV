int main1(int k,int n,int p,int q){
  int l, i, v;

  l=71;
  i=0;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 0;
    loop invariant 0 <= i;
    loop invariant i <= l;
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant 0 <= i <= l;
    loop invariant 0 <= i && i <= l;
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      if ((i%9)==0) {
          v = v-v;
      }
      i = i+1;
  }

}