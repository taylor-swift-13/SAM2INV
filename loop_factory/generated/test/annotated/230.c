int main1(int a,int p){
  int l, i, v;

  l=36;
  i=0;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 0;
    loop invariant a == \at(a, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant l == 36;
    loop invariant 0 <= i && i <= l;
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v-v;
      i = i+1;
  }

}