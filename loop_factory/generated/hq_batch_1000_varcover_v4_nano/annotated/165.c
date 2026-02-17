int main1(int b,int k,int p){
  int l, i, v;

  l=36;
  i=0;
  v=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 36;
    loop invariant 0 <= i;
    loop invariant i <= l;
    loop invariant v == 0 || v == 4;
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      if (i+2<=p+l) {
          v = v-v;
      }
      i = i+1;
  }

}