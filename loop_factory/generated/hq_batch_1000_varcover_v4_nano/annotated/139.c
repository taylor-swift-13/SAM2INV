int main1(int m,int n,int q){
  int l, i, v;

  l=36;
  i=0;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 36;
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant v == 0;
    loop assigns v, i;
  */
  while (i<l) {
      v = v-v;
      i = i+1;
  }

}