int main1(int a,int n,int p){
  int l, i, v;

  l=75;
  i=l;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 75;
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant v <= i;
    loop invariant v >= 0;
    loop invariant (i < l) ==> (v == 0);
    loop assigns i, v;
    loop variant i;
  */
  while (i>0) {
      v = v-v;
      if (i+5<=n+l) {
          v = v-v;
      }
      else {
          v = v+v;
      }
      i = i-1;
  }

}