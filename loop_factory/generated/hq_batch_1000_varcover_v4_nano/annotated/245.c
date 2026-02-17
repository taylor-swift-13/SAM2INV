int main1(int m,int p,int q){
  int l, i, v;

  l=69;
  i=0;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant (i == 0) ==> (v == 69);
    loop invariant 0 <= i;
    loop invariant i <= l;
    loop invariant l == 69;
    loop invariant v >= 0;
    loop assigns v, i;
  */
  while (i<l) {
      v = v-v;
      if (v+7<l) {
          v = v+i;
      }
      else {
          v = v+6;
      }
      v = v+v;
      i = i+1;
  }

}