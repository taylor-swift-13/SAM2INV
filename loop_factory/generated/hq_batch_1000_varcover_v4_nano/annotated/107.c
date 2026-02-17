int main1(int b,int k,int n){
  int l, i, v;

  l=31;
  i=0;
  v=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i && i <= l;
    loop invariant (i == 0) ==> (v == -3);
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+i;
      v = v-v;
      v = v+1;
      v = v+4;
      i = i+1;
  }

}