int main1(int a,int b,int m,int p){
  int l, i, v;

  l=40;
  i=0;
  v=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i <= l;
    loop invariant l == 40;
    loop invariant (i == 0) ==> (v == b);
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+1;
      if ((i%8)==0) {
          v = v-v;
      }
      else {
          v = v+2;
      }
      i = i+1;
  }

}