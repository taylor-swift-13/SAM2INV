int main1(int n,int p,int q){
  int l, i, v;

  l=p+11;
  i=0;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == p + 11;
    loop invariant 0 <= i;
    loop invariant i <= l || l <= 0;
    loop invariant (p <= 0) ==> (v >= p);
    loop assigns i, v;
  */
while (i<l) {
      if ((i%5)==0) {
          v = v+1;
      }
      else {
          v = v+4;
      }
      if (v+3<l) {
          v = v+3;
      }
      v = v+1;
      if ((i%6)==0) {
          v = v-v;
      }
      i = i+1;
  }

}