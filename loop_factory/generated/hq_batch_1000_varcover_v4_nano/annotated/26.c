int main1(int a,int n,int p){
  int l, i, v;

  l=58;
  i=0;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant l == 58;
    loop invariant (i == 0) ==> v == \at(p, Pre);
    loop invariant (i > 0) ==> v == 1;
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      if (i+2<=p+l) {
          v = v+i;
      }
      else {
          v = v+i;
      }
      v = v-v;
      v = v+v;
      if (i+1<=l+l) {
          v = v+1;
      }
      i = i+1;
  }

}