int main1(int m,int p,int q){
  int l, i, v;

  l=43;
  i=0;
  v=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 43;
    loop invariant 0 <= i;
    loop invariant i <= l;
    loop invariant v <= -2;
    loop invariant (i == 0) ==> (v == -2);
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v+v;
      v = v+1;
      i = i+1;
  }

}