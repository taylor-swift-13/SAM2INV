int main1(int b,int n){
  int l, i, v;

  l=46;
  i=0;
  v=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 46;
    loop invariant i <= l;
    loop invariant (i == 0) <==> (v == 2);
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant 0 <= i <= l;
    loop invariant (i == 0) ==> (v == 2);
    loop invariant i >= 0;
    loop invariant v == 2 || v == 0;
    loop invariant i >= 0 && i <= l;
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = l*(-6);
      v = v-v;
      i = i+1;
  }

}