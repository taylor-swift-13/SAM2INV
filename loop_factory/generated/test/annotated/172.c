int main1(int a,int n,int p,int q){
  int l, i, v;

  l=a+17;
  i=0;
  v=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant ((i == 0 && v == 4) ||
                    (i > 0 && v == i - 1 && i <= l));

    loop invariant l == a + 17;
    loop invariant i >= 0;
    loop invariant v >= 0;
    loop invariant v <= i + 4;
    loop invariant (i == 0) ==> (v == 4);
    loop invariant (i > 0) ==> (v == i - 1);

    loop invariant l == \at(a, Pre) + 17;
    loop invariant 0 <= i;
    loop invariant a == \at(a, Pre);
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v-v;
      v = v+i;
      i = i+1;
  }

}