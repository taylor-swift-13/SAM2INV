int main1(int b,int k){
  int l, i, v;

  l=k-3;
  i=l;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
        /*@
      loop invariant k == \at(k, Pre);
      loop invariant b == \at(b, Pre);
      loop invariant l == k - 3;
      loop invariant i <= l;

      loop invariant (i == l) ==> (v == k);
      loop invariant (i < l) ==> (v == 1);
      loop invariant v == k || v == 1;

      loop invariant i <= k - 3;

      loop invariant l == \at(k, Pre) - 3;
      loop invariant i <= \at(k, Pre) - 3;
      loop invariant i >= 0 || i == \at(k, Pre) - 3;

      loop assigns i, v;
    */
while (i>0) {
      v = v-v;
      v = v+1;
      i = i-1;
  }

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant k == \at(k, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant l == k - 3;

    loop assigns v;
    */
while (v<i) {
      v = v+1;
  }

}