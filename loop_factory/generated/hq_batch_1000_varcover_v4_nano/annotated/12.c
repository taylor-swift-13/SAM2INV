int main1(int b,int k,int n){
  int l, i, v;

  l=25;
  i=l;
  v=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant l == 25;
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop assigns i;
    loop variant i;
  */
  while (i>0) {
      i = i-1;
  }

}