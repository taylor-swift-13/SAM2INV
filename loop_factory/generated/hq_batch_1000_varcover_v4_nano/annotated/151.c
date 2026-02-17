int main1(int a,int n,int p){
  int l, i, v;

  l=46;
  i=l;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 46;
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant v == a || v == 0;
    loop invariant a == \at(a, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop assigns v, i;
    loop variant i;
  */
  while (i>0) {
      v = v+1;
      v = v+4;
      v = v-v;
      v = v+v;
      i = i-1;
  }

}