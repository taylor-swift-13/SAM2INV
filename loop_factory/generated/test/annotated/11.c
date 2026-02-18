int main1(int a,int b,int k,int n){
  int l, i, v;

  l=77;
  i=0;
  v=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant v == -5 + i*(i-1)/2 + 4*i;
    loop invariant l == 77;
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant 0 <= i && i <= l;
    loop invariant v == -5 + (i*(i+7))/2;
    loop invariant i*i + 7*i == 2*v + 10;
    loop invariant 0 <= i;
    loop invariant 0 <= i <= l;
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+i;
      v = v+4;
      i = i+1;
  }

}