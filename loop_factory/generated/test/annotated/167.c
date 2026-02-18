int main1(int a,int k,int m,int p){
  int l, i, v;

  l=a-3;
  i=0;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v <= i;
    loop invariant v >= i - 4;
    loop invariant i >= 0;
    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant l == a - 3;
    loop invariant i - 3 <= v <= i;

    loop invariant (i == 0) ==> (v == 0);
    loop invariant (i > 0) ==> (v == i - 3);
    loop invariant (i == 0 && v == 0) || (i >= 1 && v == i - 3);
    loop invariant ((i == 0 && v == 0) || (v == i - 3));
    loop assigns i, v;
    loop variant (l - i);
  */
  while (i<l) {
      v = i-3;
      v = v+1;
      i = i+1;
  }

}