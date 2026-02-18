int main1(int b,int k,int n,int p){
  int l, i, v;

  l=58;
  i=l;
  v=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant l == 58;
    loop invariant i >= 0;
    loop invariant i <= 58;
    loop invariant v == -1 || v == 0;
    loop invariant (v == -1) ==> (i == 58);
    loop invariant b == \at(b, Pre) && k == \at(k, Pre) && n == \at(n, Pre) && p == \at(p, Pre);
    loop invariant i <= l;
    loop invariant (v == -1) || (v == 0);
    loop invariant b == \at(b, Pre) && k == \at(k, Pre);
    loop invariant n == \at(n, Pre) && p == \at(p, Pre);
    loop invariant 0 <= i && i <= 58;
    loop assigns i, v;
    loop variant i;
  */
  while (i>0) {
      v = v*v+v;
      i = i-1;
  }

}