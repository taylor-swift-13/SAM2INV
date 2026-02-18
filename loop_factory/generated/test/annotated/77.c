int main1(int b,int m,int n,int p){
  int l, i, v;

  l=18;
  i=0;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i <= l;
    loop invariant l == 18;
    loop invariant (i == 0) ==> (v == p);
    loop invariant (i > 0) ==> (v == 0);
    loop invariant p == \at(p, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant (i >= 1) ==> (v == 0);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant 0 <= i <= l;
    loop invariant v == 0 || v == p;
    loop invariant i == 0 ==> v == p;
    loop invariant 0 <= i && i <= l;
    loop invariant i > 0 ==> v == 0;
    loop invariant b == \at(b, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre);
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      if (l<b+2) {
          v = v+4;
      }
      v = v-v;
      if ((i%9)==0) {
          v = v-v;
      }
      i = i+1;
  }

}