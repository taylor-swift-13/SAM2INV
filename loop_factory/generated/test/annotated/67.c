int main1(int b,int m,int p,int q){
  int l, i, v;

  l=65;
  i=l;
  v=2;

  /* >>> LOOP INVARIANTS <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= 65;
    loop invariant (i == 65) ==> (v == 2);
    loop invariant l == 65 && b == \at(b, Pre) && m == \at(m, Pre) && p == \at(p, Pre) && q == \at(q, Pre);
    loop invariant (i == l) ==> (v == 2);
    loop invariant i <= l;
    loop invariant b == \at(b, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant l == 65;
    loop invariant v == 2 || v == 0;
    loop assigns i, v;
  */
  while (i>0) {
      v = v-v;
      i = i-1;
  }

}