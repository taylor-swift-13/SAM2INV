int main1(int m,int n,int p,int q){
  int l, i, v, o;

  l=79;
  i=l;
  v=q;
  o=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant ((i == 79 && o == 3 && v == q) || (o - i == 2));
    loop invariant i >= 0;
    loop invariant l == 79;
    loop invariant q == \at(q, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant 0 <= i && i <= 79;
    loop invariant ((79 - i) % 2 == 0) <==> (v == \at(q, Pre));
    loop invariant (i < 79) ==> o == i + 2;
    loop invariant m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre) && q == \at(q, Pre);
    loop invariant o >= 1;
    loop invariant o <= i + 3;
    loop invariant i < 79 ==> o == i + 2;
    loop invariant (i == 79 && o == 3) || (o - i == 2);
    loop invariant (i % 2 == 1) ==> (v == \at(q, Pre));
    loop invariant (i % 2 == 0) ==> (v == 1 - \at(q, Pre));
    loop assigns v, o, i;
  */
  while (i>0) {
      v = v+1;
      o = o+v;
      o = 1;
      v = o-v;
      v = v+1;
      o = o+i;
      i = i-1;
  }

}