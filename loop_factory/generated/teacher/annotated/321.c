int main1(int b,int k){
  int m, u, v, a;

  m=(k%34)+12;
  u=1;
  v=8;
  a=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == (k%34) + 12;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);



  loop invariant m == ((\at(k,Pre) % 34) + 12);

  loop invariant (0 <= v);
  loop invariant (v <= 8);
  loop invariant m == (k % 34) + 12 &&
                   (u == 1) ==> (a == b && v == 8) &&
                   (u != 1) ==> (a == 0 && v == 0) &&
                   u > 0;
  loop invariant (u == 1) ==> (v == 8) &&
                   (u != 1) ==> (v == 0);

  loop invariant v == 8 || (0 <= v && v <= 6);
  loop assigns v, a, u;
*/
while (u*2<=m) {
      v = v*v+v;
      v = v%9;
      a = a*v;
      v = v%7;
      u = u*2;
  }

}
