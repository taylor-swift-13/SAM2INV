int main1(int b,int k,int m,int q){
  int r, d, v;

  r=27;
  d=1;
  v=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d >= 1;
  loop invariant v == 0 || v == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant r == 27;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant ((d == 1) && (v == b)) || ((d >= 2) && (v == 0));
  loop invariant (d >= 1);
  loop invariant (r == 27);
  loop invariant (d >= 2) ==> (v == 0);
  loop invariant (d == 1) ==> v == b;
  loop invariant (d != 1) ==> v == 0;
  loop invariant (b == \at(b, Pre) && k == \at(k, Pre) && m == \at(m, Pre) && q == \at(q, Pre));
  loop invariant r == 27 && b == \at(b, Pre) && k == \at(k, Pre) && m == \at(m, Pre) && q == \at(q, Pre) && (v == 0 || v == b) && (d == 1 ==> v == b) && (d > 1 ==> v == 0);
  loop assigns v, d;
*/
while (1) {
      v = v-v;
      if (d+6<=k+r) {
          v = v+v;
      }
      d = d+1;
  }

}
