int main1(int m,int q){
  int b, l, v, r, o, y;

  b=21;
  l=1;
  v=0;
  r=q;
  o=-1;
  y=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= v;
  loop invariant v <= b;
  loop invariant (o == -1) || (o == q);
  loop invariant b == 21;
  loop invariant o <= -1 || o <= y;
  loop invariant y == q;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant o == -1 || o == q;
  loop invariant (q > -1) ==> o == -1;
  loop invariant v <= b && v >= 0 && (o == -1 || o == y) && b == 21 && y == q;
  loop invariant 0 <= v <= b;
  loop invariant o == -1 || o == y;
  loop assigns v, o;
*/
while (v<b) {
      v = v+1;
      if (y<=o) {
          o = y;
      }
  }

}
