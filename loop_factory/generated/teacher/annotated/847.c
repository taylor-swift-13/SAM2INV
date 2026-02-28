int main1(int m,int p,int q){
  int b, y, o, v;

  b=q;
  y=2;
  o=b;
  v=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == b + 3*(y - 2);
  loop invariant b == q;
  loop invariant q == \at(q, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant y >= 2;
  loop invariant (b == q);
  loop invariant (o >= q);
  loop invariant (y >= 2);
  loop invariant (m == \at(m, Pre));
  loop invariant (p == \at(p, Pre));
  loop invariant o >= b;
  loop invariant o == (y - 1)*b + 10*(y - 2) + 3*(y - 2)*(y - 3)/2;
  loop invariant b == \at(q, Pre);

  loop invariant v <= o;
  loop assigns o, y, v;
*/
while (1) {
      if (y>=b) {
          break;
      }
      o = o+1;
      y = y+1;
      o = o+5;
      v = v+3;
      if (v+7<b) {
          v = o-v;
      }
      else {
          o = o+v;
      }
      o = o+1;
  }

}
