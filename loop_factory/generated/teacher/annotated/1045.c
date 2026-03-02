int main1(int k,int p){
  int m, h, o;

  m=p+8;
  h=3;
  o=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(p, Pre) + 8;
  loop invariant h == 3;
  loop invariant p == \at(p, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant o >= m;
  loop invariant m == \at(p, Pre) + 8 && h == 3 && p == \at(p, Pre) && k == \at(k, Pre);
  loop invariant o >= m && (o - m) % 4 == 0;
  loop invariant h == 3 && m == \at(p, Pre) + 8 && p == \at(p, Pre) && k == \at(k, Pre);
  loop invariant h == 3 && m == \at(p, Pre) + 8 && o >= m;
  loop invariant p == \at(p, Pre) && k == \at(k, Pre);
  loop invariant h == 3 && m == \at(p, Pre) + 8 && p == \at(p, Pre);
  loop invariant o >= m && k == \at(k, Pre);
  loop invariant o >= \at(p, Pre) + 8;
  loop assigns o;
*/
while (1) {
      o = o+4;
      if (o+3<m) {
          o = o+h;
      }
  }

}
