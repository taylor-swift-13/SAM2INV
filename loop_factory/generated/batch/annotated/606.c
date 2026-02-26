int main1(int k,int m){
  int v, i, c, o;

  v=k+23;
  i=v;
  c=0;
  o=v;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == k + 23;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant c >= 0;
  loop invariant (c == 0) || (o >= 0);
  loop invariant 0 <= c;
  loop invariant c <= o*o;

  loop assigns c, o;
*/
while (c!=0&&o!=0) {
      if (c>o) {
          c = c-o;
      }
      else {
          o = o-c;
      }
      c = c*3;
      o = o/3;
      c = o*o;
      o = o*o+c;
      c = c*o;
  }

}
