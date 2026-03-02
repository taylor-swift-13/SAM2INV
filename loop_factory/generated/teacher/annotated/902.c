int main1(int b,int m){
  int g, w, v;

  g=(m%23)+4;
  w=0;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant g == (\at(m, Pre) % 23) + 4;
  loop invariant v >= 0;

  loop invariant b == \at(b,Pre);
  loop invariant m == \at(m,Pre);
  loop invariant g == (\at(m,Pre) % 23) + 4;

  loop invariant v == 0 || v >= 4;
  loop invariant g == \at(m, Pre) % 23 + 4;
  loop invariant b == \at(b, Pre) && m == \at(m, Pre) && g == (m % 23) + 4;
  loop invariant b == \at(b, Pre) && m == \at(m, Pre);
  loop invariant g == ((\at(m, Pre) % 23) + 4) && v >= 0;
  loop assigns v;
*/
while (1) {
      v = v+2;
      v = v*v;
  }

}
